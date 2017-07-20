-module(hipe_icode_profile_driven_inline).


-export([cfg/2, linear/2]).

%% Server Functions
-export([init/2]).

-include("../flow/cfg.hrl").
-include("../main/hipe.hrl").
-include("hipe_icode.hrl").

% -define(WITH_DYN_SERVER, true).
-define(WITH_DYN_SERVER, false).

% -define(timing, true).

-ifdef(timing).
-define(TIME_START(Flag),
  put(Flag, erlang:monotonic_time())).
-else.
-define(TIME_START(_Flag), true).
-endif.

-ifdef(timing).
-define(TIME_STOP(Flag, Text),
  io:format(standard_error, "  Duration: ~pms, ~s~n", [round((erlang:monotonic_time()-get(Flag))/1000000), Text])).
-else.
-define(TIME_STOP(_Flag, _Text), true).
-endif.

%%-------------------------------------------------------------------
%% A pass that inlines functions based on call data that has been 
%% gathered during execution
%%-------------------------------------------------------------------

%% IMPORTANT: Atm we don't allow tail recursive functions to be inlined

-spec linear(icode(), #comp_servers{}) -> icode().
linear(Icode, #comp_servers{inline = ServerPid}) ->
  MFA = hipe_icode:icode_fun(Icode),
  ServerPid ! {ready, Icode, MFA, self()},
  receive
    {done, NewIcode} ->
      update_ranges(NewIcode)
  end.

-spec cfg(cfg(), #comp_servers{}) -> cfg().
cfg(Cfg, CompServers) ->
  Icode = hipe_icode_cfg:cfg_to_linear(Cfg),
  NewIcode = linear(Icode, CompServers),
  hipe_icode_cfg:linear_to_cfg(NewIcode).

-spec init(map(), non_neg_integer()) -> ok.
init(Data, NumberProcs) ->
  case pre_pass(NumberProcs) of
    {IcodeMap, Pids} ->
      NewData = filter_data(Data, IcodeMap),
      NewIcodeMap = process(NewData, IcodeMap),
      post_pass(NewIcodeMap, Pids),
      stop();
    stop ->
      ok
  end.

update_ranges(Icode) ->
  IcodeCode = hipe_icode:icode_code(Icode),
  HighVar = hipe_icode:highest_var(IcodeCode),
  HighLabel = hipe_icode:highest_label(IcodeCode),
  hipe_gensym:set_var(icode, HighVar + 1),
  hipe_gensym:set_label(icode, HighLabel + 1),
  Icode.

pre_pass(N) ->
  pre_pass(N, #{}, []).

pre_pass(0, IcodeMap, Pids) ->
  {IcodeMap, Pids};
pre_pass(N, IcodeMap, Pids) ->
  receive
    {ready, Icode, MFA, Pid} ->
      pre_pass(N-1, IcodeMap#{MFA => Icode}, [{Pid, MFA}|Pids]);
    {stop, MainPid} ->
      MainPid ! ok,
      stop
  end.


filter_data(Data, _IcodeMap) ->

  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %% IMPORTANT: This existed previously because we didn't allow for
  %% tail recursive functions to be inlined because it created an infinite loop
  %% However the problem was probably caused by something else and now it seems
  %% fixed. We can remove the following filtering for now
  %%
  %%
  %% Find if each function is tail recursive
  % Leafness = maps:map(
  %   fun(_MFA, Icode) ->
  %     IcodeCode = hipe_icode:icode_code(Icode),
  %     IsClosure = hipe_icode:icode_is_closure(Icode),
  %     hipe_beam_to_icode:leafness(IcodeCode, IsClosure)
  %   end, IcodeMap),
  % io:format("Leafness: ~p~n", [Leafness]),
  %%
  % maps:map(
  %   fun(_Caller, CalleeList) ->
  %     [{Callee, N} || {Callee,N} <- CalleeList, maps:get(Callee, Leafness) =/= selfrec]
  %   end,Data),
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


  Data.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Priority Queue Implementation
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


prepare_call_pq(Data) ->
  CallsList0 = [[{{Caller, Callee}, N} || {Callee, N} <- CalleeList]
                  || {Caller, CalleeList} <- maps:to_list(Data)],
  CallsList = lists:flatten(CallsList0),
  CallMap = maps:from_list(CallsList),
  CallMap.

%% TODO: Find a more elegant way to initialize the fold
pop_call_from_pq(CallMap) ->
  case maps:size(CallMap) of
    0 ->
      none;
    _ ->
      {MaxKey, MaxVal} =
        maps:fold(fun keep_max/3, {{undef, undef}, 0}, CallMap),
      {MaxVal, RestCallMap} = maps:take(MaxKey, CallMap),
      {{MaxKey, MaxVal}, RestCallMap}
  end.

keep_max(Key, N, {_MaxKey, MaxN}) when N >= MaxN ->
  {Key, N};
keep_max(_Key, _N, {MaxKey, MaxN}) ->
  {MaxKey, MaxN}.

%% TODO: Complete update call_pq
%% (OK) Pre. Before calling the loop/3 function create a map containing
%%           how many times each function has been called in total
%% 1. Find all {b,x,Nbx} calls
%% 2. Add them to the Map as {a,x,(Nab/Nb)*Nbx}
%% 3. If {a,x,OldNax} already exists add the new Nax
update_call_pq({{FunA, FunB}, Nab}, CallMap, TimesCalled) ->
  CalleeCalls =
    maps:filter(
      fun({Fun, _}, _) ->
        Fun =:= FunB
      end, CallMap),
  #{FunB := Nb} = TimesCalled,
  NewCallerCalls =
    [{{FunA, Callee}, round((Nab/Nb)*Nbx)}
      || {{_FunB, Callee}, Nbx} <- maps:to_list(CalleeCalls)],
  % io:format(standard_error, "NewCallerCalls: ~p~n", [NewCallerCalls]),
  NewCallMap = lists:foldl(fun update_call_map/2, CallMap, NewCallerCalls),
  % io:format(standard_error, "NewCallMap: ~p~n", [NewCallMap]),
  NewCallMap.

update_call_map({{Caller, Callee}, NewN}, CallMap) ->
  maps:update_with({Caller, Callee},
    fun(OldN) -> OldN + NewN end, NewN, CallMap).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

total_calls(IcodeMap, CallMap) ->
  MfaMap = maps:map(fun(_MFA,_) -> 0 end, IcodeMap),
  maps:fold(fun sum_calls/3, MfaMap, CallMap).

sum_calls({_Caller, Callee}, Times, TotalCalls) ->
  maps:update_with(Callee, fun(X) -> X + Times end, TotalCalls).

%% TODO: Implement the naive algorithm here
process(Data, IcodeMap) ->

  %% Create a list with all the call info
  CallMap = prepare_call_pq(Data),
  % io:format(standard_error, "Initial Call Map: ~p~n", [CallMap]),
  NewIcodeMap = loop(IcodeMap, CallMap),

  NewIcodeMap.



loop(IcodeMap, CallMap) ->
  CurrentInlinesList = [{MFA, MFA} || {MFA, _Icode} <- maps:to_list(IcodeMap)],
  CurrentInlines = sets:from_list(CurrentInlinesList),

  TotalCalls = total_calls(IcodeMap, CallMap),
  loop(IcodeMap, TotalCalls, CurrentInlines, CallMap).


%% TODO: Fix wrong spec
-spec loop(#{mfa() := icode()},                 % A map from mfas to cfgs
           #{mfa() := integer()},               % A map from mfas to number of times called
           sets:set({mfa(), mfa()}),            % A map with the already done inlining for each function. This exists to prevent loops
           [{mfa(), {mfa(), integer()}}]) ->    % A list with all calls and their numbers
              #{mfa() := icode()}.              % A map with the new cfgs

loop(IcodeMap, TotalCalls, CurrentInlines, CallMap) ->
  case pop_call_from_pq(CallMap) of
    none ->
      IcodeMap;
    {Max, Rest} ->
      % io:format(standard_error, "Next: ~p~nRest: ~p~n", [Max, Rest]),
      case check_inline_call(Max, IcodeMap, CurrentInlines) of
        {ok, NewIcodeMap} ->
          {{Caller, Callee}, _NumCalls} = Max,
          NewCurrentInlines =
            sets:add_element({Caller, Callee}, CurrentInlines),
          NewCallMap = update_call_pq(Max, Rest, TotalCalls),
          loop(NewIcodeMap, TotalCalls, NewCurrentInlines, NewCallMap);
        false ->
          loop(IcodeMap, TotalCalls, CurrentInlines, Rest)
      end
    end.


check_inline_call(Call, IcodeMap, CurrInl) ->
  Conditions =
    [fun has_been_inlined_already/3,
     fun happens_enough_times/3],
  case lists:all(fun id/1, [F(Call, IcodeMap, CurrInl) || F <- Conditions]) of
    true ->
      inline_call(Call, IcodeMap);
    false ->
      false
  end.

has_been_inlined_already({{Caller, Callee}, _NumberCalls}, _IcodeMap, CurrentInlines) ->
  not sets:is_element({Caller, Callee}, CurrentInlines).

happens_enough_times({_, NumberCalls}, _IcodeMap, _CurrentInlines) ->
  NumberCalls > 10.

inline_call({{Caller, Callee}, _NumberCalls}, IcodeMap) ->
  % io:format("Caller: ~p~nCallee: ~p~n", [Caller, Callee]),
  #{Caller := CallerIcode} = IcodeMap,
  #{Callee := CalleeIcode} = IcodeMap,
  NewCallerIcode = make_inlines(CallerIcode, Callee, CalleeIcode),
  NewIcodeMap = IcodeMap#{Caller := NewCallerIcode},
  {ok, NewIcodeMap}.


%% TODO: Make inline should become a fold function so that if more than
%%       one inline of the same callee in the same caller happens,
%%       it will have correct variables and labels
%% TODO: Handle call continuations and fail labels
%% TODO: Fill this stub by making the inline
%% 1. Get the caller variable range
%% 2. Map all the callee variables to caller variables with different names
%% 3. Map all the callee labels to caller labels with new names
%% 3. Remove the redtest and what follows it from the caller
%% 4. For every function call to callee
%% 4.1. Put all the callee blocks inside the caller
%% 4.2. Move the arguments to the new variables
%% 4.3. Move the result to the correct variable
%% 4.3.1. In order to do this I have to find every return command and add a move after it.
%% 4.3.2. I also have to add a goto after the move so that all the return instructions go to the correct block.
%% 4.4. Turn every enter into a call if we inline an #icode_call
-spec make_inlines(icode(), mfa(), icode()) -> icode().
make_inlines(CallerIcode, _Callee, CalleeIcode) ->
  %% Find current max_var
  {_MinVar, MaxVar} = hipe_icode:icode_var_range(CallerIcode),
  VarOffset = MaxVar + 1,

  %% Map and substitute labels
  {_MinLabel, MaxLabel} = hipe_icode:icode_label_range(CallerIcode),
  LabelOffset = MaxLabel + 1,

  CallerIcodeCode = hipe_icode:icode_code(CallerIcode),
  {NewCallerIcodeCode, _FinalVarOffset, _FinalLabelOffset} = lists:foldr(fun(Ins, Acc) ->
            check_make_inline(Ins, CalleeIcode, Acc) end,
            {[], VarOffset, LabelOffset}, CallerIcodeCode),

  NewCallerIcode = hipe_icode:icode_code_update(CallerIcode, NewCallerIcodeCode),


  NewCallerIcode.

%% TODO: Make inline for enters
check_make_inline(Ins, CalleeIcode, {Code, VarOffset, LabelOffset}) ->
  Callee = hipe_icode:icode_fun(CalleeIcode),
  case Ins of
    #icode_call{} ->
      case hipe_icode:successors(Ins) of
        [] ->
          case hipe_icode:call_fun(Ins) of
            Callee ->
              {InlinedCallee, NewVarOffset, NewLabelOffset} =
                make_inline_call(Ins, CalleeIcode, VarOffset, LabelOffset),
              {InlinedCallee ++ Code, NewVarOffset, NewLabelOffset};
              % {[Ins|Code], VarOffset, LabelOffset};
            _ ->
              {[Ins|Code], VarOffset, LabelOffset}
          end;
        _Successors ->
          {[Ins|Code], VarOffset, LabelOffset}
      end;
    #icode_enter{} ->
      case hipe_icode:enter_fun(Ins) of
        Callee ->
          {InlinedCallee, NewVarOffset, NewLabelOffset} =
            make_inline_enter(Ins, CalleeIcode, VarOffset, LabelOffset),
          {InlinedCallee ++ Code, NewVarOffset, NewLabelOffset};
        _ ->
          {[Ins|Code], VarOffset, LabelOffset}
      end;
    _ ->
      {[Ins|Code], VarOffset, LabelOffset}
  end.

make_inline_call(IcodeCall, CalleeIcode, VarOffset, LabelOffset) ->
  {CalleeIcodeCode, MoveInstructions} =
    common_inline(IcodeCall, CalleeIcode, VarOffset, LabelOffset),
  %% Because this is a call we have to transform all enters into calls
  CalleeIcodeCode1 = transform_enters(CalleeIcodeCode),

  %% Create a return label
  {_, MaxLabel} = hipe_icode:icode_label_range(CalleeIcode),
  ReturnLabelName = MaxLabel + LabelOffset + 1,
  ReturnLabel = hipe_icode:mk_label(ReturnLabelName),

  [DstVar] = hipe_icode:call_dstlist(IcodeCall),
  CalleeIcodeCode2 = transform_returns(DstVar, ReturnLabelName, CalleeIcodeCode1),

  {_, MaxVar} = hipe_icode:icode_var_range(CalleeIcode),
  NewVarOffset = MaxVar + VarOffset + 1,
  NewLabelOffset = MaxLabel + LabelOffset + 2,

  FinalIcodeCode = MoveInstructions ++ CalleeIcodeCode2 ++ [ReturnLabel],
  % io:format(standard_error, "OldIcode: ~p~nNewIcode: ~p~n", [CalleeIcodeCode, FinalIcodeCode]),
  {FinalIcodeCode, NewVarOffset, NewLabelOffset}.

make_inline_enter(IcodeCall, CalleeIcode, VarOffset, LabelOffset) ->
  {CalleeIcodeCode, MoveInstructions} =
    common_inline(IcodeCall, CalleeIcode, VarOffset, LabelOffset),

  {_, MaxLabel} = hipe_icode:icode_label_range(CalleeIcode),
  {_, MaxVar} = hipe_icode:icode_var_range(CalleeIcode),
  NewVarOffset = MaxVar + VarOffset + 1,
  NewLabelOffset = MaxLabel + LabelOffset + 1,

  FinalIcodeCode = MoveInstructions ++ CalleeIcodeCode,
  % io:format(standard_error, "OldIcode: ~p~nNewIcode: ~p~n", [CalleeIcodeCode, FinalIcodeCode]),
  {FinalIcodeCode, NewVarOffset, NewLabelOffset}.

common_inline(IcodeCall, CalleeIcode, VarOffset, LabelOffset) ->
  CalleeIcodeCode = hipe_icode:icode_code(CalleeIcode),

  %% Map and substitute variables
  CalleeIcodeCode1 = map_variables(CalleeIcodeCode, VarOffset),

  %% Map and substitute labels
  CalleeIcodeCode2 = map_labels(CalleeIcodeCode1, LabelOffset),

  %% Remove redtests from callee icode code
  CalleeIcodeCode3 = [Instr || Instr <- CalleeIcodeCode2, not is_redtest(Instr)],

  %% Move arguments
  Params = [subst_var(Var, VarOffset) || Var <- hipe_icode:icode_params(CalleeIcode)],
  Args = args(IcodeCall),
  MoveInstructions = lists:zipwith(fun hipe_icode:mk_move/2, Params, Args),
  {CalleeIcodeCode3, MoveInstructions}.

transform_enters(Code) ->
  transform_enters(Code, []).

transform_enters([], NewCode) ->
  lists:reverse(NewCode);
transform_enters([Ins|Code], NewCode) ->
  case hipe_icode:is_enter(Ins) of
    true ->
      Dst = hipe_icode:mk_var(0),
      Call = icode_enter_to_call(Ins, [Dst]),
      Return = hipe_icode:mk_return([Dst]),
      transform_enters(Code, [Return, Call|NewCode]);
    false ->
      transform_enters(Code, [Ins|NewCode])
  end.

icode_enter_to_call(Enter, DstList) ->
  %% IMPORTANT: This case is important because entering
  %%            an anonymous function happens by calling
  %%            the enter_fun primop
  Fun =
    case hipe_icode:enter_fun(Enter) of
      enter_fun -> call_fun;
      F -> F
    end,
  Args = hipe_icode:enter_args(Enter),
  Type = hipe_icode:enter_type(Enter),
  hipe_icode:make_call(DstList, Fun, Args, Type, [], [], false).

transform_returns(DstVar, ReturnLabelName, Code) ->
  transform_returns(DstVar, ReturnLabelName, [], Code).

transform_returns(_DstVar, _ReturnLabelName, NewCode, []) ->
  lists:reverse(NewCode);
transform_returns(DstVar, ReturnLabelName, NewCode, [Ins|OldCode]) ->
  case hipe_icode:is_return(Ins) of
    true ->
      [ReturnVar] = hipe_icode:return_vars(Ins),
      MoveIns = hipe_icode:mk_move(DstVar, ReturnVar),
      GotoIns = hipe_icode:mk_goto(ReturnLabelName),
      transform_returns(DstVar, ReturnLabelName, [GotoIns, MoveIns|NewCode], OldCode);
    false ->
      transform_returns(DstVar, ReturnLabelName, [Ins|NewCode], OldCode)
  end.

is_redtest(Instr) ->
  case Instr of
    #icode_call{dstlist = [],
                'fun' = redtest,
                args = [],
                type = primop} ->
      true;
    Instr ->
      false
  end.

args(#icode_call{} = Call) -> hipe_icode:call_args(Call);
args(#icode_enter{} = Enter) -> hipe_icode:enter_args(Enter).

map_labels(Icode, LabelOffset) ->
  NewIcode = [subst_labels(Instr, LabelOffset) || Instr <- Icode],
  % io:format(standard_error, "OldIcode: ~p~nNewIcode: ~p~n", [Icode, NewIcode]),
  NewIcode.

subst_labels(Instr, LabelOffset) ->
  case hipe_icode:is_label(Instr) of
    true ->
      subst_label(Instr, LabelOffset);
    false ->
      OldLabels0 = hipe_icode:successors(Instr),
      %% WARNING: Very important to sort labels
      %% and process them from higher to lower so that
      %% they don't overlap
      SortingFun = fun(A,B) -> A > B end,
      OldLabels = lists:sort(SortingFun, OldLabels0),
      lists:foldl(fun(L, I) -> redirect_jmps(L, LabelOffset, I) end, Instr, OldLabels)
  end.

redirect_jmps(OldLabel, LabelOffset, Instr) ->
  NewLabel = OldLabel + LabelOffset,
  hipe_icode:redirect_jmp(Instr, OldLabel, NewLabel).

subst_label(#icode_label{name=Lbl}, LabelOffset) ->
  NewLbl = Lbl + LabelOffset,
  hipe_icode:mk_label(NewLbl).

map_variables(Icode, VarOffset) ->
  NewIcode = [subst_vars(Instr, VarOffset) || Instr <- Icode],
  % io:format(standard_error, "OldIcode: ~p~nNewIcode: ~p~n", [Icode, NewIcode]),
  NewIcode.

subst_vars(Instr, VarOffset) ->
  OldVars = hipe_icode:uses(Instr) ++ hipe_icode:defines(Instr),
  NewVars = [subst_var(Var, VarOffset) || Var <- OldVars],
  Substitutions = lists:zip(OldVars, NewVars),
  hipe_icode:subst(Substitutions, Instr).

subst_var(OldVar, VarOffset) ->
  OldName = hipe_icode:var_name(OldVar),
  NewName = OldName + VarOffset,
  hipe_icode:mk_var(NewName).




post_pass(_NewIcodeMap, []) ->
  ok;
post_pass(NewIcodeMap, [{Pid, MFA}|Pids]) ->
  #{MFA := NewIcode} = NewIcodeMap,
  Pid ! {done, NewIcode},
  post_pass(NewIcodeMap, Pids).

stop() ->
  receive
    {stop, MainPid} ->
      MainPid ! ok
  end.

id(X) -> X.
