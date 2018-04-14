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

-define(MINIMUM_CALLS_TO_INLINE, 100).

%%-------------------------------------------------------------------
%% A pass that inlines functions based on call data that has been
%% gathered during execution
%%
%% Some information on the algorithm used
%% 1. It chooses which function to inline based on how many times 
%%    it has been called.
%% 2. It doesn't allow the size of the module to grow beyond 
%%    a soft limit. Soft limit means that it might grow a bit more 
%%    than that.
%% 3. At the moment it doesn't inline a function to itself in case
%%    of recursive functions.
%%-------------------------------------------------------------------


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

%% Filters the call data and only keeps data for the functions that exist in the IcodeMap
filter_data(Data, IcodeMap) ->
    NewData = 
        maps:filter(
          fun(MFA, _) ->
                  maps:is_key(MFA, IcodeMap)
          end, Data),
    case maps:size(NewData) =:= maps:size(Data) of
        true -> ok;
        false -> 
            io:format(standard_error,
                      "HiPE Warning~n" ++
                      "  - Profile Driven Inlining data contained mfas that do not belong in this module~n", 
                      [])
    end,
    NewData.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Priority Queue Implementation
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% This priority queue implementation is naive and 
%% finds the maximum call by searching through all the calls everytime.

%% It is a implemented with a map so that updates 
%% when knowing the key are fast.

%% However finding the maximum is slow.

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

maximum_size(InitialSize) ->
  SmallAverage = 4000.0, % erl_types is 34703 on my metric
  %% This practically means that smaller modules can grow more and
  %% bigger modules can grow less (10% - 310%)
  %% Small
  round((min(SmallAverage / InitialSize , 1.0) + 1.1) * InitialSize).
  %% Med
  %% round((min(SmallAverage / InitialSize , 3.0) + 1.1) * InitialSize).
  %% Large
  %% round((min(SmallAverage / InitialSize , 4.5) + 1.5) * InitialSize).

total_calls(IcodeMap, CallMap) ->
  MfaMap = maps:map(fun(_MFA,_) -> 0 end, IcodeMap),
  maps:fold(fun sum_calls/3, MfaMap, CallMap).

sum_calls({_Caller, Callee}, Times, TotalCalls) ->
  maps:update_with(Callee, fun(X) -> X + Times end, TotalCalls).

compute_icode_sizes(IcodeMap) ->
  FullIcodeMap = maps:map(
    fun(_, Icode) ->
      Code = hipe_icode:icode_code(Icode),
      {Icode, length(Code)}
    end, IcodeMap),
  InitialSize = maps:fold(
    fun(_, {_, MfaSize}, Size) ->
      MfaSize + Size
    end, 0, FullIcodeMap),
  % io:format(standard_error, "Size: ~p~n", [InitialSize]),
  {FullIcodeMap, InitialSize}.

%% TODO: Implement the naive algorithm here
process(Data, IcodeMap) ->
  %% Create a priority queue with all the call info
  CallMap = prepare_call_pq(Data),
  % io:format(standard_error, "Initial Call Map: ~p~n", [CallMap]),
  NewIcodeMap = pre_loop(IcodeMap, CallMap),
  NewIcodeMap.



pre_loop(IcodeMap, CallMap) ->
    %% This doesn't allow calls to the same function to be inlined
    %% CurrentInlinesList = [{MFA, MFA} || {MFA, _Icode} <- maps:to_list(IcodeMap)],
    CurrentInlinesList = [],
    CurrentInlines = sets:from_list(CurrentInlinesList),

    TotalCalls = total_calls(IcodeMap, CallMap),

    {FullIcodeMap, InitialModuleSize} = compute_icode_sizes(IcodeMap),
    MaxModuleSize = maximum_size(InitialModuleSize),
    %% io:format(standard_error, "InitSize: ~p~nMaxModuleSize: ~p~n", [InitialModuleSize, MaxModuleSize]),
    NewFullIcodeMap = loop(FullIcodeMap, TotalCalls, CurrentInlines,
                           CallMap, MaxModuleSize),

    maps:map(fun(_,{Icode,_Size}) -> Icode end, NewFullIcodeMap).


%% TODO: Fix wrong spec
-spec loop(#{mfa() := {icode(), integer()}},    % A map from mfas to cfgs
           #{mfa() := integer()},               % A map from mfas to number of times called
           sets:set({mfa(), mfa()}),            % A map with the already done inlining for each function. This exists to prevent loops
           [{mfa(), {mfa(), integer()}}],       % A list with all calls and their numbers
           integer()) ->                        % The maximum module size
              #{mfa() := icode()}.              % A map with the new cfgs

loop(FullIcodeMap, TotalCalls, CurrentInlines, CallMap, MaxSize) ->
  case pop_call_from_pq(CallMap) of
    none ->
      FullIcodeMap;
    {PriorityCall, Rest} ->
      % io:format(standard_error, "Next: ~p~nRest: ~p~n", [Max, Rest]),
      case check_inline_call(PriorityCall, FullIcodeMap, CurrentInlines, MaxSize) of
        {ok, NewIcodeMap} ->
          {{Caller, Callee}, _NumCalls} = PriorityCall,
          NewCurrentInlines =
            sets:add_element({Caller, Callee}, CurrentInlines),
          NewCallMap = update_call_pq(PriorityCall, Rest, TotalCalls),
          loop(NewIcodeMap, TotalCalls, NewCurrentInlines, NewCallMap, MaxSize);
        false ->
          loop(FullIcodeMap, TotalCalls, CurrentInlines, Rest, MaxSize)
      end
    end.


check_inline_call(Call, FullIcodeMap, CurrInl, MaxSize) ->
  Conditions =
    [has_been_inlined_already(Call, CurrInl),
     happens_enough_times(Call),
     wont_outgrow_max_size(Call, FullIcodeMap, MaxSize)],
  case lists:all(fun id/1, Conditions) of
    true ->
      % io:format(standard_error, "Cool GROW~n", []),
      inline_call(Call, FullIcodeMap);
    false ->
      false
  end.

has_been_inlined_already({{Caller, Callee}, _NumberCalls}, CurrentInlines) ->
  not sets:is_element({Caller, Callee}, CurrentInlines).

happens_enough_times({_, NumberCalls}) ->
  NumberCalls > ?MINIMUM_CALLS_TO_INLINE.

%% IMPORTANT: This only estimates if its going to outgrow, that's why its a soft limit
%% The estimate is expects only one call site to be inlined
wont_outgrow_max_size({{_Caller, Callee}, _}, FullIcodeMap, MaxSize) ->
  #{Callee := {_,CalleeSize}} = FullIcodeMap,
  NewCurrSize = maps:fold(
    fun(_, {_, MfaSize}, Size) ->
      MfaSize + Size
    end, CalleeSize, FullIcodeMap),
  %% This just exists for debug purpose in order to check if it stops inline sometimes
  % case NewCurrSize < MaxSize of
  %   false -> io:format(standard_error, "NO OUTGROW~n", []);
  %   _ -> ok
  % end,
  NewCurrSize < MaxSize.

inline_call({{Caller, Callee}, _NumberCalls}, FullIcodeMap) ->
  %% io:format("Caller: ~p~nCallee: ~p~n", [Caller, Callee]),
  #{Caller := {CallerIcode, CallerSize}} = FullIcodeMap,
  #{Callee := {CalleeIcode, CalleeSize}} = FullIcodeMap,
  {NewCallerIcode, NumInlines} = make_inlines(CallerIcode, Callee, CalleeIcode),
  NewIcodeMap = FullIcodeMap#{Caller :=
        {NewCallerIcode, CallerSize + NumInlines * CalleeSize}},
  {ok, NewIcodeMap}.



%% TODO: Handle call continuations and fail labels
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
  {NewCallerIcodeCode, _FinalVarOffset, _FinalLabelOffset, NumInlines} =
        lists:foldr(fun(Ins, Acc) ->
            check_make_inline(Ins, CalleeIcode, Acc) end,
            {[], VarOffset, LabelOffset, 0}, CallerIcodeCode),

  NewCallerIcode = hipe_icode:icode_code_update(CallerIcode, NewCallerIcodeCode),


  {NewCallerIcode, NumInlines}.

%%
%% Conditions
%%

is_local(#icode_call{type = local}) -> true;
is_local(#icode_enter{type = local}) -> true;
is_local(_) -> false.

%% TODO: At some point also inline calls that have successors
no_successors(Ins = #icode_call{}) ->
  hipe_icode:successors(Ins) =:= [];
no_successors(_) -> true.

is_callee(Ins = #icode_call{}, Callee) ->
  hipe_icode:call_fun(Ins) =:= Callee;
is_callee(Ins = #icode_enter{}, Callee) ->
  hipe_icode:enter_fun(Ins) =:= Callee;
is_callee(_,_) ->
  false.

check_make_inline(Ins, CalleeIcode, {Code, VarOffset, LabelOffset, NumInl}) ->
  Callee = hipe_icode:icode_fun(CalleeIcode),
  Conds =
    [is_local(Ins),
     no_successors(Ins),
     is_callee(Ins, Callee)],
  case lists:all(fun id/1, Conds) of
    true ->
      case Ins of
        #icode_call{} ->
          {InlinedCallee, NewVarOffset, NewLabelOffset} =
            make_inline_call(Ins, CalleeIcode, VarOffset, LabelOffset),
          {InlinedCallee ++ Code, NewVarOffset, NewLabelOffset, NumInl + 1};
        #icode_enter{} ->
          {InlinedCallee, NewVarOffset, NewLabelOffset} =
            make_inline_enter(Ins, CalleeIcode, VarOffset, LabelOffset),
          {InlinedCallee ++ Code, NewVarOffset, NewLabelOffset, NumInl + 1}
      end;
    false ->
      {[Ins|Code], VarOffset, LabelOffset, NumInl}
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

subst_var(OldVar, VarOffset)->
  case hipe_icode:is_var(OldVar) of
      true-> 
          OldName = hipe_icode:var_name(OldVar),
          NewName = OldName + VarOffset,
          hipe_icode:mk_var(NewName);
      false ->
          case hipe_icode:is_fvar(OldVar) of
              true ->
                  OldName = hipe_icode:fvar_name(OldVar),
                  NewName = OldName + VarOffset,
                  hipe_icode:mk_fvar(NewName);
              false ->
                  OldName = hipe_icode:reg_name(OldVar),
                  NewName = OldName + VarOffset,
                  hipe_icode:mk_reg(NewName)
          end
  end.



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
