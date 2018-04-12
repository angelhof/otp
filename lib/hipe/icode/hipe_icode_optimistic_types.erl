-module(hipe_icode_optimistic_types).

-export([cfg/2, linear/2]).

-export([check_opt_fun_info/1]).

-include("../main/hipe.hrl").
-include("hipe_icode.hrl").
-include("hipe_icode_primops.hrl").
-include("hipe_icode_type.hrl").
-include("../flow/cfg.hrl").



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
%% A pass that adds typetests with the optimistic types acquired
%% from the dynamic type server at the beginning of the cfg so that
%% further optimizations can happen when those types are indeed true.
%%-------------------------------------------------------------------

-spec linear(icode(), map()) -> icode().
linear(Icode, Types) ->
  Cfg = hipe_icode_cfg:linear_to_cfg(Icode),
  NewCfg = cfg(Cfg, Types),
  hipe_icode_cfg:cfg_to_linear(NewCfg).

-spec cfg(cfg(), map()) -> cfg().
cfg(Cfg, Types) ->
  MFA = hipe_icode_cfg:function(Cfg),
  add_optimistic_typetests(Cfg, MFA, Types).

add_optimistic_typetests(Cfg, MFA, TypesMap) ->
  %% Split every bb after every function call 
  Cfg1 = separate_calls_into_bbs(Cfg),

  % %% Create a copy of the cfg bbs
  {CopiedCfg, LabelMappings} = copy_cfg(Cfg1),

  % %% Find the starting label of the original and copied bbs
  StartLbl = hipe_icode_cfg:start_label(Cfg1),
  {_, StartLblOpt} = lists:keyfind(StartLbl, 1, LabelMappings),

  %% Create typetests for each argument to combine the cfgs
  CombinedCfg = combine_copied_cfg(MFA, CopiedCfg, StartLbl, StartLblOpt, TypesMap),

  %% Create a typetest after the return of each non-branch function call
  FinalCfg = add_typetests(CombinedCfg, LabelMappings, TypesMap),

  % io:format("Final: ~p~n", [FinalCfg]),
  FinalCfg.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% This function adds a typetest after every function return to 
%% check if the returned value is typed as expected
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_typetests(CombinedCfg, LabelMappings, TypesMap) ->
  OptimisticLabels = [Opt || {_, Opt} <- LabelMappings],
  FinalCfg = lists:foldr(
    fun(Lbl, Cfg) ->
      add_typetest_fun_return(Lbl, Cfg, LabelMappings, TypesMap)
    end, CombinedCfg, OptimisticLabels),
  FinalCfg.


%% WARNING: This function is implemented in a very bad way, performance wise while also clarity wise
%% TODO: Prettify and optimize
add_typetest_fun_return(OptLabel, Cfg, LabelMappings, TypesMap) ->
  BB = hipe_icode_cfg:bb(Cfg, OptLabel),
  Code = hipe_bb:code(BB),
  case final_call(Code) of
    none ->
      Cfg;
    {Call, continuation} ->
      case function_to_typetest_with_continuation(Call) of
        true ->
          typetest_fun_with_continuation(OptLabel, LabelMappings, Cfg, TypesMap);
        false -> Cfg
      end;
    {Call, no_continuation} ->
      case function_to_typetest_without_continuation(Call) of
        true ->
          typetest_fun_without_continuation(OptLabel, LabelMappings, Cfg, TypesMap);
        false -> Cfg
      end
  end.

final_call(Code) ->
  case last(Code) of
    [FinalCall = #icode_call{}] ->
      {FinalCall, continuation};
    _ ->
      case last_2(Code) of
        [Ins1 = #icode_call{}, #icode_goto{}] ->
          {Ins1, no_continuation};
        _ ->
          none
      end
  end.

%% TODO: Prettify this mess of a function
typetest_fun_with_continuation(OptLabel, LabelMappings, Cfg, TypesMap) ->
  BB = hipe_icode_cfg:bb(Cfg, OptLabel),
  Code = hipe_bb:code(BB),
  [Ins = #icode_call{}] = last(Code),
  %% Sanity assertion
  true = function_to_typetest_with_continuation(Ins),
  MFA = hipe_icode:call_fun(Ins),
  [RetVal] = hipe_icode:call_dstlist(Ins),
  case function_worth_typetesting(MFA, TypesMap) of
    {true, TypetestTree} ->
      OptContLabel = hipe_icode:call_continuation(Ins),
      {StdContLabel, _} = lists:keyfind(OptContLabel, 2, LabelMappings),

      %% Add the typetests in the typetest list

      TypetestList = traverse_test_tree(TypetestTree, hipe_icode:mk_move(RetVal, RetVal), ?TYPETEST_TREE_DEPTH),
      % TypetestList = traverse_test_tree(TypetestTree, hipe_icode:mk_move(RetVal, RetVal), 0),

      % io:format("With cont MFA: ~p~nTypetest List: ~p~n", [MFA, TypetestList]),
      {Cfg1, TypetestLabel, _} = lists:foldr(fun add_typetests_fun/2, {Cfg, OptContLabel, StdContLabel}, TypetestList),

      %% Update the continuation Label
      NewCode = init(Code) ++ [hipe_icode:call_set_continuation(Ins, TypetestLabel)],
      NewBB = hipe_bb:code_update(BB, NewCode),
      hipe_icode_cfg:bb_add(Cfg1, OptLabel, NewBB);
    false -> Cfg
  end.

typetest_fun_without_continuation(OptLabel, LabelMappings, Cfg, TypesMap) ->
  BB = hipe_icode_cfg:bb(Cfg, OptLabel),
  Code = hipe_bb:code(BB),
  [Ins1 = #icode_call{}, Ins2 = #icode_goto{}] = last_2(Code),
  true = function_to_typetest_without_continuation(Ins1),
  MFA = hipe_icode:call_fun(Ins1),
  [RetVal] = hipe_icode:call_dstlist(Ins1),
  case function_worth_typetesting(MFA, TypesMap) of
    {true, TypetestTree} ->
      OptGotoLabel = hipe_icode:goto_label(Ins2),
      {StdGotoLabel, _} = lists:keyfind(OptGotoLabel, 2, LabelMappings),

      %% Add the typetests in the typetest list

      TypetestList = traverse_test_tree(TypetestTree, hipe_icode:mk_move(RetVal, RetVal), ?TYPETEST_TREE_DEPTH),
      % TypetestList = traverse_test_tree(TypetestTree, hipe_icode:mk_move(RetVal, RetVal), 0),

      % io:format("Without cont MFA: ~p~nTypetest List: ~p~n", [MFA, TypetestList]),
      {Cfg1, TypetestLabel, _} = lists:foldr(fun add_typetests_fun/2, {Cfg, OptGotoLabel, StdGotoLabel}, TypetestList),

      %% Update the continuation Label
      NewCode = init_2(Code) ++ [Ins1, hipe_icode:mk_goto(TypetestLabel)],
      NewBB = hipe_bb:code_update(BB, NewCode),
      hipe_icode_cfg:bb_add(Cfg1, OptLabel, NewBB);
    false -> Cfg
  end.

last_2(Xs) ->
  case lists:reverse(Xs) of
    [X1,X2|_] ->
      [X2,X1];
    _ ->
      []
  end.

init_2(Xs) ->
  case lists:reverse(Xs) of
    [_,_|Rest] ->
      lists:reverse(Rest);
    _ ->
      []
  end.

last(Xs) ->
  case lists:reverse(Xs) of
    [X|_] ->
      [X];
    _ ->
      []
  end.

init(Xs) ->
  case lists:reverse(Xs) of
    [_|Rest] ->
      lists:reverse(Rest);
    _ ->
      []
  end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% This function breaks the bbs after each function that
%% doesn't have a continuation label
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

separate_calls_into_bbs(Cfg) ->
  %% Make cfg linear and get code
  Linear = hipe_icode_cfg:cfg_to_linear(Cfg),
  Code = hipe_icode:icode_code(Linear),

  NewCodeRev = lists:foldl(fun separate_calls_into_bbs_fun/2, [], Code),
  NewCode = lists:reverse(NewCodeRev),
  % io:format("New code: ~p~n", [NewCode]),

  %% Update the Cfg
  NewLinear = hipe_icode:icode_code_update(Linear, NewCode),
  hipe_icode_cfg:linear_to_cfg(NewLinear).

separate_calls_into_bbs_fun(Ins = #icode_call{}, Code) ->
  case function_to_typetest_without_continuation(Ins) of
    true ->
      LabelIns = hipe_icode:mk_new_label(),
      NewLabel = hipe_icode:label_name(LabelIns),
      GotoIns = hipe_icode:mk_goto(NewLabel),
      [LabelIns, GotoIns, Ins|Code];
    false ->
      [Ins|Code]
  end;
separate_calls_into_bbs_fun(Ins, Code) ->
  [Ins|Code].

function_to_typetest_without_continuation(Ins) ->
  not hipe_icode:is_branch(Ins)
    andalso function_to_typetest(Ins).

function_to_typetest_with_continuation(Ins) ->
  hipe_icode:is_branch(Ins)
    andalso function_to_typetest(Ins).

function_to_typetest(Ins = #icode_call{type=CallType})
  when CallType =:= local orelse CallType =:= remote ->
  hipe_icode:call_dstlist(Ins) =/= [];
function_to_typetest(_Ins) ->
  false.

function_worth_typetesting(MFA, TypesMap) ->
  case ?WITH_DYN_SERVER of
    true ->
      %% Old one based on type server
      case check_opt_return_info(MFA) of
        none ->
          false;
        RetType ->
          case erl_types:t_test_tree_from_erl_type(RetType) of
            any ->
              false; %% No typetest
            TypetestTree ->
              {true, TypetestTree}
          end
      end;
    false ->
      case maps:get(MFA, TypesMap, none) of
        none ->
          false;
        {_, RetType} ->
          case erl_types:t_test_tree_from_erl_type(RetType) of
            any ->
              false; %% No typetest
            TypetestTree ->
              {true, TypetestTree}
          end
      end
  end.

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% This function combines the optimistic and the original cfg
%% using a series of typetests for the function's arguments
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

combine_copied_cfg(MFA, CopiedCfg, StartLbl, StartLblOpt, TypesMap) ->
  %% The optimistic arguments types, zipped with the arguments
  CfgParams = hipe_icode_cfg:params(CopiedCfg),

  ArgTypes =
    case ?WITH_DYN_SERVER of
      true ->
        %% Old one based on runtime_type_server
        case check_opt_call_info(MFA) of
          none ->
            [erl_types:t_any() || _ <- lists:seq(1,length(CfgParams))];
          %% The guard here makes sure that argument typetests are not going
          %% to be produced in case the params are more (e.g. when a tuple has been untupled)
          %% than the recorded argument types
          ArgTypesTemp when length(ArgTypesTemp) =:= length(CfgParams)->
            ArgTypesTemp;
          _ ->
            [erl_types:t_any() || _ <- lists:seq(1,length(CfgParams))]
        end;
      false ->
        %% New one
        case maps:get(MFA, TypesMap, none) of
          none ->
            [erl_types:t_any() || _ <- lists:seq(1,length(CfgParams))];
          %% The guard here makes sure that argument typetests are not going
          %% to be produced in case the params are more (e.g. when a tuple has been untupled)
          %% than the recorded argument types
          {ArgTypesTemp, _} when length(ArgTypesTemp) =:= length(CfgParams)->
            ArgTypesTemp;
          _ ->
            [erl_types:t_any() || _ <- lists:seq(1,length(CfgParams))]
        end
    end,
  %% New version that might add more than one typetest for each argument
  ArgTypetestTrees = lists:zip([erl_types:t_test_tree_from_erl_type(Type) || Type <- ArgTypes], [hipe_icode:mk_move(X, X) || X <- CfgParams]),
  %% Comment one line if you dont want typetests in arguments
  ArgTypetestLists = [traverse_test_tree(Tree, Param, ?TYPETEST_TREE_DEPTH) || {Tree, Param} <- ArgTypetestTrees],
  % ArgTypetestLists = [traverse_test_tree(Tree, Param, 0) || {Tree, Param} <- ArgTypetestTrees],

  {UpdatedCfg, NewStartLabel, _} = lists:foldr(fun add_typetests_fun/2, {CopiedCfg, StartLblOpt, StartLbl}, lists:flatten(ArgTypetestLists)),
  %% Check if any typetest has been really added
  case NewStartLabel of
    StartLblOpt ->
      %% WARNING: This is very important, in order to combine both cfgs in case no typetest has been added
      InitialGoto = fake_goto(StartLblOpt, StartLbl),
      NewStartingBB = hipe_bb:mk_bb([InitialGoto]),
      NewStartingLabel = hipe_icode:label_name(hipe_icode:mk_new_label()),
      SimpleUpdatedCfg = hipe_icode_cfg:bb_add(CopiedCfg, NewStartingLabel, NewStartingBB),
      hipe_icode_cfg:start_label_update(SimpleUpdatedCfg, NewStartingLabel);
    _ ->
     hipe_icode_cfg:start_label_update(UpdatedCfg, NewStartLabel)
  end.


%% This function is used as a foldr function on the typetest list
add_typetests_fun({Typetest, Instruction}, {Cfg, TrueLabel, FalseLabel}) ->
  BB = case Typetest of
    any ->
      FakeGoto = fake_goto(TrueLabel, FalseLabel),
      hipe_bb:mk_bb([Instruction, FakeGoto]);
    _ ->
      Arg = get_icode_element(Instruction),
      TypetestIns = hipe_icode:mk_type([Arg], Typetest, TrueLabel, FalseLabel, ?TYPE_TEST_PROB),
      hipe_bb:mk_bb([Instruction, TypetestIns])
  end,
  NewStartLabel = hipe_icode:label_name(hipe_icode:mk_new_label()),

  Cfg1 = hipe_icode_cfg:bb_add(Cfg, NewStartLabel, BB),
  %% This shouldn't be here
  % Cfg2 = hipe_icode_cfg:start_label_update(Cfg1, NewStartLabel),
  {Cfg1, NewStartLabel, FalseLabel}.

fake_goto(TrueLabel, FalseLabel) ->
  hipe_icode:mk_type([hipe_icode:mk_const(true)], atom, TrueLabel, FalseLabel).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% This function traverses a typetest tree (for one value and its
%% sub-values) in dfs order and returns a typetest list
%% which also contains the essential instructions in order to
%% extract the sub-values before applying the typetests
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% TODO:
%% 1. Find better smaller names

traverse_test_tree(_Node, _IcodeIns, 0) ->
  [];
traverse_test_tree({leaf, Typetest}, IcodeIns, _N) ->
  [{Typetest, IcodeIns}];
traverse_test_tree({node, Typetest, Children}, IcodeCall, N) ->
  ChildrenExtraction = lists:zip(element_extract_primop(Typetest, length(Children)), Children),
  IcodeElement = get_icode_element(IcodeCall),
  ChildrenTestTrees = [traverse_test_tree(Child, element_extract_instruction(Ins, IcodeElement), N-1)
                        || {Ins, Child} <- ChildrenExtraction],
  [{Typetest, IcodeCall}| lists:flatten(ChildrenTestTrees)].

%% TODO: Check if we also need fp_var or reg or other commands except from cariable
element_extract_instruction(Primop, Argument) ->
  DstVar = hipe_icode:mk_new_var(),
  hipe_icode:mk_primop([DstVar], Primop, [Argument]).

%% Returns a command to extract each child value from the father value
element_extract_primop(tuple, LenChildren) ->
  [#unsafe_element{index=Index} || Index <- lists:seq(1,LenChildren)];
element_extract_primop({tuple, LenChildren}, LenChildren) ->
  [#unsafe_element{index=Index} || Index <- lists:seq(1,LenChildren)].

%% TODO: Maybe the icode element is not always a call or a var (reg, fvar???)
get_icode_element(Ins = #icode_call{}) ->
  [Dst] = hipe_icode:call_dstlist(Ins),
  Dst;
get_icode_element(Ins = #icode_move{}) ->
  hipe_icode:move_dst(Ins);
get_icode_element(Var = #icode_variable{}) ->
  Var.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Create a copy of the cfg by also redirecting jmps and phis
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

copy_cfg(Cfg) ->
  %% Get the current Cfg Labels
  Labels = hipe_icode_cfg:labels(Cfg),

  %% Create the old to new label mappings
  LabelMappings = lists:foldl(
    fun(OldLbl, Mappings) ->
      NewLbl = hipe_icode:label_name(hipe_icode:mk_new_label()),
      [{OldLbl, NewLbl}|Mappings]
    end, [], Labels),

  %% Create a copy of all the bbs based on the label mappings
  {copy_bbs(Labels, LabelMappings, Cfg), LabelMappings}.

copy_bbs([OldLbl|Rest], LabelMappings, Cfg) ->
  BB = hipe_icode_cfg:bb(Cfg, OldLbl),
  Code = hipe_bb:code(BB),
  NewCode = make_copies(Code, LabelMappings),
  % NewBB = hipe_bb:code_update(BB, NewCode),
  NewBB = hipe_bb:mk_bb(NewCode),
  {_, NewLbl} = lists:keyfind(OldLbl, 1, LabelMappings),
  NewCfg = hipe_icode_cfg:bb_add(Cfg, NewLbl, NewBB),
  copy_bbs(Rest, LabelMappings, NewCfg);
copy_bbs([], _LabelMappings, Cfg) ->
  Cfg.

make_copies(Is, LabelMappings) ->
  lists:flatten([copy_insn(I, LabelMappings) || I <- Is]).

%% While copying instructions we have to also redirect all jumps and phis to correspond to the copied bbs

copy_insn(I, LabelMappings) ->
  Succs = hipe_icode:successors(I),
  RedirectedJmpsI = redirect_jmps(Succs, LabelMappings, I),
  case hipe_icode:is_phi(I) of
    false ->
      RedirectedJmpsI;
    true ->
      Labels = [ Lbl || {Lbl, _} <- hipe_icode:phi_arglist(I)],
      redirect_phis(Labels, LabelMappings, I)
  end.

redirect_phis([], _LabelMappings, I) ->
  I;
redirect_phis([Lbl|Rest], LabelMappings, I) ->
  {_, NewLbl} = lists:keyfind(Lbl, 1, LabelMappings),
  NewI = hipe_icode:phi_redirect_pred(I, Lbl, NewLbl),
  redirect_phis(Rest, LabelMappings, NewI).


redirect_jmps([], _LabelMappings, I) ->
  I;
redirect_jmps([Jmp|Rest], LabelMappings, I) ->
  {_, NewLbl} = lists:keyfind(Jmp, 1, LabelMappings),
  NewI = hipe_icode:redirect_jmp(I, Jmp, NewLbl),
  redirect_jmps(Rest, LabelMappings, NewI).



-spec check_opt_fun_info(mfa()) -> 
        'none' | {[erl_types:type()], erl_types:type()}.
check_opt_fun_info(MFA) ->
  case runtime_server_running() of 
    false -> none;
    true ->
      case hipe_runtime_type_server:get_mfa(runtime_type_server, MFA) of
        not_found -> none;
        {ok, {ArgTypes, RetType}} -> {ArgTypes, RetType}
      end
  end.

-spec check_opt_return_info(mfa()) -> 
        'none' | erl_types:type().
check_opt_return_info(MFA) ->
  case runtime_server_running() of 
    false -> none;
    true ->
      case hipe_runtime_type_server:get_mfa(runtime_type_server, MFA) of
        not_found -> none;
        {ok, {_, RetType}} -> RetType
      end
  end.

-spec check_opt_call_info(mfa()) -> 
        'none' | [erl_types:type()].
check_opt_call_info(MFA) ->
  case runtime_server_running() of 
    false -> none;
    true ->
      case hipe_runtime_type_server:get_mfa(runtime_type_server, MFA) of
        not_found -> none;
        {ok, {ArgTypes, _}} -> ArgTypes
      end
  end.

-spec runtime_server_running() -> boolean().
runtime_server_running() ->
  lists:member(runtime_type_server, erlang:registered()).

