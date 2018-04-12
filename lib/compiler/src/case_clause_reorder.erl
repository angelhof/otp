-module(case_clause_reorder).

-export([module/2]).

-include("core_parse.hrl").

-spec module(#c_module{}, [_]) -> {'ok', #c_module{}}.
module(Code, Options) ->
    NewCode =
        case lists:keyfind(case_reorder, 1, Options) of
            {case_reorder, ReorderMap} ->
                reorder_module_cases(Code, ReorderMap);
            false ->
                Code
        end,
    %% io:format("Code: ~p~nOptions: ~p~n", [NewCode, Options]),
    {ok, NewCode}.

reorder_module_cases(#c_module{name=M, defs=Defs} = Code, ReorderMap) ->
    NewDefs = [reorder_function_cases(Def, M, ReorderMap) || Def <- Defs],
    Code#c_module{defs=NewDefs}.

reorder_function_cases({FName, Fun}, MLit, ReorderMap) ->
    M = cerl:concrete(MLit),
    #c_var{name={F,A}} = FName,
    NewFun = 
        case maps:get({M,F,A}, ReorderMap, undefined) of
            undefined ->
                Fun;
            ReorderList ->
                %% io:format("MFA: ~p~n", [{M, F, A}]),
                io:format("Fun: ~p~n", [core_case_analysis:clear_tree_annos(Fun)]),
                reorder_cases(Fun, ReorderList)
        end,
    {FName, NewFun}.

reorder_cases(Fun, ReorderList) ->
    postorder(
      fun(Node) ->
	      reorder_case(Node, ReorderList) 
      end, Fun).

reorder_case(#c_case{id=Id, arg=Arg, clauses=Cs} = Case, ReorderList) ->
    CId = cerl:concrete(Id),
    _Matches = clauses_matches(Arg, Cs),
    case lists:keyfind(CId, 1, ReorderList) of
        {CId, ClauseList} ->
            NewClauses = reorder_clauses(Cs, CId, ClauseList),
            Case#c_case{clauses=NewClauses};
        false ->
            Case
    end;
reorder_case(Node, _ReorderList) ->
    Node.

reorder_clauses(Cs, _Id, CsList) ->
    CsOrder = maps:from_list(
                lists:zip(CsList, lists:seq(1, length(CsList)))),
    NewCs = lists:sort(
              fun(#c_clause{id=Id1}, #c_clause{id=Id2}) ->
                      CId1 = maps:get(cerl:concrete(Id1), CsOrder),
                      CId2 = maps:get(cerl:concrete(Id2), CsOrder),
                      CId1 < CId2
              end, Cs),
    NewCs.
    

clauses_matches(Arg, Clauses) ->
    Matches = [core_case_analysis:match_arg_clause(Arg,C) || C <- Clauses], 
    io:format("Matches: ~p~n", [Matches]),

    {Lets, TempVars} = lists:foldl(fun match_codegen/2, {cerl:abstract(true), []}, Matches),
    io:format("Lets: ~p~nTempVars: ~p~n", [Lets, TempVars]).
    
match_codegen({match, _V1, _V2}, {_Lets, _TempVars}) ->
    undefined.
    %% NewTemp = make_new_var(TempVars),
    %% TODO: Create a let with an equality in the arg and the previous lets in the body

%% %% WARNING: VERY BAD WAY OF GENERATING VARIABLES
%% %% -- VERY INEFFICIENT
%% %% -- IT MIGHT CREATE NAME CLASHES
%% make_new_var(TempVars) ->
    

postorder(F, Tree) ->
    F(case cerl:subtrees(Tree) of
          [] -> Tree;
          List -> cerl:update_tree(
		    Tree,
		    [[postorder(F, Subtree)
		      || Subtree <- Group]
		     || Group <- List])
      end).

