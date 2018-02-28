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
                %% io:format("Fun: ~p~n", [Fun]),
                reorder_cases(Fun, ReorderList)
        end,
    {FName, NewFun}.

reorder_cases(Fun, ReorderList) ->
    postorder(
      fun(Node) ->
	      reorder_case(Node, ReorderList) 
      end, Fun).

reorder_case(#c_case{id=Id, clauses=Cs} = Case, ReorderList) ->
    CId = cerl:concrete(Id),
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
    

%% negate_guard(


postorder(F, Tree) ->
    F(case cerl:subtrees(Tree) of
          [] -> Tree;
          List -> cerl:update_tree(
		    Tree,
		    [[postorder(F, Subtree)
		      || Subtree <- Group]
		     || Group <- List])
      end).

