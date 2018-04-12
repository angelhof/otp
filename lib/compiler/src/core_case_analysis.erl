-module(core_case_analysis).

-export([clear_tree_annos/1,
         extract_core_cases/1,
         match_arg_clause/2]).

-include("core_parse.hrl").

%%%
%%% This module is used to extract information for the case clauses of 
%%% core code. This information is used to then efficiently trace the 
%%% times each clause is satisfied during execution.
%%%

-spec extract_core_cases(#c_module{}) -> [{mfa(), [{non_neg_integer(), [fun()]}]}].
extract_core_cases(Tree) ->
    CleanTree = clear_tree_annos(Tree), 
    extract_core_cases0(CleanTree).

extract_core_cases0(#c_module{defs = Functions, name = #c_literal{val = M}}) ->
    %% io:format("Core: ~s~n", [core_pp:format(Core)]),
    FunctionCases = [{{M, F, A}, extract_fun_case(Fun)} || 
			{#c_var{name = {F,A}}, Fun} <- Functions],
    %% io:format("Cases: ~p~n", [FunctionCases]),
    CaseConditions = [{MFA, {Vars, get_case_conditions(Case)}} ||
			    {MFA, {Vars, Case}} <- FunctionCases],
    io:format("Conditions: ~p~n", [CaseConditions]),
    Unions = [{MFA, {Vars, reduce_clauses_conditions(Conditions, Vars)}} ||
		 {MFA, {Vars, Conditions}} <- CaseConditions],
    io:format("Unions: ~p~n", [Unions]),
    FinalConditions = [{MFA, get_final_conditions(Vars, Us)} ||
			  {MFA, {Vars, Us}} <- Unions],
    io:format("Reduced: ~p~n", [FinalConditions]),
    FinalConditions.


%%
%% This function extracts the main case of each function.
%%
%% NOTE:It assumes that a function with multiple definitions
%% always starts with a case.
%%
 
extract_fun_case(#c_fun{vars = Vars, body = Body}) ->
    case Body of
	#c_case{} ->
	    {Vars, Body};
	_ ->
	    {Vars, no_case}
    end.

%%
%% The following functions are used to get constraints that have to 
%% be satisfied so that a clause is indeed satisfied. It gathers
%% those constraints from the patterns and the guard of each clause.
%%
%% NOTE: Not all guards and patterns are taken care of at the moment.
%%

get_case_conditions(no_case) ->
    [];
get_case_conditions(#c_case{arg = Arg, clauses = Clauses}) ->
    [match_arg_clause(Arg, Clause) ++ 
         guard_matches(Clause) || Clause <- Clauses].


-spec match_arg_clause(cerl:cerl(), #c_clause{}) -> [{'match', cerl:cerl(), cerl:cerl()}].
%% WARNING: I still don't care about all guards
match_arg_clause(#c_values{es = Args}, #c_clause{pats = Patterns}) ->
    lists:zipwith(
      fun(X, Y) ->
              {match, X, Y}
      end, Args, Patterns);
match_arg_clause(#c_var{} = Arg, #c_clause{pats = [Pattern]}) ->
    [{match, Arg, Pattern}];
match_arg_clause(_Arg, _Clause) ->
    [].

guard_matches(#c_clause{guard = Guard}) ->
    Constraints = guard_to_constraint_tree(Guard),
    FlatConstraints = flatten_constrain_tree(Constraints),
    %% io:format("Guard: ~p~n", [FlatConstraints]),
    FlatConstraints.

%%
%% The following functions perform a 'unification' type algorithm.
%% Their purpose is to reduce the constraints that we have to check
%% by grouping variables and literals in unions.
%%
%% NOTE: The unification algorithm that I have used is inefficient
%%

reduce_clauses_conditions(Conditions, Vars) ->
    lists:zip(lists:seq(1, length(Conditions)),
	      [reduce_clause_condition1(C, Vars) || C <- Conditions]).

%% group2(List) -> 
%%     lists:foldr(
%%       fun({V,K}, M) -> 
%% 	      maps:update_with(K, fun(V0) -> [V|V0] end, [V], M) 
%%       end, #{}, List).

%%
%% Alternative unify algorithm
%%

reduce_clause_condition1(Conditions, Vars) ->
    ValSet = 
	lists:foldl(
	  fun({match, V1, V2}, Acc) ->
		  sets:add_element(
		    V1, sets:add_element(V2, Acc))
	  end, sets:new(), Conditions),
    Vals = sets:to_list(ValSet),
    InitUnions = maps:from_list(
		   lists:zip(Vals, Vals)),
    Unions = lists:foldl(fun(Match, Unions) ->
				 unify1(Match, Unions, Vars)
			 end, InitUnions, Conditions),
    Unifications = group21(maps:to_list(Unions)),
    {_, UnificationList} = lists:unzip(maps:to_list(Unifications)),
    UnificationList.

%% WARNING: Inefficient unification algorithm
unify1({match, V1, V2}, Unions, Vars) ->
    #{V1 := U1} = Unions,
    #{V2 := U2} = Unions,
    case cerl:type(U1) =:= cerl:type(U2) 
	andalso not cerl:is_leaf(U1) of
	true ->
	    Children = lists:zip(
			 cerl:data_es(U1),
			 cerl:data_es(U1)),
	    lists:foldl(
	      fun({Ua, Ub}, Uns) ->
		      unify1({match, Ua, Ub}, Uns, Vars)
	      end, Unions, Children);
	false ->
	    case cerl:type(U1) =:= var 
		orelse cerl:type(U2) =:= var of
		true ->
		    union(U1, U2, Unions, Vars);
		false ->
		    io:format("V1: ~p, V2: ~p~n", [V1, V2]),
		    throw({error, {unable_to_match, U1, U2}})
	    end
    end.

union(U1, U2, Unions, Vars) ->	
    {Big, Small} =
	case cerl:is_leaf(U1) andalso cerl:is_leaf(U2) of
	    false ->
		case not cerl:is_leaf(U1) of
		    true  -> {U1, U2};
		    false -> {U2, U1}
		end;
	    true ->
		case lists:member(U2, Vars) of
		    true  -> {U2, U1};
		    false -> {U1, U2}
		end
	end,
    maps:map(
      fun(_, U) when Small =:= U ->
	      Big;
	 (_, U) ->
	      U
      end, Unions).

group21(List) -> 
    lists:foldr(
      fun({V,K}, M) -> 
	      maps:update_with(K, fun(V0) -> [V|V0] end, [V], M) 
      end, #{}, List).


%%
%% Old BAD Unify algorithm
%%

%% reduce_clause_condition(Conditions) ->
%%     ValSet = 
%% 	lists:foldl(
%% 	  fun({match, V1, V2}, Acc) ->
%% 		  sets:add_element(
%% 		    V1, sets:add_element(V2, Acc))
%% 	  end, sets:new(), Conditions),
%%     Vals = sets:to_list(ValSet),
%%     InitUnions = maps:from_list(
%% 		   lists:zip(Vals, lists:seq(1, length(Vals)))),
%%     Unions = lists:foldl(fun unify/2, InitUnions, Conditions),
%%     Unifications = group2(maps:to_list(Unions)),
%%     {_, UnificationList} = lists:unzip(maps:to_list(Unifications)),
%%     UnificationList.

%% %% WARNING: Inefficient unification algorithm
%% unify({match, V1, V2}, Unions) ->
%%     #{V1 := U1} = Unions,
%%     #{V2 := U2} = Unions,
%%     maps:map(
%%       fun(Key, U) when U2 =:= U ->
%% 	      U1;
%% 	 (_, U) ->
%% 	      U
%%       end, Unions).



%%
%% This function transforms the unions from the previous step 
%% to boolean functions that check whether some arguments
%% satisfy the constraints imposed by the unions.
%%
%% NOTE: At the moment I only handle a set of '=:=' constraints  
%% combined with 'and'.
%%

get_final_conditions(Vars, CaseUnions) ->
    [{ClauseId, get_final_clause_conditions(Vars, Unions)} ||
	{ClauseId, Unions} <- CaseUnions].

%% WARNING: At the moment I only handle '=:=' and 'and'
get_final_clause_conditions(Vars, Unions) ->
    VarUnions = [{V, find_union(V, Unions)} || V <- Vars],
    %% Matches = [{V, filter_union(Vars, U)} || {V, U} <- VarUnions],
    Matches = VarUnions,
    lists:append([make_conditions(Vars, VarMatches) || VarMatches <- Matches]).
    

find_union(Var, Unions) ->
    util:find(
      fun(U) ->
	      lists:member(Var, U)
      end, [], Unions).

%% filter_union(Vars, Union) ->
%%     [Element || Element <- Union, 
%% 		cerl:is_literal(Element)
%% 		    orelse lists:member(Element, Vars)].


%% find_literal(Union) ->
%%     util:find(
%%       fun(Node) ->
%% 	      cerl:is_literal(Node)
%%       end, no_literal, Union).

make_conditions(Vars, {Var, Matches}) ->
    lists:append([make_condition(Vars, Var, Match) || Match <- Matches]).


%%
%% TODO: Write this clearly
%% I make the conditions by passing a function that takes all variables
%% and returns the needed variable or the needed part of it.
%% In essence when handling complex data types this function is refined
%% until it returns the correct variable part.
%% 
%% If the variable in question does not follow the data type structure
%% then its function crashes so I hve to handle this by catching errors 
%% when checking the conditions.
%%

make_condition(Vars, Var, Match) ->
    VarIndex = util:index(Var, Vars),
    VarFun = 
	fun(Variables) ->
		lists:nth(VarIndex, Variables)
	end,
    make_condition_rec(VarFun, Vars, Match).

make_condition_rec(VarFun, _Vars, #c_literal{val = Val}) ->
    [fun(Variables) ->
	    VarFun(Variables) =:= Val
    end];
make_condition_rec(VarFun, Vars, #c_var{} = MatchVar) ->
    case lists:member(MatchVar, Vars) of
	true ->
	    MatchVarIndex = util:index(MatchVar, Vars),
	    [fun(Variables) ->
		    VarFun(Variables) =:= lists:nth(MatchVarIndex, Variables)
	    end];
	false ->
	    [fun(_) ->
		    true
	    end]
    end;
make_condition_rec(VarFun, Vars, #c_cons{hd = H, tl = T}) ->
    HVarFun = 
	fun(Variables) ->
	        hd(VarFun(Variables))
	end,
    TVarFun =
	fun(Variables) ->
	        tl(VarFun(Variables))
	end,
    make_condition_rec(HVarFun, Vars, H) ++
	make_condition_rec(TVarFun, Vars, T);
make_condition_rec(VarFun, Vars, #c_tuple{es = Elements}) ->
    ElFuns = 
	lists:map(
	  fun(Index) ->
		  fun(Variables) ->
			  element(Index, VarFun(Variables))
		  end
	  end, lists:seq(1, length(Elements))),
    lists:append(lists:zipwith(
		  fun(Fun, El) ->
			  make_condition_rec(Fun, Vars, El)
		  end, ElFuns, Elements));
%% TODO: To implement this
make_condition_rec(_VarFun, _Vars, #c_binary{}) ->
    [fun(_) -> true end].	    

%%
%% This functions transforms a cerl guard to a constraint tree
%%

guard_to_constraint_tree(Guard) ->
    ConstraintTree = evaluate_guard(#{}, Guard),
    simplify_constraint_tree(ConstraintTree).

%%
%% This functions is used to evaluate a guard expression into an
%% equivalent tree of calls to bif functions
%%

%% WARNING: I have not implemented it for all possible cerl nodes
evaluate_guard(Map, Var = #c_var{}) ->
    case maps:get(Var, Map, none) of
	none ->
	    Var;
	Replacement ->
	    evaluate_guard(Map, Replacement)
    end;
evaluate_guard(_Map, Literal = #c_literal{}) ->
    Literal;
evaluate_guard(Map, #c_call{module = M, name = F, args = Args}) ->
    cerl:c_call(M, F, [evaluate_guard(Map, Arg) || Arg <- Args]);
evaluate_guard(Map, #c_let{vars = [Var], arg = Arg, body = Body}) ->
    evaluate_guard(Map#{Var => Arg}, Body);
%% WARNING: I am not sure if I handle try correctly
evaluate_guard(Map, #c_try{arg = Arg}) ->
    evaluate_guard(Map, Arg).


%%
%% This function simplifies the tree so that it is is easier 
%% to flatten the constraints
%%

%% WARNING: I don't make sure that the module is always erlang 
simplify_constraint_tree(#c_call{name = #c_literal{val = Op}, args = Args}) -> 
    {Op, [simplify_constraint_tree(Arg) || Arg <- Args]};
simplify_constraint_tree(Literal = #c_literal{}) -> 
    Literal;
simplify_constraint_tree(Var = #c_var{}) -> 
    Var.

%%
%% This functions flattens an 'and' constraint tree to a list of constraints
%% 

%% WARNING: I only handle 'and' trees of equalities
flatten_constrain_tree({'and', [Arg1, Arg2]}) ->
    flatten_constrain_tree(Arg1) ++ flatten_constrain_tree(Arg2);
flatten_constrain_tree({'=:=', [Arg1, Arg2]}) ->
    [{match, Arg1, Arg2}];
flatten_constrain_tree(_) ->
    [].


%%
%% This is just used to remove all annotations from a cerl tree for debugging purposes
%%

-spec clear_tree_annos(cerl:cerl()) -> cerl:cerl().
clear_tree_annos(Tree) ->
    postorder(
      fun(Node) ->
	      cerl:set_ann(Node, [])
      end, Tree).

postorder(F, Tree) ->
    F(case cerl:subtrees(Tree) of
          [] -> Tree;
          List -> cerl:update_tree(
		    Tree,
		    [[postorder(F, Subtree)
		      || Subtree <- Group]
		     || Group <- List])
      end).

