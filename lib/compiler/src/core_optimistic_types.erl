-module(core_optimistic_types).

-export([module/2,
         optimistic_fun_name/1,
         standard_fun_name/1]).

-include("core_parse.hrl").

-define(TYPE_TEST_PROB, 0.85).
-define(TYPETEST_TREE_DEPTH, 1).

%% TODO:
%% 1. I probably have to inform profile driven inlining about the function name changes.
%%    Maybe a good place to do that would be the module attributes.
%%
%% Notes:
%% 1. BE CAREFUL WITH C_VARs. In cerl.erl it states that the number names cannot 
%%    (and should not) be used everywhere
%% 2. Maybe change the annotations for the standard and optimistic functions. 
%%    (Put something like compiler generated)
%%



-spec module(#c_module{}, [_]) -> {'ok', #c_module{}}.
module(Code, Options) ->
    OptTypes = get_optimistic_types_option(Options),
    %% io:format("Types: ~p~n", [OptTypes]),
    NewCode = main(Code, OptTypes),
    %% io:format("New Code:~n~p~n", [core_case_analysis:clear_tree_annos(NewCode)]),
    {ok, NewCode}.

%% TODO: Add a test that checks whether the types are for this module only
get_optimistic_types_option(Options) ->
    case lists:keyfind(optimistic_types, 1, Options) of
        {optimistic_types, OptTypes} ->
            OptTypes;
        _ ->
            #{}
    end.

main(#c_module{name = #c_literal{val = M}, defs = Funs} = Code, OptTypes) ->
    {NewFuns, OptFAs} = 
        lists:foldr(
          fun(Fun, {AccFuns, AccFAs}) ->
                  {NewFuns, NewFAs} = check_create_optimistic_functions(M, Fun, OptTypes),
                  {NewFuns ++ AccFuns, NewFAs ++ AccFAs}
          end, {[], []}, Funs),
    FinalFuns = inline_typetest_headers(OptFAs, NewFuns),
    Code#c_module{defs = FinalFuns}.

%% TODO: Check all the conditions that I have in optimistic types in Hipe and put them all here
check_create_optimistic_functions(M, {Name, Fun}, OptTypes) ->
    #c_var{name = {F,A}} = Name,
    case maps:find({M,F,A}, OptTypes) of
        {ok, Types} ->
            {create_optimistic_functions({Name, Fun}, Types), [{F,A}]};
        error ->
            {[{Name, Fun}], []}
    end.
    

%% TODO: Create the typetests from the types.
create_optimistic_functions({Name, Fun}, Type) ->
    %% io:format("Fun: ~p~nType: ~p~n", [Name, Type]),
    StdFun = {standard_fun_var(Name), Fun},

    OptFun = {optimistic_fun_var(Name), Fun},

    HeaderFun = create_header_fun(Name, Fun, Type),
    [{Name, HeaderFun}, OptFun, StdFun].
    

%% TODO: Find a better (unique) way to create optimistic and standard function names
optimistic_fun_var(#c_var{name = {F,A}}) ->
    cerl:c_var({optimistic_fun_name(F), A}).

standard_fun_var(#c_var{name = {F,A}}) ->
    cerl:c_var({standard_fun_name(F), A}).

-spec optimistic_fun_name(atom()) -> atom().
optimistic_fun_name(Name) ->
    list_to_atom(atom_to_list(Name) ++ "$opt").

-spec standard_fun_name(atom()) -> atom().
standard_fun_name(Name) ->
    list_to_atom(atom_to_list(Name) ++ "$std").


create_header_fun(Name, #c_fun{vars = Args} = Fun, {ArgTypes, _RetType}) ->
    %% io:format("Fun: ~p~nTypes: ~p~n", [core_case_analysis:clear_tree_annos(Fun), ArgTypes]),
    VarRange = var_range(Fun),
    %% io:format("Var Range: ~p~n", [VarRange]),
    put(var_range, VarRange),
    %% io:format("PD: ~p~n", [get()]),
    
    TypetestTrees = [erl_types:t_test_tree_from_erl_type(Type) || Type <- ArgTypes],
    ArgTypetestTrees = lists:zip(TypetestTrees, Args),
    ArgTypetestList = 
        lists:flatten([bfs_test_tree(Tree, Arg, Arg, ?TYPETEST_TREE_DEPTH) 
                       || {Tree, Arg} <- ArgTypetestTrees]),
    %% io:format("Typetest Trees: ~p~n", [ArgTypetestTrees]),
    %% io:format("Typetest List: ~p~n", [ArgTypetestList]),
    TestsCode = make_tests(ArgTypetestList, Name, Args),
    %% io:format("Tests Code: ~p~n", [TestsCode]),
    Fun#c_fun{body = TestsCode}.

%% TODO: Create a primop call to the typetest for each argument in the tree
%%       Start from the call to the optimistic function and the call to the standard function and 
%%       wrap them with all the typetests in the typetest tree. So make a tree fold in a way. 

%% WARNING: Name would be a value and not an atom so generating the optimistic one wont be so easy
bfs_test_tree(_Node, _Dst, _Exp, 0) ->
    [];
bfs_test_tree({leaf, Typetest}, Dst, Exp, _N) ->
    [{Dst, Exp, Typetest}];
bfs_test_tree({node, Typetest, Children}, Dst, Exp, N) ->
    ChildrenExtraction = 
        lists:zip(element_extract_expression(Typetest, length(Children), Dst), Children),
    ChildrenBFS = 
        [bfs_test_tree(Child, ChildDst, ChildExp, N-1) 
         || {{ChildDst, ChildExp}, Child} <- ChildrenExtraction],
    [{Dst, Exp, Typetest} | lists:flatten(ChildrenBFS)].
    
element_extract_expression(tuple, LenChildren, Dst) ->
    ErlangAtom = cerl:abstract(erlang),
    ElementAtom = cer:abstract(element),
    [{new_var(), cerl:c_call(ErlangAtom, ElementAtom, [cerl:abstract(X), Dst])} 
     || X <- lists:seq(1, LenChildren)];
element_extract_expression({tuple, LenChildren}, LenChildren, Dst) ->
    ErlangAtom = cerl:abstract(erlang),
    ElementAtom = cerl:abstract(element),
    [{new_var(), cerl:c_call(ErlangAtom, ElementAtom, [cerl:abstract(X), Dst])} 
     || X <- lists:seq(1, LenChildren)].


make_tests(ArgTypetestList, FunName, Args) ->
    TrueBody = cerl:c_apply(optimistic_fun_var(FunName), Args),
    FalseBody = cerl:c_apply(standard_fun_var(FunName), Args),
    make_tests0(ArgTypetestList, TrueBody, FalseBody). 

%% TODO: At some point I have to put better clause and case ids
make_tests0([], TrueBody, _FalseBody) ->
    TrueBody;
make_tests0([{Dst, Exp, Typetest}|Rest], TrueBody, FalseBody) ->
    TypetestFun = make_typetest(Typetest, Dst),
    cerl:c_let([Dst], Exp, 
          cerl:c_case(
            cerl:abstract(0),
            TypetestFun, 
            [cerl:c_clause(cerl:abstract(0), [cerl:abstract(true)], 
                           cerl:abstract(true), make_tests0(Rest, TrueBody, FalseBody)),
             cerl:c_clause(cerl:abstract(0), [cerl:abstract(false)], 
                           cerl:abstract(true), FalseBody)]
           )).


var_range(#c_fun{vars = Args, body = Body}) ->
    ArgsMax = 
        case Args of
            [] -> 0;
            _ -> lists:max([var_id(Arg) || Arg <- Args])
        end,
    max(ArgsMax, var_range0(Body)).

var_range0(Tree) ->
    Curr = var_id(Tree),
    case lists:flatten(cerl:subtrees(Tree)) of
        [] ->
            Curr;
        Children ->
            ChildrenMax = lists:max([var_range0(C) || C <- Children]),
            max(Curr, ChildrenMax)
    end.
            
var_id(#c_var{name = N}) when is_integer(N) -> N;
var_id(_) -> 0.

new_var() ->
    VarRange = get(var_range),
    NewVarId = VarRange + 1,
    put(var_range, NewVarId),
    cerl:c_var(NewVarId).

%% WARNING: Be careful of the function clause error as they do in cerl_inline
inline_typetest_headers(FAs, Funs) ->
    HeaderFunsList = 
        [{Name, Fun} || {#c_var{name=Name},Fun} <- Funs, lists:member(Name, FAs)],
    HeaderFuns = maps:from_list(HeaderFunsList),
    %% io:format("Headers: ~p~n", [maps:keys(HeaderFuns)]),
    [inline_typetest_headers_in_fun(Fun, HeaderFuns) || Fun <- Funs].

inline_typetest_headers_in_fun({FunName, Fun}, HeaderFuns) ->
    VarRange = var_range(Fun),
    put(var_range, VarRange),
    
    NewBody = inline_typetest_headers_in_fun0(cerl:fun_body(Fun), fun new_var/0, HeaderFuns),
    %% io:format("NewFun: ~p~n~p~n", [FunName, core_case_analysis:clear_tree_annos(NewBody)]),
    {FunName, Fun#c_fun{body=NewBody}}.

inline_typetest_headers_in_fun0(FunBody, VarGen, Headers) ->
    postorder(
      fun(Node) ->
              check_inline_cerl(Node, VarGen, Headers)
      end, FunBody).

check_inline_cerl(Node, VarGen, Bodies) ->
    case cerl:type(Node) of
        apply ->
            ApplyFA = cerl:var_name(cerl:apply_op(Node)),
            case maps:find(ApplyFA, Bodies) of
                {ok, Body} ->
                    inline_cerl(Node, VarGen, Body);
                error ->
                    Node
            end;
        _ ->
            Node
    end.

inline_cerl(Apply, VarGen, Callee) ->
    CalleeVars = reduce_tree(fun get_var/1, Callee),
    VarMap = 
        lists:foldl(
          fun(VarName, Map) ->
                  case maps:is_key(VarName, Map) of
                      true -> Map;
                      false -> Map#{VarName => VarGen()}
                  end
          end, #{}, CalleeVars),
    %% io:format("Apply: ~p~n", [core_case_analysis:clear_tree_annos(Apply)]),
    %% io:format("Body: ~p~n", [core_case_analysis:clear_tree_annos(Callee)]),
    %% io:format("Vars: ~p~nVarMap: ~p~n", [CalleeVars, VarMap]),
    NewCallee = postorder(fun(N) -> update_var(N, VarMap) end, Callee),
    %% io:format("NewBody:~n~p~n", [core_case_analysis:clear_tree_annos(NewCallee)]),
    CalleeArgs = cerl:fun_vars(NewCallee),
    CalleeBody = cerl:fun_body(NewCallee),
    ApplyArgs = cerl:apply_args(Apply),
    cerl:c_let(CalleeArgs, 
               cerl:c_values(ApplyArgs),
               CalleeBody).


%% This function only keeps normal variables (and not function names)
get_var(Node) ->
    case cerl:type(Node) of
        var ->
            case cerl:var_name(Node) of
                {_,_} ->
                    [];
                Name ->
                    [Name]
            end;
        _ ->
            []
    end.

update_var(Node, VarMap) ->
    case cerl:type(Node) of
        var ->
            case cerl:var_name(Node) of
                {_,_} ->
                    Node;
                Name ->
                    maps:get(Name, VarMap)
            end;
        _ ->
            Node
    end.



%% WARNING: Here I have to handle all the possible typetests that erl_types:t_test_from_erl_type/1
%%          can return.
%% TODO:
%% 1. Make the CORRECT typetest for cons
%% 2. Make the CORRECT typetest for tuple, Arity
make_typetest({tuple, _Arity}, Dst) ->
    ErlangAtom = cerl:abstract(erlang),
    cerl:c_call(ErlangAtom, cerl:abstract(is_tuple), [Dst]);
make_typetest(Typetest, Dst) ->
    {TFun, TArgs} = make_typetest_fun_simple(Typetest, Dst),
    ErlangAtom = cerl:abstract(erlang),
    cerl:c_call(ErlangAtom, TFun, TArgs).

make_typetest_fun_simple({atom, Atom}, Dst) ->
    {cerl:abstract('=:='), [cerl:abstract(Atom), Dst]};
make_typetest_fun_simple(atom, Dst) ->
    {cerl:abstract(is_atom), [Dst]};
make_typetest_fun_simple(boolean, Dst) ->
    {cerl:abstract(is_boolean), [Dst]};
make_typetest_fun_simple(binary, Dst) ->
    {cerl:abstract(is_binary), [Dst]};
make_typetest_fun_simple(bitstring, Dst) ->
    {cerl:abstract(is_bitstring), [Dst]};
make_typetest_fun_simple(cons, Dst) ->
    {cerl:abstract(is_list), [Dst]};
make_typetest_fun_simple(float, Dst) ->
    {cerl:abstract(is_float), [Dst]};
make_typetest_fun_simple(function, Dst) ->
    {cerl:abstract(is_function), [Dst]};
make_typetest_fun_simple({integer, Integer}, Dst) ->
    {cerl:abstract('=:='), [cerl:abstract(Integer), Dst]};
make_typetest_fun_simple(integer, Dst) ->
    {cerl:abstract(is_integer), [Dst]};
make_typetest_fun_simple(map, Dst) ->
    {cerl:abstract(is_map), [Dst]};
make_typetest_fun_simple(nil, Dst) ->
    {cerl:abstract('=:='), [cerl:abstract([]), Dst]};
make_typetest_fun_simple(number, Dst) ->
    {cerl:abstract(is_number), [Dst]};
make_typetest_fun_simple(pid, Dst) ->
    {cerl:abstract(is_pid), [Dst]};
make_typetest_fun_simple(port, Dst) ->
    {cerl:abstract(is_port), [Dst]};
make_typetest_fun_simple(reference, Dst) ->
    {cerl:abstract(is_reference), [Dst]};
make_typetest_fun_simple(map, Dst) ->
    {cerl:abstract(is_map), [Dst]};
make_typetest_fun_simple(any, _Dst) ->
    True = cerl:abstract(true),
    {cerl:abstract('=:='), [True, True]}.

%% Maybe quadratic
reduce_tree(F, Tree) ->
    F(Tree) ++ lists:flatten([reduce_tree(F, C) || C <- lists:flatten(cerl:subtrees(Tree))]).

postorder(F, Tree) ->
    F(case cerl:subtrees(Tree) of
          [] -> Tree;
          List -> cerl:update_tree(
		    Tree,
		    [[postorder(F, Subtree)
		      || Subtree <- Group]
		     || Group <- List])
      end).

