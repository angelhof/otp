-module(hipe_runtime_type_server).

%% Default gen_server functions
-export([init/1, handle_call/3, handle_cast/2, handle_info/2,
         terminate/2, code_change/3]).

%% API Functions
-export([ init/0
        , add_mfa/2
        , remove_mfa/2
        , get_mfa/2
        , get_all/1
        , terminate/1
        ]).

-define(debug, true).

-ifdef(debug).
-define(LOG(F, X), 
  io:format(standard_error, 
    "{~p,~p}: " ++ F, 
    [?MODULE,?LINE] ++ X)).
-else.
-define(LOG(F, X), true).
-endif.


%%---------------------------------------------------------------------
%%
%%  API Functions
%%
%%---------------------------------------------------------------------

-spec init() -> pid().
init() ->
  {ok, Pid} = gen_server:start_link(?MODULE, #{}, []),
  Pid.

-spec add_mfa(pid(), {mfa(), any()}) -> ok.
add_mfa(Pid, {MFA, Signature}) ->
  gen_server:call(Pid, {add_mfa, {MFA, Signature}}).

-spec remove_mfa(pid(), mfa()) -> ok.
remove_mfa(Pid, MFA) ->
  gen_server:call(Pid, {remove_mfa, MFA}).

-spec get_mfa(pid(), mfa()) -> {ok, any()}.
get_mfa(Pid, MFA) ->
  gen_server:call(Pid, {get_mfa, MFA}).

-spec get_all(pid()) -> {ok, list()}.
get_all(Pid) ->
  gen_server:call(Pid, get_all).

-spec terminate(pid()) -> ok.
terminate(Pid) ->
	gen_server:call(Pid, terminate).

%%---------------------------------------------------------------------
%%
%%  Server-side
%%
%%---------------------------------------------------------------------

-spec init(#{}) -> {ok, #{}}.
init(InitState) ->
  {ok, InitState}.

-spec handle_call(any(), pid(), map()) -> {reply, ok, map()}.
handle_call({add_mfa, {MFA, Signature}}, _From, S) ->
  {reply, ok, S#{MFA => Signature}};

handle_call({get_mfa, MFA}, _From, S) ->
  case maps:find(MFA, S) of
  	{ok, Signature} ->
  		{reply, {ok, Signature}, S};
  	error ->
  		{reply, not_found, S}
  end;

handle_call(get_all, _From, S) ->
  {reply, {ok, maps:to_list(S)}, S};

handle_call({remove_mfa, MFA}, _From, S) ->
  {reply, ok, maps:remove(MFA, S)};

%%---------------------------------------------------------------------
%%-- terminate
%%---------------------------------------------------------------------

handle_call(terminate, _From, State) ->
  {stop, normal, ok, State}.

%%---------------------------------------------------------------------
%%-- cast, info, terminate & code change
%%---------------------------------------------------------------------

-spec handle_cast(any(), map()) -> {noreply, map()}.
handle_cast(Msg, State) ->
  io:format(standard_error, "Unexpected cast: ~p~n",[Msg]),
  {noreply, State}.

-spec handle_info(any(), map()) -> {noreply, map()}.
handle_info(Msg, State) ->
  io:format(standard_error, "Unexpected message: ~p~n",[Msg]),
  {noreply, State}.

-spec terminate(normal, map()) -> ok.
terminate(normal, _State) ->
  %% Maybe dump state somewhere
  ok.

-spec code_change(any(), map(), any()) -> {ok, map()}.
code_change(_OldVsn, State, _Extra) ->
  %% No change planned. The function is there for the behaviour,
  %% but will not be used. Only a version on the next
  {ok, State}.


%% --------------------------------------------------------------------
%%
%%  AUX Functions
%%
%% --------------------------------------------------------------------
