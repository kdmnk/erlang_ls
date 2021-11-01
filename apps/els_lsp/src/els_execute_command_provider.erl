-module(els_execute_command_provider).

-behaviour(els_provider).

-export([ handle_request/2
        , is_enabled/0
        , options/0
        ]).

%%==============================================================================
%% Includes
%%==============================================================================
-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

-spec is_enabled() -> boolean().
is_enabled() -> true.

-spec options() -> map().
options() ->
  #{ commands => [ els_command:with_prefix(<<"rename-fun">>)
                 , els_command:with_prefix(<<"code_action_do_something">>)
                 ] }.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({workspace_executecommand, Params}, State) ->
  #{ <<"command">> := PrefixedCommand } = Params,
  Arguments = maps:get(<<"arguments">>, Params, []),
  Result = execute_command(els_command:without_prefix(PrefixedCommand),
                           Arguments),
  {Result, State}.

%%==============================================================================
%% Internal Functions
%%==============================================================================

-spec execute_command(els_command:command_id(), [any()]) -> [map()].
execute_command(<<"code_action_do_something">>
               , [#{ <<"uri">>   := Uri
                   , <<"from">>  := LineFrom
                   , <<"to">>    := LineTo }]) ->
  els_server:send_notification(<<"window/showMessage">>,
    #{ type => ?MESSAGE_TYPE_INFO,
        message => <<"Doing something">>
      }),
  ?LOG_INFO("code_action_do_something: ~p, ~p, ~p", [Uri, LineFrom, LineTo]),
  [];
execute_command(<<"rename-fun">>, [Mod, Fun, Arity, Path]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming fun... (~p, ~p, ~p, ~p)", [Mod, Fun, Arity, Path]),
  A = api_wrangler:rename_fun(binary_to_atom(Mod), binary_to_atom(Fun), Arity, newfun, [Path]),
  ?LOG_INFO("Rename result: ~p", [A]),
  % case A of
  %   {ok, _FilesChanged} -> els_server:send_notification(<<"window/showMessage">>,
  %     #{ type => ?MESSAGE_TYPE_INFO,
  %       message => <<"Renaming successful">>
  %     });
  %   {error, Reason} -> els_server:send_notification(<<"window/showMessage">>,
  %   #{ type => ?MESSAGE_TYPE_INFO,
  %     message => <<Reason>>
  %   })
  % end,
  [];
execute_command(Command, Arguments) ->
  ?LOG_INFO("Unsupported command: [Command=~p] [Arguments=~p]"
           , [Command, Arguments]),
  [].
