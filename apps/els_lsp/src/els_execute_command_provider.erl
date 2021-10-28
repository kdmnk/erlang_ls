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
  #{ commands => [ els_command:with_prefix(<<"replace-lines">>)
                 , els_command:with_prefix(<<"rename-fun">>)
                 , els_command:with_prefix(<<"ct-run-test">>)
                 , els_command:with_prefix(<<"show-behaviour-usages">>)
                 , els_command:with_prefix(<<"suggest-spec">>)
                 , els_command:with_prefix(<<"function-references">>)
                 , els_command:with_prefix(<<"code_action_do_something">>)
                 ] }.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({workspace_executecommand, Params}, State) ->
  #{ <<"command">> := PrefixedCommand } = Params,
  Arguments = maps:get(<<"arguments">>, Params, []),
  Result = execute_command( els_command:without_prefix(PrefixedCommand)
                          , Arguments),
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
execute_command(<<"rename-fun">>, [Module, Function, Arity, Path]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming fun... (~p, ~p, ~p, ~p)", [Module, Function, Arity, Path]),
  %api_wrangler:rename_fun(binary_to_atom(Module), binary_to_atom(Function), Arity, newfun, [binary_to_list(Path)]),
  %spawn(api_wrangler, rename_fun, [binary_to_atom(Module), binary_to_atom(Function), Arity, newfun, [binary_to_list(Path)]]),
  %?LOG_INFO("Renamed fun..."),
  els_server:send_notification(<<"window/showMessage">>,
                               #{ type => ?MESSAGE_TYPE_INFO,
                                  message => <<"Hello">>
                                }),
  [];
execute_command(<<"function-references">>, [_Params]) ->
  [];
execute_command(<<"show-behaviour-usages">>, [_Params]) ->
  [];
execute_command(<<"suggest-spec">>, []) ->
  [];
execute_command(<<"suggest-spec">>, [#{ <<"uri">> := Uri
                                      , <<"line">> := Line
                                      , <<"spec">> := Spec
                                      }]) ->
  Method = <<"workspace/applyEdit">>,
  {ok, #{text := Text}} = els_utils:lookup_document(Uri),
  LineText = els_text:line(Text, Line - 1),
  NewText = <<Spec/binary, "\n", LineText/binary, "\n">>,
  Params =
    #{ edit =>
         els_text_edit:edit_replace_text(Uri, NewText, Line - 1, Line)
     },
  els_server:send_request(Method, Params),
  [];
execute_command(Command, Arguments) ->
  ?LOG_INFO("Unsupported command: [Command=~p] [Arguments=~p]"
           , [Command, Arguments]),
  [].
