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
                 , els_command:with_prefix(<<"rename-mod">>)
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

execute_command(<<"rename-fun">>, [Mod, Fun, Arity, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming fun... (~p, ~p, ~p, ~p, ~p)", [Mod, Fun, Arity, Path, NewMod]),
  Changes = api_wrangler:rename_fun(binary_to_atom(Mod), binary_to_atom(Fun), Arity, binary_to_atom(NewMod), [Path]),
  ?LOG_INFO("Rename result: ~p", [Changes]),
  {ok, [{OldName, NewName, Text}]} = Changes,

  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => #{
      documentChanges => [
        #{
          kind => <<"rename">>,
          oldUri => els_uri:uri(list_to_binary(OldName)),
          newUri => els_uri:uri(list_to_binary("/Users/domi/Documents/GitHub/vscode/erlang_ls/apps/els_lsp/src/els_execute_command_provider2.erl"))
        },
        #{
          textDocument => #{ uri => els_uri:uri(list_to_binary("/Users/domi/Documents/GitHub/vscode/erlang_ls/apps/els_lsp/src/els_execute_command_provider2.erl")) },
          edits => #{
            range => #{
              start => #{ line => 0, character => 0 },
              'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0 }
            },
            newText => els_utils:to_binary(Text)
          }
        }
      ]
    }
  },
  els_server:send_request(Method, Params),
  [];
execute_command(<<"rename-mod">>, [Mod, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming mod... (~p, ~p, ~p)", [Mod, Path, NewMod]),
  A = api_wrangler:rename_fun(binary_to_atom(Mod), binary_to_atom(NewMod), [Path]),
  ?LOG_INFO("Rename result: ~p", [A]),
  [];
execute_command(Command, Arguments) ->
  ?LOG_INFO("Unsupported command: [Command=~p] [Arguments=~p]"
           , [Command, Arguments]),
  [].
