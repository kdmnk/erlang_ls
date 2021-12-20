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
                 , els_command:with_prefix(<<"extract-fun">>)
                 , els_command:with_prefix(<<"generalise-fun">>)
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
  {ok, [{OldName, _NewName, Text}]} = Changes,

  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => #{
      documentChanges => [
        #{
          textDocument => #{
            uri => els_uri:uri(list_to_binary(OldName)),
            version => null
          },
          edits => [#{
            range => #{
              start => #{ line => 0, character => 0 },
              'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0 }
            },
            newText => els_utils:to_binary(Text)
          }]
        }
      ]
    }
  },
  els_server:send_request(Method, Params),
  [];
execute_command(<<"rename-mod">>, [Mod, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming mod... (~p, ~p, ~p)", [Mod, Path, NewMod]),
  Changes = api_wrangler:rename_mod(binary_to_atom(Mod), binary_to_atom(NewMod), [binary_to_list(Path)]),
  {ok, [{OldName, NewName, Text}]} = Changes,

  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => #{
      documentChanges => [
         #{
           kind => <<"rename">>,
           oldUri => els_uri:uri(list_to_binary(OldName)),
           newUri => els_uri:uri(list_to_binary(NewName))
         },
        #{
          textDocument => #{
            uri => els_uri:uri(list_to_binary(NewName)),
            version => null
          },
          edits => [#{
            range => #{
              start => #{ line => 0, character => 0 },
              'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0 }
            },
            newText => els_utils:to_binary(Text)
          }]
        }
      ]
    }
  },
  els_server:send_request(Method, Params),
  [];
execute_command(<<"extract-fun">>, [Path, StartLine, StartCol, EndLine, EndCol, NewName]) ->
  Changes = refac_new_fun:fun_extraction(Path, {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(NewName), command, 4),
  {ok, [{OldPath, _NewPath, Text}]} = Changes,

  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => #{
      changes => #{
        els_uri:uri(list_to_binary(OldPath)) => [#{
          range => #{
            start => #{ line => 0, character => 0 },
            'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0 }
          },
          newText => els_utils:to_binary(Text)
        }]
      }
    }
  },
  els_server:send_request(Method, Params),
  [];

execute_command(<<"generalise-fun">>, [Path, StartLine, StartCol, EndLine, EndCol, ParName]) ->
  Changes = refac_gen:generalise(Path, {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(ParName), [Path], command, 8),
  {ok, [{OldPath, _NewPath, Text}]} = Changes,

  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => #{
      changes => #{
        els_uri:uri(list_to_binary(OldPath)) => [#{
          range => #{
            start => #{ line => 0, character => 0 },
            'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0 }
          },
          newText => els_utils:to_binary(Text)
        }]
      }
    }
  },
  els_server:send_request(Method, Params),
  [];

execute_command(Command, Arguments) ->
  ?LOG_INFO("Unsupported command: [Command=~p] [Arguments=~p]"
           , [Command, Arguments]),
  [].
