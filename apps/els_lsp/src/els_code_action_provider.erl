-module(els_code_action_provider).

-behaviour(els_provider).

-export([handle_request/2, is_enabled/0]).

-include("els_lsp.hrl").

-include_lib("kernel/include/logger.hrl").

-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

-spec is_enabled() -> boolean().
is_enabled() ->
  true.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({document_codeaction, Params}, State) ->
  #{<<"textDocument">> := #{<<"uri">> := Uri},
    <<"range">> := RangeLSP,
    <<"context">> := Context} =
    Params,
  Result = code_actions(Uri, RangeLSP, Context),
  {Result, State}.

%%==============================================================================
%% Internal Functions
%%==============================================================================

%% @doc Result: `(Command | CodeAction)[] | null'
-spec code_actions(uri(), range(), code_action_context()) -> [map()].
code_actions(Uri, Range, _Context) ->
  %% get the position of the text hovered:
  #{<<"start">> := #{<<"character">> := StartCol, <<"line">> := StartLine},
    <<"end">> := #{<<"character">> := _EndCol, <<"line">> := _EndLine}} =
    Range,

  {module, _Module} = code:ensure_loaded(wrangler_syntax),
  {module, _Module2} = code:ensure_loaded(api_interface),
  Path = binary_to_list(els_uri:path(Uri)),
  case api_interface:pos_to_fun_name(Path, {StartLine, StartCol}) of
    {ok, {Mod, Fun, Arity, _OccurPos, _DefPos}} ->
      [#{title => <<"Rename function">>,
        kind => ?CODE_ACTION_KIND_REFACTOR,
        command =>
          els_command:make_command(
            <<"Rename function">>,
            <<"rename-fun">>,
            [Mod, Fun, Arity, Path]
          )
      }];
    {error, Reason} ->
      ?LOG_INFO("Not a function: ~p", [Reason]),
      []
  end.

%%------------------------------------------------------------------------------
