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
  <<"end">> := #{<<"character">> := EndCol, <<"line">> := EndLine}} =
  Range,

  {module, _Module} = code:ensure_loaded(wrangler_syntax),
  {module, _Module2} = code:ensure_loaded(api_interface),
  Path = binary_to_list(els_uri:path(Uri)),
  lists:filter(fun (X) -> X /= #{} end, [ check_for_rename_fun(Path, {StartCol, StartLine, EndCol, EndLine}), check_for_extract_fun(Path, {StartCol, StartLine, EndCol, EndLine}) ]).


check_for_rename_fun(Path, {StartCol, StartLine, _EndCol, _EndLine}) ->
  case api_interface:pos_to_fun_name(Path, {StartLine+1, StartCol}) of
    {ok, {Mod, Fun, Arity, _OccurPos, _DefPos}} ->
      #{title => Fun,
        kind => ?CODE_ACTION_KIND_REFACTOR,
        command =>
          els_command:make_command(
            Mod,
            <<"rename-fun">>,
            [Mod, Fun, Arity, Path]
          )
      };
    {error, _Reason} -> #{}
  end.

check_for_extract_fun(Path, {StartCol, StartLine, EndCol, EndLine}) ->
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(Path, true),
  case api_interface:pos_to_expr_list(AnnAST, {StartLine+1, StartCol}, {EndLine+1, EndCol}) of
  [] -> #{};
  _ExpList ->
    #{title => <<"Extract function">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"Extract function">>,
        <<"extract-fun">>,
        [Path, StartCol, StartLine+1, EndCol+1, EndLine]
      )
    }
  end.


%%------------------------------------------------------------------------------
