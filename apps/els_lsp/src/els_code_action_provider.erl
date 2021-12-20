-module(els_code_action_provider).

-behaviour(els_provider).

-export([handle_request/2, is_enabled/0, extract_fun/2, rename_fun/2, generalise/2]).

-include("els_lsp.hrl").

-include_lib("kernel/include/logger.hrl").

-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

is_enabled() -> is_enabled(true).

-spec is_enabled(any()) ->  boolean().
is_enabled(N) ->
  N.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({document_codeaction, Params}, State) ->
  #{<<"textDocument">> := #{<<"uri">> := Uri},
    <<"range">> := RangeLSP,
    <<"context">> := Context} =
    Params,
  Result = code_actions(Uri, RangeLSP, Context),
  {Result, State}.

refactorings() -> [rename_fun, extract_fun, generalise].

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
  WRange = {{StartLine+1, StartCol+1}, {EndLine+1, EndCol+1}},
  lists:filter(fun (X) -> X /= #{} end, [ apply(els_code_action_provider, F, [Uri, WRange]) || F <- refactorings() ]).


rename_fun(Uri, {{StartLine, StartCol}, _End}) ->
  Path = binary_to_list(els_uri:path(Uri)),
  case api_interface:pos_to_fun_name(Path, {StartLine, StartCol}) of
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

extract_fun(Uri, {{StartLine, StartCol}, {EndLine, EndCol}}) ->
  Path = binary_to_list(els_uri:path(Uri)),
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(Path, true),
  case api_interface:pos_to_expr_list(AnnAST, {StartLine, StartCol}, {EndLine, EndCol}) of
  [] -> #{};
  _ExpList ->
    #{title => <<"Extract function">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"Extract function">>,
        <<"extract-fun">>,
        [Path, StartLine, StartCol, EndLine, EndCol]
      )
    }
  end.

generalise(Uri, {{StartLine, StartCol}, {EndLine, EndCol}}) ->
  Path = binary_to_list(els_uri:path(Uri)),
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(Path, true),
  case api_interface:pos_to_expr(AnnAST, {StartLine, StartCol}, {EndLine, EndCol}) of
    {ok, Exp} ->
      case api_interface:expr_to_fun(AnnAST, Exp) of
        {ok, _Fun} ->
          #{title => <<"Generalise function">>,
            kind => ?CODE_ACTION_KIND_REFACTOR,
            command => 
              els_command:make_command(
                <<"Generalise function">>,
                <<"generalise-fun">>,
                [Path, StartLine, StartCol, EndLine, EndCol]
              )
             };
        {error, _} -> 
          ?LOG_INFO("Not in a function"),
          #{}
      end;
    {error, _} -> 
      ?LOG_INFO("Not an expression"),
      #{}
  end.
