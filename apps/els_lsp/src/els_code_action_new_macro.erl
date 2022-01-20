-module(els_code_action_new_macro).


-behaviour(els_code_actions).
-export([ command/2
        , precondition/2
        , is_default/0
        ]).

-include("els_lsp.hrl").

%% init(path()) -> state()

-spec command(wls_utils:path(), range()) -> map().
command(Path, Range) ->
  {{StartLine, StartCol}, {EndLine, EndCol}} = wls_utils:range(Range),
  #{title => <<"New macro">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"New macro">>,
        <<"new-macro">>,
        [Path, StartLine, StartCol, EndLine, EndCol]
      )
    }.

-spec is_default() -> boolean().
is_default() ->
  true.


-spec precondition(wls_utils:path(), range()) -> boolean().
precondition(Path, Range) ->
  {StartPos, EndPos} = wls_utils:range(Range),
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(binary_to_list(Path), true),
  case api_interface:pos_to_expr_or_pat_list(AnnAST, StartPos, EndPos) of
    [] -> false;
    _ExpList ->
      true
  end.

