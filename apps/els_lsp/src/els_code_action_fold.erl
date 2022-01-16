-module(els_code_action_fold).


-behaviour(els_code_actions).
-export([ command/2
        , precondition/2
        , is_default/0
        ]).

-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

%% init(path()) -> state()

-spec command(wls_utils:path(), range()) -> map().
command(Path, Range) ->
  {{StartLine, StartCol}, {EndLine, EndCol}} = wls_utils:range(Range),
  #{title => <<"Fold">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"Fold">>,
        <<"fold">>,
        [Path, StartLine, StartCol, EndLine, EndCol]
      )
    }.

-spec is_default() -> boolean().
is_default() ->
  true.


-spec precondition(wls_utils:path(), range()) -> boolean().
precondition(Path, Range) ->
  {{Line, Col}, _EndPos} = wls_utils:range(Range),
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(binary_to_list(Path), true),
    case refac_fold_expression:pos_to_fun_clause(AnnAST, {Line, Col}) of
      {ok, _} -> true;
      _ ->false
  end.

