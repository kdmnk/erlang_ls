-module(els_code_action_new_var).


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
  #{title => <<"Introduce a new variable">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"Introduce a new variable">>,
        <<"new-var">>,
        [Path, StartLine, StartCol, EndLine, EndCol]
      )
    }.

-spec is_default() -> boolean().
is_default() ->
  false.


-spec precondition(wls_utils:path(), range()) -> boolean().
precondition(Path, Range) ->
  {StartPos, EndPos} = wls_utils:range(Range),
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(binary_to_list(Path), true),
  case api_interface:pos_to_expr(AnnAST, StartPos, EndPos) of
    {error, _} -> false;
    _Exp -> true
      % case api_interface:expr_to_fun(AnnAST, Exp) of
      %   {ok, _Fun} ->
      %       true;
      %   {error, _} ->
      %       false
      % end
  end.

