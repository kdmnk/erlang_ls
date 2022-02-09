-module(els_code_action_extract_fun).


-behaviour(els_code_actions).
-export([ command/3
        , precondition/2
        , is_default/0
        ]).

-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

%% init(path()) -> state()

-spec command(uri(), range(), any()) -> map().
command(Uri, Range, _State) ->
  #{title => <<"Extract function">>,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        <<"Extract function">>,
        <<"extract-fun">>,
        [#{ <<"uri">>   => Uri
          , <<"range">> => Range}]
      )
    }.

-spec is_default() -> boolean().
is_default() ->
  true.


-spec precondition(uri(), range()) -> boolean().
precondition(Uri, Range) ->
  Path = binary_to_list(els_uri:path(Uri)),
  % convert the range representation
  {StartPos, EndPos} = wls_utils:range(Range),
  % create an annotated syntax tree
  {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(Path, true),
  % check if the highlighted range is list of expressions
  case api_interface:pos_to_expr_list(AnnAST, StartPos, EndPos) of
    []       -> false;
    _ExpList -> true
  end.

