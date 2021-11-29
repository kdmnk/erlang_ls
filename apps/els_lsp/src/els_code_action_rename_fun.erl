%%==============================================================================
%% Code Action: Rename module
%%==============================================================================

-module(els_code_action_rename_fun).

-behaviour(els_code_actions).
-export([ command/2
        , precondition/2
        , is_default/0
        ]).

-include("els_lsp.hrl").


%% init(path()) -> state()

-spec command(wls_utils:path(), range()) -> map().
command(Path, Range) ->
  {StartPos, _} = wls_utils:range(Range),
  {ok, {Mod, Fun, Arity, _OccurPos, _DefPos}} = api_interface:pos_to_fun_name(binary_to_list(Path), StartPos),
  #{title => Fun,
    kind => ?CODE_ACTION_KIND_REFACTOR,
    command =>
      els_command:make_command(
        Mod,
        <<"rename-fun">>,
        [Mod, Fun, Arity, Path]
      )
  }.

-spec is_default() -> boolean().
is_default() ->
  true.


-spec precondition(wls_utils:path(), range()) -> boolean().
precondition(Path, Range) ->
  {StartPos, _} = wls_utils:range(Range),
  case api_interface:pos_to_fun_name(binary_to_list(Path), StartPos) of
    {ok, _} -> true;
    _ -> false
  end.

