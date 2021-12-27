-module(els_execute_command_provider).

-behaviour(els_provider).

-export([ handle_request/2
        , is_enabled/0
        , options/0
        ]).

%%TODO change search paths to project path
%%TODO fix TabWith


%%==============================================================================
%% Includes
%%==============================================================================
-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

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
                 , els_command:with_prefix(<<"comment-out-spec">>)
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
  Changes = refac_rename_fun:rename_fun_by_name(binary_to_atom(Mod), {binary_to_atom(Fun), Arity}, binary_to_atom(NewMod), [binary_to_list(Path)], wls, 4),
  case Changes of
    {ok, [{OldPath, _NewPath, Text}]} -> 
      Edit = #{
        documentChanges => [
          text_document_edit(OldPath, Text)
        ]
      },
      apply_edit(Edit);
    {error, Err} -> 
      ?LOG_INFO("Error renaming fun: ~p", Err)
  end,
  [];

execute_command(<<"rename-mod">>, [Mod, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming mod... (~p, ~p, ~p)", [Mod, Path, NewMod]),
  Changes = refac_rename_mod:rename_mod(binary_to_list(Path), binary_to_atom(NewMod), [binary_to_list(Path)], wls, 4),
  case Changes of
    {ok, [{OldPath, NewPath, Text}]} -> 
      Edit = #{
        documentChanges => [
          rename_file(OldPath, NewPath),
          text_document_edit(NewPath, Text)
        ]
      },
      apply_edit(Edit);
    {error, Err} -> 
      ?LOG_INFO("Error renaming fun: ~p", Err)
  end,
  [];

execute_command(<<"extract-fun">>, [Path, StartLine, StartCol, EndLine, EndCol, NewName]) ->
  Changes = refac_new_fun:fun_extraction(binary_to_list(Path), {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(NewName), wls, 4),
  case Changes of
    {ok, [{OldName, _NewPath, Text}]} -> 
      Edit = #{
        changes => #{
          els_uri:uri(list_to_binary(OldName)) => [text_edit(Text)]
        }
      },
      apply_edit(Edit);
    {error, Err} -> 
      ?LOG_INFO("Error renaming fun: ~p", Err)
  end,
  [];

execute_command(<<"comment-out-spec">>, [Path]) ->
  refac_comment_out_spec:comment_out([binary_to_list(Path)]),
  %% TODO use workspaceEdit
  [];

execute_command(Command, Arguments) ->
  ?LOG_INFO("Unsupported command: [Command=~p] [Arguments=~p]",
             [Command, Arguments]),
  [].


%% HElPER FUNCTIONS

-type state() :: any().
-type refactor_type() :: binary().
-type optionalVersionedTextDocumentIdentifier() :: #{'uri' := uri(), 'version' := integer() | null }.
-type textEdit() :: #{'range' := range(), 'newText' := binary() }.
-type textDocumentEdit() :: #{'textDocument' := optionalVersionedTextDocumentIdentifier(), 'edits' := [textEdit()]} | #{'changes' := #{uri() := [textEdit()]}}.
-type workspaceEdit() :: #{'documentChanges' := textDocumentEdit() | renameFile() }.
-type renameFile() :: #{'kind':=refactor_type(),  'newUri':=uri(),  'oldUri':=uri()}.


-spec apply_edit(workspaceEdit()) -> ok.
apply_edit(Body) -> 
  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => Body
  },
  els_server:send_request(Method, Params).


-spec rename_file(wls_utils:path(), wls_utils:path()) -> renameFile().
rename_file(OldName, NewName) ->
  #{
    kind => <<"rename">>,
    oldUri => els_uri:uri(list_to_binary(OldName)),
    newUri => els_uri:uri(list_to_binary(NewName))
  }.

-spec text_document_edit(wls_utils:path(), binary()) -> textDocumentEdit().
text_document_edit(Name, Text) ->
  #{
  textDocument =>
    #{
      uri => els_uri:uri(list_to_binary(Name)),
      version => null
    },
  edits =>
    [
      text_edit(Text)
    ]
  }.

-spec text_edit(binary()) ->  textEdit().
text_edit(Text) -> #{
  range =>
    #{ start => #{ line => 0, character => 0},
      'end' => #{ line => length(binary:split(Text, <<"\n">>, [global])), character => 0}
    },
  newText => els_utils:to_binary(Text)}.