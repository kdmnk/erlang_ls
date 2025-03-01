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
                 , els_command:with_prefix(<<"copy-mod">>)
                 , els_command:with_prefix(<<"extract-fun">>)
                 , els_command:with_prefix(<<"move-fun">>)
                 , els_command:with_prefix(<<"comment-out-spec">>)
                 , els_command:with_prefix(<<"generalise-fun">>)
                 , els_command:with_prefix(<<"new-var">>)
                 , els_command:with_prefix(<<"new-macro">>)
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
      ?LOG_INFO("Error renaming fun: ~p", [Err])
  end,
  [];

execute_command(<<"rename-mod">>, [Mod, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming mod... (~p, ~p, ~p)", [Mod, Path, NewMod]),
  Changes = refac_rename_mod:rename_mod(binary_to_list(Path), binary_to_list(NewMod), [binary_to_list(Path)], wls, 4),
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
      ?LOG_INFO("Error renaming mod: ~p", [Err])
  end,
  [];

execute_command(<<"copy-mod">>, [Mod, Path, NewMod]) ->
  {module, _Module} = code:ensure_loaded(api_wrangler),
  ?LOG_INFO("Renaming mod... (~p, ~p, ~p)", [Mod, Path, NewMod]),
  Changes = refac_copy_mod:copy_mod(binary_to_list(Path), binary_to_list(NewMod), [binary_to_list(Path)], wls, 4),
  case Changes of
    {ok, [{_OldPath, NewPath, Text}]} ->
      Edit = #{
        documentChanges => [
          create_file(NewPath),
          text_document_edit(NewPath, Text)
        ]
      },
      apply_edit(Edit);
    {error, Err} ->
      ?LOG_INFO("Error renaming mod: ~p", [Err])
  end,
  [];

execute_command(<<"extract-fun">>, [#{ <<"uri">>  := Uri
                                     , <<"range">> := Range}
                                    , NewName]) ->
  Path = binary_to_list(els_uri:path(Uri)),
  {Start, End} = wls_utils:range(Range), % convert to wrangler representation
  Changes = refac_new_fun:fun_extraction(Path, Start, End, binary_to_list(NewName), wls, 4),
  case Changes of
    {ok, [{OldPath, _NewPath, Text}]} ->
      Edit = #{
        documentChanges => [
          text_document_edit(OldPath, Text)
        ]
      },
      apply_edit(Edit); %% send applyEdit request
    {error, Err} ->
      ?LOG_INFO("Error extracting fun: ~p", [Err])
  end,
  [];

execute_command(<<"new-macro">>, [Path, StartLine, StartCol, EndLine, EndCol, NewName]) ->
  Changes = refac_new_macro:new_macro(binary_to_list(Path), {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(NewName), [binary_to_list(Path)], wls, 4),
  case Changes of
    {ok, [{OldName, _NewPath, Text}]} ->
      Edit = #{
        changes => #{
          els_uri:uri(list_to_binary(OldName)) => [text_edit(Text)]
        }
      },
      apply_edit(Edit);
    {error, Err} ->
      ?LOG_INFO("Error new macro: ~p", [Err])
  end,
  [];

execute_command(<<"generalise-fun">>, [Path, StartLine, StartCol, EndLine, EndCol, ParName]) ->
  try %%TODO try catch not working
    Changes = refac_gen:generalise(binary_to_list(Path), {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(ParName), [binary_to_list(Path)], wls, 8),
    case Changes of
      {ok, [{OldPath, _NewPath, Text}]} ->
        Edit = #{
          documentChanges => [
              text_document_edit(OldPath, Text)
            ]
          },
          apply_edit(Edit);
      Err ->
        ?LOG_INFO("Error generalising fun: ~p", [Err])
    end
  catch error:Reason:StackTrace -> ?LOG_INFO("Error generalising fun: ~p, ~p", [Reason, StackTrace]) end,
  [];

execute_command(<<"new-var">>, [Path, StartLine, StartCol, EndLine, EndCol, NewName]) ->
  Changes = refac_intro_new_var:intro_new_var(binary_to_list(Path), {StartLine, StartCol}, {EndLine, EndCol}, binary_to_list(NewName), [binary_to_list(Path)], wls, 4),
  case Changes of
    {ok, [{OldName, _NewPath, Text}]} ->
      Edit = #{
        changes => #{
          els_uri:uri(list_to_binary(OldName)) => [text_edit(Text)]
        }
      },
      apply_edit(Edit);
    {error, Err} ->
      ?LOG_INFO("Error introducing new variable: ~p", [Err])
  end,
  [];
execute_command(<<"move-fun">>, [Module, _Path, Function, Arity, NewPath]) ->
  Changes = refac_move_fun:move_fun_by_name(binary_to_atom(Module), {binary_to_atom(Function), Arity}, binary_to_list(NewPath), ["/Users/domi/Documents/GitHub/vscode/erlang_ls/apps/els_lsp"], wls, 4),
  case Changes of
    {ok, [{File1, _File1, Text}]} ->
      Edit = #{
        changes => #{
          els_uri:uri(list_to_binary(File1)) => [text_edit(Text)]
        }
      },
      apply_edit(Edit);
    {ok, [{File1, _File1, Text}, {File2, _File2, Text2}]} ->
      Edit = #{
        changes => #{
          els_uri:uri(list_to_binary(File1)) => [text_edit(Text)],
          els_uri:uri(list_to_binary(File2)) => [text_edit(Text2)]
        }
      },
      apply_edit(Edit);
    {error, Err} ->
      ?LOG_INFO("Error moving fun: ~p", [Err])
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
-type createFile() :: #{'kind':=refactor_type(),  'uri':=uri()}.
-type renameFile() :: #{'kind':=refactor_type(),  'newUri':=uri(),  'oldUri':=uri()}.


-spec apply_edit(workspaceEdit()) -> ok.
apply_edit(Body) ->
  Method = <<"workspace/applyEdit">>,
  Params = #{
    edit => Body
  },
  els_server:send_request(Method, Params).

-spec create_file(wls_utils:path()) -> createFile().
create_file(Name) ->
  #{
    kind => <<"create">>,
    uri => els_uri:uri(list_to_binary(Name))
  }.

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
