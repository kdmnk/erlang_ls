-module(els_text_synchronization).

-include_lib("kernel/include/logger.hrl").
-include("els_lsp.hrl").

-export([ sync_mode/0
        , did_change/1
        , did_open/1
        , did_save/1
        , did_close/1
        ]).

-spec sync_mode() -> text_document_sync_kind().
sync_mode() ->
  case els_config:get(incremental_sync) of
    true  -> ?TEXT_DOCUMENT_SYNC_KIND_INCREMENTAL;
    false -> ?TEXT_DOCUMENT_SYNC_KIND_FULL
  end.

-spec did_change(map()) -> ok.
did_change(Params) ->
  ContentChanges = maps:get(<<"contentChanges">>, Params),
  TextDocument   = maps:get(<<"textDocument">>  , Params),
  Uri            = maps:get(<<"uri">>           , TextDocument),
  case ContentChanges of
    [] ->
      ok;
    [Change] when not is_map_key(<<"range">>, Change) ->
      %% Full text sync
      #{<<"text">> := Text} = Change,
      {Duration, ok} =
        timer:tc(fun() -> els_indexing:index(Uri, Text, 'deep') end),
      ?LOG_DEBUG("didChange FULLSYNC [size: ~p] [duration: ~pms]\n",
                 [size(Text), Duration div 1000]),
      ok;
    ContentChanges ->
      %% Incremental sync
      ?LOG_DEBUG("didChange INCREMENTAL [changes: ~p]", [ContentChanges]),
      Edits = [to_edit(Change) || Change <- ContentChanges],
      {Duration, ok} =
        timer:tc(fun() -> els_index_buffer:apply_edits_async(Uri, Edits) end),
      ?LOG_DEBUG("didChange INCREMENTAL [duration: ~pms]\n",
                 [Duration div 1000]),
      ok
  end.

-spec did_open(map()) -> ok.
did_open(Params) ->
  TextDocument = maps:get(<<"textDocument">>, Params),
  Uri          = maps:get(<<"uri">>         , TextDocument),
  Text         = maps:get(<<"text">>        , TextDocument),
  ok           = els_indexing:index(Uri, Text, 'deep'),
  ok.

-spec did_save(map()) -> ok.
did_save(Params) ->
  TextDocument = maps:get(<<"textDocument">>, Params),
  Uri          = maps:get(<<"uri">>         , TextDocument),
  ok = els_index_buffer:flush(Uri),
  ok.

-spec did_close(map()) -> ok.
did_close(_Params) -> ok.

-spec to_edit(map()) -> els_text:edit().
to_edit(#{<<"text">> := Text, <<"range">> := Range}) ->
  #{ <<"start">> := #{<<"character">> := FromC, <<"line">> := FromL}
   , <<"end">> := #{<<"character">> := ToC, <<"line">> := ToL}
   } = Range,
  {#{ from => {FromL, FromC}
    , to => {ToL, ToC}
    }, els_utils:to_list(Text)}.
