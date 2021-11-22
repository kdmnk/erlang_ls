%%==============================================================================
%% Code Lens: server_info
%%==============================================================================

-module(els_code_lens_rename_mod).

-behaviour(els_code_lens).
-export([asd/3
        , is_default/0
        , pois/1
        ]).

-include("els_lsp.hrl").

-spec asd(els_dt_document:item(), poi(), els_code_lens:state()) ->
             els_command:command().
asd(Document, _POI, _State) ->
  Title = title(),
  CommandId = <<"rename-mod">>,
  #{uri := Uri} = Document,
  M = els_uri:module(Uri),
  P = els_uri:path(Uri),
  els_command:make_command(Title, CommandId, [M, P]).

-spec is_default() -> boolean().
is_default() ->
  false.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  els_dt_document:pois(Document, [module]).

-spec title() -> binary().
title() ->
  <<"Wrangler: rename module">>.
