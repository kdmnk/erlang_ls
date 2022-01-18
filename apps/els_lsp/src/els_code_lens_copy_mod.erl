%%==============================================================================
%% Code Lens: server_info
%%==============================================================================

-module(els_code_lens_copy_mod).

-behaviour(els_code_lens).
-export([command/3
         ,is_default/0
         ,pois/1
        ]).

-include("els_lsp.hrl").

-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
                 els_command:command().
command(Document, _POI, _State) ->
  Title = title(),
  CommandId = <<"copy-mod">>,
  #{uri := Uri} = Document,
  M = els_uri:module(Uri),
  P = els_uri:path(Uri),
  els_command:make_command(Title, CommandId, [M, P]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  els_dt_document:pois(Document, [module]).

-spec title() -> binary().
title() ->
  <<"Copy module">>.
