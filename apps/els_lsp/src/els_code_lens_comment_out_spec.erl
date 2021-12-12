-module(els_code_lens_comment_out_spec).

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
  CommandId = <<"comment-out-spec">>,
  #{uri := Uri} = Document,
  P = els_uri:path(Uri),
  els_command:make_command(Title, CommandId, [P]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(_Document) ->
  [els_poi:new(#{from => {1, 1}, to => {2, 1}}, dummy, dummy)].

-spec title() -> binary().
title() ->
  <<"Comment out spec">>.
