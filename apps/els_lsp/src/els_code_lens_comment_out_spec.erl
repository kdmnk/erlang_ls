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
  false.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  #{kind := Kind} = Document,
  case Kind of
    refactor_form -> [];
    _ -> [els_poi:new(#{from => {1, 1}, to => {1, 1}}, dummy, dummy)]
  end.

-spec title() -> binary().
title() ->
  <<"Comment out spec">>.
