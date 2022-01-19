-module(els_code_lens_form_exit).

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
  CommandId = <<"refactor-form-exit">>,
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  els_command:make_command(Title, CommandId, [Path]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  #{kind := Kind} = Document,
  case Kind of
    refactor_form ->
      [els_poi:new(#{from => {1, 2}, to => {1, 2}}, dummy, dummy)];
    _ -> []
  end.

-spec title() -> binary().
title() ->
  <<"Exit">>.
