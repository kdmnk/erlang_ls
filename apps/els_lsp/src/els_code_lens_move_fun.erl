-module(els_code_lens_move_fun).

-behaviour(els_code_lens).
-export([command/3
         ,is_default/0
         ,pois/1
        ]).

-include("els_lsp.hrl").

-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
                 els_command:command().
command(Document, POI, _State) ->
  #{id := {Function, Arity}} = POI,
  Title = title(),
  CommandId = <<"move-fun">>,
  #{uri := Uri} = Document,
  M = els_uri:module(Uri),
  P = els_uri:path(Uri),
  els_command:make_command(Title, CommandId, [M, P, Function, Arity]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  els_dt_document:pois(Document, [function]).

-spec title() -> binary().
title() ->
  <<"Move function">>.
