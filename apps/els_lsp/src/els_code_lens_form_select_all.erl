-module(els_code_lens_form_select_all).

-behaviour(els_code_lens).

-export([command/3
         ,is_default/0
         ,pois/1
        ]).

-include("els_lsp.hrl").

-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
                 els_command:command().
command(Document, POI, _State) ->
  Title = title(),
  CommandId = <<"refactor-form-select-all">>,
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  %#{command := Command, function := {Function, Arity}} = POI,
  els_command:make_command(Title, CommandId, [Path, <<"fold">>, <<"fun_to_fold">>, 0]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  {ok, Text} = file:read_file(Path),
  Lines = binary:split(Text, <<"\n">>, [global]),
  case Lines of
    [<<"%!wrangler io form">>|L] ->
      [els_poi:new(#{from => {1, 1}, to => {1, 1}}, dummy, dummy)]; %#{command => <<"fold">>, function => {fun_to_fold, 0}})];
    _ -> []
  end.

-spec title() -> binary().
title() ->
  <<"Refactor all">>.
