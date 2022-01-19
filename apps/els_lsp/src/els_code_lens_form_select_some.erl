-module(els_code_lens_form_select_some).

-behaviour(els_code_lens).

-export([command/3
         ,is_default/0
         ,pois/1
        ]).

-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").


-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
                 els_command:command().
command(Document, POI, _State) ->
  Title = title(),
  CommandId = <<"refactor-form-select-some">>,
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  %#{command := Command, function := {Function, Arity}} = POI,
  els_command:make_command(Title, CommandId, [Path]).%, Command, Function, Arity]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  #{kind := Kind, uri := Uri} = Document,
  Path = els_uri:path(Uri),
  case Kind of
    refactor_form ->
      {ok, Text} = file:read_file(Path),
      Lines = binary:split(Text, <<"\n">>, [global]),
      POIs = getPois(Lines, 1),
      ?LOG_INFO("POIs: ~p", [POIs]),
      POIs;
    _ -> []
  end.

-spec title() -> binary().
title() ->
  <<"Refactor this instance">>.


getPois([], _LineCounter) -> [];
getPois([H|T], LineCounter) ->
  case H of
    <<"%!", L/binary>> ->
      POI = createPoi(L, LineCounter),
      ?LOG_INFO("Poi: ~p", [POI]),
      [ POI | getPois(T, LineCounter+1)];
    L -> getPois(T, LineCounter+1)
  end.

createPoi(Line, LineCounter) ->
  Splitted = string:split(Line, ":", all),
  Refactoring = lists:nth(1, Splitted),
  Function = string:split(lists:nth(2, Splitted), "/"),
  FunName = lists:nth(1, Function),
  FunArity = list_to_integer(binary_to_list(lists:nth(2, Function))),
  Pos = string:split(lists:nth(3, Splitted), "-", all),
  StartPos = string:split(lists:nth(1, Pos), ","),
  StartLine = list_to_integer(binary_to_list(lists:nth(1, StartPos))),
  StartCol = list_to_integer(binary_to_list(lists:nth(2, StartPos))),
  EndPos = string:split(lists:nth(2, Pos), ","),
  EndLine = list_to_integer(binary_to_list(lists:nth(1, EndPos))),
  EndCol = list_to_integer(binary_to_list(lists:nth(2, EndPos))),
  els_poi:new(
    #{from => {LineCounter, 1}, to => {LineCounter, 1}},
    dummy,
    dummy,
    #{command => Refactoring, function => {FunName, FunArity}, pos => {{StartLine, StartCol}, {EndLine, EndCol}}}
  ).

