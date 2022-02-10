-module(els_code_lens_form_select_some).

-behaviour(els_code_lens).

-export([command/3
         ,is_default/0
         ,pois/1
         ,init/1
        ]).

-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

-spec init(els_dt_document:item()) -> els_code_lens:state().
init(Document) ->
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  Mod = els_uri:module(Uri),
  {ok, Text} = file:read_file(Path),
  Lines = binary:split(Text, <<"\n">>, [global]),
  case Lines of
    [<<"%!wrangler io form">>|L] ->
      [<<"%!fold:", Fun/binary>>|_] = L,
      S = binary:split(Fun, <<"/">>, [global]),
      FunName = binary_to_atom(hd(S)),
      Arity = list_to_integer(binary_to_list(lists:nth(2,S))),
      ClauseIndex = list_to_integer(binary_to_list(lists:nth(3,S))),
      {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(binary_to_list(Path), true),
      {ok, {_Mod, _FunName, _Arity, FunClauseDef}} = refac_fold_expression:get_fun_clause_def(AnnAST, FunName, Arity, ClauseIndex),
      #{ <<"function">> => FunName
       , <<"arity">> => Arity
       , <<"module">> => Mod
       , <<"ann_ast">> => dummy
       , <<"clause_index">> => dummy
       , <<"fun_clause_def">> => dummy};
    _ -> null
  end.



-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
                 els_command:command().
command(Document, _POI, State) ->
  Title = title(),
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  CommandId = <<"refactor-form-select-some">>,
  #{ <<"function">> := FunName
   , <<"ann_ast">> := AnnAST
   , <<"module">> := Mod
   , <<"fun_clause_def">> := FunClauseDef} = State,
  Candidates = refac_fold_expression:search_candidate_exprs(AnnAST, {Mod, Mod}, FunName, FunClauseDef),

  Argument = #{ <<"path">>  => Path
              , <<"refactor">> => fold
              , <<"ann_ast">> => AnnAST
              , <<"candidate">> => hd(Candidates)},
  els_command:make_command(Title, CommandId, [Argument]).

-spec is_default() -> boolean().
is_default() ->
  true.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  #{uri := Uri} = Document,
  Path = els_uri:path(Uri),
  Mod = els_uri:module(Uri),
  {ok, Text} = file:read_file(Path),
  Lines = binary:split(Text, <<"\n">>, [global]),
  case Lines of
    [<<"%!wrangler io form">>|L] ->
      [<<"%!fold:", Fun/binary>>|_] = L,
      S = binary:split(Fun, <<"/">>, [global]),
      FunName = binary_to_atom(hd(S)),
      Arity = list_to_integer(binary_to_list(lists:nth(2,S))),
      ClauseIndex = list_to_integer(binary_to_list(lists:nth(3,S))),
      {ok, {AnnAST, _Info}} = wrangler_ast_server:parse_annotate_file(binary_to_list(Path), true),
      {ok, {_Mod, _FunName, _Arity, FunClauseDef}} = refac_fold_expression:get_fun_clause_def(AnnAST, FunName, Arity, ClauseIndex),
      Candidates = refac_fold_expression:search_candidate_exprs(AnnAST, {Mod, Mod}, FunName, FunClauseDef),
      [getPoi(Candidate, AnnAST) || Candidate <- Candidates];
    _ ->
      []
  end.

-spec title() -> binary().
title() ->
  <<"Refactor this instance">>.
getPoi({{{StartLine, StartCol}, {EndLine, EndCol}}, _Expr, _NewExp} = _Candidate, _AnnAST) ->
  els_poi:new(
    #{from => {StartLine -1, StartCol}, to => {EndLine -1, EndCol}},
    dummy,
    dummy,
    #{<<"refactor">> => fold} %%TODO add Candidate and AnnAST
  ).

