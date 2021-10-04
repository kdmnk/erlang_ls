%%==============================================================================
%% Code Lens: test
%%==============================================================================

-module(els_code_lens_test).

-behaviour(els_code_lens).
-export([ command/3
        , is_default/0
        , pois/1
        ]).

-include("els_lsp.hrl").

-spec command(els_dt_document:item(), poi(), els_code_lens:state()) ->
        els_command:command().
command(_Document, _POI, _State) ->
  Title = <<"Wrangler test">>,
  CommandId = <<"test">>,
  CommandArgs = [],
  els_command:make_command(Title, CommandId, CommandArgs).

-spec is_default() -> boolean().
is_default() ->
  false.

-spec pois(els_dt_document:item()) -> [poi()].
pois(Document) ->
  els_dt_document:pois(Document, [function]).
