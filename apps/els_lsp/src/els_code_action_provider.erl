-module(els_code_action_provider).

-behaviour(els_provider).

-export([handle_request/2, is_enabled/0]).

-include("els_lsp.hrl").

-include_lib("kernel/include/logger.hrl").

-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

-spec is_enabled() -> boolean().
is_enabled() ->
  true.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({document_codeaction, Params}, State) ->
  #{<<"textDocument">> := #{<<"uri">> := Uri},
    <<"range">> := RangeLSP,
    <<"context">> := Context} =
    Params,
  Result = code_actions(Uri, RangeLSP, Context),
  {Result, State}.

%%==============================================================================
%% Internal Functions
%%==============================================================================

%% @doc Result: `(Command | CodeAction)[] | null'
-spec code_actions(uri(), range(), code_action_context()) -> [map()].
code_actions(Uri, Range, _Context) ->
  Actions = filter([els_code_actions:actions(Id, Uri, Range) || Id <- els_code_actions:enabled_actions()]),
  case Actions of
    [] -> null;
    A -> A
  end.

filter([]) -> [];
filter([null | T]) -> filter(T);
filter([H | T]) -> [H | filter(T)].
