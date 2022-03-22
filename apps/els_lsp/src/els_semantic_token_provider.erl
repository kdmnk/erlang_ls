-module(els_semantic_token_provider).

-behaviour(els_provider).

-include("els_lsp.hrl").

-include_lib("kernel/include/logger.hrl").

-export([handle_request/2, is_enabled/0]).

%%==============================================================================
%% els_provider functions
%%==============================================================================

-type state() :: any().

-spec is_enabled() -> boolean().
is_enabled() ->
  true.

-spec handle_request(els_provider:request(), state()) -> {any(), state()}.
handle_request({semantic_tokens, Params}, State) ->
  #{<<"textDocument">> := #{<<"uri">> := Uri}} = Params,
  Result = #{<<"data">> => semantic_tokens(Uri)},
  {Result, State}.

-spec semantic_tokens(uri()) -> [integer()].
semantic_tokens(Uri) ->
   wls_semantic_tokens:semantic_tokens(Uri).
