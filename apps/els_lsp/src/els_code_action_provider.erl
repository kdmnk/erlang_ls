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
  %% get the position of the text hovered:
  #{<<"start">> := #{<<"character">> := StartCol, <<"line">> := StartLine},
    <<"end">> := #{<<"character">> := _EndCol, <<"line">> := _EndLine}} =
    Range,

  %% get the whole function
  {module, _Module} = code:ensure_loaded(wrangler_syntax),
  {module, _Module2} = code:ensure_loaded(api_interface),
  Path = binary_to_list(els_uri:path(Uri)),
  ?LOG_INFO(Path),
  %% TODO fails:
  %% api_interface:pos_to_node(Path, {StartLine, StartCol}, fun (B) -> true end),
  %{ok, Node} = api_interface:pos_to_node(Path, {StartLine, StartCol}, fun (B) -> wrangler_syntax:type(B) == function end),
  %?LOG_INFO(wrangler_syntax:get_pos(Node)),
  %% return a list of the possible commands that will appear in the light bulb
  %% does nothing currently
  [#{title => <<"Do something">>,
     kind => ?CODE_ACTION_KIND_REFACTOR,
     command =>
       els_command:make_command(<<"Do something">>,
                                <<"code_action_do_something">>,
                                [#{uri => Uri,
                                   from => StartLine,
                                   to => StartCol}])}].

%%------------------------------------------------------------------------------
