-module(els_methods).

-export([ dispatch/4
        ]).

-export([ exit/2
        , initialize/2
        , initialized/2
        , shutdown/2
        , textdocument_didopen/2
        , textdocument_didchange/2
        , textdocument_didsave/2
        , textdocument_didclose/2
        , textdocument_documentsymbol/2
        , textdocument_foldingrange/2
        , workspace_didchangeconfiguration/2
        , textdocument_codeaction/2
        , textdocument_codelens/2
        , workspace_executecommand/2
        , workspace_didchangewatchedfiles/2
        , workspace_symbol/2
        ]).

%%==============================================================================
%% Includes
%%==============================================================================
-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

-type method_name()  :: binary().
-type state()        :: map().
-type params()       :: map().
-type result()       :: {response, params() | null, state()}
                      | {error, params(), state()}
                      | {noresponse, state()}
                      | {noresponse, {els_provider:provider(), pid()}, state()}
                      | {notification, binary(), params(), state()}.
-type request_type() :: notification | request.

%%==============================================================================
%% @doc Dispatch the handling of the method to els_method
%%==============================================================================
-spec dispatch(method_name(), params(), request_type(), state()) -> result().
dispatch(<<"$/", Method/binary>>, Params, notification, State) ->
  Msg = "Ignoring $/ notification [method=~p] [params=~p]",
  Fmt = [Method, Params],
  ?LOG_DEBUG(Msg, Fmt),
  {noresponse, State};
dispatch(<<"$/", Method/binary>>, Params, request, State) ->
  Msg = "Ignoring $/ request [method=~p] [params=~p]",
  Fmt = [Method, Params],
  ?LOG_DEBUG(Msg, Fmt),
  Error = #{ code    => ?ERR_METHOD_NOT_FOUND
           , message => <<"Method not found: ", Method/binary>>
           },
  {error, Error, State};
dispatch(Method, Params, _Type, State) ->
  Function = method_to_function_name(Method),
  ?LOG_DEBUG("Dispatching request [method=~p] [params=~p]", [Method, Params]),
  try do_dispatch(Function, Params, State)
  catch
    error:undef ->
      not_implemented_method(Method, State);
    Type:Reason:Stack ->
      ?LOG_ERROR( "Unexpected error [type=~p] [error=~p] [stack=~p]"
                , [Type, Reason, Stack]),
      Error = #{ code    => ?ERR_UNKNOWN_ERROR_CODE
               , message => <<"Unexpected error while ", Method/binary>>
               },
      {error, Error, State}
  end.

-spec do_dispatch(atom(), params(), state()) -> result().
do_dispatch(exit, Params, State) ->
  els_methods:exit(Params, State);
do_dispatch(_Function, _Params, #{status := shutdown} = State) ->
  Message = <<"Server is shutting down">>,
  Result  = #{ code    => ?ERR_INVALID_REQUEST
             , message => Message
             },
  {error, Result, State};
do_dispatch(initialize, Params, State) ->
  els_methods:initialize(Params, State);
do_dispatch(Function, Params, #{status := initialized} = State) ->
  els_methods:Function(Params, State);
do_dispatch(_Function, _Params, State) ->
  Message = <<"The server is not fully initialized yet, please wait.">>,
  Result  = #{ code    => ?ERR_SERVER_NOT_INITIALIZED
             , message => Message
             },
  {error, Result, State}.

-spec not_implemented_method(method_name(), state()) -> result().
not_implemented_method(Method, State) ->
  ?LOG_WARNING("[Method not implemented] [method=~s]", [Method]),
  Message = <<"Method not implemented: ", Method/binary>>,
  Method1 = <<"window/showMessage">>,
  Params  = #{ type    => ?MESSAGE_TYPE_INFO
             , message => Message
             },
  {notification, Method1, Params, State}.

-spec method_to_function_name(method_name()) -> atom().
method_to_function_name(<<"$/", Method/binary>>) ->
  method_to_function_name(<<"$_", Method/binary>>);
method_to_function_name(Method) ->
  Replaced = string:replace(Method, <<"/">>, <<"_">>),
  Lower    = string:lowercase(Replaced),
  Binary   = els_utils:to_binary(Lower),
  binary_to_atom(Binary, utf8).

%%==============================================================================
%% Initialize
%%==============================================================================

-spec initialize(params(), state()) -> result().
initialize(Params, State) ->
  Provider = els_general_provider,
  Request  = {initialize, Params},
  Response = els_provider:handle_request(Provider, Request),
  {response, Response, State#{status => initialized}}.

%%==============================================================================
%% Initialized
%%==============================================================================

-spec initialized(params(), state()) -> result().
initialized(Params, State) ->
  Provider = els_general_provider,
  Request  = {initialized, Params},
  _Response = els_provider:handle_request(Provider, Request),
  %% Report to the user the server version
  {ok, Version} = application:get_key(?APP, vsn),
  ?LOG_INFO("initialized: [App=~p] [Version=~p]", [?APP, Version]),
  BinVersion = els_utils:to_binary(Version),
  Root = filename:basename(els_uri:path(els_config:get(root_uri))),
  OTPVersion = els_utils:to_binary(erlang:system_info(otp_release)),
  Message = <<"Erlang LS (in ", Root/binary, "), version: "
             , BinVersion/binary, ", OTP version: "
             , OTPVersion/binary>>,
  NMethod  = <<"window/showMessage">>,
  NParams  = #{ type    => ?MESSAGE_TYPE_INFO
              , message => Message
             },
  {notification, NMethod, NParams, State}.

%%==============================================================================
%% shutdown
%%==============================================================================

-spec shutdown(params(), state()) -> result().
shutdown(Params, State) ->
  Provider = els_general_provider,
  Request  = {shutdown, Params},
  Response = els_provider:handle_request(Provider, Request),
  {response, Response, State#{status => shutdown}}.

%%==============================================================================
%% exit
%%==============================================================================

-spec exit(params(), state()) -> no_return().
exit(_Params, State) ->
  Provider = els_general_provider,
  Request  = {exit, #{status => maps:get(status, State, undefined)}},
  _Response = els_provider:handle_request(Provider, Request),
  {noresponse, #{}}.

%%==============================================================================
%% textDocument/didopen
%%==============================================================================

-spec textdocument_didopen(params(), state()) -> result().
textdocument_didopen(Params, State) ->
  ok = els_text_synchronization:did_open(Params),
  {noresponse, State}.

%%==============================================================================
%% textDocument/didchange
%%==============================================================================

-spec textdocument_didchange(params(), state()) -> result().
textdocument_didchange(Params, State) ->
  ok = els_text_synchronization:did_change(Params),
  {noresponse, State}.

%%==============================================================================
%% textDocument/didsave
%%==============================================================================

-spec textdocument_didsave(params(), state()) -> result().
textdocument_didsave(Params, State) ->
  ok = els_text_synchronization:did_save(Params),
  {noresponse, State}.

%%==============================================================================
%% textDocument/didclose
%%==============================================================================

-spec textdocument_didclose(params(), state()) -> result().
textdocument_didclose(Params, State) ->
  ok = els_text_synchronization:did_close(Params),
  {noresponse, State}.

%%==============================================================================
%% textdocument/documentSymbol
%%==============================================================================

-spec textdocument_documentsymbol(params(), state()) -> result().
textdocument_documentsymbol(Params, State) ->
  Provider = els_document_symbol_provider,
  Request  = {document_symbol, Params},
  Response = els_provider:handle_request(Provider, Request),
  {response, Response, State}.

%%==============================================================================
%% textDocument/foldingRange
%%==============================================================================

-spec textdocument_foldingrange(params(), state()) -> result().
textdocument_foldingrange(Params, State) ->
  Provider = els_folding_range_provider,
  Response = els_provider:handle_request( Provider
                                        , {document_foldingrange, Params}),
  {response, Response, State}.


%%==============================================================================
%% workspace/didChangeConfiguration
%%==============================================================================

-spec workspace_didchangeconfiguration(params(), state()) -> result().
workspace_didchangeconfiguration(_Params, State) ->
  %% Some clients send this notification on startup, even though we
  %% have no server-side config.  So swallow it without complaining.
  {noresponse, State}.

%%==============================================================================
%% textDocument/codeAction
%%==============================================================================

-spec textdocument_codeaction(params(), state()) -> result().
textdocument_codeaction(Params, State) ->
  Provider = els_code_action_provider,
  Response = els_provider:handle_request(Provider,
                                         {document_codeaction, Params}),
  {response, Response, State}.

%%==============================================================================
%% textDocument/codeLens
%%==============================================================================

-spec textdocument_codelens(params(), state()) -> result().
textdocument_codelens(Params, State) ->
  Provider = els_code_lens_provider,
  Job = els_provider:handle_request(Provider, {document_codelens, Params}),
  {noresponse, {Provider, Job}, State}.

%%==============================================================================
%% workspace/executeCommand
%%==============================================================================

-spec workspace_executecommand(params(), state()) -> result().
workspace_executecommand(Params, State) ->
  Provider = els_execute_command_provider,
  Response = els_provider:handle_request(Provider,
                                         {workspace_executecommand, Params}),
  {response, Response, State}.

%%==============================================================================
%% workspace/didChangeWatchedFiles
%%==============================================================================

-spec workspace_didchangewatchedfiles(map(), state()) -> result().
workspace_didchangewatchedfiles(_Params, State) ->
  %% Some clients rely on these notifications to be successful.
  %% Let's just ignore them.
  {noresponse, State}.

%%==============================================================================
%% workspace/symbol
%%==============================================================================

-spec workspace_symbol(map(), state()) -> result().
workspace_symbol(Params, State) ->
  Provider = els_workspace_symbol_provider,
  Response = els_provider:handle_request(Provider, {symbol, Params}),
  {response, Response, State}.
