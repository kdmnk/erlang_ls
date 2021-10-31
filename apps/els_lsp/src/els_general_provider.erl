-module(els_general_provider).

-behaviour(els_provider).
-export([ handle_request/2
        , is_enabled/0
        ]).

-export([ server_capabilities/0
        ]).

%%==============================================================================
%% Includes
%%==============================================================================
-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

%%==============================================================================
%% Types
%%==============================================================================

-type server_capabilities() :: map().
-type initialize_request() :: {initialize, initialize_params()}.
-type initialize_params() :: #{ processId             := number() | null
                              , rootPath              => binary() | null
                              , rootUri               := uri() | null
                              , initializationOptions => any()
                              , capabilities          := client_capabilities()
                              , trace                 => off
                                                       | messages
                                                       | verbose
                              , workspaceFolders      => [workspace_folder()]
                                                       | null
                              }.
-type initialize_result() :: #{ capabilities => server_capabilities() }.
-type initialized_request() :: {initialized, initialized_params()}.
-type initialized_params() :: #{}.
-type initialized_result() :: null.
-type shutdown_request() :: {shutdown, shutdown_params()}.
-type shutdown_params() :: #{}.
-type shutdown_result() :: null.
-type exit_request() :: {exit, exit_params()}.
-type exit_params() :: #{status => atom()}.
-type exit_result() :: null.
-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

-spec is_enabled() -> boolean().
is_enabled() -> true.

-spec handle_request( initialize_request()
                    | initialized_request()
                    | shutdown_request()
                    | exit_request()
                    , state()) ->
        { initialize_result()
        | initialized_result()
        | shutdown_result()
        | exit_result()
        , state()
        }.
handle_request({initialize, Params}, State) ->
  #{ <<"rootUri">> := RootUri0
   , <<"capabilities">> := Capabilities
   } = Params,
  RootUri = case RootUri0 of
              null ->
                {ok, Cwd} = file:get_cwd(),
                els_uri:uri(els_utils:to_binary(Cwd));
              _ -> RootUri0
            end,
  InitOptions = case maps:get(<<"initializationOptions">>, Params, #{}) of
                  InitOptions0 when is_map(InitOptions0) ->
                    InitOptions0;
                  _ -> #{}
                end,
  ok = els_config:initialize(RootUri, Capabilities, InitOptions, true),
  NewState = State#{ root_uri => RootUri, init_options => InitOptions},
  {server_capabilities(), NewState};
handle_request({initialized, _Params}, State) ->
  #{root_uri := RootUri} = State,

  NodeName = els_distribution_server:node_name( <<"erlang_ls">>
                                              , filename:basename(RootUri)),
  els_distribution_server:start_distribution(NodeName),
  ?LOG_INFO("Started distribution for: [~p]", [NodeName]),


  {null, State};
handle_request({shutdown, _Params}, State) ->
  {null, State};
handle_request({exit, #{status := Status}}, State) ->
  ?LOG_INFO("Language server stopping..."),
  ExitCode = case Status of
               shutdown -> 0;
               _        -> 1
             end,
  els_utils:halt(ExitCode),
  {null, State}.

%%==============================================================================
%% API
%%==============================================================================

-spec server_capabilities() -> server_capabilities().
server_capabilities() ->
  {ok, Version} = application:get_key(?APP, vsn),
  #{ capabilities =>
       #{ textDocumentSync =>
            #{ openClose => true
             , change    => els_text_synchronization:sync_mode()
             , save      => #{includeText => false}
             }
        , documentSymbolProvider =>
            els_document_symbol_provider:is_enabled()
        , workspaceSymbolProvider =>
            els_workspace_symbol_provider:is_enabled()
        , codeActionProvider =>
            els_code_action_provider:is_enabled()
        , foldingRangeProvider =>
            els_folding_range_provider:is_enabled()
        , implementationProvider =>
            els_implementation_provider:is_enabled()
        , executeCommandProvider =>
            els_execute_command_provider:options()
        , codeLensProvider =>
            els_code_lens_provider:options()
       },
     serverInfo =>
       #{ name    => <<"Erlang LS">>
        , version => els_utils:to_binary(Version)
        }
   }.
