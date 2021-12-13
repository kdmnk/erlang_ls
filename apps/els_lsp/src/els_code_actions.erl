
%% Code Lens: Behaviour and API
%%==============================================================================

-module(els_code_actions).

%%==============================================================================
%% Callback Functions
%%==============================================================================

-callback init(path()) -> state(). %% TODO store AST?
-callback command(path(), range()) -> map().
-callback is_default() -> boolean().
-callback precondition(path(), range()) -> boolean().
-optional_callbacks([ init/1
                    , precondition/2
                    ]).

%%==============================================================================
%% API
%%==============================================================================

-export([ available_actions/0
        , default_actions/0
        , enabled_actions/0
        , actions/3
        ]).

%%==============================================================================
%% Includes
%%==============================================================================

-include("els_lsp.hrl").
-include_lib("kernel/include/logger.hrl").

%%==============================================================================
%% Type Definitions
%%==============================================================================

-type state() :: any().
-type action_id() :: binary().
-type path() :: binary().
-export_type([path/0]).

%%==============================================================================
%% API
%%==============================================================================

-spec available_actions() -> [action_id()].
available_actions() ->
  [ <<"rename_fun">>
  , <<"extract_fun">>
  ].

-spec default_actions() ->  [action_id()].
default_actions() ->
  [Id || Id <- available_actions(), (cb_module(Id)):is_default()].

-spec enabled_actions() ->  [action_id()].
enabled_actions() ->
  %%TODO
  %Config = els_config:get(actions),
  %Default = default_actions(),
  %Enabled = maps:get("enabled", Config, []),
  %Disabled = maps:get("disabled", Config, []),
  %lists:usort((Default ++ valid(Enabled)) -- valid(Disabled)).
  default_actions().

-spec actions(action_id(), path(), range()) ->  [action_id()].
actions(Id, Path, Range) ->
  CbModule = cb_module(Id),
  case precondition(CbModule, Path, Range) of
    true ->
      % State = case erlang:function_exported(CbModule, init, 1) of
      %           true ->
      %             CbModule:init(Path, Range);
      %           false ->
      %             'state_not_initialized'
      %         end,
      CbModule:command(Path, Range);
    false ->
      null
  end.

%%==============================================================================
%% Constructors
%%==============================================================================


% make_action(CbModule, Path, Range) ->
%   #{ range   => els_protocol:range(Range),
%      command => CbModule:command(Document, POI, State),
%      data    => []
%    }.

%% @doc Return the callback module for a given Code Action Identifier
-spec cb_module(action_id()) -> module().
cb_module(Id0) ->
  Id = re:replace(Id0, "-", "_", [global, {return, binary}]),
  binary_to_atom(<<"els_code_action_", Id/binary>>, utf8).

%%==============================================================================
%% Internal Functions
%%==============================================================================

% -spec is_valid(action_id()) -> boolean().
% is_valid(Id) ->
%   lists:member(Id, available_actions()).

% -spec valid([string()]) -> [action_id()].
% valid(Ids0) ->
%   Ids = [els_utils:to_binary(Id) || Id <- Ids0],
%   {Valid, Invalid} = lists:partition(fun is_valid/1, Ids),
%   case Invalid of
%     [] ->
%       ok;
%     _ ->
%       Fmt = "Skipping invalid lenses in config file: ~p",
%       Args = [Invalid],
%       Msg = lists:flatten(io_lib:format(Fmt, Args)),
%       ?LOG_WARNING(Msg),
%       els_server:send_notification(<<"window/showMessage">>,
%                                    #{ type => ?MESSAGE_TYPE_WARNING,
%                                       message => els_utils:to_binary(Msg)
%                                     })
%   end,
%   Valid.

-spec precondition(atom(), path(), wls_utils:range()) -> boolean().
precondition(CbModule, Path, Range) ->
  case erlang:function_exported(CbModule, precondition, 2) of
    true ->
      CbModule:precondition(Path, Range);
    false ->
      true
  end.
