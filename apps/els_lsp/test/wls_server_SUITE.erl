-module(wls_server_SUITE).

%% CT Callbacks
-export([suite/0, init_per_suite/1, end_per_suite/1, init_per_testcase/2,
         end_per_testcase/2, all/0]).
%% Test cases
-export([empty/1]).
-export([start_refactoring/1]).
-export([refactor_candidate/1]).
-export([exit_form/1]).

%%==============================================================================
%% Includes
%%==============================================================================
-include_lib("common_test/include/ct.hrl").
-include_lib("stdlib/include/assert.hrl").

%%==============================================================================
%% Types
%%==============================================================================
-type config() :: [{atom(), any()}].

%%==============================================================================
%% CT Callbacks
%%==============================================================================
-spec suite() -> [tuple()].
suite() ->
  [{timetrap, {seconds, 30}}].

-spec all() -> [atom()].
all() ->
  els_test_utils:all(?MODULE).

-spec init_per_suite(config()) -> config().
init_per_suite(Config) ->
  els_test_utils:init_per_suite(Config).

-spec end_per_suite(config()) -> ok.
end_per_suite(Config) ->
  els_test_utils:end_per_suite(Config).

-spec init_per_testcase(atom(), config()) -> config().
init_per_testcase(TestCase, Config) ->
  Config2 = els_test_utils:init_per_testcase(TestCase, Config),
  els_config:set(wrangler,
                 #{"enabled" => true, "enabled_refactorings" => ["fold-expression"]}),
  wls_server:start(),
  Uri = ?config(wls_uri, Config2),
  Path = wls_utils:path(Uri),
  UriBackup = ?config(wls_backup_uri, Config2),
  PathBackup = wls_utils:path(UriBackup),
  file:copy(PathBackup, Path),
  Config2.

-spec end_per_testcase(atom(), config()) -> ok.
end_per_testcase(TestCase, Config) ->
  els_test_utils:end_per_testcase(TestCase, Config).

-spec empty(config()) -> ok.
empty(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  Result = wls_server:get_state(Path),
  ?assertEqual(not_exists, Result),
  ok.

-spec start_refactoring(config()) -> ok.
start_refactoring(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  % Check new state
  ok = wls_server:start_refactoring(Path, fold_expression, {17, 3}),
  {ok, Candidates, Data} = wls_code_action_fold_expression:calculate_regions(Path, {20, 3}),
  Expected =
    {under_refactoring,
     #{refactor => fold_expression,
       regions => Candidates,
       data => Data}},
  ?assertEqual(Expected, wls_server:get_state(Path)),

  % Check code lenses
  PrefixedCommandExit = els_command:with_prefix(<<"wrangler-form-exit">>),
  PrefixedCommandFold = els_command:with_prefix(<<"wrangler-fold-expression">>),
  #{result := Result} = els_client:document_codelens(Uri),
  FilteredResultExit =
    [L || #{command := #{command := Command}} = L <- Result, Command =:= PrefixedCommandExit],
  FilteredResultFold =
    [L || #{command := #{command := Command}} = L <- Result, Command =:= PrefixedCommandFold],
  ExpectedExit =
    [#{command =>
         #{arguments => [#{uri => Uri}],
           command => PrefixedCommandExit,
           title => <<"Exit">>},
       data => [],
       range =>
         #{'end' => #{character => EC, line => EL}, start => #{character => SC, line => SL}}}
       || {EC, EL, SC, SL} <- [{40,29,2,29}, {40,33,2,33}, {1, 0, 0, 0}]],
  ?assertEqual(ExpectedExit, FilteredResultExit),
  ExpectedFold =
    [#{command =>
         #{arguments => [#{uri => Uri, index => Index}],
           command => PrefixedCommandFold,
           title => <<"Refactor this instance">>},
       data => [],
       range =>
         #{'end' => #{character => EC, line => EL}, start => #{character => SC, line => SL}}}
       || {EC, EL, SC, SL, Index} <- [{40,29,2,29,1}, {40,33,2,33,2}]],
  ?assertEqual(ExpectedFold, FilteredResultFold),
  ok.


-spec refactor_candidate(config()) -> ok.
refactor_candidate(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  wls_server:start_refactoring(Path, fold_expression, {18, 3}),
  {under_refactoring, #{regions := Regions}} = wls_server:get_state(Path),
  ?assertEqual(2, length(Regions)),
  wls_code_action_fold_expression:execute_command([#{ <<"uri">> => Uri, <<"index">> => 1}]),
  {under_refactoring, #{regions := Regions2}} = wls_server:get_state(Path),
  ?assertEqual(1, length(Regions2)),
  wls_code_action_fold_expression:execute_command([#{ <<"uri">> => Uri, <<"index">> => 1}]),
  ?assertEqual(not_exists, wls_server:get_state(Path)).

-spec exit_form(config()) -> ok.
exit_form(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  wls_server:start_refactoring(Path, fold_expression, {18, 3}),
  wls_server:exit_form(Path),
  ?assertEqual(not_exists, wls_server:get_state(Path)).
