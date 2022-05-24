-module(wls_server_SUITE).

%% CT Callbacks
-export([ suite/0
        , init_per_suite/1
        , end_per_suite/1
        , init_per_testcase/2
        , end_per_testcase/2
        , all/0
        ]).

%% Test cases
-export([empty/1]).
-export([start_refactoring/1]).
-export([refactor_a_candidate/1]).

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
  els_config:set(wrangler, #{
    "enabled" => true,
    "enabled_refactorings" => ["fold-expression"]
  }),
  wls_server:start(),
  Config2.

-spec end_per_testcase(atom(), config()) -> ok.
end_per_testcase(TestCase, Config) ->
  els_test_utils:end_per_testcase(TestCase, Config),
  % Delete header if it exists
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  {ok, Text} = file:read_file(Path),
  case binary:split(Text, <<"\n">>) of
    [<<"%! Wrangler refactor form.">>, RemText1] ->
        [_, RemText2] = binary:split(RemText1, <<"\n">>),
        [_, RemText3] = binary:split(RemText2, <<"\n">>),
        file:write_file(Path, RemText3);
    _ -> ok
  end.


-spec empty(config()) ->  ok.
empty(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  Result = wls_server:get_state(Path),
  ?assertEqual(not_exists, Result),
  ok.

-spec start_refactoring(config()) ->  ok.
start_refactoring(Config) ->
  Uri = ?config(wls_uri, Config),
  Path = wls_utils:path(Uri),
  Result = wls_server:start_refactoring(Path, fold_expression, {17, 3}),
  ?assertEqual(ok, Result),
  {ok, Candidates, Data} = wls_code_action_fold_expression:calculate_regions(Path, {20, 3}),
  Expected = {under_refactoring,
    #{refactor => fold_expression, regions => Candidates, data => Data}
  },
  ?assertEqual(Expected, wls_server:get_state(Path)),
  ok.

-spec refactor_a_candidate(config()) ->  ok.
refactor_a_candidate(_Config) -> ok.
