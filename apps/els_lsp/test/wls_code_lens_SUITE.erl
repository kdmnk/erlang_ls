-module(wls_code_lens_SUITE).

%% CT Callbacks
-export([ suite/0
        , init_per_suite/1
        , end_per_suite/1
        , init_per_testcase/2
        , end_per_testcase/2
        , all/0
        ]).

%% Test cases
-export([comment_out_spec/1]).


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
    "enabled_refactorings" => [
      "comment-out-spec"]
  }),
  Config2.

-spec end_per_testcase(atom(), config()) -> ok.
end_per_testcase(TestCase, Config) ->
  els_test_utils:end_per_testcase(TestCase, Config).


-spec comment_out_spec(config()) ->  ok.
comment_out_spec(Config) ->
  Uri = ?config(wls_uri, Config),
   PrefixedCommand = els_command:with_prefix(<<"wrangler-comment-out-spec">>),
   #{result := Result} = els_client:document_codelens(Uri),
  FilteredResult = [
      L
   || #{command := #{command := Command}} = L <-
          Result,
      Command =:= PrefixedCommand
  ],
  Expected = [
      #{
          command => #{
              arguments => [#{uri => Uri}],
              command => PrefixedCommand,
              title => <<"Comment out spec">>
          },
          data => [],
          range => #{
              'end' => #{
                  character => 0,
                  line => 1
              },
              start => #{
                  character => 0,
                  line => 0
              }
          }
      }
  ],
  ?assertEqual(Expected, FilteredResult),
  ok.
