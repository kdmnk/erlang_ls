-module(wls_generalise_fun_SUITE).

%% CT Callbacks
-export([ suite/0
        , init_per_suite/1
        , end_per_suite/1
        , init_per_testcase/2
        , end_per_testcase/2
        , all/0
        ]).

%% Test cases
-export([generalise_fun_expression/1]).

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
    "enabled_refactorings" => ["generalise-fun"]
  }),
  Config2.

-spec end_per_testcase(atom(), config()) -> ok.
end_per_testcase(TestCase, Config) ->
  els_test_utils:end_per_testcase(TestCase, Config).


-spec generalise_fun_expression(config()) ->  ok.
generalise_fun_expression(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {8, 13},
                                to => {8, 15}}),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  Expected =
    [ #{ command => #{
     title => <<"Generalise function">>,
     command => els_command:with_prefix(<<"wrangler-generalise-fun">>),
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"variable">>, 'text' => <<"New argument's name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Generalise function">>
      }
    ],
  ?assertEqual(Expected, Result),
  ok.
