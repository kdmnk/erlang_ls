-module(wls_code_actions_SUITE).

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
-export([introduce_new_var/1]).
-export([move_fun_fun_call/1]).
-export([move_fun_fun_name/1]).
-export([extract_fun_one_expr/1]).
-export([extract_fun_more_expr/1]).
-export([new_macro_expr/1]).
-export([new_macro_pattern/1]).
-export([rename_fun/1]).
-export([rename_var/1]).
-export([fold_expression/1]).
-export([empty/1]).

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
      "generalise-fun",
      "fold-expression",
      "generalise-fun",
      "move-fun",
      "new-fun",
      "new-macro",
      "new-var",
      "rename-fun",
      "rename-var"]
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
  PrefixedCommand = els_command:with_prefix(<<"wrangler-generalise-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Generalise function">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"variable">>, 'text' => <<"New argument's name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Generalise function">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec empty(config()) ->  ok.
empty(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {1, 1},
                                to => {1, 1}}),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  Expected = [],
  ?assertEqual(Expected, Result),
  ok.

-spec introduce_new_var(config()) ->  ok.
introduce_new_var(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {11, 3},
                                to => {11, 15}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-new-var">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Introduce new variable">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"variable">>, 'text' => <<"Variable name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Introduce new variable">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec move_fun_fun_name(config()) ->  ok.
move_fun_fun_name(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {10, 4},
                                to => {10, 4}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-move-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Move function">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"file">>, 'text' => <<"File name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Move function">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec move_fun_fun_call(config()) ->  ok.
move_fun_fun_call(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {13, 9},
                               to => {13, 9}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-move-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
    <- Result, Command =:= PrefixedCommand],
  Expected =
  [ #{ command => #{
    title => <<"Move function">>,
    command => PrefixedCommand,
    arguments => [#{
      range => Range,
      uri   => Uri,
      user_input => #{'type' => <<"file">>, 'text' => <<"File name">>}
  }]},
      kind => <<"refactor">>,
      title => <<"Wrangler: Move function">>
    }
  ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec extract_fun_one_expr(config()) ->  ok.
extract_fun_one_expr(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {12, 14},
                                to => {12, 23}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-new-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Extract function">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"atom">>, 'text' => <<"The new function`s name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Extract function">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.
-spec extract_fun_more_expr(config()) ->  ok.
extract_fun_more_expr(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {12, 3},
                                to => {14, 43}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-new-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Extract function">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"atom">>, 'text' => <<"The new function`s name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Extract function">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec new_macro_expr(config()) ->  ok.
new_macro_expr(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {23, 3},
                                to => {23, 6}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-new-macro">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Introduce new macro">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"macro">>, 'text' => <<"Macro name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Introduce new macro">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec new_macro_pattern(config()) ->  ok.
new_macro_pattern(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {36, 5},
                                to => {36, 7}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-new-macro">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Introduce new macro">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"macro">>, 'text' => <<"Macro name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Introduce new macro">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

-spec rename_fun(config()) ->  ok.
rename_fun(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {25, 3},
                                to => {25, 3}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-rename-fun">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Rename Function">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"atom">>, 'text' => <<"New function name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Rename Function">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

rename_var(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {34, 6},
                                to => {34, 6}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-rename-var">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Rename Variable">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri,
       user_input => #{'type' => <<"variable">>, 'text' => <<"New variable name">>}
   }]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Rename Variable">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.

fold_expression(Config) ->
  Uri = ?config(wls_uri, Config),
  Range = els_protocol:range(#{from => {17, 2},
                                to => {17, 2}}),
  PrefixedCommand = els_command:with_prefix(<<"wrangler-fold-expression">>),
  #{result := Result} = els_client:document_codeaction(Uri, Range, []),
  FilteredResult = [L || #{ command := #{ command := Command }} = L
                        <- Result, Command =:= PrefixedCommand],
  Expected =
    [ #{ command => #{
     title => <<"Fold expression">>,
     command => PrefixedCommand,
     arguments => [#{
       range => Range,
       uri   => Uri}]},
        kind => <<"refactor">>,
        title => <<"Wrangler: Fold expression">>
      }
    ],
  ?assertEqual(Expected, FilteredResult),
  ok.
