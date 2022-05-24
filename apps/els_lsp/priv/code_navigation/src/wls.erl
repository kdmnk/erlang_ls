-module(wls).
-export([fun1/0]).
-export([fun2/0, fun3/0]).
-export([fun5/0]).
-export([fun6/0]).

-spec fun1() -> 'ok'.
fun1() -> ok.

fun2() ->
  do_something,
  file:write("asd.erl", <<"Hello World">>),
  A = fun4(5),
  file:write("asd.erl", <<"Hello World">>),
  fun4(A).

fun3() ->
  file:write("asd.erl", <<"Hello World">>).

-spec fun4(number()) ->  number().
fun4(B) ->
  file:write("asd.erl", <<"Hello World">>),
  B+1.

fun5() ->
  file:write("asd.erl", <<"Hello World">>),
  file:write("asd.erl", <<"Hello User">>).

fun6() ->
  file:write("asd.erl", <<"Hello World">>),
  file:write("asd.erl", <<"Hello User">>),
  fun4(5).

