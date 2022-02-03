-module(test).

fun_to_fold() ->
  file:write_file("alma.erl", <<"Hello world">>),
  ok.

-spec test2() -> 'ok'.
test2() -> ok.

test3() ->
  case false of
     false -> file:write_file("alma.erl", <<"Hello world">>),
    ok;
    true -> nok
  end,
  ok.

test5() ->
  something1,
  something2,
  something3,
  ok,
  something4,
   file:write_file("alma.erl", <<"Hello world">>),
  ok,
  something6,
  something7.
