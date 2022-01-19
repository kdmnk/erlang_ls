-module(test).

fun_to_fold() -> ok.

-spec test2() -> 'ok'.
test2() -> ok.

test3() ->
  case false of
    false -> ok;
    true -> nok
  end,
  ok.

test5() ->
  something1,
  something2,
  something3,
  ok,
  something4,
  something5,
  something6,
  something7.

