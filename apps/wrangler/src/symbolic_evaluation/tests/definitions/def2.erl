%% @private
-module(def2).
-export([bar/1]).

bar(N) when N > 0 -> N + bar(N-1);
bar(0) -> 0.

