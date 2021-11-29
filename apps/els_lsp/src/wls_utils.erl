-module(wls_utils).

-export([range/1, pos/1]).

-type path() :: binary().
-type wrangler_position() :: {els_core:line(), els_core:coloumn()}.
-type wrangler_range() :: {wrangler_position(), wrangler_position()}.
-export_type([path/0]).

-spec range(els_core:range()) -> wrangler_range().
range(Range) ->
  #{<<"start">> := StartPos
  , <<"end">>   := EndPos} = Range,
  {pos(StartPos), pos(EndPos)}.


-spec pos(els_core:position()) -> wrangler_position().
pos(Pos) ->
  #{<<"character">> := Col, <<"line">> := Line} = Pos,
  {Line+1, Col+1}.
