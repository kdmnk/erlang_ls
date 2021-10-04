-module(els_code_action_provider).

-behaviour(els_provider).

-export([ handle_request/2
        , is_enabled/0
        ]).

-include("els_lsp.hrl").

-type state() :: any().

%%==============================================================================
%% els_provider functions
%%==============================================================================

-spec is_enabled() -> boolean().
is_enabled() -> true.

-spec handle_request(any(), state()) -> {any(), state()}.
handle_request({document_codeaction, Params}, State) ->
  #{ <<"textDocument">> := #{ <<"uri">> := Uri}
   , <<"range">>        := RangeLSP
   , <<"context">>      := Context } = Params,
  Result = code_actions(Uri, RangeLSP, Context),
  {Result, State}.

%%==============================================================================
%% Internal Functions
%%==============================================================================


%% @doc Result: `(Command | CodeAction)[] | null'
-spec code_actions(uri(), range(), code_action_context()) -> [map()].
code_actions(Uri, Range, _Context) ->
  %% #{ <<"diagnostics">> := Diagnostics } = Context,

  #{ <<"start">> := #{ <<"character">> := _StartCol
                     , <<"line">>      := StartLine }
   , <<"end">>   := #{ <<"character">> := _EndCol
                     , <<"line">>      := EndLine }
   } = Range,
  
  [#{ title => <<"Do something">>
    , kind => ?CODE_ACTION_KIND_REFACTOR
    , command => 
       els_command:make_command( <<"Do something">>
                               , <<"code_action_do_something">>
                               , [#{ uri   => Uri
                                   , from  => StartLine
                                   , to    => EndLine }])
   }].

%%------------------------------------------------------------------------------
