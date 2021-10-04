%% @private
-module(utils_transform).
-export([transform_body/3,transform_body/4]).

%% Include files
-include("wrangler.hrl").
transform_body(Node, RulesFun, Scope) ->   
    transform_body(Node, RulesFun, {{[],[]}, Scope,[]}, unknown).

%%--------------------------------------------------------------------
%% @private
%% @doc
%% This function tries to transform the body as much as possible.
%% @spec(transform_body(Node::[syntaxTree()] | syntaxTree(),Info::[{{modulename(),functionname(),arity()},syntaxTree(),syntaxTree() | [syntaxTree()]}]) -> [syntaxTree()] | syntaxTree()).
%% @end
%%--------------------------------------------------------------------  
-spec(transform_body(Node::[syntaxTree()] | syntaxTree(),RulesFun::fun((_) -> any()),Info::[{{modulename(),functionname(),arity()},syntaxTree(),syntaxTree() | [syntaxTree()]}], FunDefInfo::{modulename(),functionname(),arity()}) -> [syntaxTree()] | syntaxTree()).
transform_body(Node,RulesFun,FunArgsWithScope,FunDefInfo) ->
    {FunArgs,Scope,BoundVars} = FunArgsWithScope,
    VarsInfo = core_unreferenced_assign:collector_var_expr_value(Scope),
    Subst = ?STOP_TD_TP((RulesFun({FunArgs,VarsInfo,BoundVars}, FunDefInfo)), Node),
    case Subst of
	{ok, NewNode@@} ->
	    Changed = ?PP(Node) /= ?PP(NewNode@@),
	    if
		Changed -> 
		    Match = ?MATCH(?T("f@(Args@@) when Guards@@ -> Body@@;"), Scope),
		    
		    if
			Match ->
			    NewScope = ?TO_AST("f@(Args@@) when Guards@@ -> NewNode@@;"),
			    transform_body(NewNode@@, RulesFun, {FunArgs, NewScope, api_refac:bound_vars(NewScope)}, FunDefInfo);
			true -> transform_body(NewNode@@, RulesFun, {FunArgs, Scope,BoundVars}, FunDefInfo)
		    end;
		true -> NewNode@@
	    end;
	_ -> Node
    end.
