%% Copyright 2015 Mariano Guerra
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.

-module(fn_to_erl).
-export([ast_to_ast/2, to_erl/3, to_erl/4, add_error/4, new_state/2, expected_got/2,
         lc_to_ast/4, state_map/3, kv_to_ast/3]).

% used by pretty printer
-export([map_op_reverse/1]).

-include("efene.hrl").

new_state(Module, Path) ->
    #{module => Module,
      path => Path,
      module_dir => filename:dirname(Path),
      errors => [],
      warnings => [],
      attrs => [],
      extensions => fn_exts:get_extensions(),
      macros => dict:new(),
      fns => [],
      fns_by_name => #{},
      level => 0}.

to_erl(Ast, Module, Path) ->
    to_erl(Ast, Module, Path, #{}).

to_erl(Ast, Module, Path, Opts) ->
    {EAst, State} = ast_to_ast(Ast, new_state(Module, Path)),
    case maps:get(replace_fn_holders, Opts, true) of
        true ->
            EAst1 = replace_fn_holders(EAst, State, [], #{}),
            {EAst1, State};
        false ->
            {EAst, State}
    end.

replace_fn_holders([], _State, Accum, _EmittedFns) ->
    lists:reverse(Accum);
replace_fn_holders([{fn, Name, Arity}|T], State=#{fns_by_name:=FnsByName},
                   Accum, EmittedFns) ->
    case maps:get({Name, Arity}, EmittedFns, undefined) of
        undefined ->
            FnKey = {Name, Arity},
            FnInfo = maps:get(FnKey, FnsByName),
            #{ast := Ast} = FnInfo,
            %% Ast is either a single function form or a [function, spec_attr]
            %% list; splice lists into the form list instead of nesting them so
            %% the result stays a flat list of forms (erl_syntax:form_list and
            %% friends reject nested lists, even though compile:forms tolerates
            %% them).
            Accum1 = case Ast of
                         L when is_list(L) -> lists:reverse(L, Accum);
                         _ -> [Ast|Accum]
                     end,
            replace_fn_holders(T, State, Accum1, EmittedFns#{FnKey => FnInfo});
        _ ->
            replace_fn_holders(T, State, Accum, EmittedFns)
    end;
replace_fn_holders([H|T], State, Accum, EmittedFns) ->
    replace_fn_holders(T, State, [H|Accum], EmittedFns).

ast_to_ast(Nodes, State) when is_list(Nodes) -> ast_to_ast(Nodes, [], State);

%-export([...]).
ast_to_ast({attr, Line, [?Atom(export=Name)], Params, noresult}, #{level := 0}=State) ->
    export_like_to_ast(Name, Line, Params, State);
%-export_type([...]).
ast_to_ast({attr, Line, [?Atom(export_type=Name)], Params, noresult}, #{level := 0}=State) ->
    export_like_to_ast(Name, Line, Params, State);
%-on_load(fname/<arity>).
ast_to_ast({attr, Line, [?Atom(on_load=Name)], [?O(_Line, '/', ?Atom(FunName), ?V(_ArLine, integer, Arity))], noresult}, #{level := 0}=State) ->
    R = {attribute, Line, Name, {FunName, Arity}},
    {R, State};
%-import(module_name, [...]).
ast_to_ast({attr, Line, [?Atom(import=Name)],
            [?Atom(ModuleName), ?S(_FaLine, list, FunNamesAndArities)], noresult},
           #{level := 0}=State) ->
    {EFuns, State1} = state_map(fun ast_to_export_fun/2, FunNamesAndArities, State),
    R = {attribute, Line, Name, {ModuleName, EFuns}},
    {R, State1};
%-vsn(<literal_term>).
ast_to_ast({attr, Line, [?Atom(vsn=Name)], [Vsn], noresult}, #{level := 0}=State) ->
    {EVsn, State1} = ast_to_ast(Vsn, State#{level := 1}),
    R = {attribute, Line, Name, erl_syntax:concrete(EVsn)},
    {R, State1#{level := 0}};
%-include(Path).
ast_to_ast({attr, Line, [?Atom(include_lib)], [?V(_, string, Path)], noresult},
           State) ->
    [Module | Rest] = filename:split(Path),
    case code:lib_dir(Module) of
        {error, bad_name} ->
            Reason = lib_not_found,
            %% TODO: add error pretty message
            State1 = add_error(State, error_parsing_include_file, Line, {Path, Reason}),
            R = {atom, Line, error},
            {R, State1};
        ModuleFullPath ->
            FullPath = filename:absname(filename:join([ModuleFullPath|Rest])),
            include_macro_file(Line, FullPath, State)
    end;
ast_to_ast({attr, Line, [?Atom(include)], [?V(_, string, Path)], noresult},
           State=#{module_dir := ModuleDir}) ->
    AbsPath = filename:absname(filename:join(ModuleDir, Path)),
    case filelib:is_regular(AbsPath) of
        true ->
            include_macro_file(Line, AbsPath, State);
        false ->
            Reason = file_not_found,
            %% TODO: add error pretty message
            State1 = add_error(State, error_parsing_include_file, Line, {AbsPath, Reason}),
            R = {atom, Line, error},
            {R, State1}
    end;

%-behavio[u]r(name)
ast_to_ast({attr, Line, [?Atom(AttrName)], [?Atom(BName)], noresult},
           #{level := 0}=State)
  when AttrName == behavior orelse AttrName == behaviour ->
    R = {attribute, Line, AttrName, BName},
    {R, State};
% top level function
ast_to_ast(?E(Line, fn, {Name, Attrs, ?E(_CLine, 'case', Cases)}),
           #{level := 0, fns := Fns, fns_by_name := FnsByName,
             module := Module, path := Path}=State) ->
    [FirstCase|_TCases] = Cases,
    {cmatch, _FCLine, {FCCond, _FCWhen, _FCBody}} = FirstCase,
    Arity = length(FCCond),
    {ok, FixedCases} = expand_case_else_match(Cases),
    BareName = unwrap(Name),
    StateLevel1 = State#{level := 1, function_name => BareName, function_arity => Arity},
    {EFixedCases, State1} = ast_to_ast(FixedCases, StateLevel1),
    EFn = {function, Line, BareName, Arity, EFixedCases},
    FnRef = {Name, Arity},
    {R, RestAttrs, State2} = case extract_spec_attr(FnRef, Attrs, [], nil, State1) of
                                 {found, ESpecAttr, IRestAttrs, State21} ->
                                     {[EFn, ESpecAttr], IRestAttrs, State21};
                                 {notfound, IRestAttrs, State21} ->
                                     {EFn, IRestAttrs, State21}
                             end,
    State3 = add_attributes(State2, fn, Line, {BareName, Arity}, Attrs),
    State4 = add_attributes(State3, fn_attrs, Line, {BareName, Arity}, RestAttrs),
    State5 = check_case_arities_equal(Cases, State4, Arity),
    FnInfo = #{name => BareName, arity => Arity, line => Line, ast => R,
               module => Module, module_path => Path, attrs => Attrs},

    State6 = check_fn_override(FnInfo, State5),
    State7 = State6#{level := 0,
                     fns := [FnInfo|Fns],
                     fns_by_name := FnsByName#{{BareName, Arity} => FnInfo}},
    {{fn, BareName, Arity}, State7};

% record declaration
ast_to_ast({attr, Line, [?Atom(record)], [?Atom(RecordName)], ?S(_TLine, tuple, Fields)},
           #{level := 0}=State) ->
    {RFields, State1} = lists:mapfoldl(fun to_record_field_decl/2,
                                       State#{level := 1}, Fields),
    R = {attribute, Line, record, {RecordName, RFields}},
    {R, State1#{level := 0}};

% type and opaque without result, error
ast_to_ast({attr, Line, [?Atom(Type)], _Params, noresult}=Ast, #{level := 0}=State)
  when Type == type orelse Type == opaque ->
    invalid_type_declaration(State, Line, Ast);
% type and opaque without params, error
ast_to_ast({attr, Line, [?Atom(Type)], noparams, _Result}=Ast, #{level := 0}=State)
  when Type == type orelse Type == opaque ->
    invalid_type_declaration(State, Line, Ast);
% type and opaque attributes
ast_to_ast({attr, _Line, [?Atom(Type)], _Params, _Result}=Ast, #{level := 0}=State)
  when Type == type orelse Type == opaque ->
    fn_spec:type_to_spec(Ast, State);

% ^<path> <expr>
ast_to_ast(?T(Line, Path, Ast), State) ->
    handle_tag(Line, "expr_", Path, Path, Ast, State);

% #<path> <val>
ast_to_ast(?LTag(Line, Path, Ast), State) ->
    handle_tag(Line, "val_", Path, Path, Ast, State);

ast_to_ast(Ast, #{level := 0}=State) ->
    Line = element(2, Ast),
    State1 = add_error(State, invalid_top_level_expression, Line, {ast, Ast}),
    R = {atom, Line, error},
    {R, State1};

ast_to_ast(?E(_Line, call_do, {Place, Call, Fun}), State) ->
    with_childs(State, Call, Fun,
                fun ({call, CallLine, FCall, Args}, EFun) ->
                        AllArgs = case Place of
                                      first -> [EFun|Args];
                                      last  -> Args ++ [EFun]
                                  end,
                        {call, CallLine, FCall, AllArgs}
                end);

% -> and ->>
ast_to_ast(?E(_Line, call_thread, {InitialVal, Calls}), State) ->
    Threaded = lists:foldl(fun (Current, Accum) ->
                                   {Pos, Call} = Current,
                                   ?E(CallLine, call, {Fun, Args}) = Call,
                                   NewArgs = case Pos of
                                                 first -> [Accum|Args];
                                                 last -> Args ++ [Accum]
                                             end,
                                   ?E(CallLine, call, {Fun, NewArgs})
                           end, InitialVal, Calls),
    ast_to_ast(Threaded, State);

% list
ast_to_ast(?S(Line, list, Val), State) ->
    list_to_cons_list(Line, Val, State);

% <var>#<map>
ast_to_ast(?S(Line, map=Type, {Var, KVs}), State) ->
    {EVar, State1} = ast_to_ast(Var, State),
    {Items, State2} = state_map(fun to_map_field/2, KVs, State1),
    R = {Type, Line, EVar, Items},
    {R, State2};
% <map>
ast_to_ast(?S(Line, map=Type, KVs), State) ->
    {Items, State1} = state_map(fun to_map_field/2, KVs, State),
    R = {Type, Line, Items},
    {R, State1};

% tuple
ast_to_ast(?S(Line, tuple=Type, Val), State)   ->
    {EVal, State1} = ast_to_ast(Val, State),
    {{Type, Line, EVal}, State1};

% <val> :: <val>
ast_to_ast(?S(Line, cons=Type, {H, T}), State) ->
    with_childs(State, H, T, fun (EH, ET) -> {Type, Line, EH, ET} end);

% function reference
ast_to_ast(?V(Line, fn_ref, {[Mod, Fun], Arity}), State) ->
    with_childs(State, Mod, Fun, Arity,
                fun (EMod, EFun, EArity) ->
                        {'fun', Line, {function, EMod, EFun, EArity}}
                end);

% function reference
ast_to_ast(?V(Line, fn_ref, {[?Var(Fun)=FunAst], Arity}), State) ->
    State1 = add_error(State, invalid_fn_ref, Line,
                       expected_got("atom", {ast, FunAst})),
    R = {'fun', Line, {function, Fun, unwrap(Arity)}},
    {R, State1};

% function reference
ast_to_ast(?V(Line, fn_ref, {[Fun], Arity}), State) ->
    R = {'fun', Line, {function, unwrap(Fun), unwrap(Arity)}},
    {R, State};

% when
ast_to_ast(?E(Line, 'when', Clauses), State) ->
    {EClauses, State1} = ast_to_ast(Clauses, State),
    R = {'if', Line, EClauses},
    {R, State1};

% when condition
ast_to_ast({wcond, Line, Cond, Body}, State) ->
    {ECond, State1} = when_to_ast(Cond, State),
    {EBody, State2} = ast_to_ast(Body, State1),
    R = {clause, Line, [], ECond, EBody},
    {R, State2};

% when else
ast_to_ast({welse, Line, Body}, State) ->
    {EBody, State1} = ast_to_ast(Body, State),
    R = {clause, Line, [], [[{atom, Line, true}]], EBody},
    {R, State1};

% list comprehension
ast_to_ast(?E(Line, 'for', {Qualifiers, Body}), State) ->
    {Items, EBody, State1} = lc_to_ast(Line, Qualifiers, Body, State),
    R = {lc, Line, EBody, Items},
    {R, State1};

% try expression
ast_to_ast(?E(Line, 'try', {Body, Catch, After}), State) ->
    {EBody, State1} = ast_to_ast(Body, State),
    {ECatch, State2} = case Catch of
                           ?E(_CLine, 'case', Clauses) ->
                               state_map(fun ast_to_catch/2, Clauses, State);
                           nocatch -> {[], State1}
                       end,

    {EAfter, State3} = case After of
                           noafter -> {[], State2};
                           AfterBody -> ast_to_ast(AfterBody, State2)
                       end,
    R = {'try', Line, EBody, [], ECatch, EAfter},
    {R, State3};

% receive without case clauses
ast_to_ast(?E(Line, 'receive', {[], {After, AfterBody}}), State) ->
    with_childs(State, After, AfterBody,
                fun(EAfter, EAfterBody) ->
                        {'receive', Line, [], EAfter, EAfterBody}
                end);

% receive with case clauses and no after
ast_to_ast(?E(Line, 'receive', {?E(_CLine, 'case', Clauses), noafter}), State) ->
    {EClauses, State1} = ast_to_ast(Clauses, State),
    TupleClauses = lists:map(fun to_tuple_clause/1, EClauses),
    R= {'receive', Line, TupleClauses},
    {R, State1};

% receive with case clauses and after
ast_to_ast(?E(Line, 'receive', {?E(_CLine, 'case', Clauses), {After, AfterBody}}), State) ->
    with_childs(State, Clauses, After, AfterBody,
                fun(EClauses, EAfter, EAfterBody) ->
                        TupleClauses = lists:map(fun to_tuple_clause/1, EClauses),
                        {'receive', Line, TupleClauses, EAfter, EAfterBody}
                end);

% match
ast_to_ast(?E(Line, switch, {Value, ?E(_CaseLine, 'case', Clauses)}), State) ->
    with_childs(State, Clauses, Value,
                fun(EClauses, EValue) ->
                        TupleClauses = lists:map(fun to_tuple_clause/1, EClauses),
                        {'case', Line, EValue, TupleClauses}
                end);

% match clause
ast_to_ast({cmatch, Line, {Conds, When, Body}}, State) ->
    {EConds, State1} = ast_to_ast(Conds, State),
    {EWhen, State2} = when_to_ast(When, State1),
    {EBody, State3} = ast_to_ast(Body, State2),
    R = {clause, Line, EConds, EWhen, EBody},
    {R, State3};

% match else clause
ast_to_ast({celse, Line, Body}, State) ->
    {EBody, State1} = ast_to_ast(Body, State),
    R = {clause, Line, [{var, Line, '_'}], [], EBody},
    {R, State1};

% begin
ast_to_ast(?E(Line, 'begin', Body), State) ->
    {EBody, State1} = ast_to_ast(Body, State),
    R = {block, Line, EBody},
    {R, State1};

% fn
ast_to_ast(?E(Line, fn, ?E(_CLine, 'case', Cases)), State) ->
    {ok, FixedCases} = expand_case_else_match(Cases),
    {EFixedCases, State1} = ast_to_ast(FixedCases, State),
    R = {'fun', Line, {clauses, EFixedCases}},
    {R, State1};

% named fn
ast_to_ast(?E(Line, fn, {?V(_VLine, var, FName), ?E(_CLine, 'case', Cases)}), State) ->
    {ok, FixedCases} = expand_case_else_match(Cases),
    {EFixedCases, State1} = ast_to_ast(FixedCases, State),
    R = {named_fun, Line, FName, EFixedCases},
    {R, State1};

% call
ast_to_ast(?E(Line, call, {[Mod, Fun], Args}), State) ->
    with_childs(State, Mod, Fun, Args,
                fun (EMod, EFun, EArgs) ->
                        {call, Line, {remote, Line, EMod, EFun}, EArgs}
                end);

% call
ast_to_ast(?E(Line, call, {[Fun], Args}), State) ->
    with_childs(State, Fun, Args,
                fun (EFun, EArgs) -> {call, Line, EFun, EArgs} end);

% =
ast_to_ast(?O(Line, '=', Left, Right), State) ->
    with_childs(State, Left, Right,
                fun (ELeft, ERight) -> {match, Line, ELeft, ERight} end);

% ops
ast_to_ast(?O(Line, Op, Left, Right), State) ->
    with_childs(State, Left, Right,
                fun (ELeft, ERight) -> {op, Line, map_op(Op), ELeft, ERight} end);

% values
ast_to_ast(?V(Line, atom=Type, Val), State)    -> {{Type, Line, Val}, State};
ast_to_ast(?V(Line, integer=Type, Val), State) -> {{Type, Line, Val}, State};
ast_to_ast(?V(Line, float=Type, Val), State)   -> {{Type, Line, Val}, State};
ast_to_ast(?V(Line, boolean, Val), State)      -> {{atom, Line, Val}, State};
ast_to_ast(?V(Line, var=Type, Val), State)     -> {{Type, Line, Val}, State};
ast_to_ast(?V(Line, string=Type, Val), State)  -> {{Type, Line, Val}, State};
ast_to_ast(?V(Line, bstring, Val), State) ->
    R = {bin, Line, [{bin_element, Line, {string, Line, Val}, default, default}]},
    {R, State};

% unary ops
ast_to_ast(?UO(Line, Op, Val), State) ->
    {EVal, State1} = ast_to_ast(Val, State),
    R = {op, Line, map_op(Op), EVal},
    {R, State1};

ast_to_ast(Ast, State) ->
    Line = element(2, Ast),
    State1 = add_error(State, invalid_expression, Line, {ast, Ast}),
    R = {atom, Line, error},
    {R, State1}.


ast_to_ast([], Accum, State) ->
    {lists:reverse(Accum), State};
ast_to_ast([H|T], Accum, State) ->
    {EH, State1} = ast_to_ast(H, State),
    NewAccum = if is_list(EH) -> EH ++ Accum;
                  EH == 'fn compiler ignore' -> Accum;
                  true -> [EH|Accum]
               end,
    ast_to_ast(T, NewAccum, State1).

map_op('=') -> '=';
map_op('+') -> '+';
map_op('-') -> '-';
map_op('*') -> '*';
map_op('/') -> '/';
map_op('//') -> 'div';
map_op('%') -> 'rem';
map_op('|') -> 'bor';
map_op('&') -> 'band';
map_op('^') -> 'bxor';
map_op('>>') -> 'bsr';
map_op('<<') -> 'bsl';
map_op('~') -> 'bnot';
map_op('and') -> 'andalso';
map_op('andd') -> 'and';
map_op('or') -> 'orelse';
map_op('orr') -> 'or';
map_op('xor') -> 'xor';
map_op('!') -> '!';
map_op('not') -> 'not';
map_op('++') -> '++';
map_op('--') -> '--';
map_op('<') -> '<';
map_op('<=') -> '=<';
map_op('>') -> '>';
map_op('>=') -> '>=';
map_op('==') -> '==';
map_op('is') -> '=:=';
map_op('!=') -> '/=';
map_op('isnt') -> '=/='.

map_op_reverse('=') -> '=';
map_op_reverse('+') -> '+';
map_op_reverse('-') -> '-';
map_op_reverse('*') -> '*';
map_op_reverse('/') -> '/';
map_op_reverse('div') -> '//';
map_op_reverse('rem') -> '%';
map_op_reverse('bor') -> '|';
map_op_reverse('band') -> '&';
map_op_reverse('bxor') -> '^';
map_op_reverse('bsr') -> '>>';
map_op_reverse('bsl') -> '<<';
map_op_reverse('bnot') -> '~';
map_op_reverse('andalso') -> 'and';
map_op_reverse('and') -> 'andd';
map_op_reverse('orelse') -> 'or';
map_op_reverse('or') -> 'orr';
map_op_reverse('xor') -> 'xor';
map_op_reverse('!') -> '!';
map_op_reverse('not') -> 'not';
map_op_reverse('++') -> '++';
map_op_reverse('--') -> '--';
map_op_reverse('<') -> '<';
map_op_reverse('=<') -> '<=';
map_op_reverse('>') -> '>';
map_op_reverse('>=') -> '>=';
map_op_reverse('==') -> '==';
map_op_reverse('=:=') -> 'is';
map_op_reverse('/=') -> '!=';
map_op_reverse('=/=') -> 'isnt'.

list_to_cons_list(Line, Val, State) ->
    list_to_cons_list_r(Line, lists:reverse(Val), {nil, Line}, State).

list_to_cons_list_r(_Line, [], Cons, State) ->
    {Cons, State};

list_to_cons_list_r(Line, [H|T], Cons, State) ->
    {EH, State1} = ast_to_ast(H, State),
    list_to_cons_list_r(Line, T, {cons, Line, EH, Cons}, State1).

ast_to_export_fun(?O(_Line, '/', ?Atom(FunName), ?V(_ArLine, integer, Arity)), State) ->
    R = {FunName, Arity},
    {R, State};
ast_to_export_fun(Ast, State) ->
    Line = element(2, Ast),
    State1 = add_error(State, invalid_export, Line,
                       expected_got("funname/Arity", {ast, Ast})),
    {{atom, Line, error}, State1}.

ast_to_catch({cmatch, Line, {[Match], When, Body}}, State) ->
    cmatch_to_catch(Line, ?V(Line, atom, throw), Match, When, Body, State);
ast_to_catch({cmatch, Line, {[?V(_ALine, atom, throw=_ClassName)=CN, Match], When, Body}}, State) ->
    cmatch_to_catch(Line, CN, Match, When, Body, State);
ast_to_catch({cmatch, Line, {[?V(_ALine, atom, error=_ClassName)=CN, Match], When, Body}}, State) ->
    cmatch_to_catch(Line, CN, Match, When, Body, State);
ast_to_catch({cmatch, Line, {[?V(_ALine, atom, exit=_ClassName)=CN, Match], When, Body}}, State) ->
    cmatch_to_catch(Line, CN, Match, When, Body, State);
ast_to_catch({cmatch, Line, {[?V(_ALine, var, _VarName)=Var, Match], When, Body}}, State) ->
    cmatch_to_catch(Line, Var, Match, When, Body, State);
ast_to_catch({celse, Line, Body}, State) ->
    EMatch = {tuple, Line, [{var, Line, '_'}, {var, Line, '_'}, {var, Line, '_'}]},
    {EBody, State1} = ast_to_ast(Body, State),
    R = {clause, Line, [EMatch], [], EBody},
    {R, State1};
ast_to_catch({cmatch, Line, {Match, _When, _Body}}, State) ->
    State1 = add_error(State, invalid_catch, Line,
                       expected_got("throw:T, error:E, exit:X or T",
                                    {ast, ?S(Line, tuple, Match)})),
    {{atom, Line, error}, State1}.

cmatch_to_catch(Line, Class, Match, When, Body, State) ->
    {EClass, State1} = ast_to_ast(Class, State),
    {EMatch, State2} = ast_to_ast(Match, State1),
    ETupleMatch = {tuple, Line, [EClass, EMatch, {var, Line, '_'}]},
    {EBody, State3} = ast_to_ast(Body, State2),
    {EWhen, State4} = when_to_ast(When, State3),
    R = {clause, Line, [ETupleMatch], EWhen, EBody},
    {R, State4}.

when_to_ast(nowhen, State) -> {[], State};
when_to_ast(When, State) when is_list(When) ->
    state_map(fun when_to_ast/2, When, State);
when_to_ast(When, State) ->
    ast_to_ast(When, State).

kv_to_ast(Key, Val, State) ->
    with_childs(State, Key, Val, fun (EKey, EVal) -> {EKey, EVal} end).

to_map_field({kv, Line, Key, Val}, State) ->
    {{EKey, EVal}, State1} = kv_to_ast(Key, Val, State),
    R = {map_field_assoc, Line, EKey, EVal},
    {R, State1};
to_map_field({kvmatch, Line, Key, Val}, State) ->
    {{EKey, EVal}, State1} = kv_to_ast(Key, Val, State),
    R = {map_field_exact, Line, EKey, EVal},
    {R, State1}.

% erlang ast
% NOTE for now empty case in switch matches the empty tuple
to_tuple_clause({clause, Line, [], Guard, Body}) ->
    {clause, Line, [{tuple, Line, []}], Guard, Body};
to_tuple_clause({clause, _Line, [_Match], _Guard, _Body}=Ast) ->
    Ast;
to_tuple_clause({clause, Line, Matches, Guard, Body}) ->
    {clause, Line, [{tuple, Line, Matches}], Guard, Body}.

for_qualifier_to_ast({filter, Ast}, State) -> ast_to_ast(Ast, State);
for_qualifier_to_ast({Gen, Line, Left, Right}, State)
  when Gen =:= generate orelse Gen =:= b_generate ->
    {{ELeft, ERight}, State1} = kv_to_ast(Left, Right, State),
    R = {generate, Line, ELeft, ERight},
    {R, State1}.

expand_case_else_match([{cmatch, _Line, {Matches, _When, _Body}}=H|T]) ->
    Arity = length(Matches),
    expand_case_else_match(T, Arity, [H]).

expand_case_else_match([], _Arity, Accum) ->
    {ok, lists:reverse(Accum)};
expand_case_else_match([{celse, Line, Body}|T], Arity, Accum) ->
    Matches = [?V(Line, var, '_') || _ <- lists:seq(1, Arity)],
    NewElse = {cmatch, Line, {Matches, nowhen, Body}},
    expand_case_else_match(T, Arity, [NewElse|Accum]);
expand_case_else_match([H|T], Arity, Accum) ->
    expand_case_else_match(T, Arity, [H|Accum]).

state_map(Fun, Seq, State) ->
    {R, FState} = lists:foldl(fun (Item, {Accum, StateIn}) ->
                                      {R, State1} = Fun(Item, StateIn),
                                      {[R|Accum], State1}
                              end,  {[], State}, Seq),
    {lists:reverse(R), FState}.

add_attributes(#{attrs := AttrList}=State, Type, Line, Name, Attrs) ->
    NewAttrList = [{Type, Line, Name, Attrs}|AttrList],
    State#{attrs := NewAttrList}.

expected_got(Expected, Got) -> {expected, Expected, got, Got}.

check_case_arities_equal([{cmatch, Line, {Cond, _When, _Body}}|T], State, Arity) ->
    CaseArity = length(Cond),
    if CaseArity == Arity -> check_case_arities_equal(T, State, Arity);
       true ->
           State1 = add_error(State, case_mismatch, Line,
                              expected_got(Arity, CaseArity)),
           check_case_arities_equal(T, State1, Arity)
    end;
check_case_arities_equal([{celse, _Line, _Body}|T], State, Arity) ->
    check_case_arities_equal(T, State, Arity);
check_case_arities_equal([], State, _Arity) -> State.

lc_to_ast(Line, Qualifiers, Body, State) ->
    {EBody, State1} = case Body of
                          [Node] -> ast_to_ast(Node, State);
                          Nodes ->
                              {EBlockBody, S1} = ast_to_ast(Nodes, State),
                              Ri = {block, Line, EBlockBody},
                              {Ri, S1}
                      end,
    {Items, State2} = state_map(fun for_qualifier_to_ast/2, Qualifiers, State1),
    {Items, EBody, State2}.

add_error(#{errors:=Errors}=State, ErrType, Line, Detail) ->
    Error = {ErrType, Line, Detail},
    NewErrors = [Error|Errors],
    State#{errors := NewErrors}.

add_warning(#{warnings:=Warns}=State, WarnType, Line, Detail) ->
    Warn = {WarnType, Line, Detail},
    NewWarns = [Warn|Warns],
    State#{warnings := NewWarns}.

unwrap(?V(_Line, _Type, Val)) -> Val.

with_childs(State, Ast1, Ast2, Fun) ->
    {EAst1, State1} = ast_to_ast(Ast1, State),
    {EAst2, State2} = ast_to_ast(Ast2, State1),
    {Fun(EAst1, EAst2), State2}.

with_childs(State, Ast1, Ast2, Ast3, Fun) ->
    {EAst1, State1} = ast_to_ast(Ast1, State),
    {EAst2, State2} = ast_to_ast(Ast2, State1),
    {EAst3, State3} = ast_to_ast(Ast3, State2),
    {Fun(EAst1, EAst2, EAst3), State3}.

invalid_type_declaration(State, Line, Ast) ->
    State1 = add_error(State, invalid_type_declaration, Line, {ast, Ast}),
    R = {atom, Line, error},
    {R, State1}.

extract_spec_attr({Name, Arity}, [], Accum, nil, State) ->
    {notfound, make_fun_attrs(Name, Arity, Accum), State};
extract_spec_attr({Name, Arity}=FnRef, [], Accum, SpecAttr, State) ->
    {ESpecAttr, State1} = parse_spec_attr(FnRef, SpecAttr, State),
    {found, ESpecAttr, make_fun_attrs(Name, Arity, Accum), State1};
extract_spec_attr(FnRef, [{attr, _Line, [?Atom(spec)], _Params, _Result}=SpecAttr|T],
                  Accum, nil, State) ->
    extract_spec_attr(FnRef, T, Accum, SpecAttr, State);
extract_spec_attr(FnRef, [{attr, Line, [?Atom(spec)], _Params, _Result}=SpecAttr|T],
                  Accum, ExistingSpecAttr, State) ->
    State1 = add_error(State, duplicated_function_spec, Line, {ast, SpecAttr}),
    extract_spec_attr(FnRef, T, Accum, ExistingSpecAttr, State1);
extract_spec_attr(FnRef, [{attr, Line, Name, Params, Result}|T],
                  Accum, SpecAttr, State) ->
    {ENameList, State1} = ast_to_ast(Name, State),
    EName = ast_list_to_cons(lists:reverse(ENameList), Line),
    {NParams, State2} = if Params == noparams -> {[], State1};
                           true -> {Params, State1}
                        end,
    {EResult, State3} = if Result == noresult -> {{nil, Line}, State2};
                           true -> ast_to_ast(Result, State2)
                        end,
    {EParams, State4} = list_to_cons_list(Line, NParams, State3),
    EAttr = {tuple, Line, [EName, {tuple, Line, [EParams, EResult]}]},
    extract_spec_attr(FnRef, T, [EAttr|Accum], SpecAttr, State4).

parse_spec_attr({?Atom(Name), Arity}, {attr, Line, [?Atom(spec)], Args, Return},
                State) ->
    fn_spec:parse_spec_attr(Name, Arity, Line, Args, Return, State).

export_like_to_ast(Name, Line, Params, State) ->
    {EFuns, State1} = state_map(fun ast_to_export_fun/2, Params, State),
    R = {attribute, Line, Name, EFuns},
    {R, State1}.

% assumes Items is reversed
ast_list_to_cons([], Line) ->
    {nil, Line};
ast_list_to_cons(Items, Line) ->
    ast_list_to_cons(Items, Line, {nil, Line}).

ast_list_to_cons([], _Line, Cons) ->
    Cons;
ast_list_to_cons([H|T], Line, Cons) when is_list(T) ->
    ast_list_to_cons(T, Line, {cons, Line, maybe_consify_head(H, Line), Cons});
ast_list_to_cons([H|T], Line, Cons) ->
    {cons, Line, maybe_consify_head(H, Line), {cons, Line, T, Cons}}.

maybe_consify_head(H, Line) when is_list(H) -> ast_list_to_cons(H, Line);
maybe_consify_head(H, _Line) -> H.

make_fun_attrs(?V(Line, atom, Name), Arity, Accum) ->
    ConsAttrs = {tuple, Line, [{atom, Line, Name}, {integer, Line, Arity},
                               ast_list_to_cons(Accum, Line)]},
    {attribute, Line, fn_attrs, erl_syntax:concrete(ConsAttrs)}.

path_to_ext_string(Path) ->
    Parts = lists:map(fun (?Var(Name)) -> "var_" ++ atom_to_list(Name);
                          (?Atom(Name)) -> "atom_" ++ atom_to_list(Name)
                      end, Path),
    string:join(Parts, "_").

handle_tag(Line, _Prefix, [], _FullPath, Ast, State) ->
    add_error(State, tag_handler_not_found, Line, {ast, Ast});

handle_tag(Line, Prefix, Path, FullPath, Ast, State=#{extensions := Extensions}) ->
    ExtStr = Prefix ++ path_to_ext_string(Path),
    case fn_exts:handle(ExtStr, FullPath, Ast, State, Extensions) of
        {error, notfound} ->
            % retry dropping the last item in path, this will try from
            % most specific to most general, when all path items dropped
            % it will fail with tag_handler_not_found
            handle_tag(Line, Prefix, lists:droplast(Path), FullPath, Ast, State);
        {error, Reason} when is_atom(Reason) -> add_error(State, Reason, Line, nil);
        {error, {Reason, Data}} -> add_error(State, Reason, Line, Data);
        Other -> Other
    end.

to_record_field_decl(?O(Line, '=', ?V(FLine, atom, FieldName), ?O(_OLine, is, Val, Type)), State) ->
    {EType, State1} = fn_spec:parse_type_value(Type, State),
    {EVal, State2} = ast_to_ast(Val, State1),
    R = {typed_record_field, {record_field, Line, {atom, FLine, FieldName}, EVal}, EType},
    {R, State2};
to_record_field_decl(?O(Line, is, ?V(FLine, 'atom', FieldName), Type), State) ->
    {EType, State1} = fn_spec:parse_type_value(Type, State),
    R = {typed_record_field, {record_field, Line, {atom, FLine, FieldName}}, EType},
    {R, State1};
to_record_field_decl(?O(Line, '=', ?V(FLine, atom, FieldName), Val), State) ->
    {EVal, State1} = ast_to_ast(Val, State),
    R = {record_field, Line, {atom, FLine, FieldName}, EVal},
    {R, State1};
to_record_field_decl(?V(Line, 'atom', FieldName), State) ->
    R = {record_field, Line, {atom, Line, FieldName}},
    {R, State};
to_record_field_decl(Other, State) ->
    Line = element(2, Other),
    State1 = add_error(State, bad_record_field_decl, Line,
                       expected_got("atom or assignment", {ast, Other})),
    {{atom, Line, error}, State1}.

include_macro_file(Line, Path, State) ->
    case filename:extension(Path) of
        ".hfn" ->
            include_macro_file_fn(Line, Path, State);
        _ ->
            include_macro_file_erl(Line, Path, State)
    end.

include_macro_file_fn(Line, Path, #{level := 0, path := ModulePath}=State0) ->
    case efene:to_erl_ast(Path, #{replace_fn_holders => false}) of
        % TODO: merge errors, declared functions and so on
        {ok, {Ast, HfnState}} ->
            StartLineAttr = {attribute, Line, file, {Path, 1}},
            AstWithLine = [StartLineAttr|Ast],
            EndLineAttr = {attribute, Line, file, {ModulePath, Line}},
            State = merge_included_state(State0, HfnState),
            {[EndLineAttr|lists:reverse(AstWithLine)], State};
        {error, Reason} ->
            State = add_error(State0, error_parsing_include_file, Line, {Path, Reason}),
            R = {atom, Line, error},
            {R, State}
    end.

merge_included_state(CurState=#{fns := Fns, fns_by_name := FnsByName,
                                errors := CErrors, warnings := CWarns},
                     #{fns := InclFns, fns_by_name := InclFnsByName,
                       errors := IErrors, warnings := IWarns}) ->
    NewFns = InclFns ++ Fns,
    NewErrors = IErrors ++ CErrors,
    NewWarns = IWarns ++ CWarns,
    NewFnsByName = maps:merge(FnsByName, InclFnsByName),
    CurState#{fns := NewFns, fns_by_name := NewFnsByName,
              errors := NewErrors, warnings := NewWarns}.

include_macro_file_erl(Line, Path, #{level := 0, path := ModulePath, macros := Macros}=State) ->
    case fn_erl_macro:parse_to_include(Path) of
        {ok, Ast, FileMacros} ->
            NewMacros = dict:merge(fun(_Key, _Value1, Value2) -> Value2 end,
                                   Macros, FileMacros),
            {[{attribute, Line, file, {ModulePath, Line}}|lists:reverse(Ast)],
             State#{macros := NewMacros}};
        {error, Reason} ->
            State1 = add_error(State, error_parsing_include_file, Line, {Path, Reason}),
            R = {atom, Line, error},
            {R, State1}
    end.

check_fn_override(#{name := Name, arity := Arity, line := Line, attrs := Attrs},
                  State=#{fns_by_name := FnsByName}) ->
    Key = {Name, Arity},
    case maps:get(Key, FnsByName, undefined) of
        undefined ->
            State;
        FnInfo ->
            case has_override_attr(Attrs) of
                true -> State;
                false ->
                    add_warning(State, implicit_override, Line,
                                #{fn => Key, prev_fn => FnInfo})
            end
    end.

is_override_attr({attr, _, [{val, _, atom, override}], noparams, noresult}) ->
    true;
is_override_attr(_) ->
    false.

has_override_attr(Attrs) ->
    case lists:filter(fun is_override_attr/1, Attrs) of
        [] -> false;
        _ -> true
    end.
