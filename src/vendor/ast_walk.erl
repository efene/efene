%% code based on erl_id_trans
-module(ast_walk).

%% A module to walk and maybe modify ast nodes

%% This module only traverses legal Erlang code. This is most noticeable
%% in guards where only a limited number of expressions are allowed.
%% N.B. if this module is to be used as a basis for tranforms then
%% all the error cases must be handled otherwise this module just crashes!

-export([walk/3, expr/3, exprs/3, forms/3, form/3]).
-export([id_walker/2, print_walker/2]).

id_walker(State, Node) ->
	{Node, State}.

print_walker(State, Node) ->
	io:format("~p~n~n", [Node]),
	{Node, State}.

walk(Forms, Fun, State) ->
    forms(Forms, Fun, State).

%% forms(Fs) -> lists:map(fun (F) -> form(F) end, Fs).

forms([F0|Fs0], Fun, State) ->
    {F1, State1} = form(F0, Fun, State),
    {Fs1, State2} = forms(Fs0, Fun, State1),
    case is_list(F1) of
        true -> {F1 ++ Fs1, State2};
        false -> {[F1|Fs1], State2}
    end;
forms([], _Fun, State) -> {[], State}.

%% -type form(Form) -> Form.
%%  Here we show every known form and valid internal structure. We do not
%%  that the ordering is correct!

%% First the various attributes.
form(Node={attribute, _Line, module, _Mod}, Fun, State) ->
    Fun(State, Node);
form(Node={attribute, _Line, file, {_File, _Line1}}, Fun, State) ->	%This is valid anywhere.
    Fun(State, Node);
form({attribute, Line, export, Es0}, Fun, State) ->
    {Es1, State1} = farity_list(Es0, Fun, State),
    Fun(State1, {attribute,Line,export,Es1});
form({attribute, Line, import, {Mod, Is0}}, Fun, State) ->
    {Is1, State1} = farity_list(Is0, Fun, State),
    Fun(State1, {attribute,Line,import,{Mod,Is1}});
form(Node={attribute, _Line, compile, _C}, Fun, State) ->
    Fun(State, Node);
form({attribute, Line, record, {Name, Defs0}}, Fun, State) ->
    {Defs1, State1} = record_defs(Defs0, Fun, State),
    Fun(State1, {attribute,Line,record,{Name,Defs1}});
form(Node={attribute, _Line, asm, {function, _N, _A, _Code}}, Fun, State) ->
    Fun(State, Node);
form(Node={attribute, _Line, _Attr, _Val}, Fun, State) -> %The general attribute.
    Fun(State, Node);
form({function, Line, Name0, Arity0, Clauses0}, Fun, State) ->
    {_, State1} = Fun(State, {pre, {function,Line,Name0,Arity0,Clauses0}}),
    {{Name,Arity,Clauses}, State2} = function(Name0, Arity0, Clauses0, Fun, State1),
    Fun(State2, {function,Line,Name,Arity,Clauses});
% Mnemosyne, ignore...
form(Node={rule, _Line, _Name, _Arity, _Body}, _Fun, State) ->
    {Node, State}; % Dont dig into this
%% Extra forms from the parser.
form({error,E}, Fun, State) -> Fun(State, {error,E});
form({warning,W}, Fun, State) -> Fun(State, {warning,W});
form({eof,Line}, Fun, State) -> Fun(State, {eof,Line}).

%% -type farity_list([Farity]) -> [Farity] when Farity <= {atom(),integer()}.

farity_list([{Name,Arity}|Fas], Fun, State) ->
    {H, State1} = Fun(State, {Name,Arity}),
    {T, State2} = farity_list(Fas, Fun, State1),
    {[H|T], State2};
farity_list([], _Fun, State) -> {[], State}.

%% -type record_defs([RecDef]) -> [RecDef].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *parser*!

record_defs([{record_field, Line, {atom, La, A}, Val0}|Is], Fun, State) ->
    {Val1, State1} = expr(Val0, Fun, State),
    {R, State2} = Fun(State1, {record_field,Line,{atom,La,A},Val1}),
    {T, State3} = record_defs(Is, Fun, State2),
    {[R|T], State3};
record_defs([Node={record_field, _Line, {atom, _La, _A}}|Is], Fun, State) ->
    {R, State1} = Fun(State, Node),
    {T, State2} = record_defs(Is, Fun, State1),
    {[R|T], State2};

record_defs([{typed_record_field,
              {record_field, Line, {atom, La, A}, Val0}, Type}|Is],
           Fun, State) ->
    {Val1, State1} = expr(Val0, Fun, State),
    {Type1, State2} = type(Type, Fun, State1),
    Node1 = {typed_record_field, {record_field, Line, {atom, La, A}, Val1}, Type1},
    {Node2, State3} = Fun(State2, Node1),
    {T, State4} = record_defs(Is, Fun, State3),
    {[Node2|T], State4};

record_defs([{typed_record_field,
				   {record_field, Line, {atom, La, A}}, Type}|Is],
           Fun, State) ->
    {Type1, State1} = type(Type, Fun, State),
    Node1 = {typed_record_field, {record_field, Line, {atom, La, A}}, Type1},
    {Node2, State2} = Fun(State1, Node1),
    {T, State3} = record_defs(Is, Fun, State2),
    {[Node2|T], State3};

record_defs([], _Fun, State) -> {[], State}.

%% -type function(atom(), integer(), [Clause]) -> {atom(),integer(),[Clause]}.

function(Name, Arity, Clauses0, Fun, State) ->
    {Clauses1, State1} = clauses(Clauses0, Fun, State),
    {{Name,Arity,Clauses1}, State1}.

%% -type clauses([Clause]) -> [Clause].

clauses([C0|Cs], Fun, State) ->
    {C1, State1} = clause(C0, Fun, State),
    {T, State2} = clauses(Cs, Fun, State1),
    {[C1|T], State2};
clauses([], _Fun, State) -> {[], State}.

%% -type clause(Clause) -> Clause.

clause({clause, Line, H0, G0, B0}, Fun, State) ->
    {H1, State1} = head(H0, Fun, State),
    {G1, State2} = guard(G0, Fun, State1),
    {B1, State3} = exprs(B0, Fun, State2),
    Fun(State3, {clause, Line, H1, G1, B1}).

%% -type head([Pattern]) -> [Pattern].

head(Ps, Fun, State) -> patterns(Ps, Fun, State).

%% -type patterns([Pattern]) -> [Pattern].
%%  These patterns are processed "sequentially" for purposes of variable
%%  definition etc.

patterns([P0|Ps], Fun, State) ->
    {P1, State1} = pattern(P0, Fun, State),
    {T, State2} = patterns(Ps, Fun, State1),
    {[P1|T], State2};
patterns([], _Fun, State) -> {[], State}.

%% -type pattern(Pattern) -> Pattern.
%%  N.B. Only valid patterns are included here.

pattern({var,Line,V}, Fun, State) -> Fun(State, {var,Line,V});
pattern({match,Line,L0,R0}, Fun, State) ->
    {L1, State1} = pattern(L0, Fun, State),
    {R1, State2} = pattern(R0, Fun, State1),
    Fun(State2, {match,Line,L1,R1});
pattern({integer,Line,I}, Fun, State) -> Fun(State, {integer,Line,I});
pattern({char,Line,C}, Fun, State) -> Fun(State, {char,Line,C});
pattern({float,Line,F}, Fun, State) -> Fun(State, {float,Line,F});
pattern({atom,Line,A}, Fun, State) -> Fun(State, {atom,Line,A});
pattern({string,Line,S}, Fun, State) -> Fun(State, {string,Line,S});
pattern({nil,Line}, Fun, State) -> Fun(State, {nil,Line});
pattern({cons,Line,H0,T0}, Fun, State) ->
    {H1, State1} = pattern(H0, Fun, State),
    {T1, State2} = pattern(T0, Fun, State1),
    Fun(State2, {cons,Line,H1,T1});
pattern({tuple,Line,Ps0}, Fun, State) ->
    {Ps1, State1} = pattern_list(Ps0, Fun, State),
    Fun(State1, {tuple,Line,Ps1});
pattern({map,Line,Ps0}, Fun, State) ->
    {Ps1, State1} = pattern_list(Ps0, Fun, State),
    Fun(State1, {map,Line,Ps1});
pattern({map_field_exact,Line,K,V}, Fun, State) ->
    {Ke, State1} = expr(K, Fun, State),
    {Ve, State2} = pattern(V, Fun, State1),
    Fun(State2, {map_field_exact,Line,Ke,Ve});
%%pattern({struct,Line,Tag,Ps0}) ->
%%    Ps1 = pattern_list(Ps0),
%%    {struct,Line,Tag,Ps1};
pattern({record,Line,Name,Pfs0}, Fun, State) ->
    {Pfs1, State1} = pattern_fields(Pfs0, Fun, State),
    Fun(State1, {record,Line,Name,Pfs1});
pattern({record_index,Line,Name,Field0}, Fun, State) ->
    {Field1, State1} = pattern(Field0, Fun, State),
    Fun(State1, {record_index,Line,Name,Field1});
pattern({record_field,Line,Rec0,Name,Field0}, Fun, State) ->
    {Rec1, State1} = expr(Rec0, Fun, State),
    {Field1, State2} = expr(Field0, Fun, State1),
    Fun(State2, {record_field,Line,Rec1,Name,Field1});
pattern({record_field,Line,Rec0,Field0}, Fun, State) ->
    {Rec1, State1} = expr(Rec0, Fun, State),
    {Field1, State2} = expr(Field0, Fun, State1),
    Fun(State2, {record_field,Line,Rec1,Field1});
pattern({bin,Line,Fs}, Fun, State) ->
    {Fs2, State1} = pattern_grp(Fs, Fun, State),
    Fun(State1, {bin,Line,Fs2});
pattern({op,Line,Op,A}, Fun, State) ->
    Fun(State, {op,Line,Op,A});
pattern({op,Line,Op,L,R}, Fun, State) ->
    Fun(State, {op,Line,Op,L,R});


% otp/lib/syntax_tools/test/merl_SUITE.erl:77 in 19.2 has this call
% {call,77, {remote,77,{atom,77,merl},{atom,77,quote}},
%   [{integer,77,77}, {string,77,"{foo, _@Bar, '@Baz'}"}]}

pattern(Other, Fun, State) ->
    Fun(State, Other).

pattern_grp([{bin_element,L1,E1,S1,T1} | Fs], Fun, State) ->
    {S2, State1} = case S1 of
                       default ->
                           {default, State};
                       _ ->
                           expr(S1, Fun, State)
                   end,
    {T2, State2} = case T1 of
                       default ->
                           {default, State1};
                       _ ->
                           bit_types(T1, Fun, State1)
                   end,
    {E2, State3} = expr(E1, Fun, State2),
    {R, State4} = Fun(State3, {bin_element,L1, E2,S2,T2}),
    {T, State5} = pattern_grp(Fs, Fun, State4),
    {[R|T], State5};
pattern_grp([], _Fun, State) ->
    {[], State}.

bit_types([], _Fun, State) ->
    {[], State};
bit_types([Atom | Rest], Fun, State) when is_atom(Atom) ->
    {R, State1} = bit_types(Rest, Fun, State),
    {[Atom | R], State1};
bit_types([{Atom, Integer} | Rest], Fun, State) when is_atom(Atom), is_integer(Integer) ->
    {R, State1} = bit_types(Rest, Fun, State),
    {[{Atom, Integer} | R], State1}.



%% -type pattern_list([Pattern]) -> [Pattern].
%%  These patterns are processed "in parallel" for purposes of variable
%%  definition etc.

pattern_list([P0|Ps], Fun, State) ->
    {P1, State1} = pattern(P0, Fun, State),
    {T, State2} = pattern_list(Ps, Fun, State1),
    {[P1|T], State2};
pattern_list([], _Fun, State) -> {[], State}.

%% -type pattern_fields([Field]) -> [Field].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

pattern_fields([{record_field,Lf,{atom,La,F},P0}|Pfs], Fun, State) ->
    {P1, State1} = pattern(P0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{atom,La,F},P1}),
    {T, State3} = pattern_fields(Pfs, Fun, State2),
    {[H|T], State3};
pattern_fields([{record_field,Lf,{var,La,'_'},P0}|Pfs], Fun, State) ->
    {P1, State1} = pattern(P0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{var,La,'_'},P1}),
    {T, State3} = pattern_fields(Pfs, Fun, State2),
    {[H|T], State3};
pattern_fields([], _Fun, State) -> {[], State}.

%% -type guard([GuardTest]) -> [GuardTest].

guard([G0|Gs], Fun, State) when is_list(G0) ->
    {H, State1} = guard0(G0, Fun, State),
    {T, State2} = guard(Gs, Fun, State1),
    {[H|T], State2};
guard(L, Fun, State) ->
    guard0(L, Fun, State).

guard0([G0|Gs], Fun, State) ->
    {G1, State1} = guard_test(G0, Fun, State),
    {T, State2} = guard0(Gs, Fun, State1),
    {[G1|T], State2};
guard0([], _Fun, State) -> {[], State}.

guard_test(Expr={call,Line,{atom,La,F},As0}, Fun, State) ->
    case erl_internal:type_test(F, length(As0)) of
        true ->
            {As1, State1} = gexpr_list(As0, Fun, State),
            Fun(State1, {call,Line,{atom,La,F},As1});
        _ ->
            gexpr(Expr, Fun, State)
    end;
guard_test(Any, Fun, State) ->
    gexpr(Any, Fun, State).

%% Before R9, there were special rules regarding the expressions on
%% top level in guards. Those limitations are now lifted - therefore
%% there is no need for a special clause for the toplevel expressions.
%% -type gexpr(GuardExpr) -> GuardExpr.

gexpr({var,Line,V}, Fun, State) -> Fun(State, {var,Line,V});
gexpr({integer,Line,I}, Fun, State) -> Fun(State, {integer,Line,I});
gexpr({char,Line,C}, Fun, State) -> Fun(State, {char,Line,C});
gexpr({float,Line,F}, Fun, State) -> Fun(State, {float,Line,F});
gexpr({atom,Line,A}, Fun, State) -> Fun(State, {atom,Line,A});
gexpr({string,Line,S}, Fun, State) -> Fun(State, {string,Line,S});
gexpr({nil,Line}, Fun, State) -> Fun(State, {nil,Line});
gexpr({map,Line,Map0,Es0}, Fun, State) ->
    {[Map1|Es1], State1} = gexpr_list([Map0|Es0], Fun, State),
    Fun(State1, {map,Line,Map1,Es1});
gexpr({map,Line,Es0}, Fun, State) ->
    {Es1, State1} = gexpr_list(Es0, Fun, State),
    Fun(State1, {map,Line,Es1});
gexpr({map_field_assoc,Line,K,V}, Fun, State) ->
    {Ke, State1} = gexpr(K, Fun, State),
    {Ve, State2} = gexpr(V, Fun, State1),
    Fun(State2, {map_field_assoc,Line,Ke,Ve});
gexpr({map_field_exact,Line,K,V}, Fun, State) ->
    {Ke, State1} = gexpr(K, Fun, State),
    {Ve, State2} = gexpr(V, Fun, State1),
    Fun(State2, {map_field_exact,Line,Ke,Ve});
gexpr({cons,Line,H0,T0}, Fun, State) ->
    {H1, State1} = gexpr(H0, Fun, State),
    {T1, State2} = gexpr(T0, Fun, State1),				%They see the same variables
    Fun(State2, {cons,Line,H1,T1});
gexpr({tuple,Line,Es0}, Fun, State) ->
    {Es1, State1} = gexpr_list(Es0, Fun, State),
    Fun(State1, {tuple,Line,Es1});
gexpr({record_index,Line,Name,Field0}, Fun, State) ->
    {Field1, State1} = gexpr(Field0, Fun, State),
    Fun(State1, {record_index,Line,Name,Field1});
gexpr({record_field,Line,Rec0,Name,Field0}, Fun, State) ->
    {Rec1, State1} = gexpr(Rec0, Fun, State),
    {Field1, State2} = gexpr(Field0, Fun, State1),
    Fun(State2, {record_field,Line,Rec1,Name,Field1});
gexpr({record,Line,Name,Inits0}, Fun, State) ->
    {Inits1, State1} = grecord_inits(Inits0, Fun, State),
    Fun(State1, {record,Line,Name,Inits1});
gexpr(Node={call,Line,{atom,La,F},As0}, Fun, State) ->
    case erl_internal:guard_bif(F, length(As0)) of
        true ->
            {As1, State1} = gexpr_list(As0, Fun, State),
            Fun(State1, {call,Line,{atom,La,F},As1});
        false ->
            %% NOTE: otp/lib/compiler/test/guard_SUITE.erl has a code that
            %% makes this return false
            {Node, State}
    end;
% Guard bif's can be remote, but only in the module erlang...
gexpr({call,Line,{remote,La,{atom,Lb,erlang},{atom,Lc,F}},As0}, Fun, State) ->
    case erl_internal:guard_bif(F, length(As0)) or
         erl_internal:arith_op(F, length(As0)) or
         erl_internal:comp_op(F, length(As0)) or
         erl_internal:bool_op(F, length(As0)) of
        true ->
            {As1, State1} = gexpr_list(As0, Fun, State),
            Fun(State1, {call,Line,{remote,La,{atom,Lb,erlang},{atom,Lc,F}},As1})
    end;
gexpr({bin,Line,Fs}, Fun, State) ->
    {Fs2, State1} = pattern_grp(Fs, Fun, State),
    Fun(State1, {bin,Line,Fs2});
gexpr({op,Line,Op,A0}, Fun, State) ->
    case erl_internal:arith_op(Op, 1) or
         erl_internal:bool_op(Op, 1) of
        true ->
            {A1, State1} = gexpr(A0, Fun, State),
            Fun(State1, {op,Line,Op,A1})
    end;
gexpr({op,Line,Op,L0,R0}, Fun, State) when Op =:= 'andalso'; Op =:= 'orelse' ->
    %% R11B: andalso/orelse are now allowed in guards.
    {L1, State1} = gexpr(L0, Fun, State),
    {R1, State2} = gexpr(R0, Fun, State1), %They see the same variables
    Fun(State2, {op,Line,Op,L1,R1});
gexpr({op,Line,Op,L0,R0}, Fun, State) ->
    case erl_internal:arith_op(Op, 2) or
         erl_internal:bool_op(Op, 2) or
         erl_internal:comp_op(Op, 2) of
        true ->
            {L1, State1} = gexpr(L0, Fun, State),
            {R1, State2} = gexpr(R0, Fun, State1), %They see the same variables
            Fun(State2, {op,Line,Op,L1,R1})
    end.

%% -type gexpr_list([GuardExpr]) -> [GuardExpr].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

gexpr_list([E0|Es], Fun, State) ->
    {E1, State1} = gexpr(E0, Fun, State),
    {T, State2} = gexpr_list(Es, Fun, State1),
    {[E1|T], State2};
gexpr_list([], _Fun, State) -> {[], State}.

grecord_inits([{record_field,Lf,{atom,La,F},Val0}|Is], Fun, State) ->
    {Val1, State1} = gexpr(Val0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{atom,La,F},Val1}),
    {T, State3} = grecord_inits(Is, Fun, State2),
    {[H|T], State3};
grecord_inits([{record_field,Lf,{var,La,'_'},Val0}|Is], Fun, State) ->
    {Val1, State1} = gexpr(Val0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{var,La,'_'},Val1}),
    {T, State3} = grecord_inits(Is, Fun, State2),
    {[H|T], State3};
grecord_inits([], _Fun, State) -> {[], State}.

%% -type exprs([Expression]) -> [Expression].
%%  These expressions are processed "sequentially" for purposes of variable
%%  definition etc.

exprs([E0|Es], Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {T, State2} = exprs(Es, Fun, State1),
    {[E1|T], State2};
exprs([], _Fun, State) -> {[], State}.

%% -type expr(Expression) -> Expression.

expr({var,Line,V}, Fun, State) -> Fun(State, {var,Line,V});
expr({integer,Line,I}, Fun, State) -> Fun(State, {integer,Line,I});
expr({float,Line,F}, Fun, State) -> Fun(State, {float,Line,F});
expr({atom,Line,A}, Fun, State) -> Fun(State, {atom,Line,A});
expr({string,Line,S}, Fun, State) -> Fun(State, {string,Line,S});
expr({char,Line,C}, Fun, State) -> Fun(State, {char,Line,C});
expr({nil,Line}, Fun, State) -> Fun(State, {nil,Line});
expr({cons,Line,H0,T0}, Fun, State) ->
    {H1, State1} = expr(H0, Fun, State),
    {T1, State2} = expr(T0, Fun, State1),				%They see the same variables
    Fun(State2, {cons,Line,H1,T1});
expr({lc,Line,E0,Qs0}, Fun, State) ->
    {Qs1, State1} = lc_bc_quals(Qs0, Fun, State),
    {E1, State2} = expr(E0, Fun, State1),
    Fun(State2, {lc,Line,E1,Qs1});
expr({bc,Line,E0,Qs0}, Fun, State) ->
    {Qs1, State1} = lc_bc_quals(Qs0, Fun, State),
    {E1, State2} = expr(E0, Fun, State1),
    Fun(State2, {bc,Line,E1,Qs1});
expr({tuple,Line,Es0}, Fun, State) ->
    {Es1, State1} = expr_list(Es0, Fun, State),
    Fun(State1, {tuple,Line,Es1});
expr({map,Line,Map0,Es0}, Fun, State) ->
    {[Map1|Es1], State1} = exprs([Map0|Es0], Fun, State),
    Fun(State1, {map,Line,Map1,Es1});
expr({map,Line,Es0}, Fun, State) ->
    {Es1, State1} = exprs(Es0, Fun, State),
    Fun(State1, {map,Line,Es1});
expr({map_field_assoc,Line,K,V}, Fun, State) ->
    {Ke, State1} = expr(K, Fun, State),
    {Ve, State2} = expr(V, Fun, State1),
    Fun(State2, {map_field_assoc,Line,Ke,Ve});
expr({map_field_exact,Line,K,V}, Fun, State) ->
    {Ke, State1} = expr(K, Fun, State),
    {Ve, State2} = expr(V, Fun, State1),
    Fun(State2, {map_field_exact,Line,Ke,Ve});
%%expr({struct,Line,Tag,Es0}) ->
%%    Es1 = pattern_list(Es0),
%%    {struct,Line,Tag,Es1};
expr({record_index,Line,Name,Field0}, Fun, State) ->
    {Field1, State1} = expr(Field0, Fun, State),
    Fun(State1, {record_index,Line,Name,Field1});
expr({record,Line,Name,Inits0}, Fun, State) ->
    {Inits1, State1} = record_inits(Inits0, Fun, State),
    Fun(State1, {record,Line,Name,Inits1});
expr({record_field,Line,Rec0,Name,Field0}, Fun, State) ->
    {Rec1, State1} = expr(Rec0, Fun, State),
    {Field1, State2} = expr(Field0, Fun, State1),
    Fun(State2, {record_field,Line,Rec1,Name,Field1});
expr({record,Line,Rec0,Name,Upds0}, Fun, State) ->
    {Rec1, State1} = expr(Rec0, Fun, State),
    {Upds1, State2} = record_updates(Upds0, Fun, State1),
    Fun(State2, {record,Line,Rec1,Name,Upds1});
expr({record_field,Line,Rec0,Field0}, Fun, State) ->
    {Rec1, State1} = expr(Rec0, Fun, State),
    {Field1, State2} = expr(Field0, Fun, State1),
    Fun(State2, {record_field,Line,Rec1,Field1});
expr({block,Line,Es0}, Fun, State) ->
    %% Unfold block into a sequence.
    {Es1, State1} = exprs(Es0, Fun, State),
    Fun(State1, {block,Line,Es1});
expr({'if',Line,Cs0}, Fun, State) ->
    {Cs1, State1} = icr_clauses(Cs0, Fun, State),
    Fun(State1, {'if',Line,Cs1});
expr({'case',Line,E0,Cs0}, Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {Cs1, State2} = icr_clauses(Cs0, Fun, State1),
    Fun(State2, {'case',Line,E1,Cs1});
expr({'receive',Line,Cs0}, Fun, State) ->
    {Cs1, State1} = icr_clauses(Cs0, Fun, State),
    Fun(State1, {'receive',Line,Cs1});
expr({'receive',Line,Cs0,To0,ToEs0}, Fun, State) ->
    {To1, State1} = expr(To0, Fun, State),
    {ToEs1, State2} = exprs(ToEs0, Fun, State1),
    {Cs1, State3} = icr_clauses(Cs0, Fun, State2),
    Fun(State3, {'receive',Line,Cs1,To1,ToEs1});
expr({'try',Line,Es0,Scs0,Ccs0,As0}, Fun, State) ->
    {Es1, State1} = exprs(Es0, Fun, State),
    {Scs1, State2} = icr_clauses(Scs0, Fun, State1),
    {Ccs1, State3} = icr_clauses(Ccs0, Fun, State2),
    {As1, State4} = exprs(As0, Fun, State3),
    Fun(State4, {'try',Line,Es1,Scs1,Ccs1,As1});
expr({'fun',Line,Body}, Fun, State) ->
    case Body of
        {clauses,Cs0} ->
            {Cs1, State1} = fun_clauses(Cs0, Fun, State),
            Fun(State1, {'fun',Line,{clauses,Cs1}});
        {function,F,A} ->
            Fun(State, {'fun',Line,{function,F,A}});
        {function,M,F,A} when is_atom(M), is_atom(F), is_integer(A) ->
            %% R10B-6: fun M:F/A. (Backward compatibility)
            Fun(State, {'fun',Line,{function,M,F,A}});
        {function,M0,F0,A0} ->
            %% R15: fun M:F/A with variables.
            {M, State1} = expr(M0, Fun, State),
            {F, State2} = expr(F0, Fun, State1),
            {A, State3} = expr(A0, Fun, State2),
            Fun(State3, {'fun',Line,{function,M,F,A}})
    end;
expr({named_fun,Loc,Name,Cs}, Fun, State) ->
    {R, State1} = fun_clauses(Cs, Fun, State),
    Fun(State1, {named_fun,Loc,Name,R});
expr({call,Line,F0,As0}, Fun, State) ->
    %% N.B. If F an atom then call to local function or BIF, if F a
    %% remote structure (see below) then call to other module,
    %% otherwise apply to "function".
    {F1, State1} = expr(F0, Fun, State),
    {As1, State2} = expr_list(As0, Fun, State1),
    Fun(State2, {call,Line,F1,As1});
expr({'catch',Line,E0}, Fun, State) ->
    %% No new variables added.
    {E1, State1} = expr(E0, Fun, State),
    Fun(State1, {'catch',Line,E1});
expr({match,Line,P0,E0}, Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {P1, State2} = pattern(P0, Fun, State1),
    Fun(State2, {match,Line,P1,E1});
expr({bin,Line,Fs}, Fun, State) ->
    {Fs2, State1} = pattern_grp(Fs, Fun, State),
    Fun(State1, {bin,Line,Fs2});
expr({op,Line,Op,A0}, Fun, State) ->
    {A1, State1} = expr(A0, Fun, State),
    Fun(State1, {op,Line,Op,A1});
expr({op,Line,Op,L0,R0}, Fun, State) ->
    {L1, State1} = expr(L0, Fun, State),
    {R1, State2} = expr(R0, Fun, State1), %They see the same variables
    Fun(State2, {op,Line,Op,L1,R1});
%% The following are not allowed to occur anywhere!
expr({remote,Line,M0,F0}, Fun, State) ->
    {M1, State1} = expr(M0, Fun, State),
    {F1, State2} = expr(F0, Fun, State1),
    Fun(State2, {remote,Line,M1,F1}).

%% -type expr_list([Expression]) -> [Expression].
%%  These expressions are processed "in parallel" for purposes of variable
%%  definition etc.

expr_list([E0|Es], Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {T, State2} = expr_list(Es, Fun, State1),
    {[E1|T], State2};
expr_list([], _Fun, State) -> {[], State}.

%% -type record_inits([RecordInit]) -> [RecordInit].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_inits([{record_field,Lf,{atom,La,F},Val0}|Is], Fun, State) ->
    {Val1, State1} = expr(Val0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{atom,La,F},Val1}),
    {T, State3} = record_inits(Is, Fun, State2),
    {[H|T], State3};
record_inits([{record_field,Lf,{var,La,'_'},Val0}|Is], Fun, State) ->
    {Val1, State1} = expr(Val0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{var,La,'_'},Val1}),
    {T, State3} = record_inits(Is, Fun, State2),
    {[H|T], State3};
record_inits([], _Fun, State) -> {[], State}.

%% -type record_updates([RecordUpd]) -> [RecordUpd].
%%  N.B. Field names are full expressions here but only atoms are allowed
%%  by the *linter*!.

record_updates([{record_field,Lf,{atom,La,F},Val0}|Us], Fun, State) ->
    {Val1, State1} = expr(Val0, Fun, State),
    {H, State2} = Fun(State1, {record_field,Lf,{atom,La,F},Val1}),
    {T, State3} = record_updates(Us, Fun, State2),
    {[H|T], State3};
record_updates([], _Fun, State) -> {[], State}.

%% -type icr_clauses([Clause]) -> [Clause].

icr_clauses([C0|Cs], Fun, State) ->
    {C1, State1} = clause(C0, Fun, State),
    {T, State2} = icr_clauses(Cs, Fun, State1),
    {[C1|T], State2};
icr_clauses([], _Fun, State) -> {[], State}.

%% -type lc_bc_quals([Qualifier]) -> [Qualifier].
%%  Allow filters to be both guard tests and general expressions.

lc_bc_quals([{generate,Line,P0,E0}|Qs], Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {P1, State2} = pattern(P0, Fun, State1),
    {H, State3} = Fun(State2, {generate,Line,P1,E1}),
    {T, State4} = lc_bc_quals(Qs, Fun, State3),
    {[H|T], State4};
lc_bc_quals([{b_generate,Line,P0,E0}|Qs], Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {P1, State2} = pattern(P0, Fun, State1),
    {H, State3} = Fun(State2, {b_generate,Line,P1,E1}),
    {T, State4} = lc_bc_quals(Qs, Fun, State3),
    {[H|T], State4};
lc_bc_quals([E0|Qs], Fun, State) ->
    {E1, State1} = expr(E0, Fun, State),
    {T, State2} = lc_bc_quals(Qs, Fun, State1),
    {[E1|T], State2};
lc_bc_quals([], _Fun, State) -> {[], State}.

%% -type fun_clauses([Clause]) -> [Clause].

fun_clauses([C0|Cs], Fun, State) ->
    {C1, State1} = clause(C0, Fun, State),
    {T, State2} = fun_clauses(Cs, Fun, State1),
    {[C1|T], State2};
fun_clauses([], _Fun, State) -> {[], State}.

type({ann_type,Line,[{var,Lv,V},T]}, Fun, State) ->
    {T1, State1} = type(T, Fun, State),
    Fun(State1, {ann_type,Line,[{var,Lv,V},T1]});
type({atom,Line,A}, Fun, State) ->
    Fun(State, {atom,Line,A});
type({integer,Line,I}, Fun, State) ->
    Fun(State, {integer,Line,I});
type({op,Line,Op,T}, Fun, State) ->
    {T1, State1} = type(T, Fun, State),
    Fun(State1, {op,Line,Op,T1});
type({op,Line,Op,L,R}, Fun, State) ->
    {L1, State1} = type(L, Fun, State),
    {R1, State2} = type(R, Fun, State1),
    Fun(State2, {op,Line,Op,L1,R1});
type({type,Line,binary,[M,N]}, Fun, State) ->
    {M1, State1} = type(M, Fun, State),
    {N1, State2} = type(N, Fun, State1),
    Fun(State2, {type,Line,binary,[M1,N1]});
type({type,Line,'fun',[]}, Fun, State) ->
    Fun(State, {type,Line,'fun',[]});
type({type,Line,'fun',[{type,Lt,any},B]}, Fun, State) ->
    {B1, State1} = type(B, Fun, State),
    Fun(State1, {type,Line,'fun',[{type,Lt,any},B1]});
type({type,Line,range,[L,H]}, Fun, State) ->
    {L1, State1} = type(L, Fun, State),
    {H1, State2} = type(H, Fun, State1),
    Fun(State2, {type,Line,range,[L1,H1]});
type({type,Line,map,any}, Fun, State) ->
    Fun(State, {type,Line,map,any});
type({type,Line,map,Ps}, Fun, State) ->
    {Ps1, State1} = map_pair_types(Ps, Fun, State),
    Fun(State1, {type,Line,map,Ps1});
type({type,Line,record,[{atom,La,N}|Fs]}, Fun, State) ->
    {Fs1, State1} = field_types(Fs, Fun, State),
    Fun(State1, {type,Line,record,[{atom,La,N}|Fs1]});
type({remote_type,Line,[{atom,Lm,M},{atom,Ln,N},As]}, Fun, State) ->
    {As1, State1} = type_list(As, Fun, State),
    Fun(State1, {remote_type,Line,[{atom,Lm,M},{atom,Ln,N},As1]});
type({type,Line,tuple,any}, Fun, State) ->
    Fun(State, {type,Line,tuple,any});
type({type,Line,tuple,Ts}, Fun, State) ->
    {Ts1, State1} = type_list(Ts, Fun, State),
    Fun(State1, {type,Line,tuple,Ts1});
type({type,Line,union,Ts}, Fun, State) ->
    {Ts1, State1} = type_list(Ts, Fun, State),
    Fun(State1, {type,Line,union,Ts1});
type({var,Line,V}, Fun, State) ->
    Fun(State, {var,Line,V});
type({user_type,Line,N,As}, Fun, State) ->
    {As1, State1} = type_list(As, Fun, State),
    Fun(State1, {user_type,Line,N,As1});
type({type,Line,N,As}, Fun, State) ->
    {As1, State1} = type_list(As, Fun, State),
    Fun(State1, {type,Line,N,As1});

% seen in dialyzer/test/small_SUITE_data/src/chars.erl
type(Node={char, _Line, _C}, Fun, State) ->
    Fun(State, Node).

map_pair_types([{type,Line,map_field_assoc,[K,V]}|Ps], Fun, State) ->
    {K1, State1} = type(K, Fun, State),
    {V1, State2} = type(V, Fun, State1),
    H = {type,Line,map_field_assoc,[K1,V1]},
    {T, State3} = map_pair_types(Ps, Fun, State2),
    {[H|T], State3};

map_pair_types([{type,Line,map_field_exact,[K,V]}|Ps], Fun, State) ->
    {K1, State1} = type(K, Fun, State),
    {V1, State2} = type(V, Fun, State1),
    H = {type,Line,map_field_exact,[K1,V1]},
    {T, State3} = map_pair_types(Ps, Fun, State2),
    {[H|T], State3};

map_pair_types([], _Fun, State) -> {[], State}.

field_types([{type,Line,field_type,[{atom,La,A},T]}|Fs], Fun, State) ->
    {T1, State1} = type(T, Fun, State),
    H = {type,Line,field_type,[{atom,La,A},T1]},
    {Tail, State2} = field_types(Fs, Fun, State1),
    {[H|Tail], State2};

field_types([], _Fun, State) -> {[], State}.

type_list([T|Ts], Fun, State) ->
    {T1, State1} = type(T, Fun, State),
    {Ts1, State2} = type_list(Ts, Fun, State1),
    {[T1|Ts1], State2};
type_list([], _Fun, State) -> {[], State}.
