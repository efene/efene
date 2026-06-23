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

-module(fn_pp).
-export([format/1, layout/1]).
-import(prettypr, [sep/1, beside/2, empty/0, text/1, floating/1, nest/2, par/2,
                   above/2, follow/3]).
-import(erl_parse, [inop_prec/1, preop_prec/1]).

% used on tests
-export([pp_guards/2, default_ctx/0]).

-include("efene.hrl").

-define(PADDING, 2).
-define(PAPER, 80). % 80
-define(RIBBON, 56). % 56
-define(NOUSER, undefined).
-define(NOHOOK, none).

-record(ctxt, {prec = 0       :: integer(),
	       sub_indent = 2     :: non_neg_integer(),
           exports_all = false,
           exports = #{},
           % {Name, Arity} => spec function types / fn_attrs, collected in a
           % pre-pass so they can be rendered inside their `fn` block instead
           % of being dropped (see collect_fn_meta/2, pp_fn_annotations/3)
           specs = #{},
           fnattrs = #{},
	       break_indent = 4   :: non_neg_integer(),
	       paper = ?PAPER     :: integer(),
	       ribbon = ?RIBBON   :: integer()}).

layout(V) -> layout(V, default_ctx()).

layout(V, Ctx) when is_list(V) -> pp_mod(V, collect_fn_meta(V, Ctx));
layout(V, Ctx) -> pp(V, Ctx).

format(V) -> prettypr:format(layout(V), ?PAPER, ?RIBBON).

default_ctx() -> #ctxt{}.

% collect per-function specs and fn_attrs (doc and friends) up front, so they
% can be attached to their `fn` block rather than dropped or rendered loose
collect_fn_meta([], Ctx) -> Ctx;
collect_fn_meta([{attribute, _, spec, {{Name, Arity}, Types}} | Rest],
                Ctx=#ctxt{specs=Specs}) ->
    collect_fn_meta(Rest, Ctx#ctxt{specs=Specs#{{Name, Arity} => Types}});
collect_fn_meta([{attribute, _, fn_attrs, {Name, Arity, Attrs}} | Rest],
                Ctx=#ctxt{fnattrs=FnAttrs}) ->
    collect_fn_meta(Rest, Ctx#ctxt{fnattrs=FnAttrs#{{Name, Arity} => Attrs}});
collect_fn_meta([_ | Rest], Ctx) ->
    collect_fn_meta(Rest, Ctx).

pp_mod([], _Ctx) -> empty();
pp_mod([Node | Nodes], Ctx) ->
    Ctx1 = maybe_update_ctx(Node, Ctx),
    above(pp(Node, Ctx1), pp_mod(Nodes, Ctx1)).

maybe_update_ctx({attribute, _, compile, export_all}, Ctx) ->
    Ctx1 = Ctx#ctxt{exports_all=true},
    Ctx1;
maybe_update_ctx({attribute, _, export, Exports}, Ctx=#ctxt{exports=CurExports}) ->
    NewExports = maps:merge(CurExports, maps:from_list([{K, true} || K <- Exports])),
    Ctx1 = Ctx#ctxt{exports=NewExports},
    Ctx1;
maybe_update_ctx(_Node, Ctx) ->
    Ctx.

function_exported(#ctxt{exports_all=true}, _, _) -> true;
function_exported(#ctxt{exports=Exports}, Name, Arity) ->
    maps:is_key({Name, Arity}, Exports).

arity_to_list('_') -> "`_`";
arity_to_list(V) -> integer_to_list(V).

pp_fn_ref({FNameAtom, Arity}, _Ctx) ->
    text(atom_to_list(FNameAtom) ++ "/" ++ arity_to_list(Arity)).

pp_fn_deprecated_ref({FName, Arity, When}, _Ctx) ->
    text("(" ++ atom_to_list(FName) ++ ", " ++ arity_to_list(Arity) ++ ", "
         ++ atom_to_list(When) ++ ")");
pp_fn_deprecated_ref(FnRef, Ctx) ->
    pp_fn_ref(FnRef, Ctx).

pp_attr_fun_list(Prefix, Funs, Ctx) ->
    besidel([text(Prefix),
             join(Funs, Ctx, fun pp_fn_ref/2, comma_f()),
             cparen_f()]).

gen_attr(Attr, V) when is_atom(V) ->
    text("@" ++ atom_to_list(Attr) ++ "(" ++ quote_atom_raw(V) ++ ")");
gen_attr(Attr, V) when is_list(V) ->
    text("@" ++ atom_to_list(Attr) ++ "(" ++ io_lib:write_string(V) ++ ")").

% TODO: what to do with errors
pp({error, _}, _Ctx) -> empty();
% TODO: handle specs
pp({attribute, _, spec, _}, _Ctx) -> empty();
% TODO: handle opaque
pp({attribute, _, opaque, _}, _Ctx) -> empty();
% TODO: handle dialyzer
pp({attribute, _, dialyzer, _}, _Ctx) -> empty();
% TODO: handle callback
pp({attribute, _, callback, _}, _Ctx) -> empty();
% TODO: handle optional_callbacks
pp({attribute, _, optional_callbacks, _}, _Ctx) -> empty();
% TODO: render fn_attrs (public/doc) as efene annotations
pp({attribute, _, fn_attrs, _}, _Ctx) -> empty();
pp({attribute, _, file, _}, _Ctx) -> empty();
pp({attribute, _, module, _}, _Ctx) -> empty();
pp({attribute, _, Attr=behaviour, V}, _Ctx) ->
    gen_attr(Attr, V);
pp({attribute, _, behavior, V}, _Ctx) ->
    gen_attr(behaviour, V);
pp({attribute, _, Attr=author, V}, _Ctx) ->
    gen_attr(Attr, V);
pp({attribute, _, Attr=vsn, V}, _Ctx) ->
    gen_attr(Attr, V);
pp({attribute, _, Attr=date, V}, _Ctx) ->
    gen_attr(Attr, V);
pp({attribute, _, Attr=vc, V}, _Ctx) ->
    gen_attr(Attr, V);
pp({attribute, _, import, {ModNameAtom, Imports}}, Ctx) ->
    beside(text("@import("),
           followc(Ctx, beside(text(atom_to_list(ModNameAtom)), comma_f()),
                   beside(wrap_list(join(Imports, Ctx, fun pp_fn_ref/2, comma_f())), cparen_f())));
pp({attribute, _, export_type, Exports}, Ctx) ->
    pp_attr_fun_list("@export_type(", Exports, Ctx);
pp({attribute, _, on_load, V={_FName, _Arity}}, Ctx) ->
    besidel([text("@on_load("), pp_fn_ref(V, Ctx), cparen_f()]);
pp({attribute, _, deprecated, V={_FName, _Arity, _When}}, Ctx) ->
    besidel([text("@deprecated("), pp_fn_deprecated_ref(V, Ctx), cparen_f()]);
pp({attribute, _, deprecated, module}, _Ctx) ->
    text("@deprecated(module)");
pp({attribute, _, deprecated, Funs}, Ctx) ->
    besidel([text("@deprecated("),
             join(Funs, Ctx, fun pp_fn_deprecated_ref/2, comma_f()),
             cparen_f()]);
pp({attribute, _, inline, Exports}, Ctx) ->
    pp_attr_fun_list("@inline(", Exports, Ctx);
pp({attribute, _, type, {PName, Type, _Vars}}, Ctx) ->
    followc(Ctx, text("@type(" ++ atom_to_list(PName) ++ ") ->"),
            pp_type(Type, Ctx));
pp({attribute, _, export, _}, _Ctx) -> empty();
pp({attribute, _, compile, export_all}, _Ctx) -> text("@compile(export_all)");
pp({attribute, _, compile, _}, _Ctx) -> empty();

pp({attribute, _, record, {Name, Fields}}, Ctx) ->
    followc(Ctx, wrap(text(atom_to_list(Name)), text("@record("), text(") ->")),
            wrap_paren(pp_rec_fields(Fields, Ctx)));

pp({var, _, V}, _Ctx) -> text(atom_to_list(V));
pp({integer, _, Num}, _Ctx) -> text(integer_to_list(Num));
pp({float, _, Num}, _Ctx) -> text(io_lib:write(Num));
pp({char, _, V}, _Ctx) -> text("#c " ++ io_lib:write_string([V]));
pp({atom, _, V}, _Ctx) -> quote_atom(V);
pp({string, _, V}, _Ctx) -> text(io_lib:write_string(V));
pp({bin, _, [{bin_element, _, {string, _, V}, default, default}]}, _Ctx) ->
    text(io_lib:write_string(V, $'));
%pp({bin, _, []}, _Ctx) -> text("#b {}");
pp({bin, _, Elems}, Ctx) -> beside(text("#b "), wrap_map(pp_bin_es(Elems, Ctx)));

pp({tuple, _, []}, _Ctx) -> text("()");
pp({tuple, _, [Item]}, Ctx) ->
    wrap_paren(beside(pp(Item, Ctx), comma_f()));
pp({tuple, _, Items}, Ctx) ->
    wrap_paren(pp_items(Items, Ctx));

pp({map, _, []}, _Ctx) -> text("{}");
pp({map, _, Items}, Ctx) ->
    pp_map(Items, Ctx);
pp({map, _, CurMap, Items}, Ctx) ->
    wrap(text(" # "), pp(CurMap, Ctx), pp_map(Items, Ctx));

pp({record, _, RName, Args}, Ctx) ->
    beside(text("#r." ++ atom_to_list(RName) ++ " "),
        wrap_map(join(Args, Ctx, fun pp_rec_pair/2, comma_f())));

pp({record, _, CurRec, RName, Args}, Ctx) ->
    beside(text("#r." ++ atom_to_list(RName) ++ " "),
        wrap(text(" # "), pp(CurRec, Ctx), wrap_map(join(Args, Ctx, fun pp_rec_pair/2, comma_f()))));

pp({record_field, _, RVal, RName, Field}, Ctx) ->
    sep([beside(text("#r." ++ atom_to_list(RName) ++ "."), pp(Field, Ctx)),
         pp(RVal, Ctx)]);

pp({record_index, _, RName, Field}, Ctx) ->
    beside(text("#r." ++ atom_to_list(RName) ++ " "), pp(Field, Ctx));

pp({'catch', _, Expr}, Ctx) ->
    beside(text("catch "), pp(Expr, Ctx));

% fun references
pp({'fun', Line, {function, FName, Arity}}, Ctx) ->
    beside(text("fn "), wrap(colon_f(), pp({atom, Line, FName}, Ctx), pp({integer, Line, Arity}, Ctx)));
pp({'fun', _, {function, MName, FName, Arity}}, Ctx) ->
    beside(text("fn "), wrap(colon_f(), wrap(dot_f(), pp(MName, Ctx), pp(FName, Ctx)), pp(Arity, Ctx)));

pp({nil, _}, _Ctx) -> text("[]");
pp(V={cons, _, _H, _T}, Ctx) -> pp_cons(V, Ctx);

pp({call, _, {remote, _, MName, FName}, Args}, Ctx) ->
    pp_call(MName, FName, Args, Ctx);

pp({call, _, FName, Args}, Ctx) ->
    pp_call(FName, Args, Ctx);

pp({match, Line, Left, Right}, Ctx) ->
    % reuse logic
    pp({op, Line, '=', Left, Right}, Ctx);
pp({op, _, Op, Left, Right}, Ctx) ->
    {LeftPrec, Prec, RightPrec} = inop_prec(Op),
    D1 = pp(Left, Ctx#ctxt{prec=LeftPrec}),
    D2 = text(atom_to_list(fn_to_erl:map_op_reverse(Op))),
    D3 = pp(Right, Ctx#ctxt{prec=RightPrec}),
    % efene is newline-significant outside brackets, so the operator and its
    % operands must stay on one line (any soft break happens inside D1/D3)
    D4 = besidel([D1, text(" "), D2, text(" "), D3]),
    maybe_paren(Prec, Ctx#ctxt.prec, D4);

% unary
pp({op, _, Op, Right}, Ctx) ->
    {Prec, RightPrec} = preop_prec(Op),
    LOp = text(atom_to_list(fn_to_erl:map_op_reverse(Op))),
    LRight = pp(Right, Ctx#ctxt{prec=RightPrec}),
    L = besidel([LOp, text(" "), LRight]),
    maybe_paren(Prec, Ctx#ctxt.prec, L);

pp({lc, _, {block, _, Body}, Gens}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    pp_for(Gens, Ctx1, pp_body(Body, Ctx1), "for");
pp({lc, _, Body, Gens}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    pp_for(Gens, Ctx1, pp(Body, Ctx1), "for");

pp({bc, _, {block, _, Body}, Gens}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    pp_for(Gens, Ctx1, pp_body(Body, Ctx1), "#b for");
pp({bc, _, Body, Gens}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    pp_for(Gens, Ctx1, pp(Body, Ctx1), "#b for");

pp({block, _, [Expr]}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    sep([
         text("begin"),
         nestc(Ctx1, pp(Expr, Ctx1)),
         text("end")
        ]);
pp({block, _, Body}, Ctx) ->
    Ctx1 = reset_prec(Ctx),
    above(text("begin"),
          above(nestc(Ctx1, pp_body(Body, Ctx1)),
                text("end")));

pp({'try', _, Body, [], Clauses, AfterBody}, Ctx0) ->
    Ctx = reset_prec(Ctx0),
    above(text("try"),
          above(
            maybe_above(
              maybe_above(
                nestc(Ctx, pp_body(Body, Ctx)),
                pp_try_catch_clauses(Clauses, Ctx)),
              pp_try_after(AfterBody, Ctx)),
            text("end")));

pp({'try', _, Expr, OfCases, Clauses, AfterBody}, Ctx0) ->
    Ctx = reset_prec(Ctx0),
    abovel([besidel([text("try "), pp_body(Expr, Ctx)]),
            maybe_above(
              maybe_above(nestc(Ctx, pp_case_clauses(OfCases, Ctx)),
                          pp_try_catch_clauses(Clauses, Ctx)),
              pp_try_after(AfterBody, Ctx)),
            text("end")]);

% receive no after
pp({'receive', _, Clauses}, Ctx0) ->
    Ctx = reset_prec(Ctx0),
    abovel([text("receive"),
            pp_case_clauses(Clauses, Ctx),
            text("end")]);

pp({'receive', _, [], AfterExpr, AfterBody}, Ctx0) ->
    Ctx = reset_prec(Ctx0),
    abovel([besidel([text("receive"), text(" after "), pp(AfterExpr, Ctx), colon_f()]),
            nestc(Ctx, pp_body(AfterBody, Ctx)),
            text("end")]);
pp({'receive', _, Clauses, AfterExpr, AfterBody}, Ctx0) ->
    Ctx = reset_prec(Ctx0),
    abovel([text("receive"),
            pp_case_clauses(Clauses, Ctx),
            besidel([text("after "), pp(AfterExpr, Ctx), colon_f()]),
            nestc(Ctx, pp_body(AfterBody, Ctx)),
            text("end")]);

pp({'if', _, Clauses}, Ctx) ->
    pp_if_clauses(Clauses, Ctx, first);

pp({'case', _, Expr, Clauses}, Ctx) ->
    % keep `match EXPR:` header on one line (newline before `:` is illegal)
    above(besidel([text("match "), pp(Expr, Ctx), colon_f()]),
          above(pp_case_clauses(Clauses, Ctx),
                text("end")));

% special case one clause, put it in the same line
pp({'fun', _, {clauses, [Clause]}}, Ctx) ->
    above(pp_case_clause(Clause, Ctx, "fn case"),
          text("end"));
pp({'fun', _, {clauses, Clauses}}, Ctx) ->
    above(sep([text("fn"), pp_case_clauses(Clauses, Ctx)]),
          text("end"));

pp({named_fun, _, AName, Clauses}, Ctx) ->
    above(sep([text("fn " ++ atom_to_list(AName)), pp_case_clauses(Clauses, Ctx)]),
          text("end"));
pp({function, _, Name, Arity, Clauses}, Ctx) ->
    IsExported = function_exported(Ctx, Name, Arity),
    % HACK: force a new line above each top level function.
    % avoid a trailing space when the function has no @public attribute
    Header = case IsExported of
                 true -> besidel([text("\nfn "), quote_atom(Name), text(" @public")]);
                 false -> besidel([text("\nfn "), quote_atom(Name)])
             end,
    % @spec/@doc/... annotations live between the `fn` header and the clauses
    Body = abovel(pp_fn_annotations(Name, Arity, Ctx)
                  ++ [pp_case_clauses(Clauses, Ctx)]),
    above(Header, above(Body, text("end")));

pp({eof, _}, _Ctx) -> empty().

% render the @spec and @doc/... annotations of a function as a list of layouts
% (one per line), to be placed between the `fn` header and its clauses
pp_fn_annotations(Name, Arity, Ctx) ->
    Specs = [pp_spec_annotation(T, Ctx)
             || T <- maps:get({Name, Arity}, Ctx#ctxt.specs, [])],
    % @public is already shown on the header, so skip it here
    Attrs = [pp_fn_attr(A, Ctx)
             || A={Path, _} <- maps:get({Name, Arity}, Ctx#ctxt.fnattrs, []),
                Path =/= [public]],
    Specs ++ Attrs.

pp_spec_annotation({type, _, bounded_fun, [FunType, _Constraints]}, Ctx) ->
    pp_spec_annotation(FunType, Ctx);
pp_spec_annotation({type, _, 'fun', [{type, _, product, ArgTypes}, RetType]}, Ctx) ->
    besidel([text("@spec"),
             wrap_paren(join(ArgTypes, Ctx, fun pp_type/2, comma_f())),
             text(" -> "), pp_type(RetType, Ctx)]).

% a fn_attr is {[atom(), ...], {Args, Ret}} e.g. {[http, get], {["/p"], json}};
% Args/Ret are raw terms and Ret == [] means "no -> clause"
pp_fn_attr({Path, {Args, Ret}}, _Ctx) ->
    PathTxt = "@" ++ lists:join(".", [atom_to_list(P) || P <- Path]),
    Head = case Args of
               [] -> text(PathTxt);
               _ -> beside(text(PathTxt), wrap_paren(join_terms(Args)))
           end,
    case Ret of
        [] -> Head;
        _ -> besidel([Head, text(" -> "), pp_term(Ret)])
    end.

join_terms([T]) -> pp_term(T);
join_terms([H | T]) -> besidel([pp_term(H), comma_f(), text(" "), join_terms(T)]).

% render a raw Erlang term (fn_attr argument) as efene source
pp_term(V) when is_atom(V) -> quote_atom(V);
pp_term(V) when is_integer(V) -> text(integer_to_list(V));
pp_term(V) when is_float(V) -> text(io_lib:write(V));
pp_term(V) when is_list(V) ->
    case io_lib:printable_unicode_list(V) of
        true -> text(io_lib:write_string(V));
        false -> wrap_list(join_terms(V))
    end;
pp_term(V) -> text(io_lib:write(V)).

pp_bin_es(Es, Ctx) -> join(Es, Ctx, fun pp_bin_e/2, comma_f()).

pp_bin_e({bin_element, _, Left, default, [binary]}, Ctx) ->
    wrap_pair(Ctx, colon_f(), pp(Left, Ctx), text("binary"));
pp_bin_e({bin_element, _, Left, Size, default}, Ctx) when Size =/= default ->
    wrap_pair(Ctx, colon_f(), pp(Left, Ctx), pp(Size, Ctx));
pp_bin_e({bin_element, _, Left, default, default}, Ctx) ->
    wrap_pair(Ctx, colon_f(), pp(Left, Ctx), text("_"));
pp_bin_e({bin_element, _, Left, Size, Types}, Ctx) ->
    TypeMap = pp_bin_e_types(Types, Size, Ctx),
    wrap_pair(Ctx, colon_f(), pp(Left, Ctx), TypeMap).

pp_bin_e_types(Types, Size, Ctx) ->
    pp_bin_e_types([{size, Size} | Types], Ctx).

pp_bin_e_types(Types, Ctx) ->
    wrap_map(join(Types, Ctx, fun pp_bin_e_type/2, comma_f())).

pp_attr_pair(Ctx, KeyTxt, ValTxt) ->
    wrap_pair(Ctx, colon_f(), text(KeyTxt), text(ValTxt)).

pp_bin_e_type({size, default}, _Ctx) -> empty();
pp_bin_e_type({size, V}, Ctx) ->
    wrap_pair(Ctx, colon_f(), text("size"), pp(V, Ctx));

pp_bin_e_type({unit, V}, Ctx) ->
    pp_attr_pair(Ctx, "unit", integer_to_list(V));

pp_bin_e_type(Type=integer, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=float, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=binary, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=bytes, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=bitstring, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=bits, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=utf8, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=utf16, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));
pp_bin_e_type(Type=utf32, Ctx) ->
    pp_attr_pair(Ctx, "type", atom_to_list(Type));

pp_bin_e_type(Type=signed, Ctx) ->
    pp_attr_pair(Ctx, "sign", atom_to_list(Type));
pp_bin_e_type(Type=unsigned, Ctx) ->
    pp_attr_pair(Ctx, "sign", atom_to_list(Type));

pp_bin_e_type(Type=big, Ctx) ->
    pp_attr_pair(Ctx, "endianness", atom_to_list(Type));
pp_bin_e_type(Type=little, Ctx) ->
    pp_attr_pair(Ctx, "endianness", atom_to_list(Type));
pp_bin_e_type(Type=native, Ctx) ->
    pp_attr_pair(Ctx, "endianness", atom_to_list(Type)).


pp_call(FName, Args, Ctx) ->
    pp_call_f(FName, Args, Ctx, fun pp_elem/2).

pp_call(MName, FName, Args, Ctx) ->
    pp_call_f(MName, FName, Args, Ctx, fun pp_elem/2).

pp_call_f(FName, Args, Ctx, PPFun) ->
    beside(pp_call_pos(FName, Ctx), pp_args(Args, Ctx, PPFun)).

pp_call_f(MName, FName, Args, Ctx, PPFun) ->
    beside(wrap(dot_f(), pp_call_pos(MName, Ctx),  pp_call_pos(FName, Ctx)), pp_args(Args, Ctx, PPFun)).

pp_map(Items, Ctx) ->
    wrap_map(join(Items, Ctx, fun pp_pair/2, comma_f())).

pp_type_map(Items, Ctx) ->
    wrap_map(join(Items, Ctx, fun pp_pair_type/2, comma_f())).

pp_lc_gens(Items, Ctx) ->
    join(Items, Ctx, fun pp_lc_gen/2, scolon_f()).

pp_lc_gen({generate, _, Left, Right}, Ctx) ->
    % parenthesize the source so low-precedence sources (e.g. `H :: T`) parse
    wrap(text(" in "), pp(Left, Ctx), pp_gen_src(Right, Ctx));
% if there's a b_generate the for loop should be tagged with #b so it should be
% handled as a b_generate anyway?
pp_lc_gen({b_generate, _, Left, Right}, Ctx) ->
    wrap(text(" in "), pp(Left, Ctx), pp_gen_src(Right, Ctx));
pp_lc_gen(Filter, Ctx) ->
    beside(text("when "), pp(Filter, Ctx)).

pp_for(Gens, Ctx, BodyL, Kw) ->
    % keep the `for ... :` header on one line (newline-significant grammar);
    % sub-expression parens are added at element sites via pp_elem/2
    above(besidel([text(Kw ++ " "), pp_lc_gens(Gens, Ctx), colon_f()]),
          above(nestc(Ctx, BodyL),
                text("end"))).

wrap_list(Items) ->
    wrap(Items, olist_f(), clist_f()).

wrap_map(Items) ->
    wrap(Items, omap_f(), cmap_f()).

wrap_paren(Items) ->
    wrap(Items, oparen_f(), cparen_f()).

wrap(Items, Open, Close) ->
    beside(Open, beside(Items, Close)).

abovel([]) -> empty();
abovel([H]) -> H;
% maybe skip empty() here?
abovel([H | T]) -> above(H, abovel(T)).

besidel([]) -> empty();
besidel([H]) -> H;
besidel([H | T]) -> beside(H, besidel(T)).

% null is empty()
maybe_above(L, null) -> L;
maybe_above(null, L) -> L;
maybe_above(LLeft, LRight) -> above(LLeft, LRight).

nestc(Ctx, Layout) ->
    nest(Ctx#ctxt.sub_indent, Layout).

followc(Ctx, L1, L2) ->
    follow(L1, L2, Ctx#ctxt.sub_indent * 2).

parc(Ctx, L) ->
    par(L, Ctx#ctxt.sub_indent).

pp_try_catch_clauses([], _Ctx) -> empty();
pp_try_catch_clauses(Clauses, Ctx) ->
    above(text("catch"),
          nestc(Ctx, pp_try_catch_cases(Clauses, Ctx))).

pp_try_after([], _Ctx) -> empty();
pp_try_after(Body, Ctx) ->
    above(text("after"), nestc(Ctx, pp_body(Body, Ctx))).


pp_try_catch_cases([], _Ctx) -> empty();
pp_try_catch_cases([H | T], Ctx) ->
    above(pp_try_catch_case(H, Ctx), pp_try_catch_cases(T, Ctx)).

pp_try_catch_case({clause, _, [{tuple, _, TItems}], [], Body}, Ctx) ->
    pp_header_and_body(Ctx,
                       beside(text("case "), beside(pp_try_catch_case_items(TItems, Ctx), colon_f())),
                       Body);
pp_try_catch_case({clause, _, [{tuple, _, TItems}], Guards, Body}, Ctx) ->
    pp_header_and_body(Ctx,
                       followc(Ctx,
                               beside(text("case "), pp_try_catch_case_items(TItems, Ctx)),
                               beside(text("when "), beside(pp_guards(Guards, Ctx), colon_f()))),
                       Body).

pp_try_catch_case_items([{atom, _, throw}, Var, {var, _, '_'}], Ctx) ->
    pp(Var, Ctx);
pp_try_catch_case_items([Type, Var, {var, _, '_'}], Ctx) ->
    pp_items([Type, Var], Ctx);
pp_try_catch_case_items([Type, Var, StackTrace], Ctx) ->
    pp_items([Type, Var, StackTrace], Ctx).

pp_call_pos(V={var, _, _}, Ctx) -> pp(V, Ctx);
pp_call_pos(V={atom, _, _}, Ctx) -> pp(V, Ctx);
pp_call_pos(V, Ctx) -> beside(oparen_f(), beside(pp(V, Ctx), cparen_f())).

pp_args([], _Ctx, _PPFun) -> text("()");
pp_args(Args, Ctx, PPFun) ->
    beside(oparen_f(), beside(pp_args_inn(Args, Ctx, PPFun), cparen_f())).

pp_args_inn(Args, Ctx) -> pp_args_inn(Args, Ctx, fun pp/2).

pp_args_inn([], _Ctx, _PPFun)   -> empty();
pp_args_inn([Arg], Ctx, PPFun) -> PPFun(Arg, Ctx);
pp_args_inn(Args, Ctx, PPFun)  -> join(Args, Ctx, PPFun, comma_f()).

pp_case_clauses([Clause], Ctx) ->
    pp_case_clause(Clause, Ctx);
pp_case_clauses([Clause | Clauses], Ctx) ->
    above(pp_case_clause(Clause, Ctx), pp_case_clauses(Clauses, Ctx)).

pp_case_clause(Clause, Ctx) ->
    pp_case_clause(Clause, Ctx, "case").

pp_case_clause({clause, _, [], [], Body}, Ctx, Kw) ->
    pp_header_and_body(Ctx, text(Kw ++ ":"), Body);
pp_case_clause({clause, _, Patterns, [], Body}, Ctx, Kw) ->
    pp_header_and_body(Ctx,
                       beside(text(Kw ++ " "), beside(pp_args_inn(Patterns, Ctx), colon_f())),
                       Body);
pp_case_clause({clause, _, Patterns, Guards, Body}, Ctx, Kw) ->
    pp_header_and_body(Ctx,
                       followc(Ctx,
                               beside(text(Kw ++ " "), pp_args_inn(Patterns, Ctx)),
                               beside(text("when "), beside(pp_guards(Guards, Ctx), colon_f()))),
                       Body).

pp_if_clauses([Clause], Ctx, GuardPos) ->
    NewGuardPos = if GuardPos == first -> first; true -> last end,
    above(pp_if_clause(Clause, Ctx, NewGuardPos),
          text("end"));
pp_if_clauses([Clause | Clauses=[_|_]], Ctx, GuardPos) ->
    above(pp_if_clause(Clause, Ctx, GuardPos),
          pp_if_clauses(Clauses, Ctx, middle)).

pp_if_clause({clause, _, _, [[{atom, _, true}]], Body}, Ctx, last) ->
    pp_header_and_body(Ctx, text("else:"), Body);
pp_if_clause({clause, _, _, Guards, Body}, Ctx, first) ->
    pp_header_and_body(Ctx,
                       pp_if_header(Ctx, "when ", Guards),
                       Body);
pp_if_clause({clause, _, _, Guards, Body}, Ctx, _) ->
    pp_header_and_body(Ctx,
                       pp_if_header(Ctx, "else ", Guards),
                       Body).

pp_if_header(Ctx, KwT, Guards) ->
    beside(text(KwT), beside(pp_guards(Guards, Ctx), colon_f())).

pp_header_and_body(Ctx, HeaderLayout, Body) ->
    sep([HeaderLayout, nestc(Ctx, pp_body(Body, Ctx))]).

pp_guards(Guards, Ctx) ->
    join(Guards, Ctx, fun pp_guard/2, scolon_f()).

pp_guard(SGuards, Ctx) ->
    join(SGuards, Ctx, fun pp/2, comma_f()).

join(Items, Ctx, PPFun, Sep) ->
    join(Items, Ctx, PPFun, Sep, []).

join([], _Ctx, _PPFun, _Sep, []) ->
    empty();
join([Item], Ctx, PPFun, _Sep, []) ->
    PPFun(Item, Ctx);
join([Item], Ctx, PPFun, _Sep, Accum) ->
    par(lists:reverse([PPFun(Item, Ctx) | Accum]), 2);
join([H | T=[_|_]], Ctx, PPFun, Sep, Accum) ->
    join(T, Ctx, PPFun, Sep, [beside(PPFun(H, Ctx), Sep) | Accum]);
join([H | T], Ctx, PPFun, Sep, Accum) ->
    join([T], Ctx, PPFun, Sep, [beside(PPFun(H, Ctx), Sep) | Accum]).

pp_items(Items, Ctx) ->
    join(Items, Ctx, fun pp/2, comma_f()).

pp_pair({map_field_assoc, _, K, V}, Ctx) ->
    wrap_pair(Ctx, colon_f(), pp(K, Ctx), pp_elem(V, Ctx));
pp_pair({map_field_exact, _, K, V}, Ctx) ->
    wrap_pair_eq(Ctx, pp(K, Ctx), pp_elem(V, Ctx)).

% Some constructs are only valid bare in statement/RHS position; in a
% sub-expression (element) position they need parens. Examples:
%   match as map value `k=(v=w)`, `for`/`if` as map value or call arg.
pp_elem(V, Ctx) ->
    case needs_elem_paren(V) of
        true -> wrap_paren(pp(V, Ctx));
        false -> pp(V, Ctx)
    end.

needs_elem_paren({match, _, _, _}) -> true;
needs_elem_paren({'if', _, _}) -> true;
needs_elem_paren({lc, _, _, _}) -> true;
needs_elem_paren({bc, _, _, _}) -> true;
needs_elem_paren(_) -> false.

% the source of a generator needs parens for low-precedence forms like
% an improper cons: `for X in ((a, b) :: T):`
pp_gen_src(V={cons, _, _, _}, Ctx) ->
    case is_proper_cons(V) of
        true -> pp(V, Ctx);
        false -> wrap_paren(pp(V, Ctx))
    end;
pp_gen_src(V, Ctx) -> pp_elem(V, Ctx).

is_proper_cons(V) -> is_proper_list(cons_to_list(V, [])).

is_proper_list([]) -> true;
is_proper_list([_ | T]) -> is_proper_list(T);
is_proper_list(_) -> false.

pp_pair_type({type, _, map_field_assoc, [K, V]}, Ctx) ->
    wrap_pair(Ctx, colon_f(), pp_type(K, Ctx), pp_type(V, Ctx));
pp_pair_type({type, _, map_field_exact, [K, V]}, Ctx) ->
    wrap_pair_eq(Ctx, pp_type(K, Ctx), pp_type(V, Ctx)).

wrap_pair(Ctx, Sep, Left, Right) ->
    parc(Ctx, [beside(Left, Sep), Right]).

% like wrap_pair but with a spaced `=` separator: `Left = Right`.
% the `=` must stay attached to the key (a break before `=` is illegal),
% so only the value may wrap onto the next line
wrap_pair_eq(Ctx, Left, Right) ->
    parc(Ctx, [beside(Left, text(" =")), Right]).

pp_rec_pair({record_field, _, K, V}, Ctx) ->
    parc(Ctx, [beside(pp(K, Ctx), colon_f()), pp_elem(V, Ctx)]).

% a single-field record needs a trailing comma, else `(field)` parses as a
% parenthesized expression instead of a one-element field list
pp_rec_fields([Field], Ctx) ->
    beside(pp_rec_def(Field, Ctx), comma_f());
pp_rec_fields(Fields, Ctx) ->
    join(Fields, Ctx, fun pp_rec_def/2, comma_f()).

pp_rec_def({record_field, _, Name}, Ctx) -> pp(Name, Ctx);
pp_rec_def({record_field, _, Name, Val}, Ctx) -> besidel([pp(Name, Ctx), text(" = "), pp(Val, Ctx)]);
pp_rec_def({typed_record_field, {record_field, _, Name}, Type}, Ctx) ->
    followc(Ctx, beside(pp(Name, Ctx), text(" is")), pp_type(Type, Ctx));
pp_rec_def({typed_record_field, {record_field, _, Name, Val}, Type}, Ctx) ->
    followc(Ctx, beside(besidel([pp(Name, Ctx), text(" = "), pp(Val, Ctx)]), text(" is")), pp_type(Type, Ctx)).

pp_type({ann_type, _, [Type, AnnType]}, Ctx) ->
    wrap(text(" is "), pp_type(Type, Ctx), pp_type(AnnType, Ctx));
pp_type(V={op, _, _, _}, Ctx) -> pp(V, Ctx);
pp_type(V={op, _, _, _, _}, Ctx) -> pp(V, Ctx);
pp_type(V={atom, _, _}, Ctx) -> pp(V, Ctx);
pp_type(V={var, _, _}, Ctx) -> pp(V, Ctx);
pp_type(V={integer, _, _}, Ctx) -> pp(V, Ctx);
pp_type({user_type, Line, Name, Args}, Ctx) ->
    pp_call_f({atom, Line, Name}, Args, Ctx, fun pp_type/2);

pp_type({type, _, tuple, any}, _Ctx) ->
    text("tuple()");
pp_type({type, _, map, any}, _Ctx) ->
    text("map()");
pp_type({type, _, list, []}, _Ctx) ->
    text("list()");

% function types: `fun()`, `fun(any, Ret)`, `fun([Arg, ...], Ret)`
pp_type({type, _, 'fun', []}, _Ctx) ->
    text("fun()");
pp_type({type, _, 'fun', [{type, _, any}, RetType]}, Ctx) ->
    besidel([text("fun(any, "), pp_type(RetType, Ctx), cparen_f()]);
pp_type({type, _, 'fun', [{type, _, product, Args}, RetType]}, Ctx) ->
    besidel([text("fun("),
             wrap_list(join(Args, Ctx, fun pp_type/2, comma_f())),
             text(", "), pp_type(RetType, Ctx), cparen_f()]);

pp_type({type, _, tuple, [Item]}, Ctx) ->
    wrap_paren(beside(pp_type(Item, Ctx), comma_f()));
pp_type({type, _, tuple, Items}, Ctx) ->
    wrap_paren(join(Items, Ctx, fun pp_type/2, comma_f()));
pp_type({type, _, list, Args}, Ctx) ->
    wrap_list(join(Args, Ctx, fun pp_type/2, comma_f()));
pp_type({type, _, map, Args}, Ctx) ->
    pp_type_map(Args, Ctx);
    %wrap_map(join(Args, Ctx, fun pp_type_map/2, comma_f()));
pp_type({type, _, union, Args}, Ctx) ->
    wrap_list(join(Args, Ctx, fun pp_type/2, text(" or")));
pp_type({remote_type, _, [AMod, AFName, Args]}, Ctx) ->
    pp_call_f(AMod, AFName, Args, Ctx, fun pp_type/2);
pp_type({type, Line, Name, Args}, Ctx) ->
    pp_call_f({atom, Line, Name}, Args, Ctx, fun pp_type/2).

pp_cons(V, Ctx) ->
    case cons_to_list(V, []) of
        [A | B] when not is_list(A), not is_list(B) ->
            besidel([pp(A, Ctx), text(" :: "), pp(B, Ctx)]);
        [A | B] when not is_list(B) ->
            besidel([wrap_list(pp_items(A, Ctx)), text(" :: "), pp(B, Ctx)]);
        L -> wrap_list(pp_items(L, Ctx))
    end.

cons_to_list({cons, _, H, {nil, _}}, Accum) ->
    % proper list tail
    lists:reverse([H | Accum]);
cons_to_list({cons, _, H, T={cons, _, _, _}}, Accum) ->
    cons_to_list(T, [H | Accum]);
cons_to_list({cons, _, H, T}, []) ->
    [H | T];
cons_to_list({cons, _, H, T}, Accum) ->
    % improper list
    [lists:reverse([H | Accum]) | T].

% not sure if the best way
pp_body([], _Ctx) ->
    empty();
pp_body([H | T], Ctx) ->
    above(pp(H, Ctx), pp_body(T, Ctx)).

olist_f() -> floating(text("[")).
clist_f() -> floating(text("]")).
oparen_f() -> floating(text("(")).
cparen_f() -> floating(text(")")).
omap_f() -> floating(text("{")).
cmap_f() -> floating(text("}")).

comma_f() -> floating(text(",")).
dot_f() -> floating(text(".")).
colon_f() -> floating(text(":")).
scolon_f() -> floating(text(";")).

maybe_paren(P, Prec, Expr) when P < Prec ->
    beside(beside(oparen_f(), Expr), cparen_f());
maybe_paren(_P, _Prec, Expr) ->
    Expr.

set_prec(Ctxt, Prec) ->
    Ctxt#ctxt{prec = Prec}.    % used internally

reset_prec(Ctxt) ->
    set_prec(Ctxt, 0).    % used internally

quote_atom(V) ->
    text(quote_atom_raw(V)).

quote_atom_raw(V) ->
    Chars = atom_to_list(V),
    % will quote all erlang reserved words, I think it's ok
    case io_lib:quote_atom(V, Chars) of
        true -> io_lib:write_string(Chars, $`);
        false ->
            case fn_lexer:is_reserved(Chars) of
                true -> io_lib:write_string(Chars, $`);
                false -> Chars
            end
    end.
