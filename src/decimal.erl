%% @author Hunter Morris <hunter.morris@smarkets.com>
%% @copyright 2011 Smarkets Limited.

%% @doc Decimal operations based on the General Decimal Arithmetic
%% Specification:
%%
%% http://www2.hursley.ibm.com/decimal/decarith.html
%%
%% and also IEEE standard 854-1987:
%%
%% http://www.cs.berkeley.edu/~ejr/projects/754/private/drafts/854-1987/dir.html
%%
%% This should support arithmetic using basic rules, avoiding a good deal of
%% the tricky representation issues associated with binary floating
%% point. The obvious use is for representing money where 1.00 rem 0.1 gives
%% 0.09999999999999995 instead of the expected 0.00 when dealing with normal
%% decimal operations.

-module(decimal).
-author('Hunter Morris <hunter.morris@smarkets.com>').

% Conversion methods
-export([to_decimal/1, to_decimal/2, to_list/1, to_list/2, to_list/3, to_integer/1]).

% Predicates
-export([is_nan/1, is_infinite/1, is_finite/1, is_int/1, is_normal/2, is_signed/1, is_nonzero/1]).

% Operations
-export([add/2, add/3, sub/2, sub/3, mult/2, mult/3, divide/2, divide/3,
         divide_int/2, divide_int/3, neg/1, abs/1, abs/2, minus/1, minus/2,
         plus/1, plus/2, copy_abs/1, copy_negate/1, copy_sign/2,
         logical_and/2, logical_and/3]).

% Quantize methods
-export([quantize/2, quantize/3]).

% Comparisons
-export([compare/2, compare/3, compare_total/2, compare_total_mag/2]).
-export([lt/2, le/2, gt/2, ge/2, eq/2, ne/2, cmp/2]).

% Standard
-export([apply/2, apply/1, class/2, class/1]).

% Context-related (perhaps the process dictionary usage here is a bad idea?)
-export([set_context/1, get_context/0]).

%% Useful constants
-export([zero/0]).

-include("decimal.hrl").

-compile({inline, [{set_trap,2},
                   {get_trap,2},
                   {adjusted, 1},
                   {inf_signs,1}]}).

-define(CONTEXT_KEY, '__decimal_context').

-define(_DEBUG_LOG_ARGS(A, B), io:format(A, B)).
-define(_DEBUG_LOG(A), io:format(A)).

-define(INF_STR, "Infinity").
-define(NAN_STR, "NaN").
-define(SNAN_STR, "sNaN").
-define(IS_DIGIT(D), (is_integer(D) and (D >= $0) and (D =< $9))).
-define(IS_SIGN(D), ((D =:= $+) or (D =:= $-))).
-define(IS_SPECIAL(D), (is_atom(D#d.exp))).
-define(IS_NAN(D), ((D#d.exp =:= ?dnan) or (D#d.exp =:= ?dsnan))).
-define(IS_SNAN(D), (D#d.exp =:= ?dsnan)).
-define(IS_INFINITY(D), (D#d.exp =:= ?dinf)).

-define(INF, #d{exp=?dinf}).
-define(NEG_INF, (?INF)#d{sign=1}).
-define(NAN, #d{exp=?dnan}).
-define(DEC_P1, #d{coeff=1}).
-define(DEC_N1, #d{sign=1, coeff=1}).
-define(ZERO, #d{sign=0, coeff=0, exp=0}).

-define(ETINY(C), (C#context.emin - C#context.prec + 1)).
-define(ETOP(C), (C#context.emax - C#context.prec + 1)).
-define(ECAPS(C), (case C of true -> "E"; _ -> "e" end)).

-define(OUTPUT_SIGNS(Sign), (if Sign =:= 1 -> "-"; true -> "" end)).
-define(INF_TYPE(D), case D of
                         #d{sign=1, exp=?dinf} -> -1;
                         #d{exp=?dinf}         ->  1;
                         D when ?is_decimal(D)            ->  0
                     end).
-define(is_decimal(D), is_record(D, d)).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-define(TO_D_TO_L(A), to_list(to_decimal(A))).
-endif.

%% Parser context
-record(pctx, {
          orig=[],
          sign=0,
          coeff=[],
          frac=[],
          exp=[],
          exp_sign=0,
          infinity=false,
          signal=false,
          nan=false,
          diag=[]
         }).

to_list(D) when ?is_decimal(D) ->
    to_list(D, false).

to_list(D, Eng) when ?is_decimal(D) ->
    ctx_op(fun to_list/3, [D, Eng]).

to_list(#d{exp=?dinf, sign=S}, _, C) ->
    {?OUTPUT_SIGNS(S) ++ ?INF_STR, C};
to_list(#d{exp=?dnan, sign=S, coeff=0}, _, C) ->
    {?OUTPUT_SIGNS(S) ++ ?NAN_STR, C};
to_list(#d{exp=?dnan, sign=S, coeff=I}, _, C) ->
    {?OUTPUT_SIGNS(S) ++ ?NAN_STR ++ integer_to_list(I), C};
to_list(#d{exp=?dsnan, sign=S, coeff=0}, _, C) ->
    {?OUTPUT_SIGNS(S) ++ ?SNAN_STR, C};
to_list(#d{exp=?dsnan, sign=S, coeff=I}, _, C) ->
    {?OUTPUT_SIGNS(S) ++ ?SNAN_STR ++ integer_to_list(I), C};
to_list(#d{sign=S, exp=Exp, coeff=Int}=D, Eng, #context{capitals=Caps}=C) ->
    IntStr = integer_to_list(Int),
    LeftDigits = Exp + length(IntStr),
    DotPlace = dot_place(D, Eng, LeftDigits),
    {IntPart, FracPart} = int_frac_parts(DotPlace, IntStr),
    ExpStr = exp_str(LeftDigits, DotPlace, Caps),
    {?OUTPUT_SIGNS(S) ++ IntPart ++ FracPart ++ ExpStr, C}.

exp_str(LeftDigits, LeftDigits, _) ->
    [];
exp_str(LeftDigits, DotPlace, Caps) ->
    ExpE = ?ECAPS(Caps),
    case LeftDigits - DotPlace of
        NewExp when NewExp < 0 ->
            ExpE ++ integer_to_list(NewExp);
        NewExp ->
            ExpE ++ "+" ++ integer_to_list(NewExp)
    end.

dot_place(#d{exp=Exp}, _, LeftDigits) when Exp =< 0, LeftDigits > -6 ->
    LeftDigits;
dot_place(_, false, _) ->
    1;
dot_place(#d{coeff=0}, _, LeftDigits) ->
    frem((LeftDigits + 1), 3) - 1;
dot_place(_, _, LeftDigits) ->
    frem((LeftDigits - 1), 3) + 1.

frem(A, B) when (A < 0) and (B > 0) ->
    frem1(erlang:abs(A rem B), B);
frem(A, B) ->
    A rem B.

frem1(0, _) ->
    0;
frem1(R, B) ->
    B - R.

int_frac_parts(DotPlace, IntStr) when DotPlace =< 0 ->
    {"0", "." ++ zero_list(-1 * DotPlace, IntStr)};
int_frac_parts(DotPlace, IntStr) when DotPlace >= length(IntStr) ->
    {IntStr ++ zero_list(DotPlace - length(IntStr)), []};
int_frac_parts(DotPlace, IntStr) ->
    {IntPart, F} = lists:split(DotPlace, IntStr),
    {IntPart, "." ++ F}.

to_decimal(In) ->
    case to_decimal(In, undefined) of
        {D, undefined} ->
            D;
        {D, Ctx} ->
            set_context(Ctx),
            D
    end.

to_decimal(#d{} = D, Ctx) -> {D, Ctx};
to_decimal({Sign, Coeff, Exp}, Ctx) ->
    fix_new_decimal(#d{sign = Sign, coeff = Coeff, exp = Exp}, Ctx);
to_decimal(F, _) when is_float(F) ->
    throw({error, "Cannot create decimal from float. Convert to list first."});
to_decimal(I, Ctx) when is_integer(I), I >= 0 ->
    fix_new_decimal(integer_to_decimal(I, #d{sign=0}), Ctx);
to_decimal(I, Ctx) when is_integer(I) ->
    fix_new_decimal(integer_to_decimal(I, #d{sign=1}), Ctx);
to_decimal(B, Ctx) when is_binary(B) ->
    to_decimal(binary_to_list(B), Ctx);
to_decimal(L, Ctx) when is_list(L), length(L) > 0 ->
    to_decimal(safe_parse(L), Ctx);
to_decimal(#pctx{infinity=true, sign=S}, Ctx) ->
    fix_new_decimal(#d{sign=S, exp=?dinf}, Ctx);
to_decimal(#pctx{sign=S, nan=true, signal=true, diag=D}, Ctx) ->
    fix_new_decimal(#d{sign=S, exp=?dsnan, coeff=diag_coeff(D)}, Ctx);
to_decimal(#pctx{sign=S, nan=true, signal=false, diag=D}, Ctx) ->
    fix_new_decimal(#d{sign=S, exp=?dnan, coeff=diag_coeff(D)}, Ctx);
to_decimal(#pctx{sign=S, coeff=I, frac=F, exp=E, exp_sign=Es}, Ctx) ->
    fix_new_decimal(#d{sign=S, coeff=list_to_integer(I ++ F), exp=exp_from_list(E, Es, length(F))}, Ctx);
to_decimal({error, L}, Ctx) ->
    to_decimal_error(L, Ctx);
to_decimal(L, Ctx) ->
    to_decimal_error(L, Ctx).

to_decimal_error(L, undefined) ->
    to_decimal_error(L, get_context());
to_decimal_error(L, Ctx) ->
    Msg = lists:flatten(io_lib:format("Invalid literal for decimal: ~p", [L])),
    raise_error(Ctx, invalid_operation, Msg, []).

fix_new_decimal(D, undefined) ->
    {D, undefined};
fix_new_decimal(D, Ctx) when ?IS_NAN(D) ->
    Clamp = case Ctx#context.clamp of true -> 1; _ -> 0 end,
    case length(integer_to_list(D#d.coeff)) of
        L when L > (Ctx#context.prec - Clamp) ->
            raise_error(Ctx, invalid_operation, "diagnostic info too long in NaN", []);
        _ ->
            fix(D, Ctx)
    end;
fix_new_decimal(D, Ctx) ->
    fix(D, Ctx).

exp_from_list([], _, F) ->
    0 - F;
exp_from_list(E, Es, F) when is_list(E) ->
    (list_to_integer(E) * sign_mult(Es)) - F.

diag_coeff([]) ->
    0;
diag_coeff(D) when is_list(D) ->
    list_to_integer(D).

-ifdef(EUNIT).

explicit_from_int_test_() ->
    [?_assert(?TO_D_TO_L(45) =:= "45"),
     ?_assert(?TO_D_TO_L(500000123) =:= "500000123"),
     ?_assert(?TO_D_TO_L(-45) =:= "-45"),
     ?_assert(?TO_D_TO_L(0) =:= "0")].

explicit_from_string_test_() ->
    [?_assert(?TO_D_TO_L("45") =:= "45"),
%%     ?_assert(?TO_D_TO_L([]) =:= "NaN"),
     ?_assert(?TO_D_TO_L("45.34") =:= "45.34"),
     ?_assert(?TO_D_TO_L("45e2") =:= "4.5E+3"),
%%     ?_assert(?TO_D_TO_L("ugly") =:= "NaN"),
%%     ?_assert(?TO_D_TO_L("1.3E4 \n") =:= "1.3E+4"),
%%     ?_assert(?TO_D_TO_L("  -7.89") =:= "-7.89"),
     ?_assert(?TO_D_TO_L("0E-017") =:= "0E-17"),
     ?_assert(?TO_D_TO_L("-Inf") =:= "-Infinity"),
     ?_assert(?TO_D_TO_L("NaN123") =:= "NaN123")].

explicit_from_records_test_() ->
    [?_assert(to_list(#d{sign=0, coeff=0, exp=0}) =:= "0"),
     ?_assert(to_list(#d{sign=1, coeff=45, exp=0}) =:= "-45"),
     ?_assert(to_list(#d{sign=0, coeff=4534, exp=-2}) =:= "45.34"),
     ?_assert(to_list(#d{sign=1, coeff=434913534, exp=-25}) =:= "-4.34913534E-17")].

-endif.

integer_to_decimal(I, D) ->
    D#d{exp=0, coeff=erlang:abs(I)}.

is_nan(#d{exp=?dnan}) ->
    true;
is_nan(D) when ?is_decimal(D) ->
    false.

is_infinite(#d{exp=?dinf}) ->
    true;
is_infinite(D) when ?is_decimal(D) ->
    false.

is_finite(D) when ?IS_SPECIAL(D) ->
    false;
is_finite(D) when ?is_decimal(D) ->
    true.

is_normal(D, _) when ?IS_SPECIAL(D) ->
    false;
is_normal(D, #context{emin=Emin, emax=Emax})
  when ?is_decimal(D), is_integer(Emin), is_integer(Emax) ->
    case adjusted(D) of
        A when Emin =< A, A =< Emax ->
            true;
        _ ->
            false
    end.

is_subnormal(#d{coeff=S}=D, _) when ?IS_SPECIAL(D); S =:= 0 ->
    false;
is_subnormal(D, #context{emin=E}) ->
    adjusted(D) < E.

is_int(D) when ?IS_SPECIAL(D) ->
    false;
is_int(#d{exp=E}) when E >= 0 ->
    true;
is_int(#d{coeff=I, exp=E}) ->
    Rest = sub_digits(I, E),
    0 =:= Rest.

adjusted(#d{exp=E, coeff=I}) when is_integer(E) ->
    E + length(integer_to_list(I)) - 1;
adjusted(D) when ?is_decimal(D) ->
    0.

is_signed(#d{sign=1}) ->
    true;
is_signed(D) when ?is_decimal(D) ->
    false.

%% Converts to an integer, truncating if necessary
to_integer(D) ->
    to_integer(D, get_context()).

to_integer(D, C) when ?IS_NAN(D) ->
    raise_error(C, invalid_context);
to_integer(D, _) when ?IS_SPECIAL(D) ->
    throw({error, "Overflow: cannot convert infinity to integer"});
to_integer(#d{sign=Sign, coeff=I, exp=E}, _) when E >= 0 ->
    sign_mult(Sign) * I * xmath:pow(10, E);
to_integer(#d{sign=Sign, coeff=I, exp=E}, _) ->
    sign_mult(Sign) * first_digits(I, digits(I) + E).

compare(L, R) ->
    ctx_op(fun compare/3, [L, R]).

compare(L0, R0, Ctx) ->
    L = convert_other(L0, true),
    R = convert_other(R0, true),
    compare_dec(L, R, Ctx).

compare_dec(L, R, C) when ?IS_SPECIAL(L); ?IS_SPECIAL(R) ->
    case check_nans(L, R, C) of
        false ->
            {decimal:to_decimal(cmp(L, R)), C};
        Ans ->
            Ans
    end;
compare_dec(L, R, C) ->
    {decimal:to_decimal(cmp(L, R)), C}.

%% Quiet
compare_total(#d{sign=0}, #d{sign=1}) ->
    ?DEC_P1;
compare_total(#d{sign=1}, #d{sign=0}) ->
    ?DEC_N1;
compare_total(#d{sign=0, coeff=Li, exp=?dnan}, #d{coeff=Li, exp=?dnan}) ->
    ?ZERO;
compare_total(#d{sign=0, coeff=Li, exp=?dsnan}, #d{coeff=Li, exp=?dsnan}) ->
    ?ZERO;
compare_total(#d{sign=0, coeff=Li, exp=?dnan}, #d{coeff=Ri, exp=?dnan}) when Li < Ri ->
    ?DEC_N1;
compare_total(#d{sign=0, coeff=Li, exp=?dsnan}, #d{coeff=Ri, exp=?dsnan}) when Li < Ri ->
    ?DEC_N1;
compare_total(#d{sign=0, coeff=Li, exp=?dnan}, #d{coeff=Ri, exp=?dnan}) when Li > Ri ->
    ?DEC_P1;
compare_total(#d{sign=0, coeff=Li, exp=?dsnan}, #d{coeff=Ri, exp=?dsnan}) when Li > Ri ->
    ?DEC_P1;
compare_total(#d{sign=1, coeff=Li, exp=?dnan}, #d{coeff=Li, exp=?dnan}) ->
    ?ZERO;
compare_total(#d{sign=1, coeff=Li, exp=?dsnan}, #d{coeff=Li, exp=?dsnan}) ->
    ?ZERO;
compare_total(#d{sign=1, coeff=Li, exp=?dnan}, #d{coeff=Ri, exp=?dnan}) when Li > Ri ->
    ?DEC_N1;
compare_total(#d{sign=1, coeff=Li, exp=?dsnan}, #d{coeff=Ri, exp=?dsnan}) when Li > Ri ->
    ?DEC_N1;
compare_total(#d{sign=1, coeff=Li, exp=?dnan}, #d{coeff=Ri, exp=?dnan}) when Li < Ri ->
    ?DEC_P1;
compare_total(#d{sign=1, coeff=Li, exp=?dsnan}, #d{coeff=Ri, exp=?dsnan}) when Li < Ri ->
    ?DEC_P1;
compare_total(#d{sign=1, exp=?dnan}, _) ->
    ?DEC_N1;
compare_total(#d{sign=1}, #d{exp=?dnan}) ->
    ?DEC_P1;
compare_total(#d{sign=1, exp=?dsnan}, _) ->
    ?DEC_N1;
compare_total(#d{sign=1}, #d{exp=?dsnan}) ->
    ?DEC_P1;
compare_total(#d{sign=0, exp=?dnan}, _) ->
    ?DEC_P1;
compare_total(#d{sign=0}, #d{exp=?dnan}) ->
    ?DEC_N1;
compare_total(#d{sign=0, exp=?dsnan}, _) ->
    ?DEC_P1;
compare_total(#d{sign=0}, #d{exp=?dsnan}) ->
    ?DEC_N1;
compare_total(L, R) ->
    compare_exp_total(cmp_dec(L, R), L, R).

compare_exp_total(-1, _, _) ->
    ?DEC_N1;
compare_exp_total(1, _, _) ->
    ?DEC_P1;
compare_exp_total(0, #d{sign=1, exp=L}, #d{exp=R}) when L < R ->
    ?DEC_P1;
compare_exp_total(0, #d{sign=0, exp=L}, #d{exp=R}) when L < R ->
    ?DEC_N1;
compare_exp_total(0, #d{sign=1, exp=L}, #d{exp=R}) when L > R ->
    ?DEC_N1;
compare_exp_total(0, #d{sign=0, exp=L}, #d{exp=R}) when L > R ->
    ?DEC_P1;
compare_exp_total(_, _, _) ->
    ?ZERO.

compare_total_mag(L0, R0) ->
    L = copy_abs(L0),
    R = copy_abs(R0),
    compare_total(L, R).

cmp(L0, R0) ->
    L = convert_other(L0),
    R = convert_other(R0),
    cmp_dec(L, R).

cmp_dec(L, R) when ?IS_SPECIAL(L) or ?IS_SPECIAL(R) ->
    int_cmp(?INF_TYPE(L), ?INF_TYPE(R));
cmp_dec(#d{coeff=0}, #d{coeff=0}) ->
    0;
cmp_dec(#d{coeff=0}, #d{sign=RS}) ->
    -1 * xmath:pow(-1, RS);
cmp_dec(#d{sign=LS}, #d{coeff=0}) ->
    xmath:pow(-1, LS);
cmp_dec(#d{sign=LS}, #d{sign=RS}) when RS < LS ->
    -1;
cmp_dec(#d{sign=LS}, #d{sign=RS}) when LS < RS ->
    1;
cmp_dec(L, R) ->
    Ladj = adjusted(L),
    Radj = adjusted(R),
    if Ladj =:= Radj ->
            Lpadded = list_to_integer(integer_to_list(L#d.coeff)
                                      ++ zero_list(L#d.exp - R#d.exp)),
            Rpadded = list_to_integer(integer_to_list(R#d.coeff)
                                      ++ zero_list(R#d.exp - L#d.exp)),
            xmath:pow(-1, L#d.sign) * int_cmp(Lpadded, Rpadded);
       Ladj > Radj ->
            xmath:pow(-1, L#d.sign);
       true ->
            -1 * xmath:pow(-1, L#d.sign)
    end.

is_nonzero(D) when ?IS_SPECIAL(D) ->
    true;
is_nonzero(#d{coeff=0}) ->
    false;
is_nonzero(D) when ?is_decimal(D) ->
    true.

neg(D) when ?IS_SPECIAL(D) ->
    D;
neg(D) when ?is_decimal(D) ->
    case is_nonzero(D) of
        true ->
            negate(D);
        false ->
            D#d{sign=0}
    end.

eq(L0, R0) ->
    gcmp(L0, R0, false, false, fun(I) -> I =:= 0 end).

ne(L0, R0) ->
    gcmp(L0, R0, false, true, fun(I) -> I =/= 0 end).

lt(L0, R0) ->
    gcmp(L0, R0, true, false, fun(I) -> I < 0 end).

le(L0, R0) ->
    gcmp(L0, R0, true, false, fun(I) -> I =< 0 end).

gt(L0, R0) ->
    gcmp(L0, R0, true, false, fun(I) -> I > 0 end).

ge(L0, R0) ->
    gcmp(L0, R0, true, false, fun(I) -> I >= 0 end).

gcmp(L0, R0, DoThrow, NRes, CFun) ->
    L = convert_other(L0),
    R = convert_other(R0),
    LNan = is_nan(L),
    RNan = is_nan(R),
    if LNan or RNan ->
            if DoThrow ->
                    throw("Comparison involving NaN");
               true ->
                    NRes
            end;
       true -> CFun(cmp(L, R))
    end.

ctx_op(F, Args0) ->
    Args = Args0 ++ [get_context()],
    {Res, Ctx} = erlang:apply(F, Args),
    set_context(Ctx),
    Res.

abs(D) ->
    ctx_op(fun abs/2, [D]).

abs(D, Ctx) ->
    abs(D, true, Ctx).

%% abs(D, false, _) ->
%%     copy_abs(D);
abs(D, true, Ctx) when ?IS_SPECIAL(D) ->
    case check_nans(D, Ctx) of
        false ->
            abs1(D, Ctx);
        Ans ->
            Ans
    end;
abs(D, _, Ctx) ->
    abs1(D, Ctx).

abs1(#d{sign=1}=D, Ctx) ->
    minus(D, Ctx);
abs1(#d{sign=0}=D, Ctx) ->
    plus(D, Ctx).

minus(D) ->
    ctx_op(fun minus/2, [D]).

minus(D, Ctx) when ?IS_SPECIAL(D) ->
    case check_nans(D, Ctx) of
        false ->
            minus1(D, Ctx);
        Ans ->
            Ans
    end;
minus(D, Ctx) ->
    minus1(D, Ctx).

minus1(#d{coeff=0}=D, Ctx) when not ?IS_SPECIAL(D) ->
    fix(copy_abs(D), Ctx);
minus1(D, Ctx) ->
    fix(copy_negate(D), Ctx).

plus(D) ->
    ctx_op(fun plus/2, [D]).

plus(D, Ctx) when ?IS_SPECIAL(D) ->
    case check_nans(D, Ctx) of
        false ->
            plus1(D, Ctx);
        Ans ->
            Ans
    end;
plus(D, Ctx) ->
    plus1(D, Ctx).

plus1(#d{coeff=0}=D, Ctx) when not ?IS_SPECIAL(D) ->
    fix(copy_abs(D), Ctx);
plus1(D, Ctx) ->
    fix(D, Ctx).

copy_abs(D) when ?is_decimal(D) ->
    D#d{sign=0}.

copy_negate(#d{sign=0}=D) ->
    D#d{sign=1};
copy_negate(#d{sign=1}=D) ->
    D#d{sign=0}.

copy_sign(D, #d{sign=S}) ->
    D#d{sign=S}.

add(L, R) ->
    ctx_op(fun add/3, [L, R]).

add(L0, R0, Context) ->
    L = convert_other(L0),
    R = convert_other(R0),
    add_dec(L, R, Context).

add_dec(L, R, Context) when ?IS_SPECIAL(L) or ?IS_SPECIAL(R) ->
    case check_nans(L, R, Context) of
        false ->
            add_inf(L, R, Context);
        Ans ->
            Ans
    end;
add_dec(#d{exp=Lexp, sign=Ls}=L, #d{exp=Rexp, sign=Rs}=R, Context) ->
    Exp = int_min(Lexp, Rexp),
    % If the result is 0, the sign should be negative in this case
    NegZero = (Context#context.rounding =:= 'ROUND_FLOOR') and (Ls =/= Rs),
    add_finite(L, R, Exp, NegZero, Context).

add_inf(#d{sign=Ls}=L, #d{sign=Rs}=R, Context)
  when ?IS_INFINITY(L), ?IS_INFINITY(R), Ls =/= Rs ->
    raise_error(Context, invalid_operation, "-INF + INF", []);
add_inf(L, _, Ctx) when ?IS_INFINITY(L) ->
    {L, Ctx};
add_inf(_, R, Ctx) when ?IS_INFINITY(R) ->
    {R, Ctx}.

%% Zero adding (both, left, or right)
add_finite(#d{coeff=0}=L, #d{coeff=0}=R, Exp, NegZero, Context) ->
    add_zeros(L, R, Exp, NegZero, Context);
add_finite(#d{coeff=0}, R, Exp0, _, C) ->
    Exp = int_max(Exp0, R#d.exp - C#context.prec - 1),
    fix(rescale(R, Exp, C#context.rounding), C);
add_finite(L, #d{coeff=0}, Exp0, _, C) ->
    Exp = int_max(Exp0, L#d.exp - C#context.prec - 1),
    fix(rescale(L, Exp, C#context.rounding), C);

%% Neither L or R is a zero, so proceed normally after normalizing them so
%% that they share the same exponent and coefficient length.
add_finite(L0, R0, Exp, NegZero, C) ->
    {L, R} = normalize(L0, R0, C#context.prec),
    add_finite_nonzero(L, R, Exp, NegZero, C).

%% Two numbers with the same coefficient (and exp) but opposite signs will
%% become negative or positive zero.
add_finite_nonzero(#d{coeff=I, sign=Ls}, #d{coeff=I, sign=Rs}, Exp, true, Context)
  when Ls =/= Rs ->
    fix(#d{sign=1, coeff=0, exp=Exp}, Context);
add_finite_nonzero(#d{coeff=I, sign=Ls}, #d{coeff=I, sign=Rs}, Exp, false, Context)
  when Ls =/= Rs ->
    fix(#d{sign=0, coeff=0, exp=Exp}, Context);

%% Re-arrange so abs(L) > abs(R)
add_finite_nonzero(#d{coeff=Lc, sign=Ls}=L, #d{coeff=Rc, sign=Rs}=R, Exp, NegZero, Context)
  when Lc < Rc, Ls =/= Rs ->
    add_finite_nonzero(R, L, Exp, NegZero, Context);

%% If the first number is negative and the second positive, reverse the two
%% signs and produce a signed result
add_finite_nonzero(#d{sign=1}=L, #d{sign=0}=R, _, _, Context) ->
    add_finite_nonzero_coeffs(L#d{sign=0}, R#d{sign=1}, Context, 1);

%% If the right number is negative, the result will be positive (because
%% abs(L) > abs(R))
add_finite_nonzero(#d{sign=Ls}=L, #d{sign=Rs}=R, _, _, Context)
  when Ls =/= Rs ->
    add_finite_nonzero_coeffs(L, R, Context, 0);

%% If both are negative, the result is signed
add_finite_nonzero(#d{sign=1}=L, R, _, _, Context) ->
    add_finite_nonzero_coeffs(L#d{sign=0}, R#d{sign=0}, Context, 1);

%% All other cases are standard unsigned addition
add_finite_nonzero(L, R, _, _, Context) ->
    add_finite_nonzero_coeffs(L, R, Context, 0).

%% Add the two coefficients together with the given sign
add_finite_nonzero_coeffs(L, #d{sign=0}=R, Context, Sign) ->
    fix(#d{sign=Sign, coeff=L#d.coeff+R#d.coeff, exp=L#d.exp}, Context);
add_finite_nonzero_coeffs(L, R, Context, Sign) ->
    fix(#d{sign=Sign, coeff=L#d.coeff-R#d.coeff, exp=L#d.exp}, Context).

%% Add two zeros, producing another zero, either negative or positive.
add_zeros(_, _, Exp, true, Context) ->
    fix(#d{sign=1, coeff=0, exp=Exp}, Context);
add_zeros(#d{sign=L}, #d{sign=R}, Exp, false, Context) ->
    fix(#d{sign=int_min(L, R), coeff=0, exp=Exp}, Context).

-ifdef(EUNIT).

addition_test_() ->
    D1 = to_decimal("-11.1"),
    D2 = to_decimal("22.2"),
    [?_assert(add(D1,D2) =:= to_decimal("11.1")),
     ?_assert(add(D2,D1) =:= to_decimal("11.1")),
     ?_assert(add(D1, 5) =:= to_decimal("-6.1")),
     ?_assert(add(5, D1) =:= to_decimal("-6.1"))].

-endif.

sub(L, R) ->
    ctx_op(fun sub/3, [L, R]).

sub(L0, R0, Context) ->
    L = convert_other(L0),
    R = convert_other(R0),
    sub1(L, R, Context).

sub1(L, R, Context) when ?IS_SPECIAL(L) or ?IS_SPECIAL(R) ->
    case check_nans(L, R, Context) of
        false ->
            add(L, negate(R), Context);
        Ans ->
            Ans
    end;
sub1(L, R, Context) ->
    add(L, negate(R), Context).

-ifdef(EUNIT).

subtraction_test_() ->
    D1 = to_decimal("-11.1"),
    D2 = to_decimal("22.2"),
    [?_assert(sub(D1,D2) =:= to_decimal("-33.3")),
     ?_assert(sub(D2,D1) =:= to_decimal("33.3")),
     ?_assert(sub(D1, 5) =:= to_decimal("-16.1")),
     ?_assert(sub(5, D1) =:= to_decimal("16.1"))].

-endif.

quantize(D, Exp) ->
    ctx_op(fun quantize/3, [D, Exp]).

quantize(D, Exp, C) when is_record(C, context) ->
    quantize(D, Exp, C#context.rounding, C).

%% Quantize so that D's exponent is the same as Exp. Behaves similarly to
%% rescale/3 but has error checking.
quantize(D, Exp, R, C) ->
    quantize(D, Exp, R, C, true).

quantize(D, Exp0, R, C, WatchExp) when ?is_decimal(D),
                                       is_atom(R),
                                       is_record(C, context) ->
    Exp = convert_other(Exp0),
    quantize1(D, Exp, R, C, WatchExp).

quantize1(D, Exp, _, C, _) when ?IS_SPECIAL(D) or ?IS_SPECIAL(Exp) ->
    case check_nans(D, Exp, C) of
        false ->
            quantize_inf(D, Exp, C);
        Ans ->
            Ans
    end;
%% Simple scale since we're not watching exponents
%% quantize1(D, Exp, R, C, false) ->
%%     case rescale(D, Exp#d.exp, R) of
%%         Ans when Ans#d.exp > D#d.exp ->
%%             C1 = element(2, raise_error(C, rounded)),
%%             C2 = case ne(Ans, D) of
%%                      true ->
%%                          element(2, raise_error(C1, inexact));
%%                      false ->
%%                          C1
%%                  end,
%%             {Ans, C2};
%%         Ans ->
%%             {Ans, C}
%%     end;
quantize1(_, Exp, _, C, true) when (?ETINY(C) > Exp#d.exp) or (C#context.emax < Exp#d.exp) ->
    raise_error(C, invalid_operation, "target exponent out of bounds in quantize");
quantize1(#d{sign=Sign, coeff=0}, #d{exp=Exp}, _, C, true) ->
    fix(#d{sign=Sign, coeff=0, exp=Exp}, C);
quantize1(D, Exp, R, C, true) ->
    quantize_adj(D, Exp, R, C, adjusted(D)).

quantize_adj(_, _, _, #context{emax=Emax}=C, Adj) when Adj > Emax ->
    raise_error(C, invalid_operation, "exponent of quantize result too large for current context");
quantize_adj(_, #d{exp=Exp}, _, #context{prec=Prec}=C, Adj) when (Adj - Exp + 1) > Prec ->
    raise_error(C, invalid_operation, "quantize result has too many digits for current context");
quantize_adj(D, Exp, R, C, _) ->
    Rescaled = rescale(D, Exp#d.exp, R),
    RescaledAdj = adjusted(Rescaled),
    quantize_rescaled(D, Rescaled, RescaledAdj, C).

quantize_rescaled(_, _, AnsAdj, #context{emax=Emax}=C) when AnsAdj > Emax ->
    raise_error(C, invalid_operation, "exponent of quantize result too large for current context");
quantize_rescaled(D, Ans, AnsAdj, C) ->
    quantize_rescaled1(D, Ans, AnsAdj, digits(Ans#d.coeff), C).

quantize_rescaled1(_, _, _, AnsLen, #context{prec=Prec}=C) when AnsLen > Prec ->
    raise_error(C, invalid_operation, "quantize result has too many digits for current context");
quantize_rescaled1(D, Ans, AnsAdj, _, C) ->
    C1 = case Ans#d.exp > D#d.exp of
             true ->
                 CRnd = element(2, raise_error(C, rounded)),
                 case ne(Ans, D) of
                     true ->
                         element(2, raise_error(CRnd, inexact));
                     false ->
                         CRnd
                 end;
             false ->
                 C
         end,
    C2 = if Ans#d.coeff =/= 0, AnsAdj < C#context.emin ->
                 element(2, raise_error(C1, subnormal));
            true ->
                 C1
         end,
    fix(Ans, C2).

quantize_inf(D, Exp, C) when ?IS_INFINITY(D) and ?IS_INFINITY(Exp) ->
    {D, C};
quantize_inf(_, _, C) ->
    raise_error(C, invalid_operation, "quantize with one INF").

%% Quiet: doesn't use nor change context
rescale(A, _, _) when ?IS_SPECIAL(A) ->
    A;
rescale(#d{coeff=0}=D, Exp, _) ->
    D#d{exp=Exp};
rescale(#d{exp=Exp}=D, Exp, _) ->
    D;
rescale(#d{coeff=Coeff0}=D, Exp, _) when D#d.exp >= Exp ->
    Diff = D#d.exp - Exp,
    Coeff = pad_zeros(Coeff0, Diff),
    D#d{coeff=Coeff, exp=Exp};
rescale(D0, Exp, Rounding) ->
    %% Too many digits. Round and lose data. If self.adjusted() < exp-1,
    %% replace self by 10 ^ (exp-1) before rounding
    {D, Digits, F} = rescale_digits(D0, Exp),
    Coeff = case (pick_rounding_function(Rounding))(D, Digits) of
                1 ->
                    F + 1;
                _ ->
                    F
            end,
    #d{sign=D#d.sign, coeff=Coeff, exp=Exp}.

rescale_digits(#d{coeff=Coeff0, exp=Exp0}=D0, Exp) ->
    rescale_rl(D0, Exp, digits(Coeff0) + Exp0 - Exp).

rescale_rl(D, Exp, Dig) when Dig < 0 ->
    {D#d{coeff=1, exp=Exp-1}, 0, first_digits(D#d.coeff, Dig)};
rescale_rl(D, _, Dig) ->
    {D, Dig, first_digits(D#d.coeff, Dig)}.

digits(I) when is_integer(I) ->
    length(integer_to_list(I)).

pad_zeros(Int, Num) when is_integer(Int), is_integer(Num), Num > 0 ->
    list_to_integer(integer_to_list(Int) ++ string:chars($0, Num)).

mult(L, R) ->
    ctx_op(fun mult/3, [L, R]).

mult(L0, R0, Context) ->
    L = convert_other(L0),
    R = convert_other(R0),
    ResultSign = L#d.sign bxor R#d.sign,
    mult1(L, R, ResultSign, Context).

mult1(L, R, ResultSign, Context) when ?IS_SPECIAL(L) or ?IS_SPECIAL(R) ->
    case check_nans(L, R, Context) of
        false ->
            mult_inf(L, R, ResultSign, Context);
        Ans ->
            Ans
    end;
mult1(L, R, ResultSign, Context) ->
    ResultExp = L#d.exp + R#d.exp,
    mult_normal(L, R, ResultSign, ResultExp, Context).

mult_inf(L, R, S, C) when ?IS_INFINITY(L), ?IS_INFINITY(R) ->
    {inf_signs(S), C};
mult_inf(L, #d{coeff=0}, _, C) when ?IS_INFINITY(L) ->
    raise_error(C, invalid_operation, "(+-)INF * 0", []);
mult_inf(L, _, S, C) when ?IS_INFINITY(L) ->
    {inf_signs(S), C};
mult_inf(#d{coeff=0}, R, _, C) when ?IS_INFINITY(R) ->
    raise_error(C, invalid_operation, "0 * (+-)INF", []);
mult_inf(_, R, S, C) when ?IS_INFINITY(R) ->
    {inf_signs(S), C}.

mult_normal(_, #d{coeff=0}, Sign, Exp, Ctx) ->
    fix(#d{sign=Sign, exp=Exp, coeff=0}, Ctx);
mult_normal(#d{coeff=0}, _, Sign, Exp, Ctx) ->
    fix(#d{sign=Sign, exp=Exp, coeff=0}, Ctx);
mult_normal(#d{coeff=1}, #d{coeff=Other}, Sign, Exp, Ctx) ->
    fix(#d{sign=Sign, exp=Exp, coeff=Other}, Ctx);
mult_normal(#d{coeff=Other}, #d{coeff=1}, Sign, Exp, Ctx) ->
    fix(#d{sign=Sign, exp=Exp, coeff=Other}, Ctx);
mult_normal(#d{coeff=L}, #d{coeff=R}, Sign, Exp, Ctx) ->
    fix(#d{sign=Sign, exp=Exp, coeff=L*R}, Ctx).

-ifdef(EUNIT).

multiplication_test_() ->
    D1 = to_decimal("-5"),
    D2 = to_decimal("3"),
    [?_assert(mult(D1,D2) =:= to_decimal("-15")),
     ?_assert(mult(D2,D1) =:= to_decimal("-15")),
     ?_assert(mult(D1, 5) =:= to_decimal("-25")),
     ?_assert(mult(5, D1) =:= to_decimal("-25"))].

-endif.

divide(L, R) ->
    ctx_op(fun divide/3, [L, R]).

divide(L0, R0, Context) ->
    L = convert_other(L0),
    R = convert_other(R0),
    div1(L, R, L#d.sign bxor R#d.sign, Context).

div1(L, R, Sign, C) when ?IS_SPECIAL(L) or ?IS_SPECIAL(R) ->
    case check_nans(L, R, C) of
        false ->
            div_inf(L, R, Sign, C);
        Ans ->
            Ans
    end;
div1(#d{coeff=0}, #d{coeff=0}, _, C) ->
    raise_error(C, division_undefined, "0 / 0");
div1(_, #d{coeff=0}, S, C) ->
    raise_error(C, division_by_zero, "x / 0", [S]);
div1(#d{coeff=0, exp=Le}, #d{exp=Re}, Sign, C) ->
    fix(#d{sign=Sign, coeff=0, exp=Le-Re}, C);
div1(L, R, Sign, C) ->
    %% Neither are zero, infinity or NaN
    Shift = digits(R#d.coeff) - digits(L#d.coeff) + C#context.prec + 1,
    Exp = L#d.exp - R#d.exp - Shift,
    case div_get_rem(L#d.coeff, R#d.coeff, Shift) of
        {Coeff, 0} ->
            div_get_ideal(Sign, L#d.exp - R#d.exp, Exp, Coeff, C);
        %% Result is not exact; adjust to ensure correct rounding
        {Coeff, _} when Coeff rem 5 =:= 0 ->
            fix(#d{sign=Sign, coeff=Coeff + 1, exp=Exp}, C);
        {Coeff, _} ->
            fix(#d{sign=Sign, coeff=Coeff, exp=Exp}, C)
    end.

div_get_rem(Op1, Op2, Shift) when Shift >= 0 ->
    divmod(Op1 * xmath:pow(10, Shift), Op2);
div_get_rem(Op1, Op2, Shift) ->
    divmod(Op1, Op2 * xmath:pow(10, -1 * Shift)).

div_get_ideal(Sign, IdealExp, Exp0, Coeff0, C) ->
    {Coeff, Exp} = div_get_ideal1(IdealExp, Exp0, Coeff0),
    fix(#d{sign=Sign, coeff=Coeff, exp=Exp}, C).

div_get_ideal1(IdealExp, Exp, Coeff)
  when Exp < IdealExp, Coeff rem 10 =:= 0 ->
    div_get_ideal1(IdealExp, Exp + 1, Coeff div 10);
div_get_ideal1(_, Exp, Coeff) ->
    {Coeff, Exp}.

div_inf(L, R, _, C) when ?IS_INFINITY(L) and ?IS_INFINITY(R) ->
    raise_error(C, invalid_operation, "(+-)INF/(+-)INF", []);
div_inf(L, _, Sign, C) when ?IS_INFINITY(L) ->
    {inf_signs(Sign), C};
div_inf(_, R, S, C0) when ?IS_INFINITY(R) ->
    {_, C} = raise_error(C0, clamped, "Division by infinity"),
    {#d{sign=S, coeff=0, exp=?ETINY(C)}, C}.

-ifdef(EUNIT).

division_test_() ->
    D1 = to_decimal("-5"),
    D2 = to_decimal("2"),
    [?_assert(divide(D1,D2) =:= to_decimal("-2.5")),
     ?_assert(divide(D2,D1) =:= to_decimal("-0.4")),
     ?_assert(divide(D1, 4) =:= to_decimal("-1.25")),
     ?_assert(divide(4, D1) =:= to_decimal("-0.8"))].

-endif.

divide_int(L, R) ->
    ctx_op(fun divide_int/3, [L, R]).

divide_int(L0, R0, Ctx) ->
    L = convert_other(L0),
    R = convert_other(R0),
    case check_nans(L, R, Ctx) of
        false ->
            divide_int1(L, R, Ctx);
        Ans ->
            Ans
    end.

divide_int1(L, R, Ctx) when ?IS_INFINITY(L), ?IS_INFINITY(R) ->
    raise_error(Ctx, invalid_operation, "INF // INF", []);
divide_int1(#d{sign=Ls}=L, #d{sign=Rs}, Ctx) when ?IS_INFINITY(L) ->
    case Ls bxor Rs of
        0 ->
            {?INF, Ctx};
        _ ->
            {?NEG_INF, Ctx}
    end;
divide_int1(#d{coeff=0}=L, #d{coeff=0}=R, Ctx) when not ?IS_SPECIAL(L), not ?IS_SPECIAL(R) ->
    raise_error(Ctx, division_undefined, "0 // 0", []);
divide_int1(#d{sign=Ls}, #d{sign=Rs, coeff=0}=R, Ctx) when not ?IS_SPECIAL(R) ->
    raise_error(Ctx, division_by_zero, "x // 0", [Ls bxor Rs]);
divide_int1(L, R, Ctx) ->
    {{Res, _}, Ctx1} = divmod_prec(L, R, Ctx),
    {Res, Ctx1}.

divmod_prec(#d{sign=Ls}=L, #d{sign=Rs}=R, Ctx) ->
    Sign = Ls bxor Rs,
    IdealExp = case ?IS_INFINITY(R) of
                   true ->
                       L#d.exp;
                   _ ->
                       int_min(L#d.exp, R#d.exp)
               end,
    ExpDiff = adjusted(L) - adjusted(R),
    divmod_prec1(L, R, Ctx, Sign, IdealExp, ExpDiff).

divmod_prec1(L, R, Ctx, Sign, IdealExp, ExpDiff)
  when (not ?IS_SPECIAL(L) and (L#d.coeff =:= 0)) or ?IS_INFINITY(R) or (ExpDiff =< -2) ->
    {{#d{sign=Sign, coeff=0, exp=0}, rescale(L, IdealExp, Ctx#context.rounding)},
     Ctx};
divmod_prec1(#d{exp=Le}=L0, #d{exp=Re}=R0, #context{prec=P}=Ctx, Sign, IdealExp, ExpDiff) when ExpDiff =< P ->

    {L, R} = case Le >= Re of
                 true ->
                     Fac = xmath:pow(10, Le - Re),
                     {L0#d{coeff=(L0#d.coeff*Fac)}, R0};
                 false ->
                     Fac = xmath:pow(10, Re - Le),
                     {L0, R0#d{coeff=(R0#d.coeff*Fac)}}
             end,
    PBound = xmath:pow(10, P),
    case L#d.coeff div R#d.coeff of
        Quo when Quo < PBound ->
            Rem = L#d.coeff rem R#d.coeff,
            {{#d{sign=Sign, coeff=Quo, exp=0},
              #d{sign=L#d.sign, coeff=Rem, exp=IdealExp}}, Ctx};
        _ ->
            divmod_prec_error(Ctx)
    end;
divmod_prec1(_, _, Ctx, _, _, _) ->
    divmod_prec_error(Ctx).

divmod_prec_error(Ctx) ->
    {Ans, Ctx1} = raise_error(Ctx, division_impossible,
                              "quotient too large in //, % or divmod"),
    {{Ans, Ans}, Ctx1}.

apply(D) ->
    ctx_op(fun ?MODULE:apply/2, [D]).

apply(D, Ctx) ->
    fix(D, Ctx).

class(D) ->
    ctx_op(fun class/2, [D]).

class(D, C) when ?IS_SNAN(D) ->
    {"sNaN", C};
class(D, C) when ?IS_NAN(D) ->
    {"NaN", C};
class(#d{sign=1}=D, C) when ?IS_INFINITY(D) ->
    {"-Infinity", C};
class(#d{sign=0}=D, C) when ?IS_INFINITY(D) ->
    {"+Infinity", C};
class(#d{sign=0, coeff=0}, C) ->
    {"+Zero", C};
class(#d{sign=1, coeff=0}, C) ->
    {"-Zero", C};
class(#d{sign=1}=D, C) ->
    case is_subnormal(D, C) of
        true ->
            {"-Subnormal", C};
        false ->
            {"-Normal", C}
    end;
class(#d{sign=0}=D, C) ->
    case is_subnormal(D, C) of
        true ->
            {"+Subnormal", C};
        false ->
            {"+Normal", C}
    end.

%% Decapitate the payload of a NaN to fit the context
fix_nan(#d{coeff=Payload0}=D, #context{clamp=Clamp0, prec=P}=C) ->
    Clamp = case Clamp0 of true -> 1; _ -> 0 end,
    MaxPayloadLength = P - Clamp,
    Payload = integer_to_list(Payload0),
    if length(Payload) > MaxPayloadLength ->
            Start = length(Payload) - MaxPayloadLength + 1,
            Payload1 = list_to_integer(string:substr(Payload, Start)),
            {D#d{coeff=Payload1}, C};
       true ->
            {D, C}
    end.

%% Round if necessary to keep with the precision specified by the context. Do
%% not raise a signalling NaN.
fix(D, C) when ?IS_NAN(D) ->
    % Decapitate the payload if necessary
    fix_nan(D, C);
fix(D, C) when ?IS_SPECIAL(D) ->
    % Return +/-Infinity unaltered
    {D, C};
fix(D, C) ->
    fix_finite(D, ?ETINY(C), ?ETOP(C), C).

%% If the decimal is zero, then the exponent must be between Etiny and Emax
%% if clamp is false and Etiny and Etop if clamp is true.
fix_finite(#d{coeff=0}=D, Etiny, Etop, #context{clamp=true}=C) ->
    fix_zero(D, int_min(int_max(D#d.exp, Etiny), Etop), C);
fix_finite(#d{coeff=0}=D, Etiny, _, #context{clamp=false, emax=Emax}=C) ->
    fix_zero(D, int_min(int_max(D#d.exp, Etiny), Emax), C);

%% ExpMin is the smallest allowable exponent of the result
fix_finite(D, Etiny, Etop, C) ->
    ExpMin = digits(D#d.coeff) + D#d.exp - C#context.prec,
    fix_finite(D, Etiny, Etop, ExpMin, C).

%% Overflow: ExpMin > Etop if and only if adjusted(D) > Emax
fix_finite(D, _Etiny, Etop, ExpMin, C0) when ExpMin > Etop ->
    C = raise_foldl(C0, [inexact, rounded]),
    raise_error(C, overflow, "above Emax", [D#d.sign]);

%% Subnormal
fix_finite(D, Etiny, Etop, ExpMin, C0) when ExpMin < Etiny ->
    {_, C} = raise_error(C0, subnormal),
    fix_finite_mayround(D, Etiny, Etop, Etiny, C, true);

%% Proceed
fix_finite(D, Etiny, Etop, ExpMin, C) ->
    fix_finite_mayround(D, Etiny, Etop, ExpMin, C, false).

%% Round if D has too many digits
fix_finite_mayround(#d{exp=E}=D, _, Etop, ExpMin, C0, Sn) when E < ExpMin ->
    {_, C} = raise_error(C0, rounded),
    fix_finite_round(D, Etop, ExpMin, C, Sn);

%% Fold down if clamp is true and D has too few digits
fix_finite_mayround(#d{coeff=Coeff, exp=E}=D, _Etiny, Etop, _ExpMin,
                    #context{clamp=true}=C0, _) when E > Etop ->
    {_, C} = raise_error(C0, clamped),
    Padded = pad_zeros(Coeff, E - Etop),
    {D#d{coeff=Padded, exp=Etop}, C};

%% Whew, this one happened to be representable accurately, so return it
%% unchanged
fix_finite_mayround(D, _, _, _, C, _) ->
    {D, C}.

%% Proceed with rounding
fix_finite_round(#d{coeff=Coeff, exp=Exp0}=D0, Etop, ExpMin, C, Sn) ->
    {D, Digits} = case digits(Coeff) + Exp0 - ExpMin of
                      Digs when Digs < 0 ->
                          {D0#d{coeff=1, exp=ExpMin-1}, 0};
                      Digs ->
                          {D0, Digs}
                  end,
    Changed = (pick_rounding_function(C#context.rounding))(D, Digits),
    case Changed of
        1 ->
            fix_finite_inexact(D#d{coeff=first_digits(D#d.coeff, Digits) + 1,
                                     exp=ExpMin}, C, Sn, Etop);
        0 ->
            {D#d{coeff=first_digits(D#d.coeff, Digits), exp=ExpMin}, C};
        -1 ->
            fix_finite_inexact(D#d{coeff=first_digits(D#d.coeff, Digits),
                                     exp=ExpMin}, C, Sn, Etop)
    end.

fix_finite_inexact(D, C0, SubNormal, Etop) ->
    {_, C} = raise_error(C0, inexact),
    fix_finite_inexact1(D, C, SubNormal, Etop).

fix_finite_inexact1(#d{coeff=0}=D, C0, true, _) ->
    C = raise_foldl(C0, [underflow, clamped]),
    {D, C};
fix_finite_inexact1(D, C0, true, _) ->
    {_, C} = raise_error(C0, underflow),
    {D, C};
fix_finite_inexact1(D, C, false, Etop) ->
    case digits(D#d.coeff) of
        Prec1 when Prec1 =:= C#context.prec + 1 ->
            % Only if rescaling rounds the coefficient up to 10 ^ precision
            fix_finite_prec_rescale(D, C, Etop);
        _ ->
            {D, C}
    end.
%% fix_finite_inexact1(D, C, _, _) ->
%%     {D, C}.

fix_finite_prec_rescale(#d{exp=E, coeff=Coeff0}=D, C, Etop) when E < Etop ->
    Coeff = first_digits(Coeff0, digits(Coeff0) - 1),
    {D#d{exp=E+1, coeff=Coeff}, C};
fix_finite_prec_rescale(D, C, _) ->
    raise_error(C, overflow, "above Emax", [D#d.sign]).

fix_zero(#d{exp=E}=D, E, C) ->
    {D, C};
fix_zero(D, NewExp, C0) ->
    {_, C} = raise_error(C0, clamped),
    {D#d{coeff=0, exp=NewExp}, C}.

zero() ->
    ?ZERO.

sign_mult(Sign) when is_integer(Sign), Sign rem 2 =:= 0 ->
    1;
sign_mult(Sign) when is_integer(Sign), Sign rem 2 =:= 1 ->
    -1.

negate(#d{sign=1}=D) ->
    D#d{sign=0};
negate(#d{sign=0}=D) ->
    D#d{sign=1}.

first_digits(_, E) when E =< 0 ->
    0;
first_digits(I, E) when is_integer(I) ->
    first_digits(integer_to_list(I), E);
first_digits(I, E) when is_list(I), is_integer(E), E > 0 ->
    l2i(lists:sublist(I, E)).

l2i([]) ->
    0;
l2i(L) when is_list(L) ->
    list_to_integer(L).

sub_digits(I, 0) ->
    I;
sub_digits(I, E) when is_integer(I) ->
    sub_digits(integer_to_list(I), E);
sub_digits(I, E) when is_list(I), is_integer(E), E < 0 ->
    sub_digits(I, length(I) + E);
sub_digits(I, E) when is_list(I), is_integer(E), E > 0 ->
    case lists:nthtail(E, I) of
        [] ->
            0;
        L when length(L) > 0 ->
            list_to_integer(L)
    end.

convert_other(Other) ->
    convert_other(Other, false).

convert_other(Other, _) when is_integer(Other) ->
    to_decimal(Other);
convert_other(Other, _) when ?is_decimal(Other) ->
    Other;
convert_other(Other, true) ->
    throw({error, io_lib:format("Unable to convert ~p to decimal", [Other])}).

int_cmp(L, R) when is_integer(L), is_integer(R), L < R ->
    -1;
int_cmp(L, R) when is_integer(L), is_integer(R), L > R ->
    1;
int_cmp(L, R) when is_integer(L), is_integer(R), L =:= R ->
    0.

zero_list(I, Tail) when I < 1 ->
    Tail;
zero_list(I, Tail) when is_integer(I) ->
    string:chars($0, I, Tail).

zero_list(I) when I < 1 ->
    [];
zero_list(I) when is_integer(I) ->
    string:chars($0, I).

%% Decimal parser... This could be a convenient regular expression, but they
%% suck in Erlang.
safe_parse(L) when is_list(L) ->
    case catch(parse(L)) of
        {'EXIT', _} ->
            {error, L};
        Ctx when is_record(Ctx, pctx) ->
            Ctx
    end.

%% Beastly regular expression: (?P<sign>[-+])?((?=[0-9]|\.[0-9])(?P<int>[0-9]*)(\.(?P<frac>[0-9]*))?(E(?P<exp>(?P<exp_sign>[-+])?[0-9]+))?|Inf(inity)?|(?P<signal>s)?NaN(?P<diag>[0-9]*))

parse(Str) ->
    parse_sign(string:to_lower(Str), #pctx{orig=Str}).

parse_sign([$+|Rest], Pctx) ->
    parse_topnum(Rest, Pctx#pctx{sign=0});
parse_sign([$-|Rest], Pctx) ->
    parse_topnum(Rest, Pctx#pctx{sign=1});
parse_sign(Rest, Pctx) ->
    parse_topnum(Rest, Pctx#pctx{sign=0}).

parse_topnum("infinity", Pctx) ->
    Pctx#pctx{infinity=true};
parse_topnum("inf", Pctx) ->
    Pctx#pctx{infinity=true};
parse_topnum([$s|Rest], Pctx) ->
    parse_nan(Rest, Pctx#pctx{signal=true});
parse_topnum([$.,Digit|Rest], Pctx) when ?IS_DIGIT(Digit) ->
    parse_frac([Digit|Rest], Pctx);
parse_topnum([Digit|_]=Num, Pctx) when ?IS_DIGIT(Digit) ->
    parse_num(Num, Pctx);
parse_topnum(Else, Pctx) ->
    parse_nan(Else, Pctx).

parse_nan([$n,$a,$n|Rest], Pctx) ->
    parse_nan_diag(Rest, Pctx#pctx{nan=true}).

parse_nan_diag([], Pctx) ->
    Pctx#pctx{diag=lists:reverse(Pctx#pctx.diag)};
parse_nan_diag([Num|Rest], Pctx) when ?IS_DIGIT(Num) ->
    parse_nan_diag(Rest, Pctx#pctx{diag=[Num|Pctx#pctx.diag]}).

parse_num(L, Pctx) when L =:= []; L =:= "." ->
    Pctx#pctx{coeff=lists:reverse(Pctx#pctx.coeff)};
parse_num([$.,Digit|Rest], Pctx) when ?IS_DIGIT(Digit) or (Digit =:= $e) ->
    parse_frac([Digit|Rest], Pctx#pctx{coeff=lists:reverse(Pctx#pctx.coeff)});
parse_num([Digit|Rest], Pctx) when ?IS_DIGIT(Digit) ->
    parse_num(Rest, Pctx#pctx{coeff=[Digit|Pctx#pctx.coeff]});
parse_num([$e|Rest], Pctx) ->
    parse_exp_sign(Rest, Pctx#pctx{coeff=lists:reverse(Pctx#pctx.coeff)}).

parse_frac([], Pctx) ->
    Pctx#pctx{frac=lists:reverse(Pctx#pctx.frac)};
parse_frac([$e|Rest], Pctx) ->
    parse_exp_sign(Rest, Pctx#pctx{frac=lists:reverse(Pctx#pctx.frac)});
parse_frac([Digit|Rest], Pctx) when ?IS_DIGIT(Digit) ->
    parse_frac(Rest, Pctx#pctx{frac=[Digit|Pctx#pctx.frac]}).

parse_exp_sign([$-,D|Rest], Pctx) when ?IS_DIGIT(D) ->
    parse_exp([D|Rest], Pctx#pctx{exp_sign=1});
parse_exp_sign([$+,D|Rest], Pctx) when ?IS_DIGIT(D) ->
    parse_exp([D|Rest], Pctx#pctx{exp_sign=0});
parse_exp_sign([D|_]=Rest, Pctx) when ?IS_DIGIT(D) ->
    parse_exp(Rest, Pctx).

parse_exp([], Pctx) ->
    Pctx#pctx{exp=lists:reverse(Pctx#pctx.exp)};
parse_exp([Digit|Rest], Pctx) when ?IS_DIGIT(Digit) ->
    parse_exp(Rest, Pctx#pctx{exp=[Digit|Pctx#pctx.exp]}).

get_context() ->
    case get(?CONTEXT_KEY) of
        undefined ->
            #context{};
        C when is_record(C, context) ->
            C
    end.

set_context(C) when is_record(C, context) ->
    put(?CONTEXT_KEY, C).

condition_map(conversion_syntax) ->
    invalid_operation;
condition_map(division_impossible) ->
    invalid_operation;
condition_map(division_undefined) ->
    invalid_operation;
condition_map(invalid_context) ->
    invalid_operation;
condition_map(C) ->
    C.

%% Context-based error handling and trap setting

set_trap(T, clamped) ->
    T#traps{clamped=true};
set_trap(T, invalid_operation) ->
    T#traps{invalid_operation=true};
set_trap(T, division_by_zero) ->
    T#traps{division_by_zero=true};
set_trap(T, inexact) ->
    T#traps{inexact=true};
set_trap(T, rounded) ->
    T#traps{rounded=true};
set_trap(T, subnormal) ->
    T#traps{subnormal=true};
set_trap(T, overflow) ->
    T#traps{overflow=true};
set_trap(T, underflow) ->
    T#traps{underflow=true}.

get_trap(T, clamped) ->
    T#traps.clamped;
get_trap(T, invalid_operation) ->
    T#traps.invalid_operation;
get_trap(T, division_by_zero) ->
    T#traps.division_by_zero;
get_trap(T, inexact) ->
    T#traps.inexact;
get_trap(T, rounded) ->
    T#traps.rounded;
get_trap(T, subnormal) ->
    T#traps.subnormal;
get_trap(T, overflow) ->
    T#traps.overflow;
get_trap(T, underflow) ->
    T#traps.underflow.

handle_condition(invalid_operation, C, [#d{sign=S, coeff=I}|_]) ->
    fix_nan(#d{sign=S, coeff=I, exp=?dnan}, C);
handle_condition(invalid_operation, C, _) ->
    {?NAN, C};
handle_condition(clamped, C, _) ->
    {ok, C};
handle_condition(conversion_syntax, C, _) ->
    {?NAN, C};
handle_condition(division_by_zero, C, [0|_]) ->
    {?INF, C};
handle_condition(division_by_zero, C, [1|_]) ->
    {?NEG_INF, C};
handle_condition(division_impossible, C, _) ->
    {?NAN, C};
handle_condition(division_undefined, C, _) ->
    {?NAN, C};
handle_condition(inexact, C, _) ->
    {ok, C};
handle_condition(invalid_context, C, _) ->
    {?NAN, C};
handle_condition(rounded, C, _) ->
    {ok, C};
handle_condition(subnormal, C, _) ->
    {ok, C};
handle_condition(overflow, #context{rounding=Rounding}=C, [0|_])
  when Rounding =:= 'ROUND_HALF_UP';
       Rounding =:= 'ROUND_HALF_EVEN';
       Rounding =:= 'ROUND_HALF_DOWN';
       Rounding =:= 'ROUND_UP' ->
    {?INF, C};
handle_condition(overflow, #context{rounding=Rounding}=C, [1|_])
  when Rounding =:= 'ROUND_HALF_UP';
       Rounding =:= 'ROUND_HALF_EVEN';
       Rounding =:= 'ROUND_HALF_DOWN';
       Rounding =:= 'ROUND_UP' ->
    {?NEG_INF, C};
handle_condition(overflow, #context{rounding='ROUND_CEILING'}=C, [0|_]) ->
    {?INF, C};
handle_condition(overflow, #context{prec=Prec, emax=EMax}=C, [0|_]) ->
    Coeff = list_to_integer(string:chars($9, Prec)),
    {#d{sign=0, coeff=Coeff, exp=EMax-Prec+1}, C};
handle_condition(overflow, #context{rounding='ROUND_FLOOR'}=C, [1|_]) ->
    {?NEG_INF, C};
handle_condition(overflow, #context{prec=Prec, emax=EMax}=C, [1|_]) ->
    Coeff = list_to_integer(string:chars($9, Prec)),
    {#d{sign=1, coeff=Coeff, exp=EMax-Prec+1}, C};
handle_condition(underflow, C, _) ->
    {ok, C}.

raise_error(C, Cond) ->
    raise_error(C, Cond, []).

raise_error(C, Cond, Args) ->
    raise_error(C, Cond, [], Args).

raise_error(#context{traps=T, flags=F}=Ctx0, Cond, Explanation, Args) ->
    Error = condition_map(Cond),
    Ctx = Ctx0#context{flags=set_trap(F, Error)},
    case get_trap(T, Error) of
        true ->
            throw({error, Explanation});
        false ->
            handle_condition(Cond, Ctx, Args)
    end.

raise_foldl(Ctx, L) ->
    lists:foldl(fun(T, C) ->
                        {_, Ctx1} = raise_error(C, T),
                        Ctx1
                end, Ctx, L).

inf_signs(0) ->
    ?INF;
inf_signs(1) ->
    ?NEG_INF.

check_nans(L, C) ->
    check_nans(L, undefined, C).

check_nans(L, _, C) when ?IS_SNAN(L) ->
    raise_error(C, invalid_operation, "sNaN", [L]);
check_nans(_, R, C) when ?IS_SNAN(R) ->
    raise_error(C, invalid_operation, "sNaN", [R]);
check_nans(L, _, C) when ?IS_NAN(L) ->
    fix_nan(L, C);
check_nans(_, R, C) when ?IS_NAN(R) ->
    fix_nan(R, C);
check_nans(_, _, _) ->
    false.

int_min(A, B) when is_integer(A), is_integer(B), A > B ->
    B;
int_min(A, B) when is_integer(A), is_integer(B), A =< B ->
    A.

int_max(A, B) when is_integer(A), is_integer(B), A < B ->
    B;
int_max(A, B) when is_integer(A), is_integer(B), A >= B ->
    A.

%% Rounding functions

%% Round-towards-0, truncate
round_down(#d{coeff=I}, P) ->
    case all_zeros(I, P) of
        true ->
            0;
        _ ->
            -1
    end.

%% Round away from 0
round_up(D, Prec) ->
    -1 * round_down(D, Prec).

%% Round 5 up (away from 0)
round_half_up(#d{coeff=I}=D, Prec) ->
    round_half_up(D, Prec, integer_to_list(I)).

round_half_up(D, Prec, I) when length(I) >= Prec ->
    case lists:nth(Prec + 1, I) of
        Dig when Dig >= $5, Dig =< $9 ->
            1;
        _ ->
            round_down(D, Prec)
    end;
round_half_up(D, Prec, _) ->
    round_down(D, Prec).

%% Round 5 down
round_half_down(#d{coeff=I}=D, Prec) ->
    case exact_half(I, Prec) of
        true ->
            -1;
        _ ->
            round_half_up(D, Prec)
    end.

%% Round 5 to even, rest to nearest
round_half_even(#d{coeff=I}=D, Prec) ->
    round_half_even(D, Prec, exact_half(I, Prec)).

round_half_even(_, 0, true) ->
    -1;
round_half_even(#d{coeff=I}=D, Prec, true) ->
    case lists:nth(Prec, integer_to_list(I)) of
        Dig when Dig =:= $0;
                 Dig =:= $2;
                 Dig =:= $4;
                 Dig =:= $6;
                 Dig =:= $8 ->
            -1;
        _ ->
            round_half_up(D, Prec)
    end;
round_half_even(D, Prec, _) ->
    round_half_up(D, Prec).

%% Round up (not away from 0 if negative)
round_ceiling(#d{sign=0}=D, Prec) ->
    -1 * round_down(D, Prec);
round_ceiling(#d{sign=1}=D, Prec) ->
    round_down(D, Prec).

%% Round down (not toward 0 if negative)
round_floor(#d{sign=1}=D, Prec) ->
    -1 * round_down(D, Prec);
round_floor(#d{sign=0}=D, Prec) ->
    round_down(D, Prec).

%% Round down unless the digit at position Prec-1 is 0 or 5
round_05up(#d{coeff=I}=D, Prec) when Prec > 0 ->
    case lists:nth(Prec, integer_to_list(I)) of
        Dig when Dig =/= $0, Dig =/= $5 ->
            round_down(D, Prec);
        _ ->
            round_down(negate(D), Prec)
    end;
round_05up(D, Prec) ->
    round_down(negate(D), Prec).

pick_rounding_function('ROUND_DOWN') ->
    fun round_down/2;
pick_rounding_function('ROUND_UP') ->
    fun round_up/2;
pick_rounding_function('ROUND_HALF_UP') ->
    fun round_half_up/2;
pick_rounding_function('ROUND_HALF_DOWN') ->
    fun round_half_down/2;
pick_rounding_function('ROUND_HALF_EVEN') ->
    fun round_half_even/2;
pick_rounding_function('ROUND_CEILING') ->
    fun round_ceiling/2;
pick_rounding_function('ROUND_FLOOR') ->
    fun round_floor/2;
pick_rounding_function('ROUND_05UP') ->
    fun round_05up/2.

all_zeros(I, P) when is_integer(I), is_integer(P) ->
    all_zeros(integer_to_list(I), P);
all_zeros(I, P) when is_list(I), is_integer(P), length(I) =< P ->
    true;
all_zeros(I, P) when is_list(I), is_integer(P) ->
    0 =:= list_to_integer(string:substr(I, P + 1)).

exact_half(I, P) when is_integer(I), is_integer(P) ->
    exact_half(integer_to_list(I), P);
exact_half(I, P) when is_list(I), is_integer(P), length(I) =< P ->
    false;
exact_half(I, P) when is_list(I), is_integer(P) ->
    exact_half(string:substr(I, P + 1)).

exact_half("5") ->
    true;
exact_half([$5|Rest]) ->
    lists:all(fun(A) -> A =:= $0 end, Rest);
exact_half(_) ->
    false.

normalize(L0, R0, Prec) when L0#d.exp < R0#d.exp ->
    {R, L} = normalize(R0, L0, Prec),
    {L, R};
normalize(Tmp0, Other0, Prec) ->
    TmpLen = digits(Tmp0#d.coeff),
    OtherLen = digits(Other0#d.coeff),
    Exp = Tmp0#d.exp + int_min(-1, TmpLen - Prec - 2),
    Other = case OtherLen + Other0#d.exp - 1 < Exp of
                true ->
                    Other0#d{coeff=1, exp=Exp};
                false ->
                    Other0
            end,
    Tmp = Tmp0#d{exp=Other#d.exp,
                   coeff=Tmp0#d.coeff * xmath:pow(10, Tmp0#d.exp - Other#d.exp)},
    {Tmp, Other}.

divmod(L, R) when is_integer(L), is_integer(R) ->
    {L div R, L rem R}.

is_logical(#d{sign=0, exp=0, coeff=I}) ->
    lists:all(fun(Dig) -> (Dig =:= $0) or (Dig =:= $1) end,
              integer_to_list(I));
is_logical(_) ->
    false.

fill_logical(L0, R0, #context{prec=P}) ->
    L = integer_to_list(L0),
    R = integer_to_list(R0),
    {fill_logical1(P, L),
     fill_logical1(P, R)}.

fill_logical1(P, I) ->
    case P - length(I) of
        Dif when Dif > 0 ->
            string:chars($0, Dif) ++ I;
        _ ->
            string:substr(I, length(I) - P + 1)
    end.

and_char($1, $1) ->
    $1;
and_char(_, _) ->
    $0.

logical_and(L, R) ->
    ctx_op(fun logical_and/3, [L, R]).

logical_and(L, R, Ctx) ->
    case is_logical(L) of
        false ->
            raise_error(Ctx, invalid_operation);
        true ->
            case is_logical(R) of
                false ->
                    raise_error(Ctx, invalid_operation);
                true ->
                    logical_and1(L, R, Ctx)
            end
    end.

logical_and1(L, R, Ctx) ->
    {Opa, Opb} = fill_logical(L#d.coeff, R#d.coeff, Ctx),
    I = [and_char(A, B) || {A, B} <- lists:zip(Opa, Opb)],
    {#d{sign=0, exp=0, coeff=l2i(I)}, Ctx}.
