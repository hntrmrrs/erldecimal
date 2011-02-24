%% @author Hunter Morris <hunter.morris@smarkets.com>
%% @copyright 2011 Smarkets Limited.

-define(dnan,  'NaN').
-define(dsnan, 'sNaN').
-define(dinf,  'Infinity').

-type decimal_exp() :: integer() | ?dnan | ?dsnan | ?dinf.
%% Generally, the value of the decimal instance is given by:
%%     (-1)^sign * coeff * 10^exp
-record(d, {
          sign = 0  :: 0 | 1,
          coeff = 0 :: non_neg_integer(), % could be the NaN diagnostic payload
          exp = 0   :: decimal_exp() % number is exponent, atom indicates special type
         }).

-record(traps, {
          clamped = false,
          invalid_operation = false,
          division_by_zero = false,
          inexact = false,
          rounded = false,
          subnormal = false,
          overflow = false,
          underflow = false
         }).

-record(context, {
          prec = 28, % precision (for use in rounding, division, sqrt, ...)
          rounding = 'ROUND_HALF_EVEN', % how they are rounded
          emin = -999999999, % minimum exponent
          emax = 999999999, % maximum exponent
          capitals = true, % if true, 1*10^1 printed as 1E+1; if false, as 1e1
          clamp = false, % if true, change exponents when too high
          traps = #traps{invalid_operation = true, division_by_zero = true, overflow = true},
          flags = #traps{}
         }).

-type     decimal() :: #d{}.
-type pos_decimal() :: #d{sign :: 0}.

-define(dec(S, I, E), #d{sign = S, coeff = I, exp = E}).
-define(d2l(D), decimal:to_list(D)).
-define(l2d(L), decimal:to_decimal(L)).
