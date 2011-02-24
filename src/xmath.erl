%% @author Hunter Morris <hunter.morris@smarkets.com>
%% @copyright 2011 Smarkets

%% @doc Extra math functions

-module(xmath).

-export([pow/2]).

-spec pow(integer(), integer()) -> integer().
pow(0, 0) -> 0;
pow(X, 0) when is_integer(X) -> 1;
pow(X, N) when is_integer(X), is_integer(N), N > 0 -> pow(X, N, 1);
pow(Fl, Fr) when is_float(Fl), is_float(Fr) -> math:pow(Fl, Fr).

pow(X, N, R) when N < 2 -> R * X;
pow(X, N, R) -> pow(X * X, N bsr 1, case N band 1 of 1 -> R * X; 0 -> R end).

%% Unit tests
-ifdef(TEST).

-include_lib("eunit/include/eunit.hrl").

pow_test_() ->
    [?_assertEqual(0, pow(0, 0)),
     ?_assertEqual(1, pow(1, 0)),
     ?_assertEqual(1, pow(982734987234987234, 0)),
     ?_assertEqual(2, pow(2, 1)),
     ?_assertEqual(4, pow(2, 2)),
     ?_assertEqual(8, pow(2, 3)),
     ?_assertEqual(16, pow(2, 4)),
     ?_assertEqual(32, pow(2, 5)),
     ?_assertEqual(64, pow(2, 6)),
     ?_assertEqual(128, pow(2, 7)),
     ?_assertEqual(256, pow(2, 8)),
     ?_assertEqual(362821239651129784206041437181418830235162923906587148548813717431294723408708581691952375848426673796645485699333018085406663479859473134988678258043133631703,
                   pow(7832487, 23))].

-endif.
