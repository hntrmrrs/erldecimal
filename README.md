# erldecimal, a pure-Erlang implementation of decimal arithmetic

## Introduction

Erlang has native big integer support and double-precision floating
point support. For some scientific and financial applications, decimal
precision is required.

## Building

    $ ./rebar compile
    ==> erldecimal (compile)
    Compiled src/decimal.erl

## Using

    1> decimal:to_decimal("12")
    {d,0,12,0}
    2> decimal:to_list(decimal:mult(decimal:to_decimal("144"), decimal:to_decimal("0.1"))).
    "14.4"
