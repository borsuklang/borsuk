# Borsuk v0.0.2 work plan

The agent that builds v0.0.2 follows [`goal.md`](../../process/goal.md) with `V` = `0.0.2`.
The sources are the design [`language-core-v0.1.html`](../../design/language-core-v0.1.html) (sections 6, 8, 9, 13, 14, 15, 16), [`milestones.md`](../../roadmap/milestones.md) (row 0.0.2 and the implementation stack) and the [v0.0.1 plan](../v0.0.1/plan.md).

## 1. Result

v0.0.2 adds canonical bytes and exact numbers to the Borsuk core:

- the codec: one byte form for each value of each type, with a format version, and a Lean proof that encode and decode are inverse;
- the Q1 experiment of design section 14, which selects the byte layout from three arms;
- the float types `F64` and `F32` with strict IEEE 754 semantics and 18 correctly rounded math functions;
- the exact decimal type `(Decimal S)`.

`brk-ref` (Lean) and `brk` (Rust) give equal outputs on the corpus of v0.0.1 and on the corpus of section 8.

### 1.1 Changes to v0.0.1 rules

Each rule of the v0.0.1 plan stays in force, except these changes.

| v0.0.1 section | v0.0.1 rule | Change in v0.0.2 |
|---|---|---|
| 1 | The grammar of section 2 is the complete language. | The complete language is the grammar of v0.0.1 section 2 with the changes of section 2 here. |
| 2 | `(record ID (ID type)+)` | Replaced by `(record ID field+ ifield*)`. |
| 2 | `+`, `-` and `*` work on `Int`. `<` works on `Int`, `Time` and `Duration`. | The types table of section 2 here. |
| 2 | The reserved words | Section 2 adds words. |
| 3 | `Time` has no literal. | `(time INT)` exists in a `decode` item and in an `init` value. |
| 3 | The faults are `overflow` and `impossible`. | Section 3.6 adds three faults. |
| 4 | The table of codes | Section 4 adds `recursive-type`, and `layout-limit` if the codec is arm F. A type that contains itself is refused. |
| 4 | `check` prints the first error in tree order. | `recursive-type` selects its place by the rule of section 4: each type that reaches itself comes before each machine key. |
| 4 | ITEM is the `fn`, machine or example. | ITEM is also the record of an `init` value, or a `decode` item (section 4). |
| 5 | `Borsuk.coverage` is the proof. | Section 7.1 adds four theorems. |
| 7 | The `test FILE` row | `test` also runs `decode` items. With no example and no `decode` item, it prints nothing and exits 0 (section 3.8). |
| 7 | The steps of `check.sh` | Section 9. |
| 9 | The corpus, `check.sh` and the proof are the only checks. Do not write a unit test, a test helper or a mock. | The Kani harnesses of section 7.2 are checks too. The experiment runner has its own checks: the round trip, the comparison of the arms, the test of the refused frames (section 6.4) and the smoke mode (section 10, P1a). The oracle has its own stops (section 8). No other test code is legal. |
| 9 | Do not use external code. | The oracle of section 8 and Kani are tools outside the product (section 11). |
| 9 | Do not do performance work. | The arms of the experiment and the corrections of section 11 are the exceptions. |
| 9 | Lean is the reference, and Rust uses the module names of Lean. | `nat.rs`, `proofs.rs` and the experiment crate have no Lean module (section 11). |

## 2. Core IR

```
item    ::= (record ID field+ ifield*)
          | (decode ID type TEXT (value xexpr))            TEXT: a frame in lowercase hex
          | (decode ID type TEXT (invalid))
field   ::= (ID type)
ifield  ::= (ID type (init xexpr))
type    ::= F64 | F32 | (Decimal INT)
expr    ::= (f64 FLOAT) | (f32 FLOAT) | (dec DECIMAL)
          | (/ expr expr) | (sqrt expr) | (fma expr expr expr)
          | (FN1 expr) | (FN2 expr expr)
          | (round type MODE expr) | (div type MODE expr expr)
FN1     ::= exp | exp2 | log | log2 | log10 | sin | cos | tan | asin | acos | atan
          | sinh | cosh | tanh | cbrt
FN2     ::= pow | atan2 | hypot
MODE    ::= up | down | ceiling | floor | half_up | half_down | half_even | exact
xexpr   ::= (f64 FLOAT) | (f32 FLOAT) | (dec DECIMAL)
          | (time INT) | (principal TEXT)                          only in a decode item or an init value
          | (step ID xexpr INT INT) | (ticket ID xexpr INT INT INT)   only in a decode item or an init value
```

The `record` line replaces the v0.0.1 rule `(record ID (ID type)+)`. Each other line adds alternatives to the v0.0.1 rule of the same name.

Tokens:

- A `FLOAT` or a `DECIMAL` is one atom. The lexer of v0.0.1 does not change. The reader examines the atom in its position.
- A `FLOAT` in `(f64 X)` is legal when `X` is the text of a binary64 value (section 3.3). A `FLOAT` in `(f32 X)` is legal when `X` is the text of a binary32 value.
- A `DECIMAL` is legal when it is the text of a decimal value (section 3.5).
- The `TEXT` of a `decode` item has an even number of characters, each in `[0-9a-f]`.
- In `(Decimal S)`, `S` is an `INT` with 0 ≤ S ≤ 37.
- A `FLOAT` atom of more than 25 characters, a `FLOAT` atom with an exponent of more than 3 digits, or a `DECIMAL` atom of more than 40 characters, is a `parse` error. The reader refuses it before any arithmetic. Each canonical text fits in these limits.
- Each other atom or `TEXT` in these positions is a `parse` error. A form that is legal only in a `decode` item or an `init` value is a `parse` error in each other position.

Reserved words: v0.0.1 section 2 lists them. v0.0.2 adds each new form head, `F64`, `F32`, `Decimal`, each `FN1` and each `FN2`. A `MODE` word has a fixed position, so it is not reserved.

Names and types:

- `(init X)` gives the value that a field gets when it is absent from old bytes (section 5.7). `X` has the type of the field. `(new R e*)` still takes every field.
- An `init` value and an `xexpr` of a `decode` item have no actor name, no `(step INT)` and no `(ticket INT)`.
- `(time N)` is the `Time` of `N` nanoseconds. `(principal "a")` is the `Principal` with the name `a`.
- `(step M K life seq)` is the `StepId` of machine `M`, key `K`, life number `life` and sequence `seq`. `(ticket M K life seq idx)` is the ticket with index `idx`. `M` is a machine. `K` has the key type of `M`. Each `INT` of these forms is legal in the signed 64-bit range, also when it is negative or zero.
- In `(decode N T H (value X))`, `X` has the type `T`.
- A `decode` item is a declared name in the name space of v0.0.1 section 2.

Types of the number forms. The operands of one form have one type, except in the decimal `*` row and the `div` row. `(Decimal A)` and `(Decimal B)` are different types when A ≠ B.

| Form | Operand types | Result type |
|---|---|---|
| `+`, `-` | `Int`, `F64`, `F32`, `(Decimal S)` | the operand type |
| `*` | `Int`, `F64`, `F32` | the operand type |
| `*` | `(Decimal A)` and `(Decimal B)`, with A + B ≤ 37 | `(Decimal A+B)` |
| `/` | `F64`, `F32` | the operand type |
| `sqrt`, `fma`, each `FN1`, each `FN2` | `F64`, `F32` | the operand type |
| `==` | each type | `Bool` |
| `<` | `Int`, `Time`, `Duration`, `F64`, `F32`, `(Decimal S)` | `Bool` |
| `(round T MODE e)` | `e`: `(Decimal A)`, with `T` = `(Decimal S)` and S ≠ A, or with `T` = `Int`; or `e`: `Int`, with `T` = `(Decimal S)` | `T` |
| `(div T MODE a b)` | `a`: `(Decimal A)`, `b`: `(Decimal B)`, with `T` = `(Decimal S)` | `T` |

A `round` that cannot lose a digit has the mode `exact`: from `Int`, from `(Decimal A)` to `(Decimal S)` with S > A, and from `(Decimal 0)` to `Int`. So each such conversion has one form. Each other combination of this section is a `type-mismatch`.

## 3. Semantics

### 3.1 Values

| Type | Value |
|---|---|
| `F64` | A binary64 bit pattern of IEEE 754-2019 |
| `F32` | A binary32 bit pattern of IEEE 754-2019 |
| `(Decimal S)` | An integer coefficient `c` with \|c\| ≤ 10^38 − 1. The number is c × 10^−S. |

Each format has one NaN bit pattern: `0x7FF8000000000000` for binary64 and `0x7FC00000` for binary32. Each operation that gives a NaN gives this pattern. No value holds another NaN pattern.

### 3.2 Float operations

| Topic | Rule |
|---|---|
| Rounding | Each operation rounds with roundTiesToEven. This is the only rounding direction for floats. |
| `+ - * /`, `sqrt`, `fma` | IEEE 754-2019 section 5.4, with its special cases. `(fma a b c)` is a × b + c with one rounding. |
| Fusion | The runtime never fuses a multiplication and an addition. Only `fma` has one rounding. |
| Subnormal numbers | They are values. No operation flushes them to zero. |
| Faults | The only float fault is `undecided` (section 3.4). No status flag exists. |
| `==` | The bit patterns are equal. So `nan == nan` is `true`, and `0 == -0` is `false`. |
| `<` | `(< a b)` is true when the totalOrder predicate of IEEE 754-2019 section 5.10 is true for a and b, and the bit patterns of a and b are different. With the one NaN pattern, the order is −∞ < negative numbers < −0 < +0 < positive numbers < +∞ < NaN. |

### 3.3 Float text

Traces and `FLOAT` atoms use one text for each float value. The text of a value `x` in its format:

- NaN is `nan`. +∞ is `inf`. −∞ is `-inf`. +0 is `0`. −0 is `-0`.
- A negative finite `x` is `-` followed by the text of −x.
- For a positive finite `x`, let `k`, `n` and `s` be integers with k ≥ 1 and 10^(k−1) ≤ s < 10^k. The decimal s × 10^(n−k), rounded to the format of `x` with roundTiesToEven, is `x`. `k` is as small as possible. If more than one pair (`n`, `s`) fits, take the pair whose decimal s × 10^(n−k) is closest to `x`. If two are equally close, take the pair with the even `s`. `d1 … dk` are the digits of `s`.

| Condition | Text |
|---|---|
| k ≤ n ≤ 21 | `d1 … dk`, then n − k zeros |
| 0 < n < k | `d1 … dn`, then `.`, then `d(n+1) … dk` |
| −6 < n ≤ 0 | `0.`, then −n zeros, then `d1 … dk` |
| each other n | `d1`, then `.` and `d2 … dk` if k > 1, then `e`, then `+` or `-`, then \|n − 1\| in decimal |

This is the rule of ECMA-262, Number::toString, with the tie rule of its note, with `-0`, and with the three special names above. Examples: `0.1`, `1`, `-2.5e-300`, `1e+21`, `1.5e-7`, `123.456`.

A `FLOAT` atom `X` names a value. `nan`, `inf`, `-inf` and `-0` name their values. Each other `X` must match `-?(0|[1-9][0-9]*)(\.[0-9]+)?(e[+-](0|[1-9][0-9]*))?`. It names its decimal value rounded to the format with roundTiesToEven. `X` is legal only when the text of that value is `X`. So `0.10`, `1e400` and `1.0` are `parse` errors.

Lean and Rust compute the text and the value with exact integer arithmetic. Rust does not use the float formatting or the float parsing of `std`.

### 3.4 Math functions

Each `FN1` and `FN2` gives the correctly rounded value: the exact real value of the function, rounded to the format of the operands with roundTiesToEven. A value whose magnitude is at least 2^emax × (2 − 2^−p) rounds to ±∞ (IEEE 754-2019 section 4.3.1; p is 53 or 24, emax is 1023 or 127). A tiny result rounds to a subnormal number or to a zero with the sign of the exact value.

Appendix A gives the special cases: NaN, infinite and zero operands, and the edges of each domain. A special case with the value of a constant, for example ±π/2, gives the correctly rounded value of that constant.

The engine has three parts:

1. **Dyadic values.** The table lists each case where the value of the function is a dyadic rational (an integer multiple of a power of two). The engine computes such a value exactly and rounds it exactly. This includes midpoints, values beyond the range and tiny values. The engine keeps a dyadic value as an odd integer and an exponent, and it compares the exponent with the range of the format before it builds a larger integer.
2. **Algebraic functions.** `sqrt`, `cbrt` and `hypot` round exactly with integer square roots and cube roots and their remainders. They do not use the loop.
3. **Loop.** Each other case uses a loop on the working precision w = 64 × 2^j bits, for j = 0 to 10. Step j computes dyadic bounds lo ≤ f(x) ≤ hi with hi − lo ≤ 2^(−w) × max(\|lo\|, \|hi\|). When lo and hi round to the same value, that value is the result. After j = 10, the result is the fault `undecided`. The width is a target. If step j cannot reach it, the step uses the bounds that it has. The bounds are always correct (lo ≤ f(x) ≤ hi), and a step has no loop of its own.

| Function | Cases with a dyadic value |
|---|---|
| `exp`, `cos`, `cosh` | x = ±0 (value 1) |
| `sinh`, `tanh`, `sin`, `tan`, `asin`, `atan` | x = ±0 (value x) |
| `exp2` | x an integer (value 2^x) |
| `log` | x = 1 (value +0) |
| `log2` | x = 2^m (value m) |
| `log10` | x = 10^m with m ≥ 0 an integer (value m) |
| `acos` | x = 1 (value +0) |
| `atan2` | the cases of Appendix A with the value ±0 |
| `pow` | x and y finite and nonzero, outside Appendix A. Write \|x\| = a × 2^e with `a` odd and positive. Write y = c × 2^(−k) with the smallest k ≥ 0, so `c` is odd when k ≥ 1. The value is dyadic when k = 0 and (y > 0 or a = 1), or when k ≥ 1, 2^k divides e, `a` is a perfect 2^k-th power, and (c > 0 or a = 1). For x < 0, y is an integer (Appendix A gives NaN for each other y), and the value is negative when y is odd. The engine computes the odd part of a dyadic value only when it has at most 54 bits (binary64) or 25 bits (binary32). A longer odd part is not on a rounding boundary, so such a case uses the loop. Before it computes a power, the engine bounds the bit count from below: for an odd integer m of b bits, m^n has at least (b − 1) × n + 1 bits. |

Each other case has a value that is not dyadic (Lindemann–Weierstrass, Gelfond–Schneider). So no rounding boundary is equal to it, and the loop ends for each such input at some precision. The published searches of hard-to-round cases cover one-argument binary64 functions on the ranges that they state. Their hardest cases need far fewer than 65536 bits. `undecided` covers each input outside a searched range. It never gives a wrong bit.

The engine computes each constant (π, ln 2, ln 10) at the working precision. No constant in the code has more than 64 bits. The argument reduction of `sin`, `cos` and `tan` uses π at the precision that the exponent of x needs.

### 3.5 Decimal

`(Decimal S)` has its scale in the type, 38 digits, exact `+ - *`, and no rounding except in `round` and `div` with an explicit mode. So each number of a type has one byte form, and no operation loses a digit in silence. Daml `Numeric` has 38 digits and the scale in the type. Arrow `Decimal128` has a 128-bit coefficient and a fixed scale. SQL `NUMERIC(p,s)` has the same fixed scale. The eight modes are the rounding modes of Daml `DA.Numeric`.

| Topic | Rule |
|---|---|
| Range | \|c\| ≤ 10^38 − 1 for each scale |
| `+`, `-` | Exact. A result beyond the range gives the fault `overflow`. |
| `*` | Exact. The coefficients multiply, and the scales add. A result beyond the range gives `overflow`. |
| `==`, `<` | They compare the coefficients. |
| `(round T MODE e)` | The exact number of `e`, moved to the scale of `T` (0 for `Int`) and rounded with the mode. |
| `(div T MODE a b)` | The exact quotient a / b, moved to the scale of `T` and rounded with the mode. |
| Text | `-` if c < 0, then the digits of \|c\| with at least S + 1 digits (zeros on the left), with `.` before the last S digits when S > 0. Examples: `(dec 12.50)` is `(Decimal 2)`, `(dec 0.05)` is `(Decimal 2)`, `(dec -7)` is `(Decimal 0)`. |
| `DECIMAL` atom | It matches `-?(0\|[1-9][0-9]*)(\.[0-9]+)?`. Its scale is the number of digits after `.`, or 0. It is legal only when the text of its value is the atom. So `-0.00`, `00.5`, a scale above 37 and a coefficient above 10^38 − 1 are `parse` errors. |

Each mode rounds an exact rational number r to an integer.

| Mode | Result |
|---|---|
| `up` | away from zero |
| `down` | toward zero |
| `ceiling` | toward +∞ |
| `floor` | toward −∞ |
| `half_up` | the nearest integer; a tie goes away from zero |
| `half_down` | the nearest integer; a tie goes toward zero |
| `half_even` | the nearest integer; a tie goes to the even integer |
| `exact` | r if r is an integer, else the fault `inexact` |

### 3.6 Faults

| Fault | Cause |
|---|---|
| `overflow` | Also each decimal result and each `round` result beyond the range of its type |
| `inexact` | The mode `exact` met a number that needs rounding. |
| `div_zero` | `div` with a zero divisor |
| `undecided` | The loop of section 3.4 ended at j = 10. |

When one operation meets two faults, the first in this order is the result: `div_zero`, `inexact`, `overflow`.

### 3.7 Value text

| Value | Text |
|---|---|
| F64, F32 | `(f64 X)`, `(f32 X)`. `X` is the text of section 3.3. |
| Decimal | `(dec X)`. `X` is the text of section 3.5. |

### 3.8 The `decode` item

`test` runs the items of the file in file order: each `example` as in v0.0.1, and each `decode` item. A `decode` item prints no trace line.

| Item | Pass condition | Output |
|---|---|---|
| `(decode N T H (value X))` | `decode T H` gives `X`. When `H` is full (section 5.7), `encode T X` also gives `H`. | `pass N` or `fail N` |
| `(decode N T H (invalid))` | `decode T H` refuses `H`. | `pass N` or `fail N` |

The exit code of `test` is 0 when each example and each item passes, else 1. With no example and no `decode` item, `test` prints nothing and exits 0. The usage line does not change.

## 4. Static rules

`check` runs the rules in this table order. The order of v0.0.1 section 4 stays, and the new codes take the places below. Each v0.0.1 row stays, with the additions in this table.

| Code | Additions | Message |
|---|---|---|
| `parse` | Section 2: an illegal `FLOAT`, `DECIMAL`, hex `TEXT` or scale; an atom above its length limit; a field with `init` before a field without `init`; a form outside its legal position | ``text is not a program`` |
| `unknown-name` | An actor name in an `init` value or in a `decode` item; the machine of a `step` or `ticket` form that the file does not declare | ``name `N` is not declared`` |
| `duplicate-name` | — | ``name `N` is declared twice`` |
| `recursion` | — | `` `F` calls `G` before its declaration`` |
| `recursive-type` | A record, enum or newtype that reaches itself. A type reaches each type in its fields and variants, in `Option` and `Result`, and in the records, enums and newtypes that these types name. `StepId` and `Ticket` reach the key type of each machine. Also a machine whose key type reaches `StepId` or `Ticket`. | ``type `T` contains itself`` |
| `layout-limit` | Only if the codec is arm F: a record with more than 65535 fields, or an enum with more than 256 variants | ``type `T` exceeds the layout limits`` |
| `wrong-ending` | — | ``wrong ending in `ITEM` `` |
| `type-mismatch` | Each combination of section 2 with a wrong type; a mode other than `exact` in a `round` that cannot lose a digit; `(step INT)` or `(ticket INT)` in an `init` value or a `decode` item | ``type mismatch in `ITEM` `` |
| `match-arms` | — | ``match in `ITEM` does not name each constructor once`` |
| `effect-position` | — | ``wrong operation position in `ITEM` `` |
| `effect-not-declared` | — | `` `ITEM` does not declare effect `E` `` |
| `env-position` | — | `` `(env X)` is not legal in `ITEM` `` |
| `init-has-fields` | — | ``init state `S` of machine `M` has fields`` |
| `duplicate-cell` | — | ``machine `M` has two cells for (S, I)`` |
| `missing-cell` | — | ``machine `M` has no cell for (S, I)`` |
| `reject-not-declared` | — | ``command `C` does not declare reject `R` `` |
| `bad-entry` | — | ``deployment `D` has no legal entry`` |

For `recursive-type`, `T` is the first record, enum or newtype in file order that reaches itself. If no such type exists, the error is at the `key` of the first machine in file order whose key type reaches `StepId` or `Ticket`. `T` is then `StepId` or `Ticket`: the first of the two in depth-first order, left to right, of the key type. For `layout-limit`, the place is the record or the enum. For an `init` value, ITEM is the record. For a `decode` item, ITEM is the item.

The codec recurses on the type declarations. Without a cycle, encode and decode end for each type, and the fixed-size rule of arm F has one answer. A later release can remove `recursive-type` and break no program and no stored byte.

## 5. Codec

### 5.1 Frame

A frame is the byte form of one value of one type `T`: a format version, then the encoding of the value.

- The format version is a number with the value 1. In arms F and P it is a `u16` in little-endian order. In arm S it is a ULEB128 number (section 5.6).
- Decode refuses a frame with another version.
- After the encoding, the frame has no other byte.

### 5.2 The three arms

The Q1 experiment (section 6) compares three arms. Its decision selects the codec of Borsuk.

| Arm | Name | Model |
|---|---|---|
| F | Fixed offsets | Slots at fixed offsets with 32-bit offsets to the variable parts, like SSZ |
| P | Fixed offsets, packed in the log | The frames of arm F. The log record packs zero bytes with the packing of Cap'n Proto. |
| S | Compact stream | Fields one after another with LEB128 integers, like BCS with variable-length integers |

If the decision is arm F or arm P, the codec of v0.0.2 is arm F. With arm P, the packed log form belongs to the store of milestone 0.0.7, and v0.0.2 builds no packing outside the experiment. If the decision is arm S, the codec is arm S. Lean and Rust implement only the codec. The other arms exist only in the experiment.

### 5.3 Rules for each arm

- Byte order: little-endian. Integers: two's complement. No alignment.
- `Bool`: one byte, `0x00` or `0x01`. `Unit`: no bytes.
- `Text` and `Principal`: the UTF-8 bytes of the text, or of the name.
- `Option`: tag 0 is `none`, tag 1 is `some`. `Result`: tag 0 is `ok`, tag 1 is `err`. The tag is one byte.
- An enum: the tag is the index of the variant in declared order, from 0, then the fields of the variant in order.
- A record: the field count (section 5.7), then the fields in declared order.
- A newtype: the encoding of its inner value.
- `F64`, `F32`: the bit pattern, 8 or 4 bytes.
- `(Decimal S)`: the coefficient. The scale is in the type, so the bytes do not hold it.
- `StepId` and `Ticket`: the rows of sections 5.4 and 5.6. `life`, `seq` and `idx` encode as `Int`.

### 5.4 Arm F: fixed offsets

A type is fixed-size when it is `Unit`, `Bool`, `Int`, `Time`, `Duration`, `F64`, `F32` or `(Decimal S)`, or an `Option`, a `Result`, an enum or a newtype that holds fixed-size types only. Each other type is variable-size. A record is always variable-size, so that it can get new fields (section 5.7).

| Part | Size or form |
|---|---|
| `Int`, `Time`, `Duration`, `F64` | 8 bytes |
| `F32` | 4 bytes |
| `(Decimal S)` | 16 bytes, `i128` |
| Enum tag | `u8` |
| Record field count | `u16` |
| Offset, name length | `u32` |
| Fixed-size `Option`, `Result`, enum | The tag, then the fields of the variant, then zero bytes up to the size of the largest variant |
| `StepId` | A `u32` length of the machine name, the name bytes, then a composite with the slots key, `life`, `seq` |
| `Ticket` | The same as `StepId`, with a fourth slot `idx` |

A composite is a record, the composite part of a `StepId` or a `Ticket`, or a variable-size `Option`, `Result` or enum. Its encoding has two parts:

1. The fixed part. Of a record: the count, then one slot for each field. Of an `Option`, a `Result` or an enum: the tag, then one slot for each field of the variant of that tag. Of the composite part of a `StepId` or a `Ticket`: the slots only. A slot of a fixed-size type holds the encoding of the field. A slot of a variable-size type holds a `u32` offset.
2. The variable parts: the encoding of each variable-size field, in slot order.

Each offset counts from the first byte of the composite.

- The first offset equals the size of the fixed part.
- Each next offset is not below the previous offset. No offset is beyond the end of the composite.
- A part ends where the next part starts, or at the end of the composite for the last part.
- A `Text` or `Principal` part is all bytes of its part. Each other part must use all bytes of its part.
- A value at the top of a frame ends at the end of the frame.

Decode refuses each other offset, a nonzero padding byte, and a frame of 2^32 bytes or more. Encode gives no frame for a value that needs one. Lean computes the size of a fixed-size type as a `Nat`. Rust computes it with saturation at 2^32. This size of a type is a different function from `size p t v` of section 5.9, and it has a Rust mirror. Encode and decode compare the size with 2^32 before they write or read a byte of the value.

### 5.5 Arm P: packed

Arm P uses the frames of arm F. Let `B` be the complete log record of section 6.4 in the form of arm F: the version, then the four parts, each with its length: the input frame, the change, the outputs and the decision. The log record of arm P is:

1. `B` with zero bytes added up to a multiple of 8, then packed.
2. The reader finds the end of `B` from its four lengths.

The packing works on words of 8 bytes. For each word: a tag byte in which bit i is 1 when byte i of the word is not zero, then the nonzero bytes in order. Byte 0 is the first byte of the word. Bit 0 is the least significant bit of the tag.

- After a tag `0x00`, one byte N follows. N is the number of the next words that are all zero, as many as possible, at most 255.
- After a tag `0xFF` and its 8 bytes, one byte N follows. N is the number of the next words that have at most one zero byte, as many as possible, at most 255. Those words follow as they are.

### 5.6 Arm S: compact stream

| Part | Form |
|---|---|
| `Int`, `Time`, `Duration` | zigzag (`(n << 1) ^ (n >> 63)`), then ULEB128 |
| `(Decimal S)` | zigzag of the `i128` coefficient (`(c << 1) ^ (c >> 127)`), then ULEB128 |
| `F64`, `F32` | 8 or 4 bytes |
| `Text`, `Principal` | the length in bytes as ULEB128, then the bytes |
| Format version, enum tag, record count | ULEB128 |
| `Option`, `Result` tag | one byte |
| `StepId` | the machine name as `Text`, the key, `life`, `seq` |
| `Ticket` | the same, then `idx` |

A ULEB128 number has 7 bits in each byte, the low bits first. Bit 7 is 1 in each byte except the last. Decode refuses a form that is not the shortest one, and a number above the range of its type. A text length is below 2^32. A record count is at most the field count of the type, as section 5.7 gives. An enum tag is below the variant count. Decode refuses a frame of 2^32 bytes or more, and encode gives no frame for a value that needs one.

### 5.7 New fields and old bytes

Design section 15: "An added field goes last and has an initial value, so old bytes stay readable." For a record with n declared fields:

- Encode writes the count n and all n fields.
- Decode accepts a count k < n when each field k+1 to n has `init`. Those fields get their `init` values.
- Decode refuses a count above n, and a count that leaves out a field without `init`.

In arm F, the fixed part of a record with the count k has k slots, and the size of that part gives the first offset. A frame is full when each record in it has the count of its type. Each frame that encode makes is full. The fields of machine states get the same rule with the store of milestone 0.0.7 (design section 9). v0.0.2 encodes no machine state, except in the experiment (section 6.3).

### 5.8 Decode checks

Decode refuses each full frame that encode does not make, and each frame that is not full, except as section 5.7 allows. In each arm, decode refuses:

- a version other than 1, a short frame, and bytes after the value;
- a `Bool` byte other than `0x00` and `0x01`, and a tag outside the variants;
- a NaN bit pattern other than the canonical one;
- a decimal coefficient outside the range;
- a text that is not valid UTF-8;
- a `StepId` or a `Ticket` whose machine name is not a machine of the program;
- a record count that section 5.7 refuses;
- the cases of the arm (section 5.4 or 5.6).

### 5.9 Values and termination

"`v` is a value of type `t` in `p`" is the Lean predicate `Typed p t v`. It requires that each name in `t` names a record, enum or newtype of `p`. `Typed` is a Lean `Prop`. `Typed` and `size` are Lean only, and Rust has no mirror of them. The Rust `encode` makes the same refusals as the Lean `encode`.

| Type | `v` |
|---|---|
| `Unit`, `Bool` | `unit`, a `bool` |
| `Int`, `Time`, `Duration` | an `int`, `time` or `dur` in the signed 64-bit range |
| `Text`, `Principal` | a `text`, a `principal` |
| `F64`, `F32` | a bit pattern that is not a NaN, or the canonical NaN |
| `(Decimal S)` | scale S and \|c\| ≤ 10^38 − 1 |
| `StepId`, `Ticket` | the name of a machine `m` of `p`, a key `k` with `Typed p (key type of m) k`, and `life`, `seq` (and `idx`) in the signed 64-bit range |
| `(Option t)`, `(Result a b)` | `none`, or `some w` with `Typed p t w`; `ok w` with `Typed p a w`, or `err w` with `Typed p b w` |
| A record `R` | `R` with one value for each declared field, each `Typed` at the field type |
| An enum `E` | a variant `V` of `E` with one value for each field of `V`, each `Typed` at the field type |
| A newtype `N` | `N` with one value, `Typed` at the inner type |

`encode p t v` gives a frame (version and encoding) or nothing. `decode p t b` takes a frame. `full p t b` recurses on the type and the bytes as decode does, and it does not call `encode`. It is true when `b` decodes and each record count in `b` equals the field count of its record type.

Encode recurses on the value and has no fuel of its own. `encode p t v` gives nothing when `Typed p t v` is false (`Borsuk.encode_typed`). So `Borsuk.encode_decode` also shows that each value that decode gives from a full frame is typed. Decode recurses on the type and the bytes. Each step into a record, enum, newtype, `StepId` or `Ticket` uses one unit of fuel. The start fuel is the number of record, enum and newtype items plus 3. In arm F, the fixed-size test and the size of a type also recurse on the type, with the same fuel and the same start fuel. With no fuel they give nothing, and encode then gives nothing. After `check`, no path through the types is longer, because `recursive-type` refuses each cycle. The proof of `Borsuk.decode_encode` shows that this start fuel is sufficient in decode. The proof of `Borsuk.encode_total` shows that it is sufficient in encode and in the type functions. `size p t v` is the frame length of a typed value by the rules of the codec, as a `Nat`, with no limit of 2^32.

## 6. The Q1 experiment

### 6.1 Question and rule

This is question 1 ("Byte layout and zero copy") of design section 14:

> Keep fixed offsets if the step path is at most 2 % slower, and the log bytes per step and the wire bytes per message grow at most 1.3 times. The test uses the mean, and the report names the worst type.

The comparison base is arm S. The speed rule compares 95 % confidence intervals. The byte counts are exact, so the interval of a byte ratio is the ratio itself.

### 6.2 What v0.0.2 measures

v0.0.2 has no store, no network and no compiled steps. The report states each of these definitions.

| Term of the design | Definition in v0.0.2 |
|---|---|
| Step path | One step of section 6.4, in Rust code that is written by hand for each type and arm in the form that a compiler would make |
| State in memory | Arms F and P: the state frame, which a step changes in place. Arm S: a native Rust struct, decoded one time when the instance loads. This is the split layout of design section 14, fallback step 3. |
| Checked reads | Arms F and P read frames through checked slices, because the experiment crate forbids `unsafe` code. A compiler can leave out these checks after admission. The report states this limit. |
| Wire bytes per message | The mean frame size of the input values of a group |
| Log bytes per step | The mean size of the log record of section 6.4. The record holds the input, the change to the state, the outputs and the decision, as design section 6 gives for the default log record. The command ID is in the input, so the decision part holds the reply of the step (section 6.4). |
| Batch compression | None, because no store exists. The decision holds for a store that does not compress batches. If a later plan adds batch compression to the store, Q1 runs again before the first stored byte. |

### 6.3 Corpus

The corpus is in `experiments/q1-byte-layout/`. It has four groups.

| Group | Input types | State type |
|---|---|---|
| Booking | `HoldIn (cmd CommandId) (key SlotId) (sender Principal) (now Time)` and `ConfirmIn (cmd CommandId) (key SlotId) (sender Principal) (now Time) (token HoldToken)` | `SlotState`: the enum `(Absent) (Free) (Held HeldFields) (Booked BookedFields)`, with the records `HeldFields (holder Principal) (hold HoldToken) (timer Ticket)` and `BookedFields (owner Principal) (hold HoldToken)` |
| Wide | `WideIn`: `cmd CommandId`, then the fields of `Wide`. `Wide`: 14 `Int`, 4 `Flag`, 2 `Bool`, 3 `F64`, 1 `(Decimal 2)`, in this order. `Flag` is the enum `(A) (B) (C) (D)`. The mix follows the field types of the fleet study (Figure 4a: integers 38.4 %, enums 12.5 %, floats 8.8 %, booleans 6.0 %). The `(Decimal 2)` field is a choice (design section 8: money uses `Decimal`), and it takes the place of one enum field. | `Wide` |
| Varied | `VariedIn`: `cmd CommandId`, then the fields of `Varied`. `Varied`: 4 `Text`, `(Option Text)`, `(Result Int Text)`, `Kind`, 4 `Int`, in this order. `Kind` is the enum `(Plain) (Tagged Text) (Scored Int Int)`. | `Varied` |
| Personal | `PersonIn`: `cmd CommandId`, `id Int`, `name Text`, `email Text`, `phone Text`, `visits Int`, `score Int`, `since Time`, in this order | `Person`: the fields of `PersonIn` after `cmd`, with a sealed slot in place of each of the three texts |

- `HoldIn`, `ConfirmIn`, `WideIn`, `Wide`, `VariedIn`, `Varied`, `PersonIn` and `Person` are records (section 5.3), so each frame of them holds the field count.
- `CommandId` holds the four parts of a command ID in design section 6: a format version, the client identity, the issue time and a 128-bit random part. A client library of the runtime makes it, so it is a runtime header and not a user type. It is a fixed-size part of 34 bytes in each arm, with no count, no tag and no length: the version as a `u16`, the client identity as a `u64`, the issue time as an `i64`, then the 16 random bytes, each number in little-endian order. In arm F it is in the slot of its field, with no offset. The caller sends it with each command, so it is the first field of each input type.
- `SlotId` is `(newtype SlotId Int)`. `HoldToken` is `(newtype HoldToken StepId)` of machine `Slot`.
- The fields of each state form a record with a count, because a state can get new fields (design section 9).
- The runtime encrypts personal fields at admission (design section 6). So the wire frame holds the plain texts, and the state and the log record hold the slots. No source gives the count of three personal fields. The count is a choice.
- A sealed slot stands for a personal field after the encryption. It is a fixed-size part of 128 bytes in each arm, with no tag and no length. In arm F it is in the slot of its field, with no offset. The admit step of the Personal group fills each slot: the text length n as a `u16` in little-endian order, the n text bytes, then byte j of the slot pad at each position j from 2 + n to 127. Admission refuses a personal text of more than 86 bytes, in each arm, and the test of the refused frames has one such frame for `PersonIn`. v0.0.2 does no encryption. This copy stands for it, and it costs the same in each arm. The size holds 40 bytes of AEAD overhead (XChaCha20-Poly1305: a 24-byte nonce and a 16-byte tag), a 2-byte length and 86 bytes of text: a 39-character name at 2 bytes per character, a 64-octet local part of an email address, or a 15-digit phone number.

A generator makes 1000 input values for each input type. It is one SplitMix64 stream (Steele, Lea and Flood, 2014) with the seed `0x5EED`. Each draw is one `u64` value u: the state starts at the seed; for each draw, state = state + 0x9E3779B97F4A7C15 (wrapping), z = state, z = (z ^ (z >> 30)) × 0xBF58476D1CE4E5B9 (wrapping), z = (z ^ (z >> 27)) × 0x94D049BB133111EB (wrapping), and u = z ^ (z >> 31).

- Draw order: the slot pad (16 draws, each draw as 8 bytes in little-endian order). Then the 1000 values of `HoldIn`: value i, then the draws of the `cmd` and of the `now` of `ConfirmIn` number i. Then the 1000 values of `WideIn`. Then the 1000 values of `VariedIn`. Then the 1000 values of `PersonIn`. Each value draws its fields in declared order. The other fields of `ConfirmIn` come from section 6.4.
- "Uniform in [a, b)" is a + (u mod (b − a)) with one draw. "Uniform in [a, b]" is a + (u mod (b − a + 1)).
- A choice with percentages uses one draw: u mod 100, compared with the cumulative percentages in table order. A rule that names one alternative with p % selects that alternative when u mod 100 < p (`some`, `ok`, the negative sign). The `Text` weights use u mod 949 with the weights 338, 153, 76, 135, 106, 61 and 80. Equal shares among n choices use u mod n.
- An `Int` uses three draws: its class, its magnitude, its sign. A text uses one draw for its class (if its rule has classes), one for its length, and one for each character: `a` + (u mod 26) for a letter, `0` + (u mod 10) for a digit. An `Option` or a `Result` uses one draw for its tag, then the draws of its field. An enum uses one draw for its variant, then the draws of its fields. A `(Decimal 2)` uses one draw for its class and one for its coefficient. A `Bool` is true when u mod 100 < 50. An `F64` is (u mod 100000) / 100, as one correctly rounded division. "Fleet study" is Karandikar et al., MICRO 2021 (section 12).

| Kind | Rule | Source |
|---|---|---|
| `Int` | The magnitude is in [0, 2^7) with 16 %, [2^7, 2^14) with 26 %, [2^14, 2^21) with 19 %, [2^21, 2^28) with 19 %, [2^28, 2^35) with 12 % and [2^49, 2^56) with 8 %, uniform in the range. The sign is negative with 2 %. | The classes are the varint classes of 1, 2, 3, 4, 5 and 8 bytes of the fleet study. Arm S also pays its zigzag sign bit. The weights of the classes of 2 to 8 bytes are the shares of Figure 5 (7.6 %, 5.8 %, 5.6 %, 3.5 %, 2.5 %) scaled to a sum of 84 and rounded to integers. The 1-byte weight is a choice, because the 1-byte share of Figure 5 (18.9 %) also holds booleans and enums. No source gives the sign. |
| `Time` | Uniform in the year 2026 in nanoseconds: [1767225600 × 10^9, 1798761600 × 10^9) | The current epoch time |
| Key of `SlotId` | Uniform in [0, 2^32) | No source. The key is a choice of the application. |
| `CommandId` | The version is 1 (no draw). The client identity is uniform in [0, 2^32). The issue time follows the `Time` rule. The random part is two draws, each as 8 bytes in little-endian order. | Design section 6. The range of the client identity is a choice. |
| `life` | 1 | Section 6.4 |
| `Bool` | 50 % each | No source. The size is equal in each arm. |
| `F64` | (u mod 100000) / 100 for a random `u` | No source. The size is equal in arms F and S. |
| `(Decimal 2)` | The coefficient is in [50, 500), [500, 5000) or [5000, 50000) cents with equal shares, uniform in the class, positive. | The classes are the three decades from 0.50 to 500, and their limits are a choice around these means. Mean card payments: euro area about €38 (ECB, first half of 2025); United States 2024: debit card $44, credit card $97 (Federal Reserve) |
| `Text` | The length is in [0, 8], [9, 16], [17, 22], [23, 32], [33, 64], [65, 128] and [129, 512] with the weights 33.8, 15.3, 7.6, 13.5, 10.6, 6.1 and 8.0, each divided by their sum 94.9, uniform in the range. Lowercase ASCII letters. | Fleet study, Figure 4c. The classes above 512 bytes are left out, because 93 % of the messages have 512 bytes or fewer (Figure 3). |
| Principal name | The length is in [10, 28] with 80 %, [29, 31] with 15 % and [32, 60] with 5 %, uniform in the range. Lowercase ASCII letters. | Lengths of email addresses (AtData, about 90 million addresses) |
| `Option` | `some` with 50 % | Fleet study, section 3.9: more than 90 % of the messages set fewer than 52 % of their fields. |
| `Result` | `ok` with 70 % | No source |
| `Kind`, `Flag` | Each variant with the same share | No source. Equal shares are neutral. |
| Personal `name` | Length uniform in [5, 39], lowercase ASCII letters | ICAO Doc 9303: 39 characters for a name field. The lower end is a choice. |
| Personal `email` | The rule of the principal name | Lengths of email addresses (AtData) |
| Personal `phone` | Length uniform in [8, 15], ASCII digits | ITU-T E.164: at most 15 digits. The lower end is a choice. |
| Slot pad | The first 128 bytes that the generator makes, one pad for the whole run | The slot size above |

### 6.4 One step

A step takes the frame of an input value and the state of the instance in the memory form of the arm (section 6.2).

1. Admit: check the version, and check the whole input frame by the decode checks of section 5.8. Each arm makes one pass over the input frame. Step 2 can use the results of step 1. In arms F and P, these are the field positions. In arm S, step 1 decodes the input into a native struct at each depth: each `Int`, `Time`, `Bool`, `F64` and `(Decimal 2)`, each tag, and each `life`, `seq` and `idx`. Each `Text`, each `Principal` name and each machine name stays a position and a length in the frame. Step 2 reads only that struct and those positions. No arm decodes the `CommandId`. Its 34 bytes go into the log record only as bytes of the input part: in step 3, or in step 1 in the Personal group. In the Personal group, admission also fills the three slots: it writes the admitted input frame directly into the log record buffer of the step, at its final position. In each arm, the slots of the admitted input exist only in that buffer. No arm builds a slot in another place. Step 2 does not read the admitted frame: arms F and P read the input fields in the wire frame, and arm S reads the struct of step 1. Step 3 does not copy the input part again.
2. Read: read the fields of the table, from the input frame and from the state in its memory form. Fold each field into a `u64` checksum:
   - `Int`, `Time` and `F64` by their bits;
   - a `Bool` or a tag by its byte;
   - a `(Decimal 2)` by the two 64-bit halves of its coefficient;
   - a `Text` or a `Principal` by its length, its first byte and its last byte (0 for an empty text);
   - a `StepId` by its key, `life` and `seq`;
   - a `Result` or an enum by its tag only.

   A newtype folds as its inner value. A `(Decimal 2)` folds its low 64-bit half, then its high half. The input fields fold first, in the order of the table, then the state fields. The checksum starts at 0. For each folded value v as a `u64`, c = c.rotate_left(5) ^ v. A step does no other work on the checksum. Pass the checksum to `std::hint::black_box`.
3. Write: write the log record into one output buffer that each step of the arm reuses. Then change the state in its memory form. A step reads the old state only before the change, and no arm copies a part of the old state to a third buffer. In arms F and P, a Booking step copies the version and the change part of the log record into the state buffer. Arms F and P: when each changed field is fixed-size, the step writes only the slots of those fields; in the Booking group, the step writes the complete new frame into the state buffer of the instance. Arm S changes the struct. Pass the state and the log record to `std::hint::black_box`.

No arm calls the allocator in a timed step. Each instance of arm S owns one byte buffer for the variable-size parts of its struct, and it keeps each text, each principal name and each machine name as its bytes in that buffer. Each buffer keeps its capacity between passes. The warm-up passes bring each buffer of each arm to its final capacity. Arm P builds `B` (section 5.5) in a second buffer that each step of the arm reuses; in the Personal group, "final position" is the position in `B`. Step 3 then packs `B` into the output buffer, and the timed step includes the packing.

The log record is the format version of section 5.1 in the form of the arm, then four parts, each with a length before it: the input frame, the change, the outputs and the decision. In the Personal group, the input part is the frame of the admitted input: the version, then the encoding in the arm of the input with each personal text in its slot. Each length and each field index has the integer form of the arm: `u32` and `u16` in arms F and P, ULEB128 in arm S. In arm P, the log record is packed (section 5.5).

The outputs are the outputs of the Slot cells of `corpus/accept/slot.brk`: a `HoldIn` step makes `Timer.after` with the duration 30 s (`(dur 30000000000)`) and the ticket of its `Held` state; a `ConfirmIn` step makes `Timer.cancel` with the ticket of the `Held` state. Each output is a value of the enum `(After Duration Ticket) (Cancel Ticket)`, encoded in the arm with no version. A step of the other groups has no output, so its outputs part is empty.

The decision is the reply of the step (design section 6: an outcome value or a rejection with a named reason): one byte with the value 0 for an outcome or 1 for a rejection, then the outcome value or the reason, encoded in the arm with no version. For `HoldIn`, the outcome is the `HoldToken` (the `hold` of the new `Held` state). For each other step, the outcome is `(unit)`, which has no bytes. No step of the corpus gives a rejection, and no arm has code for a rejection.

| State | Change |
|---|---|
| A record state (Wide, Varied, Personal) | For each field whose value changes: the field index (the first field has the index 0), then the encoding of the new field value in the arm, with no version |
| An enum state (Booking) | The encoding of the new state in the arm, with no version |

| Group | Fields that step 2 reads | New state |
|---|---|---|
| Booking, `HoldIn` | `key`, `sender`, `now` of the input; the tag of the state | `HoldIn` number i runs on `Free` and gives `Held` with `holder` = `sender`, `hold` = the `StepId` of `Slot`, the key, life 1 and sequence i + 1, and `timer` = the ticket of `Slot`, the key, life 1, sequence i + 1 and index 0. |
| Booking, `ConfirmIn` | `token`, `sender` of the input; `holder`, `hold` of the state | `ConfirmIn` number i has the `key` and the `sender` of `HoldIn` number i, and its `token` is the `hold` of the `Held` state of `HoldIn` number i. It runs on that `Held` state and gives `Booked` with `owner` = `holder` and the same `hold`. |
| Wide | the first top-level `Int`, `Bool`, `F64` and `(Decimal 2)` field of the input and of the state | The state of step i is input value (i + 1) mod 1000 without its `cmd`, in the memory form of the arm, made before the timed passes. The new state is that state with its first top-level `Int` field (index 0) plus 1 (wrapping). |
| Varied | the first `Text`, the `Result`, the `Kind` and the first top-level `Int` of the input and of the state | The same rule as Wide, with the first top-level `Int` field at index 7 |
| Personal | `id`, `visits` and `since` of the input and of the state | The state of step i is input value (i + 1) mod 1000 after admission and without its `cmd`, in the memory form of the arm, made before the timed passes. The new state is that state with `visits` plus 1 (wrapping). |

Each arm first runs a round trip of each corpus value: decode of encode gives the value. Then the runner does one pass in each arm and compares the arms: for each step, the checksums, the decoded input parts, the decoded new states, the decoded changes, the decoded outputs and the decoded decisions are equal in each arm. In the Personal group, each slot of the input part equals the slot that section 6.3 gives, byte for byte. The runner stops at the first difference. Then each arm gets, for each input type, one frame for each refusal of section 5.8 and of the arm that the type can have, except the frame size limit of 2^32 bytes. Each such frame is the frame of one input value with a change only in the bytes of that cause. The runner stops if an admit step accepts one. The timed runs start only when each round trip and each comparison passes. Before the commit of P1a, only the round trip, the comparison, the test of the refused frames, the hex mode and the smoke mode run: no byte ratio and no time.

### 6.5 Measurement

- Build: `cargo build --release`, with no special flags.
- Quiet host: before each run, the 1-minute load average is below 1.0. The coordinator examines it each minute for 60 minutes at most. If the load stays at 1.0 or above, stop and ask. The report gives the 1-minute load average that the coordinator read before each run. When the byte ratios already fix the decision of section 6.6, the runs go on with the load that the host has, the report marks each such run "not quiet", and this case is not a stop.
- Each run uses `taskset -c 1`, with no `nice`.
- One run: the three arms in a rotated order (F P S, then P S F, then S F P). For each arm, warm-up passes for at least 1 second and at least 3 passes, then timed passes until each group has at least 1 second of timed steps and at least 30 passes. A pass runs each step of each group once, with the groups in the order Booking, Wide, Varied, Personal. In a CSV file, `arm` is `F`, `P` or `S`, and `group` is `booking`, `wide`, `varied` or `personal`. In the Booking group, a pass runs the 1000 `HoldIn` steps, then the 1000 `ConfirmIn` steps. Each group has its own time, and it covers only the steps of the group. One timed duration covers one block of steps: the 1000 steps of a group in a pass, the 1000 `HoldIn` steps, or the 1000 `ConfirmIn` steps. The runner reads `Instant` one time before the first step of the block and one time after the last step, and never between two steps.
- Before each pass, outside the timed part, each arm puts each state back in its start form.
- Runs: 12, so that each arm is first in 4 runs. The result of a run for a group is the mean time per step for each arm.
- A CSV file has one header line and one row for each arm and group: `run,position,arm,group,passes,steps,nanos`. `position` is the place of the arm in the order of the run (1 to 3). `steps` is the number of timed steps. `nanos` is the sum of the timed durations of `std::time::Instant` in whole nanoseconds. Each number is a decimal integer. Only the report mode computes the mean time per step, as `nanos / steps`. The file name is `run-NN.csv`, and `repeat-NN.csv` for the 24 runs of the repeat.
- The first 12 runs are the result. Each run that ends makes a CSV file: the runner writes the file after the last timed pass. Each file is in the commit. A run that does not end is a stop. No run is made again, except the 24 runs of the repeat.
- Speed ratio of an arm: for each run, the geometric mean over the four groups of (time of the arm) / (time of arm S). The reported speed ratio is the exponential of the mean of the log ratios of the runs. The 95 % interval is the t interval of the log ratios over the runs, with 11 degrees of freedom. For speed, the report also gives the arithmetic mean and the ratio of totals for each run, with no interval. Run NN, in the first runs and in the repeat, uses rotation number (NN − 1) mod 3 of the list F P S, P S F, S F P.
- Byte ratios of an arm: the geometric mean over the four groups of (mean bytes of the arm) / (mean bytes of arm S). A byte ratio passes when it is at most 1.3.
- The t quantiles are 2.201 for 11 degrees of freedom and 2.069 for 23 degrees of freedom.
- The runner has a report mode. It always prints the byte numbers: the mean wire bytes and the mean log bytes of each group, input type and arm, and, for each of arms F and P and for wire bytes and log bytes, the ratio of each group, the ratio of each Booking input type, the geometric mean, the arithmetic mean, the ratio of totals and the worst group. P1b runs it with no CSV file before run 01. With the files `run-NN.csv`, it also prints, for each of arms F and P, the time of each group and arm, the speed ratio and its interval for each group and for the arm with the quantile for 11 degrees of freedom, the worst group, and the arithmetic mean and the ratio of totals of each run. When `repeat-NN.csv` files exist, it prints the same speed numbers for them with the quantile for 23 degrees of freedom. A count of `run` files other than 0 and 12, a count of `repeat` files other than 0 and 24, or `repeat` files with no `run` file, is an error.
- The speed ratio of one group is the computation of the speed ratio of an arm with that group only. The time of a group and arm in the table is the exponential of the mean over the runs of the log of `nanos / steps`. For one run, the arithmetic mean is the mean over the four groups of (time of the arm) / (time of arm S), and the ratio of totals is the sum over the groups of (time per step × steps of the group in one pass) for the arm, divided by the same sum for arm S.
- "The mean" of the design rule is the geometric mean, the standard mean of benchmark ratios (Fleming and Wallace, 1986). The report also gives the arithmetic mean of the group ratios and the ratio of the totals over all steps. The decision uses the geometric mean.

A speed ratio passes when the upper end of its interval is at most 1.02. It fails when the lower end is above 1.02. Else it is unclear. An unclear result runs again with 24 runs and 23 degrees of freedom. If it is still unclear, stop and ask. The owner then chooses between the stream form and the offset form, with the numbers (design section 14). A speed result that cannot change the decision of section 6.6 needs no second run, and the report gives it as unclear.

### 6.6 Decision

1. If arm F passes the speed rule, the wire rule and the log rule, the decision is arm F.
2. Else, if arm F passes the wire rule and the log rule, stop and ask. Give the owner the numbers and the limit of the checked reads (section 6.2).
3. Else, if arm P passes the three rules, with its packed log records and with the packing in its step, the decision is arm P.
4. Else, if arm P passes the wire rule and the log rule, stop and ask, as in step 2.
5. Else the decision is arm S.

Steps 2 and 4 are an owner exception to the design rule: the checked reads of section 6.2 can cause a speed fail that a compiled step does not have. Arm P has the wire frames of arm F. So steps 3 and 4 apply only when arm F passes the wire rule and fails the log rule.

### 6.7 Report

The byte ratios are exact, so the runner computes them first, before the timed runs. The report gives them in this order.

`docs/releases/v0.0.2/q1-byte-layout.md` gives the host (CPU model, kernel, `rustc` version, commit), the definitions of section 6.2, the table of times and bytes for each group and arm, the three ratios of each arm with their intervals, the worst group of each ratio, the wire ratio and the log ratio of each input type of the Booking group, and the decision. The raw times are in `experiments/q1-byte-layout/results/`, one CSV file for each run.

## 7. Proofs

### 7.1 Lean

Each theorem has no `sorry` and no new `axiom`. Imports come only from Lean core (`Init`) and this package.

| Theorem | Statement |
|---|---|
| `Borsuk.coverage` | v0.0.1 section 5, for the v0.0.2 IR |
| `Borsuk.decode_encode` | If `check p = .ok ()`, `Typed p t v`, and `encode p t v = some b`, then `decode p t b = some v`. |
| `Borsuk.encode_decode` | If `check p = .ok ()`, `decode p t b = some v`, and `b` is full, then `encode p t v = some b`. |
| `Borsuk.encode_typed` | If `encode p t v = some b`, then `Typed p t v`. |
| `Borsuk.encode_total` | If `check p = .ok ()`, `Typed p t v` and `size p t v < 2^32`, then `encode p t v = some b` for some `b` of `size p t v` bytes. |

### 7.2 Kani

Kani 0.66.0 runs bounded proofs on the Rust codec. The harnesses are in `crates/borsuk-core/src/proofs.rs`, behind `#[cfg(kani)]`. Each harness has a `#[kani::unwind]` value: the smallest value with which it passes.

| Harness | Property |
|---|---|
| `codec_round_trip_scalars` | For each value of `Int`, `Bool`, `F64`, `F32`, `(Decimal 2)`, `Time` and `Duration`: encode gives a frame, and decode of that frame gives the value. For each `F64` and `F32` bit pattern and each `i128` coefficient at `(Decimal 2)`, with no assumption: encode gives a frame if and only if the value is a value of section 5.9. |
| `codec_round_trip_composite` | For each typed value of a record of `Int`, `Bool`, `(Option Int)` and `(Decimal 2)`, and of the enum `(A) (B Int) (C Bool Int)`: encode gives a frame, and decode of that frame gives the value. |
| `codec_canonical` | For each byte string of up to 12 bytes at `Int`, `(Option Int)` and `Text`, and of up to 20 bytes at a record of `Int` and `Text` with no `init` field: if decode accepts it, encode gives the same bytes. |

Each harness has `kani::cover!` statements. A harness that takes byte strings has one for an accepted frame of each of its types. A round-trip harness has one for each of its types, after its assumptions and the decode. So a bound or an assumption that admits no case fails step 8.

## 8. Corpus

The v0.0.1 corpus and its traces are frozen. `brk-ref` and `brk` of v0.0.2 give the same outputs on them.

| File | Content |
|---|---|
| `accept/float.brk` + `.trace` | A machine with one query for each float operation of section 3.2 and each format. Examples with one `send` line for each case: special values, signed zeros, the subnormal edges, overflow, ties to even, the canonical NaN from each operation that gives a NaN, and the total order. Values at each edge of the text table of section 3.3: n = 21 and n = 22, n = −5 and n = −6, n = k, k = 1, k = 17 for binary64, k = 9 for binary32, one value with two shortest candidates `s`, and the value 2 × 2^−1074 (text `1e-323`), whose candidates differ in `n`. For each of `+ - * /`, `sqrt` and `fma` and each format: 100 inputs over the whole domain and 100 in the main range, by the draw rules of `math.brk`, with x > 0 for `sqrt` in the main range; the stream has the seed `0x0F10A7`, and the order is `+ - * /`, `sqrt`, `fma`, each with `F64` before `F32`. A second machine keeps an `F64` field in a state, to show float text in a step line. |
| `accept/math.brk` + `.trace` | A machine with one query for each `FN1` and `FN2` and each format. For each function and format: each row of Appendix A; the dyadic cases of section 3.4; 100 inputs over the whole domain and 100 in the main range of the function; the hard cases below. "Over the whole domain" is a uniform draw of the bit patterns of the format that are not NaN, one draw for each operand. "In the main range" is a uniform draw of the bit patterns with 2^−10 ≤ \|x\| ≤ 2^10 for each operand, with x > 0 for `log`, `log2` and `log10` and for the first operand of `pow`, and with \|x\| ≤ 1 for `asin` and `acos`. The limits of the main range are a choice. The draws use the SplitMix64 stream of section 6.3 with the seed `0x0AC1E`, one stream for the file. They go function by function, in the order of the grammar of section 2. For each function: the 100 whole-domain inputs for `F64`, the 100 main-range inputs for `F64`, then the same for `F32`. An input draws its operands in order, the first operand first. A binary64 operand over the whole domain is the draw u as a bit pattern, and a binary32 operand is the low 32 bits of u. If the pattern is a NaN, the operand uses the next draw. In the main range, bit 63 of u is the sign where the function permits a negative operand, and the magnitude is the bit pattern lo + ((u mod 2^63) mod (hi − lo + 1)), where lo and hi are the bit patterns of the range limits in the format. |
| `accept/decimal.brk` + `.trace` | A machine with one query for each decimal form. Cases: literals; each operation; each mode on a tie and on a value that is not a tie, positive and negative; each fault; the order of two faults; the largest coefficient; scale sums. A second machine keeps a `(Decimal 2)` field in a state, to show decimal text in a step line. |
| `accept/codec.brk` + `.trace` | `decode` items with `(value X)` for each type kind: each scalar at its edges, empty and multibyte text, a 4-byte UTF-8 character, `F64` and `F32` at −0, NaN, ±∞ and a subnormal, `StepId`, `Ticket`, `Option`, `Result`, a newtype, nested records, a record with `init` fields and an old count. `decode` items with `(invalid)` for each refusal of section 5.8 and of the selected arm, except the frame size limit of 2^32 bytes. Each `(invalid)` frame has one cause of refusal, and it differs from the frame of a `(value X)` item of the file only in the bytes of that cause. The record count has two `(invalid)` items: a count above n, and a count that leaves out a field without `init`. |
| `accept/enum256.brk` + `.trace` | An enum with the variants `V0` to `V255`, and `decode` items with `(value X)` for `V0` and `V255` |
| `reject/recursive-type.brk` + `.err` | A recursive enum |
| `reject/recursive-type-key.brk` + `.err` | A machine whose key type is `(Option StepId)` |
| `reject/layout-limit.brk`, `layout-limit-record.brk` + `.err` | Only if the codec is arm F: an enum with the variants `V0` to `V256`; a record with the fields `f0` to `f65535` of type `Int` |
| `reject/parse-float.brk`, `parse-float-long.brk`, `parse-float-exponent.brk`, `parse-decimal.brk`, `parse-decimal-range.brk`, `parse-hex.brk`, `parse-init.brk`, `parse-scale.brk`, `parse-time.brk`, `parse-reserved.brk` + `.err` | A `FLOAT` that is not canonical; a `FLOAT` of 26 characters; a `FLOAT` with a 4-digit exponent; a `DECIMAL` that is not canonical; a `DECIMAL` of 39 digits; a hex `TEXT` with an odd length; a field without `init` after a field with `init`; `(Decimal 38)`; `(time 0)` in an example line; a `fn` with the name `log` |
| `reject/unknown-name-init.brk`, `unknown-name-step.brk` + `.err` | An actor name in an `init` value; a `step` form of a machine that the file does not declare |
| `reject/type-mismatch-decimal.brk`, `type-mismatch-step.brk`, `type-mismatch-round.brk`, `type-mismatch-init.brk` + `.err` | A `*` of two decimals with a scale sum of 38; `(step 1)` in a `decode` item; a `round` from `Int` with the mode `half_even`; an `init` value whose type differs from the field type |
| `fail/wrong-decode.brk` + `.out` | One `decode` item with a wrong expected value |
| `oracle/` | The oracle that writes `accept/float.brk`, `accept/math.brk`, `accept/decimal.brk` and `accept/enum256.brk`, and, if the codec is arm F, `reject/layout-limit.brk` and `reject/layout-limit-record.brk` |
| `oracle/hard-cases/` | The hard-case inputs, with the source of each |

Each alternative of each grammar rule of section 2 appears in an accepted file. Each query result of the numeric files is an `answer` fact, or a `fault` fact. A `.trace` file holds the stdout of `brk-ref test FILE`. The coordinator selects each name and each value that this section does not give.

The hard cases of `math.brk` (binary64):

- the inputs of the worst cases in Lefèvre and Muller, [Worst Cases for Correct Rounding of the Elementary Functions in Double Precision](https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf), for each function of this plan that the source lists;
- the inputs of [`WorstCaseTests.java`](https://raw.githubusercontent.com/openjdk/jdk/jdk-25-ga/test/jdk/java/lang/Math/WorstCaseTests.java) of OpenJDK at the tag `jdk-25-ga`, for each function of this plan that the source lists.

A function that no source lists has no hard case. This is not a stop.

For each hard case of Lefèvre and Muller, the oracle computes the value at 200 bits. If fewer than 20 equal bits follow the rounding bit, the oracle stops and names the input. The coordinator then compares that input with its source. If the input differs from its source, the coordinator corrects the copy error. If the input equals its source, stop and ask. The inputs of OpenJDK do not get this test.

The oracle:

- It is a Rust package in `corpus/oracle/` with its own `[workspace]` table and its own `Cargo.lock`. It is outside the workspace of `check.sh` step 1. It has no comments.
- It uses `rug` 1.30.0, the Rust interface to MPFR and GMP, with `default-features = false` and the features `integer`, `rational`, `float` and `std`. Its package `gmp-mpfr-sys` builds its own GMP and MPFR from source with `cc`, `m4` and `make`. MPFR gives the correctly rounded value of each function of this plan at each precision.
- It computes each value with MPFR at the precision of the format (53 or 24 bits) with round-to-nearest-even, applies the subnormal range of the format with the subnormalize function of MPFR, and gives ±∞ beyond the largest finite value. A value whose magnitude is below the smallest subnormal number rounds with the integer code of the oracle, to ±0 or to the smallest subnormal number.
- It writes the rows of Appendix A from its own copy of that table. It also computes each row with MPFR. A difference between the two is a stop.
- It computes the decimal values with the integers and rationals of `rug`.
- It computes each float text with an exact search on `rug` integers and rationals.

## 9. Layout and `check.sh`

```
Cargo.toml                       workspace; members add experiments/q1-byte-layout
crates/borsuk-core/src/          adds float.rs approx.rs math.rs decimal.rs codec.rs nat.rs proofs.rs
spec/Borsuk/                     adds Float Approx Math Decimal Codec .lean
spec/Borsuk/Proofs/              adds Codec.lean
experiments/q1-byte-layout/      the crate borsuk-q1: arms, generator, runner; results/
corpus/oracle/                   the oracle package; hard-cases/
docs/releases/v0.0.2/            plan.md, q1-byte-layout.md
```

| Lean module | Content | Rust mirror |
|---|---|---|
| `Float` | formats, bit patterns, exact rounding of a rational, `+ - * / sqrt fma`, total order, text | `float.rs` |
| `Approx` | dyadic bounds, constants, series | `approx.rs` |
| `Math` | the 18 functions, the dyadic cases, the loop | `math.rs` |
| `Decimal` | decimal operations, modes, text | `decimal.rs` |
| `Codec` | the codec, `Typed`, `full`, `size` | `codec.rs` |
| Lean `Nat` and `Int` | integers of any size | `nat.rs` |

`check.sh` keeps each v0.0.1 step and changes these steps:

| Step | Change |
|---|---|
| 3 | `Axioms.lean` prints one axiom line for each theorem of section 7.1. `check.sh` holds the list of the theorem names. Each listed theorem has exactly one line, and each axiom in it is `propext`, `Classical.choice` or `Quot.sound`. |
| 4 | The search covers `crates spec experiments corpus/oracle`, with `--exclude-dir=target`. |
| 5 | Each accepted file: `check` exits 0 with no output. Each accepted file except `hello.brk` has a trace, and `test` output equals the trace, exit 0. The v0.0.1 checks of `hello` and `slot` stay. |
| 6 | Each code of section 4 has a reject file. Each reject file: `check` output equals its `.err` file, exit 1. |
| 7 | Each fail file: `test` output equals its `.out` file, exit 1. |
| 8 | For each harness of section 7.2: `systemd-run --user --scope -q -p MemoryMax=2G -p MemorySwapMax=0 timeout -k 10 900 nice -n 19 ionice -c3 cargo kani -p borsuk-core --harness NAME` exits 0, and its output has the line `VERIFICATION:- SUCCESSFUL` exactly one time. For each harness, the output also has a line that ends with `** N of N cover properties satisfied`, with the same number N two times. N equals the count that `check.sh` holds for the harness: 7 for `codec_round_trip_scalars`, 2 for `codec_round_trip_composite`, 4 for `codec_canonical`. |

| Stage | Steps |
|---|---|
| `setup` | 1, 2, 4 |
| `lean` | `setup`, 3, and 5 to 7 for `brk-ref` |
| `all` | Steps 1 to 4, 5 to 7 for both executables, and 8 |

P0 writes these changes. After P0, `check.sh` changes only in two cases. In P2, if the codec is arm F, P2 adds `layout-limit` to the list of codes of step 6. In each later phase, the agent can correct the script only where it disagrees with this section. The phase reviewer examines each such correction, and the commit body names it. A change that weakens a step stays forbidden.

The only lint setting: the workspace `Cargo.toml` declares the `kani` configuration in `[workspace.lints.rust]` with `unexpected_cfgs = { level = "warn", check-cfg = ['cfg(kani)'] }`, and each crate of the workspace has `[lints] workspace = true`. The oracle package has no `[lints]` table.

## 10. Phases

| Phase | Work | Stage | Gate | Done when |
|---|---|---|---|---|
| P0 Setup | Branch `build/v0.0.2`. Check the tools: Lean v4.36.0, Rust 1.98.1, `cargo kani --version` 0.66.0, `cargo kani -p borsuk-core --only-codegen` on the toolchain of Kani, a build of `rug` 1.30.0 with the features of section 8 and with `cc`, `m4` and `make`, `taskset`, and `systemd-run --user --scope` with `MemoryMax`. Write the GMP and MPFR versions that `gmp-mpfr-sys` builds in the commit body. If `rustup toolchain list` does not show the toolchain that `~/.kani/kani-0.66.0/rust-toolchain-version` names, install it with `rustup toolchain install` and that name. Write the versions in the commit body. Add the scopes `float`, `approx`, `math`, `decimal`, `codec` and `experiment` to `cog.toml` and to the scope table of `docs/process/commits.md`. The lint setting, the `check.sh` changes and the skeletons of the new modules and packages. | `setup` | — | `check.sh setup` passes. |
| P1a Q1 code | The experiment crate: the three arms for the corpus types, the generator, the round trip, the comparison of the arms, the runner with its report mode, and a mode that prints in hex the frame and the log record of these values in each arm: input value 0 of each input type, and the first input value in generator order that has each of these: `none`, `some`, `ok`, `err`, each `Kind` variant, each `Flag` variant, a negative `Int` and an empty `Text`. For each value that it prints, the hex mode also prints the input value, its start state and its new state in the value text of v0.0.1 section 3 and section 3.7. A sealed slot prints as a `TEXT` of its 128 bytes in lowercase hex. A `CommandId` prints as a `TEXT` of its 34 bytes in lowercase hex. A smoke mode makes 12 runs and then 24 repeat runs. Each run has one pass on the first 10 values of each input type and uses the rotation of its run number. The mode writes the CSV files to a temporary directory outside the repository, runs the report mode on that directory, and prints only `smoke ok` or the error. It prints no time and no ratio. The experiment crate prints an `F64` with the `{}` format of `std`: for the corpus values (u mod 100000) / 100, this text equals the text of section 3.3. The rule of section 3.3 on `std` applies to `borsuk-core` only. | `setup` | G1 | The runner passes each round trip, each comparison and each test of the refused frames of section 6.4, the smoke mode prints `smoke ok`, G1 passes, and the commit of the crate is pushed. |
| P1b Q1 run | The byte ratios, then the timed runs, from the commit of P1a with a clean working tree. The report and the decision. A row for the report in the v0.0.2 table of `docs/index.md`. | `setup` | G1b | G1b passes, the report exists, and the commit body gives the decision. |
| P2 Corpus | The oracle, the hard cases, and each corpus file of section 8 except the `.trace` files. The codec files use the selected codec. The `check.sh` change of section 9, if the codec is arm F. | `setup` | G2 | G2 passes. |
| P3 Lean | The Lean modules, the changes to `Ir`, `Read`, `Check`, `Eval`, `Print` and `Main`, and the proofs. The coordinator makes the `.trace` files with `brk-ref`, again after each change in `spec/`. | `lean` | G3 | G3 passes. |
| P4 Rust | The Rust mirror and the Kani harnesses. | `all` | — | `check.sh all` passes. |
| P5 Release | The release steps of the goal. The `spec/` row of `docs/index.md` names the theorems of section 7.1. | `all` | G4 | The tag `v0.0.2` is on the remote. |

Freeze points:

| Files | Frozen when |
|---|---|
| `experiments/q1-byte-layout/` code | The commit of P1a. A change after that commit is a stop. |
| `experiments/q1-byte-layout/results/` and `q1-byte-layout.md` | The decision is in a commit. |
| The new `.brk`, `.err` and `.out` files, `corpus/oracle/` and its hard cases | G2 passes. P3 makes only the `.trace` files. If `brk-ref` differs from a frozen expected value, find which one the plan supports. If the plan supports the frozen value, correct `spec/`. Else stop and ask. |
| The new `.trace` files | G3 passes. |

| Gate | The Fable reviewer examines | Added class |
|---|---|---|
| G1 | The three arms against section 5, the generator against section 6.3, the step against section 6.4, the runner against section 6.5. It looks for each difference that makes one arm faster or smaller than its definition. It examines the output of the round trips and the comparisons. It runs the hex mode and compares each byte string of each printed value with the output of a Rust program that it writes in its own scratch directory from sections 5 and 6.4, and that does not use the experiment crate. It examines that the test of the refused frames has one frame for each refusal of sections 5.4, 5.6 and 5.8 that each input type can have, in each arm. It runs no measurement. | "unfair arm" |
| G1b | It runs the report mode on the CSV files and compares each number of the report with that output. With a Rust program that it writes in its own scratch directory and that does not use the experiment crate, it computes each speed ratio and each interval again from the CSV files, and the mean wire bytes and the mean log bytes of each group and arm again from sections 5, 6.3 and 6.4. A difference is a finding. It examines that 12 `run` files exist, and 24 `repeat` files for a repeat; that each file has one row for each arm and group; that `run` equals NN; that `position` follows the rotation of run NN; that each row has at least 30 passes and at least 10^9 nanos; and that `steps` equals `passes` × 1000, or `passes` × 2000 for the Booking group. It derives the decision from section 6.6 and compares it with the report. It runs no measurement. | "wrong decision" |
| G2 | Each corpus file against sections 2 to 5, 8 and Appendix A. It computes 30 values of the numeric files again with a Rust program with `rug` that it writes in its own scratch directory, outside the repository. The program does not use `corpus/oracle/`. It runs the oracle from a copy of `corpus/oracle/` in its scratch directory, and compares each file that the oracle writes with the file of the same path in the working tree of the phase, byte by byte. A difference is a finding. It computes the frame of each `(value X)` item of `codec.brk` and `enum256.brk` from section 5 with a Rust program that it writes in its scratch directory, and compares it with the `TEXT` of the item. Its program also computes each frame that is not full, from the first k fields of the record. It examines the one cause of refusal of each `(invalid)` frame. | "wrong expected value" |
| G3 | Each line of `float.trace` and `decimal.trace`, and 30 lines of `math.trace`, against sections 3 and 5; that each `decode` item of `codec.brk` and `enum256.brk` has its `pass` line; the statement of each theorem against section 7.1; the definitions of `Typed`, `full` and `size` against section 5.9 | "wrong expected value" |
| G4 | The full diff of the release against this plan and the design | — |

The coordinator runs the P1b measurement directly, not through a subagent.

## 11. Rules

These rules add to v0.0.1 section 9:

- The product uses Rust `std` and Lean `Init` only. Kani, the oracle (`rug`, MPFR, GMP) and the hard-case data are tools outside the product.
- `borsuk-core` compiles on the toolchain of Kani 0.66.0. If clippy 1.98.1 and that toolchain disagree, stop and ask.
- `partial` is legal only in `Read.lean`. Each definition that a theorem uses is total.
- The coordinator and each gate reviewer compute a numeric value or a byte string with a Rust program. A float or decimal value uses `rug`. No other language computes an expected value.
- `nat.rs` and `proofs.rs` are the only modules of `borsuk-core` with no Lean module. `nat.rs` mirrors Lean `Nat` and `Int`. `proofs.rs` holds the Kani harnesses.
- Rust can use the hardware `f64` and `f32` operations for `+ - * / sqrt` and `mul_add` for `fma`, because IEEE 754 fixes their results. After each one, Rust replaces a NaN with the canonical NaN. For the text of floats and the 18 functions, Rust mirrors the Lean algorithm.
- Rust can use `i128` for decimal coefficients where Lean uses `Int` with a range check.
- Do not do performance work, except in the arms of the experiment.
- A change that bounds the stack depth, or that makes a check of the largest corpus file end within the host rules, is a correction. The rule on performance work does not apply to it.
- `experiments/q1-byte-layout/` has no Lean module and does not depend on `borsuk-core`. It uses `std` only and has `#![forbid(unsafe_code)]`.
- Measurement data is never edited. A new run makes new files.

## 12. Sources

- IEEE 754-2019, sections 5.4 and 5.10. ISO/IEC 9899:2024 (C23), Annex F, section F.10. ECMA-262, Number::toString.
- [SSZ (Simple Serialize)](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md), [Cap'n Proto encoding and packing](https://capnproto.org/encoding.html#packing), BCS (Binary Canonical Serialization of the Diem project).
- Lefèvre and Muller, worst cases (link in section 8). Lauter and Lefèvre, "An efficient rounding boundary test for pow(x, y) in double precision", IEEE Transactions on Computers 58(2), 2009 (the `pow` row of section 3.4).
- [Daml `DA.Numeric`](https://docs.canton.network/appdev/reference/daml-standard-library/da-numeric.md) (section 3.5).
- Fleming and Wallace, "How not to lie with statistics: the correct way to summarize benchmark results", Communications of the ACM 29(3), 1986 (section 6.5).
- Steele, Lea and Flood, "Fast splittable pseudorandom number generators", OOPSLA 2014 (SplitMix64, section 6.3).
- [MPFR](https://www.mpfr.org/), [`rug`](https://docs.rs/rug).
- The fleet study: Karandikar et al., "A Hardware Accelerator for Protocol Buffers", MICRO 2021 ([preprint](https://sagark.org/assets/pubs/protoacc-micro2021-preprint.pdf)), Figures 3, 4a, 4c and 5, section 3.9.
- [ECB payment statistics, first half of 2025](https://ecb.europa.eu/press/stats/paysec/html/ecb.pis2025h1~36edd636c8.en.html). [Federal Reserve Payments Study](https://www.federalreserve.gov/paymentsystems/frps%5Fcy2015%5F24%5Ftopline.htm). [AtData, lengths of email addresses](https://www.atdata.com/blog/long-email-addresses).
- RFC 5116 and RFC 8439 (AEAD), the libsodium documentation of XChaCha20-Poly1305, RFC 5321 section 4.5.3.1 (email address limits), ITU-T E.164 (phone numbers), ICAO Doc 9303 (name fields).

## Appendix A. Special cases of the math functions

These rows follow C23 Annex F, section F.10, for roundTiesToEven. Each NaN result is the canonical NaN. A NaN operand gives NaN, except in the rows that say otherwise. A value with π is the correctly rounded value of the whole expression, for example of 3π/4. In an operand condition, `<` and `>` compare numbers, so ±0 is not below 0 and not above 0. They include −∞ and +∞, and "finite" excludes them.

| Function | Operand | Value |
|---|---|---|
| `exp`, `exp2` | ±0 | 1 |
| `exp`, `exp2` | −∞ | +0 |
| `exp`, `exp2` | +∞ | +∞ |
| `log`, `log2`, `log10` | ±0 | −∞ |
| `log`, `log2`, `log10` | 1 | +0 |
| `log`, `log2`, `log10` | x < 0 | NaN |
| `log`, `log2`, `log10` | +∞ | +∞ |
| `sin`, `tan` | ±0 | ±0 |
| `sin`, `cos`, `tan` | ±∞ | NaN |
| `cos` | ±0 | 1 |
| `asin` | ±0 | ±0 |
| `asin`, `acos` | \|x\| > 1 | NaN |
| `acos` | 1 | +0 |
| `atan` | ±0 | ±0 |
| `atan` | ±∞ | ±π/2 |
| `sinh`, `tanh` | ±0 | ±0 |
| `sinh` | ±∞ | ±∞ |
| `cosh` | ±0 | 1 |
| `cosh` | ±∞ | +∞ |
| `tanh` | ±∞ | ±1 |
| `cbrt` | ±0, ±∞ | the operand |
| `atan2(y, x)` | y = ±0, x = −0 | ±π |
| `atan2(y, x)` | y = ±0, x = +0 | ±0 |
| `atan2(y, x)` | y = ±0, x < 0 | ±π |
| `atan2(y, x)` | y = ±0, x > 0 | ±0 |
| `atan2(y, x)` | y < 0, x = ±0 | −π/2 |
| `atan2(y, x)` | y > 0, x = ±0 | +π/2 |
| `atan2(y, x)` | y = ±(finite > 0), x = −∞ | ±π |
| `atan2(y, x)` | y = ±(finite > 0), x = +∞ | ±0 |
| `atan2(y, x)` | y = ±∞, x finite | ±π/2 |
| `atan2(y, x)` | y = ±∞, x = −∞ | ±3π/4 |
| `atan2(y, x)` | y = ±∞, x = +∞ | ±π/4 |
| `hypot(x, y)` | x = ±∞ or y = ±∞, also when the other operand is NaN | +∞ |
| `hypot(x, y)` | y = ±0 | \|x\| |
| `hypot(x, y)` | x = ±0 | \|y\| |
| `pow(x, y)` | x = +1, each y, also NaN | 1 |
| `pow(x, y)` | y = ±0, each x, also NaN | 1 |
| `pow(x, y)` | x = ±0, y an odd integer < 0 | ±∞ |
| `pow(x, y)` | x = ±0, y < 0 and y not an odd integer | +∞ |
| `pow(x, y)` | x = ±0, y an odd integer > 0 | ±0 |
| `pow(x, y)` | x = ±0, y > 0 and y not an odd integer | +0 |
| `pow(x, y)` | x = −1, y = ±∞ | 1 |
| `pow(x, y)` | x < 0 finite, y finite and not an integer | NaN |
| `pow(x, y)` | \|x\| < 1, y = −∞ | +∞ |
| `pow(x, y)` | \|x\| > 1, y = −∞ | +0 |
| `pow(x, y)` | \|x\| < 1, y = +∞ | +0 |
| `pow(x, y)` | \|x\| > 1, y = +∞ | +∞ |
| `pow(x, y)` | x = −∞, y an odd integer < 0 | −0 |
| `pow(x, y)` | x = −∞, y < 0 and y not an odd integer | +0 |
| `pow(x, y)` | x = −∞, y an odd integer > 0 | −∞ |
| `pow(x, y)` | x = −∞, y > 0 and y not an odd integer | +∞ |
| `pow(x, y)` | x = +∞, y < 0 | +0 |
| `pow(x, y)` | x = +∞, y > 0 | +∞ |
