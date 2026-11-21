# Borsuk v0.0.3 work plan

The agent that builds v0.0.3 follows [`goal.md`](../../process/goal.md) with `V` = `0.0.3`.
The sources are the design [`language-core-v0.1.html`](../../design/language-core-v0.1.html) (sections 3, 5, 8, 10, 11, 14 and 16), [`milestones.md`](../../roadmap/milestones.md) (row 0.0.3 and the implementation stack), the [v0.0.1 plan](../v0.0.1/plan.md) and the [v0.0.2 plan](../v0.0.2/plan.md).

## 1. Result

v0.0.3 adds the memory model and native code to the Borsuk core:

- owned values, with the parameter mode `take` and the written copy `copy` (section 3);
- the mode function M, which computes the one legal signature of a `fn` from its body, with a Lean proof and the Q3 count of design section 14 (sections 3.4 and 8);
- user generics: type parameters on `newtype`, `record`, `enum` and `fn` (section 3.5);
- the bounded collections `List` and `Map`, each with a maximum size, the age limit `retain` on a state field, and the loop `for` (sections 3.6 and 3.7);
- the native lowering of machine steps to Rust text, with one arena for each step and an update in place (section 6);
- the test-cell part of question 2 of design section 14, which selects the memory form of the lowering (section 7);
- the differential tests of the implementation stack: `brk-ref` against `brk` on generated programs, and the interpreter against the compiled steps (sections 6.5 and 10.2);
- the limits of section 2.1, the scope rule for each declared name, the frame limit for each type, and the rules against equal forms and unused names (section 4);
- the cost rule of the goal, with the scale files of section 10.4;
- the layout table of the codec, and the corrections of section 1.2.

`brk-ref` (Lean) and `brk` (Rust) give equal outputs on the corpus of v0.0.1, on the corpus of v0.0.2 and on the corpus of section 10.

### 1.1 Changes to earlier rules

Each rule of the v0.0.1 plan and of the v0.0.2 plan stays in force, except these changes. "1:" is a section of the v0.0.1 plan. "2:" is a section of the v0.0.2 plan.

| Section | Earlier rule | Change in v0.0.3 |
|---|---|---|
| 1: 1, 2: 1.1 | The complete language is the grammar of v0.0.1 section 2 with the changes of v0.0.2 section 2. | The complete language also has the changes of section 2 here. |
| 1: 2 | `(newtype ID type)`, `(enum ID (ID type*)+)`, `(fn ID ((ID type)*) type (uses ConsoleOut?) block)`, `(state ID (ID type)*)` | Replaced by the forms of section 2 with `head`, `param` and `sfield`. Each text of the earlier forms stays legal. |
| 2: 2 | `(record ID field+ ifield*)` | Replaced by `(record head field+ ifield*)`. |
| 1: 2, 2: 2 | The reserved words | Section 2 adds words. |
| 1: 2 | Items, variants, states, groups, commands and queries share one name space. A name of it is legal at each place of the file. | A declared name is in scope only after its item (sections 2 and 4.1). |
| 1: 2 | An `ID`, a `SYM`, an `INT` and a `TEXT` have no length limit. The grammar has no depth limit. | Section 2.1 gives a limit for each of them. |
| 1: 3 | A `Text` is valid UTF-8. A `Principal` is a name. | Each has the size limit of section 2.1. |
| 1: 2 | `(new T e*)`, `(call ID expr*)` and the pattern `(ID bind*)` name a constructor or a `fn` by its name. | A generic item is named with its type arguments in `new` and `call` (section 3.5). |
| 1: 2 | `==` works on each type. | It also works on `List` and `Map` (section 3.6). No form compares a state collection. |
| 1: 3 | In each envelope of an example, `now` and `deadline` are `(time 0)`. | The line `(clock INT)` sets them for the later lines (section 3.10). |
| 1: 3, 2: 3.6 | The faults | Section 3.8 adds the fault `full`. |
| 1: 3, 2: 3.7 | The table of the canonical value text | Section 3.9 adds two rows. |
| 1: 3 | A fault does not change the state. | The rule stays. Section 6.3 gives the same rule for a lowered step. |
| 1: 4, 2: 4 | The table of codes and their order | Section 4 adds `mode-mismatch`, `copy-mismatch`, `collection-use` and `unused-name` after `bad-entry`, and it adds cases to earlier codes. |
| 1: 4 | `check` accepts a reject reason, a group member or an actor role that is in its list two times, two `in` blocks for one target, a fact with a fault kind or a reject reason that does not exist, and a name with no use. | `check` refuses each of them (section 4.4). |
| 2: 4 | `recursive-type` refuses a type that reaches itself. `T` is the first record, enum or newtype in file order that reaches itself. | The scope rule of section 4.1 replaces the search for a cycle. The rule for a machine key stays. |
| 2: 4 | "A later release can remove `recursive-type` and break no program and no stored byte." | Removed. A type never contains itself (section 4.1). |
| 2: 4 | `layout-limit` refuses a record with more than 65535 fields, and an enum with more than 256 variants. | It also refuses a type whose largest frame has 2^32 bytes or more, and a type above the type depth (section 4.2). |
| 2: 4 | "The codec recurses on the type declarations." | The codec reads the layout table (section 5.1). |
| 1: 4, 2: 4 | ITEM is the `fn`, machine, example, record of an `init` value, or `decode` item. | The rule stays. For `collection-use`, ITEM is the machine. |
| 2: 3.8 | The pass condition of a `decode` item | The item also compares `frame_ok` with decode (section 5.4). |
| 2: 5.4 | The definition of a fixed-size type | Section 5.2 adds the collection types and the instances of generic types. |
| 2: 5.4 | "Lean computes the size of a fixed-size type as a `Nat`. Rust computes it with saturation at 2^32. … Encode and decode compare the size with 2^32 before they write or read a byte of the value." | Removed. `check` refuses each type whose largest frame has 2^32 bytes or more (section 4.2), so encode and decode do not compare a size. The Rust `tagged` has the parameters of the Lean `tagged`. |
| 2: 5.4, 2: 5.6 | "Decode refuses … a frame of 2^32 bytes or more. Encode gives no frame for a value that needs one." | Removed. After `check`, each typed value has a frame below 2^32 bytes, and decode accepts no larger byte string (section 9.1). |
| 2: 5.8 | The decode checks | Decode also refuses a text and a name above the size limit of section 2.1. |
| 2: 5.9 | Decode, the fixed-size test and the type size use fuel. The start fuel is the number of record, enum and newtype items plus 3. | Removed. These functions recurse on the row number of the layout table (section 5.5). The fuel of `call` in `Eval` stays. |
| 2: 5.9 | The table of `Typed` | Section 5.3 adds rows, and the size limit of a text and of a name. |
| 2: 7.1 | The five theorems. `Borsuk.encode_total` has the premise `size p t v < 2^32`. | Section 9.1 states them for the v0.0.3 IR and adds theorems. `Borsuk.encode_total` has no size premise. |
| 1: 5 | "`stuck` cannot occur after `check`", with no theorem | Section 9.1 has the theorem `Borsuk.fuel_sufficient`. |
| 2: 7.2 | Two Kani harnesses. "Kani does not prove the codec on records, enums, `Option`, `Result` and `Text`." | Section 9.2 adds harnesses on the layout table, with its own memory limits. |
| 1: 7 | The usage line and the commands of `brk` and `brk-ref` | `brk` also has the command `lower` (section 6.4). `brk-ref` does not change. |
| 1: 7, 2: 9 | The steps and the stages of `check.sh` | Section 11. |
| 2: 9 | Step 8 runs each harness with `MemoryMax=4G`. | Each harness has the limit of section 9.2. |
| 1: 9, 2: 1.1 | The only checks are the corpus, `check.sh`, the proofs, the Kani harnesses, and the checks of the Q1 runner and of the oracle. | The checks of section 7.5 and section 8.4, the replay of section 6.5 and the generated programs of section 10.2 are checks too. No other test code is legal. |
| 1: 9, 2: 11 | The product uses Rust `std` and Lean `Init` only. Kani and the oracle are tools outside the product. | The rule stays. `valgrind` is a tool outside the product (section 7.5). The lowered text is an output of `brk`. It uses `std`, `borsuk-core` and `borsuk-native` only. |
| 1: 9, 2: 11 | Do not do performance work, except in the arms of the experiment. A change that bounds the stack depth, or that makes a check of the largest corpus file end within the host rules, is a correction. | The cost rule of the goal replaces both rules for v0.0.3 (section 13). A finding against the cost rule is a correction. The permitted performance work is the lowering, the arena, the crate `borsuk-native` and the test cells. |
| 2: 9 | The only lint setting is the `kani` configuration. | The release profile also has `overflow-checks = true` (section 11). |
| 1: 9, 2: 11 | Lean is the reference. `nat.rs` and `proofs.rs` are the only modules of `borsuk-core` with no Lean module. | `lower.rs` and the crate `borsuk-native` have no Lean module (section 13). Three steps of `check.sh` examine the mirror rule: the names (step 11), equal outputs (steps 5 to 7 and 9) and one cost class (step 12). |
| 1: 9 | Each concept has one type. The IR types are the syntax tree, and no second tree exists. | The rule stays. The layout table is data that `layout` computes from the tree. The lowered text is an output. |
| 2: 10 | The experiment crate of Q1 is frozen. | The rule stays. The crates of sections 7 and 8 do not change it and do not use it. |

### 1.2 Corrections to the v0.0.2 code

These corrections change no output and no byte on the frozen corpus. The scope rule refuses a forward reference, which v0.0.2 accepted. The frozen corpus has no such reference. Each correction has a check that fails without it, except the fourth: the depth limits of section 2.1 bound its cost.

| Correction | Rule | Check |
|---|---|---|
| Layout table | The fixed-size test, the sizes and the slots come from one table that `layout` computes in one pass over the items (section 5.1). No type function uses fuel. | `accept/depth64.brk` |
| Name table | `check` and `Eval` find each declared name through a sorted table of the declared names, which holds the index of each item. Lean uses `List.mergeSort` and `Array.binSearch` of `Init`. Rust uses `sort` and `binary_search` of `std`. | The scale file `names.brk` |
| Scope rule | Section 4.1 | The reject files of section 10.1 for a forward reference |
| Wanted type by reference | The Rust functions `walk_expr` and `walk_x_expr` take the wanted type as `Option<&Ty>`. They make no copy of a type for each level of a value. | None |
| Frame limit | Section 4.2 | `reject/layout-limit-size.brk`, `reject/layout-limit-frame.brk` |
| Lists of names | The check for two equal names in one list (fields, parameters, variants, reject reasons, group members, roles) sorts the list. It does not compare each pair. | The scale file `fields.brk` |
| Default stack | `brk` runs its command on the main thread, and `main.rs` starts no thread with a larger stack. The reader counts the text depth on the tokens, before it reads a form. | `accept/depth512.brk`, `reject/parse-nest8000.brk`, the scale file `stmts.brk` |
| `INT` atoms | The reader refuses an `INT` atom above its length limit before any arithmetic, as v0.0.2 does for a `FLOAT`. | The scale file `int-long.brk` |
| Integer helpers | `nat.rs` holds the one definition of `int`, `amount` and `to_u`. `approx.rs` holds the one public definition of `lit`. `math.rs` has no `int`, `lit`, `to_u` and `abs_u`, and its `pow_odd` uses `to_u`. `Approx.lean` defines `amount` and `toU`: `amount d` is the smaller of `d.natAbs` and 2^64 − 1, and `toU x` is the smaller of `x.toNat` and 2^64 − 1. Lean uses them at each place where Rust uses `amount` and `to_u`. Each of the two Lean functions also takes a proof that its argument is below 2^64 (section 9.1). | Step 11, `Borsuk.amount_exact`, and the frozen traces of `float.brk` and `math.brk` |
| No silent cut | No Rust code outside `nat.rs` has an integer `as` cast, a `saturating_` call or a `wrapping_` call. A conversion uses `From` or `try_from`. `nat.rs` holds one helper for the Lean `Nat` subtraction and one for `Int.toNat`, and each other module calls them. The release profile has `overflow-checks = true`. | Step 13, and step 1 |

## 2. Core IR

```
item    ::= (newtype head type)
          | (record head field+ ifield*)
          | (enum head (ID type*)+)
          | (fn head (param*) type (uses ConsoleOut?) block)
head    ::= ID | (ID ID+)                          a name, or a name with its type parameters
param   ::= (ID type) | (take ID type)
state   ::= (state ID sfield*)
sfield  ::= (ID type) | (ID type (retain (dur INT)))
type    ::= (List type INT) | (Map type type INT) | (ID type+)
expr    ::= (copy place)
          | (new (ID type+) expr*) | (call (ID type+) expr*)
          | (list type INT) | (map type type INT)
          | (push expr expr) | (put expr expr expr) | (drop expr expr)
          | (at expr expr) | (count expr)
          | (for (ID expr) (ID expr) block)           element, list; accumulator, start value
          | (for (ID ID expr) (ID expr) block)        key, value, map; accumulator, start value
place   ::= ID | (get place ID)
xexpr   ::= (new (ID type+) xexpr*) | (list xexpr*) | (map (xexpr xexpr)*)
line    ::= (clock INT)
```

The `item` lines and the `state` line replace the rules of the same form in v0.0.1 section 2 and v0.0.2 section 2. Each other line adds alternatives to the earlier rule of the same name. `place` is a new rule.

Tokens:

- The `INT` of a `List` type, of a `Map` type, of `(list type INT)` and of `(map type type INT)` is the maximum size. It is legal from 1 to 4294967295. Each other value is a `parse` error.
- The `INT` of `retain` is a count of nanoseconds. It is legal from 1 to 9223372036854775807. Each other value is a `parse` error.
- A file of 2^32 bytes or more is a `parse` error. So each count of a file fits in 32 bits.
- An `ID`, a `SYM`, an `INT` atom and a `TEXT` in a value position have the length limits of section 2.1. The reader refuses a longer token as a `parse` error, before any arithmetic. A `TEXT` is in a value position when it is an `expr`, an `xexpr` or the name of a `(principal TEXT)` form. The hex `TEXT` of a `decode` item is not in a value position.

Reserved words: v0.0.3 adds `take`, `copy`, `list`, `map`, `push`, `put`, `drop`, `at`, `count`, `for`, `retain`, `clock`, `List` and `Map`. No declared name of the frozen corpus is one of these words. Three frozen files have a field with the name `count`. A field name and a local name are not declared names (v0.0.1 section 2), so these files stay legal.

Names and types:

- A declared name is in scope from the end of its item to the end of the program. This applies to the name of an item and to each variant, state, group, command and query that the item declares. A state and a group are also in scope in the whole machine that declares them. Section 4.1 gives the code of a name that is not in scope.
- A type parameter is a local name of its item. It is in scope in the whole item. It is legal in each position of a `type`. Only `newtype`, `record`, `enum` and `fn` have type parameters.
- `(ID type+)` is an instance of a generic `newtype`, `record` or `enum`. It has one type argument for each type parameter. An `ID` alone names a type with no type parameter, or a type parameter.
- `(new (C T1 … Tn) e*)` builds a value of a generic record or newtype `C`, or of a variant `C` of a generic enum. The type arguments are the arguments of the record, the newtype or the enum. `(call (F T1 … Tn) e*)` calls a generic `fn`. `(new C e*)` and `(call F e*)` are legal only when the item has no type parameter. A pattern `(C bind*)` has no type argument.
- In a generic `fn`, each type argument of a `call` is a type parameter of that `fn` or a closed type. So a `fn` gets at most one instance for each list of type arguments that the text of the program holds.
- `(take x T)` is a parameter that the `fn` consumes (section 3). Only a `fn` has such parameters.
- `(list T N)` is the empty list of the type `(List T N)`. `(map K V N)` is the empty map of the type `(Map K V N)`.
- `(List T N)` and `(List T M)` are different types when N ≠ M. The same rule applies to `Map`.
- The key type `K` of a `Map` is `Int`, `Time`, `Duration`, `Text`, `Principal`, `(Decimal S)`, or a newtype of a key type.
- `(retain (dur D))` is legal only on a state field with a `Map` type.
- An `xexpr` `(list x*)` or `(map (k v)*)` takes its type from its position, as `(none)` does. The keys of a `map` form are in strictly ascending key order (section 3.6).
- In `(for (x c) (a s) body)`, `c` is a list, and `x` has its element type. In `(for (k v c) (a s) body)`, `c` is a map, and `k` and `v` have its key type and its value type. `s` has the type that the position of the `for` form needs. When the position gives no type, `s` gives the type. The `for` form and `a` have the type of `s`. `body` is a block with the tails of a `fn` (v0.0.1 section 4), and its value has the type of `s`. `x`, `k`, `v` and `a` are local names in scope in `body` only.
- The collection of `push`, `put`, `drop`, `at`, `count` and `for` gives no type to its expression, as the subject of a `match` does.

| Form | Operand types | Result type |
|---|---|---|
| `(push l e)` | `l`: `(List T N)`, `e`: `T` | `(List T N)` |
| `(put m k v)` | `m`: `(Map K V N)`, `k`: `K`, `v`: `V` | `(Map K V N)` |
| `(drop m k)` | `m`: `(Map K V N)`, `k`: `K` | `(Map K V N)` |
| `(at l i)` | `l`: `(List T N)`, `i`: `Int` | `(Option T)` |
| `(at m k)` | `m`: `(Map K V N)`, `k`: `K` | `(Option V)` |
| `(count c)` | `c`: a list or a map | `Int` |
| `(copy p)` | `p`: an owned type (section 3.1) | the type of `p` |

Each other combination of this section is a `type-mismatch`.

### 2.1 Limits

This table is the only place of each number. Design section 8 states that a type and a program text have a depth limit, and it gives the limits of a text and of an identifier. Each limit is a part of the language. A later release can raise a limit and break no program and no stored byte. It cannot lower one.

| Limit | Value | Result above the limit |
|---|---|---|
| Text depth | 512 | `parse` |
| Type depth | 64 | `layout-limit` (section 4.2) |
| Bytes of a text value, and of a principal name | 65535 | `parse` for a `TEXT` in a value position; a refusal in decode |
| Characters of an `ID` and of a `SYM` | 63 | `parse` |
| Characters of an `INT` atom, with its sign | 20 | `parse` |
| Bytes of the largest frame of a type | 2^32 − 1 | `layout-limit` (section 4.2) |

- The text depth of a token is the number of open parentheses before it that have no closing parenthesis before it. A parenthesis inside a `TEXT` does not count. The reader computes it on the list of the tokens.
- The type depth of a scalar type is 0. The type depth of `StepId` and of `Ticket` is 1 plus the largest depth of a machine key type. The type depth of an `Option`, a `Result`, a `List`, a `Map`, a record, an enum and a newtype is 1 plus the largest depth of the types that it holds. An enum holds the fields of each variant. A name counts with the depth of its declaration, and an instance with the depth of the instance.
- 64 is the default depth limit of two formats with fixed offsets, Cap'n Proto and FlatBuffers. 512 is the next power of two above 449 = 5 + 3 × 127 + 63: C11 section 5.2.4.1 asks a compiler for 127 levels of blocks and 63 levels of parentheses, and one `match` of the IR uses 3 parentheses. 65535 is the largest `u16`, as for the field count of a record. 20 characters hold each `INT` of the signed 64-bit range.
- The deepest text of the frozen corpus has 15 levels, its deepest type has the depth 2, its longest text has 88 bytes, and its longest `ID` has 27 characters.
- v0.0.3 has no text operation, so each text value comes from a literal or from a frame. A text type with its own maximum, `(Text N)`, comes with the text operations of milestone 0.0.4.

## 3. Semantics

The memory model is the model of design section 8: each value has one owner, a value is a tree, a binding never changes, and each copy that is not trivial is written. The rules of sections 3.1 to 3.4 are static. They change no result of `Eval`: `(copy p)` has the value of `p`.

### 3.1 Plain types and owned types

- `Text`, each `List` type and each `Map` type are owned.
- A type parameter is owned.
- An `Option`, a `Result`, a record, an enum or a newtype is owned when it holds an owned type: in a field, in a variant, as its inner type, or through a type that it names.
- Each other type is plain.

A copy of a plain value is trivial, and it has no text. Each plain type has a largest size (section 4.2), so each such copy has a bound: the size limit of section 2.1 for a `Principal`. So `Principal`, `StepId` and `Ticket` are plain, as in the Slot machine of design section 5, which uses `hold` and `owner` two times with no `copy`. With these rules, each `fn` of the frozen corpus has only parameters with no keyword, and no frozen file needs `copy`. If a frozen accepted file fails `check`, stop and ask.

### 3.2 Places and positions

A place is a local name with an owned type, or `(get p F)` where `p` is a place and the field `F` has an owned type. The root of a place is its local name. A part of a place `p` is `(get p F)`, a part of a part, or a binder of a `match` whose subject is `p` or a part of `p`. Two places overlap when they are the same place, or one is a part of the other.

A use is one occurrence of a place in a body. The largest place at that occurrence is the place of the use. Each use is in an owner position or in a read position.

| Owner position | Read position |
|---|---|
| An argument of `new`; the inner expression of `some`, `ok` and `err` | An operand of `==`, `<`, `and`, `not` and of each number form |
| An argument of `next` | The subject of a `match` |
| The expression of a `value` tail | The argument of an operation; the expression of `outcome` and of `answer` |
| The right side of `let` | An argument of `call` at a parameter with no keyword |
| An argument of `call` at a `take` parameter | The collection and the key of `at`; the key of `drop`; the collection of `count` and of `for` |
| The collection and the value of `push`; the collection, the key and the value of `put`; the collection of `drop` |  |
| The start value of a `for` |  |

The runtime writes the argument of an operation and the value of `outcome` and `answer` into the record of the step. Design section 14 does not count that copy. So these positions are read positions.

Each local name with an owned type is an owner name or a read name:

| Local name | Kind |
|---|---|
| A `take` parameter | owner |
| A parameter of a `fn` with no keyword | read |
| An input parameter of a cell | owner |
| A state field in a query cell | read |
| A state field in a command cell or a `Fired` cell | owner at a use from which each path ends in a `next` tail; read at each other use |
| A `let` name; the accumulator of a `for` | owner |
| An element name, a key name or a value name of a `for` | read |
| A binder of a `match` | the kind of the root, when the subject is a place; owner for each other subject |

"Path" has the meaning of v0.0.1 section 4. An expression that is not a place gives a new value. A new value in an owner position moves into its owner, and it has no `copy`.

### 3.3 Moves and copies

A use of a place `p` in an owner position is a move when each of these conditions is true:

1. The root of `p` is an owner name at this use.
2. No use that comes after it on a path overlaps `p`. The order on a path is the evaluation order of v0.0.1 section 3. Two arms of one `match` are on different paths.
3. If the use is in the body of a `for`, the declaration of the root is in that body too. Else the body can run the use more than one time.

Each other use of a place in an owner position is a copy.

| Use | The only legal text |
|---|---|
| A move | the place: `p` |
| A copy | `(copy p)` |
| A use in a read position | the place: `p` |

`check` refuses each other text with `copy-mismatch`. So the text of a body with no `copy` form fixes the place of each `copy` form, and no value is in use after its move.

### 3.4 The mode function M

M is the function of design section 8. For a `fn` `f`, `M(f)` gives one mode for each parameter:

- `take`, when the type of the parameter is owned, and the body has a use in an owner position whose place is the parameter itself. A use of a part of the parameter does not count.
- no keyword (a read), in each other case.

`check` accepts a `fn` only when the modes of its text equal `M(f)`. Else the code is `mode-mismatch`, and the message prints the parameters with the modes of `M(f)`. So a `fn` that passes a parameter on to an owner takes it, and it never copies a whole parameter that it only reads. A copy of a part of a read parameter is legal, and it is written.

| Rule of design section 8 | v0.0.3 |
|---|---|
| 1. A private function takes a parameter that it passes on to an owner. | The definition above. It applies to each `fn`. |
| 2. The mode inside a function parameter | No form of v0.0.3 has a function parameter. The rule comes with the parameter forms of milestone 0.0.5. |
| 3. The parameters of a private function are in the order of their first use. | v0.0.3 has no private `fn` and no public `fn`. The rule comes with the modules of milestone 0.0.4. |
| 4. The mode of a generic parameter is computed for the owned case. | A type parameter is owned (section 3.1). At a plain type argument, a `take` parameter gets a plain value, and no `copy` applies. |
| 5. The hash of a definition covers the signatures of the functions that it calls. | v0.0.3 has no hash. The rule comes with the cell hashes of milestone 0.0.4. |

`erase` is a Lean function on a program. It removes each `take` keyword and replaces each `(copy p)` with `p`. Section 9.1 proves that two accepted programs with the same `erase` result are equal.

### 3.5 Generics

- An instance of a generic item is the item with each type parameter replaced by its type argument. The fields, the variants, the inner type and the layout of `(C T1 … Tn)` are those of the instance.
- `check` examines a generic item one time, with its type parameters as owned types that are different from each other type. The only forms that work on a value of a type parameter are `==`, the forms that move, copy or keep a value, and a `call` of a generic `fn`.
- `Eval` does not read a type argument of `new` or `call`. The fuel rule of v0.0.1 section 5 does not change.
- The scope rule of section 4.1 applies to each type argument. The rule `recursion` of v0.0.1 applies to a generic `fn`. So the set of instances of a program is finite.
- The limits of section 4.2 apply to each instance that the text names, and to each parameter type and the result type of a generic `fn` at each `call` with closed type arguments, with these arguments in place.
- A `decode` item, an `init` value, a protocol and a machine name no type parameter, because no type parameter is in scope there.

### 3.6 Collections

| Type | Value |
|---|---|
| `(List T N)` | N and at most N elements of `T`, in order. The first element has the index 0. |
| `(Map K V N)` | N and at most N entries. An entry is a key of `K` and a value of `V`. No two entries have equal keys. The entries are in ascending key order. |

The key order compares two keys of one key type:

| Key type | Order |
|---|---|
| `Int`, `Time`, `Duration`, `(Decimal S)` | the order of `<` (v0.0.2 section 2) |
| `Text`, `Principal` | the order of the UTF-8 bytes: the first different byte decides, as an unsigned number; a text that is a prefix of another text comes first |
| A newtype | the order of its inner value |

| Form | Result |
|---|---|
| `(push l e)` | `l` with `e` after its last element. If `l` has N elements, the fault `full`. |
| `(put m k v)` | `m` with the entry (`k`, `v`). An entry with an equal key is replaced. If `m` has N entries and no entry with an equal key, the fault `full`. |
| `(drop m k)` | `m` without the entry of `k`. `m` itself, if it has no such entry. |
| `(at l i)` | `(some e)` for the element at index `i`. `(none)` if `i` is below 0, or not below the count. |
| `(at m k)` | `(some v)` for the entry of `k`. `(none)` if no such entry exists. |
| `(count c)` | The number of elements or entries, as an `Int`. |
| `==` | Two lists are equal when their counts are equal and each pair of elements at one index is equal. Two maps are equal when their counts are equal and each pair of entries at one position has equal keys and equal values. |

Each form evaluates its operands left to right. A collection form never changes a value: `push`, `put` and `drop` give a new value. The lowering makes the update in place (section 6.3).

A state collection is a state field with a `List` type or a `Map` type. Design section 8 gives two rules for it: each collection states a maximum size, and "a step reads a collection entry only by a key that the input or the fixed record gives". Section 4.3 gives the static rule for the second sentence.

A state field with `(retain (dur D))` keeps a stamp with each entry. The stamp is a `Time`.

- `put` gives the new entry the `now` of the step as its stamp.
- An entry is expired in a step when `now` − stamp ≥ D. Lean computes the difference as an `Int`. Rust computes it as an `i128`.
- `put` and `drop` first remove each expired entry. Then they do their work. So an expired entry does not count for the fault `full`.
- `at` gives `(none)` for an expired entry.
- The text of a state (section 3.9) and a `state` fact show only the entries that are not expired at the `now` of their line. They do not show a stamp.
- A map value outside a state field has no stamp. When a `next` moves a state field to its own position, each entry keeps its stamp.

The design lets each collection state an age limit. v0.0.3 gives `retain` to a state map only, because an age needs the time of a step, and only a map entry has a key that a later step can name.

v0.0.3 has no store. The load of a cold entry before the step, the time floor and the removal of dead bytes come with milestones 0.0.7 and 0.0.11.

### 3.7 `for`

`(for (x c) (a s) body)` evaluates `c`, then `s`. Then, for each element of `c` in index order, it evaluates `body` with `x` as the element and `a` as the accumulator. The accumulator is `s` for the first element, and the value of the last `body` for each next element. The value of the form is the last accumulator, or `s` for an empty list. `(for (k v c) (a s) body)` does the same for each entry of a map in key order.

- A fault in `body` is the fault of the form.
- An operation in `body` follows the rules of v0.0.1 section 4. Its outputs keep the order of the elements.
- The loop ends, because a collection has at most N elements. `Eval` recurses on the list of the elements, and this uses no fuel.
- `for` is the only loop form (design section 11).

### 3.8 Faults

| Fault | Cause |
|---|---|
| `full` | `push` or `put` on a collection that has its maximum size |

A collection form meets at most one fault. The order of v0.0.2 section 3.6 does not change.

No operation of the language clamps, wraps or cuts a value (design section 3). A result that does not fit gives a fault or an error value: `full` for a collection, `overflow` for a number, `(none)` for `at`. The rounding of IEEE 754 and the forms `round` and `div` with a mode are the named exceptions of v0.0.2.

### 3.9 Value text

| Value | Text |
|---|---|
| List | `(list v*)`, the elements in order. The empty list is `(list)`. |
| Map | `(map (k v)*)`, the entries in key order. The empty map is `(map)`. |
| A value of a generic record, enum or newtype | `(Name v*)`, as in v0.0.1 section 3. The text has no type argument. |

A `list` or `map` `xexpr` with more elements than the maximum of its type is a `type-mismatch`. A `map` `xexpr` whose keys are not in strictly ascending key order is a `type-mismatch`. So each collection value has one `xexpr` text.

### 3.10 The `clock` line

`(clock N)` sets `now` and `deadline` of each later envelope of its example to `(time N)`. It runs no step and prints no trace line. It is a `line` form for the count of `fail NAME: line N`. `N` is not below the `N` of the earlier `clock` line of the example, and not below 0. Else the line is a `type-mismatch`. The line exists because `retain` needs two steps with different times.

## 4. Static rules

`check` runs the rules in this table order. The order of v0.0.2 section 4 stays, and the four new codes come after `bad-entry`. Each earlier row stays, with the additions in this table. A code with no row here has no addition.

| Code | Additions | Message |
|---|---|---|
| `parse` | Section 2: a maximum size or a `retain` value outside its range; a `copy` of a form that is not a `place`; a file of 2^32 bytes or more. Section 2.1: a text above the text depth; an `ID`, a `SYM`, an `INT` atom or a `TEXT` in a value position above its length limit | ``text is not a program`` |
| `unknown-name` | A declared name that is not in scope at its place, except the two cases of `recursion` and `recursive-type` (section 4.1); a type argument, or a name with type arguments, that the file does not declare; a `fault` fact with a name that is not a fault of the language | ``name `N` is not declared`` |
| `duplicate-name` | A type parameter that equals a declared name or another type parameter of its item; the equal forms of section 4.4 | ``name `N` is declared twice`` |
| `recursive-type` | Section 4.1 replaces the v0.0.2 row, except its last sentence on the machine key. | ``type `T` contains itself``, or ``type `T` names `U` before its declaration`` |
| `layout-limit` | Section 4.2 | ``type `T` exceeds the layout limits`` |
| `type-mismatch` | Each combination of section 2 with a wrong type; a wrong number of type arguments; a generic name with no type argument; type arguments on a name that is not generic; a `new` or a `call` of a generic item with no type argument; in a generic `fn`, a type argument of a `call` that holds a type parameter and is not a type parameter; a `Map` key type outside section 2; `retain` on a field that is not a `Map`; the cases of sections 3.9 and 3.10; a `reject` fact on a line that is not a `send` of a command | ``type mismatch in `ITEM` `` |
| `reject-not-declared` | A `reject` fact with a reason that is not in the `rejects` list of the command of its line | ``command `C` does not declare reject `R` `` |
| `bad-entry` | A deployment entry `fn` with a type parameter | ``deployment `D` has no legal entry`` |
| `mode-mismatch` | A `fn` whose parameter modes differ from `M(f)` (section 3.4) | ``fn `F` must have the parameters `PARAMS` `` |
| `copy-mismatch` | A use whose text differs from the one legal text of section 3.3 | ``wrong copy in `ITEM` `` |
| `collection-use` | Section 4.3 | ``wrong use of collection `F` in `ITEM` `` |
| `unused-name` | Section 4.4 | ``name `N` is not used`` |

`PARAMS` is the parameter list of the `fn` with the modes of `M(f)`, in the text of the grammar with one space between two elements, for example `((take a Text) (b Int))`. For `mode-mismatch`, the place is the `fn`. For `copy-mismatch`, the place is the first wrong use in tree order. For `collection-use`, `F` is the state field, and ITEM is the machine. For `unused-name`, the place is the declaration of the name.

### 4.1 The scope rule

An item names only declared names that are in scope (section 2, design section 11). So each reference goes back in the text, the items form a graph with no cycle, and one pass over the text can check a program.

| Name that is not in scope | Code and message |
|---|---|
| A `fn` that a `call` names, in its own body or before its declaration | `recursion`, with the message of v0.0.1 |
| A `newtype`, `record` or `enum` that names itself, in a field, a variant, an inner type or a type argument | `recursive-type`: ``type `T` contains itself`` |
| A `newtype`, `record` or `enum` that names a type before the declaration of that type | `recursive-type`: ``type `T` names `U` before its declaration`` |
| Each other name: a type in a `fn`, a protocol, a machine or a `decode` item; a constructor; a role; the protocol of a machine; the machine of an example, of a `step` form or of a `ticket` form; the entry of a deployment | `unknown-name`, with its message |

- For `recursive-type`, `T` is the first item in file order with such a name. `U` is the first such name in `T`, depth first, left to right. That name selects the message.
- A type never contains itself (design section 8). This ban is permanent. Data that nests to any depth uses a collection with a maximum size.
- The rule for a machine key of v0.0.2 section 4 stays: a machine whose key type holds `StepId` or `Ticket`, through the types that it names, is refused, with the place and the `T` of v0.0.2. `check` computes this answer for each type one time, in file order, from the answers of the earlier types.
- A type parameter is a local name, so this rule does not apply to it.

### 4.2 The layout limits

`layout-limit` also refuses a type whose largest frame has 2^32 bytes or more, and a type whose depth is above the type depth of section 2.1. The place is the first type expression in tree order above a limit. `T` is the text of that type in the form of the grammar. For a record, enum or newtype with no type parameter, this text is its name.

The largest frame of a type is 2 bytes of version and `most` of the type. `most` is the largest size of the encoding of a value of the type. `whole` of a type is its size if it is fixed-size, else 4 + `most`: its slot and its part.

| Type | `most` |
|---|---|
| A fixed-size type | its size (v0.0.2 section 5.4) |
| `Text`, `Principal` | the size limit of section 2.1 |
| `StepId` | The largest value, over the machines of the program, of 4 + the bytes of the machine name + `whole` of the key type + 16. 0 for a program with no machine. |
| `Ticket` | As `StepId`, with 24 in place of 16 |
| A variable-size `(Option t)` | 1 + `whole` of `t` |
| A variable-size `(Result a b)` | 1 + the larger of `whole` of `a` and `whole` of `b` |
| A newtype | `most` of its inner type |
| A record | 2 + the sum of `whole` of each field |
| A variable-size enum | 1 + the largest sum, over its variants, of `whole` of each field |
| `(List T N)` | 4 + N × `whole` of `T` |
| `(Map K V N)` | 4 + N × (`whole` of `K` + `whole` of `V`) |

- Lean computes `most` as a `Nat`. Rust uses the checked operations of `u64`. A result that does not fit in a `u64` is above the limit.
- After `check`, each typed value of each type that the program names has a frame below 2^32 bytes (section 9.1). So encode gives a frame for each typed value, and neither encode nor decode compares a size with the limit.
- No corpus file can hold a frame at this limit. The reject files of section 10.1 check the refusal, and `Borsuk.size_bound` is the only check of the other side.

### 4.3 State collections

In a cell, a state collection `F` (section 3.6) is legal only in these positions:

- the collection of `(at F k)`;
- the collection of `(put c k v)`, `(drop c k)` or `(push c e)`, where `c` is `F` or one of these three forms on `F`, and the outer form is an argument of `next`;
- an argument of `next`.

In these forms, `k` is a key expression: a literal, an input parameter, a state field that is not a state collection, an `(env X)` form, or `(get k G)` of a key expression. Each other use of `F` is a `collection-use` error. So no cell has a `for`, a `count`, a `==` or a `call` on a state collection, and the key of each entry that a step reads comes from the input, the envelope or the fixed record.

### 4.4 Equal forms, facts and unused names

Two texts that differ only in a repeated part, or in a part with no use, have one behavior. `check` refuses them, so that one behavior has fewer texts.

| Form | Code |
|---|---|
| A reason that is two times in one `rejects` list | `duplicate-name` |
| A state that is two times in one group | `duplicate-name` |
| A role that is two times in the list of one actor | `duplicate-name` |
| Two `in` blocks of one machine with one target | `duplicate-name`, with the target as `N` |
| A `(fault SYM)` fact whose `SYM` is not a fault name of v0.0.1 section 3, v0.0.2 section 3.6 or section 3.8 | `unknown-name` |
| A `(reject SYM)` fact on a `send` of a command that does not declare `SYM` | `reject-not-declared` |
| A `(reject SYM)` fact on a `fire` line or on a `send` of a query | `type-mismatch` |
| A name with no use | `unused-name` |

`unused-name` applies to these names. `check` prints the first one in tree order of the declarations.

| Name | A use |
|---|---|
| A `newtype`, `record` or `enum` | Its name in a type, a `new` or a pattern; for an enum, also one of its variants |
| A `role` | A `by`, or the role list of an actor |
| A `fn` | A `call`, or the entry of a deployment |
| A `protocol` | The `protocol` of a machine |
| A group | The target of an `in` block |
| A type parameter | A type of its item |
| A parameter of a `fn` | An occurrence in the body |
| A parameter of a command or a query | An occurrence in a cell of that input, in one machine at least |
| A `let` name | An occurrence after it in its block |
| A named binder of a pattern | An occurrence in its arm. A binder with no use is written `_`. |
| An actor | An occurrence in a line of its example |

A machine, a deployment, an example, a `decode` item, a variant, a state, a command, a query, a field and a name of a `for` form need no use.

## 5. Codec

The codec is arm F of v0.0.2 section 5. This section changes how the codec finds the layout of a type, and it adds the collection types.

### 5.1 The layout table

`layout p` computes one table from a program. The table has three parts.

| Part | Content |
|---|---|
| Rows | One row for each closed type that the program names, and for each type of section 3.5 that a `call` gives. A closed type holds no type parameter. |
| Field rows | One list of row numbers. A row names `count` numbers of it, from the index `first`. |
| Machines | For each machine in file order: its name, and the row of its key type. |

A row has eight fields: `kind`, `fixed`, `size`, `most`, `depth`, `first`, `count` and `arg`. Each number is a `u32` in Rust and a `Nat` in Lean. `most` and `depth` are the values of section 4.2 and of section 2.1.

| `kind` | Field rows | `fixed` and `size` | `arg` |
|---|---|---|---|
| `unit`, `bool`, `int`, `time`, `duration`, `f64`, `f32`, `decimal` | none | true; the size of v0.0.2 section 5.4 | 0 |
| `text`, `principal`, `stepId`, `ticket` | none | false; 0 | 0 |
| `option` | the inner type | fixed when the inner type is fixed; 1 + its size | 0 |
| `result` | the `ok` type, the `err` type | fixed when both are fixed; 1 + the larger size | 0 |
| `newtype` | the inner type | those of the inner type | 0 |
| `record` | each field in order | false; 0 | the number of fields with no `init` |
| `enum` | one `variant` row for each variant in order | fixed when each variant is fixed; 1 + the largest variant size | 0 |
| `variant` | each field in order | fixed when each field is fixed; the sum of the field sizes | 0 |
| `list` | the element type | false; 0 | the maximum N |
| `map` | the key type, the value type | false; 0 | the maximum N |

- Each field row has a smaller number than its row. So a function that recurses on the row number ends.
- `layout` makes the rows in this order: the key type of each machine in file order, then `StepId` and `Ticket`, then each other closed type in tree order. Each row comes after the rows of its parts. The rule for a machine key (section 4.1) makes the first group free of `StepId` and `Ticket`.
- A row of an instance of a generic item has the fields of the instance (section 3.5). A generic item alone makes no row.
- `layout` ends at the first row above a limit of section 4.2. So each `size`, each `most` and each `depth` of the table fits in a `u32`.
- The codec takes each fixed-size answer, each size and each slot from the table. `encode`, `decode`, `full` and `frame_ok` find the row of their type one time.

### 5.2 Fixed-size types

The definition of v0.0.2 section 5.4 stays, with two additions: a `List` type and a `Map` type are variable-size, and an instance of a generic item has the answer of the instance.

### 5.3 Collections

A list and a map are composites (v0.0.2 section 5.4).

| Type | Fixed part | Variable parts |
|---|---|---|
| `(List T N)` | The count n as a `u32`, then one slot of `T` for each element in order | The encoding of each variable-size element, in slot order |
| `(Map K V N)` | The count n as a `u32`, then, for each entry in key order, the slot of the key and then the slot of the value | The encoding of each variable-size key and value, in slot order |

- Each offset counts from the first byte of the composite, which is the first byte of the count. The offset rules of v0.0.2 section 5.4 apply.
- Decode refuses a count above N, a count that needs more slots than the composite has bytes, and a map whose keys are not in strictly ascending key order.
- In each type, decode refuses a `Text` part, a `Principal` part and a principal name above the size limit of section 2.1.
- A frame of an empty list or an empty map is the four bytes `00 00 00 00` after the version.

`Typed` (v0.0.2 section 5.9) gets these rows:

| Type | `v` |
|---|---|
| `Text`, `Principal` | the v0.0.2 row, and at most the bytes of section 2.1 |
| `(List T N)` | a list with the maximum N and at most N elements, each `Typed` at `T` |
| `(Map K V N)` | a map with the maximum N and at most N entries, with keys in strictly ascending key order, each key `Typed` at `K` and each value `Typed` at `V` |
| An instance `(C T1 … Tn)` | a value that is `Typed` at the instance of section 3.5 |

`size` and `full` follow the same rules. A frame is full when each record in it has the count of its type, also in an element, a key or a value.

### 5.4 `frame_ok`

`frame_ok` takes the layout table, a row number and the bytes of a frame after its version. It makes each decode check of v0.0.2 section 5.8 and of section 5.3, and it builds no value. Section 9.1 proves that it accepts a byte string exactly when decode gives a value. The lowered step uses it to admit an input frame, so that the step can read each field in the received bytes (design section 8).

A `decode` item also compares the two functions: a `(value X)` item passes only when `H` has the version 1 and `frame_ok` accepts the bytes after it. An `(invalid)` item passes only when `H` has another version, or `frame_ok` refuses the bytes after it.

### 5.5 Termination

Encode recurses on the value. Decode, `full` and `frame_ok` recurse on the row number and the bytes. `layout` recurses on the list of the items and on each type. No function of the codec uses fuel. `startFuel` and each fuel parameter of v0.0.2 leave `Codec`.

## 6. Native lowering

### 6.1 What v0.0.3 lowers

`brk` lowers each cell of each machine of a program, with each `fn` that a cell calls. A generic `fn` gets one lowered function for each list of type arguments. The entry `fn` of a deployment stays with the interpreter.

The design names no code generator. The lowering of v0.0.3 writes Rust text, and `rustc` 1.98.1 compiles it to native code. This keeps the rule that the product uses `std` only, and it needs no `unsafe` code. The lowering reads the checked syntax tree and the layout table. Rule 3 of design section 16 stays true: no value of the IR and no offset depends on the pointer size.

### 6.2 Memory forms

Section 7 selects the memory form of the state: `frame` or `split`.

| Part | Form |
|---|---|
| Input | The input frame: the frame of a record whose fields are the parameters of the input, in order. A step reads it where the caller put it. |
| State, form `frame` | The state frame, in one byte buffer that the instance owns |
| State, form `split` | A Rust value: one `enum` variant for each state. A fixed-size field is a Rust value of its size. A `Text`, a `Principal` and each other variable-size part has its own byte buffer, which keeps its capacity. This is the split layout of design section 14, fallback step 3. |
| Envelope | A Rust value with `now`, `deadline`, the step identity and the sender |
| Result | One byte buffer for each step, with the reply and each output in arm F encodings |
| Temporary values | The arena (section 6.3) |

The state frame is the frame of an enum that has one variant for each state, in declared order, with the fields of the state. It is always a composite, and its tag is a `u32`. An entry of a map field with `retain` has a third slot after the key slot: its stamp, a `Time`.

The input frame, the state frame and the result buffer are internal forms of v0.0.3. They are not stored bytes and not wire bytes. The coordinator selects each detail of the result buffer that this section does not give. Milestone 0.0.7 defines the log record and the stored state.

### 6.3 Rules of a lowered step

| Rule | Content |
|---|---|
| K1 Admit | The step calls `frame_ok` on the input frame, with the layout table of the program as a constant. It runs the cell only for an accepted frame. |
| K2 Read in place | The step reads each input field and each state field at its place. It copies no variable-size part, except a new value into the state, and bytes into the result buffer. |
| K3 Arena | Each temporary value of variable size is in the arena. An allocation moves one position forward. The driver clears the arena after each step. The arena is a list of blocks. The first block has 65536 bytes. When a block is full, the arena adds a block of two times the size of the last block, or of the size that the value needs if that is larger. A clear keeps the first block only. |
| K4 Update in place | An argument of `next` that is the state field or the part that its slot holds writes nothing. The same applies to each argument of a `new` in such a position, at each depth. A new value of a fixed-size slot goes into the slot. A new value of a variable-size part goes to its place: in the form `frame`, the parts after it move when its size changes; in the form `split`, the buffer of the part gets the new bytes. |
| K5 Faults | The step evaluates each expression of its path before its first write to the state. So a step that ends in a fault leaves each byte of the state as it was. |
| K6 Calls | A parameter with no keyword gets a view of its argument. A `take` parameter gets the storage of its argument. A result is a new value in the arena, or storage that the function took. |
| K7 Copies | `(copy p)` copies the bytes of `p` into the arena. No other form copies a variable-size part, except as K2 says. |
| K8 Numbers | Each `Int` form uses the checked operations of `std`. Each float form, math form and decimal form calls the function of `borsuk-core` that the interpreter calls. |
| K9 Code | The lowered text has no `unsafe` code, no integer `as` cast, and no `saturating_` or `wrapping_` call. It uses `std`, `borsuk-core` and `borsuk-native` only. |

Each value has a largest size (section 4.2), and each `for` has a largest count. So the arena use of a step has a bound. v0.0.3 does not compute that bound: the arena grows by blocks, no step has a fault from the arena, and `brk-ref` needs no arena.

The compiled program of step 10 runs on the default stack. The depth limits of section 2.1 bound the stack use of a lowered step.

### 6.4 The command `lower`

| Use | Behavior |
|---|---|
| `brk lower FILE` | Runs `check` first, as each command does. Then it prints one Rust module on stdout and exits 0. The same file gives the same text. |
| Any other use of `brk` | The usage line `usage: brk check\|run\|test\|lower FILE` on stderr, exit 2 |

The module has these public items:

| Item | Content |
|---|---|
| `SOURCE` | The text of the program, as a constant |
| `machines()` | For each machine in file order: its name and its three functions |
| `load` | From a state frame to the memory form of the state. It refuses a frame that `frame_ok` refuses. |
| `step` | One step by the rules of section 6.3: from the state in its memory form, the envelope, the input name and the input frame, to the changed state and the result buffer. A query does not change the state. |
| `store` | From the memory form of the state to a state frame |

In the form `frame`, `load` and `store` copy the frame. The usage line of `brk-ref` does not change.

### 6.5 The replay

The replay is the compiler oracle of design section 10: "The tools compare its state hash and outputs with the compiled step." It is the function `replay` of the crate `borsuk-native`. It takes `SOURCE` and `machines()` of one lowered module.

1. It reads and checks the program with `borsuk-core`.
2. It runs each example with the interpreter of `borsuk-core`, as `brk test` does.
3. For each step and each query that the interpreter ran, it encodes the state before the event into a state frame and the input into an input frame. It calls `load`, `step` and `store` of the machine.
4. It decodes the new state frame and the result buffer. It compares the state, each output in order, and the reply with those of the interpreter. For a fault, it compares the fault name, and the state frame equals the frame before the step.
5. At the first difference, it prints `native differs: EXAMPLE line N` and gives a failure. Else it gives the number of events that it compared.

Step 10 of `check.sh` (section 11) runs the replay. Steps 5 and 9 compare `brk-ref` with the interpreter of `brk`. So the three steps together compare the Lean interpreter with the compiled steps, as the implementation stack requires.

## 7. The Q2 test cells

### 7.1 Question and rule

This is the test-cell part of question 2 ("Speed of the memory model") of design section 14:

> Four test cells lowered by hand in four ways.

The fallback table of the design gives the rule:

| Step | Trigger | Action |
|---|---|---|
| 2 | A test cell misses its limits. | Repair the compiler lowering, in at most two rounds. |
| 3 | After step 2, a test cell meets its limits only with the split layout. | Split layout |
| 4 | After step 2, a test cell meets its limits only with a path update. | Add the expression `set s.a.b = e`, with a normal-form rule that keeps one text. |

"Only the test cells, which need a prototype of the lowering and no runtime, must close before the first public example. The full speed run can close later." So v0.0.3 measures no time. The speed part of question 2 (the packet path, arm H and the two Rust versions) closes with milestone 0.0.7.

The design does not list the cells, the ways or the limits. Sections 7.2 to 7.4 define them.

### 7.2 Limits

A limit is a count for one cell in one way, over the 1000 steps of section 7.5. A cell meets its limits in a way when the three counts are 0.

| Limit | Count | Source in the design |
|---|---|---|
| A, no payload copy | The bytes of each variable-size part that the step copies, except the bytes of a new value that go to their place in the state, and the bytes that go into the result buffer | Section 14: "A payload copy is a copy of a part of variable size on the admit or step path. Personal fields and the copy into the commit buffer do not count." |
| B, update in place | The bytes of each fixed-size slot, offset, count and tag that the step writes with the value that the place holds before the write | Section 8: "the compiler reuses its storage, so the update happens in place" |
| C, arena only | The calls of the system allocator in the step | Section 8: "An allocation costs one addition, and hot paths free nothing." |

### 7.3 Cells

| Cell | Machine, state and input | What it tests |
|---|---|---|
| `hold` | `Slot` of `corpus/accept/slot.brk`: `Free`, `Hold` | A new state with three variable-size fields from the envelope; an output; an outcome that reads a new field |
| `confirm` | `Slot`: `Held`, `Confirm` with the token of the hold and the sender of the hold | The move of two variable-size fields from the old state to the new state; two reads in the received bytes |
| `visit` | `Account`: `Active`, `Visit` | A new value of one fixed-size field at depth 2 of the state, between two variable-size fields |
| `rename` | `Account`: `Active`, `Rename` | A new value of one variable-size field at depth 2 of the state, before two other variable-size parts |

`experiments/q2-test-cells/cells.brk` holds the machine `Account`:

```
(program
  (record Profile (name Text) (visits Int) (email Text))
  (protocol AccountApi
    (command Open ((name Text) (email Text) (note Text)) Unit (rejects Exists))
    (command Visit () Int (rejects NotOpen))
    (command Rename ((name Text)) Unit (rejects NotOpen)))
  (machine Account (key Int) (protocol AccountApi) (uses) (init Closed)
    (state Closed)
    (state Active (id Int) (profile Profile) (note Text))
    (in Closed
      (on Open (block (next (Active 0 (new Profile name 0 email) note) (outcome (unit)))))
      (on Visit (block (reject NotOpen)))
      (on Rename (block (reject NotOpen))))
    (in Active
      (on Open (block (reject Exists)))
      (on Visit
        (block
          (let seen (+ (get profile visits) 1))
          (next (Active id (new Profile (get profile name) seen (get profile email)) note)
            (outcome seen))))
      (on Rename
        (block
          (next (Active id (new Profile name (get profile visits) (get profile email)) note)
            (outcome (unit))))))))
```

The file is legal in v0.0.2 and in v0.0.3. Step 5 of `check.sh` runs `check` on it.

### 7.4 Ways

A way is a memory form and a text form.

| Way | Memory form of the state | Text form of the cell |
|---|---|---|
| `frame-value` | `frame` (section 6.2) | The text of the cell |
| `split-value` | `split` (section 6.2) | The text of the cell |
| `frame-path` | `frame` | The path text of the cell |
| `split-path` | `split` | The path text of the cell |

The path text replaces the `new Profile` form of `visit` with `(set profile visits seen)`, and that of `rename` with `(set profile name name)` (section 7.8). `hold` and `confirm` have no path text, so a path way uses the code of its value way for them.

Each way is Rust code that a person writes by hand in the form that the lowering of section 6 makes: rules K1 to K9, the input frame, the result buffer and the arena. For a `set` form, the step writes only the field of the path, by rule K4 for a new value. The crate is `experiments/q2-test-cells/`, with the name `borsuk-q2`. It uses `std` only, has `#![forbid(unsafe_code)]`, has no Lean module, and does not depend on `borsuk-core` or on `borsuk-q1`.

### 7.5 Inputs, counters and checks

A generator makes 1000 steps for each cell. It is the SplitMix64 stream of v0.0.2 section 6.3 with the seed `0x7E57CE11`, and it uses the draw rules and the kind rules of that section.

| Draws, in this order | Content |
|---|---|
| `hold`, i = 0 to 999 | The key: uniform in [0, 2^32). The sender: the rule of the principal name. |
| `visit`, i = 0 to 999 | The start state: `id` and `visits` by the `Int` rule, `name` by the rule of the personal `name`, `email` by the rule of the principal name, `note` by the `Text` rule; in the order `id`, `name`, `visits`, `email`, `note` |
| `rename`, i = 0 to 999 | The new name: the rule of the personal `name` |

- Step i of `hold` runs on `Free` of the instance with its key. Step i of `confirm` runs on the `Held` state that step i of `hold` gives, with the same sender and with the `hold` of that state as its token.
- Step i of `visit` and step i of `rename` run on start state i, on the instance with the key i.
- In each envelope, `now` and `deadline` are 0, the life number is 1, and the sequence is i + 1.

The module `mem.rs` of the crate holds the only functions that write the state or copy a variable-size part. Each function adds to the counters:

| Function | Work | Counter |
|---|---|---|
| `set_fixed` | Writes a fixed-size slot, an offset, a count or a tag | B: the number of bytes, when the new bytes equal the bytes that the place holds |
| `write_part` | Writes the bytes of a new variable-size value at its place in the state, or bytes into the result buffer | none |
| `move_part` | Moves or copies the bytes of a variable-size part to another place in the state, or to a place outside the state and the result buffer | A: the number of bytes |

The program has four modes.

| Mode | Work |
|---|---|
| `check` | For each cell, it runs the 1000 steps in each way. After each step, it stores the state into a state frame. It compares the state frames and the result buffers of the four ways, step by step. It prints `check ok`, or the first difference. |
| `hex` | For step 0 of each cell, it prints in lowercase hex the input frame, the state frame before the step, the state frame after the step and the result buffer. |
| `count` | It runs the 1000 steps of each cell in each way, and prints one line `CELL WAY A B` for each pair, with the sums of the two counters as decimal integers. |
| `steps WAY CELL N` | It makes the inputs and the states of the cell. It runs the 1000 steps one time and puts each state back in its start form. Then it runs the first N steps again. It prints nothing. |

Limit C uses `valgrind` 3.18.1 with the tool DHAT, a tool outside the product. For each way and cell, the coordinator runs `valgrind --tool=dhat --dhat-out-file=/dev/null target/release/borsuk-q2 steps WAY CELL N` with N = 0 and with N = 1000, each under `nice -n 19 ionice -c3`. DHAT prints one line of the form `==PID== Total: B bytes in M blocks`. `B` and `M` are decimal numbers with a `,` between groups of three digits, and the coordinator removes each `,`. The count C is M for N = 1000 minus M for N = 0. The first run of the 1000 steps brings each buffer and the arena to its final capacity, so that run is not in the count.

### 7.6 Decision

A way passes when each of the four cells meets its limits in that way. The first row that applies gives the decision.

| Row | Condition | Decision | Fallback step of the design |
|---|---|---|---|
| 1 | `frame-value` passes. | The memory form is `frame`. The language gets no `set` form. | 0 |
| 2 | `frame-value` fails, and a count that is not 0 comes from code that differs from section 6.3. | The coordinator corrects that code in a new commit, and all modes run again. This row applies two times at most. | 2 |
| 3 | `split-value` passes. | The memory form is `split`. The language gets no `set` form. | 3 |
| 4 | `frame-path` passes. | The memory form is `frame`. The language gets the `set` form of section 7.8. | 4 |
| 5 | `split-path` passes. | The memory form is `split`. The language gets the `set` form of section 7.8. | 3 and 4 |
| 6 | No way passes. | Stop and ask. Give the owner the counts. | 5 and 6 |

The counts are exact numbers. So no result is unclear, and no run is made again, except for row 2.

### 7.7 Report

`docs/releases/v0.0.3/q2-test-cells.md` gives the commit of the experiment code, the definitions of sections 7.2 to 7.4, the output of the mode `count`, the two block counts and the count C for each way and cell, the row of section 7.6 that applies, and the decision. For each count that is not 0, it names the write or the copy that causes it, with the file and the line. The outputs of the modes `count` and `hex` and each DHAT line are in `experiments/q2-test-cells/results/`.

### 7.8 The path update

This section applies only if the decision of section 7.6 is row 4 or row 5.

```
expr    ::= (set ID ID+ expr)
```

- `(set x F1 … Fn e)` gives the value of the local name `x` with the field at the path `F1 … Fn` replaced by `e`. `x` has a record type, each field of the path except the last has a record type, and `e` has the type of the last field. `set` is a reserved word.
- `x` is in an owner position, and `e` is in an owner position.
- Normal form: a `new` of a record type is refused when each argument except one is `(get p F)` of one place `p` for the field `F` of its position, as a move. The code is `copy-mismatch`. So a change of one field has one text, the `set` form.
- The corpus gets `accept/set.brk` with its trace, and `reject/copy-mismatch-set.brk` with a `new` that the normal form refuses.

## 8. The Q3 count

### 8.1 Question and rule

This is question 3 ("One signature per function") of design section 14:

> Every body up to a fixed size, from the ownership part of the grammar. The test erases modes and `copy`, and counts every completion that the checker accepts.
>
> Pass: exactly one completion for each body, and it equals M(body) (section 8). Two completions: add one rule to M, and count again.

### 8.2 Bodies

Each program of the count is one `(program …)` form with this fixed part, then one `fn` with the name `f`, then the last part below:

```
(record Box (a Text) (b Text))
(fn keep ((x Text)) Bool (uses) (block (value (== x x))))
(fn sink ((take x Text)) Box (uses) (block (value (new Box x ""))))
```

A body is a `fn` of this grammar. It is the ownership part of the grammar of section 2 with one plain type, one owned scalar type and one owned record type.

```
f  ::= (fn f (P*) R (uses) (block S? (value E)))      zero, one or two P
P  ::= (x T) | (y T)                                  the first parameter is x, the second is y
S  ::= (let z E)
T  ::= Text | Box
R  ::= Text | Box | Bool
E  ::= N | "" | (get N a) | (get N b) | (new Box E E) | (call keep E) | (call sink E) | (== E E)
N  ::= x | y | z
```

- The set holds each `fn` of this grammar in which each name is in scope and each expression has the type that its position needs. `z` is in scope only in the `value` tail. The two sides of `==` have the type `Text`.
- Each parameter and `z` has one use at least in the body, so no body breaks the rule `unused-name`.
- The size of a body is the number of its `E` nodes. The set holds each body of the size 6 or less.
- No body has a `take` keyword or a `copy` form.

The last part uses `keep`, `sink` and `f`, so that each name of the program has a use. It follows from the parameters and the result type of `f`, and it adds no choice:

```
(protocol UApi (query Q () Bool))
(machine U (key Int) (protocol UApi) (uses) (init S)
  (state S)
  (in S (on Q (block (answer (and (call keep "") (and (== (get (call sink "") a) "") USE)))))))
```

`USE` is `(call f A*)` for the result type `Bool`, `(== (call f A*) "")` for `Text`, and `(== (get (call f A*) a) "")` for `Box`. `A` is `""` for a `Text` parameter and `(new Box "" "")` for a `Box` parameter.

### 8.3 Completions

A completion of a body selects, for each parameter, the keyword `take` or no keyword, and, for each occurrence of `N`, `(get N a)` or `(get N b)` in the body, the text with `copy` or the text with no `copy`. An occurrence of `N` as the target of a `get` is not an occurrence of its own. A body with k parameters and m such occurrences has 2^(k+m) completions.

### 8.4 The count

The crate `experiments/q3-one-signature/` has the name `borsuk-q3`. It uses `std` and `borsuk-core` only, has `#![forbid(unsafe_code)]` and has no Lean module.

- The mode `count` makes each body in a fixed order: by size, then by the text. For each body, it makes each completion as a program text, reads it with `read` of `borsuk-core`, and counts the completions for which `check` gives no error. It keeps no list of the bodies in memory.
- For each body, it computes `M(f)` with its own code for the definition of section 3.4. It does not call `mode.rs`.
- It prints these lines, each with a decimal integer: `bodies N`, `completions N`, `one N`, `none N`, `many N`, `other-mode N`. `one`, `none` and `many` count the bodies with exactly one, zero, and two or more accepted completions. `other-mode` counts the bodies with exactly one accepted completion whose modes differ from `M(f)`.
- For each of the first 20 bodies that are not in `one`, or that are in `other-mode`, it prints the erased text and each accepted completion.
- The mode `list K` prints, for each K-th body in the order, each completion and `accepted` or `refused`.
- The coordinator runs `timeout -k 10 3600 nice -n 19 ionice -c3 target/release/borsuk-q3 count` one time. A timeout is a stop.

| Result | Decision |
|---|---|
| `none`, `many` and `other-mode` are 0. | Pass: the compiler accepts one signature for each body, and it is `M(f)`. Question 3 is closed. |
| Each other result | Stop and ask. Give the owner the printed bodies. |

The design rule for a result that is not clear compares the pass rate of agents with `inout`. v0.0.3 has no agent task, so v0.0.3 adds no rule to M after a count. That comparison can run with the tasks of question 4.

`docs/releases/v0.0.3/q3-one-signature.md` gives the commit of the count code, the grammar and the size of section 8.2, the output of the mode `count` and the decision. The output is in `experiments/q3-one-signature/results/count.txt`.

## 9. Proofs

### 9.1 Lean

Each theorem has no `sorry` and no new `axiom`. Imports come only from Lean core (`Init`) and this package. Each definition that a theorem uses is total.

| Theorem | Statement |
|---|---|
| `Borsuk.coverage` | v0.0.1 section 5, for the v0.0.3 IR |
| `Borsuk.decode_encode`, `Borsuk.encode_decode`, `Borsuk.encode_typed` | The statements of v0.0.2 section 7.1, for the v0.0.3 IR, with `Typed`, `full` and `size` of section 5.3. No statement has a fuel premise. |
| `Borsuk.size_bound` | If `check p = .ok ()`, `t` has a row in `layout p` and `Typed p t v`, then `size p t v` is at most 2 + `most` of that row, and it is below 2^32. |
| `Borsuk.encode_total` | If `check p = .ok ()`, `t` has a row in `layout p` and `Typed p t v`, then `encode p t v = some b` for some `b` of `size p t v` bytes. The proof uses `Borsuk.size_bound`. |
| `Borsuk.frame_ok_decode` | If `check p = .ok ()` and `r` is the row of the closed type `t` in `layout p`, then `frameOk (layout p) r b = true` if and only if `decode p t (w ++ b) = some v` for some `v`. Here `w` is the two bytes of the version 1. |
| `Borsuk.mode_exact` | If `check p = .ok ()` and `f` is a `fn` of `p`, then the modes of `f` equal `M(f)`, and `M(f)` equals `M` of `f` in `erase p`. |
| `Borsuk.one_signature` | If `check p = .ok ()`, `check q = .ok ()` and `erase p = erase q`, then `p = q`. |
| `Borsuk.fuel_sufficient` | If `check p = .ok ()`, then for each `fn` name, each list of arguments and each `k`: `callFn p (fuelOf p + k)` and `callFn p (fuelOf p)` give the same result. So no `call` meets the fuel 0, which is the cause of `stuck` that v0.0.1 section 5 names. |
| `Borsuk.amount_exact` | For each `d` and each proof `h` that `d.natAbs < 2^64`: `amount d h = d.natAbs`. For each `x` and each proof `h` that `x.toNat < 2^64`: `toU x h = x.toNat`. |
| `Borsuk.round_int_range` | If `round` or `div` with the type `Int` gives a value and no fault, that value is in the signed 64-bit range. |

- `Borsuk.one_signature` is the Lean proof of design section 8 that M is deterministic. It also covers each `copy` form. `M` has the Lean name `mode`. `erase`, `mode`, `layout` and `frameOk` are the definitions of sections 3.4, 5.1 and 5.4.
- `amount` and `toU` take the proof `h` as a parameter. So each call in `Approx` and `Math` states that its argument is below 2^64, and Lean checks it. With `Borsuk.amount_exact`, the limit of these two functions changes no result. This is the theorem for the claim "no input reaches the saturation".
- `Borsuk.round_int_range` is the theorem for the Rust conversion from `i128` to `i64` in `dec_value`: the conversion cannot fail.
- v0.0.3 states no other claim "this cannot occur" without a theorem, a harness or a result that the user sees.

### 9.2 Kani

Kani 0.68.0 runs bounded proofs on the Rust code. The harnesses are behind `#[cfg(kani)]`, in `proofs.rs` of their crate. Each harness has a `#[kani::unwind]` value: the smallest value with which it passes.

Kani checks only the code that reads bytes from outside (the frame check of section 5.4) and the code that gives out memory (the arena of section 6.3), and it keeps the two harnesses of v0.0.2. A Kani limit is never a reason to change the IR, the codec or the lowering.

| Harness | Crate | Property | Covers | `MemoryMax` |
|---|---|---|---|---|
| `codec_round_trip_scalars` | `borsuk-core` | v0.0.2 section 7.2 | 7 | 4G |
| `codec_canonical` | `borsuk-core` | v0.0.2 section 7.2 | 7 | 4G |
| `layout_frame_fixed` | `borsuk-core` | For each byte string of up to 12 bytes at the row of `(Option Int)`: `frame_ok` ends with no panic and no overflow. | 1 | 2G |
| `layout_frame_variable` | `borsuk-core` | The same, for up to 12 bytes at the row of `(Option Text)` | 1 | 6G |
| `layout_frame_record` | `borsuk-core` | The same, for up to 16 bytes at the row of a record with one `Int` field and one `Text` field | 1 | 8G |
| `arena_alloc` | `borsuk-native` | For each three sizes, each a `u32` of at most 131072: three allocations on a new arena end with no panic and no overflow, and no two of the three ranges share a byte. | 1 | 2G |

- The three `layout_frame` harnesses use one constant layout table in `proofs.rs`, with the rows of `Int`, `Text`, `(Option Int)`, `(Option Text)` and the record. They call `frame_ok` with a row number. They build no `Value` and no `Program`.
- "No panic and no overflow" is the set of default checks of Kani: each panic, each arithmetic overflow and each access outside a slice fails the harness. The release build has the same overflow checks (section 11).
- A `layout_frame` harness has one `kani::cover!` for an accepted byte string. The harness `arena_alloc` has one for three sizes that are not 0. The bounds admit an accepted frame of each type: 9 bytes for `(Option Int)`, 5 bytes for `(Option Text)` with an empty text, and 14 bytes for the record with an empty text.
- A prototype of the table form gave these values with Kani 0.68.0: 0.11 GB for the fixed row, 5.0 GB and 338 seconds for the variable row, 6.3 GB and about 850 seconds for the record row at 16 bytes. A step of the prototype read `core::str` for the UTF-8 check. The codec uses its own UTF-8 check. If a harness passes only above its limit, or only above 900 seconds, stop and ask.
- Kani does not prove `frame_ok` on an enum, a `Result`, a list, a map, a `StepId` and a `Ticket`, and it proves no round trip of a composite. The theorems of section 9.1 and the corpus check these types.

## 10. Corpus

The corpus of v0.0.1 and of v0.0.2 and their expected outputs are frozen. `brk-ref` and `brk` of v0.0.3 give the same outputs on them.

### 10.1 Files

| File | Content |
|---|---|
| `accept/own.brk` + `.trace` | A `fn` with a `take` parameter, a `fn` that only reads, and a `fn` with a type parameter. A copy of a part of a read parameter. A copy that a later use causes. A copy of a read name in an owner position. A move of a part, with a later use of another part. A cell that moves state fields into `next`, a cell with one arm that ends in `stay` and one that ends in `next`, and a query cell that copies a state field. A step with a fault after an expression that moves a state field: its trace line shows the state of before. Each row of the two tables of section 3.2 is in the file. |
| `accept/generic.brk` + `.trace` | A generic `newtype`, `record`, `enum` and `fn`. Instances with a plain type argument, with an owned type argument and with an instance as a type argument. A generic `fn` that calls a generic `fn` with its own type parameter. `new`, `call`, `match` and `==` on them. `decode` items with `(value X)` at three instances, one of them fixed-size. |
| `accept/collect.brk` + `.trace` | Each form of section 3.6 on a list and on a map. Each key type. The key order: a negative and a positive `Int`, a text that is a prefix of another text, and two texts whose first different byte is above `0x7F`. The fault `full` of `push` and of `put`. A `put` that replaces an entry of a full map. `at` below 0 and at the count. A state list and a state map in cells. A state map with `retain` and `clock` lines: an entry at the age D − 1 and at the age D, an expired entry that does not count for `full`, and a `state` fact after an expiry. `decode` items with `(value X)`: an empty list, a list of fixed-size elements, a list of variable-size elements, an empty map and a map with two entries. `decode` items with `(invalid)` for each refusal of section 5.3. Each `(invalid)` frame has one cause, and it differs from the frame of a `(value X)` item of the file only in the bytes of that cause. |
| `accept/for.brk` + `.trace` | `for` on a list, on a map and on an empty collection. A `for` in a `for`. An operation in a body, with the order of its outputs. A fault in a body. An accumulator with an owned type that `push` builds. A `for` in a `fn` and in a cell. |
| `accept/depth64.brk` + `.trace` | `(enum E0 (A0))`, then `(enum Ei (Ai Ei−1) (Bi Ei−1))` for i = 1 to 63, then one `decode` item with `(value X)` at `E63`, with the tag 0 at each level. `E63` is at the type depth limit of section 2.1, and it has 64 bytes. A function that examines both variants of each level needs 2^63 steps. |
| `accept/depth512.brk` + `.trace` | A machine with one query whose cell is `(answer (not (not … true)))`, with as many `not` forms as put `true` at the text depth limit of section 2.1, and an example that sends the query. The count of the `not` forms is even. |
| `accept/limits.brk` + `.trace` | `decode` items with `(value X)` for a `Text` and for a `Principal` at the size limit. An `(invalid)` item for a `Text` one byte above the limit. An `ID` at its length limit. |
| `reject/parse-depth.brk`, `parse-nest8000.brk` + `.err` | The text of `depth512.brk` with one more `not` form; a `decode` item whose type is `Int` in 8000 levels of `Option` and whose value is `5` in 8000 levels of `some` |
| `reject/parse-text.brk`, `parse-id.brk`, `parse-int.brk` + `.err` | A `TEXT` one byte above the size limit in a `decode` value; an `ID` one character above its limit; the `INT` atom `-10000000000000000000`, which has one character above its limit |
| `reject/layout-limit-depth.brk`, `layout-limit-chain8000.brk` + `.err` | The enums of `depth64.brk` and `E64`; the `.err` file names `E64`. `(newtype N0 Int)`, then `(newtype Ni Ni−1)` for i = 1 to 7999; the `.err` file names `N64`. |
| `reject/layout-limit-size.brk`, `layout-limit-frame.brk` + `.err` | `(enum E0 (V0))`, then `(enum Ei (Vi Ei−1 Ei−1))` for i = 1 to 33: the size of `Ei` is 2^(i+1) − 1, so the `.err` file names `E31`. The same enums up to `E30`, then `(record R (a E30) (b E30))`: each type is below the limit, the fixed part of `R` has 2^32 bytes, and the `.err` file names `R`. |
| `reject/recursive-type-forward.brk` + `.err` | `(newtype A B)` before `(newtype B Int)` |
| `reject/unknown-name-forward-type.brk`, `-forward-ctor.brk`, `-forward-role.brk`, `-forward-protocol.brk`, `-forward-machine.brk` + `.err` | A `fn` with a parameter of a record that comes later; a `new` of a variant before its enum; a `by` before its role; a machine before its protocol; an example before its machine |
| `reject/unknown-name-fault.brk`, `reject-not-declared-fact.brk`, `type-mismatch-fact.brk` + `.err` | The fact `(fault nonsense)`; a `reject` fact with a reason that the command does not declare; a `reject` fact on a `send` of a query |
| `reject/duplicate-name-reject.brk`, `-group.brk`, `-role.brk`, `-in.brk` + `.err` | `(rejects No No)`; `(group G A B A)`; `(actor a Admin Admin)`; two `in` blocks for one state |
| `reject/unused-name.brk`, and one file `unused-name-KIND.brk` for each other row of the second table of section 4.4, + `.err` | A `fn` with no `call`; then one file for each kind of name with no use |
| `reject/mode-mismatch.brk`, `mode-mismatch-take.brk` + `.err` | A `fn` that passes a parameter with no keyword on to an owner; a `take` parameter that the body only reads |
| `reject/copy-mismatch.brk`, `copy-mismatch-move.brk`, `copy-mismatch-read.brk`, `copy-mismatch-for.brk` + `.err` | A copy with no `copy`; a `copy` at a move; a `copy` in a read position; a place that a `for` body takes from outside with no `copy` |
| `reject/collection-use.brk`, `collection-use-key.brk` + `.err` | A `for` on a state collection; an `at` on a state collection with a `let` name as its key |
| `reject/parse-max.brk`, `parse-retain.brk`, `parse-copy.brk` + `.err` | `(List Int 0)`; `(retain (dur 0))`; `(copy (call f x))` |
| `reject/type-mismatch-generic.brk`, `type-mismatch-bare.brk`, `type-mismatch-args.brk`, `type-mismatch-new.brk`, `type-mismatch-call.brk`, `type-mismatch-instance.brk`, `type-mismatch-key.brk`, `type-mismatch-retain.brk`, `type-mismatch-clock.brk`, `type-mismatch-map.brk`, `type-mismatch-list.brk` + `.err` | An instance with one type argument too many; a generic record with no type argument as a field type; a type argument on a record that is not generic; a `new` of a generic record with no type argument; a `call` of a generic `fn` with no type argument; in a generic `fn`, a `call` with the type argument `(Option A)`; `(Map F64 Int 4)`; `retain` on a list field; a `clock` line below the earlier `clock` line; a `map` `xexpr` with its keys in descending order; a `list` `xexpr` with one element more than its maximum |
| `reject/duplicate-name-param.brk`, `unknown-name-arg.brk`, `bad-entry-generic.brk` + `.err` | A type parameter with the name of a declared record; a type argument that the file does not declare; an entry `fn` with a type parameter |
| `gen/` | The package `borsuk-gen` (sections 10.2 to 10.4) |

- Each alternative of each grammar rule of section 2 is in an accepted file. Each code of section 4 has a reject file with the name of the code, and each addition of section 4 has a reject file, except the limit of 2^32 bytes of a file.
- Each limit of section 2.1 has an accepted file at the limit and a reject file one above it, except the frame limit (section 4.2). `check.sh` holds the names of these pairs: `depth512` and `parse-depth`, `depth64` and `layout-limit-depth`, `limits` and `parse-text`, `limits` and `parse-id`, `codec` (its item `int_min`) and `parse-int`.
- Each reject file gives exactly its own code, and it differs from an accepted text only in the form of that cause. Each new accepted file obeys section 4.4, so each of its names has a use.
- A `.trace` file holds the stdout of `brk-ref test FILE`. The coordinator selects each name and each value that this section does not give.

### 10.2 Generated programs

`borsuk-gen programs DIR` writes the 200 files `g000.brk` to `g199.brk` into `DIR`. Step 9 of `check.sh` runs `brk-ref` and `brk` on each file and compares their outputs. Step 10 lowers each file and runs the replay. The files are not in the repository.

- `borsuk-gen` is a Rust package in `corpus/gen/` with its own `[workspace]` table, its own `Cargo.lock` and the release profile of section 11. It uses `std` only, has `#![forbid(unsafe_code)]` and has no comments. It does not use `borsuk-core`.
- File i uses one SplitMix64 stream (v0.0.2 section 6.3) with the seed `0xD1FF0000` + i. `pick(n)` is u mod n with one draw.
- Each file has this text, with the parts in capitals from the rules below, in the order of the text:

```
(program
  (record Rec (a Int) (b Text))
  (enum En (E0) (E1 Int) (E2 Text))
  (record (Pair A B) (first A) (second B))
  FN FN FN FN
  (protocol GApi
    (command C0 ((n0 Int)) Int (rejects R0))
    (command C1 ((t0 Text)) Text (rejects R0))
    (command C2 ((r0 Rec)) (Pair Int Text) (rejects R0))
    (query Q0 () Int))
  (machine G (key Int) (protocol GApi) (uses) (init S0)
    (state S0)
    (state S1 (n Int) (t Text) (r Rec) (e En) (l (List Int 4)) (m (Map Int Text 3)))
    (in S0 CELL CELL CELL CELL)
    (in S1 CELL CELL CELL CELL))
  (example run (machine G) (key 1)
    (actor a)
    LINE × 16))
```

| Part | Rule |
|---|---|
| The type pool | `Int`, `Text`, `Rec`, `En`, `(Pair Int Text)`, `(List Int 4)`, in this order |
| `FN` number j (0 to 3) | `(fn fj ((p T1) (q T2)) R (uses) (block (match (and (== p p) (== q q)) (arm true (block (value E))) (arm false (block (value L))))))`. `T1`, `T2` and `R` are three picks from the type pool. `E` is `gen(R, 3)` with `p` and `q` in scope. `L` is the first literal of `R`. The `match` gives each parameter a use. |
| `gen(T, d)` | It lists its candidates in this order: the literals of `T`; each name of the type `T` in scope, in declared order; if d > 0, the forms of `T`. It selects one candidate with `pick` of their number. Each part of a form is `gen` of its type with d − 1. |
| Literals | `Int`: `0`, `1`, `-1`, `7`, `4611686018427387904`. `Text`: `""`, `"a"`, `"żó"`. `Rec`: `(new Rec 1 "a")`. `En`: `(new E0)`. `(Pair Int Text)`: `(new (Pair Int Text) 1 "a")`. `(List Int 4)`: `(list Int 4)`. |
| Forms of `Int` | `(+ Int Int)`, `(* Int Int)`, `(get Rec a)`, `(count List)`, `(for (x List) (acc Int) (block (value (+ acc x))))`, then `(call fk E E)` for each earlier `fn` with this result type |
| Forms of `Text` | `(get Rec b)`; then the calls |
| Forms of `Rec`, `En`, the pair | `(new Rec Int Text)`; `(new E1 Int)`, `(new E2 Text)`; `(new (Pair Int Text) Int Text)`; then the calls |
| Forms of the list | `(push List Int)`; then the calls |
| `CELL` of a command | The cells of a block are in protocol order. The cell is `(block (match (== x x) (arm true (block TAIL)) (arm false (block (reject R0)))))`, where `x` is the input parameter. `TAIL` is one pick of 4: 0 gives `(reject R0)`; 1 gives `(stay (outcome E))`; 2 and 3 give `(next (S1 En Et Er Ee El Em) (outcome E))`. `E` is `gen` of the result type with d = 2. `En`, `Et`, `Er` and `Ee` are `gen` of the field type with d = 2. The scope is the input parameter, and in `S1` the fields `n`, `t`, `r` and `e`. |
| `El` and `Em` | In `S0`: `(list Int 4)` and `(map Int Text 3)`. In `S1`, one pick of 2 for each: 0 gives `l` or `m`; 1 gives `(push l Int)` or `(put m K Text)`, with `gen` at d = 1 for the `Int` and the `Text`. `K` is one pick of 3: `0`, `1`, or `n`. |
| `CELL` of `Q0` in `S0` | `(block (match (and (and U0 U1) (and U2 U3)) (arm true (block (answer E))) (arm false (block (answer 0)))))`. `Uj` is `(== (call fj L1 L2) (call fj L1 L2))`, with the first literals of the two parameter types of `fj`. `E` is `gen(Int, 2)`. So each `fn` has a use. |
| `CELL` of `Q0` in `S1` | `(block (answer E))`, with `gen(Int, 2)` |
| `LINE` | One pick of 4 selects `C0`, `C1`, `C2` or `Q0`. The argument is a literal of the parameter type, selected with `pick`. The line is `(send a C x (expect))`. |

- `gen` first makes the text with no `take` and no `copy`. Then the package adds each `take` and each `copy` with its own code for sections 3.2 to 3.4.
- Each declared name of the frame has a use in the frame, and each item comes after the items that it names.
- `check` accepts each of the 200 files. A file that `check` refuses is a defect of the package or of `check`.

### 10.3 Large files

`borsuk-gen corpus DIR` writes these files into `DIR`: `accept/depth64.brk`, `accept/depth512.brk`, `accept/limits.brk`, and, each with its `.err` file, `reject/parse-depth.brk`, `reject/parse-nest8000.brk`, `reject/parse-text.brk`, `reject/layout-limit-depth.brk`, `reject/layout-limit-chain8000.brk`, `reject/layout-limit-size.brk` and `reject/layout-limit-frame.brk`. It computes each frame from section 5 with its own code. Step 9 compares each of these files with the file in `corpus/`, byte by byte.

### 10.4 Scale files

`borsuk-gen scale DIR` writes the scale files into `DIR`. Step 12 of `check.sh` runs each one in both executables under one limit of time and one limit of memory (section 11). The files are not in the repository. They are the check of the cost rule: a sample for each size that grows with the text, not a proof.

| File | Content | Command and result | v0.0.2 |
|---|---|---|---|
| `names.brk` | 660000 `role` items, one protocol with one query, one machine, and one example whose actor has each role | `check`: exit 0, no output | `check` on 20000 and on 40000 `role` items needs 0.93 s and 3.75 s in `brk`, and 3.1 s and 10.7 s in `brk-ref`. So 660000 names need more than 1000 s in each. |
| `fields.brk` | Four records, each with 65535 `Int` fields, and one machine with a query whose cell compares two `new` forms of each record | `check`: exit 0, no output | A record with 60000 fields needs 7.6 s in `brk` and 14.3 s in `brk-ref`. |
| `stmts.brk` | The entry `fn` of a deployment, with one block of 300000 `(do (ConsoleOut.print "a"))` statements | `check`: exit 0, no output | `brk` needs its thread of 1 GiB. |
| `states.brk` | One command, and one machine with 20000 states, each with one `in` block and one cell | `check`: exit 0, no output | No measurement |
| `frame.brk` | One `decode` item with `(value X)` at `(List Text 60000)`, with 60000 texts of one byte | `test`: exit 0, one `pass` line | No measurement |
| `int-long.brk` | One `decode` item whose value is an `INT` atom of 400000 digits | `check`: exit 1, the `parse` line | `brk-ref` needs 16.4 s. |

- Each scale file that `check` accepts obeys section 4.4.
- `check.sh` holds the command and the expected result of each file.
## 11. Layout and `check.sh`

```
Cargo.toml                       workspace; members add crates/borsuk-native, experiments/q2-test-cells,
                                 experiments/q3-one-signature; [profile.release] overflow-checks = true
crates/borsuk-core/src/          adds layout.rs own.rs mode.rs lower.rs
crates/borsuk-native/            Cargo.toml; src/ lib.rs arena.rs frame.rs replay.rs proofs.rs
spec/Borsuk/                     adds Layout Own Mode .lean
spec/Borsuk/Proofs/              adds Mode.lean Limits.lean
experiments/q2-test-cells/       the crate borsuk-q2; cells.brk; results/
experiments/q3-one-signature/    the crate borsuk-q3; results/
corpus/gen/                      the package borsuk-gen
docs/releases/v0.0.3/            plan.md, q2-test-cells.md, q3-one-signature.md
```

| Lean module | Content | Rust mirror |
|---|---|---|
| `Layout` | the layout table, `layout`, the row of a type, `most` and the type depth | `layout.rs` |
| `Own` | plain and owned types, places, positions, moves and copies, `erase` | `own.rs` |
| `Mode` | `mode`, the function M | `mode.rs` |
| `Read` | adds the limits of the tokens and the text depth | `read.rs` |
| `Check` | adds the name table, the scope rule, the rules of section 4.4 and the new codes | `check.rs` |
| `Eval` | adds the collection forms and `for` | `eval.rs` |
| `Codec` | reads the layout table; adds the collections and `frameOk` | `codec.rs` |
| none | the lowering | `lower.rs` |
| none | the arena, the reads and writes of a frame, the replay | the crate `borsuk-native` |

`borsuk-native` depends on `borsuk-core` and `std` only. Each new crate of the workspace has `#![forbid(unsafe_code)]` and `[lints] workspace = true`.

The only new tool setting: the release profile of the workspace, of `corpus/gen/` and of the crate of step 10 has `overflow-checks = true`. So an integer overflow in a release build stops the program with a message. It never wraps.

`check.sh` keeps each step of v0.0.2 and changes these steps. No step sets a stack size: each executable runs on the default stack of the host.

| Step | Change |
|---|---|
| 3 | The list of the theorem names is the list of section 9.1: twelve names. |
| 4 | The search also covers `corpus/gen`. |
| 5, 6, 7 | Each command of an executable runs under `timeout -k 5 60`. A command that the timeout ends fails the step. Step 5 also runs `check` on `experiments/q2-test-cells/cells.brk`: exit 0 with no output. Steps 5 and 6 also fail when a file of a limit pair of section 10.1 does not exist. |
| 8 | Each harness of `borsuk-core` in section 9.2 runs with its `MemoryMax` and its cover count. The command and the two output tests of v0.0.2 do not change. The harnesses run one after the other. This step is the exception that the host rules of the goal permit for one step: one Kani process can use up to its limit. |
| 9 | `cargo build --release --manifest-path corpus/gen/Cargo.toml`. `borsuk-gen corpus` writes the large files into a temporary directory, and each file equals the file of the same path in `corpus/`. `borsuk-gen programs` writes the 200 files into a temporary directory. For each file and each executable, under the timeout of step 5: `check` exits 0 with no output, and `test` exits 0. The `test` outputs of the two executables are equal, byte by byte. |
| 10 | The step makes a crate in a temporary directory: a `Cargo.toml` with path dependencies on `borsuk-core` and `borsuk-native`, one module from `brk lower FILE` for each accepted corpus file and each file of step 9, and a `main.rs` that `check.sh` holds. `main.rs` has `#![forbid(unsafe_code)]`. For each module, it calls `replay` and prints `native ok FILE N`, with the number of the compared events, or it prints the difference and exits 1. The step runs `cargo build --release --manifest-path` on that crate with `--target-dir target/native`, then runs the program. The step passes when the program exits 0 and prints one `native ok` line for each file. Then the step runs the harness `arena_alloc` with the command of step 8 and `-p borsuk-native`. |
| 11 | For each pair of a Lean module and its Rust mirror, of v0.0.1, of v0.0.2 and of this section: each Rust function name has a Lean definition with that name in the module, or it is on the list that `check.sh` holds. A Rust function name is the word after `fn` on a line that matches `^\s*(pub )?fn [a-z0-9_]+`. A Lean definition name is the last part, after the last `.`, of the word after `def` or `abbrev` on a line that matches `^\s*(private \|partial \|protected )*(def\|abbrev) `, in `snake_case`: a `_` goes before each capital letter that follows a small letter or a digit, and before each capital letter that a small letter follows; then each letter becomes small. The step also fails when an entry of the list names no Rust function, or names a function that has a Lean definition. |
| 12 | The step builds `borsuk-gen` as step 9 does. `borsuk-gen scale` writes the scale files of section 10.4 into a temporary directory. For each file and each executable, the step runs `systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 timeout -k 5 10 EXE CMD FILE`, and the exit code and the output are those of section 10.4. The limits have the same values for both executables. |
| 13 | The search below finds nothing. |

This is the search of step 13. `nat.rs` holds the arithmetic on limbs and the helpers of section 1.2, so it is the one file outside the search. The frozen crate of Q1 and the frozen oracle are not in the search.

```
grep -rnE '\bas (u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)\b|saturating_|wrapping_' crates experiments/q2-test-cells experiments/q3-one-signature corpus/gen --include='*.rs' --exclude-dir=target --exclude=nat.rs
```

| Stage | Steps |
|---|---|
| `setup` | 1, 2, 4, 11, 13 |
| `lean` | `setup`, 3, and 5 to 7 and 12 for `brk-ref` |
| `rust` | 1 to 4, 5 to 7 for both executables, 8, 9, 11, 12 for both executables, 13 |
| `all` | `rust` and 10 |

The list of step 11 holds these entries, as `FILE:NAME`. Each one is a Rust function for a Lean core operation, a Lean literal or a Lean coercion, or a helper of the Rust reader.

```
read.rs:lookup read.rs:r float.rs:span_digits approx.rs:lit approx.rs:nat_dyadic
approx.rs:of_int_with_prec approx.rs:of_int approx.rs:shift_left approx.rs:round_down approx.rs:round_up
approx.rs:div_at_prec approx.rs:dyadic_add approx.rs:dyadic_mul approx.rs:dyadic_neg approx.rs:dyadic_sub
approx.rs:cmp approx.rs:partial_cmp
```

Until P4 removes them, the list also holds `approx.rs:int`, `approx.rs:amount`, `math.rs:int`, `math.rs:lit`, `math.rs:to_u` and `math.rs:abs_u`. A new entry is legal only for a Rust function of one of the three kinds above. The phase reviewer examines each new entry, and the commit body names it.

P0 writes these changes. After P0, `check.sh` changes only in these cases. P4 removes the six entries from the list of step 11. Until P4, the first path of the search of step 13 is `crates/borsuk-native`, because the v0.0.2 code has such casts and calls. P4 sets that path to `crates`. In each later phase, the agent can correct the script only where it disagrees with this section. The phase reviewer examines each such correction, and the commit body names it. A change that weakens a step stays forbidden.

## 12. Phases

| Phase | Work | Stage | Gate | Done when |
|---|---|---|---|---|
| P0 Setup | Branch `build/v0.0.3`. Check the tools: Lean v4.36.0, Rust 1.98.1, `cargo kani --version` 0.68.0 and its toolchain `nightly-2026-08-21` in `rustup toolchain list`, `valgrind --version` 3.18.1 and `valgrind --tool=dhat` on a small program, `systemd-run --user --scope` with `MemoryMax`, and `timeout`. Write the versions in the commit body. Add the scopes `layout`, `own`, `mode`, `lower` and `native` to `cog.toml` and to the scope table of `docs/process/commits.md`. The release profile, the `check.sh` changes and the skeletons of the new modules, crates and packages. | `setup` | — | `check.sh setup` passes. |
| P1a Q2 code | The crate `borsuk-q2` with its four ways, its generator and its four modes, and `cells.brk`. | `setup` | G1 | The mode `check` prints `check ok`, G1 passes, and the commit of the crate is pushed. |
| P1b Q2 count | From the commit of P1a with a clean working tree: the mode `count`, the mode `hex` and the DHAT runs of section 7.5, into `results/`. The report and the decision. A row for the report in the v0.0.3 table of `docs/index.md`. For row 2 of section 7.6: the corrected code in its own commit, with a new G1, then this phase again. | `setup` | G1b | G1b passes, the report exists, and the commit body gives the decision. |
| P2 Corpus | The package `borsuk-gen` and each corpus file of section 10.1 except the `.trace` files. If the decision adds the `set` form: the two files of section 7.8. | `setup` | G2 | G2 passes. |
| P3 Lean | The Lean modules of section 11, the changes to `Ir`, `Print`, `Runtime`, `Approx`, `Math` and `Main`, the corrections of section 1.2, and the proofs. The coordinator makes the `.trace` files with `brk-ref`, again after each change in `spec/`. The commit body gives the time and the peak memory of each run of step 12. If a run needs more than half of a limit of step 12, stop and ask. | `lean` | G3 | G3 passes. |
| P4 Rust | The Rust mirror, the corrections of section 1.2, and the five harnesses of `borsuk-core`. P4 removes the six entries from the list of step 11 and sets the first path of the search of step 13 to `crates`. The commit body gives the time and the peak memory of each run of step 12 with `brk`, with the rule of P3. | `rust` | — | `check.sh rust` passes. |
| P5 Lowering | `lower.rs` with the command `lower`, the crate `borsuk-native` and its harness. The memory form of the state is the form of the decision of section 7.6. | `all` | G4 | `check.sh all` passes, and G4 passes. |
| P6a Q3 code | The crate `borsuk-q3`. | `all` | — | The mode `list 1000` ends, and the commit of the crate is pushed. |
| P6b Q3 count | From the commit of P6a with a clean working tree: the count of section 8.4, into `results/`. The report and the decision. A row for the report in `docs/index.md`. | `all` | G5 | G5 passes, the report exists, and the commit body gives the decision. |
| P7 Release | The release steps of the goal. The `spec/` row of `docs/index.md` names the theorems of section 9.1. | `all` | G6 | The tag `v0.0.3` is on the remote. |

Freeze points:

| Files | Frozen when |
|---|---|
| `experiments/q2-test-cells/` code and `cells.brk` | The commit of P1a. Row 2 of section 7.6 is the only legal change after it. Each other change is a stop. |
| `experiments/q2-test-cells/results/` and `q2-test-cells.md` | The decision is in a commit. |
| The new `.brk`, `.err` and `.out` files, and `corpus/gen/` | G2 passes. P3 makes only the `.trace` files. If `brk-ref` differs from a frozen expected value, find which one the plan supports. If the plan supports the frozen value, correct `spec/`. Else stop and ask. |
| The new `.trace` files | G3 passes. |
| `experiments/q3-one-signature/` code | The commit of P6a. A change after that commit is a stop. |
| `experiments/q3-one-signature/results/` and `q3-one-signature.md` | The decision is in a commit. |

| Gate | The Fable reviewer examines | Added class |
|---|---|---|
| G1 | Each way against sections 6.2, 6.3 and 7.4, each cell against section 7.3, and the generator against section 7.5. It looks for each write to the state and each copy of a variable-size part that does not go through `mem.rs`, and for each use of a function of `mem.rs` that hides a count. It runs the modes `check` and `hex`. With a Rust program that it writes in its own scratch directory, and that does not use the crate, it computes the input frame and the two state frames of step 0 of each cell from sections 5, 6.2 and 7.5, and compares them with the output of `hex`. It runs no count. | "hidden write" |
| G1b | It runs the mode `count` and compares its output with the file in `results/`. It examines that `results/` has two DHAT lines for each way and cell, and it computes each count C again. It derives the row of section 7.6 and the decision from the counts, and compares them with the report. For each count that is not 0, it examines the cause that the report names. | "wrong decision" |
| G2 | Each corpus file against sections 2 to 5 and 10. It runs `borsuk-gen corpus` from a copy of `corpus/gen/` in its scratch directory and compares each file with the working tree, byte by byte. With a Rust program that it writes in its scratch directory, it computes the frame of each `(value X)` item of `collect.brk`, `generic.brk`, `depth64.brk` and `limits.brk` from section 5 and compares it with the `TEXT` of the item. The same program computes `most` and the depth of the types of the four `layout-limit` files of section 10.1 from sections 2.1 and 4.2, and the reviewer compares the first type above a limit with each `.err` file. It examines the one cause of each `(invalid)` frame and of each reject file. It examines `borsuk-gen` against sections 10.2 and 10.4, and that 20 of the generated files follow the rules of sections 2 to 4. | "wrong expected value" |
| G3 | Each line of `own.trace`, `generic.trace`, `collect.trace` and `for.trace` against sections 3 and 5; that each `decode` item has its `pass` line; the statement of each theorem against section 9.1; that each call of `amount` and of `toU` gives its proof; the definitions of `erase`, `mode`, `layout`, `frameOk`, `Typed`, `full` and `size` against sections 3.4 and 5 | "wrong expected value" |
| G4 | The output of `brk lower` for `slot.brk`, `own.brk`, `collect.brk` and `cells.brk` against sections 6.2 to 6.4: each rule K1 to K9, and the memory form of the decision. The replay against section 6.5. | "breaks a lowering rule" |
| G5 | The count crate against section 8. With a Rust program that it writes in its scratch directory, and that does not use the crate, it makes each body of the size 4 or less and counts them. It compares that number, and the bodies, with the mode `list 1` limited to those sizes. It runs `brk-ref check` on each completion of 20 bodies that `list 1000` prints, and compares each answer. It derives the decision from `count.txt` and compares it with the report. | "wrong decision" |
| G6 | The full diff of the release against this plan and the design | — |

The coordinator runs the counts of P1b and P6b directly, not through a subagent.

## 13. Rules

These rules add to v0.0.1 section 9 and v0.0.2 section 11:

- The cost rule of the goal applies: `read`, `check`, `print`, `encode` and `decode` use at most O(n log n) time and O(n) memory, and a finding against it is a correction. The rule "do not do performance work" of the earlier plans does not apply to v0.0.3. The lowering, the arena, the crate `borsuk-native` and the test cells are the only other work on speed.
- For the cost rule, n counts each instance of a generic `fn` (section 2) with the text of that `fn`. `Eval` finds each declared name through the name table, so a lookup costs O(log n).
- `brk-ref` and `brk` run on the default stack. Each corpus file, each generated program and each scale file passes on it.
- The mirror rule of the goal has three checks in `check.sh`: the names (step 11), equal outputs of `brk-ref` and `brk` (steps 5 to 7 and 9), and one cost class (step 12, with the same limits for both executables). No tool compares the parameters of a Lean function with those of its Rust mirror.
- `nat.rs`, `proofs.rs` and `lower.rs` are the only modules of `borsuk-core` with no Lean module. The crate `borsuk-native`, the experiment crates and `borsuk-gen` have no Lean module. This is the exception to the mirror rule that the goal permits a plan to name. The replay of section 6.5 is the check of the lowering.
- No Rust code outside `nat.rs` clamps, wraps or cuts an integer (step 13). `min`, `max` and the two helpers of section 1.2 are mathematics with a defined result.
- The product uses Rust `std` and Lean `Init` only. Kani, `valgrind` and the oracle of v0.0.2 are tools outside the product.
- No code of v0.0.3 has `unsafe`. The arena gives positions, not pointers. Each crate has `#![forbid(unsafe_code)]`.
- `borsuk-core` and `borsuk-native` compile on the toolchain of Kani 0.68.0. If clippy 1.98.1 and that toolchain disagree, stop and ask.
- The lowering has no pass that changes the order or the number of the operations of a cell. Rules K1 to K9 are its only memory rules.
- v0.0.3 builds no store, no log record, no wire form of a message, no hash, no module, no function parameter, no text operation and no code generator other than the Rust text.
- The coordinator and each gate reviewer compute a byte string or a count with a Rust program. No other language computes an expected value.
- Measurement data is never edited. A new run makes new files.
- The memory limits of this plan are the limits of step 8 and of step 12. Each other heavy job obeys the host rules of the goal.

## 14. Sources

- The design, sections 3, 5, 8, 10, 11, 14 and 16. The milestones: row 0.0.3, the implementation stack, and "Reasons for the order".
- The v0.0.1 plan and the v0.0.2 plan. v0.0.2 section 6.3 gives the SplitMix64 stream and the kind rules of the generators.
- Cap'n Proto, `ReaderOptions::nestingLimit`, and FlatBuffers, `Verifier` `max_depth`: the default depth 64 (section 2.1). ISO/IEC 9899:2011 (C11), section 5.2.4.1: 127 levels of blocks and 63 levels of parentheses (section 2.1).
- [The Kani Rust Verifier](https://model-checking.github.io/kani/), version 0.68.0 (section 9.2).
- [Valgrind DHAT](https://valgrind.org/docs/manual/dh-manual.html), version 3.18.1 (section 7.5).
