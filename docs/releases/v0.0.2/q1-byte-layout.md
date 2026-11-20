# Q1 byte layout: report

This report gives the result of the Q1 experiment of the v0.0.2 plan (section 6) and the decision. The raw times are in `experiments/q1-byte-layout/results/`, one CSV file for each run.

## Host

| Item | Value |
|---|---|
| CPU | 12th Gen Intel Core i9-12900H, 20 threads |
| Kernel | Linux 6.2.0-36-generic x86_64 |
| `rustc` | 1.98.1 (48a229cea 2026-09-01) |
| Commit of the experiment code | `3cdb3c9` |
| Build | `cargo build --release`, no special flags |
| Run command | `taskset -c 1 target/release/borsuk-q1 run run NN experiments/q1-byte-layout/results`, no `nice` |

## Definitions

v0.0.2 has no store, no network and no compiled steps. These definitions apply (plan section 6.2).

| Term of the design | Definition in v0.0.2 |
|---|---|
| Step path | One step of plan section 6.4, in Rust code that is written by hand for each type and arm in the form that a compiler would make |
| State in memory | Arms F and P: the state frame, which a step changes in place. Arm S: a native Rust struct, decoded one time when the instance loads. This is the split layout of design section 14, fallback step 3. |
| Checked reads | Arms F and P read frames through checked slices, because the experiment crate forbids `unsafe` code. A compiler can leave out these checks after admission. This limit can make arms F and P slower than a compiled step. |
| Wire bytes per message | The mean frame size of the input values of a group |
| Log bytes per step | The mean size of the log record of plan section 6.4: the input, the change to the state, the outputs and the decision (the reply of the step) |
| Batch compression | None, because no store exists. The decision holds for a store that does not compress batches. If a later plan adds batch compression to the store, Q1 runs again before the first stored byte. |

## Bytes

The byte counts are exact, so the interval of a byte ratio is the ratio itself. A byte ratio passes when it is at most 1.3.

Mean bytes for each group and arm:

| Group | Wire F | Wire P | Wire S | Log F | Log P | Log S |
|---|---|---|---|---|---|---|
| booking | 98.13 | 98.13 | 79.55 | 273.27 | 179.36 | 154.89 |
| wide | 196.00 | 196.00 | 121.04 | 225.00 | 143.26 | 132.04 |
| varied | 364.35 | 364.35 | 312.64 | 393.35 | 340.32 | 324.23 |
| personal | 137.17 | 137.17 | 114.55 | 483.00 | 457.07 | 452.20 |
| booking, HoldIn | 80.13 | 80.13 | 73.10 | 297.27 | 189.08 | 164.84 |
| booking, ConfirmIn | 116.13 | 116.13 | 86.00 | 249.27 | 169.64 | 144.94 |

Byte ratios against arm S:

| Ratio | Wire F | Wire P | Log F | Log P |
|---|---|---|---|---|
| booking | 1.2336 | 1.2336 | 1.7643 | 1.1580 |
| wide | 1.6194 | 1.6194 | 1.7040 | 1.0849 |
| varied | 1.1654 | 1.1654 | 1.2132 | 1.0496 |
| personal | 1.1975 | 1.1975 | 1.0681 | 1.0108 |
| booking, HoldIn | 1.0962 | 1.0962 | 1.8034 | 1.1470 |
| booking, ConfirmIn | 1.3504 | 1.3504 | 1.7198 | 1.1704 |
| Geometric mean (the rule) | 1.2922 | 1.2922 | 1.4049 | 1.0745 |
| Arithmetic mean | 1.3040 | 1.3040 | 1.4374 | 1.0758 |
| Ratio of totals | 1.2636 | 1.2636 | 1.3527 | 1.0666 |
| Worst group | wide | wide | booking | booking |

## Speed

The 12 runs are the result. Each run had a 1-minute load average below 1.0 before it, so each run is quiet. The time of a group and arm is the exponential of the mean over the runs of the log of `nanos / steps`.

Time per step in nanoseconds:

| Group | F | P | S |
|---|---|---|---|
| booking | 45.79 | 332.87 | 98.45 |
| wide | 21.08 | 269.06 | 193.70 |
| varied | 155.76 | 497.52 | 256.58 |
| personal | 80.75 | 415.91 | 181.11 |

Speed ratios against arm S, with the 95 % t interval over 12 runs (11 degrees of freedom, quantile 2.201). A speed ratio passes when the upper end of its interval is at most 1.02, and fails when the lower end is above 1.02.

| Ratio | F | P |
|---|---|---|
| booking | 0.4651 [0.4603, 0.4700] | 3.3812 [3.3410, 3.4218] |
| wide | 0.1088 [0.0987, 0.1200] | 1.3890 [1.3808, 1.3973] |
| varied | 0.6071 [0.6019, 0.6123] | 1.9391 [1.9239, 1.9543] |
| personal | 0.4459 [0.4424, 0.4493] | 2.2964 [2.2738, 2.3192] |
| Geometric mean (the rule) | 0.3421 [0.3334, 0.3510] | 2.1385 [2.1212, 2.1559] |
| Worst group | varied | booking |

Each run, with the 1-minute load average that the coordinator read before it, and the arithmetic mean and the ratio of totals (no interval):

| Run | Order | Load | F arithmetic mean | F ratio of totals | P arithmetic mean | P ratio of totals |
|---|---|---|---|---|---|---|
| 01 | F P S | 0.87 | 0.4082 | 0.4238 | 2.2817 | 2.2616 |
| 02 | P S F | 0.75 | 0.4116 | 0.4254 | 2.2265 | 2.2075 |
| 03 | S F P | 0.65 | 0.4032 | 0.4185 | 2.2385 | 2.2201 |
| 04 | F P S | 0.97 | 0.3983 | 0.4132 | 2.2193 | 2.1995 |
| 05 | P S F | 0.99 | 0.4090 | 0.4234 | 2.2208 | 2.2017 |
| 06 | S F P | 0.92 | 0.4058 | 0.4210 | 2.2912 | 2.2708 |
| 07 | F P S | 0.62 | 0.4025 | 0.4174 | 2.2422 | 2.2231 |
| 08 | P S F | 0.95 | 0.4224 | 0.4375 | 2.2455 | 2.2234 |
| 09 | S F P | 0.69 | 0.4068 | 0.4208 | 2.3065 | 2.2817 |
| 10 | F P S | 0.64 | 0.3989 | 0.4138 | 2.2369 | 2.2180 |
| 11 | P S F | 0.60 | 0.4104 | 0.4249 | 2.2204 | 2.2021 |
| 12 | S F P | 0.76 | 0.4076 | 0.4226 | 2.2904 | 2.2694 |

## Result of each rule

| Rule | Arm F | Arm P |
|---|---|---|
| Speed (upper end at most 1.02) | Pass (0.3421 [0.3334, 0.3510]) | Fail (2.1385 [2.1212, 2.1559]) |
| Wire bytes (at most 1.3) | Pass (1.2922) | Pass (1.2922) |
| Log bytes (at most 1.3) | Fail (1.4049) | Pass (1.0745) |

## Decision

The rules of plan section 6.6 apply in order:

1. Arm F fails the log rule, so step 1 does not apply.
2. Arm F does not pass both the wire rule and the log rule, so step 2 does not apply.
3. Arm P fails the speed rule, so step 3 does not apply.
4. Arm P passes the wire rule and the log rule, so step 4 applies: the coordinator stopped and asked the owner, with these numbers and the limit of the checked reads.

The owner chose the offset form. So the codec of Borsuk v0.0.2 is arm F (plan section 5.2). v0.0.2 builds no packing outside the experiment. A packed log form belongs to the store of milestone 0.0.7.

The time of arm P is mostly the time of the packing of the log record. The experiment code is frozen at commit `3cdb3c9`.
