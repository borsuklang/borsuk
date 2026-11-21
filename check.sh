#!/usr/bin/env bash
set -uo pipefail

cd "$(dirname "$0")" || exit 2

ref=spec/.lake/build/bin/brk-ref
rust=target/release/brk
codes=(parse unknown-name duplicate-name recursion recursive-type layout-limit wrong-ending
  type-mismatch match-arms effect-position effect-not-declared env-position init-has-fields
  duplicate-cell missing-cell reject-not-declared bad-entry)
theorems=(Borsuk.coverage Borsuk.decode_encode Borsuk.encode_decode Borsuk.encode_typed
  Borsuk.encode_total)
harnesses=(codec_round_trip_scalars codec_canonical)
covers=(7 7)

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT

fail() {
  echo "check.sh: FAIL: $*" >&2
  exit 1
}

pass() {
  echo "check.sh: pass: $*"
}

expect() {
  local exe=$1 cmd=$2 file=$3 want_rc=$4 want_out=$5 rc=0
  "$exe" "$cmd" "$file" >"$tmp/out" 2>"$tmp/err" || rc=$?
  if [ "$rc" -ne "$want_rc" ]; then
    head -20 "$tmp/out" "$tmp/err" >&2
    fail "$exe $cmd $file: exit $rc, expected $want_rc"
  fi
  if [ -s "$tmp/err" ]; then
    head -20 "$tmp/err" >&2
    fail "$exe $cmd $file: output on stderr"
  fi
  if ! cmp -s "$tmp/out" "$want_out"; then
    diff "$want_out" "$tmp/out" | head -40 >&2
    fail "$exe $cmd $file: stdout differs from $want_out"
  fi
}

step1() {
  cargo fmt --check || fail "step 1: cargo fmt --check"
  cargo clippy --workspace --all-targets -- -D warnings || fail "step 1: cargo clippy"
  cargo build --release || fail "step 1: cargo build --release"
  pass "step 1: fmt, clippy, build"
}

step2() {
  (cd spec && lake build --wfail) || fail "step 2: lake build --wfail"
  pass "step 2: lake build --wfail"
}

step3() {
  local out line name list axiom n
  local -a lines axioms
  out=$(cd spec && lake env lean Borsuk/Proofs/Axioms.lean 2>&1) || {
    echo "$out" >&2
    fail "step 3: lake env lean Borsuk/Proofs/Axioms.lean"
  }
  echo "$out"
  mapfile -t lines <<<"$out"
  if [ "${#lines[@]}" -ne "${#theorems[@]}" ]; then
    fail "step 3: the output does not have one axiom line for each theorem"
  fi
  for name in "${theorems[@]}"; do
    n=0
    for line in "${lines[@]}"; do
      case "$line" in
        "'$name' does not depend on any axioms")
          n=$((n + 1))
          ;;
        "'$name' depends on axioms: ["*"]")
          n=$((n + 1))
          list=${line#*\[}
          list=${list%\]}
          IFS=',' read -ra axioms <<<"$list"
          for axiom in "${axioms[@]}"; do
            axiom=${axiom# }
            case "$axiom" in
              propext | Classical.choice | Quot.sound) ;;
              *) fail "step 3: $name depends on the axiom $axiom" ;;
            esac
          done
          ;;
      esac
    done
    [ "$n" -eq 1 ] || fail "step 3: $name has $n axiom lines"
  done
  pass "step 3: axioms of ${#theorems[@]} theorems"
}

step4() {
  local rc=0
  grep -rnE '^[[:space:]]*(//|/\*|--|/-)|[[:space:]](//|--)[[:space:]]' \
    crates spec experiments corpus/oracle --exclude-dir=target \
    --include='*.rs' --include='*.lean' || rc=$?
  case "$rc" in
    1) ;;
    0) fail "step 4: the comment search found comments" ;;
    *) fail "step 4: the comment search failed" ;;
  esac
  pass "step 4: no comments"
}

step5() {
  local exe=$1 f base n=0
  for base in corpus/accept/hello corpus/accept/slot corpus/accept/tally; do
    [ -e "$base.brk" ] || fail "step 5: $base.brk does not exist"
  done
  [ -e corpus/accept/hello.out ] || fail "step 5: corpus/accept/hello.out does not exist"
  [ ! -e corpus/accept/hello.trace ] || fail "step 5: hello.brk has a trace file"
  for f in corpus/accept/*.brk; do
    n=$((n + 1))
    base=${f%.brk}
    expect "$exe" check "$f" 0 /dev/null
    if [ -e "$base.trace" ]; then
      expect "$exe" test "$f" 0 "$base.trace"
    else
      [ "$base" = corpus/accept/hello ] || fail "step 5: $base.trace does not exist"
      expect "$exe" test "$f" 0 /dev/null
    fi
  done
  expect "$exe" run corpus/accept/hello.brk 0 corpus/accept/hello.out
  printf 'error[bad-entry]: no deployment\n' >"$tmp/no-deployment"
  expect "$exe" run corpus/accept/slot.brk 1 "$tmp/no-deployment"
  pass "step 5: $n accepted files with $exe"
}

step6() {
  local exe=$1 code f n=0
  for code in "${codes[@]}"; do
    [ -e "corpus/reject/$code.brk" ] || fail "step 6: corpus/reject/$code.brk does not exist"
    [ -e "corpus/reject/$code.err" ] || fail "step 6: corpus/reject/$code.err does not exist"
  done
  for f in corpus/reject/*.brk; do
    n=$((n + 1))
    expect "$exe" check "$f" 1 "${f%.brk}.err"
  done
  pass "step 6: $n reject files with $exe"
}

step7() {
  local exe=$1 f n=0
  [ -e corpus/fail/wrong-fact.brk ] || fail "step 7: corpus/fail/wrong-fact.brk does not exist"
  for f in corpus/fail/*.brk; do
    n=$((n + 1))
    expect "$exe" test "$f" 1 "${f%.brk}.out"
  done
  pass "step 7: $n fail files with $exe"
}

step8() {
  local i name want out rc
  for i in "${!harnesses[@]}"; do
    name=${harnesses[$i]}
    want=${covers[$i]}
    rc=0
    out=$(systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 \
      timeout -k 10 900 nice -n 19 ionice -c3 cargo kani -p borsuk-core --harness "$name" 2>&1) ||
      rc=$?
    if [ "$rc" -ne 0 ]; then
      printf '%s\n' "$out" | tail -40 >&2
      fail "step 8: cargo kani --harness $name: exit $rc"
    fi
    if [ "$(printf '%s\n' "$out" | grep -cxF 'VERIFICATION:- SUCCESSFUL')" -ne 1 ]; then
      printf '%s\n' "$out" | tail -40 >&2
      fail "step 8: $name: the line VERIFICATION:- SUCCESSFUL is not there exactly one time"
    fi
    if ! grep -qE "\*\* $want of $want cover properties satisfied\$" <<<"$out"; then
      printf '%s\n' "$out" | tail -40 >&2
      fail "step 8: $name: no line with $want of $want cover properties satisfied"
    fi
    pass "step 8: kani harness $name"
  done
}

stage=${1:-}
case "$stage" in
  setup)
    step1
    step2
    step4
    ;;
  lean)
    step1
    step2
    step3
    step4
    step5 "$ref"
    step6 "$ref"
    step7 "$ref"
    ;;
  all)
    step1
    step2
    step3
    step4
    for exe in "$ref" "$rust"; do
      step5 "$exe"
      step6 "$exe"
      step7 "$exe"
    done
    step8
    ;;
  *)
    echo "usage: check.sh setup|lean|all" >&2
    exit 2
    ;;
esac
pass "stage $stage"
