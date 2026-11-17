# Lean 4 Proofs — "Original Identities" (5 Masters)

All proofs machine-checked in Lean 4.34.0 / Mathlib v4.34.0, project `~/workspace/basel/`.
Verified with `lake env lean --json <file>` (exit 0, zero errors, zero warnings, zero
sorries) and `lake build` (passes). Every `#print axioms` shows only the standard
axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx` anywhere.

## 1. Nested-Radical Master — `NestedRadicalMaster.lean`

**Theorem** `nested_radical_master (hd : 1 ≤ d) (h : d < c)`:
the nested radical `√(A(0) + B(0)√(A(1) + ⋯))` tends to `c`.

**What was proven:** the full **m = 2** case for all `1 ≤ d < c`, via exact tails
`t n = n + c` and a two-regime contraction (`c ≥ d+2`: telescoping product,
error O(1/N); `c = d+1`: boundary regime, error O(1/√M)).
**Not proven:** general `m ≥ 3` (same telescoping structure with m-th roots;
not formalized). Stated in the file header.
**Status:** ✅ clean. Axioms: `[propext, Classical.choice, Quot.sound]`.

## 2. q-Nested Radicals Master — `QNestedRadical.lean`

**Theorem** `q_nested_radical_master`: for all `m ≥ 2`, `c > 0`, `0 < q < 1`,
`0 < B < 1/(1+c)`, the truncations of the m-th-root nested radical tend to `1 + c`.

**What was proven:** the **full master theorem** — all parameters, infinite limit.
Proof via exact tails `t n = 1 + c·q^n`, geometric-sum factorisation
`x^m − y^m = (x−y)·S` with `S ≥ 1`, giving `δ(0,N) ≤ B^N·(1+c) → 0`.
**Status:** ✅ clean. Axioms: `[propext, Classical.choice, Quot.sound]`.

## 3. Mixed-Root Master — `MixedRootMaster.lean`

**Theorem** `mixed_root_master (hc : 2 ≤ c)`: the depth-`N` truncations of the
alternating sqrt/cbrt nested radical tend to `c`.

**What was proven:** the **full master theorem** for all `c ≥ 2`, infinite limit.
Proof via exact tails `t n = n + c`, geometric-sum contraction
`δ(n,k+1) ≤ δ(n+1,k)/(n+c)`, iterated to `δ(0,N) ≤ (N+c)/∏_{j<N}(j+c) ≤
(N+c)/c^N → 0` (polynomial × geometric).
**Caveat:** `c ≥ 2` is required — for `c = 1`, `A 0 = 1² − 2 = −1 < 0`, so the
level-0 square root is not real. Stated in the file header.
**Status:** ✅ clean. Axioms: `[propext, Classical.choice, Quot.sound]`.

## 4. q-Continued Fraction Master (Q1 & Q2) — `QContinuedFraction.lean`

**Theorems** `qcf1_exact` and `qcf2_exact`: for `0 < c`, `0 < q < 1`
(and arbitrary `d : ℝ` for Q2), every depth-`N` truncation with the exact tail
`P n = 1 + c·q^n` substituted equals `P n` exactly — i.e. the Q1 and Q2
continued-fraction constructions are exact at every finite depth.

**What was proven:** the **finite exact-tail identities** for both Q1 and Q2.
The numerator factorises against the tail at every level
(`c·q^n + c²·q^(2n+1) = c·q^n·P(n+1)`), so each level contributes exactly `c·q^n`.
**Not proven:** the *infinite* limit — that the continued fraction with the
standard terminator `1` converges to `1 + c`. That needs a contraction estimate
for the Möbius maps and is a separate argument. Stated in the file header.
**Status:** ✅ clean. Axioms: `[propext, Classical.choice, Quot.sound]`.

## 5. Cyclic-Root Master — `CyclicRootMaster.lean`

**Theorem** `cyclic_root_master (hc : 2 ≤ c)`: the depth-`N` truncations of the
nested radical with root degrees cycling (2, 3, 4) with period 3 tend to `c`.

**What was proven:** the **full master theorem** for all `c ≥ 2`, infinite limit.
The period-3 analogue of the Mixed-Root Master: every lemma in that proof uses
only `deg n ≥ 2`, so the same geometric-sum contraction
`δ(n,k+1) ≤ δ(n+1,k) / (n+c)` carries over unchanged, giving
`δ(0,N) ≤ (N+c) / c^N → 0`. Numerical check (mpmath, 50 digits, tail N=300)
had already verified the statement for c = 2, 3, 5 with error 0.0.
**Caveat:** same as Master 03 — `c ≥ 2` is required; for `c = 1`,
`A 0 = 1² − 2 = −1 < 0`. Stated in the file header.
**Status:** ✅ clean, verified 2026-11-09. Axioms: `[propext, Classical.choice, Quot.sound]`.

## Verification commands

```sh
cd ~/workspace/basel
~/.elan/bin/lake env lean --json NestedRadicalMaster.lean   # exit 0, 0 errors
~/.elan/bin/lake env lean --json QNestedRadical.lean        # exit 0, 0 errors
~/.elan/bin/lake env lean --json MixedRootMaster.lean       # exit 0, 0 errors
~/.elan/bin/lake env lean --json QContinuedFraction.lean    # exit 0, 0 errors
~/.elan/bin/lake env lean --json CyclicRootMaster.lean      # exit 0, 0 errors (2026-11-09)
~/.elan/bin/lake build                                      # Build completed successfully
```

## Files

- `~/workspace/basel/RamanujanNestedRadical.lean` — pre-existing (m=2,d=1,c=3)
  instance proof; untouched.
- `~/workspace/basel/NestedRadicalMaster.lean` — Master 1 (m=2 case).
- `~/workspace/basel/QNestedRadical.lean` — Master 4 (full).
- `~/workspace/basel/MixedRootMaster.lean` — Master 3 (full, c ≥ 2).
- `~/workspace/basel/QContinuedFraction.lean` — Master 2 (finite exact-tail, Q1 & Q2).
- `~/workspace/basel/CyclicRootMaster.lean` — Master 5 (full, c ≥ 2, period-3 cycle (2,3,4)).
- `~/workspace/basel/LEAN_PROOFS_STATUS.md` — this file.
