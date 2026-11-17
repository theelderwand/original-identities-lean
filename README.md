# Original Identities — Lean 4 Proofs

Machine-checked Lean 4 proofs of five original master identities, found by
exact-tail synthesis. All proofs compile clean in Lean 4.34.0 / Mathlib
v4.34.0: zero errors, zero warnings, zero `sorry`s, and only the standard
axioms `[propext, Classical.choice, Quot.sound]`.

## The identities

Each master is a *general* identity, proved for a family of parameters — not
a single numerical curiosity. They were constructed by exact-tail synthesis:
prescribe an exact tail, choose an iteration, and solve for the generators.

| File | Master | What is proved | Scope note |
|---|---|---|---|
| `NestedRadicalMaster.lean` | Nested radicals | The nested radical `√(A(0) + B(0)√(A(1) + ⋯))` tends to `c` for all `1 ≤ d < c` | Full **m = 2** case; general `m ≥ 3` not formalized |
| `QContinuedFraction.lean` | q-continued fractions | Finite exact-tail identities (depth-N truncations) | Finite truncations; the infinite limit is not formalized |
| `MixedRootMaster.lean` | Mixed-root radicals | Full master theorem, all `c ≥ 2` | Complete |
| `QNestedRadical.lean` | q-nested radicals | Full master theorem, all `m ≥ 2`, `c > 0`, `0 < q < 1` | Complete |
| `CyclicRootMaster.lean` | Cyclic-root radicals | Period-3 cycle of 2nd/3rd/4th roots | Complete |

`RamanujanNestedRadical.lean` is a single (2, 1, 3) instance, kept for
reference. `LEAN_PROOFS_STATUS.md` records the verification status of every
file.

## Verifying

Requires [elan](https://github.com/leanprover/elan) (Lean toolchain manager).
Mathlib v4.34.0 is fetched automatically on first build.

```sh
lake build
lake env lean --json NestedRadicalMaster.lean   # exit 0, no errors, no sorries
```

Every file's `#print axioms` shows only the standard axioms — no `sorryAx`
anywhere.

## Background

These identities are part of the *Original Identities* project: new formulas,
constructed and proved here, not published work. The companion repositories
are
[ramanujan-prime-degree-theta-theory](https://github.com/theelderwand/ramanujan-prime-degree-theta-theory)
(degree-11, 13, and 17 modular equations in Ramanujan's prime-degree theta
function theory) and
[modular-forms](https://github.com/theelderwand/modular-forms)
(554 proven eta-quotient identities).
