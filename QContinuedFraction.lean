/-
# q-Continued Fraction Master (Q1 & Q2), machine-checked in Lean 4

**Theorems (finite exact-tail identities).** Let `0 < c` and `0 < q < 1`, and
write `P n = 1 + c·q^n` for the exact tails.

* **Q1.** With the depth-`N` truncation defined by `T(n, 0) = P n` and
  `T(n, k+1) = 1 + (c·q^n + c²·q^(2n+1)) / T(n+1, k)`, we have
  `T(n, N) = P n` for every `n` and every `N`. In particular at `n = 0`:
  `1 + c = 1 + (c + c²q)/(1 + (cq + c²q³)/(1 + ⋯))` with the exact tail
  substituted at any depth.

* **Q2.** With `T(n, 0) = P n` and
  `T(n, k+1) = (1 + d·q^n) + (c − d)(q^n + c·q^(2n+1)) / T(n+1, k)`, we have
  `T(n, N) = P n` for every `n` and every `N`, for arbitrary `d : ℝ`.
  At `n = 0` this is the Q2 continued fraction.

**Why the tail identity holds.** At each level the numerator factorises:
`c·q^n + c²·q^(2n+1) = c·q^n · (1 + c·q^(n+1)) = c·q^n · P(n+1)`, so the
fraction contributes exactly `c·q^n` and `1 + c·q^n = P n`. The `d`
in Q2 cancels the same way.

**What is proven here — and what is not.** These are the *finite*
exact-tail identities: substituting the exact tail at any finite depth
recovers the target value exactly. The *infinite* limit — that the
continued fraction with the standard terminator `1` converges to `1 + c`
— is **not** proven here; it would need a contraction estimate for the
Möbius maps, which is a separate argument.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter Topology

noncomputable section

namespace QContinuedFraction

/-- Depth-`N` truncation of the Q1 continued fraction at level `n`,
with the exact tail `1 + c·q^n` substituted at depth `0`. -/
def qcf1 (c q : ℝ) : ℕ → ℕ → ℝ
  | n, 0 => 1 + c * q ^ n
  | n, k + 1 => 1 + (c * q ^ n + c ^ 2 * q ^ (2 * n + 1)) / qcf1 c q (n + 1) k

/-- Depth-`N` truncation of the Q2 continued fraction at level `n`,
with the exact tail `1 + c·q^n` substituted at depth `0`. -/
def qcf2 (c d q : ℝ) : ℕ → ℕ → ℝ
  | n, 0 => 1 + c * q ^ n
  | n, k + 1 =>
      (1 + d * q ^ n) + (c - d) * (q ^ n + c * q ^ (2 * n + 1)) / qcf2 c d q (n + 1) k

/-- Exponent bookkeeping: `q^(2n+1) = (q^n)² · q`. -/
lemma qpow_two_n_add_one (q : ℝ) (n : ℕ) :
    q ^ (2 * n + 1) = (q ^ n) ^ 2 * q := by
  rw [pow_add, pow_one, show (2 * n) = n * 2 from by ring, pow_mul]

/-- The Q1 numerator factorises against the tail `1 + c·q^(n+1)`. -/
lemma qcf1_step (c q : ℝ) (hc : 0 < c) (hq : 0 < q) (n : ℕ) :
    1 + (c * q ^ n + c ^ 2 * q ^ (2 * n + 1)) / (1 + c * q ^ (n + 1))
      = 1 + c * q ^ n := by
  have hP : (1 + c * q ^ (n + 1)) ≠ 0 := by
    have hpos : (0 : ℝ) ≤ c * q ^ (n + 1) := by positivity
    linarith
  have hnum : c * q ^ n + c ^ 2 * q ^ (2 * n + 1)
      = c * q ^ n * (1 + c * q ^ (n + 1)) := by
    rw [qpow_two_n_add_one, pow_succ]
    ring
  rw [hnum, mul_div_assoc, div_self hP, mul_one]

/-- **Q1 exact-tail identity.** Every exact-tail truncation equals the tail. -/
theorem qcf1_exact (c q : ℝ) (hc : 0 < c) (hq : 0 < q) (n N : ℕ) :
    qcf1 c q n N = 1 + c * q ^ n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih =>
      simp only [qcf1]
      rw [ih (n + 1)]
      exact qcf1_step c q hc hq n

/-- The Q2 numerator factorises against the tail `1 + c·q^(n+1)`. -/
lemma qcf2_step (c q : ℝ) (hc : 0 < c) (hq : 0 < q) (d : ℝ) (n : ℕ) :
    (1 + d * q ^ n)
        + (c - d) * (q ^ n + c * q ^ (2 * n + 1)) / (1 + c * q ^ (n + 1))
      = 1 + c * q ^ n := by
  have hP : (1 + c * q ^ (n + 1)) ≠ 0 := by
    have hpos : (0 : ℝ) ≤ c * q ^ (n + 1) := by positivity
    linarith
  have hnum : (c - d) * (q ^ n + c * q ^ (2 * n + 1))
      = (c - d) * q ^ n * (1 + c * q ^ (n + 1)) := by
    rw [qpow_two_n_add_one, pow_succ]
    ring
  rw [hnum, mul_div_assoc, div_self hP, mul_one]
  ring

/-- **Q2 exact-tail identity.** Every exact-tail truncation equals the tail,
for arbitrary `d`. -/
theorem qcf2_exact (c q : ℝ) (hc : 0 < c) (hq : 0 < q) (d : ℝ) (n N : ℕ) :
    qcf2 c d q n N = 1 + c * q ^ n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih =>
      simp only [qcf2]
      rw [ih (n + 1)]
      exact qcf2_step c q hc hq d n

#print axioms qcf1_exact
#print axioms qcf2_exact

end QContinuedFraction

end
