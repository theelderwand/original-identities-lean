/-
# A new Ramanujan-style nested radical, machine-checked in Lean 4

Discovered 2026-10-12 by a telescoping-ansatz search
(see `~/workspace/your_files/ramanujan-inspired-new-formulas.md`).

**Theorem** (`nested_radical_eq_three`). With `A n = n + 5` and `B n = n + 1`,
the depth-`N` truncations of

    3 = √(5 + √(6 + 2√(7 + 3√(8 + 4√(9 + 5√(10 + ⋯))))))

converge to `3`. This is the `(m, d, c) = (2, 1, 3)` instance of the master
theorem in the note: the exact tails `t n = n + 3` satisfy
`t n ^ 2 = A n + B n * t (n+1)`, so the truncation error contracts by the
factor `(n+1)/(n+3)` at each level, and the total error is `O(1/N)`.

Ramanujan's own `3 = √(1 + 2√(1 + 3√(1 + ⋯)))` is the `(2, 2, 3)` instance;
the `d < c - 1` cases — this one included — are new.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology

noncomputable section

/-- `A n = n + 5`: the additive terms under the radicals. -/
def radA (n : ℕ) : ℝ := (n : ℝ) + 5

/-- `B n = n + 1`: the multipliers in front of the nested radicals. -/
def radB (n : ℕ) : ℝ := (n : ℝ) + 1

/-- Depth-`k` truncation of the nested radical starting at level `n`,
with tail `√(A N)` at the bottom. -/
def radS : ℕ → ℕ → ℝ
  | n, 0 => Real.sqrt (radA n)
  | n, k + 1 => Real.sqrt (radA n + radB n * radS (n + 1) k)

/-- The truncation error at level `n`, depth `k`: `δ n k = (n+3) - radS n k`. -/
def radDelta (n k : ℕ) : ℝ := (n : ℝ) + 3 - radS n k

/-- Closed-form error bound:
`radBound n N = (n + N + 3) * (n+1)(n+2) / ((n+N+1)(n+N+2))`. -/
def radBound (n N : ℕ) : ℝ :=
  ((n : ℝ) + (N : ℝ) + 3)
    * ((((n : ℝ) + 1) * ((n : ℝ) + 2))
      / ((((n : ℝ) + (N : ℝ) + 1) * ((n : ℝ) + (N : ℝ) + 2))))

/-- The telescoping identity: `(n+3)² = A n + B n * (n+4)`. -/
lemma key_identity (n : ℕ) : ((n : ℝ) + 3) ^ 2 = radA n + radB n * ((n : ℝ) + 4) := by
  simp only [radA, radB]
  ring

lemma radS_nonneg (n k : ℕ) : 0 ≤ radS n k := by
  induction k generalizing n with
  | zero => simp only [radS]; exact Real.sqrt_nonneg _
  | succ k _ => simp only [radS]; exact Real.sqrt_nonneg _

/-- Every truncation is bounded above by the exact tail `n + 3`. -/
lemma radS_le (n k : ℕ) : radS n k ≤ (n : ℝ) + 3 := by
  induction k generalizing n with
  | zero =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [radS, radA]
      have h4 : (0 : ℝ) ≤ (n : ℝ) + 4 := by linarith
      have h5 : (n : ℝ) + 5 ≤ ((n : ℝ) + 3) ^ 2 := by
        nlinarith [mul_nonneg hn h4]
      calc Real.sqrt ((n : ℝ) + 5) ≤ Real.sqrt (((n : ℝ) + 3) ^ 2) :=
            Real.sqrt_le_sqrt h5
        _ = (n : ℝ) + 3 := Real.sqrt_sq (by linarith)
  | succ k ih =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      simp only [radS]
      have h1 : radS (n + 1) k ≤ ((n + 1 : ℕ) : ℝ) + 3 := ih (n + 1)
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      have h1' : radS (n + 1) k ≤ (n : ℝ) + 4 := by linarith
      have hB : (0 : ℝ) ≤ radB n := by
        simp only [radB]; linarith
      have hmul := mul_le_mul_of_nonneg_left h1' hB
      have harg : radA n + radB n * radS (n + 1) k ≤ ((n : ℝ) + 3) ^ 2 := by
        have hkey := key_identity n
        linarith
      calc Real.sqrt (radA n + radB n * radS (n + 1) k)
            ≤ Real.sqrt (((n : ℝ) + 3) ^ 2) := Real.sqrt_le_sqrt harg
        _ = (n : ℝ) + 3 := Real.sqrt_sq (by linarith)

lemma delta_nonneg (n k : ℕ) : 0 ≤ radDelta n k :=
  sub_nonneg.mpr (radS_le n k)

lemma sq_eq (n k : ℕ) :
    (radS n (k + 1)) ^ 2 = radA n + radB n * radS (n + 1) k := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp only [radS]
  apply Real.sq_sqrt
  have hA : (0 : ℝ) ≤ radA n := by simp only [radA]; linarith
  have hB : (0 : ℝ) ≤ radB n := by simp only [radB]; linarith
  have hs := radS_nonneg (n + 1) k
  exact add_nonneg hA (mul_nonneg hB hs)

/-- One level of error contraction: `δ n (k+1) ≤ (n+1)/(n+3) * δ (n+1) k`. -/
lemma delta_step (n k : ℕ) :
    radDelta n (k + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 3) * radDelta (n + 1) k := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdiff : ((n : ℝ) + 3) ^ 2 - (radS n (k + 1)) ^ 2
      = ((n : ℝ) + 1) * radDelta (n + 1) k := by
    rw [sq_eq n k, key_identity n]
    simp only [radA, radB, radDelta]
    push_cast
    ring
  have hfac : ((n : ℝ) + 3) ^ 2 - (radS n (k + 1)) ^ 2
      = radDelta n (k + 1) * (((n : ℝ) + 3) + radS n (k + 1)) := by
    simp only [radDelta]
    ring
  have hden_pos : (0 : ℝ) < ((n : ℝ) + 3) + radS n (k + 1) := by
    have hs := radS_nonneg n (k + 1)
    linarith
  have h3_pos : (0 : ℝ) < (n : ℝ) + 3 := by linarith
  have hnum_nonneg : (0 : ℝ) ≤ ((n : ℝ) + 1) * radDelta (n + 1) k :=
    mul_nonneg (by linarith) (delta_nonneg (n + 1) k)
  have heq : radDelta n (k + 1)
      = (((n : ℝ) + 1) * radDelta (n + 1) k) / (((n : ℝ) + 3) + radS n (k + 1)) := by
    have hmul : radDelta n (k + 1) * (((n : ℝ) + 3) + radS n (k + 1))
        = ((n : ℝ) + 1) * radDelta (n + 1) k := by
      rw [← hfac, hdiff]
    exact (eq_div_iff (ne_of_gt hden_pos)).mpr hmul
  have hle : (((n : ℝ) + 1) * radDelta (n + 1) k) / (((n : ℝ) + 3) + radS n (k + 1))
      ≤ (((n : ℝ) + 1) * radDelta (n + 1) k) / ((n : ℝ) + 3) :=
    div_le_div_of_nonneg_left hnum_nonneg h3_pos (by
      have hs := radS_nonneg n (k + 1)
      linarith)
  calc radDelta n (k + 1)
      = (((n : ℝ) + 1) * radDelta (n + 1) k) / (((n : ℝ) + 3) + radS n (k + 1)) := heq
    _ ≤ (((n : ℝ) + 1) * radDelta (n + 1) k) / ((n : ℝ) + 3) := hle
    _ = ((n : ℝ) + 1) / ((n : ℝ) + 3) * radDelta (n + 1) k := by ring

/-- The closed-form error bound holds at every level and depth. -/
lemma delta_bound (n N : ℕ) : radDelta n N ≤ radBound n N := by
  induction N generalizing n with
  | zero =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hRB : radBound n 0 = (n : ℝ) + 3 := by
        have hden : ((n : ℝ) + 0 + 1) * ((n : ℝ) + 0 + 2)
            = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
          ring
        have e : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 :=
          mul_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
        simp only [radBound, Nat.cast_zero]
        rw [hden, div_self e, mul_one]
        ring
      rw [hRB]
      have h2 : radDelta n 0 = (n : ℝ) + 3 - radS n 0 := rfl
      rw [h2]
      linarith [radS_nonneg n 0]
  | succ N ih =>
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have h1 := delta_step n N
      have h2 := ih (n + 1)
      have h4 : (0 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 3) :=
        div_nonneg (by linarith) (by linarith)
      have h5 := le_trans h1 (mul_le_mul_of_nonneg_left h2 h4)
      -- the one-step bound telescopes exactly into `radBound n (N+1)`
      have hEE : ((n : ℝ) + 1) / ((n : ℝ) + 3) * radBound (n + 1) N
          = radBound n (N + 1) := by
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hcastN : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        simp only [radBound, hcast, hcastN]
        have f1 : ((n : ℝ) + 3) ≠ 0 := ne_of_gt (by linarith)
        have f2 : (((n : ℝ) + 1) + (N : ℝ) + 1) ≠ 0 := ne_of_gt (by linarith)
        have f3 : (((n : ℝ) + 1) + (N : ℝ) + 2) ≠ 0 := ne_of_gt (by linarith)
        have f4 : ((n : ℝ) + ((N : ℝ) + 1) + 1) ≠ 0 := ne_of_gt (by linarith)
        have f5 : ((n : ℝ) + ((N : ℝ) + 1) + 2) ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring
      rw [← hEE]
      exact h5

/-- The depth-`N` truncations of `√(5 + √(6 + 2√(7 + ⋯)))` converge to `3`. -/
theorem nested_radical_eq_three : Tendsto (fun N : ℕ => radS 0 N) atTop (𝓝 3) := by
  have hN0 : ∀ N : ℕ, (0 : ℝ) ≤ (N : ℝ) := fun N => Nat.cast_nonneg N
  have h6 : Tendsto (fun N : ℕ => (6 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun N : ℕ => (6 : ℝ) * ((1 : ℝ) / ((N : ℝ) + 1)))
        atTop (𝓝 ((6 : ℝ) * 0)) :=
      tendsto_const_nhds.mul h1
    have h3 : (fun N : ℕ => (6 : ℝ) * ((1 : ℝ) / ((N : ℝ) + 1)))
        = (fun N : ℕ => (6 : ℝ) / ((N : ℝ) + 1)) := by
      ext N
      rw [mul_one_div]
    rw [h3] at h2
    simpa using h2
  have hbound : ∀ N : ℕ, |radS 0 N - 3| ≤ (6 : ℝ) / ((N : ℝ) + 1) := by
    intro N
    have hd := delta_bound 0 N
    have hde : radDelta 0 N = 3 - radS 0 N := by simp only [radDelta]; push_cast; ring
    have hnn : 0 ≤ radDelta 0 N := delta_nonneg 0 N
    have hNn := hN0 N
    have e1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have e2 : (0 : ℝ) < (N : ℝ) + 2 := by linarith
    have hRB0 : radBound 0 N
        = 2 * ((N : ℝ) + 3) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
      simp only [radBound]
      push_cast
      ring
    have hdb : radDelta 0 N ≤ (6 : ℝ) / ((N : ℝ) + 1) := by
      have hX : 2 * ((N : ℝ) + 3) / (((N : ℝ) + 1) * ((N : ℝ) + 2)) * ((N : ℝ) + 1)
          = 2 * ((N : ℝ) + 3) / ((N : ℝ) + 2) := by
        have e1' : ((N : ℝ) + 1) ≠ 0 := ne_of_gt e1
        have e2' : ((N : ℝ) + 2) ≠ 0 := ne_of_gt e2
        field_simp
      have h6' : 2 * ((N : ℝ) + 3) / (((N : ℝ) + 1) * ((N : ℝ) + 2))
          ≤ (6 : ℝ) / ((N : ℝ) + 1) := by
        rw [le_div_iff₀ e1, hX, div_le_iff₀ e2]
        nlinarith [hNn]
      rw [hRB0] at hd
      linarith [hd, h6']
    rw [hde] at hnn hdb
    have habs : |radS 0 N - 3| = 3 - radS 0 N := by
      have hneg : radS 0 N - 3 = -(3 - radS 0 N) := by ring
      rw [hneg, abs_neg, abs_of_nonneg hnn]
    linarith
  have hlow : ∀ N : ℕ, (3 : ℝ) - 6 / ((N : ℝ) + 1) ≤ radS 0 N := by
    intro N
    have h := hbound N
    rw [abs_le] at h
    linarith [h.1]
  have hglow : Tendsto (fun N : ℕ => (3 : ℝ) - 6 / ((N : ℝ) + 1)) atTop (𝓝 3) := by
    have hsub : Tendsto (fun N : ℕ => (3 : ℝ) - 6 / ((N : ℝ) + 1))
        atTop (𝓝 ((3 : ℝ) - 0)) :=
      tendsto_const_nhds.sub h6
    simpa using hsub
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hglow tendsto_const_nhds hlow
    (fun N => by simpa using radS_le 0 N)

#print axioms nested_radical_eq_three
