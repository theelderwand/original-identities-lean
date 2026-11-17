/-
# Nested-Radical Master Theorem (m = 2), machine-checked in Lean 4

**Theorem.** For natural numbers `d, c` with `1 ≤ d < c`, define

    A n = (n + c)² - (n + d)·(n + c + 1),   B n = n + d.

Then the depth-`N` truncations of the nested radical

    c = √(A 0 + B 0 · √(A 1 + B 1 · √(A 2 + ⋯)))

converge to `c` as `N → ∞`.

**What is proven here.** The full `m = 2` case of the Nested-Radical Master
Theorem, for *all* `1 ≤ d < c`. Two regimes:

* `c ≥ d + 2`: the one-step error contraction factor `(n+d)/(n+c)` telescopes
  to a product `≤ d(d+1)/((N+d)(N+d+1))`, giving error `O(1/N)`.
* `c = d + 1` (the boundary case, including the classical
  `3 = √(1 + 2√(1 + 3√(1 + ⋯)))` at `(d, c) = (2, 3)`): here `A n = 1` for
  all `n`, and the contraction factor is `1 - 1/√(n+d+1)`; the error is
  bounded by `(N+d)·exp(-(N-1)/√(N+d))`, which tends to `0` since
  `exp t ≥ (t/3)³`.

The key algebraic fact throughout is the exact-tail identity
`(n + c)² = A n + B n · (n + c + 1)`, i.e. the tails `t n = n + c` are exact.

**What is NOT proven here.** The master theorem for general `m ≥ 3` (the
same telescoping structure applies, with `m`-th roots in place of square
roots; the contraction analysis is analogous but not formalized here).
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology

noncomputable section

namespace NestedRadicalMaster

variable {d c : ℕ}

/-- `A n = (n+c)² - (n+d)(n+c+1) = (c-d-1)(n+c) + (c-d)`. -/
def radA (d c : ℕ) (n : ℕ) : ℝ :=
  ((n : ℝ) + c) ^ 2 - ((n : ℝ) + d) * ((n : ℝ) + c + 1)

/-- `B n = n + d`. -/
def radB (d : ℕ) (n : ℕ) : ℝ := (n : ℝ) + d

/-- The exact tail at level `n`: `t n = n + c`. -/
def tail (c : ℕ) (n : ℕ) : ℝ := (n : ℝ) + c

/-- Depth-`k` truncation of the nested radical starting at level `n`,
with tail `√(A N)` at the bottom. -/
def radS (d c : ℕ) : ℕ → ℕ → ℝ
  | n, 0 => Real.sqrt (radA d c n)
  | n, k + 1 => Real.sqrt (radA d c n + radB d n * radS d c (n + 1) k)

/-- The truncation error at level `n`, depth `k`. -/
def radDelta (d c : ℕ) (n k : ℕ) : ℝ := tail c n - radS d c n k

/-- Closed form: `A n = (c-d-1)(n+c) + (c-d)`. -/
lemma radA_eq (n : ℕ) :
    radA d c n = ((c : ℝ) - d - 1) * ((n : ℝ) + c) + ((c : ℝ) - d) := by
  simp only [radA]
  ring

/-- `A n ≥ 1` whenever `d < c`. -/
lemma radA_pos (h : d < c) (n : ℕ) : 1 ≤ radA d c n := by
  rw [radA_eq]
  have hdc : (1 : ℝ) ≤ (c : ℝ) - d := by
    have h1 : (d : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast h
    linarith
  have h1 : (0 : ℝ) ≤ (c : ℝ) - d - 1 := by linarith
  have h2 : (0 : ℝ) ≤ (n : ℝ) + c := by positivity
  have h3 : (0 : ℝ) ≤ ((c : ℝ) - d - 1) * ((n : ℝ) + c) := mul_nonneg h1 h2
  linarith

lemma radA_nonneg (h : d < c) (n : ℕ) : 0 ≤ radA d c n :=
  le_trans zero_le_one (radA_pos h n)

lemma radB_nonneg (n : ℕ) : 0 ≤ radB d n := by
  simp only [radB]
  positivity

/-- The telescoping identity: `(n+c)² = A n + B n · (n+c+1)`. -/
lemma key_identity (n : ℕ) :
    (tail c n) ^ 2 = radA d c n + radB d n * tail c (n + 1) := by
  simp only [radA, radB, tail]
  push_cast
  ring

lemma radS_nonneg (n k : ℕ) : 0 ≤ radS d c n k := by
  induction k generalizing n with
  | zero => simp only [radS]; exact Real.sqrt_nonneg _
  | succ k _ => simp only [radS]; exact Real.sqrt_nonneg _

/-- Every truncation is bounded above by the exact tail. -/
lemma radS_le (n k : ℕ) : radS d c n k ≤ tail c n := by
  induction k generalizing n with
  | zero =>
      have h5 : radA d c n ≤ (tail c n) ^ 2 := by
        have hkey := key_identity (d := d) (c := c) n
        have hB : 0 ≤ radB d n * tail c (n + 1) := by
          apply mul_nonneg (radB_nonneg n)
          simp only [tail]; positivity
        linarith
      calc Real.sqrt (radA d c n) ≤ Real.sqrt ((tail c n) ^ 2) :=
            Real.sqrt_le_sqrt h5
        _ = tail c n := Real.sqrt_sq (by simp only [tail]; positivity)
  | succ k ih =>
      simp only [radS]
      have h1 : radS d c (n + 1) k ≤ tail c (n + 1) := ih (n + 1)
      have hmul : radB d n * radS d c (n + 1) k ≤ radB d n * tail c (n + 1) :=
        mul_le_mul_of_nonneg_left h1 (radB_nonneg (d := d) n)
      have harg : radA d c n + radB d n * radS d c (n + 1) k ≤ (tail c n) ^ 2 := by
        have hkey := key_identity (d := d) (c := c) n
        have hc : tail c (n + 1) = tail c n + 1 := by
          simp only [tail]; push_cast; ring
        linarith
      calc Real.sqrt (radA d c n + radB d n * radS d c (n + 1) k)
            ≤ Real.sqrt ((tail c n) ^ 2) := Real.sqrt_le_sqrt harg
        _ = tail c n := Real.sqrt_sq (by simp only [tail]; positivity)

lemma delta_nonneg (n k : ℕ) : 0 ≤ radDelta d c n k :=
  sub_nonneg.mpr (radS_le n k)

lemma sq_eq (h : d < c) (n k : ℕ) :
    (radS d c n (k + 1)) ^ 2 = radA d c n + radB d n * radS d c (n + 1) k := by
  simp only [radS]
  apply Real.sq_sqrt
  exact add_nonneg (radA_nonneg h n)
    (mul_nonneg (radB_nonneg n) (radS_nonneg (n + 1) k))

/-- Exact one-step error identity:
`δ(n, k+1) = B n · δ(n+1, k) / (t n + S(n, k+1))`. -/
lemma delta_eq (h : d < c) (n k : ℕ) :
    radDelta d c n (k + 1)
      = (radB d n * radDelta d c (n + 1) k) / (tail c n + radS d c n (k + 1)) := by
  have hdiff : (tail c n) ^ 2 - (radS d c n (k + 1)) ^ 2
      = radB d n * radDelta d c (n + 1) k := by
    rw [sq_eq h n k, key_identity (d := d) (c := c) n]
    simp only [radB, radDelta, tail]
    push_cast
    ring
  have hfac : (tail c n) ^ 2 - (radS d c n (k + 1)) ^ 2
      = radDelta d c n (k + 1) * (tail c n + radS d c n (k + 1)) := by
    simp only [radDelta]
    ring
  have hden_pos : (0 : ℝ) < tail c n + radS d c n (k + 1) := by
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
      have h0 : (0 : ℕ) < c := lt_of_le_of_lt (Nat.zero_le d) h
      exact_mod_cast h0
    have ht : (0 : ℝ) < tail c n := by
      simp only [tail]
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hs := radS_nonneg (d := d) (c := c) n (k + 1)
    linarith
  have hmul : radDelta d c n (k + 1) * (tail c n + radS d c n (k + 1))
      = radB d n * radDelta d c (n + 1) k := by
    rw [← hfac, hdiff]
  exact (eq_div_iff (ne_of_gt hden_pos)).mpr hmul

/-- One level of error contraction (crude denominator bound). -/
lemma delta_step (h : d < c) (n k : ℕ) :
    radDelta d c n (k + 1)
      ≤ ((n : ℝ) + d) / ((n : ℝ) + c) * radDelta d c (n + 1) k := by
  rw [delta_eq h n k]
  have ht_pos : (0 : ℝ) < tail c n := by
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
      have h0 : (0 : ℕ) < c := lt_of_le_of_lt (Nat.zero_le d) h
      exact_mod_cast h0
    simp only [tail]
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hnum_nonneg : (0 : ℝ) ≤ radB d n * radDelta d c (n + 1) k :=
    mul_nonneg (radB_nonneg n) (delta_nonneg (n + 1) k)
  have hle : (radB d n * radDelta d c (n + 1) k) / (tail c n + radS d c n (k + 1))
      ≤ (radB d n * radDelta d c (n + 1) k) / tail c n :=
    div_le_div_of_nonneg_left hnum_nonneg ht_pos (by
      have hs := radS_nonneg (d := d) (c := c) n (k + 1)
      simp only [tail]; linarith)
  calc (radB d n * radDelta d c (n + 1) k) / (tail c n + radS d c n (k + 1))
      ≤ (radB d n * radDelta d c (n + 1) k) / tail c n := hle
    _ = ((n : ℝ) + d) / ((n : ℝ) + c) * radDelta d c (n + 1) k := by
        simp only [radB, tail]; ring

/-- Iterating the contraction. -/
lemma delta_iter (h : d < c) (n k : ℕ) :
    radDelta d c n k
      ≤ (∏ j ∈ Finset.range k, (((n + j : ℕ) : ℝ) + d) / (((n + j : ℕ) : ℝ) + c))
        * radDelta d c (n + k) 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      have h1 := delta_step h n k
      have h2 := ih (n + 1)
      have hfac : (0 : ℝ) ≤ ((n : ℝ) + d) / ((n : ℝ) + c) := by
        apply div_nonneg <;> positivity
      have hprod : (∏ j ∈ Finset.range (k + 1),
            (((n + j : ℕ) : ℝ) + d) / (((n + j : ℕ) : ℝ) + c))
          = ((n : ℝ) + d) / ((n : ℝ) + c)
            * ∏ j ∈ Finset.range k,
              ((((n + 1) + j : ℕ) : ℝ) + d) / ((((n + 1) + j : ℕ) : ℝ) + c) := by
        calc (∏ j ∈ Finset.range (k + 1),
              (((n + j : ℕ) : ℝ) + d) / (((n + j : ℕ) : ℝ) + c))
            = (∏ j ∈ Finset.range k,
                  (((n + (j + 1) : ℕ) : ℝ) + d) / (((n + (j + 1) : ℕ) : ℝ) + c))
                * ((((n + 0 : ℕ) : ℝ) + d) / (((n + 0 : ℕ) : ℝ) + c)) :=
              Finset.prod_range_succ' _ _
          _ = (∏ j ∈ Finset.range k,
                  (((n + (j + 1) : ℕ) : ℝ) + d) / (((n + (j + 1) : ℕ) : ℝ) + c))
                * ((((n : ℝ) + d) / ((n : ℝ) + c))) := by
              rw [show ((((n + 0 : ℕ) : ℝ) + d) / (((n + 0 : ℕ) : ℝ) + c))
                  = (((n : ℝ) + d) / ((n : ℝ) + c)) by simp]
          _ = ((n : ℝ) + d) / ((n : ℝ) + c)
                * ∏ j ∈ Finset.range k,
                  (((n + (j + 1) : ℕ) : ℝ) + d) / (((n + (j + 1) : ℕ) : ℝ) + c) := by ring
          _ = ((n : ℝ) + d) / ((n : ℝ) + c)
                * ∏ j ∈ Finset.range k,
                  ((((n + 1) + j : ℕ) : ℝ) + d) / ((((n + 1) + j : ℕ) : ℝ) + c) := by
              apply congrArg (fun p => ((n : ℝ) + d) / ((n : ℝ) + c) * p)
              apply Finset.prod_congr rfl
              intro j _
              have e : n + (j + 1) = (n + 1) + j := by omega
              rw [e]
      have hcast2 : (n + 1 + k : ℕ) = n + (k + 1) := by omega
      rw [hprod]
      calc radDelta d c n (k + 1)
          ≤ ((n : ℝ) + d) / ((n : ℝ) + c) * radDelta d c (n + 1) k := h1
        _ ≤ ((n : ℝ) + d) / ((n : ℝ) + c)
              * ((∏ j ∈ Finset.range k,
                    ((((n + 1) + j : ℕ) : ℝ) + d) / ((((n + 1) + j : ℕ) : ℝ) + c))
                  * radDelta d c (n + (k + 1)) 0) :=
            mul_le_mul_of_nonneg_left (by rwa [hcast2] at h2) hfac
        _ = ((n : ℝ) + d) / ((n : ℝ) + c)
              * (∏ j ∈ Finset.range k,
                    ((((n + 1) + j : ℕ) : ℝ) + d) / ((((n + 1) + j : ℕ) : ℝ) + c))
              * radDelta d c (n + (k + 1)) 0 := by ring

/-- The bottom error is at most the tail itself. -/
lemma delta_bottom (n : ℕ) : radDelta d c n 0 ≤ (n : ℝ) + c := by
  simp only [radDelta, tail]
  have hs := radS_nonneg (d := d) (c := c) n 0
  linarith

section Regime1

/-- Telescoping product: `∏_{j<N} (j+d)/(j+d+2) = d(d+1)/((N+d)(N+d+1))`. -/
lemma prod_telescope (hd : 1 ≤ d) (N : ℕ) :
    (∏ j ∈ Finset.range N, (((j : ℝ) + d) / ((j : ℝ) + d + 2)))
      = (d : ℝ) * ((d : ℝ) + 1) / (((N : ℝ) + d) * ((N : ℝ) + d + 1)) := by
  induction N with
  | zero =>
      have hne : (d : ℝ) * ((d : ℝ) + 1) ≠ 0 := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        apply mul_ne_zero (by linarith) (by linarith)
      simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, zero_add]
      exact (div_self hne).symm
  | succ N ih =>
      rw [Finset.prod_range_succ, ih]
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have e1 : ((N : ℝ) + d) ≠ 0 := ne_of_gt (by linarith)
      have e2 : ((N : ℝ) + d + 1) ≠ 0 := ne_of_gt (by linarith)
      have e3 : ((N : ℝ) + d + 2) ≠ 0 := ne_of_gt (by linarith)
      have e4 : ((N : ℝ) + 1 + d) ≠ 0 := ne_of_gt (by linarith)
      have e5 : ((N : ℝ) + 1 + d + 1) ≠ 0 := ne_of_gt (by linarith)
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      field_simp
      ring

/-- The contraction product is small when `c ≥ d + 2`. -/
lemma prod_bound (hd : 1 ≤ d) (hc : d + 2 ≤ c) (N : ℕ) :
    ∏ j ∈ Finset.range N, ((j : ℝ) + d) / ((j : ℝ) + c)
      ≤ (d : ℝ) * ((d : ℝ) + 1) / (((N : ℝ) + d) * ((N : ℝ) + d + 1)) := by
  have hle : ∏ j ∈ Finset.range N, ((j : ℝ) + d) / ((j : ℝ) + c)
      ≤ ∏ j ∈ Finset.range N, ((j : ℝ) + d) / ((j : ℝ) + d + 2) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        have hcc : ((N : ℝ) + d + 2) ≤ ((N : ℝ) + c) := by
          have h2 : ((d : ℝ) + 2) ≤ (c : ℝ) := by exact_mod_cast hc
          linarith
        have hle1 : ((N : ℝ) + d) / ((N : ℝ) + c)
            ≤ ((N : ℝ) + d) / ((N : ℝ) + d + 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hcc
        exact mul_le_mul ih hle1 (by apply div_nonneg <;> positivity)
          (Finset.prod_nonneg (fun j _ => by apply div_nonneg <;> positivity))
  rw [← prod_telescope hd N]
  exact hle

/-- Error bound in the regime `c ≥ d + 2`. -/
lemma delta_bound_regime1 (hd : 1 ≤ d) (hc : d + 2 ≤ c) (h : d < c) (N : ℕ) :
    radDelta d c 0 N ≤ (d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1) / ((N : ℝ) + 1) := by
  have h1 := delta_iter h 0 N
  simp only [Nat.zero_add] at h1
  have h2 := prod_bound hd hc N
  have h3 := delta_bottom (d := d) (c := c) N
  have h4 : radDelta d c 0 N
      ≤ ((d : ℝ) * ((d : ℝ) + 1) / (((N : ℝ) + d) * ((N : ℝ) + d + 1)))
        * ((N : ℝ) + c) :=
    le_trans h1 (mul_le_mul h2 h3 (delta_nonneg N 0) (by positivity))
  have h5 : ((d : ℝ) * ((d : ℝ) + 1) / (((N : ℝ) + d) * ((N : ℝ) + d + 1)))
        * ((N : ℝ) + c)
      ≤ (d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1) / ((N : ℝ) + 1) := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hc' : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have e1 : (0 : ℝ) < (N : ℝ) + d := by positivity
    have e2 : (0 : ℝ) < (N : ℝ) + d + 1 := by positivity
    have e3 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos e1 e2), div_mul_eq_mul_div,
      le_div_iff₀ e3]
    have hNd : (N : ℝ) + 1 ≤ (N : ℝ) + d := by
      have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hNd1 : (N : ℝ) + 1 ≤ (N : ℝ) + d + 1 := by linarith
    have hNc : (N : ℝ) + c ≤ ((c : ℝ) + 1) * ((N : ℝ) + 1) := by
      nlinarith [mul_nonneg hc' hN]
    calc (d : ℝ) * ((d : ℝ) + 1) * ((N : ℝ) + c) * ((N : ℝ) + 1)
        ≤ (d : ℝ) * ((d : ℝ) + 1) * (((c : ℝ) + 1) * ((N : ℝ) + 1)) * ((N : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hNc (by positivity)
      _ = (d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1) * (((N : ℝ) + 1) * ((N : ℝ) + 1)) := by
          ring
      _ ≤ (d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1) * (((N : ℝ) + d) * ((N : ℝ) + d + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hNd hNd1 (by positivity) (by positivity)
  exact le_trans h4 h5

/-- Convergence in the regime `c ≥ d + 2`. -/
theorem tendsto_regime1 (hd : 1 ≤ d) (hc : d + 2 ≤ c) (h : d < c) :
    Tendsto (fun N : ℕ => radS d c 0 N) atTop (𝓝 (c : ℝ)) := by
  have hK0 : Tendsto
      (fun N : ℕ => ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto
        (fun N : ℕ => ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1))
          * ((1 : ℝ) / ((N : ℝ) + 1)))
        atTop (𝓝 (((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) * 0)) :=
      tendsto_const_nhds.mul h1
    have h3 : (fun N : ℕ => ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1))
          * ((1 : ℝ) / ((N : ℝ) + 1)))
        = (fun N : ℕ => ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1)) := by
      ext N
      rw [mul_one_div]
    rw [h3] at h2
    simpa using h2
  have hbound : ∀ N : ℕ,
      |(radS d c 0 N) - (c : ℝ)|
        ≤ ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1) := by
    intro N
    have hd1 := delta_bound_regime1 hd hc h N
    have hde : radDelta d c 0 N = (c : ℝ) - radS d c 0 N := by
      simp only [radDelta, tail]; push_cast; ring
    have hnn : 0 ≤ radDelta d c 0 N := delta_nonneg 0 N
    rw [hde] at hnn hd1
    have habs : |radS d c 0 N - (c : ℝ)| = (c : ℝ) - radS d c 0 N := by
      have hneg : radS d c 0 N - (c : ℝ) = -((c : ℝ) - radS d c 0 N) := by ring
      rw [hneg, abs_neg, abs_of_nonneg hnn]
    rw [habs]
    exact hd1
  have hlow : ∀ N : ℕ,
      (c : ℝ) - ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1)
        ≤ radS d c 0 N := by
    intro N
    have h := hbound N
    rw [abs_le] at h
    linarith [h.1]
  have hglow : Tendsto
      (fun N : ℕ => (c : ℝ)
        - ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1))
      atTop (𝓝 ((c : ℝ) - 0)) :=
    tendsto_const_nhds.sub hK0
  have hglow' : Tendsto
      (fun N : ℕ => (c : ℝ)
        - ((d : ℝ) * ((d : ℝ) + 1) * ((c : ℝ) + 1)) / ((N : ℝ) + 1))
      atTop (𝓝 (c : ℝ)) := by simpa using hglow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hglow' tendsto_const_nhds hlow
    (fun N => by simpa [tail] using radS_le 0 N)

end Regime1

section Regime2

/-- When `c = d + 1`, `A n = 1` for all `n`. -/
lemma radA_eq_one (hceq : c = d + 1) (n : ℕ) : radA d c n = 1 := by
  rw [radA_eq]
  have hcc : (c : ℝ) = (d : ℝ) + 1 := by exact_mod_cast hceq
  rw [hcc]
  ring

/-- `S(n, 1) = √(n+d+1)`. -/
lemma radS_one (hceq : c = d + 1) (n : ℕ) :
    radS d c n 1 = Real.sqrt ((n : ℝ) + d + 1) := by
  have e1 : radS d c n 1
      = Real.sqrt (radA d c n + radB d n * radS d c (n + 1) 0) := rfl
  have e2 : radS d c (n + 1) 0 = Real.sqrt (radA d c (n + 1)) := rfl
  rw [e1, e2, radA_eq_one hceq n, radA_eq_one hceq (n + 1), Real.sqrt_one]
  congr 1
  simp only [radB]
  ring

/-- Truncations are monotone in depth. -/
lemma radS_succ_le (n k : ℕ) : radS d c n k ≤ radS d c n (k + 1) := by
  induction k generalizing n with
  | zero =>
      have e1 : radS d c n 0 = Real.sqrt (radA d c n) := rfl
      have e2 : radS d c n 1
          = Real.sqrt (radA d c n + radB d n * radS d c (n + 1) 0) := rfl
      rw [e1, e2]
      apply Real.sqrt_le_sqrt
      have hB : (0 : ℝ) ≤ radB d n * radS d c (n + 1) 0 :=
        mul_nonneg (radB_nonneg n) (radS_nonneg (n + 1) 0)
      linarith
  | succ k ih =>
      have e1 : radS d c n (k + 1)
          = Real.sqrt (radA d c n + radB d n * radS d c (n + 1) k) := rfl
      have e2 : radS d c n (k + 2)
          = Real.sqrt (radA d c n + radB d n * radS d c (n + 1) (k + 1)) := rfl
      rw [e1, e2]
      apply Real.sqrt_le_sqrt
      have h1 := ih (n + 1)
      have h2 : radB d n * radS d c (n + 1) k
          ≤ radB d n * radS d c (n + 1) (k + 1) :=
        mul_le_mul_of_nonneg_left h1 (radB_nonneg (d := d) n)
      linarith

/-- For `k ≥ 1`, `S(n, k) ≥ √(n+d+1)`. -/
lemma radS_ge_sqrt (hceq : c = d + 1) (n k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt ((n : ℝ) + d + 1) ≤ radS d c n k := by
  have hmono : Monotone (radS d c n) :=
    monotone_nat_of_le_succ (radS_succ_le (d := d) (c := c) n)
  have h1 : radS d c n 1 ≤ radS d c n k := hmono hk
  rw [radS_one hceq n] at h1
  exact h1

/-- The contraction factor in regime 2:
`(n+d)/((n+d+1)+√(n+d+1)) = 1 - 1/√(n+d+1)`. -/
lemma contract_factor (n : ℕ) :
    ((n : ℝ) + d) / (((n : ℝ) + d + 1) + Real.sqrt ((n : ℝ) + d + 1))
      = 1 - 1 / Real.sqrt ((n : ℝ) + d + 1) := by
  set u := Real.sqrt ((n : ℝ) + d + 1) with hu
  have hu2 : u ^ 2 = (n : ℝ) + d + 1 := Real.sq_sqrt (by positivity)
  have hu0 : (0 : ℝ) < u := Real.sqrt_pos.mpr (by positivity)
  have h1 : ((n : ℝ) + d) = u ^ 2 - 1 := by rw [hu2]; ring
  have h2 : ((n : ℝ) + d + 1) + u = u * (u + 1) := by
    rw [← hu2]; ring
  rw [h2, h1]
  have h3 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  rw [h3, mul_div_mul_right _ _ (ne_of_gt (by positivity : (0 : ℝ) < u + 1))]
  rw [sub_div, div_self (ne_of_gt hu0)]

/-- Sharp one-step contraction in regime 2. -/
lemma delta_step_regime2 (hceq : c = d + 1) (h : d < c) (n k : ℕ) :
    radDelta d c n (k + 1)
      ≤ (1 - 1 / Real.sqrt ((n : ℝ) + d + 1)) * radDelta d c (n + 1) k := by
  rw [delta_eq h n k]
  have ht_pos : (0 : ℝ) < tail c n + Real.sqrt ((n : ℝ) + d + 1) := by
    simp only [tail]; positivity
  have hnum_nonneg : (0 : ℝ) ≤ radB d n * radDelta d c (n + 1) k :=
    mul_nonneg (radB_nonneg n) (delta_nonneg (n + 1) k)
  have hden : tail c n + Real.sqrt ((n : ℝ) + d + 1)
      ≤ tail c n + radS d c n (k + 1) := by
    have hs := radS_ge_sqrt hceq n (k + 1) (by omega)
    simp only [tail]
    linarith
  have hle : (radB d n * radDelta d c (n + 1) k) / (tail c n + radS d c n (k + 1))
      ≤ (radB d n * radDelta d c (n + 1) k) / (tail c n + Real.sqrt ((n : ℝ) + d + 1)) :=
    div_le_div_of_nonneg_left hnum_nonneg ht_pos hden
  calc (radB d n * radDelta d c (n + 1) k) / (tail c n + radS d c n (k + 1))
      ≤ (radB d n * radDelta d c (n + 1) k)
          / (tail c n + Real.sqrt ((n : ℝ) + d + 1)) := hle
    _ = (1 - 1 / Real.sqrt ((n : ℝ) + d + 1)) * radDelta d c (n + 1) k := by
        have hcc : tail c n = (n : ℝ) + d + 1 := by
          have h1 : (c : ℝ) = (d : ℝ) + 1 := by exact_mod_cast hceq
          simp only [tail]; rw [h1]; ring
        rw [← div_mul_eq_mul_div, hcc]
        simp only [radB]
        rw [contract_factor n]

/-- Iterating the sharp contraction. -/
lemma delta_iter2 (hceq : c = d + 1) (h : d < c) (n : ℕ) (M : ℕ) :
    radDelta d c n (M + 1)
      ≤ (∏ j ∈ Finset.range M,
            (1 - 1 / Real.sqrt ((((n + j : ℕ) : ℝ) + d + 1))))
        * radDelta d c (n + M) 1 := by
  induction M generalizing n with
  | zero => simp
  | succ M ih =>
      have h1 := delta_step_regime2 hceq h n (M + 1)
      have h2 := ih (n + 1)
      have hfac : (0 : ℝ) ≤ 1 - 1 / Real.sqrt (((n : ℝ) + d + 1)) := by
        have hpos : (0 : ℝ) < Real.sqrt (((n : ℝ) + d + 1)) :=
          Real.sqrt_pos.mpr (by positivity)
        have hge : (1 : ℝ) ≤ Real.sqrt (((n : ℝ) + d + 1)) := by
          have h1 : Real.sqrt (1 : ℝ) ≤ Real.sqrt (((n : ℝ) + d + 1)) :=
            Real.sqrt_le_sqrt (by
              have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
              linarith)
          rwa [Real.sqrt_one] at h1
        have h3 : (1 : ℝ) / Real.sqrt (((n : ℝ) + d + 1)) ≤ 1 := by
          rw [div_le_one hpos]; exact hge
        linarith
      have hprod : (∏ j ∈ Finset.range (M + 1),
            (1 - 1 / Real.sqrt ((((n + j : ℕ) : ℝ) + d + 1))))
          = (1 - 1 / Real.sqrt (((n : ℝ) + d + 1)))
            * ∏ j ∈ Finset.range M,
              (1 - 1 / Real.sqrt (((((n + 1) + j : ℕ) : ℝ) + d + 1))) := by
        calc (∏ j ∈ Finset.range (M + 1),
              (1 - 1 / Real.sqrt ((((n + j : ℕ) : ℝ) + d + 1))))
            = (∏ j ∈ Finset.range M,
                  (1 - 1 / Real.sqrt ((((n + (j + 1) : ℕ) : ℝ) + d + 1))))
                * (1 - 1 / Real.sqrt ((((n + 0 : ℕ) : ℝ) + d + 1))) :=
              Finset.prod_range_succ' _ _
          _ = (∏ j ∈ Finset.range M,
                  (1 - 1 / Real.sqrt ((((n + (j + 1) : ℕ) : ℝ) + d + 1))))
                * (1 - 1 / Real.sqrt (((n : ℝ) + d + 1))) := by
              rw [show (1 - 1 / Real.sqrt ((((n + 0 : ℕ) : ℝ) + d + 1)))
                  = (1 - 1 / Real.sqrt (((n : ℝ) + d + 1))) by simp]
          _ = (1 - 1 / Real.sqrt (((n : ℝ) + d + 1)))
                * ∏ j ∈ Finset.range M,
                  (1 - 1 / Real.sqrt ((((n + (j + 1) : ℕ) : ℝ) + d + 1))) := by ring
          _ = (1 - 1 / Real.sqrt (((n : ℝ) + d + 1)))
                * ∏ j ∈ Finset.range M,
                  (1 - 1 / Real.sqrt (((((n + 1) + j : ℕ) : ℝ) + d + 1))) := by
              apply congrArg
                (fun p => (1 - 1 / Real.sqrt (((n : ℝ) + d + 1))) * p)
              apply Finset.prod_congr rfl
              intro j _
              have e : n + (j + 1) = (n + 1) + j := by omega
              rw [e]
      have hcast : (n + 1 + M : ℕ) = n + (M + 1) := by omega
      rw [hprod]
      calc radDelta d c n (M + 1 + 1)
          ≤ (1 - 1 / Real.sqrt (((n : ℝ) + d + 1))) * radDelta d c (n + 1) (M + 1) := h1
        _ ≤ (1 - 1 / Real.sqrt (((n : ℝ) + d + 1)))
              * ((∏ j ∈ Finset.range M,
                    (1 - 1 / Real.sqrt (((((n + 1) + j : ℕ) : ℝ) + d + 1))))
                  * radDelta d c (n + (M + 1)) 1) :=
            mul_le_mul_of_nonneg_left (by rwa [hcast] at h2) hfac
        _ = (1 - 1 / Real.sqrt (((n : ℝ) + d + 1)))
              * (∏ j ∈ Finset.range M,
                    (1 - 1 / Real.sqrt (((((n + 1) + j : ℕ) : ℝ) + d + 1))))
              * radDelta d c (n + (M + 1)) 1 := by ring

/-- `∏ (1 - f j) ≤ exp(-∑ f j)` for `0 ≤ f j ≤ 1`. -/
lemma prod_one_sub_le_exp (s : Finset ℕ) (f : ℕ → ℝ) :
    (∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1) → ∏ j ∈ s, (1 - f j) ≤ Real.exp (-∑ j ∈ s, f j) := by
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hf
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hfa : (0 : ℝ) ≤ f a := (hf a (Finset.mem_insert_self a s)).1
      have hfa1 : f a ≤ 1 := (hf a (Finset.mem_insert_self a s)).2
      have hfa' : (0 : ℝ) ≤ 1 - f a := by linarith
      have h1 : (1 - f a) ≤ Real.exp (-f a) := by
        have h := Real.add_one_le_exp (-f a)
        linarith
      calc (1 - f a) * (∏ j ∈ s, (1 - f j))
          ≤ (1 - f a) * Real.exp (-∑ j ∈ s, f j) :=
            mul_le_mul_of_nonneg_left
              (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) hfa'
        _ ≤ Real.exp (-f a) * Real.exp (-∑ j ∈ s, f j) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = Real.exp (-(f a + ∑ j ∈ s, f j)) := by
            rw [← Real.exp_add]
            congr 1
            ring

/-- The reciprocal square roots sum to at least `M/√(M+d)`. -/
lemma sum_sqrt_bound (M : ℕ) :
    ((M : ℝ)) / Real.sqrt ((M : ℝ) + d)
      ≤ ∑ j ∈ Finset.range M, 1 / Real.sqrt (((j : ℝ) + d + 1)) := by
  have h1 : ∀ j ∈ Finset.range M,
      (1 : ℝ) / Real.sqrt ((M : ℝ) + d) ≤ 1 / Real.sqrt (((j : ℝ) + d + 1)) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hle : ((j : ℝ) + d + 1) ≤ (M : ℝ) + d := by
      have hj' : (j : ℝ) ≤ (M : ℝ) - 1 := by
        have h2 : j + 1 ≤ M := hjM
        have h3 : ((j : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast h2
        linarith
      linarith
    apply one_div_le_one_div_of_le (by positivity)
    exact Real.sqrt_le_sqrt hle
  calc ((M : ℝ)) / Real.sqrt ((M : ℝ) + d)
      = (Finset.range M).card • (1 / Real.sqrt ((M : ℝ) + d)) := by
        rw [Finset.card_range, nsmul_eq_mul]
        rw [mul_one_div]
    _ ≤ ∑ j ∈ Finset.range M, 1 / Real.sqrt (((j : ℝ) + d + 1)) := by
        rw [← Finset.sum_const]
        exact Finset.sum_le_sum h1

/-- `exp(-t) ≤ 27/t³` for `t > 0`. -/
lemma exp_neg_le (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ 27 / t ^ 3 := by
  have h1 : (t / 3) ^ 3 ≤ Real.exp t := by
    have h2 : (t / 3) + 1 ≤ Real.exp (t / 3) := Real.add_one_le_exp (t / 3)
    have h3 : Real.exp t = (Real.exp (t / 3)) ^ 3 := by
      rw [show t = (t / 3) + (t / 3) + (t / 3) by ring, Real.exp_add, Real.exp_add]
      ring_nf
    rw [h3]
    have h4 : (0 : ℝ) ≤ t / 3 := by linarith
    have h5 : (t / 3) ^ 3 ≤ ((t / 3) + 1) ^ 3 :=
      pow_le_pow_left₀ h4 (by linarith) 3
    have h6 : ((t / 3) + 1) ^ 3 ≤ (Real.exp (t / 3)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) h2 3
    exact le_trans h5 h6
  have h2 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  rw [h2]
  have h4 : ((t / 3) ^ 3)⁻¹ = 27 / t ^ 3 := by
    rw [div_pow, show (3 : ℝ) ^ 3 = 27 by norm_num, inv_div]
  rw [← h4]
  exact (inv_le_inv₀ (Real.exp_pos t) (by positivity)).mpr h1

/-- Error bound in the regime `c = d + 1`. -/
lemma delta_bound_regime2 (hceq : c = d + 1) (h : d < c) (M : ℕ) (hM : d + 1 ≤ M) :
    radDelta d c 0 (M + 1) ≤ 162 * Real.sqrt 2 / Real.sqrt (M : ℝ) := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    have h1 : (1 : ℕ) ≤ M := le_trans (by omega : 1 ≤ d + 1) hM
    exact_mod_cast h1
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have h1 := delta_iter2 hceq h 0 M
  have h2 : radDelta d c M 1 ≤ (M : ℝ) + d + 1 := by
    have hcc : tail c M = (M : ℝ) + d + 1 := by
      have h3 : (c : ℝ) = (d : ℝ) + 1 := by exact_mod_cast hceq
      simp only [tail]; rw [h3]; ring
    have hs := radS_nonneg (d := d) (c := c) M 1
    simp only [radDelta]
    rw [hcc]
    linarith
  have h3 : (∏ j ∈ Finset.range M,
        (1 - 1 / Real.sqrt ((((0 + j : ℕ) : ℝ) + d + 1))))
      ≤ Real.exp (-((M : ℝ) / Real.sqrt ((M : ℝ) + d))) := by
    have h4 := prod_one_sub_le_exp (Finset.range M)
      (fun j => 1 / Real.sqrt (((j : ℝ) + d + 1)))
      (fun j _ => by
        constructor
        · positivity
        · have hpos : (0 : ℝ) < Real.sqrt (((j : ℝ) + d + 1)) :=
            Real.sqrt_pos.mpr (by positivity)
          have hge : (1 : ℝ) ≤ Real.sqrt (((j : ℝ) + d + 1)) := by
            have h6 : Real.sqrt (1 : ℝ) ≤ Real.sqrt (((j : ℝ) + d + 1)) :=
              Real.sqrt_le_sqrt (by
                have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
                have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
                linarith)
            rwa [Real.sqrt_one] at h6
          rw [div_le_one hpos]
          exact hge)
    have h5 := sum_sqrt_bound (d := d) M
    have h6 : Real.exp (-∑ j ∈ Finset.range M, 1 / Real.sqrt (((j : ℝ) + d + 1)))
        ≤ Real.exp (-((M : ℝ) / Real.sqrt ((M : ℝ) + d))) := by
      apply Real.exp_le_exp.mpr
      linarith [h5]
    have h7 : (∏ j ∈ Finset.range M,
          (1 - 1 / Real.sqrt ((((0 + j : ℕ) : ℝ) + d + 1))))
        = ∏ j ∈ Finset.range M, (1 - 1 / Real.sqrt (((j : ℝ) + d + 1))) := by
      apply Finset.prod_congr rfl
      intro j _
      simp
    rw [h7]
    exact le_trans h4 h6
  have h4 : radDelta d c 0 (M + 1)
      ≤ Real.exp (-((M : ℝ) / Real.sqrt ((M : ℝ) + d))) * ((M : ℝ) + d + 1) := by
    have h5 : radDelta d c 0 (M + 1)
        ≤ (∏ j ∈ Finset.range M,
              (1 - 1 / Real.sqrt ((((0 + j : ℕ) : ℝ) + d + 1))))
          * radDelta d c (0 + M) 1 := h1
    rw [show (0 + M : ℕ) = M from Nat.zero_add M] at h5
    exact le_trans h5 (mul_le_mul h3 h2 (delta_nonneg M 1) (Real.exp_nonneg _))
  have ht : (0 : ℝ) < (M : ℝ) / Real.sqrt ((M : ℝ) + d) := by
    apply div_pos hMpos
    apply Real.sqrt_pos.mpr; positivity
  have h6 : Real.exp (-((M : ℝ) / Real.sqrt ((M : ℝ) + d)))
      ≤ 27 / ((M : ℝ) / Real.sqrt ((M : ℝ) + d)) ^ 3 :=
    exp_neg_le _ ht
  have h7 : 27 / ((M : ℝ) / Real.sqrt ((M : ℝ) + d)) ^ 3 * ((M : ℝ) + d + 1)
      ≤ 162 * Real.sqrt 2 / Real.sqrt (M : ℝ) := by
    have hMd : (M : ℝ) + d ≤ 2 * (M : ℝ) := by
      have hdd : (d : ℝ) ≤ (M : ℝ) := by
        have hdd' : d ≤ M := le_trans (by omega : d ≤ d + 1) hM
        exact_mod_cast hdd'
      linarith
    have hMd1 : (M : ℝ) + d + 1 ≤ 3 * (M : ℝ) := by linarith
    have hsqrt : Real.sqrt ((M : ℝ) + d) ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) := by
      have h8 : Real.sqrt ((M : ℝ) + d) ≤ Real.sqrt (2 * (M : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h8
      exact h8
    have hsqrtpos : (0 : ℝ) < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMpos
    have hM3 : (0 : ℝ) < (M : ℝ) ^ 3 := by positivity
    have hsq : (Real.sqrt ((M : ℝ) + d)) ^ 3
        = ((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) := by
      rw [pow_succ, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (M : ℝ) + d)]
    have key : 27 / ((M : ℝ) / Real.sqrt ((M : ℝ) + d)) ^ 3 * ((M : ℝ) + d + 1)
        = 27 * (((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) * ((M : ℝ) + d + 1))
          / (M : ℝ) ^ 3 := by
      have hM3' : (M : ℝ) ^ 3 ≠ 0 := ne_of_gt hM3
      have hS : Real.sqrt ((M : ℝ) + d) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (by positivity))
      have hMd' : (M : ℝ) + d ≠ 0 := ne_of_gt (by positivity)
      have hprod : ((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) ≠ 0 :=
        mul_ne_zero hMd' hS
      rw [div_pow, hsq]
      field_simp
    have h9 : ((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) * ((M : ℝ) + d + 1)
        ≤ 6 * (M : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (M : ℝ)) := by
      have b1 : ((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) * ((M : ℝ) + d + 1)
          ≤ (2 * (M : ℝ)) * (Real.sqrt 2 * Real.sqrt (M : ℝ)) * (3 * (M : ℝ)) := by
        apply mul_le_mul (mul_le_mul hMd hsqrt (by positivity) (by positivity))
          hMd1 (by positivity) (by positivity)
      calc ((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) * ((M : ℝ) + d + 1)
          ≤ (2 * (M : ℝ)) * (Real.sqrt 2 * Real.sqrt (M : ℝ)) * (3 * (M : ℝ)) := b1
        _ = 6 * (M : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (M : ℝ)) := by ring
    have h10 : 27 * (((M : ℝ) + d) * Real.sqrt ((M : ℝ) + d) * ((M : ℝ) + d + 1))
          / (M : ℝ) ^ 3
        ≤ 27 * (6 * (M : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (M : ℝ))) / (M : ℝ) ^ 3 := by
      apply (div_le_div_iff_of_pos_right hM3).mpr
      exact mul_le_mul_of_nonneg_left h9 (by norm_num)
    have h11 : 27 * (6 * (M : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (M : ℝ))) / (M : ℝ) ^ 3
        = 162 * Real.sqrt 2 / Real.sqrt (M : ℝ) := by
      have hS' : Real.sqrt (M : ℝ) ≠ 0 := ne_of_gt hsqrtpos
      have hM3' : (M : ℝ) ^ 3 ≠ 0 := ne_of_gt hM3
      have h13 : (M : ℝ) ^ 2 * Real.sqrt (M : ℝ) / (M : ℝ) ^ 3
          = 1 / Real.sqrt (M : ℝ) := by
        have h14 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
          Real.mul_self_sqrt (by positivity)
        field_simp
        nlinarith [h14]
      have h14 : 27 * (6 * (M : ℝ) ^ 2 * (Real.sqrt 2 * Real.sqrt (M : ℝ))) / (M : ℝ) ^ 3
          = 162 * Real.sqrt 2 * ((M : ℝ) ^ 2 * Real.sqrt (M : ℝ) / (M : ℝ) ^ 3) := by
        field_simp
        ring
      rw [h14, h13, mul_one_div]
    rw [key]
    exact h10.trans_eq h11
  exact le_trans (le_trans h4 (mul_le_mul_of_nonneg_right h6 (by positivity))) h7

/-- Convergence in the regime `c = d + 1`. -/
theorem tendsto_regime2 (hceq : c = d + 1) (h : d < c) :
    Tendsto (fun N : ℕ => radS d c 0 N) atTop (𝓝 (c : ℝ)) := by
  have hshift : Tendsto (fun M : ℕ => radS d c 0 (M + 1)) atTop (𝓝 (c : ℝ)) := by
    have hK0 : Tendsto (fun M : ℕ => 162 * Real.sqrt 2 / Real.sqrt (M : ℝ))
        atTop (𝓝 0) := by
      have hsqrt : Tendsto (fun M : ℕ => Real.sqrt (M : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      have hinv : Tendsto (fun M : ℕ => (Real.sqrt (M : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hsqrt
      have h2 : Tendsto (fun M : ℕ => (162 * Real.sqrt 2) * (Real.sqrt (M : ℝ))⁻¹)
          atTop (𝓝 ((162 * Real.sqrt 2) * 0)) :=
        tendsto_const_nhds.mul hinv
      have h3 : (fun M : ℕ => (162 * Real.sqrt 2) * (Real.sqrt (M : ℝ))⁻¹)
          = (fun M : ℕ => 162 * Real.sqrt 2 / Real.sqrt (M : ℝ)) := by
        ext M; rw [div_eq_mul_inv]
      rw [h3] at h2
      simpa using h2
    have hbound : ∀ᶠ (M : ℕ) in atTop,
        |radS d c 0 (M + 1) - (c : ℝ)| ≤ 162 * Real.sqrt 2 / Real.sqrt (M : ℝ) := by
      rw [eventually_atTop]
      refine ⟨d + 1, fun M hM => ?_⟩
      have hd1 := delta_bound_regime2 hceq h M hM
      have hde : radDelta d c 0 (M + 1) = (c : ℝ) - radS d c 0 (M + 1) := by
        simp only [radDelta, tail]; push_cast; ring
      have hnn : 0 ≤ radDelta d c 0 (M + 1) := delta_nonneg 0 (M + 1)
      rw [hde] at hnn hd1
      have habs : |radS d c 0 (M + 1) - (c : ℝ)| = (c : ℝ) - radS d c 0 (M + 1) := by
        have hneg : radS d c 0 (M + 1) - (c : ℝ) = -((c : ℝ) - radS d c 0 (M + 1)) := by ring
        rw [hneg, abs_neg, abs_of_nonneg hnn]
      rw [habs]
      exact hd1
    have hlow : ∀ᶠ (M : ℕ) in atTop,
        (c : ℝ) - 162 * Real.sqrt 2 / Real.sqrt (M : ℝ) ≤ radS d c 0 (M + 1) := by
      filter_upwards [hbound] with M hM
      rw [abs_le] at hM
      linarith [hM.1]
    have hglow : Tendsto
        (fun M : ℕ => (c : ℝ) - 162 * Real.sqrt 2 / Real.sqrt (M : ℝ))
        atTop (𝓝 ((c : ℝ) - 0)) :=
      tendsto_const_nhds.sub hK0
    have hglow' : Tendsto
        (fun M : ℕ => (c : ℝ) - 162 * Real.sqrt 2 / Real.sqrt (M : ℝ))
        atTop (𝓝 (c : ℝ)) := by simpa using hglow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hglow' tendsto_const_nhds hlow
      (Filter.Eventually.of_forall (fun M => by
        have hle := radS_le (d := d) (c := c) 0 (M + 1)
        simpa [tail] using hle))
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end Regime2

/-- **The Nested-Radical Master Theorem (m = 2).** For all `1 ≤ d < c`, the
depth-`N` truncations of `√(A 0 + B 0 √(A 1 + ⋯))` converge to `c`. -/
theorem nested_radical_master (hd : 1 ≤ d) (h : d < c) :
    Tendsto (fun N : ℕ => radS d c 0 N) atTop (𝓝 (c : ℝ)) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h1 | h1
  · have hceq : c = d + 1 := by omega
    exact tendsto_regime2 hceq h
  · have hc : d + 2 ≤ c := by omega
    exact tendsto_regime1 hd hc h

#print axioms nested_radical_master

end NestedRadicalMaster

end
