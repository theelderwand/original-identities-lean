/-
# Mixed-Root Master Theorem, machine-checked in Lean 4

**Theorem.** Let `c ≥ 2`. Define the degree at level `n` by
`deg n = 2` if `n` is even, `deg n = 3` if `n` is odd, and

    A n = (n + c)^(deg n) − (n + c + 1).

Then the depth-`N` truncations of the alternating nested radical

    c = ²√(A 0 + ³√(A 1 + ²√(A 2 + ³√(A 3 + ⋯))))

converge to `c` as `N → ∞`.

**Proof idea.** The exact tails are `t n = n + c`, since
`(t n)^(deg n) = A n + t (n+1)`. Writing `δ(n,k) = t n − S(n,k)`, the
factorisation `x^d − y^d = (x − y)·S` (geometric sum) gives
`δ(n,k+1) = δ(n+1,k) / S` with `S ≥ (t n)^(deg n − 1) ≥ t n = n + c`, hence
`δ(n,k+1) ≤ δ(n+1,k) / (n+c)`. Iterating,
`δ(0,N) ≤ (N+c) / ∏_{j<N} (j+c) ≤ (N+c) / c^N → 0` since `c ≥ 2`
(polynomial times geometric).

**What is proven here.** The full master theorem for all `c ≥ 2`.
The `deg n`-th root is `Real.rpow` with exponent `1/(deg n)`.
The hypothesis `c ≥ 2` is needed: for `c = 1`, `A 0 = 1² − 2 = −1 < 0`,
so the level-0 square root is not even real.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology

noncomputable section

namespace MixedRootMaster

variable {c : ℕ}

/-- The root degree at level `n`: `2` at even levels, `3` at odd levels. -/
def mdeg (n : ℕ) : ℕ := if n % 2 = 0 then 2 else 3

lemma mdeg_ge_two (n : ℕ) : 2 ≤ mdeg n := by
  unfold mdeg
  split_ifs <;> norm_num

lemma mdeg_pos (n : ℕ) : 0 < mdeg n := by
  have h := mdeg_ge_two n
  omega

lemma mdeg_ne_zero (n : ℕ) : mdeg n ≠ 0 := by
  have h := mdeg_pos n
  omega

/-- The `deg n`-th root, via `Real.rpow`. -/
def mroot (n : ℕ) (x : ℝ) : ℝ := x ^ ((mdeg n : ℝ)⁻¹)

lemma mroot_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ mroot n x :=
  Real.rpow_nonneg hx _

lemma mroot_pow (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (mroot n x) ^ (mdeg n) = x := by
  have hm0 : (mdeg n : ℝ) ≠ 0 := by
    have h := mdeg_pos n
    exact_mod_cast (ne_of_gt h)
  simp only [mroot]
  rw [← Real.rpow_natCast _ (mdeg n), ← Real.rpow_mul hx,
    inv_mul_cancel₀ hm0]
  exact Real.rpow_one x

/-- `A n = (n+c)^(deg n) − (n+c+1)`. -/
def mA (c : ℕ) (n : ℕ) : ℝ := ((n : ℝ) + c) ^ (mdeg n) - ((n : ℝ) + c + 1)

/-- The exact tail at level `n`: `t n = n + c`. -/
def mtail (c : ℕ) (n : ℕ) : ℝ := (n : ℝ) + c

/-- Depth-`k` truncation of the alternating nested radical starting at level `n`. -/
def mS (c : ℕ) : ℕ → ℕ → ℝ
  | n, 0 => mroot n (mA c n)
  | n, k + 1 => mroot n (mA c n + mS c (n + 1) k)

/-- The truncation error at level `n`, depth `k`. -/
def mDelta (c : ℕ) (n k : ℕ) : ℝ := mtail c n - mS c n k

/-- The telescoping identity: `(t n)^(deg n) = A n + t (n+1)`. -/
lemma key_identity (n : ℕ) :
    (mtail c n) ^ (mdeg n) = mA c n + mtail c (n + 1) := by
  simp only [mA, mtail]
  push_cast
  ring

lemma mtail_ge_one (hc : 1 ≤ c) (n : ℕ) : 1 ≤ mtail c n := by
  simp only [mtail]
  have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma mtail_pos (hc : 1 ≤ c) (n : ℕ) : 0 < mtail c n :=
  lt_of_lt_of_le zero_lt_one (mtail_ge_one hc n)

/-- `A n ≥ 0` whenever `c ≥ 2`. -/
lemma mA_nonneg (hc : 2 ≤ c) (n : ℕ) : 0 ≤ mA c n := by
  have hd : 2 ≤ mdeg n := mdeg_ge_two n
  have hx : (2 : ℝ) ≤ (n : ℝ) + c := by
    have hc' : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1 : ((n : ℝ) + c) ^ 2 ≤ ((n : ℝ) + c) ^ (mdeg n) := by
    apply pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + c)
    exact hd
  have h2 : (0 : ℝ) ≤ ((n : ℝ) + c) ^ 2 - ((n : ℝ) + c + 1) := by
    nlinarith [hx]
  simp only [mA]
  linarith

lemma mS_nonneg (hc : 2 ≤ c) (n k : ℕ) : 0 ≤ mS c n k := by
  induction k generalizing n with
  | zero =>
      simp only [mS]
      exact mroot_nonneg n _ (mA_nonneg hc n)
  | succ k ih =>
      simp only [mS]
      apply mroot_nonneg
      have h1 := mA_nonneg hc n
      have h2 := ih (n + 1)
      linarith

/-- Every truncation is bounded above by the exact tail. -/
lemma mS_le (hc : 2 ≤ c) (n k : ℕ) : mS c n k ≤ mtail c n := by
  have hm0 : mdeg n ≠ 0 := mdeg_ne_zero n
  induction k generalizing n with
  | zero =>
      have harg : mA c n ≤ (mtail c n) ^ (mdeg n) := by
        have hkey := key_identity (c := c) n
        have hB : (0 : ℝ) ≤ mtail c (n + 1) :=
          le_of_lt (mtail_pos (by omega : 1 ≤ c) (n + 1))
        linarith
      have hpow : (mS c n 0) ^ (mdeg n) ≤ (mtail c n) ^ (mdeg n) := by
        have e1 : mS c n 0 = mroot n (mA c n) := rfl
        rw [e1, mroot_pow n _ (mA_nonneg hc n)]
        exact harg
      exact le_of_pow_le_pow_left₀ hm0
        (le_of_lt (mtail_pos (by omega : 1 ≤ c) n)) hpow
  | succ k ih =>
      have h1 : mS c (n + 1) k ≤ mtail c (n + 1) := ih (n + 1) (mdeg_ne_zero (n + 1))
      have harg : mA c n + mS c (n + 1) k ≤ (mtail c n) ^ (mdeg n) := by
        have hkey := key_identity (c := c) n
        linarith
      have hpow : (mS c n (k + 1)) ^ (mdeg n) ≤ (mtail c n) ^ (mdeg n) := by
        have e1 : mS c n (k + 1) = mroot n (mA c n + mS c (n + 1) k) := rfl
        have harg_nonneg : (0 : ℝ) ≤ mA c n + mS c (n + 1) k := by
          have ha := mA_nonneg hc n
          have hb := mS_nonneg hc (n + 1) k
          linarith
        rw [e1, mroot_pow n _ harg_nonneg]
        exact harg
      exact le_of_pow_le_pow_left₀ hm0
        (le_of_lt (mtail_pos (by omega : 1 ≤ c) n)) hpow

lemma mDelta_nonneg (hc : 2 ≤ c) (n k : ℕ) : 0 ≤ mDelta c n k :=
  sub_nonneg.mpr (mS_le hc n k)

/-- The geometric-sum denominator is at least `n + c`. -/
lemma geom_sum_ge (hc : 2 ≤ c) (n k : ℕ) :
    ((n : ℝ) + c) ≤ ∑ i ∈ Finset.range (mdeg n),
      (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i) := by
  have hd : 2 ≤ mdeg n := mdeg_ge_two n
  have hm1 : mdeg n - 1 ∈ Finset.range (mdeg n) := by
    rw [Finset.mem_range]
    omega
  have hterms : ∀ i ∈ Finset.range (mdeg n),
      (0 : ℝ) ≤ (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i) := by
    intro i _
    apply mul_nonneg (pow_nonneg (le_of_lt (mtail_pos (by omega : 1 ≤ c) n)) _)
    apply pow_nonneg
    exact mS_nonneg hc n (k + 1)
  have hsingle := Finset.single_le_sum hterms hm1
  have hval : (mtail c n) ^ (mdeg n - 1)
        * (mS c n (k + 1)) ^ (mdeg n - 1 - (mdeg n - 1))
      = (mtail c n) ^ (mdeg n - 1) := by
    simp
  have hge : (mtail c n) ^ 1 ≤ (mtail c n) ^ (mdeg n - 1) := by
    apply pow_le_pow_right₀ (mtail_ge_one (by omega : 1 ≤ c) n)
    omega
  rw [hval] at hsingle
  calc ((n : ℝ) + c) = (mtail c n) ^ 1 := by simp [mtail]
    _ ≤ (mtail c n) ^ (mdeg n - 1) := hge
    _ ≤ ∑ i ∈ Finset.range (mdeg n),
          (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i) := hsingle

/-- One step of error contraction. -/
lemma mDelta_step (hc : 2 ≤ c) (n k : ℕ) :
    mDelta c n (k + 1) ≤ mDelta c (n + 1) k / ((n : ℝ) + c) := by
  have hpowS : (mS c n (k + 1)) ^ (mdeg n) = mA c n + mS c (n + 1) k := by
    have e1 : mS c n (k + 1) = mroot n (mA c n + mS c (n + 1) k) := rfl
    have harg_nonneg : (0 : ℝ) ≤ mA c n + mS c (n + 1) k := by
      have ha := mA_nonneg hc n
      have hb := mS_nonneg hc (n + 1) k
      linarith
    rw [e1, mroot_pow n _ harg_nonneg]
  have hpowT : (mtail c n) ^ (mdeg n) = mA c n + mtail c (n + 1) :=
    key_identity n
  have hdiff : (mtail c n) ^ (mdeg n) - (mS c n (k + 1)) ^ (mdeg n)
      = mDelta c (n + 1) k := by
    rw [hpowT, hpowS]
    simp only [mDelta]
    ring
  have hfactor : (mtail c n - mS c n (k + 1))
        * (∑ i ∈ Finset.range (mdeg n),
            (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i))
      = (mtail c n) ^ (mdeg n) - (mS c n (k + 1)) ^ (mdeg n) := by
    rw [mul_comm, geom_sum₂_mul]
  have hS : ((n : ℝ) + c) ≤ ∑ i ∈ Finset.range (mdeg n),
      (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i) :=
    geom_sum_ge hc n k
  have hdelta_nn : (0 : ℝ) ≤ mDelta c n (k + 1) := mDelta_nonneg hc n (k + 1)
  have hprod : mDelta c n (k + 1)
        * (∑ i ∈ Finset.range (mdeg n),
            (mtail c n) ^ i * (mS c n (k + 1)) ^ (mdeg n - 1 - i))
      = mDelta c (n + 1) k := by
    have h1 : mDelta c n (k + 1) = mtail c n - mS c n (k + 1) := rfl
    rw [h1, hfactor, hdiff]
  have hnc : (0 : ℝ) < (n : ℝ) + c := by
    have hc' : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    linarith
  have hle : mDelta c n (k + 1) * ((n : ℝ) + c) ≤ mDelta c (n + 1) k := by
    have h2 := mul_le_mul_of_nonneg_left hS hdelta_nn
    rw [hprod] at h2
    exact h2
  exact (le_div_iff₀ hnc).mpr hle

/-- Iterating the contraction. -/
lemma mDelta_iter (hc : 2 ≤ c) (n : ℕ) (N : ℕ) :
    mDelta c n N
      ≤ (((n + N : ℕ) : ℝ) + c) / ∏ j ∈ Finset.range N, (((n + j : ℕ) : ℝ) + c) := by
  induction N generalizing n with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, div_one, Nat.add_zero]
      have hs := mS_nonneg hc n 0
      simp only [mDelta, mtail]
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h3 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
      linarith
  | succ N ih =>
      have h1 := mDelta_step hc n N
      have h2 := ih (n + 1)
      have hcast : (n + 1 + N : ℕ) = n + (N + 1) := by omega
      have hnc : (0 : ℝ) < (n : ℝ) + c := by
        have hc' : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h2' : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
        linarith
      have hprod : (∏ j ∈ Finset.range (N + 1), (((n + j : ℕ) : ℝ) + c))
          = (((n : ℝ) + c))
            * ∏ j ∈ Finset.range N, ((((n + 1) + j : ℕ) : ℝ) + c) := by
        calc (∏ j ∈ Finset.range (N + 1), (((n + j : ℕ) : ℝ) + c))
            = (∏ j ∈ Finset.range N, (((n + (j + 1) : ℕ) : ℝ) + c))
                * ((((n + 0 : ℕ) : ℝ) + c)) :=
              Finset.prod_range_succ' _ _
          _ = (∏ j ∈ Finset.range N, (((n + (j + 1) : ℕ) : ℝ) + c))
                * ((((n : ℝ) + c))) := by
              rw [show ((((n + 0 : ℕ) : ℝ) + c)) = (((n : ℝ) + c)) by simp]
          _ = (((n : ℝ) + c))
                * ∏ j ∈ Finset.range N, (((n + (j + 1) : ℕ) : ℝ) + c) := by ring
          _ = (((n : ℝ) + c))
                * ∏ j ∈ Finset.range N, ((((n + 1) + j : ℕ) : ℝ) + c) := by
              apply congrArg (fun p => ((n : ℝ) + c) * p)
              apply Finset.prod_congr rfl
              intro j _
              have e : n + (j + 1) = (n + 1) + j := by omega
              rw [e]
      rw [hprod]
      calc mDelta c n (N + 1)
          ≤ mDelta c (n + 1) N / ((n : ℝ) + c) := h1
        _ ≤ ((((n + (N + 1) : ℕ) : ℝ) + c)
              / ∏ j ∈ Finset.range N, ((((n + 1) + j : ℕ) : ℝ) + c))
              / ((n : ℝ) + c) := by
            exact (div_le_div_iff_of_pos_right hnc).mpr (by rwa [hcast] at h2)
        _ = ((((n + (N + 1) : ℕ) : ℝ) + c))
              / ((((n : ℝ) + c))
                * ∏ j ∈ Finset.range N, ((((n + 1) + j : ℕ) : ℝ) + c)) := by
            rw [div_div, mul_comm]

/-- The product `∏_{j<N} (j+c)` is at least `c^N`. -/
lemma prod_ge_pow (hc : 2 ≤ c) (N : ℕ) :
    ((c : ℝ) ^ N) ≤ ∏ j ∈ Finset.range N, ((j : ℝ) + c) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ, pow_succ]
      apply mul_le_mul ih _ (by positivity)
        (Finset.prod_nonneg (fun j _ => by positivity))
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hc' : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
      linarith

/-- **The Mixed-Root Master Theorem.** For all `c ≥ 2`, the depth-`N`
truncations of the alternating sqrt/cbrt nested radical converge to `c`. -/
theorem mixed_root_master (hc : 2 ≤ c) :
    Tendsto (fun N : ℕ => mS c 0 N) atTop (𝓝 (c : ℝ)) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * ((1 / 2 : ℝ) ^ N)) atTop (𝓝 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_lt_one 1 (r := (1 / 2 : ℝ))
      (by norm_num) (by norm_num)
    simpa using h
  have h2 : Tendsto (fun N : ℕ => (c : ℝ) * ((1 / 2 : ℝ) ^ N)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have h3 : Tendsto (fun N : ℕ => (c : ℝ) * ((1 / 2 : ℝ) ^ N))
        atTop (𝓝 ((c : ℝ) * 0)) :=
      tendsto_const_nhds.mul h
    simpa using h3
  have h3 : Tendsto (fun N : ℕ => ((N : ℝ) + c) / (2 : ℝ) ^ N) atTop (𝓝 0) := by
    have h4 : (fun N : ℕ => ((N : ℝ) + c) / (2 : ℝ) ^ N)
        = (fun N : ℕ => (N : ℝ) * ((1 / 2 : ℝ) ^ N)
            + (c : ℝ) * ((1 / 2 : ℝ) ^ N)) := by
      ext N
      have h5 : ((1 / 2 : ℝ) ^ N) = 1 / (2 : ℝ) ^ N := by
        rw [div_pow, one_pow]
      rw [h5, ← add_mul, mul_one_div]
    rw [h4]
    have h5 : Tendsto (fun N : ℕ => (N : ℝ) * ((1 / 2 : ℝ) ^ N)
          + (c : ℝ) * ((1 / 2 : ℝ) ^ N))
        atTop (𝓝 (0 + 0)) := h1.add h2
    simpa using h5
  have hK0 : Tendsto (fun N : ℕ => ((N : ℝ) + c) / (c : ℝ) ^ N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) h3
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by exact_mod_cast hc) N
  have hbound : ∀ N : ℕ,
      |mS c 0 N - (c : ℝ)| ≤ ((N : ℝ) + c) / (c : ℝ) ^ N := by
    intro N
    have hd1 : mDelta c 0 N ≤ ((N : ℝ) + c) / (c : ℝ) ^ N := by
      have h1 := mDelta_iter hc 0 N
      simp only [Nat.zero_add] at h1
      have h2 : (c : ℝ) ^ N ≤ ∏ j ∈ Finset.range N, ((j : ℝ) + c) :=
        prod_ge_pow hc N
      have h3 : ((N : ℝ) + c) / ∏ j ∈ Finset.range N, ((j : ℝ) + c)
          ≤ ((N : ℝ) + c) / (c : ℝ) ^ N := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) h2
      exact le_trans h1 h3
    have hde : mDelta c 0 N = (c : ℝ) - mS c 0 N := by
      simp only [mDelta, mtail, Nat.cast_zero, zero_add]
    have hnn : 0 ≤ mDelta c 0 N := mDelta_nonneg hc 0 N
    rw [hde] at hnn hd1
    have habs : |mS c 0 N - (c : ℝ)| = (c : ℝ) - mS c 0 N := by
      have hneg : mS c 0 N - (c : ℝ) = -((c : ℝ) - mS c 0 N) := by ring
      rw [hneg, abs_neg, abs_of_nonneg hnn]
    rw [habs]
    exact hd1
  have hlow : ∀ N : ℕ,
      (c : ℝ) - ((N : ℝ) + c) / (c : ℝ) ^ N ≤ mS c 0 N := by
    intro N
    have h := hbound N
    rw [abs_le] at h
    linarith [h.1]
  have hglow : Tendsto (fun N : ℕ => (c : ℝ) - ((N : ℝ) + c) / (c : ℝ) ^ N)
      atTop (𝓝 ((c : ℝ) - 0)) :=
    tendsto_const_nhds.sub hK0
  have hglow' : Tendsto (fun N : ℕ => (c : ℝ) - ((N : ℝ) + c) / (c : ℝ) ^ N)
      atTop (𝓝 (c : ℝ)) := by simpa using hglow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hglow' tendsto_const_nhds hlow
    (fun N => by
      have hle := mS_le hc 0 N
      have htail : mtail c 0 = (c : ℝ) := by simp [mtail]
      rw [htail] at hle
      exact hle)

#print axioms mixed_root_master

end MixedRootMaster

end
