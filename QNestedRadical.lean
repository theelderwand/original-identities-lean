/-
# q-Nested-Radical Master Theorem, machine-checked in Lean 4

**Theorem.** Let `m ≥ 2`, `c > 0`, `0 < q < 1`, and `0 < B < 1 / (1 + c)`.
Define

    A n = (1 + c·q^n)^m − B·(1 + c·q^{n+1}).

Then the depth-`N` truncations of the nested `m`-th root

    1 + c = m√(A 0 + B·m√(A 1 + B·m√(A 2 + ⋯)))

converge to `1 + c` as `N → ∞`.

**Proof idea.** The exact tails are `t n = 1 + c·q^n`, since
`(t n)^m = A n + B·t (n+1)`. Writing `δ(n,k) = t n − S(n,k)` for the
truncation error, the factorisation `x^m − y^m = (x − y)·S` (geometric sum)
gives `δ(n,k+1) = B·δ(n+1,k) / S` with `S ≥ (t n)^{m−1} ≥ 1`, hence
`δ(n,k+1) ≤ B·δ(n+1,k)`. Iterating, `δ(0,N) ≤ B^N·(1+c) → 0` since `B < 1`.

**What is proven here.** The full master theorem for all `m ≥ 2`,
`c > 0`, `0 < q < 1`, `0 < B < 1/(1+c)`. The `m`-th root is `Real.rpow`
with exponent `1/m`.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Algebra.Order.Field

open Filter Topology

noncomputable section

namespace QNestedRadical

variable {c q B : ℝ} {m : ℕ}

/-- The `m`-th root, via `Real.rpow`. -/
def qroot (m : ℕ) (x : ℝ) : ℝ := x ^ ((m : ℝ)⁻¹)

lemma qroot_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ qroot m x :=
  Real.rpow_nonneg hx _

lemma qroot_pow (hm : m ≠ 0) (x : ℝ) (hx : 0 ≤ x) :
    (qroot m x) ^ m = x := by
  simp only [qroot]
  rw [← Real.rpow_natCast _ m, ← Real.rpow_mul hx,
    inv_mul_cancel₀ (by exact_mod_cast hm : (m : ℝ) ≠ 0)]
  exact Real.rpow_one x

/-- `A n = (1 + c·q^n)^m − B·(1 + c·q^{n+1})`. -/
def qA (c q B : ℝ) (m : ℕ) (n : ℕ) : ℝ :=
  (1 + c * q ^ n) ^ m - B * (1 + c * q ^ (n + 1))

/-- The exact tail at level `n`: `t n = 1 + c·q^n`. -/
def qtail (c q : ℝ) (n : ℕ) : ℝ := 1 + c * q ^ n

/-- Depth-`k` truncation of the nested `m`-th root starting at level `n`. -/
def qS (c q B : ℝ) (m : ℕ) : ℕ → ℕ → ℝ
  | n, 0 => qroot m (qA c q B m n)
  | n, k + 1 => qroot m (qA c q B m n + B * qS c q B m (n + 1) k)

/-- The truncation error at level `n`, depth `k`. -/
def qDelta (c q B : ℝ) (m : ℕ) (n k : ℕ) : ℝ := qtail c q n - qS c q B m n k

/-- The telescoping identity: `(t n)^m = A n + B·t (n+1)`. -/
lemma key_identity (n : ℕ) :
    (qtail c q n) ^ m = qA c q B m n + B * qtail c q (n + 1) := by
  simp only [qA, qtail]
  ring

lemma qtail_ge_one (hc : 0 < c) (hq0 : 0 < q) (n : ℕ) : 1 ≤ qtail c q n := by
  simp only [qtail]
  have h1 : (0 : ℝ) < q ^ n := pow_pos hq0 n
  have h2 : (0 : ℝ) < c * q ^ n := mul_pos hc h1
  linarith

lemma qtail_pos (hc : 0 < c) (hq0 : 0 < q) (n : ℕ) : 0 < qtail c q n :=
  lt_of_lt_of_le zero_lt_one (qtail_ge_one hc hq0 n)

/-- `A n > 0` whenever `0 < B < 1/(1+c)`. -/
lemma qA_pos (_hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n : ℕ) : 0 < qA c q B m n := by
  have h1 : (1 : ℝ) ≤ (1 + c * q ^ n) ^ m := by
    apply one_le_pow₀
    have h2 : (0 : ℝ) < c * q ^ n := mul_pos hc (pow_pos hq0 n)
    linarith
  have h2 : (1 : ℝ) ≤ 1 + c := by linarith
  have h3 : (1 : ℝ) + c * q ^ (n + 1) ≤ 1 + c := by
    have h4 : q ^ (n + 1) ≤ 1 := by
      apply pow_le_one₀ (le_of_lt hq0) (le_of_lt hq1)
    have h5 : c * q ^ (n + 1) ≤ c * 1 := mul_le_mul_of_nonneg_left h4 (le_of_lt hc)
    linarith
  have h6 : B * (1 + c * q ^ (n + 1)) < 1 := by
    have h7 : B * (1 + c * q ^ (n + 1)) ≤ B * (1 + c) := by
      apply mul_le_mul_of_nonneg_left h3 (le_of_lt hB0)
    have h8 : B * (1 + c) < 1 := by
      have h9 : (0 : ℝ) < 1 + c := by linarith
      have h10 := hB1
      rwa [lt_div_iff₀ h9] at h10
    exact lt_of_le_of_lt h7 h8
  simp only [qA]
  linarith

lemma qA_nonneg (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n : ℕ) : 0 ≤ qA c q B m n :=
  le_of_lt (qA_pos hm hc hq0 hq1 hB0 hB1 n)

lemma qS_nonneg (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n k : ℕ) :
    0 ≤ qS c q B m n k := by
  induction k generalizing n with
  | zero =>
      simp only [qS]
      exact qroot_nonneg _ (qA_nonneg hm hc hq0 hq1 hB0 hB1 n)
  | succ k ih =>
      simp only [qS]
      apply qroot_nonneg
      have h1 := qA_nonneg hm hc hq0 hq1 hB0 hB1 n
      have h2 := ih (n + 1)
      have h3 : (0 : ℝ) ≤ B * qS c q B m (n + 1) k :=
        mul_nonneg (le_of_lt hB0) h2
      linarith

/-- Every truncation is bounded above by the exact tail. -/
lemma qS_le (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n k : ℕ) :
    qS c q B m n k ≤ qtail c q n := by
  have hm0 : m ≠ 0 := by omega
  induction k generalizing n with
  | zero =>
      have harg : qA c q B m n ≤ (qtail c q n) ^ m := by
        have hkey := key_identity (c := c) (q := q) (B := B) (m := m) n
        have hB : (0 : ℝ) ≤ B * qtail c q (n + 1) :=
          mul_nonneg (le_of_lt hB0) (le_of_lt (qtail_pos hc hq0 (n + 1)))
        linarith
      have hpow : (qS c q B m n 0) ^ m ≤ (qtail c q n) ^ m := by
        have e1 : qS c q B m n 0 = qroot m (qA c q B m n) := rfl
        rw [e1, qroot_pow hm0 _ (qA_nonneg hm hc hq0 hq1 hB0 hB1 n)]
        exact harg
      exact le_of_pow_le_pow_left₀ hm0
        (le_of_lt (qtail_pos hc hq0 n)) hpow
  | succ k ih =>
      have h1 : qS c q B m (n + 1) k ≤ qtail c q (n + 1) := ih (n + 1)
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hB0)
      have harg : qA c q B m n + B * qS c q B m (n + 1) k ≤ (qtail c q n) ^ m := by
        have hkey := key_identity (c := c) (q := q) (B := B) (m := m) n
        linarith
      have hpow : (qS c q B m n (k + 1)) ^ m ≤ (qtail c q n) ^ m := by
        have e1 : qS c q B m n (k + 1)
            = qroot m (qA c q B m n + B * qS c q B m (n + 1) k) := rfl
        have harg_nonneg : (0 : ℝ) ≤ qA c q B m n + B * qS c q B m (n + 1) k := by
          have ha := qA_nonneg hm hc hq0 hq1 hB0 hB1 n
          have hb : (0 : ℝ) ≤ B * qS c q B m (n + 1) k :=
            mul_nonneg (le_of_lt hB0)
              (qS_nonneg hm hc hq0 hq1 hB0 hB1 (n + 1) k)
          linarith
        rw [e1, qroot_pow hm0 _ harg_nonneg]
        exact harg
      exact le_of_pow_le_pow_left₀ hm0
        (le_of_lt (qtail_pos hc hq0 n)) hpow

lemma qdelta_nonneg (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n k : ℕ) :
    0 ≤ qDelta c q B m n k :=
  sub_nonneg.mpr (qS_le hm hc hq0 hq1 hB0 hB1 n k)

/-- The geometric-sum denominator is at least `1`. -/
lemma geom_sum_ge_one (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n k : ℕ) :
    (1 : ℝ) ≤ ∑ i ∈ Finset.range m,
      (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i) := by
  have hm1 : m - 1 ∈ Finset.range m := by
    rw [Finset.mem_range]
    omega
  have hterms : ∀ i ∈ Finset.range m,
      (0 : ℝ) ≤ (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i) := by
    intro i _
    apply mul_nonneg (pow_nonneg (le_of_lt (qtail_pos hc hq0 n)) _)
    apply pow_nonneg
    exact qS_nonneg hm hc hq0 hq1 hB0 hB1 n (k + 1)
  have hsingle := Finset.single_le_sum hterms hm1
  have hval : (qtail c q n) ^ (m - 1) * (qS c q B m n (k + 1)) ^ (m - 1 - (m - 1))
      = (qtail c q n) ^ (m - 1) := by
    simp
  have hge : (1 : ℝ) ≤ (qtail c q n) ^ (m - 1) := by
    apply one_le_pow₀
    exact qtail_ge_one hc hq0 n
  rw [hval] at hsingle
  exact le_trans hge hsingle

/-- One step of error contraction. -/
lemma qdelta_step (hm : 2 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n k : ℕ) :
    qDelta c q B m n (k + 1) ≤ B * qDelta c q B m (n + 1) k := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : 1 ≤ m := by omega
  -- The two m-th powers.
  have hpowS : (qS c q B m n (k + 1)) ^ m
      = qA c q B m n + B * qS c q B m (n + 1) k := by
    have e1 : qS c q B m n (k + 1)
        = qroot m (qA c q B m n + B * qS c q B m (n + 1) k) := rfl
    have harg_nonneg : (0 : ℝ) ≤ qA c q B m n + B * qS c q B m (n + 1) k := by
      have ha := qA_nonneg hm1 hc hq0 hq1 hB0 hB1 n
      have hb : (0 : ℝ) ≤ B * qS c q B m (n + 1) k :=
        mul_nonneg (le_of_lt hB0)
          (qS_nonneg hm1 hc hq0 hq1 hB0 hB1 (n + 1) k)
      linarith
    rw [e1, qroot_pow hm0 _ harg_nonneg]
  have hpowT : (qtail c q n) ^ m = qA c q B m n + B * qtail c q (n + 1) :=
    key_identity n
  -- The difference of m-th powers.
  have hdiff : (qtail c q n) ^ m - (qS c q B m n (k + 1)) ^ m
      = B * qDelta c q B m (n + 1) k := by
    rw [hpowT, hpowS]
    simp only [qDelta]
    ring
  -- Factor it via the geometric sum.
  have hfactor : (qtail c q n - qS c q B m n (k + 1))
        * (∑ i ∈ Finset.range m,
            (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i))
      = (qtail c q n) ^ m - (qS c q B m n (k + 1)) ^ m := by
    rw [mul_comm, geom_sum₂_mul]
  have hS : (1 : ℝ) ≤ ∑ i ∈ Finset.range m,
      (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i) :=
    geom_sum_ge_one hm1 hc hq0 hq1 hB0 hB1 n k
  have hdelta_nn : (0 : ℝ) ≤ qDelta c q B m n (k + 1) :=
    qdelta_nonneg hm1 hc hq0 hq1 hB0 hB1 n (k + 1)
  -- Conclude: δ * S = B * δ', S ≥ 1, δ ≥ 0, so δ ≤ B * δ'.
  have hprod : qDelta c q B m n (k + 1)
        * (∑ i ∈ Finset.range m,
            (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i))
      = B * qDelta c q B m (n + 1) k := by
    have h1 : qDelta c q B m n (k + 1) = qtail c q n - qS c q B m n (k + 1) := rfl
    rw [h1, hfactor, hdiff]
  have hle : qDelta c q B m n (k + 1)
      ≤ qDelta c q B m n (k + 1)
        * (∑ i ∈ Finset.range m,
            (qtail c q n) ^ i * (qS c q B m n (k + 1)) ^ (m - 1 - i)) :=
    le_mul_of_one_le_right hdelta_nn hS
  rw [hprod] at hle
  exact hle

/-- Iterating the contraction. -/
lemma qdelta_iter (hm : 2 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n : ℕ) (N : ℕ) :
    qDelta c q B m n N ≤ B ^ N * qDelta c q B m (n + N) 0 := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
      have h1 := qdelta_step hm hc hq0 hq1 hB0 hB1 n N
      have h2 := ih (n + 1)
      have hcast : (n + 1 + N : ℕ) = n + (N + 1) := by omega
      have hBnn : (0 : ℝ) ≤ B := le_of_lt hB0
      calc qDelta c q B m n (N + 1)
          ≤ B * qDelta c q B m (n + 1) N := h1
        _ ≤ B * (B ^ N * qDelta c q B m (n + (N + 1)) 0) :=
            mul_le_mul_of_nonneg_left (by rwa [hcast] at h2) hBnn
        _ = B ^ (N + 1) * qDelta c q B m (n + (N + 1)) 0 := by
            rw [pow_succ]; ring

/-- The bottom error is at most `1 + c`. -/
lemma qdelta_bottom (hm : 1 ≤ m) (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1)
    (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) (n : ℕ) :
    qDelta c q B m n 0 ≤ 1 + c := by
  have hs := qS_nonneg hm hc hq0 hq1 hB0 hB1 n 0
  have hq : q ^ n ≤ 1 := pow_le_one₀ (le_of_lt hq0) (le_of_lt hq1)
  simp only [qDelta, qtail]
  have h2 : c * q ^ n ≤ c := by
    have h3 : c * q ^ n ≤ c * 1 := mul_le_mul_of_nonneg_left hq (le_of_lt hc)
    linarith
  linarith

/-- **The q-Nested-Radical Master Theorem.** For all `m ≥ 2`, `c > 0`,
`0 < q < 1`, `0 < B < 1/(1+c)`, the depth-`N` truncations converge to `1 + c`. -/
theorem q_nested_radical_master (hm : 2 ≤ m) (hc : 0 < c) (hq0 : 0 < q)
    (hq1 : q < 1) (hB0 : 0 < B) (hB1 : B < 1 / (1 + c)) :
    Tendsto (fun N : ℕ => qS c q B m 0 N) atTop (𝓝 (1 + c)) := by
  have hm1 : 1 ≤ m := by omega
  have hB1' : B < 1 := by
    have h2 : (1 : ℝ) ≤ 1 + c := by linarith
    have h3 : (1 : ℝ) / (1 + c) ≤ 1 := by
      rw [div_le_one (by linarith : (0 : ℝ) < 1 + c)]
      exact h2
    exact lt_of_lt_of_le hB1 h3
  have hK0 : Tendsto (fun N : ℕ => B ^ N * (1 + c)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => B ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hB0) hB1'
    have h2 : Tendsto (fun N : ℕ => B ^ N * (1 + c)) atTop (𝓝 (0 * (1 + c))) :=
      h1.mul tendsto_const_nhds
    simpa using h2
  have hbound : ∀ N : ℕ,
      |qS c q B m 0 N - (1 + c)| ≤ B ^ N * (1 + c) := by
    intro N
    have hd1 : qDelta c q B m 0 N ≤ B ^ N * (1 + c) := by
      have h1 := qdelta_iter hm hc hq0 hq1 hB0 hB1 0 N
      simp only [Nat.zero_add] at h1
      have h2 := qdelta_bottom hm1 hc hq0 hq1 hB0 hB1 N
      have h3 : B ^ N * qDelta c q B m N 0 ≤ B ^ N * (1 + c) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt hB0) N)
      exact le_trans h1 h3
    have hde : qDelta c q B m 0 N = (1 + c) - qS c q B m 0 N := by
      simp only [qDelta, qtail]
      ring
    have hnn : 0 ≤ qDelta c q B m 0 N :=
      qdelta_nonneg hm1 hc hq0 hq1 hB0 hB1 0 N
    rw [hde] at hnn hd1
    have habs : |qS c q B m 0 N - (1 + c)| = (1 + c) - qS c q B m 0 N := by
      have hneg : qS c q B m 0 N - (1 + c) = -((1 + c) - qS c q B m 0 N) := by ring
      rw [hneg, abs_neg, abs_of_nonneg hnn]
    rw [habs]
    exact hd1
  have hlow : ∀ N : ℕ,
      (1 + c) - B ^ N * (1 + c) ≤ qS c q B m 0 N := by
    intro N
    have h := hbound N
    rw [abs_le] at h
    linarith [h.1]
  have hglow : Tendsto (fun N : ℕ => (1 + c) - B ^ N * (1 + c))
      atTop (𝓝 ((1 + c) - 0)) :=
    tendsto_const_nhds.sub hK0
  have hglow' : Tendsto (fun N : ℕ => (1 + c) - B ^ N * (1 + c))
      atTop (𝓝 (1 + c)) := by simpa using hglow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hglow' tendsto_const_nhds hlow
    (fun N => by
      have hle := qS_le hm1 hc hq0 hq1 hB0 hB1 0 N
      have htail : qtail c q 0 = 1 + c := by simp [qtail]
      rw [htail] at hle
      exact hle)

#print axioms q_nested_radical_master

end QNestedRadical

end
