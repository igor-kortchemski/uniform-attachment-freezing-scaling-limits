module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The numerical constants in the one-block tightness estimate

Exact ceiling and square-root estimates for source N14/U33/U35. The repaired
expectation denominator `m - M_n` permits these finite inequalities without
an additional asymptotic subtraction of one.
-/

@[expose] public section

namespace Freezing2

/-- The manuscript's block length, with a natural ceiling. -/
noncomputable def tightnessBlockLength (M : ℝ) (n k : ℕ) : ℕ :=
  4 * ⌈M * n / Real.sqrt k⌉₊

theorem tightnessBlockLength_lower (M : ℝ) (n k : ℕ) :
    4 * M * n / Real.sqrt k ≤ (tightnessBlockLength M n k : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil (M * n / Real.sqrt k))
    (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [tightnessBlockLength, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc,
    mul_assoc] using h

/-- A single explicit threshold supplies the source's sufficiently large
sample size, independently of the horizon and number of marked vertices. -/
theorem exists_tightness_sample_threshold {M : ℝ} (hM : 0 < M) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → 0 < k ∧ 12 ≤ M * Real.sqrt k := by
  refine ⟨max 1 ⌈(12 / M) ^ 2⌉₊, le_max_left _ _, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hc : ⌈(12 / M) ^ 2⌉₊ ≤ k := (le_max_right _ _).trans hk
  have hsq : (12 / M) ^ 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hc)
  have hs : 12 / M ≤ Real.sqrt k :=
    (Real.le_sqrt (by positivity) (Nat.cast_nonneg k)).mpr hsq
  exact ⟨by omega, by simpa only [mul_comm] using (div_le_iff₀ hM).mp hs⟩

/-- The population-square numerator is controlled by the actual block gap.
The original condition `k³ ≤ n` is stronger than the `k ≤ n` used here. -/
theorem tightnessBlockLength_gap {M : ℝ} (hM : 0 < M) {n k : ℕ}
    (hk : 0 < k) (hkn : k ≤ n) :
    3 * (M * Real.sqrt n) ^ 2 ≤
      (M * Real.sqrt k) * ((tightnessBlockLength M n k : ℝ) - M * Real.sqrt n) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkr
  have hsn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hroots : Real.sqrt k ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  have hprod : Real.sqrt k * Real.sqrt n ≤ (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hroots hsn
    nlinarith [Real.sq_sqrt hnr]
  have hm := (div_le_iff₀ hs).mp (tightnessBlockLength_lower M n k)
  have hm' := mul_le_mul_of_nonneg_left hm hM.le
  have hp' := mul_le_mul_of_nonneg_left hprod (sq_nonneg M)
  have hb : (M * Real.sqrt n) ^ 2 = M ^ 2 * n := by
    rw [mul_pow, Real.sq_sqrt hnr]
  rw [hb]
  nlinarith

/-- The source coefficient follows uniformly from the block gap once
`M sqrt(k) ≥ 12`, for every positive number `K` of other marked vertices. -/
theorem one_block_isolation_numeric_bound {B a m : ℝ} (hB : 0 < B)
    (ha : 12 ≤ a) (hgap : 3 * B ^ 2 ≤ a * (m - B))
    {K : ℕ} (hK : 0 < K) :
    (1 + 2 * B ^ 2 / (m - B)) / ((K : ℝ) + 1) ≤ 3 * a / (4 * K) := by
  have ha0 : 0 < a := by linarith
  have hd : 0 < m - B := by
    by_contra h
    have hp := mul_nonpos_of_nonneg_of_nonpos ha0.le (le_of_not_gt h)
    nlinarith [sq_pos_of_pos hB]
  have ht : 2 * B ^ 2 / (m - B) ≤ 2 * a / 3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) + 1)).mpr
  apply (le_trans (by linarith : 1 + 2 * B ^ 2 / (m - B) ≤ 1 + 2 * a / 3))
  have he : (3 * a / (4 * (K : ℝ))) * ((K : ℝ) + 1) =
      3 * a / 4 + 3 * a / (4 * K) := by
    field_simp
  rw [he]
  have hnonneg : 0 ≤ 3 * a / (4 * (K : ℝ)) := by positivity
  linarith

end Freezing2
