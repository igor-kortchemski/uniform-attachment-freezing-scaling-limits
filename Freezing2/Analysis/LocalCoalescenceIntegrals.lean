module

public import Freezing2.Analysis.SquareCorrection
public import Freezing2.Analysis.MeshIntervals
public import Freezing2.Discrete.CoalescenceEstimates

/-!
# Exact local integrals for the coalescence sums

The one-based interval `(a,a+m]` consists of mesh cells indexed by
`a+1,…,a+m`. Its integral therefore runs from `(a+1)/N` to `(a+m+1)/N`.
No endpoint is silently moved to the source's comparison interval: controlling
that shift is a separate asymptotic obligation.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Freezing2

/-- A shifted range sum is the corresponding half-open interval sum. -/
theorem sum_Ico_one_based_interval (v : ℕ → ℝ) (a m : ℕ) :
    (∑ i ∈ Finset.Ico (a + 1) (a + m + 1), v i) =
      ∑ i ∈ Finset.range m, v (a + i + 1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : a + m + 1 - (a + 1) = m := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- Exact integration formula with precisely the cells of `(a,a+m]`. -/
theorem integral_stepProfile_one_based_interval (v : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (a m : ℕ) :
    (∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
      stepProfile v N t) = (1 / (N : ℝ)) * ∑ i ∈ Finset.range m, v (a + i + 1) := by
  have h := integral_stepProfile_meshInterval v hN (a + 1) (a + m + 1)
  rw [sum_Ico_one_based_interval] at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The positive-shift coalescence sum is exactly its shifted mesh integral.
This algebraic identity is valid even without survival assumptions. -/
theorem integral_shiftedSquareProfile_one_based {x : ℕ → ℕ → ℤ} {α : ℝ}
    {N : ℕ} (hN : 0 < N) (a m : ℕ) :
    (∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
      shiftedSquareProfile x α N t) =
      (((N : ℝ) ^ α) ^ 2 / N) * coalescencePlusSum (x N) a m := by
  change (∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
    stepProfile (fun i ↦ ((N : ℝ) ^ α) ^ 2 /
      ((activeCount (x N) i : ℝ) * ((activeCount (x N) i : ℝ) + 1))) N t) = _
  rw [integral_stepProfile_one_based_interval _ hN]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  unfold coalescencePlusSum
  ring

/-- The cubic correction at a reciprocal population is its finite denominator
`S²(S+1)`, with all factors strictly positive. -/
theorem squareCorrection_div_eq_inv {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    squareCorrection c (c / s) = c ^ 2 * (s ^ 2 * (s + 1))⁻¹ := by
  have hcne := ne_of_gt hc
  have hsne := ne_of_gt hs
  have hs1 : s + 1 ≠ 0 := by positivity
  unfold squareCorrection
  field_simp

/-- Exact correction-sum integral. The upper endpoint is discarded only using
its zero Lebesgue measure, so survival through `a+m` suffices. -/
theorem integral_squareCorrection_profile_one_based {x : ℕ → ℕ → ℤ} {α : ℝ}
    (hx : AdmissibleArray x) {N a m : ℕ} (hN : 0 < N) (ham : a + m ≤ N) :
    (∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
      squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) =
      (((N : ℝ) ^ α) ^ 2 / N) * coalescenceErrorSum (x N) a m := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN' _
  have he : (fun t ↦ squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t))
      =ᵐ[volume.restrict (Ico (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N))]
      stepProfile (fun i ↦ ((N : ℝ) ^ α) ^ 2 *
        (((activeCount (x N) i : ℝ) ^ 2) * ((activeCount (x N) i : ℝ) + 1))⁻¹) N := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    have hi : ⌊(N : ℝ) * t⌋₊ ≤ N := by
      apply Nat.lt_succ_iff.mp
      apply (Nat.floor_lt' (Nat.succ_ne_zero N)).mpr
      have htop : ((a : ℝ) + m) ≤ N := by exact_mod_cast ham
      have hlt := (lt_div_iff₀ hN').mp ht.2
      push_cast
      nlinarith
    exact squareCorrection_div_eq_inv hc (activeCount_real_pos hx N hi)
  have hint :
      (∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
        squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t)) =
      ∫ t in Icc (((a : ℝ) + 1) / N) (((a : ℝ) + m + 1) / N),
        stepProfile (fun i ↦ ((N : ℝ) ^ α) ^ 2 *
          (((activeCount (x N) i : ℝ) ^ 2) * ((activeCount (x N) i : ℝ) + 1))⁻¹) N t := by
    rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
    exact integral_congr_ae he
  rw [hint, integral_stepProfile_one_based_interval _ hN, ← Finset.mul_sum]
  unfold coalescenceErrorSum
  ring

/-- The cubic correction is nonnegative at every time in the surviving horizon. -/
theorem squareCorrection_profile_nonneg {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) (α : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t) :=
  squareCorrection_nonneg (Real.rpow_pos_of_pos (by exact_mod_cast hN) _)
    (reciprocalProfile_nonneg hx α N ht)

/-- The same positivity statement on any fixed closed subinterval. -/
theorem ae_nonneg_squareCorrection_profile {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) (α : ℝ) {N : ℕ} (hN : 0 < N)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      0 ≤ squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact squareCorrection_profile_nonneg hx α hN ⟨ha.trans ht.1, ht.2.trans hb⟩

/-- The concrete correction profile is integrable on every closed subinterval. -/
theorem integrableOn_squareCorrection_profile {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) (α : ℝ) {N : ℕ} (hN : 0 < N)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    IntegrableOn (fun t ↦ squareCorrection ((N : ℝ) ^ α) (reciprocalProfile x α N t))
      (Icc a b) volume := by
  apply integrable_squareCorrection
    (integrableOn_reciprocalProfile x α N ha hb).aestronglyMeasurable
    (integrableOn_sq_reciprocalProfile x α N ha hb)
  · rw [← profileMeasure_restrict_Icc ha hb]
    exact ae_restrict_of_ae (reciprocalProfile_nonneg_ae hx α N)
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

end Freezing2
