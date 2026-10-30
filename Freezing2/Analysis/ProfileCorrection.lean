module

public import Freezing2.Analysis.ProfileIntegrals
public import Freezing2.Analysis.ReciprocalCorrection

/-!
# The reciprocal population correction tends to zero

This is equation `eq:lemme hnalpha convergence somme vers 0`, used in parts
(iii) and (iv) of Lemma `lem:hnalpha`. The one-based sum is related exactly to
the floor-mesh integral, including the two endpoint terms. The analytic proof
uses the contraction and dominated-convergence argument of
`ReciprocalCorrection` instead of the manuscript's uniform-integrability route.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Freezing2

/-- The nonnegative scalar correction at a time in a surviving driving walk. -/
noncomputable def reciprocalErrorAt (x : ℕ → ℤ) (i : ℕ) : ℝ :=
  ((activeCount x i : ℝ) * ((activeCount x i : ℝ) + 1))⁻¹

/-- The source's one-based sum of reciprocal population corrections. -/
noncomputable def reciprocalErrorTotal (x : ℕ → ℕ → ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, reciprocalErrorAt (x n) (i + 1)

theorem reciprocalErrorAt_nonneg {x : ℕ → ℤ} {n i : ℕ}
    (hx : SurvivesThrough x n) (hi : i ≤ n) : 0 ≤ reciprocalErrorAt x i := by
  have hs : (0 : ℝ) < activeCount x i := by exact_mod_cast hx i hi
  unfold reciprocalErrorAt
  positivity

theorem reciprocalErrorAt_le_one {x : ℕ → ℤ} {n i : ℕ}
    (hx : SurvivesThrough x n) (hi : i ≤ n) : reciprocalErrorAt x i ≤ 1 := by
  have hs : (1 : ℝ) ≤ activeCount x i := by
    have hs := hx i hi
    have hs' : (1 : ℤ) ≤ activeCount x i := by omega
    exact_mod_cast hs'
  have hd : 1 ≤ (activeCount x i : ℝ) * ((activeCount x i : ℝ) + 1) := by
    nlinarith
  simpa only [reciprocalErrorAt, one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd

/-- Integrating the scalar correction gives precisely the zero-based finite sum. -/
theorem integral_reciprocalCorrection_profile {x : ℕ → ℕ → ℤ} {α : ℝ}
    (hx : AdmissibleArray x) {n : ℕ} (hn : 0 < n) :
    (∫ t, reciprocalCorrection ((n : ℝ) ^ α) (reciprocalProfile x α n t)
      ∂profileMeasure) =
      ((n : ℝ) ^ α / n) * ∑ i ∈ Finset.range n, reciprocalErrorAt (x n) i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn' _
  have he : (fun t ↦ reciprocalCorrection ((n : ℝ) ^ α) (reciprocalProfile x α n t))
      =ᵐ[profileMeasure]
      stepProfile (fun i ↦ (n : ℝ) ^ α * reciprocalErrorAt (x n) i) n := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hi : ⌊(n : ℝ) * t⌋₊ ≤ n := by
      apply Nat.floor_le_of_le
      nlinarith [ht.2]
    have hs : (0 : ℝ) < activeCount (x n) ⌊(n : ℝ) * t⌋₊ := by
      exact_mod_cast (hx n).2 _ hi
    simp only [reciprocalProfile, stepProfile, reciprocalErrorAt]
    rw [reciprocalCorrection_div hc hs]
    ring
  rw [integral_congr_ae he]
  change (∫ t in Set.Icc (0 : ℝ) 1,
    stepProfile (fun i ↦ (n : ℝ) ^ α * reciprocalErrorAt (x n) i) n t) = _
  rw [integral_stepProfile_Icc _ hn, ← Finset.mul_sum]
  ring

/-- The scalar correction for the floor-mesh reciprocal profile tends to zero
in integral. This needs only the positive exponent and L¹ convergence. -/
theorem tendsto_integral_profile_correction {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : 0 < α) (hL1 : HasL1ReciprocalProfile x α g)
    (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ ∫ t, reciprocalCorrection ((n : ℝ) ^ α)
      (reciprocalProfile x α n t) ∂profileMeasure) atTop (𝓝 0) := by
  let c : ℕ → ℝ := fun n : ℕ ↦ if n = 0 then 1 else (n : ℝ) ^ α
  have hcpos (n : ℕ) : 0 < c n := by
    dsimp [c]
    split_ifs with hn
    · norm_num
    · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  have hc_eq : c =ᶠ[atTop] (fun n : ℕ ↦ (n : ℝ) ^ α) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [c, Nat.ne_of_gt hn]
  have hc : Tendsto c atTop atTop :=
    ((tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr' hc_eq.symm
  have h := tendsto_integral_reciprocalCorrection_of_l1
    (fun n : ℕ ↦ integrable_reciprocalProfile x α n) hL1.1
    (fun n : ℕ ↦ reciprocalProfile_nonneg_ae hx α n) hg hcpos hc hL1.2
  apply h.congr'
  filter_upwards [hc_eq] with n hn
  rw [hn]

/-- Equation `eq:lemme hnalpha convergence somme vers 0` with its original
one-based indexing and normalization `n^α/n`. -/
theorem tendsto_reciprocalErrorTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g)
    (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α / n) * reciprocalErrorTotal x n) atTop (𝓝 0) := by
  have hc := tendsto_integral_profile_correction hx hα0 hL1 hg
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α / n) atTop (𝓝 0) := by
    simpa using tendsto_profile_spike_bound hα1 (by norm_num : (0 : ℝ) < 2)
  have hnonneg (n : ℕ) : 0 ≤ ((n : ℝ) ^ α / n) * reciprocalErrorTotal x n := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i hi ↦ reciprocalErrorAt_nonneg (hx n).2
      (by have := Finset.mem_range.mp hi; omega)
  refine squeeze_zero' (Eventually.of_forall hnonneg) ?_ (by simpa using hc.add hsmall)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [integral_reciprocalCorrection_profile hx hn]
  have hs := sum_range_shift_eq (reciprocalErrorAt (x n)) n
  have he₀ := reciprocalErrorAt_nonneg (hx n).2 (Nat.zero_le n)
  have he₁ := reciprocalErrorAt_le_one (hx n).2 (le_refl n)
  have hsum : reciprocalErrorTotal x n ≤
      (∑ i ∈ Finset.range n, reciprocalErrorAt (x n) i) + 1 := by
    unfold reciprocalErrorTotal
    linarith
  have hcoef : 0 ≤ (n : ℝ) ^ α / n := by positivity
  calc
    _ ≤ ((n : ℝ) ^ α / n) *
        ((∑ i ∈ Finset.range n, reciprocalErrorAt (x n) i) + 1) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = _ := by ring

/-- The equivalent power normalization used in Lemma `lem:hnalpha`. -/
theorem tendsto_rpow_mul_reciprocalErrorTotal {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g)
    (hg : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α - 1) * reciprocalErrorTotal x n) atTop (𝓝 0) := by
  apply (tendsto_reciprocalErrorTotal hx hα0 hα1 hL1 hg).congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n), Real.rpow_one]

/-- Every interval correction from the weighted up/down identity is bounded by
one common nonnegative sum over the full horizon. This is uniform in both
interval endpoints. -/
theorem driver_reciprocalErrorSum_le_total {x : ℕ → ℕ → ℤ}
    (hx : AdmissibleArray x) {N a n : ℕ} (han : a + n ≤ N) :
    reciprocalErrorSum (fun i ↦ (activeCount (x N) i).toNat) a n ≤
      reciprocalErrorTotal x N := by
  unfold reciprocalErrorSum reciprocalErrorTotal
  apply Finset.sum_le_sum_of_injOn (fun i ↦ a + i)
  · intro i _ j _ hij
    exact Nat.add_left_cancel hij
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i hi
    have hiN : a + i + 1 ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    have hcast : ((activeCount (x N) (a + i + 1)).toNat : ℝ) =
        (activeCount (x N) (a + i + 1) : ℝ) := by
      exact_mod_cast activeCount_nat_cast (x N) (hx N).2 hiN
    split_ifs
    · simp only [hcast, reciprocalErrorAt, le_refl]
    · exact reciprocalErrorAt_nonneg (hx N).2 hiN
  · intro j hj _
    exact reciprocalErrorAt_nonneg (hx N).2 (by
      have := Finset.mem_range.mp hj
      omega)

end Freezing2
