module

public import Freezing2.Discrete.Estimates

/-!
# Finite coalescence-weight estimates for signed population walks

All sums use the original signs and integer populations on `(a,a+m]`.
The exact crossing-potential identity gives the boundary term, and a scalar
reciprocal estimate controls replacing `S(S−1)` by `S(S+1)` at upward steps.
These are the finite, uniform ingredients of Lemma `lem:hnalpha(v)`.
-/

@[expose] public section

open scoped BigOperators

namespace Freezing2

/-- Coalescence hazard at upward steps in `(a,a+m]`. -/
noncomputable def coalescenceUpSum (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, if x (a + i + 1) = 1 then
    ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) - 1))⁻¹ else 0

/-- Upward-step weights with the positive shift in the denominator. -/
noncomputable def coalescenceUpPlusSum (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, if x (a + i + 1) = 1 then
    ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹ else 0

/-- Downward-step weights with the positive shift in the denominator. -/
noncomputable def coalescenceDownPlusSum (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, if x (a + i + 1) = -1 then
    ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹ else 0

/-- All positive-shift weights in the interval. -/
noncomputable def coalescencePlusSum (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m,
    ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹

/-- The positive reciprocal-square correction in the interval. -/
noncomputable def coalescenceErrorSum (x : ℕ → ℤ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m,
    (((activeCount x (a + i + 1) : ℝ) ^ 2) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹

/-- Natural and integer population representations have identical real casts
throughout survival. -/
theorem activeCount_toNat_real_cast (x : ℕ → ℤ) {N i : ℕ}
    (hs : SurvivesThrough x N) (hi : i ≤ N) :
    ((activeCount x i).toNat : ℝ) = (activeCount x i : ℝ) := by
  exact_mod_cast activeCount_nat_cast x hs hi

/-- The signed walk splits the positive-shift sum exactly into its two signs. -/
theorem coalescence_up_plus_add_down_plus (x : ℕ → ℤ) (hx : IsSigned x) (a m : ℕ) :
    coalescenceUpPlusSum x a m + coalescenceDownPlusSum x a m = coalescencePlusSum x a m := by
  unfold coalescenceUpPlusSum coalescenceDownPlusSum coalescencePlusSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases hx (a + i + 1) (by omega) with hi | hi <;> simp [hi]

/-- Exact signed-walk counterpart of the coalescence crossing-potential formula. -/
theorem coalescence_signed_pairing (x : ℕ → ℤ) (hx : IsSigned x) {N a m : ℕ}
    (hs : SurvivesThrough x N) (ham : a + m ≤ N) :
    coalescenceUpSum x a m - coalescenceDownPlusSum x a m =
      (activeCount x a : ℝ)⁻¹ - (activeCount x (a + m) : ℝ)⁻¹ := by
  have h := coalescence_crossing_balance (fun j ↦ (activeCount x j).toNat) a m
    (fun i hi ↦ activeCount_nat_steps x hx hs (by omega : a + i < N))
    (activeCount_nat_pos x hs (by omega : a ≤ N)) (activeCount_nat_pos x hs ham)
  have hu : coalescenceUpSum x a m =
      ∑ i ∈ Finset.range m,
        if (activeCount x (a + i + 1)).toNat = (activeCount x (a + i)).toNat + 1 then
          (((activeCount x (a + i + 1)).toNat : ℝ) *
            (((activeCount x (a + i + 1)).toNat : ℝ) - 1))⁻¹ else 0 := by
    unfold coalescenceUpSum
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [activeCount_nat_up_iff x hs (by omega : a + i < N),
      activeCount_toNat_real_cast x hs (by omega : a + i + 1 ≤ N)]
  have hd : coalescenceDownPlusSum x a m =
      ∑ i ∈ Finset.range m,
        if (activeCount x (a + i)).toNat = (activeCount x (a + i + 1)).toNat + 1 then
          (((activeCount x (a + i + 1)).toNat : ℝ) *
            (((activeCount x (a + i + 1)).toNat : ℝ) + 1))⁻¹ else 0 := by
    unfold coalescenceDownPlusSum
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [activeCount_nat_down_iff x hs (by omega : a + i < N),
      activeCount_toNat_real_cast x hs (by omega : a + i + 1 ≤ N)]
  rw [hu, hd, h, activeCount_toNat_real_cast x hs (by omega : a ≤ N),
    activeCount_toNat_real_cast x hs ham]

/-- Scalar correction bound at an upward step from a positive population. -/
theorem coalescence_weight_correction_bound {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ (s * (s - 1))⁻¹ - (s * (s + 1))⁻¹ ∧
      (s * (s - 1))⁻¹ - (s * (s + 1))⁻¹ ≤ 4 * (s ^ 2 * (s + 1))⁻¹ := by
  have hs0 : 0 < s := by linarith
  have hsminus : 0 < s - 1 := by linarith
  have hsplus : 0 < s + 1 := by linarith
  have he : (s * (s - 1))⁻¹ - (s * (s + 1))⁻¹ =
      (2 * s / (s - 1)) * (s ^ 2 * (s + 1))⁻¹ := by
    field_simp
    ring
  have hcoef : 2 * s / (s - 1) ≤ 4 := (div_le_iff₀ hsminus).mpr (by linarith)
  rw [he]
  exact ⟨by positivity, mul_le_mul_of_nonneg_right hcoef (by positivity)⟩

/-- An actual upward step from a surviving population ends at size at least two. -/
theorem activeCount_ge_two_of_up (x : ℕ → ℤ) {N j : ℕ}
    (hs : SurvivesThrough x N) (hj : j < N) (hup : x (j + 1) = 1) :
    (2 : ℝ) ≤ activeCount x (j + 1) := by
  have hprev := hs j (Nat.le_of_lt hj)
  have hstep := activeCount_succ x j
  have h : (2 : ℤ) ≤ activeCount x (j + 1) := by omega
  exact_mod_cast h

/-- The difference between the two upward-step weights is nonnegative and
bounded by four times the full reciprocal-square correction. -/
theorem coalescence_up_sub_up_plus_bounds (x : ℕ → ℤ) {N a m : ℕ}
    (hs : SurvivesThrough x N) (ham : a + m ≤ N) :
    0 ≤ coalescenceUpSum x a m - coalescenceUpPlusSum x a m ∧
      coalescenceUpSum x a m - coalescenceUpPlusSum x a m ≤
        4 * coalescenceErrorSum x a m := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range m) :
      0 ≤ (if x (a + i + 1) = 1 then
        ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) - 1))⁻¹ else 0) -
        (if x (a + i + 1) = 1 then
        ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹ else 0) ∧
      (if x (a + i + 1) = 1 then
        ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) - 1))⁻¹ else 0) -
        (if x (a + i + 1) = 1 then
        ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹ else 0) ≤
        4 * (((activeCount x (a + i + 1) : ℝ) ^ 2) *
          ((activeCount x (a + i + 1) : ℝ) + 1))⁻¹ := by
    have hi' := Finset.mem_range.mp hi
    have hj : a + i < N := by omega
    by_cases hup : x (a + i + 1) = 1
    · simpa only [hup, ite_true] using
        coalescence_weight_correction_bound (activeCount_ge_two_of_up x hs hj hup)
    · have hpop : (0 : ℝ) < activeCount x (a + i + 1) := by
        exact_mod_cast hs (a + i + 1) (by omega)
      simp only [hup, ite_false, sub_zero]
      exact ⟨le_rfl, by positivity⟩
  unfold coalescenceUpSum coalescenceUpPlusSum coalescenceErrorSum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact ⟨Finset.sum_nonneg (fun i hi ↦ (hterm i hi).1),
    Finset.sum_le_sum (fun i hi ↦ (hterm i hi).2)⟩

/-- Uniform finite-interval estimate used in `hnalpha(v)`, with explicit
endpoint terms and an error sum independent of the signs. -/
theorem coalescence_uniform_pairing_bound (x : ℕ → ℤ) (hx : IsSigned x) {N a m : ℕ}
    (hs : SurvivesThrough x N) (ham : a + m ≤ N) :
    |coalescenceUpSum x a m - coalescencePlusSum x a m / 2| ≤
      ((activeCount x a : ℝ)⁻¹ + (activeCount x (a + m) : ℝ)⁻¹) / 2 +
        2 * coalescenceErrorSum x a m := by
  have hp := coalescence_signed_pairing x hx hs ham
  have hsplit := coalescence_up_plus_add_down_plus x hx a m
  have he := coalescence_up_sub_up_plus_bounds x hs ham
  have ha : (0 : ℝ) ≤ (activeCount x a : ℝ)⁻¹ := by
    apply inv_nonneg.mpr
    exact_mod_cast (hs a (by omega)).le
  have hb : (0 : ℝ) ≤ (activeCount x (a + m) : ℝ)⁻¹ := by
    apply inv_nonneg.mpr
    exact_mod_cast (hs (a + m) ham).le
  apply abs_le.mpr
  constructor <;> linarith

end Freezing2
