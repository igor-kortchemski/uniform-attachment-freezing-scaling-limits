module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Exact integral and sum formulas for discrete profiles

The reciprocal profiles in Lemma `lem:hnalpha` are constant on intervals of
length `1/n`. This module records their exact integral, including the shift
between the sums indexed by `0,…,n−1` and `1,…,n`. The value at `t=1` is retained
in the definition and removed from integrals only through the null-measure
endpoint theorem for Lebesgue measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Freezing2

/-- A sequence sampled at `⌊n t⌋`, including its actual endpoint value at `t=1`. -/
noncomputable def stepProfile (v : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ := v ⌊(n : ℝ) * t⌋₊

/-- The `i`-th half-open interval of the mesh with spacing `1/n`. -/
def profileCell (n i : ℕ) : Set ℝ := Ico ((i : ℝ) / n) (((i : ℝ) + 1) / n)

/-- An arbitrary sequence gives a measurable step profile. -/
theorem measurable_stepProfile (v : ℕ → ℝ) (n : ℕ) : Measurable (stepProfile v n) :=
  (measurable_of_countable v).comp (measurable_const.mul measurable_id).nat_floor

/-- On a mesh cell, the floor really is its index. -/
theorem floor_eq_of_mem_profileCell {n i : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ profileCell n i) : ⌊(n : ℝ) * t⌋₊ = i := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht₀ : 0 ≤ t := (div_nonneg (Nat.cast_nonneg i) hn'.le).trans ht.1
  apply (Nat.floor_eq_iff (mul_nonneg hn'.le ht₀)).mpr
  constructor
  · have h := (div_le_iff₀ hn').mp ht.1
    simpa only [mul_comm t] using h
  · have h := (lt_div_iff₀ hn').mp ht.2
    simpa only [mul_comm t] using h

/-- Exact constant value on each mesh cell. -/
theorem stepProfile_eq_on_cell (v : ℕ → ℝ) {n i : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ profileCell n i) : stepProfile v n t = v i := by
  rw [stepProfile, floor_eq_of_mem_profileCell hn ht]

/-- The mesh cells partition `[0,1)` without adding or omitting endpoints. -/
theorem profileCells_union {n : ℕ} (hn : 0 < n) :
    (⋃ i ∈ Finset.range n, profileCell n i) = Ico 0 1 := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.mp hi
    refine ⟨(div_nonneg (Nat.cast_nonneg i) hn'.le).trans ht.1, ?_⟩
    exact ht.2.trans_le ((div_le_one hn').mpr hi')
  · intro ht
    have ht₀ : 0 ≤ (n : ℝ) * t := mul_nonneg hn'.le ht.1
    refine mem_iUnion₂.mpr ⟨⌊(n : ℝ) * t⌋₊, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      apply (Nat.floor_lt ht₀).mpr
      nlinarith [ht.2]
    · constructor
      · apply (div_le_iff₀ hn').mpr
        simpa only [mul_comm t] using Nat.floor_le ht₀
      · apply (lt_div_iff₀ hn').mpr
        simpa only [mul_comm t] using Nat.lt_floor_add_one ((n : ℝ) * t)

/-- Different mesh cells are disjoint. -/
theorem profileCells_pairwise {n : ℕ} (hn : 0 < n) :
    Set.Pairwise ((Finset.range n : Finset ℕ) : Set ℕ)
      (fun i j => Disjoint (profileCell n i) (profileCell n j)) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact hij ((floor_eq_of_mem_profileCell hn hi).symm.trans
    (floor_eq_of_mem_profileCell hn hj))

/-- Every step profile is integrable on each of its bounded mesh cells. -/
theorem integrableOn_stepProfile_cell (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    IntegrableOn (stepProfile v n) (profileCell n i) volume := by
  have hc : IntegrableOn (fun _ : ℝ => v i) (profileCell n i) volume := by
    exact integrableOn_const (by simp [profileCell]) (by simp)
  exact hc.congr_fun (fun t ht => (stepProfile_eq_on_cell v hn ht).symm) measurableSet_Ico

/-- Integrability on the exact closed unit interval used for the paper's `L¹` assumption. -/
theorem integrableOn_stepProfile_Icc (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (stepProfile v n) (Icc 0 1) volume := by
  rw [integrableOn_Icc_iff_integrableOn_Ico, ← profileCells_union hn]
  exact integrableOn_finset_iUnion.mpr (fun i _ => integrableOn_stepProfile_cell v hn i)

/-- The exact integral over one mesh cell is its constant value divided by `n`. -/
theorem integral_stepProfile_cell (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    ∫ t in profileCell n i, stepProfile v n t = (1 / (n : ℝ)) * v i := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hab : (i : ℝ) / n ≤ ((i : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by linarith) hn'.le
  calc
    (∫ t in profileCell n i, stepProfile v n t) = ∫ _ in profileCell n i, v i :=
      setIntegral_congr_fun measurableSet_Ico (fun t ht => stepProfile_eq_on_cell v hn ht)
    _ = (1 / (n : ℝ)) * v i := by
      rw [setIntegral_const, profileCell, Real.volume_real_Ico_of_le hab]
      simp only [smul_eq_mul]
      ring

/-- Exact discrete integral formula; the endpoint `t=1` contributes zero measure. -/
theorem integral_stepProfile_Icc (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ t in Icc (0 : ℝ) 1, stepProfile v n t =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, v i := by
  rw [integral_Icc_eq_integral_Ico, ← profileCells_union hn,
    integral_biUnion_finset (s := profileCell n) (Finset.range n)
      (fun _ _ => measurableSet_Ico)
      (profileCells_pairwise hn) (fun i _ => integrableOn_stepProfile_cell v hn i)]
  simp_rw [integral_stepProfile_cell v hn]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact relation between the paper's one-based sum and the zero-based mesh sum. -/
theorem sum_range_shift_eq (v : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, v (i + 1)) = (∑ i ∈ Finset.range n, v i) + v n - v 0 := by
  have h₀ := Finset.sum_range_succ v n
  have h₁ := Finset.sum_range_succ' v n
  linarith

/-- Shifted profiles integrate to the corresponding one-based average. -/
theorem integral_stepProfile_shift_Icc (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ t in Icc (0 : ℝ) 1, stepProfile (fun i => v (i + 1)) n t =
      (1 / (n : ℝ)) * ((∑ i ∈ Finset.range n, v i) + v n - v 0) := by
  rw [integral_stepProfile_Icc _ hn, sum_range_shift_eq]

/-- The two mesh conventions differ in their integrals only by the endpoint correction. -/
theorem integral_stepProfile_shift_sub (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ t in Icc (0 : ℝ) 1, stepProfile (fun i => v (i + 1)) n t) -
      (∫ t in Icc (0 : ℝ) 1, stepProfile v n t) = (v n - v 0) / n := by
  rw [integral_stepProfile_shift_Icc v hn, integral_stepProfile_Icc v hn]
  ring

end Freezing2
