module

public import Freezing2.Analysis.StepProfile

/-!
# Exact integration over arbitrary mesh intervals

The closed interval `[a/n,b/n]` integrates the cells indexed by `a,…,b−1`.
An inclusive sum over `a,…,b` instead ends at `(b+1)/n`. These identities
make the endpoint convention explicit for the local estimates in
Lemma `lem:hnalpha(v)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Freezing2

/-- Any finite consecutive family of mesh cells partitions its half-open
real interval, including the case of an empty index interval. -/
theorem profileCells_interval_union {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    (⋃ i ∈ Finset.Ico a b, profileCell n i) = Ico ((a : ℝ) / n) ((b : ℝ) / n) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi, ht⟩ := mem_iUnion₂.mp ht
    have hai : (a : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    have hib : (i : ℝ) + 1 ≤ b := by exact_mod_cast (Finset.mem_Ico.mp hi).2
    exact ⟨(div_le_div_of_nonneg_right hai hn'.le).trans ht.1,
      ht.2.trans_le (div_le_div_of_nonneg_right hib hn'.le)⟩
  · intro ht
    have ht₀ : 0 ≤ t := (div_nonneg (Nat.cast_nonneg a) hn'.le).trans ht.1
    have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg hn'.le ht₀
    refine mem_iUnion₂.mpr ⟨⌊(n : ℝ) * t⌋₊, ?_, ?_⟩
    · apply Finset.mem_Ico.mpr
      constructor
      · apply Nat.le_floor
        have := (div_le_iff₀ hn').mp ht.1
        nlinarith
      · apply (Nat.floor_lt hnt).mpr
        have := (lt_div_iff₀ hn').mp ht.2
        nlinarith
    · constructor
      · apply (div_le_iff₀ hn').mpr
        simpa only [mul_comm t] using Nat.floor_le hnt
      · apply (lt_div_iff₀ hn').mpr
        simpa only [mul_comm t] using Nat.lt_floor_add_one ((n : ℝ) * t)

/-- Distinct cells remain disjoint for an arbitrary consecutive index interval. -/
theorem profileCells_interval_pairwise {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Set.Pairwise ((Finset.Ico a b : Finset ℕ) : Set ℕ)
      (fun i j ↦ Disjoint (profileCell n i) (profileCell n j)) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact hij ((floor_eq_of_mem_profileCell hn hi).symm.trans
    (floor_eq_of_mem_profileCell hn hj))

/-- Every finite mesh interval gives an integrable step profile; no upper bound
on the sequence or the indices is required. -/
theorem integrableOn_stepProfile_meshInterval (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (a b : ℕ) :
    IntegrableOn (stepProfile v n) (Icc ((a : ℝ) / n) ((b : ℝ) / n)) volume := by
  rw [integrableOn_Icc_iff_integrableOn_Ico, ← profileCells_interval_union hn a b]
  exact integrableOn_finset_iUnion.mpr (fun i _ ↦ integrableOn_stepProfile_cell v hn i)

/-- Exact mesh integration over `[a/n,b/n]`; the upper cell index is excluded. -/
theorem integral_stepProfile_meshInterval (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (a b : ℕ) :
    (∫ t in Icc ((a : ℝ) / n) ((b : ℝ) / n), stepProfile v n t) =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.Ico a b, v i := by
  rw [integral_Icc_eq_integral_Ico, ← profileCells_interval_union hn a b,
    integral_biUnion_finset (s := profileCell n) (Finset.Ico a b)
      (fun _ _ ↦ measurableSet_Ico)
      (profileCells_interval_pairwise hn a b)
      (fun i _ ↦ integrableOn_stepProfile_cell v hn i)]
  simp_rw [integral_stepProfile_cell v hn]
  exact (Finset.mul_sum _ _ _).symm

/-- An inclusive sum has upper integration endpoint `(b+1)/n`.
This also handles reversed index intervals correctly. -/
theorem integral_stepProfile_inclusive_meshInterval (v : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (a b : ℕ) :
    (∫ t in Icc ((a : ℝ) / n) (((b : ℝ) + 1) / n), stepProfile v n t) =
      (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc a b, v i := by
  have hset : Finset.Ico a (b + 1) = Finset.Icc a b := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simpa only [Nat.cast_add, Nat.cast_one, hset] using
    integral_stepProfile_meshInterval v hn a (b + 1)

end Freezing2
