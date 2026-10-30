module

public import Freezing2.Probability.Bennett
public import Freezing2.Analysis.HeightConcentrationRate
public import Mathlib.Probability.IdentDistrib

/-!
# Uniform concentration for a finite family with Bernoulli-sum marginals

This is the concentration engine in source lines 900–923. Each height needs
its own verified Bernoulli-sum law, but the heights need not be independent of
one another. The auxiliary Bernoulli laws may depend on the family member.
Zero means and empty sums are handled explicitly.

The final theorem is conditional on those marginal laws. It does not construct
the paper's reverse forest or prove its height representation, so it does not
by itself complete Proposition `height=ok`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators ProbabilityTheory

namespace Freezing2

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The maximum absolute centered deviation, with zero on an empty family. -/
noncomputable def finiteHeightDeviationMax {κ : Type*} [Fintype κ]
    (Z : κ → Ω → ℝ) (m : κ → ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Option κ)).sup' Finset.univ_nonempty
    (fun j ↦ match j with | none => 0 | some j => |Z j ω - m j|)

omit [MeasurableSpace Ω] in
/-- At a nonnegative threshold the maximum event is exactly the finite union
of the individual deviation events; the auxiliary zero contributes nothing. -/
theorem lt_finiteHeightDeviationMax_iff {κ : Type*} [Fintype κ]
    (Z : κ → Ω → ℝ) (m : κ → ℝ) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    t < finiteHeightDeviationMax Z m ω ↔ ∃ j, t < |Z j ω - m j| := by
  simp only [finiteHeightDeviationMax, Finset.lt_sup'_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    cases j with
    | none => exact (not_lt.mpr ht hj).elim
    | some j => exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨some j, hj⟩

/-- A Bernoulli sum with zero mean is zero almost surely, including an empty sum. -/
theorem bernoulli_sum_ae_eq_zero_of_mean_zero {μ : Measure Ω} {d : ℕ}
    {Y : Fin d → Ω → ℝ} {p : Fin d → unitInterval}
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (hm : ∑ i, (p i : ℝ) = 0) :
    (fun ω ↦ ∑ i, Y i ω) =ᵐ[μ] (fun _ ↦ 0) := by
  have hp (i : Fin d) : p i = 0 := by
    apply Subtype.ext
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ (p j).2.1)).mp hm i (Finset.mem_univ i)
  have hvars (i : Fin d) : Y i =ᵐ[μ] (fun _ ↦ 0) := by
    apply HasLaw.ae_eq_of_dirac
    simpa only [hp i, bernoulliMeasure_zero] using hY i
  filter_upwards [ae_all_iff.mpr hvars] with ω hω
  simp only [hω, Finset.sum_const_zero]

/-- Bennett's absolute-deviation estimate using a positive upper bound for the
mean. Individual means may equal zero. -/
theorem bennett_abs_deviation_le_cap {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} {Y : Fin d → Ω → ℝ} {p : Fin d → unitInterval}
    (hInd : iIndepFun Y μ)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    {t H : ℝ} (ht : 0 < t) (_hH : 0 < H) (hmean : ∑ i, (p i : ℝ) ≤ H) :
    μ.real {ω | t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))|} ≤
      2 * Real.exp (-bennettExponent t H) := by
  have hm0 : 0 ≤ ∑ i, (p i : ℝ) := Finset.sum_nonneg fun i _ ↦ (p i).2.1
  rcases eq_or_lt_of_le hm0 with hm | hm
  · have hsum := bernoulli_sum_ae_eq_zero_of_mean_zero hY hm.symm
    have he : {ω | t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))|} =ᵐ[μ] ∅ := by
      filter_upwards [hsum] with ω hω
      simp only [mem_empty_iff_false, hω, ← hm, sub_zero, abs_zero]
      simp only [not_lt.mpr ht.le]
    rw [measureReal_congr he]
    simp only [measureReal_empty]
    positivity
  · calc
      _ ≤ 2 * Real.exp (-bennettExponent t (∑ i, (p i : ℝ))) := by
        simpa only [bennettExponent, neg_mul] using bennett_abs_deviation hInd hY hm ht
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (exp_neg_bennettExponent_le_of_le ht hm hmean) (by norm_num)

/-- Transfer of the concentration bound through the actual distributional law.
The Bernoulli variables can live on a separate auxiliary probability space. -/
theorem height_deviation_le_of_bernoulli_law {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure ν] {Z : Ω → ℝ} {d : ℕ}
    {Y : Fin d → Ω' → ℝ} {p : Fin d → unitInterval}
    (hLaw : IdentDistrib Z (fun ω ↦ ∑ i, Y i ω) μ ν)
    (hInd : iIndepFun Y ν)
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) ν)
    {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hmean : ∑ i, (p i : ℝ) ≤ H) :
    μ.real {ω | t < |Z ω - (∑ i, (p i : ℝ))|} ≤
      2 * Real.exp (-bennettExponent t H) := by
  have he := hLaw.measure_mem_eq (s := {z : ℝ | t < |z - (∑ i, (p i : ℝ))|})
    (by measurability)
  have he' := congrArg ENNReal.toReal he
  change μ.real {ω | t < |Z ω - (∑ i, (p i : ℝ))|} =
    ν.real {ω | t < |(∑ i, Y i ω) - (∑ i, (p i : ℝ))|} at he'
  rw [he']
  exact bennett_abs_deviation_le_cap hInd hY ht hH hmean

/-- Finite union bound for heights having Bernoulli-sum marginals. There is
no independence premise relating different members of the family. -/
theorem finite_height_deviation_union_bound {κ : Type*} [Fintype κ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : κ → Measure Ω'} [∀ j, IsProbabilityMeasure (ν j)]
    (d : κ → ℕ) (Z : κ → Ω → ℝ)
    (Y : (j : κ) → Fin (d j) → Ω' → ℝ) (p : (j : κ) → Fin (d j) → unitInterval)
    (hLaw : ∀ j, IdentDistrib (Z j) (fun ω ↦ ∑ i, Y j i ω) μ (ν j))
    (hInd : ∀ j, iIndepFun (Y j) (ν j))
    (hY : ∀ j i, HasLaw (Y j i) (bernoulliMeasure (1 : ℝ) 0 (p j i)) (ν j))
    {t H : ℝ} (ht : 0 < t) (hH : 0 < H)
    (hmean : ∀ j, ∑ i, (p j i : ℝ) ≤ H) :
    μ.real {ω | ∃ j, t < |Z j ω - (∑ i, (p j i : ℝ))|} ≤
      2 * Fintype.card κ * Real.exp (-bennettExponent t H) := by
  have he : {ω | ∃ j, t < |Z j ω - (∑ i, (p j i : ℝ))|} =
      ⋃ j, {ω | t < |Z j ω - (∑ i, (p j i : ℝ))|} := by ext ω; simp
  rw [he]
  calc
    _ ≤ ∑ j, μ.real {ω | t < |Z j ω - (∑ i, (p j i : ℝ))|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : κ, 2 * Real.exp (-bennettExponent t H) :=
      Finset.sum_le_sum fun j _ ↦ height_deviation_le_of_bernoulli_law
        (hLaw j) (hInd j) (hY j) ht hH (hmean j)
    _ = _ := by simp; ring

/-- Conditional uniform height concentration at the source scale. The missing
model obligation is exactly `hLaw` (and its Bernoulli representation), stated
explicitly for every height rather than assumed as a tail estimate. -/
theorem tendsto_uniform_height_deviation_of_bernoulli_laws
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (μ : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : (n : ℕ) → κ n → Measure Ω')
    [∀ n j, IsProbabilityMeasure (ν n j)]
    (d : (n : ℕ) → κ n → ℕ) (Z : (n : ℕ) → κ n → Ω → ℝ)
    (Y : (n : ℕ) → (j : κ n) → Fin (d n j) → Ω' → ℝ)
    (p : (n : ℕ) → (j : κ n) → Fin (d n j) → unitInterval)
    (hLaw : ∀ n j, IdentDistrib (Z n j) (fun ω ↦ ∑ i, Y n j i ω) (μ n) (ν n j))
    (hInd : ∀ n j, iIndepFun (Y n j) (ν n j))
    (hY : ∀ n j i, HasLaw (Y n j i) (bernoulliMeasure (1 : ℝ) 0 (p n j i)) (ν n j))
    (hmean : ∀ n j, ∑ i, (p n j i : ℝ) ≤ harmonicUpTotal x n)
    (hcard : ∀ n, Fintype.card (κ n) ≤ (n + 1) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (μ n).real {ω |
      ε * (n : ℝ) ^ (1 - α) < finiteHeightDeviationMax (Z n)
        (fun j ↦ ∑ i, (p n j i : ℝ)) ω})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) ?_
    (tendsto_uniform_height_bennett_bound hx hα0 hα1 hL1 hpos hε)
  filter_upwards [eventually_harmonicUpTotal_pos hx hα0 hα1 hL1 hpos,
    eventually_gt_atTop 0] with n hH hn
  have ht : 0 < ε * (n : ℝ) ^ (1 - α) :=
    mul_pos hε (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  rw [show {ω | ε * (n : ℝ) ^ (1 - α) <
      finiteHeightDeviationMax (Z n) (fun j ↦ ∑ i, (p n j i : ℝ)) ω} =
      {ω | ∃ j, ε * (n : ℝ) ^ (1 - α) < |Z n j ω - (∑ i, (p n j i : ℝ))|} by
    ext ω
    exact lt_finiteHeightDeviationMax_iff _ _ _ ht.le]
  have hbound := finite_height_deviation_union_bound (ν := ν n) (d n) (Z n) (Y n) (p n)
    (hLaw n) (hInd n) (hY n) ht hH (hmean n)
  have hcard' : (Fintype.card (κ n) : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    exact_mod_cast hcard n
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard' (by norm_num)) (Real.exp_pos _).le)

end Freezing2
