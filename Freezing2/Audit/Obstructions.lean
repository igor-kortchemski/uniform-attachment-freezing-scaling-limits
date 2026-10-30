module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.HasLaw
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Diagonal audit for the supercritical limit

The display in `thm:sur-critique` in the source includes diagonal entries but
assigns them the sum of the two branch lengths. A distance matrix has zero
diagonal, and this property survives convergence in distribution. The results
below verify this obstruction and the elementary properties of the corrected
star matrix. They do not prove the paper's stochastic scaling limit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Freezing2.Audit

variable {I : Type*}

/-- The uncorrected matrix displayed in the paper's supercritical theorem. -/
def additiveMatrix (length : I → ℝ) (i j : I) : ℝ := length i + length j

/-- The corrected matrix retains the off-diagonal formula and has zero diagonal. -/
def starDistance [DecidableEq I] (length : I → ℝ) (i j : I) : ℝ :=
  if i = j then 0 else length i + length j

@[simp] theorem additiveMatrix_self (length : I → ℝ) (i : I) :
    additiveMatrix length i i = 2 * length i := by
  simp [additiveMatrix, two_mul]

theorem additiveMatrix_self_pos (length : I → ℝ) (i : I) (h : 0 < length i) :
    0 < additiveMatrix length i i := by
  simp only [additiveMatrix_self]
  positivity

theorem additiveMatrix_ne_zeroDiagonal (length : I → ℝ) (i : I)
    (h : length i ≠ 0) (d : I → I → ℝ) (hd : d i i = 0) :
    d ≠ additiveMatrix length := by
  intro heq
  have : 2 * length i = 0 := by simpa [heq] using hd
  exact h (by linarith)

@[simp] theorem starDistance_self [DecidableEq I] (length : I → ℝ) (i : I) :
    starDistance length i i = 0 := by simp [starDistance]

theorem starDistance_of_ne [DecidableEq I] (length : I → ℝ) {i j : I} (h : i ≠ j) :
    starDistance length i j = length i + length j := by simp [starDistance, h]

theorem starDistance_comm [DecidableEq I] (length : I → ℝ) (i j : I) :
    starDistance length i j = starDistance length j i := by
  simp [starDistance, eq_comm, add_comm]

theorem starDistance_nonneg [DecidableEq I] (length : I → ℝ)
    (h : ∀ i, 0 ≤ length i) (i j : I) : 0 ≤ starDistance length i j := by
  unfold starDistance
  split_ifs
  · exact le_rfl
  · exact add_nonneg (h i) (h j)

theorem starDistance_triangle [DecidableEq I] (length : I → ℝ)
    (h : ∀ i, 0 ≤ length i) (i j k : I) :
    starDistance length i k ≤ starDistance length i j + starDistance length j k := by
  by_cases hij : i = j
  · subst j
    simp
  by_cases hjk : j = k
  · subst k
    simp
  by_cases hik : i = k
  · subst k
    rw [starDistance_self]
    exact add_nonneg (starDistance_nonneg length h i j)
      (starDistance_nonneg length h j i)
  · simp only [starDistance, hij, hjk, hik, ite_false]
    linarith [h j]

/-- The corrected star formula defines a pseudometric for nonnegative lengths. -/
@[instance_reducible]
def starPseudoMetric [DecidableEq I] (length : I → ℝ) (h : ∀ i, 0 ≤ length i) :
    PseudoMetricSpace I where
  dist := starDistance length
  dist_self := starDistance_self length
  dist_comm := starDistance_comm length
  dist_triangle := starDistance_triangle length h

theorem starDistance_eq_zero_iff [DecidableEq I] (length : I → ℝ)
    (h : ∀ i, 0 < length i) (i j : I) : starDistance length i j = 0 ↔ i = j := by
  constructor
  · intro hzero
    by_contra hij
    rw [starDistance_of_ne length hij] at hzero
    linarith [h i, h j]
  · rintro rfl
    simp

/-- In the source definition a vertex coalesces with itself at its birth time,
so every strictly earlier self-coalescence event is empty. -/
theorem measure_self_coalescence_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (coal : Ω → I → I → ℕ) (birth : I → ℕ) (u : I)
    (hself : ∀ ω, coal ω u u = birth u) {c : ℕ} (hc : c < birth u) :
    μ {ω | coal ω u u = c} = 0 := by
  simp [hself, ne_of_gt hc]

/-- For one attachment step, `S₁ = 2`, `birth(u) = 1`, and `c = 0`.
The displayed formula in the source gives `1 / choose 2 2 = 1`, whereas
the self-coalescence event has probability zero. This is the numerical
obstruction to allowing `u = v` in that formula. -/
theorem oneStep_self_coalescence_formula_false {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) :
    (μ {_ω : Ω | (1 : ℕ) = 0}).toReal ≠ (Nat.choose 2 2 : ℝ)⁻¹ := by
  norm_num

/-- The inclusive-endpoint formula for the source's auxiliary `D` has a
nonzero self-entry: substitute `coal(u,u) = birth(u) = b`. -/
theorem inclusive_reciprocal_self (S : ℕ → ℝ) (b : ℕ) :
    (1 / 2 : ℝ) * (∑ i ∈ Finset.Icc b b, 1 / S i) +
      (1 / 2 : ℝ) * (∑ i ∈ Finset.Icc b b, 1 / S i) = 1 / S b := by
  simp only [Finset.Icc_self, Finset.sum_singleton]
  linarith

theorem inclusive_reciprocal_self_pos (S : ℕ → ℝ) (b : ℕ) (hb : 0 < S b) :
    0 < (1 / 2 : ℝ) * (∑ i ∈ Finset.Icc b b, 1 / S i) +
      (1 / 2 : ℝ) * (∑ i ∈ Finset.Icc b b, 1 / S i) := by
  rw [inclusive_reciprocal_self]
  positivity

section Distribution

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']

/-- A sequence of almost surely zero real variables can only converge in law
to an almost surely zero variable, even when the underlying spaces vary. -/
theorem ae_eq_zero_of_tendstoInDistribution
    {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}
    (hX : ∀ n, X n =ᵐ[μ n] fun _ ↦ 0)
    (h : TendstoInDistribution X atTop Z μ μ') : Z =ᵐ[μ'] fun _ ↦ 0 := by
  have hlaw (n : ℕ) : HasLaw (X n) (Measure.dirac 0) (μ n) :=
    hasLaw_dirac_of_ae_eq (hX n)
  have hzero : HasLaw (fun _ : Ω' ↦ (0 : ℝ)) (Measure.dirac 0) μ' :=
    hasLaw_dirac_of_ae_eq (Filter.EventuallyEq.refl _ _)
  have h' : TendstoInDistribution X atTop (fun _ : Ω' ↦ (0 : ℝ)) μ μ' :=
    tendstoInDistribution_of_identDistrib 0
      (fun n ↦ (hlaw 0).identDistrib (hlaw n)) ((hlaw 0).identDistrib hzero)
  have hmap : μ'.map Z = Measure.dirac 0 :=
    (tendstoInDistribution_unique X h h').trans hzero.map_eq
  exact (show HasLaw Z (Measure.dirac 0) μ' from ⟨h.aemeasurable_limit, hmap⟩).ae_eq_of_dirac

/-- Every fixed diagonal entry of a weak limit of zero-diagonal random matrices
is almost surely zero. This applies in particular to rescaled distance matrices. -/
theorem zeroDiagonal_of_tendstoInDistribution [Fintype I]
    {M : (n : ℕ) → Ω n → I → I → ℝ} {L : Ω' → I → I → ℝ}
    (hM : ∀ n i, ∀ᵐ ω ∂μ n, M n ω i i = 0)
    (h : TendstoInDistribution M atTop L μ μ') (i : I) :
    ∀ᵐ ω ∂μ', L ω i i = 0 := by
  have hc : Continuous (fun m : I → I → ℝ ↦ m i i) :=
    (continuous_apply i).comp (continuous_apply i)
  exact ae_eq_zero_of_tendstoInDistribution (fun n ↦ hM n i) (h.continuous_comp hc)

/-- An all-entry additive matrix can be such a limit only when every fixed
branch length is almost surely zero. -/
theorem branchLength_eq_zero_of_additive_limit [Fintype I]
    {M : (n : ℕ) → Ω n → I → I → ℝ} {length : Ω' → I → ℝ}
    (hM : ∀ n i, ∀ᵐ ω ∂μ n, M n ω i i = 0)
    (h : TendstoInDistribution M atTop (fun ω ↦ additiveMatrix (length ω)) μ μ')
    (i : I) : ∀ᵐ ω ∂μ', length ω i = 0 := by
  filter_upwards [zeroDiagonal_of_tendstoInDistribution hM h i] with ω hω
  simp only [additiveMatrix_self] at hω
  linarith

/-- Positive branch lengths contradict the uncorrected all-entry formula. -/
theorem not_tendstoInDistribution_additiveMatrix [Fintype I]
    {M : (n : ℕ) → Ω n → I → I → ℝ} {length : Ω' → I → ℝ}
    (hM : ∀ n i, ∀ᵐ ω ∂μ n, M n ω i i = 0)
    (i : I) (hpos : ∀ᵐ ω ∂μ', 0 < length ω i) :
    ¬ TendstoInDistribution M atTop (fun ω ↦ additiveMatrix (length ω)) μ μ' := by
  intro h
  have hz := branchLength_eq_zero_of_additive_limit hM h i
  have hf : ∀ᵐ ω ∂μ', False := by
    filter_upwards [hz, hpos] with ω hzero hpositive
    linarith
  obtain ⟨ω, hω⟩ := hf.exists
  exact hω

/-- Specialization to actual rescaled metric distance matrices. No assumption
on independence of the sampled points or on the scaling factors is needed. -/
theorem not_tendstoInDistribution_additive_of_dist [Fintype I]
    {E : ℕ → Type*} [∀ n, PseudoMetricSpace (E n)]
    (sample : (n : ℕ) → Ω n → I → E n) (scale : ℕ → ℝ)
    {length : Ω' → I → ℝ} (i : I) (hpos : ∀ᵐ ω ∂μ', 0 < length ω i) :
    ¬ TendstoInDistribution
      (fun n ω a b ↦ scale n * dist (sample n ω a) (sample n ω b))
      atTop (fun ω ↦ additiveMatrix (length ω)) μ μ' := by
  apply not_tendstoInDistribution_additiveMatrix (i := i) (hpos := hpos)
  intro n a
  filter_upwards [] with ω
  simp

end Distribution

end Freezing2.Audit
