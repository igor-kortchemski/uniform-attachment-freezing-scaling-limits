module

public import Freezing2.Probability.SampledDistanceContinuity
public import Freezing2.Probability.CoverRadiusSupport
public import Freezing2.Probability.SampledCoverRadiusContinuity
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Annealed sampled laws of random measured spaces

For a random compact measured space with law `P` on the GHP space, the source
samples iid points conditionally on the space. The resulting law of a sampled
observable is the mixture `∫ L(X) dP(X)` of its conditional laws `L(X)`. The
conditional sampled laws are continuous in the GHP topology; by the Portmanteau
lower bound on open sets they are therefore measurable for the Giry structure,
so the mixture is a genuine probability measure.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal BoundedContinuousFunction

universe u

namespace Freezing2

/-- A family of probability laws which is continuous for the weak topology is
measurable for the Giry structure. -/
theorem measurable_toMeasure_of_continuous {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [PseudoMetricSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] {L : X → ProbabilityMeasure Ω} (hL : Continuous L) :
    Measurable (fun x ↦ (L x : Measure Ω)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {s : Set Ω | IsOpen s}) (BorelSpace.measurable_eq.trans rfl) isPiSystem_isOpen
  intro s hs
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro x
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto (hL.tendsto x) hs

/-- The mixture `∫ L(x) dP(x)` of a continuous family of probability laws. -/
noncomputable def continuousMixture {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [PseudoMetricSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] (P : ProbabilityMeasure X)
    {L : X → ProbabilityMeasure Ω} (hL : Continuous L) : ProbabilityMeasure Ω :=
  ⟨(P : Measure X).bind (fun x ↦ (L x : Measure Ω)),
    isProbabilityMeasure_bind (measurable_toMeasure_of_continuous hL).aemeasurable
      (ae_of_all _ fun _ ↦ inferInstance)⟩

theorem continuousMixture_apply {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [PseudoMetricSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] (P : ProbabilityMeasure X)
    {L : X → ProbabilityMeasure Ω} (hL : Continuous L) {s : Set Ω} (hs : MeasurableSet s) :
    (continuousMixture P hL : Measure Ω) s = ∫⁻ x, (L x : Measure Ω) s ∂(P : Measure X) :=
  Measure.bind_apply hs (measurable_toMeasure_of_continuous hL).aemeasurable

/-- Weak convergence of the mixing laws gives weak convergence of the mixtures. -/
theorem tendsto_continuousMixture {X Ω : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [PseudoMetricSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] {ι : Type*} {l : Filter ι}
    {P : ι → ProbabilityMeasure X} {Q : ProbabilityMeasure X} (h : Tendsto P l (𝓝 Q))
    {L : X → ProbabilityMeasure Ω} (hL : Continuous L) :
    Tendsto (fun i ↦ continuousMixture (P i) hL) l (𝓝 (continuousMixture Q hL)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at h ⊢
  intro f
  let g₀ : X → ℝ≥0 := fun x ↦ (L x).toFiniteMeasure.testAgainstNN f
  have hg₀ : Continuous g₀ := (ProbabilityMeasure.continuous_testAgainstNN_eval f).comp hL
  let C : ℝ≥0 := nndist f 0
  have hbound (x : X) : g₀ x ≤ C := by
    calc
      g₀ x ≤ (L x).toFiniteMeasure.testAgainstNN (BoundedContinuousFunction.const Ω C) :=
        FiniteMeasure.testAgainstNN_mono _ fun ω ↦ BoundedContinuousFunction.NNReal.upper_bound f ω
      _ = C := by
        rw [FiniteMeasure.testAgainstNN_const, ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
  let g : X →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfBound ⟨g₀, hg₀⟩ C fun x y ↦ by
    have hx : (g₀ x : ℝ) ≤ C := by exact_mod_cast hbound x
    have hy : (g₀ y : ℝ) ≤ C := by exact_mod_cast hbound y
    change dist (g₀ x) (g₀ y) ≤ (C : ℝ)
    rw [NNReal.dist_eq]
    exact abs_sub_le_iff.mpr ⟨by linarith [NNReal.coe_nonneg (g₀ y)], by linarith [NNReal.coe_nonneg (g₀ x)]⟩
  have he (μ : ProbabilityMeasure X) : ∫⁻ ω, f ω ∂(continuousMixture μ hL : Measure Ω) =
      ∫⁻ x, g x ∂(μ : Measure X) := by
    change ∫⁻ ω, f ω ∂(μ : Measure X).bind (fun x ↦ (L x : Measure Ω)) = _
    rw [Measure.lintegral_bind (measurable_toMeasure_of_continuous hL).aemeasurable
      f.continuous.measurable.coe_nnreal_ennreal.aemeasurable]
    congr 1
    funext x
    change _ = (((L x).toFiniteMeasure.testAgainstNN f : ℝ≥0) : ℝ≥0∞)
    rw [FiniteMeasure.testAgainstNN_coe_eq]
    rfl
  simp_rw [he]
  exact h g

namespace MeasuredGHSpace

/-- The annealed law of the `k × k` matrix of distances between `k` points
sampled iid from the measure of a random measured space with law `P`. -/
noncomputable def annealedDistanceLaw (P : ProbabilityMeasure MeasuredGHSpace.{u}) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  continuousMixture P (continuous_sampledDistanceLaw k)

/-- The annealed law of the Hausdorff distance between a random measured space
and `k + 1` points sampled iid from its measure. -/
noncomputable def annealedCoverRadiusLaw (P : ProbabilityMeasure MeasuredGHSpace.{u}) (k : ℕ) :
    ProbabilityMeasure ℝ :=
  continuousMixture P (continuous_sampledCoverRadiusLaw k)

/-- The `k × k` upper-left block of an infinite matrix. -/
def matrixBlock (k : ℕ) (m : ℕ → ℕ → ℝ) : Fin k → Fin k → ℝ := fun i j ↦ m i j

theorem measurable_matrixBlock (k : ℕ) : Measurable (matrixBlock k) :=
  measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦
    (measurable_pi_apply (j : ℕ)).comp (measurable_pi_apply (i : ℕ))

/-- The finite-dimensional marginals of the law of an infinite random matrix. -/
noncomputable def matrixBlockLaw (M : ProbabilityMeasure (ℕ → ℕ → ℝ)) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  M.map (matrixBlock k)

/-- **Proposition `C.1`** (leaf-tightness criterion), stated in the universe `u`.
If the annealed sampled distance matrices of random compact measured spaces
with laws `P n` converge in distribution to a random infinite matrix with law
`M` (convergence of every finite block), and the spaces are leaf-tight, then
`P n` converges weakly in the GHP topology to the law `Q` of a random compact
measured space whose sampled matrix has law `M` and whose measure has full
support almost surely.

Leaf-tightness, `lim_{δ→0} lim_k limsup_n P(d_H(Xⁿ, {x₁, …, x_k}) > δ) = 0`, is
encoded as `lim_k limsup_n P(d_H > δ) = 0` for every `δ > 0`; the two are
equivalent because the probability decreases in `δ` and in `k`. The `k`-th
covering radius uses `k + 1` samples. -/
def LeafTightCriterion : Prop :=
  ∀ (P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}) (M : ProbabilityMeasure (ℕ → ℕ → ℝ)),
    (∀ k : ℕ, Tendsto (fun n ↦ annealedDistanceLaw (P n) k) atTop
      (𝓝 (matrixBlockLaw M k))) →
    (∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0)) →
    ∃ Q : ProbabilityMeasure MeasuredGHSpace.{u}, Tendsto P atTop (𝓝 Q) ∧
      (∀ k : ℕ, annealedDistanceLaw Q k = matrixBlockLaw M k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X

end MeasuredGHSpace

end Freezing2
