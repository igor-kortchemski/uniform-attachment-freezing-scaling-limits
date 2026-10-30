module

public import Freezing2.Probability.LeafTightLimits
public import Freezing2.Probability.EmpiricalMeasure
public import Freezing2.Probability.SampleDensity

/-!
# Reconstruction from sampled distance matrices and Proposition `C.1`

For a fully supported compact measured space, the finite measured spaces
reconstructed from the distance matrices of the first `k + 1` iid samples
converge almost surely to the space in the GHP topology: the samples become
dense and their empirical measure converges in the Lévy–Prokhorov distance.
Consequently every bounded continuous test of a random fully supported space is
the limit of tests of its annealed sampled matrices, so two such laws with the
same annealed matrices coincide. With the tightness and limit properties this
proves the leaf-tightness criterion.

This replaces the source's identification through the Gromov–Prokhorov
topology, Lemma `equivGP` and Lemma `GP+GH=GHP`, by direct empirical
reconstruction for compact spaces; those general lemmas are not proved here.
-/

@[expose] public section

open Filter MeasureTheory Set Metric Topology
open scoped ENNReal NNReal BoundedContinuousFunction

universe u

namespace Freezing2

namespace CompactMeasuredSpace

/-- Reconstructions from the first `k + 1` iid samples converge almost surely
to a fully supported space. -/
theorem ae_tendsto_matrixSpace (X : CompactMeasuredSpace.{u})
    [Measure.IsOpenPosMeasure (X.law : Measure X)] :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ ↦ (X.law : Measure X)),
      Tendsto (fun k ↦ matrixSpace.{u} k (distanceMatrix (k + 1) fun i : Fin (k + 1) ↦ ω i))
        atTop (𝓝 (toMeasuredGHSpace X)) := by
  filter_upwards [ae_tendsto_levyProkhorovDist_empiricalMeasure (X.law : Measure X),
    ae_tendsto_hausdorffDist_samples (X.law : Measure X)] with ω hLP hH
  rw [tendsto_iff_dist_tendsto_zero]
  have h := hLP.add hH
  rw [add_zero] at h
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun k ↦ dist_matrixSpace_distanceMatrix_le X fun i : Fin (k + 1) ↦ ω i) h

/-- Tests of the reconstructions converge to the test of the space. -/
theorem tendsto_lintegral_matrixSpace (X : CompactMeasuredSpace.{u})
    [Measure.IsOpenPosMeasure (X.law : Measure X)] (F : MeasuredGHSpace.{u} →ᵇ ℝ≥0) :
    Tendsto (fun k ↦ ∫⁻ m, F (matrixSpace.{u} k m) ∂(iidDistanceLaw X (k + 1) :
      Measure (Fin (k + 1) → Fin (k + 1) → ℝ))) atTop (𝓝 (F (toMeasuredGHSpace X))) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ (X.law : Measure X))
  have hpre (k : ℕ) : P.map (fun ω (i : Fin (k + 1)) ↦ ω i) =
      Measure.pi (fun _ : Fin (k + 1) ↦ (X.law : Measure X)) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin (k + 1) ↦ (i : ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]
  have hmF (k : ℕ) : Measurable fun m : Fin (k + 1) → Fin (k + 1) → ℝ ↦
      ((F (matrixSpace.{u} k m) : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (F.continuous.comp (continuous_matrixSpace k))).measurable
  have hrestrict (k : ℕ) : Measurable fun ω : ℕ → X ↦ fun i : Fin (k + 1) ↦ ω i :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (i : ℕ)
  have hrw (k : ℕ) : ∫⁻ m, F (matrixSpace.{u} k m) ∂(iidDistanceLaw X (k + 1) :
      Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) =
        ∫⁻ ω, F (matrixSpace.{u} k (distanceMatrix (k + 1) fun i : Fin (k + 1) ↦ ω i)) ∂P := by
    change ∫⁻ m, _ ∂((Measure.pi (fun _ : Fin (k + 1) ↦ (X.law : Measure X))).map
      (distanceMatrix (k + 1))) = _
    rw [lintegral_map (hmF k) (continuous_distanceMatrix (k + 1)).measurable, ← hpre k]
    exact lintegral_map ((hmF k).comp (continuous_distanceMatrix (k + 1)).measurable)
      (hrestrict k)
  simp_rw [hrw]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := P)
    (fun _ ↦ ((nndist F 0 : ℝ≥0) : ℝ≥0∞))
    (fun k ↦ (hmF k).comp ((continuous_distanceMatrix (k + 1)).measurable.comp (hrestrict k)))
    (fun k ↦ Eventually.of_forall fun ω ↦
      ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound F _))
    (by simp [lintegral_const])
    ((ae_tendsto_matrixSpace X).mono fun ω hω ↦
      (ENNReal.continuous_coe.tendsto _).comp ((F.continuous.tendsto _).comp hω))
  simpa [lintegral_const] using hlim

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- Tests of a random fully supported space are limits of tests of its
annealed sampled distance matrices. -/
theorem tendsto_lintegral_annealedDistanceLaw (Q : ProbabilityMeasure MeasuredGHSpace.{u})
    (hQ : ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X)
    (F : MeasuredGHSpace.{u} →ᵇ ℝ≥0) :
    Tendsto (fun k ↦ ∫⁻ m, F (matrixSpace.{u} k m) ∂(annealedDistanceLaw Q (k + 1) :
      Measure (Fin (k + 1) → Fin (k + 1) → ℝ))) atTop
        (𝓝 (∫⁻ X, F X ∂(Q : Measure MeasuredGHSpace.{u}))) := by
  have hmF (k : ℕ) : Measurable fun m : Fin (k + 1) → Fin (k + 1) → ℝ ↦
      ((F (matrixSpace.{u} k m) : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (F.continuous.comp (continuous_matrixSpace k))).measurable
  have hL (k : ℕ) := measurable_toMeasure_of_continuous (continuous_sampledDistanceLaw.{u} (k + 1))
  have hrw (k : ℕ) : ∫⁻ m, F (matrixSpace.{u} k m) ∂(annealedDistanceLaw Q (k + 1) :
      Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) =
        ∫⁻ X, ∫⁻ m, F (matrixSpace.{u} k m) ∂(sampledDistanceLaw (k + 1) X :
          Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) ∂(Q : Measure MeasuredGHSpace.{u}) := by
    change ∫⁻ m, _ ∂((Q : Measure MeasuredGHSpace.{u}).bind
      (fun X ↦ (sampledDistanceLaw (k + 1) X : Measure (Fin (k + 1) → Fin (k + 1) → ℝ)))) = _
    rw [Measure.lintegral_bind (hL k).aemeasurable (hmF k).aemeasurable]
  simp_rw [hrw]
  apply tendsto_lintegral_of_dominated_convergence (fun _ ↦ ((nndist F 0 : ℝ≥0) : ℝ≥0∞))
  · exact fun k ↦ (Measure.measurable_lintegral (hmF k)).comp (hL k)
  · intro k
    refine Eventually.of_forall fun X ↦ ?_
    calc
      ∫⁻ m, F (matrixSpace.{u} k m) ∂(sampledDistanceLaw (k + 1) X :
          Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) ≤
          ∫⁻ _, ((nndist F 0 : ℝ≥0) : ℝ≥0∞) ∂(sampledDistanceLaw (k + 1) X :
            Measure (Fin (k + 1) → Fin (k + 1) → ℝ)) :=
        lintegral_mono fun m ↦ ENNReal.coe_le_coe.mpr
          (BoundedContinuousFunction.NNReal.upper_bound F _)
      _ = _ := by simp [lintegral_const]
  · simp [lintegral_const]
  · filter_upwards [hQ] with X hX
    induction X using Quotient.inductionOn with
    | _ X =>
      have : Measure.IsOpenPosMeasure (X.law : Measure X) := hX
      exact CompactMeasuredSpace.tendsto_lintegral_matrixSpace X F

/-- Laws of random fully supported spaces are determined by their annealed
sampled distance matrices. -/
theorem eq_of_annealedDistanceLaw_eq (Q Q' : ProbabilityMeasure MeasuredGHSpace.{u})
    (h : ∀ k, annealedDistanceLaw Q k = annealedDistanceLaw Q' k)
    (hQ : ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X)
    (hQ' : ∀ᵐ X ∂(Q' : Measure MeasuredGHSpace.{u}), HasFullSupport X) : Q = Q' := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro F
  refine tendsto_nhds_unique (tendsto_lintegral_annealedDistanceLaw Q hQ F) ?_
  simp_rw [h]
  exact tendsto_lintegral_annealedDistanceLaw Q' hQ' F

/-- **Proposition `C.1`** (leaf-tightness criterion). -/
theorem leafTightCriterion : LeafTightCriterion.{u} :=
  leafTightCriterion_of_uniqueness eq_of_annealedDistanceLaw_eq

/-- **Proposition `C.1` for a family of block laws.** Convergence of every annealed
sampled block to a law `L k` and leaf-tightness give weak convergence to the unique
law with annealed blocks `L k` and almost surely full support. -/
theorem leafTightFamily (P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u})
    (L : ∀ k : ℕ, ProbabilityMeasure (Fin k → Fin k → ℝ))
    (hM : ∀ k : ℕ, Tendsto (fun n ↦ annealedDistanceLaw (P n) k) atTop (𝓝 (L k)))
    (hleaf : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℕ ↦ limsup (fun n : ℕ ↦
      (annealedCoverRadiusLaw (P n) k : Measure ℝ) (Ioi δ)) atTop) atTop (𝓝 0)) :
    ∃ Q : ProbabilityMeasure MeasuredGHSpace.{u}, Tendsto P atTop (𝓝 Q) ∧
      (∀ k : ℕ, annealedDistanceLaw Q k = L k) ∧
      ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X :=
  leafTightFamily_of_uniqueness eq_of_annealedDistanceLaw_eq P L hM hleaf

end MeasuredGHSpace

end Freezing2
