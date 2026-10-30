module

public import Freezing2.Geometry.CompactMeasuredRepresentation
public import Freezing2.Probability.SampledCoverRadius

/-!
# GHP continuity of iid covering-radius laws

A common compact realization retains both whole carriers and their sampling
measures. The actual finite covering-radius law is jointly continuous in
these two inputs. Compact subsequence extraction and GHP uniqueness then
give continuity on whole-space measured-isometry classes.
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace GromovHausdorff
open scoped Topology BoundedContinuousFunction

universe u

namespace Freezing2

theorem compactMeasuredRange_eq_fullCarrierCompact_map
    (X : CompactMeasuredSpace.{u}) {Z : Type u} [MetricSpace Z]
    (f : X → Z) (hf : Isometry f) :
    compactMeasuredRange X f hf = (fullCarrierCompact X).map f hf.continuous := by
  apply NonemptyCompacts.ext
  change range f = f '' univ
  exact image_univ.symm

/-- A common compact realization gives convergence of every actual finite
covering-radius law. No full-support premise is needed. -/
theorem CompactMeasuredRepresentation.tendsto_iidCoverRadiusLaw
    {X : ℕ → CompactMeasuredSpace.{u}} (R : CompactMeasuredRepresentation X) (k : ℕ) :
    Tendsto (fun n ↦ iidCoverRadiusLaw (X (R.indices n)) k) atTop
      (𝓝 (iidCoverRadiusLaw R.limit k)) := by
  have h := (continuous_iidCoverRadiusLawOn (X := R.ambient) k).tendsto
    (compactMeasuredRange R.limit R.limitEmbedding R.limitEmbedding_isometry,
      R.limit.law.map R.limitEmbedding) |>.comp
        (R.carrier_tendsto.prodMk_nhds R.measure_tendsto)
  have hleft (n : ℕ) : iidCoverRadiusLawOn
      (compactMeasuredRange (X (R.indices n)) (R.embedding n) (R.embedding_isometry n))
      ((X (R.indices n)).law.map (R.embedding n)) k = iidCoverRadiusLaw (X (R.indices n)) k := by
    rw [compactMeasuredRange_eq_fullCarrierCompact_map]
    exact iidCoverRadiusLawOn_map_isometry (fullCarrierCompact (X (R.indices n)))
      (X (R.indices n)).law (R.embedding n) (R.embedding_isometry n) k
  have hright : iidCoverRadiusLawOn
      (compactMeasuredRange R.limit R.limitEmbedding R.limitEmbedding_isometry)
      (R.limit.law.map R.limitEmbedding) k = iidCoverRadiusLaw R.limit k := by
    rw [compactMeasuredRange_eq_fullCarrierCompact_map]
    exact iidCoverRadiusLawOn_map_isometry (fullCarrierCompact R.limit)
      R.limit.law R.limitEmbedding R.limitEmbedding_isometry k
  simpa only [Function.comp_def, hleft, hright] using h

namespace MeasuredGHSpace

/-- Continuity of the full carrier's iid covering-radius law in the exact
source GHP topology. Sample collisions remain in the product probability law. -/
theorem continuous_sampledCoverRadiusLaw (k : ℕ) :
    Continuous (sampledCoverRadiusLaw.{u} k) := by
  classical
  apply SeqContinuous.continuous
  intro v p hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let X : ℕ → CompactMeasuredSpace.{u} := fun n ↦ Quotient.out (v (ns n))
  have hX (n : ℕ) : toMeasuredGHSpace (X n) = v (ns n) := Quotient.out_eq _
  have hseq : Tendsto (fun n ↦ toMeasuredGHSpace (X n)) atTop (𝓝 p) := by
    simpa only [hX, Function.comp_def] using hv.comp hns
  have hGH : CauchySeq (fun n ↦ toGHSpace (X n)) :=
    ((continuous_underlyingGH.tendsto p).comp hseq).cauchySeq
  obtain ⟨R⟩ := exists_compactMeasuredRepresentation_of_gh_cauchy X hGH
  have heq : toMeasuredGHSpace R.limit = p :=
    tendsto_nhds_unique R.tendsto (hseq.comp R.indices_strictMono.tendsto_atTop)
  refine ⟨R.indices, ?_⟩
  have hleft (n : ℕ) : iidCoverRadiusLaw (X n) k = sampledCoverRadiusLaw k (v (ns n)) := by
    rw [← hX]
    rfl
  have hright : iidCoverRadiusLaw R.limit k = sampledCoverRadiusLaw k p := by
    rw [← heq]
    rfl
  simpa only [hleft, hright, Function.comp_def] using R.tendsto_iidCoverRadiusLaw k

/-- Bounded continuous tests of the full carrier's sampled covering radius
are continuous observables of the measured-isometry class. -/
theorem continuous_sampledCoverRadiusIntegral (k : ℕ) (f : ℝ →ᵇ ℝ) :
    Continuous (fun X : MeasuredGHSpace.{u} ↦ ∫ r, f r ∂sampledCoverRadiusLaw k X) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    (continuous_sampledCoverRadiusLaw k)

theorem norm_sampledCoverRadiusIntegral_le (k : ℕ) (f : ℝ →ᵇ ℝ)
    (X : MeasuredGHSpace.{u}) :
    ‖∫ r, f r ∂sampledCoverRadiusLaw k X‖ ≤ ‖f‖ := by
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (sampledCoverRadiusLaw k X : Measure ℝ))
      (ae_of_all _ (fun r ↦ f.norm_coe_le_norm r)))

/-- A bounded continuous covering-radius test on the whole GHP quotient. -/
noncomputable def sampledCoverRadiusTest (k : ℕ) (f : ℝ →ᵇ ℝ) :
    MeasuredGHSpace.{u} →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun X ↦ ∫ r, f r ∂sampledCoverRadiusLaw k X, continuous_sampledCoverRadiusIntegral k f⟩
    (2 * ‖f‖) (by
      intro X Y
      change dist (∫ r, f r ∂sampledCoverRadiusLaw k X)
        (∫ r, f r ∂sampledCoverRadiusLaw k Y) ≤ 2 * ‖f‖
      exact (dist_le_norm_add_norm _ _).trans (by
        simpa only [two_mul] using add_le_add
          (norm_sampledCoverRadiusIntegral_le k f X) (norm_sampledCoverRadiusIntegral_le k f Y)))

/-- Weak convergence of random measured spaces preserves bounded tests of
every fixed finite covering radius. -/
theorem tendsto_sampledCoverRadiusTest_integral {ι : Type*} {l : Filter ι}
    {P : ι → ProbabilityMeasure MeasuredGHSpace.{u}}
    {Q : ProbabilityMeasure MeasuredGHSpace.{u}} (h : Tendsto P l (𝓝 Q))
    (k : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ X, ∫ r, f r ∂sampledCoverRadiusLaw k X ∂P n) l
      (𝓝 (∫ X, ∫ r, f r ∂sampledCoverRadiusLaw k X ∂Q)) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h (sampledCoverRadiusTest k f)

end MeasuredGHSpace
end Freezing2
