module

public import Freezing2.Probability.SampledCoverRadius
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Full support detected by actual sampled covering radii

A nonempty open set of zero measure contains a null ball. Every finite iid
sample then misses that ball almost surely, so its full-carrier covering
radius stays bounded away from zero. This proves the support implication
without discarding zero-mass carrier points or assuming sample density.
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

universe u

namespace Freezing2

/-- A null ball forces every actual finite covering radius to exceed half
its radius with probability one. -/
theorem iidCoverRadiusLaw_tail_eq_one_of_null_ball (X : CompactMeasuredSpace.{u})
    (x : X) {r : ℝ} (hr : 0 < r) (hnull : (X.law : Measure X) (ball x r) = 0)
    (k : ℕ) :
    (iidCoverRadiusLaw X k : Measure ℝ) (Ioi (r / 2)) = 1 := by
  have ha : ∀ᵐ y ∂(X.law : Measure X), y ∉ ball x r := by
    exact measure_eq_zero_iff_ae_notMem.mp hnull
  have hp : ∀ᵐ v ∂Measure.pi (fun _ : Fin (k + 1) ↦ (X.law : Measure X)),
      ∀ i, v i ∉ ball x r :=
    eventually_all.mpr (fun i ↦ (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (k + 1) ↦ (X.law : Measure X)) (i := i)).eventually ha)
  have hm : Measurable (sampleCoverRadiusOn (fullCarrierCompact X) k) :=
    ((continuous_sampleCoverRadiusOn (X := X) k).comp
      (continuous_const.prodMk continuous_id)).measurable
  change (Measure.pi (fun _ : Fin (k + 1) ↦ (X.law : Measure X))).map
    (sampleCoverRadiusOn (fullCarrierCompact X) k) (Ioi (r / 2)) = 1
  rw [Measure.map_apply hm measurableSet_Ioi]
  apply (mem_ae_iff_prob_eq_one (measurableSet_Ioi.preimage hm)).mp
  filter_upwards [hp] with v hv
  have hlow : r ≤ infDist x (range v) := by
    apply (le_infDist (range_nonempty v)).mpr
    rintro _ ⟨i, rfl⟩
    simpa only [mem_ball, not_lt, dist_comm] using hv i
  have hfin : hausdorffEDist (univ : Set X) (range v) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded univ_nonempty (range_nonempty v)
      isCompact_univ.isBounded (finite_range v).isBounded
  have hbound := infDist_le_hausdorffDist_of_mem (mem_univ x) hfin
  change r / 2 < hausdorffDist (univ : Set X) (range v)
  exact (by linarith : r / 2 < r).trans_le (hlow.trans hbound)

/-- Failure of full support is visible at one fixed positive radius for
every number of samples. -/
theorem exists_coverRadius_tail_eq_one_of_not_fullSupport
    (X : CompactMeasuredSpace.{u})
    (h : ¬ Measure.IsOpenPosMeasure (X.law : Measure X)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, (iidCoverRadiusLaw X k : Measure ℝ) (Ioi ε) = 1 := by
  classical
  have hno : ¬ ∀ U : Set X, IsOpen U → U.Nonempty → (X.law : Measure X) U ≠ 0 :=
    fun hp ↦ h ⟨hp⟩
  push Not at hno
  obtain ⟨U, hU, ⟨x, hx⟩, hnull⟩ := hno
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨r / 2, by positivity, fun k ↦ iidCoverRadiusLaw_tail_eq_one_of_null_ball X x hr
    (measure_mono_null hball hnull) k⟩

/-- If finite iid samples approximate the whole carrier in probability,
the original probability measure has full support. -/
theorem fullSupport_of_tendsto_coverRadius_tail (X : CompactMeasuredSpace.{u})
    (h : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun k : ℕ ↦ (iidCoverRadiusLaw X k : Measure ℝ).real (Ioi ε)) atTop (𝓝 0)) :
    Measure.IsOpenPosMeasure (X.law : Measure X) := by
  by_contra hnot
  obtain ⟨ε, hε, htail⟩ := exists_coverRadius_tail_eq_one_of_not_fullSupport X hnot
  have hone : Tendsto (fun k : ℕ ↦ (iidCoverRadiusLaw X k : Measure ℝ).real (Ioi ε))
      atTop (𝓝 1) := by
    simpa only [Measure.real, htail, ENNReal.toReal_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique hone (h ε hε)
  norm_num at he

namespace CompactMeasuredSpace

theorem fullSupport_of_measuredIsometry {X Y : CompactMeasuredSpace.{u}}
    (h : X.MeasuredIsometry Y) (hX : Measure.IsOpenPosMeasure (X.law : Measure X)) :
    Measure.IsOpenPosMeasure (Y.law : Measure Y) := by
  let : Measure.IsOpenPosMeasure (X.law : Measure X) := hX
  obtain ⟨e, he⟩ := h
  have hmap := e.continuous.isOpenPosMeasure_map (μ := (X.law : Measure X)) e.surjective
  rwa [he] at hmap

theorem fullSupport_iff_of_measuredIsometry {X Y : CompactMeasuredSpace.{u}}
    (h : X.MeasuredIsometry Y) :
    Measure.IsOpenPosMeasure (X.law : Measure X) ↔
      Measure.IsOpenPosMeasure (Y.law : Measure Y) :=
  ⟨fullSupport_of_measuredIsometry h, fullSupport_of_measuredIsometry (measuredIsometry_symm h)⟩

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- Full support of the original measure on the entire carrier. -/
def HasFullSupport : MeasuredGHSpace.{u} → Prop :=
  Quotient.lift (fun X ↦ Measure.IsOpenPosMeasure (X.law : Measure X))
    (fun _ _ h ↦ propext (CompactMeasuredSpace.fullSupport_iff_of_measuredIsometry h))

@[simp] theorem hasFullSupport_toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) :
    HasFullSupport (toMeasuredGHSpace X) ↔ Measure.IsOpenPosMeasure (X.law : Measure X) := Iff.rfl

theorem hasFullSupport_of_tendsto_sampledCoverRadius_tail (X : MeasuredGHSpace.{u})
    (h : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun k : ℕ ↦ (sampledCoverRadiusLaw k X : Measure ℝ).real (Ioi ε)) atTop (𝓝 0)) :
    HasFullSupport X := by
  induction X using Quotient.inductionOn with
  | _ X => exact fullSupport_of_tendsto_coverRadius_tail X h

end MeasuredGHSpace
end Freezing2
