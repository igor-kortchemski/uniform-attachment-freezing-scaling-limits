module

public import Freezing2.Probability.SampledDistanceLaw
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Topology.MetricSpace.Closeds

/-!
# Actual iid covering radii

The covering radius compares the entire compact carrier with a nonempty
finite iid sample. Repetitions are retained in the sampling law. Whole-space
measured isometries preserve the law; points of zero sampling mass remain
part of the carrier in the Hausdorff distance.
-/

@[expose] public section

open MeasureTheory Metric Set TopologicalSpace
open scoped Topology

universe u

namespace Freezing2

/-- The nonempty compact range of a finite tuple. -/
def finiteSampleRange {X : Type*} [TopologicalSpace X] (k : ℕ)
    (v : Fin (k + 1) → X) : NonemptyCompacts X :=
  ⟨⟨range v, (finite_range v).isCompact⟩, range_nonempty v⟩

@[simp] theorem coe_finiteSampleRange {X : Type*} [TopologicalSpace X]
    (k : ℕ) (v : Fin (k + 1) → X) :
    (finiteSampleRange k v : Set X) = range v := rfl

theorem lipschitz_finiteSampleRange {X : Type*} [MetricSpace X] (k : ℕ) :
    LipschitzWith 1 (finiteSampleRange (X := X) k) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  change hausdorffDist (range v) (range w) ≤ dist v w
  apply hausdorffDist_le_of_mem_dist dist_nonneg
  · rintro _ ⟨i, rfl⟩
    exact ⟨w i, mem_range_self i, dist_le_pi_dist v w i⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨v i, mem_range_self i, by simpa only [dist_comm] using dist_le_pi_dist v w i⟩

/-- The Hausdorff radius relative to an arbitrary nonempty compact carrier. -/
noncomputable def sampleCoverRadiusOn {X : Type*} [MetricSpace X]
    (S : NonemptyCompacts X) (k : ℕ) (v : Fin (k + 1) → X) : ℝ :=
  dist S (finiteSampleRange k v)

theorem continuous_sampleCoverRadiusOn {X : Type*} [MetricSpace X] (k : ℕ) :
    Continuous (fun p : NonemptyCompacts X × (Fin (k + 1) → X) ↦
      sampleCoverRadiusOn p.1 k p.2) :=
  continuous_fst.dist ((lipschitz_finiteSampleRange k).continuous.comp continuous_snd)

theorem sampleCoverRadiusOn_isometry {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Isometry f) (S : NonemptyCompacts X) (k : ℕ)
    (v : Fin (k + 1) → X) :
    sampleCoverRadiusOn (S.map f hf.continuous) k (fun i ↦ f (v i)) =
      sampleCoverRadiusOn S k v := by
  change hausdorffDist (f '' (S : Set X)) (range (f ∘ v)) =
    hausdorffDist (S : Set X) (range v)
  rw [range_comp, hausdorffDist_image hf]

/-- The whole compact carrier, including all zero-mass points. -/
def fullCarrierCompact (X : Type*) [TopologicalSpace X] [CompactSpace X] [Nonempty X] :
    NonemptyCompacts X := ⟨⟨univ, isCompact_univ⟩, univ_nonempty⟩

theorem fullCarrierCompact_map_isometryEquiv {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (e : X ≃ᵢ Y) :
    (fullCarrierCompact X).map e e.continuous = fullCarrierCompact Y := by
  apply NonemptyCompacts.ext
  change e '' univ = univ
  exact image_univ.trans (range_eq_univ.mpr e.surjective)

section FixedAmbient

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

local instance : MeasurableSpace (NonemptyCompacts X) := borel _
local instance : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩

/-- Actual iid covering-radius law for a specified carrier in a common
ambient space. The measure need not have full support in that carrier. -/
noncomputable def iidCoverRadiusLawOn (S : NonemptyCompacts X)
    (μ : ProbabilityMeasure X) (k : ℕ) : ProbabilityMeasure ℝ :=
  (ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ μ)).map (sampleCoverRadiusOn S k)

theorem iidCoverRadiusLawOn_eq_dirac_prod (S : NonemptyCompacts X)
    (μ : ProbabilityMeasure X) (k : ℕ) :
    iidCoverRadiusLawOn S μ k =
      ((diracProba S).prod
        (ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ μ))).map
          (fun p ↦ sampleCoverRadiusOn p.1 k p.2) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.pi (fun _ : Fin (k + 1) ↦ (μ : Measure X))).map _ =
    ((Measure.dirac S).prod (Measure.pi (fun _ : Fin (k + 1) ↦ (μ : Measure X)))).map _
  rw [Measure.dirac_prod, Measure.map_map (continuous_sampleCoverRadiusOn k).measurable
    measurable_prodMk_left]
  rfl

/-- Simultaneous Hausdorff convergence of carriers and weak convergence of
their sampling measures gives convergence of the actual covering-radius law. -/
theorem continuous_iidCoverRadiusLawOn (k : ℕ) :
    Continuous (fun p : NonemptyCompacts X × ProbabilityMeasure X ↦
      iidCoverRadiusLawOn p.1 p.2 k) := by
  have hD : Continuous (fun p : NonemptyCompacts X × ProbabilityMeasure X ↦ diracProba p.1) :=
    (continuous_diracProba (X := NonemptyCompacts X)).comp continuous_fst
  have hP : Continuous (fun p : NonemptyCompacts X × ProbabilityMeasure X ↦
      ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ p.2)) :=
    ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ ↦ continuous_snd))
  have h := (ProbabilityMeasure.continuous_map (continuous_sampleCoverRadiusOn (X := X) k)).comp
    (ProbabilityMeasure.continuous_prod.comp (hD.prodMk hP))
  simpa only [iidCoverRadiusLawOn_eq_dirac_prod, Function.comp_def] using h

omit [SecondCountableTopology X] in
/-- Isometrically mapping both carrier and sampling measure preserves the
covering-radius law, even when the ambient map is not surjective. -/
theorem iidCoverRadiusLawOn_map_isometry {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (S : NonemptyCompacts X) (μ : ProbabilityMeasure X)
    (f : X → Y) (hf : Isometry f) (k : ℕ) :
    iidCoverRadiusLawOn (S.map f hf.continuous) (μ.map f) k = iidCoverRadiusLawOn S μ k := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.pi (fun _ : Fin (k + 1) ↦ (μ : Measure X).map f)).map _ =
    (Measure.pi (fun _ : Fin (k + 1) ↦ (μ : Measure X))).map _
  rw [← Measure.pi_map_pi (fun _ : Fin (k + 1) ↦ hf.continuous.measurable.aemeasurable)]
  have hm : Measurable (sampleCoverRadiusOn (S.map f hf.continuous) k) :=
    ((continuous_sampleCoverRadiusOn (X := Y) k).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hfm : Measurable f := hf.continuous.measurable
  rw [Measure.map_map hm (by fun_prop)]
  congr 1
  funext v
  exact sampleCoverRadiusOn_isometry f hf S k v

end FixedAmbient

/-- Actual iid law of the full carrier's covering radius for `k+1` samples. -/
noncomputable def iidCoverRadiusLaw (X : CompactMeasuredSpace.{u}) (k : ℕ) :
    ProbabilityMeasure ℝ :=
  (ProbabilityMeasure.pi (fun _ : Fin (k + 1) ↦ X.law)).map
    (sampleCoverRadiusOn (fullCarrierCompact X) k)

theorem iidCoverRadiusLaw_eq_of_measuredIsometry {X Y : CompactMeasuredSpace.{u}}
    (h : X.MeasuredIsometry Y) (k : ℕ) : iidCoverRadiusLaw X k = iidCoverRadiusLaw Y k := by
  obtain ⟨e, he⟩ := h
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.pi (fun _ : Fin (k + 1) ↦ (X.law : Measure X))).map _ =
    (Measure.pi (fun _ : Fin (k + 1) ↦ (Y.law : Measure Y))).map _
  rw [← he, ← Measure.pi_map_pi (fun _ : Fin (k + 1) ↦ e.continuous.measurable.aemeasurable)]
  have hm : Measurable (sampleCoverRadiusOn (fullCarrierCompact Y) k) :=
    ((continuous_sampleCoverRadiusOn (X := Y) k).comp
      (continuous_const.prodMk continuous_id)).measurable
  rw [Measure.map_map hm (by fun_prop)]
  congr 1
  funext v
  exact ((fullCarrierCompact_map_isometryEquiv e) ▸
    sampleCoverRadiusOn_isometry e e.isometry (fullCarrierCompact X) k v).symm

namespace MeasuredGHSpace

/-- Covering-radius law on whole-space measured-isometry classes. -/
noncomputable def sampledCoverRadiusLaw (k : ℕ) : MeasuredGHSpace.{u} → ProbabilityMeasure ℝ :=
  Quotient.lift (fun X ↦ iidCoverRadiusLaw X k)
    (fun _ _ h ↦ iidCoverRadiusLaw_eq_of_measuredIsometry h k)

@[simp] theorem sampledCoverRadiusLaw_toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) (k : ℕ) :
    sampledCoverRadiusLaw k (toMeasuredGHSpace X) = iidCoverRadiusLaw X k := rfl

end MeasuredGHSpace
end Freezing2
