module

public import Freezing2.Geometry.GHPTransport
public import Mathlib.Topology.MetricSpace.Gluing

/-!
# Triangle inequality for the source measured GHP infimum

Two actual ambient realizations are glued isometrically along their common
middle space. The pushed middle measures and images then coincide. The
Prokhorov and Hausdorff triangle inequalities bound the summed cost; taking
arbitrarily close ambient costs proves the triangle inequality for the exact
infimum itself.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Classical

universe u

namespace Freezing2

variable {X Y Z : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Nonempty Y]
  [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z] [Nonempty Z]

omit [Nonempty Z] in
/-- Two admissible ambient costs give an admissible upper bound after gluing
along the whole middle space, preserving its probability measure exactly. -/
theorem ghpDistance_le_add_of_costs (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {a b : ℝ} (ha : a ∈ ghpCosts μ ν) (hb : b ∈ ghpCosts ν κ) :
    ghpDistance μ κ ≤ a + b := by
  obtain ⟨A, mA, i, j, hi, hj, rfl⟩ := ha
  obtain ⟨B, mB, k, l, hk, hl, rfl⟩ := hb
  let := mA
  let : TopologicalSpace A := mA.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let := mB
  let : TopologicalSpace B := mB.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace B := borel B
  let : BorelSpace B := ⟨rfl⟩
  let W := GlueSpace hj hk
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let p : A → W := toGlueL hj hk
  let q : B → W := toGlueR hj hk
  have hp : Isometry p := toGlueL_isometry hj hk
  have hq : Isometry q := toGlueR_isometry hj hk
  have hmiddle : p ∘ j = q ∘ k := toGlue_commute hj hk
  have hleft : levyProkhorovDist (μ.map (p ∘ i)) (ν.map (p ∘ j)) ≤
      levyProkhorovDist (μ.map i) (ν.map j) := by
    rw [← Measure.map_map hp.continuous.measurable hi.continuous.measurable,
      ← Measure.map_map hp.continuous.measurable hj.continuous.measurable]
    exact levyProkhorovDist_map_le _ _ hp.lipschitzWith
  have hright : levyProkhorovDist (ν.map (p ∘ j)) (κ.map (q ∘ l)) ≤
      levyProkhorovDist (ν.map k) (κ.map l) := by
    rw [hmiddle, ← Measure.map_map hq.continuous.measurable hk.continuous.measurable,
      ← Measure.map_map hq.continuous.measurable hl.continuous.measurable]
    exact levyProkhorovDist_map_le _ _ hq.lipschitzWith
  have hprob : levyProkhorovDist (μ.map (p ∘ i)) (κ.map (q ∘ l)) ≤
      levyProkhorovDist (μ.map i) (ν.map j) + levyProkhorovDist (ν.map k) (κ.map l) :=
    (levyProkhorovDist_triangle _ (ν.map (p ∘ j)) _).trans (add_le_add hleft hright)
  have hHleft : hausdorffDist (range (p ∘ i)) (range (p ∘ j)) =
      hausdorffDist (range i) (range j) := by
    rw [range_comp, range_comp, hausdorffDist_image hp]
  have hHright : hausdorffDist (range (p ∘ j)) (range (q ∘ l)) =
      hausdorffDist (range k) (range l) := by
    rw [hmiddle, range_comp, range_comp, hausdorffDist_image hq]
  have hfinite : hausdorffEDist (range (p ∘ i)) (range (p ∘ j)) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range (hp.continuous.comp hi.continuous)).isBounded
      (isCompact_range (hp.continuous.comp hj.continuous)).isBounded
  have hhaus : hausdorffDist (range (p ∘ i)) (range (q ∘ l)) ≤
      hausdorffDist (range i) (range j) + hausdorffDist (range k) (range l) := by
    simpa only [hHleft, hHright] using
      (hausdorffDist_triangle (u := range (q ∘ l)) hfinite)
  have hcost := ghpDistance_le_of_isometries μ κ W (p ∘ i) (q ∘ l)
    (hp.comp hi) (hq.comp hl)
  exact hcost.trans (by linarith)

omit [Nonempty Z] in
/-- The exact summed ambient-isometry GHP infimum obeys the triangle
inequality on nonempty compact probability spaces. -/
theorem ghpDistance_triangle (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] :
    ghpDistance μ κ ≤ ghpDistance μ ν + ghpDistance ν κ := by
  by_contra! h
  let ε : ℝ := (ghpDistance μ κ - (ghpDistance μ ν + ghpDistance ν κ)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨a, ha, ha'⟩ := exists_lt_of_csInf_lt (ghpCosts_nonempty μ ν)
    (show sInf (ghpCosts μ ν) < ghpDistance μ ν + ε by change ghpDistance μ ν < _; linarith)
  obtain ⟨b, hb, hb'⟩ := exists_lt_of_csInf_lt (ghpCosts_nonempty ν κ)
    (show sInf (ghpCosts ν κ) < ghpDistance ν κ + ε by change ghpDistance ν κ < _; linarith)
  have hbound := ghpDistance_le_add_of_costs μ ν κ ha hb
  dsimp [ε] at ha' hb'
  linarith

omit [Nonempty X] in
/-- A compact probability space has zero GHP distance from itself. -/
theorem ghpDistance_self (μ : Measure X) [IsProbabilityMeasure μ] : ghpDistance μ μ = 0 := by
  apply le_antisymm _ (ghpDistance_nonneg μ μ)
  have h := ghpDistance_le_of_isometries μ μ X id id isometry_id isometry_id
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  simpa only [hb, Measure.map_id, levyProkhorovDist_self, hausdorffDist_self_zero, add_zero] using h

end Freezing2
