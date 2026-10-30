module

public import Freezing2.Geometry.GHPSeparability
public import Freezing2.Geometry.GHPChainGluing
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The Gromov--Prokhorov space

Background subsection `GPdef` of the source (inventory items U49 and E09, GP
half; source issue S18).

A Polish measured space is a complete separable metric space with a Borel
probability law. Two such spaces are GP-isometric when a measure-preserving
isometry identifies the closed supports of their laws (`Measure.support`);
points outside the supports are ignored. The GP distance is the exact source
infimum, over common ambient metric spaces of the same universe and isometric
embeddings, of the Lévy--Prokhorov distance of the pushed laws.

Main results.
* `PolishMeasuredSpace.gpSetoid`: GP isometry is an equivalence relation;
  `GPSpace` is the quotient, the source's `𝕂_GP`.
* `gpDistance_triangle`, by gluing along the whole middle space.
* `PolishMeasuredSpace.distance_eq_zero_iff`: the GP distance vanishes exactly
  on GP-isometric pairs. Compactness of supports is not assumed: tightness and
  an ultrafilter limit produce the isometry
  (`exists_isometry_map_eq_of_levyProkhorovEDist_lt`).
* The metric space instance on `GPSpace`.
* `MeasuredGHSpace.gpProjection`: the natural projection from GHP classes,
  which is 1-Lipschitz, hence continuous and measurable, and is not injective
  (`MeasuredGHSpace.not_injective_gpProjection`, source issue S18).
* Separability (compact spaces are GP-dense) and completeness (successive
  gluing, tightness of Lévy--Prokhorov Cauchy sequences and Prokhorov's
  theorem), so `GPSpace.polishSpace` holds, as cited from ADH13.
-/

@[expose] public section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Topology ENNReal

universe u

namespace Freezing2

/-- A complete separable metric space with a Borel probability measure. -/
structure PolishMeasuredSpace where
  carrier : Type u
  metric : MetricSpace carrier
  complete : @CompleteSpace carrier metric.toUniformSpace
  separable : @SeparableSpace carrier metric.toUniformSpace.toTopologicalSpace
  measurable : MeasurableSpace carrier
  borel : @BorelSpace carrier metric.toUniformSpace.toTopologicalSpace measurable
  law : @ProbabilityMeasure carrier measurable

namespace PolishMeasuredSpace

instance : CoeSort PolishMeasuredSpace.{u} (Type u) := ⟨carrier⟩
instance (X : PolishMeasuredSpace) : MetricSpace X := X.metric
instance (X : PolishMeasuredSpace) : CompleteSpace X := X.complete
instance (X : PolishMeasuredSpace) : SeparableSpace X := X.separable
instance (X : PolishMeasuredSpace) : MeasurableSpace X := X.measurable
instance (X : PolishMeasuredSpace) : BorelSpace X := X.borel
instance (X : PolishMeasuredSpace) : Nonempty X :=
  nonempty_of_isProbabilityMeasure (X.law : Measure X)

/-- Bundle an existing Polish metric space and its actual probability law. -/
def of (X : Type u) [MetricSpace X] [CompleteSpace X] [SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) : PolishMeasuredSpace.{u} where
  carrier := X
  metric := inferInstance
  complete := inferInstance
  separable := inferInstance
  measurable := inferInstance
  borel := inferInstance
  law := μ

end PolishMeasuredSpace

section Support

variable {X : Type*} [MetricSpace X] [SeparableSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The law transported to its closed topological support. -/
noncomputable def supportLaw (μ : Measure X) : Measure μ.support :=
  μ.comap Subtype.val

omit [SeparableSpace X] in
/-- The support is closed, so its inclusion is a measurable embedding. -/
theorem measurableEmbedding_support_val (μ : Measure X) :
    MeasurableEmbedding (Subtype.val : μ.support → X) :=
  MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet

/-- No mass is lost by restricting a law on a separable metric space to its support. -/
theorem map_supportLaw (μ : Measure X) : (supportLaw μ).map Subtype.val = μ := by
  rw [supportLaw, (measurableEmbedding_support_val μ).map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem Measure.support_mem_ae

/-- The support law of a trace of a Borel set is the original mass. -/
theorem supportLaw_apply_preimage (μ : Measure X) {s : Set X} (hs : MeasurableSet s) :
    supportLaw μ (Subtype.val ⁻¹' s) = μ s := by
  conv_rhs => rw [← map_supportLaw μ]
  rw [Measure.map_apply measurable_subtype_coe hs]

instance (μ : Measure X) [IsProbabilityMeasure μ] : IsProbabilityMeasure (supportLaw μ) :=
  ⟨by simpa using supportLaw_apply_preimage μ MeasurableSet.univ⟩

/-- Every ball centred in the support has positive mass for the support law. -/
theorem supportLaw_ball_pos (μ : Measure X) (x : μ.support) {r : ℝ} (hr : 0 < r) :
    0 < supportLaw μ (ball x r) := by
  have hb : ball x r = Subtype.val ⁻¹' ball (x : X) r := rfl
  rw [hb, supportLaw_apply_preimage μ measurableSet_ball]
  exact (Measure.mem_support_iff_forall _).1 x.2 _ (ball_mem_nhds _ hr)

end Support

namespace PolishMeasuredSpace

/-- The source GP relation: a measure-preserving isometry between the
closed supports of the two laws. Points outside the supports are ignored. -/
def GPIsometric (X Y : PolishMeasuredSpace.{u}) : Prop :=
  ∃ e : (X.law : Measure X).support ≃ᵢ (Y.law : Measure Y).support,
    (supportLaw (X.law : Measure X)).map e = supportLaw (Y.law : Measure Y)

/-- Reflexivity of GP isometry. -/
theorem gpIsometric_refl (X : PolishMeasuredSpace.{u}) : GPIsometric X X :=
  ⟨IsometryEquiv.refl _, Measure.map_id⟩

/-- Symmetry of GP isometry. -/
theorem gpIsometric_symm {X Y : PolishMeasuredSpace.{u}} (h : GPIsometric X Y) :
    GPIsometric Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']

/-- Transitivity of GP isometry. -/
theorem gpIsometric_trans {X Y Z : PolishMeasuredSpace.{u}}
    (hXY : GPIsometric X Y) (hYZ : GPIsometric Y Z) : GPIsometric X Z := by
  obtain ⟨e, he⟩ := hXY
  obtain ⟨f, hf⟩ := hYZ
  refine ⟨e.trans f, ?_⟩
  change (supportLaw (X.law : Measure X)).map (f ∘ e) = _
  rw [← Measure.map_map f.continuous.measurable e.continuous.measurable, he, hf]

/-- The source GP-isometry-equivalence relation. -/
def gpSetoid : Setoid PolishMeasuredSpace.{u} where
  r := GPIsometric
  iseqv := ⟨gpIsometric_refl, gpIsometric_symm, gpIsometric_trans⟩

end PolishMeasuredSpace

section Costs

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y]

/-- All costs allowed by the source GP infimum over common metric spaces and
isometric embeddings. The ambient measurable structure is its Borel one. -/
def gpCosts (μ : Measure X) (ν : Measure Y) : Set ℝ :=
  {r | ∃ Z : Type u, ∃ m : MetricSpace Z,
    letI := m
    letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace Z := borel Z
    ∃ i : X → Z, ∃ j : Y → Z, Isometry i ∧ Isometry j ∧
      r = levyProkhorovDist (μ.map i) (ν.map j)}

/-- The source Gromov--Prokhorov infimum, before passage to classes. -/
noncomputable def gpDistance (μ : Measure X) (ν : Measure Y) : ℝ := sInf (gpCosts μ ν)

/-- Admissible costs are nonnegative. -/
theorem gpCosts_bddBelow (μ : Measure X) (ν : Measure Y) : BddBelow (gpCosts μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact ENNReal.toReal_nonneg

/-- The disjoint union supplies an admissible cost. -/
theorem gpCosts_nonempty (μ : Measure X) (ν : Measure Y) : (gpCosts μ ν).Nonempty := by
  let : MetricSpace (X ⊕ Y) := metricSpaceSum
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  refine ⟨_, X ⊕ Y, inferInstance, @Sum.inl X Y, @Sum.inr X Y, ?_, ?_, rfl⟩
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl

/-- The GP infimum is nonnegative. -/
theorem gpDistance_nonneg (μ : Measure X) (ν : Measure Y) : 0 ≤ gpDistance μ ν := by
  apply le_csInf (gpCosts_nonempty μ ν)
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact ENNReal.toReal_nonneg

/-- Any actual common ambient realization bounds the GP distance. -/
theorem gpDistance_le_of_isometries (μ : Measure X) (ν : Measure Y)
    (Z : Type u) [MetricSpace Z] (i : X → Z) (j : Y → Z) (hi : Isometry i) (hj : Isometry j) :
    letI : MeasurableSpace Z := borel Z
    gpDistance μ ν ≤ levyProkhorovDist (μ.map i) (ν.map j) := by
  apply csInf_le (gpCosts_bddBelow μ ν)
  exact ⟨Z, inferInstance, i, j, hi, hj, rfl⟩

/-- The same bound when the ambient space already carries its Borel structure. -/
theorem gpDistance_le_of_isometries_of_borelSpace (μ : Measure X) (ν : Measure Y)
    (Z : Type u) [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] (i : X → Z) (j : Y → Z)
    (hi : Isometry i) (hj : Isometry j) :
    gpDistance μ ν ≤ levyProkhorovDist (μ.map i) (ν.map j) := by
  have h := gpDistance_le_of_isometries μ ν Z i j hi hj
  obtain ⟨hb⟩ := ‹BorelSpace Z›
  subst hb
  exact h

/-- Exchanging the two embeddings exchanges the two laws. -/
theorem gpCosts_comm (μ : Measure X) (ν : Measure Y) : gpCosts μ ν = gpCosts ν μ := by
  apply Set.Subset.antisymm
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    exact ⟨Z, m, j, i, hj, hi, by simpa only [levyProkhorovDist_comm] using hr⟩
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    exact ⟨Z, m, j, i, hj, hi, by simpa only [levyProkhorovDist_comm] using hr⟩

/-- Symmetry of the GP infimum. -/
theorem gpDistance_comm (μ : Measure X) (ν : Measure Y) :
    gpDistance μ ν = gpDistance ν μ := by
  simp only [gpDistance, gpCosts_comm μ ν]

/-- A law has zero GP distance from itself. -/
theorem gpDistance_self [BorelSpace X] (μ : Measure X) : gpDistance μ μ = 0 := by
  apply le_antisymm _ (gpDistance_nonneg μ μ)
  have h := gpDistance_le_of_isometries μ μ X id id isometry_id isometry_id
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  simpa only [hb, Measure.map_id, levyProkhorovDist_self] using h

/-- Every GHP cost dominates the GP cost of the same ambient realization. -/
theorem gpDistance_le_ghpDistance [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : gpDistance μ ν ≤ ghpDistance μ ν := by
  apply le_csInf (ghpCosts_nonempty μ ν)
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact (csInf_le (gpCosts_bddBelow μ ν) ⟨Z, m, i, j, hi, hj, rfl⟩).trans
    (le_add_of_nonneg_right hausdorffDist_nonneg)

end Costs

section Triangle

variable {X Y W : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
  [MetricSpace W] [MeasurableSpace W] [BorelSpace W]

/-- Two admissible ambient costs glue along the whole middle space. -/
theorem gpDistance_le_add_of_costs (μ : Measure X) (ν : Measure Y) (κ : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {a b : ℝ} (ha : a ∈ gpCosts μ ν) (hb : b ∈ gpCosts ν κ) :
    gpDistance μ κ ≤ a + b := by
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
  let G := GlueSpace hj hk
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let p : A → G := toGlueL hj hk
  let q : B → G := toGlueR hj hk
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
  have hcost := gpDistance_le_of_isometries μ κ G (p ∘ i) (q ∘ l) (hp.comp hi) (hq.comp hl)
  exact hcost.trans ((levyProkhorovDist_triangle _ (ν.map (p ∘ j)) _).trans
    (add_le_add hleft hright))

/-- The exact GP infimum obeys the triangle inequality. -/
theorem gpDistance_triangle (μ : Measure X) (ν : Measure Y) (κ : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] :
    gpDistance μ κ ≤ gpDistance μ ν + gpDistance ν κ := by
  by_contra! h
  let ε : ℝ := (gpDistance μ κ - (gpDistance μ ν + gpDistance ν κ)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨a, ha, ha'⟩ := exists_lt_of_csInf_lt (gpCosts_nonempty μ ν)
    (show sInf (gpCosts μ ν) < gpDistance μ ν + ε by change gpDistance μ ν < _; linarith)
  obtain ⟨b, hb, hb'⟩ := exists_lt_of_csInf_lt (gpCosts_nonempty ν κ)
    (show sInf (gpCosts ν κ) < gpDistance ν κ + ε by change gpDistance ν κ < _; linarith)
  have hbound := gpDistance_le_add_of_costs μ ν κ ha hb
  dsimp [ε] at ha' hb'
  linarith

end Triangle

section Separation

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A ball of positive mass in the first space is matched, within a set of
nearly full second mass, by a point at ambient distance below radius plus
Prokhorov bound. -/
theorem exists_near_of_levyProkhorovEDist_lt {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (μ : Measure X) (ν : Measure Y) {i : X → Z} {j : Y → Z}
    (hi : Isometry i) (hj : Isometry j) {δ : ℝ≥0∞}
    (hP : levyProkhorovEDist (μ.map i) (ν.map j) < δ) (x : X) (r : ℝ) {L : Set Y}
    (hlt : ν Lᶜ + δ < μ (ball x r)) :
    ∃ y ∈ L, dist (i x) (j y) < δ.toReal + r := by
  by_contra! h
  have hb := left_measure_le_of_levyProkhorovEDist_lt hP (B := ball (i x) r) measurableSet_ball
  rw [Measure.map_apply hi.continuous.measurable measurableSet_ball, hi.preimage_ball,
    Measure.map_apply hj.continuous.measurable isOpen_thickening.measurableSet] at hb
  have hsub : j ⁻¹' thickening δ.toReal (ball (i x) r) ⊆ Lᶜ := by
    intro y hy hyL
    have hy' := Metric.thickening_ball (i x) δ.toReal r hy
    rw [mem_ball, dist_comm] at hy'
    exact (h y hyL).not_gt hy'
  have hle : μ (ball x r) ≤ ν Lᶜ + δ := hb.trans (by gcongr)
  exact absurd hlt (not_lt.2 hle)

/-- The analytic core of GP separation: if a law of full support on a Polish
space and a law on a Polish space admit common isometric realizations with
vanishing Prokhorov cost, then an isometry transports the first law onto the
second. Compactness of supports is not assumed: tightness of the second law
and an ultrafilter limit replace it. -/
theorem exists_isometry_map_eq_of_levyProkhorovEDist_lt
    [CompleteSpace X] [SeparableSpace X] [CompleteSpace Y] [SeparableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfull : ∀ (x : X) (r : ℝ), 0 < r → 0 < μ (ball x r))
    (Z : ℕ → Type*) [∀ n, MetricSpace (Z n)] [∀ n, MeasurableSpace (Z n)]
    [∀ n, BorelSpace (Z n)] (i : ∀ n, X → Z n) (j : ∀ n, Y → Z n)
    (hi : ∀ n, Isometry (i n)) (hj : ∀ n, Isometry (j n))
    (hP : ∀ n : ℕ, levyProkhorovEDist (μ.map (i n)) (ν.map (j n)) <
      ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    ∃ f : X → Y, Isometry f ∧ μ.map f = ν := by
  classical
  set ρ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hρ
  have hρpos : ∀ n, 0 < ρ n := fun n ↦ by positivity
  have hρlim : Tendsto ρ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hρanti : ∀ {m n : ℕ}, m ≤ n → ρ n ≤ ρ m := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hδlim : Tendsto (fun n ↦ ENNReal.ofReal (ρ n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hρlim
  have hδreal : ∀ n, (ENNReal.ofReal (ρ n)).toReal = ρ n :=
    fun n ↦ ENNReal.toReal_ofReal (hρpos n).le
  obtain ⟨y0⟩ : Nonempty Y := nonempty_of_isProbabilityMeasure ν
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  -- Step 1: for each point and scale, matched points staying in one compact set.
  have step1 : ∀ (x : X) (m : ℕ), ∃ y : ℕ → Y, ∃ z : Y, Tendsto y U (𝓝 z) ∧
      ∀ᶠ n in atTop, dist (i n x) (j n (y n)) < 2 * ρ m := by
    intro x m
    have hc := hfull x (ρ m) (hρpos m)
    have hc2 : 0 < μ (ball x (ρ m)) / 2 := ENNReal.half_pos hc.ne'
    obtain ⟨K, hK, hKc⟩ := exists_isCompact_closure_measure_compl_lt ν _ hc2
    have hLc : ν (closure K)ᶜ < μ (ball x (ρ m)) / 2 :=
      (measure_mono (compl_subset_compl.2 subset_closure)).trans_lt hKc
    have hev : ∀ᶠ n in atTop, ∃ y ∈ closure K, dist (i n x) (j n y) < 2 * ρ m := by
      have h1 : ∀ᶠ n in atTop, ENNReal.ofReal (ρ n) < μ (ball x (ρ m)) / 2 :=
        hδlim.eventually (gt_mem_nhds hc2)
      filter_upwards [h1, eventually_ge_atTop m] with n hn hmn
      have hlt : ν (closure K)ᶜ + ENNReal.ofReal (ρ n) < μ (ball x (ρ m)) :=
        calc _ < μ (ball x (ρ m)) / 2 + μ (ball x (ρ m)) / 2 := ENNReal.add_lt_add hLc hn
          _ = _ := ENNReal.add_halves _
      obtain ⟨y, hyL, hy⟩ := exists_near_of_levyProkhorovEDist_lt μ ν (hi n) (hj n)
        ((hP n).trans_le le_rfl) x (ρ m) hlt
      refine ⟨y, hyL, ?_⟩
      rw [hδreal] at hy
      linarith [hρanti hmn]
    have hch : ∀ n, ∃ y : Y, (∃ y' ∈ closure K, dist (i n x) (j n y') < 2 * ρ m) →
        y ∈ closure K ∧ dist (i n x) (j n y) < 2 * ρ m := by
      intro n
      by_cases h : ∃ y' ∈ closure K, dist (i n x) (j n y') < 2 * ρ m
      · obtain ⟨y', hy', h'⟩ := h
        exact ⟨y', fun _ ↦ ⟨hy', h'⟩⟩
      · exact ⟨y0, fun h' ↦ absurd h' h⟩
    choose y hy using hch
    have hev' : ∀ᶠ n in atTop, y n ∈ closure K ∧ dist (i n x) (j n (y n)) < 2 * ρ m :=
      hev.mono fun n hn ↦ hy n hn
    have hUL : (Ultrafilter.map y U : Filter Y) ≤ 𝓟 (closure K) := by
      rw [Ultrafilter.coe_map, le_principal_iff]
      exact hU (hev'.mono fun n hn ↦ hn.1)
    obtain ⟨z, -, hz⟩ := hK.ultrafilter_le_nhds _ hUL
    refine ⟨y, z, ?_, hev'.mono fun n hn ↦ hn.2⟩
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hz
  choose y z hz hnear using step1
  have hUe : ∀ {p : ℕ → Prop}, (∀ᶠ n in atTop, p n) → ∀ᶠ n in (U : Filter ℕ), p n :=
    fun h ↦ hU h
  -- Step 2: the limits are almost isometric, uniformly in the scales.
  have B1 : ∀ x x' m m', |dist (z x m) (z x' m') - dist x x'| ≤ 2 * ρ m + 2 * ρ m' := by
    intro x x' m m'
    have hlim : Tendsto (fun n ↦ |dist (y x m n) (y x' m' n) - dist x x'|) U
        (𝓝 |dist (z x m) (z x' m') - dist x x'|) :=
      (((hz x m).dist (hz x' m')).sub_const _).abs
    apply le_of_tendsto hlim
    filter_upwards [hUe (hnear x m), hUe (hnear x' m')] with n h1 h2
    have h := dist_dist_dist_le (j n (y x m n)) (j n (y x' m' n)) (i n x) (i n x')
    rw [(hj n).dist_eq, (hi n).dist_eq, Real.dist_eq, dist_comm (j n _) (i n x),
      dist_comm (j n _) (i n x')] at h
    linarith
  -- Step 3: the scales form Cauchy sequences; their limits define the isometry.
  have hcauchy : ∀ x, CauchySeq (z x) := by
    intro x
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ 4 * ρ N) (fun m m' N hm hm' ↦ ?_) ?_
    · have h := B1 x x m m'
      rw [dist_self, sub_zero, abs_of_nonneg dist_nonneg] at h
      linarith [hρanti hm, hρanti hm']
    · simpa using hρlim.const_mul 4
  choose f hf using fun x ↦ cauchySeq_tendsto_of_complete (hcauchy x)
  have hiso : Isometry f := by
    refine Isometry.of_dist_eq fun x x' ↦ ?_
    have hlim : Tendsto (fun m ↦ |dist (z x m) (z x' m) - dist x x'|) atTop
        (𝓝 |dist (f x) (f x') - dist x x'|) :=
      (((hf x).dist (hf x')).sub_const _).abs
    have h0 : Tendsto (fun m ↦ 2 * ρ m + 2 * ρ m) atTop (𝓝 0) := by
      simpa using (hρlim.const_mul 2).add (hρlim.const_mul 2)
    have h := abs_nonpos_iff.1 (le_of_tendsto_of_tendsto' hlim h0 fun m ↦ B1 x x' m m)
    linarith
  have B2 : ∀ x m, dist (z x m) (f x) ≤ 2 * ρ m := by
    intro x m
    have hlim : Tendsto (fun m' ↦ dist (z x m) (z x m')) atTop (𝓝 (dist (z x m) (f x))) :=
      tendsto_const_nhds.dist (hf x)
    have h0 : Tendsto (fun m' ↦ 2 * ρ m + 2 * ρ m') atTop (𝓝 (2 * ρ m)) := by
      simpa using (hρlim.const_mul 2).const_add (2 * ρ m)
    refine le_of_tendsto_of_tendsto' hlim h0 fun m' ↦ ?_
    have h := B1 x x m m'
    rwa [dist_self, sub_zero, abs_of_nonneg dist_nonneg] at h
  -- Step 4: the isometry transports the measure, by a quantitative estimate.
  refine ⟨f, hiso, ?_⟩
  have hfm : Measurable f := hiso.continuous.measurable
  have key : ∀ ε > 0, ∀ B, MeasurableSet B →
      μ.map f B ≤ ν (thickening (4 * ε) B) + ENNReal.ofReal (2 * ε) := by
    intro ε hε B hB
    obtain ⟨K0, hK0, hK0c⟩ :=
      exists_isCompact_closure_measure_compl_lt μ (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    have hKc : μ (closure K0)ᶜ < ENNReal.ofReal ε :=
      (measure_mono (compl_subset_compl.2 subset_closure)).trans_lt hK0c
    obtain ⟨T, -, hTfin, hcover⟩ := finite_cover_balls_of_compact hK0 hε
    set S : Finset X := hTfin.toFinset.filter
      (fun t ↦ ∃ x ∈ closure K0, f x ∈ B ∧ dist x t < ε) with hSdef
    have hS : ∀ t ∈ S, ∃ x ∈ closure K0, f x ∈ B ∧ dist x t < ε :=
      fun t ht ↦ (Finset.mem_filter.1 ht).2
    set V : Set X := ⋃ t ∈ S, ball t ε with hVdef
    have hcov : f ⁻¹' B ⊆ V ∪ (closure K0)ᶜ := by
      intro x hx
      by_cases hxK : x ∈ closure K0
      · obtain ⟨t, htT, hxt⟩ := mem_iUnion₂.1 (hcover hxK)
        exact Or.inl (mem_iUnion₂.2
          ⟨t, Finset.mem_filter.2 ⟨hTfin.mem_toFinset.2 htT, x, hxK, hx, hxt⟩, hxt⟩)
      · exact Or.inr hxK
    obtain ⟨m, hm⟩ : ∃ m, 5 * ρ m < ε :=
      ((hρlim.const_mul 5).eventually (gt_mem_nhds (by simpa using hε))).exists
    have hev : ∀ᶠ n in (U : Filter ℕ), (∀ t ∈ S, dist (i n t) (j n (y t m n)) < 2 * ρ m) ∧
        (∀ t ∈ S, dist (y t m n) (z t m) < ρ m) ∧ ρ n < ε :=
      (hUe ((eventually_all_finset S).2 fun t _ ↦ hnear t m)).and
        (((eventually_all_finset S).2 fun t _ ↦
          (hz t m).eventually (ball_mem_nhds _ (hρpos m))).and
          (hUe (hρlim.eventually (gt_mem_nhds hε))))
    obtain ⟨n, hn1, hn2, hn3⟩ := hev.exists
    set W : Set (Z n) := ⋃ t ∈ S, ball (i n t) ε with hWdef
    have hWm : MeasurableSet W := Finset.measurableSet_biUnion S fun t _ ↦ measurableSet_ball
    have hVW : i n ⁻¹' W = V := by
      simp only [hWdef, hVdef, preimage_iUnion₂, (hi n).preimage_ball]
    have h1 : μ.map f B ≤ μ V + ENNReal.ofReal ε := by
      rw [Measure.map_apply hfm hB]
      exact (measure_mono hcov).trans ((measure_union_le _ _).trans (by gcongr))
    have h2 : μ V ≤ ν (j n ⁻¹' thickening (ρ n) W) + ENNReal.ofReal (ρ n) := by
      have h := left_measure_le_of_levyProkhorovEDist_lt (hP n) hWm
      rwa [Measure.map_apply (hi n).continuous.measurable hWm, hVW,
        Measure.map_apply (hj n).continuous.measurable isOpen_thickening.measurableSet,
        hδreal] at h
    have h3 : j n ⁻¹' thickening (ρ n) W ⊆ thickening (4 * ε) B := by
      intro y' hy'
      obtain ⟨w, hw, hdw⟩ := mem_thickening_iff.1 hy'
      obtain ⟨t, htS, hwt⟩ := mem_iUnion₂.1 hw
      obtain ⟨x, -, hxB, hxt⟩ := hS t htS
      rw [mem_ball] at hwt
      refine mem_thickening_iff.2 ⟨f x, hxB, ?_⟩
      have e1 : dist y' (y t m n) < ρ n + ε + 2 * ρ m := by
        rw [← (hj n).dist_eq]
        calc dist (j n y') (j n (y t m n))
            ≤ dist (j n y') w + dist w (i n t) + dist (i n t) (j n (y t m n)) :=
              dist_triangle4 _ _ _ _
          _ < ρ n + ε + 2 * ρ m := by linarith [hn1 t htS]
      have e2 := hn2 t htS
      have e3 := B2 t m
      have e4 : dist (f t) (f x) < ε := by rw [hiso.dist_eq, dist_comm]; exact hxt
      have e5 := dist_triangle4 y' (y t m n) (z t m) (f t)
      have e6 := dist_triangle y' (f t) (f x)
      linarith
    calc μ.map f B ≤ μ V + ENNReal.ofReal ε := h1
      _ ≤ ν (j n ⁻¹' thickening (ρ n) W) + ENNReal.ofReal (ρ n) + ENNReal.ofReal ε := by
          gcongr
      _ ≤ ν (thickening (4 * ε) B) + ENNReal.ofReal ε + ENNReal.ofReal ε :=
          add_le_add (add_le_add (measure_mono h3) (ENNReal.ofReal_le_ofReal hn3.le)) le_rfl
      _ = ν (thickening (4 * ε) B) + ENNReal.ofReal (2 * ε) := by
          rw [add_assoc, ← ENNReal.ofReal_add hε.le hε.le, two_mul]
  have hLP : levyProkhorovDist (μ.map f) ν = 0 := by
    have hbound : ∀ ε > 0, levyProkhorovDist (μ.map f) ν ≤ 4 * ε := by
      intro ε hε
      apply levyProkhorovDist_le_of_forall_le _ _ (by positivity)
      intro ε' B hε' hB
      exact (key ε hε B hB).trans (add_le_add (measure_mono (thickening_mono hε'.le _))
        (ENNReal.ofReal_le_ofReal (by linarith)))
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra! hpos
    have hpos' : 0 < levyProkhorovDist (μ.map f) ν := hpos
    have h := hbound (levyProkhorovDist (μ.map f) ν / 8) (div_pos hpos' (by norm_num))
    linarith
  have heq := @eq_of_dist_eq_zero (LevyProkhorov (ProbabilityMeasure Y)) _
    (LevyProkhorov.ofMeasure ⟨μ.map f, inferInstance⟩)
    (LevyProkhorov.ofMeasure ⟨ν, inferInstance⟩)
    (by rw [LevyProkhorov.dist_probabilityMeasure_def]; exact hLP)
  have h2 := congrArg (fun P : LevyProkhorov (ProbabilityMeasure Y) ↦
    ((P.toMeasure : ProbabilityMeasure Y) : Measure Y)) heq
  exact h2

end Separation

section LevyProkhorovCompleteness

/-- An isometric embedding of a complete space cannot decrease the extended
Prokhorov distance. -/
theorem levyProkhorovEDist_le_map_of_isometry
    {X Y : Type*} [MetricSpace X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Isometry f) :
    levyProkhorovEDist μ ν ≤ levyProkhorovEDist (μ.map f) (ν.map f) := by
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε _ hB
  have hm : MeasurableEmbedding f := hf.isClosedEmbedding.measurableEmbedding
  have hi : MeasurableSet (f '' B) := hm.measurableSet_image.mpr hB
  have h := left_measure_le_of_levyProkhorovEDist_lt hε hi
  rw [Measure.map_apply hf.continuous.measurable hi,
    Measure.map_apply hf.continuous.measurable isOpen_thickening.measurableSet,
    hf.injective.preimage_image, preimage_thickening_image_of_isometry hf] at h
  exact h

variable {S : Type*} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A sequence of probability laws which is Cauchy for the Lévy--Prokhorov
distance, in the anchored form below, is tight. -/
theorem exists_isCompact_forall_measure_compl_le_of_anchored
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)]
    (h : ∀ δ > 0, ∃ N, ∀ n ≥ N, levyProkhorovEDist (ν N) (ν n) < ENNReal.ofReal δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set S, IsCompact K ∧ ∀ n, ν n Kᶜ ≤ ENNReal.ofReal ε := by
  classical
  set r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hr
  have hrpos : ∀ k, 0 < r k := fun k ↦ by positivity
  set δ : ℕ → ℝ := fun k ↦ ε / 2 / 2 ^ k / 2 with hδ
  have hδpos : ∀ k, 0 < δ k := fun k ↦ by positivity
  have step : ∀ k, ∃ G : Set S, IsOpen G ∧
      (∃ T : Set S, T.Finite ∧ G ⊆ ⋃ x ∈ T, ball x (2 * r k)) ∧
      ∀ n, ν n Gᶜ ≤ ENNReal.ofReal (2 * δ k) := by
    intro k
    obtain ⟨N, hN⟩ := h (min (δ k) (r k)) (lt_min (hδpos k) (hrpos k))
    have hcpt : ∀ j, ∃ C : Set S, IsCompact C ∧ ν j Cᶜ < ENNReal.ofReal (δ k) := by
      intro j
      obtain ⟨K, hK, hKc⟩ := exists_isCompact_closure_measure_compl_lt (ν j)
        (ENNReal.ofReal (δ k)) (ENNReal.ofReal_pos.2 (hδpos k))
      exact ⟨closure K, hK,
        (measure_mono (compl_subset_compl.2 subset_closure)).trans_lt hKc⟩
    choose C hC hCc using hcpt
    set D : Set S := ⋃ j ∈ Finset.range (N + 1), C j with hD
    have hDc : IsCompact D := (Finset.range (N + 1)).isCompact_biUnion fun j _ ↦ hC j
    have hDj : ∀ j ≤ N, ν j Dᶜ < ENNReal.ofReal (δ k) := by
      intro j hj
      refine (measure_mono (compl_subset_compl.2 ?_)).trans_lt (hCc j)
      exact subset_biUnion_of_mem (u := C) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    obtain ⟨T, -, hTfin, hcover⟩ := finite_cover_balls_of_compact hDc (hrpos k)
    set U : Set S := ⋃ x ∈ T, ball x (r k) with hU
    set G : Set S := ⋃ x ∈ T, ball x (2 * r k) with hG
    have hUG : U ⊆ G := iUnion₂_mono fun x _ ↦ ball_subset_ball (by linarith [hrpos k])
    have hGo : IsOpen G := isOpen_biUnion fun x _ ↦ isOpen_ball
    refine ⟨G, hGo, ⟨T, hTfin, subset_rfl⟩, fun n ↦ ?_⟩
    rcases le_or_gt n N with hn | hn
    · calc ν n Gᶜ ≤ ν n Dᶜ := measure_mono (compl_subset_compl.2 (hcover.trans hUG))
        _ ≤ ENNReal.ofReal (δ k) := (hDj n hn).le
        _ ≤ ENNReal.ofReal (2 * δ k) := ENNReal.ofReal_le_ofReal (by linarith [hδpos k])
    · have hLP := hN n hn.le
      have hUo : MeasurableSet U := (isOpen_biUnion fun x _ ↦ isOpen_ball).measurableSet
      have h1 := left_measure_le_of_levyProkhorovEDist_lt hLP hUo
      have hmin : (ENNReal.ofReal (min (δ k) (r k))).toReal = min (δ k) (r k) :=
        ENNReal.toReal_ofReal (le_min (hδpos k).le (hrpos k).le)
      rw [hmin] at h1
      have hthick : thickening (min (δ k) (r k)) U ⊆ G := by
        intro y hy
        obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hy
        obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 hw
        refine mem_iUnion₂.2 ⟨x, hx, ?_⟩
        rw [mem_ball] at hwx ⊢
        linarith [dist_triangle y w x, min_le_right (δ k) (r k)]
      have hUc : ν N Uᶜ ≤ ENNReal.ofReal (δ k) :=
        (measure_mono (compl_subset_compl.2 hcover)).trans (hDj N le_rfl).le
      have h2 : (1 : ℝ≥0∞) ≤ ν n G + ENNReal.ofReal (2 * δ k) := by
        calc (1 : ℝ≥0∞) = ν N U + ν N Uᶜ :=
              ((measure_add_measure_compl hUo).trans measure_univ).symm
          _ ≤ (ν n G + ENNReal.ofReal (min (δ k) (r k))) + ENNReal.ofReal (δ k) :=
              add_le_add (h1.trans (add_le_add (measure_mono hthick) le_rfl)) hUc
          _ ≤ (ν n G + ENNReal.ofReal (δ k)) + ENNReal.ofReal (δ k) :=
              add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (min_le_left _ _))) le_rfl
          _ = ν n G + ENNReal.ofReal (2 * δ k) := by
              rw [add_assoc, ← ENNReal.ofReal_add (hδpos k).le (hδpos k).le, two_mul]
      rw [prob_compl_eq_one_sub hGo.measurableSet]
      exact tsub_le_iff_left.2 h2
  choose G hGo hGcov hGc using step
  set T : Set S := ⋂ k, G k with hT
  have htb : TotallyBounded T := by
    rw [Metric.totallyBounded_iff]
    intro e he
    obtain ⟨k, hk⟩ : ∃ k, 2 * r k < e := by
      have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlim : Tendsto (fun k ↦ 2 * r k) atTop (𝓝 0) := by
        have h2 := hr0.const_mul 2
        rwa [mul_zero] at h2
      exact (hlim.eventually (gt_mem_nhds he)).exists
    obtain ⟨F, hF, hFcov⟩ := hGcov k
    exact ⟨F, hF, (iInter_subset _ k).trans (hFcov.trans
      (iUnion₂_mono fun x _ ↦ ball_subset_ball hk.le))⟩
  refine ⟨closure T, htb.closure.isCompact_of_isClosed isClosed_closure,
    fun n ↦ ?_⟩
  have hsum : ∑' k, ENNReal.ofReal (2 * δ k) = ENNReal.ofReal ε := by
    have heq : ∀ k, 2 * δ k = ε / 2 / 2 ^ k := fun k ↦ by simp only [hδ]; ring
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) (summable_geometric_two' ε),
      tsum_geometric_two' ε]
  calc ν n (closure T)ᶜ ≤ ν n Tᶜ := measure_mono (compl_subset_compl.2 subset_closure)
    _ = ν n (⋃ k, (G k)ᶜ) := by rw [hT, compl_iInter]
    _ ≤ ∑' k, ν n (G k)ᶜ := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (2 * δ k) := ENNReal.tsum_le_tsum fun k ↦ hGc k n
    _ = ENNReal.ofReal ε := hsum

/-- On a complete separable metric space, a sequence of probability laws that
is Cauchy for the Lévy--Prokhorov metric converges in that metric. -/
theorem exists_tendsto_levyProkhorovDist_of_cauchySeq (ν : ℕ → ProbabilityMeasure S)
    (hν : CauchySeq fun n ↦ LevyProkhorov.ofMeasure (ν n)) :
    ∃ ν₀ : ProbabilityMeasure S,
      Tendsto (fun n ↦ levyProkhorovDist (ν n : Measure S) (ν₀ : Measure S)) atTop (𝓝 0) := by
  have hanch : ∀ δ > 0, ∃ N, ∀ n ≥ N,
      levyProkhorovEDist (ν N : Measure S) (ν n : Measure S) < ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hν δ hδ
    refine ⟨N, fun n hn ↦ ?_⟩
    have h := hN n hn
    rw [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist_comm] at h
    exact (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 h
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure S) : Measure S) | μ ∈ range ν} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · exact ⟨∅, isCompact_empty, fun _ _ ↦ le_top⟩
    obtain ⟨K, hK, hKc⟩ := exists_isCompact_forall_measure_compl_le_of_anchored
      (fun n ↦ (ν n : Measure S)) hanch (ENNReal.toReal_pos hε.ne' hεtop)
    refine ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact (hKc n).trans (ENNReal.ofReal_toReal hεtop).le
  have hcpt := isCompact_closure_of_isTightMeasureSet htight
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := S)
  have hcpt' : IsCompact (e '' closure (range ν)) := hcpt.image e.continuous
  obtain ⟨v, -, hv⟩ := cauchySeq_tendsto_of_isComplete hcpt'.isComplete
    (fun n ↦ ⟨ν n, subset_closure ⟨n, rfl⟩, rfl⟩) hν
  refine ⟨v.toMeasure, ?_⟩
  refine Tendsto.congr (fun n ↦ ?_) (tendsto_iff_dist_tendsto_zero.1 hv)
  rw [LevyProkhorov.dist_probabilityMeasure_def]
  rfl

end LevyProkhorovCompleteness

section Bridge

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Vanishing exact GP infimum, for a first law of full support, yields an
isometry transporting it onto the second law. -/
theorem exists_isometry_map_eq_of_gpDistance_eq_zero
    [CompleteSpace X] [SeparableSpace X] [CompleteSpace Y] [SeparableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfull : ∀ (x : X) (r : ℝ), 0 < r → 0 < μ (ball x r)) (h : gpDistance μ ν = 0) :
    ∃ f : X → Y, Isometry f ∧ μ.map f = ν := by
  have hn : ∀ n : ℕ, ∃ Z : Type u, ∃ m : MetricSpace Z,
      letI := m
      letI : MeasurableSpace Z := borel Z
      ∃ i : X → Z, ∃ j : Y → Z, Isometry i ∧ Isometry j ∧
        levyProkhorovEDist (μ.map i) (ν.map j) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨r, ⟨Z, m, i, j, hi, hj, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (gpCosts_nonempty μ ν)
      (show sInf (gpCosts μ ν) < 1 / ((n : ℝ) + 1) by
        change gpDistance μ ν < _
        rw [h]
        positivity)
    refine ⟨Z, m, i, j, hi, hj, ?_⟩
    let := m
    let : MeasurableSpace Z := borel Z
    exact (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).2 hr
  choose Z m i j hi hj hP using hn
  let : ∀ n, MetricSpace (Z n) := m
  let : ∀ n, MeasurableSpace (Z n) := fun n ↦ borel (Z n)
  have : ∀ n, BorelSpace (Z n) := fun n ↦ ⟨rfl⟩
  exact exists_isometry_map_eq_of_levyProkhorovEDist_lt μ ν hfull Z i j hi hj hP

omit [BorelSpace Y] in
/-- Restricting the first law to its support does not increase the GP infimum. -/
theorem gpDistance_supportLaw_le [SeparableSpace X] (μ : Measure X) (ν : Measure Y) :
    gpDistance (supportLaw μ) ν ≤ gpDistance μ ν := by
  apply csInf_le_csInf (gpCosts_bddBelow _ ν) (gpCosts_nonempty μ ν)
  rintro r ⟨Z, m, i, j, hi, hj, hr⟩
  let := m
  let : MeasurableSpace Z := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  refine ⟨Z, m, i ∘ Subtype.val, j, hi.comp isometry_subtype_coe, hj, ?_⟩
  rw [← Measure.map_map hi.continuous.measurable measurable_subtype_coe, map_supportLaw]
  exact hr

end Bridge

namespace PolishMeasuredSpace

/-- The exact source GP infimum between represented Polish measured spaces. -/
noncomputable def distance (X Y : PolishMeasuredSpace.{u}) : ℝ :=
  gpDistance (X.law : Measure X) (Y.law : Measure Y)

/-- Nonnegativity of the represented GP distance. -/
theorem distance_nonneg (X Y : PolishMeasuredSpace.{u}) : 0 ≤ distance X Y :=
  gpDistance_nonneg _ _

/-- Symmetry of the represented GP distance. -/
theorem distance_comm (X Y : PolishMeasuredSpace.{u}) : distance X Y = distance Y X :=
  gpDistance_comm _ _

/-- A represented space has GP distance zero from itself. -/
theorem distance_self (X : PolishMeasuredSpace.{u}) : distance X X = 0 :=
  gpDistance_self _

/-- Triangle inequality for the represented GP distance. -/
theorem distance_triangle (X Y W : PolishMeasuredSpace.{u}) :
    distance X W ≤ distance X Y + distance Y W :=
  gpDistance_triangle _ _ _

/-- GP-isometric spaces are glued along their supports into one ambient space
in which the two pushed laws coincide exactly. -/
theorem distance_eq_zero_of_gpIsometric {X Y : PolishMeasuredSpace.{u}}
    (h : GPIsometric X Y) : distance X Y = 0 := by
  obtain ⟨e, he⟩ := h
  have : Nonempty (X.law : Measure X).support :=
    (Measure.nonempty_support (IsProbabilityMeasure.ne_zero _)).to_subtype
  have hΦ : Isometry (Subtype.val : (X.law : Measure X).support → X) := isometry_subtype_coe
  have hΨ : Isometry ((Subtype.val : (Y.law : Measure Y).support → Y) ∘ e) :=
    isometry_subtype_coe.comp e.isometry
  let G := GlueSpace hΦ hΨ
  let : MeasurableSpace G := _root_.borel G
  have : BorelSpace G := ⟨rfl⟩
  have hp : Isometry (toGlueL hΦ hΨ) := toGlueL_isometry hΦ hΨ
  have hq : Isometry (toGlueR hΦ hΨ) := toGlueR_isometry hΦ hΨ
  have hcomm := toGlue_commute hΦ hΨ
  have hmeas : (X.law : Measure X).map (toGlueL hΦ hΨ) =
      (Y.law : Measure Y).map (toGlueR hΦ hΨ) := by
    have h1 : (X.law : Measure X).map (toGlueL hΦ hΨ) =
        (supportLaw (X.law : Measure X)).map (toGlueL hΦ hΨ ∘ Subtype.val) := by
      rw [← Measure.map_map hp.continuous.measurable measurable_subtype_coe, map_supportLaw]
    have h2 : (Y.law : Measure Y).map (toGlueR hΦ hΨ) =
        (supportLaw (X.law : Measure X)).map ((toGlueR hΦ hΨ ∘ Subtype.val) ∘ e) := by
      rw [← Measure.map_map (hq.continuous.measurable.comp measurable_subtype_coe)
        e.continuous.measurable, he, ← Measure.map_map hq.continuous.measurable
        measurable_subtype_coe, map_supportLaw]
    rw [h1, h2, hcomm]
    rfl
  apply le_antisymm _ (gpDistance_nonneg _ _)
  have hle := gpDistance_le_of_isometries (X.law : Measure X) (Y.law : Measure Y) G _ _ hp hq
  rwa [hmeas, levyProkhorovDist_self] at hle

/-- A measure-preserving isometric embedding of the first support into the
second carrier is automatically onto the second support. -/
theorem gpIsometric_of_isometry {X Y : PolishMeasuredSpace.{u}}
    (f : (X.law : Measure X).support → Y) (hf : Isometry f)
    (hfμ : (supportLaw (X.law : Measure X)).map f = (Y.law : Measure Y)) :
    GPIsometric X Y := by
  have : IsClosed (X.law : Measure X).support := Measure.isClosed_support
  have hfm : Measurable f := hf.continuous.measurable
  have hclosed : IsClosed (range f) := hf.isClosedEmbedding.isClosed_range
  have hsub : range f ⊆ (Y.law : Measure Y).support := by
    rintro _ ⟨a, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro V hV
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
    calc 0 < supportLaw (X.law : Measure X) (ball a r) := supportLaw_ball_pos _ a hr
      _ = (Y.law : Measure Y) (ball (f a) r) := by
        rw [← hfμ, Measure.map_apply hfm measurableSet_ball, hf.preimage_ball]
      _ ≤ (Y.law : Measure Y) V := measure_mono hball
  have hsup : (Y.law : Measure Y).support ⊆ range f := by
    apply Measure.support_subset_of_isClosed hclosed
    rw [mem_ae_iff, ← hfμ, Measure.map_apply hfm hclosed.isOpen_compl.measurableSet]
    simp
  let g : (X.law : Measure X).support → (Y.law : Measure Y).support :=
    fun a ↦ ⟨f a, hsub ⟨a, rfl⟩⟩
  have hg : Isometry g := Isometry.of_dist_eq fun a a' ↦ hf.dist_eq a a'
  have hgs : Function.Surjective g := by
    rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := hsup hb
    exact ⟨a, rfl⟩
  let e : (X.law : Measure X).support ≃ᵢ (Y.law : Measure Y).support :=
    { Equiv.ofBijective g ⟨hg.injective, hgs⟩ with isometry_toFun := hg }
  refine ⟨e, ?_⟩
  have hval : (Subtype.val : (Y.law : Measure Y).support → Y) ∘ e = f := rfl
  rw [← (measurableEmbedding_support_val (Y.law : Measure Y)).comap_map
      ((supportLaw (X.law : Measure X)).map e),
    Measure.map_map measurable_subtype_coe e.continuous.measurable, hval, hfμ]
  rfl

/-- The source's literal formulation: an isometry `supp X → supp X'`, not
assumed surjective, pushing the first law to the second. Surjectivity is then
automatic, so this agrees with `GPIsometric`. -/
theorem gpIsometric_iff_exists_isometry (X Y : PolishMeasuredSpace.{u}) :
    GPIsometric X Y ↔ ∃ f : (X.law : Measure X).support → (Y.law : Measure Y).support,
      Isometry f ∧
        (supportLaw (X.law : Measure X)).map f = supportLaw (Y.law : Measure Y) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, e.isometry, he⟩
  · rintro ⟨f, hf, hfμ⟩
    apply gpIsometric_of_isometry (Subtype.val ∘ f) (isometry_subtype_coe.comp hf)
    rw [← Measure.map_map measurable_subtype_coe hf.continuous.measurable, hfμ, map_supportLaw]

/-- Vanishing GP distance forces a measure-preserving isometry between the
closed supports. No compactness of the supports is assumed. -/
theorem gpIsometric_of_distance_eq_zero {X Y : PolishMeasuredSpace.{u}}
    (h : distance X Y = 0) : GPIsometric X Y := by
  have : IsClosed (X.law : Measure X).support := Measure.isClosed_support
  have h' : gpDistance (supportLaw (X.law : Measure X)) (Y.law : Measure Y) = 0 :=
    le_antisymm ((gpDistance_supportLaw_le _ _).trans h.le) (gpDistance_nonneg _ _)
  obtain ⟨f, hf, hfμ⟩ := exists_isometry_map_eq_of_gpDistance_eq_zero
    (supportLaw (X.law : Measure X)) (Y.law : Measure Y)
    (fun x _ hr ↦ supportLaw_ball_pos _ x hr) h'
  exact gpIsometric_of_isometry f hf hfμ

/-- Separation in the source sense: the GP distance vanishes exactly on
GP-isometric pairs. -/
theorem distance_eq_zero_iff (X Y : PolishMeasuredSpace.{u}) :
    distance X Y = 0 ↔ GPIsometric X Y :=
  ⟨gpIsometric_of_distance_eq_zero, distance_eq_zero_of_gpIsometric⟩

/-- The represented GP distance is invariant under GP isometry in each argument. -/
theorem distance_congr {X Y X' Y' : PolishMeasuredSpace.{u}}
    (hX : GPIsometric X X') (hY : GPIsometric Y Y') : distance X Y = distance X' Y' := by
  have h1 := distance_eq_zero_of_gpIsometric hX
  have h2 := distance_eq_zero_of_gpIsometric hY
  have h3 := distance_eq_zero_of_gpIsometric (gpIsometric_symm hX)
  have h4 := distance_eq_zero_of_gpIsometric (gpIsometric_symm hY)
  have t1 := distance_triangle X X' Y
  have t2 := distance_triangle X' Y' Y
  have t3 := distance_triangle X' X Y'
  have t4 := distance_triangle X Y Y'
  rw [distance_comm Y' Y] at t2
  linarith

end PolishMeasuredSpace

/-- Polish measured spaces modulo measure-preserving isometry of the supports:
the source space `𝕂_GP`. -/
def GPSpace : Type (u + 1) := Quotient PolishMeasuredSpace.gpSetoid.{u}

/-- The GP class of a represented Polish measured space. -/
def toGPSpace (X : PolishMeasuredSpace.{u}) : GPSpace.{u} :=
  Quotient.mk PolishMeasuredSpace.gpSetoid X

namespace GPSpace

/-- The exact GP infimum descends to the quotient and is a genuine metric. -/
noncomputable instance : MetricSpace GPSpace.{u} where
  dist := Quotient.lift₂ PolishMeasuredSpace.distance
    (fun _ _ _ _ hX hY ↦ PolishMeasuredSpace.distance_congr hX hY)
  dist_self X := by
    induction X using Quotient.inductionOn with
    | _ X => exact PolishMeasuredSpace.distance_self X
  dist_comm X Y := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y => exact PolishMeasuredSpace.distance_comm X Y
  dist_triangle X Y Z := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        induction Z using Quotient.inductionOn with
        | _ Z => exact PolishMeasuredSpace.distance_triangle X Y Z
  eq_of_dist_eq_zero := by
    intro X Y h
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y => exact Quotient.sound (PolishMeasuredSpace.gpIsometric_of_distance_eq_zero h)

/-- The Borel structure of the GP topology. -/
noncomputable instance : MeasurableSpace GPSpace.{u} := borel _
instance : BorelSpace GPSpace.{u} := ⟨rfl⟩

/-- Distances in the quotient are literally the original ambient infima. -/
theorem dist_toGPSpace (X Y : PolishMeasuredSpace.{u}) :
    dist (toGPSpace X) (toGPSpace Y) = PolishMeasuredSpace.distance X Y := rfl

/-- Equality of GP classes is GP isometry of representatives. -/
theorem toGPSpace_eq_iff (X Y : PolishMeasuredSpace.{u}) :
    toGPSpace X = toGPSpace Y ↔ PolishMeasuredSpace.GPIsometric X Y :=
  Quotient.eq

end GPSpace

namespace CompactMeasuredSpace

/-- A compact measured space is a Polish measured space with the same
carrier, metric, measurable structure and law. -/
def toPolishMeasuredSpace (X : CompactMeasuredSpace.{u}) : PolishMeasuredSpace.{u} where
  carrier := X
  metric := inferInstance
  complete := inferInstance
  separable := inferInstance
  measurable := inferInstance
  borel := inferInstance
  law := X.law

/-- The GP distance is bounded by the source GHP distance. -/
theorem gpDistance_le_distance (X Y : CompactMeasuredSpace.{u}) :
    PolishMeasuredSpace.distance X.toPolishMeasuredSpace Y.toPolishMeasuredSpace ≤
      distance X Y :=
  gpDistance_le_ghpDistance (X.law : Measure X) (Y.law : Measure Y)

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- The natural projection from whole-space measured isometry classes to GP
classes. It is a projection, not an inclusion (source issue S18). -/
noncomputable def gpProjection : MeasuredGHSpace.{u} → GPSpace.{u} :=
  Quotient.lift (fun X : CompactMeasuredSpace.{u} ↦ toGPSpace X.toPolishMeasuredSpace) (by
    intro X Y h
    apply Quotient.sound
    apply PolishMeasuredSpace.gpIsometric_of_distance_eq_zero
    have h0 : CompactMeasuredSpace.distance X Y = 0 := by
      rw [← dist_toMeasuredGHSpace, (toMeasuredGHSpace_eq_iff X Y).2 h, dist_self]
    exact le_antisymm ((CompactMeasuredSpace.gpDistance_le_distance X Y).trans h0.le)
      (gpDistance_nonneg _ _))

/-- The projection keeps the carrier, metric and law of a representative. -/
@[simp] theorem gpProjection_toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) :
    gpProjection (toMeasuredGHSpace X) = toGPSpace X.toPolishMeasuredSpace := rfl

/-- The GHP-to-GP projection cannot increase distances. -/
theorem lipschitzWith_gpProjection : LipschitzWith 1 gpProjection.{u} := by
  apply LipschitzWith.mk_one
  intro X Y
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact CompactMeasuredSpace.gpDistance_le_distance X Y

/-- The GHP-to-GP projection is continuous. -/
theorem continuous_gpProjection : Continuous gpProjection.{u} :=
  lipschitzWith_gpProjection.continuous

/-- The GHP-to-GP projection is Borel measurable. -/
theorem measurable_gpProjection : Measurable gpProjection.{u} :=
  continuous_gpProjection.measurable

end MeasuredGHSpace

namespace PolishMeasuredSpace

/-- Every Polish measured space is GP-close to a compact measured space
carried by a compact subset of it: mass outside a large compact set is moved
to one of its points. -/
theorem exists_compact_distance_le (X : PolishMeasuredSpace.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : CompactMeasuredSpace.{u}, distance X Y.toPolishMeasuredSpace ≤ ε := by
  classical
  set μ : Measure X := (X.law : Measure X) with hμ
  obtain ⟨K0, hK0, hK0c⟩ :=
    exists_isCompact_closure_measure_compl_lt μ (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  obtain ⟨x0⟩ : Nonempty X := inferInstance
  set K : Set X := insert x0 (closure K0) with hKdef
  have hK : IsCompact K := hK0.insert x0
  have hKc : μ Kᶜ < ENNReal.ofReal ε :=
    (measure_mono (compl_subset_compl.2 (subset_closure.trans (subset_insert _ _)))).trans_lt
      hK0c
  have hx0 : x0 ∈ K := mem_insert _ _
  have : Nonempty K := ⟨⟨x0, hx0⟩⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let p : X → K := fun x ↦ if hx : x ∈ K then id (⟨x, hx⟩ : K) else (fun _ ↦ ⟨x0, hx0⟩) x
  have hp : Measurable p := Measurable.dite measurable_id measurable_const
    hK.isClosed.measurableSet
  have hpK : ∀ x ∈ K, (p x : X) = x := fun x hx ↦ by simp [p, hx]
  refine ⟨CompactMeasuredSpace.of K (⟨μ.map p, inferInstance⟩ : ProbabilityMeasure K), ?_⟩
  have hle := gpDistance_le_of_isometries_of_borelSpace μ (μ.map p) X id Subtype.val
    isometry_id isometry_subtype_coe
  rw [Measure.map_id] at hle
  refine hle.trans (levyProkhorovDist_le_of_forall_le _ _ hε.le fun ε' B hε' hB ↦ ?_)
  rw [Measure.map_map measurable_subtype_coe hp,
    Measure.map_apply (measurable_subtype_coe.comp hp) isOpen_thickening.measurableSet]
  have hsub : B ⊆ (Subtype.val ∘ p) ⁻¹' thickening ε' B ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      change (p x : X) ∈ thickening ε' B
      rw [hpK x hxK]
      exact self_subset_thickening (hε.trans hε') _ hx
    · exact Or.inr hxK
  calc μ B ≤ μ ((Subtype.val ∘ p) ⁻¹' thickening ε' B) + μ Kᶜ :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ μ ((Subtype.val ∘ p) ⁻¹' thickening ε' B) + ENNReal.ofReal ε' :=
        add_le_add le_rfl (hKc.le.trans (ENNReal.ofReal_le_ofReal hε'.le))

end PolishMeasuredSpace

namespace MeasuredGHSpace

/-- Compact measured spaces are GP-dense among Polish measured spaces. -/
theorem denseRange_gpProjection : DenseRange gpProjection.{u} := by
  refine Metric.denseRange_iff.2 fun P r hr ↦ ?_
  induction P using Quotient.inductionOn with
  | _ X =>
    obtain ⟨Y, hY⟩ := X.exists_compact_distance_le (half_pos hr)
    exact ⟨toMeasuredGHSpace Y, lt_of_le_of_lt hY (half_lt_self hr)⟩

end MeasuredGHSpace

namespace GPSpace

/-- The GP space is separable: the image of the separable GHP space under the
continuous projection is dense. -/
instance : SeparableSpace GPSpace.{u} :=
  MeasuredGHSpace.denseRange_gpProjection.separableSpace
    MeasuredGHSpace.continuous_gpProjection

end GPSpace

namespace CompactMeasuredSpace

/-- One point with its Dirac law. -/
noncomputable def onePoint : CompactMeasuredSpace.{u} :=
  of PUnit.{u + 1} ⟨Measure.dirac PUnit.unit, inferInstance⟩

/-- The unit segment with a Dirac law at one endpoint: its support is a point. -/
noncomputable def segmentDirac : CompactMeasuredSpace.{u} :=
  of (ULift.{u} unitInterval) ⟨Measure.dirac (ULift.up 0), inferInstance⟩

/-- A point and a segment are not isometric, so their GHP classes differ. -/
theorem not_measuredIsometry_onePoint_segmentDirac :
    ¬ MeasuredIsometry onePoint.{u} segmentDirac.{u} := by
  rintro ⟨e, -⟩
  have h : e.symm (ULift.up (0 : unitInterval)) = e.symm (ULift.up 1) :=
    Subsingleton.elim (α := PUnit.{u + 1}) _ _
  have h01 := ULift.up_injective (e.symm.injective h)
  exact absurd h01 (by simp)

/-- The point and the segment with an endpoint Dirac law have GP distance zero. -/
theorem distance_onePoint_segmentDirac :
    PolishMeasuredSpace.distance onePoint.{u}.toPolishMeasuredSpace
      segmentDirac.{u}.toPolishMeasuredSpace = 0 := by
  apply le_antisymm _ (gpDistance_nonneg _ _)
  have hle := gpDistance_le_of_isometries_of_borelSpace (Measure.dirac PUnit.unit)
    (Measure.dirac (ULift.up 0 : ULift.{u} unitInterval)) (ULift.{u} unitInterval)
    (fun _ ↦ ULift.up 0) id isometry_subsingleton isometry_id
  simp only [Measure.map_id, Measure.map_const, measure_univ, one_smul,
    levyProkhorovDist_self] at hle
  exact hle

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- Source issue S18: the GHP-to-GP map is a projection and not an
inclusion. A point of zero mass changes the GHP class but not the GP class. -/
theorem not_injective_gpProjection : ¬ Function.Injective gpProjection.{u} := by
  intro h
  have heq := h (a₁ := toMeasuredGHSpace CompactMeasuredSpace.onePoint)
    (a₂ := toMeasuredGHSpace CompactMeasuredSpace.segmentDirac) (by
      rw [gpProjection_toMeasuredGHSpace, gpProjection_toMeasuredGHSpace]
      exact Quotient.sound (PolishMeasuredSpace.gpIsometric_of_distance_eq_zero
        CompactMeasuredSpace.distance_onePoint_segmentDirac))
  exact CompactMeasuredSpace.not_measuredIsometry_onePoint_segmentDirac
    ((toMeasuredGHSpace_eq_iff _ _).1 heq)

end MeasuredGHSpace

namespace GPSpace

/-- A near-optimal actual GP realization, packaged as a common ambient
coupling of the two carriers. -/
theorem exists_coupling_levyProkhorovDist_lt {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
    [MetricSpace Y] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) {ε : ℝ}
    (hε : gpDistance μ ν < ε) :
    ∃ C : GHPCoupling X Y, levyProkhorovDist (μ.map C.left) (ν.map C.right) < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (gpCosts_nonempty μ ν) hε
  obtain ⟨A, m, i, j, hi, hj, rfl⟩ := hr
  let := m
  let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace A := _root_.borel A
  exact ⟨⟨A, m, i, j, hi, hj⟩, hlt⟩

/-- The GP space is complete. A fast Cauchy sequence is realized in one
complete ambient space by successive gluing; the closed separable hull of the
images is Polish, the pushed laws are Lévy--Prokhorov Cauchy there, and their
limit, given by Prokhorov's theorem, defines the limiting space. -/
noncomputable instance : CompleteSpace GPSpace.{u} := by
  let d : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  refine Metric.complete_of_convergent_controlled_sequences d (fun _ ↦ by positivity) ?_
  intro w hw
  let X : ℕ → PolishMeasuredSpace.{u} := fun n ↦ Quotient.out (w n)
  have hX (n : ℕ) : toGPSpace (X n) = w n := Quotient.out_eq (w n)
  have hdist (n : ℕ) : gpDistance ((X n).law : Measure (X n))
      ((X (n + 1)).law : Measure (X (n + 1))) < (1 / 2 : ℝ) ^ n := by
    have h := hw n n (n + 1) le_rfl (Nat.le_succ n)
    rw [← hX n, ← hX (n + 1)] at h
    exact h
  choose C hC using fun n ↦ exists_coupling_levyProkhorovDist_lt
    ((X n).law : Measure (X n)) ((X (n + 1)).law : Measure (X (n + 1))) (hdist n)
  obtain ⟨Z, m, hcomplete, ι, hι, hfactor⟩ :=
    GHPChain.exists_complete_realization (fun n ↦ (X n).carrier) C
  let := m
  let : MeasurableSpace Z := _root_.borel Z
  have : BorelSpace Z := ⟨rfl⟩
  set S : Set Z := closure (⋃ n, range (ι n)) with hSdef
  have hSsep : IsSeparable S :=
    (isSeparable_iUnion.2 fun n ↦ isSeparable_range (hι n).continuous).closure
  have : SeparableSpace S := hSsep.separableSpace
  have : IsClosed S := isClosed_closure
  have hmem : ∀ n x, ι n x ∈ S := fun n x ↦ subset_closure (mem_iUnion.2 ⟨n, mem_range_self x⟩)
  let κ : ∀ n, X n → S := fun n x ↦ ⟨ι n x, hmem n x⟩
  have hκ : ∀ n, Isometry (κ n) := fun n ↦ Isometry.of_dist_eq fun x y ↦ (hι n).dist_eq x y
  have hval : ∀ n, (Subtype.val : S → Z) ∘ κ n = ι n := fun n ↦ rfl
  let ν : ℕ → ProbabilityMeasure S := fun n ↦
    ⟨((X n).law : Measure (X n)).map (κ n), inferInstance⟩
  have hstep : ∀ n, dist (LevyProkhorov.ofMeasure (ν n)) (LevyProkhorov.ofMeasure (ν (n + 1))) ≤
      2 / 2 / 2 ^ n := by
    intro n
    rw [LevyProkhorov.dist_probabilityMeasure_def]
    obtain ⟨j, hj, hl, hr⟩ := hfactor n
    have h1 : levyProkhorovDist (((X n).law : Measure (X n)).map (κ n))
        (((X (n + 1)).law : Measure (X (n + 1))).map (κ (n + 1))) ≤
        levyProkhorovDist (((X n).law : Measure (X n)).map (ι n))
          (((X (n + 1)).law : Measure (X (n + 1))).map (ι (n + 1))) := by
      have h := levyProkhorovEDist_le_map_of_isometry
        (((X n).law : Measure (X n)).map (κ n))
        (((X (n + 1)).law : Measure (X (n + 1))).map (κ (n + 1))) (isometry_subtype_coe (s := S))
      rw [Measure.map_map measurable_subtype_coe (hκ n).continuous.measurable,
        Measure.map_map measurable_subtype_coe (hκ (n + 1)).continuous.measurable,
        hval, hval] at h
      exact ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _) h
    have h2 : levyProkhorovDist (((X n).law : Measure (X n)).map (ι n))
        (((X (n + 1)).law : Measure (X (n + 1))).map (ι (n + 1))) ≤
        levyProkhorovDist (((X n).law : Measure (X n)).map (C n).left)
          (((X (n + 1)).law : Measure (X (n + 1))).map (C n).right) := by
      rw [hl, hr, ← Measure.map_map hj.continuous.measurable
          (C n).left_isometry.continuous.measurable,
        ← Measure.map_map hj.continuous.measurable (C n).right_isometry.continuous.measurable]
      exact levyProkhorovDist_map_le _ _ hj.lipschitzWith
    have h3 := hC n
    have hd : (2 : ℝ) / 2 / 2 ^ n = (1 / 2) ^ n := by rw [div_self two_ne_zero, one_div_pow]
    rw [hd]
    exact h1.trans (h2.trans h3.le)
  obtain ⟨ν₀, hν₀⟩ := exists_tendsto_levyProkhorovDist_of_cauchySeq ν
    (cauchySeq_of_le_geometric_two hstep)
  refine ⟨toGPSpace (PolishMeasuredSpace.of S ν₀), ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hν₀
  rw [← hX n]
  have h := gpDistance_le_of_isometries_of_borelSpace ((X n).law : Measure (X n))
    (ν₀ : Measure S) S (κ n) id (hκ n) isometry_id
  rw [Measure.map_id] at h
  exact h

/-- The GP space is Polish, as asserted in the source (cited from ADH13). -/
theorem polishSpace : PolishSpace GPSpace.{u} := inferInstance

end GPSpace

end Freezing2
