module

public import Freezing2.Geometry.GHPCompleteness
public import Freezing2.Geometry.GromovProkhorov
public import Freezing2.Probability.GHPTightness
public import Freezing2.Probability.CoverRadiusSupport
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# GP and GH convergence give GHP convergence

Lemma `GP+GH=GHP` of the source (inventory N16, cited from [Bla21, Lemma 4]).
Let `Pₙ` and `Q` be laws of random compact measured spaces, that is, probability
measures on `MeasuredGHSpace`, and assume that `Q` is carried by fully supported
spaces. If the Gromov--Prokhorov projections of `Pₙ` converge weakly to that of
`Q`, and the underlying Gromov--Hausdorff projections of `Pₙ` converge weakly to
that of `Q`, then `Pₙ → Q` weakly in the GHP topology. No further hypothesis is
needed.

Proof.
* Tightness: weakly convergent GH laws have compact closure, hence are tight;
  GHP tightness is equivalent to GH tightness of the underlying spaces
  (`isTightMeasureSet_range_iff_underlyingGH`), and Prokhorov's theorem gives
  subsequential limits.
* Identification of a subsequential limit `R`: by continuity of both
  projections, `R` and `Q` have the same GP law and the same GH law. The two
  marginal laws do not determine the joint law of the pair (GP class, GH
  class), so the identification uses the following events.
  - For `ε > 0` and `k`, the support of the measure contains `k` points at
    pairwise distance above `ε`. This event is open in the GHP topology and
    is a union of fibres of the GP projection. By the Lusin separation theorem
    it is the preimage of a Borel set of GP classes, so `R` and `Q` give it the
    same mass.
  - Likewise the whole carrier contains `k` points at pairwise distance above
    `ε`. This event is open and a union of fibres of the GH projection.
  - The first event is contained in the second, and the two coincide on fully
    supported spaces. Hence their difference is `Q`-null, so `R`-null.
  - If a compact measured space is not fully supported, one point at positive
    distance from the support can be added to a maximal separated family of
    the support, at a small rational scale. So `R` is carried by fully
    supported spaces.
  - On fully supported spaces the GP projection is injective. The
    Lusin--Souslin separation argument then shows that two laws carried by
    such spaces with the same GP law are equal, so `R = Q`.
* Every subsequence then has a further subsequence converging to `Q`.

This file does not use the sampled-matrix reconstruction of
`SampledReconstruction.lean`, nor the GP matrix characterization.

## Main results

* `MeasuredGHSpace.ae_hasFullSupport_of_map_eq`: equal GP and GH laws and a
  fully supported `Q` force a fully supported `R`.
* `MeasuredGHSpace.eq_of_map_gpProjection_eq_of_map_underlyingGH_eq`: such
  laws coincide.
* `MeasuredGHSpace.tendsto_ghp_of_gp_of_gh`: Lemma `GP+GH=GHP`.
-/

@[expose] public section

open Filter MeasureTheory Metric Set Topology GromovHausdorff
open scoped ENNReal

universe u

namespace Freezing2

section LusinSeparation

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Lusin separation through a continuous map: a Borel set whose trace on a
Borel set `G` has image disjoint from the image of the complementary trace is,
on `G`, the preimage of a Borel set. -/
theorem exists_measurableSet_preimage_inter_eq {f : X → Y} (hf : Continuous f) {s G : Set X}
    (hs : MeasurableSet s) (hG : MeasurableSet G)
    (hdisj : Disjoint (f '' (s ∩ G)) (f '' (sᶜ ∩ G))) :
    ∃ C : Set Y, MeasurableSet C ∧ f ⁻¹' C ∩ G = s ∩ G := by
  obtain ⟨C, hsub, hCdisj, hC⟩ := AnalyticSet.measurablySeparable
    ((hs.inter hG).analyticSet.image_of_continuous hf)
    ((hs.compl.inter hG).analyticSet.image_of_continuous hf) hdisj
  refine ⟨C, hC, ?_⟩
  ext x
  constructor
  · rintro ⟨hxC, hxG⟩
    refine ⟨?_, hxG⟩
    by_contra hxs
    exact Set.disjoint_left.1 hCdisj (mem_image_of_mem f ⟨hxs, hxG⟩) hxC
  · rintro ⟨hxs, hxG⟩
    exact ⟨hsub (mem_image_of_mem f ⟨hxs, hxG⟩), hxG⟩

/-- Two measures with the same push-forward under a continuous map agree on a
Borel set whose traces on a common conull Borel set have disjoint images. -/
theorem measure_eq_of_map_eq_of_disjoint_image {f : X → Y} (hf : Continuous f)
    {μ ν : Measure X} (hmap : μ.map f = ν.map f) {s G : Set X} (hs : MeasurableSet s)
    (hG : MeasurableSet G) (hμ : μ Gᶜ = 0) (hν : ν Gᶜ = 0)
    (hdisj : Disjoint (f '' (s ∩ G)) (f '' (sᶜ ∩ G))) : μ s = ν s := by
  obtain ⟨C, hC, hCs⟩ := exists_measurableSet_preimage_inter_eq hf hs hG hdisj
  rw [← measure_inter_conull hμ, ← measure_inter_conull hν, ← hCs, measure_inter_conull hμ,
    measure_inter_conull hν, ← Measure.map_apply hf.measurable hC, hmap,
    Measure.map_apply hf.measurable hC]

/-- Two measures with the same push-forward under a continuous map agree on
every Borel set which is a union of fibres of that map. -/
theorem measure_preimage_eq_of_map_eq {f : X → Y} (hf : Continuous f) {μ ν : Measure X}
    (hmap : μ.map f = ν.map f) {V : Set Y} (hV : MeasurableSet (f ⁻¹' V)) :
    μ (f ⁻¹' V) = ν (f ⁻¹' V) := by
  refine measure_eq_of_map_eq_of_disjoint_image hf hmap hV MeasurableSet.univ (by simp)
    (by simp) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩ ⟨y, ⟨hy, -⟩, hxy⟩
  exact hy (by rw [mem_preimage, hxy]; exact hx)

/-- The Lusin--Souslin uniqueness argument: two measures carried by a Borel set
on which a continuous map is injective, and with the same push-forward, are
equal. -/
theorem eq_of_map_eq_of_injOn {f : X → Y} (hf : Continuous f) {μ ν : Measure X}
    (hmap : μ.map f = ν.map f) {G : Set X} (hG : MeasurableSet G) (hμ : μ Gᶜ = 0)
    (hν : ν Gᶜ = 0) (hinj : InjOn f G) : μ = ν := by
  ext s hs
  refine measure_eq_of_map_eq_of_disjoint_image hf hmap hs hG hμ hν ?_
  rw [Set.disjoint_left]
  rintro _ ⟨x, ⟨hx, hxG⟩, rfl⟩ ⟨y, ⟨hy, hyG⟩, hxy⟩
  exact hy (hinj hyG hxG hxy ▸ hx)

end LusinSeparation

section Separated

/-- A metric space contains `k` points whose pairwise distances exceed `ε`. -/
def HasSeparatedPoints (X : Type*) [PseudoMetricSpace X] (ε : ℝ) (k : ℕ) : Prop :=
  ∃ f : Fin k → X, Pairwise fun a b ↦ ε < dist (f a) (f b)

/-- The empty family is separated at every scale. -/
theorem hasSeparatedPoints_zero (X : Type*) [PseudoMetricSpace X] (ε : ℝ) :
    HasSeparatedPoints X ε 0 :=
  ⟨Fin.elim0, fun a ↦ a.elim0⟩

/-- Separated families are transported by isometric embeddings. -/
theorem HasSeparatedPoints.of_isometry {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {g : X → Y} (hg : Isometry g) {ε : ℝ} {k : ℕ} (h : HasSeparatedPoints X ε k) :
    HasSeparatedPoints Y ε k := by
  obtain ⟨f, hf⟩ := h
  exact ⟨g ∘ f, fun a b hab ↦ by simpa only [Function.comp_apply, hg.dist_eq] using hf hab⟩

/-- A finite strictly separated family has a uniform positive margin. -/
theorem exists_pos_add_two_mul_le_of_pairwise {k : ℕ} {d : Fin k → Fin k → ℝ} {ε : ℝ}
    (h : Pairwise fun a b ↦ ε < d a b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a b, a ≠ b → ε + 2 * ρ ≤ d a b := by
  have hev : ∀ᶠ ρ in 𝓝 (0 : ℝ), ∀ p : Fin k × Fin k, p.1 ≠ p.2 → ε + 2 * ρ < d p.1 p.2 := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h ↦ absurd hp h
    · have hc : Continuous fun ρ : ℝ ↦ ε + 2 * ρ := by fun_prop
      have h0 : ε + 2 * 0 < d p.1 p.2 := by simpa using h hp
      filter_upwards [(hc.tendsto 0).eventually (gt_mem_nhds h0)] with ρ hρ _ using hρ
  obtain ⟨ρ, hρ, hρpos⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨ρ, hρpos, fun a b hab ↦ (hρ (a, b) hab).le⟩

/-- Points matched, within the margin, to a separated family are separated. -/
theorem pairwise_lt_dist_of_near {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z] {i : X → Z} {j : Y → Z} (hi : Isometry i) (hj : Isometry j) {k : ℕ}
    {f : Fin k → X} {g : Fin k → Y} {ε ρ : ℝ}
    (hf : ∀ a b, a ≠ b → ε + 2 * ρ ≤ dist (f a) (f b))
    (hfg : ∀ a, dist (i (f a)) (j (g a)) < ρ) :
    Pairwise fun a b ↦ ε < dist (g a) (g b) := by
  intro a b hab
  have h1 := hf a b hab
  have h2 := hfg a
  have h3 := hfg b
  have h4 := dist_triangle4 (i (f a)) (j (g a)) (j (g b)) (i (f b))
  rw [hi.dist_eq, hj.dist_eq, dist_comm (j (g b))] at h4
  linarith

/-- Separated families in a compact space have bounded cardinality. -/
theorem exists_bound_of_hasSeparatedPoints {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k, HasSeparatedPoints s ε k → k ≤ K := by
  obtain ⟨t, -, htfin, hcover⟩ := finite_cover_balls_of_compact hs (half_pos hε)
  have : Finite t := htfin.to_subtype
  refine ⟨Nat.card t, ?_⟩
  rintro k ⟨f, hf⟩
  have hc : ∀ a, ∃ c : t, (f a : X) ∈ ball (c : X) (ε / 2) := by
    intro a
    obtain ⟨c, hc, hfc⟩ := mem_iUnion₂.1 (hcover (f a).2)
    exact ⟨⟨c, hc⟩, hfc⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    have h1 := hc a
    have h2 := hc b
    rw [hab, mem_ball] at h1
    rw [mem_ball] at h2
    have h3 : ε < dist (f a : X) (f b : X) := hf hne
    have h4 := dist_triangle_right (f a : X) (f b : X) (c b : X)
    linarith
  simpa using Nat.card_le_card_of_injective c hinj

end Separated

namespace GPSpace

/-- The support of the law contains `k` points at pairwise distance above `ε`.
This depends only on the GP class. -/
def SupportSeparated (ε : ℝ) (k : ℕ) : GPSpace.{u} → Prop :=
  Quotient.lift (fun X : PolishMeasuredSpace.{u} ↦ HasSeparatedPoints (X.law : Measure X).support ε k)
    (fun _ _ h ↦ by
      obtain ⟨e, -⟩ := h
      exact propext ⟨fun hX ↦ hX.of_isometry e.isometry, fun hY ↦ hY.of_isometry e.symm.isometry⟩)

end GPSpace

/-- Separated families of a compact space and of its GH representative agree. -/
theorem hasSeparatedPoints_rep_toGHSpace (X : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] {ε : ℝ} {k : ℕ} :
    HasSeparatedPoints (toGHSpace X).Rep ε k ↔ HasSeparatedPoints X ε k := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.1 (GHSpace.toGHSpace_rep (toGHSpace X))
  exact ⟨fun h ↦ h.of_isometry e.isometry, fun h ↦ h.of_isometry e.symm.isometry⟩

namespace CompactMeasuredSpace

/-- A small GHP distance is witnessed by one ambient realization with small
Prokhorov and Hausdorff costs. -/
theorem exists_realization_of_distance_lt {X Y : CompactMeasuredSpace.{u}} {η : ℝ}
    (h : distance X Y < η) :
    ∃ (Z : Type u) (_ : MetricSpace Z) (_ : MeasurableSpace Z) (_ : BorelSpace Z)
      (i : X → Z) (j : Y → Z), Isometry i ∧ Isometry j ∧
      levyProkhorovEDist ((X.law : Measure X).map i) ((Y.law : Measure Y).map j) <
        ENNReal.ofReal η ∧
      hausdorffDist (range i) (range j) < η := by
  obtain ⟨r, ⟨Z, m, i, j, hi, hj, rfl⟩, hr⟩ :=
    exists_lt_of_csInf_lt (ghpCosts_nonempty _ _) (show sInf (ghpCosts _ _) < η from h)
  let := m
  let : MeasurableSpace Z := _root_.borel Z
  have : BorelSpace Z := ⟨rfl⟩
  have hP : 0 ≤ levyProkhorovDist ((X.law : Measure X).map i) ((Y.law : Measure Y).map j) :=
    ENNReal.toReal_nonneg
  have hH : 0 ≤ hausdorffDist (range i) (range j) := hausdorffDist_nonneg
  refine ⟨Z, m, _root_.borel Z, ⟨rfl⟩, i, j, hi, hj, ?_, by linarith⟩
  rw [ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)]
  change levyProkhorovDist _ _ < η
  linarith

end CompactMeasuredSpace

namespace MeasuredGHSpace

/-- Classes whose measure support contains `k` points at pairwise distance
above `ε`: a union of fibres of the GP projection. -/
def supportSeparatedSet (ε : ℝ) (k : ℕ) : Set MeasuredGHSpace.{u} :=
  gpProjection ⁻¹' {p | GPSpace.SupportSeparated ε k p}

/-- Classes whose whole carrier contains `k` points at pairwise distance above
`ε`: a union of fibres of the GH projection. -/
def carrierSeparatedSet (ε : ℝ) (k : ℕ) : Set MeasuredGHSpace.{u} :=
  underlyingGH ⁻¹' {p | HasSeparatedPoints p.Rep ε k}

/-- Membership in the support event, read on a representative. -/
theorem mem_supportSeparatedSet (X : CompactMeasuredSpace.{u}) {ε : ℝ} {k : ℕ} :
    toMeasuredGHSpace X ∈ supportSeparatedSet ε k ↔
      HasSeparatedPoints (X.law : Measure X).support ε k :=
  Iff.rfl

/-- Membership in the carrier event, read on a representative. -/
theorem mem_carrierSeparatedSet (X : CompactMeasuredSpace.{u}) {ε : ℝ} {k : ℕ} :
    toMeasuredGHSpace X ∈ carrierSeparatedSet ε k ↔ HasSeparatedPoints X ε k :=
  hasSeparatedPoints_rep_toGHSpace X

/-- Separated support points persist under small GHP perturbations. -/
theorem isOpen_supportSeparatedSet (ε : ℝ) (k : ℕ) :
    IsOpen (supportSeparatedSet.{u} ε k) := by
  rw [Metric.isOpen_iff]
  intro Y hY
  induction Y using Quotient.inductionOn with
  | _ X =>
  obtain ⟨f, hf⟩ := (mem_supportSeparatedSet X).1 hY
  obtain ⟨ρ, hρ, hfρ⟩ := exists_pos_add_two_mul_le_of_pairwise hf
  have hmass : ∀ a, 0 < (X.law : Measure X) (ball (f a : X) (ρ / 2)) := fun a ↦
    (Measure.mem_support_iff_forall _).1 (f a).2 _ (ball_mem_nhds _ (half_pos hρ))
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < ρ / 2 ∧
      ∀ a, ENNReal.ofReal δ < (X.law : Measure X) (ball (f a : X) (ρ / 2)) := by
    refine (gt_mem_nhds (half_pos hρ)).and (eventually_all.2 fun a ↦ ?_)
    have hc : Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.continuous_ofReal.tendsto 0
    rw [ENNReal.ofReal_zero] at hc
    exact hc.eventually (gt_mem_nhds (hmass a))
  obtain ⟨δ, ⟨hδρ, hδm⟩, hδ⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  refine ⟨δ, hδ, fun Y' hY' ↦ ?_⟩
  induction Y' using Quotient.inductionOn with
  | _ X' =>
  have hd : CompactMeasuredSpace.distance X X' < δ := by
    rw [← dist_toMeasuredGHSpace, dist_comm]
    exact hY'
  obtain ⟨Z, _, _, _, i, j, hi, hj, hP, -⟩ :=
    CompactMeasuredSpace.exists_realization_of_distance_lt hd
  have hnull : (X'.law : Measure X') ((X'.law : Measure X').support)ᶜ = 0 :=
    mem_ae_iff.1 Measure.support_mem_ae
  have hnear : ∀ a, ∃ y : (X'.law : Measure X').support, dist (i (f a)) (j y) < ρ := by
    intro a
    obtain ⟨y, hy, hdist⟩ := exists_near_of_levyProkhorovEDist_lt (X.law : Measure X)
      (X'.law : Measure X') hi hj hP (f a) (ρ / 2) (L := (X'.law : Measure X').support)
      (by rw [hnull, zero_add]; exact hδm a)
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [ENNReal.toReal_ofReal (le_of_lt hδ)] at hdist
    change dist (i (f a)) (j y) < ρ
    linarith
  choose g hg using hnear
  exact (mem_supportSeparatedSet X').2 ⟨g, pairwise_lt_dist_of_near
    (hi.comp isometry_subtype_coe) (hj.comp isometry_subtype_coe) hfρ hg⟩

/-- Separated carrier points persist under small GHP perturbations. -/
theorem isOpen_carrierSeparatedSet (ε : ℝ) (k : ℕ) :
    IsOpen (carrierSeparatedSet.{u} ε k) := by
  rw [Metric.isOpen_iff]
  intro Y hY
  induction Y using Quotient.inductionOn with
  | _ X =>
  obtain ⟨f, hf⟩ := (mem_carrierSeparatedSet X).1 hY
  obtain ⟨ρ, hρ, hfρ⟩ := exists_pos_add_two_mul_le_of_pairwise hf
  refine ⟨ρ, hρ, fun Y' hY' ↦ ?_⟩
  induction Y' using Quotient.inductionOn with
  | _ X' =>
  have hd : CompactMeasuredSpace.distance X X' < ρ := by
    rw [← dist_toMeasuredGHSpace, dist_comm]
    exact hY'
  obtain ⟨Z, _, _, _, i, j, hi, hj, -, hH⟩ :=
    CompactMeasuredSpace.exists_realization_of_distance_lt hd
  have hfin : hausdorffEDist (range i) (range j) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty i) (range_nonempty j)
      (isCompact_range hi.continuous).isBounded (isCompact_range hj.continuous).isBounded
  have hnear : ∀ a, ∃ y : X', dist (i (f a)) (j y) < ρ := by
    intro a
    obtain ⟨_, ⟨y, rfl⟩, hdist⟩ :=
      exists_dist_lt_of_hausdorffDist_lt (mem_range_self (f a)) hH hfin
    exact ⟨y, hdist⟩
  choose g hg using hnear
  exact (mem_carrierSeparatedSet X').2 ⟨g, pairwise_lt_dist_of_near hi hj hfρ hg⟩

/-- Separated support points are separated carrier points. -/
theorem supportSeparatedSet_subset (ε : ℝ) (k : ℕ) :
    supportSeparatedSet.{u} ε k ⊆ carrierSeparatedSet ε k := by
  intro Y hY
  induction Y using Quotient.inductionOn with
  | _ X =>
  exact (mem_carrierSeparatedSet X).2
    (((mem_supportSeparatedSet X).1 hY).of_isometry isometry_subtype_coe)

/-- For a fully supported space the two separation events coincide. -/
theorem mem_supportSeparatedSet_of_hasFullSupport {Y : MeasuredGHSpace.{u}}
    (hY : HasFullSupport Y) {ε : ℝ} {k : ℕ} (h : Y ∈ carrierSeparatedSet ε k) :
    Y ∈ supportSeparatedSet ε k := by
  induction Y using Quotient.inductionOn with
  | _ X =>
  have : Measure.IsOpenPosMeasure (X.law : Measure X) := hY
  obtain ⟨f, hf⟩ := (mem_carrierSeparatedSet X).1 h
  have hmem : ∀ x : X, x ∈ (X.law : Measure X).support := fun x ↦ by
    rw [Measure.support_eq_univ]
    exact mem_univ x
  exact (mem_supportSeparatedSet X).2 ⟨fun a ↦ ⟨f a, hmem (f a)⟩, hf⟩

/-- If at every rational scale each separated family of the carrier is matched
by one of the support, the measure has full support: a point at positive
distance from the support enlarges a maximal separated family of the support. -/
theorem hasFullSupport_of_forall_mem_supportSeparatedSet {Y : MeasuredGHSpace.{u}}
    (h : ∀ n k : ℕ, Y ∈ carrierSeparatedSet (1 / ((n : ℝ) + 1)) k →
      Y ∈ supportSeparatedSet (1 / ((n : ℝ) + 1)) k) :
    HasFullSupport Y := by
  classical
  induction Y using Quotient.inductionOn with
  | _ X =>
  change Measure.IsOpenPosMeasure (X.law : Measure X)
  by_contra hnot
  have hno : ¬ ∀ U : Set X, IsOpen U → U.Nonempty → (X.law : Measure X) U ≠ 0 :=
    fun hp ↦ hnot ⟨hp⟩
  push Not at hno
  obtain ⟨U, hU, ⟨x, hx⟩, hnull⟩ := hno
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hfar : ∀ z ∈ (X.law : Measure X).support, r ≤ dist x z := by
    intro z hz
    by_contra hlt
    have hz' : z ∈ ball x r := by
      rw [mem_ball, dist_comm]
      exact not_le.1 hlt
    exact Measure.subset_compl_support_of_isOpen isOpen_ball (measure_mono_null hball hnull)
      hz' hz
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨K, hK⟩ := exists_bound_of_hasSeparatedPoints
    (Measure.isClosed_support (μ := (X.law : Measure X))).isCompact hεpos
  set S : ℕ → Prop := fun k ↦ HasSeparatedPoints (X.law : Measure X).support ε k with hS
  set k₀ := Nat.findGreatest S K with hk₀
  have hk₀S : S k₀ := Nat.findGreatest_spec (Nat.zero_le K) (hasSeparatedPoints_zero _ ε)
  have hk₁ : ¬ S (k₀ + 1) := fun h₁ ↦
    Nat.findGreatest_is_greatest (Nat.lt_succ_self k₀) (hK _ h₁) h₁
  apply hk₁
  apply (mem_supportSeparatedSet X).1
  apply h n (k₀ + 1)
  apply (mem_carrierSeparatedSet X).2
  obtain ⟨f, hf⟩ := hk₀S
  refine ⟨Fin.lastCases x (fun a ↦ (f a : X)), ?_⟩
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => exact absurd rfl hab
    | cast b =>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      exact hn.trans_le (hfar _ (f b).2)
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [dist_comm]
      exact hn.trans_le (hfar _ (f a).2)
    | cast b =>
      simp only [Fin.lastCases_castSucc]
      exact hf fun hab' ↦ hab (congrArg Fin.castSucc hab')

/-- On fully supported spaces the GP projection is injective: a measure-preserving
isometry of the supports is then one of the whole carriers. -/
theorem eq_of_gpProjection_eq_of_hasFullSupport {Y Y' : MeasuredGHSpace.{u}}
    (hY : HasFullSupport Y) (hY' : HasFullSupport Y') (h : gpProjection Y = gpProjection Y') :
    Y = Y' := by
  induction Y using Quotient.inductionOn with
  | _ X =>
  induction Y' using Quotient.inductionOn with
  | _ X' =>
  have : Measure.IsOpenPosMeasure (X.law : Measure X) := hY
  have : Measure.IsOpenPosMeasure (X'.law : Measure X') := hY'
  have key : ∃ e : (X.law : Measure X).support ≃ᵢ (X'.law : Measure X').support,
      (supportLaw (X.law : Measure X)).map e = supportLaw (X'.law : Measure X') :=
    (GPSpace.toGPSpace_eq_iff _ _).1 h
  obtain ⟨e, he⟩ := key
  have hX : ∀ x : X, x ∈ (X.law : Measure X).support := fun x ↦ by
    rw [Measure.support_eq_univ]
    exact mem_univ x
  have hX' : ∀ x : X', x ∈ (X'.law : Measure X').support := fun x ↦ by
    rw [Measure.support_eq_univ]
    exact mem_univ x
  let E : X ≃ᵢ X' :=
    { toFun := fun x ↦ (e ⟨x, hX x⟩ : X')
      invFun := fun y ↦ (e.symm ⟨y, hX' y⟩ : X)
      left_inv := fun x ↦ by simp
      right_inv := fun y ↦ by simp
      isometry_toFun := Isometry.of_dist_eq fun x y ↦ e.dist_eq ⟨x, hX x⟩ ⟨y, hX y⟩ }
  apply Quotient.sound
  refine ⟨E, ?_⟩
  have hcomp : (E : X → X') ∘ Subtype.val = Subtype.val ∘ e := rfl
  rw [← map_supportLaw (X.law : Measure X),
    Measure.map_map E.continuous.measurable measurable_subtype_coe, hcomp,
    ← Measure.map_map measurable_subtype_coe e.continuous.measurable]
  rw [he]
  exact map_supportLaw (X'.law : Measure X')

variable [MeasurableSpace GHSpace] [BorelSpace GHSpace]

/-- **Full support of a law with the GP and GH laws of a fully supported law.**
Two finite measures on GHP classes with the same GP law and the same GH law,
the second carried by fully supported spaces, are both carried by fully
supported spaces. -/
theorem ae_hasFullSupport_of_map_eq {R Q : Measure MeasuredGHSpace.{u}}
    [IsFiniteMeasure R] (hQ : ∀ᵐ X ∂Q, HasFullSupport X)
    (hgp : R.map gpProjection = Q.map gpProjection)
    (hgh : R.map underlyingGH = Q.map underlyingGH) :
    ∀ᵐ X ∂R, HasFullSupport X := by
  have hA (ε : ℝ) (k : ℕ) : R (supportSeparatedSet ε k) = Q (supportSeparatedSet ε k) :=
    measure_preimage_eq_of_map_eq continuous_gpProjection hgp
      (isOpen_supportSeparatedSet ε k).measurableSet
  have hB (ε : ℝ) (k : ℕ) : R (carrierSeparatedSet ε k) = Q (carrierSeparatedSet ε k) :=
    measure_preimage_eq_of_map_eq continuous_underlyingGH hgh
      (isOpen_carrierSeparatedSet ε k).measurableSet
  have hQdiff (ε : ℝ) (k : ℕ) :
      Q (carrierSeparatedSet ε k \ supportSeparatedSet ε k) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hQ] with Y hY hmem
    exact hmem.2 (mem_supportSeparatedSet_of_hasFullSupport hY hmem.1)
  have hRdiff (ε : ℝ) (k : ℕ) :
      R (carrierSeparatedSet ε k \ supportSeparatedSet ε k) = 0 := by
    have hQfin : Q (supportSeparatedSet ε k) ≠ ⊤ := by
      rw [← hA]
      exact measure_ne_top _ _
    rw [measure_sdiff (supportSeparatedSet_subset ε k)
      (isOpen_supportSeparatedSet ε k).measurableSet.nullMeasurableSet (measure_ne_top _ _),
      hA, hB, ← measure_sdiff (supportSeparatedSet_subset ε k)
      (isOpen_supportSeparatedSet ε k).measurableSet.nullMeasurableSet hQfin, hQdiff]
  have hall : ∀ᵐ Y ∂R, ∀ n k : ℕ, Y ∈ carrierSeparatedSet (1 / ((n : ℝ) + 1)) k →
      Y ∈ supportSeparatedSet (1 / ((n : ℝ) + 1)) k := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    rw [ae_iff]
    refine measure_mono_null (fun Y hY ↦ ?_) (hRdiff (1 / ((n : ℝ) + 1)) k)
    simp only [mem_ofPred_eq, not_imp] at hY
    exact hY
  filter_upwards [hall] with Y hY
  exact hasFullSupport_of_forall_mem_supportSeparatedSet hY

/-- **Identification of laws.** Two finite measures on GHP classes with the same
GP law and the same GH law, the second carried by fully supported spaces, are
equal. -/
theorem eq_of_map_gpProjection_eq_of_map_underlyingGH_eq {R Q : Measure MeasuredGHSpace.{u}}
    [IsFiniteMeasure R] (hQ : ∀ᵐ X ∂Q, HasFullSupport X)
    (hgp : R.map gpProjection = Q.map gpProjection)
    (hgh : R.map underlyingGH = Q.map underlyingGH) : R = Q := by
  have hR := ae_hasFullSupport_of_map_eq hQ hgp hgh
  obtain ⟨N, hNsub, hNmeas, hN⟩ := exists_measurable_superset_of_null (ae_iff.1 hR)
  obtain ⟨N', hNsub', hNmeas', hN'⟩ := exists_measurable_superset_of_null (ae_iff.1 hQ)
  have hfull : ∀ Y ∈ (N ∩ N')ᶜ, HasFullSupport Y := by
    intro Y hY
    by_contra hnot
    exact hY ⟨hNsub hnot, hNsub' hnot⟩
  refine eq_of_map_eq_of_injOn continuous_gpProjection hgp (hNmeas.inter hNmeas').compl
    ?_ ?_ ?_
  · rw [compl_compl]
    exact measure_mono_null inter_subset_left hN
  · rw [compl_compl]
    exact measure_mono_null inter_subset_right hN'
  · intro Y hY Y' hY' hYY'
    exact eq_of_gpProjection_eq_of_hasFullSupport (hfull Y hY) (hfull Y' hY') hYY'

/-- **Lemma `GP+GH=GHP`** ([Bla21, Lemma 4]). Let `Pₙ` and `Q` be laws of random
compact measured spaces, `Q` being carried by fully supported spaces. If the
laws of the GP classes converge weakly and the laws of the underlying GH
classes converge weakly, then `Pₙ → Q` weakly for the GHP topology. -/
theorem tendsto_ghp_of_gp_of_gh {P : ℕ → ProbabilityMeasure MeasuredGHSpace.{u}}
    {Q : ProbabilityMeasure MeasuredGHSpace.{u}}
    (hfull : ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{u}), HasFullSupport X)
    (hgp : Tendsto (fun n ↦ (P n).map gpProjection) atTop (𝓝 (Q.map gpProjection)))
    (hgh : Tendsto (fun n ↦ (P n).map underlyingGH) atTop (𝓝 (Q.map underlyingGH))) :
    Tendsto P atTop (𝓝 Q) := by
  have hghT : IsTightMeasureSet
      (range fun n ↦ ((P n : Measure MeasuredGHSpace.{u})).map underlyingGH) := by
    have hcomp : IsCompact (closure (range fun n ↦ (P n).map underlyingGH)) :=
      hgh.isCompact_insert_range.closure_of_subset (subset_insert _ _)
    convert isTightMeasureSet_of_isCompact_closure hcomp using 1
    ext μ
    simp [ProbabilityMeasure.toMeasure_map]
  have htight : IsTightMeasureSet (range fun n ↦ (P n : Measure MeasuredGHSpace.{u})) := by
    obtain ⟨hb⟩ := ‹BorelSpace GHSpace›
    subst hb
    rw [isTightMeasureSet_range_iff_underlyingGH]
    exact hghT
  have hcomp : IsCompact (closure (range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext μ
    simp
  apply tendsto_of_subseq_tendsto
  intro ψ hψ
  obtain ⟨R, -, φ, hφ, hR⟩ := hcomp.tendsto_subseq fun n ↦ subset_closure (mem_range_self (ψ n))
  refine ⟨φ, ?_⟩
  have hsub : Tendsto (ψ ∘ φ) atTop atTop := hψ.comp hφ.tendsto_atTop
  have hRgp : R.map gpProjection = Q.map gpProjection :=
    tendsto_nhds_unique (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hR
      continuous_gpProjection) (hgp.comp hsub)
  have hRgh : R.map underlyingGH = Q.map underlyingGH :=
    tendsto_nhds_unique (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hR
      continuous_underlyingGH) (hgh.comp hsub)
  have hRQ : R = Q := by
    apply ProbabilityMeasure.toMeasure_injective
    apply eq_of_map_gpProjection_eq_of_map_underlyingGH_eq hfull
    · simpa only [ProbabilityMeasure.toMeasure_map] using congrArg ProbabilityMeasure.toMeasure hRgp
    · simpa only [ProbabilityMeasure.toMeasure_map] using congrArg ProbabilityMeasure.toMeasure hRgh
  rw [hRQ] at hR
  exact hR

end MeasuredGHSpace

end Freezing2
