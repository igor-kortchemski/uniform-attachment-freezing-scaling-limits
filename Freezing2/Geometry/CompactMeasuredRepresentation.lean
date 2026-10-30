module

public import Freezing2.Geometry.GHPCompactness

/-!
# Common compact realizations of measured subsequences

The geometric compactness argument is exposed together with its actual
embeddings and pushed measures. This retains the joint carrier/measure
information needed by sampled covering radii and other whole-space tests.
No full-support hypothesis is imposed.
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace GromovHausdorff
open scoped Topology Uniformity

universe u

namespace Freezing2

/-- The compact range of an isometric embedding of a compact carrier. -/
def compactMeasuredRange (X : CompactMeasuredSpace.{u}) {Z : Type u} [MetricSpace Z]
    (f : X → Z) (hf : Isometry f) : NonemptyCompacts Z :=
  ⟨⟨range f, isCompact_range hf.continuous⟩, range_nonempty f⟩

/-- One common compact ambient space realizes a measured subsequence and its
limit, with convergence of both whole carriers and their original measures. -/
structure CompactMeasuredRepresentation (X : ℕ → CompactMeasuredSpace.{u}) where
  ambient : CompactMeasuredSpace.{u}
  limit : CompactMeasuredSpace.{u}
  indices : ℕ → ℕ
  indices_strictMono : StrictMono indices
  embedding : ∀ n, X (indices n) → ambient
  limitEmbedding : limit → ambient
  embedding_isometry : ∀ n, Isometry (embedding n)
  limitEmbedding_isometry : Isometry limitEmbedding
  measure_tendsto : Tendsto (fun n ↦ (X (indices n)).law.map (embedding n)) atTop
    (𝓝 (limit.law.map limitEmbedding))
  carrier_tendsto : Tendsto
    (fun n ↦ compactMeasuredRange (X (indices n)) (embedding n) (embedding_isometry n)) atTop
    (𝓝 (compactMeasuredRange limit limitEmbedding limitEmbedding_isometry))

/-- The realized carrier and measure limits imply convergence in the exact
GHP metric, using their common ambient realization. -/
theorem CompactMeasuredRepresentation.tendsto {X : ℕ → CompactMeasuredSpace.{u}}
    (R : CompactMeasuredRepresentation X) :
    Tendsto (fun n ↦ toMeasuredGHSpace (X (R.indices n))) atTop
      (𝓝 (toMeasuredGHSpace R.limit)) := by
  have hP := tendsto_levyProkhorovDist_of_tendsto R.measure_tendsto
  have hH : Tendsto
      (fun n ↦ hausdorffDist (range (R.embedding n)) (range R.limitEmbedding))
      atTop (𝓝 0) := by
    have h := R.carrier_tendsto.dist (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ compactMeasuredRange R.limit R.limitEmbedding R.limitEmbedding_isometry)
      atTop (𝓝 (compactMeasuredRange R.limit R.limitEmbedding R.limitEmbedding_isometry)))
    have h' : Tendsto
        (fun n ↦ dist (compactMeasuredRange (X (R.indices n)) (R.embedding n)
          (R.embedding_isometry n))
          (compactMeasuredRange R.limit R.limitEmbedding R.limitEmbedding_isometry))
        atTop (𝓝 0) := by simpa only [dist_self] using h
    convert h' using 1
    funext n
    rfl
  apply tendsto_iff_dist_tendsto_zero.mpr
  change Tendsto (fun n ↦ ghpDistance ((X (R.indices n)).law : Measure (X (R.indices n)))
    (R.limit.law : Measure R.limit)) atTop (𝓝 0)
  apply squeeze_zero (fun n ↦ ghpDistance_nonneg
    ((X (R.indices n)).law : Measure (X (R.indices n))) (R.limit.law : Measure R.limit)) _
    (by simpa only [zero_add] using hP.add hH)
  intro n
  have hB := ghpDistance_le_of_isometries ((X (R.indices n)).law : Measure (X (R.indices n)))
    (R.limit.law : Measure R.limit) R.ambient (R.embedding n) R.limitEmbedding
      (R.embedding_isometry n) R.limitEmbedding_isometry
  have hb : borel R.ambient.carrier = R.ambient.measurable := BorelSpace.measurable_eq.symm
  convert hB using 1
  rw [hb]
  rfl

/-- A Hausdorff-Cauchy common realization yields a compact measured
subsequence representation. Arbitrary original probability measures are kept. -/
theorem exists_compactMeasuredRepresentation_of_common_ambient
    (X : ℕ → CompactMeasuredSpace.{u}) {Z : Type u}
    [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace Z]
    (ι : ∀ n, X n → Z) (hι : ∀ n, Isometry (ι n))
    (S : ℕ → NonemptyCompacts Z) (hS : ∀ n, (S n : Set Z) = range (ι n))
    (hcS : CauchySeq S) : Nonempty (CompactMeasuredRepresentation X) := by
  classical
  borelize Z
  obtain ⟨L, K, hSL, hLK, hSK⟩ := exists_common_compact_of_cauchySeq S hcS
  let ιK : ∀ n, X n → K := fun n x ↦ ⟨ι n x, hSK n (by rw [hS n]; exact mem_range_self x)⟩
  have hιK (n : ℕ) : Isometry (ιK n) := Isometry.of_dist_eq (fun x y ↦ (hι n).dist_eq x y)
  let ν : ℕ → ProbabilityMeasure K := fun n ↦ (X n).law.map (ιK n)
  have hmapK (n : ℕ) : (ν n : Measure K).map (fun x : K ↦ (x : Z)) =
      ((X n).law : Measure (X n)).map (ι n) := by
    change (((X n).law : Measure (X n)).map (ιK n)).map _ = _
    rw [Measure.map_map continuous_subtype_val.measurable (hιK n).continuous.measurable]
    rfl
  obtain ⟨ν₀, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq ν
  let νZ : ProbabilityMeasure Z := ν₀.map (fun x : K ↦ (x : Z))
  let νs : ℕ → ProbabilityMeasure Z := fun n ↦ (X (φ n)).law.map (ι (φ n))
  have hνZ : Tendsto νs atTop (𝓝 νZ) := by
    have h := (ProbabilityMeasure.continuous_map continuous_subtype_val).tendsto ν₀ |>.comp hν
    convert h using 1
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    exact (hmapK (φ n)).symm
  have hs : ∀ n, (νs n : Measure Z) (S (φ n) : Set Z) = 1 := by
    intro n
    rw [hS]
    change (((X (φ n)).law : Measure (X (φ n))).map (ι (φ n))) (range (ι (φ n))) = 1
    rw [Measure.map_apply (hι _).continuous.measurable (isCompact_range (hι _).continuous).measurableSet,
      preimage_range, measure_univ]
  have hsupport := probabilityMeasure_compact_limit_eq_one hνZ
    (hSL.comp hφ.tendsto_atTop) hs
  obtain ⟨η, hη⟩ := exists_probabilityMeasure_on_compact νZ L hsupport
  let Y : CompactMeasuredSpace.{u} := CompactMeasuredSpace.of ↥L η
  let jL : L → K := fun x ↦ ⟨(x : Z), hLK x.property⟩
  have hjL : Isometry jL := Isometry.of_dist_eq (fun _ _ ↦ rfl)
  have hηK : η.map jL = ν₀ := by
    apply ProbabilityMeasure.toMeasure_injective
    apply (MeasurableEmbedding.subtype_coe K.isCompact.measurableSet).map_injective
    change ((η : Measure ↥L).map jL).map (fun x : K ↦ (x : Z)) =
      (ν₀ : Measure K).map (fun x : K ↦ (x : Z))
    rw [Measure.map_map continuous_subtype_val.measurable hjL.continuous.measurable]
    exact hη
  let A : CompactMeasuredSpace.{u} := CompactMeasuredSpace.of ↥K ν₀
  have hcarrier : Tendsto
      (fun n ↦ compactMeasuredRange (X (φ n)) (ιK (φ n)) (hιK (φ n))) atTop
      (𝓝 (compactMeasuredRange Y jL hjL)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h : Tendsto (fun n ↦ dist (S (φ n)) L) atTop (𝓝 0) := by
      simpa only [Function.comp_def, dist_self] using
        (hSL.comp hφ.tendsto_atTop).dist
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ L) atTop (𝓝 L))
    convert h using 1
    funext n
    change hausdorffDist (range (ιK (φ n))) (range jL) =
      hausdorffDist (S (φ n) : Set Z) (L : Set Z)
    rw [← hausdorffDist_image (Φ := fun x : K ↦ (x : Z)) isometry_subtype_coe,
      ← range_comp, ← range_comp]
    change hausdorffDist (range (ι (φ n))) (range (fun x : L ↦ (x : Z))) = _
    have hRange : range (fun x : L ↦ (x : Z)) = (L : Set Z) := Subtype.range_coe
    rw [hRange, hS]
  exact ⟨{
    ambient := A
    limit := Y
    indices := φ
    indices_strictMono := hφ
    embedding := fun n ↦ ιK (φ n)
    limitEmbedding := jL
    embedding_isometry := fun n ↦ hιK (φ n)
    limitEmbedding_isometry := hjL
    measure_tendsto := by
      change Tendsto (ν ∘ φ) atTop (𝓝 (η.map jL))
      rw [hηK]
      exact hν
    carrier_tendsto := hcarrier }⟩

/-- GH-Cauchy underlying carriers admit an actual common compact measured
subsequence realization. This requires no GHP-Cauchy assumption. -/
theorem exists_compactMeasuredRepresentation_of_gh_cauchy
    (X : ℕ → CompactMeasuredSpace.{u})
    (hc : CauchySeq (fun n ↦ toGHSpace (X n))) :
    Nonempty (CompactMeasuredRepresentation X) := by
  classical
  have hV (n : ℕ) : {p : GHSpace × GHSpace | dist p.1 p.2 < (1 / 2 : ℝ) ^ n}
      ∈ 𝓤 GHSpace := dist_mem_uniformity (by positivity)
  obtain ⟨σ, hσ, hstep⟩ := hc.subseq_mem hV
  let C : ∀ n, GHPCoupling (X (σ n)) (X (σ (n + 1))) := fun n ↦
    { ambient := OptimalGHCoupling (X (σ n)) (X (σ (n + 1)))
      metric := inferInstance
      left := optimalGHInjl _ _
      right := optimalGHInjr _ _
      left_isometry := isometry_optimalGHInjl _ _
      right_isometry := isometry_optimalGHInjr _ _ }
  obtain ⟨Z, m, hcomplete, ι, hι, hfactor⟩ :=
    GHPChain.exists_complete_realization (fun n ↦ X (σ n)) C
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  let : CompleteSpace Z := hcomplete
  let S : ℕ → NonemptyCompacts Z := fun n ↦
    ⟨⟨range (ι n), isCompact_range (hι n).continuous⟩, range_nonempty _⟩
  have hdist (n : ℕ) : dist (S n) (S (n + 1)) ≤ (1 / 2 : ℝ) ^ n := by
    change hausdorffDist (range (ι n)) (range (ι (n + 1))) ≤ _
    obtain ⟨j, hj, hl, hr⟩ := hfactor n
    rw [hl, hr, range_comp, range_comp, hausdorffDist_image hj]
    change hausdorffDist (range (optimalGHInjl (X (σ n)) (X (σ (n + 1)))))
      (range (optimalGHInjr (X (σ n)) (X (σ (n + 1))))) ≤ _
    rw [hausdorffDist_optimal]
    have h : dist (toGHSpace (X (σ (n + 1)))) (toGHSpace (X (σ n))) < (1 / 2 : ℝ) ^ n :=
      hstep n
    simpa only [ghDist, dist_comm] using h.le
  have hcS : CauchySeq S := cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
    (fun n ↦ by simpa only [one_mul] using hdist n)
  obtain ⟨R⟩ := exists_compactMeasuredRepresentation_of_common_ambient
    (fun n ↦ X (σ n)) ι hι S (fun _ ↦ rfl) hcS
  exact ⟨{
    ambient := R.ambient
    limit := R.limit
    indices := σ ∘ R.indices
    indices_strictMono := hσ.comp R.indices_strictMono
    embedding := R.embedding
    limitEmbedding := R.limitEmbedding
    embedding_isometry := R.embedding_isometry
    limitEmbedding_isometry := R.limitEmbedding_isometry
    measure_tendsto := R.measure_tendsto
    carrier_tendsto := R.carrier_tendsto }⟩

end Freezing2
