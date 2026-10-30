module

public import Freezing2.MainResults.BoundedPopulation
public import Freezing2.Probability.UniformHeightConcentration
public import Freezing2.Geometry.GHPSeparation

/-!
# Bounded population: the measured limit is not universal

Inventory item U20 (source line 1034). Theorem `thm:alpha0` (N09,
`bounded_population_GH_limit`) gives a Gromov–Hausdorff limit `[0,1]` for bounded
population. The source adds that the limit holds "for the Gromov–Hausdorff topology,
and not in the Gromov–Hausdorff–Prokhorov sense (in general there is no universal
behavior for the latter topology)". This file makes that assertion precise and proves it.

* **General measured limit** (`bounded_population_GHP_limit`). Under the hypotheses of
  N09, if `h_k^+ / h_n^+ → H(k/n)` uniformly in `k ≤ n` for a continuous `H`, the actual
  forward trees with their uniform vertex measures, distances scaled by `1 / h_n^+`,
  converge in probability in the GHP distance of `MeasuredGHSpace` to `[0,1]` carrying
  `H_* Leb` (`measuredSegment H`). With bounded population the normalized birth times of
  uniform vertices are always asymptotically uniform, so `H` alone determines the limit.
* **Nonuniversality** (`bounded_population_GHP_nonuniversal`,
  `bounded_population_no_universal_GHP_limit`). For the alternating array (population in
  `{1,2}`) the limit is `([0,1], Leb)`; for an array that is alternating up to time
  `≈ n/2` and then oscillates in `{2,3}`, the limit is `[0,1]` with
  `H(t) = (4t + 2 min(t, 1/2))/5`. These measured segments are at positive GHP distance,
  so no single measured space is the limit for every admissible bounded array.

The proof works on the reverse construction and is transported to the forward tree by
the canonical measure-preserving isometry (N01).

* **Heights.** A label born at reverse time `b` has depth a sum of independent
  Bernoulli variables of total mean `h_b^+` (`identDistrib_heightAt_sum_heightBernoulli`).
  Bennett's inequality and a union bound over the at most `n+1` labels give
  `|depth(v) - h_{b(v)}^+| ≤ η h_n^+` for all `v` with high probability, since
  `h_n^+ ≥ n/(2M)`.
* **Side branches.** The branching-excess estimate of N09 bounds
  `d(u,v) - |ht u - ht v|` by `η h_n^+` with high probability.
* **Deterministic GHP bound** (`forestMeasuredSpace_dist_le`). The map
  `v ↦ clamp(depth(v)/h_n^+)` into `[0,1]` has small distortion, dense image, and pushes
  the uniform measure close (Lévy–Prokhorov) to the law of `h_{b(V)}^+ / h_n^+`.
* **Deterministic measure limit** (`tendsto_coordinateLaw_levyProkhorovDist`). The
  birth-time law converges to Lebesgue measure, and the uniform profile hypothesis
  transfers this to `H_* Leb`.
* **Distinct limits.** An isometry of `[0,1]` preserves the distance to `1/2`. The band
  `|s - 1/2| ≤ 1/10` has mass `1/5` under Lebesgue measure and `1/6` under the
  switched limit, so the separation theorem `ghpDistance_eq_zero_iff_measured_isometry`
  gives a positive GHP distance.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Classical

namespace Freezing2

open ReverseHistory MeasuredGHSpace

/-! ### The limiting measured segments -/

/-- Lebesgue probability on `[0,1]` pushed through `H`, projected onto `[0,1]`. -/
noncomputable def segmentLaw (H : ℝ → ℝ) : ProbabilityMeasure unitInterval :=
  profileProbabilityMeasure.map (fun t ↦ projIcc (0 : ℝ) 1 zero_le_one (H t))

/-- The unit segment carrying the measure `segmentLaw H`. -/
noncomputable def measuredSegment (H : ℝ → ℝ) : CompactMeasuredSpace :=
  CompactMeasuredSpace.of unitInterval (segmentLaw H)

/-- Forgetting the measure gives the unit segment, the GH limit of N09. -/
theorem underlyingGH_measuredSegment (H : ℝ → ℝ) :
    underlyingGH (toMeasuredGHSpace (measuredSegment H)) =
      GromovHausdorff.toGHSpace unitInterval := rfl

/-! ### The reverse measured tree and transport to the forward tree -/

/-- The scaled reverse forest with its uniform vertex measure. The fallback is used
only outside the connected positive-scale domain. -/
noncomputable def forestMeasuredSpace (c : ℝ) (F : Freezing1.Reverse.Forest) :
    CompactMeasuredSpace :=
  if h : F.toGraph.Connected ∧ 0 < c then
    letI := scaledGraphMetric F.toGraph h.1 c h.2
    letI := h.1.nonempty
    letI : IsProbabilityMeasure (forestVertexMeasure F) :=
      uniformOfFinset_probability_of_nonempty _ Finset.univ_nonempty
    CompactMeasuredSpace.of {v // v ∈ F.vertices} ⟨forestVertexMeasure F, inferInstance⟩
  else singletonMeasuredSpace

namespace ReverseStamped

/-- The canonical vertex bijection is a measure-preserving isometry between the
measured terminal reverse tree and the measured canonical forward tree. -/
theorem forestMeasuredSpace_measuredIsometry
    {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {c : ℝ} (hc : 0 < c) :
    CompactMeasuredSpace.MeasuredIsometry (forestMeasuredSpace c F.forest)
      (forwardMeasuredSpace c (canonicalForwardState x n F)) := by
  have hconnF : F.forest.toGraph.Connected :=
    (F.forest.isTree_of_one_root (one_root_of_terminal_valid hF) hF.acyclic).connected
  have hconnS : (canonicalForwardState x n F).tree.Connected :=
    (ForwardHistory.state_valid x (canonicalHistory x n F)).tree_connected
  rw [forestMeasuredSpace, dite_eq_left ⟨hconnF, hc⟩,
    forwardMeasuredSpace, dite_eq_left ⟨hconnS, hc⟩]
  exact ⟨canonicalScaledIsometry hF ht ho c hc hconnF hconnS,
    map_forestVertexMeasure_canonicalVertexEquiv hF ht ho⟩

end ReverseStamped

/-- The probability that the forward measured tree is far from a fixed measured
space equals the same probability for the terminal reverse forest. -/
theorem forward_measured_far_eq_reverse (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {c : ℝ} (hc : 0 < c)
    (L : MeasuredGHSpace) (ε : ℝ) :
    (Freezing1.Forward.treeLaw x n).real
        {s | ε < dist (toMeasuredGHSpace (forwardMeasuredSpace c s)) L} =
      (jointLaw x n).real
        {ω | ε < dist (toMeasuredGHSpace (forestMeasuredSpace c (ω n))) L} := by
  have hrev : Freezing1.Reverse.treeLaw x n = (jointLaw x n).map (fun ω ↦ ω n) := by
    rw [jointLaw_map_eval]
    rfl
  have hae : ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n,
      toMeasuredGHSpace (forestMeasuredSpace c F.forest) =
        toMeasuredGHSpace (forwardMeasuredSpace c (ReverseStamped.canonicalForwardState x n F)) := by
    filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
      Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
      ReverseStamped.treeLaw_canonicalOrder x n hn] with F hF ht ho
    exact (toMeasuredGHSpace_eq_iff _ _).mpr
      (ReverseStamped.forestMeasuredSpace_measuredIsometry
        (by simpa only [Nat.sub_self] using hF) ht ho hc)
  have h2 : (jointLaw x n) {ω | ε < dist (toMeasuredGHSpace (forestMeasuredSpace c (ω n))) L} =
      (Freezing1.Reverse.treeLaw x n)
        {F | ε < dist (toMeasuredGHSpace (forestMeasuredSpace c F)) L} := by
    rw [hrev, Measure.map_apply (measurable_pi_apply n) (MeasurableSet.of_discrete)]
    rfl
  have h3 : (Freezing1.Reverse.treeLaw x n)
        {F | ε < dist (toMeasuredGHSpace (forestMeasuredSpace c F)) L} =
      (Freezing1.ReverseStamped.treeLaw x n)
        {F | ε < dist (toMeasuredGHSpace (forestMeasuredSpace c F.forest)) L} := by
    rw [← Freezing1.ReverseStamped.map_treeLaw,
      Measure.map_apply measurable_from_top (MeasurableSet.of_discrete)]
    rfl
  rw [measureReal_def, measureReal_def, h2, h3, ← ReverseStamped.forward_reverse_same_law x n hn,
    Measure.map_apply measurable_from_top (MeasurableSet.of_discrete)]
  congr 1
  apply measure_congr
  filter_upwards [hae] with F hF
  change (ε < dist _ L) = (ε < dist _ L)
  rw [hF]

/-! ### Deterministic GHP bound -/

/-- Projection onto `[0,1]` is `1`-Lipschitz. -/
theorem dist_projIcc_le (a b : ℝ) :
    dist (projIcc (0 : ℝ) 1 zero_le_one a) (projIcc (0 : ℝ) 1 zero_le_one b) ≤ |a - b| := by
  have h := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul a b
  rwa [Real.dist_eq, NNReal.coe_one, one_mul] at h

/-- A nonnegative point within `T` of `[0,1]` moves by at most `T` under projection. -/
theorem abs_projIcc_sub_self_le {a A T : ℝ} (ha : 0 ≤ a) (hA : A ≤ 1) (haA : |a - A| ≤ T) :
    |(projIcc (0 : ℝ) 1 zero_le_one a : ℝ) - a| ≤ T ∧
      0 ≤ a - (projIcc (0 : ℝ) 1 zero_le_one a : ℝ) := by
  rw [coe_projIcc]
  have h1 := (abs_le.mp haA).2
  rcases le_total a 1 with h | h
  · rw [min_eq_right h, max_eq_right ha, sub_self, abs_zero]
    exact ⟨(abs_nonneg _).trans haA, le_rfl⟩
  · rw [min_eq_left h, max_eq_right zero_le_one, abs_sub_comm, abs_of_nonneg (by linarith)]
    constructor <;> linarith

/-- Two clamping errors in `[0,T]` change a difference by at most `T`. -/
theorem abs_sub_sub_le_of_clamp {s t P Q T : ℝ} (h1 : |P - s| ≤ T) (h2 : 0 ≤ s - P)
    (h3 : |Q - t| ≤ T) (h4 : 0 ≤ t - Q) : |(s - t) - (P - Q)| ≤ T := by
  rw [abs_le] at h1 h3 ⊢
  constructor <;> linarith

/-- The deterministic coordinate of a reverse label: its scaled harmonic centre. -/
noncomputable def labelCoordinate (x : Freezing1.SignSequence) (n : ℕ) (c : ℝ) (v : ℕ ⊕ ℕ) :
    unitInterval :=
  projIcc (0 : ℝ) 1 zero_le_one (c * Freezing1.heightScale x (Freezing1.birthTime n v))

/-- The law of the coordinate of a uniform reverse label. -/
noncomputable def coordinateLaw (x : Freezing1.SignSequence) (n : ℕ) (c : ℝ) :
    Measure unitInterval :=
  (Freezing1.uniformVertex x n).map (labelCoordinate x n c)

/-- Uniform measure on a valid terminal forest, mapped to label coordinates. -/
theorem map_forestVertexMeasure_labelCoordinate {x : Freezing1.SignSequence} {n : ℕ}
    {F : Freezing1.Reverse.Forest} (hF : Freezing1.Reverse.ValidAt x n 0 F) (c : ℝ) :
    (forestVertexMeasure F).map (fun v ↦ labelCoordinate x n c v.val) = coordinateLaw x n c := by
  have hV : F.vertices = Freezing1.vertexLabels x n := by
    simpa only [Freezing1.Reverse.phaseLabels_zero] using hF.vertices_eq
  have hval : (forestVertexMeasure F).map Subtype.val = Measure.uniformOfFinset F.vertices :=
    map_uniform_vertex_subtype_val F.vertices
  rw [show (fun v : {v // v ∈ F.vertices} ↦ labelCoordinate x n c v.val) =
      labelCoordinate x n c ∘ Subtype.val from rfl,
    ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hval, hV]
  rfl

/-- **Deterministic GHP bound.** A valid terminal reverse tree whose branching
excess is at most `D` and whose depths are within `T` of their harmonic centres
is GHP-close to the measured segment. -/
theorem forestMeasuredSpace_dist_le {x : Freezing1.SignSequence} {n : ℕ}
    {F : Freezing1.Reverse.Forest} (hF : Freezing1.Reverse.ValidAt x n 0 F)
    {H : ℝ → ℝ} {c D T ρ p : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hexc : F ∉ reverseExcessEvent D)
    (hheight : ∀ v ∈ F.vertices,
      |(F.depth v : ℝ) - Freezing1.heightScale x (Freezing1.birthTime n v)| ≤ T)
    (hcoord : ∀ v ∈ F.vertices,
      c * Freezing1.heightScale x (Freezing1.birthTime n v) ∈ Icc (0 : ℝ) 1)
    (hdense : ∀ y ∈ Icc (0 : ℝ) 1, ∃ v ∈ F.vertices,
      |c * Freezing1.heightScale x (Freezing1.birthTime n v) - y| ≤ ρ)
    (hprob : levyProkhorovDist (coordinateLaw x n c) (segmentLaw H : Measure unitInterval) ≤ p) :
    dist (toMeasuredGHSpace (forestMeasuredSpace c F)) (toMeasuredGHSpace (measuredSegment H)) ≤
      c * D + 4 * (c * T) + ρ + p := by
  have hroot : F.roots.card = 1 := by simpa using hF.roots_card
  have hconn : F.toGraph.Connected := (F.isTree_of_one_root hroot hF.acyclic).1
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hroot
  have hrR : r ∈ F.roots := by rw [hr]; exact Finset.mem_singleton_self r
  have hrV : r ∈ F.vertices := (Freezing1.RootedForest.mem_roots.mp hrR).1
  have hdepth (v : ℕ ⊕ ℕ) (hv : v ∈ F.vertices) : F.depth v = F.graph.dist r v := by
    have h1 := F.root_mem_roots hv
    rw [hr, Finset.mem_singleton] at h1
    rw [F.depth_eq_dist hv, h1]
  have hexc' : ∀ u ∈ F.vertices, ∀ v ∈ F.vertices,
      (F.graph.dist u v : ℝ) - |(F.depth u : ℝ) - F.depth v| ≤ D := by
    intro u hu v hv
    rw [hdepth u hu, hdepth v hv]
    by_contra hlt
    exact hexc ⟨r, hrR, u, hu, v, hv, lt_of_not_ge hlt⟩
  have hD : 0 ≤ D := by simpa using hexc' r hrV r hrV
  -- triangle inequality through the root
  have htri : ∀ u ∈ F.vertices, ∀ v ∈ F.vertices,
      |(F.depth u : ℝ) - F.depth v| ≤ F.graph.dist u v := by
    intro u hu v hv
    have e1 := forest_toGraph_dist_eq F ⟨r, hrV⟩ ⟨u, hu⟩
    have e2 := forest_toGraph_dist_eq F ⟨r, hrV⟩ ⟨v, hv⟩
    have e3 := forest_toGraph_dist_eq F ⟨u, hu⟩ ⟨v, hv⟩
    have t1 := hconn.dist_triangle (u := ⟨r, hrV⟩) (v := ⟨u, hu⟩) (w := ⟨v, hv⟩)
    have t2 := hconn.dist_triangle (u := ⟨r, hrV⟩) (v := ⟨v, hv⟩) (w := ⟨u, hu⟩)
    rw [SimpleGraph.dist_comm (u := (⟨v, hv⟩ : {w // w ∈ F.vertices}))] at t2
    simp only [e1, e2, e3] at t1 t2
    rw [hdepth u hu, hdepth v hv, abs_le]
    constructor
    · have : (F.graph.dist r v : ℝ) ≤ F.graph.dist r u + F.graph.dist u v := by exact_mod_cast t1
      linarith
    · have : (F.graph.dist r u : ℝ) ≤ F.graph.dist r v + F.graph.dist u v := by exact_mod_cast t2
      linarith
  let := scaledGraphMetric F.toGraph hconn c hc
  let := hconn.nonempty
  have : IsProbabilityMeasure (forestVertexMeasure F) :=
    uniformOfFinset_probability_of_nonempty _ Finset.univ_nonempty
  set A : {v // v ∈ F.vertices} → ℝ :=
    fun v ↦ c * Freezing1.heightScale x (Freezing1.birthTime n v.val) with hAdef
  let f : {v // v ∈ F.vertices} → unitInterval :=
    fun v ↦ projIcc (0 : ℝ) 1 zero_le_one (c * F.depth v.val)
  let g : {v // v ∈ F.vertices} → unitInterval := fun v ↦ labelCoordinate x n c v.val
  have hdA (v : {v // v ∈ F.vertices}) : |c * (F.depth v.val : ℝ) - A v| ≤ c * T := by
    rw [hAdef]
    simp only
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hheight v.val v.property) hc.le
  have hfg (v : {v // v ∈ F.vertices}) : dist (f v) (g v) ≤ c * T :=
    (dist_projIcc_le _ _).trans (hdA v)
  have hproj (v : {v // v ∈ F.vertices}) :=
    abs_projIcc_sub_self_le (by positivity) (hcoord v.val v.property).2 (hdA v)
  have hdis : ∀ u v : {v // v ∈ F.vertices},
      |dist u v - dist (f u) (f v)| ≤ 2 * ((c * D + 2 * (c * T)) / 2) := by
    intro u v
    change abs (c * (F.toGraph.dist u v : ℝ) - abs ((f u : ℝ) - f v)) ≤ _
    rw [forest_toGraph_dist_eq F u v]
    have he := hexc' u.val u.property v.val v.property
    have ht := htri u.val u.property v.val v.property
    obtain ⟨pu1, pu2⟩ := hproj u
    obtain ⟨pv1, pv2⟩ := hproj v
    set a := c * (F.depth u.val : ℝ) with ha
    set b := c * (F.depth v.val : ℝ) with hb
    have hab : c * |(F.depth u.val : ℝ) - F.depth v.val| = |a - b| := by
      rw [ha, hb, ← mul_sub, abs_mul, abs_of_pos hc]
    have he' : c * (F.graph.dist u.val v.val : ℝ) - |a - b| ≤ c * D := by
      rw [← hab, ← mul_sub]
      exact mul_le_mul_of_nonneg_left he hc.le
    have ht' : |a - b| ≤ c * (F.graph.dist u.val v.val : ℝ) := by
      rw [← hab]
      exact mul_le_mul_of_nonneg_left ht hc.le
    have hcl : abs (|a - b| - |(f u : ℝ) - f v|) ≤ c * T :=
      (abs_abs_sub_abs_le_abs_sub (a - b) ((f u : ℝ) - f v)).trans
        (abs_sub_sub_le_of_clamp pu1 pu2 pv1 pv2)
    have hcT : 0 ≤ c * T := by positivity
    rw [abs_le] at hcl ⊢
    constructor <;> linarith
  have hδ : 0 < (c * D + 2 * (c * T)) / 2 := by positivity
  have hdense' : ∀ y : unitInterval, ∃ v, dist y (f v) ≤ c * T + ρ := by
    intro y
    obtain ⟨v, hv, hvy⟩ := hdense y.val y.property
    refine ⟨⟨v, hv⟩, ?_⟩
    have h1 : dist (f ⟨v, hv⟩) (g ⟨v, hv⟩) ≤ c * T := hfg _
    have h2 : dist y (g ⟨v, hv⟩) ≤ ρ := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      change |(projIcc (0 : ℝ) 1 zero_le_one
        (c * Freezing1.heightScale x (Freezing1.birthTime n v)) : ℝ) - y| ≤ ρ
      rw [projIcc_of_mem _ (hcoord v hv)]
      exact hvy
    have h3 := dist_triangle y (g ⟨v, hv⟩) (f ⟨v, hv⟩)
    rw [dist_comm (g _)] at h3
    linarith
  have hprob' : levyProkhorovDist ((forestVertexMeasure F).map f)
      (segmentLaw H : Measure unitInterval) ≤ c * T + p := by
    have h1 : levyProkhorovDist ((forestVertexMeasure F).map f)
        ((forestVertexMeasure F).map g) ≤ c * T :=
      levyProkhorovDist_map_le_of_dist_le _ (measurable_of_countable _)
        (measurable_of_countable _) (by positivity) hfg
    have h2 : (forestVertexMeasure F).map g = coordinateLaw x n c :=
      map_forestVertexMeasure_labelCoordinate hF c
    have h3 := levyProkhorovDist_triangle ((forestVertexMeasure F).map f)
      ((forestVertexMeasure F).map g) (segmentLaw H : Measure unitInterval)
    rw [h2] at h3
    rw [h2] at h1
    linarith
  have hb := ghpDistance_le_of_approx (forestVertexMeasure F)
    (segmentLaw H : Measure unitInterval) f (measurable_of_countable _) hδ hdis hdense' hprob'
  rw [dist_toMeasuredGHSpace]
  change CompactMeasuredSpace.distance _ (CompactMeasuredSpace.of unitInterval (segmentLaw H)) ≤ _
  rw [forestMeasuredSpace, dite_eq_left ⟨hconn, hc⟩]
  change ghpDistance (forestVertexMeasure F) (segmentLaw H : Measure unitInterval) ≤ _
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-! ### Birth times and the limiting coordinate law -/

/-- A sequence bounded at positive indices, divided by `n`, tends to zero. -/
theorem tendsto_div_natCast_of_abs_le {u : ℕ → ℝ} {C : ℝ} (h : ∀ n, 0 < n → |u n| ≤ C) :
    Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat C)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hC : 0 ≤ C := (abs_nonneg _).trans (h 1 one_pos)
    simp
  · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (h n hn) (Nat.cast_nonneg n)

/-- With bounded population, normalized birth times of uniform vertices are
asymptotically uniform on `[0,1]`. -/
theorem tendsto_uniformBirthProbability_of_bounded {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    {M : ℕ} (hM : ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) :
    Tendsto (fun n ↦ uniformBirthProbability (x n) n (hx n).1 ((hx n).2 n le_rfl).le)
      atTop (𝓝 profileProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
  change Tendsto (fun n ↦ uniformBirthTimeMeasure (x n) n (hx n).1 ((hx n).2 n le_rfl).le)
    atTop (𝓝 profileFiniteMeasure)
  have hS (n k : ℕ) (hk : k ≤ n) : |(activeCount (x n) k : ℝ)| ≤ M := by
    have h1 := (hx n).2 k hk
    have h2 := hM n k hk
    rw [abs_of_pos (by exact_mod_cast h1)]
    exact_mod_cast h2
  apply finiteMeasure_tendsto_of_Iic profileFiniteMeasure_ne_zero
  · simpa only [uniformBirthTimeMeasure_mass, profileFiniteMeasure_mass] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
  · intro a
    by_cases ha : 0 ≤ a
    · by_cases ha1 : a < 1
      · rw [profileFiniteMeasure_real_Iic ha ha1.le]
        set m : ℕ → ℕ := fun n ↦ ⌊(n : ℝ) * a⌋₊ + 1 with hm
        have hmn : ∀ n : ℕ, 0 < n → m n ≤ n := by
          intro n hn
          have hn' : (0 : ℝ) < n := by exact_mod_cast hn
          have : ⌊(n : ℝ) * a⌋₊ < n :=
            Nat.floor_lt (mul_nonneg hn'.le ha) |>.mpr (by nlinarith)
          simp only [hm]
          omega
        have hnum : Tendsto (fun n : ℕ ↦ ((m n : ℝ) + 1 - activeCount (x n) (m n)) / n)
            atTop (𝓝 a) := by
          have h1 : Tendsto (fun n : ℕ ↦ (⌊a * (n : ℝ)⌋₊ : ℝ) / n) atTop (𝓝 a) :=
            (tendsto_nat_floor_mul_div_atTop ha).comp tendsto_natCast_atTop_atTop
          have h2 : Tendsto (fun n : ℕ ↦ (2 - (activeCount (x n) (m n) : ℝ)) / n) atTop
              (𝓝 0) := by
            apply tendsto_div_natCast_of_abs_le (C := 2 + M)
            intro n hn
            have := hS n (m n) (hmn n hn)
            have := abs_sub (2 : ℝ) (activeCount (x n) (m n))
            rw [abs_two] at this
            linarith
          have h3 := h1.add h2
          rw [add_zero] at h3
          apply h3.congr
          intro n
          simp only [hm]
          rw [mul_comm a, ← add_div]
          push_cast
          ring_nf
        have hden : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1 + activeCount (x n) n) / n)
            atTop (𝓝 1) := by
          have h2 : Tendsto (fun n : ℕ ↦ (1 + (activeCount (x n) n : ℝ)) / n) atTop (𝓝 0) := by
            apply tendsto_div_natCast_of_abs_le (C := 1 + M)
            intro n _
            have := hS n n le_rfl
            have := abs_add_le (1 : ℝ) (activeCount (x n) n)
            rw [abs_one] at this
            linarith
          have h3 := (tendsto_const_nhds (x := (1 : ℝ))).add h2
          rw [add_zero] at h3
          apply h3.congr'
          filter_upwards [eventually_gt_atTop 0] with n hn
          have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
          field_simp
          ring
        have hlim := hnum.div hden one_ne_zero
        rw [div_one] at hlim
        apply hlim.congr'
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [uniformBirthTimeMeasure_real_Iic _ _ _ hn ha ha1]
        have hlab := vertexLabels_card (x n) (hx n).1 ((hx n).2 n le_rfl).le
        have hfr := twice_frozen_count (x n) (hx n).1 (m n)
        have hv := twice_vertex_count (x n) (hx n).1 n
        have hfr' : 2 * ((downSteps (x n) 0 (m n)).card : ℝ) =
            (m n : ℝ) + 1 - activeCount (x n) (m n) := by exact_mod_cast hfr
        have hv' : 2 * ((vertexLabels (x n) n).card : ℝ) =
            (n : ℝ) + 1 + activeCount (x n) n := by
          rw [hlab]
          push_cast
          exact_mod_cast hv
        have hpos : (0 : ℝ) < (vertexLabels (x n) n).card := by
          exact_mod_cast (vertexLabels_nonempty (x n) (hx n).1
            ((hx n).2 n le_rfl).le).card_pos
        change ((m n : ℝ) + 1 - activeCount (x n) (m n)) / n /
          (((n : ℝ) + 1 + activeCount (x n) n) / n) = _
        rw [← hfr', ← hv']
        field_simp
        rfl
      · rw [profileFiniteMeasure_real_Iic_of_one_le (le_of_not_gt ha1)]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop 0] with n hn
        exact (uniformBirthTimeMeasure_real_Iic_of_one_le (x n) (hx n).1
          ((hx n).2 n le_rfl).le hn (le_of_not_gt ha1)).symm
    · simp only [uniformBirthTimeMeasure_real_Iic_of_neg _ _ _ _ (lt_of_not_ge ha),
        profileFiniteMeasure_real_Iic_of_neg (lt_of_not_ge ha)]
      exact tendsto_const_nhds


/-- The uniform-label coordinate law written with the paper's labels. -/
theorem coordinateLaw_eq_paper (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) (c : ℝ) :
    coordinateLaw (companionSchedule x) n c =
      (uniformVertex x n).map (fun v ↦ projIcc (0 : ℝ) 1 zero_le_one
        (c * Freezing1.heightScale (companionSchedule x) (birthTime n v))) := by
  rw [← map_companion_uniformVertex x hx n,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  unfold coordinateLaw
  congr 1
  funext v
  simp only [Function.comp_apply, labelCoordinate]
  rw [← companion_birthTime, to_fromCompanionLabel]

/-- **Deterministic measure part.** If the height profile converges uniformly to
a continuous `H`, the coordinate law of a uniform vertex converges to `segmentLaw H`
in the Lévy–Prokhorov distance. -/
theorem tendsto_coordinateLaw_levyProkhorovDist {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    {M : ℕ} (hM : ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {H : ℝ → ℝ} (hH : Continuous H)
    (hconv : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
      |Freezing1.heightScale (companionSchedule (x n)) k /
        Freezing1.heightScale (companionSchedule (x n)) n - H (k / n)| ≤ η) :
    Tendsto (fun n ↦ levyProkhorovDist
      (coordinateLaw (companionSchedule (x n)) n
        (1 / Freezing1.heightScale (companionSchedule (x n)) n))
      (segmentLaw H : Measure unitInterval)) atTop (𝓝 0) := by
  set h : ℕ → ℕ → ℝ := fun n k ↦ Freezing1.heightScale (companionSchedule (x n)) k with hh
  let μ : (n : ℕ) → ProbabilityMeasure VertexLabel :=
    fun n ↦ uniformLabelProbability (x n) n (hx n).1 ((hx n).2 n le_rfl).le
  let F : (n : ℕ) → VertexLabel → ℝ := fun n v ↦ 1 / h n n * h n (birthTime n v)
  let G : (n : ℕ) → VertexLabel → ℝ := fun n v ↦ H ((birthTime n v : ℝ) / n)
  let e : ℕ → ℝ := fun n ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k ↦ |h n k / h n n - H (k / n)|)
  have he0 (n : ℕ) : 0 ≤ e n :=
    (abs_nonneg _).trans (Finset.le_sup' (fun k ↦ |h n k / h n n - H (k / n)|)
      (Finset.self_mem_range_succ n))
  have he : Tendsto e atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv (η / 2) (by positivity))
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)]
    have : e n ≤ η / 2 := by
      apply Finset.sup'_le
      intro k hk
      exact hN n hn k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    linarith
  have hbound : ∀ᶠ n in atTop, ∀ᵐ v ∂(μ n : Measure VertexLabel), |F n v - G n v| ≤ e n := by
    refine Eventually.of_forall fun n ↦ ?_
    filter_upwards [uniformVertex_mem (x n) (hx n).1 ((hx n).2 n le_rfl).le] with v hv
    have hb := birthTime_le (x n) hv
    simp only [F, G, one_div_mul_eq_div]
    exact Finset.le_sup' (fun k ↦ |h n k / h n n - H (k / n)|)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))
  have hG : Tendsto (fun n ↦ (μ n).map (G n)) atTop (𝓝 (profileProbabilityMeasure.map H)) := by
    have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (tendsto_uniformBirthProbability_of_bounded hx hM) hH
    apply h1.congr
    intro n
    apply Subtype.ext
    change ((uniformVertex (x n) n).map (fun v ↦ (birthTime n v : ℝ) / n)).map H =
      (uniformVertex (x n) n).map (G n)
    rw [Measure.map_map hH.measurable (measurable_of_countable _)]
    rfl
  have hF := tendsto_probabilityMap_of_uniform_ae_error μ (fun _ ↦ measurable_of_countable _)
    (fun _ ↦ measurable_of_countable _) he hbound hG
  have hP := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hF
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one))
  have hseg : (profileProbabilityMeasure.map H).map (projIcc (0 : ℝ) 1 zero_le_one) =
      segmentLaw H := by
    apply Subtype.ext
    change (profileMeasure.map H).map (projIcc (0 : ℝ) 1 zero_le_one) =
      profileMeasure.map (fun t ↦ projIcc (0 : ℝ) 1 zero_le_one (H t))
    rw [Measure.map_map continuous_projIcc.measurable hH.measurable]
    rfl
  rw [hseg] at hP
  have hL := tendsto_levyProkhorovDist_of_tendsto hP
  apply hL.congr
  intro n
  congr 1
  change ((uniformVertex (x n) n).map (F n)).map (projIcc (0 : ℝ) 1 zero_le_one) = _
  rw [Measure.map_map continuous_projIcc.measurable (measurable_of_countable _),
    coordinateLaw_eq_paper (x n) (hx n).1 n]
  rfl

/-! ### The height scale and density of harmonic centres -/

/-- Each summand of the height scale lies in `[0,1]` before extinction. -/
theorem heightScale_term_mem {y : Freezing1.SignSequence} {n i : ℕ}
    (hpos : Freezing1.PositiveThrough y n) (hi : i < n) :
    0 ≤ (if y (i + 1) then 1 / (Freezing1.activeCount y (i + 1) : ℝ) else 0) ∧
      (if y (i + 1) then 1 / (Freezing1.activeCount y (i + 1) : ℝ) else 0) ≤ 1 := by
  split_ifs
  · have h1 : (1 : ℝ) ≤ Freezing1.activeCount y (i + 1) := by
      have := hpos (i + 1) (by omega)
      exact_mod_cast this
    exact ⟨by positivity, (div_le_one (by linarith)).mpr h1⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- Before extinction the height scale is nondecreasing, with increments at most one
per step. -/
theorem heightScale_le_le {y : Freezing1.SignSequence} {n k l : ℕ}
    (hpos : Freezing1.PositiveThrough y n) (hkl : k ≤ l) (hl : l ≤ n) :
    Freezing1.heightScale y k ≤ Freezing1.heightScale y l ∧
      Freezing1.heightScale y l ≤ Freezing1.heightScale y k + (l - k : ℕ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  unfold Freezing1.heightScale
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  have hmem (i : ℕ) (hi : i ∈ Finset.range d) := heightScale_term_mem (y := y) hpos
    (show k + i < n by have := Finset.mem_range.mp hi; omega)
  have h0 := Finset.sum_nonneg fun i hi ↦ (hmem i hi).1
  have h1 : (∑ i ∈ Finset.range d,
      if y (k + i + 1) then 1 / (Freezing1.activeCount y (k + i + 1) : ℝ) else 0) ≤ d := by
    calc
      _ ≤ ∑ _i ∈ Finset.range d, (1 : ℝ) := Finset.sum_le_sum fun i hi ↦ (hmem i hi).2
      _ = d := by simp
  constructor <;> linarith

/-- Before extinction the height scale is nonnegative. -/
theorem heightScale_nonneg {y : Freezing1.SignSequence} {n k : ℕ}
    (hpos : Freezing1.PositiveThrough y n) (hk : k ≤ n) : 0 ≤ Freezing1.heightScale y k := by
  simpa using (heightScale_le_le hpos (Nat.zero_le k) hk).1

/-- With population at most `M`, every time `k ≤ n` is followed within `M` steps
by the birth time of some label. -/
theorem exists_label_birthTime_near {y : Freezing1.SignSequence} {n M : ℕ}
    (hpos : Freezing1.PositiveThrough y n) (hM : ∀ k ≤ n, Freezing1.activeCount y k ≤ M)
    {k : ℕ} (hk : k ≤ n) :
    ∃ v ∈ Freezing1.vertexLabels y n, k ≤ Freezing1.birthTime n v ∧
      Freezing1.birthTime n v ≤ k + M := by
  by_contra hno
  push Not at hno
  have hact : (Sum.inl 0 : ℕ ⊕ ℕ) ∈ Freezing1.vertexLabels y n := by
    have := hpos n le_rfl
    simp only [Freezing1.vertexLabels, Finset.inl_mem_disjSum, Finset.mem_range]
    omega
  have hclaim : ∀ j ≤ M, k + j ≤ n ∧
      Freezing1.activeCount y (k + j) = Freezing1.activeCount y k + j := by
    intro j
    induction j with
    | zero => intro _; simpa using hk
    | succ j ih =>
      intro hj
      obtain ⟨hkj, hS⟩ := ih (by omega)
      have hlt : k + j < n := by
        rcases Nat.lt_or_ge (k + j) n with h | h
        · exact h
        · have := hno _ hact (by simp [Freezing1.birthTime]; omega)
          simp only [Freezing1.birthTime] at this
          omega
      have hup : y (k + j + 1) = true := by
        by_contra hdown
        have hmem : (Sum.inr (k + j) : ℕ ⊕ ℕ) ∈ Freezing1.vertexLabels y n := by
          simp only [Freezing1.vertexLabels, Finset.inr_mem_disjSum, Freezing1.frozenIndices,
            Finset.mem_filter, Finset.mem_range]
          exact ⟨hlt, by simpa using hdown⟩
        have := hno _ hmem (by simp [Freezing1.birthTime])
        simp only [Freezing1.birthTime] at this
        omega
      refine ⟨by omega, ?_⟩
      rw [show k + (j + 1) = k + j + 1 by omega, Freezing1.activeCount_succ, hS, hup,
        ite_eq_left rfl]
      push_cast
      ring
  obtain ⟨hkM, hS⟩ := hclaim M le_rfl
  have h1 := hM (k + M) hkM
  have h2 := hpos k hk
  omega

/-- Every point of `[0, h_n]` is within `M + 1` of the harmonic centre of some label. -/
theorem exists_label_heightScale_near {y : Freezing1.SignSequence} {n M : ℕ}
    (hpos : Freezing1.PositiveThrough y n) (hM : ∀ k ≤ n, Freezing1.activeCount y k ≤ M)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ Freezing1.heightScale y n) :
    ∃ v ∈ Freezing1.vertexLabels y n,
      |Freezing1.heightScale y (Freezing1.birthTime n v) - s| ≤ M + 1 := by
  have hP : ∃ k, s ≤ Freezing1.heightScale y k := ⟨n, hs1⟩
  set k := Nat.find hP with hkdef
  have hkn : k ≤ n := Nat.find_min' hP hs1
  have hks : s ≤ Freezing1.heightScale y k := Nat.find_spec hP
  have hk1 : Freezing1.heightScale y k - s ≤ 1 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos'
    · rw [h0] at hks ⊢
      simp only [Freezing1.heightScale_zero] at hks ⊢
      linarith
    · have hlt : ¬ s ≤ Freezing1.heightScale y (k - 1) := Nat.find_min hP (by omega)
      have hstep := (heightScale_le_le hpos (Nat.sub_le k 1) hkn).2
      rw [show k - (k - 1) = 1 by omega] at hstep
      push_cast at hstep
      linarith
  obtain ⟨v, hv, hb1, hb2⟩ := exists_label_birthTime_near hpos hM hkn
  refine ⟨v, hv, ?_⟩
  have hbn : Freezing1.birthTime n v ≤ n := by
    cases v with
    | inl j => simp [Freezing1.birthTime]
    | inr i =>
      simp only [Freezing1.vertexLabels, Finset.inr_mem_disjSum, Freezing1.frozenIndices,
        Finset.mem_filter, Finset.mem_range] at hv
      simp only [Freezing1.birthTime]
      omega
  obtain ⟨h1, h2⟩ := heightScale_le_le hpos hb1 hbn
  have hd : ((Freezing1.birthTime n v - k : ℕ) : ℝ) ≤ M := by
    exact_mod_cast (show Freezing1.birthTime n v - k ≤ M by omega)
  rw [abs_le]
  constructor <;> linarith

/-! ### Probabilistic estimates on the reverse tree -/

/-- **Uniform height concentration** (Bennett plus a union bound over labels). -/
theorem height_deviation_probability_le {y : Freezing1.SignSequence} {n : ℕ}
    (hpos : Freezing1.PositiveThrough y n) {t : ℝ} (ht : 0 < t)
    (hH : 0 < Freezing1.heightScale y n) :
    (jointLaw y n).real {ω | ∃ v ∈ Freezing1.vertexLabels y n,
        t < |((ω n).depth v : ℝ) - Freezing1.heightScale y (Freezing1.birthTime n v)|} ≤
      2 * ((n : ℝ) + 1) * Real.exp (-bennettExponent t (Freezing1.heightScale y n)) := by
  have hn : (n : ℕ∞) ≤ Freezing1.extinctionTime y :=
    ((Freezing1.lt_extinctionTime_iff y n).mpr hpos).le
  let κ := {v // v ∈ Freezing1.vertexLabels y n}
  have hsum (v : κ) : (∑ i, (heightBernoulliParameter y n 0 v.val i : ℝ)) =
      Freezing1.heightScale y (Freezing1.birthTime n v.val) := by
    rw [sum_heightBernoulliParameter hn v.property]
    simp only [Nat.sub_zero, zero_add]
    rfl
  have hbn (v : κ) : Freezing1.birthTime n v.val ≤ n := birthTime_le_horizon v.property
  have hmean (v : κ) : (∑ i, (heightBernoulliParameter y n 0 v.val i : ℝ)) ≤
      Freezing1.heightScale y n := by
    rw [hsum v]
    exact (heightScale_le_le hpos (hbn v) le_rfl).1
  have hb := finite_height_deviation_union_bound (κ := κ) (μ := jointLaw y n)
    (ν := fun _ ↦ jointLaw y n)
    (fun v ↦ Freezing1.birthTime n v.val - 0) (fun v ↦ heightAt n 0 v.val)
    (fun v ↦ heightBernoulli n 0 v.val) (fun v ↦ heightBernoulliParameter y n 0 v.val)
    (fun v ↦ identDistrib_heightAt_sum_heightBernoulli hn v.property (Nat.zero_le _))
    (fun v ↦ iIndepFun_heightBernoulli hn v.property)
    (fun v i ↦ hasLaw_heightBernoulli y n 0 v.val i) ht hH hmean
  have hsub : {ω : History | ∃ v ∈ Freezing1.vertexLabels y n,
      t < |((ω n).depth v : ℝ) - Freezing1.heightScale y (Freezing1.birthTime n v)|} ⊆
      {ω | ∃ j : κ, t < |heightAt n 0 j.val ω -
        (∑ i, (heightBernoulliParameter y n 0 j.val i : ℝ))|} := by
    rintro ω ⟨v, hv, hlt⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [hsum ⟨v, hv⟩]
    simpa only [heightAt, forestAt, Nat.sub_zero] using hlt
  have hcard : (Fintype.card κ : ℝ) ≤ (n : ℝ) + 1 := by
    have h1 : Fintype.card κ = (Freezing1.vertexLabels y n).card := Fintype.card_coe _
    have h2 := Freezing1.card_vertexLabels (x := y) (n := n) (hpos n le_rfl).le
    have h3 := Freezing1.plusCount_le y n
    have : Fintype.card κ ≤ n + 1 := by omega
    exact_mod_cast this
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := hb
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith

/-- Macroscopic branching excess in the reverse tree is unlikely under bounded
population (the side-branch estimate of N09, at threshold `η h_n^+`). -/
theorem tendsto_reverseExcess_probability {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x) {M : ℕ}
    (hM : ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ω n ∈ reverseExcessEvent
        (η * Freezing1.heightScale (companionSchedule (x n)) n)}) atTop (𝓝 0) := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  have hMpos : (0 : ℝ) < M := by linarith
  set b : ℝ := η / (8 * (M : ℝ) ^ 3) with hb
  have hbpos : 0 < b := by positivity
  have hlim := (tendsto_sq_mul_exp_neg_linear hbpos).const_mul (Real.exp (1 / (M : ℝ)))
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hlim
  refine Eventually.of_forall fun n ↦ ?_
  have hsx := (hx n).2
  have hτ := (companion_before_extinction (x n) (hx n).1 hsx).le
  have hl := heightScale_ge_of_bounded (x n) (hx n).1 hsx (hM n)
  set h := Freezing1.heightScale (companionSchedule (x n)) n with hh
  set D := η * h with hD
  have hDpos : 0 ≤ D := by
    have : (0 : ℝ) ≤ h := (by positivity : (0 : ℝ) ≤ n / (2 * M)).trans hl
    positivity
  set K := ⌊D / 2⌋₊ + 1 with hK
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  have hDK : 2 * ((K : ℝ) - 1) ≤ D := by
    have := Nat.floor_le (show 0 ≤ D / 2 by positivity)
    rw [hK]
    push_cast
    linarith
  have hKlow : D / 2 ≤ K := by
    have := Nat.lt_floor_add_one (D / 2)
    rw [hK]
    push_cast
    linarith
  have hexp : Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) ≤
      Real.exp (1 / (M : ℝ)) * Real.exp (-(b * n)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hK' : η * n / (4 * M) ≤ K := by
      have : η * ((n : ℝ) / (2 * M)) ≤ η * h := mul_le_mul_of_nonneg_left hl hη.le
      have e : η * ((n : ℝ) / (2 * M)) / 2 = η * n / (4 * M) := by
        field_simp
        ring
      linarith
    have e1 : ((K : ℝ) - M) / (M : ℝ) ^ 2 = (K : ℝ) / (M : ℝ) ^ 2 - 1 / M := by
      field_simp
    have e2 : b * n = (η * n / (4 * M)) / (M : ℝ) ^ 2 / 2 := by
      rw [hb]
      field_simp
      ring
    rw [e1, e2]
    have : (η * n / (4 * M)) / (M : ℝ) ^ 2 ≤ (K : ℝ) / (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hK' (by positivity)
    have hnn : 0 ≤ (η * n / (4 * M)) / (M : ℝ) ^ 2 := by positivity
    linarith
  calc
    _ ≤ (jointLaw (companionSchedule (x n)) n).real
        (slowGapEvent (companionSchedule (x n)) n K) :=
      jointLaw_reverseExcess_le_slowGap hτ hDK
    _ ≤ ((n : ℝ) + 1) ^ 2 * Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) :=
      slowGapEvent_probability_le (x n) (hx n).1 hsx (hM n) hK1
    _ ≤ ((n : ℝ) + 1) ^ 2 * (Real.exp (1 / (M : ℝ)) * Real.exp (-(b * n))) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- Heights of all reverse vertices are within `η h_n^+` of their harmonic centres,
with high probability. -/
theorem tendsto_height_deviation_probability {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    {M : ℕ} (hM : ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ∃ v ∈ Freezing1.vertexLabels (companionSchedule (x n)) n,
        η * Freezing1.heightScale (companionSchedule (x n)) n <
          |((ω n).depth v : ℝ) - Freezing1.heightScale (companionSchedule (x n))
            (Freezing1.birthTime n v)|}) atTop (𝓝 0) := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  set β := bennettFunction η with hβ
  have hβpos : 0 < β := bennettFunction_pos hη
  set b : ℝ := β / (2 * M) with hb
  have hbpos : 0 < b := by positivity
  have hlim := (tendsto_sq_mul_exp_neg_linear hbpos).const_mul 2
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpos := companion_positiveThrough (x n) (hx n).1 (hx n).2
  have hl := heightScale_ge_of_bounded (x n) (hx n).1 (hx n).2 (hM n)
  set h := Freezing1.heightScale (companionSchedule (x n)) n with hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hhpos : 0 < h := lt_of_lt_of_le (by positivity) hl
  have hbd := height_deviation_probability_le hpos (mul_pos hη hhpos) hhpos
  have hexp : bennettExponent (η * h) h = h * β := by
    rw [bennettExponent, mul_div_cancel_right₀ _ hhpos.ne']
  rw [hexp] at hbd
  refine hbd.trans ?_
  have h1 : Real.exp (-(h * β)) ≤ Real.exp (-(b * n)) := by
    apply Real.exp_le_exp.mpr
    have : b * n ≤ h * β := by
      have e : b * n = (n / (2 * M)) * β := by rw [hb]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hl hβpos.le
    linarith
  have h2 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * ((n : ℝ) + 1) ^ 2 * Real.exp (-(b * n)) := by
      apply mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-! ### The general measured limit -/

/-- **Measured limit, reverse form.** For an admissible array with bounded population
whose height profile `h_k^+ / h_n^+` converges uniformly to `H(k/n)`, the uniformly
measured terminal reverse trees, scaled by `1 / h_n^+`, converge in probability for the
GHP distance to the unit segment carrying `segmentLaw H`. -/
theorem tendsto_forestMeasuredSpace_dist {x : ℕ → ℕ → ℤ} (hx : AdmissibleArray x)
    {M : ℕ} (hM : ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {H : ℝ → ℝ} (hH : Continuous H)
    (hconv : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
      |Freezing1.heightScale (companionSchedule (x n)) k /
        Freezing1.heightScale (companionSchedule (x n)) n - H (k / n)| ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε < dist (toMeasuredGHSpace (forestMeasuredSpace
        (1 / Freezing1.heightScale (companionSchedule (x n)) n) (ω n)))
        (toMeasuredGHSpace (measuredSegment H))}) atTop (𝓝 0) := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  set η := ε / 10 with hηdef
  have hη : 0 < η := by positivity
  have hsum := (tendsto_reverseExcess_probability hx hM hη).add
    (tendsto_height_deviation_probability hx hM hη)
  rw [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hsum
  have hp := (tendsto_coordinateLaw_levyProkhorovDist hx hM hH hconv).eventually_lt_const hη
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * M * (M + 1) / η ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop 0, hp, hlarge] with n hn hpn hnl
  set y := companionSchedule (x n) with hy
  have hpos : Freezing1.PositiveThrough y n := companion_positiveThrough (x n) (hx n).1 (hx n).2
  have hτ : (n : ℕ∞) ≤ Freezing1.extinctionTime y :=
    (companion_before_extinction (x n) (hx n).1 (hx n).2).le
  have hM' : ∀ k ≤ n, Freezing1.activeCount y k ≤ M := by
    intro k hk
    rw [hy, companion_activeCount (x n) (hx n).1]
    exact hM n k hk
  have hl := heightScale_ge_of_bounded (x n) (hx n).1 (hx n).2 (hM n)
  set h := Freezing1.heightScale y n with hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hhpos : 0 < h := lt_of_lt_of_le (by positivity) hl
  have hρ : ((M : ℝ) + 1) / h ≤ η := by
    rw [div_le_iff₀ hhpos]
    have h1 : 2 * M * (M + 1) ≤ η * n := by
      have := (div_le_iff₀ hη).mp hnl
      linarith
    have h2 : η * ((n : ℝ) / (2 * M)) ≤ η * h := mul_le_mul_of_nonneg_left hl hη.le
    have h3 : η * ((n : ℝ) / (2 * M)) = η * n / (2 * M) := by ring
    rw [h3, div_le_iff₀ (by positivity)] at h2
    nlinarith
  have hsub : {ω | ε < dist (toMeasuredGHSpace (forestMeasuredSpace (1 / h) (ω n)))
        (toMeasuredGHSpace (measuredSegment H))} ≤ᵐ[jointLaw y n]
      {ω | ω n ∈ reverseExcessEvent (η * h)} ∪
        {ω | ∃ v ∈ Freezing1.vertexLabels y n,
          η * h < |((ω n).depth v : ℝ) - Freezing1.heightScale y (Freezing1.birthTime n v)|} := by
    filter_upwards [jointLaw_forestAt_valid y n hτ] with ω hvalid
    intro hbad
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hnot
    obtain ⟨hnexc, hnh⟩ := hnot
    have hF : Freezing1.Reverse.ValidAt y n 0 (ω n) := by
      simpa only [forestAt, Nat.sub_zero] using hvalid 0 (Nat.zero_le n)
    have hV : (ω n).vertices = Freezing1.vertexLabels y n := by
      simpa only [Freezing1.Reverse.phaseLabels_zero] using hF.vertices_eq
    have hcoord : ∀ v ∈ (ω n).vertices,
        1 / h * Freezing1.heightScale y (Freezing1.birthTime n v) ∈ Icc (0 : ℝ) 1 := by
      intro v hv
      rw [hV] at hv
      have hb := birthTime_le_horizon hv
      have h1 := heightScale_nonneg hpos hb
      have h2 := (heightScale_le_le hpos hb le_rfl).1
      refine ⟨by positivity, ?_⟩
      rw [one_div_mul_eq_div, div_le_one hhpos]
      exact h2
    have hdense : ∀ t ∈ Icc (0 : ℝ) 1, ∃ v ∈ (ω n).vertices,
        |1 / h * Freezing1.heightScale y (Freezing1.birthTime n v) - t| ≤ η := by
      intro t ht
      obtain ⟨v, hv, hvt⟩ := exists_label_heightScale_near hpos hM'
        (s := t * h) (by nlinarith [ht.1]) (by nlinarith [ht.2])
      refine ⟨v, hV ▸ hv, ?_⟩
      have e : 1 / h * Freezing1.heightScale y (Freezing1.birthTime n v) - t =
          (Freezing1.heightScale y (Freezing1.birthTime n v) - t * h) / h := by
        field_simp
      rw [e, abs_div, abs_of_pos hhpos]
      exact (div_le_div_of_nonneg_right hvt hhpos.le).trans hρ
    have hbound := forestMeasuredSpace_dist_le hF (H := H) (one_div_pos.mpr hhpos)
      (mul_pos hη hhpos) hnexc (fun v hv ↦ hnh v (hV ▸ hv)) hcoord hdense hpn.le
    have e : 1 / h * (η * h) = η := by field_simp
    rw [e] at hbound
    change ε < _ at hbad
    linarith
  calc
    _ ≤ (jointLaw y n).real ({ω | ω n ∈ reverseExcessEvent (η * h)} ∪
        {ω | ∃ v ∈ Freezing1.vertexLabels y n,
          η * h < |((ω n).depth v : ℝ) - Freezing1.heightScale y (Freezing1.birthTime n v)|}) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ _ := measureReal_union_le _ _

/-- **Measured limit for bounded population (general form).** Under the hypotheses
of N09 (`bounded_population_GH_limit`), if moreover `h_k^+ / h_n^+ → H(k/n)` uniformly in
`k ≤ n` for a continuous `H`, then the actual forward trees with their uniform vertex
measures, distances scaled by `1 / h_n^+`, converge in probability in the GHP distance
to the unit segment carrying the image of Lebesgue measure under `H`. -/
theorem bounded_population_GHP_limit {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {H : ℝ → ℝ} (hH : Continuous H)
    (hconv : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
      |Freezing1.heightScale (companionSchedule (x n)) k /
        Freezing1.heightScale (companionSchedule (x n)) n - H (k / n)| ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw x n).real {s | ε < dist
      (toMeasuredGHSpace
        (forwardMeasuredSpace (1 / Freezing1.heightScale (companionSchedule (x n)) n) s))
      (toMeasuredGHSpace (measuredSegment H))}) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hM
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  set y := initialRowExtension x with hydef
  have hy := admissible_initialRowExtension hx
  have hyM : ∀ n k : ℕ, k ≤ n → activeCount (y n) k ≤ M := by
    intro n k hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      rw [activeCount_zero]
      exact_mod_cast hM1
    · simp only [hydef, initialRowExtension, ite_eq_right (Nat.ne_of_gt hn)]
      exact hM n k hk
  have hyconv : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
      |Freezing1.heightScale (companionSchedule (y n)) k /
        Freezing1.heightScale (companionSchedule (y n)) n - H (k / n)| ≤ η := by
    intro η hη
    filter_upwards [hconv η hη, initialRowExtension_eventually_eq x] with n hn he
    rw [hydef, he]
    exact hn
  have hrev := tendsto_forestMeasuredSpace_dist hy hyM hH hyconv hε
  apply hrev.congr'
  filter_upwards [eventually_gt_atTop 0, initialRowExtension_eventually_eq x] with n hn he
  have hpos : 0 < Freezing1.heightScale (companionSchedule (x n)) n :=
    lt_of_lt_of_le (by positivity)
      (heightScale_ge_of_bounded (x n) (hx n hn).1 (hx n hn).2 (hM n))
  rw [freezingTreeLaw, forward_measured_far_eq_reverse _ n
    (companion_before_extinction (x n) (hx n hn).1 (hx n hn).2).le (one_div_pos.mpr hpos),
    ← he]

/-! ### Uniqueness of limits in probability -/

/-- Two limits in probability of the same random measured spaces are at distance zero. -/
theorem dist_eq_zero_of_tendsto_far {Ω : Type*} [MeasurableSpace Ω] {μ : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (μ n)] {T : ℕ → Ω → MeasuredGHSpace.{0}}
    {L₁ L₂ : MeasuredGHSpace.{0}}
    (h₁ : ∀ ε > 0, Tendsto (fun n ↦ (μ n).real {s | ε < dist (T n s) L₁}) atTop (𝓝 0))
    (h₂ : ∀ ε > 0, Tendsto (fun n ↦ (μ n).real {s | ε < dist (T n s) L₂}) atTop (𝓝 0)) :
    dist L₁ L₂ = 0 := by
  apply le_antisymm _ dist_nonneg
  by_contra hpos
  push Not at hpos
  set δ := dist L₁ L₂ / 3 with hδ
  have hδpos : 0 < δ := by positivity
  have hsum := (h₁ δ hδpos).add (h₂ δ hδpos)
  rw [add_zero] at hsum
  obtain ⟨n, hn⟩ := (hsum.eventually_lt_const one_pos).exists
  have hne : {s | δ < dist (T n s) L₁} ∪ {s | δ < dist (T n s) L₂} ≠ univ := by
    intro huniv
    have h1 := measureReal_union_le (μ := μ n) {s | δ < dist (T n s) L₁}
      {s | δ < dist (T n s) L₂}
    rw [huniv, probReal_univ] at h1
    linarith
  obtain ⟨s, hs⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hs
  have htri := dist_triangle_left L₁ L₂ (T n s)
  linarith

/-! ### Two explicit bounded-population arrays -/

/-- Signs `+1` at odd times up to `m + 1`, then `+1` at even times from `m + 2` on
(`-1` otherwise). For even `m` the population is `1 + (k mod 2) ∈ {1,2}` up to time
`m + 1` and `3 - (k mod 2) ∈ {2,3}` afterwards. -/
def switchedSign (m : ℕ) (i : ℕ) : ℤ :=
  if (i ≤ m + 1 ∧ i % 2 = 1) ∨ (m + 2 ≤ i ∧ i % 2 = 0) then 1 else -1

/-- The switched sequence takes values `±1`. -/
theorem switchedSign_isSigned (m : ℕ) : IsSigned (switchedSign m) := by
  intro i _
  unfold switchedSign
  split_ifs <;> simp

/-- Exact population of the switched sequence. -/
theorem activeCount_switchedSign {m : ℕ} (hm : m % 2 = 0) (k : ℕ) :
    activeCount (switchedSign m) k =
      if k ≤ m + 1 then 1 + (k % 2 : ℕ) else 3 - (k % 2 : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [activeCount_succ, ih]
    unfold switchedSign
    split_ifs <;> omega

/-- The switched population lies in `{1,2,3}`. -/
theorem activeCount_switchedSign_mem {m : ℕ} (hm : m % 2 = 0) (k : ℕ) :
    1 ≤ activeCount (switchedSign m) k ∧ activeCount (switchedSign m) k ≤ 3 := by
  rw [activeCount_switchedSign hm]
  split_ifs <;> omega

/-- One step of the switched height scale: `1/2` at odd up-steps before the switch,
`1/3` at even up-steps after it. -/
theorem heightScale_switchedSign_succ {m : ℕ} (hm : m % 2 = 0) (k : ℕ) :
    Freezing1.heightScale (companionSchedule (switchedSign m)) (k + 1) =
      Freezing1.heightScale (companionSchedule (switchedSign m)) k +
        if k + 1 ≤ m + 1 then (if (k + 1) % 2 = 1 then 1 / 2 else 0)
        else (if (k + 1) % 2 = 0 then 1 / 3 else 0) := by
  rw [Freezing1.heightScale_succ, companion_activeCount _ (switchedSign_isSigned m)]
  congr 1
  have hS := activeCount_switchedSign hm (k + 1)
  simp only [companionSchedule]
  by_cases h1 : k + 1 ≤ m + 1
  · rw [ite_eq_left h1] at hS
    rw [ite_eq_left h1]
    rcases Nat.mod_two_eq_zero_or_one (k + 1) with hp | hp
    · have hx : switchedSign m (k + 1) = -1 := by
        unfold switchedSign
        rw [ite_eq_right (by omega)]
      simp [hx, hp]
    · have hx : switchedSign m (k + 1) = 1 := by
        unfold switchedSign
        rw [ite_eq_left (by omega)]
      have hS2 : activeCount (switchedSign m) (k + 1) = 2 := by rw [hS, hp]; rfl
      simp [hx, hp, hS2]
  · rw [ite_eq_right h1] at hS
    rw [ite_eq_right h1]
    rcases Nat.mod_two_eq_zero_or_one (k + 1) with hp | hp
    · have hx : switchedSign m (k + 1) = 1 := by
        unfold switchedSign
        rw [ite_eq_left (by omega)]
      have hS2 : activeCount (switchedSign m) (k + 1) = 3 := by rw [hS, hp]; rfl
      simp [hx, hp, hS2]
    · have hx : switchedSign m (k + 1) = -1 := by
        unfold switchedSign
        rw [ite_eq_right (by omega)]
      simp [hx, hp]

/-- Exact switched height scale. -/
theorem heightScale_switchedSign {m : ℕ} (hm : m % 2 = 0) (k : ℕ) :
    Freezing1.heightScale (companionSchedule (switchedSign m)) k =
      if k ≤ m + 1 then (((k + 1) / 2 : ℕ) : ℝ) / 2
      else (((m + 2) / 2 : ℕ) : ℝ) / 2 + (((k - m) / 2 : ℕ) : ℝ) / 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [heightScale_switchedSign_succ hm, ih]
    by_cases h1 : k + 1 ≤ m + 1
    · rw [ite_eq_left h1, ite_eq_left (show k ≤ m + 1 by omega), ite_eq_left h1]
      rcases Nat.mod_two_eq_zero_or_one (k + 1) with hp | hp
      · have e : (k + 1 + 1) / 2 = (k + 1) / 2 := by omega
        rw [ite_eq_right (by omega), e, add_zero]
      · have e : (k + 1 + 1) / 2 = (k + 1) / 2 + 1 := by omega
        rw [ite_eq_left hp, e]
        push_cast
        ring
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : k ≤ m + 1
      · have hk : k = m + 1 := by omega
        subst hk
        rw [ite_eq_left h2]
        have e1 : (m + 1 + 1) % 2 = 0 := by omega
        have e2 : (m + 1 + 1 - m) / 2 = 1 := by omega
        have e3 : (m + 1 + 1) / 2 = (m + 2) / 2 := by omega
        rw [ite_eq_left e1, e2, e3]
        push_cast
        ring
      · rw [ite_eq_right h2]
        rcases Nat.mod_two_eq_zero_or_one (k + 1) with hp | hp
        · have e : (k + 1 - m) / 2 = (k - m) / 2 + 1 := by omega
          rw [ite_eq_left hp, e]
          push_cast
          ring
        · have e : (k + 1 - m) / 2 = (k - m) / 2 := by omega
          rw [ite_eq_right (by omega), e, add_zero]

/-- Within horizon `n`, the alternating height profile is `k/4` up to `1/4`. -/
theorem alternating_heightScale_approx (n k : ℕ) (hk : k ≤ n) :
    |Freezing1.heightScale (companionSchedule (switchedSign (2 * n))) k -
      n * ((k / n : ℝ) / 4)| ≤ 1 := by
  rw [heightScale_switchedSign (by omega), ite_eq_left (by omega)]
  have hq : 2 * (((k + 1) / 2 : ℕ) : ℝ) = k ∨ 2 * (((k + 1) / 2 : ℕ) : ℝ) = k + 1 := by
    rcases (show 2 * ((k + 1) / 2) = k ∨ 2 * ((k + 1) / 2) = k + 1 by omega) with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have ht : (n : ℝ) * ((k / n : ℝ) / 4) = k / 4 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : k = 0 := by omega
      subst this
      simp
    · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
  rw [ht, abs_le]
  constructor <;> rcases hq with h | h <;> linarith

/-- Within horizon `n`, the switched height profile is `k/6 + min(k, n/2)/12` up to `1`. -/
theorem switched_heightScale_approx (n k : ℕ) (hk : k ≤ n) :
    |Freezing1.heightScale (companionSchedule (switchedSign (2 * (n / 4)))) k -
      n * ((k / n : ℝ) / 6 + min (k / n : ℝ) (1 / 2) / 12)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : k = 0 := by omega
    subst this
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (n : ℝ) * ((k / n : ℝ) / 6 + min (k / n : ℝ) (1 / 2) / 12) =
      k / 6 + min (k : ℝ) (n / 2) / 12 := by
    have hmin : (n : ℝ) * min (k / n : ℝ) (1 / 2) = min (k : ℝ) (n / 2) := by
      rw [mul_min_of_nonneg _ _ hnR.le, mul_div_cancel₀ _ hnR.ne']
      ring_nf
    rw [mul_add, ← hmin]
    field_simp
  rw [heightScale_switchedSign (by omega), ht]
  set m := 2 * (n / 4) with hm
  have hm1 : 2 * (m : ℝ) ≤ n := by exact_mod_cast (show 2 * m ≤ n by omega)
  have hm2 : (n : ℝ) < 2 * m + 4 := by exact_mod_cast (show n < 2 * m + 4 by omega)
  by_cases h1 : k ≤ m + 1
  · rw [ite_eq_left h1]
    have hq : 2 * (((k + 1) / 2 : ℕ) : ℝ) = k ∨ 2 * (((k + 1) / 2 : ℕ) : ℝ) = k + 1 := by
      rcases (show 2 * ((k + 1) / 2) = k ∨ 2 * ((k + 1) / 2) = k + 1 by omega) with h | h
      · left
        exact_mod_cast h
      · right
        exact_mod_cast h
    have hkm : (k : ℝ) ≤ m + 1 := by exact_mod_cast h1
    rw [abs_le]
    rcases le_total (k : ℝ) (n / 2) with h2 | h2
    · rw [min_eq_left h2]
      constructor <;> rcases hq with h | h <;> linarith
    · rw [min_eq_right h2]
      constructor <;> rcases hq with h | h <;> linarith
  · rw [ite_eq_right h1]
    have hp : 2 * (((m + 2) / 2 : ℕ) : ℝ) = m + 2 := by
      exact_mod_cast (show 2 * ((m + 2) / 2) = m + 2 by omega)
    have hr : 2 * (((k - m) / 2 : ℕ) : ℝ) = k - m ∨ 2 * (((k - m) / 2 : ℕ) : ℝ) = k - m - 1 := by
      have hkm : m ≤ k := by omega
      rcases (show 2 * ((k - m) / 2) = k - m ∨ 2 * ((k - m) / 2) + 1 = k - m by omega)
        with h | h
      · left
        have : ((k - m : ℕ) : ℝ) = k - m := by push_cast [hkm]; ring
        rw [← this]
        exact_mod_cast h
      · right
        have : ((k - m : ℕ) : ℝ) = k - m := by push_cast [hkm]; ring
        have h' : (2 * (((k - m) / 2 : ℕ) : ℝ)) + 1 = ((k - m : ℕ) : ℝ) := by exact_mod_cast h
        linarith
    have hkm : (m : ℝ) + 2 ≤ k := by exact_mod_cast (show m + 2 ≤ k by omega)
    have h2 : (n : ℝ) / 2 ≤ k := by linarith
    rw [min_eq_right h2, abs_le]
    constructor <;> rcases hr with h | h <;> linarith


/-- A height profile within a bounded distance of `n G(k/n)` has the normalized
uniform limit `G / G(1)`. -/
theorem uniform_profile_of_linear_approx {h : ℕ → ℕ → ℝ} {G : ℝ → ℝ} {C B : ℝ}
    (hG1 : 0 < G 1) (hGB : ∀ t ∈ Icc (0 : ℝ) 1, |G t| ≤ B)
    (happrox : ∀ n k : ℕ, k ≤ n → |h n k - n * G (k / n)| ≤ C) :
    ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n, |h n k / h n n - G (k / n) / G 1| ≤ η := by
  intro η hη
  have hC : 0 ≤ C := (abs_nonneg _).trans (happrox 0 0 le_rfl)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hGB 0 ⟨le_rfl, zero_le_one⟩)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      2 * C / G 1 + 2 * C * (G 1 + B) / (η * G 1 ^ 2) ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop 0, hlarge] with n hn hnl k hk
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hT1 : 0 ≤ 2 * C / G 1 := by positivity
  have hT2 : 0 ≤ 2 * C * (G 1 + B) / (η * G 1 ^ 2) := by positivity
  have hn1 : 2 * C ≤ n * G 1 := by
    have := (div_le_iff₀ hG1).mp (show 2 * C / G 1 ≤ n by linarith)
    linarith
  have hn2 : 2 * C * (G 1 + B) ≤ η * G 1 ^ 2 * n := by
    have := (div_le_iff₀ (by positivity : 0 < η * G 1 ^ 2)).mp
      (show 2 * C * (G 1 + B) / (η * G 1 ^ 2) ≤ n by linarith)
    linarith
  have hkn : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hnpos).mpr (by exact_mod_cast hk)⟩
  have hGk := hGB _ hkn
  have hk' := happrox n k hk
  have hn' := happrox n n le_rfl
  rw [div_self hnpos.ne'] at hn'
  set a := h n k
  set b := h n n
  set g := G ((k : ℝ) / n)
  set g1 := G 1
  have hb : n * g1 / 2 ≤ b := by
    rw [abs_le] at hn'
    linarith
  have hbpos : 0 < b := lt_of_lt_of_le (by positivity) hb
  have e : a / b - g / g1 = ((a - n * g) * g1 - (b - n * g1) * g) / (b * g1) := by
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : 0 < b * g1), div_le_iff₀ (by positivity)]
  have h1 : |(a - n * g) * g1 - (b - n * g1) * g| ≤ C * g1 + C * B := by
    calc
      _ ≤ |(a - n * g) * g1| + |(b - n * g1) * g| := abs_sub _ _
      _ = |a - n * g| * g1 + |b - n * g1| * |g| := by
        rw [abs_mul, abs_mul, abs_of_pos hG1]
      _ ≤ C * g1 + C * B := by
        apply add_le_add (mul_le_mul_of_nonneg_right hk' hG1.le)
        exact mul_le_mul hn' hGk (abs_nonneg _) hC
  have h2 : η * (n * g1 / 2 * g1) ≤ η * (b * g1) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hG1.le) hη.le
  nlinarith


/-- Alternating signs `+1, -1, +1, -1, …` at every horizon: population in `{1,2}`. -/
def alternatingArray (n : ℕ) : ℕ → ℤ := switchedSign (2 * n)

/-- Within its horizon, `alternatingArray n` is the alternating sign sequence. -/
theorem alternatingArray_apply {n i : ℕ} (hi : i ≤ n) :
    alternatingArray n i = if i % 2 = 1 then 1 else -1 := by
  unfold alternatingArray switchedSign
  by_cases h : i % 2 = 1
  · rw [ite_eq_left (Or.inl ⟨by omega, h⟩), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- Alternating signs up to time `2⌊n/4⌋ + 1` (population in `{1,2}`), then a population
oscillating in `{2,3}`: same vertex birth rate, smaller slope of `h^+` on the second half. -/
def switchedArray (n : ℕ) : ℕ → ℤ := switchedSign (2 * (n / 4))

/-- The limiting height profile of `alternatingArray`: `H(t) = t`. -/
def alternatingProfile : ℝ → ℝ := fun t ↦ t

/-- The limiting height profile of `switchedArray`: `6t/5` on `[0,1/2]`, `(4t+1)/5` on
`[1/2,1]`. -/
noncomputable def switchedProfile : ℝ → ℝ := fun t ↦ (4 * t + 2 * min t (1 / 2)) / 5

/-- Every horizon of a switched sequence is admissible. -/
theorem switchedSign_admissible {m : ℕ} (hm : m % 2 = 0) (n : ℕ) :
    IsSigned (switchedSign m) ∧ SurvivesThrough (switchedSign m) n :=
  ⟨switchedSign_isSigned m, fun k _ ↦ (activeCount_switchedSign_mem hm k).1⟩

/-- The alternating array satisfies the hypotheses of `thm:alpha0`. -/
theorem alternatingArray_admissible :
    ∀ n : ℕ, 0 < n → IsSigned (alternatingArray n) ∧ SurvivesThrough (alternatingArray n) n :=
  fun n _ ↦ switchedSign_admissible (by omega) n

/-- The alternating population is at most `3` (in fact `2`). -/
theorem alternatingArray_bounded :
    ∀ n k : ℕ, k ≤ n → activeCount (alternatingArray n) k ≤ 3 :=
  fun n k _ ↦ (activeCount_switchedSign_mem (by omega) k).2

/-- The switched array satisfies the hypotheses of `thm:alpha0`. -/
theorem switchedArray_admissible :
    ∀ n : ℕ, 0 < n → IsSigned (switchedArray n) ∧ SurvivesThrough (switchedArray n) n :=
  fun n _ ↦ switchedSign_admissible (by omega) n

/-- The switched population is at most `3`. -/
theorem switchedArray_bounded :
    ∀ n k : ℕ, k ≤ n → activeCount (switchedArray n) k ≤ 3 :=
  fun n k _ ↦ (activeCount_switchedSign_mem (by omega) k).2

/-- The height profile of `alternatingArray` converges uniformly to `t ↦ t`. -/
theorem alternatingArray_profile : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
    |Freezing1.heightScale (companionSchedule (alternatingArray n)) k /
      Freezing1.heightScale (companionSchedule (alternatingArray n)) n -
        alternatingProfile (k / n)| ≤ η := by
  have h := uniform_profile_of_linear_approx (h := fun n k ↦
      Freezing1.heightScale (companionSchedule (alternatingArray n)) k)
    (G := fun t ↦ t / 4) (C := 1) (B := 1) (by norm_num)
    (fun t ht ↦ by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    (fun n k hk ↦ alternating_heightScale_approx n k hk)
  intro η hη
  filter_upwards [h η hη] with n hn k hk
  have e : ((k : ℝ) / n / 4) / (1 / 4) = alternatingProfile (k / n) := by
    unfold alternatingProfile
    ring
  rw [← e]
  exact hn k hk

/-- The height profile of `switchedArray` converges uniformly to `switchedProfile`. -/
theorem switchedArray_profile : ∀ η > 0, ∀ᶠ n in atTop, ∀ k ≤ n,
    |Freezing1.heightScale (companionSchedule (switchedArray n)) k /
      Freezing1.heightScale (companionSchedule (switchedArray n)) n -
        switchedProfile (k / n)| ≤ η := by
  have h := uniform_profile_of_linear_approx (h := fun n k ↦
      Freezing1.heightScale (companionSchedule (switchedArray n)) k)
    (G := fun t ↦ t / 6 + min t (1 / 2) / 12) (C := 1) (B := 1)
    (by have := le_min (zero_le_one' ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 2); positivity)
    (fun t ht ↦ by
      have h1 := min_le_right t (1 / 2)
      have h2 := le_min ht.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2])
    (fun n k hk ↦ switched_heightScale_approx n k hk)
  intro η hη
  filter_upwards [h η hη] with n hn k hk
  have e : ((k : ℝ) / n / 6 + min ((k : ℝ) / n) (1 / 2) / 12) /
      (1 / 6 + min (1 : ℝ) (1 / 2) / 12) = switchedProfile (k / n) := by
    unfold switchedProfile
    rw [min_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    ring
  rw [← e]
  exact hn k hk

/-- The switched profile is continuous. -/
theorem continuous_switchedProfile : Continuous switchedProfile := by
  unfold switchedProfile
  fun_prop

/-- The uniformly measured alternating trees converge in probability (GHP) to
`([0,1], Lebesgue)`. -/
theorem alternatingArray_GHP_limit {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw alternatingArray n).real {s | ε < dist
      (toMeasuredGHSpace (forwardMeasuredSpace
        (1 / Freezing1.heightScale (companionSchedule (alternatingArray n)) n) s))
      (toMeasuredGHSpace (measuredSegment alternatingProfile))}) atTop (𝓝 0) :=
  bounded_population_GHP_limit alternatingArray_admissible ⟨3, alternatingArray_bounded⟩
    (H := alternatingProfile) continuous_id alternatingArray_profile hε

/-- The uniformly measured switched trees converge in probability (GHP) to `[0,1]`
carrying the image of Lebesgue measure under `switchedProfile`, a non-uniform measure
with density `5/6` on `[0,3/5]` and `5/4` on `[3/5,1]`. -/
theorem switchedArray_GHP_limit {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw switchedArray n).real {s | ε < dist
      (toMeasuredGHSpace (forwardMeasuredSpace
        (1 / Freezing1.heightScale (companionSchedule (switchedArray n)) n) s))
      (toMeasuredGHSpace (measuredSegment switchedProfile))}) atTop (𝓝 0) :=
  bounded_population_GHP_limit switchedArray_admissible ⟨3, switchedArray_bounded⟩
    continuous_switchedProfile switchedArray_profile hε

/-! ### The two limits are different -/

/-- An isometry of `[0,1]` is the identity or the reflection; in particular it
preserves the distance to the midpoint. -/
theorem abs_isometryEquiv_unitInterval_sub_half (e : unitInterval ≃ᵢ unitInterval)
    (s : unitInterval) : |(e s : ℝ) - 1 / 2| = |(s : ℝ) - 1 / 2| := by
  have h01 : |(e 0 : ℝ) - e 1| = 1 := by
    have := e.dist_eq 0 1
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at this
    rw [this]
    simp
  have hs0 : |(e s : ℝ) - e 0| = s := by
    have := e.dist_eq s 0
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at this
    rw [this]
    simp [abs_of_nonneg s.2.1]
  have ha := (e 0).2
  have hb := (e 1).2
  have hc := (e s).2
  have hs := s.2
  simp only [mem_Icc] at ha hb hc hs
  rcases abs_cases ((e 0 : ℝ) - e 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases ((e s : ℝ) - e 0) with ⟨h2, _⟩ | ⟨h2, _⟩
  · -- `e 0 = 1` and `e s ≥ e 0`
    have : (e s : ℝ) = 1 := by linarith
    have : (s : ℝ) = 0 := by linarith
    rw [‹(e s : ℝ) = 1›, this]
    norm_num
  · have he : (e s : ℝ) = 1 - s := by linarith
    rw [he, show (1 : ℝ) - s - 1 / 2 = -((s : ℝ) - 1 / 2) by ring, abs_neg]
  · have he : (e s : ℝ) = s := by linarith
    rw [he]
  · have : (s : ℝ) = 0 := by linarith
    have : (e s : ℝ) = 0 := by linarith
    rw [‹(e s : ℝ) = 0›, ‹(s : ℝ) = 0›]

/-- Points of `[0,1]` within `1/10` of the midpoint. -/
def midBand : Set unitInterval := {s | |(s : ℝ) - 1 / 2| ≤ 1 / 10}

/-- The midpoint band is measurable. -/
theorem measurableSet_midBand : MeasurableSet midBand :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

/-- Evaluation of `segmentLaw H` on a measurable set. -/
theorem segmentLaw_apply {H : ℝ → ℝ} (hH : Continuous H) {A : Set unitInterval}
    (hA : MeasurableSet A) :
    (segmentLaw H : Measure unitInterval) A =
      volume ({t | projIcc (0 : ℝ) 1 zero_le_one (H t) ∈ A} ∩ Icc 0 1) := by
  have hm : Measurable (fun t ↦ projIcc (0 : ℝ) 1 zero_le_one (H t)) :=
    (continuous_projIcc.comp hH).measurable
  change (profileMeasure.map (fun t ↦ projIcc (0 : ℝ) 1 zero_le_one (H t))) A = _
  rw [Measure.map_apply hm hA, Measure.restrict_apply (hm hA)]
  rfl

/-- Projection fixes points of `[0,1]`. -/
theorem coe_projIcc_unit {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    ((projIcc (0 : ℝ) 1 zero_le_one v : unitInterval) : ℝ) = v := by
  rw [projIcc_of_mem _ hv]

/-- Lebesgue measure gives the midpoint band mass `1/5`. -/
theorem segmentLaw_alternating_midBand :
    (segmentLaw alternatingProfile : Measure unitInterval) midBand = ENNReal.ofReal (1 / 5) := by
  rw [segmentLaw_apply (H := alternatingProfile) continuous_id measurableSet_midBand]
  have e : {t | projIcc (0 : ℝ) 1 zero_le_one (alternatingProfile t) ∈ midBand} ∩ Icc 0 1 =
      Icc (2 / 5 : ℝ) (3 / 5) := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, midBand, alternatingProfile]
    constructor
    · rintro ⟨h, h0, h1⟩
      rw [coe_projIcc_unit ⟨h0, h1⟩, abs_le] at h
      constructor <;> linarith [h.1, h.2]
    · rintro ⟨h0, h1⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [coe_projIcc_unit ⟨by linarith, by linarith⟩, abs_le]
      constructor <;> linarith
  rw [e, Real.volume_Icc]
  norm_num

/-- The switched limit gives the midpoint band mass `1/6`. -/
theorem segmentLaw_switched_midBand :
    (segmentLaw switchedProfile : Measure unitInterval) midBand = ENNReal.ofReal (1 / 6) := by
  have hc : Continuous switchedProfile := by unfold switchedProfile; fun_prop
  rw [segmentLaw_apply hc measurableSet_midBand]
  have e : {t | projIcc (0 : ℝ) 1 zero_le_one (switchedProfile t) ∈ midBand} ∩ Icc 0 1 =
      Icc (1 / 3 : ℝ) (1 / 2) := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, midBand, switchedProfile]
    constructor
    · rintro ⟨h, h0, h1⟩
      rcases le_total t (1 / 2) with ht | ht
      · rw [min_eq_left ht] at h
        rw [coe_projIcc_unit ⟨by linarith, by linarith⟩, abs_le] at h
        constructor <;> linarith [h.1, h.2]
      · rw [min_eq_right ht] at h
        rw [coe_projIcc_unit ⟨by linarith, by linarith⟩, abs_le] at h
        constructor <;> linarith [h.1, h.2]
    · rintro ⟨h0, h1⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [min_eq_left h1, coe_projIcc_unit ⟨by linarith, by linarith⟩, abs_le]
      constructor <;> linarith
  rw [e, Real.volume_Icc]
  norm_num

/-- The two measured segments are at positive GHP distance: no measure-preserving
isometry of `[0,1]` carries one measure to the other. -/
theorem measuredSegment_alternating_switched_dist_pos :
    0 < dist (toMeasuredGHSpace (measuredSegment alternatingProfile))
      (toMeasuredGHSpace (measuredSegment switchedProfile)) := by
  rw [dist_toMeasuredGHSpace]
  change 0 < ghpDistance (segmentLaw alternatingProfile : Measure unitInterval)
    (segmentLaw switchedProfile : Measure unitInterval)
  apply lt_of_le_of_ne (ghpDistance_nonneg _ _)
  intro h
  obtain ⟨e, he⟩ := (ghpDistance_eq_zero_iff_measured_isometry _ _).mp h.symm
  have hpre : e ⁻¹' midBand = midBand := by
    ext s
    simp only [mem_preimage, midBand, mem_ofPred_eq, abs_isometryEquiv_unitInterval_sub_half]
  have h1 := congrArg (fun μ : Measure unitInterval ↦ μ midBand) he
  rw [Measure.map_apply e.continuous.measurable measurableSet_midBand, hpre,
    segmentLaw_alternating_midBand, segmentLaw_switched_midBand,
    ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)] at h1
  norm_num at h1


/-! ### Nonuniversality (U20) -/

/-- **U20 (source line 1034), nonuniversality of the measured limit.** Two arrays
satisfying the hypotheses of `thm:alpha0` (population at most `3`) have uniformly
measured trees, scaled by `1 / h_n^+`, converging in probability in the GHP distance to
two measured segments at positive GHP distance, although both have the same GH limit
`[0,1]` (as N09 asserts). -/
theorem bounded_population_GHP_nonuniversal :
    (∀ n : ℕ, 0 < n → IsSigned (alternatingArray n) ∧ SurvivesThrough (alternatingArray n) n) ∧
    (∀ n k : ℕ, k ≤ n → activeCount (alternatingArray n) k ≤ 3) ∧
    (∀ n : ℕ, 0 < n → IsSigned (switchedArray n) ∧ SurvivesThrough (switchedArray n) n) ∧
    (∀ n k : ℕ, k ≤ n → activeCount (switchedArray n) k ≤ 3) ∧
    (∀ ε > 0, Tendsto (fun n ↦ (freezingTreeLaw alternatingArray n).real {s | ε < dist
      (toMeasuredGHSpace (forwardMeasuredSpace
        (1 / Freezing1.heightScale (companionSchedule (alternatingArray n)) n) s))
      (toMeasuredGHSpace (measuredSegment alternatingProfile))}) atTop (𝓝 0)) ∧
    (∀ ε > 0, Tendsto (fun n ↦ (freezingTreeLaw switchedArray n).real {s | ε < dist
      (toMeasuredGHSpace (forwardMeasuredSpace
        (1 / Freezing1.heightScale (companionSchedule (switchedArray n)) n) s))
      (toMeasuredGHSpace (measuredSegment switchedProfile))}) atTop (𝓝 0)) ∧
    0 < dist (toMeasuredGHSpace (measuredSegment alternatingProfile))
      (toMeasuredGHSpace (measuredSegment switchedProfile)) ∧
    underlyingGH (toMeasuredGHSpace (measuredSegment alternatingProfile)) =
      GromovHausdorff.toGHSpace unitInterval ∧
    underlyingGH (toMeasuredGHSpace (measuredSegment switchedProfile)) =
      GromovHausdorff.toGHSpace unitInterval :=
  ⟨alternatingArray_admissible, alternatingArray_bounded, switchedArray_admissible,
    switchedArray_bounded, fun _ hε ↦ alternatingArray_GHP_limit hε,
    fun _ hε ↦ switchedArray_GHP_limit hε, measuredSegment_alternating_switched_dist_pos,
    underlyingGH_measuredSegment _, underlyingGH_measuredSegment _⟩

/-- **No universal GHP limit.** No single measured space is the GHP limit in probability
of the uniformly measured trees for every array satisfying the hypotheses of
`thm:alpha0`. -/
theorem bounded_population_no_universal_GHP_limit :
    ¬ ∃ L : MeasuredGHSpace.{0}, ∀ x : ℕ → ℕ → ℤ,
      (∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n) →
      (∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M) →
      ∀ ε > 0, Tendsto (fun n ↦ (freezingTreeLaw x n).real {s | ε < dist
        (toMeasuredGHSpace (forwardMeasuredSpace
          (1 / Freezing1.heightScale (companionSchedule (x n)) n) s)) L}) atTop (𝓝 0) := by
  rintro ⟨L, hL⟩
  have hx := dist_eq_zero_of_tendsto_far (fun _ hε ↦ alternatingArray_GHP_limit hε)
    (hL alternatingArray alternatingArray_admissible ⟨3, alternatingArray_bounded⟩)
  have hy := dist_eq_zero_of_tendsto_far (fun _ hε ↦ switchedArray_GHP_limit hε)
    (hL switchedArray switchedArray_admissible ⟨3, switchedArray_bounded⟩)
  have h := dist_triangle_right (toMeasuredGHSpace (measuredSegment alternatingProfile))
    (toMeasuredGHSpace (measuredSegment switchedProfile)) L
  have hpos := measuredSegment_alternating_switched_dist_pos
  linarith
end Freezing2
