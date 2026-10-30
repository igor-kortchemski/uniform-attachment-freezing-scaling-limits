module

public import Freezing2.Probability.ForestGeometry
public import Freezing2.Probability.CoalescenceHistory
public import Freezing2.Probability.ReverseHeightConcentration
public import Freezing2.Analysis.SourceHypotheses

/-!
# Uniform approximation of the actual reverse-tree distances

The graph distance is the sum of the two heights at their first common
component. This includes the diagonal, where both heights at birth are zero.
The source's inclusive harmonic expression is retained literally, even on
the diagonal; it is an approximation and is not asserted to be a metric.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- Lifting a walk to the induced graph preserves its length. -/
theorem walk_induce_length {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (s : Set V) : ∀ hp, (p.induce s hp).length = p.length := by
  induction p with
  | nil => intro hp; rfl
  | cons h p ih =>
    intro hp
    simp only [SimpleGraph.Walk.induce_cons, SimpleGraph.Walk.length_cons]
    exact congrArg Nat.succ (ih _)

/-- Restricting a forest to its actual finite vertex set preserves distances;
the ambient countable label type does not change the metric being studied. -/
theorem forest_toGraph_dist_eq {V : Type*} [DecidableEq V] (F : Freezing1.RootedForest V)
    (u v : {w // w ∈ F.vertices}) : F.toGraph.dist u v = F.graph.dist u.val v.val := by
  let e : F.toGraph →g F.graph := ⟨Subtype.val, fun {_ _} h ↦ h⟩
  by_cases h : F.graph.Reachable u.val v.val
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    let q : F.toGraph.Walk u v := p.induce (F.vertices : Set V) (F.walk_support_mem p u.property)
    have hq : q.length = p.length := by
      exact walk_induce_length p _ _
    apply le_antisymm
    · exact (F.toGraph.dist_le q).trans_eq (hq.trans hp)
    · obtain ⟨r, hr⟩ := q.reachable.exists_walk_length_eq_dist
      have hdist := F.graph.dist_le (r.map e)
      rw [SimpleGraph.Walk.length_map, hr] at hdist
      rw [show e u = u.val from rfl, show e v = v.val from rfl] at hdist
      exact hdist
  · have hn : ¬F.toGraph.Reachable u v := by
      rintro ⟨p⟩
      exact h ⟨p.map e⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hn,
      SimpleGraph.dist_eq_zero_of_not_reachable h]

/-- The first merger and subsequent acyclic growth give the exact distance
identity used in the source proof of N07. -/
theorem jointLaw_distance_eq_heights_at_coalescence
    {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n,
      (forestAt n 0 ω).graph.dist u v =
        (forestAt n (coalescenceTime n u v ω) ω).depth u +
        (forestAt n (coalescenceTime n u v ω) ω).depth v := by
  by_cases huv : u = v
  · subst v
    filter_upwards [jointLaw_depth_at_birth_zero hn hu] with ω hω
    simp only [coalescenceTime_self, hω, zero_add, SimpleGraph.dist_self]
  · filter_upwards [jointLaw_coalescenceTime_lt_commonBirth hn hu hv huv,
      jointLaw_coalescenceTime_eq_iff hn hu hv, jointLaw_members hn hu hv,
      ForestGeometry.jointLaw_new_connection_distance x n hn,
      ForestGeometry.jointLaw_dist_preserved x n hn] with ω hlt hfirst hmem hnew hdist
    let c := coalescenceTime n u v ω
    have hcb : c < commonBirth n u v := hlt
    have hcn : c < n := hcb.trans_le (commonBirth_le_horizon hu)
    have hc := (hfirst c hcb).mp rfl
    have hmem1 := hmem (c + 1) (by omega)
    have hindex : n - (c + 1) + 1 = n - c := by omega
    have hjoin := hnew (n - (c + 1)) (by omega)
    rw [hindex] at hjoin
    have heq : (forestAt n c ω).graph.dist u v =
        (forestAt n c ω).depth u + (forestAt n c ω).depth v :=
      hjoin u hmem1.1 v hmem1.2 hc.2 hc.1
    have hmemc := hmem c hcb.le
    have hreach : (forestAt n c ω).graph.Reachable u v :=
      (ForestCoalescence.root_eq_iff_reachable _ hmemc.1 hmemc.2).mp hc.1
    have hkeep := hdist (n - c) n (Nat.sub_le _ _) le_rfl u v hreach
    simpa only [forestAt, Nat.sub_zero] using hkeep.trans heq

/-- Actual graph distance, using the source's one-based vertex labels. -/
noncomputable def reverseDistance (n : ℕ) (u v : VertexLabel) (ω : History) : ℝ :=
  ((forestAt n 0 ω).graph.dist (toCompanionLabel u) (toCompanionLabel v) : ℝ)

/-- The source's inclusive harmonic comparison function, including its
nonzero diagonal. -/
noncomputable def coalescenceHarmonicDistance (x : ℕ → ℤ) (n : ℕ)
    (u v : VertexLabel) (ω : History) : ℝ :=
  inclusiveHarmonic x (sourceCoalescenceTime n u v ω) (birthTime n u) / 2 +
    inclusiveHarmonic x (sourceCoalescenceTime n u v ω) (birthTime n v) / 2

theorem sourceCoalescenceTime_le_birth_left (n : ℕ) (u v : VertexLabel) (ω : History) :
    sourceCoalescenceTime n u v ω ≤ birthTime n u := by
  simpa only [companion_birthTime, sourceCoalescenceTime] using
    (coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω).trans
      (min_le_left _ _)

theorem sourceCoalescenceTime_le_birth_right (n : ℕ) (u v : VertexLabel) (ω : History) :
    sourceCoalescenceTime n u v ω ≤ birthTime n v := by
  simpa only [companion_birthTime, sourceCoalescenceTime] using
    (coalescenceTime_le_commonBirth n (toCompanionLabel u) (toCompanionLabel v) ω).trans
      (min_le_right _ _)

/-- Each pairwise distance error is bounded by two actual height errors. -/
theorem jointLaw_distance_error_le_height_error
    (x : ℕ → ℕ → ℤ) (n : ℕ) (hx : IsSigned (x n))
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule (x n)))
    {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n) :
    ∀ᵐ ω ∂jointLaw (companionSchedule (x n)) n,
      |reverseDistance n u v ω - coalescenceHarmonicDistance (x n) n u v ω| ≤
        2 * reverseHeightErrorMax x n ω := by
  filter_upwards [jointLaw_distance_eq_heights_at_coalescence hn
    (toCompanionLabel_mem (x n) hx hu) (toCompanionLabel_mem (x n) hx hv)] with ω hω
  have hd : reverseDistance n u v ω =
      heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel u) ω +
      heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel v) ω := by
    unfold reverseDistance heightAt sourceCoalescenceTime
    exact_mod_cast hω
  have h1 := height_error_le_reverseHeightErrorMax x n _ hu
    (sourceCoalescenceTime_le_birth_left n u v ω) ω
  have h2 := height_error_le_reverseHeightErrorMax x n _ hv
    (sourceCoalescenceTime_le_birth_right n u v ω) ω
  rw [hd, coalescenceHarmonicDistance]
  have hab := abs_add_le
    (heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel u) ω -
      inclusiveHarmonic (x n) (sourceCoalescenceTime n u v ω) (birthTime n u) / 2)
    (heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel v) ω -
      inclusiveHarmonic (x n) (sourceCoalescenceTime n u v ω) (birthTime n v) / 2)
  convert hab.trans (show _ ≤ 2 * reverseHeightErrorMax x n ω by linarith) using 1
  ring_nf

/-- The finite maximum in N07, taken over every ordered pair of legal labels. -/
noncomputable def reverseDistanceErrorMax (x : ℕ → ℕ → ℤ) (n : ℕ) (ω : History) : ℝ :=
  finiteHeightDeviationMax
    (fun p : {v // v ∈ vertexLabels (x n) n} × {v // v ∈ vertexLabels (x n) n} ↦
      fun ω ↦ reverseDistance n p.1.val p.2.val ω -
        coalescenceHarmonicDistance (x n) n p.1.val p.2.val ω)
    (fun _ ↦ 0) ω

/-- Every legal pair's error is bounded by the finite all-pairs maximum. -/
theorem distance_error_le_reverseDistanceErrorMax (x : ℕ → ℕ → ℤ) (n : ℕ)
    {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n) (hv : v ∈ vertexLabels (x n) n)
    (ω : History) :
    |reverseDistance n u v ω - coalescenceHarmonicDistance (x n) n u v ω| ≤
      reverseDistanceErrorMax x n ω := by
  unfold reverseDistanceErrorMax finiteHeightDeviationMax
  rw [Finset.le_sup'_iff]
  refine ⟨some (⟨u, hu⟩, ⟨v, hv⟩), Finset.mem_univ _, ?_⟩
  simp only [sub_zero, le_refl]

theorem measurable_reverseDistance (n : ℕ) (u v : VertexLabel) :
    Measurable (reverseDistance n u v) := by
  exact (show Measurable (fun F : Forest ↦
    (F.graph.dist (toCompanionLabel u) (toCompanionLabel v) : ℝ)) from
      measurable_from_top).comp (measurable_pi_apply (n - 0))

theorem measurable_coalescenceHarmonicDistance (x : ℕ → ℤ) (n : ℕ)
    (u v : VertexLabel) : Measurable (coalescenceHarmonicDistance x n u v) := by
  exact (show Measurable (fun c : ℕ ↦ inclusiveHarmonic x c (birthTime n u) / 2 +
    inclusiveHarmonic x c (birthTime n v) / 2) from measurable_from_top).comp
      (measurable_sourceCoalescenceTime n u v)

theorem measurable_reverseDistanceErrorMax (x : ℕ → ℕ → ℤ) (n : ℕ) :
    Measurable (reverseDistanceErrorMax x n) := by
  let κ := {v // v ∈ vertexLabels (x n) n} × {v // v ∈ vertexLabels (x n) n}
  let f : Option κ → History → ℝ := fun p ω ↦ match p with
    | none => 0
    | some p => |reverseDistance n p.1.val p.2.val ω -
        coalescenceHarmonicDistance (x n) n p.1.val p.2.val ω|
  have hf : Measurable ((Finset.univ : Finset (Option κ)).sup' Finset.univ_nonempty f) := by
    apply Finset.measurable_sup'
    intro p _
    cases p with
    | none => exact measurable_const
    | some p => simpa only [f, Real.norm_eq_abs, Pi.sub_apply] using
        ((measurable_reverseDistance n p.1.val p.2.val).sub
          (measurable_coalescenceHarmonicDistance (x n) n p.1.val p.2.val)).norm
  convert hf using 1
  funext ω
  rw [Finset.sup'_apply]
  unfold reverseDistanceErrorMax finiteHeightDeviationMax
  congr 1
  funext p
  cases p <;> simp [f]

theorem lt_reverseDistanceErrorMax_iff (x : ℕ → ℕ → ℤ) (n : ℕ) (ω : History)
    {t : ℝ} (ht : 0 ≤ t) :
    t < reverseDistanceErrorMax x n ω ↔
      ∃ u ∈ vertexLabels (x n) n, ∃ v ∈ vertexLabels (x n) n,
        t < |reverseDistance n u v ω - coalescenceHarmonicDistance (x n) n u v ω| := by
  rw [reverseDistanceErrorMax, lt_finiteHeightDeviationMax_iff _ _ _ ht]
  simp only [sub_zero]
  constructor
  · rintro ⟨⟨u, v⟩, h⟩
    exact ⟨u, u.property, v, v.property, h⟩
  · rintro ⟨u, hu, v, hv, h⟩
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), h⟩

/-- The paper's maximum inequality holds almost surely, with birth endpoints
included so that the diagonal and the first frozen vertex are covered. -/
theorem jointLaw_distanceErrorMax_le (x : ℕ → ℕ → ℤ) (n : ℕ)
    (hx : IsSigned (x n))
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule (x n))) :
    ∀ᵐ ω ∂jointLaw (companionSchedule (x n)) n,
      reverseDistanceErrorMax x n ω ≤ 2 * reverseHeightErrorMax x n ω := by
  have hp (p : {v // v ∈ vertexLabels (x n) n} × {v // v ∈ vertexLabels (x n) n}) :=
    jointLaw_distance_error_le_height_error x n hx hn p.1.property p.2.property
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  unfold reverseDistanceErrorMax finiteHeightDeviationMax
  rw [Finset.sup'_le_iff]
  intro p _
  cases p with
  | none => exact mul_nonneg (by norm_num) (reverseHeightErrorMax_nonneg x n ω)
  | some p => simpa only [sub_zero] using hω p

/-- N07 (`height=ok`): the actual reverse-tree graph distances are uniformly
approximated by the source's inclusive harmonic coalescence formula. The
local square-profile assumption is unnecessary for this particular result. -/
theorem tendsto_reverseDistanceErrorMax
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα0 : 0 < α) (hα1 : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      (jointLaw (companionSchedule (x n)) n).real
        {ω | ε * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω})
      atTop (𝓝 0) := by
  have ht := tendsto_reverseHeightErrorMax hx hα0 hα1 hL1 hpos (half_pos hε)
  apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ ht
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [jointLaw_distanceErrorMax_le x n (hx n).1
    (companion_before_extinction (x n) (hx n).1 (hx n).2).le] with ω hω
  intro h
  change ε * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω at h
  change ε / 2 * (n : ℝ) ^ (1 - α) < reverseHeightErrorMax x n ω
  nlinarith

/-- The original positive-horizon source statement, with no extra assumption
on an unused row at zero. -/
theorem tendsto_reverseDistanceErrorMax_positive_horizons
    {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (jointLaw (companionSchedule (x n)) n).real
      {ω | ε * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax x n ω}) atTop (𝓝 0) := by
  apply (tendsto_reverseDistanceErrorMax (admissible_initialRowExtension hx)
    hα0 hα1 (hasL1ReciprocalProfile_initialRowExtension hL1)
    (positiveProfile_reciprocal hf) hε).congr'
  filter_upwards [initialRowExtension_eventually_eq x] with n hn
  exact congrArg (fun row : ℕ → ℤ ↦ (jointLaw (companionSchedule row) n).real
    {ω | ε * (n : ℝ) ^ (1 - α) < reverseDistanceErrorMax (fun _ ↦ row) n ω}) hn

end Freezing2
