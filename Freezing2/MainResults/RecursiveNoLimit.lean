module

public import Freezing2.MainResults.RecursiveTrees
public import Freezing2.Probability.UniformHeightConcentration
public import Freezing2.Probability.PointMassLimit

/-!
# Uniform recursive trees have no nondegenerate GHP scaling limit

The Introduction of the source (line 280, inventory row U04b) asserts that recursive trees
without freezing have no scaling limits for the Gromov–Hausdorff–Prokhorov topology. Source
issue S19 notes that the literal claim needs qualifying: the diameter after `n` steps is
at most twice the height, hence at most `2n`, so sufficiently strong shrinking collapses the
tree to a point. This file proves the
qualified statement for the uniform recursive tree `urtLaw n` (the all-`+1` forward law, see
`treeLaw_allPlus_eq_urtLaw`), equipped with the uniform probability on its vertices and its
graph distance divided by a positive scale `a n` (`urtMeasuredLaw (a n) n`).

* **Collapse** (`tendsto_urtMeasuredLaw_onePoint`). If `a n / log n → ∞`, the scaled trees
  converge to the one-point space. The height is at most `(e + 1) h_n⁺ ≤ (e + 1) log (n + 1)`
  with probability tending to one (companion Theorem `thm:height` II), and a measured space of
  diameter `D` is within GHP distance `D` of the point.
* **Two-point estimate** (`tendsto_urt_sampled_close_probability`). Two iid uniform vertices
  are at distance more than `log n / 4` with probability tending to one. In the reverse
  construction every vertex is born at the horizon, two distinct vertices merge after phase
  `i` with probability at most `2/(i+1)`, and before the merger the first vertex accumulates
  a sum of independent Bernoulli increments of mean `h_n⁺ - h_i⁺ ≥ log n - O_i(1)`, which is
  at least half its mean except with exponentially small probability (Bennett).
* **Covering numbers blow up at logarithmic scales** (`urt_not_coverable_of_le_log`). The
  annealed sampled distances of the scaled tree are transported to the reverse construction
  (`annealedDistanceLaw_urtMeasuredLaw`), and the separated-matrices argument of
  `SupercriticalNonTight.lean` applies with radius `1 / (8 C)` whenever `a n ≤ C log n`.
* **Main statements.** At the natural scale `a n = log n` the laws are not tight
  (`urt_log_not_tight`) and no subsequence converges (`urt_log_no_weak_limit`). For every
  sequence of eventually positive scales, any weak limit of the laws is the Dirac mass at the
  one-point space (`urt_weak_limit_eq_onePoint`), and a weak limit exists exactly when
  `a n / log n → ∞` (`urt_tendsto_iff`).
-/

@[expose] public section

open Filter MeasureTheory Set Topology ProbabilityTheory

namespace Freezing2

open ReverseHistory ReverseCoalescence MeasuredGHSpace GHCovering

/-! ### The all-`+1` schedule -/

/-- Under the all-`true` companion schedule, `n + 1` vertices are active after `n` steps. -/
theorem allTrue_activeCount (n : ℕ) :
    Freezing1.activeCount (fun _ ↦ true) n = n + 1 := by
  simp [Freezing1.activeCount, add_comm]

/-- The all-`true` companion schedule never goes extinct. -/
theorem allTrue_lt_extinctionTime (n : ℕ) :
    (n : ℕ∞) < Freezing1.extinctionTime (fun _ ↦ true) := by
  rw [Freezing1.lt_extinctionTime_iff]
  intro k _
  rw [allTrue_activeCount]
  omega

/-- Upper harmonic bound: `h_n⁺ = 1/2 + ... + 1/(n+1) ≤ log (n + 1)` without freezing. -/
theorem allTrue_heightScale_le_log (n : ℕ) :
    Freezing1.heightScale (fun _ ↦ true) n ≤ Real.log ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Freezing1.heightScale_succ, allTrue_activeCount]
    simp only [↓reduceIte]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hn' : 0 < (n : ℝ) + 2 := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hn' hn)
    rw [Real.log_div hn'.ne' hn.ne', inv_div] at hlog
    have hr : 1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) = 1 / ((n : ℝ) + 2) := by
      field_simp
      ring
    push_cast
    rw [hr] at hlog
    have heq : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [heq]
    linarith

/-- `log (n + 1) ≤ 2 log n` for `n ≥ 2`. -/
theorem log_succ_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.log_rpow (by positivity), show ((n : ℝ) ^ (2 : ℝ)) = (n : ℝ) ^ (2 : ℕ) by
    exact_mod_cast Real.rpow_natCast (n : ℝ) 2]
  apply Real.log_le_log (by positivity)
  nlinarith

/-- The integer sign sequence of the uniform recursive tree: every step attaches. -/
def urtSigns : ℕ → ℤ := fun _ ↦ 1

/-- The all-`+1` sequence is a sign sequence. -/
theorem urtSigns_isSigned : IsSigned urtSigns := fun _ _ ↦ Or.inl rfl

/-- Without freezing, the population after `n` steps is `n + 1`. -/
theorem urtSigns_activeCount (n : ℕ) : activeCount urtSigns n = n + 1 := by
  simp [activeCount, urtSigns, add_comm]

/-- The all-`+1` sequence survives through every horizon. -/
theorem urtSigns_survives (n : ℕ) : SurvivesThrough urtSigns n := by
  intro k _
  rw [urtSigns_activeCount]
  omega

/-- The Boolean encoding of the all-`+1` sequence is the all-`true` schedule. -/
theorem companionSchedule_urtSigns : companionSchedule urtSigns = fun _ ↦ true := by
  funext i
  simp [companionSchedule, urtSigns]

/-- Every horizon precedes extinction for the all-`+1` sequence. -/
theorem urtSigns_horizon (n : ℕ) :
    (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule urtSigns) :=
  (companion_before_extinction urtSigns urtSigns_isSigned (urtSigns_survives n)).le

/-- Without freezing, every label is active at the horizon, hence born at the horizon. -/
theorem urtSigns_birthTime {n : ℕ} {u : VertexLabel} (hu : u ∈ vertexLabels urtSigns n) :
    birthTime n u = n := by
  cases u with
  | inl i =>
    simp [vertexLabels, downSteps, urtSigns] at hu
  | inr j => rfl

/-- The uniform recursive tree after `n` steps has `n + 1` vertex labels. -/
theorem urtSigns_vertexLabels_card (n : ℕ) : (vertexLabels urtSigns n).card = n + 1 := by
  have hd : downSteps urtSigns 0 n = ∅ := by
    ext i
    simp [downSteps, urtSigns]
  simp [vertexLabels, hd, urtSigns_activeCount]

/-- The merger hazards of the uniform recursive tree telescope. -/
theorem urtSigns_coalescenceUpSum (i m : ℕ) :
    coalescenceUpSum urtSigns i m = 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + m + 1) := by
  induction m with
  | zero => simp [coalescenceUpSum]
  | succ m ih =>
    rw [coalescenceUpSum, Finset.sum_range_succ, ← coalescenceUpSum, ih]
    simp only [urtSigns, ↓reduceIte, urtSigns_activeCount]
    push_cast
    have hy : (0 : ℝ) < (i : ℝ) + m + 1 := by positivity
    have hy1 : (0 : ℝ) < (i : ℝ) + m + 1 + 1 := by positivity
    rw [show (i : ℝ) + m + 1 + 1 - 1 = (i : ℝ) + m + 1 by ring,
      show (i : ℝ) + (m + 1) + 1 = (i : ℝ) + m + 1 + 1 by ring]
    field_simp
    ring

/-- Two distinct vertices merge after phase `i` with total hazard at most `1/(i+1)`. -/
theorem urtSigns_coalescenceUpSum_le (i m : ℕ) :
    coalescenceUpSum urtSigns i m ≤ 1 / ((i : ℝ) + 1) := by
  rw [urtSigns_coalescenceUpSum]
  have : 0 < 1 / ((i : ℝ) + m + 1) := by positivity
  linarith

/-- The triangular array whose rows are all `+1`. -/
def urtArray : ℕ → ℕ → ℤ := fun _ ↦ urtSigns

/-- Every row of `urtArray` is a sign sequence. -/
theorem urtArray_isSigned (n : ℕ) : IsSigned (urtArray n) := urtSigns_isSigned

/-- Every row of `urtArray` survives through its horizon. -/
theorem urtArray_survives (n : ℕ) : SurvivesThrough (urtArray n) n := urtSigns_survives n

/-- The forward tree law of the all-`+1` array is the uniform recursive tree law. -/
theorem freezingTreeLaw_urtArray (n : ℕ) : freezingTreeLaw urtArray n = urtLaw n := by
  rw [freezingTreeLaw, urtArray, companionSchedule_urtSigns, treeLaw_allPlus_eq_urtLaw]

/-! ### The scaled measured uniform recursive trees -/

/-- The uniform recursive tree after `n` steps, with graph distances divided by `a` and the
uniform probability on its `n + 1` vertices, as a random GHP isometry class. -/
noncomputable def urtMeasuredLaw (a : ℝ) (n : ℕ) : ProbabilityMeasure MeasuredGHSpace.{0} :=
  ProbabilityMeasure.map
    (⟨urtLaw n, inferInstance⟩ : ProbabilityMeasure Freezing1.Forward.State)
    (fun s ↦ toMeasuredGHSpace (forwardMeasuredSpace (1 / a) s))

/-- The GHP class of the one-point space with its unique probability measure. -/
noncomputable def onePointGHSpace : MeasuredGHSpace.{0} :=
  toMeasuredGHSpace singletonMeasuredSpace

/-- The Dirac mass at the one-point space. -/
noncomputable def onePointLaw : ProbabilityMeasure MeasuredGHSpace.{0} :=
  ⟨Measure.dirac onePointGHSpace, inferInstance⟩

/-! ### Collapse under strong shrinking -/

/-- A compact measured space of diameter at most `D` is within GHP distance `D` of the
one-point space: map everything to the point. -/
theorem distance_singletonMeasuredSpace_le (X : CompactMeasuredSpace.{0}) {D : ℝ}
    (hD : ∀ x y : X, dist x y ≤ D) :
    CompactMeasuredSpace.distance X singletonMeasuredSpace ≤ D := by
  obtain ⟨x0⟩ := X.nonempty
  let y0 : singletonMeasuredSpace := ()
  have hD0 : 0 ≤ D := by simpa using hD x0 x0
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hδ : 0 < (D + ε / 2) / 2 := by positivity
  have hmap : (X.law : Measure X).map (fun _ ↦ y0) =
      (singletonMeasuredSpace.law : Measure singletonMeasuredSpace) := by
    rw [Measure.map_const, measure_univ, one_smul]
    rfl
  have h := ghpDistance_le_of_approx (X.law : Measure X)
    (singletonMeasuredSpace.law : Measure singletonMeasuredSpace)
    (fun _ ↦ y0) measurable_const hδ (r := 0) (p := 0)
    (fun x x' ↦ by
      have hxx := hD x x'
      have hnn := dist_nonneg (x := x) (y := x')
      rw [dist_self, sub_zero, abs_of_nonneg hnn]
      linarith)
    (fun y ↦ ⟨x0, by rw [show y = y0 from rfl, dist_self]⟩)
    (by rw [hmap, levyProkhorovDist_self])
  change ghpDistance _ _ < _
  linarith

/-- The diameter of a forward tree is at most twice its height. -/
theorem forward_tree_dist_le_two_mul_treeHeight {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) (u v : {v // v ∈ s.vertices}) :
    s.tree.dist u v ≤ 2 * Freezing1.Forward.treeHeight s := by
  let r : {v // v ∈ s.vertices} := ⟨0, hs.root_mem⟩
  have h := hs.tree_connected.dist_triangle (u := u) (v := r) (w := v)
  have h2 : s.tree.dist u r = s.tree.dist r u := SimpleGraph.dist_comm
  have hu : s.tree.dist r u ≤ Freezing1.Forward.treeHeight s := by
    rw [← hs.height_eq_tree_dist u]
    exact Freezing1.Forward.height_le_treeHeight u.2
  have hv : s.tree.dist r v ≤ Freezing1.Forward.treeHeight s := by
    rw [← hs.height_eq_tree_dist v]
    exact Freezing1.Forward.height_le_treeHeight v.2
  omega

/-- A scaled forward measured tree is within GHP distance `c · 2 · height` of the point. -/
theorem forwardMeasuredSpace_distance_singleton_le {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {c : ℝ} (hc : 0 < c) :
    CompactMeasuredSpace.distance (forwardMeasuredSpace c s) singletonMeasuredSpace ≤
      c * (2 * (Freezing1.Forward.treeHeight s : ℝ)) := by
  have hconn := hs.tree_connected
  rw [forwardMeasuredSpace, dite_eq_left (show s.tree.Connected ∧ 0 < c from ⟨hconn, hc⟩)]
  apply distance_singletonMeasuredSpace_le
  intro u v
  let := scaledGraphMetric s.tree hconn c hc
  let u' : {v // v ∈ s.vertices} := u
  let v' : {v // v ∈ s.vertices} := v
  change c * (s.tree.dist u' v' : ℝ) ≤ _
  have hsum : (s.tree.dist u' v' : ℝ) ≤ 2 * (Freezing1.Forward.treeHeight s : ℝ) := by
    exact_mod_cast forward_tree_dist_le_two_mul_treeHeight hs u' v'
  exact mul_le_mul_of_nonneg_left hsum hc.le

/-- **Collapse under strong shrinking.** If `a n / log n → ∞`, the scaled uniform recursive
trees converge to the one-point space, because their height is at most `(e + 1) log (n + 1)`
with probability tending to one. -/
theorem tendsto_urtMeasuredLaw_onePoint {a : ℕ → ℝ}
    (hscale : Tendsto (fun n ↦ a n / Real.log n) atTop atTop) :
    Tendsto (fun n ↦ urtMeasuredLaw (a n) n) atTop (𝓝 onePointLaw) := by
  apply tendsto_probabilityMap_const_of_tail
    (μ := fun n ↦ (⟨urtLaw n, inferInstance⟩ : ProbabilityMeasure Freezing1.Forward.State))
    (F := fun n s ↦ toMeasuredGHSpace (forwardMeasuredSpace (1 / a n) s))
    (fun _ ↦ measurable_from_top) onePointGHSpace
  intro ε hε
  set e1 : ℝ := Real.exp 1 + 1
  have he1 : 0 < e1 := by positivity
  have hheight := Freezing1.maximum_height_universal_upper_tendsto_zero (fun _ _ ↦ true)
    (fun n ↦ allTrue_lt_extinctionTime n) one_pos
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hheight
  filter_upwards [eventually_ge_atTop 2,
    hscale.eventually_gt_atTop (4 * e1 / ε)] with n hn hlarge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ha : 0 < a n := by
    have h0 : 0 < a n / Real.log n := lt_trans (by positivity) hlarge
    exact (div_pos_iff_of_pos_right hlog).mp h0
  have hsmall : 4 * e1 * Real.log n < ε * a n := by
    rw [div_lt_div_iff₀ hε hlog] at hlarge
    linarith
  have hpos : 0 < Freezing1.heightScale (fun _ ↦ true) n :=
    Freezing1.heightScale_pos (by omega) ((Freezing1.lt_extinctionTime_iff _ _).mp
      (allTrue_lt_extinctionTime n))
  have hscale_le := (allTrue_heightScale_le_log n).trans (log_succ_le_two_mul_log hn)
  change (urtLaw n).real _ ≤ (Freezing1.Forward.treeLaw (fun _ ↦ true) n).real _
  rw [← treeLaw_allPlus_eq_urtLaw]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [Freezing1.Forward.treeLaw_valid (fun _ ↦ true) n] with s hs hεs
  change ε < dist (toMeasuredGHSpace (forwardMeasuredSpace (1 / a n) s)) onePointGHSpace at hεs
  change Real.exp 1 + 1 < (Freezing1.Forward.treeHeight s : ℝ) /
    Freezing1.heightScale (fun _ ↦ true) n
  by_contra hle
  rw [not_lt, div_le_iff₀ hpos] at hle
  rw [onePointGHSpace, MeasuredGHSpace.dist_toMeasuredGHSpace] at hεs
  have hd := forwardMeasuredSpace_distance_singleton_le hs (one_div_pos.mpr ha)
  have hH : (Freezing1.Forward.treeHeight s : ℝ) ≤ e1 * (2 * Real.log n) :=
    hle.trans (mul_le_mul_of_nonneg_left hscale_le he1.le)
  have hbound : 1 / a n * (2 * (Freezing1.Forward.treeHeight s : ℝ)) < ε := by
    rw [one_div_mul_eq_div, div_lt_iff₀ ha]
    linarith
  linarith

/-! ### Two iid uniform vertices are logarithmically far apart -/

/-- Reverse heights decrease as the phase increases from zero to the birth time. -/
theorem jointLaw_heightAt_antitone {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {v : ℕ ⊕ ℕ}
    (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ c i, c ≤ i → i ≤ Freezing1.birthTime n v →
      heightAt n i v ω ≤ heightAt n c v ω := by
  have hstep (k : ℕ) : ∀ᵐ ω ∂jointLaw x n, k + 1 ≤ Freezing1.birthTime n v →
      heightAt n (k + 1) v ω ≤ heightAt n k v ω := by
    by_cases hk : k + 1 ≤ Freezing1.birthTime n v
    · filter_upwards [heightIncrementVariable_eq_sub hn (Nat.le_add_left 1 k) hv hk] with ω hω _
      have h0 : 0 ≤ heightIncrementVariable n v (n - (k + 1)) ω := by
        unfold heightIncrementVariable
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
      rw [hω, Nat.add_sub_cancel] at h0
      linarith
    · exact Eventually.of_forall fun _ h ↦ absurd h hk
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  intro c i hci hib
  induction i, hci using Nat.le_induction with
  | base => exact le_rfl
  | succ i hci ih => exact (hω i hib).trans (ih (by omega))

/-- The mean depth accumulated by a vertex of the reverse uniform recursive tree between
phase `i` and the horizon `n`: the harmonic increment `1/(i+2) + ... + 1/(n+1)`. -/
noncomputable def urtHeightMean (n i : ℕ) : ℝ :=
  Freezing1.heightScale (fun _ ↦ true) n - Freezing1.heightScale (fun _ ↦ true) i

/-- The harmonic increment grows like `log n`, up to a constant depending on `i`. -/
theorem log_sub_le_urtHeightMean {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    Real.log n - (Real.log 4 + Real.log ((i : ℝ) + 1)) ≤ urtHeightMean n i := by
  have hpos : Freezing1.PositiveThrough (fun _ ↦ true) n :=
    (Freezing1.lt_extinctionTime_iff _ _).mp (allTrue_lt_extinctionTime n)
  have hlow := Freezing1.log_quarter_le_heightScale hn hpos
  rw [Real.log_div (by positivity) (by norm_num)] at hlow
  have hup := allTrue_heightScale_le_log i
  rw [urtHeightMean]
  linarith

/-- Two distinct vertices are close only if they merge late, or if one of them accumulates
little depth after the merger phase `i`. -/
theorem urt_pair_distance_le_probability {n i : ℕ} (hi : i ≤ n) {u v : VertexLabel}
    (hu : u ∈ vertexLabels urtSigns n) (hv : v ∈ vertexLabels urtSigns n) (huv : u ≠ v)
    (t : ℝ) :
    (jointLaw (companionSchedule urtSigns) n).real {ω | reverseDistance n u v ω ≤ t} ≤
      2 / ((i : ℝ) + 1) + (jointLaw (companionSchedule urtSigns) n).real
        {ω | heightAt n i (toCompanionLabel u) ω ≤ t} := by
  let μ := jointLaw (companionSchedule urtSigns) n
  have hn := urtSigns_horizon n
  have hu' := toCompanionLabel_mem urtSigns urtSigns_isSigned hu
  have hv' := toCompanionLabel_mem urtSigns urtSigns_isSigned hv
  have hbu : Freezing1.birthTime n (toCompanionLabel u) = n :=
    (companion_birthTime n u).trans (urtSigns_birthTime hu)
  have hmin : i ≤ min (birthTime n u) (birthTime n v) := by
    rw [urtSigns_birthTime hu, urtSigns_birthTime hv, min_self]
    exact hi
  have hcoal := source_coalescence_ge_probability_le_sum urtSigns urtSigns_isSigned
    (urtSigns_survives n) hu hv huv hmin
  have hsum := urtSigns_coalescenceUpSum_le i (min (birthTime n u) (birthTime n v) - i)
  have hsub : {ω | reverseDistance n u v ω ≤ t} ≤ᵐ[μ]
      {ω | i ≤ sourceCoalescenceTime n u v ω} ∪
        {ω | heightAt n i (toCompanionLabel u) ω ≤ t} := by
    filter_upwards [jointLaw_distance_eq_heights_at_coalescence hn hu' hv',
      jointLaw_heightAt_antitone hn hu'] with ω hdist hmono hle
    change reverseDistance n u v ω ≤ t at hle
    by_cases hc : i ≤ sourceCoalescenceTime n u v ω
    · exact Or.inl hc
    · right
      change heightAt n i (toCompanionLabel u) ω ≤ t
      have hci : sourceCoalescenceTime n u v ω ≤ i := (not_le.mp hc).le
      have hm := hmono (sourceCoalescenceTime n u v ω) i hci (hbu.symm ▸ hi)
      have hd : reverseDistance n u v ω =
          heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel u) ω +
            heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel v) ω := by
        unfold reverseDistance heightAt sourceCoalescenceTime
        exact_mod_cast hdist
      have hv0 : 0 ≤ heightAt n (sourceCoalescenceTime n u v ω) (toCompanionLabel v) ω :=
        Nat.cast_nonneg _
      linarith
  calc
    μ.real {ω | reverseDistance n u v ω ≤ t} ≤
        μ.real ({ω | i ≤ sourceCoalescenceTime n u v ω} ∪
          {ω | heightAt n i (toCompanionLabel u) ω ≤ t}) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ μ.real {ω | i ≤ sourceCoalescenceTime n u v ω} +
          μ.real {ω | heightAt n i (toCompanionLabel u) ω ≤ t} := measureReal_union_le _ _
    _ ≤ _ := by
      gcongr
      calc
        _ ≤ 2 * coalescenceUpSum urtSigns i (min (birthTime n u) (birthTime n v) - i) := hcoal
        _ ≤ 2 * (1 / ((i : ℝ) + 1)) := by linarith
        _ = 2 / ((i : ℝ) + 1) := by ring

/-- The Bernoulli parameters of a reverse height of the uniform recursive tree sum to the
harmonic increment `urtHeightMean`. -/
theorem urt_sum_heightBernoulliParameter {n i : ℕ} (hi : i ≤ n) {u : VertexLabel}
    (hu : u ∈ vertexLabels urtSigns n) :
    (∑ j, (heightBernoulliParameter (companionSchedule urtSigns) n i
      (toCompanionLabel u) j : ℝ)) = urtHeightMean n i := by
  have hu' := toCompanionLabel_mem urtSigns urtSigns_isSigned hu
  have hbu : Freezing1.birthTime n (toCompanionLabel u) = n :=
    (companion_birthTime n u).trans (urtSigns_birthTime hu)
  rw [sum_heightBernoulliParameter (urtSigns_horizon n) hu', hbu, companionSchedule_urtSigns,
    urtHeightMean, Freezing1.heightScale, Freezing1.heightScale,
    show n = i + (n - i) from (Nat.add_sub_cancel' hi).symm, Finset.sum_range_add,
    Nat.add_sub_cancel_left]
  simp only [add_assoc]
  ring

/-- **Depth lower tail.** A reverse height of the uniform recursive tree is at least half its
mean, except with exponentially small probability in the mean. -/
theorem urt_heightAt_lower_tail {n i : ℕ} (hi : i ≤ n) {u : VertexLabel}
    (hu : u ∈ vertexLabels urtSigns n) {t : ℝ} (hm : 0 < urtHeightMean n i)
    (ht : t < urtHeightMean n i / 2) :
    (jointLaw (companionSchedule urtSigns) n).real
        {ω | heightAt n i (toCompanionLabel u) ω ≤ t} ≤
      2 * Real.exp (-(urtHeightMean n i * bennettFunction (1 / 2))) := by
  have hn := urtSigns_horizon n
  have hu' := toCompanionLabel_mem urtSigns urtSigns_isSigned hu
  have hbu : Freezing1.birthTime n (toCompanionLabel u) = n :=
    (companion_birthTime n u).trans (urtSigns_birthTime hu)
  have hib : i ≤ Freezing1.birthTime n (toCompanionLabel u) := hbu.symm ▸ hi
  have hmean := urt_sum_heightBernoulliParameter hi hu
  have he := height_deviation_le_of_bernoulli_law
    (identDistrib_heightAt_sum_heightBernoulli hn hu' hib) (iIndepFun_heightBernoulli hn hu')
    (fun j ↦ hasLaw_heightBernoulli _ n i _ j) (half_pos hm) hm hmean.le
  rw [hmean] at he
  have hexp : bennettExponent (urtHeightMean n i / 2) (urtHeightMean n i) =
      urtHeightMean n i * bennettFunction (1 / 2) := by
    rw [bennettExponent, div_div_cancel_left' hm.ne', one_div]
  rw [hexp] at he
  refine le_trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)) he
  change heightAt n i (toCompanionLabel u) ω ≤ t at hω
  change urtHeightMean n i / 2 < |heightAt n i (toCompanionLabel u) ω - urtHeightMean n i|
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- **Two-point estimate.** Two independent uniform vertices of the reverse uniform
recursive tree are at distance at most `t < urtHeightMean n i / 2` with probability at most
`1/(n+1)` (collision), plus `2/(i+1)` (late merger), plus an exponential depth tail. -/
theorem urt_sampled_distance_le_probability {n i : ℕ} (hi : i ≤ n) {t : ℝ}
    (hm : 0 < urtHeightMean n i) (ht : t < urtHeightMean n i / 2) :
    (sampledReverseLaw urtSigns n).real {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ t} ≤
      1 / ((n : ℝ) + 1) + (2 / ((i : ℝ) + 1) +
        2 * Real.exp (-(urtHeightMean n i * bennettFunction (1 / 2)))) := by
  have h0 : 0 ≤ activeCount urtSigns n := (urtSigns_survives n n le_rfl).le
  let := uniformVertex_isProbabilityMeasure urtSigns urtSigns_isSigned h0
  have hmem : ∀ᵐ p ∂(uniformVertex urtSigns n).prod (uniformVertex urtSigns n),
      p.1 ∈ vertexLabels urtSigns n ∧ p.2 ∈ vertexLabels urtSigns n := by
    apply (Measure.ae_prod_iff_ae_ae (by exact (Set.to_countable _).measurableSet)).mpr
    filter_upwards [uniformVertex_mem urtSigns urtSigns_isSigned h0] with u hu
    exact (uniformVertex_mem urtSigns urtSigns_isSigned h0).mono fun v hv ↦ ⟨hu, hv⟩
  have hmeas : Measurable (fun q : History × (VertexLabel × VertexLabel) ↦
      reverseDistance n q.2.1 q.2.2 q.1) :=
    measurable_from_prod_countable_left fun p ↦ measurable_reverseDistance n p.1 p.2
  have hη : 0 ≤ 2 / ((i : ℝ) + 1) +
      2 * Real.exp (-(urtHeightMean n i * bennettFunction (1 / 2))) := by positivity
  have h := measureReal_prod_event_le_bad_add
    (μ := jointLaw (companionSchedule urtSigns) n)
    (ν := (uniformVertex urtSigns n).prod (uniformVertex urtSigns n))
    (E := {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ t}) (B := {p | p.1 = p.2})
    (measurableSet_le hmeas measurable_const) ((Set.to_countable _).measurableSet) hη
    (by
      filter_upwards [hmem] with p hp hne
      have hb := urt_pair_distance_le_probability hi hp.1 hp.2 hne t
      have hl := urt_heightAt_lower_tail hi hp.1 hm ht
      change (jointLaw (companionSchedule urtSigns) n).real
        {ω | reverseDistance n p.1 p.2 ω ≤ t} ≤ _
      linarith)
  rw [uniformVertex_collision urtSigns urtSigns_isSigned h0, urtSigns_vertexLabels_card] at h
  push_cast at h
  exact h

/-- **Typical distances are logarithmic.** Two independent uniform vertices of the uniform
recursive tree are at distance more than `log n / 4` with probability tending to one. -/
theorem tendsto_urt_sampled_close_probability :
    Tendsto (fun n ↦ (sampledReverseLaw urtSigns n).real
      {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ Real.log n / 4}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set i : ℕ := ⌈6 / ε⌉₊
  set K : ℝ := Real.log 4 + Real.log ((i : ℝ) + 1)
  set B : ℝ := bennettFunction (1 / 2)
  have hB : 0 < B := bennettFunction_pos (by norm_num)
  have hi : 2 / ((i : ℝ) + 1) < ε / 3 := by
    have h6 : 6 / ε ≤ (i : ℝ) := Nat.le_ceil _
    rw [div_lt_iff₀ (by positivity)]
    have : 6 ≤ ε * (i : ℝ) := by
      rw [div_le_iff₀ hε] at h6
      linarith
    nlinarith
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun n : ℕ ↦ 2 * Real.exp (-((Real.log n - K) * B))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      ((tendsto_atTop_add_const_right _ (-K) hlog).atTop_mul_const hB))
    simpa [Function.comp_def, sub_eq_add_neg] using h.const_mul 2
  have hhalf : Tendsto (fun n : ℕ ↦ Real.log n / 2 - K) atTop atTop :=
    tendsto_atTop_add_const_right _ (-K) (hlog.atTop_div_const two_pos)
  filter_upwards [eventually_ge_atTop (max i 1), hinv.eventually_lt_const (show 0 < ε / 3 by
      positivity), hexp.eventually_lt_const (show 0 < ε / 3 by positivity),
    hhalf.eventually_gt_atTop 0] with n hn hinvn hexpn hhalfn
  have hin : i ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hmean := log_sub_le_urtHeightMean hn1 i
  have hm : 0 < urtHeightMean n i := by
    have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    linarith
  have hb := urt_sampled_distance_le_probability hin (t := Real.log n / 4) hm (by linarith)
  have hexple : Real.exp (-(urtHeightMean n i * B)) ≤ Real.exp (-((Real.log n - K) * B)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-! ### Annealed sampled distances of the scaled tree -/

/-- The exponent for which the source normalization `n ^ (1 - α)` equals a given scale. -/
noncomputable def urtExponent (a : ℝ) (n : ℕ) : ℝ := 1 - Real.log a / Real.log n

/-- For `n ≥ 2`, the normalization `n ^ (1 - urtExponent a n)` is exactly `a`. -/
theorem rpow_one_sub_urtExponent {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a) :
    (n : ℝ) ^ (1 - urtExponent a n) = a := by
  have hlog : Real.log n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  rw [urtExponent, sub_sub_cancel, Real.rpow_def_of_pos (by positivity),
    mul_div_cancel₀ _ hlog, Real.exp_log ha]

/-- The scaled uniform recursive tree law is a forward measured tree law of the all-`+1`
array, with the exponent `urtExponent a n`. -/
theorem urtMeasuredLaw_eq_forwardMeasuredTreeLaw {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a) :
    urtMeasuredLaw a n = forwardMeasuredTreeLaw urtArray (urtExponent a n) n := by
  have hP : (⟨freezingTreeLaw urtArray n, inferInstance⟩ :
      ProbabilityMeasure Freezing1.Forward.State) = ⟨urtLaw n, inferInstance⟩ :=
    Subtype.ext (freezingTreeLaw_urtArray n)
  rw [urtMeasuredLaw, forwardMeasuredTreeLaw, rpow_one_sub_urtExponent hn ha, hP]

/-- **Annealed sampled distances of the scaled uniform recursive tree.** The annealed
`k`-point distance matrix law of `urtMeasuredLaw a n` is the law of the scaled reverse-tree
distances between `k` independent uniform labels. -/
theorem annealedDistanceLaw_urtMeasuredLaw {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 < a)
    (k : ℕ) :
    (annealedDistanceLaw (urtMeasuredLaw a n) k : Measure (Fin k → Fin k → ℝ)) =
      (sampledReverseVectorLaw urtSigns n k).map
        (fun q i j ↦ reverseDistance n (q.2 i) (q.2 j) q.1 / a) := by
  have hmeas : Measurable (sourceSampledDistanceMatrix (urtExponent a n) n k) :=
    (continuous_sourceMatrixReindex k).measurable.comp
      (measurable_rootedSampledDistanceMatrix _ n k)
  rw [urtMeasuredLaw_eq_forwardMeasuredTreeLaw hn ha,
    annealedDistanceLaw_forwardMeasuredTreeLaw_eq_dropRoot urtArray _ (by omega) k,
    ← sourceSampledDistanceLaw_eq_forwardSampledDistanceLaw urtArray _ n k
      (urtArray_isSigned n) (urtArray_survives n),
    sourceSampledDistanceLaw_eq_map, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map (continuous_dropRootMatrix k).measurable hmeas]
  change Measure.map _ (sampledReverseVectorLaw urtSigns n k) = _
  apply Measure.map_congr
  filter_upwards [sourceSampledDistanceMatrix_eq_graphDistance urtSigns urtSigns_isSigned
    (urtSigns_survives n) (urtExponent a n) (k := k)] with q hq
  funext i j
  simp only [Function.comp_apply, dropRootMatrix]
  rw [hq, sourceSampledVertex_succ, sourceSampledVertex_succ, rpow_one_sub_urtExponent hn ha]
  rfl

/-! ### Covering numbers at logarithmic scales -/

/-- At scales `b ≤ C log n`, the annealed probability that `K + 1` iid uniform vertices fail to
be pairwise more than `2 / (8 C)` apart is at most `(K + 1)^2` times the probability that two
iid uniform vertices are within distance `log n / 4`. -/
theorem urt_separated_compl_le {n : ℕ} (hn : 2 ≤ n) {b C : ℝ} (hb : 0 < b) (hC : 0 < C)
    (hbC : b ≤ C * Real.log n) (K : ℕ) :
    (annealedDistanceLaw (urtMeasuredLaw b n) (K + 1) :
        Measure (Fin (K + 1) → Fin (K + 1) → ℝ))
        (separatedMatrices (K + 1) K (1 / (8 * C)))ᶜ ≤
      (Fintype.card (Fin (K + 1) × Fin (K + 1)) : ENNReal) *
        ENNReal.ofReal ((sampledReverseLaw urtSigns n).real
          {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ Real.log n / 4}) := by
  set k := K + 1
  set E2 : Set (History × (VertexLabel × VertexLabel)) :=
    {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ Real.log n / 4}
  have hE2 : MeasurableSet E2 := measurableSet_le
    (measurable_from_prod_countable_left fun p ↦ measurable_reverseDistance n p.1 p.2)
    measurable_const
  have hmeasD : Measurable (fun q : History × (Fin k → VertexLabel) ↦
      fun i j ↦ reverseDistance n (q.2 i) (q.2 j) q.1 / b) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    apply measurable_from_prod_countable_left
    intro v
    exact (measurable_reverseDistance n (v i) (v j)).div_const _
  have hpair (p : Fin k × Fin k) (hp : p.1 ≠ p.2) :
      sampledReverseVectorLaw urtSigns n k
        {q | reverseDistance n (q.2 p.1) (q.2 p.2) q.1 ≤ Real.log n / 4} =
        ENNReal.ofReal ((sampledReverseLaw urtSigns n).real E2) := by
    let := sampledReverseLaw_probability urtSigns urtSigns_isSigned (urtSigns_survives n)
    rw [ofReal_measureReal, ← sampledReverseVectorLaw_map_pair urtSigns urtSigns_isSigned
      (urtSigns_survives n) hp, Measure.map_apply (by fun_prop) hE2]
    rfl
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [annealedDistanceLaw_urtMeasuredLaw hn hb,
    Measure.map_apply hmeasD (isOpen_separatedMatrices _ _ _).measurableSet.compl]
  calc
    _ ≤ sampledReverseVectorLaw urtSigns n k (⋃ p : Fin k × Fin k,
        {q | p.1 ≠ p.2 ∧ reverseDistance n (q.2 p.1) (q.2 p.2) q.1 ≤ Real.log n / 4}) := by
      apply measure_mono
      intro q hq
      simp only [mem_preimage, mem_compl_iff, separatedMatrices, mem_ofPred_eq, not_exists,
        not_forall, not_lt] at hq
      obtain ⟨i, j, hij, hle⟩ := hq id
      refine mem_iUnion.mpr ⟨(i, j), hij, ?_⟩
      rw [div_le_iff₀ hb] at hle
      have h8 : 2 * (1 / (8 * C)) * b ≤ Real.log n / 4 := by
        rw [show 2 * (1 / (8 * C)) * b = b / (4 * C) by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      exact hle.trans h8
    _ ≤ ∑ p : Fin k × Fin k, sampledReverseVectorLaw urtSigns n k
        {q | p.1 ≠ p.2 ∧ reverseDistance n (q.2 p.1) (q.2 p.2) q.1 ≤ Real.log n / 4} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin k × Fin k, ENNReal.ofReal ((sampledReverseLaw urtSigns n).real E2) := by
      gcongr with p
      by_cases hp : p.1 = p.2
      · simp [hp]
      · rw [← hpair p hp]
        exact measure_mono fun q hq ↦ hq.2
    _ = _ := by simp

/-- **Covering numbers blow up at logarithmic scales.** Along horizons `N m → ∞` with scales
`0 < b m ≤ C log (N m)`, for every `K` the probability that the scaled uniform recursive tree
is not covered by `K` open balls of radius `1 / (8 C)` tends to one, provided two iid uniform
vertices are at distance more than `log n / 4` with probability tending to one. -/
theorem urt_not_coverable_of_le_log_of_pair {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {b : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hb : ∀ᶠ m in atTop, 0 < b m ∧ b m ≤ C * Real.log (N m))
    (hpair : Tendsto (fun n ↦ (sampledReverseLaw urtSigns n).real
      {q | reverseDistance n q.2.1 q.2.2 q.1 ≤ Real.log n / 4}) atTop (𝓝 0)) (K : ℕ) :
    Tendsto (fun m ↦ (urtMeasuredLaw (b m) (N m) : Measure MeasuredGHSpace.{0})
      {X | ¬ Coverable (underlyingGH X).Rep K (1 / (8 * C))}) atTop (𝓝 1) := by
  set r : ℝ := 1 / (8 * C)
  set S := separatedMatrices (K + 1) K r
  have hS : MeasurableSet S := (isOpen_separatedMatrices _ _ _).measurableSet
  have hbound : Tendsto (fun m ↦ (Fintype.card (Fin (K + 1) × Fin (K + 1)) : ENNReal) *
      ENNReal.ofReal ((sampledReverseLaw urtSigns (N m)).real
        {q | reverseDistance (N m) q.2.1 q.2.2 q.1 ≤ Real.log (N m) / 4})) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (hpair.comp hN))
      (a := (Fintype.card (Fin (K + 1) × Fin (K + 1)) : ENNReal))
      (Or.inr (ENNReal.natCast_ne_top _))
    simpa [Function.comp_def] using h
  have hcompl : Tendsto (fun m ↦ (annealedDistanceLaw (urtMeasuredLaw (b m) (N m)) (K + 1) :
      Measure (Fin (K + 1) → Fin (K + 1) → ℝ)) Sᶜ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      (Eventually.of_forall fun _ ↦ zero_le)
    filter_upwards [hb, hN.eventually_ge_atTop 2] with m hm hm2
    exact urt_separated_compl_le hm2 hm.1 hC hm.2 K
  have hlow : Tendsto (fun m ↦ 1 - (annealedDistanceLaw (urtMeasuredLaw (b m) (N m)) (K + 1) :
      Measure (Fin (K + 1) → Fin (K + 1) → ℝ)) Sᶜ) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hcompl (Or.inl ENNReal.one_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro m
    have h := annealedDistanceLaw_separatedMatrices_le (urtMeasuredLaw (b m) (N m)) (K + 1) K r
    change 1 - _ ≤ _
    rw [← prob_compl_eq_one_sub hS.compl, compl_compl]
    exact h
  · intro m
    exact prob_le_one

/-- **Covering numbers blow up at logarithmic scales.** Along horizons `N m → ∞` with scales
`0 < b m ≤ C log (N m)`, for every `K` the probability that the scaled uniform recursive tree
is not covered by `K` open balls of radius `1 / (8 C)` tends to one. -/
theorem urt_not_coverable_of_le_log {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {b : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hb : ∀ᶠ m in atTop, 0 < b m ∧ b m ≤ C * Real.log (N m)) (K : ℕ) :
    Tendsto (fun m ↦ (urtMeasuredLaw (b m) (N m) : Measure MeasuredGHSpace.{0})
      {X | ¬ Coverable (underlyingGH X).Rep K (1 / (8 * C))}) atTop (𝓝 1) :=
  urt_not_coverable_of_le_log_of_pair hN hC hb tendsto_urt_sampled_close_probability K

/-! ### Main statements -/

/-- **Non-tightness at logarithmic scales.** If `0 < a n ≤ C log n` for all large `n`, the laws
of the scaled uniform recursive trees are not tight in the GHP topology. -/
theorem urt_not_tight_of_le_log {a : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (ha : ∀ᶠ n in atTop, 0 < a n ∧ a n ≤ C * Real.log n) :
    ¬ IsTightMeasureSet
      (range fun n ↦ (urtMeasuredLaw (a n) n : Measure MeasuredGHSpace.{0})) := by
  intro htight
  have hr : 0 < 1 / (8 * C) := by positivity
  have hK := urt_not_coverable_of_le_log tendsto_id hC ha
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨S, hS, hSmass⟩ := htight 2⁻¹ (by norm_num)
  obtain ⟨K, hKS⟩ := exists_coverable_of_isCompact (hS.image continuous_underlyingGH) hr
  have hle (n : ℕ) : (urtMeasuredLaw (a n) n : Measure MeasuredGHSpace.{0})
      {X | ¬ Coverable (underlyingGH X).Rep K (1 / (8 * C))} ≤ 2⁻¹ :=
    (measure_mono (show {X : MeasuredGHSpace.{0} |
        ¬ Coverable (underlyingGH X).Rep K (1 / (8 * C))} ⊆ Sᶜ
      from fun X hX hXS ↦ hX (hKS _ (mem_image_of_mem _ hXS)))).trans
      (hSmass _ (mem_range_self n))
  obtain ⟨n, hn⟩ := ((hK K).eventually (lt_mem_nhds ENNReal.one_half_lt_one)).exists
  exact (hle n).not_gt hn

/-- **Non-tightness at the natural scale (U04b).** The laws of the uniform recursive trees
with distances divided by `log n` are not tight in the GHP topology. This is the analogue of
`supercritical_not_tight`. -/
theorem urt_log_not_tight :
    ¬ IsTightMeasureSet
      (range fun n : ℕ ↦ (urtMeasuredLaw (Real.log n) n : Measure MeasuredGHSpace.{0})) := by
  refine urt_not_tight_of_le_log (a := fun n : ℕ ↦ Real.log n) one_pos ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact ⟨Real.log_pos (by exact_mod_cast (show 1 < n by omega)), by rw [one_mul]⟩

/-- **No subsequential limit at logarithmic scales.** If `0 < a n ≤ C log n` for all large `n`,
no subsequence of the laws of the scaled uniform recursive trees converges weakly in the GHP
topology. -/
theorem urt_no_weak_limit_of_le_log {a : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (ha : ∀ᶠ n in atTop, 0 < a n ∧ a n ≤ C * Real.log n) :
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Q : ProbabilityMeasure MeasuredGHSpace.{0},
      ¬ Tendsto (fun n ↦ urtMeasuredLaw (a (φ n)) (φ n)) atTop (𝓝 Q) := by
  intro φ hφ Q
  exact not_tendsto_of_not_coverable (by positivity)
    (urt_not_coverable_of_le_log hφ.tendsto_atTop hC (hφ.tendsto_atTop.eventually ha)) Q

/-- **No scaling limit at the natural scale (U04b).** No subsequence of the laws of the
uniform recursive trees with distances divided by `log n` converges weakly in the GHP
topology. -/
theorem urt_log_no_weak_limit :
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ Q : ProbabilityMeasure MeasuredGHSpace.{0},
      ¬ Tendsto (fun n ↦ urtMeasuredLaw (Real.log (φ n)) (φ n)) atTop (𝓝 Q) := by
  refine urt_no_weak_limit_of_le_log (a := fun n : ℕ ↦ Real.log n) one_pos ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact ⟨Real.log_pos (by exact_mod_cast (show 1 < n by omega)), by rw [one_mul]⟩

/-- A sequence of eventually positive scales not dominating `log n` stays below `C log n`
along a subsequence, for some `C > 0`. -/
theorem exists_strictMono_le_log_of_not_tendsto {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    (hscale : ¬ Tendsto (fun n ↦ a n / Real.log n) atTop atTop) :
    ∃ C > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ m, 0 < a (φ m) ∧ a (φ m) ≤ C * Real.log (φ m) := by
  rw [tendsto_atTop] at hscale
  push Not at hscale
  obtain ⟨C0, hC0⟩ := hscale
  set C : ℝ := max C0 1
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfreq : ∃ᶠ n in atTop, 0 < a n ∧ a n ≤ C * Real.log n := by
    refine (hC0.and_eventually (ha.and (eventually_ge_atTop 2))).mono ?_
    rintro n ⟨hlt, hpos, hn⟩
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    refine ⟨hpos, ?_⟩
    have h1 : a n / Real.log n ≤ C := hlt.le.trans (le_max_left _ _)
    rw [div_le_iff₀ hlog] at h1
    exact h1
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
  exact ⟨C, hC, φ, hφ, hP⟩

/-- **U04b, corrected as in S19: recursive trees have no nondegenerate GHP scaling limit.**
For every sequence of eventually positive scales `a n`, if the laws of the uniform recursive
trees with distances divided by `a n` and uniform vertex measures converge weakly in the GHP
topology to some `Q`, then `Q` is the Dirac mass at the one-point space. -/
theorem urt_weak_limit_eq_onePoint {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    {Q : ProbabilityMeasure MeasuredGHSpace.{0}}
    (hQ : Tendsto (fun n ↦ urtMeasuredLaw (a n) n) atTop (𝓝 Q)) : Q = onePointLaw := by
  by_cases hscale : Tendsto (fun n ↦ a n / Real.log n) atTop atTop
  · exact tendsto_nhds_unique hQ (tendsto_urtMeasuredLaw_onePoint hscale)
  · exfalso
    obtain ⟨C, hC, φ, hφ, hP⟩ := exists_strictMono_le_log_of_not_tendsto ha hscale
    exact not_tendsto_of_not_coverable (by positivity)
      (urt_not_coverable_of_le_log hφ.tendsto_atTop hC (Eventually.of_forall hP)) Q
      (hQ.comp hφ.tendsto_atTop)

/-- **Characterization of the scales with a GHP limit.** For eventually positive scales, the
laws of the scaled uniform recursive trees converge weakly in the GHP topology if and only if
`a n / log n → ∞`, and the limit is then the one-point space. -/
theorem urt_tendsto_iff {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n) :
    (∃ Q : ProbabilityMeasure MeasuredGHSpace.{0},
      Tendsto (fun n ↦ urtMeasuredLaw (a n) n) atTop (𝓝 Q)) ↔
      Tendsto (fun n ↦ a n / Real.log n) atTop atTop := by
  constructor
  · rintro ⟨Q, hQ⟩
    by_contra hscale
    obtain ⟨C, hC, φ, hφ, hP⟩ := exists_strictMono_le_log_of_not_tendsto ha hscale
    exact not_tendsto_of_not_coverable (by positivity)
      (urt_not_coverable_of_le_log hφ.tendsto_atTop hC (Eventually.of_forall hP)) Q
      (hQ.comp hφ.tendsto_atTop)
  · intro hscale
    exact ⟨onePointLaw, tendsto_urtMeasuredLaw_onePoint hscale⟩

end Freezing2
