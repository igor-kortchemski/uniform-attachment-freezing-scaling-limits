module

public import Freezing2.Probability.SubcriticalCoalescenceLaw
public import Freezing2.Probability.DistanceApproximation
public import Freezing2.Probability.ForwardReverseLaw
public import Freezing2.Probability.CanonicalMetricTransport
public import Freezing2.Geometry.TreeMeasuredSpaces
public import Freezing2.Geometry.GHPUnderlyingProjection
public import Freezing2.Analysis.SourceHypotheses

/-!
# Bounded population: the GH limit is the unit segment

This is Theorem `thm:alpha0` (inventory item N09). If `τ(Xⁿ) > n` and `Sⁿ_k ≤ M` for
all `k ≤ n`, the actual forward tree `𝒯_n`, with graph distances scaled by `1 / h_n^+`,
converges in probability to `[0,1]` for the Gromov–Hausdorff distance.

The proof follows the source.

* **Deterministic reduction.** Map every vertex to its scaled height. Distortion is
  `d(u,v) - |ht u - ht v| = 2 min(d(u,w), d(v,w))`, with `w` the nearest common ancestor,
  and the heights along a longest branch are dense. A clamp map compares `[0, c·Height]`
  with `[0,1]`.
* **Height.** `Height(𝒯_n)/h_n^+ → 1` in probability is the companion theorem
  `maximum_height_deviation_tendsto_zero`. Its premise `log n = o(h_n^+)` holds because
  bounded population gives `h_n^+ ≥ n/(2M)`.
* **Side branches.** On the reverse history, the depths of two vertices in a common
  component are shifted by the same amount at every later step, so the terminal excess
  `d(u,v) - |ht u - ht v|` equals twice the smaller depth at the coalescence phase.
  That depth is at most `b_n(u) - coal_n(u,v)`, as in the source. The exact survival
  product of `coalescenceTime_lt_probability` is exponentially small under bounded
  population, since every up-step hazard is at least `2/M²` and a window of length `m`
  contains at least `(m + 1 - M)/2` up-steps. A union bound over the at most `(n+1)²`
  pairs concludes.
* **Transport.** The excess event is carried from the forward law to the reverse law
  by the canonical forward/reverse identification N01, which preserves graph distances
  and sends the reverse root to the forward root `0`.

The zero row of the array is unconstrained; it is replaced by `initialRowExtension`
only for the companion height theorem, whose premises are stated for all horizons.
-/

@[expose] public section

open Filter MeasureTheory Set GromovHausdorff
open scoped ENNReal Topology

namespace Freezing2

open ReverseHistory ReverseCoalescence ForestCoalescence MeasuredGHSpace

/-! ### Deterministic Gromov–Hausdorff reduction -/

/-- A map onto an approximately dense subset of a segment, with additive
distortion `η`, bounds the GH distance to the segment. -/
theorem ghDist_Icc_le {V : Type*} [MetricSpace V] [CompactSpace V] [Nonempty V] {H η ρ : ℝ}
    [Nonempty (Icc (0 : ℝ) H)] (φ : V → ℝ) (hφ : ∀ v, φ v ∈ Icc 0 H)
    (hdense : ∀ t ∈ Icc 0 H, ∃ v, |t - φ v| ≤ ρ)
    (hdist : ∀ u v, abs (dist u v - abs (φ u - φ v)) ≤ η) :
    ghDist V (Icc (0 : ℝ) H) ≤ η / 2 + ρ := by
  have h := ghDist_le_of_approx_subsets (s := (Set.univ : Set V))
    (fun v ↦ (⟨φ v.1, hφ v.1⟩ : Icc (0 : ℝ) H)) (ε₁ := 0) (ε₂ := η) (ε₃ := ρ)
    (fun x ↦ ⟨x, Set.mem_univ x, by simp⟩)
    (fun t ↦ by
      obtain ⟨v, hv⟩ := hdense t.1 t.2
      exact ⟨⟨v, Set.mem_univ v⟩, by rw [Subtype.dist_eq, Real.dist_eq]; exact hv⟩)
    (fun x y ↦ by
      have e : dist (⟨φ x.1, hφ x.1⟩ : Icc (0 : ℝ) H) ⟨φ y.1, hφ y.1⟩ =
          |φ x.1 - φ y.1| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      rw [e]
      exact hdist x.1 y.1)
  linarith

/-- Two segments starting at zero are within `3/2` times their length difference,
using the clamp map `t ↦ min t b`. -/
theorem ghDist_Icc_Icc_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    [Nonempty (Icc (0 : ℝ) a)] [Nonempty (Icc (0 : ℝ) b)] :
    ghDist (Icc (0 : ℝ) a) (Icc (0 : ℝ) b) ≤ 3 / 2 * |a - b| := by
  have hclamp : ∀ t : Icc (0 : ℝ) a, 0 ≤ t.1 - min t.1 b ∧ t.1 - min t.1 b ≤ |a - b| := by
    intro t
    have h1 := t.2.1
    have h2 := t.2.2
    constructor
    · have := min_le_left t.1 b
      linarith
    · rcases le_total t.1 b with h | h
      · rw [min_eq_left h]
        simp
      · rw [min_eq_right h]
        have := le_abs_self (a - b)
        linarith
  have h := ghDist_Icc_le (V := Icc (0 : ℝ) a) (H := b) (η := |a - b|) (ρ := |a - b|)
    (fun t ↦ min t.1 b)
    (fun t ↦ ⟨le_min t.2.1 hb, min_le_right _ _⟩)
    (fun t ht ↦ by
      refine ⟨⟨min t a, le_min ht.1 ha, min_le_right _ _⟩, ?_⟩
      have hmin : min (min t a) b = min t a :=
        min_eq_left ((min_le_left t a).trans ht.2)
      simp only [hmin]
      rcases le_total t a with h | h
      · rw [min_eq_left h]
        simp
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        have := le_abs_self (b - a)
        rw [abs_sub_comm] at this
        linarith [ht.2])
    (fun u v ↦ by
      rw [Subtype.dist_eq, Real.dist_eq]
      obtain ⟨hu1, hu2⟩ := hclamp u
      obtain ⟨hv1, hv2⟩ := hclamp v
      calc
        _ ≤ |(u.1 - v.1) - (min u.1 b - min v.1 b)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |(u.1 - min u.1 b) - (v.1 - min v.1 b)| := by ring_nf
        _ ≤ |a - b| := by
          rw [abs_le]
          constructor <;> linarith)
  linarith

/-- Every height between zero and the tree height is attained by a vertex. -/
theorem exists_vertex_height_eq {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {k : ℕ} (hk : k ≤ Freezing1.Forward.treeHeight s) :
    ∃ v ∈ s.vertices, s.height v = k := by
  obtain ⟨w, hw, hwH⟩ := Finset.exists_mem_eq_sup s.vertices ⟨0, hs.root_mem⟩ s.height
  have key : ∀ v, v ∈ s.vertices → ∀ k ≤ s.height v,
      ∃ u ∈ s.vertices, s.height u = k := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro hv k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact ⟨v, hv, rfl⟩
      · have hv0 : v ≠ 0 := by
          rintro rfl
          rw [hs.height_root] at hlt
          exact Nat.not_lt_zero _ hlt
        have hp := hs.height_parent v hv hv0
        exact ih (s.parent v) (hs.parent_lt v hv hv0) (hs.parent_mem v hv) k (by omega)
  exact key w hw k (by rw [← hwH]; exact hk)

/-- **Deterministic GH reduction.** In a valid forward tree, scaled by `c > 0`, suppose
every pair of vertices satisfies `d(u,v) - |ht u - ht v| ≤ D`; this quantity is twice the
smaller distance from `u` or `v` to their nearest common ancestor. Then the tree is within
`c * D / 2 + c + 3/2 * |c * height - 1|` of the unit segment. The map is `v ↦ c * ht v`,
and all intermediate heights are attained along the path to a deepest vertex. -/
theorem forward_dist_unitInterval_le {n : ℕ} {s : Freezing1.Forward.State}
    (hs : Freezing1.Forward.ValidAt n s) {c D : ℝ} (hc : 0 < c)
    (hD : ∀ u ∈ s.vertices, ∀ v ∈ s.vertices,
      (s.graph.dist u v : ℝ) - |(s.height u : ℝ) - s.height v| ≤ D) :
    dist (MeasuredGHSpace.underlyingGH (toMeasuredGHSpace (forwardMeasuredSpace c s)))
        (toGHSpace unitInterval) ≤
      c * D / 2 + c + 3 / 2 * |c * Freezing1.Forward.treeHeight s - 1| := by
  have hconn := hs.tree_connected
  set H := c * (Freezing1.Forward.treeHeight s : ℝ) with hH
  have hH0 : 0 ≤ H := by positivity
  have : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH0⟩⟩
  have : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by norm_num, by norm_num⟩⟩
  let := scaledGraphMetric s.tree hconn c hc
  have := hconn.nonempty
  have hheight (v : {v // v ∈ s.vertices}) :
      (s.height v : ℝ) ≤ Freezing1.Forward.treeHeight s := by
    exact_mod_cast Finset.le_sup (f := s.height) v.property
  have h1 : ghDist {v // v ∈ s.vertices} (Icc (0 : ℝ) H) ≤ c * D / 2 + c := by
    apply ghDist_Icc_le (fun v : {v // v ∈ s.vertices} ↦ c * (s.height v : ℝ))
    · intro v
      exact ⟨by positivity, mul_le_mul_of_nonneg_left (hheight v) hc.le⟩
    · intro t ht
      have htc : 0 ≤ t / c := div_nonneg ht.1 hc.le
      have hk : ⌊t / c⌋₊ ≤ Freezing1.Forward.treeHeight s := by
        have h1 : (⌊t / c⌋₊ : ℝ) ≤ t / c := Nat.floor_le htc
        have h2 : t / c ≤ Freezing1.Forward.treeHeight s := by
          rw [div_le_iff₀ hc]
          linarith [ht.2]
        exact_mod_cast h1.trans h2
      obtain ⟨v, hv, hvk⟩ := exists_vertex_height_eq hs hk
      refine ⟨⟨v, hv⟩, ?_⟩
      have hf1 : (⌊t / c⌋₊ : ℝ) ≤ t / c := Nat.floor_le htc
      have hf2 : t / c < ⌊t / c⌋₊ + 1 := Nat.lt_floor_add_one _
      have e1 : c * (⌊t / c⌋₊ : ℝ) ≤ t := by
        have := mul_le_mul_of_nonneg_left hf1 hc.le
        rwa [mul_div_cancel₀ _ hc.ne'] at this
      have e2 : t < c * ((⌊t / c⌋₊ : ℝ) + 1) := by
        have := mul_lt_mul_of_pos_left hf2 hc
        rwa [mul_div_cancel₀ _ hc.ne'] at this
      simp only [hvk]
      rw [abs_le]
      constructor <;> nlinarith
    · intro u v
      change abs (c * (s.tree.dist u v : ℝ) - abs (c * (s.height u : ℝ) - c * s.height v)) ≤
        c * D
      have hu := hs.height_eq_tree_dist u
      have hv := hs.height_eq_tree_dist v
      have htri1 := hconn.dist_triangle (u := ⟨0, hs.root_mem⟩) (v := u) (w := v)
      have htri2 := hconn.dist_triangle (u := ⟨0, hs.root_mem⟩) (v := v) (w := u)
      rw [SimpleGraph.dist_comm (u := v) (v := u)] at htri2
      rw [← hu, ← hv] at htri1
      rw [← hu, ← hv] at htri2
      have hge : |(s.height u : ℝ) - s.height v| ≤ s.tree.dist u v := by
        rw [abs_le]
        constructor
        · have : (s.height v : ℝ) ≤ s.height u + s.tree.dist u v := by exact_mod_cast htri1
          linarith
        · have : (s.height u : ℝ) ≤ s.height v + s.tree.dist u v := by exact_mod_cast htri2
          linarith
      have hle := hD u u.property v v.property
      rw [← forward_tree_dist_eq hs u v] at hle
      rw [← mul_sub, abs_mul, abs_of_pos hc, ← mul_sub, abs_mul, abs_of_pos hc,
        abs_of_nonneg (by nlinarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have h2 : ghDist (Icc (0 : ℝ) H) (Icc (0 : ℝ) 1) ≤ 3 / 2 * |H - 1| :=
    ghDist_Icc_Icc_le hH0 zero_le_one
  rw [MeasuredGHSpace.underlyingGH_toMeasuredGHSpace]
  have heq : toGHSpace (forwardMeasuredSpace c s) = toGHSpace {v // v ∈ s.vertices} := by
    rw [forwardMeasuredSpace, dite_eq_left ⟨hconn, hc⟩]
    rfl
  calc
    _ ≤ dist (toGHSpace (forwardMeasuredSpace c s)) (toGHSpace (Icc (0 : ℝ) H)) +
        dist (toGHSpace (Icc (0 : ℝ) H)) (toGHSpace unitInterval) := dist_triangle _ _ _
    _ ≤ (c * D / 2 + c) + 3 / 2 * |H - 1| := by
      rw [heq]
      exact add_le_add h1 h2
    _ = _ := by rw [hH]

/-! ### Uniform depth shifts in the reverse construction -/

/-- A transition adds the same depth to two vertices lying in one component. -/
def DepthShift (F G : Freezing1.Reverse.Forest) : Prop :=
  ∀ u ∈ F.vertices, ∀ v ∈ F.vertices, F.root u = F.root v →
    G.depth u + F.depth v = G.depth v + F.depth u

/-- The depth-shift relation is a measurable event on pairs of forests. -/
theorem measurableSet_depthShift :
    MeasurableSet {p : Freezing1.Reverse.Forest × Freezing1.Reverse.Forest |
      DepthShift p.1 p.2} := by
  have ho (u v : ℕ ⊕ ℕ) : Measurable (fun F : Freezing1.Reverse.Forest ↦
      u ∈ F.vertices ∧ v ∈ F.vertices ∧ F.root u = F.root v) := measurable_from_top
  have hd (u : ℕ ⊕ ℕ) : Measurable (fun F : Freezing1.Reverse.Forest ↦ F.depth u) :=
    measurable_from_top
  have he (u v : ℕ ⊕ ℕ) : Measurable (fun p : Freezing1.Reverse.Forest ×
      Freezing1.Reverse.Forest ↦ p.2.depth u + p.1.depth v = p.2.depth v + p.1.depth u) :=
    measurableSet_setOfPred.mp (measurableSet_eq_fun
      (((hd u).comp measurable_snd).add ((hd v).comp measurable_fst))
      (((hd v).comp measurable_snd).add ((hd u).comp measurable_fst)))
  have hset : {p : Freezing1.Reverse.Forest × Freezing1.Reverse.Forest | DepthShift p.1 p.2} =
      {p | ∀ u v, (u ∈ p.1.vertices ∧ v ∈ p.1.vertices ∧ p.1.root u = p.1.root v) →
        p.2.depth u + p.1.depth v = p.2.depth v + p.1.depth u} := by
    ext p
    constructor
    · intro h u v huv
      exact h u huv.1 v huv.2.1 huv.2.2
    · intro h u hu v hv hr
      exact h u v ⟨hu, hv, hr⟩
  rw [hset]
  exact (Measurable.forall fun u ↦ Measurable.forall fun v ↦
    ((ho u v).comp measurable_fst).imp (he u v)).setOf

/-- A merge adds one to the depth of a whole component, or nothing. -/
theorem joinChoice_depthShift (F : Freezing1.Reverse.Forest) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    DepthShift F (F.joinChoice p) := by
  intro u _ v _ huv
  by_cases hp : p ∈ F.roots.offDiag
  · rw [Freezing1.RootedForest.joinChoice_depth F hp,
      Freezing1.RootedForest.joinChoice_depth F hp, huv]
    omega
  · simp only [Freezing1.RootedForest.joinChoice, dite_eq_right hp]
    omega

/-- Both reverse transitions (merging and inserting a frozen label) shift depths
uniformly on each existing component. -/
theorem transitionLaw_ae_depthShift (x : Freezing1.SignSequence) (i : ℕ)
    (F : Freezing1.Reverse.Forest) :
    ∀ᵐ G ∂Freezing1.Reverse.transitionLaw x i F, DepthShift F G := by
  unfold Freezing1.Reverse.transitionLaw
  split_ifs
  · by_cases htwo : 2 ≤ F.roots.card
    · exact F.joinLaw_ae htwo _ fun p _ ↦ joinChoice_depthShift F p
    · simp only [Freezing1.RootedForest.joinLaw, ite_eq_right htwo]
      apply (ae_dirac_iff (by trivial)).mpr
      intro u _ v _ _
      omega
  · apply (ae_dirac_iff (by trivial)).mpr
    intro u hu v hv _
    unfold Freezing1.Reverse.insertLabel
    split_ifs with h
    · omega
    · rw [Freezing1.RootedForest.adjoin_depth_old F h hu,
        Freezing1.RootedForest.adjoin_depth_old F h hv]
      omega

/-- Every actual reverse step shifts the depths of a common component uniformly. -/
theorem jointLaw_depthShift (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, ∀ k, DepthShift (ω k) (ω (k + 1)) := by
  apply ae_all_iff.mpr
  intro k
  apply jointLaw_ae_transition x n k measurableSet_depthShift
  apply Eventually.of_forall
  intro ω
  apply (ae_iff_prob_eq_one measurable_from_top).mp
  change ∀ᵐ G ∂(if k < n then Freezing1.Reverse.transitionLaw x (n - (k + 1)) (ω k)
    else Measure.dirac (ω k)), DepthShift (ω k) G
  split_ifs
  · exact transitionLaw_ae_depthShift x _ _
  · apply (ae_dirac_iff (by trivial)).mpr
    intro u _ v _ _
    omega

/-- Depth differences inside a component persist along the whole reverse history. -/
theorem depth_difference_persists {ω : History}
    (hshift : ∀ k, DepthShift (ω k) (ω (k + 1)))
    (hco : ∀ k, Coarsens (ω k) (ω (k + 1))) {k l : ℕ} (hkl : k ≤ l)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ (ω k).vertices) (hv : v ∈ (ω k).vertices)
    (hr : (ω k).root u = (ω k).root v) :
    (ω l).depth u + (ω k).depth v = (ω l).depth v + (ω k).depth u := by
  have hchain : ∀ m, k ≤ m → Coarsens (ω k) (ω m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact Coarsens.refl _
    | succ m _ ih => exact ih.trans (hco m)
  induction l, hkl using Nat.le_induction with
  | base => omega
  | succ l hkl ih =>
    have hc := hchain l hkl
    have h := hshift l u (hc.1 hu) v (hc.1 hv) (hc.2 u hu v hv hr)
    omega

/-- A reverse depth is at most the number of steps since the vertex's birth. -/
theorem jointLaw_depth_le_birth {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ a ≤ Freezing1.birthTime n v,
      (forestAt n a ω).depth v + a ≤ Freezing1.birthTime n v := by
  apply ae_all_iff.mpr
  intro a
  by_cases ha : a ≤ Freezing1.birthTime n v
  · filter_upwards [heightAt_eq_sum_heightBernoulli hn hv ha] with ω hω _
    have hle : heightAt n a v ω ≤ (Freezing1.birthTime n v - a : ℕ) := by
      rw [hω]
      calc
        _ ≤ ∑ _i : Fin (Freezing1.birthTime n v - a), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          unfold heightBernoulli heightIncrementVariable
          exact Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ zero_le_one)
        _ = _ := by simp
    have hle' : (forestAt n a ω).depth v ≤ Freezing1.birthTime n v - a := by
      unfold heightAt at hle
      exact_mod_cast hle
    omega
  · exact Eventually.of_forall fun _ h ↦ (ha h).elim

/-- For every pair of labels, the terminal branching excess is at most twice
the delay between the common birth and the coalescence time. -/
theorem jointLaw_excess_le_gap {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, ∀ r ∈ (ω n).roots,
      ((ω n).graph.dist u v : ℝ) - |((ω n).graph.dist r u : ℝ) - (ω n).graph.dist r v| ≤
        2 * ((commonBirth n u v - coalescenceTime n u v ω : ℕ) : ℝ) := by
  filter_upwards [jointLaw_distance_eq_heights_at_coalescence hn hu hv, jointLaw_depthShift x n,
    jointLaw_step_coarsens x n, jointLaw_members hn hu hv, jointLaw_connected_zero hn hu hv,
    jointLaw_depth_le_birth hn hu, jointLaw_depth_le_birth hn hv,
    jointLaw_forestAt_valid x n hn] with ω hdist hshift hco hmem hzero hbu hbv hvalid
  intro r hr
  have hcB : coalescenceTime n u v ω ≤ commonBirth n u v :=
    coalescenceTime_le_commonBirth n u v ω
  have hconn : connectedAt n u v (coalescenceTime n u v ω) ω :=
    connectedAt_coalescenceTime hzero
  have hmemc := hmem _ hcB
  have hpers := depth_difference_persists hshift hco (Nat.sub_le n (coalescenceTime n u v ω))
    hmemc.1 hmemc.2 hconn
  have hroots : (ω n).roots.card = 1 := by
    simpa [forestAt] using (hvalid 0 (Nat.zero_le n)).roots_card
  obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hroots
  have hroot (w : ℕ ⊕ ℕ) (hw : w ∈ (ω n).vertices) : (ω n).root w = r := by
    have h1 := (ω n).root_mem_roots hw
    rw [hr0, Finset.mem_singleton] at h1
    rw [hr0, Finset.mem_singleton] at hr
    rw [h1, hr]
  have hu0 : u ∈ (ω n).vertices := by simpa [forestAt] using (hmem 0 (Nat.zero_le _)).1
  have hv0 : v ∈ (ω n).vertices := by simpa [forestAt] using (hmem 0 (Nat.zero_le _)).2
  have hdu : (ω n).graph.dist r u = (ω n).depth u := by
    rw [(ω n).depth_eq_dist hu0, hroot u hu0]
  have hdv : (ω n).graph.dist r v = (ω n).depth v := by
    rw [(ω n).depth_eq_dist hv0, hroot v hv0]
  have hdist' : (ω n).graph.dist u v =
      (forestAt n (coalescenceTime n u v ω) ω).depth u +
        (forestAt n (coalescenceTime n u v ω) ω).depth v := by
    simpa [forestAt] using hdist
  have hbu' := hbu _ (hcB.trans (min_le_left _ _))
  have hbv' := hbv _ (hcB.trans (min_le_right _ _))
  simp only [forestAt] at hbu' hbv' hdist'
  rw [hdu, hdv, hdist', Nat.cast_sub hcB]
  set du := (ω (n - coalescenceTime n u v ω)).depth u
  set dv := (ω (n - coalescenceTime n u v ω)).depth v
  set c := coalescenceTime n u v ω
  have hB : commonBirth n u v = min (Freezing1.birthTime n u) (Freezing1.birthTime n v) := rfl
  have hbu'' : (du : ℝ) + c ≤ Freezing1.birthTime n u := by exact_mod_cast hbu'
  have hbv'' : (dv : ℝ) + c ≤ Freezing1.birthTime n v := by exact_mod_cast hbv'
  have hpers' : ((ω n).depth u : ℝ) + dv = (ω n).depth v + du := by exact_mod_cast hpers
  have habs : |((ω n).depth u : ℝ) - (ω n).depth v| = |(du : ℝ) - dv| := by
    congr 1
    linarith
  rw [habs]
  push_cast
  have hBu : (commonBirth n u v : ℝ) =
      min (Freezing1.birthTime n u : ℝ) (Freezing1.birthTime n v) := by
    rw [hB, Nat.cast_min]
  rcases le_total (du : ℝ) dv with h | h
  · rw [abs_of_nonpos (by linarith)]
    have : (du : ℝ) + c ≤ commonBirth n u v := by
      rw [hBu]
      exact le_min hbu'' (by linarith)
    linarith
  · rw [abs_of_nonneg (by linarith)]
    have : (dv : ℝ) + c ≤ commonBirth n u v := by
      rw [hBu]
      exact le_min (by linarith) hbv''
    linarith

/-! ### Coalescence delays under bounded population -/

/-- Counting the up-steps of a window. -/
theorem sum_up_indicator (x : ℕ → ℤ) (a m : ℕ) (c : ℝ) :
    (∑ i ∈ Finset.range m, (if x (a + i + 1) = 1 then c else 0)) =
      ((upSteps x a (a + m)).card : ℝ) * c := by
  rw [← sum_Ico_one_based_interval (fun j ↦ if x j = 1 then c else 0)]
  have hI : Finset.Ico (a + 1) (a + m + 1) = Finset.Ioc a (a + m) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hI, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- Bounded population makes every up-step contribute a uniformly positive
coalescence hazard. -/
theorem coalescenceUpSum_ge_of_bounded (x : ℕ → ℤ) (hx : IsSigned x) {n a m M : ℕ}
    (hs : SurvivesThrough x n) (ham : a + m ≤ n) (hM : ∀ k ≤ n, activeCount x k ≤ M) :
    ((m : ℝ) + 1 - M) / (2 * (M : ℝ) ^ 2) ≤ coalescenceUpSum x a m := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 (Nat.zero_le n)
    rw [activeCount_zero] at h
    exact_mod_cast h
  have hterm : ∀ i ∈ Finset.range m,
      (if x (a + i + 1) = 1 then ((M : ℝ) ^ 2)⁻¹ else 0) ≤
        (if x (a + i + 1) = 1 then
          ((activeCount x (a + i + 1) : ℝ) * ((activeCount x (a + i + 1) : ℝ) - 1))⁻¹
          else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    split_ifs with hup
    · have h2 := activeCount_ge_two_of_up x hs (show a + i < n by omega) hup
      have hS : (activeCount x (a + i + 1) : ℝ) ≤ M := by exact_mod_cast hM _ (by omega)
      apply inv_anti₀ (by nlinarith)
      nlinarith
    · exact le_rfl
  have hcount :
      (∑ i ∈ Finset.range m, (if x (a + i + 1) = 1 then ((M : ℝ) ^ 2)⁻¹ else 0)) =
        ((upSteps x a (a + m)).card : ℝ) * ((M : ℝ) ^ 2)⁻¹ :=
    sum_up_indicator x a m _
  have htwice := twice_upSteps_card x hx (Nat.le_add_right a m)
  have hSend := hs (a + m) ham
  have hSa := hM a (by omega)
  have hcard : ((m : ℝ) + 1 - M) ≤ 2 * ((upSteps x a (a + m)).card : ℝ) := by
    have : ((m : ℤ) + 1 - M) ≤ 2 * ((upSteps x a (a + m)).card : ℤ) := by
      push_cast at htwice
      omega
    exact_mod_cast this
  have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  calc
    _ ≤ ((upSteps x a (a + m)).card : ℝ) * ((M : ℝ) ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : ((upSteps x a (a + m)).card : ℝ) * ((M : ℝ) ^ 2)⁻¹ * (2 * (M : ℝ) ^ 2) =
          2 * ((upSteps x a (a + m)).card : ℝ) := by
        field_simp
      linarith
    _ = _ := hcount.symm
    _ ≤ coalescenceUpSum x a m := Finset.sum_le_sum hterm

/-- Exponential tail of one pair's coalescence delay under bounded population. -/
theorem coalescence_gap_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n M K : ℕ}
    (hs : SurvivesThrough x n) (hM : ∀ k ≤ n, activeCount x k ≤ M) (hK : 1 ≤ K)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ Freezing1.vertexLabels (companionSchedule x) n)
    (hv : v ∈ Freezing1.vertexLabels (companionSchedule x) n) :
    (jointLaw (companionSchedule x) n).real
      {ω | K ≤ commonBirth n u v - coalescenceTime n u v ω} ≤
        Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) := by
  have hpos := (Real.exp_pos (-(((K : ℝ) - M) / (M : ℝ) ^ 2))).le
  by_cases huv : u = v
  · subst v
    have he : {ω : History | K ≤ commonBirth n u u - coalescenceTime n u u ω} = ∅ := by
      ext ω
      simp only [coalescenceTime_self, commonBirth, min_self, Nat.sub_self,
        Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      omega
    rw [he, measureReal_empty]
    exact hpos
  by_cases hKB : commonBirth n u v < K
  · have he : {ω : History | K ≤ commonBirth n u v - coalescenceTime n u v ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      omega
    rw [he, measureReal_empty]
    exact hpos
  have hn := (companion_before_extinction x hx hs).le
  have hBn := commonBirth_le_horizon (v := v) hu
  set B := commonBirth n u v with hB
  have hab : B - K + 1 + (K - 1) = B := by omega
  have hsub : {ω : History | K ≤ B - coalescenceTime n u v ω} ⊆
      {ω | coalescenceTime n u v ω < B - K + 1} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    omega
  have hlow := coalescenceUpSum_ge_of_bounded x hx (a := B - K + 1) (m := K - 1) hs
    (by omega) hM
  have hKm : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    rw [Nat.cast_sub hK]
    ring
  rw [hKm] at hlow
  calc
    _ ≤ (jointLaw (companionSchedule x) n).real
        {ω | coalescenceTime n u v ω < B - K + 1} := measureReal_mono hsub
    _ = ∏ j ∈ Finset.Ioc (B - K + 1) B, (1 - coalescenceHazard (companionSchedule x) j) :=
      coalescenceTime_lt_probability hn hu hv huv (by omega)
    _ ≤ Real.exp (-2 * coalescenceUpSum x (B - K + 1) (K - 1)) := by
      have h := companion_survival_product_le_exp x hx hs (a := B - K + 1) (m := K - 1)
        (by omega)
      rwa [hab] at h
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hM1 : (1 : ℝ) ≤ M := by
        have h := hM 0 (Nat.zero_le n)
        rw [activeCount_zero] at h
        exact_mod_cast h
      have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      have : ((K : ℝ) - M) / (M : ℝ) ^ 2 = 2 * (((K : ℝ) - M) / (2 * (M : ℝ) ^ 2)) := by
        field_simp
      rw [this]
      linarith

/-- Some ordered pair of labels has coalescence delay at least `K`. -/
def slowGapEvent (x : Freezing1.SignSequence) (n K : ℕ) : Set History :=
  ⋃ p ∈ Freezing1.vertexLabels x n ×ˢ Freezing1.vertexLabels x n,
    {ω | K ≤ commonBirth n p.1 p.2 - coalescenceTime n p.1 p.2 ω}

/-- Union bound over the at most `(n+1)^2` ordered pairs of labels. -/
theorem slowGapEvent_probability_le (x : ℕ → ℤ) (hx : IsSigned x) {n M K : ℕ}
    (hs : SurvivesThrough x n) (hM : ∀ k ≤ n, activeCount x k ≤ M) (hK : 1 ≤ K) :
    (jointLaw (companionSchedule x) n).real (slowGapEvent (companionSchedule x) n K) ≤
      ((n : ℝ) + 1) ^ 2 * Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) := by
  set L := Freezing1.vertexLabels (companionSchedule x) n
  have hL : (L.card : ℝ) ≤ (n : ℝ) + 1 := by
    have h0 : 0 ≤ Freezing1.activeCount (companionSchedule x) n := by
      rw [companion_activeCount x hx]
      exact (hs n le_rfl).le
    have h : L.card = _ := Freezing1.card_vertexLabels h0
    have h' := Freezing1.plusCount_le (companionSchedule x) n
    have : L.card ≤ n + 1 := by omega
    exact_mod_cast this
  have hpos := (Real.exp_pos (-(((K : ℝ) - M) / (M : ℝ) ^ 2))).le
  calc
    _ ≤ ∑ p ∈ L ×ˢ L, (jointLaw (companionSchedule x) n).real
        {ω | K ≤ commonBirth n p.1 p.2 - coalescenceTime n p.1 p.2 ω} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ L ×ˢ L, Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      exact coalescence_gap_probability_le x hx hs hM hK h1 h2
    _ = ((L ×ˢ L).card : ℝ) * Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hpos
      rw [Finset.card_product, Nat.cast_mul, sq]
      exact mul_le_mul hL hL (Nat.cast_nonneg _) (by positivity)

/-! ### Transport of the branching-excess event -/

/-- Some pair of terminal reverse vertices has root-relative branching excess above `D`. -/
def reverseExcessEvent (D : ℝ) : Set Freezing1.Reverse.Forest :=
  {F | ∃ r ∈ F.roots, ∃ u ∈ F.vertices, ∃ v ∈ F.vertices,
    D < (F.graph.dist u v : ℝ) - |(F.graph.dist r u : ℝ) - F.graph.dist r v|}

/-- A large terminal branching excess forces a long coalescence delay. -/
theorem jointLaw_reverseExcess_le_slowGap {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) {D : ℝ} {K : ℕ}
    (hDK : 2 * ((K : ℝ) - 1) ≤ D) :
    (jointLaw x n).real {ω | ω n ∈ reverseExcessEvent D} ≤
      (jointLaw x n).real (slowGapEvent x n K) := by
  have hall : ∀ᵐ ω ∂jointLaw x n, ∀ u v, u ∈ Freezing1.vertexLabels x n →
      v ∈ Freezing1.vertexLabels x n → ∀ r ∈ (ω n).roots,
        ((ω n).graph.dist u v : ℝ) - |((ω n).graph.dist r u : ℝ) - (ω n).graph.dist r v| ≤
          2 * ((commonBirth n u v - coalescenceTime n u v ω : ℕ) : ℝ) := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    by_cases hu : u ∈ Freezing1.vertexLabels x n
    · by_cases hv : v ∈ Freezing1.vertexLabels x n
      · exact (jointLaw_excess_le_gap hn hu hv).mono fun _ h _ _ ↦ h
      · exact Eventually.of_forall fun _ _ h ↦ (hv h).elim
    · exact Eventually.of_forall fun _ h ↦ (hu h).elim
  have hsub : {ω : History | ω n ∈ reverseExcessEvent D} ≤ᵐ[jointLaw x n]
      slowGapEvent x n K := by
    filter_upwards [hall, jointLaw_forestAt_valid x n hn] with ω hω hvalid
    rintro ⟨r, hr, u, hu, v, hv, hlt⟩
    have hV : (ω n).vertices = Freezing1.vertexLabels x n := by
      simpa [forestAt, Freezing1.Reverse.phaseLabels_zero] using
        (hvalid 0 (Nat.zero_le n)).vertices_eq
    rw [hV] at hu hv
    have hle := hω u v hu hv r hr
    simp only [slowGapEvent, Set.mem_iUnion]
    refine ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, ?_⟩
    have hreal : (K : ℝ) < ((commonBirth n u v - coalescenceTime n u v ω : ℕ) : ℝ) + 1 := by
      linarith
    have hnat : K < commonBirth n u v - coalescenceTime n u v ω + 1 := by exact_mod_cast hreal
    change K ≤ commonBirth n u v - coalescenceTime n u v ω
    omega
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

/-- Some pair of forward vertices has root-relative branching excess above `D`. -/
def forwardExcessEvent (D : ℝ) : Set Freezing1.Forward.State :=
  {s | ∃ u ∈ s.vertices, ∃ v ∈ s.vertices,
    D < (s.graph.dist u v : ℝ) - |(s.height u : ℝ) - s.height v|}

/-- The canonical forward/reverse identification transports the excess event. -/
theorem forwardExcessEvent_le_reverse (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (D : ℝ) :
    (Freezing1.Forward.treeLaw x n).real (forwardExcessEvent D) ≤
      (jointLaw x n).real {ω | ω n ∈ reverseExcessEvent D} := by
  have hrev : Freezing1.Reverse.treeLaw x n = (jointLaw x n).map (fun ω ↦ ω n) := by
    rw [jointLaw_map_eval]
    rfl
  have h : (Freezing1.Forward.treeLaw x n) (forwardExcessEvent D) ≤
      (Freezing1.Reverse.treeLaw x n) (reverseExcessEvent D) := by
    rw [← ReverseStamped.forward_reverse_same_law x n hn,
      Measure.map_apply measurable_from_top (MeasurableSet.of_discrete),
      ← Freezing1.ReverseStamped.map_treeLaw,
      Measure.map_apply measurable_from_top (MeasurableSet.of_discrete)]
    apply measure_mono_ae
    filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
      Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
      ReverseStamped.treeLaw_canonicalOrder x n hn] with F hF ht ho
    have hF' : Freezing1.Reverse.ValidAt x n 0 F.forest := by
      simpa only [Nat.sub_self] using hF
    rintro ⟨u', hu', v', hv', hlt⟩
    have hvalid := ForwardHistory.state_valid x (ReverseStamped.canonicalHistory x n F)
    change Freezing1.Forward.ValidAt (ReverseStamped.canonicalHistory x n F).length
      (ReverseStamped.canonicalForwardState x n F) at hvalid
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (ReverseStamped.one_root_of_terminal_valid hF')
    have hrmem : r ∈ F.forest.roots := by
      rw [hr]
      exact Finset.mem_singleton_self r
    have hu'' := hu'
    have hv'' := hv'
    rw [ReverseStamped.canonicalForwardState_vertices hF' ht ho] at hu' hv'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hv'
    refine ⟨r, hrmem, u, hu, v, hv, ?_⟩
    rw [hvalid.height_eq_dist _ hu'', hvalid.height_eq_dist _ hv'',
      ReverseStamped.canonicalForwardState_root_dist hF' ht ho hrmem hu,
      ReverseStamped.canonicalForwardState_root_dist hF' ht ho hrmem hv,
      ReverseStamped.canonicalForwardState_graph_dist hF' ht ho hu hv] at hlt
    exact hlt
  rw [hrev, Measure.map_apply (measurable_pi_apply n) (MeasurableSet.of_discrete)] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

/-! ### Linear growth of the height scale -/

/-- With population at most `M`, the height scale grows at least linearly. -/
theorem heightScale_ge_of_bounded (x : ℕ → ℤ) (hx : IsSigned x) {n M : ℕ}
    (hs : SurvivesThrough x n) (hM : ∀ k ≤ n, activeCount x k ≤ M) :
    (n : ℝ) / (2 * M) ≤ Freezing1.heightScale (companionSchedule x) n := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 (Nat.zero_le n)
    rw [activeCount_zero] at h
    exact_mod_cast h
  rw [companion_heightScale x hx n]
  have hterm : ∀ i ∈ Finset.range n,
      (if x (0 + i + 1) = 1 then (M : ℝ)⁻¹ else 0) ≤
        (if x (0 + i + 1) = 1 then (activeCount x (0 + i + 1) : ℝ)⁻¹ else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    split_ifs
    · have hpos : (0 : ℝ) < activeCount x (0 + i + 1) := by
        exact_mod_cast hs _ (by omega)
      have hS : (activeCount x (0 + i + 1) : ℝ) ≤ M := by exact_mod_cast hM _ (by omega)
      exact inv_anti₀ hpos hS
    · exact le_rfl
  have htwice := twice_upSteps_card x hx (Nat.zero_le n)
  have hSn := hs n le_rfl
  have hcard : (n : ℝ) ≤ 2 * ((upSteps x 0 (0 + n)).card : ℝ) := by
    have : (n : ℤ) ≤ 2 * ((upSteps x 0 (0 + n)).card : ℤ) := by
      simp only [Nat.zero_add] at htwice ⊢
      simp only [activeCount_zero, Nat.cast_zero, sub_zero] at htwice
      omega
    exact_mod_cast this
  calc
    _ ≤ ((upSteps x 0 (0 + n)).card : ℝ) * (M : ℝ)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : ((upSteps x 0 (0 + n)).card : ℝ) * (M : ℝ)⁻¹ * (2 * (M : ℝ)) =
          2 * ((upSteps x 0 (0 + n)).card : ℝ) := by
        field_simp
      linarith
    _ = _ := (sum_up_indicator x 0 n _).symm
    _ ≤ harmonicUpInterval x 0 n := Finset.sum_le_sum hterm

/-- Quadratic prefactors are negligible against a linear exponential rate. -/
theorem tendsto_sq_mul_exp_neg_linear {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * Real.exp (-(b * n))) atTop (𝓝 0) := by
  have hr : |Real.exp (-b)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h1 := (tendsto_add_atTop_iff_nat 1).mpr
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr)
  have h2 := h1.const_mul (Real.exp b)
  rw [mul_zero] at h2
  refine h2.congr fun n ↦ ?_
  rw [← Real.exp_nat_mul]
  push_cast
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/-- Logarithms are negligible against the linearly growing height scale. -/
theorem tendsto_log_div_heightScale_of_bounded {y : ℕ → ℕ → ℤ}
    (hy : ∀ n : ℕ, 0 < n → IsSigned (y n) ∧ SurvivesThrough (y n) n) {M : ℕ}
    (hM : ∀ n k : ℕ, k ≤ n → activeCount (y n) k ≤ M) :
    Tendsto (fun n : ℕ ↦ Real.log n / Freezing1.heightScale (companionSchedule (y n)) n)
      atTop (𝓝 0) := by
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  have hlog : Tendsto (fun n : ℕ ↦ 2 * M * (Real.log n / n)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have h' := h.const_mul (2 * (M : ℝ))
    rw [mul_zero] at h'
    refine h'.congr fun n ↦ ?_
    simp
  apply squeeze_zero' _ _ hlog
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := heightScale_ge_of_bounded (y n) (hy n hn).1 (hy n hn).2 (hM n)
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn))
      ((by positivity : (0 : ℝ) ≤ n / (2 * M)).trans hh)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hh := heightScale_ge_of_bounded (y n) (hy n hn).1 (hy n hn).2 (hM n)
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    calc
      _ ≤ Real.log n / ((n : ℝ) / (2 * M)) :=
        div_le_div_of_nonneg_left hlogn (by positivity) hh
      _ = _ := by
        field_simp

/-! ### The main theorem -/

/-- **N09 (`thm:alpha0`).** With uniformly bounded population, the forward trees rescaled
by `1 / h_n^+` converge in probability to the unit segment for the Gromov–Hausdorff
distance. -/
theorem bounded_population_GH_limit {x : ℕ → ℕ → ℤ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hM : ∃ M : ℕ, ∀ n k : ℕ, k ≤ n → activeCount (x n) k ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (freezingTreeLaw x n).real {s | ε < dist
      (underlyingGH (toMeasuredGHSpace
        (forwardMeasuredSpace (1 / Freezing1.heightScale (companionSchedule (x n)) n) s)))
      (GromovHausdorff.toGHSpace unitInterval)}) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hM
  have hM1 : (1 : ℝ) ≤ M := by
    have h := hM 0 0 le_rfl
    rw [activeCount_zero] at h
    exact_mod_cast h
  set h : ℕ → ℝ := fun n ↦ Freezing1.heightScale (companionSchedule (x n)) n with hh
  have hlower : ∀ n : ℕ, 0 < n → (n : ℝ) / (2 * M) ≤ h n := fun n hn ↦
    heightScale_ge_of_bounded (x n) (hx n hn).1 (hx n hn).2 (hM n)
  -- Height concentration.
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
  have hheight : Tendsto (fun n ↦ (freezingTreeLaw x n).real
      {s | ε / 8 ≤ |(Freezing1.Forward.treeHeight s : ℝ) / h n - 1|}) atTop (𝓝 0) := by
    have hτ (n : ℕ) : (n : ℕ∞) < Freezing1.extinctionTime (companionSchedule (y n)) :=
      companion_before_extinction (y n) (hy n).1 (hy n).2
    have hlog := tendsto_log_div_heightScale_of_bounded (y := y)
      (fun n _ ↦ hy n) hyM
    have h0 := Freezing1.maximum_height_deviation_tendsto_zero
      (fun n ↦ companionSchedule (y n)) hτ hlog (show 0 < ε / 8 by positivity)
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
    rw [ENNReal.toReal_zero] at h1
    apply h1.congr'
    filter_upwards [initialRowExtension_eventually_eq x] with n hn
    simp only [Function.comp_apply, hh, freezingTreeLaw, ← hn, hydef]
    rfl
  -- Excess control through the reverse coalescence estimate.
  set b : ℝ := ε / (16 * (M : ℝ) ^ 3) with hb
  have hbpos : 0 < b := by positivity
  have hexc : Tendsto (fun n ↦ (freezingTreeLaw x n).real
      (forwardExcessEvent (ε * h n / 2))) atTop (𝓝 0) := by
    have hlim := (tendsto_sq_mul_exp_neg_linear hbpos).const_mul (Real.exp (1 / (M : ℝ)))
    rw [mul_zero] at hlim
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsx := (hx n hn).2
    have hτ := (companion_before_extinction (x n) (hx n hn).1 hsx).le
    set D := ε * h n / 2 with hD
    have hDpos : 0 ≤ D := by
      have := hlower n hn
      have : (0 : ℝ) ≤ h n := (by positivity : (0 : ℝ) ≤ n / (2 * M)).trans this
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
      have hl := hlower n hn
      have hMpos : (0 : ℝ) < M := by linarith
      have hK' : ε * n / (8 * M) ≤ K := by
        have : ε * ((n : ℝ) / (2 * M)) ≤ ε * h n := mul_le_mul_of_nonneg_left hl hε.le
        have e : ε * ((n : ℝ) / (2 * M)) / 4 = ε * n / (8 * M) := by
          field_simp
          ring
        linarith
      have e1 : ((K : ℝ) - M) / (M : ℝ) ^ 2 = (K : ℝ) / (M : ℝ) ^ 2 - 1 / M := by
        field_simp
      have e2 : b * n = (ε * n / (8 * M)) / (M : ℝ) ^ 2 / 2 := by
        rw [hb]
        field_simp
        ring
      rw [e1, e2]
      have : (ε * n / (8 * M)) / (M : ℝ) ^ 2 ≤ (K : ℝ) / (M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hK' (by positivity)
      have hnn : 0 ≤ (ε * n / (8 * M)) / (M : ℝ) ^ 2 := by positivity
      linarith
    calc
      _ ≤ (jointLaw (companionSchedule (x n)) n).real {ω | ω n ∈ reverseExcessEvent D} :=
        forwardExcessEvent_le_reverse _ n hτ D
      _ ≤ (jointLaw (companionSchedule (x n)) n).real
          (slowGapEvent (companionSchedule (x n)) n K) :=
        jointLaw_reverseExcess_le_slowGap hτ hDK
      _ ≤ ((n : ℝ) + 1) ^ 2 * Real.exp (-(((K : ℝ) - M) / (M : ℝ) ^ 2)) :=
        slowGapEvent_probability_le (x n) (hx n hn).1 hsx (hM n) hK1
      _ ≤ ((n : ℝ) + 1) ^ 2 * (Real.exp (1 / (M : ℝ)) * Real.exp (-(b * n))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  -- Deterministic reduction.
  have hsum := hexc.add hheight
  rw [add_zero] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hsum
  have hlarge : ∀ᶠ n : ℕ in atTop, 8 * M / ε ≤ n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop 0, hlarge] with n hn hnl
  have hl := hlower n hn
  have hMpos : (0 : ℝ) < M := by linarith
  have hhpos : 0 < h n := by
    have : (0 : ℝ) < n / (2 * M) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    linarith
  have hsmall : 1 / h n ≤ ε / 4 := by
    rw [div_le_iff₀ hhpos]
    have : (n : ℝ) / (2 * M) * ε ≥ 4 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have := (div_le_iff₀ hε).mp hnl
      nlinarith
    nlinarith
  have hsub : {s | ε < dist (underlyingGH (toMeasuredGHSpace
        (forwardMeasuredSpace (1 / h n) s))) (toGHSpace unitInterval)} ≤ᵐ[freezingTreeLaw x n]
      forwardExcessEvent (ε * h n / 2) ∪
        {s | ε / 8 ≤ |(Freezing1.Forward.treeHeight s : ℝ) / h n - 1|} := by
    filter_upwards [freezingTreeLaw_valid x n] with s hs
    intro hbad
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨hnexc, hnh⟩ := hnot
    have hD : ∀ u ∈ s.vertices, ∀ v ∈ s.vertices,
        (s.graph.dist u v : ℝ) - |(s.height u : ℝ) - s.height v| ≤ ε * h n / 2 := by
      intro u hu v hv
      by_contra hlt
      exact hnexc ⟨u, hu, v, hv, lt_of_not_ge hlt⟩
    have hhn : |(Freezing1.Forward.treeHeight s : ℝ) / h n - 1| < ε / 8 :=
      lt_of_not_ge hnh
    have hbound := forward_dist_unitInterval_le hs (one_div_pos.mpr hhpos) hD
    have e1 : 1 / h n * (ε * h n / 2) / 2 = ε / 4 := by
      field_simp
      ring
    have e2 : 1 / h n * (Freezing1.Forward.treeHeight s : ℝ) =
        (Freezing1.Forward.treeHeight s : ℝ) / h n := by
      rw [one_div_mul_eq_div]
    rw [e1, e2] at hbound
    change ε < dist _ _ at hbad
    linarith
  calc
    _ ≤ (freezingTreeLaw x n).real (forwardExcessEvent (ε * h n / 2) ∪
        {s | ε / 8 ≤ |(Freezing1.Forward.treeHeight s : ℝ) / h n - 1|}) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ ≤ _ := measureReal_union_le _ _

end Freezing2
