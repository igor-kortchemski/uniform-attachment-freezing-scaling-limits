module

public import Freezing2.Probability.ReverseObservations

/-!
# The sampled history follows the edge-labelling construction

The observation bridge is tied to the actual trajectory: it starts with an
edgeless graph, each attachment step adds the edge between two distinct roots,
and each freezing step leaves the graph unchanged. Consequently the replayed
edge labels implement the source's step labels on the sampled history.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseHistory

/-- The graph action of one legal source step. Vertex insertion on freezing
steps is already recorded by the deterministic valid phase-label set. -/
def GraphStep (up : Bool) (F G : Forest) : Prop :=
  if up then ∃ a b, a ∈ F.roots ∧ b ∈ F.roots ∧ a ≠ b ∧
    G.graph = F.graph ⊔ SimpleGraph.edge a b
  else G.graph = F.graph

theorem measurable_graph_relation (g : Forest → SimpleGraph (ℕ ⊕ ℕ)) :
    Measurable (fun p : Forest × Forest ↦ p.2.graph = g p.1) := by
  have he : (fun p : Forest × Forest ↦ p.2.graph = g p.1) =
      fun p ↦ ∀ u v, p.2.graph.Adj u v ↔ (g p.1).Adj u v := by
    funext p
    apply propext
    constructor
    · intro h
      simp only [h, iff_self, implies_true]
    · intro h
      ext u v
      exact h u v
  rw [he]
  exact Measurable.forall fun u ↦ Measurable.forall fun v ↦
    ((show Measurable (fun F : Forest ↦ F.graph.Adj u v) from measurable_from_top).comp
      measurable_snd).iff
      ((show Measurable (fun F : Forest ↦ (g F).Adj u v) from measurable_from_top).comp
        measurable_fst)

theorem measurable_graphStep (up : Bool) :
    Measurable (fun p : Forest × Forest ↦ GraphStep up p.1 p.2) := by
  cases up
  · exact measurable_graph_relation (fun F ↦ F.graph)
  · apply Measurable.exists
    intro a
    apply Measurable.exists
    intro b
    exact ((show Measurable (fun F : Forest ↦ a ∈ F.roots) from measurable_from_top).comp
      measurable_fst).and
      (((show Measurable (fun F : Forest ↦ b ∈ F.roots) from measurable_from_top).comp
        measurable_fst).and
        (measurable_const.and (measurable_graph_relation
          (fun F ↦ F.graph ⊔ SimpleGraph.edge a b))))

theorem transitionLaw_ae_graphStep {x : Freezing1.SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : i < n)
    (hF : Freezing1.Reverse.ValidAt x n (i + 1) F) :
    ∀ᵐ G ∂Freezing1.Reverse.transitionLaw x i F, GraphStep (x (i + 1)) F G := by
  cases hx : x (i + 1)
  · simp only [Freezing1.Reverse.transitionLaw, hx, Bool.false_eq_true, ite_false]
    apply (ae_dirac_iff (by trivial)).mpr
    change (Freezing1.Reverse.insertLabel F i).graph = F.graph
    unfold Freezing1.Reverse.insertLabel
    split_ifs with h
    · rfl
    · exact F.adjoin_graph h
  · have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ Freezing1.extinctionTime x :=
      le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast Nat.succ_le_of_lt hi) hn
    have htwo : 2 ≤ F.roots.card := by
      rw [hF.roots_card]
      exact Freezing1.two_le_activeCount_toNat_succ_of_attachment hiτ hx
    simp only [Freezing1.Reverse.transitionLaw, hx, ite_true]
    apply F.joinLaw_ae htwo
    intro p hp
    simp only [Freezing1.RootedForest.joinChoice, dite_eq_left hp]
    exact ⟨p.1, p.2, (Finset.mem_offDiag.mp hp).1, (Finset.mem_offDiag.mp hp).2.1,
      (Finset.mem_offDiag.mp hp).2.2, F.join_graph _ _ _⟩

/-- The actual sampled transition has precisely the graph action used to
reconstruct the source edge labels. -/
theorem jointLaw_ae_graphStep {x : Freezing1.SignSequence} {n k : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hk : k < n) :
    ∀ᵐ ω ∂jointLaw x n, GraphStep (x (n - k)) (ω k) (ω (k + 1)) := by
  have ht : n - (k + 1) + 1 = n - k := by omega
  have hkn : n - (k + 1) < n := by omega
  apply jointLaw_ae_transition x n k (measurable_graphStep (x (n - k))).setOf
  filter_upwards [jointLaw_valid x n hn] with ω hω
  have hF : Freezing1.Reverse.ValidAt x n (n - (k + 1) + 1) (ω k) := by
    simpa only [ht] using hω k hk.le
  have hs := transitionLaw_ae_graphStep hn hkn hF
  have hp := (mem_ae_iff_prob_eq_one (show MeasurableSet
    {G : Forest | GraphStep (x (n - (k + 1) + 1)) (ω k) G} from by trivial)).mp hs
  simpa only [stepKernel, Kernel.coe_mk, hk, ite_true, ht] using hp

/-- All source steps satisfy the graph construction simultaneously. -/
theorem jointLaw_ae_graphSteps {x : Freezing1.SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ ω ∂jointLaw x n, ∀ k < n, GraphStep (x (n - k)) (ω k) (ω (k + 1)) := by
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k < n
  · exact (jointLaw_ae_graphStep hn hk).mono fun _ h _ ↦ h
  · exact Eventually.of_forall fun _ h ↦ (hk h).elim

theorem jointLaw_ae_initial (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, ω 0 = Freezing1.Reverse.initial x n := by
  have h : ∀ᵐ F ∂(jointLaw x n).map (fun ω ↦ ω 0),
      F = Freezing1.Reverse.initial x n := by
    rw [jointLaw_map_zero]
    exact (ae_dirac_iff (by trivial)).mpr rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h

theorem jointLaw_ae_initial_graph (x : Freezing1.SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂jointLaw x n, (ω 0).graph = ⊥ := by
  filter_upwards [jointLaw_ae_initial x n] with ω hω
  simp only [hω, Freezing1.Reverse.initial, Freezing1.RootedForest.isolated_graph]

/-- Graph-step support implies that the new joining edge receives exactly
its source index, without assuming equality of hidden forest fields. -/
theorem edgeLabelAt_graphJoin (n k : ℕ) (ω : History) {a b : ℕ ⊕ ℕ}
    (ha : a ∈ (ω k).roots) (hb : b ∈ (ω k).roots) (hab : a ≠ b)
    (hgraph : (ω (k + 1)).graph = (ω k).graph ⊔ SimpleGraph.edge a b) :
    edgeLabelAt n (k + 1) ω a b = n - k := by
  apply edgeLabelAt_newEdge
  · rw [hgraph]
    simp [SimpleGraph.edge_adj, hab]
  · exact fun hadj ↦ (ω k).not_reachable_roots ha hb hab hadj.reachable

end Freezing2.ReverseHistory
