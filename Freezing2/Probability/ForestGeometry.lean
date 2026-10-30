module

public import Freezing2.Discrete.ForestDistances
public import Freezing2.Probability.CoalescenceTransition
public import Freezing2.Probability.ReverseConditional

/-!
# Graph geometry of reverse transitions

The actual reverse process only adds edges. Its acyclic states therefore keep
all distances between already connected vertices. A newly coalescing pair has
distance equal to the sum of its heights just after the merge.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Freezing2.ForestGeometry

open Freezing1

variable {V : Type*} [DecidableEq V]

theorem joinChoice_graph_le (F : RootedForest V) (p : V × V) :
    F.graph ≤ (F.joinChoice p).graph := by
  unfold RootedForest.joinChoice
  split_ifs with hp
  · rw [RootedForest.join_graph]
    exact le_sup_left
  · exact le_rfl

/-- The first merger joins the two old root paths through exactly one new edge. -/
theorem joinChoice_new_connection_distance (F : RootedForest V) (hF : F.graph.IsAcyclic)
    {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (hne : F.root u ≠ F.root v) (p : V × V)
    (hnew : (F.joinChoice p).root u = (F.joinChoice p).root v) :
    (F.joinChoice p).graph.dist u v = (F.joinChoice p).depth u + (F.joinChoice p).depth v := by
  by_cases hp : p ∈ F.roots.offDiag
  · obtain he | he := (ForestCoalescence.joinChoice_root_eq_iff F hp hne).mp hnew
    · subst p
      simpa [RootedForest.joinChoice, hp, RootedForest.join_depth, hne, Nat.add_assoc] using
        join_cross_distance F hF hu hv hne
    · subst p
      have hd := join_cross_distance F hF hv hu hne.symm
      rw [SimpleGraph.dist_comm] at hd
      simpa [RootedForest.joinChoice, hp, RootedForest.join_depth, hne.symm,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd
  · simp only [RootedForest.joinChoice, dite_eq_right hp] at hnew
    exact (hne hnew).elim

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

theorem joinLaw_ae_graph_le (F : RootedForest V) : ∀ᵐ G ∂F.joinLaw, F.graph ≤ G.graph := by
  by_cases hF : 2 ≤ F.roots.card
  · exact F.joinLaw_ae hF _ fun p _ ↦ joinChoice_graph_le F p
  · simp only [RootedForest.joinLaw, ite_eq_right hF]
    simp

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- Countably many edge coordinates suffice for measurability; the product of
forest state spaces is not assumed discrete. -/
theorem measurableSet_graph_le :
    MeasurableSet {p : RootedForest V × RootedForest V | p.1.graph ≤ p.2.graph} := by
  have hm (u v : V) : Measurable (fun F : RootedForest V ↦ F.graph.Adj u v) :=
    measurable_from_top
  exact (Measurable.forall fun u ↦ Measurable.forall fun v ↦
    ((hm u v).comp measurable_fst).imp ((hm u v).comp measurable_snd)).setOf

/-- Inserting a prescribed frozen label adds no edges. -/
theorem insertLabel_graph (F : Reverse.Forest) (i : ℕ) :
    (Reverse.insertLabel F i).graph = F.graph := by
  unfold Reverse.insertLabel
  split_ifs with h
  · rfl
  · exact RootedForest.adjoin_graph F h

theorem transitionLaw_ae_graph_le (x : SignSequence) (i : ℕ) (F : Reverse.Forest) :
    ∀ᵐ G ∂Reverse.transitionLaw x i F, F.graph ≤ G.graph := by
  unfold Reverse.transitionLaw
  split_ifs
  · exact joinLaw_ae_graph_le F
  · simp [insertLabel_graph]

/-- Every successive sampled state contains the graph of its predecessor,
including the deterministic continuation after the finite horizon. -/
theorem jointLaw_graph_mono (x : SignSequence) (n : ℕ) :
    ∀ᵐ ω ∂ReverseHistory.jointLaw x n, Monotone (fun k ↦ (ω k).graph) := by
  have hstep (k : ℕ) : ∀ᵐ ω ∂ReverseHistory.jointLaw x n,
      (ω k).graph ≤ (ω (k + 1)).graph := by
    apply ReverseHistory.jointLaw_ae_transition x n k measurableSet_graph_le
    apply Eventually.of_forall
    intro ω
    apply (ae_iff_prob_eq_one measurable_from_top).mp
    change ∀ᵐ G ∂(if k < n then Reverse.transitionLaw x (n - (k + 1)) (ω k)
      else Measure.dirac (ω k)), (ω k).graph ≤ G.graph
    split_ifs
    · exact transitionLaw_ae_graph_le x _ _
    · simp
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  exact monotone_nat_of_le_succ hω

/-- Later reverse growth preserves graph distance between vertices that were
already connected. All acyclicity premises come from the actual history law. -/
theorem jointLaw_dist_preserved (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ ω ∂ReverseHistory.jointLaw x n, ∀ k l : ℕ, k ≤ l → l ≤ n →
      ∀ u v : ℕ ⊕ ℕ, (ω k).graph.Reachable u v →
        (ω l).graph.dist u v = (ω k).graph.dist u v := by
  filter_upwards [jointLaw_graph_mono x n, ReverseHistory.jointLaw_valid x n hn]
    with ω hmono hvalid
  intro k l hkl hln u v huv
  exact dist_eq_of_acyclic_supergraph (hmono hkl) (hvalid l hln).acyclic huv

/-- The metric assertion for pairs that coalesce in a single transition. -/
def NewConnectionDistance (F G : RootedForest V) : Prop :=
  ∀ u ∈ F.vertices, ∀ v ∈ F.vertices, F.root u ≠ F.root v → G.root u = G.root v →
    G.graph.dist u v = G.depth u + G.depth v

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem measurableSet_newConnectionDistance :
    MeasurableSet {p : RootedForest V × RootedForest V | NewConnectionDistance p.1 p.2} := by
  have ho (u v : V) : Measurable (fun F : RootedForest V ↦
      u ∈ F.vertices ∧ v ∈ F.vertices ∧ F.root u ≠ F.root v) := measurable_from_top
  have hn (u v : V) : Measurable (fun G : RootedForest V ↦
      G.root u = G.root v → G.graph.dist u v = G.depth u + G.depth v) := measurable_from_top
  have he : {p : RootedForest V × RootedForest V | NewConnectionDistance p.1 p.2} =
      {p | ∀ u v, (u ∈ p.1.vertices ∧ v ∈ p.1.vertices ∧ p.1.root u ≠ p.1.root v) →
        (p.2.root u = p.2.root v → p.2.graph.dist u v = p.2.depth u + p.2.depth v)} := by
    ext p
    simp only [NewConnectionDistance, Set.mem_ofPred_eq]
    aesop
  rw [he]
  exact (Measurable.forall fun u ↦ Measurable.forall fun v ↦
    ((ho u v).comp measurable_fst).imp ((hn u v).comp measurable_snd)).setOf

theorem joinLaw_ae_newConnectionDistance (F : RootedForest V) (hF : F.graph.IsAcyclic) :
    ∀ᵐ G ∂F.joinLaw, NewConnectionDistance F G := by
  by_cases htwo : 2 ≤ F.roots.card
  · apply F.joinLaw_ae htwo
    intro p _ u hu v hv hne hnew
    exact joinChoice_new_connection_distance F hF hu hv hne p hnew
  · simp only [RootedForest.joinLaw, ite_eq_right htwo]
    apply (ae_dirac_iff (by trivial)).mpr
    intro u hu v hv hne hnew
    exact (hne hnew).elim

theorem transitionLaw_ae_newConnectionDistance (x : SignSequence) (i : ℕ)
    (F : Reverse.Forest) (hF : F.graph.IsAcyclic) :
    ∀ᵐ G ∂Reverse.transitionLaw x i F, NewConnectionDistance F G := by
  unfold Reverse.transitionLaw
  split_ifs
  · exact joinLaw_ae_newConnectionDistance F hF
  · apply (ae_dirac_iff (by trivial)).mpr
    intro u hu v hv hne hnew
    rw [ForestCoalescence.insertLabel_root_old F i hu,
      ForestCoalescence.insertLabel_root_old F i hv] at hnew
    exact (hne hnew).elim

/-- At every actual merger, the graph distance is the sum of the two resulting
heights. This event is proved simultaneously for all times and vertex pairs. -/
theorem jointLaw_new_connection_distance (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ ω ∂ReverseHistory.jointLaw x n, ∀ k < n, NewConnectionDistance (ω k) (ω (k + 1)) := by
  apply ae_all_iff.mpr
  intro k
  by_cases hk : k < n
  · have hs : ∀ᵐ ω ∂ReverseHistory.jointLaw x n,
        NewConnectionDistance (ω k) (ω (k + 1)) := by
      apply ReverseHistory.jointLaw_ae_transition x n k measurableSet_newConnectionDistance
      filter_upwards [ReverseHistory.jointLaw_valid x n hn] with ω hvalid
      change (if k < n then Reverse.transitionLaw x (n - (k + 1)) (ω k)
        else Measure.dirac (ω k)) {G | NewConnectionDistance (ω k) G} = 1
      rw [ite_eq_left hk]
      exact (ae_iff_prob_eq_one measurable_from_top).mp
        (transitionLaw_ae_newConnectionDistance x _ _ (hvalid k hk.le).acyclic)
    exact hs.mono fun _ h _ ↦ h
  · exact Eventually.of_forall fun _ h ↦ (hk h).elim

end Freezing2.ForestGeometry
