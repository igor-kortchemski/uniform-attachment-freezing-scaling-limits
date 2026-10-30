module

public import Freezing2.Probability.ReverseHeightIncrements

/-!
# The edge-labelled forest history as an observation

The source labels a newly joined edge by its source step. Replaying adjacency
changes reconstructs these labels from the exposed rooted-forest history.
The observation below retains vertices, roots, adjacency, and edge labels, and
forgets the auxiliary parent and depth fields. Its sigma algebra is contained
in that of the full trajectory prefix. The tower property therefore transfers
the height-increment conditional probability to this labelled observation.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Freezing2.ReverseHistory

/-- Reconstruct edge labels by the source rule: an edge newly appearing at
construction step `k` receives label `n-k`; existing edge labels are preserved.
The value zero on a nonedge is immaterial to the observed labelled graph. -/
noncomputable def edgeLabelAt (n : ℕ) : ℕ → History → (ℕ ⊕ ℕ) → (ℕ ⊕ ℕ) → ℕ
  | 0, _, _, _ => 0
  | k + 1, ω, u, v =>
      if (ω (k + 1)).graph.Adj u v ∧ ¬(ω k).graph.Adj u v then n - k
      else edgeLabelAt n k ω u v

theorem edgeLabelAt_newEdge (n k : ℕ) (ω : History) {u v : ℕ ⊕ ℕ}
    (hnew : (ω (k + 1)).graph.Adj u v) (hold : ¬(ω k).graph.Adj u v) :
    edgeLabelAt n (k + 1) ω u v = n - k := by
  simp [edgeLabelAt, hnew, hold]

theorem edgeLabelAt_oldEdge (n k : ℕ) (ω : History) {u v : ℕ ⊕ ℕ}
    (hold : (ω k).graph.Adj u v) :
    edgeLabelAt n (k + 1) ω u v = edgeLabelAt n k ω u v := by
  simp only [edgeLabelAt, hold, not_true_eq_false, and_false, ite_false]

theorem edgeLabelAt_sameGraph (n k : ℕ) (ω : History)
    (hgraph : (ω (k + 1)).graph = (ω k).graph) (u v : ℕ ⊕ ℕ) :
    edgeLabelAt n (k + 1) ω u v = edgeLabelAt n k ω u v := by
  simp only [edgeLabelAt, hgraph, and_not_self, ite_false]

/-- The actual root-joining operation creates precisely the source-labelled
edge. Distinct roots could not already have been adjacent. -/
theorem edgeLabelAt_joinRoots (n k : ℕ) (ω : History) {a b : ℕ ⊕ ℕ}
    (ha : a ∈ (ω k).roots) (hb : b ∈ (ω k).roots) (hab : a ≠ b)
    (hjoin : ω (k + 1) = (ω k).join a b ha hb hab) :
    edgeLabelAt n (k + 1) ω a b = n - k := by
  apply edgeLabelAt_newEdge
  · rw [hjoin, Freezing1.RootedForest.join_graph]
    simp [SimpleGraph.edge_adj, hab]
  · exact fun hadj ↦ (ω k).not_reachable_roots ha hb hab hadj.reachable

/-- Inserting the prescribed singleton adds no edge and changes no edge label. -/
theorem edgeLabelAt_adjoin (n k : ℕ) (ω : History) {w : ℕ ⊕ ℕ}
    (hw : w ∉ (ω k).vertices) (hinsert : ω (k + 1) = (ω k).adjoin w hw)
    (u v : ℕ ⊕ ℕ) :
    edgeLabelAt n (k + 1) ω u v = edgeLabelAt n k ω u v := by
  apply edgeLabelAt_sameGraph
  rw [hinsert, Freezing1.RootedForest.adjoin_graph]

theorem measurableSet_adj_piLE {j k : ℕ} (hj : j ≤ k) (u v : ℕ ⊕ ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Forest) k]
      {ω : History | (ω j).graph.Adj u v} :=
  (show MeasurableSet {F : Forest | F.graph.Adj u v} from by trivial).preimage
    (measurable_eval_piLE hj)

theorem measurable_edgeLabelAt (n k : ℕ) (u v : ℕ ⊕ ℕ) :
    Measurable[Filtration.piLE (X := fun _ ↦ Forest) k]
      (fun ω : History ↦ edgeLabelAt n k ω u v) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact Measurable.ite
      ((measurableSet_adj_piLE (le_refl (k + 1)) u v).inter
        (measurableSet_adj_piLE (Nat.le_succ k) u v).compl)
      measurable_const (ih.mono (Filtration.piLE.mono (Nat.le_succ k)) le_rfl)

/-- The information in an edge-labelled rooted forest, represented through
countable adjacency and edge-label coordinates. -/
abbrev LabelledForestObservation :=
  (Finset (ℕ ⊕ ℕ) × Finset (ℕ ⊕ ℕ)) ×
    (((ℕ ⊕ ℕ) → (ℕ ⊕ ℕ) → Bool) × ((ℕ ⊕ ℕ) → (ℕ ⊕ ℕ) → ℕ))

noncomputable def labelledForestAt (n k : ℕ) (ω : History) : LabelledForestObservation :=
  (((ω k).vertices, (ω k).roots),
    (fun u v ↦ decide ((ω k).graph.Adj u v), edgeLabelAt n k ω))

theorem measurable_labelledForestAt (n k : ℕ) :
    Measurable[Filtration.piLE (X := fun _ ↦ Forest) k] (labelledForestAt n k) := by
  let : MeasurableSpace History := Filtration.piLE (X := fun _ ↦ Forest) k
  have hv : Measurable[Filtration.piLE (X := fun _ ↦ Forest) k]
      (fun ω : History ↦ (ω k).vertices) :=
    (show Measurable (fun F : Forest ↦ F.vertices) from measurable_from_top).comp
      (measurable_eval_piLE le_rfl)
  have hr : Measurable[Filtration.piLE (X := fun _ ↦ Forest) k]
      (fun ω : History ↦ (ω k).roots) :=
    (show Measurable (fun F : Forest ↦ F.roots) from measurable_from_top).comp
      (measurable_eval_piLE le_rfl)
  have ha : Measurable[Filtration.piLE (X := fun _ ↦ Forest) k]
      (fun ω : History ↦ fun u v ↦ decide ((ω k).graph.Adj u v)) := by
    apply Measurable.of_eval
    intro u
    apply Measurable.of_eval
    intro v
    exact (show Measurable (fun F : Forest ↦ decide (F.graph.Adj u v)) from
      measurable_from_top).comp (measurable_eval_piLE le_rfl)
  exact (hv.prodMk hr).prodMk (ha.prodMk
    (Measurable.of_eval fun u ↦ Measurable.of_eval fun v ↦ measurable_edgeLabelAt n k u v))

/-- All labelled forests exposed through construction time `k`. -/
noncomputable def labelledPrefix (n k : ℕ) (ω : History) :
    Finset.Iic k → LabelledForestObservation :=
  fun j ↦ labelledForestAt n j ω

theorem measurable_labelledPrefix (n k : ℕ) :
    Measurable[Filtration.piLE (X := fun _ ↦ Forest) k] (labelledPrefix n k) := by
  let : MeasurableSpace History := Filtration.piLE (X := fun _ ↦ Forest) k
  exact Measurable.of_eval fun j ↦
    (measurable_labelledForestAt n j).mono
      (Filtration.piLE.mono (Finset.mem_Iic.mp j.2)) le_rfl

@[instance_reducible] noncomputable def labelledHistorySigma (n k : ℕ) : MeasurableSpace History :=
  MeasurableSpace.comap (labelledPrefix n k) inferInstance

theorem labelledHistorySigma_le_piLE (n k : ℕ) :
    labelledHistorySigma n k ≤ Filtration.piLE (X := fun _ ↦ Forest) k :=
  (measurable_labelledPrefix n k).comap_le

/-- The source conditional increment formula with respect to the history of
edge-labelled rooted forests, obtained by observing the actual trajectory. -/
theorem conditional_height_increment_labelled {x : Freezing1.SignSequence} {n i : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hi : 1 ≤ i)
    {v : ℕ ⊕ ℕ} (hv : v ∈ Freezing1.vertexLabels x n)
    (hib : i ≤ Freezing1.birthTime n v) :
    (jointLaw x n)[incrementIndicator (n - i) v | labelledHistorySigma n (n - i)]
      =ᵐ[jointLaw x n]
      fun _ ↦ if x i then 1 / (Freezing1.activeCount x i : ℝ) else 0 :=
  conditional_const_of_le (labelledHistorySigma_le_piLE n (n - i))
    (conditional_height_increment hn hi hv hib)

end Freezing2.ReverseHistory
