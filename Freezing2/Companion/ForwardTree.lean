module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Freezing2.Companion.Extinction
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The forward attachment and freezing construction

Vertices have persistent identifiers: zero is the initial root, and a new
vertex has the time of its birth as identifier. Its displayed label is `a`
while active and its freezing time afterwards. Thus identifiers are distinct
even when several vertices carry the displayed label `a`.

The deterministic transition below is Algorithm 1 conditional on its choice
of an active vertex. No probability law is assumed in its invariants.
-/

@[expose] public section

namespace Freezing1.Forward

structure State where
  vertices : Finset ℕ
  active : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ
  frozenAt : ℕ → Option ℕ

def initial : State where
  vertices := {0}
  active := {0}
  graph := ⊥
  parent := fun _ => 0
  height := fun _ => 0
  frozenAt := fun _ => none

/-- Attach the fresh vertex `t` to the chosen active vertex `v`. -/
def attach (s : State) (t v : ℕ) : State where
  vertices := insert t s.vertices
  active := insert t s.active
  graph := s.graph ⊔ SimpleGraph.edge v t
  parent := Function.update s.parent t v
  height := Function.update s.height t (s.height v + 1)
  frozenAt := Function.update s.frozenAt t none

/-- Freeze the chosen vertex and record its displayed label. -/
def freeze (s : State) (t v : ℕ) : State where
  vertices := s.vertices
  active := s.active.erase v
  graph := s.graph
  parent := s.parent
  height := s.height
  frozenAt := Function.update s.frozenAt v (some t)

/-- Algorithm 1's transition. Invalid choices leave the state unchanged;
all theorems about the process require a legal active choice when one exists. -/
def step (s : State) (t : ℕ) (sign : Bool) (v : ℕ) : State :=
  if v ∈ s.active then if sign then attach s t v else freeze s t v else s

/-- Structural invariants, subsequently proved for every constructed state. -/
structure ValidAt (n : ℕ) (s : State) : Prop where
  root_mem : 0 ∈ s.vertices
  active_subset : s.active ⊆ s.vertices
  vertices_le : ∀ v ∈ s.vertices, v ≤ n
  adj_mem : ∀ {u v}, s.graph.Adj u v → u ∈ s.vertices ∧ v ∈ s.vertices
  acyclic : s.graph.IsAcyclic
  reachable : ∀ v ∈ s.vertices, s.graph.Reachable 0 v
  parent_mem : ∀ v ∈ s.vertices, s.parent v ∈ s.vertices
  parent_lt : ∀ v ∈ s.vertices, v ≠ 0 → s.parent v < v
  parent_adj : ∀ v ∈ s.vertices, v ≠ 0 → s.graph.Adj (s.parent v) v
  height_root : s.height 0 = 0
  height_parent : ∀ v ∈ s.vertices, v ≠ 0 → s.height v = s.height (s.parent v) + 1
  active_iff : ∀ v ∈ s.vertices, v ∈ s.active ↔ s.frozenAt v = none
  adj_height : ∀ {u v}, s.graph.Adj u v →
    s.height u + 1 = s.height v ∨ s.height v + 1 = s.height u

theorem initial_valid : ValidAt 0 initial := by
  constructor <;> simp [initial, SimpleGraph.reachable_bot]

theorem ValidAt.mono {n m : ℕ} {s : State} (h : ValidAt n s) (hnm : n ≤ m) :
    ValidAt m s :=
  { h with vertices_le := fun v hv => (h.vertices_le v hv).trans hnm }

theorem ValidAt.attach {n : ℕ} {s : State} (h : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) : ValidAt (n + 1) (attach s (n + 1) v) := by
  have hvV := h.active_subset hv
  have hvt : v ≠ n + 1 := by have := h.vertices_le v hvV; omega
  have hfresh : n + 1 ∉ s.vertices := by
    intro ht; have := h.vertices_le _ ht; omega
  have hne : n + 1 ≠ 0 := by omega
  have hnr : ¬s.graph.Reachable v (n + 1) := by
    apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hvt
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hfresh (h.adj_mem hw).1
  constructor
  · exact Finset.mem_insert_of_mem h.root_mem
  · intro w hw
    simpa only [Forward.attach, Finset.mem_insert] using
      (show w = n + 1 ∨ w ∈ s.vertices from
        (Finset.mem_insert.mp hw).imp id (fun hw => h.active_subset hw))
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact le_rfl
    · exact (h.vertices_le w hw).trans (Nat.le_succ n)
  · intro a b hab
    change s.graph.Adj a b ∨ (SimpleGraph.edge v (n + 1)).Adj a b at hab
    rcases hab with hab | hab
    · exact ⟨Finset.mem_insert_of_mem (h.adj_mem hab).1,
        Finset.mem_insert_of_mem (h.adj_mem hab).2⟩
    · simp only [SimpleGraph.edge_adj] at hab
      rcases hab with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;>
        simp [Forward.attach, hvV]
  · exact h.acyclic.sup_edge_of_not_reachable hnr
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ((h.reachable v hvV).mono le_sup_left).trans
        (SimpleGraph.Adj.reachable (show (s.graph ⊔ SimpleGraph.edge v (n + 1)).Adj v (n + 1)
          from Or.inr (by simp [SimpleGraph.edge_adj, hvt])))
    · exact (h.reachable w hw).mono le_sup_left
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [Forward.attach] using Finset.mem_insert_of_mem (b := n + 1) hvV
    · have hwne : w ≠ n + 1 := fun he => hfresh (he ▸ hw)
      simpa [Forward.attach, hwne] using Finset.mem_insert_of_mem (b := n + 1) (h.parent_mem w hw)
  · intro w hw hw0
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [Forward.attach, Function.update_self]
      exact Nat.lt_succ_of_le (h.vertices_le v hvV)
    · have hwne : w ≠ n + 1 := fun he => hfresh (he ▸ hw)
      simpa [Forward.attach, hwne] using h.parent_lt w hw hw0
  · intro w hw hw0
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [Forward.attach, SimpleGraph.edge_adj, hvt]
    · have hwne : w ≠ n + 1 := fun he => hfresh (he ▸ hw)
      exact Or.inl (by simpa [Forward.attach, hwne] using h.parent_adj w hw hw0)
  · simpa [Forward.attach, hne.symm] using h.height_root
  · intro w hw hw0
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [Forward.attach, hvt]
    · have hwne : w ≠ n + 1 := fun he => hfresh (he ▸ hw)
      have hpne : s.parent w ≠ n + 1 := fun he => hfresh (he ▸ h.parent_mem w hw)
      simpa [Forward.attach, hwne, hpne] using h.height_parent w hw hw0
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp [Forward.attach]
    · have hwne : w ≠ n + 1 := fun he => hfresh (he ▸ hw)
      simpa [Forward.attach, hwne] using h.active_iff w hw

  · intro a b hab
    change s.graph.Adj a b ∨ (SimpleGraph.edge v (n + 1)).Adj a b at hab
    rcases hab with hab | hab
    · have ha : a ≠ n + 1 := fun he => hfresh (he ▸ (h.adj_mem hab).1)
      have hb : b ≠ n + 1 := fun he => hfresh (he ▸ (h.adj_mem hab).2)
      simpa [Forward.attach, ha, hb] using h.adj_height hab
    · simp only [SimpleGraph.edge_adj] at hab
      rcases hab with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;>
        simp [Forward.attach, hvt]

theorem ValidAt.freeze {n : ℕ} {s : State} (h : ValidAt n s) (v : ℕ) :
    ValidAt (n + 1) (freeze s (n + 1) v) := by
  refine { h.mono (Nat.le_succ n) with
    active_subset := fun w hw => h.active_subset (Finset.mem_of_mem_erase hw)
    active_iff := ?_ }
  intro w hw
  by_cases hwv : w = v
  · subst w; simp [Forward.freeze]
  · simpa [Forward.freeze, hwv] using h.active_iff w hw

/-- Every legal choice produces a valid tree at the next time. -/
theorem ValidAt.step {n : ℕ} {s : State} (h : ValidAt n s) (sign : Bool) (v : ℕ) :
    ValidAt (n + 1) (step s (n + 1) sign v) := by
  unfold Forward.step
  split_ifs with hv hs
  · exact h.attach hv
  · exact h.freeze v
  · exact h.mono (Nat.le_succ n)

/-- The deterministic trajectory driven by choices of persistent vertex IDs. -/
def run (x : SignSequence) (choice : ℕ → ℕ) : ℕ → State
  | 0 => initial
  | n + 1 => step (run x choice n) (n + 1) (x (n + 1)) (choice (n + 1))

theorem run_valid (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ) :
    ValidAt n (run x choice n) := by
  induction n with
  | zero => exact initial_valid
  | succ n ih => exact ih.step _ _

/-- The actual finite graph, restricting the ambient isolated identifiers. -/
def State.tree (s : State) : SimpleGraph {v // v ∈ s.vertices} :=
  s.graph.induce (s.vertices : Set ℕ)

theorem ValidAt.tree_connected {n : ℕ} {s : State} (h : ValidAt n s) :
    s.tree.Connected := by
  have hroot : ∀ v : {v // v ∈ s.vertices},
      s.tree.Reachable ⟨0, h.root_mem⟩ v := by
    intro ⟨v, hv⟩
    induction v using Nat.strong_induction_on with
    | h v ih =>
      by_cases hv0 : v = 0
      · subst v; exact SimpleGraph.Reachable.rfl
      · exact (ih (s.parent v) (h.parent_lt v hv hv0) (h.parent_mem v hv)).trans
          (SimpleGraph.Adj.reachable (h.parent_adj v hv hv0))
  have : Nonempty {v // v ∈ s.vertices} := ⟨⟨0, h.root_mem⟩⟩
  exact ⟨fun u v => (hroot u).symm.trans (hroot v)⟩

/-- Algorithm 1 really constructs finite trees, not merely numerical heights. -/
theorem ValidAt.isTree {n : ℕ} {s : State} (h : ValidAt n s) : s.tree.IsTree :=
  ⟨h.tree_connected, h.acyclic.induce _⟩

theorem ValidAt.height_le_walk_length {n : ℕ} {s : State} (h : ValidAt n s)
    {u v : ℕ} (p : s.graph.Walk u v) : s.height v ≤ s.height u + p.length := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    have hh := h.adj_height hadj
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem ValidAt.exists_walk_length_height {n : ℕ} {s : State} (h : ValidAt n s)
    (v : ℕ) (hv : v ∈ s.vertices) :
    ∃ p : s.graph.Walk 0 v, p.length = s.height v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv0 : v = 0
    · subst v
      exact ⟨.nil, h.height_root.symm⟩
    · obtain ⟨p, hp⟩ := ih (s.parent v) (h.parent_lt v hv hv0) (h.parent_mem v hv)
      refine ⟨p.concat (h.parent_adj v hv hv0), ?_⟩
      simpa [hp] using (h.height_parent v hv hv0).symm

/-- The recursively maintained height equals the ordinary graph distance. -/
theorem ValidAt.height_eq_dist {n : ℕ} {s : State} (h : ValidAt n s)
    (v : ℕ) (hv : v ∈ s.vertices) : s.height v = s.graph.dist 0 v := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_height v hv
  obtain ⟨q, hq⟩ := (h.reachable v hv).exists_walk_length_eq_dist
  apply le_antisymm
  · simpa [h.height_root, hq] using h.height_le_walk_length q
  · simpa [hp] using s.graph.dist_le p

set_option backward.isDefEq.respectTransparency false in
/-- The parent path also exists inside the actual finite vertex carrier. -/
theorem ValidAt.exists_tree_walk_length_height {n : ℕ} {s : State} (h : ValidAt n s)
    (v : {v // v ∈ s.vertices}) :
    ∃ p : s.tree.Walk ⟨0, h.root_mem⟩ v, p.length = s.height v := by
  rcases v with ⟨v, hv⟩
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv0 : v = 0
    · subst v
      exact ⟨.nil, h.height_root.symm⟩
    · obtain ⟨p, hp⟩ := ih (s.parent v) (h.parent_lt v hv hv0) (h.parent_mem v hv)
      refine ⟨p.concat (h.parent_adj v hv hv0), ?_⟩
      rw [SimpleGraph.Walk.length_concat, hp]
      exact (h.height_parent v hv hv0).symm

set_option backward.isDefEq.respectTransparency false in
/-- The maintained height is precisely distance in the finite tree, so its
interpretation does not rely on unused isolated identifiers in the ambient graph. -/
theorem ValidAt.height_eq_tree_dist {n : ℕ} {s : State} (h : ValidAt n s)
    (v : {v // v ∈ s.vertices}) : s.height v = s.tree.dist ⟨0, h.root_mem⟩ v := by
  obtain ⟨p, hp⟩ := h.exists_tree_walk_length_height v
  obtain ⟨q, hq⟩ :=
    (show s.tree.Reachable ⟨0, h.root_mem⟩ v from ⟨p⟩).exists_walk_length_eq_dist
  apply le_antisymm
  · have hh := h.height_le_walk_length
      (q.map (SimpleGraph.Embedding.induce (s.vertices : Set ℕ)).toHom)
    change s.height v ≤ s.height 0 +
      (q.map (SimpleGraph.Embedding.induce (s.vertices : Set ℕ)).toHom).length at hh
    rw [SimpleGraph.Walk.length_map, h.height_root, zero_add, hq] at hh
    exact hh
  · simpa only [hp] using s.tree.dist_le p

theorem run_isTree (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ) :
    (run x choice n).tree.IsTree := (run_valid x choice n).isTree

/-- Choices are legal whenever the current active set is nonempty. -/
def LegalThrough (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k < n, (run x choice k).active.Nonempty → choice (k + 1) ∈ (run x choice k).active

theorem LegalThrough.mono {x : SignSequence} {choice : ℕ → ℕ} {m n : ℕ}
    (h : LegalThrough x choice n) (hmn : m ≤ n) : LegalThrough x choice m :=
  fun k hk => h k (hk.trans_le hmn)

/-- Both counting identities of Algorithm 1 hold through its extinction time. -/
theorem run_counts (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ)
    (hc : LegalThrough x choice n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ((run x choice n).active.card : ℤ) = activeCount x n ∧
      (run x choice n).vertices.card = plusCount x n + 1 := by
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hτ
    have ih := ih (hc.mono (Nat.le_succ n)) hnτ.le
    have hpos : 0 < activeCount x n := ((lt_extinctionTime_iff x n).mp hnτ) n le_rfl
    have hcard : 0 < (run x choice n).active.card := by omega
    have hchoice := hc n (Nat.lt_succ_self n) (Finset.card_pos.mp hcard)
    have hv := run_valid x choice n
    have hfresh : n + 1 ∉ (run x choice n).vertices := by
      intro hf; have := hv.vertices_le _ hf; omega
    have hafresh : n + 1 ∉ (run x choice n).active :=
      fun hf => hfresh (hv.active_subset hf)
    rw [run, Forward.step, ite_eq_left hchoice, activeCount_succ, plusCount_succ]
    cases hx : x (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, Forward.freeze]
      rw [Finset.card_erase_of_mem hchoice]
      constructor
      · rw [Nat.cast_sub (by omega), Nat.cast_one, ih.1]
        omega
      · simpa using ih.2
    · simp only [↓reduceIte, Forward.attach]
      rw [Finset.card_insert_of_notMem hafresh, Finset.card_insert_of_notMem hfresh]
      constructor
      · simp [ih.1]
      · omega

theorem run_active_card (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ)
    (hc : LegalThrough x choice n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ((run x choice n).active.card : ℤ) = activeCount x n :=
  (run_counts x choice n hc hτ).1

theorem run_vertices_card (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ)
    (hc : LegalThrough x choice n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    (run x choice n).vertices.card = plusCount x n + 1 :=
  (run_counts x choice n hc hτ).2

/-- The paper's exact vertex-count expression, including the extinction endpoint. -/
theorem run_vertices_card_real (x : SignSequence) (choice : ℕ → ℕ) (n : ℕ)
    (hc : LegalThrough x choice n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ((run x choice n).vertices.card : ℝ) = ((n : ℝ) + 1 + activeCount x n) / 2 := by
  rw [run_vertices_card x choice n hc hτ, activeCount_eq]
  push_cast
  ring

@[simp] theorem step_of_active_empty (s : State) (t : ℕ) (sign : Bool) (v : ℕ)
    (h : s.active = ∅) : step s t sign v = s := by
  simp [Forward.step, h]

end Freezing1.Forward
