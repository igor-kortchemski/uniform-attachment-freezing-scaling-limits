module

/-
Vendored from the freezing1 companion project. Local imports are relocated;
namespace, statements, and proofs are preserved. See docs/companion-provenance.md.
-/

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Tactic

/-!
# Finite rooted forests and root-to-root merging

A forest is represented by its parent map, component-root map and depth. The
invariants below are established by the constructors. The associated undirected
graph is defined from parent edges; depth is subsequently identified with graph
distance, rather than being used as an unverified surrogate for height.

Joining two distinct roots is the deterministic operation in Algorithm 2 of
*Uniform attachment with freezing*. It increases the depth precisely in the
component of the second root.
-/

@[expose] public section

namespace Freezing1

/-- A finite forest with explicit roots and parent pointers. -/
structure RootedForest (V : Type*) [DecidableEq V] where
  vertices : Finset V
  parent : V → V
  root : V → V
  depth : V → ℕ
  parent_mem : ∀ v ∈ vertices, parent v ∈ vertices
  root_mem : ∀ v ∈ vertices, root v ∈ vertices
  root_fixed : ∀ v ∈ vertices, root (root v) = root v
  parent_root : ∀ v ∈ vertices, parent (root v) = root v
  root_parent : ∀ v ∈ vertices, root (parent v) = root v
  depth_root : ∀ v ∈ vertices, depth (root v) = 0
  depth_parent : ∀ v ∈ vertices, v ≠ root v → depth (parent v) + 1 = depth v

namespace RootedForest

variable {V : Type*} [DecidableEq V]

/-- A forest consisting of the specified isolated vertices. -/
def isolated (s : Finset V) : RootedForest V where
  vertices := s
  parent := id
  root := id
  depth := fun _ => 0
  parent_mem := by simp
  root_mem := by simp
  root_fixed := by simp
  parent_root := by simp
  root_parent := by simp
  depth_root := by simp
  depth_parent := by simp

/-- Each component is represented once by its root. -/
def roots (F : RootedForest V) : Finset V :=
  F.vertices.filter fun v => F.root v = v

@[simp] theorem mem_roots {F : RootedForest V} {v : V} :
    v ∈ F.roots ↔ v ∈ F.vertices ∧ F.root v = v := Finset.mem_filter

theorem root_mem_roots (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    F.root v ∈ F.roots := mem_roots.mpr ⟨F.root_mem v hv, F.root_fixed v hv⟩

theorem depth_eq_zero_iff (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    F.depth v = 0 ↔ F.root v = v := by
  constructor
  · intro hz
    by_contra h
    have := F.depth_parent v hv (Ne.symm h)
    omega
  · intro h
    simpa only [h] using F.depth_root v hv

theorem parent_of_root (F : RootedForest V) {v : V} (hv : v ∈ F.roots) :
    F.parent v = v := by
  obtain ⟨hv, hr⟩ := mem_roots.mp hv
  simpa only [hr] using F.parent_root v hv

/-- Merge the component rooted at `b` into the component rooted at `a`, adding
the parent edge from `b` to `a`. Both roots must exist and be distinct. -/
def join (F : RootedForest V) (a b : V) (ha : a ∈ F.roots) (hb : b ∈ F.roots)
    (hab : a ≠ b) : RootedForest V where
  vertices := F.vertices
  parent v := if v = b then a else F.parent v
  root v := if F.root v = b then a else F.root v
  depth v := F.depth v + if F.root v = b then 1 else 0
  parent_mem := by
    intro v hv
    split_ifs
    · exact (mem_roots.mp ha).1
    · exact F.parent_mem v hv
  root_mem := by
    intro v hv
    split_ifs
    · exact (mem_roots.mp ha).1
    · exact F.root_mem v hv
  root_fixed := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hrr := F.root_fixed v hv
    by_cases h : F.root v = b <;> simp [h, hra, hab, hrr]
  parent_root := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hpa := F.parent_of_root ha
    have hpr := F.parent_root v hv
    by_cases h : F.root v = b <;> simp [h, hpa, hab, hpr]
  root_parent := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hrb := (mem_roots.mp hb).2
    have hrp := F.root_parent v hv
    by_cases h : v = b <;> simp [h, hra, hrb, hab, hrp]
  depth_root := by
    intro v hv
    have hra := (mem_roots.mp ha).2
    have hda : F.depth a = 0 := (F.depth_eq_zero_iff (mem_roots.mp ha).1).mpr hra
    have hdr := F.depth_root v hv
    have hrr := F.root_fixed v hv
    by_cases h : F.root v = b <;> simp [h, hra, hab, hda, hdr, hrr]
  depth_parent := by
    intro v hv hne
    have hra := (mem_roots.mp ha).2
    have hrb := (mem_roots.mp hb).2
    have hda : F.depth a = 0 := (F.depth_eq_zero_iff (mem_roots.mp ha).1).mpr hra
    have hdb : F.depth b = 0 := (F.depth_eq_zero_iff (mem_roots.mp hb).1).mpr hrb
    have hrp := F.root_parent v hv
    by_cases hvb : v = b
    · subst v
      simp [hra, hrb, hda, hdb, hab]
    · have hvr : v ≠ F.root v := by
        intro heq
        have hnot : F.root v ≠ b := by simpa only [← heq] using hvb
        simp only [hnot, ↓reduceIte] at hne
        exact hne heq
      have hd := F.depth_parent v hv hvr
      simp only [hvb, ↓reduceIte, hrp]
      omega

@[simp] theorem join_vertices (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).vertices = F.vertices := rfl

/-- The height increment in a merge is the indicator of the second component. -/
theorem join_depth (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) (v : V) :
    (F.join a b ha hb hab).depth v = F.depth v + if F.root v = b then 1 else 0 := rfl

/-- A merge removes exactly its second root. -/
theorem join_roots (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).roots = F.roots.erase b := by
  ext v
  have hra := (mem_roots.mp ha).2
  have hrb := (mem_roots.mp hb).2
  simp only [mem_roots, join, Finset.mem_erase]
  by_cases h : F.root v = b
  · simp only [h, ↓reduceIte]
    constructor
    · rintro ⟨hv, heq⟩
      subst v
      exact False.elim (hab (hra.symm.trans h))
    · rintro ⟨hv, _, heq⟩
      exact False.elim (hv heq.symm)
  · simp only [h, ↓reduceIte]
    constructor
    · rintro ⟨hv, hr⟩
      exact ⟨by intro heq; subst v; exact h hrb, hv, hr⟩
    · rintro ⟨_, hv, hr⟩
      exact ⟨hv, hr⟩

theorem join_card_roots (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).roots.card + 1 = F.roots.card := by
  rw [join_roots]
  exact Finset.card_erase_add_one hb

/-- The undirected graph of the forest, with unused labels isolated. -/
def graph (F : RootedForest V) : SimpleGraph V where
  Adj u v := u ∈ F.vertices ∧ v ∈ F.vertices ∧ u ≠ v ∧
    (F.parent u = v ∨ F.parent v = u)
  symm := by
    constructor
    intro u v h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩
  loopless := ⟨by simp⟩

theorem parent_ne (F : RootedForest V) {v : V} (hv : v ∈ F.vertices)
    (hn : v ≠ F.root v) : F.parent v ≠ v := by
  have := F.depth_parent v hv hn
  intro h
  rw [h] at this
  omega

theorem parent_adj (F : RootedForest V) {v : V} (hv : v ∈ F.vertices)
    (hn : v ≠ F.root v) : F.graph.Adj (F.parent v) v :=
  ⟨F.parent_mem v hv, hv, F.parent_ne hv hn, Or.inr rfl⟩

theorem root_eq_of_adj (F : RootedForest V) {u v : V} (h : F.graph.Adj u v) :
    F.root u = F.root v := by
  rcases h with ⟨hu, hv, _, h | h⟩
  · simpa only [h] using (F.root_parent u hu).symm
  · simpa only [h] using F.root_parent v hv

theorem root_eq_of_walk (F : RootedForest V) {u v : V} (p : F.graph.Walk u v) :
    F.root u = F.root v := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (F.root_eq_of_adj h).trans ih

theorem depth_le_of_adj (F : RootedForest V) {u v : V} (h : F.graph.Adj u v) :
    F.depth v ≤ F.depth u + 1 := by
  rcases h with ⟨hu, hv, hne, h | h⟩
  · have hn : u ≠ F.root u := by
      intro heq
      have hp : F.parent u = u := by simpa only [← heq] using F.parent_root u hu
      exact hne (hp.symm.trans h)
    have hd := F.depth_parent u hu hn
    rw [h] at hd
    omega
  · have hn : v ≠ F.root v := by
      intro heq
      have hp : F.parent v = v := by simpa only [← heq] using F.parent_root v hv
      exact hne (h.symm.trans hp)
    have hd := F.depth_parent v hv hn
    rw [h] at hd
    omega

theorem depth_le_add_length (F : RootedForest V) {u v : V} (p : F.graph.Walk u v) :
    F.depth v ≤ F.depth u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := F.depth_le_of_adj h
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- Following parent pointers gives a root-to-vertex walk of exactly the stored depth. -/
theorem exists_root_walk (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    ∃ p : F.graph.Walk (F.root v) v, p.length = F.depth v := by
  generalize hd : F.depth v = d
  induction d using Nat.strong_induction_on generalizing v with
  | h d ih =>
    by_cases hr : v = F.root v
    · have hz : F.depth v = 0 := by simpa only [← hr] using F.depth_root v hv
      rw [← hr]
      exact ⟨.nil, hd.symm.trans hz |>.symm⟩
    · have hp := F.depth_parent v hv hr
      obtain ⟨p, hlen⟩ := ih (F.depth (F.parent v)) (by omega)
        (F.parent_mem v hv) rfl
      have hp' : ∃ q : F.graph.Walk (F.root (F.parent v)) v,
          q.length = F.depth v :=
        ⟨p.concat (F.parent_adj hv hr), by simpa [hlen] using hp⟩
      rw [F.root_parent v hv, hd] at hp'
      exact hp'

/-- The stored depth is the actual undirected graph distance from the root. -/
theorem depth_eq_dist (F : RootedForest V) {v : V} (hv : v ∈ F.vertices) :
    F.depth v = F.graph.dist (F.root v) v := by
  obtain ⟨p, hp⟩ := F.exists_root_walk hv
  apply le_antisymm
  · obtain ⟨q, hq⟩ := (show F.graph.Reachable (F.root v) v from ⟨p⟩).exists_walk_length_eq_dist
    have := F.depth_le_add_length q
    simpa only [F.depth_root v hv, zero_add, hq] using this
  · simpa only [hp] using F.graph.dist_le p

/-- Distinct roots lie in different connected components. -/
theorem not_reachable_roots (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    ¬F.graph.Reachable a b := by
  rintro ⟨p⟩
  have h := F.root_eq_of_walk p
  rw [(mem_roots.mp ha).2, (mem_roots.mp hb).2] at h
  exact hab h

/-- Joining roots adds exactly the edge between them. -/
theorem join_graph (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).graph = F.graph ⊔ SimpleGraph.edge a b := by
  ext u v
  have hpb := F.parent_of_root hb
  have ha' := (mem_roots.mp ha).1
  have hb' := (mem_roots.mp hb).1
  simp only [graph, join, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  by_cases hu : u = b <;> by_cases hv : v = b <;> simp_all <;> grind only

theorem join_isAcyclic (F : RootedForest V) (hF : F.graph.IsAcyclic) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).graph.IsAcyclic := by
  rw [join_graph]
  exact hF.sup_edge_of_not_reachable (F.not_reachable_roots ha hb hab)

@[simp] theorem isolated_graph (s : Finset V) : (isolated s).graph = ⊥ := by
  ext u v
  simp [graph, isolated]
  exact fun _ _ h => ⟨h, Ne.symm h⟩

/-- Insert a fresh isolated vertex, the reverse-time operation at a freezing step. -/
def adjoin (F : RootedForest V) (v : V) (hv : v ∉ F.vertices) : RootedForest V where
  vertices := insert v F.vertices
  parent w := if w = v then v else F.parent w
  root w := if w = v then v else F.root w
  depth w := if w = v then 0 else F.depth w
  parent_mem := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp only [hwv, ↓reduceIte]
      exact Finset.mem_insert_of_mem (F.parent_mem w hw)
  root_mem := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      simp only [hwv, ↓reduceIte]
      exact Finset.mem_insert_of_mem (F.root_mem w hw)
  root_fixed := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.root_fixed w hw]
  parent_root := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.parent_root w hw]
  root_parent := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hpv : F.parent w ≠ v := fun h => hv (h ▸ F.parent_mem w hw)
      simp [hwv, hpv, F.root_parent w hw]
  depth_root := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hrv : F.root w ≠ v := fun h => hv (h ▸ F.root_mem w hw)
      simp [hwv, hrv, F.depth_root w hw]
  depth_parent := by
    intro w hw hn
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp at hn
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      have hpv : F.parent w ≠ v := fun h => hv (h ▸ F.parent_mem w hw)
      simp only [hwv, ↓reduceIte] at hn
      simp [hwv, hpv, F.depth_parent w hw hn]

@[simp] theorem adjoin_vertices (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).vertices = insert v F.vertices := rfl

theorem adjoin_roots (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).roots = insert v F.roots := by
  ext w
  simp only [mem_roots, adjoin, Finset.mem_insert]
  by_cases hw : w = v <;> simp [hw]

theorem adjoin_card_roots (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).roots.card = F.roots.card + 1 := by
  rw [adjoin_roots, Finset.card_insert_of_notMem]
  exact fun h => hv (mem_roots.mp h).1

theorem adjoin_graph (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).graph = F.graph := by
  ext a b
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a; subst b; simp
  · subst a
    have hpb : b ∈ F.vertices → F.parent b ≠ v :=
      fun h e => hv (e ▸ F.parent_mem b h)
    simp [graph, adjoin, hb, hv]
    exact fun h hn => ⟨hn, hpb h⟩
  · subst b
    have hpa : a ∈ F.vertices → F.parent a ≠ v :=
      fun h e => hv (e ▸ F.parent_mem a h)
    simp [graph, adjoin, ha, hv]
    exact fun h => ⟨hpa h, Ne.symm ha⟩
  · simp [graph, adjoin, ha, hb]

theorem adjoin_depth_old (F : RootedForest V) {v w : V}
    (hv : v ∉ F.vertices) (hw : w ∈ F.vertices) :
    (F.adjoin v hv).depth w = F.depth w := by
  have h : w ≠ v := fun h => hv (h ▸ hw)
  simp [adjoin, h]

@[simp] theorem adjoin_depth_new (F : RootedForest V) {v : V} (hv : v ∉ F.vertices) :
    (F.adjoin v hv).depth v = 0 := by simp [adjoin]

/-- Restrict the ambient graph to the forest's actual vertices. -/
def toGraph (F : RootedForest V) : SimpleGraph {v // v ∈ F.vertices} :=
  F.graph.induce (F.vertices : Set V)

theorem walk_support_mem (F : RootedForest V) {u v : V}
    (p : F.graph.Walk u v) (hu : u ∈ F.vertices) :
    ∀ w ∈ p.support, w ∈ F.vertices := by
  induction p with
  | nil => simpa using hu
  | cons h p ih =>
    intro w hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact ih h.2.1 w hw

theorem root_reachable_induced (F : RootedForest V) (v : {v // v ∈ F.vertices}) :
    F.toGraph.Reachable ⟨F.root v, F.root_mem v v.property⟩ v := by
  obtain ⟨p, _⟩ := F.exists_root_walk v.property
  exact ⟨p.induce (F.vertices : Set V) (F.walk_support_mem p (F.root_mem v v.property))⟩

/-- One component in an acyclic rooted forest gives a finite tree in Mathlib's
graph sense. This is applied to the final state of Algorithm 2. -/
theorem isTree_of_one_root (F : RootedForest V) (hcard : F.roots.card = 1)
    (hacyc : F.graph.IsAcyclic) : F.toGraph.IsTree := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have haR : a ∈ F.roots := by rw [ha]; simp
  have haV := (mem_roots.mp haR).1
  have hroot : ∀ v : {v // v ∈ F.vertices}, F.root v = a := by
    intro v
    have hv := F.root_mem_roots v.property
    rwa [ha, Finset.mem_singleton] at hv
  have hreached : ∀ v : {v // v ∈ F.vertices}, F.toGraph.Reachable ⟨a, haV⟩ v := by
    intro v
    simpa only [hroot v] using F.root_reachable_induced v
  have : Nonempty {v // v ∈ F.vertices} := ⟨⟨a, haV⟩⟩
  exact ⟨⟨fun u v => (hreached u).symm.trans (hreached v)⟩, hacyc.induce _⟩

end RootedForest
end Freezing1
