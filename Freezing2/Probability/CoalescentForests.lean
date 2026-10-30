module

public import Freezing2.Probability.CoalescentDecoding

/-!
# The labelled plane forests of the coalescent genealogy

This file completes Proposition `loi du coalescent généralisé` (inventory N11) of
`attachement-uniforme-2-final.tex` in the source's combinatorial form: the joint law of the
labelled plane forest `𝓕 ∈ 𝔉⁺_{r,k}`, the births `B` and the merge times `C` of the limiting
coalescent genealogy, with uniform child orders.

## The forests `𝔉⁺_{r,k}`

* `KidsMap n`, `IsPlaneForest`: a plane binary forest on the vertices `Fin n` is its children map,
  `none` at a leaf and the ordered pair (left, right) of children at an internal vertex; children
  carry larger labels than their parent, are distinct, and every vertex has at most one parent.
* `SourceForest r k` is the source's `𝔉⁺_{r,k}`: such forests with `r + 1` trees (`rootCount`) on
  `2k - 1 - r` vertices, the vertex `v` carrying the label `r + 1 + v` (`vertexLabel`), so the
  labels `r + 1, …, 2k - 1` increase along the branches. The trees are ordered by their root
  labels (convention S09), so no extra datum orders them. `SourceForest.card_internal`,
  `SourceForest.card_leaves`: they have `k - 1 - r` internal vertices and `k` leaves.
* `SourceAdmissible F₀ b c`: the source's admissibility (increasing-bijection definition),
  combined with the Proposition's range `0 < c < 1`; births are not restricted here (the
  cube `[0,1]^k` enters through the reference measure). The `2k - 1 - r` times are
  distinct, `0 < c_{r+1} < ⋯ < c_{k-1} < 1` (with `c i = c_{r+1+i}`), and there is an increasing
  bijection `φ` from `{c_j} ∪ {b_j}` onto `{r + 1, …, 2k - 1}` sending births to leaf labels and
  merge times to internal labels. The particle `j` sits at the leaf labelled `φ (b j)`.

## The bijection with plane histories

For a labelling `e : Fin k ⊕ Fin m ≃ Fin n` of the `k` births and `m` merges, increasing in time:
* `histForest e xs σ`: the forest of a merge history `xs` with child orders `σ`. The vertex
  `e (inr s)` of the `s`-th merge has as children the vertices of the two clusters it joins
  (`IsParent`, `DAdm.kidSet_eq`), in increasing order, exchanged when `σ s = true`; particle `j`
  is the leaf `e (inl j)`.
* `forestStates`, `forestOrders`: the merge history and the child orders of a forest; after the
  `s`-th merge two particles are related when they lie below a common merge vertex of rank `≤ s`.
* `historyForestEquiv`: admissible merge histories with child orders (`DAdm`) correspond
  bijectively to the plane forests fitting `e` (`Fits`: leaves at births, internal vertices at
  merges). The merge order gives the internal labels by time rank, and `σ` the left/right order.
* `isAdmissible_iff_dAdm`: for distinct times, `IsAdmissible` is `DAdm` for the labelling of the
  events by their ranks (`rankFin`, `labelEquiv`).
* `sourceAdmissible_iff`: the source's admissibility of `(F₀, b, cs ∘ rev)` is the distinctness
  of the times, `cs` decreasing in `(0, 1)`, and `Fits` for the rank labelling; any increasing
  bijection `φ` is the rank (`phi_eq_countBelow`), and the rank is one (`exists_phi`).
* `sourceTripletEquiv`: for `r < k`, the admissible plane histories `(xs, σ, b, cs)` with
  `m = k - 1 - r` merges and distinct times are in bijection with the admissible source triplets
  `(F₀, b, c)`, `F₀ ∈ 𝔉⁺_{r,k}`, where `c = cs ∘ rev` lists the merge times increasingly.
* `planeForest`: the random forest `𝓕` of a plane history (`none` off the admissible histories
  with distinct times). `exists_planeForest` and `existsUnique_planeForest`: it maps the
  admissible plane histories with distinct times onto the admissible triplets, bijectively.
  `planeLaw_planeForest_eq_none`: it is almost surely defined.
* `birthTimes`, `sourceMergeTimes`, `upperMergeTimes`: the births `B`, the source's ordered merge
  times `C_1 ≤ ⋯ ≤ C_{k-1}` (with `C_1 = ⋯ = C_r = 0`), and `(C_{r+1}, …, C_{k-1})`.

## The law

* `sourceDensity g F₀ b c`: the density `g_{r,k}` (with `g = 1/f`), extended by `0` off the
  admissible triplets.
* `sum_planeDensity_patternForest`: at fixed times, summing the plane density over the plane
  histories with forest `F₀` gives `g_{r,k}(F₀, b, c)`.
* `planeLaw_forestEvent`, `planeLaw_forestEvent_prod`, `map_restrict_planeLaw`: under
  `planeLaw g k`, the law of the decoded genealogy of `criticalGenealogyLimit g k` with
  independent uniform child orders (`planeLaw_eq_uniformOrders`, `map_forgetOrders_planeLaw`),
  `P(𝓕 = F₀, C₁ = ⋯ = C_r = 0, (B, (C_{r+1}, …, C_{k-1})) ∈ S)` is the Lebesgue integral of
  `g_{r,k}(F₀, b, c)` over `(b, c) ∈ S` with `b ∈ [0, 1]^k`. `sourceForest_law` collects these
  statements under the source hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Freezing2.CoalescentDensity

open TrackedGenealogy CriticalGenealogy

/-! ### Plane binary forests with increasing labels -/

section PlaneForest

variable {n : ℕ}

/-- The children map of a plane binary forest on the vertex set `Fin n`: `none` at a leaf,
and the ordered pair `(left child, right child)` at an internal vertex. -/
abbrev KidsMap (n : ℕ) := Fin n → Option (Fin n × Fin n)

/-- `v` is one of the two children of `w`. -/
def IsKid (F : KidsMap n) (w v : Fin n) : Prop :=
  ∃ a c, F w = some (a, c) ∧ (v = a ∨ v = c)

instance (F : KidsMap n) : DecidableRel (IsKid F) := fun _ _ ↦ by
  unfold IsKid; infer_instance

/-- A plane binary forest whose labels increase along branches: children carry larger
labels than their parent, the two children of a vertex are distinct, and every vertex has
at most one parent. -/
def IsPlaneForest (F : KidsMap n) : Prop :=
  (∀ w a c, F w = some (a, c) → w < a ∧ w < c ∧ a ≠ c) ∧
    ∀ w w' v, IsKid F w v → IsKid F w' v → w = w'

instance : DecidablePred (IsPlaneForest (n := n)) := fun _ ↦ by
  unfold IsPlaneForest; infer_instance

/-- The number of trees of a forest: the number of vertices without parent. -/
def rootCount (F : KidsMap n) : ℕ :=
  (Finset.univ.filter fun v ↦ ∀ w, ¬ IsKid F w v).card

/-- `v` is a descendant of `w` (or `w` itself). -/
def Desc (F : KidsMap n) (w v : Fin n) : Prop :=
  Relation.ReflTransGen (IsKid F) w v

variable {F : KidsMap n}

theorem isKid_iff_of_eq {w a c : Fin n} (h : F w = some (a, c)) (v : Fin n) :
    IsKid F w v ↔ v = a ∨ v = c := by
  constructor
  · rintro ⟨a', c', h', hv⟩
    rw [h] at h'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact hv
  · exact fun hv ↦ ⟨a, c, h, hv⟩

theorem isKid_iff_of_eq_some {w : Fin n} {p : Fin n × Fin n} (h : F w = some p) (v : Fin n) :
    IsKid F w v ↔ v = p.1 ∨ v = p.2 := by
  obtain ⟨a, c⟩ := p
  exact isKid_iff_of_eq h v

theorem not_isKid_of_eq_none {w : Fin n} (h : F w = none) (v : Fin n) : ¬ IsKid F w v := by
  rintro ⟨a, c, h', -⟩
  rw [h] at h'
  cases h'

theorem IsPlaneForest.lt (hF : IsPlaneForest F) {w v : Fin n} (h : IsKid F w v) : w < v := by
  obtain ⟨a, c, h, hv | hv⟩ := h
  · rw [hv]; exact (hF.1 w a c h).1
  · rw [hv]; exact (hF.1 w a c h).2.1

theorem IsPlaneForest.desc_le (hF : IsPlaneForest F) {w v : Fin n} (h : Desc F w v) : w ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hk ih => exact ih.trans (hF.lt hk).le

theorem Desc.refl (w : Fin n) : Desc F w w := Relation.ReflTransGen.refl

theorem Desc.trans {u v w : Fin n} (h₁ : Desc F u v) (h₂ : Desc F v w) : Desc F u w :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Desc.of_kid {w v : Fin n} (h : IsKid F w v) : Desc F w v :=
  Relation.ReflTransGen.single h

theorem Desc.head {u w v : Fin n} (h : IsKid F u w) (h' : Desc F w v) : Desc F u v :=
  Relation.ReflTransGen.head h h'

theorem Desc.exists_kid {w v : Fin n} (h : Desc F w v) (hne : w ≠ v) :
    ∃ y, IsKid F w y ∧ Desc F y v := by
  rcases Relation.ReflTransGen.cases_head h with h | h
  · exact absurd h hne
  · exact h

theorem Desc.eq_of_none {w v : Fin n} (hw : F w = none) (h : Desc F w v) : v = w := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨y, hy, -⟩
  · exact h.symm
  · exact absurd hy (not_isKid_of_eq_none hw y)

theorem IsPlaneForest.desc_antisymm (hF : IsPlaneForest F) {w v : Fin n} (h₁ : Desc F w v)
    (h₂ : Desc F v w) : w = v :=
  le_antisymm (hF.desc_le h₁) (hF.desc_le h₂)

/-- A proper ancestor of a child is an ancestor of its parent. -/
theorem IsPlaneForest.desc_parent (hF : IsPlaneForest F) {w a u : Fin n} (hk : IsKid F w a)
    (h : Desc F u a) (hne : u ≠ a) : Desc F u w := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨y, hy, hya⟩
  · exact absurd h.symm hne
  · rw [hF.2 w y a hk hya]
    exact hy

/-- The ancestors of a vertex form a chain. -/
theorem IsPlaneForest.desc_total (hF : IsPlaneForest F) {u u' x : Fin n} (h : Desc F u x)
    (h' : Desc F u' x) : Desc F u u' ∨ Desc F u' u := by
  induction h generalizing u' with
  | refl => exact Or.inr h'
  | @tail y z hy hyz ih =>
    rcases Relation.ReflTransGen.cases_tail h' with h' | ⟨y', hy', hy'z⟩
    · subst h'
      exact Or.inl (hy.tail hyz)
    · rw [hF.2 y' y z hy'z hyz] at hy'
      exact ih hy'

/-- Distinct children of a vertex have no common descendant. -/
theorem IsPlaneForest.desc_disjoint (hF : IsPlaneForest F) {w a c : Fin n}
    (h : F w = some (a, c)) {x : Fin n} (ha : Desc F a x) (hc : Desc F c x) : False := by
  have hka : IsKid F w a := ⟨a, c, h, Or.inl rfl⟩
  have hkc : IsKid F w c := ⟨a, c, h, Or.inr rfl⟩
  have hac := (hF.1 w a c h).2.2
  rcases hF.desc_total ha hc with h' | h'
  · have := hF.desc_le (hF.desc_parent hkc h' hac)
    exact absurd (hF.1 w a c h).1 (not_lt.mpr this)
  · have := hF.desc_le (hF.desc_parent hka h' (Ne.symm hac))
    exact absurd (hF.1 w a c h).2.1 (not_lt.mpr this)

end PlaneForest


/-! ### Labelled forests and the forests determined by clusters -/

section Labelled

variable {k m n : ℕ}

theorem vertex_cases (e : Fin k ⊕ Fin m ≃ Fin n) (v : Fin n) :
    (∃ j, e (.inl j) = v) ∨ ∃ s, e (.inr s) = v := by
  rcases h : e.symm v with j | s
  · exact Or.inl ⟨j, by rw [← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨s, by rw [← h, Equiv.apply_symm_apply]⟩

/-- A forest fits the event labelling `e`: its leaves are the vertices `e (inl j)` of the
births and its internal vertices are the vertices `e (inr s)` of the merges. -/
def Fits (F : KidsMap n) (e : Fin k ⊕ Fin m ≃ Fin n) : Prop :=
  IsPlaneForest F ∧ (∀ j, F (e (.inl j)) = none) ∧ ∀ s, F (e (.inr s)) ≠ none

/-- The particles below `w`: those whose leaf `e (inl j)` descends from `w`. -/
def leafSet (F : KidsMap n) (e : Fin k ⊕ Fin m ≃ Fin n) (w : Fin n) : Set (Fin k) :=
  {j | Desc F w (e (.inl j))}

/-- `u` is a child of `v` in the forest determined by the clusters `C`: `v` is a merge
vertex below `u` whose cluster contains that of `u`, and no merge vertex strictly between
them has this property. -/
def IsParent (e : Fin k ⊕ Fin m ≃ Fin n) (C : Fin n → Set (Fin k)) (v u : Fin n) : Prop :=
  v < u ∧ (∃ s, e (.inr s) = v) ∧ C u ⊆ C v ∧
    ∀ w, v < w → w < u → (∃ s, e (.inr s) = w) → ¬ C u ⊆ C w

open Classical in
/-- The children of `v` in the forest determined by the clusters `C`. -/
noncomputable def kidSet (e : Fin k ⊕ Fin m ≃ Fin n) (C : Fin n → Set (Fin k)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (IsParent e C v)

/-- The children of a vertex in increasing order. -/
def kidPair (S : Finset (Fin n)) : Option (Fin n × Fin n) :=
  if h : S.Nonempty then some (S.min' h, S.max' h) else none

/-- Exchanging the two children when `σ = true`. -/
def orient (σ : Bool) (p : Fin n × Fin n) : Fin n × Fin n :=
  if σ then p.swap else p

/-- The plane forest determined by the clusters `C` and the child orders `σ`: the vertex of
the `s`-th merge has its two children ordered increasingly, exchanged when `σ s = true`. -/
noncomputable def histKids (e : Fin k ⊕ Fin m ≃ Fin n) (C : Fin n → Set (Fin k))
    (σ : Fin m → Bool) : KidsMap n := fun v ↦
  match e.symm v with
  | .inl _ => none
  | .inr s => (kidPair (kidSet e C v)).map (orient (σ s))

/-- The child orders of a plane forest: `true` when the left child carries the larger
label. -/
def forestOrders (e : Fin k ⊕ Fin m ≃ Fin n) (F : KidsMap n) : Fin m → Bool := fun s ↦
  match F (e (.inr s)) with
  | some (a, c) => decide (c < a)
  | none => false

@[simp] theorem histKids_inl (e : Fin k ⊕ Fin m ≃ Fin n) (C : Fin n → Set (Fin k))
    (σ : Fin m → Bool) (j : Fin k) : histKids e C σ (e (.inl j)) = none := by
  simp [histKids]

theorem histKids_inr (e : Fin k ⊕ Fin m ≃ Fin n) (C : Fin n → Set (Fin k))
    (σ : Fin m → Bool) (s : Fin m) : histKids e C σ (e (.inr s)) =
      (kidPair (kidSet e C (e (.inr s)))).map (orient (σ s)) := by
  simp [histKids]

theorem mem_kidSet {e : Fin k ⊕ Fin m ≃ Fin n} {C : Fin n → Set (Fin k)} {v u : Fin n} :
    u ∈ kidSet e C v ↔ IsParent e C v u := by
  classical
  simp [kidSet]

theorem kidPair_pair (a c : Fin n) : kidPair {a, c} = some (min a c, max a c) := by
  have hne : ({a, c} : Finset (Fin n)).Nonempty := Finset.insert_nonempty _ _
  simp only [kidPair, hne, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [Finset.min'_insert _ _ (Finset.singleton_nonempty c), Finset.min'_singleton, min_comm]
  · rw [Finset.max'_insert _ _ (Finset.singleton_nonempty c), Finset.max'_singleton, max_comm]

theorem orient_min_max {a c : Fin n} (h : a ≠ c) :
    orient (decide (c < a)) (min a c, max a c) = (a, c) := by
  rcases lt_or_gt_of_ne h with hac | hac
  · simp [orient, not_lt.mpr hac.le, min_eq_left hac.le, max_eq_right hac.le]
  · simp [orient, hac, min_eq_right hac.le, max_eq_left hac.le]

variable {F : KidsMap n} {e : Fin k ⊕ Fin m ≃ Fin n}

theorem Fits.not_inl (hF : Fits F e) {v : Fin n} (hv : F v ≠ none) : ∃ s, e (.inr s) = v := by
  rcases vertex_cases e v with ⟨j, rfl⟩ | h
  · exact absurd (hF.2.1 j) hv
  · exact h

theorem Fits.exists_kids (hF : Fits F e) {v : Fin n} (hv : ∃ s, e (.inr s) = v) :
    ∃ a c, F v = some (a, c) := by
  obtain ⟨s, rfl⟩ := hv
  obtain ⟨⟨a, c⟩, h⟩ := Option.ne_none_iff_exists'.mp (hF.2.2 s)
  exact ⟨a, c, h⟩

theorem Fits.internal_of_desc (hF : Fits F e) {w v : Fin n} (h : Desc F w v) (hne : w ≠ v) :
    ∃ s, e (.inr s) = w := by
  obtain ⟨y, hy, -⟩ := h.exists_kid hne
  refine hF.not_inl fun hw ↦ ?_
  exact not_isKid_of_eq_none hw y hy

theorem Fits.leafSet_inl (hF : Fits F e) (j : Fin k) : leafSet F e (e (.inl j)) = {j} := by
  ext l
  simp only [leafSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Sum.inl_injective (e.injective (h.eq_of_none (hF.2.1 j)))
  · rintro rfl
    exact Desc.refl _

theorem Fits.leafSet_mono (_hF : Fits F e) {w u : Fin n} (h : Desc F w u) :
    leafSet F e u ⊆ leafSet F e w :=
  fun _ hj ↦ h.trans hj

theorem Fits.leafSet_nonempty (hF : Fits F e) (v : Fin n) : (leafSet F e v).Nonempty := by
  induction v using WellFoundedGT.induction with
  | _ v ih =>
    rcases vertex_cases e v with ⟨j, rfl⟩ | hv
    · rw [hF.leafSet_inl]
      exact Set.singleton_nonempty j
    · obtain ⟨a, c, h⟩ := hF.exists_kids hv
      have hka : IsKid F v a := ⟨a, c, h, Or.inl rfl⟩
      obtain ⟨j, hj⟩ := ih a (hF.1.lt hka)
      exact ⟨j, hF.leafSet_mono (Desc.of_kid hka) hj⟩

theorem Fits.leafSet_kids (hF : Fits F e) {w a c : Fin n} (h : F w = some (a, c)) :
    leafSet F e w = leafSet F e a ∪ leafSet F e c := by
  ext j
  simp only [leafSet, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro hj
    have hne : w ≠ e (.inl j) := fun he ↦ by
      rw [he, hF.2.1 j] at h
      cases h
    obtain ⟨y, hy, hyj⟩ := hj.exists_kid hne
    rcases (isKid_iff_of_eq h y).mp hy with rfl | rfl
    · exact Or.inl hyj
    · exact Or.inr hyj
  · rintro (hj | hj)
    · exact Desc.head ⟨a, c, h, Or.inl rfl⟩ hj
    · exact Desc.head ⟨a, c, h, Or.inr rfl⟩ hj

theorem Fits.leafSet_disjoint (hF : Fits F e) {w a c : Fin n} (h : F w = some (a, c)) :
    Disjoint (leafSet F e a) (leafSet F e c) :=
  Set.disjoint_left.mpr fun _ ha hc ↦ hF.1.desc_disjoint h ha hc

/-- In a forest fitting `e`, the children determined by the particle sets below the
vertices are the children of the forest. -/
theorem Fits.isParent_iff (hF : Fits F e) {v u : Fin n} :
    IsParent e (leafSet F e) v u ↔ IsKid F v u := by
  constructor
  · rintro ⟨hvu, hv, hsub, hmin⟩
    obtain ⟨j, hj⟩ := hF.leafSet_nonempty u
    have hvj : Desc F v (e (.inl j)) := hsub hj
    rcases hF.1.desc_total hvj hj with hd | hd
    · obtain ⟨y, hy, hyu⟩ := hd.exists_kid hvu.ne
      by_cases hyu' : y = u
      · rw [← hyu']
        exact hy
      · exfalso
        have hylt : y < u := lt_of_le_of_ne (hF.1.desc_le hyu) hyu'
        exact hmin y (hF.1.lt hy) hylt (hF.internal_of_desc hyu hyu')
          (hF.leafSet_mono hyu)
    · exact absurd (hF.1.desc_le hd) (not_le.mpr hvu)
  · intro hk
    obtain ⟨a, c, h, -⟩ := id hk
    refine ⟨hF.1.lt hk, hF.not_inl (by rw [h]; exact Option.some_ne_none _),
      hF.leafSet_mono (Desc.of_kid hk), fun w hvw hwu _ hsub ↦ ?_⟩
    obtain ⟨j, hj⟩ := hF.leafSet_nonempty u
    rcases hF.1.desc_total (hsub hj) hj with hd | hd
    · have := hF.1.desc_le (hF.1.desc_parent hk hd (ne_of_lt hwu))
      exact absurd hvw (not_lt.mpr this)
    · exact absurd (hF.1.desc_le hd) (not_le.mpr hwu)

theorem Fits.kidSet_eq (hF : Fits F e) {v a c : Fin n} (h : F v = some (a, c)) :
    kidSet e (leafSet F e) v = {a, c} := by
  ext u
  rw [mem_kidSet, hF.isParent_iff, isKid_iff_of_eq h, Finset.mem_insert, Finset.mem_singleton]

/-- **The forest is recovered from its particle sets and child orders.** -/
theorem Fits.histKids_leafSet (hF : Fits F e) :
    histKids e (leafSet F e) (forestOrders e F) = F := by
  funext v
  rcases vertex_cases e v with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · rw [histKids_inl, hF.2.1 j]
  · obtain ⟨a, c, h⟩ := hF.exists_kids ⟨s, rfl⟩
    have hac := (hF.1.1 _ a c h).2.2
    rw [histKids_inr, hF.kidSet_eq h, kidPair_pair a c, h, Option.map_some]
    have hσ : forestOrders e F s = decide (c < a) := by simp [forestOrders, h]
    rw [hσ, orient_min_max hac]

end Labelled


/-! ### Merge histories as event-labelled clusters -/

section History

variable {k m n : ℕ}

/-- The states of a merge history started from singletons: `stateSeq xs 0 = diagState` and
`stateSeq xs (s + 1) = xs s`. -/
def stateSeq (xs : Fin m → ConnState k) : Fin (m + 1) → ConnState k :=
  Fin.cons diagState xs

/-- The cluster formed by the `s`-th merge: the particles that gain a relation. -/
def mergedSet (xs : Fin m → ConnState k) (s : Fin m) : Set (Fin k) :=
  {j | ∃ l, stateSeq xs s.succ j l = true ∧ stateSeq xs s.castSucc j l = false}

/-- The particles born before the `s`-th merge, for a labelling `ρ` of the events increasing
in time. -/
def bornSet (ρ : Fin k ⊕ Fin m → Fin n) (s : Fin m) : Finset (Fin k) :=
  Finset.univ.filter fun j ↦ ρ (.inr s) < ρ (.inl j)

/-- Admissibility of a merge history for a labelling `ρ` of the events increasing in time:
the merge labels decrease along the history, and each merge joins two distinct clusters of
particles born before it. -/
def DAdm (ρ : Fin k ⊕ Fin m → Fin n) (xs : Fin m → ConnState k) : Prop :=
  StrictAnti (fun s ↦ ρ (.inr s)) ∧
    ∀ s, IsMergeStep (bornSet ρ s) (stateSeq xs s.castSucc) (stateSeq xs s.succ)

/-- The cluster of a vertex: its particle for a birth vertex, the cluster formed by the merge
for a merge vertex. -/
def clusterOf (e : Fin k ⊕ Fin m ≃ Fin n) (xs : Fin m → ConnState k) (v : Fin n) :
    Set (Fin k) :=
  match e.symm v with
  | .inl j => {j}
  | .inr s => mergedSet xs s

/-- **The plane forest of a plane history** `(xs, σ)` for the event labelling `e`. -/
noncomputable def histForest (e : Fin k ⊕ Fin m ≃ Fin n) (xs : Fin m → ConnState k)
    (σ : Fin m → Bool) : KidsMap n :=
  histKids e (clusterOf e xs) σ

@[simp] theorem stateSeq_zero (xs : Fin m → ConnState k) : stateSeq xs 0 = diagState := rfl

@[simp] theorem stateSeq_succ (xs : Fin m → ConnState k) (s : Fin m) :
    stateSeq xs s.succ = xs s := by
  simp [stateSeq]

@[simp] theorem clusterOf_inl (e : Fin k ⊕ Fin m ≃ Fin n) (xs : Fin m → ConnState k) (j : Fin k) :
    clusterOf e xs (e (.inl j)) = {j} := by
  simp [clusterOf]

@[simp] theorem clusterOf_inr (e : Fin k ⊕ Fin m ≃ Fin n) (xs : Fin m → ConnState k) (s : Fin m) :
    clusterOf e xs (e (.inr s)) = mergedSet xs s := by
  simp [clusterOf]

theorem mem_bornSet {ρ : Fin k ⊕ Fin m → Fin n} {s : Fin m} {j : Fin k} :
    j ∈ bornSet ρ s ↔ ρ (.inr s) < ρ (.inl j) := by
  simp [bornSet]

/-- A merge of the clusters of `j₀` and `l₀` relates two particles when they were related
or each of them is in one of the two clusters. -/
theorem mergeState_iff_classes {β : Finset (Fin k)} {x : ConnState k} (hx : IsValid β x)
    (j₀ l₀ j l : Fin k) : mergeState x j₀ l₀ j l = true ↔ x j l = true ∨
      ((x j j₀ = true ∨ x j l₀ = true) ∧ (x l j₀ = true ∨ x l l₀ = true)) := by
  rw [mergeState_iff]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl h1, Or.inr h2⟩
    · exact Or.inr ⟨Or.inr h1, Or.inl h2⟩
  · rintro (h | ⟨h1 | h1, h2 | h2⟩)
    · exact Or.inl h
    · exact Or.inl (hx.trans j j₀ l h1 (hx.symm l j₀ h2))
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · exact Or.inl (hx.trans j l₀ l h1 (hx.symm l l₀ h2))

theorem newPairs_mergeState {β : Finset (Fin k)} {x : ConnState k} (hx : IsValid β x)
    {j₀ l₀ : Fin k} (h0 : x j₀ l₀ = false) :
    {j | ∃ l, mergeState x j₀ l₀ j l = true ∧ x j l = false} =
      {j | x j j₀ = true ∨ x j l₀ = true} := by
  ext j
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨l, h1, h2⟩
    rcases (mergeState_iff_classes hx j₀ l₀ j l).mp h1 with h | ⟨h, -⟩
    · rw [h] at h2
      cases h2
    · exact h
  · rintro (h | h)
    · refine ⟨l₀, (mergeState_iff_classes hx j₀ l₀ j l₀).mpr
        (Or.inr ⟨Or.inl h, Or.inr (hx.refl l₀)⟩), ?_⟩
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [hx.trans j₀ j l₀ (hx.symm j j₀ h) hc] at h0
      cases h0
    · refine ⟨j₀, (mergeState_iff_classes hx j₀ l₀ j j₀).mpr
        (Or.inr ⟨Or.inr h, Or.inl (hx.refl j₀)⟩), ?_⟩
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [hx.trans j₀ j l₀ (hx.symm j j₀ hc) h] at h0
      cases h0

variable {ρ : Fin k ⊕ Fin m → Fin n} {xs : Fin m → ConnState k}

theorem DAdm.anti (hA : DAdm ρ xs) : StrictAnti (fun s ↦ ρ (.inr s)) := hA.1

theorem DAdm.bornSet_mono (hA : DAdm ρ xs) {i s : Fin m} (h : i ≤ s) :
    bornSet ρ i ⊆ bornSet ρ s := fun j hj ↦ by
  rw [mem_bornSet] at hj ⊢
  exact lt_of_le_of_lt (hA.anti.antitone h) hj

theorem DAdm.valid (hA : DAdm ρ xs) (s : Fin m) :
    IsValid (bornSet ρ s) (stateSeq xs s.castSucc) ∧ IsValid (bornSet ρ s) (stateSeq xs s.succ) := by
  have key : ∀ t : Fin (m + 1), ∀ s : Fin m, t ≤ s.castSucc →
      IsValid (bornSet ρ s) (stateSeq xs t) := by
    intro t
    induction t using Fin.induction with
    | zero => intro s _; exact isValid_diagState _
    | succ i ih =>
      intro s hs
      have hi : i ≤ s := by
        rw [Fin.le_def] at hs ⊢
        simp only [Fin.val_succ, Fin.val_castSucc] at hs
        omega
      have h1 := ih i le_rfl
      exact (h1.isMergeStep (subset_refl _) (hA.2 i)).mono (hA.bornSet_mono hi)
  have h1 := key s.castSucc s le_rfl
  exact ⟨h1, h1.isMergeStep (subset_refl _) (hA.2 s)⟩

theorem DAdm.succ_iff (hA : DAdm ρ xs) (s : Fin m) (j l : Fin k) :
    stateSeq xs s.succ j l = true ↔
      stateSeq xs s.castSucc j l = true ∨ (j ∈ mergedSet xs s ∧ l ∈ mergedSet xs s) := by
  obtain ⟨hv, -⟩ := hA.valid s
  obtain ⟨-, j₀, -, l₀, -, h0, he⟩ := hA.2 s
  have hK : mergedSet xs s = {j | stateSeq xs s.castSucc j j₀ = true ∨
      stateSeq xs s.castSucc j l₀ = true} := by
    rw [← newPairs_mergeState hv h0, ← he]
    rfl
  rw [hK, he, mergeState_iff_classes hv]
  rfl

theorem DAdm.mergedSet_eq (hA : DAdm ρ xs) (s : Fin m) {j₀ l₀ : Fin k}
    (h0 : stateSeq xs s.castSucc j₀ l₀ = false)
    (he : stateSeq xs s.succ = mergeState (stateSeq xs s.castSucc) j₀ l₀) :
    mergedSet xs s = {j | stateSeq xs s.castSucc j j₀ = true ∨
      stateSeq xs s.castSucc j l₀ = true} := by
  rw [← newPairs_mergeState (hA.valid s).1 h0, ← he]
  rfl

theorem DAdm.stateSeq_iff (hA : DAdm ρ xs) (t : Fin (m + 1)) (j l : Fin k) :
    stateSeq xs t j l = true ↔
      j = l ∨ ∃ i : Fin m, i.castSucc < t ∧ j ∈ mergedSet xs i ∧ l ∈ mergedSet xs i := by
  induction t using Fin.induction with
  | zero =>
    simp only [stateSeq_zero, diagState, decide_eq_true_eq, Fin.not_lt_zero, false_and,
      exists_false, or_false]
  | succ s ih =>
    rw [hA.succ_iff, ih]
    constructor
    · rintro ((h | ⟨i, hi, h1, h2⟩) | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, hi.trans ((Fin.castSucc_lt_succ (i := s))), h1, h2⟩
      · exact Or.inr ⟨s, (Fin.castSucc_lt_succ (i := s)), h1, h2⟩
    · rintro (h | ⟨i, hi, h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases lt_or_eq_of_le (Fin.castSucc_lt_succ_iff.mp hi) with hi' | rfl
        · exact Or.inl (Or.inr ⟨i, Fin.castSucc_lt_castSucc_iff.mpr hi', h1, h2⟩)
        · exact Or.inr ⟨h1, h2⟩

theorem DAdm.stateSeq_mono (hA : DAdm ρ xs) {t t' : Fin (m + 1)} (h : t ≤ t') {j l : Fin k}
    (hjl : stateSeq xs t j l = true) : stateSeq xs t' j l = true := by
  rw [hA.stateSeq_iff] at hjl ⊢
  rcases hjl with h' | ⟨i, hi, h1, h2⟩
  · exact Or.inl h'
  · exact Or.inr ⟨i, lt_of_lt_of_le hi h, h1, h2⟩

theorem DAdm.mem_mergedSet_iff (hA : DAdm ρ xs) {s : Fin m} {j : Fin k} (hj : j ∈ mergedSet xs s)
    (l : Fin k) : l ∈ mergedSet xs s ↔ stateSeq xs s.succ j l = true := by
  obtain ⟨hv, hv'⟩ := hA.valid s
  obtain ⟨-, j₀, -, l₀, -, h0, he⟩ := hA.2 s
  have hK := hA.mergedSet_eq s h0 he
  constructor
  · intro hl
    exact (hA.succ_iff s j l).mpr (Or.inr ⟨hj, hl⟩)
  · intro hjl
    rcases (hA.succ_iff s j l).mp hjl with h | ⟨-, h⟩
    · rw [hK] at hj ⊢
      have hlj := hv.symm j l h
      rcases hj with h' | h'
      · exact Or.inl (hv.trans l j j₀ hlj h')
      · exact Or.inr (hv.trans l j l₀ hlj h')
    · exact h

theorem DAdm.mergedSet_subset (hA : DAdm ρ xs) {i s : Fin m} (his : i ≤ s) {j : Fin k}
    (hi : j ∈ mergedSet xs i) (hs : j ∈ mergedSet xs s) : mergedSet xs i ⊆ mergedSet xs s :=
  fun l hl ↦ (hA.mem_mergedSet_iff hs l).mpr
    (hA.stateSeq_mono (Fin.succ_le_succ_iff.mpr his) ((hA.mem_mergedSet_iff hi l).mp hl))

theorem DAdm.mergedSet_born (hA : DAdm ρ xs) {s : Fin m} {j : Fin k} (hj : j ∈ mergedSet xs s) :
    ρ (.inr s) < ρ (.inl j) := by
  obtain ⟨l, h1, h2⟩ := hj
  have hjl : j ≠ l := by
    rintro rfl
    rw [(hA.valid s).1.refl j] at h2
    cases h2
  exact mem_bornSet.mp ((hA.valid s).2.born j l hjl h1)

theorem DAdm.mem_mergedSet_self (hA : DAdm ρ xs) (s : Fin m) :
    ∃ j₀ l₀, j₀ ∈ mergedSet xs s ∧ l₀ ∈ mergedSet xs s ∧
      stateSeq xs s.castSucc j₀ l₀ = false ∧
      mergedSet xs s = {j | stateSeq xs s.castSucc j j₀ = true ∨
        stateSeq xs s.castSucc j l₀ = true} := by
  obtain ⟨-, j₀, -, l₀, -, h0, he⟩ := hA.2 s
  have hK := hA.mergedSet_eq s h0 he
  have hv := (hA.valid s).1
  refine ⟨j₀, l₀, ?_, ?_, h0, hK⟩
  · rw [hK]; exact Or.inl (hv.refl j₀)
  · rw [hK]; exact Or.inr (hv.refl l₀)

end History


/-! ### The forest of an admissible history -/

section HistoryForest

variable {k m n : ℕ} {e : Fin k ⊕ Fin m ≃ Fin n} {xs : Fin m → ConnState k}

open Classical in
/-- The merge history of a plane forest: after the `s`-th merge, two particles are related
when they lie below a common merge vertex of rank at most `s`. -/
noncomputable def forestStates (e : Fin k ⊕ Fin m ≃ Fin n) (F : KidsMap n) :
    Fin m → ConnState k := fun s j l ↦
  decide (j = l ∨ ∃ i, i ≤ s ∧ j ∈ leafSet F e (e (.inr i)) ∧ l ∈ leafSet F e (e (.inr i)))

theorem DAdm.cluster_nonempty (hA : DAdm e xs) (v : Fin n) : (clusterOf e xs v).Nonempty := by
  rcases vertex_cases e v with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · rw [clusterOf_inl]; exact Set.singleton_nonempty j
  · obtain ⟨j₀, -, hj₀, -⟩ := hA.mem_mergedSet_self s
    rw [clusterOf_inr]; exact ⟨j₀, hj₀⟩

theorem DAdm.cluster_born (hA : DAdm e xs) {s : Fin m} {j : Fin k} (hj : j ∈ mergedSet xs s) :
    e (.inr s) < e (.inl j) :=
  hA.mergedSet_born hj

/-- Clusters are nested: the cluster of a later vertex (in the history order, earlier in
time order) meeting the cluster of a merge vertex is contained in it. -/
theorem DAdm.cluster_subset (hA : DAdm e xs) {u u' : Fin n} (hlt : u' < u)
    (hu' : ∃ s, e (.inr s) = u') {j : Fin k} (hj : j ∈ clusterOf e xs u)
    (hj' : j ∈ clusterOf e xs u') : clusterOf e xs u ⊆ clusterOf e xs u' := by
  obtain ⟨s, rfl⟩ := hu'
  rcases vertex_cases e u with ⟨j'', rfl⟩ | ⟨i, rfl⟩
  · rw [clusterOf_inl] at hj ⊢
    rw [Set.mem_singleton_iff.mp hj] at hj'
    exact Set.singleton_subset_iff.mpr hj'
  · simp only [clusterOf_inr] at hj hj' ⊢
    exact hA.mergedSet_subset ((StrictAnti.lt_iff_gt hA.anti).mp hlt).le hj hj'

/-- The first vertex above the `s`-th merge whose cluster contains a born particle `j` has
the cluster of `j` just before the merge. -/
theorem DAdm.exists_top (hA : DAdm e xs) (s : Fin m) (j : Fin k) (hj : e (.inr s) < e (.inl j)) :
    ∃ u, e (.inr s) < u ∧ j ∈ clusterOf e xs u ∧
      (∀ u', e (.inr s) < u' → j ∈ clusterOf e xs u' → u ≤ u') ∧
      ∀ l, l ∈ clusterOf e xs u ↔ stateSeq xs s.castSucc j l = true := by
  classical
  obtain ⟨u, hu, humin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun u ↦ e (.inr s) < u ∧ j ∈ clusterOf e xs u) id
    ⟨e (.inl j), by simp [hj]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hu humin
  have hmin : ∀ u', e (.inr s) < u' → j ∈ clusterOf e xs u' → u ≤ u' :=
    fun u' h1 h2 ↦ humin u' ⟨h1, h2⟩
  refine ⟨u, hu.1, hu.2, hmin, fun l ↦ ?_⟩
  rw [hA.stateSeq_iff]
  obtain ⟨hu1, hu2⟩ := hu
  rcases vertex_cases e u with ⟨j', rfl⟩ | ⟨i, rfl⟩
  · rw [clusterOf_inl] at hu2 ⊢
    have hjj := Set.mem_singleton_iff.mp hu2
    subst hjj
    constructor
    · intro hl
      exact Or.inl hl.symm
    · rintro (h | ⟨i, hi, hji, -⟩)
      · exact h.symm
      · exfalso
        have h1 : e (.inr s) < e (.inr i) := hA.1 (Fin.castSucc_lt_castSucc_iff.mp hi)
        have h2 := hmin _ h1 (by rw [clusterOf_inr]; exact hji)
        exact absurd h2 (not_le.mpr (hA.cluster_born hji))
  · rw [clusterOf_inr] at hu2 ⊢
    have his : i < s := (StrictAnti.lt_iff_gt hA.anti).mp hu1
    constructor
    · intro hl
      exact Or.inr ⟨i, Fin.castSucc_lt_castSucc_iff.mpr his, hu2, hl⟩
    · rintro (rfl | ⟨i', hi', hji', hli'⟩)
      · exact hu2
      · have h1 : e (.inr s) < e (.inr i') := hA.1 (Fin.castSucc_lt_castSucc_iff.mp hi')
        have h2 : e (.inr i) ≤ e (.inr i') := hmin _ h1 (by rw [clusterOf_inr]; exact hji')
        exact hA.mergedSet_subset ((StrictAnti.le_iff_ge hA.anti).mp h2) hji' hu2 hli'

theorem DAdm.isParent_top (hA : DAdm e xs) {s : Fin m} {j : Fin k} (hj : j ∈ mergedSet xs s)
    {u : Fin n} (hu : e (.inr s) < u) (hju : j ∈ clusterOf e xs u)
    (hmin : ∀ u', e (.inr s) < u' → j ∈ clusterOf e xs u' → u ≤ u')
    (hcl : ∀ l, l ∈ clusterOf e xs u ↔ stateSeq xs s.castSucc j l = true) :
    IsParent e (clusterOf e xs) (e (.inr s)) u := by
  refine ⟨hu, ⟨s, rfl⟩, fun l hl ↦ ?_, fun w hw hwu _ hsub ↦ ?_⟩
  · rw [clusterOf_inr, hA.mem_mergedSet_iff hj, hA.succ_iff]
    exact Or.inl ((hcl l).mp hl)
  · exact absurd (hmin w hw (hsub hju)) (not_le.mpr hwu)

theorem DAdm.eq_top_of_isParent (hA : DAdm e xs) {s : Fin m} {u : Fin n}
    (hP : IsParent e (clusterOf e xs) (e (.inr s)) u) {j : Fin k} (hju : j ∈ clusterOf e xs u)
    {u₀ : Fin n} (hu₀ : e (.inr s) < u₀) (hju₀ : j ∈ clusterOf e xs u₀)
    (hmin₀ : ∀ u', e (.inr s) < u' → j ∈ clusterOf e xs u' → u₀ ≤ u') : u = u₀ := by
  have hle : u₀ ≤ u := hmin₀ u hP.1 hju
  by_contra hne
  have hlt : u₀ < u := lt_of_le_of_ne hle (Ne.symm hne)
  rcases vertex_cases e u₀ with ⟨j', rfl⟩ | ⟨i₀, rfl⟩
  · rw [clusterOf_inl, Set.mem_singleton_iff] at hju₀
    subst hju₀
    rcases vertex_cases e u with ⟨j'', rfl⟩ | ⟨i, rfl⟩
    · rw [clusterOf_inl, Set.mem_singleton_iff] at hju
      subst hju
      exact lt_irrefl _ hlt
    · rw [clusterOf_inr] at hju
      exact absurd hlt (not_lt.mpr (hA.cluster_born hju).le)
  · have hsub := hA.cluster_subset hlt ⟨i₀, rfl⟩ hju hju₀
    exact hP.2.2.2 _ hu₀ hlt ⟨i₀, rfl⟩ hsub


theorem orient_mem_iff (σ : Bool) (a c v : Fin n) :
    (v = (orient σ (a, c)).1 ∨ v = (orient σ (a, c)).2) ↔ v = a ∨ v = c := by
  cases σ <;> simp [orient, or_comm]

theorem min_max_mem_iff (a c v : Fin n) : (v = min a c ∨ v = max a c) ↔ v = a ∨ v = c := by
  rcases le_total a c with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, or_comm]

theorem orient_fst_ne_snd {a c : Fin n} (h : a ≠ c) (σ : Bool) :
    (orient σ (min a c, max a c)).1 ≠ (orient σ (min a c, max a c)).2 := by
  have hmm : min a c ≠ max a c := by
    rcases le_total a c with h' | h'
    · simpa [min_eq_left h', max_eq_right h'] using h
    · simpa [min_eq_right h', max_eq_left h'] using h.symm
  cases σ
  · exact hmm
  · exact Ne.symm hmm

/-- **The two children of a merge vertex** in the forest of an admissible history. -/
theorem DAdm.kidSet_eq (hA : DAdm e xs) (s : Fin m) :
    ∃ u₁ u₂, u₁ ≠ u₂ ∧ kidSet e (clusterOf e xs) (e (.inr s)) = {u₁, u₂} := by
  obtain ⟨j₀, l₀, hj₀, hl₀, h0, hK⟩ := hA.mem_mergedSet_self s
  have hv := (hA.valid s).1
  obtain ⟨u₁, hu₁, hj₁, hmin₁, hcl₁⟩ := hA.exists_top s j₀ (hA.cluster_born hj₀)
  obtain ⟨u₂, hu₂, hj₂, hmin₂, hcl₂⟩ := hA.exists_top s l₀ (hA.cluster_born hl₀)
  refine ⟨u₁, u₂, fun h ↦ ?_, ?_⟩
  · have hl : l₀ ∈ clusterOf e xs u₁ := by
      rw [h]
      exact (hcl₂ l₀).mpr (hv.refl l₀)
    rw [hcl₁, h0] at hl
    cases hl
  · ext u
    rw [mem_kidSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hP
      obtain ⟨j, hj⟩ := hA.cluster_nonempty u
      have hjK : j ∈ mergedSet xs s := by
        have := hP.2.2.1 hj
        rwa [clusterOf_inr] at this
      obtain ⟨u', hu', hj', hmin', hcl'⟩ := hA.exists_top s j (hA.cluster_born hjK)
      have hu'eq : u = u' := hA.eq_top_of_isParent hP hj hu' hj' hmin'
      have hjc : stateSeq xs s.castSucc j j₀ = true ∨ stateSeq xs s.castSucc j l₀ = true := by
        rw [hK] at hjK
        exact hjK
      rw [hu'eq]
      rcases hjc with hjc | hjc
      · left
        exact le_antisymm (hmin' u₁ hu₁ ((hcl₁ j).mpr (hv.symm j j₀ hjc)))
          (hmin₁ u' hu' ((hcl' j₀).mpr hjc))
      · right
        exact le_antisymm (hmin' u₂ hu₂ ((hcl₂ j).mpr (hv.symm j l₀ hjc)))
          (hmin₂ u' hu' ((hcl' l₀).mpr hjc))
    · rintro (rfl | rfl)
      · exact hA.isParent_top hj₀ hu₁ hj₁ hmin₁ hcl₁
      · exact hA.isParent_top hl₀ hu₂ hj₂ hmin₂ hcl₂

theorem DAdm.histForest_inr (hA : DAdm e xs) (σ : Fin m → Bool) (s : Fin m) :
    ∃ u₁ u₂, u₁ ≠ u₂ ∧ kidSet e (clusterOf e xs) (e (.inr s)) = {u₁, u₂} ∧
      histForest e xs σ (e (.inr s)) = some (orient (σ s) (min u₁ u₂, max u₁ u₂)) := by
  obtain ⟨u₁, u₂, hne, hK⟩ := hA.kidSet_eq s
  refine ⟨u₁, u₂, hne, hK, ?_⟩
  rw [histForest, histKids_inr, hK, kidPair_pair, Option.map_some]

/-- The cluster of a merge vertex is the union of the clusters of its children. -/
theorem DAdm.mem_mergedSet_iff_parent (hA : DAdm e xs) (s : Fin m) (j : Fin k) :
    j ∈ mergedSet xs s ↔
      ∃ u, IsParent e (clusterOf e xs) (e (.inr s)) u ∧ j ∈ clusterOf e xs u := by
  constructor
  · intro hj
    obtain ⟨u, hu, hju, hmin, hcl⟩ := hA.exists_top s j (hA.cluster_born hj)
    exact ⟨u, hA.isParent_top hj hu hju hmin hcl, hju⟩
  · rintro ⟨u, hP, hju⟩
    have := hP.2.2.1 hju
    rwa [clusterOf_inr] at this

theorem DAdm.isKid_iff (hA : DAdm e xs) (σ : Fin m → Bool) {v u : Fin n} :
    IsKid (histForest e xs σ) v u ↔ IsParent e (clusterOf e xs) v u := by
  rcases vertex_cases e v with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · have h0 : histForest e xs σ (e (.inl j)) = none := histKids_inl _ _ _ _
    constructor
    · intro h
      exact absurd h (not_isKid_of_eq_none h0 u)
    · rintro ⟨-, ⟨s, hs⟩, -⟩
      exact absurd (e.injective hs) (by simp)
  · obtain ⟨u₁, u₂, -, hK, hH⟩ := hA.histForest_inr σ s
    rw [isKid_iff_of_eq_some hH, orient_mem_iff, min_max_mem_iff, ← mem_kidSet, hK,
      Finset.mem_insert, Finset.mem_singleton]

/-- **The forest of an admissible history** is a plane forest whose leaves are the births and
whose internal vertices are the merges. -/
theorem DAdm.fits (hA : DAdm e xs) (σ : Fin m → Bool) : Fits (histForest e xs σ) e := by
  refine ⟨⟨fun w a c h ↦ ?_, fun w w' v h h' ↦ ?_⟩, fun j ↦ histKids_inl _ _ _ _, fun s ↦ ?_⟩
  · have ha := (hA.isKid_iff σ).mp ⟨a, c, h, Or.inl rfl⟩
    have hc := (hA.isKid_iff σ).mp ⟨a, c, h, Or.inr rfl⟩
    refine ⟨ha.1, hc.1, fun hac ↦ ?_⟩
    obtain ⟨s, rfl⟩ := ha.2.1
    obtain ⟨u₁, u₂, hne, -, hH⟩ := hA.histForest_inr σ s
    rw [hH, Option.some.injEq] at h
    exact orient_fst_ne_snd hne (σ s) (by rw [h]; exact hac)
  · have hP := (hA.isKid_iff σ).mp h
    have hP' := (hA.isKid_iff σ).mp h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hP.2.2.2 w' hlt hP'.1 hP'.2.1 hP'.2.2.1
    · exact hP'.2.2.2 w hlt hP.1 hP.2.1 hP.2.2.1
  · obtain ⟨u₁, u₂, -, -, hH⟩ := hA.histForest_inr σ s
    rw [hH]
    exact Option.some_ne_none _

/-- The particles below each vertex of the forest of an admissible history are the
clusters of the history. -/
theorem DAdm.leafSet_histForest (hA : DAdm e xs) (σ : Fin m → Bool) :
    leafSet (histForest e xs σ) e = clusterOf e xs := by
  funext v
  induction v using WellFoundedGT.induction with
  | _ v ih =>
    ext j
    have hdesc : Desc (histForest e xs σ) v (e (.inl j)) ↔ e (.inl j) = v ∨
        ∃ y, IsParent e (clusterOf e xs) v y ∧ j ∈ clusterOf e xs y := by
      constructor
      · intro h
        rcases Relation.ReflTransGen.cases_head h with h | ⟨y, hy, hyj⟩
        · exact Or.inl h.symm
        · have hP := (hA.isKid_iff σ).mp hy
          refine Or.inr ⟨y, hP, ?_⟩
          rw [← ih y hP.1]
          exact hyj
      · rintro (h | ⟨y, hP, hj⟩)
        · rw [h]
          exact Desc.refl _
        · rw [← ih y hP.1] at hj
          exact Desc.head ((hA.isKid_iff σ).mpr hP) hj
    change Desc (histForest e xs σ) v (e (.inl j)) ↔ _
    rw [hdesc]
    rcases vertex_cases e v with ⟨j₀, rfl⟩ | ⟨s, rfl⟩
    · rw [clusterOf_inl, Set.mem_singleton_iff]
      constructor
      · rintro (h | ⟨y, hP, -⟩)
        · exact Sum.inl_injective (e.injective h)
        · obtain ⟨s, hs⟩ := hP.2.1
          exact absurd (e.injective hs) (by simp)
      · rintro rfl
        exact Or.inl rfl
    · rw [clusterOf_inr, hA.mem_mergedSet_iff_parent]
      constructor
      · rintro (h | h)
        · exact absurd (e.injective h) (by simp)
        · exact h
      · exact Or.inr

theorem DAdm.forestStates_histForest (hA : DAdm e xs) (σ : Fin m → Bool) :
    forestStates e (histForest e xs σ) = xs := by
  funext s j l
  have hx : xs s j l = stateSeq xs s.succ j l := by rw [stateSeq_succ]
  rw [hx]
  apply Bool.eq_iff_iff.mpr
  rw [hA.stateSeq_iff]
  simp only [forestStates, decide_eq_true_eq, hA.leafSet_histForest]
  simp only [clusterOf_inr, Fin.castSucc_lt_succ_iff]

theorem DAdm.forestOrders_histForest (hA : DAdm e xs) (σ : Fin m → Bool) :
    forestOrders e (histForest e xs σ) = σ := by
  funext s
  obtain ⟨u₁, u₂, hne, -, hH⟩ := hA.histForest_inr σ s
  have hlt : min u₁ u₂ < max u₁ u₂ := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa [min_eq_left h.le, max_eq_right h.le] using h
    · simpa [min_eq_right h.le, max_eq_left h.le] using h
  simp only [forestOrders, hH]
  cases hσ : σ s
  · simp [orient, not_lt.mpr hlt.le]
  · simp [orient, hlt]

end HistoryForest

/-! ### The merge history of a labelled plane forest -/

section ForestHistory

variable {k m n : ℕ} {e : Fin k ⊕ Fin m ≃ Fin n} {F : KidsMap n}

theorem stateSeq_forestStates_iff (t : Fin (m + 1)) (j l : Fin k) :
    stateSeq (forestStates e F) t j l = true ↔ j = l ∨ ∃ i : Fin m, i.castSucc < t ∧
      j ∈ leafSet F e (e (.inr i)) ∧ l ∈ leafSet F e (e (.inr i)) := by
  refine Fin.cases ?_ (fun s ↦ ?_) t
  · simp [diagState]
  · rw [stateSeq_succ]
    simp only [forestStates, decide_eq_true_eq, Fin.castSucc_lt_succ_iff]

theorem stateSeq_forestStates_succ_iff (s : Fin m) (j l : Fin k) :
    stateSeq (forestStates e F) s.succ j l = true ↔
      stateSeq (forestStates e F) s.castSucc j l = true ∨
        (j ∈ leafSet F e (e (.inr s)) ∧ l ∈ leafSet F e (e (.inr s))) := by
  rw [stateSeq_forestStates_iff, stateSeq_forestStates_iff]
  constructor
  · rintro (h | ⟨i, hi, h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · rcases lt_or_eq_of_le (Fin.castSucc_lt_succ_iff.mp hi) with hi' | rfl
      · exact Or.inl (Or.inr ⟨i, Fin.castSucc_lt_castSucc_iff.mpr hi', h1, h2⟩)
      · exact Or.inr ⟨h1, h2⟩
  · rintro ((h | ⟨i, hi, h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi.trans (Fin.castSucc_lt_succ (i := s)), h1, h2⟩
    · exact Or.inr ⟨s, Fin.castSucc_lt_succ (i := s), h1, h2⟩

/-- Before the `s`-th merge, the particles related to a particle below a child `y` of the
merge vertex are those below `y`. -/
theorem Fits.stateSeq_class (hF : Fits F e) (hanti : StrictAnti fun s ↦ e (.inr s)) {s : Fin m}
    {y : Fin n} (hy : IsKid F (e (.inr s)) y) {j₀ : Fin k} (hj₀ : j₀ ∈ leafSet F e y)
    (j : Fin k) : stateSeq (forestStates e F) s.castSucc j j₀ = true ↔ j ∈ leafSet F e y := by
  rw [stateSeq_forestStates_iff]
  constructor
  · rintro (rfl | ⟨i, hi, hj, hj₀'⟩)
    · exact hj₀
    · have hwi : e (.inr s) < e (.inr i) := hanti (Fin.castSucc_lt_castSucc_iff.mp hi)
      rcases hF.1.desc_total hj₀' hj₀ with hd | hd
      · by_cases hiy : e (.inr i) = y
        · rw [← hiy]
          exact hj
        · have := hF.1.desc_le (hF.1.desc_parent hy hd hiy)
          exact absurd hwi (not_lt.mpr this)
      · exact hF.leafSet_mono hd hj
  · intro hj
    by_cases hjj : j = j₀
    · exact Or.inl hjj
    · right
      have hyne : y ≠ e (.inl j₀) := by
        intro hy'
        rw [hy', hF.leafSet_inl, Set.mem_singleton_iff] at hj
        exact hjj hj
      obtain ⟨i, rfl⟩ := hF.internal_of_desc hj₀ hyne
      exact ⟨i, Fin.castSucc_lt_castSucc_iff.mpr ((StrictAnti.lt_iff_gt hanti).mp (hF.1.lt hy)),
        hj, hj₀⟩

/-- **The merge history of a labelled plane forest is admissible.** -/
theorem Fits.dAdm (hF : Fits F e) (hanti : StrictAnti fun s ↦ e (.inr s)) :
    DAdm e (forestStates e F) := by
  refine ⟨hanti, fun s ↦ ?_⟩
  obtain ⟨a, c, h⟩ := hF.exists_kids ⟨s, rfl⟩
  have hka : IsKid F (e (.inr s)) a := ⟨a, c, h, Or.inl rfl⟩
  have hkc : IsKid F (e (.inr s)) c := ⟨a, c, h, Or.inr rfl⟩
  obtain ⟨j₀, hj₀⟩ := hF.leafSet_nonempty a
  obtain ⟨l₀, hl₀⟩ := hF.leafSet_nonempty c
  have hdisj := Set.disjoint_left.mp (hF.leafSet_disjoint h)
  have hLw := hF.leafSet_kids h
  have born : ∀ j, j ∈ leafSet F e (e (.inr s)) → j ∈ bornSet e s := fun j hj ↦ by
    rw [mem_bornSet]
    exact lt_of_le_of_ne (hF.1.desc_le hj) (fun h' ↦ by simpa using e.injective h')
  have hj₀w : j₀ ∈ leafSet F e (e (.inr s)) := by rw [hLw]; exact Or.inl hj₀
  have hl₀w : l₀ ∈ leafSet F e (e (.inr s)) := by rw [hLw]; exact Or.inr hl₀
  have h0 : stateSeq (forestStates e F) s.castSucc j₀ l₀ = false := by
    rw [← Bool.not_eq_true, hF.stateSeq_class hanti hkc hl₀ j₀]
    exact hdisj hj₀
  have he : stateSeq (forestStates e F) s.succ =
      mergeState (stateSeq (forestStates e F) s.castSucc) j₀ l₀ := by
    funext j l
    apply Bool.eq_iff_iff.mpr
    rw [stateSeq_forestStates_succ_iff, mergeState_iff, hF.stateSeq_class hanti hka hj₀ j,
      hF.stateSeq_class hanti hkc hl₀ l, hF.stateSeq_class hanti hkc hl₀ j,
      hF.stateSeq_class hanti hka hj₀ l, hLw]
    constructor
    · rintro (h | ⟨hj | hj, hl | hl⟩)
      · exact Or.inl h
      · exact Or.inl ((hF.stateSeq_class hanti hka hl j).mpr hj)
      · exact Or.inr (Or.inl ⟨hj, hl⟩)
      · exact Or.inr (Or.inr ⟨hj, hl⟩)
      · exact Or.inl ((hF.stateSeq_class hanti hkc hl j).mpr hj)
    · rintro (h | ⟨hj, hl⟩ | ⟨hj, hl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl hj, Or.inr hl⟩
      · exact Or.inr ⟨Or.inr hj, Or.inl hl⟩
  refine ⟨fun hc ↦ ?_, j₀, born j₀ hj₀w, l₀, born l₀ hl₀w, h0, he⟩
  have h1 : stateSeq (forestStates e F) s.succ j₀ l₀ = true :=
    (stateSeq_forestStates_succ_iff s j₀ l₀).mpr (Or.inr ⟨hj₀w, hl₀w⟩)
  rw [hc, h0] at h1
  cases h1

theorem Fits.mergedSet_forestStates (hF : Fits F e) (s : Fin m) (hanti : StrictAnti fun s ↦ e (.inr s)) :
    mergedSet (forestStates e F) s = leafSet F e (e (.inr s)) := by
  obtain ⟨a, c, h⟩ := hF.exists_kids ⟨s, rfl⟩
  have hka : IsKid F (e (.inr s)) a := ⟨a, c, h, Or.inl rfl⟩
  have hkc : IsKid F (e (.inr s)) c := ⟨a, c, h, Or.inr rfl⟩
  have hdisj := Set.disjoint_left.mp (hF.leafSet_disjoint h)
  have hLw := hF.leafSet_kids h
  ext j
  constructor
  · rintro ⟨l, h1, h2⟩
    rcases (stateSeq_forestStates_succ_iff s j l).mp h1 with h | ⟨hj, -⟩
    · rw [h] at h2
      cases h2
    · exact hj
  · intro hj
    have hj' := hj
    rw [hLw] at hj'
    rcases hj' with hj' | hj'
    · obtain ⟨l₀, hl₀⟩ := hF.leafSet_nonempty c
      refine ⟨l₀, (stateSeq_forestStates_succ_iff s j l₀).mpr
        (Or.inr ⟨hj, by rw [hLw]; exact Or.inr hl₀⟩), ?_⟩
      rw [← Bool.not_eq_true, hF.stateSeq_class hanti hkc hl₀ j]
      exact hdisj hj'
    · obtain ⟨j₀, hj₀⟩ := hF.leafSet_nonempty a
      refine ⟨j₀, (stateSeq_forestStates_succ_iff s j j₀).mpr
        (Or.inr ⟨hj, by rw [hLw]; exact Or.inl hj₀⟩), ?_⟩
      rw [← Bool.not_eq_true, hF.stateSeq_class hanti hka hj₀ j]
      exact fun h' ↦ hdisj h' hj'

theorem Fits.clusterOf_forestStates (hF : Fits F e) (hanti : StrictAnti fun s ↦ e (.inr s)) :
    clusterOf e (forestStates e F) = leafSet F e := by
  funext v
  rcases vertex_cases e v with ⟨j, rfl⟩ | ⟨s, rfl⟩
  · rw [clusterOf_inl, hF.leafSet_inl]
  · rw [clusterOf_inr, hF.mergedSet_forestStates s hanti]

/-- **A labelled plane forest is the forest of its merge history and child orders.** -/
theorem Fits.histForest_forestStates (hF : Fits F e) (hanti : StrictAnti fun s ↦ e (.inr s)) :
    histForest e (forestStates e F) (forestOrders e F) = F := by
  rw [histForest, hF.clusterOf_forestStates hanti, hF.histKids_leafSet]

/-- **The bijection between admissible plane histories and labelled plane forests**, for a
fixed labelling `e` of the births and merges by `Fin n` increasing in time. -/
noncomputable def historyForestEquiv (e : Fin k ⊕ Fin m ≃ Fin n)
    (hanti : StrictAnti fun s ↦ e (.inr s)) :
    {p : (Fin m → ConnState k) × (Fin m → Bool) // DAdm e p.1} ≃ {F : KidsMap n // Fits F e} where
  toFun p := ⟨histForest e p.1.1 p.1.2, p.2.fits p.1.2⟩
  invFun F := ⟨(forestStates e F.1, forestOrders e F.1), F.2.dAdm hanti⟩
  left_inv p := Subtype.ext (Prod.ext (p.2.forestStates_histForest _)
    (p.2.forestOrders_histForest _))
  right_inv F := Subtype.ext (F.2.histForest_forestStates hanti)

end ForestHistory


/-! ### Counting trees, and the source's forests `𝔉⁺_{r,k}` -/

section Counting

variable {n : ℕ} {F : KidsMap n}

/-- The children of a vertex, as a finite set. -/
def kidsOf (F : KidsMap n) (w : Fin n) : Finset (Fin n) :=
  match F w with
  | some (a, c) => {a, c}
  | none => ∅

theorem mem_kidsOf {w v : Fin n} : v ∈ kidsOf F w ↔ IsKid F w v := by
  unfold kidsOf
  rcases h : F w with _ | ⟨a, c⟩
  · simp [not_isKid_of_eq_none h]
  · simp [isKid_iff_of_eq h]

/-- In a plane binary forest, the number of trees plus twice the number of internal vertices
is the number of vertices. -/
theorem IsPlaneForest.rootCount_add (hF : IsPlaneForest F) :
    rootCount F + 2 * (Finset.univ.filter fun w ↦ F w ≠ none).card = n := by
  classical
  set I := Finset.univ.filter fun w ↦ F w ≠ none with hIdef
  have hNR : (Finset.univ.filter fun v ↦ ¬ ∀ w, ¬ IsKid F w v) = I.biUnion (kidsOf F) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not,
      Finset.mem_biUnion, mem_kidsOf, hIdef]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_, hw⟩
      obtain ⟨a, c, h, -⟩ := hw
      rw [h]
      exact Option.some_ne_none _
    · rintro ⟨w, -, hw⟩
      exact ⟨w, hw⟩
  have hcard : (I.biUnion (kidsOf F)).card = 2 * I.card := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_const_nat (m := 2), mul_comm]
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hIdef] at hw
      obtain ⟨⟨a, c⟩, h⟩ := Option.ne_none_iff_exists'.mp hw
      simp only [kidsOf, h]
      exact Finset.card_pair (hF.1 w a c h).2.2
    · intro w _ w' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro v hv hv'
      exact hne (hF.2 w w' v (mem_kidsOf.mp hv) (mem_kidsOf.mp hv'))
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun v ↦ ∀ w, ¬ IsKid F w v)
  rw [hNR, hcard, Finset.card_univ, Fintype.card_fin] at this
  exact this

/-- A forest fitting a labelling of `k` births and `m` merges has `k - m` trees. -/
theorem Fits.rootCount_add {k m : ℕ} {e : Fin k ⊕ Fin m ≃ Fin n} (hF : Fits F e) :
    rootCount F + m = k := by
  have h1 := hF.1.rootCount_add
  have hI : (Finset.univ.filter fun w ↦ F w ≠ none) = Finset.univ.map
      ⟨fun s ↦ e (.inr s), fun a b h ↦ Sum.inr_injective (e.injective h)⟩ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hv
      obtain ⟨s, hs⟩ := hF.not_inl hv
      exact ⟨s, hs⟩
    · rintro ⟨s, rfl⟩
      exact hF.2.2 s
  rw [hI, Finset.card_map, Finset.card_univ, Fintype.card_fin] at h1
  have hn : k + m = n := by simpa using Fintype.card_congr e
  omega

end Counting

/-- **The source's forests `𝔉⁺_{r,k}`**: ordered forests of `r + 1` plane binary trees with
`2k - 1 - r` vertices labelled `r + 1, …, 2k - 1` (the vertex `v : Fin (2k - 1 - r)` carries
the label `r + 1 + v`), the labels increasing along the branches. The trees are ordered by
their root labels (convention S09), so no extra data orders them. -/
abbrev SourceForest (r k : ℕ) :=
  {F : KidsMap (2 * k - 1 - r) // IsPlaneForest F ∧ rootCount F = r + 1}

/-- The label `r + 1 + v` of the vertex `v` of a forest of `𝔉⁺_{r,k}`. -/
def vertexLabel (r : ℕ) {N : ℕ} (v : Fin N) : ℕ := r + 1 + v

/-- `ℓ` is the label of a leaf of `F`. -/
def IsLeafLabel {r k : ℕ} (F : SourceForest r k) (ℓ : ℕ) : Prop :=
  ∃ v, vertexLabel r v = ℓ ∧ F.1 v = none

/-- `ℓ` is the label of an internal vertex of `F`. -/
def IsInternalLabel {r k : ℕ} (F : SourceForest r k) (ℓ : ℕ) : Prop :=
  ∃ v, vertexLabel r v = ℓ ∧ F.1 v ≠ none

/-- A forest of `𝔉⁺_{r,k}` has `k - 1 - r` internal vertices (and hence `k` leaves). -/
theorem SourceForest.card_internal {r k : ℕ} (hr : r < k) (F : SourceForest r k) :
    (Finset.univ.filter fun w ↦ F.1 w ≠ none).card = k - 1 - r := by
  have := F.2.1.rootCount_add
  rw [F.2.2] at this
  omega

/-- A forest of `𝔉⁺_{r,k}` has `k` leaves. -/
theorem SourceForest.card_leaves {r k : ℕ} (hr : r < k) (F : SourceForest r k) :
    (Finset.univ.filter fun w ↦ F.1 w = none).card = k := by
  have h1 : (Finset.univ.filter fun w ↦ ¬ F.1 w = none).card = k - 1 - r := F.card_internal hr
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun w ↦ F.1 w = none)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- **The source's admissibility** of a triplet `(F₀, (c_j)_{r < j < k}, (b_j)_{j ≤ k})`, with
`c i = c_{r+1+i}`, combined with the Proposition's range for the merge times (the Definition
allows `0 ≤ c_{r+1}`): the times are distinct, `0 < c_{r+1} < ⋯ < c_{k-1} < 1`, and there is an
increasing bijection `φ` from `{c_j} ∪ {b_j}` onto `{r + 1, …, 2k - 1}` sending the births to
leaf labels and the merge times to internal labels. The particle `j` sits at the leaf labelled
`φ (b j)`. -/
def SourceAdmissible {r k : ℕ} (F : SourceForest r k) (b : Fin k → ℝ) (c : Fin (k - 1 - r) → ℝ) :
    Prop :=
  Function.Injective (Sum.elim b c) ∧ StrictMono c ∧ (∀ i, 0 < c i ∧ c i < 1) ∧
    ∃ φ : ℝ → ℕ, StrictMonoOn φ (Set.range b ∪ Set.range c) ∧
      Set.BijOn φ (Set.range b ∪ Set.range c) (Set.Icc (r + 1) (2 * k - 1)) ∧
      (∀ j, IsLeafLabel F (φ (b j))) ∧ ∀ i, IsInternalLabel F (φ (c i))

/-! ### Ranks of event times -/

section Ranks

variable {k m : ℕ}

/-- Strict comparisons of event times. -/
noncomputable def cmpOf {ι : Type*} (t : ι → ℝ) : ι → ι → Bool := fun a a' ↦ decide (t a < t a')

/-- The rank of an event for a comparison pattern: the number of other events before it. -/
def rankFin (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool) (a : Fin k ⊕ Fin m) : Fin (k + m) :=
  ⟨(Finset.univ.filter fun a' ↦ a' ≠ a ∧ cmp a' a = true).card, by
    calc _ < (Finset.univ : Finset (Fin k ⊕ Fin m)).card :=
          Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨a, Finset.mem_univ _, by simp⟩)
      _ = k + m := by simp⟩

/-- The number of events strictly before a real time. -/
noncomputable def countBelow {ι : Type*} [Fintype ι] (t : ι → ℝ) (y : ℝ) : ℕ :=
  (Finset.univ.filter fun a ↦ t a < y).card

theorem rankFin_cmpOf (t : Fin k ⊕ Fin m → ℝ) (a : Fin k ⊕ Fin m) :
    (rankFin (cmpOf t) a : ℕ) = countBelow t (t a) := by
  simp only [rankFin, countBelow, cmpOf, decide_eq_true_eq]
  congr 1
  ext a'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  rintro h rfl
  exact lt_irrefl _ h

theorem countBelow_lt_countBelow {ι : Type*} [Fintype ι] {t : ι → ℝ} {a : ι} {y : ℝ}
    (h : t a < y) : countBelow t (t a) < countBelow t y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun a' ha' ↦ ?_) |>.mpr ⟨a, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha' ⊢
    exact ha'.trans h
  · simpa using h
  · simp

theorem countBelow_lt_iff {ι : Type*} [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t)
    (a a' : ι) : countBelow t (t a) < countBelow t (t a') ↔ t a < t a' := by
  constructor
  · intro h
    by_contra h'
    rcases lt_or_eq_of_le (not_lt.mp h') with h'' | h''
    · exact absurd h (not_lt.mpr (countBelow_lt_countBelow h'').le)
    · rw [ht h''] at h
      exact lt_irrefl _ h
  · exact countBelow_lt_countBelow

theorem rankFin_lt_iff {t : Fin k ⊕ Fin m → ℝ} (ht : Function.Injective t) (a a' : Fin k ⊕ Fin m) :
    rankFin (cmpOf t) a < rankFin (cmpOf t) a' ↔ t a < t a' := by
  rw [Fin.lt_def, rankFin_cmpOf, rankFin_cmpOf, countBelow_lt_iff ht]

theorem rankFin_bijective_iff {t : Fin k ⊕ Fin m → ℝ} :
    Function.Bijective (rankFin (cmpOf t)) ↔ Function.Injective t := by
  constructor
  · intro hb a a' h
    by_contra hne
    apply hne
    apply hb.1
    apply Fin.ext
    simp only [rankFin, cmpOf]
    congr 1
    ext a''
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, h]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun h3 ↦ ?_, h2⟩
      rw [h3] at h2
      exact lt_irrefl _ h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun h3 ↦ ?_, h2⟩
      rw [h3, h] at h2
      exact lt_irrefl _ h2
  · intro ht
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a a' h ↦ ?_, by simp⟩
    by_contra hne
    rcases lt_or_gt_of_ne (fun h' ↦ hne (ht h')) with h' | h'
    · exact absurd h (ne_of_lt ((rankFin_lt_iff ht a a').mpr h'))
    · exact absurd h (ne_of_gt ((rankFin_lt_iff ht a' a).mpr h'))

/-- The labelling of the events by `Fin N`, increasing in time, attached to a bijective
comparison pattern. -/
noncomputable def labelEquiv (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool)
    (hb : Function.Bijective (rankFin cmp)) {N : ℕ} (hN : k + m = N) : Fin k ⊕ Fin m ≃ Fin N :=
  (Equiv.ofBijective _ hb).trans (finCongr hN)

theorem labelEquiv_apply (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool)
    (hb : Function.Bijective (rankFin cmp)) {N : ℕ} (hN : k + m = N) (a : Fin k ⊕ Fin m) :
    labelEquiv cmp hb hN a = Fin.cast hN (rankFin cmp a) := rfl

theorem labelEquiv_lt_iff (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool)
    (hb : Function.Bijective (rankFin cmp)) {N : ℕ} (hN : k + m = N) (a a' : Fin k ⊕ Fin m) :
    labelEquiv cmp hb hN a < labelEquiv cmp hb hN a' ↔ rankFin cmp a < rankFin cmp a' := by
  rw [labelEquiv_apply, labelEquiv_apply, Fin.cast_lt_cast]

theorem labelEquiv_congr {cmp cmp' : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool} (h : cmp = cmp')
    (hb : Function.Bijective (rankFin cmp)) (hb' : Function.Bijective (rankFin cmp')) {N : ℕ}
    (hN : k + m = N) : labelEquiv cmp hb hN = labelEquiv cmp' hb' hN := by
  subst h
  rfl

theorem dAdm_congr {n n' : ℕ} {ρ : Fin k ⊕ Fin m → Fin n} {ρ' : Fin k ⊕ Fin m → Fin n'}
    (h : ∀ a a', ρ a < ρ a' ↔ ρ' a < ρ' a') (xs : Fin m → ConnState k) :
    DAdm ρ xs ↔ DAdm ρ' xs := by
  have hb : ∀ s, bornSet ρ s = bornSet ρ' s := fun s ↦ by
    ext j
    rw [mem_bornSet, mem_bornSet, h]
  unfold DAdm
  simp only [hb]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b hab ↦ (h _ _).mp (h1 hab), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b hab ↦ (h _ _).mpr (h1 hab), h2⟩

end Ranks


/-! ### Admissibility in real time -/

section RealTimes

variable {k : ℕ} {b : Fin k → ℝ}

/-- `IsAdmissible`, step by step. -/
theorem isAdmissible_iff_forall : ∀ {m : ℕ} {t : ℝ} {x : ConnState k} {xs : Fin m → ConnState k}
    {cs : Fin m → ℝ}, IsAdmissible b m t x xs cs ↔
      (∀ s : Fin m, 0 < cs s ∧ cs s < (Fin.cons t cs : Fin (m + 1) → ℝ) s.castSucc) ∧
      ∀ s : Fin m, IsMergeStep (bornAt b (cs s))
        ((Fin.cons x xs : Fin (m + 1) → ConnState k) s.castSucc)
        ((Fin.cons x xs : Fin (m + 1) → ConnState k) s.succ)
  | 0, t, x, xs, cs => by simp [IsAdmissible]
  | m + 1, t, x, xs, cs => by
    simp only [IsAdmissible]
    rw [isAdmissible_iff_forall, Fin.forall_fin_succ, Fin.forall_fin_succ]
    have h1 : (Fin.cons (cs 0) (Fin.tail cs) : Fin (m + 1) → ℝ) = cs := Fin.cons_self_tail cs
    have h2 : (Fin.cons (xs 0) (Fin.tail xs) : Fin (m + 1) → ConnState k) = xs :=
      Fin.cons_self_tail xs
    simp only [h1, h2, Fin.tail, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
      ← Fin.succ_castSucc]
    tauto

theorem lt_cons_castSucc {m : ℕ} {cs : Fin m → ℝ} {t : ℝ} (hanti : StrictAnti cs)
    (ht : ∀ s, cs s < t) (s : Fin m) : cs s < (Fin.cons t cs : Fin (m + 1) → ℝ) s.castSucc := by
  cases m with
  | zero => exact s.elim0
  | succ m =>
    induction s using Fin.cases with
    | zero => simpa using ht 0
    | succ s =>
      rw [← Fin.succ_castSucc, Fin.cons_succ]
      exact hanti (Fin.castSucc_lt_succ (i := s))

/-- **Admissibility of a history with distinct times** is the admissibility of its merge
history for the labelling of the events by their ranks. -/
theorem isAdmissible_iff_dAdm {m n : ℕ} {cs : Fin m → ℝ} (ht : Function.Injective (Sum.elim b cs))
    {ρ : Fin k ⊕ Fin m → Fin n} (hρ : ∀ a a', ρ a < ρ a' ↔ Sum.elim b cs a < Sum.elim b cs a')
    (xs : Fin m → ConnState k) :
    IsAdmissible b m 1 diagState xs cs ↔ (∀ s, 0 < cs s ∧ cs s < 1) ∧ DAdm ρ xs := by
  have hborn : ∀ s, bornAt b (cs s) = bornSet ρ s := by
    intro s
    ext j
    rw [mem_bornSet, hρ]
    simp only [bornAt, Finset.mem_filter, Finset.mem_univ, true_and, Sum.elim_inl, Sum.elim_inr]
    constructor
    · intro h
      refine lt_of_le_of_ne h fun h' ↦ ?_
      have := @ht (.inr s) (.inl j) (by simpa using h')
      simp at this
    · exact le_of_lt
  have hanti : StrictAnti cs ↔ StrictAnti (fun s ↦ ρ (.inr s)) := by
    constructor
    · intro h a a' haa
      exact (hρ _ _).mpr (by simpa using h haa)
    · intro h a a' haa
      simpa using (hρ _ _).mp (h haa)
  constructor
  · intro hadm
    have h2 := (isAdmissible_iff_forall.mp hadm).2
    simp only [hborn] at h2
    exact ⟨hadm.time_mem, hanti.mp hadm.strictAnti, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine isAdmissible_iff_forall.mpr ⟨fun s ↦ ⟨(h1 s).1,
      lt_cons_castSucc (hanti.mpr h2) (fun s ↦ (h1 s).2) s⟩, fun s ↦ ?_⟩
    rw [hborn]
    exact h3 s

/-- An increasing bijection from distinct times onto an interval of integers is the rank. -/
theorem phi_eq_countBelow {ι : Type*} [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t)
    {α β : ℕ} {φ : ℝ → ℕ} (hmono : StrictMonoOn φ (Set.range t))
    (hbij : Set.BijOn φ (Set.range t) (Set.Icc α β)) (a : ι) :
    φ (t a) = α + countBelow t (t a) := by
  classical
  set S := Finset.univ.filter fun a' ↦ t a' < t a with hS
  have hβ : φ (t a) ≤ β := (hbij.1 ⟨a, rfl⟩).2
  have himg : S.image (fun a' ↦ φ (t a')) = Finset.Ico α (φ (t a)) := by
    ext ℓ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico, hS]
    constructor
    · rintro ⟨a', ha', rfl⟩
      exact ⟨(hbij.1 ⟨a', rfl⟩).1, hmono ⟨a', rfl⟩ ⟨a, rfl⟩ ha'⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, ⟨a', rfl⟩, hy⟩ := hbij.2.2 (show ℓ ∈ Set.Icc α β from ⟨h1, by omega⟩)
      refine ⟨a', ?_, hy⟩
      by_contra hc
      rw [not_lt] at hc
      have := hmono.monotoneOn ⟨a, rfl⟩ ⟨a', rfl⟩ hc
      omega
  have hinj : Set.InjOn (fun a' ↦ φ (t a')) S :=
    fun a₁ _ a₂ _ h ↦ ht (hbij.2.1 ⟨a₁, rfl⟩ ⟨a₂, rfl⟩ h)
  have hcard := Finset.card_image_of_injOn hinj
  rw [himg, Nat.card_Ico] at hcard
  have hα : α ≤ φ (t a) := (hbij.1 ⟨a, rfl⟩).1
  simp only [countBelow]
  rw [← hS]
  omega

theorem countBelow_lt_card {ι : Type*} [Fintype ι] (t : ι → ℝ) (a : ι) :
    countBelow t (t a) < Fintype.card ι :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨a, Finset.mem_univ _, lt_irrefl _⟩)

/-- The rank map is an increasing bijection onto an interval of integers. -/
theorem exists_phi {ι : Type*} [Fintype ι] {t : ι → ℝ} (ht : Function.Injective t) {α β : ℕ}
    (hαβ : β + 1 = α + Fintype.card ι) :
    StrictMonoOn (fun y ↦ α + countBelow t y) (Set.range t) ∧
      Set.BijOn (fun y ↦ α + countBelow t y) (Set.range t) (Set.Icc α β) := by
  have hmono : StrictMonoOn (fun y ↦ α + countBelow t y) (Set.range t) := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩ h
    exact Nat.add_lt_add_left (countBelow_lt_countBelow h) α
  refine ⟨hmono, ⟨?_, hmono.injOn, ?_⟩⟩
  · rintro _ ⟨a, rfl⟩
    have := countBelow_lt_card t a
    refine ⟨Nat.le_add_right _ _, ?_⟩
    show α + countBelow t (t a) ≤ β
    omega
  · intro ℓ hℓ
    obtain ⟨h1, h2⟩ := hℓ
    let f : ι → Fin (Fintype.card ι) := fun a ↦ ⟨countBelow t (t a), countBelow_lt_card t a⟩
    have hf : Function.Bijective f := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun a a' h ↦ ?_, by simp⟩
      have h' : countBelow t (t a) = countBelow t (t a') := congrArg Fin.val h
      by_contra hne
      rcases lt_or_gt_of_ne (fun h'' ↦ hne (ht h'')) with h'' | h''
      · exact absurd h' (ne_of_lt ((countBelow_lt_iff ht a a').mpr h''))
      · exact absurd h' (ne_of_gt ((countBelow_lt_iff ht a' a).mpr h''))
    obtain ⟨a, ha⟩ := hf.2 ⟨ℓ - α, by omega⟩
    refine ⟨t a, ⟨a, rfl⟩, ?_⟩
    have : countBelow t (t a) = ℓ - α := congrArg Fin.val ha
    simp only
    omega

theorem range_sum_elim_rev {m : ℕ} (cs : Fin m → ℝ) :
    Set.range b ∪ Set.range (cs ∘ Fin.rev) = Set.range (Sum.elim b cs) := by
  rw [Set.Sum.elim_range,
    Function.Surjective.range_comp (fun i ↦ ⟨Fin.rev i, Fin.rev_rev i⟩) cs]

theorem injective_sum_elim_rev_iff {m : ℕ} (cs : Fin m → ℝ) :
    Function.Injective (Sum.elim b (cs ∘ Fin.rev)) ↔ Function.Injective (Sum.elim b cs) := by
  have : Sum.elim b (cs ∘ Fin.rev) =
      Sum.elim b cs ∘ (Equiv.sumCongr (Equiv.refl (Fin k)) Fin.revPerm) := by
    funext a
    rcases a with j | i <;> rfl
  rw [this, Equiv.injective_comp]

theorem strictMono_comp_rev_iff {m : ℕ} (cs : Fin m → ℝ) :
    StrictMono (cs ∘ Fin.rev) ↔ StrictAnti cs := by
  constructor
  · intro h a a' haa
    have := h (Fin.rev_lt_rev.mpr haa)
    simpa using this
  · intro h a a' haa
    exact h (Fin.rev_lt_rev.mpr haa)

/-- **The source's admissibility in terms of histories.** A triplet `(F, b, c)` with
`c = cs ∘ rev` (the source's increasing merge times, against the history's decreasing ones) is
admissible exactly when the times are distinct, the merge times decrease in `(0, 1)`, and the
forest fits the labelling of the events by their ranks: births at leaves, merges at internal
vertices. -/
theorem sourceAdmissible_iff {r : ℕ} (hr : r < k) (F : SourceForest r k)
    (cs : Fin (k - 1 - r) → ℝ) :
    SourceAdmissible F b (cs ∘ Fin.rev) ↔ ∃ h : Function.Injective (Sum.elim b cs),
      (∀ s, 0 < cs s ∧ cs s < 1) ∧ StrictAnti cs ∧
        Fits F.1 (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr h)
          (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) := by
  have hcard : Fintype.card (Fin k ⊕ Fin (k - 1 - r)) = k + (k - 1 - r) := by simp
  have hlab : ∀ (h : Function.Injective (Sum.elim b cs)) a,
      ((labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr h)
        (show k + (k - 1 - r) = 2 * k - 1 - r by omega) a : Fin (2 * k - 1 - r)) : ℕ) =
        countBelow (Sum.elim b cs) (Sum.elim b cs a) := by
    intro h a
    rw [labelEquiv_apply, Fin.val_cast, rankFin_cmpOf]
  rw [SourceAdmissible, injective_sum_elim_rev_iff, strictMono_comp_rev_iff, range_sum_elim_rev]
  constructor
  · rintro ⟨hinj, hanti, hunit, φ, hmono, hbij, hleaf, hint⟩
    have hφ := phi_eq_countBelow hinj hmono hbij
    refine ⟨hinj, fun s ↦ by simpa using hunit (Fin.rev s), hanti, F.2.1, fun j ↦ ?_, fun s ↦ ?_⟩
    · obtain ⟨v, hv, hF⟩ := hleaf j
      have hφj := hφ (.inl j)
      simp only [Sum.elim_inl] at hφj
      convert hF
      apply Fin.ext
      rw [hlab hinj]
      simp only [vertexLabel, Sum.elim_inl] at hv ⊢
      omega
    · obtain ⟨v, hv, hF⟩ := hint (Fin.rev s)
      have hφs := hφ (.inr s)
      simp only [Sum.elim_inr, Function.comp_apply, Fin.rev_rev] at hφs hv
      convert hF
      apply Fin.ext
      rw [hlab hinj]
      simp only [vertexLabel, Sum.elim_inr] at hv ⊢
      omega
  · rintro ⟨hinj, hunit, hanti, hfits⟩
    obtain ⟨hmono, hbij⟩ := exists_phi hinj (α := r + 1) (β := 2 * k - 1) (by rw [hcard]; omega)
    refine ⟨hinj, hanti, fun i ↦ hunit (Fin.rev i), _, hmono, hbij, fun j ↦ ?_, fun i ↦ ?_⟩
    · refine ⟨labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by omega) (.inl j), ?_, hfits.2.1 j⟩
      rw [vertexLabel, hlab hinj]
      rfl
    · refine ⟨labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by omega) (.inr (Fin.rev i)), ?_,
        hfits.2.2 (Fin.rev i)⟩
      rw [vertexLabel, hlab hinj]
      rfl

end RealTimes


/-! ### The forest of a plane history and the bijection with source triplets -/

section PlaneForestMap

variable {k : ℕ}

/-- Whether each merge time lies in `(0, 1)`. -/
noncomputable def unitPattern {m : ℕ} (cs : Fin m → ℝ) : Fin m → Bool :=
  fun s ↦ decide (0 < cs s ∧ cs s < 1)

theorem dAdm_labelEquiv_iff {m N : ℕ} (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool)
    (hb : Function.Bijective (rankFin cmp)) (hN : k + m = N) (xs : Fin m → ConnState k) :
    DAdm (labelEquiv cmp hb hN) xs ↔ DAdm (rankFin cmp) xs :=
  dAdm_congr (labelEquiv_lt_iff cmp hb hN) xs

open Classical in
/-- The forest of `𝔉⁺_{r,k}` of a plane history, as a function of its merge history `xs`, its
child orders `σ`, the comparison pattern `cmp` of its times and the pattern `u` of merge times
in `(0, 1)`; `none` unless the history is admissible with `m = k - 1 - r` merges. -/
noncomputable def patternForest (r : ℕ) {m : ℕ} (xs : Fin m → ConnState k) (σ : Fin m → Bool)
    (cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool) (u : Fin m → Bool) : Option (SourceForest r k) :=
  if hc : m + r + 1 = k ∧ Function.Bijective (rankFin cmp) ∧ (∀ s, u s = true) ∧
      DAdm (rankFin cmp) xs then
    some ⟨histForest (labelEquiv cmp hc.2.1 (show k + m = 2 * k - 1 - r by omega)) xs σ,
      (((dAdm_labelEquiv_iff cmp hc.2.1 (show k + m = 2 * k - 1 - r by omega) xs).mpr
        hc.2.2.2).fits σ).1, by
        have := (((dAdm_labelEquiv_iff cmp hc.2.1 (show k + m = 2 * k - 1 - r by omega) xs).mpr
          hc.2.2.2).fits σ).rootCount_add
        omega⟩
  else none

/-- **The random plane forest `𝓕`** of a plane history `(m, xs, σ, b, cs)`: the forest of
`𝔉⁺_{r,k}` with `r = k - 1 - m` built from the merge history, the child orders and the ranks of
the times, when the history is admissible with distinct times; `none` otherwise (a null event
under `planeLaw`). -/
noncomputable def planeForest (h : PlaneHistorySpace k) : Option (Σ r : ℕ, SourceForest r k) :=
  (patternForest (k - 1 - h.1) h.2.1 h.2.2.1 (cmpOf (Sum.elim h.2.2.2.1 h.2.2.2.2))
    (unitPattern h.2.2.2.2)).map (Sigma.mk _)

/-- The births `B` of a plane history. -/
def birthTimes (h : PlaneHistorySpace k) : Fin k → ℝ := h.2.2.2.1

/-- The source's ordered merge times `C_1 ≤ ⋯ ≤ C_{k-1}` of a plane history with `m` merges:
`C_1 = ⋯ = C_r = 0` for `r = k - 1 - m`, and `C_{r+1} < ⋯ < C_{k-1}` are the merge times in
increasing order (`C_{j+1} = cs (k - 2 - j)` in `0`-based indexing). -/
def sourceMergeTimes (h : PlaneHistorySpace k) : Fin (k - 1) → ℝ := fun j ↦
  if hj : (j : ℕ) + h.1 + 1 < k then 0 else h.2.2.2.2 ⟨k - 2 - j, by have := j.2; omega⟩

/-- The positive part `(C_{r+1}, …, C_{k-1})` of the source's merge times. -/
def upperMergeTimes (r : ℕ) (h : PlaneHistorySpace k) : Fin (k - 1 - r) → ℝ :=
  fun i ↦ sourceMergeTimes h ⟨r + i, by have := i.2; omega⟩

theorem patternForest_eq_some_imp {r m : ℕ} {xs : Fin m → ConnState k} {σ : Fin m → Bool}
    {cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool} {u : Fin m → Bool} {F : SourceForest r k}
    (h : patternForest r xs σ cmp u = some F) : m + r + 1 = k := by
  unfold patternForest at h
  split_ifs at h with hc
  exact hc.1

theorem labelEquiv_lt_iff_times {m : ℕ} {t : Fin k ⊕ Fin m → ℝ} (ht : Function.Injective t)
    {N : ℕ} (hN : k + m = N) (a a' : Fin k ⊕ Fin m) :
    labelEquiv (cmpOf t) (rankFin_bijective_iff.mpr ht) hN a <
      labelEquiv (cmpOf t) (rankFin_bijective_iff.mpr ht) hN a' ↔ t a < t a' :=
  (labelEquiv_lt_iff _ _ _ a a').trans (rankFin_lt_iff ht a a')

/-- The forest of a history with `k - 1 - r` merges, in history form. -/
theorem patternForest_eq_some_iff {r : ℕ} (hr : r < k) (xs : Fin (k - 1 - r) → ConnState k)
    (σ : Fin (k - 1 - r) → Bool) (b : Fin k → ℝ) (cs : Fin (k - 1 - r) → ℝ) (F : SourceForest r k) :
    patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F ↔
      ∃ h : Function.Injective (Sum.elim b cs), IsAdmissible b (k - 1 - r) 1 diagState xs cs ∧
        histForest (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr h)
          (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) xs σ = F.1 := by
  have hunit : (∀ s, unitPattern cs s = true) ↔ ∀ s, 0 < cs s ∧ cs s < 1 := by
    simp [unitPattern]
  unfold patternForest
  split_ifs with hc
  · rw [Option.some.injEq, Subtype.ext_iff]
    have hinj := rankFin_bijective_iff.mp hc.2.1
    constructor
    · intro hF
      refine ⟨hinj, (isAdmissible_iff_dAdm hinj (rankFin_lt_iff hinj) xs).mpr
        ⟨hunit.mp hc.2.2.1, hc.2.2.2⟩, hF⟩
    · rintro ⟨_, _, hF⟩
      exact hF
  · simp only [false_iff, not_exists, not_and]
    intro hinj hadm _
    obtain ⟨h1, h2⟩ := (isAdmissible_iff_dAdm hinj (rankFin_lt_iff hinj) xs).mp hadm
    exact hc ⟨by omega, rankFin_bijective_iff.mpr hinj, hunit.mpr h1, h2⟩

theorem planeForest_eq_some_iff (h : PlaneHistorySpace k) (r : ℕ) (F : SourceForest r k) :
    planeForest h = some ⟨r, F⟩ ↔ patternForest r h.2.1 h.2.2.1
      (cmpOf (Sum.elim h.2.2.2.1 h.2.2.2.2)) (unitPattern h.2.2.2.2) = some F := by
  unfold planeForest
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨F', hF', hsig⟩
    have hr : k - 1 - h.1 = r := congrArg Sigma.fst hsig
    subst hr
    rw [Sigma.mk.injEq] at hsig
    rw [hF', eq_of_heq hsig.2]
  · intro hF
    have hr : r = k - 1 - h.1 := by have := patternForest_eq_some_imp hF; omega
    subst hr
    exact ⟨F, hF, rfl⟩

/-- **The bijection of N11.** Admissible plane histories with `m = k - 1 - r` merges and
distinct times `(xs, σ, b, cs)` correspond to admissible source triplets `(F₀, b, c)` of
`𝔉⁺_{r,k}`: the forest is `histForest` for the labelling of the events by their ranks, and
`c = cs ∘ rev` lists the merge times increasingly. -/
noncomputable def toSourceTriplet {r : ℕ} (hr : r < k)
    (q : {q : (Fin (k - 1 - r) → ConnState k) × (Fin (k - 1 - r) → Bool) × (Fin k → ℝ) ×
      (Fin (k - 1 - r) → ℝ) // IsAdmissible q.2.2.1 (k - 1 - r) 1 diagState q.1 q.2.2.2 ∧
        Function.Injective (Sum.elim q.2.2.1 q.2.2.2)}) :
    {t : SourceForest r k × (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) //
      SourceAdmissible t.1 t.2.1 t.2.2} :=
  have hD := ((isAdmissible_iff_dAdm q.2.2 (labelEquiv_lt_iff_times q.2.2
    (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) q.1.1).mp q.2.1).2
  ⟨(⟨histForest (labelEquiv (cmpOf (Sum.elim q.1.2.2.1 q.1.2.2.2))
      (rankFin_bijective_iff.mpr q.2.2) (show k + (k - 1 - r) = 2 * k - 1 - r by omega))
      q.1.1 q.1.2.1, (hD.fits _).1, by have := (hD.fits q.1.2.1).rootCount_add; omega⟩,
    q.1.2.2.1, q.1.2.2.2 ∘ Fin.rev),
    (sourceAdmissible_iff hr _ _).mpr ⟨q.2.2, q.2.1.time_mem, q.2.1.strictAnti, hD.fits _⟩⟩

theorem sourceAdmissible_rev {r : ℕ} {F : SourceForest r k} {b : Fin k → ℝ}
    {c : Fin (k - 1 - r) → ℝ} (h : SourceAdmissible F b c) :
    SourceAdmissible F b ((c ∘ Fin.rev) ∘ Fin.rev) := by
  have : (c ∘ Fin.rev) ∘ Fin.rev = c := funext fun i ↦ by simp
  rw [this]
  exact h

/-- The inverse of `toSourceTriplet`. -/
noncomputable def ofSourceTriplet {r : ℕ} (hr : r < k)
    (t : {t : SourceForest r k × (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) //
      SourceAdmissible t.1 t.2.1 t.2.2}) :
    {q : (Fin (k - 1 - r) → ConnState k) × (Fin (k - 1 - r) → Bool) × (Fin k → ℝ) ×
      (Fin (k - 1 - r) → ℝ) // IsAdmissible q.2.2.1 (k - 1 - r) 1 diagState q.1 q.2.2.2 ∧
        Function.Injective (Sum.elim q.2.2.1 q.2.2.2)} :=
  have hS := (sourceAdmissible_iff hr t.1.1 _).mp (sourceAdmissible_rev t.2)
  have hρ := labelEquiv_lt_iff_times hS.1 (show k + (k - 1 - r) = 2 * k - 1 - r by omega)
  have hanti : StrictAnti fun s ↦ labelEquiv (cmpOf (Sum.elim t.1.2.1 (t.1.2.2 ∘ Fin.rev)))
      (rankFin_bijective_iff.mpr hS.1) (show k + (k - 1 - r) = 2 * k - 1 - r by omega) (.inr s) :=
    fun _ _ hab ↦ (hρ _ _).mpr (by simpa using hS.2.2.1 hab)
  ⟨(forestStates (labelEquiv (cmpOf (Sum.elim t.1.2.1 (t.1.2.2 ∘ Fin.rev)))
      (rankFin_bijective_iff.mpr hS.1) (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) t.1.1.1,
    forestOrders (labelEquiv (cmpOf (Sum.elim t.1.2.1 (t.1.2.2 ∘ Fin.rev)))
      (rankFin_bijective_iff.mpr hS.1) (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) t.1.1.1,
    t.1.2.1, t.1.2.2 ∘ Fin.rev),
    (isAdmissible_iff_dAdm hS.1 hρ _).mpr ⟨hS.2.1, hS.2.2.2.dAdm hanti⟩, hS.1⟩

/-- **The bijection between admissible plane histories and admissible source triplets**
(Proposition `loi du coalescent généralisé`, combinatorial part): for `r < k`, plane histories
with `k - 1 - r` merges that are admissible with distinct times correspond bijectively to the
admissible triplets `(F₀, (b_j), (c_j))` with `F₀ ∈ 𝔉⁺_{r,k}`. -/
noncomputable def sourceTripletEquiv {r : ℕ} (hr : r < k) :
    {q : (Fin (k - 1 - r) → ConnState k) × (Fin (k - 1 - r) → Bool) × (Fin k → ℝ) ×
      (Fin (k - 1 - r) → ℝ) // IsAdmissible q.2.2.1 (k - 1 - r) 1 diagState q.1 q.2.2.2 ∧
        Function.Injective (Sum.elim q.2.2.1 q.2.2.2)} ≃
    {t : SourceForest r k × (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) //
      SourceAdmissible t.1 t.2.1 t.2.2} where
  toFun := toSourceTriplet hr
  invFun := ofSourceTriplet hr
  left_inv q := by
    obtain ⟨⟨xs, σ, b, cs⟩, hadm, hinj⟩ := q
    have hcs : (cs ∘ Fin.rev) ∘ Fin.rev = cs := funext fun i ↦ by simp
    have hD := ((isAdmissible_iff_dAdm hinj (labelEquiv_lt_iff_times hinj
      (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) xs).mp hadm).2
    apply Subtype.ext
    simp only [toSourceTriplet, ofSourceTriplet]
    rw [labelEquiv_congr (congrArg (fun c ↦ cmpOf (Sum.elim b c)) hcs) _
      (rankFin_bijective_iff.mpr hinj), hD.forestStates_histForest, hD.forestOrders_histForest,
      hcs]
  right_inv t := by
    obtain ⟨⟨F, b, c⟩, hS⟩ := t
    have hc : (c ∘ Fin.rev) ∘ Fin.rev = c := funext fun i ↦ by simp
    have hS' := (sourceAdmissible_iff hr F _).mp (sourceAdmissible_rev hS)
    have hρ := labelEquiv_lt_iff_times hS'.1 (show k + (k - 1 - r) = 2 * k - 1 - r by omega)
    have hanti : StrictAnti fun s ↦ labelEquiv (cmpOf (Sum.elim b (c ∘ Fin.rev)))
        (rankFin_bijective_iff.mpr hS'.1) (show k + (k - 1 - r) = 2 * k - 1 - r by omega)
          (.inr s) :=
      fun _ _ hab ↦ (hρ _ _).mpr (by simpa using hS'.2.2.1 hab)
    apply Subtype.ext
    simp only [toSourceTriplet, ofSourceTriplet]
    rw [hc]
    congr 1
    exact Subtype.ext (hS'.2.2.2.histForest_forestStates hanti)

end PlaneForestMap


/-! ### The law of the plane forest, births and merge times -/

section Density

variable {k : ℕ}

open Classical in
/-- **The density `g_{r,k}`** of Proposition `loi du coalescent généralisé`, extended by `0`
off admissible triplets: for `F₀ ∈ 𝔉⁺_{r,k}`, births `b` and merge times `c i = c_{r+1+i}`,
`2^{-(k-1-r)} exp (-∫₀¹ C(a(t), 2) g(t)² dt) ∏_j g(c_j)²`, with `g = 1/f` and
`a(t) = #{j : b_j > t} - #{j : c_j > t}` (`sourceClusterCount`); `exp (-∞) = 0`. -/
noncomputable def sourceDensity (g : ℝ → ℝ) {r : ℕ} (F₀ : SourceForest r k) (b : Fin k → ℝ)
    (c : Fin (k - 1 - r) → ℝ) : ℝ≥0∞ :=
  (if SourceAdmissible F₀ b c then 1 else 0) * 2⁻¹ ^ (k - 1 - r) *
    (∏ i, ENNReal.ofReal (g (c i) ^ 2)) *
    expNeg (∫⁻ u in Ioc 0 1,
      ((sourceClusterCount b c u).choose 2 : ℝ≥0∞) * ENNReal.ofReal (g u ^ 2))

theorem sourceClusterCount_comp_rev (b : Fin k → ℝ) {m : ℕ} (cs : Fin m → ℝ) (u : ℝ) :
    sourceClusterCount b (cs ∘ Fin.rev) u = sourceClusterCount b cs u := by
  unfold sourceClusterCount
  congr 1
  exact Finset.card_equiv Fin.revPerm fun i ↦ by simp

theorem prod_comp_rev (g : ℝ → ℝ) {m : ℕ} (cs : Fin m → ℝ) :
    ∏ i, ENNReal.ofReal (g ((cs ∘ Fin.rev) i) ^ 2) = ∏ i, ENNReal.ofReal (g (cs i) ^ 2) :=
  Equiv.prod_comp Fin.revPerm (fun i ↦ ENNReal.ofReal (g (cs i) ^ 2))

/-- For an admissible triplet `(F₀, b, cs ∘ rev)`, the unique plane history with `k - 1 - r`
merges, births `b`, merge times `cs` and forest `F₀` is the merge history and the child orders
of `F₀`. -/
theorem patternForest_eq_some_iff_eq {r : ℕ} (hr : r < k) (F₀ : SourceForest r k)
    {b : Fin k → ℝ} {cs : Fin (k - 1 - r) → ℝ} (hinj : Function.Injective (Sum.elim b cs))
    (hunit : ∀ s, 0 < cs s ∧ cs s < 1) (hanti : StrictAnti cs)
    (hfits : Fits F₀.1 (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj)
      (show k + (k - 1 - r) = 2 * k - 1 - r by omega)))
    (xs : Fin (k - 1 - r) → ConnState k) (σ : Fin (k - 1 - r) → Bool) :
    patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀ ↔
      xs = forestStates (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) F₀.1 ∧
      σ = forestOrders (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj)
        (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) F₀.1 := by
  have hN : k + (k - 1 - r) = 2 * k - 1 - r := by omega
  have hρ := labelEquiv_lt_iff_times hinj hN
  have heanti : StrictAnti fun s ↦ labelEquiv (cmpOf (Sum.elim b cs))
      (rankFin_bijective_iff.mpr hinj) hN (.inr s) :=
    fun _ _ hab ↦ (hρ _ _).mpr (by simpa using hanti hab)
  rw [patternForest_eq_some_iff hr]
  constructor
  · rintro ⟨_, hadm, hF⟩
    have hD := ((isAdmissible_iff_dAdm hinj hρ xs).mp hadm).2
    rw [← hF, hD.forestStates_histForest, hD.forestOrders_histForest]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hinj, (isAdmissible_iff_dAdm hinj hρ _).mpr ⟨hunit, hfits.dAdm heanti⟩,
      hfits.histForest_forestStates heanti⟩

open Classical in
/-- **The fibre sum.** For fixed births `b` and merge times `cs` (listed decreasingly), summing
the plane density over the plane histories whose forest is `F₀` gives the source's density
`g_{r,k}(F₀, b, c)` at `c = cs ∘ rev`: exactly one plane history has forest `F₀` when the
triplet is admissible, and none otherwise. -/
theorem sum_planeDensity_patternForest (g : ℝ → ℝ) {r : ℕ} (hr : r < k) (F₀ : SourceForest r k)
    (b : Fin k → ℝ) (cs : Fin (k - 1 - r) → ℝ) :
    ∑ xs : Fin (k - 1 - r) → ConnState k, ∑ σ : Fin (k - 1 - r) → Bool,
      (if patternForest r xs σ (cmpOf (Sum.elim b cs)) (unitPattern cs) = some F₀ then
        planeDensity g b (k - 1 - r) xs cs else 0) = sourceDensity g F₀ b (cs ∘ Fin.rev) := by
  have hN : k + (k - 1 - r) = 2 * k - 1 - r := by omega
  unfold sourceDensity
  simp only [sourceClusterCount_comp_rev, prod_comp_rev]
  by_cases hS : SourceAdmissible F₀ b (cs ∘ Fin.rev)
  · obtain ⟨hinj, hunit, hanti, hfits⟩ := (sourceAdmissible_iff hr F₀ cs).mp hS
    have hρ := labelEquiv_lt_iff_times hinj hN
    have heanti : StrictAnti fun s ↦ labelEquiv (cmpOf (Sum.elim b cs))
        (rankFin_bijective_iff.mpr hinj) hN (.inr s) :=
      fun _ _ hab ↦ (hρ _ _).mpr (by simpa using hanti hab)
    have hadm₀ := (isAdmissible_iff_dAdm hinj hρ _).mpr ⟨hunit, hfits.dAdm heanti⟩
    have key := patternForest_eq_some_iff_eq hr F₀ hinj hunit hanti hfits
    rw [Finset.sum_eq_single (forestStates (labelEquiv (cmpOf (Sum.elim b cs))
      (rankFin_bijective_iff.mpr hinj) hN) F₀.1), Finset.sum_eq_single (forestOrders
        (labelEquiv (cmpOf (Sum.elim b cs)) (rankFin_bijective_iff.mpr hinj) hN) F₀.1)]
    · rw [ite_eq_left ((key _ _).mpr ⟨rfl, rfl⟩), ite_eq_left hS, planeDensity, historyDensity_eq_source,
        ite_eq_left hadm₀]
      ring
    · intro σ _ hσ
      rw [ite_eq_right]
      exact fun h ↦ hσ ((key _ _).mp h).2
    · exact fun h ↦ absurd (Finset.mem_univ _) h
    · intro xs _ hxs
      refine Finset.sum_eq_zero fun σ _ ↦ ?_
      rw [ite_eq_right]
      exact fun h ↦ hxs ((key _ _).mp h).1
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  · rw [ite_eq_right hS, zero_mul, zero_mul, zero_mul]
    refine Finset.sum_eq_zero fun xs _ ↦ Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [ite_eq_right]
    intro h
    apply hS
    obtain ⟨hinj, hadm, hF⟩ := (patternForest_eq_some_iff hr xs σ b cs F₀).mp h
    have hD := ((isAdmissible_iff_dAdm hinj (labelEquiv_lt_iff_times hinj hN) xs).mp hadm).2
    refine (sourceAdmissible_iff hr F₀ cs).mpr ⟨hinj, hadm.time_mem, hadm.strictAnti, ?_⟩
    rw [← hF]
    exact hD.fits σ

/-! #### Measurability -/

theorem measurable_decide_lt {X : Type*} [MeasurableSpace X] {f h : X → ℝ} (hf : Measurable f)
    (hh : Measurable h) : Measurable (fun x ↦ decide (f x < h x)) := by
  have : (fun x ↦ decide (f x < h x)) = fun x ↦ if f x < h x then true else false := by
    funext x
    by_cases hx : f x < h x <;> simp [hx]
  rw [this]
  exact Measurable.ite (measurableSet_lt hf hh) measurable_const measurable_const

/-- The fibre `m` of the plane history space. -/
abbrev PlaneFibre (k m : ℕ) :=
  (Fin m → ConnState k) × (Fin m → Bool) × (Fin k → ℝ) × (Fin m → ℝ)

theorem measurable_times (m : ℕ) (a : Fin k ⊕ Fin m) :
    Measurable (fun q : PlaneFibre k m ↦ Sum.elim q.2.2.1 q.2.2.2 a) := by
  rcases a with j | s
  · exact (measurable_pi_apply j).comp measurable_snd.snd.fst
  · exact (measurable_pi_apply s).comp measurable_snd.snd.snd

/-- The discrete data of a plane history: merge history, child orders, comparison pattern of
the times and pattern of merge times in `(0, 1)`. -/
noncomputable def discreteData (m : ℕ) (q : PlaneFibre k m) :
    (Fin m → ConnState k) × (Fin m → Bool) × (Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool) ×
      (Fin m → Bool) :=
  (q.1, q.2.1, cmpOf (Sum.elim q.2.2.1 q.2.2.2), unitPattern q.2.2.2)

theorem measurable_discreteData (m : ℕ) : Measurable (discreteData (k := k) m) := by
  refine measurable_fst.prodMk (measurable_snd.fst.prodMk (Measurable.prodMk ?_ ?_))
  · refine measurable_pi_iff.mpr fun a ↦ measurable_pi_iff.mpr fun a' ↦ ?_
    exact measurable_decide_lt (measurable_times m a) (measurable_times m a')
  · refine measurable_pi_iff.mpr fun s ↦ ?_
    have hs : Measurable fun q : PlaneFibre k m ↦ q.2.2.2 s :=
      (measurable_pi_apply s).comp measurable_snd.snd.snd
    have : (fun q : PlaneFibre k m ↦ unitPattern q.2.2.2 s) =
        fun q ↦ if 0 < q.2.2.2 s ∧ q.2.2.2 s < 1 then true else false := by
      funext q
      by_cases hq : 0 < q.2.2.2 s ∧ q.2.2.2 s < 1 <;> simp [unitPattern, hq]
    rw [this]
    exact Measurable.ite ((measurableSet_lt measurable_const hs).inter
      (measurableSet_lt hs measurable_const)) measurable_const measurable_const

theorem measurable_sourceMergeTimes (m : ℕ) (j : Fin (k - 1)) :
    Measurable (fun q : PlaneFibre k m ↦ sourceMergeTimes (⟨m, q⟩ : PlaneHistorySpace k) j) := by
  by_cases hj : (j : ℕ) + m + 1 < k
  · simp only [sourceMergeTimes, hj, ↓reduceDIte]
    exact measurable_const
  · simp only [sourceMergeTimes, hj, ↓reduceDIte]
    have hjk := j.2
    exact (measurable_pi_apply (⟨k - 2 - (j : ℕ), by omega⟩ : Fin m)).comp
      measurable_snd.snd.snd

theorem sourceMergeTimes_planeMk_of_lt {r : ℕ} (hr : r < k) (xs : Fin (k - 1 - r) → ConnState k)
    (σ : Fin (k - 1 - r) → Bool) (p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ)) (j : Fin (k - 1))
    (hj : (j : ℕ) < r) : sourceMergeTimes (planeMk (k - 1 - r) xs σ p) j = 0 := by
  have : (j : ℕ) + (k - 1 - r) + 1 < k := by omega
  simp only [sourceMergeTimes, planeMk, this, ↓reduceDIte]

theorem upperMergeTimes_planeMk {r : ℕ} (hr : r < k) (xs : Fin (k - 1 - r) → ConnState k)
    (σ : Fin (k - 1 - r) → Bool) (p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ)) :
    upperMergeTimes r (planeMk (k - 1 - r) xs σ p) = p.2 ∘ Fin.rev := by
  funext i
  have hi := i.2
  have : ¬ (r + (i : ℕ)) + (k - 1 - r) + 1 < k := by omega
  simp only [upperMergeTimes, sourceMergeTimes, planeMk, this, ↓reduceDIte, Function.comp_apply]
  exact congrArg p.2 (Fin.ext (by simp only [Fin.val_rev]; omega))

/-- The event `{𝓕 = F₀, C₁ = ⋯ = C_r = 0, (B, (C_{r+1}, …, C_{k-1})) ∈ S}`. -/
def forestEvent {r : ℕ} (F₀ : SourceForest r k) (S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))) :
    Set (PlaneHistorySpace k) :=
  {h | planeForest h = some ⟨r, F₀⟩ ∧
    (∀ j : Fin (k - 1), (j : ℕ) < r → sourceMergeTimes h j = 0) ∧
    (birthTimes h, upperMergeTimes r h) ∈ S}

theorem measurable_birthUpper (r : ℕ) :
    Measurable fun h : PlaneHistorySpace k ↦ (birthTimes h, upperMergeTimes r h) :=
  measurable_sigma_elim fun m ↦ (measurable_snd.snd.fst).prodMk
    (measurable_pi_iff.mpr fun _ ↦ measurable_sourceMergeTimes m _)

theorem measurableSet_planeForest_eq {r : ℕ} (F₀ : SourceForest r k) :
    MeasurableSet {h : PlaneHistorySpace k | planeForest h = some ⟨r, F₀⟩} := by
  refine measurableSet_sigma_iff.mpr fun m ↦ ?_
  change MeasurableSet {q : PlaneFibre k m |
    planeForest (⟨m, q⟩ : PlaneHistorySpace k) = some ⟨r, F₀⟩}
  have : {q : PlaneFibre k m | planeForest (⟨m, q⟩ : PlaneHistorySpace k) = some ⟨r, F₀⟩} =
      discreteData m ⁻¹' {y | (patternForest (k - 1 - m) y.1 y.2.1 y.2.2.1 y.2.2.2).map
        (Sigma.mk (β := fun r ↦ SourceForest r k) (k - 1 - m)) = some ⟨r, F₀⟩} := rfl
  rw [this]
  exact measurable_discreteData m (Set.to_countable _).measurableSet

theorem measurableSet_forestEvent {r : ℕ} (F₀ : SourceForest r k)
    {S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))} (hS : MeasurableSet S) :
    MeasurableSet (forestEvent F₀ S) := by
  have h3 : MeasurableSet {h : PlaneHistorySpace k | ∀ j : Fin (k - 1), (j : ℕ) < r →
      sourceMergeTimes h j = 0} := by
    have hI : {h : PlaneHistorySpace k | ∀ j : Fin (k - 1), (j : ℕ) < r →
        sourceMergeTimes h j = 0} =
        ⋂ j : Fin (k - 1), {h | (j : ℕ) < r → sourceMergeTimes h j = 0} := by
      ext h
      simp
    rw [hI]
    refine MeasurableSet.iInter fun j ↦ ?_
    by_cases hj : (j : ℕ) < r
    · have : {h : PlaneHistorySpace k | (j : ℕ) < r → sourceMergeTimes h j = 0} =
          (fun h : PlaneHistorySpace k ↦ sourceMergeTimes h j) ⁻¹' {0} := by
        ext h
        simp [hj]
      rw [this]
      exact measurable_sigma_elim (fun m ↦ measurable_sourceMergeTimes m j)
        (measurableSet_singleton 0)
    · have : {h : PlaneHistorySpace k | (j : ℕ) < r → sourceMergeTimes h j = 0} = Set.univ := by
        ext h
        simp [hj]
      rw [this]
      exact MeasurableSet.univ
  exact (measurableSet_planeForest_eq F₀).inter (h3.inter (measurable_birthUpper r hS))

/-- Membership in the event for a plane history with `k - 1 - r` merges. -/
theorem planeMk_mem_forestEvent_iff {r : ℕ} (hr : r < k) (F₀ : SourceForest r k)
    (S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))) (xs : Fin (k - 1 - r) → ConnState k)
    (σ : Fin (k - 1 - r) → Bool) (p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ)) :
    planeMk (k - 1 - r) xs σ p ∈ forestEvent F₀ S ↔
      patternForest r xs σ (cmpOf (Sum.elim p.1 p.2)) (unitPattern p.2) = some F₀ ∧
        (p.1, p.2 ∘ Fin.rev) ∈ S := by
  simp only [forestEvent, Set.mem_ofPred_eq, planeForest_eq_some_iff,
    upperMergeTimes_planeMk hr, birthTimes]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, sourceMergeTimes_planeMk_of_lt hr xs σ p, h3⟩

theorem planeMk_notMem_forestEvent {r m : ℕ} (hm : m ≠ k - 1 - r) (F₀ : SourceForest r k)
    (S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))) (xs : Fin m → ConnState k)
    (σ : Fin m → Bool) (p : (Fin k → ℝ) × (Fin m → ℝ)) :
    planeMk m xs σ p ∉ forestEvent F₀ S := by
  rintro ⟨h, -⟩
  have := patternForest_eq_some_imp ((planeForest_eq_some_iff _ r F₀).mp h)
  exact hm (by simp only [planeMk] at this; omega)

/-- The coordinate change `(b, cs) ↦ (b, cs ∘ rev)` listing the merge times increasingly. -/
noncomputable def revTimes (k M : ℕ) : (Fin k → ℝ) × (Fin M → ℝ) ≃ᵐ (Fin k → ℝ) × (Fin M → ℝ) :=
  (MeasurableEquiv.refl _).prodCongr
    (MeasurableEquiv.arrowCongr' Fin.revPerm (MeasurableEquiv.refl ℝ))

theorem revTimes_apply (M : ℕ) (p : (Fin k → ℝ) × (Fin M → ℝ)) :
    revTimes k M p = (p.1, p.2 ∘ Fin.rev) := rfl

theorem measurePreserving_revTimes (M : ℕ) :
    MeasurePreserving (revTimes k M) ((cubeMeasure k).prod volume) ((cubeMeasure k).prod volume) :=
  (MeasurePreserving.id (cubeMeasure k)).prod
    (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume))

variable {g : ℝ → ℝ}

/-- **Proposition `loi du coalescent généralisé` (N11), source form, against the history
reference measure.** Under the plane law (the decoded genealogy of the limiting coalescent,
with independent uniform child orders), for `r < k`, `F₀ ∈ 𝔉⁺_{r,k}` and a measurable set `S`
of pairs (births, positive merge times),
`P(𝓕 = F₀, C₁ = ⋯ = C_r = 0, (B, (C_{r+1}, …, C_{k-1})) ∈ S)` is the integral of
`g_{r,k}(F₀, b, c)` over `(b, c) ∈ S` against `Leb|_{[0,1]^k} ⊗ Leb`. -/
theorem planeLaw_forestEvent_cube (hg : Measurable g) {r : ℕ} (hr : r < k) (F₀ : SourceForest r k)
    {S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))} (hS : MeasurableSet S) :
    planeLaw g k (forestEvent F₀ S) =
      ∫⁻ p in S, sourceDensity g F₀ p.1 p.2 ∂((cubeMeasure k).prod volume) := by
  have hE := measurableSet_forestEvent F₀ hS
  rw [planeLaw, Measure.sum_apply _ hE]
  rw [tsum_eq_single (k - 1 - r)]
  · rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hterm : ∀ xs : Fin (k - 1 - r) → ConnState k, ∀ σ : Fin (k - 1 - r) → Bool,
        (((cubeMeasure k).prod volume).withDensity
          fun p ↦ planeDensity g p.1 (k - 1 - r) xs p.2).map
          (planeMk (k - 1 - r) xs σ) (forestEvent F₀ S) =
        ∫⁻ p, (planeMk (k - 1 - r) xs σ ⁻¹' forestEvent F₀ S).indicator
          (fun p ↦ planeDensity g p.1 (k - 1 - r) xs p.2) p ∂((cubeMeasure k).prod volume) := by
      intro xs σ
      rw [Measure.map_apply (measurable_planeMk _ xs σ) hE,
        withDensity_apply _ (measurable_planeMk _ xs σ hE),
        lintegral_indicator (measurable_planeMk _ xs σ hE)]
    have hmeas : ∀ xs : Fin (k - 1 - r) → ConnState k, ∀ σ : Fin (k - 1 - r) → Bool,
        Measurable ((planeMk (k - 1 - r) xs σ ⁻¹' forestEvent F₀ S).indicator
          (fun p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ) ↦
            planeDensity g p.1 (k - 1 - r) xs p.2)) := by
      intro xs σ
      exact ((measurable_historyDensity hg _ xs).const_mul _).indicator
        (measurable_planeMk _ xs σ hE)
    simp only [Measure.coe_finsetSum, Finset.sum_apply, hterm]
    have hswap : ∑ xs : Fin (k - 1 - r) → ConnState k, ∑ σ : Fin (k - 1 - r) → Bool,
        ∫⁻ p, (planeMk (k - 1 - r) xs σ ⁻¹' forestEvent F₀ S).indicator
          (fun p ↦ planeDensity g p.1 (k - 1 - r) xs p.2) p ∂((cubeMeasure k).prod volume) =
        ∫⁻ p, ∑ xs : Fin (k - 1 - r) → ConnState k, ∑ σ : Fin (k - 1 - r) → Bool,
          (planeMk (k - 1 - r) xs σ ⁻¹' forestEvent F₀ S).indicator
            (fun p ↦ planeDensity g p.1 (k - 1 - r) xs p.2) p
              ∂((cubeMeasure k).prod volume) := by
      rw [lintegral_finsetSum _ fun xs _ ↦ Finset.measurable_sum _ fun σ _ ↦ hmeas xs σ]
      refine Finset.sum_congr rfl fun xs _ ↦ ?_
      rw [lintegral_finsetSum _ fun σ _ ↦ hmeas xs σ]
    rw [hswap]
    have hpt : ∀ p : (Fin k → ℝ) × (Fin (k - 1 - r) → ℝ),
        ∑ xs : Fin (k - 1 - r) → ConnState k, ∑ σ : Fin (k - 1 - r) → Bool,
          (planeMk (k - 1 - r) xs σ ⁻¹' forestEvent F₀ S).indicator
            (fun p ↦ planeDensity g p.1 (k - 1 - r) xs p.2) p =
        S.indicator (fun q ↦ sourceDensity g F₀ q.1 q.2) (revTimes k (k - 1 - r) p) := by
      intro p
      rw [revTimes_apply]
      by_cases hp : (p.1, p.2 ∘ Fin.rev) ∈ S
      · rw [Set.indicator_of_mem hp, ← sum_planeDensity_patternForest g hr F₀ p.1 p.2]
        refine Finset.sum_congr rfl fun xs _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
        simp only [Set.indicator, Set.mem_preimage, planeMk_mem_forestEvent_iff hr, hp, and_true]
      · rw [Set.indicator_of_notMem hp]
        refine Finset.sum_eq_zero fun xs _ ↦ Finset.sum_eq_zero fun σ _ ↦ ?_
        rw [Set.indicator_of_notMem]
        rw [Set.mem_preimage, planeMk_mem_forestEvent_iff hr]
        exact fun h ↦ hp h.2
    rw [lintegral_congr hpt, (measurePreserving_revTimes (k - 1 - r)).lintegral_comp_emb
      (revTimes k (k - 1 - r)).measurableEmbedding, lintegral_indicator hS]
  · intro m hm
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun xs _ ↦ ?_
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    rw [Measure.map_apply (measurable_planeMk _ xs σ) hE]
    have : planeMk m xs σ ⁻¹' forestEvent F₀ S = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp ↦ planeMk_notMem_forestEvent hm F₀ S xs σ p hp
    rw [this, measure_empty]

/-- The unit cube `[0, 1]^k` of births. -/
def unitCube (k : ℕ) : Set (Fin k → ℝ) := Set.univ.pi fun _ ↦ Icc (0 : ℝ) 1

theorem cubeMeasure_eq_restrict : cubeMeasure k = (volume : Measure (Fin k → ℝ)).restrict (unitCube k) := by
  rw [cubeMeasure, unitCube, volume_pi, Measure.restrict_pi_pi]

theorem cubeMeasure_prod_eq {M : ℕ} :
    (cubeMeasure k).prod (volume : Measure (Fin M → ℝ)) =
      (volume : Measure ((Fin k → ℝ) × (Fin M → ℝ))).restrict (unitCube k ×ˢ Set.univ) := by
  rw [cubeMeasure_eq_restrict, ← Measure.restrict_univ (μ := (volume : Measure (Fin M → ℝ))),
    Measure.prod_restrict, Measure.volume_eq_prod]

/-- **Proposition `loi du coalescent généralisé` (N11), source form.** Under the plane law (the
decoded genealogy of the limiting coalescent, with independent uniform child orders), for
`k > r ≥ 0`, `F₀ ∈ 𝔉⁺_{r,k}` and a measurable set `S` of pairs (births, positive merge times),
`P(𝓕 = F₀, C₁ = ⋯ = C_r = 0, (B, (C_{r+1}, …, C_{k-1})) ∈ S)` is the Lebesgue integral of
`g_{r,k}(F₀, b, c)` over the pairs `(b, c) ∈ S` with `b ∈ [0, 1]^k`. -/
theorem planeLaw_forestEvent (hg : Measurable g) {r : ℕ} (hr : r < k) (F₀ : SourceForest r k)
    {S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))} (hS : MeasurableSet S) :
    planeLaw g k (forestEvent F₀ S) =
      ∫⁻ p in S ∩ unitCube k ×ˢ Set.univ, sourceDensity g F₀ p.1 p.2 := by
  rw [planeLaw_forestEvent_cube hg hr F₀ hS, cubeMeasure_prod_eq, Measure.restrict_restrict hS]

/-- **Proposition `loi du coalescent généralisé` (N11), product events.**
`P(𝓕 = F₀, B ∈ A, C₁ = ⋯ = C_r = 0, (C_{r+1}, …, C_{k-1}) ∈ A')` is the Lebesgue integral of
`g_{r,k}(F₀, b, c)` over `b ∈ A ∩ [0, 1]^k`, `c ∈ A'`. -/
theorem planeLaw_forestEvent_prod (hg : Measurable g) {r : ℕ} (hr : r < k)
    (F₀ : SourceForest r k) {A : Set (Fin k → ℝ)} (hA : MeasurableSet A)
    {A' : Set (Fin (k - 1 - r) → ℝ)} (hA' : MeasurableSet A') :
    planeLaw g k (forestEvent F₀ (A ×ˢ A')) =
      ∫⁻ p in (A ∩ unitCube k) ×ˢ A', sourceDensity g F₀ p.1 p.2 := by
  rw [planeLaw_forestEvent hg hr F₀ (hA.prod hA'), Set.prod_inter_prod, Set.inter_univ]

/-- **Proposition `loi du coalescent généralisé` (N11), joint law.** On the event `{𝓕 = F₀}`,
the births and the positive merge times `(B, (C_{r+1}, …, C_{k-1}))` have the density
`1_{[0,1]^k}(b) g_{r,k}(F₀, b, c)` against Lebesgue measure. -/
theorem map_restrict_planeLaw (hg : Measurable g) {r : ℕ} (hr : r < k) (F₀ : SourceForest r k) :
    ((planeLaw g k).restrict {h | planeForest h = some ⟨r, F₀⟩}).map
        (fun h ↦ (birthTimes h, upperMergeTimes r h)) =
      ((volume : Measure ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))).restrict
        (unitCube k ×ˢ Set.univ)).withDensity fun p ↦ sourceDensity g F₀ p.1 p.2 := by
  ext S hS
  rw [Measure.map_apply (measurable_birthUpper r) hS,
    Measure.restrict_apply (measurable_birthUpper r hS), withDensity_apply _ hS,
    Measure.restrict_restrict hS]
  have hev : (fun h ↦ (birthTimes h, upperMergeTimes r h)) ⁻¹' S ∩
      {h : PlaneHistorySpace k | planeForest h = some ⟨r, F₀⟩} = forestEvent F₀ S := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, forestEvent]
    constructor
    · rintro ⟨hS', hF⟩
      refine ⟨hF, fun j hj ↦ ?_, hS'⟩
      obtain ⟨m, xs, σ, b, cs⟩ := h
      have hm := patternForest_eq_some_imp ((planeForest_eq_some_iff _ r F₀).mp hF)
      simp only at hm
      obtain rfl : m = k - 1 - r := by omega
      exact sourceMergeTimes_planeMk_of_lt hr xs σ (b, cs) j hj
    · rintro ⟨hF, -, hS'⟩
      exact ⟨hS', hF⟩
  rw [hev, planeLaw_forestEvent hg hr F₀ hS]

/-! #### The forest is almost surely defined -/

theorem measurableSet_not_injective (m : ℕ) :
    MeasurableSet {q : (Fin k → ℝ) × (Fin m → ℝ) |
      Function.Injective q.2 ∧ ¬ Function.Injective (Sum.elim q.1 q.2)} := by
  have ht : ∀ a : Fin k ⊕ Fin m, Measurable fun q : (Fin k → ℝ) × (Fin m → ℝ) ↦ Sum.elim q.1 q.2 a := by
    intro a
    rcases a with j | s
    · exact (measurable_pi_apply j).comp measurable_fst
    · exact (measurable_pi_apply s).comp measurable_snd
  have h1 : {q : (Fin k → ℝ) × (Fin m → ℝ) | Function.Injective q.2} =
      ⋂ s : Fin m, ⋂ s' : Fin m, {q | q.2 s = q.2 s' → s = s'} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Function.Injective]
  have h2 : {q : (Fin k → ℝ) × (Fin m → ℝ) | ¬ Function.Injective (Sum.elim q.1 q.2)} =
      ⋃ a : Fin k ⊕ Fin m, ⋃ a' : Fin k ⊕ Fin m,
        {q | Sum.elim q.1 q.2 a = Sum.elim q.1 q.2 a' ∧ a ≠ a'} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Function.Injective, not_forall, exists_prop,
      ne_eq]
  have hset : {q : (Fin k → ℝ) × (Fin m → ℝ) |
      Function.Injective q.2 ∧ ¬ Function.Injective (Sum.elim q.1 q.2)} =
      {q : (Fin k → ℝ) × (Fin m → ℝ) | Function.Injective q.2} ∩
        {q | ¬ Function.Injective (Sum.elim q.1 q.2)} := rfl
  rw [hset, h1, h2]
  refine (MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun s' ↦ ?_).inter
    (MeasurableSet.iUnion fun a ↦ MeasurableSet.iUnion fun a' ↦ ?_)
  · by_cases hss : s = s'
    · simp [hss]
    · have : {q : (Fin k → ℝ) × (Fin m → ℝ) | q.2 s = q.2 s' → s = s'} =
          {q | q.2 s = q.2 s'}ᶜ := by
        ext q
        simp [hss]
      rw [this]
      exact (measurableSet_eq_fun ((measurable_pi_apply s).comp measurable_snd)
        ((measurable_pi_apply s').comp measurable_snd)).compl
  · by_cases haa : a = a'
    · simp [haa]
    · simp only [haa, ne_eq, not_false_eq_true, and_true]
      exact measurableSet_eq_fun (ht a) (ht a')

/-- Almost surely, births are distinct and distinct from distinct merge times. -/
theorem ae_injective_times (m : ℕ) :
    ∀ᵐ q ∂((cubeMeasure k).prod (volume : Measure (Fin m → ℝ))),
      Function.Injective q.2 → Function.Injective (Sum.elim q.1 q.2) := by
  rw [ae_iff]
  have hset : {q : (Fin k → ℝ) × (Fin m → ℝ) |
      ¬ (Function.Injective q.2 → Function.Injective (Sum.elim q.1 q.2))} =
      {q | Function.Injective q.2 ∧ ¬ Function.Injective (Sum.elim q.1 q.2)} := by
    ext q
    simp only [Set.mem_ofPred_eq, Classical.not_imp]
  rw [hset, Measure.prod_apply_symm (measurableSet_not_injective m)]
  have hzero : (fun cs : Fin m → ℝ ↦ cubeMeasure k ((fun b ↦ (b, cs)) ⁻¹'
      {q : (Fin k → ℝ) × (Fin m → ℝ) |
        Function.Injective q.2 ∧ ¬ Function.Injective (Sum.elim q.1 q.2)})) = fun _ ↦ 0 := by
    funext cs
    by_cases hcs : Function.Injective cs
    · have hgood := ae_cube_good (k := k) (Finset.univ.image cs)
      rw [ae_iff] at hgood
      refine measure_mono_null (fun b hb ↦ ?_) hgood
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hb ⊢
      rintro ⟨hb1, hb2⟩
      apply hb.2
      intro a a' h
      rcases a with j | s <;> rcases a' with j' | s'
      · exact congrArg Sum.inl (hb2 h)
      · have hmem : cs s' ∈ Finset.univ.image cs := Finset.mem_image_of_mem cs (Finset.mem_univ s')
        rw [← show b j = cs s' from h] at hmem
        exact ((hb1 j).2.2 hmem).elim
      · have hmem : cs s ∈ Finset.univ.image cs := Finset.mem_image_of_mem cs (Finset.mem_univ s)
        rw [show cs s = b j' from h] at hmem
        exact ((hb1 j').2.2 hmem).elim
      · exact congrArg Sum.inr (hcs h)
    · convert measure_empty (μ := cubeMeasure k)
      ext b
      simp [hcs]
  exact (lintegral_congr fun cs ↦ congrFun hzero cs).trans lintegral_zero

theorem patternForest_isSome {r m : ℕ} {xs : Fin m → ConnState k} {σ : Fin m → Bool}
    {cmp : Fin k ⊕ Fin m → Fin k ⊕ Fin m → Bool} {u : Fin m → Bool}
    (hc : m + r + 1 = k ∧ Function.Bijective (rankFin cmp) ∧ (∀ s, u s = true) ∧
      DAdm (rankFin cmp) xs) : (patternForest r xs σ cmp u).isSome := by
  unfold patternForest
  split_ifs
  rfl

/-- **The forest `𝓕` is almost surely defined**: under the plane law, almost every plane
history is admissible with distinct times, so it has a forest in some `𝔉⁺_{r,k}`. -/
theorem planeLaw_planeForest_eq_none (hk : 0 < k) :
    planeLaw g k {h | planeForest h = none} = 0 := by
  have hmeas : MeasurableSet {h : PlaneHistorySpace k | planeForest h = none} := by
    refine measurableSet_sigma_iff.mpr fun m ↦ ?_
    change MeasurableSet {q : PlaneFibre k m | planeForest (⟨m, q⟩ : PlaneHistorySpace k) = none}
    have : {q : PlaneFibre k m | planeForest (⟨m, q⟩ : PlaneHistorySpace k) = none} =
        discreteData m ⁻¹' {y | (patternForest (k - 1 - m) y.1 y.2.1 y.2.2.1 y.2.2.2).map
          (Sigma.mk (β := fun r ↦ SourceForest r k) (k - 1 - m)) = none} := rfl
    rw [this]
    exact measurable_discreteData m (Set.to_countable _).measurableSet
  rw [planeLaw, Measure.sum_apply _ hmeas]
  refine ENNReal.tsum_eq_zero.mpr fun m ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun xs _ ↦ ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun σ _ ↦ ?_
  rw [Measure.map_apply (measurable_planeMk _ xs σ) hmeas,
    withDensity_apply _ (measurable_planeMk _ xs σ hmeas),
    ← lintegral_indicator (measurable_planeMk _ xs σ hmeas)]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_injective_times (k := k) m] with p hp
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq]
  split_ifs with hnone
  · by_contra hne
    have hadm : IsAdmissible p.1 m 1 diagState xs p.2 := by
      by_contra ha
      apply hne
      simp [planeDensity, historyDensity, ha]
    have hinj := hp hadm.strictAnti.injective
    have hmk := hadm.le_card_sub_one
    have hc : m + (k - 1 - m) + 1 = k ∧ Function.Bijective (rankFin (cmpOf (Sum.elim p.1 p.2))) ∧
        (∀ s, unitPattern p.2 s = true) ∧ DAdm (rankFin (cmpOf (Sum.elim p.1 p.2))) xs := by
      obtain ⟨h1, h2⟩ := (isAdmissible_iff_dAdm hinj (rankFin_lt_iff hinj) xs).mp hadm
      exact ⟨by omega, rankFin_bijective_iff.mpr hinj, fun s ↦ by simp [unitPattern, h1 s], h2⟩
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp (patternForest_isSome (σ := σ) hc)
    have hsome : planeForest (planeMk m xs σ p) = some ⟨k - 1 - m, F⟩ := by
      show Option.map _ (patternForest (k - 1 - m) xs σ (cmpOf (Sum.elim p.1 p.2))
        (unitPattern p.2)) = _
      rw [hF]
      rfl
    rw [hsome] at hnone
    exact Option.some_ne_none _ hnone
  · rfl

/-! #### The forest map is a bijection onto admissible triplets -/

/-- Every admissible plane history with distinct times has a forest `F ∈ 𝔉⁺_{r,k}` with
`r = k - 1 - m`, and the triplet `(F, B, (C_{r+1}, …, C_{k-1}))` is admissible. -/
theorem exists_planeForest (hk : 0 < k) (h : PlaneHistorySpace k)
    (hadm : HistoryAdmissible (forgetOrders h))
    (hinj : Function.Injective (Sum.elim (birthTimes h) h.2.2.2.2)) :
    ∃ r, ∃ F : SourceForest r k, r < k ∧ planeForest h = some ⟨r, F⟩ ∧
      SourceAdmissible F (birthTimes h) (upperMergeTimes r h) := by
  obtain ⟨m, xs, σ, b, cs⟩ := h
  change IsAdmissible b m 1 diagState xs cs at hadm
  change Function.Injective (Sum.elim b cs) at hinj
  have hmk := hadm.le_card_sub_one
  obtain ⟨r, hr, rfl⟩ : ∃ r, r < k ∧ m = k - 1 - r := ⟨k - 1 - m, by omega, by omega⟩
  obtain ⟨h1, h2⟩ := (isAdmissible_iff_dAdm hinj (rankFin_lt_iff hinj) xs).mp hadm
  have hc : k - 1 - r + r + 1 = k ∧ Function.Bijective (rankFin (cmpOf (Sum.elim b cs))) ∧
      (∀ s, unitPattern cs s = true) ∧ DAdm (rankFin (cmpOf (Sum.elim b cs))) xs :=
    ⟨by omega, rankFin_bijective_iff.mpr hinj, fun s ↦ by simp [unitPattern, h1 s], h2⟩
  obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp (patternForest_isSome (σ := σ) hc)
  refine ⟨r, F, hr, (planeForest_eq_some_iff _ r F).mpr hF, ?_⟩
  change SourceAdmissible F b (upperMergeTimes r (planeMk (k - 1 - r) xs σ (b, cs)))
  rw [upperMergeTimes_planeMk hr]
  obtain ⟨_, _, hFeq⟩ := (patternForest_eq_some_iff hr xs σ b cs F).mp hF
  have hD := ((isAdmissible_iff_dAdm hinj (labelEquiv_lt_iff_times hinj
    (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) xs).mp hadm).2
  refine (sourceAdmissible_iff hr F cs).mpr ⟨hinj, hadm.time_mem, hadm.strictAnti, ?_⟩
  rw [← hFeq]
  exact hD.fits σ

/-- Every admissible triplet `(F₀, b, c)` with `F₀ ∈ 𝔉⁺_{r,k}` is the forest, births and
positive merge times of exactly one plane history. -/
theorem existsUnique_planeForest {r : ℕ} (hr : r < k) (F₀ : SourceForest r k) {b : Fin k → ℝ}
    {c : Fin (k - 1 - r) → ℝ} (hS : SourceAdmissible F₀ b c) :
    ∃! h : PlaneHistorySpace k, planeForest h = some ⟨r, F₀⟩ ∧ birthTimes h = b ∧
      upperMergeTimes r h = c := by
  obtain ⟨hinj, hunit, hanti, hfits⟩ :=
    (sourceAdmissible_iff hr F₀ (c ∘ Fin.rev)).mp (sourceAdmissible_rev hS)
  have key := patternForest_eq_some_iff_eq hr F₀ hinj hunit hanti hfits
  have hc : (c ∘ Fin.rev) ∘ Fin.rev = c := funext fun i ↦ by simp
  refine ⟨planeMk (k - 1 - r)
    (forestStates (labelEquiv (cmpOf (Sum.elim b (c ∘ Fin.rev))) (rankFin_bijective_iff.mpr hinj)
      (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) F₀.1)
    (forestOrders (labelEquiv (cmpOf (Sum.elim b (c ∘ Fin.rev))) (rankFin_bijective_iff.mpr hinj)
      (show k + (k - 1 - r) = 2 * k - 1 - r by omega)) F₀.1) (b, c ∘ Fin.rev),
    ⟨(planeForest_eq_some_iff _ r F₀).mpr ((key _ _).mpr ⟨rfl, rfl⟩), rfl, ?_⟩, ?_⟩
  · rw [upperMergeTimes_planeMk hr]
    exact hc
  · rintro ⟨m, xs, σ, b', cs⟩ ⟨hF, hb, hup⟩
    have hF' := (planeForest_eq_some_iff _ r F₀).mp hF
    have hm := patternForest_eq_some_imp hF'
    simp only at hm
    obtain rfl : m = k - 1 - r := by omega
    change b' = b at hb
    subst hb
    change upperMergeTimes r (planeMk (k - 1 - r) xs σ (b', cs)) = c at hup
    rw [upperMergeTimes_planeMk hr] at hup
    have hcs : cs = c ∘ Fin.rev := by
      rw [← hup]
      funext i
      simp
    subst hcs
    obtain ⟨rfl, rfl⟩ := (key xs σ).mp hF'
    rfl

/-- **Proposition `loi du coalescent généralisé` (N11)**, under the source hypotheses
(`g = 1/f` measurable with locally square-integrable windows). The plane law is the law of the
decoded genealogy of the limiting coalescent (`map_forgetOrders_planeLaw`) with independent
uniform child orders (`planeLaw_eq_uniformOrders`, by construction of `planeLaw`); for
`k ≥ 1` its forest `𝓕` is almost surely defined; and for `k > r ≥ 0` and `F₀ ∈ 𝔉⁺_{r,k}`,
`P(𝓕 = F₀, C₁ = ⋯ = C_r = 0, (B, (C_{r+1}, …, C_{k-1})) ∈ S) = ∫_S 1_{[0,1]^k}(b) g_{r,k}(F₀, b, c)`. -/
theorem sourceForest_law (hg : Measurable g) (hg2 : LocSqIntegrable g) (hk : 0 < k) :
    (planeLaw g k).map forgetOrders =
        (criticalGenealogyLimit g k : Measure (GenealogySpace k)).map decodeHistory ∧
      planeLaw g k {h | planeForest h = none} = 0 ∧
      ∀ r, r < k → ∀ (F₀ : SourceForest r k) (S : Set ((Fin k → ℝ) × (Fin (k - 1 - r) → ℝ))),
        MeasurableSet S → planeLaw g k (forestEvent F₀ S) =
          ∫⁻ p in S ∩ unitCube k ×ˢ Set.univ, sourceDensity g F₀ p.1 p.2 :=
  ⟨map_forgetOrders_planeLaw hg hg2, planeLaw_planeForest_eq_none hk,
    fun _ hr F₀ _ hS ↦ planeLaw_forestEvent hg hr F₀ hS⟩

end Density

end Freezing2.CoalescentDensity
