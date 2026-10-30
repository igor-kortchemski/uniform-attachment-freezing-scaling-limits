module

public import Freezing2.Audit.ExcursionCounterexamples
public import Freezing2.Companion.ForwardLaw

/-!
# The forward tree driven by an excursion is a uniform plane tree

This file covers the second clause of inventory item U01 and external item E02 of
`docs/source-inventory.md`. The source (lines 259 and 1744) cites [BBKK23+, Theorem 2]
for the following claim. Let the walk $(S_k)_{0 \le k \le 2n+1}$ be a simple random walk
started at $1$ and conditioned to first hit $0$ at time $2n+1$. Then $\mathcal T_{2n+1}$ has
the law of a uniform plane tree with $n+1$ vertices, "as a random compact metric space". In
`../freezing1` this example is row A03, which is open, so nothing is imported from there.

## Plane trees

Plane trees use Neveu's formalism (`IsPlaneTree`). A plane tree is a finite set
`t : Finset (List ℕ)` of words with three properties: it contains the root `[]`, it is closed
under deleting the last letter, and if it contains `a ++ [i]` then it contains `a ++ [j]` for
every `j ≤ i`. The word `a ++ [i]` is the `i`-th child of `a`, counting from `0`.
`planeTrees k` is the finite set of plane trees with `k` vertices.

## From the forward tree to a plane tree

In `Freezing1.Forward.State`, a vertex is identified by its birth time and records its
parent. Order the children of every vertex by birth time. `birthRank s u` is the number of
older siblings of `u`. `birthAddress s u` is the word of birth ranks along the ancestral line
of `u`. `planeTreeOf s` is the set of these words. For every reachable state,
`planeTreeIso` is a graph isomorphism from `s.tree` onto `planeGraph (planeTreeOf s)` that
sends the root `0` to `[]`. Graph isomorphisms preserve graph distances (`dist_eq_of_iso`).

## The conditioned walk

`finSigns w` turns an increment sequence `w : Fin m → Bool` into a sign schedule. The
measure `excursionTreeLaw n` mixes `Forward.treeLaw (finSigns w) (2n+1)` over
`Audit.excursionLaw n`, the uniform law on excursion increment sequences.
`Audit.excursionLaw_eq_cond` identifies it with the conditioned simple random walk, and
`excursionTreeLaw_eq_cond_bind` restates the mixture with that conditioning. Since the walk
hits `0` at time `2n+1`, all vertices are frozen at that time.

## Main results

* `map_planeTreeOf_excursionTreeLaw`: the law of the plane tree of $\mathcal T_{2n+1}$ is
  `Measure.uniformOfFinset (planeTrees (n + 1))`.
* `excursionTreeLaw_planeTreeOf_eq`: each plane tree with $n+1$ vertices has probability
  $1/C_n$.
* `excursionTreeLaw_ae_iso` and `excursionTreeLaw_ae_isometry`: almost surely,
  $\mathcal T_{2n+1}$ is isomorphic as a rooted graph to the graph of its plane tree, hence
  isometric to it for the graph distances.
* `card_planeTrees`: there are $C_n$ plane trees with $n+1$ vertices. This is derived from
  the two previous probability statements, not from a bijection with Dyck words.
* `iidTreeLaw_planeTreeOf_eq`: with i.i.d. uniform signs and no conditioning, each plane tree
  with $n+1$ vertices is the plane tree of $\mathcal T_{2n+1}$ with probability
  $2^{-(2n+1)}$.

## Proof

The children need no random reordering: ordering them by birth time already gives the
uniform law. Fix a plane tree `t` with $n+1$ vertices. A state is compatible with `t`
(`PlaneCompatible`) if every vertex has its address in `t`, at most as many children as
in `t`, and exactly as many once frozen. From a compatible state with active set $A$, a
$+1$ step stays compatible iff the chosen vertex still lacks a child of `t`, and a $-1$
step stays compatible iff it does not. So the probabilities of staying compatible under
the two signs add up to $|A|/|A| = 1$ (`transitionLaw_planeCompatible_add`). Hence, summed
over all $2^m$ sign sequences of length $m \le 2n+1$, the probabilities of compatibility
add up to $1$ (`sum_treeLaw_compatible`). At time $2n+1$, compatibility means that the plane
tree of the state is `t` (`planeCompatible_iff_planeTreeOf_eq`). That event forces the signs
to be an excursion (`mem_excursionPaths_of_card`). So the $C_n$ excursions carry total
probability $1$, and the mixture gives $1/C_n$.

## Relation to the source

* The source compares laws "as a random compact metric space". Here the plane tree itself
  is uniform, and the forward tree is almost surely rooted-isomorphic to the graph of its
  plane tree. The law of the isometry class is not formed in `MeasuredGHSpace`.
* [BBKK23+, Theorem 2] is the geometric Bienaymé statement for i.i.d. signs (row T02 of
  `../freezing1`). It is not used: the conditioned statement is proved by direct counting.
* The convergence to the Brownian CRT in the proof of `cor:CRT` is not addressed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Freezing2

open Freezing1

/-! ### Plane trees in Neveu's formalism -/

/-- A finite plane tree in Neveu's formalism: a finite set of words over `ℕ` containing the
root `[]`, closed under deleting the last letter, and such that if the `i`-th child
`a ++ [i]` of `a` belongs to it, so do the earlier children `a ++ [j]`, `j ≤ i`. -/
structure IsPlaneTree (t : Finset (List ℕ)) : Prop where
  nil_mem : [] ∈ t
  parent_mem : ∀ a i, a ++ [i] ∈ t → a ∈ t
  sibling_mem : ∀ a i j, a ++ [i] ∈ t → j ≤ i → a ++ [j] ∈ t

/-- The number of children of the word `a` in `t`, i.e. of words `a ++ [i]` in `t`. -/
def childNum (t : Finset (List ℕ)) (a : List ℕ) : ℕ :=
  (t.filter (fun b => b ≠ [] ∧ b.dropLast = a)).card

theorem word_append_singleton_injective (a : List ℕ) :
    Function.Injective (fun i : ℕ => a ++ [i]) := by
  intro i j h
  simpa using h

theorem IsPlaneTree.append_mem_iff {t : Finset (List ℕ)} (ht : IsPlaneTree t)
    (a : List ℕ) (i : ℕ) : a ++ [i] ∈ t ↔ i < childNum t a := by
  classical
  constructor
  · intro hi
    have hsub : (Finset.range (i + 1)).image (fun j => a ++ [j]) ⊆
        t.filter (fun b => b ≠ [] ∧ b.dropLast = a) := by
      intro b hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      simp only [Finset.mem_filter, ne_eq, List.append_eq_nil_iff, List.cons_ne_self,
        and_false, not_false_eq_true, List.dropLast_concat, and_true]
      exact ht.sibling_mem a i j hi (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (word_append_singleton_injective a),
      Finset.card_range] at this
    exact this
  · intro hi
    by_contra hni
    have hsub : t.filter (fun b => b ≠ [] ∧ b.dropLast = a) ⊆
        (Finset.range i).image (fun j => a ++ [j]) := by
      intro b hb
      obtain ⟨hbt, hb0, hba⟩ := Finset.mem_filter.mp hb
      have hb' : a ++ [b.getLast hb0] = b := by
        rw [← hba]; exact List.dropLast_append_getLast hb0
      refine Finset.mem_image.mpr ⟨b.getLast hb0, Finset.mem_range.mpr ?_, hb'⟩
      by_contra hle
      exact hni (ht.sibling_mem a (b.getLast hb0) i (by rw [hb']; exact hbt) (not_lt.mp hle))
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (word_append_singleton_injective a),
      Finset.card_range] at this
    exact absurd hi (not_lt.mpr this)

theorem IsPlaneTree.prefix_mem {t : Finset (List ℕ)} (ht : IsPlaneTree t) (b c : List ℕ)
    (h : b ++ c ∈ t) : b ∈ t := by
  induction c using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton c x ih =>
    exact ih (ht.parent_mem _ x (by simpa [List.append_assoc] using h))

/-- Every word of a plane tree has length less than its number of vertices. -/
theorem IsPlaneTree.length_lt {t : Finset (List ℕ)} (ht : IsPlaneTree t) {a : List ℕ}
    (ha : a ∈ t) : a.length < t.card := by
  classical
  have hsub : (Finset.range (a.length + 1)).image (fun j => a.take j) ⊆ t := by
    intro b hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact ht.prefix_mem _ (a.drop j) (by rw [List.take_append_drop]; exact ha)
  have hinj : Set.InjOn (fun j => a.take j) (Finset.range (a.length + 1) : Set ℕ) := by
    intro i hi j hj hij
    have := congrArg List.length hij
    simp only [List.length_take] at this
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  omega

theorem IsPlaneTree.letter_lt {t : Finset (List ℕ)} (ht : IsPlaneTree t) {a : List ℕ}
    (ha : a ∈ t) {x : ℕ} (hx : x ∈ a) : x < t.card := by
  classical
  obtain ⟨b, c, rfl⟩ := List.mem_iff_append.mp hx
  have hbx : b ++ [x] ∈ t := ht.prefix_mem _ c (by simpa using ha)
  have hb : b ∈ t := ht.parent_mem b x hbx
  have hsub : insert b ((Finset.range (x + 1)).image (fun j => b ++ [j])) ⊆ t := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hb
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
      exact ht.sibling_mem b x j hbx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have hnot : b ∉ (Finset.range (x + 1)).image (fun j => b ++ [j]) := by
    intro hb'
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb'
    have := congrArg List.length hj
    simp at this
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (word_append_singleton_injective b), Finset.card_range] at this
  omega

/-- Words of length at most `d` with letters less than `k`. -/
def wordBox (k : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | d + 1 => insert [] ((Finset.range k ×ˢ wordBox k d).image (fun p => p.1 :: p.2))

theorem mem_wordBox {k d : ℕ} {l : List ℕ} :
    l ∈ wordBox k d ↔ l.length ≤ d ∧ ∀ x ∈ l, x < k := by
  induction d generalizing l with
  | zero => cases l <;> simp [wordBox]
  | succ d ih =>
    cases l with
    | nil => simp [wordBox]
    | cons x l =>
      simp only [wordBox, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_product,
        Finset.mem_range, Prod.exists, List.cons.injEq, false_or, List.length_cons,
        List.mem_cons, forall_eq_or_imp, ih]
      constructor
      · rintro ⟨a, b, ⟨ha, hb1, hb2⟩, rfl, rfl⟩
        exact ⟨by omega, ha, hb2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨x, l, ⟨h2, by omega, h3⟩, rfl, rfl⟩

open Classical in
/-- The finite set of plane trees with `k` vertices. Every word of such a tree has length
less than `k` and letters less than `k` (`mem_planeTrees`). -/
noncomputable def planeTrees (k : ℕ) : Finset (Finset (List ℕ)) :=
  (wordBox k k).powerset.filter (fun t => IsPlaneTree t ∧ t.card = k)

theorem mem_planeTrees {k : ℕ} {t : Finset (List ℕ)} :
    t ∈ planeTrees k ↔ IsPlaneTree t ∧ t.card = k := by
  classical
  unfold planeTrees
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · rintro ⟨ht, hk⟩
    refine ⟨fun a ha => mem_wordBox.mpr ⟨?_, fun x hx => ?_⟩, ht, hk⟩
    · exact (hk ▸ ht.length_lt ha).le
    · exact hk ▸ ht.letter_lt ha hx

/-! ### The plane tree of a forward state -/

/-- The children of `v` in the forward state `s`: the non-root vertices whose parent is `v`. -/
def childSet (s : Forward.State) (v : ℕ) : Finset ℕ :=
  s.vertices.filter (fun u => u ≠ 0 ∧ s.parent u = v)

/-- The number of children of `v` in `s`. -/
def childCount (s : Forward.State) (v : ℕ) : ℕ := (childSet s v).card

/-- The birth rank of `u`: the number of its siblings born before it. -/
def birthRank (s : Forward.State) (u : ℕ) : ℕ :=
  ((childSet s (s.parent u)).filter (· < u)).card

/-- The Ulam–Harris–Neveu address of `v` when the children of every vertex are ordered by
birth time: the birth ranks along the ancestral line of `v`, from the root. -/
def birthAddress (s : Forward.State) (v : ℕ) : List ℕ :=
  if _h : v ≠ 0 ∧ s.parent v < v then birthAddress s (s.parent v) ++ [birthRank s v] else []
termination_by v
decreasing_by exact _h.2

/-- The plane tree of the forward state `s`, children ordered by birth time: the set of
addresses of its vertices. -/
def planeTreeOf (s : Forward.State) : Finset (List ℕ) := s.vertices.image (birthAddress s)

theorem birthAddress_zero (s : Forward.State) : birthAddress s 0 = [] := by
  rw [birthAddress, dite_eq_right (by simp)]

theorem birthAddress_of_ne_zero {s : Forward.State} {v : ℕ} (hv : v ≠ 0) (hp : s.parent v < v) :
    birthAddress s v = birthAddress s (s.parent v) ++ [birthRank s v] := by
  rw [birthAddress, dite_eq_left ⟨hv, hp⟩]

theorem birthAddress_eq_of_valid {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) {v : ℕ}
    (hv : v ∈ s.vertices) (h0 : v ≠ 0) :
    birthAddress s v = birthAddress s (s.parent v) ++ [birthRank s v] :=
  birthAddress_of_ne_zero h0 (h.parent_lt v hv h0)

theorem birthAddress_eq_nil_of_not {s : Forward.State} {v : ℕ}
    (h : ¬(v ≠ 0 ∧ s.parent v < v)) :
    birthAddress s v = [] := by
  rw [birthAddress, dite_eq_right h]

theorem birthAddress_congr {s₁ s₂ : Forward.State} (hV : s₁.vertices = s₂.vertices)
    (hp : s₁.parent = s₂.parent) (v : ℕ) : birthAddress s₁ v = birthAddress s₂ v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    have hr : birthRank s₁ v = birthRank s₂ v := by
      simp only [birthRank, childSet, hV, hp]
    by_cases hc : v ≠ 0 ∧ s₁.parent v < v
    · rw [birthAddress_of_ne_zero hc.1 hc.2, birthAddress_of_ne_zero hc.1 (hp ▸ hc.2),
        ih _ hc.2, hp, hr]
    · rw [birthAddress_eq_nil_of_not hc, birthAddress_eq_nil_of_not (hp ▸ hc)]

theorem mem_childSet {s : Forward.State} {v u : ℕ} :
    u ∈ childSet s v ↔ u ∈ s.vertices ∧ u ≠ 0 ∧ s.parent u = v := by
  simp [childSet]

/-! ### Birth ranks enumerate the children -/

theorem birthRank_lt_childCount {s : Forward.State} {v u : ℕ} (hu : u ∈ childSet s v) :
    birthRank s u < childCount s v := by
  have hp := (mem_childSet.mp hu).2.2
  unfold birthRank childCount
  rw [hp]
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  have := Finset.mem_filter.mp (hsub hu)
  exact lt_irrefl u this.2

theorem birthRank_lt_birthRank {s : Forward.State} {v u w : ℕ} (hu : u ∈ childSet s v)
    (hw : w ∈ childSet s v) (huw : u < w) : birthRank s u < birthRank s w := by
  have hpu := (mem_childSet.mp hu).2.2
  have hpw := (mem_childSet.mp hw).2.2
  unfold birthRank
  rw [hpu, hpw]
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx1, hx2.trans huw⟩
  · exact lt_irrefl u (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hu, huw⟩))).2

theorem birthRank_injOn (s : Forward.State) (v : ℕ) :
    Set.InjOn (birthRank s) (childSet s v : Set ℕ) := by
  intro u hu w hw huw
  rcases lt_trichotomy u w with h | h | h
  · exact absurd huw (birthRank_lt_birthRank hu hw h).ne
  · exact h
  · exact absurd huw (birthRank_lt_birthRank hw hu h).ne'

theorem image_birthRank (s : Forward.State) (v : ℕ) :
    (childSet s v).image (birthRank s) = Finset.range (childCount s v) := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (birthRank_lt_childCount hu)
  · rw [Finset.card_image_of_injOn (birthRank_injOn s v), Finset.card_range]
    rfl

theorem exists_birthRank_eq {s : Forward.State} {v i : ℕ} (hi : i < childCount s v) :
    ∃ u ∈ childSet s v, birthRank s u = i := by
  have : i ∈ (childSet s v).image (birthRank s) := by
    rw [image_birthRank]; exact Finset.mem_range.mpr hi
  exact Finset.mem_image.mp this

/-! ### Addresses of a valid state -/

theorem birthAddress_eq_nil_iff_of_valid {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    {v : ℕ} (hv : v ∈ s.vertices) : birthAddress s v = [] ↔ v = 0 := by
  constructor
  · intro hnil
    by_contra h0
    rw [birthAddress_eq_of_valid h hv h0] at hnil
    simp at hnil
  · rintro rfl; exact birthAddress_zero s

theorem birthAddress_injOn_of_valid {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) :
    Set.InjOn (birthAddress s) (s.vertices : Set ℕ) := by
  intro u hu w hw huw
  induction u using Nat.strong_induction_on generalizing w with
  | h u ih =>
    by_cases hu0 : u = 0
    · subst u
      exact ((birthAddress_eq_nil_iff_of_valid h hw).mp (huw ▸ birthAddress_zero s)).symm
    · have hw0 : w ≠ 0 := by
        rintro rfl
        exact hu0 ((birthAddress_eq_nil_iff_of_valid h hu).mp (huw.trans (birthAddress_zero s)))
      rw [birthAddress_eq_of_valid h hu hu0, birthAddress_eq_of_valid h hw hw0] at huw
      obtain ⟨hpa, hr⟩ := List.append_inj huw (by
        have := congrArg List.length huw
        simpa using this)
      have hp : s.parent u = s.parent w :=
        ih _ (h.parent_lt u hu hu0) (h.parent_mem u hu) (h.parent_mem w hw) hpa
      have hr' : birthRank s u = birthRank s w := by simpa using hr
      exact birthRank_injOn s (s.parent u)
        (mem_childSet.mpr ⟨hu, hu0, rfl⟩) (mem_childSet.mpr ⟨hw, hw0, hp.symm⟩) hr'

theorem card_planeTreeOf_of_valid {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) :
    (planeTreeOf s).card = s.vertices.card :=
  Finset.card_image_of_injOn (birthAddress_injOn_of_valid h)

theorem birthAddress_mem_planeTreeOf {s : Forward.State} {v : ℕ} (hv : v ∈ s.vertices) :
    birthAddress s v ∈ planeTreeOf s :=
  Finset.mem_image_of_mem _ hv

/-- A word `a ++ [i]` is the address of a vertex iff `a` is the address of a vertex with
more than `i` children. -/
theorem append_mem_planeTreeOf_iff {k : ℕ} {s : Forward.State}
    (h : Forward.ValidAt k s) {v : ℕ} (hv : v ∈ s.vertices) (i : ℕ) :
    birthAddress s v ++ [i] ∈ planeTreeOf s ↔ i < childCount s v := by
  constructor
  · intro hi
    obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp hi
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [birthAddress_zero] at hua
      simp at hua
    rw [birthAddress_eq_of_valid h hu hu0] at hua
    obtain ⟨hpa, hr⟩ := List.append_inj hua (by
      have := congrArg List.length hua
      simpa using this)
    have hp := birthAddress_injOn_of_valid h (h.parent_mem u hu) hv hpa
    have hr' : birthRank s u = i := by simpa using hr
    rw [← hr']
    exact birthRank_lt_childCount (mem_childSet.mpr ⟨hu, hu0, hp⟩)
  · intro hi
    obtain ⟨u, hu, rfl⟩ := exists_birthRank_eq hi
    obtain ⟨hu1, hu0, hpu⟩ := mem_childSet.mp hu
    rw [← hpu, ← birthAddress_eq_of_valid h hu1 hu0]
    exact birthAddress_mem_planeTreeOf hu1

theorem isPlaneTree_planeTreeOf {k : ℕ} {s : Forward.State}
    (h : Forward.ValidAt k s) : IsPlaneTree (planeTreeOf s) where
  nil_mem := birthAddress_zero s ▸ birthAddress_mem_planeTreeOf h.root_mem
  parent_mem a i hai := by
    obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp hai
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [birthAddress_zero] at hua
      simp at hua
    rw [birthAddress_eq_of_valid h hu hu0] at hua
    obtain ⟨hpa, -⟩ := List.append_inj hua (by
      have := congrArg List.length hua
      simpa using this)
    exact hpa ▸ birthAddress_mem_planeTreeOf (h.parent_mem u hu)
  sibling_mem a i j hai hji := by
    obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp hai
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [birthAddress_zero] at hua
      simp at hua
    rw [birthAddress_eq_of_valid h hu hu0] at hua
    obtain ⟨hpa, hr⟩ := List.append_inj hua (by
      have := congrArg List.length hua
      simpa using this)
    have hr' : birthRank s u = i := by simpa using hr
    rw [← hpa, append_mem_planeTreeOf_iff h (h.parent_mem u hu)]
    have := birthRank_lt_childCount (mem_childSet.mpr ⟨hu, hu0, rfl⟩)
    omega

theorem childNum_planeTreeOf {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    childNum (planeTreeOf s) (birthAddress s v) = childCount s v := by
  have ht := isPlaneTree_planeTreeOf h
  apply le_antisymm
  · by_contra hlt
    have := (ht.append_mem_iff (birthAddress s v) (childCount s v)).mpr (not_le.mp hlt)
    exact lt_irrefl _ ((append_mem_planeTreeOf_iff h hv _).mp this)
  · by_contra hlt
    have := (append_mem_planeTreeOf_iff h hv (childNum (planeTreeOf s) (birthAddress s v))).mpr
      (not_le.mp hlt)
    exact lt_irrefl _ ((ht.append_mem_iff _ _).mp this)

/-! ### One attachment step -/

theorem succ_notMem_vertices {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) :
    k + 1 ∉ s.vertices := by
  intro hk
  have := h.vertices_le _ hk
  omega

theorem childSet_attach {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) (v u : ℕ) :
    childSet (Forward.attach s (k + 1) v) u =
      if v = u then insert (k + 1) (childSet s u) else childSet s u := by
  have hfresh := succ_notMem_vertices h
  ext w
  by_cases hw : w = k + 1
  · subst hw
    split_ifs with hvu
    · simp [childSet, Forward.attach, hvu]
    · rw [mem_childSet, mem_childSet]
      simp [Forward.attach, hvu, hfresh]
  · have hpw : (Forward.attach s (k + 1) v).parent w = s.parent w := by
      simp only [Forward.attach]; exact Function.update_of_ne hw _ _
    have hmem : w ∈ (Forward.attach s (k + 1) v).vertices ↔ w ∈ s.vertices := by
      simp [Forward.attach, hw]
    have hc : w ∈ childSet (Forward.attach s (k + 1) v) u ↔ w ∈ childSet s u := by
      rw [mem_childSet, mem_childSet, hmem, hpw]
    rw [hc]
    split_ifs <;> simp [hw]

theorem childCount_attach {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) (v u : ℕ) :
    childCount (Forward.attach s (k + 1) v) u =
      childCount s u + if v = u then 1 else 0 := by
  unfold childCount
  rw [childSet_attach h]
  split_ifs with hvu
  · rw [Finset.card_insert_of_notMem]
    intro hk
    exact succ_notMem_vertices h (mem_childSet.mp hk).1
  · rfl

theorem childCount_fresh {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) :
    childCount s (k + 1) = 0 := by
  unfold childCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  obtain ⟨hu1, hu0, hpu⟩ := mem_childSet.mp hu
  have h1 := h.parent_lt u hu1 hu0
  have h2 := h.vertices_le u hu1
  omega

theorem birthRank_attach_of_mem {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    (v : ℕ) {u : ℕ} (hu : u ∈ s.vertices) :
    birthRank (Forward.attach s (k + 1) v) u = birthRank s u := by
  have hfresh := succ_notMem_vertices h
  have huk : u ≠ k + 1 := fun he => hfresh (he ▸ hu)
  have hlt : ¬ k + 1 < u := by have := h.vertices_le u hu; omega
  unfold birthRank
  have hp : (Forward.attach s (k + 1) v).parent u = s.parent u := by
    simp only [Forward.attach]; exact Function.update_of_ne huk _ _
  rw [hp, childSet_attach h]
  split_ifs
  · rw [Finset.filter_insert, ite_eq_right hlt]
  · rfl

theorem birthRank_attach_fresh {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) (v : ℕ) :
    birthRank (Forward.attach s (k + 1) v) (k + 1) = childCount s v := by
  unfold birthRank childCount
  have hp : (Forward.attach s (k + 1) v).parent (k + 1) = v := by
    simp only [Forward.attach, Function.update_self]
  rw [hp, childSet_attach h, ite_eq_left rfl, Finset.filter_insert, ite_eq_right (lt_irrefl _)]
  congr 1
  apply Finset.filter_true_of_mem
  intro u hu
  have := h.vertices_le u (mem_childSet.mp hu).1
  omega

theorem birthAddress_attach_of_mem {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    (v : ℕ) {u : ℕ} (hu : u ∈ s.vertices) :
    birthAddress (Forward.attach s (k + 1) v) u = birthAddress s u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    by_cases hu0 : u = 0
    · subst u; rw [birthAddress_zero, birthAddress_zero]
    · have hfresh := succ_notMem_vertices h
      have huk : u ≠ k + 1 := fun he => hfresh (he ▸ hu)
      have hp : (Forward.attach s (k + 1) v).parent u = s.parent u := by
        simp only [Forward.attach]; exact Function.update_of_ne huk _ _
      have hlt := h.parent_lt u hu hu0
      rw [birthAddress_of_ne_zero hu0 (hp ▸ hlt), birthAddress_eq_of_valid h hu hu0, hp,
        ih _ hlt (h.parent_mem u hu), birthRank_attach_of_mem h v hu]

theorem birthAddress_attach_fresh {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    {v : ℕ} (hv : v ∈ s.vertices) :
    birthAddress (Forward.attach s (k + 1) v) (k + 1) = birthAddress s v ++ [childCount s v] := by
  have hp : (Forward.attach s (k + 1) v).parent (k + 1) = v := by
    simp only [Forward.attach, Function.update_self]
  have hlt : (Forward.attach s (k + 1) v).parent (k + 1) < k + 1 := by
    rw [hp]; exact Nat.lt_succ_of_le (h.vertices_le v hv)
  rw [birthAddress_of_ne_zero (Nat.add_one_ne_zero k) hlt, hp, birthAddress_attach_of_mem h v hv,
    birthRank_attach_fresh h]

/-! ### Compatibility with a target plane tree -/

/-- The current state `s` can still grow into the plane tree `t`: every vertex has its
address in `t`, no more children than its counterpart in `t`, and exactly as many once
it is frozen. -/
def PlaneCompatible (t : Finset (List ℕ)) (s : Forward.State) : Prop :=
  ∀ v ∈ s.vertices, birthAddress s v ∈ t ∧
    childCount s v ≤ childNum t (birthAddress s v) ∧
    (v ∉ s.active → childCount s v = childNum t (birthAddress s v))

theorem planeCompatible_attach_iff {t : Finset (List ℕ)} (ht : IsPlaneTree t) {k : ℕ}
    {s : Forward.State} (h : Forward.ValidAt k s) {v : ℕ} (hv : v ∈ s.active) :
    PlaneCompatible t (Forward.attach s (k + 1) v) ↔
      PlaneCompatible t s ∧ childCount s v < childNum t (birthAddress s v) := by
  have hfresh := succ_notMem_vertices h
  have hvV := h.active_subset hv
  constructor
  · intro hc
    have hcv := hc v (Finset.mem_insert_of_mem hvV)
    rw [birthAddress_attach_of_mem h v hvV, childCount_attach h, ite_eq_left rfl] at hcv
    refine ⟨fun u hu => ?_, by omega⟩
    have hcu := hc u (Finset.mem_insert_of_mem hu)
    have huk : u ≠ k + 1 := fun he => hfresh (he ▸ hu)
    rw [birthAddress_attach_of_mem h v hu, childCount_attach h] at hcu
    refine ⟨hcu.1, ?_, fun hua => ?_⟩
    · split_ifs at hcu <;> omega
    · have hvu : v ≠ u := fun he => hua (he ▸ hv)
      have hua' : u ∉ (Forward.attach s (k + 1) v).active := by
        simp only [Forward.attach, Finset.mem_insert, huk, hua, or_self, not_false_eq_true]
      have := hcu.2.2 hua'
      rw [ite_eq_right hvu] at this
      omega
  · rintro ⟨hc, hlt⟩ u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · have hvk : v ≠ k + 1 := fun he => hfresh (he ▸ hvV)
      rw [birthAddress_attach_fresh h hvV, childCount_attach h, childCount_fresh h,
        ite_eq_right hvk]
      refine ⟨(ht.append_mem_iff _ _).mpr hlt, by omega, fun hua => ?_⟩
      exact absurd (Finset.mem_insert_self _ _) hua
    · have hcu := hc u hu
      have huk : u ≠ k + 1 := fun he => hfresh (he ▸ hu)
      rw [birthAddress_attach_of_mem h v hu, childCount_attach h]
      refine ⟨hcu.1, ?_, fun hua => ?_⟩
      · split_ifs with hvu
        · subst hvu; omega
        · omega
      · have hua' : u ∉ s.active := fun h' => hua (Finset.mem_insert_of_mem h')
        have hvu : v ≠ u := fun he => hua' (he ▸ hv)
        rw [ite_eq_right hvu]
        exact hcu.2.2 hua'

theorem planeCompatible_freeze_iff {t : Finset (List ℕ)} {k : ℕ} {s : Forward.State}
    (h : Forward.ValidAt k s) {v : ℕ} (hv : v ∈ s.active) :
    PlaneCompatible t (Forward.freeze s (k + 1) v) ↔
      PlaneCompatible t s ∧ childCount s v = childNum t (birthAddress s v) := by
  have ha : birthAddress (Forward.freeze s (k + 1) v) = birthAddress s :=
    funext (birthAddress_congr rfl rfl)
  have hc : childCount (Forward.freeze s (k + 1) v) = childCount s := rfl
  have hA : (Forward.freeze s (k + 1) v).active = s.active.erase v := rfl
  have hV : (Forward.freeze s (k + 1) v).vertices = s.vertices := rfl
  unfold PlaneCompatible
  rw [ha, hc, hA, hV]
  constructor
  · intro H
    refine ⟨fun u hu => ⟨(H u hu).1, (H u hu).2.1, fun hua => (H u hu).2.2
      (fun h' => hua (Finset.mem_of_mem_erase h'))⟩, ?_⟩
    exact (H v (h.active_subset hv)).2.2 (Finset.notMem_erase v _)
  · rintro ⟨H, heq⟩ u hu
    refine ⟨(H u hu).1, (H u hu).2.1, fun hua => ?_⟩
    by_cases huv : u = v
    · subst huv; exact heq
    · exact (H u hu).2.2 (fun h' => hua (Finset.mem_erase.mpr ⟨huv, h'⟩))

/-! ### One random step -/

theorem transitionLaw_planeCompatible_add {t : Finset (List ℕ)} (ht : IsPlaneTree t) {k : ℕ}
    {s : Forward.State} (h : Forward.ValidAt k s) (hne : s.active.Nonempty) :
    Forward.transitionLaw s (k + 1) true {s' | PlaneCompatible t s'} +
        Forward.transitionLaw s (k + 1) false {s' | PlaneCompatible t s'} =
      {s' | PlaneCompatible t s'}.indicator 1 s := by
  classical
  rw [Forward.transitionLaw_apply s _ _ hne, Forward.transitionLaw_apply s _ _ hne,
    ENNReal.div_add_div_same]
  by_cases hc : PlaneCompatible t s
  · rw [Set.indicator_of_mem (show s ∈ {s' | PlaneCompatible t s'} from hc), Pi.one_apply]
    have h1 : s.active.filter
        (fun v => Forward.step s (k + 1) true v ∈ {s' | PlaneCompatible t s'}) =
        s.active.filter (fun v => childCount s v < childNum t (birthAddress s v)) := by
      apply Finset.filter_congr
      intro v hv
      simp only [Forward.step, hv, ↓reduceIte, Set.mem_ofPred_eq]
      rw [planeCompatible_attach_iff ht h hv]
      exact and_iff_right hc
    have h2 : s.active.filter
        (fun v => Forward.step s (k + 1) false v ∈ {s' | PlaneCompatible t s'}) =
        s.active.filter (fun v => ¬ childCount s v < childNum t (birthAddress s v)) := by
      apply Finset.filter_congr
      intro v hv
      simp only [Forward.step, hv, ↓reduceIte, Bool.false_eq_true, Set.mem_ofPred_eq]
      rw [planeCompatible_freeze_iff h hv]
      have := (hc v (h.active_subset hv)).2.1
      constructor
      · rintro ⟨-, he⟩; omega
      · intro hn; exact ⟨hc, by omega⟩
    rw [h1, h2, ← Nat.cast_add, Finset.card_filter_add_card_filter_not]
    exact ENNReal.div_self (by exact_mod_cast hne.card_pos.ne') (by simp)
  · rw [Set.indicator_of_notMem (show s ∉ {s' | PlaneCompatible t s'} from hc)]
    have h1 : s.active.filter
        (fun v => Forward.step s (k + 1) true v ∈ {s' | PlaneCompatible t s'}) =
        ∅ := by
      apply Finset.filter_false_of_mem
      intro v hv
      simp only [Forward.step, hv, ↓reduceIte, Set.mem_ofPred_eq]
      rw [planeCompatible_attach_iff ht h hv]
      exact fun h' => hc h'.1
    have h2 : s.active.filter
        (fun v => Forward.step s (k + 1) false v ∈ {s' | PlaneCompatible t s'}) =
        ∅ := by
      apply Finset.filter_false_of_mem
      intro v hv
      simp only [Forward.step, hv, ↓reduceIte, Bool.false_eq_true, Set.mem_ofPred_eq]
      rw [planeCompatible_freeze_iff h hv]
      exact fun h' => hc h'.1
    rw [h1, h2]
    simp

/-! ### Counting along the random run -/

/-- The walk `S` is positive at every time before `m`. -/
def PositiveBefore (x : SignSequence) (m : ℕ) : Prop := ∀ l < m, 0 < activeCount x l

/-- Invariant of the forward run at time `m`. Before extinction, the active vertices are
counted by the walk and `2 #V = m + 1 + #A`. After extinction nothing is active and
`2 #V ≤ m`. -/
def RunInvariant (x : SignSequence) (m : ℕ) (s : Forward.State) : Prop :=
  Forward.ValidAt m s ∧
    (PositiveBefore x m → (s.active.card : ℤ) = activeCount x m ∧
      2 * s.vertices.card = m + 1 + s.active.card) ∧
    (¬ PositiveBefore x m → s.active = ∅ ∧ 2 * s.vertices.card ≤ m)

theorem treeLaw_runInvariant (x : SignSequence) (m : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw x m, RunInvariant x m s := by
  apply Forward.treeLaw_ae_induction x (RunInvariant x)
  · refine ⟨Forward.initial_valid, fun _ => ?_, fun hp => absurd (fun l hl => by omega) hp⟩
    simp [Forward.initial]
  · intro m s hs hA
    refine ⟨hs.1.mono (Nat.le_succ m), fun hp => ?_, fun _ => ⟨hA, ?_⟩⟩
    · exfalso
      have hpm : PositiveBefore x m := fun l hl => hp l (by omega)
      have h1 := (hs.2.1 hpm).1
      have h2 := hp m (by omega)
      rw [hA, Finset.card_empty] at h1
      omega
    · by_cases hpm : PositiveBefore x m
      · have := (hs.2.1 hpm).2
        rw [hA, Finset.card_empty] at this
        omega
      · have := (hs.2.2 hpm).2
        omega
  · intro m s hs v hv
    have hpm : PositiveBefore x m := by
      by_contra hpm
      rw [(hs.2.2 hpm).1] at hv
      exact Finset.notMem_empty v hv
    obtain ⟨hcard, hV⟩ := hs.2.1 hpm
    have hpos : 0 < (s.active.card : ℤ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨v, hv⟩
    have hpm1 : PositiveBefore x (m + 1) := by
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact hpm l hl
      · omega
    have hfresh := succ_notMem_vertices hs.1
    have hafresh : m + 1 ∉ s.active := fun h' => hfresh (hs.1.active_subset h')
    refine ⟨hs.1.step _ _, fun _ => ?_, fun h' => absurd hpm1 h'⟩
    rw [Forward.step, ite_eq_left hv, activeCount_succ]
    cases hx : x (m + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte, Forward.freeze]
      rw [Finset.card_erase_of_mem hv]
      have hc1 : 1 ≤ s.active.card := Finset.card_pos.mpr ⟨v, hv⟩
      constructor
      · rw [Nat.cast_sub hc1, Nat.cast_one, hcard]
        ring
      · omega
    · simp only [↓reduceIte, Forward.attach]
      rw [Finset.card_insert_of_notMem hafresh, Finset.card_insert_of_notMem hfresh]
      constructor
      · push_cast
        rw [hcard]
      · omega

/-- If `s` is compatible with `t` and nothing is active, then `s` already has all of `t`. -/
theorem subset_planeTreeOf_of_compatible {t : Finset (List ℕ)} (ht : IsPlaneTree t) {k : ℕ}
    {s : Forward.State} (h : Forward.ValidAt k s) (hc : PlaneCompatible t s) (hA : s.active = ∅) :
    t ⊆ planeTreeOf s := by
  intro a ha
  induction a using List.reverseRecOn with
  | nil => exact birthAddress_zero s ▸ birthAddress_mem_planeTreeOf h.root_mem
  | append_singleton b i ih =>
    obtain ⟨v, hv, hvb⟩ := Finset.mem_image.mp (ih (ht.parent_mem b i ha))
    rw [← hvb, append_mem_planeTreeOf_iff h hv]
    have := (ht.append_mem_iff _ _).mp ha
    rw [← hvb, ← (hc v hv).2.2 (by rw [hA]; exact Finset.notMem_empty v)] at this
    exact this

theorem planeTreeOf_subset_of_compatible {t : Finset (List ℕ)} {s : Forward.State}
    (hc : PlaneCompatible t s) : planeTreeOf s ⊆ t := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  exact (hc v hv).1

/-- A state compatible with a tree with `n + 1` vertices still has an active vertex before
time `2n + 1`. -/
theorem active_nonempty_of_compatible {x : SignSequence} {t : Finset (List ℕ)}
    (ht : IsPlaneTree t) {n m : ℕ} (htc : t.card = n + 1) {s : Forward.State}
    (hs : RunInvariant x m s) (hc : PlaneCompatible t s) (hm : m < 2 * n + 1) :
    s.active.Nonempty := by
  by_contra hA
  rw [Finset.not_nonempty_iff_eq_empty] at hA
  have hle := Finset.card_le_card (subset_planeTreeOf_of_compatible ht hs.1 hc hA)
  rw [card_planeTreeOf_of_valid hs.1, htc] at hle
  by_cases hp : PositiveBefore x m
  · have := (hs.2.1 hp).2
    rw [hA, Finset.card_empty] at this
    omega
  · have := (hs.2.2 hp).2
    omega

/-- At time `2n + 1`, compatibility with a tree with `n + 1` vertices means equality. -/
theorem planeCompatible_iff_planeTreeOf_eq {x : SignSequence} {t : Finset (List ℕ)}
    (ht : IsPlaneTree t) {n : ℕ} (htc : t.card = n + 1) {s : Forward.State}
    (hs : RunInvariant x (2 * n + 1) s) : PlaneCompatible t s ↔ planeTreeOf s = t := by
  constructor
  · intro hc
    have hsub := planeTreeOf_subset_of_compatible hc
    have hle := Finset.card_le_card hsub
    rw [card_planeTreeOf_of_valid hs.1, htc] at hle
    have hA : s.active = ∅ := by
      by_cases hp : PositiveBefore x (2 * n + 1)
      · have := (hs.2.1 hp).2
        exact Finset.card_eq_zero.mp (by omega)
      · exact (hs.2.2 hp).1
    exact Finset.Subset.antisymm hsub (subset_planeTreeOf_of_compatible ht hs.1 hc hA)
  · rintro rfl v hv
    have := childNum_planeTreeOf hs.1 hv
    exact ⟨birthAddress_mem_planeTreeOf hv, this.ge, fun _ => this.symm⟩

/-! ### Finite sign sequences -/

/-- The sign sequence whose step `i`, for `1 ≤ i ≤ m`, is `w (i - 1)`; later steps are `-1`
and index `0` is unused. -/
def finSigns {m : ℕ} (w : Fin m → Bool) : SignSequence :=
  fun i => if h : i ≠ 0 ∧ i ≤ m then w ⟨i - 1, by omega⟩ else false

theorem finSigns_succ {m : ℕ} (w : Fin m → Bool) {l : ℕ} (hl : l < m) :
    finSigns w (l + 1) = w ⟨l, hl⟩ := by
  rw [finSigns, dite_eq_left ⟨Nat.add_one_ne_zero l, hl⟩]
  rfl

theorem activeCount_finSigns {m : ℕ} (w : Fin m → Bool) {l : ℕ} (hl : l ≤ m) :
    activeCount (finSigns w) l = Audit.excursionWalk w l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [activeCount_succ, ih (by omega), Audit.excursionWalk_succ w l (by omega),
      finSigns_succ w (by omega)]
    rfl

theorem finSigns_snoc {m : ℕ} (w : Fin m → Bool) (b : Bool) {i : ℕ} (hi : i ≤ m) :
    finSigns (Fin.snoc w b : Fin (m + 1) → Bool) i = finSigns w i := by
  unfold finSigns
  by_cases h0 : i = 0
  · simp [h0]
  · rw [dite_eq_left ⟨h0, by omega⟩, dite_eq_left ⟨h0, hi⟩]
    simp [Fin.snoc, show i - 1 < m by omega]

theorem finSigns_snoc_last {m : ℕ} (w : Fin m → Bool) (b : Bool) :
    finSigns (Fin.snoc w b : Fin (m + 1) → Bool) (m + 1) = b := by
  rw [finSigns_succ _ (Nat.lt_succ_self m)]
  simp [Fin.snoc]

theorem treeLaw_congr_signs {x y : SignSequence} {m : ℕ}
    (hxy : ∀ i, i ≠ 0 → i ≤ m → x i = y i) :
    Forward.treeLaw x m = Forward.treeLaw y m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Forward.treeLaw]
    rw [ih (fun i hi him => hxy i hi (by omega)), hxy (m + 1) (by omega) le_rfl]

/-! ### Summing over all sign sequences -/

theorem planeCompatible_initial {t : Finset (List ℕ)} (ht : IsPlaneTree t) :
    PlaneCompatible t Forward.initial := by
  intro v hv
  have hv0 : v = 0 := by simpa [Forward.initial] using hv
  subst hv0
  have hc : childCount Forward.initial 0 = 0 := by
    simp [childCount, childSet, Forward.initial]
  refine ⟨birthAddress_zero _ ▸ ht.nil_mem, by omega, fun h => absurd ?_ h⟩
  simp [Forward.initial]

/-- The two possible signs of the next step, summed: the indicator of compatibility is
preserved before time `2n + 1`. -/
theorem transitionLaw_planeCompatible_add_of_runInvariant {x : SignSequence}
    {t : Finset (List ℕ)} (ht : IsPlaneTree t) {n m : ℕ} (htc : t.card = n + 1)
    (hm : m < 2 * n + 1) {s : Forward.State} (hs : RunInvariant x m s) :
    Forward.transitionLaw s (m + 1) true {s' | PlaneCompatible t s'} +
        Forward.transitionLaw s (m + 1) false {s' | PlaneCompatible t s'} =
      {s' | PlaneCompatible t s'}.indicator 1 s := by
  by_cases hne : s.active.Nonempty
  · exact transitionLaw_planeCompatible_add ht hs.1 hne
  · have hA : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hc : s ∉ {s' | PlaneCompatible t s'} :=
      fun hc => hne (active_nonempty_of_compatible ht htc hs hc hm)
    rw [Forward.transitionLaw_eq_dirac_of_empty s _ _ hA,
      Forward.transitionLaw_eq_dirac_of_empty s _ _ hA,
      Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top), Set.indicator_of_notMem hc]
    simp

/-- **Key identity.** For a plane tree `t` with `n + 1` vertices and every `m ≤ 2n + 1`,
summing over all `2^m` sign sequences of length `m` the probability that the forward
tree at time `m` is compatible with `t` gives `1`. -/
theorem sum_treeLaw_compatible {t : Finset (List ℕ)} (ht : IsPlaneTree t) {n : ℕ}
    (htc : t.card = n + 1) :
    ∀ m ≤ 2 * n + 1,
      ∑ w : Fin m → Bool, Forward.treeLaw (finSigns w) m {s | PlaneCompatible t s} = 1 := by
  intro m hm
  induction m with
  | zero =>
    rw [Fintype.sum_unique]
    change Measure.dirac Forward.initial {s | PlaneCompatible t s} = 1
    exact Measure.dirac_apply_of_mem (planeCompatible_initial ht)
  | succ m ih =>
    rw [← ih (by omega), ← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_bool]
    have hstep (b : Bool) :
        Forward.treeLaw (finSigns ((Fin.snocEquiv fun _ => Bool) (b, w))) (m + 1)
            {s | PlaneCompatible t s} =
          ∫⁻ s, Forward.transitionLaw s (m + 1) b {s' | PlaneCompatible t s'}
            ∂Forward.treeLaw (finSigns w) m := by
      change Forward.treeLaw (finSigns (Fin.snoc w b : Fin (m + 1) → Bool)) (m + 1) _ = _
      simp only [Forward.treeLaw]
      rw [Measure.bind_apply (MeasurableSpace.measurableSet_top)
        measurable_from_top.aemeasurable, finSigns_snoc_last,
        treeLaw_congr_signs (fun i _ hi => finSigns_snoc w b hi)]
    rw [hstep, hstep, ← lintegral_add_left measurable_from_top,
      ← lintegral_indicator_one (MeasurableSpace.measurableSet_top)]
    apply lintegral_congr_ae
    filter_upwards [treeLaw_runInvariant (finSigns w) m] with s hs
    exact transitionLaw_planeCompatible_add_of_runInvariant ht htc (by omega) hs

/-! ### Restriction to excursions -/

/-- If the forward tree at time `2n + 1` has `n + 1` vertices, the signs form an excursion. -/
theorem mem_excursionPaths_of_card {n : ℕ} {w : Fin (2 * n + 1) → Bool} {s : Forward.State}
    (hs : RunInvariant (finSigns w) (2 * n + 1) s) (hcard : (planeTreeOf s).card = n + 1) :
    w ∈ Audit.excursionPaths n := by
  rw [card_planeTreeOf_of_valid hs.1] at hcard
  have hp : PositiveBefore (finSigns w) (2 * n + 1) := by
    by_contra hp
    have := (hs.2.2 hp).2
    omega
  obtain ⟨h1, h2⟩ := hs.2.1 hp
  refine Audit.mem_excursionPaths.mpr ⟨fun i hi => ?_, ?_⟩
  · rw [← activeCount_finSigns w (by omega)]
    have := hp i (by omega)
    omega
  · rw [← activeCount_finSigns w le_rfl, ← h1]
    omega

/-- On an excursion, the forward tree at time `2n + 1` is a plane tree with `n + 1`
vertices. -/
theorem planeTreeOf_mem_planeTrees {n : ℕ} {w : Fin (2 * n + 1) → Bool}
    (hw : w ∈ Audit.excursionPaths n) {s : Forward.State}
    (hs : RunInvariant (finSigns w) (2 * n + 1) s) : planeTreeOf s ∈ planeTrees (n + 1) := by
  have hw' := Audit.mem_excursionPaths.mp hw
  have hp : PositiveBefore (finSigns w) (2 * n + 1) := by
    intro l hl
    rw [activeCount_finSigns w (by omega)]
    have := hw'.1 l (by omega)
    omega
  obtain ⟨h1, h2⟩ := hs.2.1 hp
  rw [activeCount_finSigns w le_rfl, hw'.2] at h1
  refine mem_planeTrees.mpr ⟨isPlaneTree_planeTreeOf hs.1, ?_⟩
  rw [card_planeTreeOf_of_valid hs.1]
  omega

theorem treeLaw_planeCompatible_eq {t : Finset (List ℕ)} (ht : IsPlaneTree t) {n : ℕ}
    (htc : t.card = n + 1) (w : Fin (2 * n + 1) → Bool) :
    Forward.treeLaw (finSigns w) (2 * n + 1) {s | PlaneCompatible t s} =
      Forward.treeLaw (finSigns w) (2 * n + 1) {s | planeTreeOf s = t} := by
  apply measure_congr
  filter_upwards [treeLaw_runInvariant (finSigns w) (2 * n + 1)] with s hs
  exact propext (planeCompatible_iff_planeTreeOf_eq ht htc hs)

theorem treeLaw_planeTreeOf_eq_of_notMem {t : Finset (List ℕ)} {n : ℕ}
    (htc : t.card = n + 1) {w : Fin (2 * n + 1) → Bool} (hw : w ∉ Audit.excursionPaths n) :
    Forward.treeLaw (finSigns w) (2 * n + 1) {s | planeTreeOf s = t} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [treeLaw_runInvariant (finSigns w) (2 * n + 1)] with s hs heq
  exact hw (mem_excursionPaths_of_card hs (by rw [heq, htc]))

/-- **Counting identity.** For every plane tree `t` with `n + 1` vertices, the
probabilities that the forward tree driven by an excursion `w` of length `2n + 1` equals
`t` sum to `1` over the `C_n` excursions. -/
theorem sum_excursionPaths_treeLaw_planeTreeOf_eq {n : ℕ} {t : Finset (List ℕ)}
    (ht : t ∈ planeTrees (n + 1)) :
    ∑ w ∈ Audit.excursionPaths n,
      Forward.treeLaw (finSigns w) (2 * n + 1) {s | planeTreeOf s = t} = 1 := by
  obtain ⟨ht, htc⟩ := mem_planeTrees.mp ht
  rw [← sum_treeLaw_compatible ht htc (2 * n + 1) le_rfl]
  simp_rw [treeLaw_planeCompatible_eq ht htc]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro w _ hw
  exact treeLaw_planeTreeOf_eq_of_notMem htc hw

/-! ### The annealed law -/

/-- The law of `𝒯_{2n+1}` when the signs are the increments of a simple random walk
started at `1` and conditioned to first hit `0` at time `2n + 1`: the forward tree law
mixed over `Audit.excursionLaw n` (see `Audit.excursionLaw_eq_cond`). -/
noncomputable def excursionTreeLaw (n : ℕ) : Measure Forward.State :=
  (Audit.excursionLaw n).bind fun w => Forward.treeLaw (finSigns w) (2 * n + 1)

theorem excursionTreeLaw_apply (n : ℕ) (A : Set Forward.State) :
    excursionTreeLaw n A =
      (catalan n : ℝ≥0∞)⁻¹ *
        ∑ w ∈ Audit.excursionPaths n, Forward.treeLaw (finSigns w) (2 * n + 1) A := by
  rw [excursionTreeLaw, Measure.bind_apply (MeasurableSpace.measurableSet_top)
    Measurable.of_discrete.aemeasurable, Audit.excursionLaw, Measure.uniformOfFinset,
    lintegral_finsetSum_measure, Finset.mul_sum, Audit.card_excursionPaths]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

instance excursionTreeLaw_probability (n : ℕ) : IsProbabilityMeasure (excursionTreeLaw n) :=
  isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (Filter.Eventually.of_forall fun _ => inferInstance)

/-- **U01 second clause / E02, pointwise form.** Under the excursion law, the plane tree
of `𝒯_{2n+1}` (children ordered by birth time) equals any given plane tree with `n + 1`
vertices with probability `1 / C_n`. -/
theorem excursionTreeLaw_planeTreeOf_eq {n : ℕ} {t : Finset (List ℕ)}
    (ht : t ∈ planeTrees (n + 1)) :
    excursionTreeLaw n {s | planeTreeOf s = t} = (catalan n : ℝ≥0∞)⁻¹ := by
  rw [excursionTreeLaw_apply, sum_excursionPaths_treeLaw_planeTreeOf_eq ht, mul_one]

/-- Almost surely, the plane tree of `𝒯_{2n+1}` has `n + 1` vertices. -/
theorem excursionTreeLaw_planeTreeOf_mem (n : ℕ) :
    excursionTreeLaw n {s | planeTreeOf s ∈ planeTrees (n + 1)} = 1 := by
  rw [excursionTreeLaw_apply]
  have hone : ∀ w ∈ Audit.excursionPaths n,
      Forward.treeLaw (finSigns w) (2 * n + 1) {s | planeTreeOf s ∈ planeTrees (n + 1)} = 1 := by
    intro w hw
    apply (ae_iff_prob_eq_one measurable_from_top).mp
    filter_upwards [treeLaw_runInvariant (finSigns w) (2 * n + 1)] with s hs
    exact planeTreeOf_mem_planeTrees hw hs
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Audit.card_excursionPaths, nsmul_eq_mul,
    mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (Audit.catalan_pos n).ne')
    (ENNReal.natCast_ne_top _)

/-- There are `C_n` plane trees with `n + 1` vertices. This is a consequence of the two
previous theorems. -/
theorem card_planeTrees (n : ℕ) : (planeTrees (n + 1)).card = catalan n := by
  have h := excursionTreeLaw_planeTreeOf_mem n
  rw [show {s | planeTreeOf s ∈ planeTrees (n + 1)} =
      planeTreeOf ⁻¹' ↑(planeTrees (n + 1)) from rfl,
    ← sum_measure_preimage_singleton _ (fun _ _ => MeasurableSpace.measurableSet_top)] at h
  have hsum : ∑ t ∈ planeTrees (n + 1), excursionTreeLaw n (planeTreeOf ⁻¹' {t}) =
      ∑ t ∈ planeTrees (n + 1), (catalan n : ℝ≥0∞)⁻¹ :=
    Finset.sum_congr rfl fun t ht => excursionTreeLaw_planeTreeOf_eq ht
  rw [hsum, Finset.sum_const, nsmul_eq_mul] at h
  have hc0 : (catalan n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Audit.catalan_pos n).ne'
  have hct : (catalan n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have : ((planeTrees (n + 1)).card : ℝ≥0∞) = catalan n := by
    rw [← ENNReal.div_eq_one_iff hc0 hct, div_eq_mul_inv]
    exact h
  exact_mod_cast this

/-- **U01 second clause / E02.** If the signs are the increments of a simple random walk
started at `1` and conditioned to first hit `0` at time `2n + 1`, then the plane tree of
`𝒯_{2n+1}`, with children ordered by birth time, is a uniform plane tree with `n + 1`
vertices. -/
theorem map_planeTreeOf_excursionTreeLaw (n : ℕ) :
    (excursionTreeLaw n).map planeTreeOf = Measure.uniformOfFinset (planeTrees (n + 1)) := by
  rw [Measure.ext_iff_singleton]
  intro t
  rw [Measure.map_apply measurable_from_top (measurableSet_singleton t),
    Measure.uniformOfFinset_apply_singleton]
  split_ifs with ht
  · rw [card_planeTrees]
    exact excursionTreeLaw_planeTreeOf_eq ht
  · apply measure_mono_null (t := {s | planeTreeOf s ∈ planeTrees (n + 1)}ᶜ)
    · intro s hs hs'
      exact ht ((show planeTreeOf s = t from hs) ▸ hs')
    · rw [prob_compl_eq_zero_iff (MeasurableSpace.measurableSet_top)]
      exact excursionTreeLaw_planeTreeOf_mem n

/-! ### The plane tree of `𝒯` is `𝒯` itself, as a rooted graph -/

/-- The graph of a set of words: a word is adjacent to the words obtained by appending one
letter, and to the word obtained by deleting its last letter. -/
def planeGraph (t : Finset (List ℕ)) : SimpleGraph {a // a ∈ t} :=
  SimpleGraph.fromRel fun a b => ∃ i, b.1 = a.1 ++ [i]

/-- In `s`, the edges are exactly the edges between a vertex and its parent. -/
def ParentEdges (s : Forward.State) : Prop :=
  ∀ a b, s.graph.Adj a b ↔ (b ∈ s.vertices ∧ b ≠ 0 ∧ s.parent b = a) ∨
    (a ∈ s.vertices ∧ a ≠ 0 ∧ s.parent a = b)

theorem parentRel_attach_iff {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) (v a b : ℕ) :
    (b ∈ (Forward.attach s (k + 1) v).vertices ∧ b ≠ 0 ∧
        (Forward.attach s (k + 1) v).parent b = a) ↔
      (b ∈ s.vertices ∧ b ≠ 0 ∧ s.parent b = a) ∨ (b = k + 1 ∧ a = v) := by
  have hfresh := succ_notMem_vertices h
  simp only [Forward.attach, Finset.mem_insert]
  by_cases hb : b = k + 1
  · subst hb
    simp only [true_or, ne_eq, Nat.add_one_ne_zero, not_false_eq_true, Function.update_self,
      true_and, hfresh, false_and, false_or]
    exact eq_comm
  · simp only [hb, false_or, ne_eq, Function.update_of_ne hb, false_and, or_false]

theorem treeLaw_parentEdges (x : SignSequence) (m : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw x m, Forward.ValidAt m s ∧ ParentEdges s := by
  apply Forward.treeLaw_ae_induction x (fun m s => Forward.ValidAt m s ∧ ParentEdges s)
  · refine ⟨Forward.initial_valid, fun a b => ?_⟩
    simp only [Forward.initial, SimpleGraph.bot_adj, Finset.mem_singleton, false_iff]
    omega
  · intro m s hs _
    exact ⟨hs.1.mono (Nat.le_succ m), hs.2⟩
  · intro m s hs v hv
    refine ⟨hs.1.step _ _, ?_⟩
    rw [Forward.step, ite_eq_left hv]
    cases x (m + 1)
    · exact hs.2
    · simp only [↓reduceIte]
      intro a b
      have hvk : v ≠ m + 1 := fun he => succ_notMem_vertices hs.1 (he ▸ hs.1.active_subset hv)
      rw [parentRel_attach_iff hs.1, parentRel_attach_iff hs.1]
      change s.graph.Adj a b ∨ (SimpleGraph.edge v (m + 1)).Adj a b ↔ _
      rw [hs.2 a b, SimpleGraph.edge_adj]
      constructor
      · rintro (h | ⟨h | h, -⟩)
        · tauto
        · exact Or.inl (Or.inr ⟨h.2, h.1⟩)
        · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
      · rintro ((h | h) | (h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨Or.inl ⟨h.2, h.1⟩, by rw [h.1, h.2]; exact hvk⟩
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨Or.inr ⟨h.1, h.2⟩, by rw [h.1, h.2]; exact hvk.symm⟩

/-- `b` is a child of `a` in `s` iff its address is that of `a` plus one letter. -/
theorem exists_birthAddress_eq_append_iff {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    {a b : ℕ} (ha : a ∈ s.vertices) (hb : b ∈ s.vertices) :
    (∃ i, birthAddress s b = birthAddress s a ++ [i]) ↔ b ≠ 0 ∧ s.parent b = a := by
  constructor
  · rintro ⟨i, hi⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [birthAddress_zero] at hi
      simp at hi
    rw [birthAddress_eq_of_valid h hb hb0] at hi
    obtain ⟨hpa, -⟩ := List.append_inj hi (by
      have := congrArg List.length hi
      simpa using this)
    exact ⟨hb0, birthAddress_injOn_of_valid h (h.parent_mem b hb) ha hpa⟩
  · rintro ⟨hb0, rfl⟩
    exact ⟨birthRank s b, birthAddress_eq_of_valid h hb hb0⟩

/-- The address map, as a bijection from the vertices of `s` onto its plane tree. -/
noncomputable def birthAddressEquiv {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s) :
    {v // v ∈ s.vertices} ≃ {a // a ∈ planeTreeOf s} :=
  Equiv.ofBijective (fun v => ⟨birthAddress s v.1, birthAddress_mem_planeTreeOf v.2⟩)
    ⟨fun u v huv =>
      Subtype.ext (birthAddress_injOn_of_valid h u.2 v.2 (congrArg Subtype.val huv)),
      fun a => by
        obtain ⟨v, hv, hva⟩ := Finset.mem_image.mp a.2
        exact ⟨⟨v, hv⟩, Subtype.ext hva⟩⟩

/-- For a valid state whose edges are its parent edges, the address map is a graph
isomorphism from the tree `s.tree` onto the graph of its plane tree. -/
noncomputable def planeTreeIso {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    (hE : ParentEdges s) : s.tree ≃g planeGraph (planeTreeOf s) where
  toEquiv := birthAddressEquiv h
  map_rel_iff' {u v} := by
    change (planeGraph (planeTreeOf s)).Adj
        ⟨birthAddress s u.1, _⟩ ⟨birthAddress s v.1, _⟩ ↔
      s.graph.Adj u.1 v.1
    rw [planeGraph, SimpleGraph.fromRel_adj, hE, exists_birthAddress_eq_append_iff h u.2 v.2,
      exists_birthAddress_eq_append_iff h v.2 u.2]
    simp only [ne_eq, Subtype.mk.injEq, u.2, v.2, true_and]
    constructor
    · exact fun h' => h'.2
    · intro h'
      refine ⟨fun huv => ?_, h'⟩
      have huv' := birthAddress_injOn_of_valid h u.2 v.2 huv
      rcases h' with ⟨hv0, hp⟩ | ⟨hu0, hp⟩
      · have := h.parent_lt v.1 v.2 hv0
        omega
      · have := h.parent_lt u.1 u.2 hu0
        omega

theorem planeTreeIso_root {k : ℕ} {s : Forward.State} (h : Forward.ValidAt k s)
    (hE : ParentEdges s) : (planeTreeIso h hE ⟨0, h.root_mem⟩).1 = [] :=
  birthAddress_zero s

theorem dist_map_le_of_hom {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (f : G →g G')
    {u v : V} (huv : G.Reachable u v) : G'.dist (f u) (f v) ≤ G.dist u v := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  calc G'.dist (f u) (f v) ≤ (p.map f).length := SimpleGraph.dist_le _
    _ = G.dist u v := by rw [SimpleGraph.Walk.length_map, hp]

/-- Graph isomorphisms preserve the graph distance. -/
theorem dist_eq_of_iso {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G')
    (u v : V) : G'.dist (e u) (e v) = G.dist u v := by
  by_cases huv : G.Reachable u v
  · apply le_antisymm (dist_map_le_of_hom e.toHom huv)
    have := dist_map_le_of_hom e.symm.toHom (huv.map e.toHom)
    simpa using this
  · have h' : ¬ G'.Reachable (e u) (e v) := fun h' => huv (by simpa using h'.map e.symm.toHom)
    rw [SimpleGraph.dist_eq_zero_of_not_reachable huv,
      SimpleGraph.dist_eq_zero_of_not_reachable h']

/-- **Rooted isomorphism (pathwise).** Almost surely under the excursion law, `𝒯_{2n+1}` is
isomorphic, as a rooted graph, to the graph of its plane tree. In particular the
isomorphism preserves graph distances (`dist_eq_of_iso`). -/
theorem excursionTreeLaw_ae_iso (n : ℕ) :
    ∀ᵐ s ∂excursionTreeLaw n, ∃ (h : 0 ∈ s.vertices)
      (e : s.tree ≃g planeGraph (planeTreeOf s)),
      (e ⟨0, h⟩).1 = [] := by
  rw [ae_iff, excursionTreeLaw_apply]
  have hzero : ∀ w ∈ Audit.excursionPaths n, Forward.treeLaw (finSigns w) (2 * n + 1)
      {s | ¬ ∃ (h : 0 ∈ s.vertices) (e : s.tree ≃g planeGraph (planeTreeOf s)),
        (e ⟨0, h⟩).1 = []} = 0 := by
    intro w _
    rw [← ae_iff]
    filter_upwards [treeLaw_parentEdges (finSigns w) (2 * n + 1)] with s hs
    exact ⟨hs.1.root_mem, planeTreeIso hs.1 hs.2, planeTreeIso_root hs.1 hs.2⟩
  rw [Finset.sum_eq_zero hzero, mul_zero]

open scoped ProbabilityTheory in
/-- The conditioning is that of `Audit.excursionLaw_eq_cond`: `excursionTreeLaw n` is the
forward tree law mixed over simple random walk increments conditioned on first hitting `0`
at time `2n + 1`. -/
theorem excursionTreeLaw_eq_cond_bind (n : ℕ) :
    excursionTreeLaw n =
      ((Audit.srwLaw (2 * n + 1))[|(Audit.excursionPaths n : Set (Fin (2 * n + 1) → Bool))]).bind
        fun w => Forward.treeLaw (finSigns w) (2 * n + 1) := by
  rw [excursionTreeLaw, Audit.excursionLaw_eq_cond]

/-- **Isometry with the plane tree (pathwise).** Almost surely under the excursion law, the address map is
a bijection from the vertices of `𝒯_{2n+1}` onto the vertices of its plane tree that sends
the root to `[]` and preserves graph distances. -/
theorem excursionTreeLaw_ae_isometry (n : ℕ) :
    ∀ᵐ s ∂excursionTreeLaw n, ∃ (h : 0 ∈ s.vertices)
      (e : {v // v ∈ s.vertices} ≃ {a // a ∈ planeTreeOf s}), (e ⟨0, h⟩).1 = [] ∧
        ∀ u v, (planeGraph (planeTreeOf s)).dist (e u) (e v) = s.tree.dist u v := by
  filter_upwards [excursionTreeLaw_ae_iso n] with s hs
  obtain ⟨h, e, he⟩ := hs
  exact ⟨h, e.toEquiv, he, dist_eq_of_iso e⟩

/-! ### Unconditioned i.i.d. signs -/

/-- The forward tree law at time `m` when the signs are i.i.d. uniform on `{-1, +1}`:
`Forward.treeLaw` mixed over `Audit.srwLaw m`. -/
noncomputable def iidTreeLaw (m : ℕ) : Measure Forward.State :=
  (Audit.srwLaw m).bind fun w => Forward.treeLaw (finSigns w) m

theorem iidTreeLaw_apply (m : ℕ) (A : Set Forward.State) :
    iidTreeLaw m A =
      ((2 : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → Bool, Forward.treeLaw (finSigns w) m A := by
  rw [iidTreeLaw, Measure.bind_apply (MeasurableSpace.measurableSet_top)
    Measurable.of_discrete.aemeasurable, Audit.srwLaw, Measure.uniformOfFinset,
    lintegral_finsetSum_measure, Finset.mul_sum, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  push_cast
  rfl

/-- With i.i.d. uniform signs, each plane tree with `n + 1` vertices is the plane tree of
`𝒯_{2n+1}` with probability `2^{-(2n+1)}`. -/
theorem iidTreeLaw_planeTreeOf_eq {n : ℕ} {t : Finset (List ℕ)}
    (ht : t ∈ planeTrees (n + 1)) :
    iidTreeLaw (2 * n + 1) {s | planeTreeOf s = t} = ((2 : ℝ≥0∞) ^ (2 * n + 1))⁻¹ := by
  obtain ⟨ht, htc⟩ := mem_planeTrees.mp ht
  have hsum := sum_treeLaw_compatible ht htc (2 * n + 1) le_rfl
  simp_rw [treeLaw_planeCompatible_eq ht htc] at hsum
  rw [iidTreeLaw_apply, hsum, mul_one]

end Freezing2
