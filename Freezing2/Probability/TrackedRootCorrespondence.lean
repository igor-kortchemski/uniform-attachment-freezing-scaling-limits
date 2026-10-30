module

public import Freezing2.Probability.TrackedClusterCount
public import Freezing2.Probability.UniformTransport

/-!
# Root correspondences for tracked-label symmetry

Two forests need not have isomorphic untracked trees for their tracked
partitions to evolve symmetrically. A permutation of their current roots,
matching tracked membership under a marked-label permutation, is enough.
The same root permutation is preserved by paired joins and by insertions of
labels fixed by both permutations. No exchangeability across birth times is
assumed.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace Freezing2.TrackedClusters

open Freezing1

variable {V : Type*} [DecidableEq V]

/-- A marked vertex is alone if no different present marked vertex shares
its component. An unborn marked vertex counts as alone, as in the source. -/
def Alone (F : RootedForest V) (A : Finset V) (v : V) : Prop :=
  ∀ w ∈ A, v ∈ F.vertices → w ∈ F.vertices → F.root v = F.root w → w = v

/-- A root permutation matches the tracked partition under a label
permutation. It imposes no correspondence of the untracked graph shapes. -/
structure RootCorrespondence (A : Finset V) (σ e : Equiv.Perm V)
    (F G : RootedForest V) : Prop where
  vertices : F.vertices.image σ = G.vertices
  roots : F.roots.image e = G.roots
  tracked : ∀ v ∈ A, v ∈ F.vertices → G.root (σ v) = e (F.root v)

theorem RootCorrespondence.mem_vertices_iff {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) (v : V) :
    σ v ∈ G.vertices ↔ v ∈ F.vertices := by
  rw [← h.vertices, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, he⟩
    exact σ.injective he ▸ hw
  · exact fun hv ↦ ⟨v, hv, rfl⟩

theorem RootCorrespondence.mem_roots_iff {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) (r : V) :
    e r ∈ G.roots ↔ r ∈ F.roots := by
  rw [← h.roots, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, he⟩
    exact e.injective he ▸ hw
  · exact fun hr ↦ ⟨r, hr, rfl⟩

theorem RootCorrespondence.card_roots {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) :
    F.roots.card = G.roots.card := by
  rw [← h.roots, Finset.card_image_of_injective _ e.injective]

/-- Supported ordered choices correspond bijectively under the root permutation. -/
theorem RootCorrespondence.pair_mem_iff {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) (p : V × V) :
    (e p.1, e p.2) ∈ G.roots.offDiag ↔ p ∈ F.roots.offDiag := by
  simp only [Finset.mem_offDiag, h.mem_roots_iff, e.injective.ne_iff]

/-- Joining paired roots preserves the tracked correspondence and removes
corresponding second roots from the two root sets. -/
theorem RootCorrespondence.joinChoice {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G)
    {p : V × V} (hp : p ∈ F.roots.offDiag) :
    RootCorrespondence A σ e (F.joinChoice p) (G.joinChoice (e p.1, e p.2)) := by
  have hq := (h.pair_mem_iff p).mpr hp
  simp only [RootedForest.joinChoice, dite_eq_left hp, dite_eq_left hq]
  constructor
  · exact h.vertices
  · rw [RootedForest.join_roots, RootedForest.join_roots,
      Finset.image_erase e.injective, h.roots]
  · intro v hv hvF
    have hr := h.tracked v hv hvF
    change (if G.root (σ v) = e p.2 then e p.1 else G.root (σ v)) =
      e (if F.root v = p.2 then p.1 else F.root v)
    rw [hr]
    by_cases he : F.root v = p.2
    · simp only [he, ite_true]
    · have he' : e (F.root v) ≠ e p.2 := e.injective.ne he
      simp only [ite_eq_right he, ite_eq_right he']

/-- The same fresh insertion preserves the correspondence when its label is
fixed by both permutations. This is the future-birth condition in the coupling. -/
theorem RootCorrespondence.adjoin {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) {w : V}
    (hwF : w ∉ F.vertices) (hwG : w ∉ G.vertices) (hσ : σ w = w) (he : e w = w) :
    RootCorrespondence A σ e (F.adjoin w hwF) (G.adjoin w hwG) := by
  constructor
  · rw [RootedForest.adjoin_vertices, RootedForest.adjoin_vertices,
      Finset.image_insert, hσ, h.vertices]
  · rw [RootedForest.adjoin_roots, RootedForest.adjoin_roots,
      Finset.image_insert, he, h.roots]
  · intro v hv hvF
    rcases Finset.mem_insert.mp hvF with rfl | hvF
    · simp [RootedForest.adjoin, hσ, he]
    · have hvw : v ≠ w := fun hvw ↦ hwF (hvw ▸ hvF)
      have hσv : σ v ≠ w := by
        rw [← hσ]
        exact σ.injective.ne hvw
      simp only [RootedForest.adjoin, ite_eq_right hvw, ite_eq_right hσv]
      exact h.tracked v hv hvF

/-- Totalized insertion also respects the correspondence, including a label
which is already present. -/
theorem RootCorrespondence.insertLabel {A : Finset (ℕ ⊕ ℕ)}
    {σ e : Equiv.Perm (ℕ ⊕ ℕ)} {F G : Reverse.Forest}
    (h : RootCorrespondence A σ e F G) (i : ℕ)
    (hσ : σ (.inr i) = .inr i) (he : e (.inr i) = .inr i) :
    RootCorrespondence A σ e (Reverse.insertLabel F i) (Reverse.insertLabel G i) := by
  have hm : Sum.inr i ∈ G.vertices ↔ Sum.inr i ∈ F.vertices := by
    simpa only [hσ] using h.mem_vertices_iff (.inr i)
  by_cases hi : Sum.inr i ∈ F.vertices
  · simpa only [Reverse.insertLabel, dite_eq_left hi, dite_eq_left (hm.mpr hi)] using h
  · simpa only [Reverse.insertLabel, dite_eq_right hi, dite_eq_right (mt hm.mp hi)] using
      h.adjoin hi (mt hm.mp hi) hσ he

/-- A correspondence transports isolation whenever the marked set is preserved. -/
theorem RootCorrespondence.alone_iff {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G)
    (hA : A.image σ = A) {v : V} (hv : v ∈ A) :
    Alone F A v ↔ Alone G A (σ v) := by
  have hmem (w : V) : σ w ∈ A ↔ w ∈ A := by
    conv_lhs => rw [← hA]
    rw [Finset.mem_image]
    constructor
    · rintro ⟨z, hz, heq⟩
      exact σ.injective heq ▸ hz
    · exact fun hw ↦ ⟨w, hw, rfl⟩
  constructor
  · intro hAl z hz hvG hzG hroot
    let w := σ.symm z
    have hw : w ∈ A := (hmem w).mp (by simpa only [w, σ.apply_symm_apply] using hz)
    have hwF : w ∈ F.vertices := (h.mem_vertices_iff w).mp (by
      simpa only [w, σ.apply_symm_apply] using hzG)
    have hvF := (h.mem_vertices_iff v).mp hvG
    have hrw := h.tracked w hw hwF
    have hrv := h.tracked v hv hvF
    have hroot' : F.root v = F.root w := e.injective (by
      rw [← hrv, ← hrw]
      simpa only [w, σ.apply_symm_apply] using hroot)
    have heq := hAl w hw hvF hwF hroot'
    have := congrArg σ heq
    simpa only [w, σ.apply_symm_apply] using this
  · intro hAl w hw hvF hwF hroot
    apply σ.injective
    exact hAl (σ w) ((hmem w).mpr hw) ((h.mem_vertices_iff v).mpr hvF)
      ((h.mem_vertices_iff w).mpr hwF) (by rw [h.tracked v hv hvF, h.tracked w hw hwF, hroot])

/-- Swapping two elements already in a finite set preserves that set. -/
theorem image_swap_eq_of_mem (s : Finset V) {u v : V} (hu : u ∈ s) (hv : v ∈ s) :
    s.image (Equiv.swap u v) = s := by
  have hmap (w : V) (hw : w ∈ s) : Equiv.swap u v w ∈ s := by
    by_cases hwu : w = u
    · subst w; simpa using hv
    by_cases hwv : w = v
    · subst w; simpa using hu
    simpa only [Equiv.swap_apply_of_ne_of_ne hwu hwv] using hw
  ext w
  constructor
  · rintro hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hmap z hz
  · intro hw
    exact Finset.mem_image.mpr ⟨Equiv.swap u v w, hmap w hw, Equiv.swap_apply_self _ _ _⟩

/-- Two currently isolated marked vertices can be interchanged at the level
of component roots, even if their untracked trees have different shapes. -/
theorem rootCorrespondence_swap_of_alone (F : RootedForest V) {A : Finset V}
    {u v : V} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huAl : Alone F A u) (hvAl : Alone F A v) :
    RootCorrespondence A (Equiv.swap u v) (Equiv.swap (F.root u) (F.root v)) F F := by
  constructor
  · exact image_swap_eq_of_mem F.vertices hu hv
  · exact image_swap_eq_of_mem F.roots (F.root_mem_roots hu) (F.root_mem_roots hv)
  · intro w hw hwF
    by_cases hwu : w = u
    · subst w
      simp
    by_cases hwv : w = v
    · subst w
      simp
    have hru : F.root w ≠ F.root u := fun he ↦ hwu (huAl w hw hu hwF he.symm)
    have hrv : F.root w ≠ F.root v := fun he ↦ hwv (hvAl w hw hv hwF he.symm)
    rw [Equiv.swap_apply_of_ne_of_ne hwu hwv, Equiv.swap_apply_of_ne_of_ne hru hrv]

variable [Countable V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The concrete ordered-pair law transports exactly under the root
permutation, including the zero measure on empty pair supports. -/
theorem RootCorrespondence.map_uniformRootPair {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G) :
    (uniformRootPair F.roots).map (fun p ↦ (e p.1, e p.2)) = uniformRootPair G.roots := by
  have hinj : Function.Injective (fun p : V × V ↦ (e p.1, e p.2)) := by
    intro p q heq
    exact Prod.ext (e.injective (congrArg Prod.fst heq)) (e.injective (congrArg Prod.snd heq))
  have himage : F.roots.offDiag.image (fun p ↦ (e p.1, e p.2)) = G.roots.offDiag := by
    ext q
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact (h.pair_mem_iff p).mpr hp
    · intro hq
      refine Finset.mem_image.mpr ⟨(e.symm q.1, e.symm q.2), ?_, by simp⟩
      apply (h.pair_mem_iff _).mp
      simpa only [e.apply_symm_apply] using hq
  rw [uniformRootPair, map_uniformOfFinset_of_injOn _ _
    (measurable_of_countable _) hinj.injOn, himage]
  rfl

/-- Every corresponding pair of observables has equal one-step join
expectations. This is an actual kernel identity, not an exchangeability axiom. -/
theorem RootCorrespondence.integral_joinLaw_eq {A : Finset V} {σ e : Equiv.Perm V}
    {F G : RootedForest V} (h : RootCorrespondence A σ e F G)
    (φ ψ : RootedForest V → ℝ)
    (hobs : ∀ F' G', RootCorrespondence A σ e F' G' → φ F' = ψ G') :
    (∫ F', φ F' ∂F.joinLaw) = ∫ G', ψ G' ∂G.joinLaw := by
  by_cases hF : 2 ≤ F.roots.card
  · have hG : 2 ≤ G.roots.card := by rwa [← h.card_roots]
    simp only [RootedForest.joinLaw, ite_eq_left hF, ite_eq_left hG]
    rw [integral_map (measurable_of_countable _).aemeasurable
        measurable_from_top.aestronglyMeasurable,
      integral_map (measurable_of_countable _).aemeasurable
        measurable_from_top.aestronglyMeasurable]
    rw [← h.map_uniformRootPair,
      integral_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable]
    apply integral_congr_ae
    have hs : ∀ᵐ p ∂uniformRootPair F.roots, p ∈ F.roots.offDiag := by
      rw [ae_iff, uniformRootPair, Measure.uniformOfFinset_apply]
      simp
      aesop
    filter_upwards [hs] with p hp
    exact hobs _ _ (h.joinChoice hp)
  · have hG : ¬2 ≤ G.roots.card := by rwa [← h.card_roots]
    simp only [RootedForest.joinLaw, ite_eq_right hF, ite_eq_right hG, integral_dirac]
    exact hobs F G h

/-- The actual sign-dependent transition preserves expectations of matched
tracked observables, when a possible birth label is fixed by the permutations. -/
theorem RootCorrespondence.integral_transitionLaw_eq {A : Finset (ℕ ⊕ ℕ)}
    {σ e : Equiv.Perm (ℕ ⊕ ℕ)} {F G : Reverse.Forest}
    (h : RootCorrespondence A σ e F G) (x : SignSequence) (i : ℕ)
    (hσ : σ (.inr i) = .inr i) (he : e (.inr i) = .inr i)
    (φ ψ : Reverse.Forest → ℝ)
    (hobs : ∀ F' G', RootCorrespondence A σ e F' G' → φ F' = ψ G') :
    (∫ F', φ F' ∂Reverse.transitionLaw x i F) =
      ∫ G', ψ G' ∂Reverse.transitionLaw x i G := by
  cases hx : x (i + 1)
  · simp only [Reverse.transitionLaw, hx, Bool.false_eq_true, ↓reduceIte, integral_dirac]
    exact hobs _ _ (h.insertLabel i hσ he)
  · simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    exact h.integral_joinLaw_eq φ ψ hobs

end Freezing2.TrackedClusters
