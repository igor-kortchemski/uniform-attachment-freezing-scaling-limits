module

public import Freezing2.Probability.TrackedGenealogy

/-!
# The tracked connectivity chain

The connectivity relation of finitely many tracked labels, with unborn labels
kept as singletons, is a finite-state Markov chain under the actual reverse
construction. Its one-step transition probabilities depend only on the current
relation: freezing steps leave it unchanged, and an attachment step keeps it
with probability `1 - C(a,2)/C(S,2)` and merges any prescribed pair of its `a`
components with probability `1/C(S,2)`.
-/

@[expose] public section

open MeasureTheory Set

namespace Freezing2.TrackedGenealogy

/-- The image of a map on a finite set has as many elements as there are
classes of the equality relation it induces. -/
theorem card_image_eq_card_classes {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (φ : α → δ) :
    (S.image φ).card = (S.image fun x ↦ S.filter fun y ↦ φ x = φ y).card := by
  have himg : (S.image fun x ↦ S.filter fun y ↦ φ x = φ y) =
      (S.image φ).image fun b ↦ S.filter fun y ↦ φ y = b := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    ext y
    simp only [Finset.mem_filter, Function.comp_apply]
    exact ⟨fun ⟨hy, he⟩ ↦ ⟨hy, he.symm⟩, fun ⟨hy, he⟩ ↦ ⟨hy, he.symm⟩⟩
  rw [himg]
  refine (Finset.card_image_of_injOn ?_).symm
  intro b₁ hb₁ b₂ hb₂ hb
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hb₁
  obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hb₂
  have hmem : x₁ ∈ S.filter fun y ↦ φ y = φ x₁ := Finset.mem_filter.mpr ⟨hx₁, rfl⟩
  rw [show (S.filter fun y ↦ φ y = φ x₁) = S.filter fun y ↦ φ y = φ x₂ from hb] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- Two maps inducing the same equality on a finite set have images of the
same cardinality. -/
theorem card_image_eq_of_eq_iff {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (S : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (S.image f).card = (S.image g).card := by
  rw [card_image_eq_card_classes S f, card_image_eq_card_classes S g]
  congr 1
  apply Finset.image_congr
  intro x hx
  ext y
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hy, he⟩ ↦ ⟨hy, (h x hx y hy).mp he⟩, fun ⟨hy, he⟩ ↦ ⟨hy, (h x hx y hy).mpr he⟩⟩

open Freezing1 TrackedClusters ReverseHistory

variable {k : ℕ} {n p : ℕ} {u : Fin k → ℕ ⊕ ℕ}

/-- The tracked connectivity state: connectivity among born tracked labels,
with labels not yet born kept as singletons. -/
noncomputable def trackedState (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (F : Reverse.Forest) :
    Fin k → Fin k → Bool :=
  open Classical in fun j l ↦
    if Born n p u j ∧ Born n p u l then decide (F.root (u j) = F.root (u l)) else decide (j = l)

/-- The born tracked labels at phase `p`. -/
noncomputable def bornSet (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) : Finset (Fin k) :=
  open Classical in Finset.univ.filter fun j ↦ Born n p u j

/-- The number of components of the born labels in a state. -/
noncomputable def stateClasses (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (s : Fin k → Fin k → Bool) : ℕ :=
  open Classical in
  ((bornSet n p u).image fun j ↦ (bornSet n p u).filter fun l ↦ s j l = true).card

theorem card_trackedRoots_eq_stateClasses (F : Reverse.Forest) :
    (trackedRoots n p u F).card = stateClasses n p u (trackedState n p u F) := by
  classical
  have h := card_image_eq_card_classes (bornSet n p u) (fun j ↦ F.root (u j))
  simp only [trackedRoots, stateClasses, bornSet] at h ⊢
  rw [h]
  congr 1
  apply Finset.image_congr
  intro j hj
  ext l
  have hj' : Born n p u j := by simpa using hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hl, he⟩
    exact ⟨hl, by simp [trackedState, hj', hl, he]⟩
  · rintro ⟨hl, he⟩
    refine ⟨hl, ?_⟩
    simpa [trackedState, hj', hl] using he

/-- States respecting the singleton convention for unborn labels. -/
def StateRespects (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (s : Fin k → Fin k → Bool) : Prop :=
  ∀ j l, ¬ (Born n p u j ∧ Born n p u l) → s j l = decide (j = l)

theorem trackedState_respects (F : Reverse.Forest) :
    StateRespects n p u (trackedState n p u F) := by
  intro j l h
  classical
  simp [trackedState, h]

/-- A forest has a respecting state exactly when it is consistent with it. -/
theorem trackedState_eq_iff_consistent {F : Reverse.Forest} {s : Fin k → Fin k → Bool}
    (hs : StateRespects n p u s) :
    trackedState n p u F = s ↔
      Consistent n p u (fun j l ↦ s j l = true) (stateClasses n p u s) F := by
  classical
  constructor
  · rintro rfl
    refine ⟨fun j l hj hl ↦ ?_, card_trackedRoots_eq_stateClasses F⟩
    simp [trackedState, hj, hl]
  · intro hF
    funext j l
    by_cases h : Born n p u j ∧ Born n p u l
    · have := hF.1 j l h.1 h.2
      simp only [trackedState, h, and_self, ↓reduceIte]
      by_cases he : F.root (u j) = F.root (u l)
      · simp [he, this.mp he]
      · simp only [he, decide_false]
        exact ((Bool.not_eq_true _).mp fun hs' ↦ he (this.mpr hs')).symm
    · simp only [trackedState, h, ↓reduceIte]
      exact (hs j l h).symm

/-- Merging the components of `j₀` and `l₀`. -/
def mergeState (s : Fin k → Fin k → Bool) (j₀ l₀ : Fin k) : Fin k → Fin k → Bool :=
  fun j l ↦ s j l || (s j j₀ && s l l₀) || (s j l₀ && s l j₀)

/-- A state reachable from `s` by merging two distinct components of born labels. -/
def IsMerge (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (s s' : Fin k → Fin k → Bool) : Prop :=
  ∃ j₀ l₀, Born n p u j₀ ∧ Born n p u l₀ ∧ s j₀ l₀ = false ∧ s' = mergeState s j₀ l₀

theorem trackedState_eq_of_conn {F : Reverse.Forest} {s : Fin k → Fin k → Bool}
    (hs : StateRespects n p u s)
    (h : ∀ j l, Born n p u j → Born n p u l → (F.root (u j) = F.root (u l) ↔ s j l = true)) :
    trackedState n p u F = s := by
  classical
  funext j l
  by_cases hb : Born n p u j ∧ Born n p u l
  · have := h j l hb.1 hb.2
    simp only [trackedState, hb, and_self, ↓reduceIte]
    by_cases he : F.root (u j) = F.root (u l)
    · simp [he, this.mp he]
    · simp only [he, decide_false]
      exact ((Bool.not_eq_true _).mp fun hs' ↦ he (this.mpr hs')).symm
  · simp only [trackedState, hb, ↓reduceIte]
    exact (hs j l hb).symm

theorem conn_of_trackedState_eq {F : Reverse.Forest} {s : Fin k → Fin k → Bool}
    (h : trackedState n p u F = s) (j l : Fin k) (hj : Born n p u j) (hl : Born n p u l) :
    F.root (u j) = F.root (u l) ↔ s j l = true := by
  classical
  subst h
  simp [trackedState, hj, hl]

theorem consistent_trackedState (F : Reverse.Forest) :
    Consistent n p u (fun j l ↦ trackedState n p u F j l = true)
      (stateClasses n p u (trackedState n p u F)) F :=
  ⟨fun j l hj hl ↦ conn_of_trackedState_eq rfl j l hj hl, card_trackedRoots_eq_stateClasses F⟩

variable {x : SignSequence}

/-- A freezing step does not change the tracked state. -/
theorem trackedState_insertLabel (hp : p < n) (hinj : Function.Injective u) {F : Reverse.Forest}
    (hFv : Reverse.ValidAt x n (p + 1) F) (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices) :
    trackedState n p u (Reverse.insertLabel F p) = trackedState n (p + 1) u F := by
  classical
  have hnot := inr_notMem_of_validAt hFv
  set G := Reverse.insertLabel F p
  have hold (j : Fin k) (hj : Born n (p + 1) u j) : G.root (u j) = F.root (u j) :=
    ForestCoalescence.insertLabel_root_old F p (hmem j hj)
  have hnewroot (j : Fin k) (hj : j ∈ newborn n p u) : G.root (u j) = Sum.inr p := by
    rw [eq_inr_of_mem_newborn hp hj]
    exact insertLabel_root_inr hnot
  have hcases (j : Fin k) (hj : Born n p u j) : Born n (p + 1) u j ∨ j ∈ newborn n p u := by
    by_cases h : Born n (p + 1) u j
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, h⟩)
  have hold_ne (j l : Fin k) (hj : Born n (p + 1) u j) (hl : l ∈ newborn n p u) :
      G.root (u j) ≠ G.root (u l) := by
    rw [hold j hj, hnewroot l hl]
    intro h
    exact hnot (h ▸ F.root_mem (u j) (hmem j hj))
  funext j l
  have hup (i : Fin k) : Born n (p + 1) u i → Born n p u i := le_trans (Nat.le_succ p)
  by_cases hb : Born n p u j ∧ Born n p u l
  · rcases hcases j hb.1 with hj | hj <;> rcases hcases l hb.2 with hl | hl
    · simp [trackedState, hb, hj, hl, hold j hj, hold l hl]
    · have hnl := (Finset.mem_filter.mp hl).2.2
      have hne : j ≠ l := fun h ↦ hnl (h ▸ hj)
      simp [trackedState, hb, hnl, hold_ne j l hj hl, hne]
    · have hnj := (Finset.mem_filter.mp hj).2.2
      have hne : j ≠ l := fun h ↦ hnj (h ▸ hl)
      simp [trackedState, hb, hnj, Ne.symm (hold_ne l j hl hj), hne]
    · have hjl : j = l := hinj ((eq_inr_of_mem_newborn hp hj).trans
        (eq_inr_of_mem_newborn hp hl).symm)
      simp [trackedState, hb, hjl]
  · have hb' : ¬ (Born n (p + 1) u j ∧ Born n (p + 1) u l) := fun h ↦ hb ⟨hup j h.1, hup l h.2⟩
    simp [trackedState, hb, hb']

theorem mergeState_eq_true_iff (s : Fin k → Fin k → Bool) (j₀ l₀ j l : Fin k) :
    mergeState s j₀ l₀ j l = true ↔ MergedRel (fun a b ↦ s a b = true) j₀ l₀ j l := by
  simp [mergeState, MergedRel, Bool.or_eq_true, Bool.and_eq_true, or_assoc]

theorem mergeState_respects {s : Fin k → Fin k → Bool} (hs : StateRespects n p u s)
    {j₀ l₀ : Fin k} (hj₀ : Born n p u j₀) (hl₀ : Born n p u l₀) :
    StateRespects n p u (mergeState s j₀ l₀) := by
  intro j l h
  have hjl := hs j l h
  by_cases hj : Born n p u j
  · have hl : ¬ Born n p u l := fun hl ↦ h ⟨hj, hl⟩
    have h1 : s l l₀ = false := by
      rw [hs l l₀ (fun h' ↦ hl h'.1)]; simp only [decide_eq_false_iff_not]
      exact fun he ↦ hl (he ▸ hl₀)
    have h2 : s l j₀ = false := by
      rw [hs l j₀ (fun h' ↦ hl h'.1)]; simp only [decide_eq_false_iff_not]
      exact fun he ↦ hl (he ▸ hj₀)
    simp [mergeState, hjl, h1, h2]
  · have h1 : s j j₀ = false := by
      rw [hs j j₀ (fun h' ↦ hj h'.1)]; simp only [decide_eq_false_iff_not]
      exact fun he ↦ hj (he ▸ hj₀)
    have h2 : s j l₀ = false := by
      rw [hs j l₀ (fun h' ↦ hj h'.1)]; simp only [decide_eq_false_iff_not]
      exact fun he ↦ hj (he ▸ hl₀)
    simp [mergeState, hjl, h1, h2]

/-- After a join that does not involve two tracked components, the state is unchanged. -/
theorem trackedState_joinChoice_of_not_tracked {F : Reverse.Forest}
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hq : q ∈ F.roots.offDiag)
    (hnot : ¬ (q.1 ∈ trackedRoots n (p + 1) u F ∧ q.2 ∈ trackedRoots n (p + 1) u F)) :
    trackedState n p u (F.joinChoice q) = trackedState n (p + 1) u F := by
  have hG := (consistent_joinChoice_noMerge_iff (consistent_trackedState F) hborn
    (fun _ _ _ _ ↦ Iff.rfl) hq).mpr hnot
  apply trackedState_eq_of_conn
  · intro j l h
    exact trackedState_respects F j l (fun h' ↦ h ⟨(hborn j).mpr h'.1, (hborn l).mpr h'.2⟩)
  · exact hG.1

/-- After a join of two tracked components, the state is the corresponding merge. -/
theorem trackedState_joinChoice_of_tracked {F : Reverse.Forest}
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hq : q ∈ F.roots.offDiag) {j₁ l₁ : Fin k}
    (hj₁ : Born n (p + 1) u j₁) (hl₁ : Born n (p + 1) u l₁)
    (h1 : q.1 = F.root (u j₁)) (h2 : q.2 = F.root (u l₁)) :
    trackedState n (p + 1) u F j₁ l₁ = false ∧
      trackedState n p u (F.joinChoice q) = mergeState (trackedState n (p + 1) u F) j₁ l₁ := by
  set s := trackedState n (p + 1) u F
  have hq12 := (Finset.mem_offDiag.mp hq).2.2
  have hsep : s j₁ l₁ = false := by
    have := conn_of_trackedState_eq (rfl : trackedState n (p + 1) u F = s) j₁ l₁ hj₁ hl₁
    rw [← h1, ← h2] at this
    exact (Bool.not_eq_true _).mp fun h ↦ hq12 (this.mpr h)
  refine ⟨hsep, ?_⟩
  have hroots : (F.joinChoice q).root (F.root (u j₁)) = (F.joinChoice q).root (F.root (u l₁)) := by
    rw [← h1, ← h2, joinChoice_root_apply F hq, joinChoice_root_apply F hq]
    have hr1 := (RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hq).1).2
    have hr2 := (RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hq).2.1).2
    rw [hr1, hr2]
    simp [joinRelabel, hq12]
  have hG := (consistent_joinChoice_merge_iff (consistent_trackedState F) hborn hmem hj₁ hl₁
    (by simpa using hsep) (R' := fun a b ↦ mergeState s j₁ l₁ a b = true)
    (fun j l _ _ ↦ mergeState_eq_true_iff s j₁ l₁ j l) hq).mpr hroots
  apply trackedState_eq_of_conn
  · apply mergeState_respects
    · intro j l h
      exact trackedState_respects F j l (fun h' ↦ h ⟨(hborn j).mpr h'.1, (hborn l).mpr h'.2⟩)
    · exact (hborn j₁).mpr hj₁
    · exact (hborn l₁).mpr hl₁
  · exact hG.1

theorem stateRespects_of_born_iff (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    {s : Fin k → Fin k → Bool} (hs : StateRespects n (p + 1) u s) : StateRespects n p u s :=
  fun j l h ↦ hs j l fun h' ↦ h ⟨(hborn j).mpr h'.1, (hborn l).mpr h'.2⟩

theorem stateClasses_congr (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (s : Fin k → Fin k → Bool) : stateClasses n p u s = stateClasses n (p + 1) u s := by
  classical
  have : bornSet n p u = bornSet n (p + 1) u := by
    ext j
    simp [bornSet, hborn j]
  simp only [stateClasses, this]

open Classical in
/-- One-step transition probabilities of the tracked connectivity chain, from the
state at phase `p + 1` to the state at phase `p`. -/
noncomputable def chainStep (x : SignSequence) (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ)
    (s s' : Fin k → Fin k → Bool) : ℝ :=
  if x (p + 1) = true then
    if s' = s then
      1 - ((stateClasses n (p + 1) u s).choose 2 : ℝ) /
        ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ)
    else if IsMerge n (p + 1) u s s' then
      1 / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ)
    else 0
  else if s' = s then 1 else 0

/-- **One-step law of the tracked connectivity chain.** The conditional probability
of the next tracked state depends only on the current tracked state. -/
theorem transitionLaw_trackedState (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u)
    {F : Reverse.Forest} (hFv : Reverse.ValidAt x n (p + 1) F)
    (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices) (s' : Fin k → Fin k → Bool) :
    (Reverse.transitionLaw x p F).real {G | trackedState n p u G = s'} =
      chainStep x n p u (trackedState n (p + 1) u F) s' := by
  classical
  set s := trackedState n (p + 1) u F with hs_def
  by_cases hx : x (p + 1) = true
  · have hborn := born_iff_of_attachment hu hp hx
    have hrespect : StateRespects n p u s :=
      stateRespects_of_born_iff hborn (trackedState_respects F)
    have htwo := two_le_roots_of_attachment hn hp hFv hx
    have hFc : Consistent n (p + 1) u (fun j l ↦ s j l = true) (stateClasses n (p + 1) u s) F :=
      consistent_trackedState F
    by_cases hss : s' = s
    · rw [hss]
      have hev : {G | trackedState n p u G = s} = {G | Consistent n p u (fun j l ↦ s j l = true)
          (stateClasses n (p + 1) u s) G} := by
        ext G
        simp only [mem_ofPred_eq]
        rw [trackedState_eq_iff_consistent hrespect, stateClasses_congr hborn]
      rw [hev, transitionLaw_consistent_noMerge hn hp hFv hx hFc hborn hmem
        (fun _ _ _ _ ↦ Iff.rfl)]
      simp [chainStep, hx]
    by_cases hmerge : IsMerge n (p + 1) u s s'
    · have hval : chainStep x n p u s s' =
          1 / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ) := by
        simp [chainStep, hx, hss, hmerge]
      rw [hval]
      obtain ⟨j₀, l₀, hj₀, hl₀, hsep, rfl⟩ := hmerge
      set q₀ : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ) := (F.root (u j₀), F.root (u l₀))
      have hrs : F.root (u j₀) ≠ F.root (u l₀) := fun h ↦ by
        have := (conn_of_trackedState_eq hs_def.symm j₀ l₀ hj₀ hl₀).mp h
        rw [hsep] at this
        exact Bool.false_ne_true this
      have hq₀ : q₀ ∈ F.roots.offDiag := Finset.mem_offDiag.mpr
        ⟨F.root_mem_roots (hmem j₀ hj₀), F.root_mem_roots (hmem l₀ hl₀), hrs⟩
      have hR' : ∀ j l, Born n (p + 1) u j → Born n (p + 1) u l →
          (mergeState s j₀ l₀ j l = true ↔ MergedRel (fun a b ↦ s a b = true) j₀ l₀ j l) :=
        fun j l _ _ ↦ mergeState_eq_true_iff s j₀ l₀ j l
      have hsep' : ¬ (s j₀ l₀ = true) := by simp [hsep]
      have hstate₀ := (trackedState_joinChoice_of_tracked hborn hmem hq₀ hj₀ hl₀ rfl rfl).2
      have hcons₀ : Consistent n p u (fun j l ↦ mergeState s j₀ l₀ j l = true)
          (stateClasses n (p + 1) u s - 1) (F.joinChoice q₀) := by
        refine (consistent_joinChoice_merge_iff hFc hborn hmem hj₀ hl₀ hsep' hR' hq₀).mpr ?_
        rw [joinChoice_root_apply F hq₀, joinChoice_root_apply F hq₀]
        have hr1 := (RootedForest.mem_roots.mp (F.root_mem_roots (hmem j₀ hj₀))).2
        have hr2 := (RootedForest.mem_roots.mp (F.root_mem_roots (hmem l₀ hl₀))).2
        rw [hr1, hr2]
        simp [joinRelabel, q₀, hrs]
      have hcount : stateClasses n p u (mergeState s j₀ l₀) = stateClasses n (p + 1) u s - 1 := by
        rw [← hstate₀, ← card_trackedRoots_eq_stateClasses]
        exact hcons₀.2
      have hrespect' : StateRespects n p u (mergeState s j₀ l₀) :=
        mergeState_respects hrespect ((hborn j₀).mpr hj₀) ((hborn l₀).mpr hl₀)
      have hev : {G | trackedState n p u G = mergeState s j₀ l₀} =
          {G | Consistent n p u (fun j l ↦ mergeState s j₀ l₀ j l = true)
            (stateClasses n (p + 1) u s - 1) G} := by
        ext G
        simp only [mem_ofPred_eq]
        rw [trackedState_eq_iff_consistent hrespect', hcount]
      rw [hev]
      exact transitionLaw_consistent_merge hn hp hFv hx hFc hborn hmem hj₀ hl₀ hsep' hR'
    · have hval : chainStep x n p u s s' = 0 := by
        simp [chainStep, hx, hss, hmerge]
      rw [hval, measureReal_def]
      have heq : (Reverse.transitionLaw x p F) {G | trackedState n p u G = s'} =
          (Reverse.transitionLaw x p F) ∅ := by
        simp only [Reverse.transitionLaw, hx, ↓reduceIte]
        apply joinLaw_congr_offDiag F htwo
        intro q hq
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro hG
        by_cases htr : q.1 ∈ trackedRoots n (p + 1) u F ∧ q.2 ∈ trackedRoots n (p + 1) u F
        · obtain ⟨j₁, hj₁, h1⟩ := Finset.mem_image.mp htr.1
          obtain ⟨l₁, hl₁, h2⟩ := Finset.mem_image.mp htr.2
          have hj₁' : Born n (p + 1) u j₁ := (Finset.mem_filter.mp hj₁).2
          have hl₁' : Born n (p + 1) u l₁ := (Finset.mem_filter.mp hl₁).2
          obtain ⟨hsep₁, hst⟩ :=
            trackedState_joinChoice_of_tracked hborn hmem hq hj₁' hl₁' h1.symm h2.symm
          exact hmerge ⟨j₁, l₁, hj₁', hl₁', hsep₁, (hst.symm.trans hG).symm⟩
        · exact hss (hG.symm.trans (trackedState_joinChoice_of_not_tracked hborn hq htr))
      rw [heq, measure_empty, ENNReal.toReal_zero]
  · have hxf : x (p + 1) = false := by simpa using hx
    have hval : chainStep x n p u s s' = if s' = s then 1 else 0 := by
      simp [chainStep, hxf]
    rw [hval]
    simp only [Reverse.transitionLaw, hxf, Bool.false_eq_true, ↓reduceIte]
    rw [measureReal_def, Measure.dirac_apply' _
      (show MeasurableSet {G : Reverse.Forest | trackedState n p u G = s'} from trivial)]
    have hst := trackedState_insertLabel hp hinj hFv hmem
    by_cases hss : s' = s
    · simp [hss, hst, hs_def]
    · have : Reverse.insertLabel F p ∉ {G | trackedState n p u G = s'} := by
        simp only [mem_ofPred_eq, hst]
        exact fun h ↦ hss (h.symm.trans hs_def.symm)
      simp [this, hss]

/-- A finite measure is the sum of its restrictions to the fibres of a map into a
finite type. -/
theorem measureReal_eq_sum_fiber {α β : Type*} [MeasurableSpace α] [Fintype β]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (g : α → β)
    (hg : ∀ c, MeasurableSet (g ⁻¹' {c})) :
    μ.real E = ∑ c, μ.real (E ∩ g ⁻¹' {c}) := by
  have h := sum_measureReal_preimage_singleton (μ := μ.restrict E) Finset.univ (fun c _ ↦ hg c)
  simp only [Finset.coe_univ, Set.preimage_univ, measureReal_restrict_apply_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [measureReal_restrict_apply (hg c), Set.inter_comm]

/-- The tracked state after `m` reverse steps, that is, at phase `n - m`. -/
noncomputable def chainState (n : ℕ) (u : Fin k → ℕ ⊕ ℕ) (m : ℕ) (ω : ReverseHistory.History) :
    Fin k → Fin k → Bool :=
  trackedState n (n - m) u (ω m)

theorem measurableSet_chainState (n : ℕ) (u : Fin k → ℕ ⊕ ℕ) {m N : ℕ} (hm : m ≤ N)
    (s : Fin k → Fin k → Bool) :
    MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N]
      {ω | chainState n u m ω = s} :=
  ReverseHistory.measurable_eval_piLE hm
    (show MeasurableSet {G : Reverse.Forest | trackedState n (n - m) u G = s} from trivial)

/-- **Markov property of the tracked chain.** Given any past event and the current
tracked state, the next tracked state follows `chainStep`. -/
theorem jointLaw_chainState_step (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u) {N : ℕ}
    (hN : N < n) {A : Set ReverseHistory.History}
    (hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A)
    (s s' : Fin k → Fin k → Bool) :
    (ReverseHistory.jointLaw x n).real
        (A ∩ {ω | chainState n u N ω = s} ∩ {ω | chainState n u (N + 1) ω = s'}) =
      (ReverseHistory.jointLaw x n).real (A ∩ {ω | chainState n u N ω = s}) *
        chainStep x n (n - (N + 1)) u s s' := by
  have hval : ∀ᵐ ω ∂ReverseHistory.jointLaw x n, Reverse.ValidAt x n (n - N) (ω N) := by
    have h := Freezing1.Reverse.lawAfter_valid x n N hn hN.le
    rw [← ReverseHistory.jointLaw_map_eval x n N] at h
    exact ae_of_ae_map (measurable_pi_apply N).aemeasurable h
  have hp1 : n - (N + 1) + 1 = n - N := by omega
  apply ReverseHistory.jointLaw_real_inter_succ x n hN
    (hA.inter (measurableSet_chainState n u le_rfl s))
    {G | trackedState n (n - (N + 1)) u G = s'}
  filter_upwards [hval] with ω hω hAω
  have hω' : Reverse.ValidAt x n (n - (N + 1) + 1) (ω N) := by rwa [hp1]
  have hmem : ∀ j, Born n (n - (N + 1) + 1) u j → u j ∈ (ω N).vertices := by
    intro j hj
    rw [hω'.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) (hu j)).mpr hj
  rw [transitionLaw_trackedState hn (by omega) hu hinj hω' hmem s', hp1]
  have hs : chainState n u N ω = s := hAω.2
  rw [← hs]
  rfl

/-- The one-step transition matrix of the tracked chain from phase `p + 1` to
phase `p`. -/
noncomputable def chainMatrix (x : SignSequence) (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) :
    Matrix (Fin k → Fin k → Bool) (Fin k → Fin k → Bool) ℝ :=
  fun s s' ↦ chainStep x n p u s s'

/-- The transition matrix of the tracked chain over the `d` steps below phase `a`. -/
noncomputable def chainPower (x : SignSequence) (n a : ℕ) (u : Fin k → ℕ ⊕ ℕ) :
    ℕ → Matrix (Fin k → Fin k → Bool) (Fin k → Fin k → Bool) ℝ
  | 0 => 1
  | d + 1 => chainPower x n a u d * chainMatrix x n (a - (d + 1)) u

/-- **Chapman–Kolmogorov for the tracked chain.** Jointly with any event of the past
up to phase `a`, the tracked state `d` phases later is obtained from the state at
phase `a` by the matrix `chainPower`. -/
theorem jointLaw_chainState_power (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u) {a : ℕ}
    (ha : a ≤ n) {A : Set ReverseHistory.History}
    (hA : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) (n - a)] A) :
    ∀ d ≤ a, ∀ s' : Fin k → Fin k → Bool,
      (ReverseHistory.jointLaw x n).real (A ∩ {ω | chainState n u (n - (a - d)) ω = s'}) =
        ∑ s, (ReverseHistory.jointLaw x n).real (A ∩ {ω | chainState n u (n - a) ω = s}) *
          chainPower x n a u d s s' := by
  classical
  intro d
  induction d with
  | zero =>
    intro _ s'
    simp only [Nat.sub_zero, chainPower, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  | succ d ih =>
    intro hd s'
    set μ := ReverseHistory.jointLaw x n
    set N := n - (a - d) with hNdef
    have hN : N < n := by omega
    have hN1 : n - (a - (d + 1)) = N + 1 := by omega
    have hAN : MeasurableSet[Filtration.piLE (X := fun _ ↦ Reverse.Forest) N] A :=
      Filtration.mono _ (by omega) _ hA
    rw [hN1, measureReal_eq_sum_fiber μ _ (chainState n u N)
      (fun c ↦ (Filtration.piLE (X := fun _ ↦ Reverse.Forest)).le N _
        (measurableSet_chainState n u le_rfl c))]
    have hstep (s'' : Fin k → Fin k → Bool) :
        μ.real (A ∩ {ω | chainState n u (N + 1) ω = s'} ∩ chainState n u N ⁻¹' {s''}) =
          μ.real (A ∩ {ω | chainState n u N ω = s''}) * chainStep x n (a - (d + 1)) u s'' s' := by
      have h := jointLaw_chainState_step hn hu hinj hN hAN s'' s'
      rw [show n - (N + 1) = a - (d + 1) by omega] at h
      rw [← h]
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      tauto
    simp_rw [hstep, ih (by omega), chainPower, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun s'' _ ↦ ?_
    simp only [chainMatrix]
    ring

end Freezing2.TrackedGenealogy
