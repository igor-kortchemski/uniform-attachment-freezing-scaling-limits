module

public import Freezing2.Probability.ReverseMarkovPath
public import Freezing2.Probability.ClusterTransition
public import Freezing2.Probability.CoalescenceTransition

/-!
# The exact genealogy law of finitely many tracked labels

Finitely many labels of the actual reverse construction are tracked. At each
phase, the born tracked labels are partitioned into connected components. A
prescribed partition path, together with the prescribed number of tracked
components, is followed with probability equal to an explicit product over
the steps: a deterministic factor at freezing steps, the survival factor
`1 - C(a,2)/C(S,2)` at attachment steps without a tracked merger, and the
factor `1/C(S,2)` at an attachment step where two prescribed components merge.

This is the exact discrete genealogy law behind the local limit `eq:cv locale`;
it is derived from the actual transition kernel and the Markov path product,
without any independence assumption.
-/

@[expose] public section

open MeasureTheory Set

namespace Freezing2.TrackedGenealogy

open Freezing1 TrackedClusters ReverseHistory

variable {k : ℕ}

/-- Tracked label `j` is present at phase `p`. -/
def Born (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (j : Fin k) : Prop := p ≤ Freezing1.birthTime n (u j)

/-- Roots of the components of the tracked labels present at phase `p`. -/
noncomputable def trackedRoots (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (F : Reverse.Forest) :
    Finset (ℕ ⊕ ℕ) :=
  open Classical in (Finset.univ.filter fun j ↦ Born n p u j).image fun j ↦ F.root (u j)

/-- The forest realizes the prescribed connectivity `R` and component count `a`
of the tracked labels present at phase `p`. -/
def Consistent (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) (R : Fin k → Fin k → Prop) (a : ℕ)
    (F : Reverse.Forest) : Prop :=
  (∀ j l, Born n p u j → Born n p u l → (F.root (u j) = F.root (u l) ↔ R j l)) ∧
    (trackedRoots n p u F).card = a

variable {n p : ℕ} {u : Fin k → ℕ ⊕ ℕ}

/-- The root relabelling performed by a join of the ordered pair `q`. -/
def joinRelabel (q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) (r : ℕ ⊕ ℕ) : ℕ ⊕ ℕ := if r = q.2 then q.1 else r

theorem joinChoice_root_apply (F : Reverse.Forest) {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hq : q ∈ F.roots.offDiag) (v : ℕ ⊕ ℕ) :
    (F.joinChoice q).root v = joinRelabel q (F.root v) := by
  simp only [RootedForest.joinChoice, dite_eq_left hq, RootedForest.join, joinRelabel]

/-- Tracked roots after a join are the relabelled tracked roots. -/
theorem trackedRoots_joinChoice (F : Reverse.Forest) {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hq : q ∈ F.roots.offDiag) (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j) :
    trackedRoots n p u (F.joinChoice q) =
      (trackedRoots n (p + 1) u F).image (joinRelabel q) := by
  classical
  simp only [trackedRoots, Finset.image_image, Function.comp_def, joinChoice_root_apply F hq]
  congr 1
  ext j
  simp [hborn]

theorem trackedRoots_subset_roots (F : Reverse.Forest)
    (hmem : ∀ j, Born n p u j → u j ∈ F.vertices) : trackedRoots n p u F ⊆ F.roots := by
  classical
  intro r hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  exact F.root_mem_roots (hmem j (Finset.mem_filter.mp hj).2)

/-- An attachment step without a prescribed tracked merger. -/
theorem consistent_joinChoice_noMerge_iff {F : Reverse.Forest} {R R' : Fin k → Fin k → Prop}
    {a : ℕ} (hF : Consistent n (p + 1) u R a F)
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (hR : ∀ j l, Born n (p + 1) u j → Born n (p + 1) u l → (R' j l ↔ R j l))
    {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hq : q ∈ F.roots.offDiag) :
    Consistent n p u R' a (F.joinChoice q) ↔
      ¬ (q.1 ∈ trackedRoots n (p + 1) u F ∧ q.2 ∈ trackedRoots n (p + 1) u F) := by
  classical
  obtain ⟨hq1, hq2, hq12⟩ := Finset.mem_offDiag.mp hq
  set A := trackedRoots n (p + 1) u F
  constructor
  · rintro hG ⟨h1, h2⟩
    obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp h1
    obtain ⟨l, hl, hlq⟩ := Finset.mem_image.mp h2
    have hj' := (Finset.mem_filter.mp hj).2
    have hl' := (Finset.mem_filter.mp hl).2
    have hGjl : (F.joinChoice q).root (u j) = (F.joinChoice q).root (u l) := by
      rw [joinChoice_root_apply F hq, joinChoice_root_apply F hq, hjq, hlq]
      simp [joinRelabel, hq12]
    have hRjl := (hR j l hj' hl').mp ((hG.1 j l ((hborn j).mpr hj') ((hborn l).mpr hl')).mp hGjl)
    exact hq12 (hjq.symm.trans (((hF.1 j l hj' hl').mpr hRjl).trans hlq))
  · intro hnot
    have hinj : Set.InjOn (joinRelabel q) A := by
      intro r₁ hr₁ r₂ hr₂ h
      by_contra hne
      simp only [joinRelabel] at h
      split_ifs at h with h₁ h₂ h₂
      · exact hne (h₁.trans h₂.symm)
      · exact hnot ⟨h ▸ hr₂, h₁ ▸ hr₁⟩
      · exact hnot ⟨h.symm ▸ hr₁, h₂ ▸ hr₂⟩
      · exact hne h
    refine ⟨fun j l hj hl ↦ ?_, ?_⟩
    · have hj' := (hborn j).mp hj
      have hl' := (hborn l).mp hl
      have hjA : F.root (u j) ∈ A := Finset.mem_image.mpr
        ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩
      have hlA : F.root (u l) ∈ A := Finset.mem_image.mpr
        ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩, rfl⟩
      rw [joinChoice_root_apply F hq, joinChoice_root_apply F hq, hinj.eq_iff hjA hlA,
        hF.1 j l hj' hl', hR j l hj' hl']
    · rw [trackedRoots_joinChoice F hq hborn, Finset.card_image_of_injOn hinj, hF.2]

/-- The prescribed merger of the components of `j₀` and `l₀`. -/
def MergedRel (R : Fin k → Fin k → Prop) (j₀ l₀ : Fin k) (j l : Fin k) : Prop :=
  R j l ∨ (R j j₀ ∧ R l l₀) ∨ (R j l₀ ∧ R l j₀)

theorem joinRelabel_eq_iff {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hq : q.1 ≠ q.2) (r₁ r₂ : ℕ ⊕ ℕ) :
    joinRelabel q r₁ = joinRelabel q r₂ ↔
      r₁ = r₂ ∨ (r₁ = q.1 ∧ r₂ = q.2) ∨ (r₁ = q.2 ∧ r₂ = q.1) := by
  unfold joinRelabel
  by_cases h₁ : r₁ = q.2 <;> by_cases h₂ : r₂ = q.2 <;> simp only [h₁, h₂, ↓reduceIte] <;>
    aesop

/-- An attachment step at which exactly the components of `j₀` and `l₀` merge. -/
theorem consistent_joinChoice_merge_iff {F : Reverse.Forest} {R R' : Fin k → Fin k → Prop}
    {a : ℕ} (hF : Consistent n (p + 1) u R a F)
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    {j₀ l₀ : Fin k} (hj₀ : Born n (p + 1) u j₀) (hl₀ : Born n (p + 1) u l₀)
    (hsep : ¬ R j₀ l₀)
    (hR : ∀ j l, Born n (p + 1) u j → Born n (p + 1) u l → (R' j l ↔ MergedRel R j₀ l₀ j l))
    {q : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)} (hq : q ∈ F.roots.offDiag) :
    Consistent n p u R' (a - 1) (F.joinChoice q) ↔
      (F.joinChoice q).root (F.root (u j₀)) = (F.joinChoice q).root (F.root (u l₀)) := by
  classical
  obtain ⟨hq1, hq2, hq12⟩ := Finset.mem_offDiag.mp hq
  set A := trackedRoots n (p + 1) u F
  have hrootroot (j : Fin k) (hj : Born n (p + 1) u j) : F.root (F.root (u j)) = F.root (u j) :=
    (RootedForest.mem_roots.mp (F.root_mem_roots (hmem j hj))).2
  have hmemA (j : Fin k) (hj : Born n (p + 1) u j) : F.root (u j) ∈ A :=
    Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  have hrs : F.root (u j₀) ≠ F.root (u l₀) := fun h ↦ hsep ((hF.1 j₀ l₀ hj₀ hl₀).mp h)
  have hRrefl (j : Fin k) (hj : Born n (p + 1) u j) : R j j := (hF.1 j j hj hj).mp rfl
  rw [joinChoice_root_apply F hq, joinChoice_root_apply F hq, hrootroot j₀ hj₀,
    hrootroot l₀ hl₀, joinRelabel_eq_iff hq12]
  constructor
  · intro hG
    have hm : MergedRel R j₀ l₀ j₀ l₀ := Or.inr (Or.inl ⟨hRrefl j₀ hj₀, hRrefl l₀ hl₀⟩)
    have h := (hG.1 j₀ l₀ ((hborn j₀).mpr hj₀) ((hborn l₀).mpr hl₀)).mpr
      ((hR j₀ l₀ hj₀ hl₀).mpr hm)
    rwa [joinChoice_root_apply F hq, joinChoice_root_apply F hq, joinRelabel_eq_iff hq12] at h
  · intro hpair
    have hqA : q.1 ∈ A ∧ q.2 ∈ A := by
      rcases hpair with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h hrs
      · exact ⟨h1 ▸ hmemA j₀ hj₀, h2 ▸ hmemA l₀ hl₀⟩
      · exact ⟨h2 ▸ hmemA l₀ hl₀, h1 ▸ hmemA j₀ hj₀⟩
    refine ⟨fun j l hj hl ↦ ?_, ?_⟩
    · have hj' := (hborn j).mp hj
      have hl' := (hborn l).mp hl
      rw [joinChoice_root_apply F hq, joinChoice_root_apply F hq, joinRelabel_eq_iff hq12,
        hR j l hj' hl', MergedRel, ← hF.1 j l hj' hl', ← hF.1 j j₀ hj' hj₀,
        ← hF.1 l l₀ hl' hl₀, ← hF.1 j l₀ hj' hl₀, ← hF.1 l j₀ hl' hj₀]
      rcases hpair with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h hrs
      · rw [← h1, ← h2]
      · rw [← h1, ← h2]
        tauto
    · have himage : A.image (joinRelabel q) = A.erase q.2 := by
        ext r
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨r', hr', rfl⟩
          unfold joinRelabel
          split_ifs with h
          · exact ⟨hq12, hqA.1⟩
          · exact ⟨h, hr'⟩
        · rintro ⟨hne, hr⟩
          exact ⟨r, hr, by simp [joinRelabel, hne]⟩
      rw [trackedRoots_joinChoice F hq hborn, himage, Finset.card_erase_of_mem hqA.2, hF.2]

theorem joinLaw_congr_offDiag (F : Reverse.Forest) (hF : 2 ≤ F.roots.card)
    {E E' : Set Reverse.Forest}
    (h : ∀ q ∈ F.roots.offDiag, F.joinChoice q ∈ E ↔ F.joinChoice q ∈ E') :
    F.joinLaw E = F.joinLaw E' := by
  classical
  rw [RootedForest.joinLaw_apply F hF, RootedForest.joinLaw_apply F hF]
  congr 3
  ext q
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hq, he⟩ ↦ ⟨hq, (h q hq).mp he⟩, fun ⟨hq, he⟩ ↦ ⟨hq, (h q hq).mpr he⟩⟩

variable {x : SignSequence}

theorem two_le_roots_of_attachment (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n)
    {F : Reverse.Forest} (hF : Reverse.ValidAt x n (p + 1) F) (hx : x (p + 1) = true) :
    2 ≤ F.roots.card := by
  have hiτ : ((p + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((p + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hp)) hn
  rw [hF.roots_card]
  exact two_le_activeCount_toNat_succ_of_attachment hiτ hx

/-- Survival factor of an attachment step without a prescribed tracked merger. -/
theorem transitionLaw_consistent_noMerge (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n)
    {F : Reverse.Forest} (hFv : Reverse.ValidAt x n (p + 1) F) (hx : x (p + 1) = true)
    {R R' : Fin k → Fin k → Prop} {a : ℕ} (hF : Consistent n (p + 1) u R a F)
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    (hR : ∀ j l, Born n (p + 1) u j → Born n (p + 1) u l → (R' j l ↔ R j l)) :
    (Reverse.transitionLaw x p F).real {G | Consistent n p u R' a G} =
      1 - (a.choose 2 : ℝ) / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ) := by
  have hA := trackedRoots_subset_roots F hmem
  have htwo := two_le_roots_of_attachment hn hp hFv hx
  have heq : (Reverse.transitionLaw x p F) {G | Consistent n p u R' a G} =
      (Reverse.transitionLaw x p F) {G | ¬ Merger (trackedRoots n (p + 1) u F) G} := by
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    apply joinLaw_congr_offDiag F htwo
    intro q hq
    simp only [mem_ofPred_eq]
    rw [consistent_joinChoice_noMerge_iff hF hborn hR hq, merger_joinChoice_iff F hA hq]
  rw [measureReal_def, heq, ← measureReal_def, transitionLaw_noMerger hn hp hFv hA, ite_eq_left hx,
    hF.2]

/-- The factor of an attachment step at which two prescribed components merge. -/
theorem transitionLaw_consistent_merge (hn : (n : ℕ∞) ≤ extinctionTime x) (hp : p < n)
    {F : Reverse.Forest} (hFv : Reverse.ValidAt x n (p + 1) F) (hx : x (p + 1) = true)
    {R R' : Fin k → Fin k → Prop} {a : ℕ} (hF : Consistent n (p + 1) u R a F)
    (hborn : ∀ j, Born n p u j ↔ Born n (p + 1) u j)
    (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    {j₀ l₀ : Fin k} (hj₀ : Born n (p + 1) u j₀) (hl₀ : Born n (p + 1) u l₀)
    (hsep : ¬ R j₀ l₀)
    (hR : ∀ j l, Born n (p + 1) u j → Born n (p + 1) u l → (R' j l ↔ MergedRel R j₀ l₀ j l)) :
    (Reverse.transitionLaw x p F).real {G | Consistent n p u R' (a - 1) G} =
      1 / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ) := by
  have htwo := two_le_roots_of_attachment hn hp hFv hx
  have hr := F.root_mem_roots (hmem j₀ hj₀)
  have hs := F.root_mem_roots (hmem l₀ hl₀)
  have hrs : F.root (u j₀) ≠ F.root (u l₀) := fun h ↦ hsep ((hF.1 j₀ l₀ hj₀ hl₀).mp h)
  have heq : (Reverse.transitionLaw x p F) {G | Consistent n p u R' (a - 1) G} =
      (Reverse.transitionLaw x p F) {G | G.root (F.root (u j₀)) = G.root (F.root (u l₀))} := by
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    apply joinLaw_congr_offDiag F htwo
    intro q hq
    simp only [mem_ofPred_eq]
    exact consistent_joinChoice_merge_iff hF hborn hmem hj₀ hl₀ hsep hR hq
  rw [measureReal_def, heq, ← measureReal_def, transitionLaw_fixedPair hn hp hFv hr hs hrs,
    ite_eq_left hx]

/-- Tracked labels born exactly at phase `p`. -/
noncomputable def newborn (n p : ℕ) (u : Fin k → ℕ ⊕ ℕ) : Finset (Fin k) :=
  open Classical in Finset.univ.filter fun j ↦ Born n p u j ∧ ¬ Born n (p + 1) u j

theorem eq_inr_of_mem_newborn (hp : p < n) {j : Fin k} (hj : j ∈ newborn n p u) :
    u j = Sum.inr p := by
  classical
  obtain ⟨hb, hnb⟩ := (Finset.mem_filter.mp hj).2
  simp only [Born, not_le] at hb hnb
  cases h : u j with
  | inl i => simp only [h, Freezing1.birthTime] at hb hnb; omega
  | inr i =>
    simp only [h, Freezing1.birthTime] at hb hnb
    rw [show i = p by omega]

theorem card_newborn_le_one (hp : p < n) (hinj : Function.Injective u) :
    (newborn n p u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj l hl
  exact hinj ((eq_inr_of_mem_newborn hp hj).trans (eq_inr_of_mem_newborn hp hl).symm)

theorem inr_notMem_of_validAt {F : Reverse.Forest} (hFv : Reverse.ValidAt x n (p + 1) F) :
    Sum.inr p ∉ F.vertices := by
  rw [hFv.vertices_eq]
  simp [Reverse.phaseLabels]

theorem insertLabel_root_inr {F : Reverse.Forest} (hp : Sum.inr p ∉ F.vertices) :
    (Reverse.insertLabel F p).root (Sum.inr p) = Sum.inr p := by
  simp [Reverse.insertLabel, hp, RootedForest.adjoin]

/-- At a freezing step the tracked structure only gains the new singleton component
of a tracked label born at this phase, so the transition probability is one. -/
theorem transitionLaw_consistent_freeze (hp : p < n) {F : Reverse.Forest}
    (hFv : Reverse.ValidAt x n (p + 1) F) (hx : x (p + 1) = false)
    {R R' : Fin k → Fin k → Prop} {a : ℕ} (hF : Consistent n (p + 1) u R a F)
    (hinj : Function.Injective u) (hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices)
    (hR : ∀ j l, Born n p u j → Born n p u l →
      (R' j l ↔ (Born n (p + 1) u j ∧ Born n (p + 1) u l ∧ R j l) ∨
        ((¬ Born n (p + 1) u j ∨ ¬ Born n (p + 1) u l) ∧ j = l))) :
    (Reverse.transitionLaw x p F).real
      {G | Consistent n p u R' (a + (newborn n p u).card) G} = 1 := by
  classical
  have hnot := inr_notMem_of_validAt hFv
  set G := Reverse.insertLabel F p
  have hold (j : Fin k) (hj : Born n (p + 1) u j) : G.root (u j) = F.root (u j) :=
    ForestCoalescence.insertLabel_root_old F p (hmem j hj)
  have hnewroot (j : Fin k) (hj : j ∈ newborn n p u) : G.root (u j) = Sum.inr p := by
    rw [eq_inr_of_mem_newborn hp hj]
    exact insertLabel_root_inr hnot
  have hborn_cases (j : Fin k) (hj : Born n p u j) : Born n (p + 1) u j ∨ j ∈ newborn n p u := by
    by_cases h : Born n (p + 1) u j
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, h⟩)
  have hold_ne (j l : Fin k) (hj : Born n (p + 1) u j) (hl : l ∈ newborn n p u) :
      G.root (u j) ≠ G.root (u l) := by
    rw [hold j hj, hnewroot l hl]
    intro h
    exact hnot (h ▸ F.root_mem (u j) (hmem j hj))
  have hcons : Consistent n p u R' (a + (newborn n p u).card) G := by
    refine ⟨fun j l hj hl ↦ ?_, ?_⟩
    · rw [hR j l hj hl]
      rcases hborn_cases j hj with hj' | hj' <;> rcases hborn_cases l hl with hl' | hl'
      · rw [hold j hj', hold l hl', hF.1 j l hj' hl']
        exact ⟨fun h ↦ Or.inl ⟨hj', hl', h⟩, fun h ↦ h.elim (fun h ↦ h.2.2)
          (fun h ↦ (h.1.elim (fun h' ↦ absurd hj' h') (fun h' ↦ absurd hl' h')))⟩
      · have hnl := (Finset.mem_filter.mp hl').2.2
        exact ⟨fun h ↦ absurd h (hold_ne j l hj' hl'), fun h ↦ h.elim
          (fun h ↦ absurd h.2.1 hnl) (fun h ↦ absurd (h.2 ▸ hj') hnl)⟩
      · have hnj := (Finset.mem_filter.mp hj').2.2
        exact ⟨fun h ↦ absurd h.symm (hold_ne l j hl' hj'), fun h ↦ h.elim
          (fun h ↦ absurd h.1 hnj) (fun h ↦ absurd (h.2 ▸ hl') hnj)⟩
      · have hnj := (Finset.mem_filter.mp hj').2.2
        rw [hnewroot j hj', hnewroot l hl']
        exact ⟨fun _ ↦ Or.inr ⟨Or.inl hnj, hinj ((eq_inr_of_mem_newborn hp hj').trans
          (eq_inr_of_mem_newborn hp hl').symm)⟩, fun _ ↦ rfl⟩
    · have hsplit : trackedRoots n p u G = trackedRoots n (p + 1) u F ∪
          (newborn n p u).image fun _ ↦ Sum.inr p := by
        ext r
        simp only [trackedRoots, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj, rfl⟩
          rcases hborn_cases j hj with hj' | hj'
          · exact Or.inl ⟨j, hj', (hold j hj').symm⟩
          · exact Or.inr ⟨j, hj', (hnewroot j hj').symm⟩
        · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
          · exact ⟨j, le_trans (Nat.le_succ p) hj, hold j hj⟩
          · exact ⟨j, (Finset.mem_filter.mp hj).2.1, hnewroot j hj⟩
      have hdisj : Disjoint (trackedRoots n (p + 1) u F)
          ((newborn n p u).image fun _ ↦ Sum.inr p) := by
        rw [Finset.disjoint_left]
        intro r hr hr'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨l, hl, hl'⟩ := Finset.mem_image.mp hr'
        exact hnot (hl' ▸ F.root_mem (u j) (hmem j (Finset.mem_filter.mp hj).2))
      have hcard : ((newborn n p u).image fun _ ↦ (Sum.inr p : ℕ ⊕ ℕ)).card =
          (newborn n p u).card := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (card_newborn_le_one hp hinj) with h0 | h1
        · rw [Finset.card_eq_zero.mp h0]
          simp
        · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
          rw [hj]
          simp
      rw [hsplit, Finset.card_union_of_disjoint hdisj, hF.2, hcard]
  simp only [Reverse.transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
  rw [measureReal_def, Measure.dirac_apply_of_mem (show G ∈ {G | Consistent n p u R'
    (a + (newborn n p u).card) G} from hcons), ENNReal.toReal_one]

/-- The kind of one prescribed step of the tracked genealogy. -/
inductive StepKind (k : ℕ)
  | freeze
  | noMerge
  | merge (j₀ l₀ : Fin k)

/-- Exact probability factor of a prescribed step from phase `p + 1` to phase `p`. -/
noncomputable def stepFactor (x : SignSequence) (a : ℕ → ℕ) (κ : ℕ → StepKind k) (p : ℕ) : ℝ :=
  match κ p with
  | .freeze => 1
  | .noMerge => 1 - ((a (p + 1)).choose 2 : ℝ) /
      ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ)
  | .merge _ _ => 1 / ((Freezing1.activeCount x (p + 1)).toNat.choose 2 : ℝ)

/-- The prescribed connectivity and counts change as the step kind requires. -/
def StepValid (x : SignSequence) (n : ℕ) (u : Fin k → ℕ ⊕ ℕ)
    (R : ℕ → Fin k → Fin k → Prop) (a : ℕ → ℕ) (κ : ℕ → StepKind k) (p : ℕ) : Prop :=
  match κ p with
  | .freeze => x (p + 1) = false ∧
      (∀ j l, Born n p u j → Born n p u l →
        (R p j l ↔ (Born n (p + 1) u j ∧ Born n (p + 1) u l ∧ R (p + 1) j l) ∨
          ((¬ Born n (p + 1) u j ∨ ¬ Born n (p + 1) u l) ∧ j = l))) ∧
      a p = a (p + 1) + (newborn n p u).card
  | .noMerge => x (p + 1) = true ∧
      (∀ j l, Born n (p + 1) u j → Born n (p + 1) u l → (R p j l ↔ R (p + 1) j l)) ∧
      a p = a (p + 1)
  | .merge j₀ l₀ => x (p + 1) = true ∧ Born n (p + 1) u j₀ ∧ Born n (p + 1) u l₀ ∧
      ¬ R (p + 1) j₀ l₀ ∧
      (∀ j l, Born n (p + 1) u j → Born n (p + 1) u l →
        (R p j l ↔ MergedRel (R (p + 1)) j₀ l₀ j l)) ∧
      a p = a (p + 1) - 1

/-- No tracked label is born at an attachment step. -/
theorem born_iff_of_attachment (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hp : p < n)
    (hx : x (p + 1) = true) (j : Fin k) : Born n p u j ↔ Born n (p + 1) u j := by
  constructor
  · intro h
    by_contra h'
    simp only [Born, not_le] at h h'
    have hj := hu j
    cases hv : u j with
    | inl i => simp only [hv, Freezing1.birthTime] at h h'; omega
    | inr i =>
      simp only [hv, Freezing1.birthTime] at h h'
      rw [hv] at hj
      have hi : i = p := by omega
      subst hi
      simp [Freezing1.vertexLabels, Freezing1.frozenIndices, hx] at hj
  · exact fun h ↦ le_trans (Nat.le_succ p) h

/-- **Exact tracked genealogy law.** A prescribed sequence of tracked
connectivity relations and component counts is followed with probability equal
to the product of the step factors. The tracked labels are distinct and born
before the horizon. -/
theorem jointLaw_trackedGenealogy (hn : (n : ℕ∞) ≤ extinctionTime x)
    (hu : ∀ j, u j ∈ Freezing1.vertexLabels x n) (hinj : Function.Injective u)
    (hbirth : ∀ j, Freezing1.birthTime n (u j) < n)
    (R : ℕ → Fin k → Fin k → Prop) (a : ℕ → ℕ) (κ : ℕ → StepKind k)
    (hκ : ∀ p < n, StepValid x n u R a κ p) (ha : a n = 0) :
    (jointLaw x n).real {ω | ∀ m ≤ n, Consistent n (n - m) u (R (n - m)) (a (n - m)) (ω m)} =
      ∏ m ∈ Finset.range n, stepFactor x a κ (n - (m + 1)) := by
  classical
  let P : ℕ → Set Reverse.Forest := fun m ↦ {F | Consistent n (n - m) u (R (n - m)) (a (n - m)) F}
  let V : ℕ → Set Reverse.Forest := fun m ↦ {F | Reverse.ValidAt x n (n - m) F}
  have hV : ∀ m ≤ n, ∀ᵐ ω ∂jointLaw x n, ω m ∈ V m := by
    intro m hm
    have h := Freezing1.Reverse.lawAfter_valid x n m hn hm
    rw [← jointLaw_map_eval x n m] at h
    exact ae_of_ae_map (measurable_pi_apply m).aemeasurable h
  have hpresent (m : ℕ) (hm : m ≤ n) (F : Reverse.Forest) (hF : F ∈ V m) (j : Fin k)
      (hj : Born n (n - m) u j) : u j ∈ F.vertices := by
    rw [hF.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) (hu j)).mpr hj
  have h0 : Reverse.initial x n ∈ P 0 := by
    have hnone (j : Fin k) : ¬ Born n n u j := by
      simp only [Born, not_le]
      exact hbirth j
    refine ⟨fun j _ hj _ ↦ absurd hj (by simpa using hnone j), ?_⟩
    have : trackedRoots n (n - 0) u (Reverse.initial x n) = ∅ := by
      simp only [trackedRoots, Nat.sub_zero, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
      exact fun j _ ↦ hnone j
    rw [this, Finset.card_empty, Nat.sub_zero, ha]
  refine jointLaw_path_eq_prod x n P V hV (fun m ↦ stepFactor x a κ (n - (m + 1))) ?_ h0 n le_rfl
  intro m hm F ⟨hFP, hFV⟩
  set p := n - (m + 1) with hpdef
  have hp : p < n := by omega
  have hp1 : p + 1 = n - m := by omega
  have hFV' : Reverse.ValidAt x n (p + 1) F := by
    have h := hFV
    simp only [V, mem_ofPred_eq] at h
    rwa [← hp1] at h
  have hFP' : Consistent n (p + 1) u (R (p + 1)) (a (p + 1)) F := by
    have h := hFP
    simp only [P, mem_ofPred_eq] at h
    rwa [← hp1] at h
  have hmem : ∀ j, Born n (p + 1) u j → u j ∈ F.vertices := fun j hj ↦
    hpresent m (by omega) F hFV j (by rwa [← hp1])
  change (Reverse.transitionLaw x p F).real
    {G | Consistent n (n - (m + 1)) u (R (n - (m + 1))) (a (n - (m + 1))) G} = _
  rw [← hpdef]
  have hstep := hκ p hp
  unfold StepValid at hstep
  unfold stepFactor
  split at hstep
  · next hk =>
    obtain ⟨hx, hR, hap⟩ := hstep
    rw [hap]
    exact transitionLaw_consistent_freeze hp hFV' hx hFP' hinj hmem hR
  · next hk =>
    obtain ⟨hx, hR, hap⟩ := hstep
    rw [hap]
    exact transitionLaw_consistent_noMerge hn hp hFV' hx hFP' (born_iff_of_attachment hu hp hx)
      hmem hR
  · next j₀ l₀ hk =>
    obtain ⟨hx, hj₀, hl₀, hsep, hR, hap⟩ := hstep
    rw [hap]
    exact transitionLaw_consistent_merge hn hp hFV' hx hFP' (born_iff_of_attachment hu hp hx)
      hmem hj₀ hl₀ hsep hR

end Freezing2.TrackedGenealogy
