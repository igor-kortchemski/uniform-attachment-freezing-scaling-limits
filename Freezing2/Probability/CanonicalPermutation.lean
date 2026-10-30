module

public import Freezing2.Probability.ActivePermutationHistory
public import Freezing2.Probability.StampedForestExt
public import Freezing2.Probability.CanonicalForwardReplay
public import Freezing2.Probability.ReverseTerminalLaw

/-!
# The exact active-label fibres of canonical forward replay

The canonical observation forgets only the names of terminal active vertices.
Incoming timestamps match their identities; the parent and freezing records
then determine all present data. Actual outside normality completes equality
of the represented forests. No equality of the stochastic laws is assumed.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseStamped

theorem OutsideNormal.relabel {F : Forest} (hF : OutsideNormal F)
    (e : Equiv.Perm (ℕ ⊕ ℕ)) : OutsideNormal (relabel e F) := by
  intro v hv
  have hv' : e.symm v ∉ F.forest.vertices := by simpa using hv
  obtain ⟨hp, hr, hd, ht⟩ := hF _ hv'
  change e (F.forest.parent (e.symm v)) = v ∧ e (F.forest.root (e.symm v)) = v ∧
    F.forest.depth (e.symm v) = 0 ∧ F.edgeTime (e.symm v) = 0
  simp only [hp, hr, hd, ht, Equiv.apply_symm_apply, and_self]

theorem vertexOfTime_relabel {F : Forest}
    (hinj : Set.InjOn F.edgeTime (F.forest.vertices : Set (ℕ ⊕ ℕ)))
    (e : Equiv.Perm (ℕ ⊕ ℕ)) {t : ℕ} (ht : t ∈ F.forest.vertices.image F.edgeTime) :
    vertexOfTime (relabel e F) t = e (vertexOfTime F t) := by
  obtain ⟨hv, htime⟩ := vertexOfTime_spec ht
  have ht' : t ∈ (relabel e F).forest.vertices.image (relabel e F).edgeTime :=
    Finset.mem_image.mpr ⟨e (vertexOfTime F t), (relabel_mem_vertices e F _).mpr hv,
      by simpa using htime⟩
  obtain ⟨hw, hwtime⟩ := vertexOfTime_spec ht'
  apply e.symm.injective
  simp only [Equiv.symm_apply_apply]
  have hw' : e.symm (vertexOfTime (relabel e F) t) ∈ F.forest.vertices := by simpa using hw
  exact hinj hw' hv (hwtime.trans htime.symm)

theorem parentId_relabel {F : Forest}
    (hinj : Set.InjOn F.edgeTime (F.forest.vertices : Set (ℕ ⊕ ℕ)))
    (e : Equiv.Perm (ℕ ⊕ ℕ)) {t : ℕ} (ht : t ∈ F.forest.vertices.image F.edgeTime) :
    parentId (relabel e F) t = parentId F t := by
  unfold parentId
  rw [vertexOfTime_relabel hinj e ht, relabel_parent_apply, relabel_edgeTime_apply]

@[simp] theorem frozenId_relabelActive {m : ℕ} (σ : Equiv.Perm (Fin m)) (F : Forest) (s : ℕ) :
    frozenId (relabelActive σ F) s = frozenId F s := by
  simp [frozenId, relabelActive, relabel, activeLabelEquiv_symm]

/-- Canonical replay ignores active-label names, but keeps every source-relevant
parent and freezing record. Unused inverse-lookup fallbacks are not compared. -/
theorem canonicalForwardState_relabelActive {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) :
    canonicalForwardState x n (relabelActive σ F) = canonicalForwardState x n F := by
  apply canonicalForwardState_eq_of_records
  · intro t ht0 htn hxt
    apply parentId_relabel
    · intro u hu v hv he
      exact hT.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF) u hu v hv he
    · rw [hT.edgeTime_image_of_one_root (one_root_of_terminal_valid hF)]
      exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, htn⟩, hxt⟩)
  · intro t _ _ _
    exact frozenId_relabelActive σ F t

/-- Equal canonical records match the active labels by their unique incoming
timestamps; frozen labels are fixed. The resulting permutation recovers the
entire represented forest once the actual outside normal form is supplied. -/
theorem exists_relabelActive_of_records {x : Freezing1.SignSequence} {n : ℕ} {F G : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (hFN : OutsideNormal F)
    (hG : Freezing1.Reverse.ValidAt x n 0 G.forest)
    (hU : Freezing1.ReverseStamped.TimesValidAt x n 0 G) (hGN : OutsideNormal G)
    (hp : ∀ t, 1 ≤ t → t ≤ n → x t = true → parentId F t = parentId G t)
    (hf : ∀ t, 1 ≤ t → t ≤ n → x t = false → frozenId F t = frozenId G t) :
    ∃ σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat), relabelActive σ F = G := by
  let m := (Freezing1.activeCount x n).toNat
  have hverts : F.forest.vertices = G.forest.vertices := hF.vertices_eq.trans hG.vertices_eq.symm
  have hinjF : Set.InjOn F.edgeTime (F.forest.vertices : Set (ℕ ⊕ ℕ)) := by
    intro u hu v hv he
    exact hT.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF) u hu v hv he
  have hinjG : Set.InjOn G.edgeTime (G.forest.vertices : Set (ℕ ⊕ ℕ)) := by
    intro u hu v hv he
    exact hU.edgeTime_injective_of_one_root (one_root_of_terminal_valid hG) u hu v hv he
  have hactive (a : Fin m) : Sum.inl a.val ∈ F.forest.vertices := by
    rw [hF.vertices_eq]
    simpa only [Freezing1.Reverse.phaseLabels, Finset.inl_mem_disjSum, Finset.mem_range] using a.isLt
  have himage : F.forest.vertices.image F.edgeTime = G.forest.vertices.image G.edgeTime := by
    rw [hT.edgeTime_image_of_one_root (one_root_of_terminal_valid hF),
      hU.edgeTime_image_of_one_root (one_root_of_terminal_valid hG)]
  have hfrozen (j : ℕ) (hj : Sum.inr j ∈ F.forest.vertices) :
      F.edgeTime (Sum.inr j) = G.edgeTime (Sum.inr j) := by
    rw [hF.vertices_eq] at hj
    simp only [Freezing1.Reverse.phaseLabels, Finset.inr_mem_disjSum,
      Finset.mem_filter, Finset.mem_range] at hj
    simpa [frozenId] using hf (j + 1) (by omega) (by omega) hj.2.2
  have hex (a : Fin m) : ∃ b : Fin m, G.edgeTime (Sum.inl b.val) = F.edgeTime (Sum.inl a.val) := by
    have htmem : F.edgeTime (Sum.inl a.val) ∈ G.forest.vertices.image G.edgeTime := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨Sum.inl a.val, hactive a, rfl⟩
    obtain ⟨v, hv, ht⟩ := Finset.mem_image.mp htmem
    cases v with
    | inl j =>
      have hj : j < m := by
        simpa only [hG.vertices_eq, Freezing1.Reverse.phaseLabels,
          Finset.inl_mem_disjSum, Finset.mem_range] using hv
      exact ⟨⟨j, hj⟩, ht⟩
    | inr j =>
      have hjF : Sum.inr j ∈ F.forest.vertices := hverts.symm ▸ hv
      have he := hinjF hjF (hactive a) ((hfrozen j hjF).trans ht)
      cases he
  choose f hft using hex
  have hfinj : Function.Injective f := by
    intro a b he
    apply Fin.ext
    apply Sum.inl.inj
    apply hinjF (hactive a) (hactive b)
    exact (hft a).symm.trans ((congrArg (fun c : Fin m ↦ G.edgeTime (Sum.inl c.val)) he).trans (hft b))
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective f ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  let e := activeLabelEquiv σ
  have hmem (v : ℕ ⊕ ℕ) (hv : v ∈ F.forest.vertices) : e v ∈ G.forest.vertices := by
    rw [hG.vertices_eq]
    apply (activeLabelEquiv_mem_phaseLabels x n 0 σ v).mpr
    rwa [← hF.vertices_eq]
  have htimes (v : ℕ ⊕ ℕ) (hv : v ∈ F.forest.vertices) : G.edgeTime (e v) = F.edgeTime v := by
    cases v with
    | inl j =>
      have hj : j < m := by
        simpa only [hF.vertices_eq, Freezing1.Reverse.phaseLabels,
          Finset.inl_mem_disjSum, Finset.mem_range] using hv
      change G.edgeTime (activeLabelEquiv σ (Sum.inl j)) = _
      rw [show activeLabelEquiv σ (Sum.inl j) = Sum.inl (σ ⟨j, hj⟩).val from
        activeLabelEquiv_active σ ⟨j, hj⟩]
      exact hft ⟨j, hj⟩
    | inr j =>
      change G.edgeTime (activeLabelEquiv σ (Sum.inr j)) = _
      rw [activeLabelEquiv_frozen]
      exact (hfrozen j hv).symm
  have hparents (v : ℕ ⊕ ℕ) (hv : v ∈ F.forest.vertices) :
      G.forest.parent (e v) = e (F.forest.parent v) := by
    by_cases hz : F.edgeTime v = 0
    · have hrF := (hT.root_zero v hv).mp hz
      have hrG := (hU.root_zero (e v) (hmem v hv)).mp ((htimes v hv).trans hz)
      rw [G.forest.parent_of_root hrG, F.forest.parent_of_root hrF]
    · have hr := hT.range v hv hz
      have he := hp (F.edgeTime v) (by omega) hr.2.1 hr.2.2
      rw [parentId_edgeTime hF hT hv] at he
      have hg := parentId_edgeTime hG hU (hmem v hv)
      rw [htimes v hv] at hg
      rw [hg] at he
      apply hinjG (G.forest.parent_mem _ (hmem v hv)) (hmem _ (F.forest.parent_mem _ hv))
      exact he.symm.trans (htimes _ (F.forest.parent_mem _ hv)).symm
  refine ⟨σ, ?_⟩
  apply stampedForest_eq_of_parent_time (hFN.relabel e) hGN
  · change F.forest.vertices.map e.toEmbedding = G.forest.vertices
    rw [hF.vertices_eq, hG.vertices_eq]
    exact activeLabelEquiv_map_phaseLabels x n 0 σ
  · intro v hv
    have hv' : e.symm v ∈ F.forest.vertices := by simpa [relabelActive] using hv
    change e (F.forest.parent (e.symm v)) = G.forest.parent v
    simpa only [Equiv.apply_symm_apply] using (hparents (e.symm v) hv').symm
  · intro v hv
    have hv' : e.symm v ∈ F.forest.vertices := by simpa [relabelActive] using hv
    change F.edgeTime (e.symm v) = G.edgeTime v
    simpa only [Equiv.apply_symm_apply] using (htimes (e.symm v) hv').symm

/-- Among terminal forests with the proved support and outside invariants,
the canonical fibre is exactly one active-label permutation orbit. -/
theorem canonicalForwardState_eq_iff_mem_activeOrbit
    {x : Freezing1.SignSequence} {n : ℕ} {F G : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n 0 F)
    (hO : CanonicalOrder F) (hFN : OutsideNormal F)
    (hG : Freezing1.Reverse.ValidAt x n 0 G.forest)
    (hU : Freezing1.ReverseStamped.TimesValidAt x n 0 G)
    (hP : CanonicalOrder G) (hGN : OutsideNormal G) :
    canonicalForwardState x n G = canonicalForwardState x n F ↔
      G ∈ activeOrbit (Freezing1.activeCount x n).toNat F := by
  constructor
  · intro he
    obtain ⟨hp, hf⟩ := records_eq_of_canonicalForwardState_eq hF hT hO hG hU hP he.symm
    obtain ⟨σ, hσ⟩ := exists_relabelActive_of_records hF hT hFN hG hU hGN hp hf
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  · intro he
    obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp he
    rw [← hσ]
    exact canonicalForwardState_relabelActive hF hT σ

/-- Concrete terminal support: the forest is the output of a legal length-`n`
ordered-root history. This is proved almost surely for the actual reverse law. -/
def TerminalSupported (x : Freezing1.SignSequence) (n : ℕ) (F : Forest) : Prop :=
  ∃ h : ReverseChoiceHistory.History,
    h.length = n ∧ ReverseChoiceHistory.Legal x n h ∧ ReverseChoiceHistory.state x n h = F

theorem treeLaw_terminalSupported (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n, TerminalSupported x n F :=
  ReverseChoiceHistory.treeLaw_ae_exists_legal_history x n hn

theorem TerminalSupported.invariants {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : TerminalSupported x n F) (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    Freezing1.Reverse.ValidAt x n 0 F.forest ∧
      Freezing1.ReverseStamped.TimesValidAt x n 0 F ∧ CanonicalOrder F ∧ OutsideNormal F := by
  obtain ⟨h, hlen, hh, rfl⟩ := hF
  obtain ⟨hv, ht⟩ := ReverseChoiceHistory.state_valid_of_legal x n hh hn
  simp only [hlen, Nat.sub_self] at hv ht
  exact ⟨hv, ht, state_canonicalOrder_of_legal x n hh hn, state_outsideNormal_of_legal x n hh⟩

theorem TerminalSupported.relabelActive {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : TerminalSupported x n F)
    (σ : Equiv.Perm (Fin (Freezing1.activeCount x n).toNat)) :
    TerminalSupported x n (relabelActive σ F) := by
  obtain ⟨h, hlen, hh, rfl⟩ := hF
  exact ⟨permuteHistory x n σ h, (permuteHistory_length x n σ h).trans hlen,
    legal_permuteHistory x n σ hh, state_permuteHistory x n σ h⟩

/-- The orbit/fibre equivalence specialized to genuinely reachable terminal
states; every structural premise above is discharged from the actual histories. -/
theorem canonicalForwardState_eq_iff_mem_activeOrbit_of_supported
    {x : Freezing1.SignSequence} {n : ℕ} {F G : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x)
    (hF : TerminalSupported x n F) (hG : TerminalSupported x n G) :
    canonicalForwardState x n G = canonicalForwardState x n F ↔
      G ∈ activeOrbit (Freezing1.activeCount x n).toNat F := by
  obtain ⟨hvF, htF, hoF, hnF⟩ := hF.invariants hn
  obtain ⟨hvG, htG, hoG, hnG⟩ := hG.invariants hn
  exact canonicalForwardState_eq_iff_mem_activeOrbit hvF htF hoF hnF hvG htG hoG hnG

/-- The complete reachable canonical fibre is the explicit finite orbit.
This is the set identity needed for the finite-atom probability calculation. -/
theorem terminal_fibre_eq_activeOrbit {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hF : TerminalSupported x n F) :
    {G : Forest | TerminalSupported x n G ∧
      canonicalForwardState x n G = canonicalForwardState x n F} =
      (activeOrbit (Freezing1.activeCount x n).toNat F : Set Forest) := by
  ext G
  constructor
  · rintro ⟨hG, he⟩
    exact (canonicalForwardState_eq_iff_mem_activeOrbit_of_supported hn hF hG).mp he
  · intro hG
    obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp hG
    subst G
    refine ⟨hF.relabelActive σ, ?_⟩
    obtain ⟨hv, ht, _, _⟩ := hF.invariants hn
    exact canonicalForwardState_relabelActive hv ht σ

theorem card_activeOrbit_of_supported {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) (hF : TerminalSupported x n F) :
    (activeOrbit (Freezing1.activeCount x n).toNat F).card =
      (Freezing1.activeCount x n).toNat.factorial := by
  obtain ⟨hv, ht, _, _⟩ := hF.invariants hn
  exact card_activeOrbit_of_terminal_valid hv ht

end Freezing2.ReverseStamped
