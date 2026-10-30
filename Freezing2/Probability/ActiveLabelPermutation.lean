module

public import Freezing2.Probability.ReverseStampedTransition
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.Fintype.Perm

/-!
# Relabelling the active vertices of a stamped reverse forest

Finite permutations of the terminal active labels extend by the identity on
all frozen labels. Relabelling transports the actual parent and root maps and
the incoming timestamps. Distinct active permutations give distinct terminal
stamped forests because their canonical incoming-time identifiers are injective.
The resulting orbit has factorial cardinality. Identifying it with a canonical
forward fibre requires the separate replay comparison.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Classical ENNReal

namespace Freezing2.ReverseStamped

/-- Equality of the four data fields determines a represented rooted forest. -/
theorem rootedForest_ext {V : Type*} [DecidableEq V]
    {F G : Freezing1.RootedForest V} (hv : F.vertices = G.vertices)
    (hp : F.parent = G.parent) (hr : F.root = G.root) (hd : F.depth = G.depth) : F = G := by
  cases F
  cases G
  cases hv
  cases hp
  cases hr
  cases hd
  rfl

/-- Equality of the forest and timestamp data determines a stamped forest. -/
theorem stampedForest_ext {F G : Forest} (hf : F.forest = G.forest)
    (ht : F.edgeTime = G.edgeTime) : F = G := by
  cases F
  cases G
  cases hf
  cases ht
  rfl

/-- Relabel every vertex and transport the complete rooted-forest structure. -/
def relabelRooted {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (F : Freezing1.RootedForest V) : Freezing1.RootedForest V where
  vertices := F.vertices.map e.toEmbedding
  parent v := e (F.parent (e.symm v))
  root v := e (F.root (e.symm v))
  depth v := F.depth (e.symm v)
  parent_mem := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using F.parent_mem (e.symm v) hv'
  root_mem := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using F.root_mem (e.symm v) hv'
  root_fixed := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using congrArg e (F.root_fixed (e.symm v) hv')
  parent_root := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using congrArg e (F.parent_root (e.symm v) hv')
  root_parent := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using congrArg e (F.root_parent (e.symm v) hv')
  depth_root := by
    intro v hv
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    simpa using F.depth_root (e.symm v) hv'
  depth_parent := by
    intro v hv hn
    have hv' : e.symm v ∈ F.vertices := by simpa using hv
    have hn' : e.symm v ≠ F.root (e.symm v) := by
      intro he
      exact hn (by simpa using congrArg e he)
    simpa using F.depth_parent (e.symm v) hv' hn'

/-- Stamped relabelling keeps the edge time attached to the same child. -/
def relabel (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) : Forest :=
  ⟨relabelRooted e F.forest, fun v ↦ F.edgeTime (e.symm v)⟩

@[simp] theorem relabel_vertices (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) :
    (relabel e F).forest.vertices = F.forest.vertices.map e.toEmbedding := rfl

@[simp] theorem relabel_mem_vertices (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (v : ℕ ⊕ ℕ) :
    e v ∈ (relabel e F).forest.vertices ↔ v ∈ F.forest.vertices := by simp

@[simp] theorem relabel_edgeTime_apply (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (v : ℕ ⊕ ℕ) :
    (relabel e F).edgeTime (e v) = F.edgeTime v := by simp [relabel]

@[simp] theorem relabel_parent_apply (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (v : ℕ ⊕ ℕ) :
    (relabel e F).forest.parent (e v) = e (F.forest.parent v) := by
  simp [relabel, relabelRooted]

@[simp] theorem relabel_root_apply (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (v : ℕ ⊕ ℕ) :
    (relabel e F).forest.root (e v) = e (F.forest.root v) := by simp [relabel, relabelRooted]

@[simp] theorem relabel_depth_apply (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (v : ℕ ⊕ ℕ) :
    (relabel e F).forest.depth (e v) = F.forest.depth v := by simp [relabel, relabelRooted]

theorem relabel_roots (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) :
    (relabel e F).forest.roots = F.forest.roots.map e.toEmbedding := by
  ext v
  simp [Freezing1.RootedForest.mem_roots, relabel, relabelRooted,
    ← Equiv.symm_apply_eq]

@[simp] theorem relabel_refl (F : Forest) : relabel (Equiv.refl _) F = F := by
  apply stampedForest_ext
  · apply rootedForest_ext <;> simp [relabel, relabelRooted]
  · rfl

theorem relabel_trans (e f : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) :
    relabel f (relabel e F) = relabel (e.trans f) F := by
  apply stampedForest_ext
  · apply rootedForest_ext
    · simp [relabel, relabelRooted, Finset.map_map, Function.Embedding.trans]
    · rfl
    · rfl
    · rfl
  · rfl

/-- Relabelling commutes with the actual ordered-root merge, including its
invalid-choice fallback. -/
theorem relabel_joinChoice (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (t : ℕ)
    (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    relabel e (Freezing1.ReverseStamped.joinChoice F t p) =
      Freezing1.ReverseStamped.joinChoice (relabel e F) t (e p.1, e p.2) := by
  have hmem : (e p.1, e p.2) ∈ (relabel e F).forest.roots.offDiag ↔
      p ∈ F.forest.roots.offDiag := by
    simp [Finset.mem_offDiag, relabel_roots]
  by_cases hp : p ∈ F.forest.roots.offDiag
  · have hp' := hmem.mpr hp
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_left hp, dite_eq_left hp']
    apply stampedForest_ext
    · apply rootedForest_ext
      · rfl
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.join,
          apply_ite, Equiv.symm_apply_eq]
        split_ifs <;> simp_all
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.join, apply_ite]
        split_ifs <;> simp_all
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.join]
    · funext v
      simp [relabel, Function.update_apply, Equiv.symm_apply_eq]
  · have hp' := hmem.not.mpr hp
    simp only [Freezing1.ReverseStamped.joinChoice, dite_eq_right hp, dite_eq_right hp']

/-- A relabelling that fixes the new frozen label commutes with insertion. -/
theorem relabel_insertLabel (e : Equiv.Perm (ℕ ⊕ ℕ)) (F : Forest) (i : ℕ)
    (hi : e (Sum.inr i) = Sum.inr i) :
    relabel e (Freezing1.ReverseStamped.insertLabel F i) =
      Freezing1.ReverseStamped.insertLabel (relabel e F) i := by
  have hmem : Sum.inr i ∈ (relabel e F).forest.vertices ↔ Sum.inr i ∈ F.forest.vertices := by
    simpa only [hi] using relabel_mem_vertices e F (Sum.inr i)
  by_cases hF : Sum.inr i ∈ F.forest.vertices
  · simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_left hF, dite_eq_left (hmem.mpr hF)]
  · have hF' := hmem.not.mpr hF
    have hcond (v : ℕ ⊕ ℕ) : (e.symm v = Sum.inr i) ↔ v = Sum.inr i := by
      rw [Equiv.symm_apply_eq, hi]
    simp only [Freezing1.ReverseStamped.insertLabel, dite_eq_right hF, dite_eq_right hF']
    apply stampedForest_ext
    · apply rootedForest_ext
      · simp [relabel, relabelRooted, hi]
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.adjoin, apply_ite, hi, hcond]
        split_ifs <;> simp_all
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.adjoin, apply_ite, hi, hcond]
        split_ifs <;> simp_all
      · funext v
        simp [relabel, relabelRooted, Freezing1.RootedForest.adjoin, hcond]
    · funext v
      simp [relabel, Function.update_apply, hcond]

/-- The finite active labels use the companion's zero-based `inl` indexing. -/
def activeEmbedding (m : ℕ) : Fin m ↪ (ℕ ⊕ ℕ) :=
  ⟨fun a ↦ Sum.inl a.val, fun _ _ h ↦ Fin.ext (Sum.inl.inj h)⟩

/-- A finite active permutation fixes every other ambient label. -/
noncomputable def activeLabelEquiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    Equiv.Perm (ℕ ⊕ ℕ) := σ.viaEmbedding (activeEmbedding m)

@[simp] theorem activeLabelEquiv_active {m : ℕ} (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    activeLabelEquiv σ (Sum.inl a.val) = Sum.inl (σ a).val :=
  σ.viaEmbedding_apply (activeEmbedding m) a

@[simp] theorem activeLabelEquiv_frozen {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : ℕ) :
    activeLabelEquiv σ (Sum.inr j) = Sum.inr j := by
  apply σ.viaEmbedding_apply_of_notMem (activeEmbedding m)
  rintro ⟨a, ha⟩
  cases ha

theorem activeLabelEquiv_inactive {m : ℕ} (σ : Equiv.Perm (Fin m)) {j : ℕ}
    (hj : m ≤ j) : activeLabelEquiv σ (Sum.inl j) = Sum.inl j := by
  apply σ.viaEmbedding_apply_of_notMem (activeEmbedding m)
  rintro ⟨a, ha⟩
  have he : a.val = j := Sum.inl.inj ha
  have := a.isLt
  omega

@[simp] theorem activeLabelEquiv_symm {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (activeLabelEquiv σ).symm = activeLabelEquiv σ.symm := rfl

@[simp] theorem activeLabelEquiv_refl (m : ℕ) :
    activeLabelEquiv (Equiv.refl (Fin m)) = Equiv.refl _ := by
  change Equiv.Perm.viaEmbeddingHom (activeEmbedding m) 1 = 1
  exact map_one _

/-- The group composition law without a global action instance on forests. -/
theorem activeLabelEquiv_trans {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    (activeLabelEquiv σ).trans (activeLabelEquiv τ) = activeLabelEquiv (σ.trans τ) := by
  change Equiv.Perm.viaEmbeddingHom (activeEmbedding m) τ *
    Equiv.Perm.viaEmbeddingHom (activeEmbedding m) σ =
    Equiv.Perm.viaEmbeddingHom (activeEmbedding m) (τ * σ)
  exact (map_mul _ τ σ).symm

/-- The concrete finite active-label action on a stamped forest. -/
noncomputable def relabelActive {m : ℕ} (σ : Equiv.Perm (Fin m)) (F : Forest) : Forest :=
  relabel (activeLabelEquiv σ) F

@[simp] theorem relabelActive_refl (m : ℕ) (F : Forest) :
    relabelActive (Equiv.refl (Fin m)) F = F := by simp [relabelActive]

theorem relabelActive_trans {m : ℕ} (σ τ : Equiv.Perm (Fin m)) (F : Forest) :
    relabelActive τ (relabelActive σ F) = relabelActive (σ.trans τ) F := by
  rw [relabelActive, relabelActive, relabel_trans, activeLabelEquiv_trans]
  rfl

/-- Distinct active permutations give distinct forests whenever all active
labels are present and the canonical incoming-time IDs are injective. -/
theorem relabelActive_injective {m : ℕ} {F : Forest}
    (hactive : ∀ a : Fin m, Sum.inl a.val ∈ F.forest.vertices)
    (ht : Set.InjOn F.edgeTime (F.forest.vertices : Set (ℕ ⊕ ℕ))) :
    Function.Injective (fun σ : Equiv.Perm (Fin m) ↦ relabelActive σ F) := by
  intro σ τ he
  have hfun : σ.symm = τ.symm := by
    apply Equiv.ext
    intro a
    have htime := congrArg (fun G : Forest ↦ G.edgeTime (Sum.inl a.val)) he
    have htime' : F.edgeTime (Sum.inl (σ.symm a).val) =
        F.edgeTime (Sum.inl (τ.symm a).val) := by
      simpa [relabelActive, relabel, activeLabelEquiv_symm] using htime
    exact Fin.ext (Sum.inl.inj (ht (hactive _) (hactive _) htime'))
  simpa only [Equiv.symm_symm] using congrArg (fun e : Equiv.Perm (Fin m) ↦ e.symm) hfun

/-- The finite relabelling orbit, kept separate from the canonical fibre until
the forward replay comparison has been proved. -/
noncomputable def activeOrbit (m : ℕ) (F : Forest) : Finset Forest :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin m) ↦ relabelActive σ F)

theorem card_activeOrbit {m : ℕ} {F : Forest}
    (hactive : ∀ a : Fin m, Sum.inl a.val ∈ F.forest.vertices)
    (ht : Set.InjOn F.edgeTime (F.forest.vertices : Set (ℕ ⊕ ℕ))) :
    (activeOrbit m F).card = m.factorial := by
  rw [activeOrbit, Finset.card_image_of_injective _ (relabelActive_injective hactive ht)]
  simp [Fintype.card_perm]

/-- Exact terminal schedule support supplies both hypotheses of freeness. -/
theorem card_activeOrbit_of_terminal_valid {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (hT : Freezing1.ReverseStamped.TimesValidAt x n 0 F) :
    (activeOrbit (Freezing1.activeCount x n).toNat F).card =
      (Freezing1.activeCount x n).toNat.factorial := by
  have hone : F.forest.roots.card = 1 := by
    simpa only [Freezing1.activeCount_zero, Int.toNat_one] using hF.roots_card
  apply card_activeOrbit
  · intro a
    rw [hF.vertices_eq]
    simpa [Freezing1.Reverse.phaseLabels] using a.isLt
  · intro u hu v hv he
    exact hT.edgeTime_injective_of_one_root hone u hu v hv he

/-- The factorial orbit cardinality holds under the genuine stamped terminal
law, including a horizon exactly at extinction and the case of no active labels. -/
theorem treeLaw_activeOrbit_card (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n,
      (activeOrbit (Freezing1.activeCount x n).toNat F).card =
        (Freezing1.activeCount x n).toNat.factorial := by
  filter_upwards [Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
    Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl] with F hT hF
  simp only [Nat.sub_self] at hF
  exact card_activeOrbit_of_terminal_valid hF hT

end Freezing2.ReverseStamped
