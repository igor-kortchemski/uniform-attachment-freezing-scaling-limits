module

public import Freezing2.Probability.CanonicalForwardReplay
public import Freezing2.Probability.ForwardReplayState

/-!
# The canonical replay preserves the actual finite tree

Incoming timestamps give a bijection between the reverse vertices and the
forward birth identifiers. Under this bijection the graph edges agree exactly.
Thus the canonical map represents the source tree after active-label erasure,
not merely an unrelated legal forward state.
-/

@[expose] public section

open scoped Classical

namespace Freezing2.ReverseStamped

theorem canonicalForwardState_vertices {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    (canonicalForwardState x n F).vertices = F.forest.vertices.image F.edgeTime := by
  ext v
  change v ∈ (ForwardHistory.state x (ForwardReplay.history x (parentId F) (frozenId F) n)).vertices ↔ _
  rw [ForwardReplay.vertices_history _ _ _ _ (canonicalHistory_legal hF ht ho),
    ht.edgeTime_image_of_one_root (one_root_of_terminal_valid hF)]
  simp only [ForwardReplay.Born, Finset.mem_insert, Freezing1.ReverseStamped.attachmentTimes,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro (hzero | ⟨hv0, hvn, hx⟩)
    · exact Or.inl hzero
    · exact Or.inr ⟨⟨by omega, hvn⟩, hx⟩
  · rintro (hzero | ⟨⟨hv0, hvn⟩, hx⟩)
    · exact Or.inl hzero
    · exact Or.inr ⟨by omega, hvn, hx⟩

/-- The extracted parent identifier agrees with the actual reverse parent
under the canonical vertex bijection. -/
theorem canonicalForwardState_parent_time {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) (hv0 : F.edgeTime v ≠ 0) :
    (canonicalForwardState x n F).parent (F.edgeTime v) = F.edgeTime (F.forest.parent v) := by
  have hr := ht.range v hv hv0
  rw [canonicalForwardState_parent hF ht ho (by omega) hr.2.1 hr.2.2,
    parentId_edgeTime hF ht hv]

/-- Adjacency is preserved in both directions, with all vertices retained. -/
theorem canonicalForwardState_adj_iff {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.forest.vertices) (hv : v ∈ F.forest.vertices) :
    (canonicalForwardState x n F).graph.Adj (F.edgeTime u) (F.edgeTime v) ↔
      F.forest.graph.Adj u v := by
  have hinj := ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF)
  change (ForwardHistory.state x (ForwardReplay.history x (parentId F) (frozenId F) n)).graph.Adj _ _ ↔ _
  rw [ForwardReplay.graph_adj_history _ _ _ _ (canonicalHistory_legal hF ht ho)]
  constructor
  · rintro ⟨t, ht0, htn, hxt, he⟩
    obtain ⟨hw, htime⟩ := attachment_vertex_spec hF ht ht0 htn hxt
    have hp := F.forest.parent_mem _ hw
    have hne : u ≠ v := fun huv ↦ (SimpleGraph.Adj.ne he) (congrArg F.edgeTime huv)
    have he' : (F.edgeTime u = parentId F t ∧ F.edgeTime v = t) ∨
        (F.edgeTime u = t ∧ F.edgeTime v = parentId F t) := by
      simpa only [SimpleGraph.edge_adj, and_iff_left (SimpleGraph.Adj.ne he)] using he
    rcases he' with ⟨hup, hvt⟩ | ⟨hut, hvp⟩
    · have hvw := hinj _ hv _ hw (hvt.trans htime.symm)
      have hup' : u = F.forest.parent (vertexOfTime F t) := hinj _ hu _ hp hup
      exact ⟨hu, hv, hne, Or.inr (by rw [hvw, hup'])⟩
    · have huw := hinj _ hu _ hw (hut.trans htime.symm)
      have hvp' : v = F.forest.parent (vertexOfTime F t) := hinj _ hv _ hp hvp
      exact ⟨hu, hv, hne, Or.inl (by rw [huw, hvp'])⟩
  · rintro ⟨_, _, hne, hpar | hpar⟩
    · have hu0 : F.edgeTime u ≠ 0 := by
        intro hz
        have hr := (ht.root_zero u hu).mp hz
        have hp := F.forest.parent_of_root hr
        exact hne (hp.symm.trans hpar)
      have hr := ht.range u hu hu0
      refine ⟨F.edgeTime u, by omega, hr.2.1, hr.2.2, ?_⟩
      rw [parentId_edgeTime hF ht hu, hpar]
      have hnid : F.edgeTime u ≠ F.edgeTime v := fun he ↦ hne (hinj _ hu _ hv he)
      simp [SimpleGraph.edge_adj, hnid]
    · have hv0 : F.edgeTime v ≠ 0 := by
        intro hz
        have hr := (ht.root_zero v hv).mp hz
        have hp := F.forest.parent_of_root hr
        exact hne (hpar.symm.trans hp)
      have hr := ht.range v hv hv0
      refine ⟨F.edgeTime v, by omega, hr.2.1, hr.2.2, ?_⟩
      rw [parentId_edgeTime hF ht hv, hpar]
      have hnid : F.edgeTime u ≠ F.edgeTime v := fun he ↦ hne (hinj _ hu _ hv he)
      simp [SimpleGraph.edge_adj, hnid]

/-- The finite vertex bijection uses the actual incoming-edge timestamps. -/
noncomputable def canonicalVertexEquiv {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    {v // v ∈ F.forest.vertices} ≃ {v // v ∈ (canonicalForwardState x n F).vertices} :=
  Equiv.ofBijective (fun v ↦ ⟨F.edgeTime v, by
    rw [canonicalForwardState_vertices hF ht ho]
    exact Finset.mem_image.mpr ⟨v, v.property, rfl⟩⟩) (by
      constructor
      · intro u v he
        apply Subtype.ext
        exact ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF)
          _ u.property _ v.property (congrArg Subtype.val he)
      · intro v
        have hv : (v : ℕ) ∈ F.forest.vertices.image F.edgeTime := by
          simpa only [canonicalForwardState_vertices hF ht ho] using v.property
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
        exact ⟨⟨u, hu⟩, Subtype.ext he⟩)

/-- The canonical map preserves the complete finite graph; active-label
permutations change only the names of its reverse vertices. -/
noncomputable def canonicalTreeIso {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    F.forest.toGraph ≃g (canonicalForwardState x n F).tree where
  toEquiv := canonicalVertexEquiv hF ht ho
  map_rel_iff' := by
    intro u v
    exact canonicalForwardState_adj_iff hF ht ho u.property v.property

/-- A reverse frozen label `inr j` is the forward label `j+1`, at the same
vertex under the canonical bijection. -/
theorem canonicalForwardState_frozen_label {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {j : ℕ} (hj : Sum.inr j ∈ F.forest.vertices) :
    (canonicalForwardState x n F).frozenAt (F.edgeTime (Sum.inr j)) = some (j + 1) := by
  have hj' := hj
  rw [hF.vertices_eq] at hj'
  have hdata : j < n ∧ x (j + 1) = false := by
    simpa [Freezing1.Reverse.phaseLabels] using hj'
  apply (canonicalForwardState_frozen_iff hF ht ho (by omega) (by omega) hdata.2).mpr
  simp [frozenId]

/-- Every reverse active label remains active in the canonical forward tree;
its numerical active index contributes no additional source label. -/
theorem canonicalForwardState_active_label {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {j : ℕ} (hj : Sum.inl j ∈ F.forest.vertices) :
    F.edgeTime (Sum.inl j) ∈ (canonicalForwardState x n F).active := by
  have hactive := (ForwardReplay.legal_and_active x n (parentId F) (frozenId F)
    (fun _ h0 hn hx ↦ parentId_born hF ht ho h0 hn hx)
    (fun _ h0 hn hx ↦ frozenId_born hF ht ho h0 hn hx)
    (fun _ h0 hn hx _ hs hst hxs ↦ parentId_not_previously_frozen hF ht ho h0 hn hx hs hst hxs)
    (frozenId_injOn hF ht) n le_rfl).2 (F.edgeTime (Sum.inl j))
  apply hactive.mpr
  constructor
  · apply time_born ht hj
    by_cases hz : F.edgeTime (Sum.inl j) = 0
    · simp [hz]
    · exact (ht.range _ hj hz).2.1
  · intro s hs0 hsn hxs he
    have hsV := frozenLabel_mem hF hs0 hsn hxs
    have hlabel := ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF)
      _ hsV _ hj he
    cases hlabel

/-- The active/frozen status agrees exactly after forgetting only active indices. -/
theorem canonicalForwardState_active_iff {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {v : ℕ ⊕ ℕ} (hv : v ∈ F.forest.vertices) :
    F.edgeTime v ∈ (canonicalForwardState x n F).active ↔ ∃ j, v = Sum.inl j := by
  cases v with
  | inl j => simp [canonicalForwardState_active_label hF ht ho hv]
  | inr j =>
    have hV : F.edgeTime (Sum.inr j) ∈ (canonicalForwardState x n F).vertices := by
      rw [canonicalForwardState_vertices hF ht ho]
      exact Finset.mem_image.mpr ⟨_, hv, rfl⟩
    have hvalid := ForwardHistory.state_valid x (canonicalHistory x n F)
    have hiff := hvalid.active_iff _ hV
    have hf := canonicalForwardState_frozen_label hF ht ho hv
    simp only [Sum.inr_ne_inl, exists_false, iff_false]
    intro ha
    have hn := hiff.mp ha
    change (canonicalForwardState x n F).frozenAt (F.edgeTime (Sum.inr j)) = none at hn
    rw [hf] at hn
    cases hn

end Freezing2.ReverseStamped
