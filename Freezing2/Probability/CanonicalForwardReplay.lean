module

public import Freezing2.Probability.ForwardReplay
public import Freezing2.Probability.ReverseCanonicalOrder

/-!
# Canonical forward replay of the actual stamped reverse tree

Incoming edge times are the persistent forward birth identifiers; the unique
root has identifier zero. A frozen label `inr j` is frozen at time `j+1`.
The proved reverse timestamp order makes every extracted forward choice legal.
-/

@[expose] public section

open MeasureTheory
open scoped Classical

namespace Freezing2.ReverseStamped

/-- Invert an incoming timestamp on the finite vertex set. The fallback is
unused for every actual birth identifier. -/
noncomputable def vertexOfTime (F : Forest) (t : ℕ) : ℕ ⊕ ℕ :=
  if h : ∃ v ∈ F.forest.vertices, F.edgeTime v = t then Classical.choose h else Sum.inl 0

theorem vertexOfTime_spec {F : Forest} {t : ℕ}
    (ht : t ∈ F.forest.vertices.image F.edgeTime) :
    vertexOfTime F t ∈ F.forest.vertices ∧ F.edgeTime (vertexOfTime F t) = t := by
  have he : ∃ v ∈ F.forest.vertices, F.edgeTime v = t := Finset.mem_image.mp ht
  simp only [vertexOfTime, dite_eq_left he]
  exact Classical.choose_spec he

/-- Parent identifier read from the terminal stamped tree. -/
noncomputable def parentId (F : Forest) (t : ℕ) : ℕ :=
  F.edgeTime (F.forest.parent (vertexOfTime F t))

/-- The forward identifier of the prescribed vertex frozen at time `s`. -/
def frozenId (F : Forest) (s : ℕ) : ℕ := F.edgeTime (Sum.inr (s - 1))

noncomputable def canonicalHistory (x : Freezing1.SignSequence) (n : ℕ) (F : Forest) :
    ForwardHistory.History := ForwardReplay.history x (parentId F) (frozenId F) n

/-- A total measurable map to the actual forward state representation, defined
by replaying the records carried by the stamped reverse forest. -/
noncomputable def canonicalForwardState (x : Freezing1.SignSequence) (n : ℕ)
    (F : Forest) : Freezing1.Forward.State := ForwardHistory.state x (canonicalHistory x n F)

@[simp] theorem canonicalHistory_length (x : Freezing1.SignSequence) (n : ℕ) (F : Forest) :
    (canonicalHistory x n F).length = n := ForwardReplay.history_length _ _ _ _

theorem one_root_of_terminal_valid {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest) : F.forest.roots.card = 1 := by
  simpa only [Freezing1.activeCount_zero, Int.toNat_one] using hF.roots_card

theorem frozenLabel_mem {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest) {s : ℕ}
    (hs0 : 1 ≤ s) (hsn : s ≤ n) (hxs : x s = false) :
    Sum.inr (s - 1) ∈ F.forest.vertices := by
  rw [hF.vertices_eq]
  have he : s - 1 + 1 = s := by omega
  simp [Freezing1.Reverse.phaseLabels, he, hxs, show s - 1 < n by omega]

theorem time_born {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) {v : ℕ ⊕ ℕ}
    (hv : v ∈ F.forest.vertices) {k : ℕ} (hk : F.edgeTime v ≤ k) :
    ForwardReplay.Born x k (F.edgeTime v) := by
  by_cases hz : F.edgeTime v = 0
  · exact Or.inl hz
  · have hr := ht.range v hv hz
    exact Or.inr ⟨by omega, hk, hr.2.2⟩

theorem attachment_vertex_spec {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) {t : ℕ}
    (ht0 : 1 ≤ t) (htn : t ≤ n) (hxt : x t = true) :
    vertexOfTime F t ∈ F.forest.vertices ∧ F.edgeTime (vertexOfTime F t) = t := by
  apply vertexOfTime_spec
  rw [ht.edgeTime_image_of_one_root (one_root_of_terminal_valid hF)]
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, htn⟩, hxt⟩

/-- The finite timestamp inverse recovers each actual vertex, including the
unique root with identifier zero. -/
theorem vertexOfTime_edgeTime {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) {v : ℕ ⊕ ℕ}
    (hv : v ∈ F.forest.vertices) : vertexOfTime F (F.edgeTime v) = v := by
  obtain ⟨hw, he⟩ := vertexOfTime_spec (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  exact ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF) _ hw _ hv he

theorem parentId_edgeTime {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) {v : ℕ ⊕ ℕ}
    (hv : v ∈ F.forest.vertices) :
    parentId F (F.edgeTime v) = F.edgeTime (F.forest.parent v) := by
  simp only [parentId, vertexOfTime_edgeTime hF ht hv]

/-- The extracted forward parent was born before its child. -/
theorem parentId_born {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {t : ℕ} (ht0 : 1 ≤ t) (htn : t ≤ n) (hxt : x t = true) :
    ForwardReplay.Born x (t - 1) (parentId F t) := by
  obtain ⟨hv, he⟩ := attachment_vertex_spec hF ht ht0 htn hxt
  have hp := F.forest.parent_mem _ hv
  apply time_born ht hp
  have hlt := ho.parent_lt _ hv (by rw [he]; omega)
  change F.edgeTime (F.forest.parent (vertexOfTime F t)) ≤ t - 1
  omega

/-- The extracted frozen vertex was born strictly before its freezing time. -/
theorem frozenId_born {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {s : ℕ} (hs0 : 1 ≤ s) (hsn : s ≤ n) (hxs : x s = false) :
    ForwardReplay.Born x (s - 1) (frozenId F s) :=
  time_born ht (frozenLabel_mem hF hs0 hsn hxs)
    (ho.frozen_le _ (frozenLabel_mem hF hs0 hsn hxs))

/-- Distinct freezing times select distinct canonical vertex identifiers. -/
theorem frozenId_injOn {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) :
    Set.InjOn (frozenId F) {s | 1 ≤ s ∧ s ≤ n ∧ x s = false} := by
  intro s hs t ht' he
  have hsV := frozenLabel_mem hF hs.1 hs.2.1 hs.2.2
  have htV := frozenLabel_mem hF ht'.1 ht'.2.1 ht'.2.2
  have hlabel := ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF)
    _ hsV _ htV he
  have hidx : s - 1 = t - 1 := Sum.inr.inj hlabel
  have hs0 : 1 ≤ s := hs.1
  have ht0 : 1 ≤ t := ht'.1
  omega

/-- No earlier freezing record removes an extracted attachment parent.
This is where the source condition on *all* incident edges is essential. -/
theorem parentId_not_previously_frozen {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {t : ℕ} (ht0 : 1 ≤ t) (htn : t ≤ n) (hxt : x t = true)
    {s : ℕ} (hs0 : 1 ≤ s) (hst : s < t) (hxs : x s = false) :
    frozenId F s ≠ parentId F t := by
  intro he
  obtain ⟨hv, htime⟩ := attachment_vertex_spec hF ht ht0 htn hxt
  have hsV := frozenLabel_mem hF hs0 (by omega) hxs
  have hpV := F.forest.parent_mem _ hv
  have hlabel := ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF)
    _ hsV _ hpV he
  have hbound := ho.frozen_parent_le _ hv _ hlabel.symm
  omega

/-- Every actual-source compatible stamped terminal tree yields a legal
forward history. The necessary ordering and support facts are explicit and
are proved almost surely for the actual reverse process below. -/
theorem canonicalHistory_legal {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    ForwardHistory.Legal x (canonicalHistory x n F) :=
  (ForwardReplay.legal_and_active x n (parentId F) (frozenId F)
    (fun _ h0 hn hx ↦ parentId_born hF ht ho h0 hn hx)
    (fun _ h0 hn hx ↦ frozenId_born hF ht ho h0 hn hx)
    (fun _ h0 hn hx _ hs hst hxs ↦ parentId_not_previously_frozen hF ht ho h0 hn hx hs hst hxs)
    (frozenId_injOn hF ht) n le_rfl).1

/-- The actual canonical image is supported on genuine legal forward histories. -/
theorem treeLaw_canonicalHistory_legal (x : Freezing1.SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n, ForwardHistory.Legal x (canonicalHistory x n F) := by
  filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
    Freezing1.ReverseStamped.treeLaw_times_valid x n hn,
    treeLaw_canonicalOrder x n hn] with F hF ht ho
  exact canonicalHistory_legal (by simpa only [Nat.sub_self] using hF) ht ho

/-- Every prescribed attachment record is visible in the canonical forward state. -/
theorem canonicalForwardState_parent {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {t : ℕ} (ht0 : 1 ≤ t) (htn : t ≤ n) (hxt : x t = true) :
    (canonicalForwardState x n F).parent t = parentId F t := by
  have he := ForwardHistory.parent_eq_choiceAt x (canonicalHistory_legal hF ht ho)
    ht0 (by simpa only [canonicalHistory_length] using htn) hxt
  simpa only [canonicalForwardState, canonicalHistory, ForwardReplay.choiceAt_history _ _ _ _ ht0 htn,
    ForwardReplay.choice, hxt, ite_true] using he

/-- Every prescribed freezing record is visible in the canonical forward state. -/
theorem canonicalForwardState_frozen_iff {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    {s v : ℕ} (hs0 : 1 ≤ s) (hsn : s ≤ n) (hxs : x s = false) :
    (canonicalForwardState x n F).frozenAt v = some s ↔ frozenId F s = v := by
  have he := ForwardHistory.frozenAt_eq_some_iff_choiceAt x (canonicalHistory_legal hF ht ho)
    (v := v) hs0 (by simpa only [canonicalHistory_length] using hsn) hxs
  simpa only [canonicalForwardState, canonicalHistory, ForwardReplay.choiceAt_history _ _ _ _ hs0 hsn,
    ForwardReplay.choice, hxs, Bool.false_eq_true, ite_false] using he

/-- Equality of the source-relevant records suffices for equality of the total
canonical replay, independent of unused fallback values. -/
theorem canonicalForwardState_eq_of_records {x : Freezing1.SignSequence} {n : ℕ}
    {F G : Forest}
    (hp : ∀ t, 1 ≤ t → t ≤ n → x t = true → parentId F t = parentId G t)
    (hf : ∀ t, 1 ≤ t → t ≤ n → x t = false → frozenId F t = frozenId G t) :
    canonicalForwardState x n F = canonicalForwardState x n G := by
  apply congrArg (ForwardHistory.state x)
  apply ForwardHistory.eq_of_choiceAt_eq (by simp)
  intro t ht0 htn
  have htn' : t ≤ n := by simpa only [canonicalHistory_length] using htn
  simp only [canonicalHistory, ForwardReplay.choiceAt_history _ _ _ _ ht0 htn']
  cases hx : x t with
  | true => simpa [ForwardReplay.choice, hx] using hp t ht0 htn' hx
  | false => simpa [ForwardReplay.choice, hx] using hf t ht0 htn' hx

/-- Conversely, equal canonical states have equal source-relevant parent and
freezing records. This is the record interface for the active-label fibres. -/
theorem records_eq_of_canonicalForwardState_eq {x : Freezing1.SignSequence} {n : ℕ}
    {F G : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F)
    (hG : Freezing1.Reverse.ValidAt x n 0 G.forest)
    (gt : Freezing1.ReverseStamped.TimesValidAt x n 0 G) (go : CanonicalOrder G)
    (he : canonicalForwardState x n F = canonicalForwardState x n G) :
    (∀ t, 1 ≤ t → t ≤ n → x t = true → parentId F t = parentId G t) ∧
      (∀ t, 1 ≤ t → t ≤ n → x t = false → frozenId F t = frozenId G t) := by
  constructor
  · intro t ht0 htn hxt
    rw [← canonicalForwardState_parent hF ht ho ht0 htn hxt,
      ← canonicalForwardState_parent hG gt go ht0 htn hxt, he]
  · intro t ht0 htn hxt
    have hf : (canonicalForwardState x n F).frozenAt (frozenId F t) = some t :=
      (canonicalForwardState_frozen_iff hF ht ho ht0 htn hxt).mpr rfl
    rw [he] at hf
    exact ((canonicalForwardState_frozen_iff hG gt go ht0 htn hxt).mp hf).symm

end Freezing2.ReverseStamped
