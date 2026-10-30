module

public import Freezing2.Probability.CoalescenceHistory
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# The coalescence-time distance used by critical chaining

This is the quantity `Δ` at source lines 1496–1502. Real subtraction is used
in `(birth u + birth v - 2 * coal u v) / 2`. Nested connected components give
the triangle inequality. On the actual finite vertex set, distinct vertices
coalesce strictly below their common birth, so the distance even separates
points. Set distances below require an explicitly nonempty finite set.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Classical

namespace Freezing2.ReverseCoalescence

open Freezing1 Freezing2.ReverseHistory

theorem coalescenceTime_comm (n : ℕ) (u v : Label) (ω : History) :
    coalescenceTime n u v ω = coalescenceTime n v u ω := by
  unfold coalescenceTime
  apply congrArg (fun s : Finset ℕ ↦ s.sup id)
  ext i
  simp only [Finset.mem_filter, Finset.mem_Iic]
  constructor <;> rintro ⟨hi, hc⟩
  · exact ⟨by simpa only [commonBirth, min_comm] using hi, hc.symm⟩
  · exact ⟨by simpa only [commonBirth, min_comm] using hi, hc.symm⟩

/-- Two connections through a common vertex give a connection at the smaller
of their coalescence phases. All three vertices are sampled from the actual
deterministic terminal label set. -/
theorem jointLaw_min_coalescenceTime_le {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v w : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (hw : w ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n,
      min (coalescenceTime n u v ω) (coalescenceTime n v w ω) ≤
        coalescenceTime n u w ω := by
  filter_upwards [jointLaw_connected_iff_le_coalescenceTime hn hu hv,
    jointLaw_connected_iff_le_coalescenceTime hn hv hw] with ω huv hvw
  let t := min (coalescenceTime n u v ω) (coalescenceTime n v w ω)
  have htu : t ≤ commonBirth n u v :=
    (min_le_left _ _).trans (coalescenceTime_le_commonBirth n u v ω)
  have htw : t ≤ commonBirth n v w :=
    (min_le_right _ _).trans (coalescenceTime_le_commonBirth n v w ω)
  apply le_coalescenceTime_of_connected
  · exact le_min (htu.trans (min_le_left _ _)) (htw.trans (min_le_right _ _))
  · exact Eq.trans ((huv t htu).mpr (min_le_left _ _))
      ((hvw t htw).mpr (min_le_right _ _))

/-- The source's time-based distance, retaining real subtraction and the factor one half. -/
noncomputable def coalescenceDistance (n : ℕ) (u v : Label) (ω : History) : ℝ :=
  ((Freezing1.birthTime n u : ℝ) + Freezing1.birthTime n v -
    2 * (coalescenceTime n u v ω : ℝ)) / 2

@[simp] theorem coalescenceDistance_self (n : ℕ) (u : Label) (ω : History) :
    coalescenceDistance n u u ω = 0 := by
  simp only [coalescenceDistance, coalescenceTime_self]
  ring

theorem coalescenceDistance_comm (n : ℕ) (u v : Label) (ω : History) :
    coalescenceDistance n u v ω = coalescenceDistance n v u ω := by
  rw [coalescenceDistance, coalescenceDistance, coalescenceTime_comm n u v]
  ring

theorem coalescenceDistance_nonneg (n : ℕ) (u v : Label) (ω : History) :
    0 ≤ coalescenceDistance n u v ω := by
  have hc := coalescenceTime_le_commonBirth n u v ω
  have hnat : 2 * coalescenceTime n u v ω ≤ Freezing1.birthTime n u + Freezing1.birthTime n v := by
    dsimp [commonBirth] at hc
    omega
  have hr : 2 * (coalescenceTime n u v ω : ℝ) ≤
      (Freezing1.birthTime n u : ℝ) + Freezing1.birthTime n v := by exact_mod_cast hnat
  unfold coalescenceDistance
  linarith

theorem measurable_coalescenceDistance (n : ℕ) (u v : Label) :
    Measurable (coalescenceDistance n u v) := by
  have hc := measurable_coalescenceTime n u v
  unfold coalescenceDistance
  fun_prop

/-- U30: the triangle inequality follows from the proved nested actual
coalescence geometry; it is not a new condition imposed on the history law. -/
theorem jointLaw_coalescenceDistance_triangle {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v w : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (hw : w ∈ Freezing1.vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw x n, coalescenceDistance n u w ω ≤
      coalescenceDistance n u v ω + coalescenceDistance n v w ω := by
  filter_upwards [jointLaw_min_coalescenceTime_le hn hu hv hw] with ω hm
  have huv := (coalescenceTime_le_commonBirth n u v ω).trans (min_le_right _ _)
  have hvw := (coalescenceTime_le_commonBirth n v w ω).trans (min_le_left _ _)
  have hnat : coalescenceTime n u v ω + coalescenceTime n v w ω ≤
      coalescenceTime n u w ω + Freezing1.birthTime n v := by omega
  have hr : (coalescenceTime n u v ω : ℝ) + coalescenceTime n v w ω ≤
      (coalescenceTime n u w ω : ℝ) + Freezing1.birthTime n v := by exact_mod_cast hnat
  unfold coalescenceDistance
  linarith

/-- The possible zero phase causes no degeneracy between distinct present
vertices: the actual strict common-birth bound gives positive distance. -/
theorem jointLaw_coalescenceDistance_pos {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) {u v : Label}
    (hu : u ∈ Freezing1.vertexLabels x n) (hv : v ∈ Freezing1.vertexLabels x n)
    (huv : u ≠ v) :
    ∀ᵐ ω ∂jointLaw x n, 0 < coalescenceDistance n u v ω := by
  filter_upwards [jointLaw_coalescenceTime_lt_commonBirth hn hu hv huv] with ω hc
  have hnat : 2 * coalescenceTime n u v ω < Freezing1.birthTime n u + Freezing1.birthTime n v := by
    dsimp [commonBirth] at hc
    omega
  have hr : 2 * (coalescenceTime n u v ω : ℝ) <
      (Freezing1.birthTime n u : ℝ) + Freezing1.birthTime n v := by exact_mod_cast hnat
  unfold coalescenceDistance
  linarith

/-- The entire actual finite vertex set simultaneously carries the source
distance as a genuine metric. No claim is made for arbitrary invalid labels
or arbitrary histories outside the full-measure event. -/
theorem jointLaw_exists_coalescenceMetric (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ ω ∂jointLaw x n, ∃ m : MetricSpace {u // u ∈ Freezing1.vertexLabels x n},
      ∀ u v, @dist _ m.toDist u v = coalescenceDistance n u.val v.val ω := by
  let V := {u // u ∈ Freezing1.vertexLabels x n}
  have htri : ∀ᵐ ω ∂jointLaw x n, ∀ u v w : V,
      coalescenceDistance n u.val w.val ω ≤
        coalescenceDistance n u.val v.val ω + coalescenceDistance n v.val w.val ω := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro w
    exact jointLaw_coalescenceDistance_triangle hn u.property v.property w.property
  have hsep : ∀ᵐ ω ∂jointLaw x n, ∀ u v : V,
      u ≠ v → 0 < coalescenceDistance n u.val v.val ω := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    by_cases huv : u = v
    · exact Eventually.of_forall fun _ h ↦ False.elim (h huv)
    · exact (jointLaw_coalescenceDistance_pos hn u.property v.property
        (fun he ↦ huv (Subtype.ext he))).mono fun _ h _ ↦ h
  filter_upwards [htri, hsep] with ω ht hs
  let m : MetricSpace V :=
    { dist u v := coalescenceDistance n u.val v.val ω
      dist_self u := coalescenceDistance_self n u.val ω
      dist_comm u v := coalescenceDistance_comm n u.val v.val ω
      dist_triangle := ht
      eq_of_dist_eq_zero := by
        intro u v he
        by_contra huv
        exact (ne_of_gt (hs u v huv)) he }
  exact ⟨m, fun _ _ ↦ rfl⟩

end Freezing2.ReverseCoalescence

namespace Freezing2

open ReverseHistory ReverseCoalescence

/-- The same distance in the manuscript's one-based label convention. -/
noncomputable def sourceCoalescenceDistance (n : ℕ) (u v : VertexLabel) (ω : History) : ℝ :=
  coalescenceDistance n (toCompanionLabel u) (toCompanionLabel v) ω

theorem sourceCoalescenceDistance_eq_formula (n : ℕ) (u v : VertexLabel) (ω : History) :
    sourceCoalescenceDistance n u v ω =
      ((birthTime n u : ℝ) + birthTime n v - 2 * (sourceCoalescenceTime n u v ω : ℝ)) / 2 := by
  simp only [sourceCoalescenceDistance, coalescenceDistance, companion_birthTime,
    sourceCoalescenceTime]

@[simp] theorem sourceCoalescenceDistance_self (n : ℕ) (u : VertexLabel) (ω : History) :
    sourceCoalescenceDistance n u u ω = 0 := coalescenceDistance_self _ _ _

theorem sourceCoalescenceDistance_comm (n : ℕ) (u v : VertexLabel) (ω : History) :
    sourceCoalescenceDistance n u v ω = sourceCoalescenceDistance n v u ω :=
  coalescenceDistance_comm _ _ _ _

theorem sourceCoalescenceDistance_nonneg (n : ℕ) (u v : VertexLabel) (ω : History) :
    0 ≤ sourceCoalescenceDistance n u v ω := coalescenceDistance_nonneg _ _ _ _

theorem measurable_sourceCoalescenceDistance (n : ℕ) (u v : VertexLabel) :
    Measurable (sourceCoalescenceDistance n u v) := measurable_coalescenceDistance _ _ _

theorem jointLaw_sourceCoalescenceDistance_triangle (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x)) {u v w : VertexLabel}
    (hu : u ∈ vertexLabels x n) (hv : v ∈ vertexLabels x n) (hw : w ∈ vertexLabels x n) :
    ∀ᵐ ω ∂jointLaw (companionSchedule x) n, sourceCoalescenceDistance n u w ω ≤
      sourceCoalescenceDistance n u v ω + sourceCoalescenceDistance n v w ω :=
  jointLaw_coalescenceDistance_triangle hn (toCompanionLabel_mem x hx hu)
    (toCompanionLabel_mem x hx hv) (toCompanionLabel_mem x hx hw)

/-- Set distance has a minimum only for a nonempty sample set, as required
by the source definition. No empty-set default is used. -/
noncomputable def sourceCoalescenceSetDistance (n : ℕ) (u : VertexLabel)
    (B : Finset VertexLabel) (hB : B.Nonempty) (ω : History) : ℝ :=
  B.inf' hB (fun v ↦ sourceCoalescenceDistance n u v ω)

theorem sourceCoalescenceSetDistance_attained (n : ℕ) (u : VertexLabel)
    (B : Finset VertexLabel) (hB : B.Nonempty) (ω : History) :
    ∃ v ∈ B, sourceCoalescenceSetDistance n u B hB ω = sourceCoalescenceDistance n u v ω :=
  Finset.exists_mem_eq_inf' hB _

theorem sourceCoalescenceSetDistance_le (n : ℕ) (u : VertexLabel)
    (B : Finset VertexLabel) (hB : B.Nonempty) (ω : History) {v : VertexLabel} (hv : v ∈ B) :
    sourceCoalescenceSetDistance n u B hB ω ≤ sourceCoalescenceDistance n u v ω :=
  Finset.inf'_le _ hv

theorem sourceCoalescenceSetDistance_nonneg (n : ℕ) (u : VertexLabel)
    (B : Finset VertexLabel) (hB : B.Nonempty) (ω : History) :
    0 ≤ sourceCoalescenceSetDistance n u B hB ω := by
  apply Finset.le_inf'
  intro v _
  exact sourceCoalescenceDistance_nonneg _ _ _ _

theorem measurable_sourceCoalescenceSetDistance (n : ℕ) (u : VertexLabel)
    (B : Finset VertexLabel) (hB : B.Nonempty) :
    Measurable (sourceCoalescenceSetDistance n u B hB) := by
  have hm : Measurable (B.inf' hB (fun v ↦ sourceCoalescenceDistance n u v)) :=
    Finset.inf'_induction hB _ (fun _ hf _ hg ↦ hf.inf hg)
      (fun v _ ↦ measurable_sourceCoalescenceDistance n u v)
  convert hm using 1
  funext ω
  exact (Finset.inf'_apply hB _ _).symm

end Freezing2
