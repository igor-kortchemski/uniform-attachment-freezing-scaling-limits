module

public import Freezing2.Probability.CompanionModel
public import Freezing2.Companion.ReverseForest
public import Freezing2.Discrete.Labels

/-!
# The paper's vertex labels and the reverse construction

The companion reverse construction has zero-based active indices and frozen
indices, in the opposite summands to the paper-facing labels. This explicit
bijection preserves birth times and identifies actual forest presence; the
index shift is not suppressed in probabilistic statements.
-/

@[expose] public section

namespace Freezing2

/-- Convert the paper's one-based labels to the companion's zero-based labels. -/
def toCompanionLabel : VertexLabel → ℕ ⊕ ℕ
  | .inl i => .inr (i - 1)
  | .inr j => .inl (j - 1)

/-- Convert a companion label back to its displayed paper label. -/
def fromCompanionLabel : (ℕ ⊕ ℕ) → VertexLabel
  | .inl j => .inr (j + 1)
  | .inr i => .inl (i + 1)

@[simp] theorem to_fromCompanionLabel (v : ℕ ⊕ ℕ) :
    toCompanionLabel (fromCompanionLabel v) = v := by
  cases v <;> simp [toCompanionLabel, fromCompanionLabel]

theorem from_toCompanionLabel {x : ℕ → ℤ} {n : ℕ} {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) : fromCompanionLabel (toCompanionLabel v) = v := by
  cases v with
  | inl i =>
    have hi : 0 < i := (Finset.mem_Ioc.mp (Finset.mem_filter.mp
      (Finset.inl_mem_disjSum.mp hv)).1).1
    simp [toCompanionLabel, fromCompanionLabel, Nat.sub_add_cancel hi]
  | inr j =>
    have hj : 0 < j := (Finset.mem_Ioc.mp (Finset.inr_mem_disjSum.mp hv)).1
    simp [toCompanionLabel, fromCompanionLabel, Nat.sub_add_cancel hj]

/-- Freezing signs agree under the Boolean encoding at every used time. -/
theorem companionSchedule_false_iff (x : ℕ → ℤ) (hx : IsSigned x) {i : ℕ} (hi : 0 < i) :
    companionSchedule x i = false ↔ x i = -1 := by
  rcases hx i hi with h | h <;> simp [companionSchedule, h]

/-- The inverse label map exactly matches the two deterministic label sets. -/
theorem fromCompanionLabel_mem_iff (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) (v : ℕ ⊕ ℕ) :
    fromCompanionLabel v ∈ vertexLabels x n ↔
      v ∈ Freezing1.vertexLabels (companionSchedule x) n := by
  cases v with
  | inl j =>
    simp only [fromCompanionLabel, vertexLabels, Finset.inr_mem_disjSum,
      Finset.mem_Ioc, Freezing1.vertexLabels, Finset.inl_mem_disjSum,
      Finset.mem_range, companion_activeCount x hx]
    omega
  | inr i =>
    simp only [fromCompanionLabel, vertexLabels, Finset.inl_mem_disjSum,
      downSteps, Finset.mem_filter, Finset.mem_Ioc,
      Freezing1.vertexLabels, Finset.inr_mem_disjSum, Freezing1.frozenIndices,
      Finset.mem_range, companionSchedule_false_iff x hx (by omega : 0 < i + 1)]
    omega

theorem toCompanionLabel_mem (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ} {v : VertexLabel}
    (hv : v ∈ vertexLabels x n) :
    toCompanionLabel v ∈ Freezing1.vertexLabels (companionSchedule x) n := by
  rw [← fromCompanionLabel_mem_iff x hx, from_toCompanionLabel hv]
  exact hv

/-- An actual bijection of the finite vertex sets, not just equality of their sizes. -/
def companionVertexEquiv (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    {v // v ∈ vertexLabels x n} ≃
      {v // v ∈ Freezing1.vertexLabels (companionSchedule x) n} where
  toFun v := ⟨toCompanionLabel v, toCompanionLabel_mem x hx v.property⟩
  invFun v := ⟨fromCompanionLabel v, (fromCompanionLabel_mem_iff x hx n v).mpr v.property⟩
  left_inv v := Subtype.ext (from_toCompanionLabel v.property)
  right_inv v := Subtype.ext (to_fromCompanionLabel v)

/-- Frozen births retain the minus-one shift and active births retain time `n`. -/
@[simp] theorem companion_birthTime (n : ℕ) (v : VertexLabel) :
    Freezing1.birthTime n (toCompanionLabel v) = birthTime n v := by
  cases v <;> rfl

/-- The paper-facing birth time characterizes membership in the actual reverse
forest at every time, once its proved deterministic phase set is used. -/
theorem companion_mem_phaseLabels_iff_birthTime (x : ℕ → ℤ) (hx : IsSigned x)
    {n i : ℕ} (hi : i ≤ n) {v : VertexLabel} (hv : v ∈ vertexLabels x n) :
    toCompanionLabel v ∈ Freezing1.Reverse.phaseLabels (companionSchedule x) n i ↔
      i ≤ birthTime n v := by
  simpa only [companion_birthTime] using
    Freezing1.Reverse.mem_phaseLabels_iff_birthTime hi (toCompanionLabel_mem x hx hv)

/-- The inverse label map is injective even before restricting to a horizon. -/
theorem fromCompanionLabel_injective : Function.Injective fromCompanionLabel :=
  Function.LeftInverse.injective to_fromCompanionLabel

/-- Relabelling the companion's finite vertex set gives exactly the paper's set. -/
theorem fromCompanionLabel_image (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    (Freezing1.vertexLabels (companionSchedule x) n).image fromCompanionLabel =
      vertexLabels x n := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (fromCompanionLabel_mem_iff x hx n w).mpr hw
  · intro hv
    exact Finset.mem_image.mpr ⟨toCompanionLabel v, toCompanionLabel_mem x hx hv,
      from_toCompanionLabel hv⟩

/-- The actual uniform sampling laws are transported by the label bijection. -/
theorem map_companion_uniformVertex (x : ℕ → ℤ) (hx : IsSigned x) (n : ℕ) :
    (Freezing1.uniformVertex (companionSchedule x) n).map fromCompanionLabel =
      uniformVertex x n := by
  classical
  apply MeasureTheory.Measure.ext
  intro A hA
  rw [MeasureTheory.Measure.map_apply (measurable_of_countable _) hA]
  simp only [Freezing1.uniformVertex, uniformVertex,
    MeasureTheory.Measure.uniformOfFinset_apply]
  rw [← fromCompanionLabel_image x hx n, Finset.filter_image,
    Finset.card_image_of_injective _ fromCompanionLabel_injective,
    Finset.card_image_of_injective _ fromCompanionLabel_injective]
  rfl

end Freezing2
