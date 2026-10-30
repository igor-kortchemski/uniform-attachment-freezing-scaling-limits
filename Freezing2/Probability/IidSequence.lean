module

public import Mathlib.Probability.ProductMeasure

/-!
# Finite marginals of an iid sequence on a countable space

The source uses an infinite iid sequence of uniform vertices `V₁, V₂, …`.
Its finite marginals along distinct indices are finite iid products. In
particular a fresh coordinate is independent of a prefix of the sequence.
-/

@[expose] public section

open MeasureTheory

namespace Freezing2

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
theorem measurable_reindex {m : ℕ} (σ : Fin m → ℕ) :
    Measurable (fun (V : ℕ → α) (j : Fin m) ↦ V (σ j)) :=
  measurable_pi_iff.mpr (fun j ↦ measurable_pi_apply (σ j))

/-- Distinct coordinates of an iid sequence form an iid vector. -/
theorem infinitePi_map_reindex (μ : Measure α) [IsProbabilityMeasure μ] {m : ℕ}
    {σ : Fin m → ℕ} (hσ : Function.Injective σ) :
    (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun V j ↦ V (σ j)) =
      Measure.pi (fun _ : Fin m ↦ μ) := by
  classical
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (measurable_reindex σ) (measurableSet_singleton w)]
  let t : ℕ → Set α := fun i ↦ {a | ∀ j, σ j = i → a = w j}
  have hpre : (fun (V : ℕ → α) (j : Fin m) ↦ V (σ j)) ⁻¹' {w} =
      Set.pi (↑(Finset.univ.image σ)) t := by
    ext V
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, Set.forall_mem_range, Set.mem_ofPred_eq, t]
    constructor
    · rintro rfl j j' h
      rw [hσ h]
    · intro h
      funext j
      exact h j j rfl
  have ht (j : Fin m) : t (σ j) = {w j} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, t]
    exact ⟨fun h ↦ h j rfl, fun h j' hj' ↦ by rw [hσ hj']; exact h⟩
  rw [hpre, Measure.infinitePi_pi (fun _ : ℕ ↦ μ) (fun i _ ↦ (Set.to_countable _).measurableSet),
    Finset.prod_image (fun a _ b _ h ↦ hσ h), ← Set.univ_pi_singleton, Measure.pi_pi]
  exact Finset.prod_congr rfl (fun j _ ↦ by rw [ht j])

/-- The first `m` coordinates of an iid sequence. -/
theorem infinitePi_map_prefix (μ : Measure α) [IsProbabilityMeasure μ] (m : ℕ) :
    (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun V (j : Fin m) ↦ V j) =
      Measure.pi (fun _ : Fin m ↦ μ) :=
  infinitePi_map_reindex μ Fin.val_injective

/-- A coordinate outside the first `m` is independent of that prefix. -/
theorem infinitePi_map_fresh_prefix (μ : Measure α) [IsProbabilityMeasure μ]
    {m i : ℕ} (hi : m ≤ i) :
    (Measure.infinitePi (fun _ : ℕ ↦ μ)).map (fun V ↦ (V i, fun j : Fin m ↦ V j)) =
      μ.prod (Measure.pi (fun _ : Fin m ↦ μ)) := by
  classical
  let σ : Fin (m + 1) → ℕ := Fin.cons i (fun j : Fin m ↦ (j : ℕ))
  have hσ : Function.Injective σ := by
    refine Fin.cons_injective_iff.mpr ⟨?_, Fin.val_injective⟩
    rintro ⟨j, hj⟩
    have hj' : (j : ℕ) = i := hj
    have := j.isLt
    omega
  have hm : Measurable (fun V : ℕ → α ↦ (V i, fun j : Fin m ↦ V j)) :=
    (measurable_pi_apply i).prodMk (measurable_reindex (fun j : Fin m ↦ (j : ℕ)))
  apply Measure.ext_of_singleton
  rintro ⟨a, w⟩
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  have hpre : (fun V : ℕ → α ↦ (V i, fun j : Fin m ↦ V j)) ⁻¹' {(a, w)} =
      (fun (V : ℕ → α) (j : Fin (m + 1)) ↦ V (σ j)) ⁻¹' {Fin.cons a w} := by
    ext V
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, funext_iff,
      Fin.forall_fin_succ, σ, Fin.cons_zero, Fin.cons_succ]
  rw [hpre, ← Measure.map_apply (measurable_reindex σ) (measurableSet_singleton _),
    infinitePi_map_reindex μ hσ, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.univ_pi_singleton, ← Set.univ_pi_singleton, Measure.pi_pi, Measure.pi_pi,
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

end Freezing2
