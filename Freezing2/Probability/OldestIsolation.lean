module

public import Freezing2.Probability.TrackedIsolation

/-!
# The oldest marked component and the actual expected component count

The birth-order isolation comparison is summed over the fixed marked set.
On a phase where every marked vertex is present, distinct isolated marked
vertices have distinct component roots. Thus their number is bounded by the
actual tracked-component count. This proves the source Step 1 comparison
without assuming exchangeability across birth times.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace Freezing2.TrackedClusters

open Freezing1

variable {V : Type*} [DecidableEq V]

/-- Isolated present marked vertices inject into the actual tracked roots. -/
theorem card_alone_le_componentCount (F : RootedForest V) {A : Finset V}
    (hA : A ⊆ F.vertices) : (A.filter (Alone F A)).card ≤ componentCount F A := by
  have hinj : Set.InjOn F.root (A.filter (Alone F A) : Set V) := by
    intro u hu v hv heq
    have hu' := Finset.mem_filter.mp hu
    have hv' := Finset.mem_filter.mp hv
    exact (hu'.2 v hv'.1 (hA hu'.1) (hA hv'.1) heq).symm
  calc
    _ = ((A.filter (Alone F A)).image F.root).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (A.image F.root).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    _ = componentCount F A := rfl

/-- The expected number of singleton marked components is bounded by the
expected number of all components meeting the marked set. -/
theorem sum_alone_probability_le_integral_count (μ : Measure (RootedForest V))
    [IsProbabilityMeasure μ] (A : Finset V) (hA : ∀ᵐ F ∂μ, A ⊆ F.vertices) :
    (∑ v ∈ A, μ.real {F | Alone F A v}) ≤ ∫ F, (componentCount F A : ℝ) ∂μ := by
  let I : V → RootedForest V → ℝ := fun v ↦ {F | Alone F A v}.indicator (fun _ ↦ 1)
  have hi (v : V) : Integrable (I v) μ := (integrable_const 1).indicator (by trivial)
  have hp (v : V) : μ.real {F | Alone F A v} = ∫ F, I v F ∂μ :=
    (integral_indicator_one (by trivial)).symm
  simp_rw [hp]
  rw [← integral_finsetSum A (fun v _ ↦ hi v)]
  apply integral_mono_ae (integrable_finsetSum A (fun v _ ↦ hi v))
    (integrable_componentCount μ A)
  filter_upwards [hA] with F hFA
  have he : (∑ v ∈ A, I v F) = ((A.filter (Alone F A)).card : ℝ) := by
    simp only [I, Set.indicator_apply, Set.mem_ofPred_eq, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [he]
  exact_mod_cast card_alone_le_componentCount F hFA

/-- U34 Step 1 for the actual reverse law. The oldest marked vertex has the
smallest isolation probability; summing all singleton events and injecting
singletons into components gives the expected-count bound. The target phase
is explicitly no later than every marked birth. -/
theorem oldest_isolation_probability_le_expectedCount {x : SignSequence} {n t : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (htn : t ≤ n)
    {A : Finset (ℕ ⊕ ℕ)} (hA : A ⊆ Freezing1.vertexLabels x n)
    {u : ℕ ⊕ ℕ} (hu : u ∈ A)
    (holdest : ∀ v ∈ A, Freezing1.birthTime n v ≤ Freezing1.birthTime n u)
    (hborn : ∀ v ∈ A, t ≤ Freezing1.birthTime n v) :
    (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} ≤
      expectedCount x n (n - t) A / A.card := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr ⟨u, hu⟩
  have hsum : (A.card : ℝ) * (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} ≤
      ∑ v ∈ A, (Reverse.lawAfter x n (n - t)).real {F | Alone F A v} := by
    calc
      _ = ∑ _v ∈ A, (Reverse.lawAfter x n (n - t)).real {F | Alone F A u} := by simp
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦
        isolation_probability_le_of_birth_order hn hA hu hv (holdest v hv) (hborn v hv)
  have hp : ∀ᵐ F ∂Reverse.lawAfter x n (n - t), A ⊆ F.vertices := by
    apply lawAfter_tracked_present x hn (Nat.sub_le _ _) hA
    simpa only [Nat.sub_sub_self htn] using hborn
  have hc := sum_alone_probability_le_integral_count (Reverse.lawAfter x n (n - t)) A hp
  apply (le_div_iff₀ hcard).mpr
  simpa only [mul_comm, expectedCount] using hsum.trans hc

end Freezing2.TrackedClusters
