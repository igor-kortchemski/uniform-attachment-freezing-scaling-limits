module

public import Freezing2.Probability.CanonicalForwardGraph
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Uniform vertex samples under the canonical tree identification

An injective map of a finite vertex set transports its uniform law to the
uniform law on its image. The canonical timestamp bijection therefore preserves
one uniform vertex and every finite vector of independent uniform vertices.
-/

@[expose] public section

open MeasureTheory
open scoped Classical ENNReal

namespace Freezing2

/-- Uniform finite-set sampling is preserved by an injection on its support;
this statement also handles an empty finite set. -/
theorem map_uniformOfFinset_of_injOn {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [DecidableEq B]
    (s : Finset A) (f : A → B) (hf : Measurable f) (hi : Set.InjOn f (s : Set A)) :
    (Measure.uniformOfFinset s).map f = Measure.uniformOfFinset (s.image f) := by
  apply Measure.ext
  intro U hU
  rw [Measure.map_apply hf hU, Measure.uniformOfFinset_apply, Measure.uniformOfFinset_apply]
  simp only [Set.mem_preimage]
  have hfilter : Set.InjOn f ((s.filter (fun a ↦ f a ∈ U) : Finset A) : Set A) :=
    hi.mono (by intro a ha; exact (Finset.mem_filter.mp ha).1)
  rw [Finset.filter_image, Finset.card_image_of_injOn hi, Finset.card_image_of_injOn hfilter]

/-- The normalized finite-set law is finite, including the empty-set case. -/
theorem uniformOfFinset_finite {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (s : Finset A) : IsFiniteMeasure (Measure.uniformOfFinset s) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  by_cases hs : s.card = 0
  · simp [hs]
  · have hc : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs
    rw [ENNReal.div_self hc (ENNReal.natCast_ne_top _)]
    exact ENNReal.one_lt_top

/-- A nonempty finite vertex set has a genuine uniform probability law. -/
theorem uniformOfFinset_probability_of_nonempty {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (s : Finset A) (hs : s.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset s) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast hs.card_pos.ne') (ENNReal.natCast_ne_top _)

/-- Uniform sampling on the finite vertex subtype, followed by its inclusion,
is exactly uniform sampling on the ambient finite vertex set. -/
theorem map_uniform_vertex_subtype_val {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [DecidableEq A] (s : Finset A) :
    (Measure.uniformOfFinset (Finset.univ : Finset ↥s)).map (fun v : ↥s ↦ (v : A)) =
      Measure.uniformOfFinset s := by
  rw [map_uniformOfFinset_of_injOn _ _ measurable_subtype_coe
    (by intro u _ v _ he; exact Subtype.ext he)]
  congr 1
  ext a
  simp

namespace ReverseStamped

/-- Conditional on the terminal tree, timestamp IDs transport exactly the
uniform reverse vertex distribution to the actual forward vertex distribution. -/
theorem map_uniform_vertices {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) :
    (Measure.uniformOfFinset F.forest.vertices).map F.edgeTime =
      Measure.uniformOfFinset (canonicalForwardState x n F).vertices := by
  rw [map_uniformOfFinset_of_injOn F.forest.vertices F.edgeTime (measurable_of_countable _)
    (by
      intro u hu v hv he
      exact ht.edgeTime_injective_of_one_root (one_root_of_terminal_valid hF) u hu v hv he)]
  rw [canonicalForwardState_vertices hF ht ho]

/-- Every finite iid uniform sample vector is transported coordinatewise.
The zero-length vector is retained. -/
theorem map_uniform_vertex_vector {x : Freezing1.SignSequence} {n : ℕ} {F : Forest}
    (hF : Freezing1.Reverse.ValidAt x n 0 F.forest)
    (ht : Freezing1.ReverseStamped.TimesValidAt x n 0 F) (ho : CanonicalOrder F) (k : ℕ) :
    (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset F.forest.vertices)).map
        (fun v i ↦ F.edgeTime (v i)) =
      Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (canonicalForwardState x n F).vertices) := by
  have : IsFiniteMeasure (Measure.uniformOfFinset F.forest.vertices) :=
    uniformOfFinset_finite F.forest.vertices
  rw [Measure.pi_map_pi (fun _ ↦ (measurable_of_countable F.edgeTime).aemeasurable)]
  simp_rw [map_uniform_vertices hF ht ho]

/-- The conditional uniform-vector identity holds for the actual reverse law,
with all structural and ordering premises discharged. -/
theorem treeLaw_map_uniform_vertex_vector (x : Freezing1.SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ Freezing1.extinctionTime x) :
    ∀ᵐ F ∂Freezing1.ReverseStamped.treeLaw x n,
      (Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset F.forest.vertices)).map
          (fun v i ↦ F.edgeTime (v i)) =
        Measure.pi (fun _ : Fin k ↦ Measure.uniformOfFinset (canonicalForwardState x n F).vertices) := by
  filter_upwards [Freezing1.ReverseStamped.lawAfter_forest_valid x n n hn le_rfl,
    Freezing1.ReverseStamped.treeLaw_times_valid x n hn, treeLaw_canonicalOrder x n hn]
    with F hF ht ho
  exact map_uniform_vertex_vector (by simpa only [Nat.sub_self] using hF) ht ho k

end ReverseStamped
end Freezing2
