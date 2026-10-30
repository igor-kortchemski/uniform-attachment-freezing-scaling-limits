module

public import Freezing2.Probability.ProfileCoordinateLaw
public import Freezing2.Probability.UniformTransport

/-!
# Uniform forest vertices and the measured segment approximation

These identities retain the actual finite vertex subtype. Its uniform law,
transported through the exact companion-to-paper label bijection and the
profile coordinate, is the coordinate law whose Prokhorov limit was proved.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical ENNReal

namespace Freezing2

/-- The uniform measure on the actual finite set of present forest vertices. -/
noncomputable def forestVertexMeasure (F : Freezing1.Reverse.Forest) :
    Measure {v // v ∈ F.vertices} :=
  Measure.uniformOfFinset Finset.univ

theorem forestVertexMeasure_isProbabilityMeasure (F : Freezing1.Reverse.Forest)
    (hF : F.vertices.Nonempty) : IsProbabilityMeasure (forestVertexMeasure F) := by
  obtain ⟨v, hv⟩ := hF
  exact uniformOfFinset_probability_of_nonempty _ ⟨⟨v, hv⟩, Finset.mem_univ _⟩

/-- The actual forest vertex map used for the common metric realization. -/
noncomputable def forestProfilePoint (g : ℝ → ℝ) (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (n : ℕ) (F : Freezing1.Reverse.Forest)
    (v : {v // v ∈ F.vertices}) : ProfileSegment g :=
  profileLabelPoint g hg hpos n (fromCompanionLabel v.val)

theorem measurable_forestProfilePoint {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) (n : ℕ) (F : Freezing1.Reverse.Forest) :
    Measurable (forestProfilePoint g hg hpos n F) := measurable_of_countable _

/-- Agreement with the unmodified coordinate used by the uniform distortion
and density theorems. -/
theorem forestProfilePoint_coe {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : PositiveProfile g) {x : ℕ → ℤ} (hx : IsSigned x) {n : ℕ} (hn : 0 < n)
    {F : Freezing1.Reverse.Forest}
    (hV : F.vertices = Freezing1.vertexLabels (companionSchedule x) n)
    (v : {v // v ∈ F.vertices}) :
    (forestProfilePoint g hg hpos n F v : ℝ) =
      profileBirthCoordinate g n (fromCompanionLabel v.val) := by
  exact profileLabelPoint_coe hg hpos x hn
    ((fromCompanionLabel_mem_iff x hx n v.val).mpr (hV ▸ v.property))

/-- The uniform measure transport is exact, not only asymptotic, and uses
all present vertices with their original sampling weights. -/
theorem map_forestVertexMeasure_profilePoint
    {x : ℕ → ℤ} (hx : IsSigned x) {n : ℕ} (hs : 0 ≤ activeCount x n)
    {F : Freezing1.Reverse.Forest}
    (hV : F.vertices = Freezing1.vertexLabels (companionSchedule x) n)
    {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (hpos : PositiveProfile g) :
    (forestVertexMeasure F).map (forestProfilePoint g hg hpos n F) =
      (uniformProfileCoordinateLaw x n hx hs g hg hpos : Measure (ProfileSegment g)) := by
  have hval : (forestVertexMeasure F).map Subtype.val = Measure.uniformOfFinset F.vertices :=
    map_uniform_vertex_subtype_val F.vertices
  calc
    (forestVertexMeasure F).map (forestProfilePoint g hg hpos n F) =
        (((forestVertexMeasure F).map Subtype.val).map fromCompanionLabel).map
          (profileLabelPoint g hg hpos n) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = (uniformProfileCoordinateLaw x n hx hs g hg hpos : Measure (ProfileSegment g)) := by
      rw [hval, hV]
      change ((Freezing1.uniformVertex (companionSchedule x) n).map fromCompanionLabel).map
        (profileLabelPoint g hg hpos n) = _
      rw [map_companion_uniformVertex x hx]
      rfl

/-- Terminal validity discharges the vertex-set identification in the actual
reverse construction. -/
theorem map_forestVertexMeasure_profilePoint_of_valid
    {x : ℕ → ℤ} (hx : IsSigned x) {n : ℕ} (hs : 0 ≤ activeCount x n)
    {F : Freezing1.Reverse.Forest} (hF : Freezing1.Reverse.ValidAt (companionSchedule x) n 0 F)
    {g : ℝ → ℝ} (hg : Integrable g profileMeasure) (hpos : PositiveProfile g) :
    (forestVertexMeasure F).map (forestProfilePoint g hg hpos n F) =
      (uniformProfileCoordinateLaw x n hx hs g hg hpos : Measure (ProfileSegment g)) := by
  apply map_forestVertexMeasure_profilePoint hx hs _ hg hpos
  simpa only [Freezing1.Reverse.phaseLabels_zero] using hF.vertices_eq

end Freezing2
