module

public import Freezing2.Geometry.MeasuredGHSpace
public import Freezing2.Probability.UniformTransport
public import Freezing2.Probability.SampledDistanceLaw
public import Freezing2.Probability.ProkhorovBounds

/-!
# Finite measured spaces reconstructed from distance matrices

A `(k+1) × (k+1)` real matrix is sent to the finite set of its rows in the sup
metric, with the uniform weight `1/(k+1)` on row indices. For the distance
matrix of points `v₀, …, v_k` of a metric space, row `l` is the Fréchet
embedding of `v_l`, so this finite measured space is isometric to the sample
set with its empirical measure. The construction is defined, and Lipschitz in
the GHP distance, for every matrix, so it is a continuous map into the GHP space.
Its distance to the original space is at most the Hausdorff distance from the
samples to the whole carrier plus the Lévy–Prokhorov distance from the
empirical measure to the original measure.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace Freezing2

/-- The GHP infimum bound with an arbitrary Borel structure on the ambient space. -/
theorem ghpDistance_le_of_isometries_borel {X Y Z : Type u} [MetricSpace X] [MeasurableSpace X]
    [CompactSpace X] [BorelSpace X] [MetricSpace Y] [MeasurableSpace Y] [CompactSpace Y]
    [BorelSpace Y] [MetricSpace Z] [mZ : MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure X) (ν : Measure Y) (i : X → Z) (j : Y → Z) (hi : Isometry i) (hj : Isometry j) :
    ghpDistance μ ν ≤ levyProkhorovDist (μ.map i) (ν.map j) + hausdorffDist (range i) (range j) := by
  have h : mZ = borel Z := BorelSpace.measurable_eq
  subst h
  exact ghpDistance_le_of_isometries μ ν Z i j hi hj

/-- The uniform law on the indices `0, …, k`. -/
noncomputable def uniformIndexLaw (k : ℕ) : ProbabilityMeasure (Fin (k + 1)) :=
  ⟨Measure.uniformOfFinset Finset.univ,
    uniformOfFinset_probability_of_nonempty _ Finset.univ_nonempty⟩

namespace RowSpace

variable {k : ℕ}

/-- The row of index `l`, as a point of the finite row set. -/
def rowPoint (m : Fin (k + 1) → Fin (k + 1) → ℝ) (l : Fin (k + 1)) : ULift.{u} (range m) :=
  ULift.up ⟨m l, mem_range_self l⟩

theorem rowPoint_surjective (m : Fin (k + 1) → Fin (k + 1) → ℝ) :
    Function.Surjective (rowPoint.{u} m) := by
  rintro ⟨⟨r, l, rfl⟩⟩
  exact ⟨l, rfl⟩

instance (m : Fin (k + 1) → Fin (k + 1) → ℝ) : Nonempty (ULift.{u} (range m)) :=
  ⟨rowPoint m 0⟩

instance (m : Fin (k + 1) → Fin (k + 1) → ℝ) : Finite (ULift.{u} (range m)) :=
  Finite.of_surjective _ (rowPoint_surjective m)

end RowSpace

open RowSpace

/-- The finite measured space of rows of a matrix, with uniform index weights. -/
noncomputable def rowSpace (k : ℕ) (m : Fin (k + 1) → Fin (k + 1) → ℝ) :
    CompactMeasuredSpace.{u} :=
  CompactMeasuredSpace.of (ULift.{u} (range m)) ((uniformIndexLaw k).map (rowPoint m))

/-- The reconstruction map from matrices to the GHP space. -/
noncomputable def matrixSpace (k : ℕ) (m : Fin (k + 1) → Fin (k + 1) → ℝ) :
    MeasuredGHSpace.{u} :=
  toMeasuredGHSpace (rowSpace.{u} k m)

/-- Pushforwards of the row-space law are pushforwards of the uniform index law. -/
theorem rowSpace_map_law (k : ℕ) (m : Fin (k + 1) → Fin (k + 1) → ℝ) {Z : Type*}
    [MeasurableSpace Z] (f : rowSpace.{u} k m → Z) (hf : Measurable f) :
    ((rowSpace.{u} k m).law : Measure (rowSpace.{u} k m)).map f =
      (uniformIndexLaw k : Measure (Fin (k + 1))).map (fun l ↦ f (rowPoint m l)) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply (measurable_of_countable _) hs]
  exact Measure.map_apply (measurable_of_countable _) (hf hs)

/-- Moving every matrix entry by at most `δ` moves the reconstruction by at most `2δ`. -/
theorem dist_matrixSpace_le (k : ℕ) (m m' : Fin (k + 1) → Fin (k + 1) → ℝ) :
    dist (matrixSpace.{u} k m) (matrixSpace.{u} k m') ≤ 2 * dist m m' := by
  let Z := ULift.{u} (Fin (k + 1) → ℝ)
  let i : (rowSpace.{u} k m) → Z := fun x ↦ ULift.up x.down.val
  let j : (rowSpace.{u} k m') → Z := fun x ↦ ULift.up x.down.val
  have hi : Isometry i := Isometry.of_dist_eq fun _ _ ↦ rfl
  have hj : Isometry j := Isometry.of_dist_eq fun _ _ ↦ rfl
  have hδ : 0 ≤ dist m m' := dist_nonneg
  have hrow (l : Fin (k + 1)) : dist (m l) (m' l) ≤ dist m m' := dist_le_pi_dist m m' l
  change CompactMeasuredSpace.distance _ _ ≤ _
  refine (ghpDistance_le_of_isometries_borel _ _ i j hi hj).trans ?_
  have hLP : levyProkhorovDist (((rowSpace.{u} k m).law : Measure _).map i)
      (((rowSpace.{u} k m').law : Measure _).map j) ≤ dist m m' := by
    rw [rowSpace_map_law k m i hi.continuous.measurable,
      rowSpace_map_law k m' j hj.continuous.measurable]
    exact levyProkhorovDist_map_le_of_dist_le _ (measurable_of_countable _)
      (measurable_of_countable _) hδ fun l ↦ hrow l
  have hH : hausdorffDist (range i) (range j) ≤ dist m m' := by
    apply hausdorffDist_le_of_mem_dist hδ
    · rintro _ ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := rowPoint_surjective m x
      exact ⟨j (rowPoint m' l), mem_range_self _, hrow l⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨l, rfl⟩ := rowPoint_surjective m' x
      exact ⟨i (rowPoint m l), mem_range_self _, by rw [dist_comm]; exact hrow l⟩
  linarith

theorem lipschitzWith_matrixSpace (k : ℕ) : LipschitzWith 2 (matrixSpace.{u} k) :=
  LipschitzWith.of_dist_le_mul fun m m' ↦ by
    simpa using dist_matrixSpace_le k m m'

theorem continuous_matrixSpace (k : ℕ) : Continuous (matrixSpace.{u} k) :=
  (lipschitzWith_matrixSpace k).continuous

/-- Rows of a distance matrix realize the Fréchet embedding. -/
theorem dist_distanceMatrix_row {X : Type*} [PseudoMetricSpace X] {k : ℕ}
    (v : Fin (k + 1) → X) (l l' : Fin (k + 1)) :
    dist (distanceMatrix (k + 1) v l) (distanceMatrix (k + 1) v l') = dist (v l) (v l') := by
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    rw [Real.dist_eq]
    exact abs_dist_sub_le (v l) (v l') (v j)
  · have h := dist_le_pi_dist (distanceMatrix (k + 1) v l) (distanceMatrix (k + 1) v l') l'
    simp only [distanceMatrix, dist_self, sub_zero, Real.dist_eq, abs_of_nonneg dist_nonneg] at h
    exact h

/-- The reconstruction of a sampled distance matrix is within the Hausdorff
distance of the samples to the carrier plus the Lévy–Prokhorov distance of the
empirical measure from the original measure. -/
theorem dist_matrixSpace_distanceMatrix_le (X : CompactMeasuredSpace.{u}) {k : ℕ}
    (v : Fin (k + 1) → X) :
    dist (matrixSpace.{u} k (distanceMatrix (k + 1) v)) (toMeasuredGHSpace X) ≤
      levyProkhorovDist ((uniformIndexLaw k : Measure (Fin (k + 1))).map v) (X.law : Measure X) +
        hausdorffDist (range v) univ := by
  classical
  let m := distanceMatrix (k + 1) v
  have hrow (l : Fin (k + 1)) (r : range m) (h : (r : Fin (k + 1) → ℝ) = m l) :
      v (Classical.choose r.2) = v l := by
    have hc := Classical.choose_spec r.2
    have h0 : dist (m (Classical.choose r.2)) (m l) = 0 := by rw [hc, h, dist_self]
    rw [dist_distanceMatrix_row] at h0
    exact dist_eq_zero.mp h0
  let i : (rowSpace.{u} k m) → X := fun x ↦ v (Classical.choose x.down.2)
  have hi_row (l : Fin (k + 1)) : i (rowPoint m l) = v l := hrow l _ rfl
  have hi : Isometry i := by
    apply Isometry.of_dist_eq
    intro x y
    obtain ⟨l, rfl⟩ := rowPoint_surjective m x
    obtain ⟨l', rfl⟩ := rowPoint_surjective m y
    rw [hi_row, hi_row]
    exact (dist_distanceMatrix_row v l l').symm
  change CompactMeasuredSpace.distance _ _ ≤ _
  refine (ghpDistance_le_of_isometries_borel _ _ i id hi isometry_id).trans (le_of_eq ?_)
  have hmap : (((rowSpace.{u} k m).law : Measure _).map i) =
      (uniformIndexLaw k : Measure (Fin (k + 1))).map v := by
    rw [rowSpace_map_law k m i hi.continuous.measurable]
    congr 1
    funext l
    exact hi_row l
  have hrange : range i = range v := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨l, rfl⟩ := rowPoint_surjective m y
      exact ⟨l, (hi_row l).symm⟩
    · rintro ⟨l, rfl⟩
      exact ⟨rowPoint m l, hi_row l⟩
  rw [hmap, Measure.map_id, hrange, range_id]

end Freezing2
