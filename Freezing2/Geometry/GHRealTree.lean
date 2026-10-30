module

public import Freezing2.Geometry.RealTree
public import Freezing2.Geometry.GHCovering

/-!
# Approximate midpoints on the Gromov–Hausdorff space

`ε`-approximate midpoints transfer across a Gromov–Hausdorff distance `η` with slack
`3η`. Consequently, for `ε ≥ 0` the classes of compact metric spaces with
`ε`-approximate midpoints form a closed subset of the Gromov–Hausdorff space; this
is how the midpoint property passes to Gromov–Hausdorff limits of graphs.
-/

@[expose] public section

open Set Metric GromovHausdorff Topology Filter

namespace Freezing2.RealTree

theorem ApproxMidpoints.mono {X : Type*} [MetricSpace X] {ε ε' : ℝ} (h : ApproxMidpoints ε X)
    (hε : ε ≤ ε') : ApproxMidpoints ε' X := by
  intro x y
  obtain ⟨m, h1, h2⟩ := h x y
  exact ⟨m, h1.trans hε, h2.trans hε⟩

/-- Approximate midpoints with every slack above `ε` give slack `ε` in a compact space. -/
theorem approxMidpoints_of_forall_gt {X : Type*} [MetricSpace X] [CompactSpace X] {ε : ℝ}
    (h : ∀ δ > 0, ApproxMidpoints (ε + δ) X) : ApproxMidpoints ε X := by
  intro x y
  choose m hm using fun n : ℕ ↦ h (1 / ((n : ℝ) + 1)) (by positivity) x y
  obtain ⟨z, -, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq (fun n ↦ mem_univ (m n))
  have hε : Tendsto (fun n ↦ ε + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (ε + 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  rw [add_zero] at hε
  have key : ∀ (f : X → ℝ), Continuous f →
      (∀ n, |f (m n) - dist x y / 2| ≤ ε + 1 / ((n : ℝ) + 1)) → |f z - dist x y / 2| ≤ ε := by
    intro f hf hb
    have h1 : Tendsto (fun n ↦ |f (m (φ n)) - dist x y / 2|) atTop (𝓝 |f z - dist x y / 2|) :=
      (((hf.tendsto z).comp hz).sub tendsto_const_nhds).abs
    exact le_of_tendsto_of_tendsto' h1 hε fun n ↦ hb (φ n)
  exact ⟨z, key (dist x) (continuous_const.dist continuous_id) (fun n ↦ (hm n).1),
    key (fun w ↦ dist w y) (continuous_id.dist continuous_const) (fun n ↦ (hm n).2)⟩

/-- Approximate midpoints transfer across a small Gromov–Hausdorff distance. -/
theorem approxMidpoints_of_dist_lt {p q : GHSpace} {η : ℝ} (hpq : dist p q < η) {ε : ℝ}
    (h : ApproxMidpoints ε p.Rep) : ApproxMidpoints (ε + 3 * η) q.Rep := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, he⟩ := ghDist_eq_hausdorffDist p.Rep q.Rep
  rw [dist_ghDist, he] at hpq
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty Φ) (range_nonempty Ψ)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  intro y y'
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hpq hfin
  obtain ⟨_, ⟨x', rfl⟩, hx'⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y') hpq hfin
  obtain ⟨m, hm1, hm2⟩ := h x x'
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self m) hpq hfin
  refine ⟨z, ?_, ?_⟩
  · have e1 : dist y z = dist (Ψ y) (Ψ z) := (hΨ.dist_eq y z).symm
    have e2 : dist y y' = dist (Ψ y) (Ψ y') := (hΨ.dist_eq y y').symm
    have e3 : dist x m = dist (Φ x) (Φ m) := (hΦ.dist_eq x m).symm
    have e4 : dist x x' = dist (Φ x) (Φ x') := (hΦ.dist_eq x x').symm
    have t1 := dist_triangle4 (Ψ y) (Φ x) (Φ m) (Ψ z)
    have t2 := dist_triangle4 (Φ x) (Ψ y) (Ψ z) (Φ m)
    have t3 := dist_triangle4 (Ψ y) (Φ x) (Φ x') (Ψ y')
    have t4 := dist_triangle4 (Φ x) (Ψ y) (Ψ y') (Φ x')
    have c1 := dist_comm (Ψ y) (Φ x)
    have c2 := dist_comm (Ψ y') (Φ x')
    have c3 := dist_comm (Ψ z) (Φ m)
    rw [abs_le] at hm1 ⊢
    constructor <;> linarith [hm1.1, hm1.2]
  · have e1 : dist z y' = dist (Ψ z) (Ψ y') := (hΨ.dist_eq z y').symm
    have e2 : dist y y' = dist (Ψ y) (Ψ y') := (hΨ.dist_eq y y').symm
    have e3 : dist m x' = dist (Φ m) (Φ x') := (hΦ.dist_eq m x').symm
    have e4 : dist x x' = dist (Φ x) (Φ x') := (hΦ.dist_eq x x').symm
    have t1 := dist_triangle4 (Ψ z) (Φ m) (Φ x') (Ψ y')
    have t2 := dist_triangle4 (Φ m) (Ψ z) (Ψ y') (Φ x')
    have t3 := dist_triangle4 (Ψ y) (Φ x) (Φ x') (Ψ y')
    have t4 := dist_triangle4 (Φ x) (Ψ y) (Ψ y') (Φ x')
    have c1 := dist_comm (Ψ y) (Φ x)
    have c2 := dist_comm (Ψ y') (Φ x')
    have c3 := dist_comm (Ψ z) (Φ m)
    rw [abs_le] at hm2 ⊢
    constructor <;> linarith [hm2.1, hm2.2]

/-- Classes with `ε`-approximate midpoints form a closed set. -/
theorem isClosed_setOf_approxMidpoints (ε : ℝ) :
    IsClosed {p : GHSpace | ApproxMidpoints ε p.Rep} := by
  apply isClosed_of_closure_subset
  intro p hp
  rw [Metric.mem_closure_iff] at hp
  apply approxMidpoints_of_forall_gt
  intro δ hδ
  obtain ⟨q, hq, hpq⟩ := hp (δ / 3) (by positivity)
  have := approxMidpoints_of_dist_lt (show dist q p < δ / 3 by rwa [dist_comm]) hq
  rwa [show ε + 3 * (δ / 3) = ε + δ by ring] at this

theorem approxMidpoints_toGHSpace_rep_iff (X : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] {ε : ℝ} : ApproxMidpoints ε (toGHSpace X).Rep ↔ ApproxMidpoints ε X := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (GHSpace.toGHSpace_rep (toGHSpace X))
  exact ⟨fun h ↦ h.of_isometryEquiv e, fun h ↦ h.of_isometryEquiv e.symm⟩

theorem fourPoint_toGHSpace_rep_iff (X : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] : FourPoint (toGHSpace X).Rep ↔ FourPoint X := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (GHSpace.toGHSpace_rep (toGHSpace X))
  exact ⟨fun h ↦ h.of_isometryEquiv e, fun h ↦ h.of_isometryEquiv e.symm⟩

end Freezing2.RealTree
