module

public import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Covering numbers and diameters on the Gromov–Hausdorff space

Covers by finitely many open balls transfer across a small Gromov–Hausdorff
distance, at the cost of twice that distance in the radius. Consequently the
set of classes covered by at most `K` open `r`-balls is open, and a diameter
bound defines a closed set. These are the measurable events used to show GH
tightness, including for finitely many individual laws.
-/

@[expose] public section

open Set Metric GromovHausdorff Topology

namespace Freezing2.GHCovering

/-- `X` is covered by at most `K` open balls of radius `r`. -/
def Coverable (X : Type*) [PseudoMetricSpace X] (K : ℕ) (r : ℝ) : Prop :=
  ∃ s : Finset X, s.card ≤ K ∧ ∀ x : X, ∃ y ∈ s, dist x y < r

theorem Coverable.mono {X : Type*} [PseudoMetricSpace X] {K K' : ℕ} {r r' : ℝ}
    (h : Coverable X K r) (hK : K ≤ K') (hr : r ≤ r') : Coverable X K' r' := by
  obtain ⟨s, hs, hcov⟩ := h
  refine ⟨s, hs.trans hK, fun x ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := hcov x
  exact ⟨y, hy, hxy.trans_le hr⟩

/-- Covers transfer across two isometric embeddings at small Hausdorff distance. -/
theorem Coverable.of_hausdorffDist_lt {X Y Z : Type*} [MetricSpace X] [MetricSpace Y]
    [MetricSpace Z] [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    {i : X → Z} {j : Y → Z} (hi : Isometry i) (hj : Isometry j) {η : ℝ}
    (hd : hausdorffDist (range i) (range j) < η) {K : ℕ} {r : ℝ} (h : Coverable X K r) :
    Coverable Y K (r + 2 * η) := by
  classical
  have hfin : hausdorffEDist (range i) (range j) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty i) (range_nonempty j)
      (isCompact_range hi.continuous).isBounded (isCompact_range hj.continuous).isBounded
  obtain ⟨s, hs, hcov⟩ := h
  have hb (a : X) : ∃ b : Y, dist (i a) (j b) < η := by
    obtain ⟨z, ⟨b, rfl⟩, hz⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self a) hd hfin
    exact ⟨b, hz⟩
  choose b hb using hb
  refine ⟨s.image b, Finset.card_image_le.trans hs, fun y ↦ ?_⟩
  obtain ⟨z, ⟨x, rfl⟩, hxz⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hd hfin
  obtain ⟨a, ha, hxa⟩ := hcov x
  refine ⟨b a, Finset.mem_image_of_mem b ha, ?_⟩
  rw [← hj.dist_eq]
  calc
    dist (j y) (j (b a)) ≤ dist (j y) (i x) + dist (i x) (i a) + dist (i a) (j (b a)) :=
      dist_triangle4 _ _ _ _
    _ < η + r + η := by
      rw [hi.dist_eq]
      have := dist_comm (j y) (i x)
      linarith [hb a]
    _ = r + 2 * η := by ring

/-- Covers transfer between Gromov–Hausdorff classes at small distance. -/
theorem coverable_of_dist_lt {p q : GHSpace} {η : ℝ} (hpq : dist p q < η) {K : ℕ} {r : ℝ}
    (h : Coverable p.Rep K r) : Coverable q.Rep K (r + 2 * η) := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, he⟩ := ghDist_eq_hausdorffDist p.Rep q.Rep
  rw [dist_ghDist, he] at hpq
  exact h.of_hausdorffDist_lt hΦ hΨ hpq

/-- A finite open-ball cover of a compact space has slack in its radius. -/
theorem Coverable.exists_lt {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {K : ℕ} {r : ℝ} (h : Coverable X K r) : ∃ r' < r, Coverable X K r' := by
  obtain ⟨s, hs, hcov⟩ := h
  have hne : (s : Set X).Nonempty := by
    obtain ⟨y, hy, _⟩ := hcov (Classical.arbitrary X)
    exact ⟨y, hy⟩
  have hsc : IsCompact (s : Set X) := s.finite_toSet.isCompact
  obtain ⟨x₀, -, hmax⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_isMaxOn univ_nonempty
    (continuous_infDist_pt (s : Set X)).continuousOn
  obtain ⟨a₀, ha₀, he₀⟩ := hsc.exists_infDist_eq_dist hne x₀
  obtain ⟨y₀, hy₀, hx₀y₀⟩ := hcov x₀
  have hlt : infDist x₀ (s : Set X) < r :=
    (infDist_le_dist_of_mem (Finset.mem_coe.mpr hy₀)).trans_lt hx₀y₀
  refine ⟨(infDist x₀ (s : Set X) + r) / 2, by linarith, s, hs, fun x ↦ ?_⟩
  obtain ⟨a, ha, he⟩ := hsc.exists_infDist_eq_dist hne x
  refine ⟨a, ha, ?_⟩
  have hx : infDist x (s : Set X) ≤ infDist x₀ (s : Set X) := hmax (mem_univ x)
  linarith

/-- Classes covered by at most `K` open `r`-balls form an open set. -/
theorem isOpen_setOf_coverable (K : ℕ) (r : ℝ) :
    IsOpen {p : GHSpace | Coverable p.Rep K r} := by
  rw [Metric.isOpen_iff]
  intro p hp
  obtain ⟨r', hr', hcov⟩ := Coverable.exists_lt hp
  refine ⟨(r - r') / 2, by linarith, fun q hq ↦ ?_⟩
  have h := coverable_of_dist_lt (mem_ball'.mp hq) hcov
  exact h.mono le_rfl (by linarith)

/-- Every compact metric space is covered by finitely many open balls. -/
theorem exists_coverable (X : Type*) [MetricSpace X] [CompactSpace X] {r : ℝ} (hr : 0 < r) :
    ∃ K : ℕ, Coverable X K r := by
  classical
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ : IsCompact (univ : Set X)) hr
  refine ⟨ht.toFinset.card, ht.toFinset, le_rfl, fun x ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov (mem_univ x))
  exact ⟨y, ht.mem_toFinset.mpr hy, mem_ball.mp hxy⟩

/-- Diameters change by at most twice the Gromov–Hausdorff distance. -/
theorem diam_le_of_dist_lt {p q : GHSpace} {η : ℝ} (hpq : dist p q < η) :
    diam (univ : Set q.Rep) ≤ diam (univ : Set p.Rep) + 2 * η := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, he⟩ := ghDist_eq_hausdorffDist p.Rep q.Rep
  rw [dist_ghDist, he] at hpq
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty Φ) (range_nonempty Ψ)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  have hη : 0 ≤ η := hausdorffDist_nonneg.trans hpq.le
  apply diam_le_of_forall_dist_le (by positivity [diam_nonneg (s := (univ : Set p.Rep))])
  intro y _ y' _
  obtain ⟨z, ⟨x, rfl⟩, hx⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hpq hfin
  obtain ⟨z', ⟨x', rfl⟩, hx'⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y') hpq hfin
  have hxx' : dist x x' ≤ diam (univ : Set p.Rep) :=
    dist_le_diam_of_mem isBounded_of_compactSpace (mem_univ _) (mem_univ _)
  rw [← hΨ.dist_eq, ← hΦ.dist_eq] at *
  calc
    dist (Ψ y) (Ψ y') ≤ dist (Ψ y) (Φ x) + dist (Φ x) (Φ x') + dist (Φ x') (Ψ y') :=
      dist_triangle4 _ _ _ _
    _ ≤ η + diam (univ : Set p.Rep) + η := by
      have h1 := dist_comm (Ψ y) (Φ x)
      have h2 := dist_comm (Φ x') (Ψ y')
      linarith
    _ = diam (univ : Set p.Rep) + 2 * η := by ring

/-- A diameter bound defines a closed set of classes. -/
theorem isClosed_setOf_diam_le (D : ℝ) :
    IsClosed {p : GHSpace | diam (univ : Set p.Rep) ≤ D} := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro p hp
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hp
  refine ⟨(diam (univ : Set p.Rep) - D) / 3, by linarith, fun q hq ↦ ?_⟩
  simp only [mem_compl_iff, mem_ofPred_eq, not_le]
  have h := diam_le_of_dist_lt (show dist q p < (diam (univ : Set p.Rep) - D) / 3 from
    mem_ball.mp hq)
  linarith

/-- Coverability only depends on the isometry class. -/
theorem Coverable.of_isometryEquiv {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (e : X ≃ᵢ Y) {K : ℕ} {r : ℝ} (h : Coverable X K r) : Coverable Y K r := by
  classical
  obtain ⟨s, hs, hcov⟩ := h
  refine ⟨s.image e, Finset.card_image_le.trans hs, fun y ↦ ?_⟩
  obtain ⟨x, hx, hxy⟩ := hcov (e.symm y)
  refine ⟨e x, Finset.mem_image_of_mem e hx, ?_⟩
  rw [← e.dist_eq (e.symm y) x, e.apply_symm_apply] at hxy
  exact hxy

theorem coverable_toGHSpace_rep_iff (X : Type*) [MetricSpace X] [CompactSpace X]
    [Nonempty X] {K : ℕ} {r : ℝ} : Coverable (toGHSpace X).Rep K r ↔ Coverable X K r := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (GHSpace.toGHSpace_rep (toGHSpace X))
  exact ⟨fun h ↦ h.of_isometryEquiv e, fun h ↦ h.of_isometryEquiv e.symm⟩

theorem diam_toGHSpace_rep (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    diam (univ : Set (toGHSpace X).Rep) = diam (univ : Set X) := by
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (GHSpace.toGHSpace_rep (toGHSpace X))
  calc
    diam (univ : Set (toGHSpace X).Rep) = diam (e '' univ) := (e.isometry.diam_image univ).symm
    _ = diam (univ : Set X) := by rw [Set.image_univ_of_surjective e.surjective]

end Freezing2.GHCovering
