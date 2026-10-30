module

public import Freezing2.MainResults.Supercritical
public import Freezing2.Probability.CriticalTreeBridge
public import Freezing2.Analysis.ProfileTimeChange

/-!
# Supercritical non-tightness

This is the claim following Theorem `thm:sur-critique` (inventory row U04b):
for `α ∈ (1/2, 1)` the scaled measured trees `𝒯_n / n^(1-α)` are not tight
for the GHP topology, because covering numbers blow up in probability.

Following correction S08, the covering statement is made at one sufficiently
small fixed radius `r`, not at every positive radius. The radius is half the
limiting branch length at time `1/2`, so each limiting branch exceeds `r` with
probability at least `1/2`.

The proof uses Theorem `thm:sur-critique` (M06) and three further facts.
* If `K + 1` sample points are pairwise more than `2r` apart, no `K` open
  `r`-balls cover the space. Hence the annealed probability of the open set of
  `2r`-separated matrices bounds the probability of non-coverability, for every
  random measured space.
* The annealed sampled matrices of the forward measured trees are the non-root
  blocks of the root-inclusive matrices of M06, for every exponent `α`.
* In the star limit, branches longer than `r` are pairwise more than `2r` apart.
  Among `(K + 1) m` independent branches, splitting into `K + 1` blocks of size
  `m` shows that fewer than `K + 1` are long with probability at most
  `(K + 1) 2^(-m)`.

The portmanteau theorem then gives limit one. For non-tightness, the image of a
compact set of measured spaces in `GHSpace` is compact, so it has bounded
covering numbers at the scale `r`.
-/

@[expose] public section

open Filter MeasureTheory Set Metric Topology GromovHausdorff
open scoped ENNReal

namespace Freezing2

open GHCovering MeasuredGHSpace

universe u

/-! ### Separated sample configurations -/

/-- Square matrices containing `K + 1` indices whose pairwise off-diagonal
entries exceed `2 * r`. -/
def separatedMatrices (k K : ℕ) (r : ℝ) : Set (Fin k → Fin k → ℝ) :=
  {M | ∃ φ : Fin (K + 1) → Fin k, ∀ a b, a ≠ b → 2 * r < M (φ a) (φ b)}

/-- Separation is a strict finite condition, hence an open set of matrices. -/
theorem isOpen_separatedMatrices (k K : ℕ) (r : ℝ) : IsOpen (separatedMatrices k K r) := by
  have he : separatedMatrices k K r = ⋃ φ : Fin (K + 1) → Fin k, ⋂ a, ⋂ b, ⋂ (_ : a ≠ b),
      {M : Fin k → Fin k → ℝ | 2 * r < M (φ a) (φ b)} := by
    ext M
    simp [separatedMatrices]
  rw [he]
  refine isOpen_iUnion fun φ ↦ isOpen_iInter_of_finite fun a ↦ isOpen_iInter_of_finite fun b ↦
    isOpen_iInter_of_finite fun _ ↦ ?_
  exact isOpen_lt continuous_const ((continuous_apply (φ b)).comp (continuous_apply (φ a)))

/-- Pigeonhole: among `K + 1` points of a space covered by `K` open `r`-balls, two distinct
indices lie in a common ball. -/
theorem GHCovering.Coverable.exists_dist_lt_two_mul {X : Type*} [PseudoMetricSpace X] {K : ℕ}
    {r : ℝ} (h : Coverable X K r) (w : Fin (K + 1) → X) :
    ∃ a b, a ≠ b ∧ dist (w a) (w b) < 2 * r := by
  obtain ⟨s, hs, hcov⟩ := h
  choose c hc hdist using fun a ↦ hcov (w a)
  obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun a ↦ (⟨c a, hc a⟩ : s)) (by simp only [Fintype.card_coe, Fintype.card_fin]; omega)
  refine ⟨a, b, hab, ?_⟩
  have hcab : c a = c b := congrArg Subtype.val he
  calc
    dist (w a) (w b) ≤ dist (w a) (c a) + dist (c a) (w b) := dist_triangle _ _ _
    _ < r + r := by
      have h2 : dist (c a) (w b) < r := by
        rw [hcab, dist_comm]
        exact hdist b
      exact add_lt_add (hdist a) h2
    _ = 2 * r := by ring

/-- A space covered by `K` open `r`-balls has no `2r`-separated `K + 1` points. -/
theorem distanceMatrix_notMem_separatedMatrices {X : Type*} [PseudoMetricSpace X] {K : ℕ}
    {r : ℝ} (h : Coverable X K r) {k : ℕ} (v : Fin k → X) :
    distanceMatrix k v ∉ separatedMatrices k K r := by
  rintro ⟨φ, hφ⟩
  obtain ⟨a, b, hab, hlt⟩ := h.exists_dist_lt_two_mul (fun a ↦ v (φ a))
  exact lt_asymm (hφ a b hab) hlt

/-- Samples of a space covered by `K` open `r`-balls are never `2r`-separated. -/
theorem iidDistanceLaw_separatedMatrices_eq_zero (X : CompactMeasuredSpace.{u}) {k K : ℕ}
    {r : ℝ} (h : Coverable X K r) :
    (iidDistanceLaw X k : Measure (Fin k → Fin k → ℝ)) (separatedMatrices k K r) = 0 := by
  rw [CompactMeasuredSpace.iidDistanceLaw_apply X k (isOpen_separatedMatrices k K r).measurableSet]
  have he : distanceMatrix k ⁻¹' separatedMatrices k K r = (∅ : Set (Fin k → X)) :=
    eq_empty_of_forall_notMem fun v hv ↦ distanceMatrix_notMem_separatedMatrices h v hv
  rw [he, measure_empty]

/-- The same vanishing on isometry classes, read through the underlying GH class. -/
theorem sampledDistanceLaw_separatedMatrices_eq_zero (X : MeasuredGHSpace.{u}) {k K : ℕ}
    {r : ℝ} (h : Coverable (underlyingGH X).Rep K r) :
    (sampledDistanceLaw k X : Measure (Fin k → Fin k → ℝ)) (separatedMatrices k K r) = 0 := by
  induction X using Quotient.inductionOn with
  | _ X =>
    change Coverable (toGHSpace X).Rep K r at h
    rw [coverable_toGHSpace_rep_iff] at h
    exact iidDistanceLaw_separatedMatrices_eq_zero X h

/-- **Annealed separation bound.** For any random compact measured space, the
annealed probability that `k` iid samples contain `K + 1` points pairwise more
than `2r` apart is at most the probability that the space is not covered by `K`
open `r`-balls. -/
theorem annealedDistanceLaw_separatedMatrices_le (P : ProbabilityMeasure MeasuredGHSpace.{u})
    (k K : ℕ) (r : ℝ) :
    (annealedDistanceLaw P k : Measure (Fin k → Fin k → ℝ)) (separatedMatrices k K r) ≤
      (P : Measure MeasuredGHSpace.{u}) {X | ¬ Coverable (underlyingGH X).Rep K r} := by
  rw [annealedDistanceLaw, continuousMixture_apply _ _
    (isOpen_separatedMatrices k K r).measurableSet]
  calc
    ∫⁻ X, (sampledDistanceLaw k X : Measure (Fin k → Fin k → ℝ)) (separatedMatrices k K r)
        ∂(P : Measure MeasuredGHSpace.{u})
      ≤ ∫⁻ X, {X : MeasuredGHSpace.{u} | ¬ Coverable (underlyingGH X).Rep K r}.indicator 1 X
          ∂(P : Measure MeasuredGHSpace.{u}) := by
        refine lintegral_mono fun X ↦ ?_
        by_cases hX : Coverable (underlyingGH X).Rep K r
        · rw [sampledDistanceLaw_separatedMatrices_eq_zero X hX]
          exact zero_le
        · rw [indicator_of_mem (show X ∈ {X : MeasuredGHSpace.{u} |
            ¬ Coverable (underlyingGH X).Rep K r} from hX), Pi.one_apply]
          exact prob_le_one
    _ ≤ _ := lintegral_indicator_one_le _

/-! ### The forward sampled matrices without the root -/

/-- Forget the root row and column of a root-inclusive matrix. -/
def dropRootMatrix (k : ℕ) (M : Fin (k + 1) → Fin (k + 1) → ℝ) : Fin k → Fin k → ℝ :=
  fun i j ↦ M i.succ j.succ

/-- Removing the root row and column is continuous. -/
theorem continuous_dropRootMatrix (k : ℕ) : Continuous (dropRootMatrix k) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply j.succ).comp (continuous_apply i.succ)

/-- For every exponent `α`, the annealed sampled-distance matrices of the scaled
forward measured trees are the non-root blocks of the root-inclusive matrices
of `TreeSampling.forwardSampledDistanceLaw`. This generalizes
`annealedDistanceLaw_forwardMeasuredTreeLaw` beyond `α = 1/2`. -/
theorem annealedDistanceLaw_forwardMeasuredTreeLaw_eq_dropRoot (x : ℕ → ℕ → ℤ) (α : ℝ)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    annealedDistanceLaw (forwardMeasuredTreeLaw x α n) k =
      (TreeSampling.forwardSampledDistanceLaw (companionSchedule (x n)) α n k).map
        (dropRootMatrix k) := by
  have hc : 0 < 1 / (n : ℝ) ^ (1 - α) :=
    one_div_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  have hg : Measurable (fun q : TreeSampling.Forward × (Fin k → ℕ) ↦
      fun i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / (n : ℝ) ^ (1 - α)) :=
    measurable_from_prod_countable_left fun _ ↦ measurable_from_top
  have hrhs : ((TreeSampling.forwardSampledDistanceLaw (companionSchedule (x n)) α n k).map
      (dropRootMatrix k) : Measure (Fin k → Fin k → ℝ)) =
      (TreeSampling.sampledForwardLaw (companionSchedule (x n)) n k).map
        (fun q i j ↦ (q.1.graph.dist (q.2 i) (q.2 j) : ℝ) / (n : ℝ) ^ (1 - α)) := by
    change Measure.map (dropRootMatrix k) (Measure.map (TreeSampling.forwardDistanceMatrix α n k)
      (TreeSampling.sampledForwardLaw (companionSchedule (x n)) n k)) = _
    rw [Measure.map_map (continuous_dropRootMatrix k).measurable
        (TreeSampling.measurable_forwardDistanceMatrix α n k)]
    rfl
  apply ProbabilityMeasure.toMeasure_injective
  rw [hrhs]
  ext E hE
  rw [annealedDistanceLaw, continuousMixture_apply _ _ hE]
  change ∫⁻ X, _ ∂((freezingTreeLaw x n).map (fun s ↦ toMeasuredGHSpace
    (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - α)) s))) = _
  rw [lintegral_map (measurable_sampledDistanceLaw_apply k hE) measurable_from_top,
    Measure.map_apply hg hE, TreeSampling.sampledForwardLaw,
    Measure.bind_apply (hg hE) measurable_from_top.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Freezing1.Forward.treeLaw_valid (companionSchedule (x n)) n] with s hs
  change (iidDistanceLaw (forwardMeasuredSpace (1 / (n : ℝ) ^ (1 - α)) s) k :
    Measure (Fin k → Fin k → ℝ)) E = _
  rw [forward_iidDistanceLaw_apply hs hc k hE, TreeSampling.forwardKernel,
    Measure.map_apply (measurable_of_countable _) (hg hE)]
  congr 1
  ext v
  simp only [mem_ofPred_eq, mem_preimage, one_div_mul_eq_div]

/-- Off-diagonal non-root entries of the star limit are sums of two branch lengths. -/
theorem dropRootMatrix_sourceStarMatrixMap {k : ℕ} (b : Fin k → ℝ) {i j : Fin k}
    (hij : i ≠ j) : dropRootMatrix k (sourceStarMatrixMap b) i j = b i + b j := by
  change sourceStarMatrixMap b i.succ j.succ = _
  rw [sourceStarMatrixMap_offDiag b ((Fin.succ_injective _).ne hij),
    sourceBranchCoordinate_succ, sourceBranchCoordinate_succ]

/-! ### Many long independent branches -/

/-- **Block bound.** Among `(K + 1) m` iid real variables, the event that no
`K + 1` distinct indices carry values above `r` forces one of `K + 1` disjoint
blocks of size `m` to lie in `Iic r`. -/
theorem pi_not_exists_injective_lt_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (K m : ℕ)
    (r : ℝ) :
    Measure.pi (fun _ : Fin ((K + 1) * m) ↦ ν)
      {b | ¬ ∃ φ : Fin (K + 1) → Fin ((K + 1) * m), Function.Injective φ ∧ ∀ a, r < b (φ a)} ≤
      ((K : ℝ≥0∞) + 1) * ν (Iic r) ^ m := by
  classical
  let e : Fin (K + 1) × Fin m ≃ Fin ((K + 1) * m) := finProdFinEquiv
  let S : Fin (K + 1) → Set (Fin ((K + 1) * m) → ℝ) := fun j ↦
    Set.pi univ (fun i ↦ if (e.symm i).1 = j then Iic r else univ)
  have hsub : {b : Fin ((K + 1) * m) → ℝ | ¬ ∃ φ : Fin (K + 1) → Fin ((K + 1) * m),
      Function.Injective φ ∧ ∀ a, r < b (φ a)} ⊆ ⋃ j, S j := by
    intro b hb
    by_contra hno
    simp only [mem_iUnion, not_exists] at hno
    apply hb
    have hj : ∀ j, ∃ i, (e.symm i).1 = j ∧ r < b i := by
      intro j
      have h := hno j
      simp only [S, Set.mem_pi, mem_univ, true_implies, not_forall] at h
      obtain ⟨i, hi⟩ := h
      split_ifs at hi with hij
      · exact ⟨i, hij, not_le.mp hi⟩
      · exact absurd (mem_univ _) hi
    choose φ hφ hr using hj
    refine ⟨φ, fun a a' h ↦ ?_, hr⟩
    rw [← hφ a, ← hφ a', h]
  have hS : ∀ j, Measure.pi (fun _ : Fin ((K + 1) * m) ↦ ν) (S j) = ν (Iic r) ^ m := by
    intro j
    rw [Measure.pi_pi]
    calc
      ∏ i, ν (if (e.symm i).1 = j then Iic r else univ) =
          ∏ p : Fin (K + 1) × Fin m, ν (if p.1 = j then Iic r else univ) :=
        Equiv.prod_comp e.symm (fun p ↦ ν (if p.1 = j then Iic r else univ))
      _ = ∏ j' : Fin (K + 1), ∏ _l : Fin m, ν (if j' = j then Iic r else univ) :=
        Fintype.prod_prod_type _
      _ = ∏ j' : Fin (K + 1), if j' = j then ν (Iic r) ^ m else 1 := by
        refine Finset.prod_congr rfl fun j' _ ↦ ?_
        split_ifs <;> simp
      _ = ν (Iic r) ^ m := by simp
  calc
    _ ≤ Measure.pi (fun _ : Fin ((K + 1) * m) ↦ ν) (⋃ j, S j) := measure_mono hsub
    _ ≤ ∑ j, Measure.pi (fun _ : Fin ((K + 1) * m) ↦ ν) (S j) := measure_iUnion_fintype_le _ _
    _ = ((K : ℝ≥0∞) + 1) * ν (Iic r) ^ m := by
      simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]

/-- The limiting non-root star matrix with `(K + 1) m` samples fails to be
`2r`-separated with probability at most `(K + 1) P(h ≤ r)^m`. -/
theorem branchLimit_separatedMatrices_compl_le (f : ℝ → ℝ) (K m : ℕ) (r : ℝ) :
    ((((iidSourceBranchLimit f ((K + 1) * m)).map sourceStarMatrixMap).map
      (dropRootMatrix ((K + 1) * m)) : ProbabilityMeasure _) :
        Measure (Fin ((K + 1) * m) → Fin ((K + 1) * m) → ℝ))
      (separatedMatrices ((K + 1) * m) K r)ᶜ ≤
      ((K : ℝ≥0∞) + 1) *
        (profileProbabilityMeasure.map (sourceBranchPrimitive f) : Measure ℝ) (Iic r) ^ m := by
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (continuous_dropRootMatrix _).measurable
      (continuous_sourceStarMatrixMap _).measurable,
    Measure.map_apply ((continuous_dropRootMatrix _).comp
      (continuous_sourceStarMatrixMap _)).measurable
      (isOpen_separatedMatrices _ K r).measurableSet.compl,
    iidSourceBranchLimit, ProbabilityMeasure.toMeasure_pi]
  refine (measure_mono ?_).trans (pi_not_exists_injective_lt_le _ K m r)
  rintro b hb ⟨φ, hφ, hr⟩
  refine hb ⟨φ, fun a a' haa' ↦ ?_⟩
  change 2 * r < dropRootMatrix _ (sourceStarMatrixMap b) (φ a) (φ a')
  rw [dropRootMatrix_sourceStarMatrixMap b (hφ.ne haa')]
  linarith [hr a, hr a']

/-- A fixed radius `r > 0` such that a limiting branch length is at most `r`
with probability at most `1/2`. This is the S08 choice of radius. -/
theorem exists_sourceBranch_Iic_le {f : ℝ → ℝ} (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hint : Integrable (fun t ↦ 1 / f t) profileMeasure) :
    ∃ r > 0,
      (profileProbabilityMeasure.map (sourceBranchPrimitive f) : Measure ℝ) (Iic r) ≤ 2⁻¹ := by
  have hmono := profilePrimitive_strictMonoOn hint (positiveProfile_reciprocal hf)
  have h0 : profilePrimitive (fun t ↦ 1 / f t) 0 = 0 := by simp [profilePrimitive]
  have hhalf : 0 < profilePrimitive (fun t ↦ 1 / f t) (1 / 2) := by
    have h := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
      (by norm_num)
    rwa [h0] at h
  have hP := continuous_profilePrimitive hint
  refine ⟨profilePrimitive (fun t ↦ 1 / f t) (1 / 2) / 2, by positivity, ?_⟩
  rw [← profilePrimitive_reciprocal_map_eq, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hP.measurable measurableSet_Iic]
  change (volume.restrict (Icc (0 : ℝ) 1)) _ ≤ _
  rw [Measure.restrict_apply (hP.measurable measurableSet_Iic)]
  calc
    volume (profilePrimitive (fun t ↦ 1 / f t) ⁻¹'
        Iic (profilePrimitive (fun t ↦ 1 / f t) (1 / 2) / 2) ∩ Icc 0 1) ≤
        volume (Icc (0 : ℝ) (1 / 2)) := by
      refine measure_mono fun t ⟨ht, ht01⟩ ↦ ⟨ht01.1, ?_⟩
      by_contra hlt
      have hle := (hmono.le_iff_le (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num) ht01).mpr
        (not_le.mp hlt).le
      simp only [mem_preimage, mem_Iic] at ht
      linarith
    _ = 2⁻¹ := by
      rw [Real.volume_Icc, sub_zero, one_div, ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]

/-! ### Compact sets of GH classes -/

/-- A compact set of GH classes has uniformly bounded covering numbers at each positive scale. -/
theorem exists_coverable_of_isCompact {C : Set GHSpace} (hC : IsCompact C) {r : ℝ}
    (hr : 0 < r) : ∃ K : ℕ, ∀ p ∈ C, Coverable p.Rep K r := by
  classical
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact hC (show 0 < r / 4 by positivity)
  have hK (p : GHSpace) : ∃ K : ℕ, Coverable p.Rep K (r / 2) :=
    exists_coverable p.Rep (by positivity)
  choose K hK using hK
  refine ⟨ht.toFinset.sup K, fun q hq ↦ ?_⟩
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hcov hq)
  have h := coverable_of_dist_lt (show dist p q < r / 4 by
    rw [dist_comm]
    exact mem_ball.mp hqp) (hK p)
  exact h.mono (Finset.le_sup (ht.mem_toFinset.mpr hp)) (by linarith)

/-! ### Main statements -/

/-- Covering numbers blow up at a small fixed scale (U04b, with the S08
correction): there is `r > 0` such that, for every `K`, the probability that
the scaled tree is not covered by `K` open `r`-balls tends to one. -/
theorem supercritical_not_coverable {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) :
    ∃ r > 0, ∀ K : ℕ, Tendsto (fun n ↦ (forwardMeasuredTreeLaw x α n : Measure MeasuredGHSpace.{0})
      {X | ¬ Coverable (underlyingGH X).Rep K r}) atTop (𝓝 1) := by
  obtain ⟨r, hr, hq⟩ := exists_sourceBranch_Iic_le hf hL1.1
  refine ⟨r, hr, fun K ↦ ?_⟩
  set u : ℕ → ℝ≥0∞ := fun n ↦ (forwardMeasuredTreeLaw x α n : Measure MeasuredGHSpace.{0})
    {X | ¬ Coverable (underlyingGH X).Rep K r}
  let L : ∀ k : ℕ, ProbabilityMeasure (Fin k → Fin k → ℝ) := fun k ↦
    ((iidSourceBranchLimit f k).map sourceStarMatrixMap).map (dropRootMatrix k)
  have hA (k : ℕ) : (L k : Measure (Fin k → Fin k → ℝ)) (separatedMatrices k K r) ≤
      liminf u atTop := by
    have hlim : Tendsto (fun n ↦ annealedDistanceLaw (forwardMeasuredTreeLaw x α n) k) atTop
        (𝓝 (L k)) := by
      have h := ((ProbabilityMeasure.continuous_map (continuous_dropRootMatrix k)).tendsto _).comp
        (supercritical_distance_matrix_limit hx hαhalf hα1 hf hL1 h2 k)
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (annealedDistanceLaw_forwardMeasuredTreeLaw_eq_dropRoot x α hn k).symm
    refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
      (isOpen_separatedMatrices k K r)).trans ?_
    exact liminf_le_liminf (Eventually.of_forall fun n ↦
      annealedDistanceLaw_separatedMatrices_le _ k K r)
  have hB (m : ℕ) : 1 ≤ (L ((K + 1) * m) : Measure _) (separatedMatrices ((K + 1) * m) K r) +
      ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m := by
    have hsum := measure_add_measure_compl (μ := (L ((K + 1) * m) : Measure _))
      (isOpen_separatedMatrices ((K + 1) * m) K r).measurableSet
    rw [measure_univ] at hsum
    calc
      (1 : ℝ≥0∞) = _ := hsum.symm
      _ ≤ _ := by
        gcongr
        refine (branchLimit_separatedMatrices_compl_le f K m r).trans ?_
        gcongr
  rw [tendsto_order]
  refine ⟨fun a ha ↦ ?_, fun a ha ↦ Eventually.of_forall fun n ↦ prob_le_one.trans_lt ha⟩
  have hpow : Tendsto (fun m : ℕ ↦ ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      ENNReal.one_half_lt_one)
      (Or.inr (show (K : ℝ≥0∞) + 1 ≠ ⊤ from by finiteness))
    simpa using h
  obtain ⟨m, hm⟩ := (hpow.eventually (gt_mem_nhds (tsub_pos_of_lt ha))).exists
  have h1 : a + ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m <
      (L ((K + 1) * m) : Measure _) (separatedMatrices ((K + 1) * m) K r) +
        ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m :=
    (lt_tsub_iff_left.mp hm).trans_le (hB m)
  have h3 : a < (L ((K + 1) * m) : Measure _) (separatedMatrices ((K + 1) * m) K r) := by
    by_contra hcon
    have h4 : (L ((K + 1) * m) : Measure _) (separatedMatrices ((K + 1) * m) K r) +
        ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m ≤ a + ((K : ℝ≥0∞) + 1) * 2⁻¹ ^ m := by
      gcongr
      exact not_lt.mp hcon
    exact lt_irrefl _ (h1.trans_le h4)
  exact eventually_lt_of_lt_liminf (h3.trans_le (hA _))

/-- **Supercritical non-tightness (U04b).** For `α ∈ (1/2, 1)`, the laws of
the scaled forward measured trees are not tight in the GHP topology. -/
theorem supercritical_not_tight {x : ℕ → ℕ → ℤ} {α : ℝ} {f : ℝ → ℝ}
    (hx : ∀ n, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hαhalf : 1 / 2 < α) (hα1 : α < 1)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x α (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x α (fun t ↦ 1 / f t)) :
    ¬ IsTightMeasureSet
      (range fun n ↦ (forwardMeasuredTreeLaw x α n : Measure MeasuredGHSpace.{0})) := by
  intro htight
  obtain ⟨r, hr, hK⟩ := supercritical_not_coverable hx hαhalf hα1 hf hL1 h2
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨C, hC, hCmass⟩ := htight 2⁻¹ (by norm_num)
  obtain ⟨K, hKC⟩ := exists_coverable_of_isCompact (hC.image continuous_underlyingGH) hr
  have hle (n : ℕ) : (forwardMeasuredTreeLaw x α n : Measure MeasuredGHSpace.{0})
      {X | ¬ Coverable (underlyingGH X).Rep K r} ≤ 2⁻¹ :=
    (measure_mono (show {X : MeasuredGHSpace.{0} | ¬ Coverable (underlyingGH X).Rep K r} ⊆ Cᶜ
      from fun X hX hXC ↦ hX (hKC _ (mem_image_of_mem _ hXC)))).trans
      (hCmass _ (mem_range_self n))
  obtain ⟨n, hn⟩ := ((hK K).eventually (lt_mem_nhds
    ENNReal.one_half_lt_one)).exists
  exact (hle n).not_gt hn

end Freezing2
