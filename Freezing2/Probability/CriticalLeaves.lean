module

public import Freezing2.Geometry.RealTreeDegree
public import Freezing2.Probability.CriticalMergeAtoms

/-!
# Leaves of the critical limit (Theorem `thm:properties` (1), M04a)

The mass measure of `𝒯(f)` gives full measure to its leaves, almost surely. A point
of degree at least two lies strictly between two other points; with full support,
iid samples would then have one sample strictly between two others with positive
probability. In the limit, such configurations force a coalescence time to equal a
birth time, which has probability zero because pairs merge at a locally integrable
rate.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2

open RealTree MeasuredGHSpace

universe u

/-- The mass measure of every representative of `X` gives full measure to its leaves. -/
def LeavesCarryMass (X : MeasuredGHSpace.{u}) : Prop :=
  ∀ Y : CompactMeasuredSpace.{u}, toMeasuredGHSpace Y = X →
    ∀ᵐ y ∂(Y.law : Measure Y), IsLeaf y

namespace CriticalGenealogy

open ReverseHistory ReverseCoalescence

variable {k : ℕ}

theorem profilePrimitive_lt {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hpos : ∀ᵐ t ∂profileMeasure, 0 < g t) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    profilePrimitive g s < profilePrimitive g t := by
  rw [profilePrimitive_eq_setIntegral g hs (hst.le.trans ht),
    profilePrimitive_eq_setIntegral g (hs.trans hst.le) ht]
  have hint : IntegrableOn g (Icc 0 t) volume := by
    have := hg.integrableOn (s := Icc 0 t)
    have hsub0 : Icc 0 t ⊆ Icc (0 : ℝ) 1 := fun u hu ↦ ⟨hu.1, hu.2.trans ht⟩
    rwa [IntegrableOn, Measure.restrict_restrict_of_subset hsub0] at this
  have hsub := setIntegral_Icc_sub_left hs hst.le hint
  have hsubset : Icc s t ⊆ Icc (0 : ℝ) 1 := fun u hu ↦ ⟨hs.trans hu.1, hu.2.trans ht⟩
  have hμ : profileMeasure (Icc s t) ≠ 0 := by
    rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hsubset, Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hst))
  have hp := setIntegral_pos_of_ae_pos hg hpos hμ
  rw [Measure.restrict_restrict_of_subset hsubset] at hp
  have : (∫ u in Icc 0 t, g u) - ∫ u in Icc 0 s, g u = ∫ u in Icc s t, g u := hsub
  linarith

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}

theorem criticalGenealogyLimit_unitCube (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) (unitCube k) = 1 := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) (isCompact_unitCube k).isClosed
  have hone : ∀ n, (genealogyLaw hx k n : Measure (GenealogySpace k)) (unitCube k) = 1 := fun n ↦
    (prob_compl_eq_zero_iff (isCompact_unitCube k).isClosed.measurableSet).mp
      (genealogyLaw_unitCube_compl hx n)
  have hconst : (fun n ↦ (genealogyLaw hx k n : Measure (GenealogySpace k)) (unitCube k)) =
      fun _ ↦ 1 := funext hone
  rw [hconst, limsup_const] at hlim
  exact le_antisymm prob_le_one hlim

/-- Three sampled points: the first lies strictly off the segment joining the other
two, and the first two are distinct. -/
def strictTriangle : Set (Fin 3 → Fin 3 → ℝ) :=
  {M | M 1 2 < M 1 0 + M 0 2 ∧ 0 < M 0 1}

theorem isOpen_strictTriangle : IsOpen strictTriangle := by
  have hc : ∀ i j : Fin 3, Continuous fun M : Fin 3 → Fin 3 → ℝ ↦ M i j := fun i j ↦
    (continuous_apply j).comp (continuous_apply i)
  exact (isOpen_lt (hc 1 2) ((hc 1 0).add (hc 0 2))).inter (isOpen_lt continuous_const (hc 0 1))

/-- **Limiting triangles are strict.** -/
theorem criticalDistanceLaw_strictTriangle (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) :
    (criticalDistanceLaw g 3 : Measure (Fin 3 → Fin 3 → ℝ)) strictTriangleᶜ = 0 := by
  set μ := (criticalGenealogyLimit g 3 : Measure (GenealogySpace 3))
  have hcont := continuous_distanceOfGenealogy (k := 3) hL1.1
  simp only [criticalDistanceLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply hcont.measurable isOpen_strictTriangle.measurableSet.compl]
  have hsupp : μ (genealogySupport 3)ᶜ = 0 := (prob_compl_eq_zero_iff
    (isClosed_genealogySupport 3).measurableSet).mpr
      (criticalGenealogyLimit_support hx hL1 hpos h2 3)
  have hcube : μ (unitCube 3)ᶜ = 0 := (prob_compl_eq_zero_iff
    (isCompact_unitCube 3).isClosed.measurableSet).mpr (criticalGenealogyLimit_unitCube hx hL1 hpos h2 3)
  have a1 := criticalGenealogyLimit_merge_ne_birth hx hL1 hpos h2 (show (0 : Fin 3) ≠ 1 by decide)
  have a2 := criticalGenealogyLimit_merge_ne_birth hx hL1 hpos h2 (show (1 : Fin 3) ≠ 0 by decide)
  have a3 := criticalGenealogyLimit_merge_ne_birth hx hL1 hpos h2 (show (0 : Fin 3) ≠ 2 by decide)
  apply measure_mono_null (t := (genealogySupport 3)ᶜ ∪ (unitCube 3)ᶜ ∪
    ({z | z.2 0 1 = z.1 0} ∪ {z | z.2 1 0 = z.1 1} ∪ {z | z.2 0 2 = z.1 0}))
  · intro z hz
    by_contra hnot
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq] at hnot
    obtain ⟨⟨hS, hC⟩, ⟨h01, h10⟩, h02⟩ := hnot
    obtain ⟨hdiag, hsymm, hultra⟩ := hS
    apply hz
    have hle : ∀ i j : Fin 3, z.2 i j ≤ z.1 i := by
      intro i j
      have := hultra i i j
      rw [hsymm j i, min_self, hdiag] at this
      exact this
    have hcube : ∀ i, z.1 i ∈ Icc (0 : ℝ) 1 := fun i ↦ hC.1 i (mem_univ _)
    have hcube2 : ∀ i j, z.2 i j ∈ Icc (0 : ℝ) 1 := fun i j ↦ hC.2 i (mem_univ _) j (mem_univ _)
    have hP := monotone_profilePrimitive hL1.1 (hpos.mono fun _ h ↦ h.le)
    have hlt : ∀ i j, z.2 i j < z.1 i → profilePrimitive g (z.2 i j) < profilePrimitive g (z.1 i) :=
      fun i j h ↦ profilePrimitive_lt hL1.1 hpos (hcube2 i j).1 h (hcube i).2
    have l01 : z.2 0 1 < z.1 0 := lt_of_le_of_ne (hle 0 1) h01
    have l10 : z.2 1 0 < z.1 1 := lt_of_le_of_ne (hle 1 0) h10
    have l02 : z.2 0 2 < z.1 0 := lt_of_le_of_ne (hle 0 2) h02
    have p01 := hlt 0 1 l01
    have p10 := hlt 1 0 l10
    have p02 := hlt 0 2 l02
    have hu := hultra 1 2 0
    rw [hsymm 1 0] at hu p10
    simp only [strictTriangle, mem_ofPred_eq, distanceOfGenealogy]
    simp only [show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
      show (0 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    rw [hsymm 1 0]
    refine ⟨?_, by linarith⟩
    have hmono := hP hu
    rcases le_total (z.2 0 1) (z.2 0 2) with h | h
    · rw [min_eq_left h] at hmono
      have := hP h
      linarith
    · rw [min_eq_right h] at hmono
      have := hP h
      linarith
  · exact measure_union_null (measure_union_null hsupp hcube)
      (measure_union_null (measure_union_null a1 a2) a3)

end CriticalGenealogy

namespace RealTree

variable {X : Type*} [MetricSpace X]

/-- Points close enough to the ends of a segment through `x` still have `x` between them. -/
theorem between_of_close (h4 : FourPoint X) {x y z y' z' : X}
    (hbet : dist y x + dist x z = dist y z) (hy' : dist y y' < dist x y)
    (hz' : dist z z' < dist x z) : dist y' x + dist x z' = dist y' z' := by
  have g0 : gromovProduct x y z = 0 := by
    unfold gromovProduct
    rw [dist_comm x y]
    linarith
  have gy : 0 < gromovProduct x y y' := by
    unfold gromovProduct
    linarith [dist_triangle x y' y, dist_comm y' y]
  have gz : 0 < gromovProduct x z' z := by
    unfold gromovProduct
    linarith [dist_triangle x z' z, dist_comm z' z, dist_comm z z']
  have h1 := gromovProduct_ge_min h4 x y z y'
  rw [g0] at h1
  have e1 : gromovProduct x y' z = 0 := by
    rcases min_le_iff.mp h1 with h | h
    · exact absurd h (not_le.mpr gy)
    · exact le_antisymm h (gromovProduct_nonneg x y' z)
  have h2 := gromovProduct_ge_min h4 x y' z z'
  rw [e1] at h2
  have e2 : gromovProduct x y' z' = 0 := by
    rcases min_le_iff.mp h2 with h | h
    · exact le_antisymm h (gromovProduct_nonneg x y' z')
    · exact absurd h (not_le.mpr gz)
  unfold gromovProduct at e2
  rw [dist_comm x y'] at e2
  linarith

end RealTree

namespace CriticalGenealogy

/-- An annealed null event is null for the sampled law of almost every space. -/
theorem ae_sampledDistanceLaw_null {Q : ProbabilityMeasure MeasuredGHSpace.{0}} {k : ℕ}
    {F : Set (Fin k → Fin k → ℝ)} (hF : MeasurableSet F)
    (h : (annealedDistanceLaw Q k : Measure (Fin k → Fin k → ℝ)) F = 0) :
    ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}),
      (sampledDistanceLaw k X : Measure (Fin k → Fin k → ℝ)) F = 0 := by
  rw [annealedDistanceLaw, continuousMixture_apply Q (continuous_sampledDistanceLaw k) hF] at h
  have hm : Measurable fun X ↦ (sampledDistanceLaw k X : Measure (Fin k → Fin k → ℝ)) F :=
    (Measure.measurable_coe hF).comp
      (measurable_toMeasure_of_continuous (continuous_sampledDistanceLaw k))
  exact (lintegral_eq_zero_iff hm).mp h

/-- **Leaves carry the mass (geometric part).** In a fully supported compact real tree
where three iid points form strict triangles almost surely, almost every point is a
leaf. -/
theorem ae_isLeaf_of_strictTriangle (Y : CompactMeasuredSpace.{0})
    (hfs : Measure.IsOpenPosMeasure (Y.law : Measure Y)) (h4 : FourPoint Y) (hT : IsRealTree Y)
    (h3 : (iidDistanceLaw Y 3 : Measure (Fin 3 → Fin 3 → ℝ)) strictTriangleᶜ = 0) :
    ∀ᵐ y ∂(Y.law : Measure Y), IsLeaf y := by
  set μ := (Y.law : Measure Y)
  have hmeasB : MeasurableSet (distanceMatrix 3 ⁻¹' strictTriangleᶜ : Set (Fin 3 → Y)) :=
    (continuous_distanceMatrix 3).measurable isOpen_strictTriangle.measurableSet.compl
  have hpi : Measure.pi (fun _ : Fin 3 ↦ μ) (distanceMatrix 3 ⁻¹' strictTriangleᶜ) = 0 := by
    simp only [iidDistanceLaw, iidDistanceLawOn, ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.toMeasure_pi] at h3
    rwa [Measure.map_apply (continuous_distanceMatrix 3).measurable
      isOpen_strictTriangle.measurableSet.compl] at h3
  -- the space has two distinct points
  have hnontriv : ∃ y y' : Y, y ≠ y' := by
    by_contra hall
    push Not at hall
    have huniv : distanceMatrix 3 ⁻¹' strictTriangleᶜ = (univ : Set (Fin 3 → Y)) := by
      ext v
      simp only [mem_preimage, mem_compl_iff, strictTriangle, mem_ofPred_eq, distanceMatrix,
        mem_univ, iff_true, not_and, not_lt]
      intro _
      rw [hall (v 0) (v 1), dist_self]
    rw [huniv, measure_univ] at hpi
    exact one_ne_zero hpi
  -- Fubini over the first coordinate
  set F : Y × (Y × Y) → (Fin 3 → Y) := fun p ↦ ![p.1, p.2.1, p.2.2]
  have hF : Measurable F := by
    refine measurable_pi_iff.mpr fun i ↦ ?_
    fin_cases i
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  have hpimap : Measure.pi (fun _ : Fin 3 ↦ μ) = (μ.prod (μ.prod μ)).map F := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply hF (MeasurableSet.univ_pi hs)]
    have : F ⁻¹' Set.pi univ s = s 0 ×ˢ (s 1 ×ˢ s 2) := by
      ext p
      simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
        IsEmpty.forall_iff, and_true, mem_prod, F]
      simp
    rw [this, Measure.prod_prod, Measure.prod_prod, Fin.prod_univ_three, mul_assoc]
  set S : Set (Y × (Y × Y)) := F ⁻¹' (distanceMatrix 3 ⁻¹' strictTriangleᶜ)
  have hS : MeasurableSet S := hF hmeasB
  have hprod : (μ.prod (μ.prod μ)) S = 0 := by
    rw [← Measure.map_apply hF hmeasB, ← hpimap]
    exact hpi
  have hfib := (Measure.measure_prod_null hS).mp hprod
  filter_upwards [hfib] with x hx
  by_contra hleaf
  have h0 : degree x ≠ 0 := by
    intro h0
    obtain ⟨y, y', hyy'⟩ := hnontriv
    have hall := (degree_eq_zero_iff x).mp h0
    exact hyy' ((hall y).trans (hall y').symm)
  have hdeg : 2 ≤ degree x := by
    have h1 : degree x ≠ 1 := hleaf
    generalize degree x = d at h0 h1 ⊢
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have hm0 : m ≠ 0 := by exact_mod_cast h0
      have hm1 : m ≠ 1 := by exact_mod_cast h1
      exact_mod_cast (show 2 ≤ m by omega)
  obtain ⟨y, z, hy, hz, hbet⟩ := exists_between_of_two_le_degree hT hdeg
  have hry : 0 < dist x y := dist_pos.mpr (Ne.symm hy)
  have hrz : 0 < dist x z := dist_pos.mpr (Ne.symm hz)
  have hsub : Metric.ball y (dist x y) ×ˢ Metric.ball z (dist x z) ⊆ Prod.mk x ⁻¹' S := by
    rintro ⟨w0, w1⟩ ⟨hw0, hw1⟩
    simp only [mem_preimage, S, F, mem_compl_iff, strictTriangle, mem_ofPred_eq, distanceMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, not_and, not_lt]
    intro h
    have hw0' : dist y w0 < dist x y := by
      have := Metric.mem_ball.mp hw0
      rwa [dist_comm] at this
    have hw1' : dist z w1 < dist x z := by
      have := Metric.mem_ball.mp hw1
      rwa [dist_comm] at this
    have heq := RealTree.between_of_close h4 hbet hw0' hw1'
    exact absurd h (not_lt.mpr heq.le)
  have hpos : 0 < (μ.prod μ) (Metric.ball y (dist x y) ×ˢ Metric.ball z (dist x z)) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos (Metric.isOpen_ball.measure_ne_zero μ (Metric.nonempty_ball.mpr hry))
      (Metric.isOpen_ball.measure_ne_zero μ (Metric.nonempty_ball.mpr hrz))
  have := (measure_mono hsub).trans_eq hx
  exact (lt_irrefl _ (hpos.trans_le this))

end CriticalGenealogy

/-- **Theorem `thm:properties` (1) (M04a).** Under the hypotheses of `thm:critique`,
almost surely the limit `𝒯(f)` is a compact real tree whose mass measure has full
support and gives full measure to the set of leaves. -/
theorem criticalTreeLaw_ae_leaves {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      HasFullSupport X ∧ IsRealTree (underlyingGH X).Rep ∧ LeavesCarryMass X := by
  open CriticalGenealogy in
  obtain ⟨hconv, hann, hfull⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  have hxa := admissible_initialRowExtension hx
  have hL1a := hasL1ReciprocalProfile_initialRowExtension hL1
  have hposa := positiveProfile_reciprocal hf
  have h2a := hasLocalSquareMomentProfile_initialRowExtension h2
  have h3 : ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      (sampledDistanceLaw 3 X : Measure (Fin 3 → Fin 3 → ℝ)) strictTriangleᶜ = 0 :=
    ae_sampledDistanceLaw_null isOpen_strictTriangle.measurableSet.compl (by
      rw [hann 3]; exact criticalDistanceLaw_strictTriangle hxa hL1a hposa h2a)
  have h4 : (annealedDistanceLaw (criticalTreeLaw (fun t ↦ 1 / f t)) 4 :
      Measure (Fin 4 → Fin 4 → ℝ)) (fourPointMatrices 4) = 1 := by
    rw [hann 4]
    exact criticalDistanceLaw_fourPoint hxa hL1a hposa h2a 4
  have hfp := ae_fourPoint_of_annealed h4 hfull
  have hmid := ae_hasMidpoints_of_tendsto hconv fun ε hε ↦ forward_ae_approxMidpoints x hε
  have hreal := criticalTreeLaw_ae_isRealTree hx hf hL1 h2 hpop
  filter_upwards [hfull, hreal, h3, hfp, hmid] with X hfs hrt h3X hfpX hmidX
  refine ⟨hfs, hrt, fun Y hY ↦ ?_⟩
  subst hY
  rw [hasFullSupport_toMeasuredGHSpace] at hfs
  rw [sampledDistanceLaw_toMeasuredGHSpace] at h3X
  rw [underlyingGH_toMeasuredGHSpace, fourPoint_toGHSpace_rep_iff] at hfpX
  rw [underlyingGH_toMeasuredGHSpace] at hmidX
  have hmidY : HasMidpoints Y := by
    apply hasMidpoints_of_approx
    intro ε hε
    refine (approxMidpoints_toGHSpace_rep_iff Y).mp fun a b ↦ ?_
    obtain ⟨m, hm1, hm2⟩ := hmidX a b
    exact ⟨m, by rw [hm1, sub_self, abs_zero]; exact hε.le, by rw [hm2, sub_self, abs_zero]; exact hε.le⟩
  exact ae_isLeaf_of_strictTriangle Y hfs hfpX (isRealTree_of_fourPoint hfpX hmidY) h3X

end Freezing2
