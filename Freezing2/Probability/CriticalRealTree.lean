module

public import Freezing2.Geometry.GHRealTree
public import Freezing2.Probability.CriticalScalingLimit
public import Freezing2.Probability.CoalescenceMetric

/-!
# The critical limit is a real tree (U26)

The limit `criticalTreeLaw (1/f)` of Theorem `thm:critique` is almost surely a
compact real tree.

* **Four-point condition.** Limiting sampled distances have the form
  `P(b_i) + P(b_j) - 2 P(c_ij)` with `P` nondecreasing and coalescence times
  satisfying `c_ij ≥ min(c_il, c_lj)`, a closed property inherited from the actual
  discrete genealogies. Such matrices satisfy the four-point condition, hence so
  do iid samples of almost every limit space, hence (full support) the whole space.
* **Midpoints.** The scaled finite graphs have `c/2`-approximate midpoints (walk
  halfway along a shortest path). This closed Gromov–Hausdorff property passes to
  the weak limit by the portmanteau theorem, and compactness gives exact midpoints.

A complete `0`-hyperbolic space with midpoints is a real tree (`Geometry/RealTree`).
The source argues instead through edge-realizations of the finite trees.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace Freezing2.RealTree

section Ultrametric

variable {ι : Type*} {m : ι → ι → ℝ}

theorem ultra_key (hs : ∀ a b, m a b = m b a) (hu : ∀ a b c, min (m a c) (m c b) ≤ m a b)
    {i j l w : ι} (h1 : m i l ≤ m i j) (h2 : m j w ≤ m i j) (h3 : m i w ≤ m i j)
    (h4 : m j l ≤ m i j) :
    m i l + m j w = m i w + m j l ∧ m i l + m j w ≤ m i j + m l w := by
  have a1 : min (m i j) (m j l) ≤ m i l := hu i l j
  have a2 : min (m i j) (m i l) ≤ m j l := by have := hu j l i; rwa [hs j i] at this
  have a3 : min (m i j) (m j w) ≤ m i w := hu i w j
  have a4 : min (m i j) (m i w) ≤ m j w := by have := hu j w i; rwa [hs j i] at this
  have a5 : min (m i l) (m i w) ≤ m l w := by have := hu l w i; rwa [hs l i] at this
  rw [min_eq_right h4] at a1
  rw [min_eq_right h1] at a2
  rw [min_eq_right h2] at a3
  rw [min_eq_right h3] at a4
  have e1 : m i l = m j l := le_antisymm a2 a1
  have e2 : m i w = m j w := le_antisymm a4 a3
  refine ⟨by rw [e1, e2]; ring, ?_⟩
  rcases le_total (m i l) (m i w) with h | h
  · rw [min_eq_left h] at a5
    linarith
  · rw [min_eq_right h] at a5
    linarith

/-- An ultrametric-type closeness gives the four-point inequality for pair sums. -/
theorem ultra_fourPoint (hs : ∀ a b, m a b = m b a) (hu : ∀ a b c, min (m a c) (m c b) ≤ m a b)
    (i j l w : ι) : min (m i l + m j w) (m i w + m j l) ≤ m i j + m l w := by
  set M := max (max (max (m i j) (m l w)) (max (m i l) (m j w))) (max (m i w) (m j l)) with hM
  have b1 : m i j ≤ M := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have b2 : m l w ≤ M := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have b3 : m i l ≤ M := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have b4 : m j w ≤ M := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have b5 : m i w ≤ M := le_max_of_le_right (le_max_left _ _)
  have b6 : m j l ≤ M := le_max_of_le_right (le_max_right _ _)
  have s1 := hs l i
  have s2 := hs w j
  have s3 := hs l j
  have s4 := hs w i
  have s5 := hs j i
  have s6 := hs w l
  rcases max_choice (max (max (m i j) (m l w)) (max (m i l) (m j w))) (max (m i w) (m j l))
    with hc | hc <;> rw [← hM] at hc
  · rcases max_choice (max (m i j) (m l w)) (max (m i l) (m j w)) with hd | hd <;>
      rw [hd] at hc
    · rcases max_choice (m i j) (m l w) with he | he <;> rw [he] at hc
      · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := i) (j := j) (l := l) (w := w)
          (hc ▸ b3) (hc ▸ b4) (hc ▸ b5) (hc ▸ b6)
        exact (min_le_left _ _).trans k2
      · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := l) (j := w) (l := i) (w := j)
          (by rw [← hc, s1]; exact b3) (by rw [← hc, s2]; exact b4)
          (by rw [← hc, s3]; exact b6) (by rw [← hc, s4]; exact b5)
        exact (min_le_left _ _).trans (by linarith)
    · rcases max_choice (m i l) (m j w) with he | he <;> rw [he] at hc
      · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := i) (j := l) (l := j) (w := w)
          (hc ▸ b1) (hc ▸ b2) (hc ▸ b5) (by rw [← hc, s3]; exact b6)
        exact (min_le_right _ _).trans (by linarith)
      · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := j) (j := w) (l := i) (w := l)
          (by rw [← hc, s5]; exact b1) (by rw [← hc, s6]; exact b2) (hc ▸ b6)
          (by rw [← hc, s4]; exact b5)
        exact (min_le_right _ _).trans (by linarith)
  · rcases max_choice (m i w) (m j l) with he | he <;> rw [he] at hc
    · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := i) (j := w) (l := j) (w := l)
        (hc ▸ b1) (by rw [← hc, s6]; exact b2) (hc ▸ b3) (by rw [← hc, s2]; exact b4)
      exact (min_le_left _ _).trans (by linarith)
    · obtain ⟨k1, k2⟩ := ultra_key hs hu (i := j) (j := l) (l := i) (w := w)
        (by rw [← hc, s5]; exact b1) (hc ▸ b2) (hc ▸ b4) (by rw [← hc, s1]; exact b3)
      exact (min_le_left _ _).trans (by linarith)

/-- Distances `h i + h j - 2 m i j` with ultrametric-type `m` satisfy the four-point
condition. -/
theorem fourPoint_of_ultra (h : ι → ℝ) (hs : ∀ a b, m a b = m b a)
    (hu : ∀ a b c, min (m a c) (m c b) ≤ m a b) (i j l w : ι) :
    (h i + h j - 2 * m i j) + (h l + h w - 2 * m l w) ≤
      max ((h i + h l - 2 * m i l) + (h j + h w - 2 * m j w))
        ((h i + h w - 2 * m i w) + (h j + h l - 2 * m j l)) := by
  have key := ultra_fourPoint hs hu i j l w
  rcases min_choice (m i l + m j w) (m i w + m j l) with hc | hc <;> rw [hc] at key
  · exact le_max_of_le_left (by linarith)
  · exact le_max_of_le_right (by linarith)

end Ultrametric

section Graphs

/-- Scaled connected graphs have `c/2`-approximate midpoints. -/
theorem graph_approxMidpoints {V : Type*} (G : SimpleGraph V) (hG : G.Connected) (c : ℝ)
    (hc : 0 < c) : @ApproxMidpoints (c / 2) V (scaledGraphMetric G hG c hc) := by
  let := scaledGraphMetric G hG c hc
  intro u v
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  set D := G.dist u v
  set a := D / 2
  refine ⟨p.getVert a, ?_, ?_⟩ <;>
  · have hu : G.dist u (p.getVert a) ≤ a :=
      (SimpleGraph.dist_le (p.take a)).trans (by rw [SimpleGraph.Walk.take_length]; omega)
    have hv : G.dist (p.getVert a) v ≤ D - a :=
      (SimpleGraph.dist_le (p.drop a)).trans (by rw [SimpleGraph.Walk.drop_length, hp])
    have htri : D ≤ G.dist u (p.getVert a) + G.dist (p.getVert a) v := hG.dist_triangle
    have e1 : G.dist u (p.getVert a) = a := by omega
    have e2 : G.dist (p.getVert a) v = D - a := by omega
    have ha1 : 2 * a ≤ D := by omega
    have ha2 : D ≤ 2 * a + 1 := by omega
    have r1 : (2 : ℝ) * a ≤ D := by exact_mod_cast ha1
    have r2 : (D : ℝ) ≤ 2 * a + 1 := by exact_mod_cast ha2
    first
      | show |c * (G.dist u (p.getVert a) : ℝ) - c * (G.dist u v : ℝ) / 2| ≤ c / 2
        rw [e1, abs_le]
        constructor <;> nlinarith
      | show |c * (G.dist (p.getVert a) v : ℝ) - c * (G.dist u v : ℝ) / 2| ≤ c / 2
        rw [e2, Nat.cast_sub (by omega), abs_le]
        constructor <;> nlinarith

/-- The scaled forward spaces have `c/2`-approximate midpoints. -/
theorem forwardMeasuredSpace_approxMidpoints {c : ℝ} (hc : 0 < c) (s : Freezing1.Forward.State) :
    ApproxMidpoints (c / 2) (forwardMeasuredSpace c s) := by
  by_cases h : s.tree.Connected ∧ 0 < c
  · rw [forwardMeasuredSpace, dite_eq_left_of_eq_true (eq_true h)]
    exact graph_approxMidpoints s.tree h.1 c h.2
  · rw [forwardMeasuredSpace, dite_eq_right_of_eq_false (eq_false h)]
    intro x y
    have hxy : x = y := Subsingleton.elim (α := Unit) x y
    subst hxy
    refine ⟨x, ?_, ?_⟩ <;> simp only [dist_self, zero_div, sub_self, abs_zero] <;> positivity

end Graphs

end Freezing2.RealTree

namespace Freezing2.CriticalGenealogy

open RealTree ReverseHistory ReverseCoalescence MeasuredGHSpace GromovHausdorff

variable {k : ℕ}

/-- Genealogy points: coalescence coordinates are symmetric, ultrametric and equal to
the births on the diagonal. -/
def genealogySupport (k : ℕ) : Set (GenealogySpace k) :=
  {z | (∀ i, z.2 i i = z.1 i) ∧ (∀ i j, z.2 i j = z.2 j i) ∧
    ∀ i j l, min (z.2 i l) (z.2 l j) ≤ z.2 i j}

theorem isClosed_genealogySupport (k : ℕ) : IsClosed (genealogySupport k) := by
  have hc : ∀ i j, Continuous fun z : GenealogySpace k ↦ z.2 i j := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)
  have hb : ∀ i, Continuous fun z : GenealogySpace k ↦ z.1 i := fun i ↦
    (continuous_apply i).comp continuous_fst
  have e : genealogySupport k = (⋂ i, {z : GenealogySpace k | z.2 i i = z.1 i}) ∩
      ((⋂ i, ⋂ j, {z : GenealogySpace k | z.2 i j = z.2 j i}) ∩
        ⋂ i, ⋂ j, ⋂ l, {z : GenealogySpace k | min (z.2 i l) (z.2 l j) ≤ z.2 i j}) := by
    ext z
    simp [genealogySupport]
  rw [e]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun i ↦ isClosed_eq (hc i i) (hb i)
  · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_eq (hc i j) (hc j i)
  · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun l ↦
      isClosed_le ((hc i l).min (hc l j)) (hc i j)

/-- The actual discrete genealogies lie in the support almost surely. -/
theorem ae_genealogyVector_mem_support (x : ℕ → ℤ) (hx : IsSigned x) {n : ℕ}
    (hs : SurvivesThrough x n) (k : ℕ) :
    ∀ᵐ q ∂sampledReverseVectorLaw x n k, genealogyVector n q ∈ genealogySupport k := by
  classical
  let := uniformVertex_isProbabilityMeasure x hx (hs n le_rfl).le
  have hmeas : MeasurableSet (genealogyVector (k := k) n ⁻¹' genealogySupport k) :=
    measurable_genealogyVector n (isClosed_genealogySupport k).measurableSet
  have hext : (n : ℕ∞) ≤ Freezing1.extinctionTime (companionSchedule x) :=
    (companion_before_extinction x hx hs).le
  -- almost every history works simultaneously for every legal label vector
  have hω : ∀ᵐ ω ∂jointLaw (companionSchedule x) n, ∀ V : Fin k → VertexLabel,
      (∀ i, V i ∈ vertexLabels x n) → (ω, V) ∈ genealogyVector n ⁻¹' genealogySupport k := by
    rw [ae_all_iff]
    intro V
    by_cases hV : ∀ i, V i ∈ vertexLabels x n
    · have hpair : ∀ᵐ ω ∂jointLaw (companionSchedule x) n, ∀ p : Fin k × Fin k,
          ∀ c ≤ commonBirth n (toCompanionLabel (V p.1)) (toCompanionLabel (V p.2)),
            connectedAt n (toCompanionLabel (V p.1)) (toCompanionLabel (V p.2)) c ω ↔
              c ≤ coalescenceTime n (toCompanionLabel (V p.1)) (toCompanionLabel (V p.2)) ω :=
        ae_all_iff.mpr fun p ↦ jointLaw_connected_iff_le_coalescenceTime hext
          (toCompanionLabel_mem x hx (hV p.1)) (toCompanionLabel_mem x hx (hV p.2))
      filter_upwards [hpair] with ω hω _
      refine ⟨fun i ↦ ?_, fun i j ↦ ?_, fun i j l ↦ ?_⟩
      · simp [genealogyVector]
      · simp only [genealogyVector, sourceCoalescenceTime]
        rw [coalescenceTime_comm]
      · simp only [genealogyVector, sourceCoalescenceTime]
        set u := fun i ↦ toCompanionLabel (V i)
        set c := min (coalescenceTime n (u i) (u l) ω) (coalescenceTime n (u l) (u j) ω)
        have hcil : c ≤ coalescenceTime n (u i) (u l) ω := min_le_left _ _
        have hclj : c ≤ coalescenceTime n (u l) (u j) ω := min_le_right _ _
        have hbil := coalescenceTime_le_commonBirth n (u i) (u l) ω
        have hblj := coalescenceTime_le_commonBirth n (u l) (u j) ω
        have h1 := (hω (i, l) c (hcil.trans hbil)).mpr hcil
        have h2 := (hω (l, j) c (hclj.trans hblj)).mpr hclj
        have hcij : c ≤ commonBirth n (u i) (u j) := by
          unfold commonBirth at hbil hblj ⊢
          exact le_min (hcil.trans (hbil.trans (min_le_left _ _)))
            (hclj.trans (hblj.trans (min_le_right _ _)))
        have h3 : connectedAt n (u i) (u j) c ω := h1.trans h2
        have hle := (hω (i, j) c hcij).mp h3
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rw [min_div_div_right hn]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hn
    · exact Eventually.of_forall fun ω h ↦ absurd h hV
  rw [sampledReverseVectorLaw]
  show ∀ᵐ q ∂_, q ∈ genealogyVector n ⁻¹' genealogySupport k
  rw [Measure.ae_prod_mem_iff_ae_ae_mem hmeas]
  have hlegalV : ∀ᵐ V ∂Measure.pi (fun _ : Fin k ↦ uniformVertex x n),
      ∀ i, V i ∈ vertexLabels x n :=
    ae_all_iff.mpr fun i ↦
      (measurePreserving_eval (fun _ : Fin k ↦ uniformVertex x n) i).quasiMeasurePreserving.ae
        (uniformVertex_mem x hx (hs n le_rfl).le)
  filter_upwards [hω] with ω hω'
  filter_upwards [hlegalV] with V hV
  exact hω' V hV

/-- Matrices satisfying the four-point condition on all index quadruples. -/
def fourPointMatrices (k : ℕ) : Set (Fin k → Fin k → ℝ) :=
  {M | ∀ i j l w, M i j + M l w ≤ max (M i l + M j w) (M i w + M j l)}

theorem isClosed_fourPointMatrices (k : ℕ) : IsClosed (fourPointMatrices k) := by
  have hc : ∀ i j, Continuous fun M : Fin k → Fin k → ℝ ↦ M i j := fun i j ↦
    (continuous_apply j).comp (continuous_apply i)
  have e : fourPointMatrices k = ⋂ i, ⋂ j, ⋂ l, ⋂ w,
      {M : Fin k → Fin k → ℝ | M i j + M l w ≤ max (M i l + M j w) (M i w + M j l)} := by
    ext M
    simp [fourPointMatrices]
  rw [e]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun l ↦
    isClosed_iInter fun w ↦ isClosed_le ((hc i j).add (hc l w))
      (((hc i l).add (hc j w)).max ((hc i w).add (hc j l)))

theorem monotone_profilePrimitive {g : ℝ → ℝ} (hg : Integrable g profileMeasure)
    (hnn : ∀ᵐ t ∂profileMeasure, 0 ≤ g t) : Monotone (profilePrimitive g) := by
  set F := (Icc (0 : ℝ) 1).indicator g
  have hF : Integrable F volume := (integrable_indicator_iff measurableSet_Icc).mpr hg
  have hFnn : 0 ≤ᵐ[volume] F := by
    have h := (ae_restrict_iff' measurableSet_Icc).mp hnn
    filter_upwards [h] with t ht
    by_cases hts : t ∈ Icc (0 : ℝ) 1
    · simp only [F, indicator_of_mem hts, Pi.zero_apply]
      exact ht hts
    · simp [F, indicator_of_notMem hts]
  intro a b hab
  unfold profilePrimitive
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume)
    (hF.intervalIntegrable (a := 0) (b := b)) (hF.intervalIntegrable (a := 0) (b := a))
  have hpos := intervalIntegral.integral_nonneg_of_ae hab hFnn
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  linarith

theorem distanceOfGenealogy_mem_fourPoint {g : ℝ → ℝ} (hP : Monotone (profilePrimitive g))
    {z : GenealogySpace k} (hz : z ∈ genealogySupport k) :
    distanceOfGenealogy g z ∈ fourPointMatrices k := by
  obtain ⟨hdiag, hsymm, hultra⟩ := hz
  set h : Fin k → ℝ := fun i ↦ profilePrimitive g (z.1 i)
  set m : Fin k → Fin k → ℝ := fun i j ↦ profilePrimitive g (z.2 i j)
  have hform : ∀ i j, distanceOfGenealogy g z i j = h i + h j - 2 * m i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [distanceOfGenealogy, h, m, hdiag]
      ring
    · simp [distanceOfGenealogy, hij, h, m]
  have hs : ∀ a b, m a b = m b a := fun a b ↦ by simp only [m, hsymm a b]
  have hu : ∀ a b c, min (m a c) (m c b) ≤ m a b := fun a b c ↦ by
    simp only [m, ← hP.map_min]
    exact hP (hultra a b c)
  intro i j l w
  simp only [hform]
  exact fourPoint_of_ultra h hs hu i j l w

section Limit

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}

theorem criticalGenealogyLimit_support (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) (genealogySupport k) = 1 := by
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) (isClosed_genealogySupport k)
  have hone : ∀ n, (genealogyLaw hx k n : Measure (GenealogySpace k)) (genealogySupport k) = 1 := by
    intro n
    simp only [genealogyLaw, ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_genealogyVector n)
      (isClosed_genealogySupport k).measurableSet]
    let := sampledReverseVectorLaw_probability (xa n) (hx n).1 (k := k) (hx n).2
    have hae := ae_genealogyVector_mem_support (xa n) (hx n).1 (hx n).2 k
    rw [ae_iff] at hae
    exact (prob_compl_eq_zero_iff ((measurable_genealogyVector n)
      (isClosed_genealogySupport k).measurableSet)).mp hae
  have hconst : (fun n ↦ (genealogyLaw hx k n : Measure (GenealogySpace k)) (genealogySupport k)) =
      fun _ ↦ 1 := funext hone
  rw [hconst, limsup_const] at hlim
  exact le_antisymm prob_le_one hlim

theorem criticalDistanceLaw_fourPoint (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    (criticalDistanceLaw g k : Measure (Fin k → Fin k → ℝ)) (fourPointMatrices k) = 1 := by
  have hP : Monotone (profilePrimitive g) :=
    monotone_profilePrimitive hL1.1 (hpos.mono fun _ h ↦ h.le)
  have hcont := continuous_distanceOfGenealogy (k := k) hL1.1
  simp only [criticalDistanceLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply hcont.measurable (isClosed_fourPointMatrices k).measurableSet]
  apply le_antisymm prob_le_one
  rw [← criticalGenealogyLimit_support hx hL1 hpos h2 k]
  exact measure_mono fun z hz ↦ distanceOfGenealogy_mem_fourPoint hP hz

end Limit

/-- If the annealed `4`-point matrices of a law of fully supported spaces satisfy the
four-point condition almost surely, almost every space is `0`-hyperbolic. -/
theorem ae_fourPoint_of_annealed {Q : ProbabilityMeasure MeasuredGHSpace.{0}}
    (h4 : (MeasuredGHSpace.annealedDistanceLaw Q 4 : Measure (Fin 4 → Fin 4 → ℝ))
      (fourPointMatrices 4) = 1)
    (hS : ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), MeasuredGHSpace.HasFullSupport X) :
    ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), FourPoint (underlyingGH X).Rep := by
  have hmeasc : MeasurableSet (fourPointMatrices 4)ᶜ :=
    (isClosed_fourPointMatrices 4).measurableSet.compl
  have hcompl : (MeasuredGHSpace.annealedDistanceLaw Q 4 : Measure (Fin 4 → Fin 4 → ℝ))
      (fourPointMatrices 4)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (isClosed_fourPointMatrices 4).measurableSet).mpr h4
  rw [MeasuredGHSpace.annealedDistanceLaw,
    continuousMixture_apply Q (MeasuredGHSpace.continuous_sampledDistanceLaw 4) hmeasc] at hcompl
  have hm : Measurable fun X ↦ (MeasuredGHSpace.sampledDistanceLaw 4 X :
      Measure (Fin 4 → Fin 4 → ℝ)) (fourPointMatrices 4)ᶜ :=
    (Measure.measurable_coe hmeasc).comp
      (measurable_toMeasure_of_continuous (MeasuredGHSpace.continuous_sampledDistanceLaw 4))
  have hae := (lintegral_eq_zero_iff hm).mp hcompl
  filter_upwards [hae, hS] with X hX hfs
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep X
  change (MeasuredGHSpace.sampledDistanceLaw 4 (toMeasuredGHSpace Y) :
    Measure (Fin 4 → Fin 4 → ℝ)) (fourPointMatrices 4)ᶜ = 0 at hX
  change MeasuredGHSpace.HasFullSupport (toMeasuredGHSpace Y) at hfs
  change FourPoint (underlyingGH (toMeasuredGHSpace Y)).Rep
  rw [MeasuredGHSpace.sampledDistanceLaw_toMeasuredGHSpace] at hX
  rw [MeasuredGHSpace.hasFullSupport_toMeasuredGHSpace] at hfs
  rw [underlyingGH_toMeasuredGHSpace, fourPoint_toGHSpace_rep_iff]
  have hopen : IsOpen (distanceMatrix 4 ⁻¹' (fourPointMatrices 4)ᶜ : Set (Fin 4 → Y)) :=
    (isClosed_fourPointMatrices 4).isOpen_compl.preimage (continuous_distanceMatrix 4)
  have hnull : Measure.pi (fun _ : Fin 4 ↦ (Y.law : Measure Y))
      (distanceMatrix 4 ⁻¹' (fourPointMatrices 4)ᶜ) = 0 := by
    simp only [iidDistanceLaw, iidDistanceLawOn, ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.toMeasure_pi] at hX
    rwa [Measure.map_apply (continuous_distanceMatrix 4).measurable hmeasc] at hX
  have hempty := (hopen.measure_eq_zero_iff _).mp hnull
  intro a b c d
  have hmem : distanceMatrix 4 ![a, b, c, d] ∈ fourPointMatrices 4 := by
    by_contra h
    have : ![a, b, c, d] ∈ (distanceMatrix 4 ⁻¹' (fourPointMatrices 4)ᶜ : Set (Fin 4 → Y)) := h
    rw [hempty] at this
    exact this
  simpa [distanceMatrix] using hmem 0 1 2 3

/-- Midpoints pass to weak limits of laws with approximate midpoints at every scale. -/
theorem ae_hasMidpoints_of_tendsto {P : ℕ → ProbabilityMeasure MeasuredGHSpace.{0}}
    {Q : ProbabilityMeasure MeasuredGHSpace.{0}} (hlim : Tendsto P atTop (𝓝 Q))
    (hP : ∀ ε > 0, ∀ᶠ n in atTop, ∀ᵐ X ∂(P n : Measure MeasuredGHSpace.{0}),
      ApproxMidpoints ε (underlyingGH X).Rep) :
    ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), HasMidpoints (underlyingGH X).Rep := by
  set S : ℝ → Set MeasuredGHSpace.{0} := fun ε ↦
    underlyingGH ⁻¹' {p : GHSpace | ApproxMidpoints ε p.Rep}
  have hS : ∀ ε, IsClosed (S ε) := fun ε ↦
    (isClosed_setOf_approxMidpoints ε).preimage continuous_underlyingGH
  have hQ : ∀ ε > 0, (Q : Measure MeasuredGHSpace.{0}) (S ε) = 1 := by
    intro ε hε
    have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim (hS ε)
    have hone : ∀ᶠ n in atTop, (P n : Measure MeasuredGHSpace.{0}) (S ε) = 1 := by
      filter_upwards [hP ε hε] with n hn
      rw [ae_iff] at hn
      exact (prob_compl_eq_zero_iff (hS ε).measurableSet).mp hn
    rw [limsup_congr hone, limsup_const] at hlimsup
    exact le_antisymm prob_le_one hlimsup
  have hae : ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}), ∀ m : ℕ,
      ApproxMidpoints (1 / ((m : ℝ) + 1)) (underlyingGH X).Rep := by
    rw [ae_all_iff]
    intro m
    have h := hQ (1 / ((m : ℝ) + 1)) (by positivity)
    rw [← prob_compl_eq_zero_iff (hS _).measurableSet] at h
    exact measure_eq_zero_iff_ae_notMem.mp h |>.mono fun X hX ↦ not_not.mp hX
  filter_upwards [hae] with X hX
  apply hasMidpoints_of_approx
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  exact (hX m).mono hm.le

/-- The actual scaled forward trees have `ε`-approximate midpoints for large `n`. -/
theorem forward_ae_approxMidpoints (x : ℕ → ℕ → ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ᵐ X ∂(forwardMeasuredTreeLaw x (1 / 2) n : Measure MeasuredGHSpace.{0}),
      ApproxMidpoints ε (underlyingGH X).Rep := by
  set c : ℕ → ℝ := fun n ↦ 1 / (n : ℝ) ^ (1 - (1 / 2 : ℝ))
  have hc : Tendsto c atTop (𝓝 0) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 - 1 / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.inv_tendsto_atTop.congr fun n ↦ ?_
    simp [c, Function.comp_def, one_div]
  have hS : MeasurableSet {X : MeasuredGHSpace.{0} | ApproxMidpoints ε (underlyingGH X).Rep} :=
    ((isClosed_setOf_approxMidpoints ε).preimage continuous_underlyingGH).measurableSet
  filter_upwards [hc.eventually (gt_mem_nhds (show (0 : ℝ) < 2 * ε by positivity)),
    eventually_gt_atTop 0] with n hn hn0
  have hcpos : 0 < c n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  show ∀ᵐ X ∂((freezingTreeLaw x n).map
    (fun s ↦ toMeasuredGHSpace (forwardMeasuredSpace (c n) s))), _
  rw [ae_map_iff (measurable_from_top).aemeasurable hS]
  refine Eventually.of_forall fun s ↦ ?_
  show ApproxMidpoints ε (underlyingGH (toMeasuredGHSpace (forwardMeasuredSpace (c n) s))).Rep
  rw [underlyingGH_toMeasuredGHSpace, approxMidpoints_toGHSpace_rep_iff]
  exact (forwardMeasuredSpace_approxMidpoints hcpos s).mono (by linarith)

/-- **The critical limit is a real tree (U26).** -/
theorem criticalTreeLaw_ae_isRealTree {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      IsRealTree (underlyingGH X).Rep := by
  obtain ⟨hconv, hann, hfull⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  have h4 : (annealedDistanceLaw (criticalTreeLaw (fun t ↦ 1 / f t)) 4 :
      Measure (Fin 4 → Fin 4 → ℝ)) (fourPointMatrices 4) = 1 := by
    rw [hann 4]
    exact criticalDistanceLaw_fourPoint (admissible_initialRowExtension hx)
      (hasL1ReciprocalProfile_initialRowExtension hL1) (positiveProfile_reciprocal hf)
      (hasLocalSquareMomentProfile_initialRowExtension h2) 4
  have hfp := ae_fourPoint_of_annealed h4 hfull
  have hmid := ae_hasMidpoints_of_tendsto hconv fun ε hε ↦ forward_ae_approxMidpoints x hε
  filter_upwards [hfp, hmid] with X h1 h2
  exact isRealTree_of_fourPoint h1 h2

end Freezing2.CriticalGenealogy

namespace Freezing2

open CriticalGenealogy RealTree MeasuredGHSpace

/-- **Theorem `thm:critique` (M03).** Under `Lim^{1/2}_{1/f}`, `Lim^{1/2}_{1/f²}` and
`max_{k ≤ n} S^n_k = O(√n)`, the actual forward trees with graph distances scaled by
`1/√n` and the uniform measure on vertices converge in distribution, for the
Gromov–Hausdorff–Prokhorov topology, to the law `criticalTreeLaw (1/f)` of a random
measured compact real tree `𝒯(f)`, which depends only on `f`. The limit has almost
surely full support and annealed sampled distance matrices `criticalDistanceLaw (1/f) k`. -/
theorem critical_scaling_limit_realTree {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    Tendsto (forwardMeasuredTreeLaw x (1 / 2)) atTop
        (𝓝 (criticalTreeLaw (fun t ↦ 1 / f t))) ∧
      (∀ k, annealedDistanceLaw (criticalTreeLaw (fun t ↦ 1 / f t)) k =
        criticalDistanceLaw (fun t ↦ 1 / f t) k) ∧
      (∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
        HasFullSupport X) ∧
      ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
        IsRealTree (underlyingGH X).Rep := by
  obtain ⟨h1, h2', h3⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  exact ⟨h1, h2', h3, criticalTreeLaw_ae_isRealTree hx hf hL1 h2 hpop⟩

end Freezing2
