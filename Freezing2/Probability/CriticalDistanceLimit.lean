module

public import Freezing2.Probability.CriticalGenealogyLaw
public import Freezing2.Probability.WeakPerturbation

/-!
# Sampled distances in the critical regime (`eq:GP` for the reverse tree)

The scaled graph distance between two vertices of the actual reverse tree is
uniformly close to `P(b) + P(b') - 2 P(c)`, where `b, b'` are the scaled birth times,
`c` is the scaled coalescence time and `P` is half the primitive of the limiting
reciprocal profile: this combines the distance approximation N07 with the uniform
harmonic-prefix approximation. Hence the sampled distance matrices of `k` iid uniform
vertices converge in distribution to the image of the limiting genealogy law under
this continuous map; the limit depends only on the profile.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Freezing2.CriticalGenealogy

open ReverseHistory ReverseCoalescence

variable {k : ℕ}

/-- The distance matrix determined by births and coalescence times. -/
noncomputable def distanceOfGenealogy (g : ℝ → ℝ) (z : GenealogySpace k) : Fin k → Fin k → ℝ :=
  fun i j ↦ if i = j then 0 else
    profilePrimitive g (z.1 i) + profilePrimitive g (z.1 j) - 2 * profilePrimitive g (z.2 i j)

theorem continuous_distanceOfGenealogy {g : ℝ → ℝ} (hg : Integrable g profileMeasure) :
    Continuous (distanceOfGenealogy (k := k) g) := by
  have hP := continuous_profilePrimitive hg
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  by_cases hij : i = j
  · simp only [distanceOfGenealogy, hij, ↓reduceIte]
    exact continuous_const
  · simp only [distanceOfGenealogy, hij, ↓reduceIte]
    exact ((hP.comp ((continuous_apply i).comp continuous_fst)).add
      (hP.comp ((continuous_apply j).comp continuous_fst))).sub
      (continuous_const.mul (hP.comp ((continuous_apply j).comp ((continuous_apply i).comp
        continuous_snd))))

theorem reverseDistanceErrorMax_nonneg (x : ℕ → ℕ → ℤ) (n : ℕ) (ω : History) :
    0 ≤ reverseDistanceErrorMax x n ω := by
  unfold reverseDistanceErrorMax finiteHeightDeviationMax
  rw [Finset.le_sup'_iff]
  exact ⟨none, Finset.mem_univ _, le_rfl⟩

/-- **Entrywise critical distance approximation.** -/
theorem scaled_reverseDistance_genealogy_error_le
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hg : Integrable g profileMeasure) {n : ℕ}
    (hn : 0 < n) {u v : VertexLabel} (hu : u ∈ vertexLabels (x n) n)
    (hv : v ∈ vertexLabels (x n) n) (ω : History) :
    |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
      (profilePrimitive g ((Freezing2.birthTime n u : ℝ) / n) +
        profilePrimitive g ((Freezing2.birthTime n v : ℝ) / n) -
        2 * profilePrimitive g ((sourceCoalescenceTime n u v ω : ℝ) / n))| ≤
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω + (n : ℝ) ^ (α - 1) +
        4 * branchPrimitiveError x α g n := by
  set c := sourceCoalescenceTime n u v ω
  have hc : c ≤ n := (sourceCoalescenceTime_le_birth_left n u v ω).trans (birthTime_le (x n) hu)
  have hs : 0 ≤ (n : ℝ) ^ (α - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he : (n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω =
      normalizedHarmonicPrefix x α n (Freezing2.birthTime n u) +
        normalizedHarmonicPrefix x α n (Freezing2.birthTime n v) +
        (n : ℝ) ^ (α - 1) * (activeCount (x n) c : ℝ)⁻¹ -
        2 * normalizedHarmonicPrefix x α n c := by
    have h := harmonic_coalescence_branch_difference (x n)
      (sourceCoalescenceTime_le_birth_left n u v ω)
      (sourceCoalescenceTime_le_birth_right n u v ω)
    unfold coalescenceHarmonicDistance normalizedHarmonicPrefix
    dsimp [c] at h ⊢
    nlinarith [h]
  have hpu := normalizedHarmonicPrefix_error_le (α := α) hx hg hn (birthTime_le (x n) hu)
  have hpv := normalizedHarmonicPrefix_error_le (α := α) hx hg hn (birthTime_le (x n) hv)
  have hpc := normalizedHarmonicPrefix_error_le (α := α) hx hg hn hc
  have hi := reciprocal_activeCount_abs_le_one (hx n).2 hc
  have hmul : |(n : ℝ) ^ (α - 1) * (activeCount (x n) c : ℝ)⁻¹| ≤ (n : ℝ) ^ (α - 1) := by
    rw [abs_mul, abs_of_nonneg hs]
    simpa using mul_le_mul_of_nonneg_left hi hs
  have hm := mul_le_mul_of_nonneg_left (distance_error_le_reverseDistanceErrorMax x n hu hv ω) hs
  have hm' : |(n : ℝ) ^ (α - 1) * reverseDistance n u v ω -
      (n : ℝ) ^ (α - 1) * coalescenceHarmonicDistance (x n) n u v ω| ≤
      (n : ℝ) ^ (α - 1) * reverseDistanceErrorMax x n ω := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hs]
    exact hm
  rw [abs_le] at hpu hpv hpc hmul hm' ⊢
  constructor <;> nlinarith [hpu.1, hpu.2, hpv.1, hpv.2, hpc.1, hpc.2, hmul.1, hmul.2,
    hm'.1, hm'.2, he]

/-- The sample probability measure of one reverse history with `k` iid uniform labels. -/
noncomputable def samplePM {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa) (k n : ℕ) :
    ProbabilityMeasure (History × (Fin k → VertexLabel)) :=
  ⟨sampledReverseVectorLaw (xa n) n k, sampledReverseVectorLaw_probability (xa n) (hx n).1 (hx n).2⟩

theorem samplePM_map_genealogyVector {xa : ℕ → ℕ → ℤ} (hx : AdmissibleArray xa) (n : ℕ) :
    (samplePM hx k n).map (genealogyVector n) = genealogyLaw hx k n :=
  rfl

/-- **Sampled distance error in probability.** -/
theorem tendsto_genealogy_distance_error {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (samplePM hx k n : Measure (History × (Fin k → VertexLabel))).real
      {q | ε < dist (sampledDistanceMatrix (1 / 2) n k q)
        (distanceOfGenealogy g (genealogyVector n q))}) atTop (𝓝 0) := by
  have hN07 := tendsto_reverseDistanceErrorMax hx (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hL1 hpos (half_pos hε)
  have hsmall : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 / 2 : ℝ) - 1) +
      4 * branchPrimitiveError xa (1 / 2) g n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 / 2 : ℝ) - 1)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop |>.congr fun n ↦ by norm_num
    simpa using h1.add ((tendsto_branchPrimitiveError (by norm_num) hL1).const_mul 4)
  have hN07' : Tendsto (fun n ↦ (samplePM hx k n : Measure (History × (Fin k → VertexLabel))).real
      {q | ε / 2 * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) < reverseDistanceErrorMax xa n q.1}) atTop (𝓝 0) := by
    apply hN07.congr
    intro n
    exact (sampledReverseVectorLaw_history_event (xa n) (hx n).1 (hx n).2
      {ω | ε / 2 * (n : ℝ) ^ (1 - (1 / 2 : ℝ)) < reverseDistanceErrorMax xa n ω}).symm
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hN07'
  filter_upwards [hsmall.eventually (gt_mem_nhds (half_pos hε)), eventually_gt_atTop 0] with n h1 hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [sampledReverseVectorLaw_ae_legal (xa n) (hx n).1 (k := k) (hx n).2] with q hq hdist
  change ε < dist (sampledDistanceMatrix (1 / 2) n k q)
    (distanceOfGenealogy g (genealogyVector n q)) at hdist
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set E := reverseDistanceErrorMax xa n q.1
  set s := (n : ℝ) ^ ((1 / 2 : ℝ) - 1)
  have hs : 0 < s := Real.rpow_pos_of_pos hnpos _
  have hE : 0 ≤ E := reverseDistanceErrorMax_nonneg xa n q.1
  set B := s * E + s + 4 * branchPrimitiveError xa (1 / 2) g n
  have hB : 0 ≤ B := by
    have := branchPrimitiveError_nonneg xa (1 / 2) g n
    positivity
  have hle : dist (sampledDistanceMatrix (1 / 2) n k q)
      (distanceOfGenealogy g (genealogyVector n q)) ≤ B := by
    rw [dist_pi_le_iff hB]
    intro i
    rw [dist_pi_le_iff hB]
    intro j
    rw [Real.dist_eq]
    by_cases hij : i = j
    · subst hij
      simp [distanceOfGenealogy, hB]
    · simp only [sampledDistanceMatrix, distanceOfGenealogy, hij, ↓reduceIte, genealogyVector]
      exact scaled_reverseDistance_genealogy_error_le hx hL1.1 hn (hq i) (hq j) q.1
  have hlt : ε / 2 < s * E := by linarith
  have hsinv : s = ((n : ℝ) ^ (1 - (1 / 2 : ℝ)))⁻¹ := by
    simp only [s]
    rw [← Real.rpow_neg hnpos.le]
    norm_num
  rw [hsinv, inv_mul_eq_div, lt_div_iff₀ (Real.rpow_pos_of_pos hnpos _)] at hlt
  exact hlt

/-- The limiting law of the scaled births and coalescence times of `k` uniform
vertices, characterized by the profile `g`. -/
noncomputable def criticalGenealogyLimit (g : ℝ → ℝ) (k : ℕ) :
    ProbabilityMeasure (GenealogySpace k) :=
  haveI : Nonempty (ProbabilityMeasure (GenealogySpace k)) := ⟨⟨Measure.dirac 0, inferInstance⟩⟩
  Classical.epsilon (IsGenealogyLimit g)

/-- The limiting law of the scaled sampled distance matrix of `k` uniform vertices. -/
noncomputable def criticalDistanceLaw (g : ℝ → ℝ) (k : ℕ) :
    ProbabilityMeasure (Fin k → Fin k → ℝ) :=
  (criticalGenealogyLimit g k).map (distanceOfGenealogy g)

theorem tendsto_genealogyLaw_criticalGenealogyLimit {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    Tendsto (genealogyLaw hx k) atTop (𝓝 (criticalGenealogyLimit g k)) := by
  classical
  obtain ⟨μ, hμ, hlim⟩ := exists_tendsto_genealogyLaw hx hL1 hpos h2 k
  have hex : ∃ μ, IsGenealogyLimit g μ := ⟨μ, hlim⟩
  have heq : criticalGenealogyLimit g k = μ := (Classical.epsilon_spec hex).unique hlim
  rw [heq]
  exact hμ

/-- **`eq:GP` for the reverse tree.** The scaled sampled distance matrices of `k`
iid uniform vertices converge in distribution to `criticalDistanceLaw g k`. -/
theorem tendsto_sampledDistanceLaw_critical {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ}
    (hx : AdmissibleArray xa) (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (k : ℕ) :
    Tendsto (fun n ↦ (samplePM hx k n).map (sampledDistanceMatrix (1 / 2) n k)) atTop
      (𝓝 (criticalDistanceLaw g k)) := by
  have hcont := continuous_distanceOfGenealogy (k := k) hL1.1
  have hlim : Tendsto (fun n ↦ (samplePM hx k n).map
      (distanceOfGenealogy g ∘ genealogyVector n)) atTop (𝓝 (criticalDistanceLaw g k)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (tendsto_genealogyLaw_criticalGenealogyLimit hx hL1 hpos h2 k) hcont
    apply h.congr
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, ← samplePM_map_genealogyVector hx n]
    rw [Measure.map_map hcont.measurable (measurable_genealogyVector n)]
  exact tendsto_probabilityMap_of_error_probability (samplePM hx k)
    (fun n ↦ measurable_sampledDistanceMatrix (1 / 2) n k)
    (fun n ↦ hcont.measurable.comp (measurable_genealogyVector n))
    (fun ε hε ↦ tendsto_genealogy_distance_error hx hL1 hpos k hε) hlim

end Freezing2.CriticalGenealogy
