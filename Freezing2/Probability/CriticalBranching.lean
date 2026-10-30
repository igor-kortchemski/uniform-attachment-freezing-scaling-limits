module

public import Freezing2.Geometry.RealTreeStar
public import Freezing2.Probability.CriticalLeaves
public import Freezing2.Probability.CriticalRootMerges
public import Freezing2.Probability.CriticalTripleMerger

/-!
# Branching of the critical limit (Theorem `thm:properties` (2), M04b–c)

Degrees of points of the limit `𝒯(f)` are read off from stars among iid samples.
A point of degree at least `m` puts `m` samples in distinct components of its
complement with positive probability, so their distances form a star; conversely a
star among samples of a real tree produces a point of degree at least `m`.

In the limiting genealogy, a star of four samples forces, by the ultrametric structure
of coalescence times, three samples with a common coalescence time. Triple mergers at
positive times have probability zero, so this common time is zero; the arms of the star
are then the heights of the samples. Consequently:

* if `∫₀^{1/2} f⁻² = ∞`, coalescence at time zero has probability zero, so there are no
  four-stars and the tree is binary (all degrees at most three);
* in general, two distinct points of degree at least four would produce two stars
  whose arms contradict each other, so there is at most one such point;
* if `∫₀^{1/2} f⁻² < ∞`, many samples born early pairwise coalesce at time zero, so
  the tree has points of arbitrarily large degree; by uniqueness, a single point has
  infinite degree.

The limit is an unpointed measured space, so the point of infinite degree represents
the source's root only up to the Gromov–Hausdorff–Prokhorov encoding. The source's
"degree two" for branch points counts children; in the metric degree used here (the
number of components of the complement) a binary branch point has degree three.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Freezing2

open RealTree MeasuredGHSpace

namespace RealTree

/-- Distance matrices of `k` points among which some `m` form a star. -/
def StarAmong (m k : ℕ) : Set (Fin k → Fin k → ℝ) :=
  {D | ∃ e : Fin m → Fin k, Function.Injective e ∧ (fun p q ↦ D (e p) (e q)) ∈ StarSet m}

theorem measurableSet_starAmong (m k : ℕ) : MeasurableSet (StarAmong m k) := by
  have he : StarAmong m k = ⋃ e : {e : Fin m → Fin k // Function.Injective e},
      (fun (D : Fin k → Fin k → ℝ) (p q : Fin m) ↦ D (e.1 p) (e.1 q)) ⁻¹' StarSet m := by
    ext D
    simp only [StarAmong, mem_ofPred_eq, mem_iUnion, mem_preimage, Subtype.exists, exists_prop]
  rw [he]
  refine MeasurableSet.iUnion fun e ↦ ?_
  have hc : Continuous (fun (D : Fin k → Fin k → ℝ) (p q : Fin m) ↦ D (e.1 p) (e.1 q)) := by
    fun_prop
  exact hc.measurable (measurableSet_starSet m)

/-- A real tree is binary when every point has degree at most three: branch points
have exactly two children besides the direction towards the rest of the tree. -/
def IsBinaryTree (X : Type*) [MetricSpace X] : Prop := ∀ x : X, degree x ≤ 3

theorem le_three_of_lt_four {d : ℕ∞} (h : d < 4) : d ≤ 3 := by
  induction d using ENat.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    have : n < 4 := by exact_mod_cast h
    exact_mod_cast (show n ≤ 3 by omega)

theorem eq_top_of_forall_natCast_le {d : ℕ∞} (h : ∀ m : ℕ, (m : ℕ∞) ≤ d) : d = ⊤ := by
  induction d using ENat.recTopCoe with
  | top => rfl
  | coe n =>
    have := h (n + 1)
    norm_cast at this
    omega

end RealTree

namespace CriticalGenealogy

open ReverseHistory ReverseCoalescence

variable {k : ℕ}

/-- Of three values below `M` whose pairwise maxima reach `M`, two equal `M`. -/
theorem two_eq_of_le_max {M a b c : ℝ} (ha : a ≤ M) (hb : b ≤ M) (hc : c ≤ M)
    (h1 : M ≤ max a b) (h2 : M ≤ max a c) (h3 : M ≤ max b c) :
    (a = M ∧ b = M) ∨ (a = M ∧ c = M) ∨ (b = M ∧ c = M) := by
  have e1 : a = M ∨ b = M := by
    rcases le_max_iff.mp h1 with h | h
    · exact Or.inl (le_antisymm ha h)
    · exact Or.inr (le_antisymm hb h)
  have e2 : a = M ∨ c = M := by
    rcases le_max_iff.mp h2 with h | h
    · exact Or.inl (le_antisymm ha h)
    · exact Or.inr (le_antisymm hc h)
  have e3 : b = M ∨ c = M := by
    rcases le_max_iff.mp h3 with h | h
    · exact Or.inl (le_antisymm hb h)
    · exact Or.inr (le_antisymm hc h)
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3 <;> tauto

/-- Four values such that in every triple each value is at most the maximum of the
other two have three equal maximal values. -/
theorem exists_triple_max (r : Fin 4 → ℝ)
    (hu : ∀ p q s, p ≠ q → p ≠ s → q ≠ s → r s ≤ max (r p) (r q)) :
    ∃ p q s, p ≠ q ∧ p ≠ s ∧ q ≠ s ∧ r q = r p ∧ r s = r p ∧ ∀ t, r t ≤ r p := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hmax : ∀ t, r t ≤ r p := fun t ↦ hp t (Finset.mem_univ t)
  have hcard : (Finset.univ.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ t, t ∈ ({a, b, c} : Finset (Fin 4)) → t ≠ p := fun t ht ↦ by
    rw [← he] at ht
    exact (Finset.mem_erase.mp ht).1
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hc := hmem c (by simp)
  rcases two_eq_of_le_max (hmax a) (hmax b) (hmax c) (hu a b p hab ha hb) (hu a c p hac ha hc)
      (hu b c p hbc hb hc) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨p, a, b, ha.symm, hb.symm, hab, h1, h2, hmax⟩
  · exact ⟨p, a, c, ha.symm, hc.symm, hac, h1, h2, hmax⟩
  · exact ⟨p, b, c, hb.symm, hc.symm, hbc, h1, h2, hmax⟩

/-- Genealogies with the almost sure properties used for branching: the support
relations, values in the unit cube, positive births, and no triple merger at a
positive time. -/
def BranchGood (k : ℕ) : Set (GenealogySpace k) :=
  {z | z ∈ genealogySupport k ∧ z ∈ unitCube k ∧ (∀ i, 0 < z.1 i) ∧
    ∀ i j l, i ≠ j → i ≠ l → j ≠ l → ¬ (0 < z.2 i j ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j)}

theorem profilePrimitive_zero (g : ℝ → ℝ) : profilePrimitive g 0 = 0 := by
  simp [profilePrimitive]

theorem mem_unitCube_fst {z : GenealogySpace k} (hz : z ∈ unitCube k) (i : Fin k) :
    z.1 i ∈ Icc (0 : ℝ) 1 :=
  (mem_prod.mp hz).1 i (mem_univ _)

theorem mem_unitCube_snd {z : GenealogySpace k} (hz : z ∈ unitCube k) (i j : Fin k) :
    z.2 i j ∈ Icc (0 : ℝ) 1 :=
  (mem_prod.mp hz).2 i (mem_univ _) j (mem_univ _)

/-- **Stars in a good genealogy.** If four samples of a good genealogy have a star
distance matrix with arms `A`, the arms are the heights of the samples and the four
samples pairwise coalesce at time zero. -/
theorem star_of_branchGood {g : ℝ → ℝ} (hP : StrictMonoOn (profilePrimitive g) (Icc 0 1))
    {z : GenealogySpace k} (hz : z ∈ BranchGood k) {e : Fin 4 → Fin k}
    (he : Function.Injective e) {A : Fin 4 → ℝ}
    (hA : ∀ p q, p ≠ q → distanceOfGenealogy g z (e p) (e q) = A p + A q) :
    (∀ p, A p = profilePrimitive g (z.1 (e p))) ∧ ∀ p q, p ≠ q → z.2 (e p) (e q) = 0 := by
  obtain ⟨⟨-, hsym, hult⟩, hcube, -, htrip⟩ := hz
  set P := profilePrimitive g with hPdef
  have hc01 := mem_unitCube_snd hcube
  have hP0 : P 0 = 0 := profilePrimitive_zero g
  have hPmono : MonotoneOn P (Icc 0 1) := hP.monotoneOn
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  set r : Fin 4 → ℝ := fun p ↦ P (z.1 (e p)) - A p with hr
  set m : Fin 4 → Fin 4 → ℝ := fun p q ↦ P (z.2 (e p) (e q)) with hm
  have hrm : ∀ p q, p ≠ q → r p + r q = 2 * m p q := by
    intro p q hpq
    have h := hA p q hpq
    simp only [distanceOfGenealogy, he.ne hpq, ↓reduceIte] at h
    simp only [r, m]
    linarith
  have hmu : ∀ p q s, min (m p s) (m s q) ≤ m p q := by
    intro p q s
    have h := hult (e p) (e q) (e s)
    simp only [m]
    rcases le_total (z.2 (e p) (e s)) (z.2 (e s) (e q)) with hle | hle
    · rw [min_eq_left hle] at h
      exact (min_le_left _ _).trans (hPmono (hc01 _ _) (hc01 _ _) h)
    · rw [min_eq_right hle] at h
      exact (min_le_right _ _).trans (hPmono (hc01 _ _) (hc01 _ _) h)
  have hu : ∀ p q s, p ≠ q → p ≠ s → q ≠ s → r s ≤ max (r p) (r q) := by
    intro p q s hpq hps hqs
    have h1 := hrm p q hpq
    have h2 := hrm p s hps
    have h3 := hrm s q (Ne.symm hqs)
    rcases min_le_iff.mp (hmu p q s) with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  obtain ⟨p, q, s, hpq, hps, hqs, hq, hs, hmax⟩ := exists_triple_max r hu
  have mpq : m p q = r p := by have := hrm p q hpq; linarith
  have mps : m p s = r p := by have := hrm p s hps; linarith
  have mqs : m q s = r p := by have := hrm q s hqs; linarith
  have hinj : InjOn P (Icc 0 1) := hP.injOn
  have c1 : z.2 (e p) (e s) = z.2 (e p) (e q) :=
    hinj (hc01 _ _) (hc01 _ _) (by simp only [m] at mps mpq; rw [mps, mpq])
  have c2 : z.2 (e q) (e s) = z.2 (e p) (e q) :=
    hinj (hc01 _ _) (hc01 _ _) (by simp only [m] at mqs mpq; rw [mqs, mpq])
  have hnot := htrip (e p) (e q) (e s) (he.ne hpq) (he.ne hps) (he.ne hqs)
  have hc0 : z.2 (e p) (e q) = 0 := by
    by_contra hne
    exact hnot ⟨lt_of_le_of_ne (hc01 _ _).1 (Ne.symm hne), c1, c2⟩
  have hM : r p = 0 := by
    rw [← mpq]
    simp only [m, hc0, hP0]
  have hall : ∀ t, r t = 0 := by
    intro t
    apply le_antisymm ((hmax t).trans hM.le)
    by_cases htp : t = p
    · rw [htp, hM]
    · have h := hrm t p htp
      have hm0 : 0 ≤ m t p := by
        simp only [m]
        rw [← hP0]
        exact hPmono h0 (hc01 _ _) (hc01 _ _).1
      linarith
  refine ⟨fun t ↦ ?_, fun a b hab ↦ ?_⟩
  · have := hall t
    simp only [r] at this
    linarith
  · have h := hrm a b hab
    rw [hall a, hall b] at h
    have hPc : P (z.2 (e a) (e b)) = P 0 := by
      simp only [m] at h
      rw [hP0]
      linarith
    exact hinj (hc01 _ _) h0 hPc

/-- Bernoulli-type bound used for groups of samples all born late. -/
theorem one_sub_pow_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (L : ℕ) :
    (1 - a) ^ L ≤ 1 / (1 + L * a) := by
  have h1 : 0 ≤ 1 - a := by linarith
  have hb : 1 + L * a ≤ (1 + a) ^ L := one_add_mul_le_pow (by linarith) L
  have hprod : (1 - a) ^ L * (1 + a) ^ L ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 < 1 + L * a := by positivity
  rw [le_div_iff₀ hpos]
  calc (1 - a) ^ L * (1 + L * a) ≤ (1 - a) ^ L * (1 + a) ^ L :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg h1 L)
    _ ≤ 1 := hprod

section Limit

variable {xa : ℕ → ℕ → ℤ} {g : ℝ → ℝ} {k : ℕ}

theorem strictMonoOn_profilePrimitive (hL1 : HasL1ReciprocalProfile xa (1 / 2) g)
    (hpos : PositiveProfile g) : StrictMonoOn (profilePrimitive g) (Icc 0 1) :=
  fun _ ha _ hb hab ↦ profilePrimitive_lt hL1.1 hpos ha.1 hab hb.2

/-- Births of the limit are almost surely positive. -/
theorem criticalGenealogyLimit_birth_nonpos_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hk : 2 ≤ k) (i : Fin k) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) {z | z.1 i ≤ 0} = 0 := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hj⟩ := exists_ne i
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _
  have hθ : (0 : ℝ) < min (η : ℝ) (1 / 2) := lt_min (by exact_mod_cast hη) (by norm_num)
  have hsub : {z : GenealogySpace k | z.1 i ≤ 0} ⊆ {z | z.1 i < min (η : ℝ) (1 / 2)} :=
    fun z hz ↦ lt_of_le_of_lt hz hθ
  refine (measure_mono hsub).trans ((criticalGenealogyLimit_birth_lt_le hx hL1 hpos h2
    (Ne.symm hj) hθ.le (by linarith [min_le_right (η : ℝ) (1 / 2)])).trans ?_)
  rw [bot_eq_zero, zero_add]
  exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq ENNReal.ofReal_coe_nnreal

/-- Almost every limiting genealogy is good. -/
theorem criticalGenealogyLimit_branchGood (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) (hk : 2 ≤ k) :
    (criticalGenealogyLimit g k : Measure (GenealogySpace k)) (BranchGood k)ᶜ = 0 := by
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  have hsupp : μ (genealogySupport k)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (isClosed_genealogySupport k).measurableSet).mpr
      (criticalGenealogyLimit_support hx hL1 hpos h2 k)
  have hcube : μ (unitCube k)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (isCompact_unitCube k).isClosed.measurableSet).mpr
      (criticalGenealogyLimit_unitCube hx hL1 hpos h2 k)
  have htrip : ∀ i j l : Fin k, μ {z | i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      (0 < z.2 i j ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j)} = 0 := by
    intro i j l
    by_cases h : i ≠ j ∧ i ≠ l ∧ j ≠ l
    · exact measure_mono_null (fun z hz ↦ hz.2.2.2)
        (criticalGenealogyLimit_tripleMerger_null hx hL1 hpos h2 h.1 h.2.1 h.2.2)
    · have he : {z : GenealogySpace k | i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
          (0 < z.2 i j ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j)} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hz ↦ h ⟨hz.1, hz.2.1, hz.2.2.1⟩
      rw [he, measure_empty]
  apply measure_mono_null (t := (genealogySupport k)ᶜ ∪ (unitCube k)ᶜ ∪
    (⋃ i, {z : GenealogySpace k | z.1 i ≤ 0}) ∪ ⋃ i, ⋃ j, ⋃ l, {z | i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      (0 < z.2 i j ∧ z.2 i l = z.2 i j ∧ z.2 j l = z.2 i j)})
  · intro z hz
    by_contra hcon
    apply hz
    simp only [mem_union, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_or, not_exists,
      not_not, not_le] at hcon
    obtain ⟨⟨⟨hs, hc⟩, hb⟩, ht⟩ := hcon
    exact ⟨hs, hc, hb, fun i j l hij hil hjl h ↦ ht i j l ⟨hij, hil, hjl, h⟩⟩
  · exact measure_union_null (measure_union_null (measure_union_null hsupp hcube)
      (measure_iUnion_null fun i ↦ criticalGenealogyLimit_birth_nonpos_null hx hL1 hpos h2 hk i))
      (measure_iUnion_null fun i ↦ measure_iUnion_null fun j ↦ measure_iUnion_null fun l ↦
        htrip i j l)

/-- **No four-star when `∫₀ g² = ∞`.** -/
theorem criticalDistanceLaw_starSet_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (hinf : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) = ⊤) :
    (criticalDistanceLaw g 4 : Measure (Fin 4 → Fin 4 → ℝ)) (StarSet 4) = 0 := by
  have hP := strictMonoOn_profilePrimitive hL1 hpos
  simp only [criticalDistanceLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (continuous_distanceOfGenealogy hL1.1).measurable
    (measurableSet_starSet 4)]
  apply measure_mono_null (t := (BranchGood 4)ᶜ ∪ {z | z.2 0 1 ≤ 0})
  · intro z hz
    by_cases hg : z ∈ BranchGood 4
    · obtain ⟨a, -, hD⟩ := hz
      refine Or.inr (show z.2 0 1 ≤ 0 from le_of_eq ?_)
      exact (star_of_branchGood hP hg (e := id) Function.injective_id (A := a)
        (fun p q hpq ↦ by simp only [id]; rw [hD p q, ite_eq_right hpq])).2 0 1 (by decide)
    · exact Or.inl hg
  · exact measure_union_null (criticalGenealogyLimit_branchGood hx hL1 hpos h2 (by norm_num))
      (criticalGenealogyLimit_coalescence_nonpos_null hx hL1 hpos h2 hinf (by decide))

/-- **Two distinct branch points of degree four never occur.** -/
theorem criticalDistanceLaw_twoStarSet_null (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g) :
    (criticalDistanceLaw g 6 : Measure (Fin 6 → Fin 6 → ℝ)) TwoStarSet = 0 := by
  have hP := strictMonoOn_profilePrimitive hL1 hpos
  simp only [criticalDistanceLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (continuous_distanceOfGenealogy hL1.1).measurable
    measurableSet_twoStarSet]
  refine measure_mono_null (t := (BranchGood 6)ᶜ) (fun z hz ↦ ?_)
    (criticalGenealogyLimit_branchGood hx hL1 hpos h2 (by norm_num))
  intro hg
  obtain ⟨a, L, hL, -, hD⟩ := hz
  have h1 := (star_of_branchGood hP hg (e := ![0, 1, 2, 3]) (by decide)
    (A := ![a 0, a 1, a 2, a 3 + L]) (fun p q hpq ↦ by
      rw [hD]
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> ring)).1 0
  have h2 := (star_of_branchGood hP hg (e := ![3, 4, 5, 0]) (by decide)
    (A := ![a 3, a 4, a 5, a 0 + L]) (fun p q hpq ↦ by
      rw [hD]
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢ <;> ring)).1 3
  simp at h1 h2
  linarith

/-- A good genealogy with `m` positive-born samples pairwise coalescing at time zero
has a star among its distances. -/
theorem distanceOfGenealogy_mem_starAmong (hP : StrictMonoOn (profilePrimitive g) (Icc 0 1))
    {m : ℕ} {z : GenealogySpace k} (hcube : z ∈ unitCube k) {e : Fin m → Fin k}
    (he : Function.Injective e) (hb : ∀ p, 0 < z.1 (e p))
    (hc : ∀ p q, p ≠ q → z.2 (e p) (e q) ≤ 0) : distanceOfGenealogy g z ∈ StarAmong m k := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  refine ⟨e, he, fun p ↦ profilePrimitive g (z.1 (e p)), fun p ↦ ?_, fun p q ↦ ?_⟩
  · have := hP h0 (mem_unitCube_fst hcube _) (hb p)
    rwa [profilePrimitive_zero] at this
  · by_cases hpq : p = q
    · subst hpq
      simp [distanceOfGenealogy]
    · have hc0 : z.2 (e p) (e q) = 0 :=
        le_antisymm (hc p q hpq) (mem_unitCube_snd hcube _ _).1
      simp only [distanceOfGenealogy, he.ne hpq, hpq, ↓reduceIte, hc0, profilePrimitive_zero]
      ring

/-- **Many root clusters when `∫₀ g² < ∞`.** For every `m ≥ 2`, some number of samples
contains a star of `m` samples with probability arbitrarily close to one. -/
theorem criticalDistanceLaw_starAmong_compl_le (hx : AdmissibleArray xa)
    (hL1 : HasL1ReciprocalProfile xa (1 / 2) g) (hpos : PositiveProfile g)
    (h2 : HasLocalSquareMomentProfile xa (1 / 2) g)
    (hfin : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal (g t ^ 2) < ⊤) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k, (criticalDistanceLaw g k : Measure (Fin k → Fin k → ℝ)) (StarAmong m k)ᶜ ≤
      ENNReal.ofReal ε := by
  have hP := strictMonoOn_profilePrimitive hL1 hpos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set M : ℝ := 4 * m / ε with hM
  have hM0 : 0 < M := by positivity
  have hεM : ε * M = 4 * m := by rw [hM]; field_simp
  set c₀ : ℝ := ε / (2 * m ^ 2 * (M + 1) ^ 2) with hc₀
  have hc₀0 : 0 < c₀ := by positivity
  obtain ⟨δ, ⟨hδ0, hδ2⟩, hδH⟩ : ∃ δ : ℝ, (0 < δ ∧ δ < 1 / 2) ∧
      ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2) ≤ ENNReal.ofReal c₀ := by
    have hlim : Tendsto (fun δ : ℝ ↦ ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2)
        ∂(volume.restrict (Ioc 0 (1 / 2)))) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_setLIntegral_zero hfin.ne
      have hv : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal δ) (𝓝[>] 0) (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv
        (fun _ ↦ bot_le) (fun δ ↦ ?_)
      simp only [Function.comp_apply]
      calc volume.restrict (Ioc 0 (1 / 2)) (Ioc 0 δ) ≤ volume (Ioc 0 δ) :=
            Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal δ := by rw [Real.volume_Ioc, sub_zero]
    have hev := (hlim.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.mpr hc₀0))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))
    obtain ⟨δ, hδ, hδmem⟩ := hev.exists
    refine ⟨δ, hδmem, ?_⟩
    rwa [Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (Ioc_subset_Ioc_right hδmem.2.le)] at hδ
  set L : ℕ := ⌈M / δ⌉₊ with hL
  have hLge : M / δ ≤ L := Nat.le_ceil _
  have hLlt : (L : ℝ) < M / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hLδ : M ≤ L * δ := by rwa [div_le_iff₀ hδ0] at hLge
  have hLδ' : (L : ℝ) * δ ≤ M + 1 := by
    have := mul_lt_mul_of_pos_right hLlt hδ0
    rw [add_mul, div_mul_cancel₀ _ hδ0.ne', one_mul] at this
    linarith
  have hLpos : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  set k := m * L with hk
  have hk2 : 2 ≤ k := le_trans hm (Nat.le_mul_of_pos_right m hLpos)
  refine ⟨k, ?_⟩
  set μ := (criticalGenealogyLimit g k : Measure (GenealogySpace k))
  set e : Fin m × Fin L ≃ Fin k := finProdFinEquiv
  set G : Fin m → Finset (Fin k) := fun p ↦ Finset.univ.image fun r ↦ e (p, r)
  have hGcard : ∀ p, (G p).card = L := fun p ↦ by
    rw [Finset.card_image_of_injective _ (fun r r' h ↦ by simpa using e.injective h)]
    simp
  set A : Set (GenealogySpace k) := ⋃ p : Fin m, {z | ∀ i ∈ G p, δ ≤ z.1 i}
  set B : Set (GenealogySpace k) := ⋃ ij : {ij : Fin k × Fin k // ij.1 ≠ ij.2},
    {z | z.1 ij.1.1 < δ ∧ z.1 ij.1.2 < δ ∧ 0 < z.2 ij.1.1 ij.1.2}
  have hcover : distanceOfGenealogy g ⁻¹' (StarAmong m k)ᶜ ⊆ (BranchGood k)ᶜ ∪ A ∪ B := by
    intro z hz
    by_contra hcon
    simp only [mem_union, not_or, mem_compl_iff, not_not] at hcon
    obtain ⟨⟨hg, hA⟩, hB⟩ := hcon
    apply hz
    have hex : ∀ p, ∃ i ∈ G p, z.1 i < δ := by
      intro p
      by_contra hne
      push Not at hne
      exact hA (mem_iUnion.mpr ⟨p, hne⟩)
    choose f hfG hfδ using hex
    have hfinj : Function.Injective f := by
      intro p q hpq
      obtain ⟨r, -, hr⟩ := Finset.mem_image.mp (hfG p)
      obtain ⟨r', -, hr'⟩ := Finset.mem_image.mp (hfG q)
      have := e.injective (hr.trans (hpq.trans hr'.symm))
      exact (Prod.mk.inj this).1
    refine distanceOfGenealogy_mem_starAmong hP hg.2.1 hfinj (fun p ↦ hg.2.2.1 _)
      (fun p q hpq ↦ ?_)
    by_contra hc
    push Not at hc
    exact hB (mem_iUnion.mpr ⟨⟨(f p, f q), hfinj.ne hpq⟩, hfδ p, hfδ q, hc⟩)
  have hAle : μ A ≤ m * ENNReal.ofReal ((1 - δ / 2) ^ L) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ p : Fin m, μ {z | ∀ i ∈ G p, δ ≤ z.1 i}
        ≤ ∑ _p : Fin m, ENNReal.ofReal ((1 - δ / 2) ^ L) :=
          Finset.sum_le_sum fun p _ ↦
            (criticalGenealogyLimit_births_ge_le hx hL1 hpos h2 (G p) hδ0 (by linarith)).trans_eq
              (by rw [hGcard])
      _ = _ := by simp
  have hBle : μ B ≤ ((k * k : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ ij : {ij : Fin k × Fin k // ij.1 ≠ ij.2},
          μ {z | z.1 ij.1.1 < δ ∧ z.1 ij.1.2 < δ ∧ 0 < z.2 ij.1.1 ij.1.2}
        ≤ ∑ _ij : {ij : Fin k × Fin k // ij.1 ≠ ij.2},
            ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2) :=
          Finset.sum_le_sum fun ij _ ↦
            criticalGenealogyLimit_early_merge_le hx hL1 hpos h2 ij.2 hδ0 hδ2
      _ = (Fintype.card {ij : Fin k × Fin k // ij.1 ≠ ij.2} : ℝ≥0∞) *
            (ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2)) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ _ := by
          gcongr
          exact (Fintype.card_subtype_le _).trans (by simp)
  have hnum1 : (m : ℝ≥0∞) * ENNReal.ofReal ((1 - δ / 2) ^ L) ≤ ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hm0.le]
    apply ENNReal.ofReal_le_ofReal
    have hp := one_sub_pow_le (a := δ / 2) (by linarith) (by linarith) L
    have hden : 0 < 1 + (L : ℝ) * (δ / 2) := by positivity
    have hq : 1 / (1 + (L : ℝ) * (δ / 2)) ≤ ε / (2 * m) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hLδ hε.le]
    calc (m : ℝ) * (1 - δ / 2) ^ L ≤ m * (ε / (2 * m)) :=
          mul_le_mul_of_nonneg_left (hp.trans hq) hm0.le
      _ = ε / 2 := by field_simp
  have hnum2 : ((k * k : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2)) ≤
        ENNReal.ofReal (ε / 2) := by
    calc ((k * k : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (δ ^ 2) * ∫⁻ t in Ioc 0 δ, ENNReal.ofReal (g t ^ 2))
        ≤ ENNReal.ofReal ((k * k : ℕ) : ℝ) * (ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal c₀) := by
          rw [ENNReal.ofReal_natCast]
          gcongr
      _ = ENNReal.ofReal (((k * k : ℕ) : ℝ) * δ ^ 2 * c₀) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          exact (mul_assoc _ _ _).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hkk : ((k * k : ℕ) : ℝ) * δ ^ 2 = (m : ℝ) ^ 2 * ((L : ℝ) * δ) ^ 2 := by
            simp only [hk]
            push_cast
            ring
          rw [hkk]
          have hsq : ((L : ℝ) * δ) ^ 2 ≤ (M + 1) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hLδ' 2
          calc (m : ℝ) ^ 2 * ((L : ℝ) * δ) ^ 2 * c₀ ≤ (m : ℝ) ^ 2 * (M + 1) ^ 2 * c₀ := by
                gcongr
            _ = ε / 2 := by rw [hc₀]; field_simp
  simp only [criticalDistanceLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (continuous_distanceOfGenealogy hL1.1).measurable
    (measurableSet_starAmong m k).compl]
  calc μ (distanceOfGenealogy g ⁻¹' (StarAmong m k)ᶜ) ≤ μ ((BranchGood k)ᶜ ∪ A ∪ B) :=
        measure_mono hcover
    _ ≤ μ (BranchGood k)ᶜ + μ A + μ B :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ 0 + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        gcongr
        · exact (criticalGenealogyLimit_branchGood hx hL1 hpos h2 hk2).le
        · exact hAle.trans hnum1
        · exact hBle.trans hnum2
    _ = ENNReal.ofReal ε := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Limit

end CriticalGenealogy

namespace MeasuredGHSpace

/-- A sampled law charging a set built from nonempty open sets is nonzero. -/
theorem iidDistanceLaw_ne_zero_of_open (Y : CompactMeasuredSpace.{0})
    (hfs : Measure.IsOpenPosMeasure (Y.law : Measure Y)) {m : ℕ}
    {F : Set (Fin m → Fin m → ℝ)} (hF : MeasurableSet F) (U : Fin m → Set Y)
    (hU : ∀ i, IsOpen (U i) ∧ (U i).Nonempty)
    (hUF : ∀ y : Fin m → Y, (∀ i, y i ∈ U i) → (fun i j ↦ dist (y i) (y j)) ∈ F) :
    (iidDistanceLaw Y m : Measure (Fin m → Fin m → ℝ)) F ≠ 0 := by
  simp only [iidDistanceLaw, iidDistanceLawOn, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_pi]
  rw [Measure.map_apply (continuous_distanceMatrix m).measurable hF]
  apply ne_of_gt
  calc (0 : ℝ≥0∞) < Measure.pi (fun _ : Fin m ↦ (Y.law : Measure Y)) (Set.pi univ U) := by
        rw [Measure.pi_pi]
        exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦
          (hU i).1.measure_ne_zero _ (hU i).2)
    _ ≤ _ := measure_mono fun y hy ↦ hUF y fun i ↦ hy i (mem_univ i)

/-- Without four-stars among samples, a fully supported real tree has no point of
degree at least `m`. -/
theorem degree_lt_of_starSet_null (Y : CompactMeasuredSpace.{0})
    (hfs : Measure.IsOpenPosMeasure (Y.law : Measure Y)) (hT : IsRealTree Y) {m : ℕ}
    (h : (iidDistanceLaw Y m : Measure (Fin m → Fin m → ℝ)) (StarSet m) = 0) (y : Y) :
    degree y < m := by
  by_contra hle
  push Not at hle
  obtain ⟨U, hU, hUF⟩ := exists_open_star hT hle
  exact iidDistanceLaw_ne_zero_of_open Y hfs (measurableSet_starSet m) U hU hUF h

/-- Without double stars among samples, a fully supported real tree has at most one
point of degree at least four. -/
theorem eq_of_twoStarSet_null (Y : CompactMeasuredSpace.{0})
    (hfs : Measure.IsOpenPosMeasure (Y.law : Measure Y)) (hT : IsRealTree Y) (h4 : FourPoint Y)
    (h : (iidDistanceLaw Y 6 : Measure (Fin 6 → Fin 6 → ℝ)) TwoStarSet = 0) {x x' : Y}
    (hx : 4 ≤ degree x) (hx' : 4 ≤ degree x') : x = x' := by
  by_contra hne
  obtain ⟨U, hU, hUF⟩ := exists_open_twoStar hT h4 hne hx hx'
  exact iidDistanceLaw_ne_zero_of_open Y hfs measurableSet_twoStarSet U hU hUF h

/-- A star among samples of a real tree witnesses a point of large degree. -/
theorem exists_le_degree_of_starAmong (Y : CompactMeasuredSpace.{0}) (hT : IsRealTree Y)
    (h4 : FourPoint Y) {m k : ℕ} (hm : 2 ≤ m)
    (h : (iidDistanceLaw Y k : Measure (Fin k → Fin k → ℝ)) (StarAmong m k) ≠ 0) :
    ∃ x : Y, (m : ℕ∞) ≤ degree x := by
  simp only [iidDistanceLaw, iidDistanceLawOn, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_pi] at h
  rw [Measure.map_apply (continuous_distanceMatrix k).measurable
    (measurableSet_starAmong m k)] at h
  obtain ⟨y, e, -, hstar⟩ := nonempty_of_measure_ne_zero h
  exact exists_le_degree_of_mem_starSet hT h4 hm (fun p ↦ y (e p)) hstar

/-- If annealed sampled events have probabilities tending to one along a sequence,
almost every space charges one of them. -/
theorem ae_exists_sampled_ne_zero {Q : ProbabilityMeasure MeasuredGHSpace.{0}} {kk : ℕ → ℕ}
    {F : ∀ N, Set (Fin (kk N) → Fin (kk N) → ℝ)} (hF : ∀ N, MeasurableSet (F N))
    (h : ∀ N, (annealedDistanceLaw Q (kk N) : Measure (Fin (kk N) → Fin (kk N) → ℝ)) (F N)ᶜ ≤
      ENNReal.ofReal (1 / ((N : ℝ) + 1))) :
    ∀ᵐ X ∂(Q : Measure MeasuredGHSpace.{0}),
      ∃ N, (sampledDistanceLaw (kk N) X : Measure (Fin (kk N) → Fin (kk N) → ℝ)) (F N) ≠ 0 := by
  set Z : ℕ → Set MeasuredGHSpace.{0} := fun N ↦
    {X | (sampledDistanceLaw (kk N) X : Measure (Fin (kk N) → Fin (kk N) → ℝ)) (F N) = 0}
  have hmeas : ∀ N, Measurable fun X : MeasuredGHSpace.{0} ↦
      (sampledDistanceLaw (kk N) X : Measure (Fin (kk N) → Fin (kk N) → ℝ)) (F N) := fun N ↦
    (Measure.measurable_coe (hF N)).comp
      (measurable_toMeasure_of_continuous (continuous_sampledDistanceLaw (kk N)))
  have hZm : ∀ N, MeasurableSet (Z N) := fun N ↦ hmeas N (measurableSet_singleton 0)
  have hZ : ∀ N, (Q : Measure MeasuredGHSpace.{0}) (Z N) ≤
      ENNReal.ofReal (1 / ((N : ℝ) + 1)) := by
    intro N
    refine le_trans ?_ (h N)
    rw [annealedDistanceLaw, continuousMixture_apply Q (continuous_sampledDistanceLaw _)
      (hF N).compl]
    calc (Q : Measure MeasuredGHSpace.{0}) (Z N) =
          ∫⁻ X, (Z N).indicator 1 X ∂(Q : Measure MeasuredGHSpace.{0}) :=
          (lintegral_indicator_one (hZm N)).symm
      _ ≤ _ := lintegral_mono fun X ↦ by
          by_cases hX : X ∈ Z N
          · have hX' : (sampledDistanceLaw (kk N) X : Measure (Fin (kk N) → Fin (kk N) → ℝ))
                (F N) = 0 := hX
            rw [indicator_of_mem hX, Pi.one_apply, prob_compl_eq_one_sub (hF N), hX', tsub_zero]
          · rw [indicator_of_notMem hX]
            exact bot_le
  rw [ae_iff]
  have he : {X : MeasuredGHSpace.{0} | ¬ ∃ N,
      (sampledDistanceLaw (kk N) X : Measure (Fin (kk N) → Fin (kk N) → ℝ)) (F N) ≠ 0} =
        ⋂ N, Z N := by
    ext X
    simp [Z]
  rw [he]
  apply le_antisymm _ bot_le
  have hlim : Tendsto (fun N : ℕ ↦ ENNReal.ofReal (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto' hlim fun N ↦ (measure_mono (iInter_subset _ N)).trans (hZ N)

/-- Every class is represented by a space isometric to the representative of its
underlying Gromov–Hausdorff class. -/
theorem exists_rep_isometryEquiv (X : MeasuredGHSpace.{0}) :
    ∃ Y : CompactMeasuredSpace.{0}, toMeasuredGHSpace Y = X ∧
      Nonempty ((underlyingGH X).Rep ≃ᵢ Y) := by
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep X
  refine ⟨Y, rfl, ?_⟩
  rw [show (⟦Y⟧ : MeasuredGHSpace.{0}) = toMeasuredGHSpace Y from rfl,
    underlyingGH_toMeasuredGHSpace]
  exact GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp
    (GromovHausdorff.GHSpace.toGHSpace_rep (GromovHausdorff.toGHSpace Y))

end MeasuredGHSpace

open RealTree MeasuredGHSpace CriticalGenealogy

/-- Almost surely, every representative of the critical limit is a fully supported
compact real tree satisfying the four-point condition, whose samples never form a
double star. -/
theorem criticalTreeLaw_ae_structure {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      ∀ Y : CompactMeasuredSpace.{0}, toMeasuredGHSpace Y = X →
        Measure.IsOpenPosMeasure (Y.law : Measure Y) ∧ FourPoint Y ∧ IsRealTree Y ∧
          (iidDistanceLaw Y 6 : Measure (Fin 6 → Fin 6 → ℝ)) TwoStarSet = 0 := by
  obtain ⟨hconv, hann, hfull⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  have hxa := admissible_initialRowExtension hx
  have hL1a := hasL1ReciprocalProfile_initialRowExtension hL1
  have hposa := positiveProfile_reciprocal hf
  have h2a := hasLocalSquareMomentProfile_initialRowExtension h2
  have h6 := ae_sampledDistanceLaw_null (Q := criticalTreeLaw (fun t ↦ 1 / f t))
    measurableSet_twoStarSet (by
      rw [hann 6]
      exact criticalDistanceLaw_twoStarSet_null hxa hL1a hposa h2a)
  have h4 : (annealedDistanceLaw (criticalTreeLaw (fun t ↦ 1 / f t)) 4 :
      Measure (Fin 4 → Fin 4 → ℝ)) (fourPointMatrices 4) = 1 := by
    rw [hann 4]
    exact criticalDistanceLaw_fourPoint hxa hL1a hposa h2a 4
  have hfp := ae_fourPoint_of_annealed h4 hfull
  have hmid := ae_hasMidpoints_of_tendsto hconv fun ε hε ↦ forward_ae_approxMidpoints x hε
  filter_upwards [hfull, h6, hfp, hmid] with X hfs h6X hfpX hmidX
  intro Y hY
  subst hY
  rw [hasFullSupport_toMeasuredGHSpace] at hfs
  rw [sampledDistanceLaw_toMeasuredGHSpace] at h6X
  rw [underlyingGH_toMeasuredGHSpace, fourPoint_toGHSpace_rep_iff] at hfpX
  rw [underlyingGH_toMeasuredGHSpace] at hmidX
  have hmidY : HasMidpoints Y := by
    apply hasMidpoints_of_approx
    intro ε hε
    refine (approxMidpoints_toGHSpace_rep_iff Y).mp fun a b ↦ ?_
    obtain ⟨m, hm1, hm2⟩ := hmidX a b
    exact ⟨m, by rw [hm1, sub_self, abs_zero]; exact hε.le,
      by rw [hm2, sub_self, abs_zero]; exact hε.le⟩
  exact ⟨hfs, hfpX, isRealTree_of_fourPoint hfpX hmidY, h6X⟩

/-- If `∫₀^{1/2} f⁻² = ∞`, the critical limit is almost surely binary. -/
theorem criticalTreeLaw_ae_binary_of_infinite {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n))
    (hinf : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) = ⊤) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      IsBinaryTree (underlyingGH X).Rep := by
  obtain ⟨-, hann, -⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  have hxa := admissible_initialRowExtension hx
  have hL1a := hasL1ReciprocalProfile_initialRowExtension hL1
  have hposa := positiveProfile_reciprocal hf
  have h2a := hasLocalSquareMomentProfile_initialRowExtension h2
  have h4s := ae_sampledDistanceLaw_null (Q := criticalTreeLaw (fun t ↦ 1 / f t))
    (measurableSet_starSet 4) (by
      rw [hann 4]
      exact criticalDistanceLaw_starSet_null hxa hL1a hposa h2a hinf)
  filter_upwards [criticalTreeLaw_ae_structure hx hf hL1 h2 hpop, h4s] with X hS h4X
  obtain ⟨Y, hY, ⟨e⟩⟩ := exists_rep_isometryEquiv X
  obtain ⟨hfs, -, hT, -⟩ := hS Y hY
  subst hY
  rw [sampledDistanceLaw_toMeasuredGHSpace] at h4X
  intro y
  rw [← degree_isometryEquiv e y]
  exact le_three_of_lt_four (by exact_mod_cast degree_lt_of_starSet_null Y hfs hT h4X (e y))

/-- **Root condensation (M04c).** If `∫₀^{1/2} f⁻² < ∞`, almost surely the critical
limit has a point of infinite degree and every other branch point has degree three.
Since the limit is unpointed, this point represents the source's root only up to the
Gromov–Hausdorff–Prokhorov encoding; it is automatically unique. -/
theorem criticalTreeLaw_ae_rootDegree {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n))
    (hfin : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) < ⊤) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      ∃ ρ : (underlyingGH X).Rep, degree ρ = ⊤ ∧ ∀ y, y ≠ ρ → 3 ≤ degree y → degree y = 3 := by
  obtain ⟨-, hann, -⟩ := critical_scaling_limit hx hf hL1 h2 hpop
  have hxa := admissible_initialRowExtension hx
  have hL1a := hasL1ReciprocalProfile_initialRowExtension hL1
  have hposa := positiveProfile_reciprocal hf
  have h2a := hasLocalSquareMomentProfile_initialRowExtension h2
  have hseq : ∀ m N : ℕ, ∃ k, (criticalDistanceLaw (fun t ↦ 1 / f t) k :
      Measure (Fin k → Fin k → ℝ)) (StarAmong (m + 2) k)ᶜ ≤
        ENNReal.ofReal (1 / ((N : ℝ) + 1)) := fun m N ↦
    criticalDistanceLaw_starAmong_compl_le hxa hL1a hposa h2a hfin (by omega) (by positivity)
  choose kk hkk using hseq
  have hex : ∀ m : ℕ, ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      ∃ N, (sampledDistanceLaw (kk m N) X : Measure (Fin (kk m N) → Fin (kk m N) → ℝ))
        (StarAmong (m + 2) (kk m N)) ≠ 0 := fun m ↦
    ae_exists_sampled_ne_zero (fun N ↦ measurableSet_starAmong _ _) (fun N ↦ by
      rw [hann]
      exact hkk m N)
  rw [← ae_all_iff] at hex
  filter_upwards [criticalTreeLaw_ae_structure hx hf hL1 h2 hpop, hex] with X hS hexX
  obtain ⟨Y, hY, ⟨e⟩⟩ := exists_rep_isometryEquiv X
  obtain ⟨hfs, h4, hT, h6⟩ := hS Y hY
  subst hY
  simp only [sampledDistanceLaw_toMeasuredGHSpace] at hexX
  have hdeg : ∀ m : ℕ, ∃ y : Y, ((m + 2 : ℕ) : ℕ∞) ≤ degree y := fun m ↦ by
    obtain ⟨N, hN⟩ := hexX m
    exact exists_le_degree_of_starAmong Y hT h4 (by omega) hN
  have huniq : ∀ y y' : Y, 4 ≤ degree y → 4 ≤ degree y' → y = y' := fun y y' hy hy' ↦
    eq_of_twoStarSet_null Y hfs hT h4 h6 hy hy'
  obtain ⟨ρ, hρ⟩ := hdeg 2
  have hρ4 : (4 : ℕ∞) ≤ degree ρ := by exact_mod_cast hρ
  have hρtop : degree ρ = ⊤ := by
    apply eq_top_of_forall_natCast_le
    intro m
    obtain ⟨y, hy⟩ := hdeg (m + 2)
    have hy4 : (4 : ℕ∞) ≤ degree y :=
      le_trans (by exact_mod_cast (show 4 ≤ m + 2 + 2 by omega)) hy
    rw [← huniq y ρ hy4 hρ4]
    exact le_trans (by exact_mod_cast (show m ≤ m + 2 + 2 by omega)) hy
  refine ⟨e.symm ρ, ?_, fun y hy h3 ↦ ?_⟩
  · rw [← degree_isometryEquiv e, e.apply_symm_apply, hρtop]
  · rw [← degree_isometryEquiv e] at h3 ⊢
    have hne : e y ≠ ρ := fun h ↦ hy (by rw [← h, e.symm_apply_apply])
    apply le_antisymm _ h3
    apply le_three_of_lt_four
    by_contra hlt
    push Not at hlt
    exact hne (huniq _ _ hlt hρ4)

/-- **Binary branching (M04b).** Almost surely, the critical limit is binary (all metric
degrees at most three) if and only if `∫₀^{1/2} f⁻² = ∞`. The source's further remark that
the root then has degree one needs a pointed limit and is not claimed here. -/
theorem criticalTreeLaw_ae_binary_iff {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      (IsBinaryTree (underlyingGH X).Rep ↔
        ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) = ⊤) := by
  by_cases hinf : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) = ⊤
  · filter_upwards [criticalTreeLaw_ae_binary_of_infinite hx hf hL1 h2 hpop hinf] with X hX
    exact ⟨fun _ ↦ hinf, fun _ ↦ hX⟩
  · filter_upwards [criticalTreeLaw_ae_rootDegree hx hf hL1 h2 hpop
      (lt_top_iff_ne_top.mpr hinf)] with X hX
    obtain ⟨ρ, hρ, -⟩ := hX
    refine ⟨fun hb ↦ absurd (hb ρ) ?_, fun h ↦ absurd h hinf⟩
    rw [hρ]
    simp

/-- **Theorem `thm:properties` (M04).** Under the hypotheses of `thm:critique`, almost
surely the critical limit `𝒯(f)` is a compact real tree whose mass measure has full
support and charges only leaves; it is binary if and only if `∫₀^{1/2} f⁻² = ∞`; and if
this integral is finite, it has a (unique) point of infinite degree, all other branch
points having degree three. Binary means all metric degrees are at most three (two
children at each branch point); the source's remark that the root has degree one when the
integral is infinite needs a pointed limit and is not claimed. -/
theorem critical_tree_properties {x : ℕ → ℕ → ℤ} {f : ℝ → ℝ}
    (hx : ∀ n : ℕ, 0 < n → IsSigned (x n) ∧ SurvivesThrough (x n) n)
    (hf : ∀ᵐ t ∂profileMeasure, 0 < f t)
    (hL1 : HasL1ReciprocalProfile x (1 / 2) (fun t ↦ 1 / f t))
    (h2 : HasLocalSquareMomentProfile x (1 / 2) (fun t ↦ 1 / f t))
    (hpop : (fun n ↦ (rowMaxPopulation (x n) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.sqrt n)) :
    ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      HasFullSupport X ∧ IsRealTree (underlyingGH X).Rep ∧ LeavesCarryMass X ∧
        (IsBinaryTree (underlyingGH X).Rep ↔
          ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) = ⊤) ∧
        (∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) < ⊤ →
          ∃ ρ : (underlyingGH X).Rep, degree ρ = ⊤ ∧
            ∀ y, y ≠ ρ → 3 ≤ degree y → degree y = 3) := by
  have hroot : ∀ᵐ X ∂(criticalTreeLaw (fun t ↦ 1 / f t) : Measure MeasuredGHSpace.{0}),
      (∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) < ⊤ →
        ∃ ρ : (underlyingGH X).Rep, degree ρ = ⊤ ∧
          ∀ y, y ≠ ρ → 3 ≤ degree y → degree y = 3) := by
    by_cases hfin : ∫⁻ t in Ioc 0 (1 / 2), ENNReal.ofReal ((1 / f t) ^ 2) < ⊤
    · filter_upwards [criticalTreeLaw_ae_rootDegree hx hf hL1 h2 hpop hfin] with X hX
      exact fun _ ↦ hX
    · exact ae_of_all _ fun X h ↦ absurd h hfin
  filter_upwards [criticalTreeLaw_ae_leaves hx hf hL1 h2 hpop,
    criticalTreeLaw_ae_binary_iff hx hf hL1 h2 hpop, hroot] with X hl hb hr
  exact ⟨hl.1, hl.2.1, hl.2.2, hb, hr⟩

end Freezing2
