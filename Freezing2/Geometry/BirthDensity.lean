module

public import Freezing2.Probability.BirthTimeLimit
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Density of actual reverse birth coordinates

Every fixed nontrivial time interval eventually contains a freezing time,
by the proved macroscopic count asymptotics. Its one-step birth shift is
retained. Compactness makes the resulting approximation uniform on `[0,1]`.
-/

@[expose] public section

open Filter Set Metric
open scoped Topology Classical

namespace Freezing2

/-- Compactness upgrades eventual pointwise approximation by varying finite
sets to eventual uniform density. -/
theorem eventually_uniform_approx_of_compact {Y V : Type*} [PseudoMetricSpace Y]
    {s : Set Y} (hs : IsCompact s) (L : ℕ → Finset V) (f : ℕ → V → Y)
    (hp : ∀ y ∈ s, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ v ∈ L n, dist y (f n v) < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ s, ∃ v ∈ L n, dist y (f n v) < ε := by
  obtain ⟨t, hts, ht, hcover⟩ := hs.finite_cover_balls (half_pos hε)
  have hall : ∀ᶠ n in atTop, ∀ z ∈ t, ∃ v ∈ L n, dist z (f n v) < ε / 2 :=
    ht.eventually_all.mpr (fun z hz ↦ hp z (hts hz) _ (half_pos hε))
  filter_upwards [hall] with n hn
  intro y hy
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hcover hy)
  obtain ⟨v, hv, hzv⟩ := hn z hz
  refine ⟨v, hv, ?_⟩
  have hdist : dist y z < ε / 2 := hyz
  linarith [dist_triangle y z (f n v)]

/-- A fixed normalized time is approximated by an actual frozen label.
In particular the endpoint zero is not inserted as an artificial vertex. -/
theorem eventually_exists_near_birth
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {t ε : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ v ∈ vertexLabels (x n) n,
      dist t ((birthTime n v : ℝ) / n) < ε := by
  let a : ℝ := max 0 (t - ε / 4)
  let b : ℝ := min 1 (t + ε / 4)
  have ha : 0 ≤ a := le_max_left _ _
  have hb : b ≤ 1 := min_le_left _ _
  have hab : a < b := by
    dsimp [a, b]
    rw [max_lt_iff]
    constructor <;> rw [lt_min_iff] <;> constructor <;> linarith [ht.1, ht.2]
  have hcount := (tendsto_downSteps_macroscopic hx hα hL1 hpos ha hab.le hb).eventually_const_lt
    (sub_pos.mpr hab)
  have hinv := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const
    (show 0 < ε / 4 by positivity)
  filter_upwards [hcount, hinv, eventually_gt_atTop 0] with n hcn hin hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : 0 < (downSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card := by
    by_contra h
    have hz : (downSteps (x n) ⌊(n : ℝ) * a⌋₊ ⌊(n : ℝ) * b⌋₊).card = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hcn
    exact lt_irrefl _ hcn
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  simp only [downSteps, Finset.mem_filter, Finset.mem_Ioc] at hi
  have hi0 : 0 < i := by omega
  have hinum : (i : ℝ) ≤ (n : ℝ) * b :=
    (by exact_mod_cast hi.1.2 : (i : ℝ) ≤ (⌊(n : ℝ) * b⌋₊ : ℝ)).trans
      (Nat.floor_le (mul_nonneg hn'.le (ha.trans hab.le)))
  have hinat : i ≤ n := by
    have : (i : ℝ) ≤ n := hinum.trans (by nlinarith)
    exact_mod_cast this
  have hia : (n : ℝ) * a < i := (Nat.floor_lt (mul_nonneg hn'.le ha)).mp hi.1.1
  have hlabel : Sum.inl i ∈ vertexLabels (x n) n := by
    simp only [vertexLabels, Finset.inl_mem_disjSum, downSteps, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hi0, hinat⟩, hi.2⟩
  refine ⟨Sum.inl i, hlabel, ?_⟩
  have hib : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have ha' : t - ε / 4 ≤ a := le_max_right _ _
  have hb' : b ≤ t + ε / 4 := min_le_right _ _
  have hsmall : 1 < ε / 4 * n := (div_lt_iff₀ hn').mp hin
  rw [Real.dist_eq, birthTime_frozen, hib, abs_lt]
  constructor
  · have : ((i : ℝ) - 1) / n < t + ε := (div_lt_iff₀ hn').mpr (by nlinarith)
    linarith
  · have : t - ε < ((i : ℝ) - 1) / n := (lt_div_iff₀ hn').mpr (by nlinarith)
    linarith

/-- The complete finite set of actual normalized birth times becomes dense
in the unit interval, uniformly including both endpoints. -/
theorem eventually_uniform_birth_density
    {x : ℕ → ℕ → ℤ} {α : ℝ} {g : ℝ → ℝ}
    (hx : AdmissibleArray x) (hα : α < 1)
    (hL1 : HasL1ReciprocalProfile x α g) (hpos : PositiveProfile g)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) 1, ∃ v ∈ vertexLabels (x n) n,
      dist t ((birthTime n v : ℝ) / n) < ε :=
  eventually_uniform_approx_of_compact isCompact_Icc (fun n ↦ vertexLabels (x n) n)
    (fun n v ↦ (birthTime n v : ℝ) / n)
    (fun _ ht _ hε ↦ eventually_exists_near_birth hx hα hL1 hpos ht hε) hε

end Freezing2
