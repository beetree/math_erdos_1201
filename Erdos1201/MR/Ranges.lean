import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Analysis.DirichletPolyBasics

open MeasureTheory

/-!
# Matomäki–Radziwiłł Prime Range Systems and Level Decompositions

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module fixes the parameters of Matomäki–Radziwiłł Sections 2 and 8 as definitions,
and proves the elementary and structural facts about them:
- Properties of the exponent sequence α_j
- The range system structure and its growth/separation consequences
- Measurability and disjoint partition of heights [T₀, T] into good levels T_j and exceptional set U
-/

namespace Erdos1201.MR

/-- A system of prime ranges [P j, Q j] with the paper's separation conditions (2), (3), for a parameter η ∈ (0, 1/6). -/
structure RangeSystem (J : ℕ) (η : ℝ) where
  P : Fin J → ℕ
  Q : Fin J → ℕ
  two_le_P : ∀ j, 2 ≤ P j
  P_le_Q : ∀ j, P j ≤ Q j
  /-- condition (2): log log Q_j / (log P_{j-1} − 1) ≤ η / (4 j²) for j ≥ 2 (paper indexing). -/
  cond2 : ∀ (j : Fin J) (i : Fin J), i.val + 1 = j.val → Real.log (Real.log (Q j)) / (Real.log (P i) - 1) ≤ η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)
  /-- condition (3): log P_j ≥ (8 j²/η) log Q_{j-1} + 16 log j. -/
  cond3 : ∀ (j : Fin J) (i : Fin J), i.val + 1 = j.val → (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q i) + 16 * Real.log ((j.val + 1 : ℕ) : ℝ) ≤ Real.log (P j)

/-- The ranges as finsets of primes. -/
def RangeSystem.R {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) : Finset ℕ := primeRange (S.P j) (S.Q j)

/-- α_j := 1/4 − η (1 + 1/(2j)) (paper (20), with the paper's index j = j.val + 1 ≥ 1; note α₁ = 1/4 − 3η/2 and α_j − α_{j−1} = η/(2j(j−1)) ≥ η/(2j²)). -/
noncomputable def alpha (η : ℝ) (j : ℕ) : ℝ := 1 / 4 - η * (1 + 1 / (2 * (j : ℝ)))

/-- H_j := j² P₁^{1/6 − η} / (log Q₁)^{1/3} (paper index j = j.val+1; P₁ = P ⟨0,_⟩, Q₁ = Q ⟨0,_⟩). -/
noncomputable def RangeSystem.Hj {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ)

/-- The index set I_j = {v : ⌊H_j log P_j⌋ ≤ v ≤ H_j log Q_j}. -/
noncomputable def RangeSystem.Ij {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J) : Finset ℕ :=
  Finset.Icc ⌊S.Hj hJ j * Real.log (S.P j)⌋₊ ⌈S.Hj hJ j * Real.log (S.Q j)⌉₊

/-- Good_j(t): all short prime polynomials at level j are small at height t. -/
noncomputable def RangeSystem.Good {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (j : Fin J) (t : ℝ) : Prop :=
  ∀ v ∈ S.Ij hJ j, ‖Qpoly β X (S.P j) (S.Q j) (S.Hj hJ j) v ((1 : ℂ) + t * Complex.I)‖ ≤ Real.exp (-(alpha η (j.val + 1)) * v / S.Hj hJ j)

/-- T_j: heights in [T₀, T] for which j is the least good level. -/
noncomputable def RangeSystem.Tset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) : Set ℝ :=
  {t | t ∈ Set.Icc T₀ T ∧ S.Good hJ β X j t ∧ ∀ i : Fin J, i < j → ¬ S.Good hJ β X i t}

/-- U: heights in [T₀, T] with no good level. -/
noncomputable def RangeSystem.Uset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc T₀ T ∧ ∀ j : Fin J, ¬ S.Good hJ β X j t}

/-- Upper bound on α_j: α_j ≤ 1/4 − η for all j. -/
theorem alpha_le (η : ℝ) (hη : 0 < η) (j : ℕ) : alpha η j ≤ 1 / 4 - η := by
  unfold alpha
  by_cases hj : j = 0
  · subst hj
    simp
  · have hj_pos : 0 < (j : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)
    have : 0 < 1 / (2 * (j : ℝ)) := by positivity
    have h1 : 1 ≤ 1 + 1 / (2 * (j : ℝ)) := by linarith
    have h2 : η * 1 ≤ η * (1 + 1 / (2 * (j : ℝ))) := mul_le_mul_of_nonneg_left h1 (le_of_lt hη)
    linarith

/-- Monotonicity of α_j in j. -/
theorem alpha_mono (η : ℝ) (hη : 0 < η) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : alpha η i ≤ alpha η j := by
  unfold alpha
  have hi_pos : (0 : ℝ) < (i : ℝ) := Nat.cast_pos.mpr (by linarith)
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by linarith)
  have hij_r : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  have h2i : (0 : ℝ) < 2 * (i : ℝ) := by linarith
  have h_le : 1 / (2 * (j : ℝ)) ≤ 1 / (2 * (i : ℝ)) := by
    apply one_div_le_one_div_of_le h2i
    linarith
  have h_add : 1 + 1 / (2 * (j : ℝ)) ≤ 1 + 1 / (2 * (i : ℝ)) := by linarith
  have h_mul : η * (1 + 1 / (2 * (j : ℝ))) ≤ η * (1 + 1 / (2 * (i : ℝ))) :=
    mul_le_mul_of_nonneg_left h_add (le_of_lt hη)
  linarith

/-- The increment used in Section 8.2: α_{j+1} − α_j ≥ η / (2 (j+1)²) for j ≥ 1. -/
theorem alpha_succ_sub_alpha (η : ℝ) (hη : 0 < η) (j : ℕ) (hj : 1 ≤ j) :
    η / (2 * ((j + 1 : ℕ) : ℝ) ^ 2) ≤ alpha η (j + 1) - alpha η j := by
  unfold alpha
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by linarith)
  have hj1_pos : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  push_cast
  have h_div_j : 1 / (2 * (j : ℝ)) = (1 / 2) * (1 / (j : ℝ)) := div_mul_eq_div_mul_one_div 1 2 (j : ℝ)
  have h_div_j1 : 1 / (2 * ((j : ℝ) + 1)) = (1 / 2) * (1 / ((j : ℝ) + 1)) :=
    div_mul_eq_div_mul_one_div 1 2 ((j : ℝ) + 1)
  rw [h_div_j, h_div_j1]
  have h_eq : (1 / 4 - η * (1 + (1 / 2) * (1 / ((j : ℝ) + 1)))) -
      (1 / 4 - η * (1 + (1 / 2) * (1 / (j : ℝ)))) =
      (η / 2) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) := by ring
  rw [h_eq]
  have h_diff : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    rw [div_sub_div _ _ (ne_of_gt hj_pos) (ne_of_gt hj1_pos)]
    ring
  rw [h_diff]
  have h_sq : (j : ℝ) * ((j : ℝ) + 1) ≤ ((j : ℝ) + 1) ^ 2 := by
    nlinarith
  have h_sq_pos : 0 < (j : ℝ) * ((j : ℝ) + 1) := mul_pos hj_pos hj1_pos
  have h_inv : 1 / (((j : ℝ) + 1) ^ 2) ≤ 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le h_sq_pos h_sq
  have h_eta2 : 0 ≤ η / 2 := by linarith
  have h_mul := mul_le_mul_of_nonneg_left h_inv h_eta2
  have h_left : η / (2 * ((j : ℝ) + 1) ^ 2) = (η / 2) * (1 / (((j : ℝ) + 1) ^ 2)) :=
    div_mul_eq_div_mul_one_div η 2 (((j : ℝ) + 1) ^ 2)
  rw [h_left]
  exact h_mul

/-- Positivity of α_j for η < 1/6 and j ≥ 1. -/
theorem alpha_pos (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (j : ℕ) (hj : 1 ≤ j) : 0 < alpha η j := by
  unfold alpha
  have hj_ge : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj_pos : 0 < (j : ℝ) := by positivity
  have h2 : 0 < (2 : ℝ) := by norm_num
  have h2j : (2 : ℝ) ≤ 2 * (j : ℝ) := by linarith
  have h_bound : 1 / (2 * (j : ℝ)) ≤ 1 / 2 := one_div_le_one_div_of_le h2 h2j
  have h_term : 1 + 1 / (2 * (j : ℝ)) ≤ 3 / 2 := by linarith
  have h_mul : η * (1 + 1 / (2 * (j : ℝ))) < 1 / 4 := by
    calc η * (1 + 1 / (2 * (j : ℝ)))
      _ ≤ η * (3 / 2) := mul_le_mul_of_nonneg_left h_term (le_of_lt hη0)
      _ < (1 / 6) * (3 / 2) := mul_lt_mul_of_pos_right hη (by norm_num)
      _ = 1 / 4 := by norm_num
  linarith

/-- Continuity of a single Dirichlet power summand t ↦ n^{-(1 + it)}. -/
lemma continuous_cpow_term (n : ℕ) (hn : 0 < n) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) := by
  have h_eq : (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) =
      (fun t : ℝ => (1 / (n : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * ((Real.log n : ℝ) : ℂ))) := by
    ext t
    exact natCast_cpow_neg_one_add_mul_I_eq_exp n hn t
  rw [h_eq]
  fun_prop

/-- Continuity of the short prime polynomial Qpoly in height t. -/
lemma continuous_Qpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Continuous (fun t : ℝ => Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)) := by
  unfold Qpoly dirichletPoly
  apply continuous_finsetSum
  intro n hn
  have hn_prime : n.Prime := by
    rw [mem_shortPrimeRange] at hn
    exact hn.1.1
  have hn_pos : 0 < n := hn_prime.pos
  have h_term := continuous_cpow_term n hn_pos
  exact continuous_const.mul h_term

/-- Continuity of the norm of Qpoly in height t. -/
lemma continuous_norm_Qpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Continuous (fun t : ℝ => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖) :=
  (continuous_Qpoly β X P Q H v).norm

/-- Measurability of the norm of Qpoly in height t. -/
lemma measurable_norm_Qpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Measurable (fun t : ℝ => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖) :=
  (continuous_norm_Qpoly β X P Q H v).measurable

/-- Measurability of the predicate Good at level j. -/
lemma RangeSystem.measurableSet_good {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (j : Fin J) :
    MeasurableSet {t : ℝ | S.Good hJ β X j t} := by
  have h_eq : {t : ℝ | S.Good hJ β X j t} =
      ⋂ v ∈ S.Ij hJ j, {t : ℝ | ‖Qpoly β X (S.P j) (S.Q j) (S.Hj hJ j) v ((1 : ℂ) + t * Complex.I)‖ ≤
        Real.exp (-(alpha η (j.val + 1)) * v / S.Hj hJ j)} := by
    ext t
    simp only [Good, Set.mem_iInter]
    exact ⟨fun h v hv => h v hv, fun h v hv => h v hv⟩
  rw [h_eq]
  apply Finset.measurableSet_biInter
  intro v hv
  exact measurableSet_le (measurable_norm_Qpoly β X (S.P j) (S.Q j) (S.Hj hJ j) v) measurable_const

/-- Measurability of the set T_j of heights where j is the least good level. -/
theorem RangeSystem.measurableSet_Tset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) :
    MeasurableSet (S.Tset hJ β X T₀ T j) := by
  have h_Tset_eq : S.Tset hJ β X T₀ T j =
      Set.Icc T₀ T ∩ {t | S.Good hJ β X j t} ∩ ⋂ i : Fin J, {t | i < j → ¬ S.Good hJ β X i t} := by
    ext t
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, Set.mem_iInter.mpr h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, Set.mem_iInter.mp h3⟩
  rw [h_Tset_eq]
  refine (measurableSet_Icc.inter (S.measurableSet_good hJ β X j)).inter ?_
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i < j
  · have h_eq : {t : ℝ | i < j → ¬ S.Good hJ β X i t} = {t : ℝ | S.Good hJ β X i t}ᶜ := by
      ext t
      simp [hi]
    rw [h_eq]
    exact (S.measurableSet_good hJ β X i).compl
  · have h_eq : {t : ℝ | i < j → ¬ S.Good hJ β X i t} = Set.univ := by
      ext t
      simp [hi]
    rw [h_eq]
    exact MeasurableSet.univ

/-- Measurability of the set U of heights with no good level. -/
theorem RangeSystem.measurableSet_Uset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    MeasurableSet (S.Uset hJ β X T₀ T) := by
  have h_Uset_eq : S.Uset hJ β X T₀ T =
      Set.Icc T₀ T ∩ ⋂ j : Fin J, {t | ¬ S.Good hJ β X j t} := by
    ext t
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Set.mem_iInter.mpr h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Set.mem_iInter.mp h2⟩
  rw [h_Uset_eq]
  refine measurableSet_Icc.inter ?_
  apply MeasurableSet.iInter
  intro j
  exact (S.measurableSet_good hJ β X j).compl

/-- The T_j and U partition [T₀, T]. -/
theorem RangeSystem.Icc_eq_iUnion_Tset_union_Uset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    Set.Icc T₀ T = (⋃ j : Fin J, S.Tset hJ β X T₀ T j) ∪ S.Uset hJ β X T₀ T := by
  ext t
  constructor
  · intro ht
    by_cases h_all : ∀ j : Fin J, ¬ S.Good hJ β X j t
    · right
      exact ⟨ht, h_all⟩
    · left
      have hj_ex : ∃ j_ex : Fin J, S.Good hJ β X j_ex t := by
        by_contra h_none
        apply h_all
        intro j hj_good
        exact h_none ⟨j, hj_good⟩
      rcases hj_ex with ⟨j_ex, hj_good⟩
      let P : ℕ → Prop := fun n => ∃ h : n < J, S.Good hJ β X ⟨n, h⟩ t
      have hP_ex : ∃ n, P n := ⟨j_ex.val, j_ex.isLt, hj_good⟩
      have : DecidablePred P := Classical.decPred P
      let n₀ := Nat.find hP_ex
      have hn₀_spec : P n₀ := Nat.find_spec hP_ex
      rcases hn₀_spec with ⟨hn₀_lt, hn₀_good⟩
      let j₀ : Fin J := ⟨n₀, hn₀_lt⟩
      have hj₀_min : ∀ i : Fin J, i < j₀ → ¬ S.Good hJ β X i t := by
        intro i hi
        have hi_lt : i.val < n₀ := hi
        have h_not_P := Nat.find_min hP_ex hi_lt
        intro h_good
        apply h_not_P
        exact ⟨i.isLt, h_good⟩
      have ht_in_T : t ∈ S.Tset hJ β X T₀ T j₀ := ⟨ht, hn₀_good, hj₀_min⟩
      exact Set.mem_iUnion.mpr ⟨j₀, ht_in_T⟩
  · intro ht
    rcases ht with ht | ht
    · rw [Set.mem_iUnion] at ht
      rcases ht with ⟨j, hj⟩
      exact hj.1
    · exact ht.1

/-- The sets T_j are pairwise disjoint. -/
theorem RangeSystem.pairwise_disjoint_Tset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    Pairwise (fun i j : Fin J => Disjoint (S.Tset hJ β X T₀ T i) (S.Tset hJ β X T₀ T j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro t hti htj
  rcases lt_or_gt_of_ne hij with h | h
  · have hj_not := htj.2.2 i h
    exact hj_not hti.2.1
  · have hi_not := hti.2.2 j h
    exact hi_not htj.2.1

/-- Each T_j is disjoint from U. -/
theorem RangeSystem.disjoint_Tset_Uset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) :
    Disjoint (S.Tset hJ β X T₀ T j) (S.Uset hJ β X T₀ T) := by
  rw [Set.disjoint_left]
  intro t htT htU
  have hT_good := htT.2.1
  have hU_not := htU.2 j
  exact hU_not hT_good

/-- Consequence of (2): log log Q_j ≤ (1/24) log P_{j−1}, hence log Q_j ≤ Q_{j-1}^{1/24}. -/
theorem RangeSystem.log_Q_le_rpow {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hη0 : 0 < η) (hη : η < 1 / 6) (j i : Fin J) (hij : i.val + 1 = j.val) (hPi : 2 ≤ Real.log (S.P i)) :
    Real.log (S.Q j) ≤ (S.Q i : ℝ) ^ (1 / 24 : ℝ) := by
  have hcond := S.cond2 j i hij
  have hj_ge2 : (2 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    have : 2 ≤ j.val + 1 := by omega
    exact_mod_cast this
  have hj_sq : (4 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hj_denom : (16 : ℝ) ≤ 4 * ((j.val + 1 : ℕ) : ℝ) ^ 2 := by linarith
  have hj_denom_pos : 0 < 4 * ((j.val + 1 : ℕ) : ℝ) ^ 2 := by linarith
  have h_bound1 : η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / 24 := by
    calc η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)
      _ ≤ (1 / 6) / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (le_of_lt hη) (le_of_lt hj_denom_pos)
      _ ≤ (1 / 6) / 16 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hj_denom
      _ ≤ 1 / 24 := by norm_num
  have h_sub_pos : 0 < Real.log (S.P i) - 1 := by linarith
  have h_loglog_le : Real.log (Real.log (S.Q j)) ≤ (1 / 24) * (Real.log (S.P i) - 1) := by
    have h_mul := (div_le_iff₀ h_sub_pos).mp hcond
    calc Real.log (Real.log (S.Q j))
      _ ≤ (η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * (Real.log (S.P i) - 1) := h_mul
      _ ≤ (1 / 24) * (Real.log (S.P i) - 1) :=
        mul_le_mul_of_nonneg_right h_bound1 (le_of_lt h_sub_pos)
  have h_sub_le_logPi : Real.log (S.P i) - 1 ≤ Real.log (S.P i) := by linarith
  have hPi_pos : (0 : ℝ) < S.P i := Nat.cast_pos.mpr (by linarith [S.two_le_P i])
  have hPi_le_Qi : (S.P i : ℝ) ≤ S.Q i := by exact_mod_cast (S.P_le_Q i)
  have h_logPi_le_logQi : Real.log (S.P i) ≤ Real.log (S.Q i) :=
    Real.log_le_log hPi_pos hPi_le_Qi
  have h_sub_le_logQi : Real.log (S.P i) - 1 ≤ Real.log (S.Q i) :=
    h_sub_le_logPi.trans h_logPi_le_logQi
  have h_loglog_le_logQi : Real.log (Real.log (S.Q j)) ≤ (1 / 24) * Real.log (S.Q i) := by
    calc Real.log (Real.log (S.Q j))
      _ ≤ (1 / 24) * (Real.log (S.P i) - 1) := h_loglog_le
      _ ≤ (1 / 24) * Real.log (S.Q i) :=
        mul_le_mul_of_nonneg_left h_sub_le_logQi (by norm_num)
  have h_exp_le := Real.exp_le_exp.mpr h_loglog_le_logQi
  have h_logQj_pos : 0 < Real.log (S.Q j) := by
    have : 2 ≤ S.Q j := (S.two_le_P j).trans (S.P_le_Q j)
    have : (1 : ℝ) < S.Q j := by exact_mod_cast (by omega : 1 < S.Q j)
    exact Real.log_pos this
  rw [Real.exp_log h_logQj_pos] at h_exp_le
  have hQi_pos : 0 < (S.Q i : ℝ) := by
    have : 2 ≤ S.Q i := (S.two_le_P i).trans (S.P_le_Q i)
    exact Nat.cast_pos.mpr (by linarith)
  rw [Real.rpow_def_of_pos hQi_pos]
  rw [mul_comm] at h_exp_le
  exact h_exp_le

/-- Consequence of (3): P_j ≥ P₁^{j²} (paper: 'since P_j ≥ P₁^{j²} by (3)'); prove the weaker but sufficient log P_j ≥ (j.val+1)² log P₁ for all j, by induction along the chain. -/
theorem RangeSystem.log_P_ge {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6) (j : Fin J) :
    ((j.val + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩) ≤ Real.log (S.P j) := by
  have hP0_pos : 0 < Real.log (S.P ⟨0, hJ⟩) := by
    have : (1 : ℝ) < (S.P ⟨0, hJ⟩ : ℝ) := by
      have := S.two_le_P ⟨0, hJ⟩
      exact_mod_cast (by omega : 1 < S.P ⟨0, hJ⟩)
    exact Real.log_pos this
  have h_ind : ∀ (k : ℕ) (hk : k < J), ((k + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩) ≤ Real.log (S.P ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have : (⟨0, hk⟩ : Fin J) = ⟨0, hJ⟩ := by ext; rfl
      rw [this]
      simp
    | succ k ih =>
      intro hk
      have hk_lt : k < J := by omega
      have ih_k := ih hk_lt
      let i : Fin J := ⟨k, hk_lt⟩
      let j_cur : Fin J := ⟨k + 1, hk⟩
      have hij : i.val + 1 = j_cur.val := rfl
      have hcond := S.cond3 j_cur i hij
      have hPi_pos : (0 : ℝ) < S.P i := Nat.cast_pos.mpr (by linarith [S.two_le_P i])
      have hPi_le_Qi : (S.P i : ℝ) ≤ S.Q i := by exact_mod_cast (S.P_le_Q i)
      have h_logPi_le_logQi : Real.log (S.P i) ≤ Real.log (S.Q i) :=
        Real.log_le_log hPi_pos hPi_le_Qi
      have hk1_sq_ge1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
        nlinarith
      have h_logP0_le_Pi : Real.log (S.P ⟨0, hJ⟩) ≤ Real.log (S.P i) := by
        calc Real.log (S.P ⟨0, hJ⟩)
          _ = 1 * Real.log (S.P ⟨0, hJ⟩) := by ring
          _ ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩) :=
            mul_le_mul_of_nonneg_right hk1_sq_ge1 (le_of_lt hP0_pos)
          _ ≤ Real.log (S.P i) := ih_k
      have h_logP0_le_Qi : Real.log (S.P ⟨0, hJ⟩) ≤ Real.log (S.Q i) :=
        h_logP0_le_Pi.trans h_logPi_le_logQi
      have h_bound_Qi : ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩) ≤
          (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) := by
        have h_eta_ge : ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η := by
          have : 8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η = ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 * (8 / η) := by ring
          rw [this]
          have : (1 : ℝ) ≤ 8 / η := by
            rw [le_div_iff₀ hη0]
            linarith
          nlinarith
        have hj_sq_pos : 0 < ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
        calc ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩)
          _ ≤ ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.Q i) :=
            mul_le_mul_of_nonneg_left h_logP0_le_Qi (le_of_lt hj_sq_pos)
          _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) :=
            mul_le_mul_of_nonneg_right h_eta_ge (by linarith [h_logP0_le_Qi, hP0_pos])
      calc ((k + 1 + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩)
        _ = ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 * Real.log (S.P ⟨0, hJ⟩) := rfl
        _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) := h_bound_Qi
        _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) + 16 * Real.log ((j_cur.val + 1 : ℕ) : ℝ) := by
          have : 0 ≤ Real.log ((j_cur.val + 1 : ℕ) : ℝ) := by
            apply Real.log_nonneg
            have : 1 ≤ j_cur.val + 1 := by omega
            exact_mod_cast this
          linarith
        _ ≤ Real.log (S.P j_cur) := hcond
  exact h_ind j.val j.isLt

end Erdos1201.MR
