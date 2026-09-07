import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Decomposition.Lemma12Boundary
import Erdos1201.MR.Decomposition.Lemma12Square

/-!
# Matomäki–Radziwiłł Lemma 12 Assembled

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open MeasureTheory intervalIntegral
open scoped BigOperators Real

namespace Erdos1201.MR

lemma filter_omegaIn_eq_unsiftedSet (X P Q : ℕ) :
    (Finset.Ioc X (2 * X)).filter (fun n => omegaIn (primeRange P Q) n = 0) =
    unsiftedSet X P Q := by
  unfold unsiftedSet omegaIn divisorsIn
  apply Finset.filter_congr
  intro n _
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem integral_norm_sq_F_le_sum_QR :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ) (H : ℝ) (a b : ℕ → ℂ) (c : ℕ → ℂ) (T : ℝ) (U : Set ℝ),
      1 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ X → (P : ℝ) ^ 4 ≤ X → 1 ≤ H → 0 ≤ T → MeasurableSet U → U ⊆ Set.Icc (-T) T →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → a (p * m) = b m * c p) →
      ∫ t in U, ‖dirichletPoly a (Finset.Ioc X (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / P + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by
  obtain ⟨C_D, hC_D_pos, hD⟩ := integral_norm_sq_A₁_sub_sum_QR_le
  obtain ⟨C_S, hC_S_pos, hS⟩ := integral_norm_sq_squareCorrection_le
  let C_3 := 36 * Real.pi + 2
  have hC_3_pos : 0 < C_3 := by positivity
  let C := max 20 (4 * (C_D + C_S + C_3))
  use C
  refine ⟨by positivity, ?_⟩
  intro X P Q H a b c T U hX hP hPQ hQX hP4 hH hT hU hUsub ha hb hc hfactor
  
  let s (t : ℝ) : ℂ := (1 : ℂ) + t * Complex.I
  let w (t : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s t)
  let V := Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊

  let A1 (t : ℝ) := ∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
    (b m * c p) * w t (p * m) / ((omegaIn (primeRange P Q) m : ℂ) + 1)
  let QR (v : ℕ) (t : ℝ) := dirichletPoly c (shortPrimeRange P Q H v) (s t) *
    dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) (s t)
  let QR_sum (t : ℝ) := ∑ v ∈ V, QR v t
  let D (t : ℝ) := A1 t - QR_sum t
  let A2 (t : ℝ) := ∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
    squareCorrection (primeRange P Q) a b c (w t) p m
  let A3 (t : ℝ) := ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => omegaIn (primeRange P Q) n = 0),
    a n * w t n
  let F (t : ℝ) := dirichletPoly a (Finset.Ioc X (2 * X)) (s t)

  have hF : ∀ (t : ℝ), F t = QR_sum t + D t + A2 t + A3 t := by
    intro t
    have h1 := F_eq_ramare X P Q a b c (s t) hfactor
    dsimp [F, A1, A2, A3, s, w] at *
    rw [h1]
    dsimp [QR_sum, D]
    ring
    
  have h_norm : ∀ (t : ℝ), ‖F t‖ ^ 2 ≤ 4 * ‖QR_sum t‖ ^ 2 + 4 * ‖D t‖ ^ 2 + 4 * ‖A2 t‖ ^ 2 + 4 * ‖A3 t‖ ^ 2 := by
    intro t
    have h2 := norm_add_four_sq_le (QR_sum t) (D t) (A2 t) (A3 t)
    rw [← hF t] at h2
    linarith

  have hV_card : (V.card : ℝ) ≤ 5 * (H * Real.log Q) := by
    exact card_Icc_log_le H P Q hH hP hPQ
    
  have h_QR_CS : ∀ (t : ℝ), ‖QR_sum t‖ ^ 2 ≤ (V.card : ℝ) * (∑ v ∈ V, ‖QR v t‖ ^ 2) := by
    intro t
    exact norm_sum_sq_le_card_mul_sum_sq V (fun v => QR v t)

  have h_QR_le : ∀ (t : ℝ), ‖QR_sum t‖ ^ 2 ≤ 5 * (H * Real.log Q) * (∑ v ∈ V, ‖QR v t‖ ^ 2) := by
    intro t
    have h1 := h_QR_CS t
    have h2 : 0 ≤ ∑ v ∈ V, ‖QR v t‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    nlinarith

  have hContF : Continuous (fun (t : ℝ) => ‖F t‖ ^ 2) :=
    continuous_norm_sq_dirichletPoly a _ (by intro n hn; exact_mod_cast (by linarith [hX, (Finset.mem_Ioc.mp hn).1] : 0 < n))
  have hContQR_sum : Continuous (fun (t : ℝ) => ‖QR_sum t‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro v _
    apply Continuous.mul
    · apply continuous_dirichletPoly_l12
      intro n hn
      exact_mod_cast (by linarith [((mem_shortPrimeRange P Q H v n).mp hn).1.1.two_le] : 0 < n)
    · apply continuous_dirichletPoly_l12
      intro n hn
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hContD : Continuous (fun (t : ℝ) => ‖D t‖ ^ 2) := by
    have hD_eq : (fun (t : ℝ) => ‖D t‖ ^ 2) = fun (t : ℝ) => ‖dirichletPoly (coeffDiff P Q X H b c) (Finset.Ioc 0 (6 * X)) (s t)‖ ^ 2 := by
      ext t
      congr 1
      dsimp [D, A1, QR_sum, QR]
      rw [A1_eq_dirichletPoly, QR_eq_dirichletPoly P Q X H hH]
      unfold coeffDiff dirichletPoly
      apply congr_arg
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hD_eq]
    apply continuous_norm_sq_dirichletPoly
    intro n hn
    exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hContA2 : Continuous (fun (t : ℝ) => ‖A2 t‖ ^ 2) := by
    have hA2_eq : (fun (t : ℝ) => ‖A2 t‖ ^ 2) = fun (t : ℝ) => ‖dirichletPoly (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) (s t)‖ ^ 2 := by
      ext t
      congr 1
      dsimp [A2]
      rw [squareCorrection_eq_sqCoeff X P Q a b c (w t)]
      unfold dirichletPoly
      rfl
    rw [hA2_eq]
    apply continuous_norm_sq_dirichletPoly
    intro n hn
    exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hContA3 : Continuous (fun (t : ℝ) => ‖A3 t‖ ^ 2) := by
    have hA3_eq : (fun (t : ℝ) => ‖A3 t‖ ^ 2) = fun (t : ℝ) => ‖dirichletPoly a (unsiftedSet X P Q) (s t)‖ ^ 2 := by
      ext t
      congr 1
      dsimp [A3]
      rw [filter_omegaIn_eq_unsiftedSet]
      rfl
    rw [hA3_eq]
    apply continuous_norm_sq_dirichletPoly
    intro n hn
    have h1 := (Finset.mem_filter.mp hn).1
    exact_mod_cast (by linarith [hX, (Finset.mem_Ioc.mp h1).1] : 0 < n)

  have hInt_F : IntegrableOn (fun (t : ℝ) => ‖F t‖ ^ 2) U := hContF.integrableOn_Icc.mono_set hUsub
  have hInt_QR_sum : IntegrableOn (fun (t : ℝ) => ‖QR_sum t‖ ^ 2) U := hContQR_sum.integrableOn_Icc.mono_set hUsub
  have hInt_D : IntegrableOn (fun (t : ℝ) => ‖D t‖ ^ 2) U := hContD.integrableOn_Icc.mono_set hUsub
  have hInt_A2 : IntegrableOn (fun (t : ℝ) => ‖A2 t‖ ^ 2) U := hContA2.integrableOn_Icc.mono_set hUsub
  have hInt_A3 : IntegrableOn (fun (t : ℝ) => ‖A3 t‖ ^ 2) U := hContA3.integrableOn_Icc.mono_set hUsub

  have hInt_bound : ∫ t in U, ‖F t‖ ^ 2 ≤
      4 * (∫ t in U, ‖QR_sum t‖ ^ 2) + 4 * (∫ t in U, ‖D t‖ ^ 2) + 4 * (∫ t in U, ‖A2 t‖ ^ 2) + 4 * (∫ t in U, ‖A3 t‖ ^ 2) := by
    have h1 : ∫ t in U, (4 * ‖QR_sum t‖ ^ 2 + 4 * ‖D t‖ ^ 2 + 4 * ‖A2 t‖ ^ 2 + 4 * ‖A3 t‖ ^ 2) =
        4 * (∫ t in U, ‖QR_sum t‖ ^ 2) + 4 * (∫ t in U, ‖D t‖ ^ 2) + 4 * (∫ t in U, ‖A2 t‖ ^ 2) + 4 * (∫ t in U, ‖A3 t‖ ^ 2) := by
      have hind1 : IntegrableOn (fun t => 4 * ‖QR_sum t‖ ^ 2 + 4 * ‖D t‖ ^ 2 + 4 * ‖A2 t‖ ^ 2) U := by
        apply Integrable.add
        · apply Integrable.add
          · exact hInt_QR_sum.const_mul 4
          · exact hInt_D.const_mul 4
        · exact hInt_A2.const_mul 4
      have hind2 : IntegrableOn (fun t => 4 * ‖QR_sum t‖ ^ 2 + 4 * ‖D t‖ ^ 2) U := by
        apply Integrable.add
        · exact hInt_QR_sum.const_mul 4
        · exact hInt_D.const_mul 4
      rw [MeasureTheory.integral_add hind1 (hInt_A3.const_mul 4)]
      rw [MeasureTheory.integral_add hind2 (hInt_A2.const_mul 4)]
      rw [MeasureTheory.integral_add (hInt_QR_sum.const_mul 4) (hInt_D.const_mul 4)]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact calc ∫ t in U, ‖F t‖ ^ 2
      _ ≤ ∫ t in U, (4 * ‖QR_sum t‖ ^ 2 + 4 * ‖D t‖ ^ 2 + 4 * ‖A2 t‖ ^ 2 + 4 * ‖A3 t‖ ^ 2) := setIntegral_mono_on hInt_F ((((hContQR_sum.const_mul 4).add (hContD.const_mul 4)).add (hContA2.const_mul 4)).add (hContA3.const_mul 4) |>.integrableOn_Icc.mono_set hUsub) hU (fun t _ => h_norm t)
      _ = 4 * (∫ t in U, ‖QR_sum t‖ ^ 2) + 4 * (∫ t in U, ‖D t‖ ^ 2) + 4 * (∫ t in U, ‖A2 t‖ ^ 2) + 4 * (∫ t in U, ‖A3 t‖ ^ 2) := h1

  have hInt_D_bound : ∫ t in U, ‖D t‖ ^ 2 ≤ C_D * (T / (X : ℝ) + 1) * (1 / H + 1 / (X : ℝ)) := by
    have hd_bound := hD X P Q H b c T U hX hP hPQ hQX hH hT hU hUsub hb hc
    have heq : (fun (t : ℝ) => ‖D t‖ ^ 2) = (fun (t : ℝ) => ‖(∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            (b m * c p) * ((p * m : ℕ) : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I)) / ((omegaIn (primeRange P Q) m : ℂ) + 1)) -
          ∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + (t : ℝ) * Complex.I) *
              dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
      rfl
    rw [heq]
    exact hd_bound

  have hInt_A2_bound : ∫ t in U, ‖A2 t‖ ^ 2 ≤ C_S * (T / X + 1) / P := by
    have hS_bound := hS X P Q a b c T U hX hP hPQ hQX hT hU hUsub ha hb hc hP4
    have heq : (fun (t : ℝ) => ‖A2 t‖ ^ 2) = (fun (t : ℝ) => ‖∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            squareCorrection (primeRange P Q) a b c (fun n => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) p m‖ ^ 2) := by
      rfl
    rw [heq]
    exact hS_bound

  have hInt_A3_bound : ∫ t in U, ‖A3 t‖ ^ 2 ≤ C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X) := by
    have heq : ∫ t in U, ‖A3 t‖ ^ 2 = ∫ t in U, ‖dirichletPoly a (unsiftedSet X P Q) ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
      apply setIntegral_congr_fun hU
      intro t _
      dsimp [A3, s, w]
      rw [filter_omegaIn_eq_unsiftedSet]
      rfl
    rw [heq]
    have h1 := setIntegral_norm_sq_dirichletPoly_le a (unsiftedSet X P Q) (by
      intro n hn
      unfold unsiftedSet at hn
      have hn_in := (Finset.mem_filter.mp hn).1
      exact_mod_cast (by linarith [hX, (Finset.mem_Ioc.mp hn_in).1] : 0 < n)) T hT U hU hUsub
    have h2 := integral_norm_sq_unsifted_le a ha X P Q hX T hT
    linarith

  have hInt_QR_le : ∫ t in U, ‖QR_sum t‖ ^ 2 ≤ 5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) := by
    exact calc ∫ t in U, ‖QR_sum t‖ ^ 2
      _ ≤ ∫ t in U, 5 * (H * Real.log Q) * (∑ v ∈ V, ‖QR v t‖ ^ 2) := setIntegral_mono_on hInt_QR_sum (by
          apply Integrable.const_mul
          apply integrable_finsetSum
          intro v _
          have hCont_v : Continuous (fun t => ‖QR v t‖ ^ 2) := by
            apply Continuous.pow
            apply Continuous.norm
            apply Continuous.mul
            · apply continuous_dirichletPoly_l12
              intro n hn
              exact_mod_cast (by linarith [((mem_shortPrimeRange P Q H v n).mp hn).1.1.two_le] : 0 < n)
            · apply continuous_dirichletPoly_l12
              intro n hn
              exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
          exact hCont_v.integrableOn_Icc.mono_set hUsub) hU (fun t _ => h_QR_le t)
      _ = 5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_finsetSum]
        intro v _
        have hCont_v : Continuous (fun t => ‖QR v t‖ ^ 2) := by
          apply Continuous.pow
          apply Continuous.norm
          apply Continuous.mul
          · apply continuous_dirichletPoly_l12
            intro n hn
            exact_mod_cast (by linarith [((mem_shortPrimeRange P Q H v n).mp hn).1.1.two_le] : 0 < n)
          · apply continuous_dirichletPoly_l12
            intro n hn
            exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
        exact hCont_v.integrableOn_Icc.mono_set hUsub
  -- Final combination
  exact calc ∫ t in U, ‖F t‖ ^ 2
    _ ≤ 4 * (∫ t in U, ‖QR_sum t‖ ^ 2) + 4 * (∫ t in U, ‖D t‖ ^ 2) + 4 * (∫ t in U, ‖A2 t‖ ^ 2) + 4 * (∫ t in U, ‖A3 t‖ ^ 2) := hInt_bound
    _ ≤ 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2)) +
        4 * (C_D * (T / (X : ℝ) + 1) * (1 / H + 1 / (X : ℝ))) +
        4 * (C_S * (T / X + 1) / P) +
        4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X)) := by
      have h1 : 4 * (∫ t in U, ‖QR_sum t‖ ^ 2) ≤ 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2)) := mul_le_mul_of_nonneg_left hInt_QR_le (by positivity)
      have h2 : 4 * (∫ t in U, ‖D t‖ ^ 2) ≤ 4 * (C_D * (T / (X : ℝ) + 1) * (1 / H + 1 / (X : ℝ))) := mul_le_mul_of_nonneg_left hInt_D_bound (by positivity)
      have h3 : 4 * (∫ t in U, ‖A2 t‖ ^ 2) ≤ 4 * (C_S * (T / X + 1) / P) := mul_le_mul_of_nonneg_left hInt_A2_bound (by positivity)
      have h4 : 4 * (∫ t in U, ‖A3 t‖ ^ 2) ≤ 4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X)) := mul_le_mul_of_nonneg_left hInt_A3_bound (by positivity)
      exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ ≤ C * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := by
      have hc20 : 20 ≤ C := le_max_left _ _
      have hT_X : 0 ≤ T / (X : ℝ) + 1 := by positivity
      
      have h_term1 : 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2)) ≤ C * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) := by
        have h_sum_nonneg : 0 ≤ ∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2 := by
          apply Finset.sum_nonneg
          intro v _
          exact setIntegral_nonneg hU (fun t _ => sq_nonneg _)
        have hH_logQ : 0 ≤ H * Real.log Q := mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by linarith)))
        have h1 : 20 * (H * Real.log Q) ≤ C * (H * Real.log Q) := mul_le_mul_of_nonneg_right hc20 hH_logQ
        have h2 : 20 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) ≤ C * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) := mul_le_mul_of_nonneg_right h1 h_sum_nonneg
        calc 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2))
          _ = 20 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) := by ring
          _ ≤ C * (H * Real.log Q) * ∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2 := h2
              
      have h_sum_X : 4 * (C_D * (T / X + 1) * (1 / H + 1 / X)) +
                     4 * (C_S * (T / X + 1) / P) +
                     4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X)) ≤
                     (4 * C_D + 4 * C_S + 4 * C_3) * (T / X + 1) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := by
        have h_X_P : 1 / (X : ℝ) ≤ 1 / (P : ℝ) := one_div_le_one_div_of_le (by exact_mod_cast (by linarith : 0 < P)) (by linarith [show (P:ℝ) ≤ Q by exact_mod_cast hPQ, hQX])
        have hd_pos : 0 ≤ 4 * C_D * (T / (X : ℝ) + 1) := by positivity
        have hs_pos : 0 ≤ 4 * C_S * (T / (X : ℝ) + 1) := by positivity
        have h3_pos : 0 ≤ 4 * C_3 * (T / (X : ℝ) + 1) := by positivity
        have h1 : 1 / H + 1 / (X : ℝ) ≤ 1 / H + 1 / (P : ℝ) + (((unsiftedSet X P Q).card : ℝ) / X) := by
          have hcard : 0 ≤ (((unsiftedSet X P Q).card : ℝ) / X) := by positivity
          linarith
        have h2 : 1 / (P : ℝ) ≤ 1 / H + 1 / (P : ℝ) + (((unsiftedSet X P Q).card : ℝ) / X) := by
          have hH_pos : 0 ≤ 1 / H := by positivity
          have hcard : 0 ≤ (((unsiftedSet X P Q).card : ℝ) / X) := by positivity
          linarith
        have h3 : (((unsiftedSet X P Q).card : ℝ) / X) ≤ 1 / H + 1 / (P : ℝ) + (((unsiftedSet X P Q).card : ℝ) / X) := by
          have hH_pos : 0 ≤ 1 / H := by positivity
          have hP_pos : 0 ≤ 1 / (P : ℝ) := by positivity
          linarith
        have hd_ineq : (4 * C_D * (T / X + 1)) * (1 / H + 1 / X) ≤ (4 * C_D * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) :=
          mul_le_mul_of_nonneg_left h1 hd_pos
        have hs_ineq : (4 * C_S * (T / X + 1)) * (1 / P) ≤ (4 * C_S * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) :=
          mul_le_mul_of_nonneg_left h2 hs_pos
        have h3_ineq : (4 * C_3 * (T / X + 1)) * (((unsiftedSet X P Q).card : ℝ) / X) ≤ (4 * C_3 * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) :=
          mul_le_mul_of_nonneg_left h3 h3_pos
        calc 4 * (C_D * (T / X + 1) * (1 / H + 1 / X)) +
             4 * (C_S * (T / X + 1) / P) +
             4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X))
          _ = (4 * C_D * (T / X + 1)) * (1 / H + 1 / X) +
              (4 * C_S * (T / X + 1)) * (1 / P) +
              (4 * C_3 * (T / X + 1)) * (((unsiftedSet X P Q).card : ℝ) / X) := by ring
          _ ≤ (4 * C_D * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) +
              (4 * C_S * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) +
              (4 * C_3 * (T / X + 1)) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := by
            exact add_le_add (add_le_add hd_ineq hs_ineq) h3_ineq
          _ = (4 * C_D + 4 * C_S + 4 * C_3) * (T / X + 1) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := by ring
          
      have h_C_bound : (4 * C_D + 4 * C_S + 4 * C_3) ≤ C := by linarith [le_max_right 20 (4 * (C_D + C_S + C_3))]
      
      calc 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2)) +
           4 * (C_D * (T / X + 1) * (1 / H + 1 / X)) +
           4 * (C_S * (T / X + 1) / P) +
           4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X))
        _ = 4 * (5 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2)) +
            (4 * (C_D * (T / X + 1) * (1 / H + 1 / X)) +
             4 * (C_S * (T / X + 1) / P) +
             4 * (C_3 * (T / X + 1) * (((unsiftedSet X P Q).card : ℝ) / X))) := by ring
        _ ≤ C * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) +
            (4 * C_D + 4 * C_S + 4 * C_3) * (T / X + 1) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := add_le_add h_term1 h_sum_X
        _ ≤ C * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖QR v t‖ ^ 2) +
            C * (T / X + 1) * (1 / H + 1 / P + (((unsiftedSet X P Q).card : ℝ) / X)) := by
          apply add_le_add
          · rfl
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_C_bound hT_X) (by positivity)

end Erdos1201.MR
