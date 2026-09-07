import Mathlib
import Erdos1201.MR.Vinogradov.FiniteFourier
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.PrimeSelection

/-!
# Hölder Restriction to a Common Residue Class (Tao's Lemma 19)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Tao's Lemma 19 (Notes 5, Section 2) for Vinogradov's mean value theorem:
bounding the prime-restricted diagonal count `Jp` by `Jtilde`, where the remaining `ℓ - k` variables
are further restricted to lie in a single residue class modulo `p`.
-/

noncomputable section

open Classical

namespace Erdos1201.MR.Vinogradov

open Finset

/-- Solutions counted by `Jp k ℓ M p hk` with the additional condition that
x_{k+1}, …, x_ℓ, y_{k+1}, …, y_ℓ are all congruent mod p. -/
def Jtilde (k ℓ M p : ℕ) (hk : k ≤ ℓ) : ℕ :=
  (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy =>
    curveSum k ℓ xy.1 = curveSum k ℓ xy.2 ∧
    (∀ i j : Fin k, i ≠ j → (xy.1 (Fin.castLE hk i) : ZMod p) ≠ (xy.1 (Fin.castLE hk j) : ZMod p)) ∧
    (∀ i j : Fin k, i ≠ j → (xy.2 (Fin.castLE hk i) : ZMod p) ≠ (xy.2 (Fin.castLE hk j) : ZMod p)) ∧
    ∃ u : ZMod p, (∀ i : Fin ℓ, k ≤ i.val → (xy.1 i : ZMod p) = u) ∧
                  (∀ i : Fin ℓ, k ≤ i.val → (xy.2 i : ZMod p) = u))).card

/-- Splitting equivalence `(Fin k → α) × (Fin m → α) ≃ (Fin ℓ → α)` when `k + m = ℓ`. -/
def splitEquiv {α : Type*} (k m ℓ : ℕ) (h : k + m = ℓ) :
    (Fin k → α) × (Fin m → α) ≃ (Fin ℓ → α) :=
  (Fin.appendEquiv k m).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl α))

/-- Evaluating `splitEquiv` at a first-block index `Fin.castAdd m i`. -/
theorem splitEquiv_apply_castAdd {α : Type*} (k m ℓ : ℕ) (h : k + m = ℓ)
    (u : Fin k → α) (v : Fin m → α) (i : Fin k) :
    splitEquiv k m ℓ h (u, v) (finCongr h (Fin.castAdd m i)) = u i := by
  change Fin.append u v (Fin.castAdd m i) = u i
  exact Fin.append_left u v i

/-- Evaluating `splitEquiv` at a second-block index `Fin.natAdd k j`. -/
theorem splitEquiv_apply_natAdd {α : Type*} (k m ℓ : ℕ) (h : k + m = ℓ)
    (u : Fin k → α) (v : Fin m → α) (j : Fin m) :
    splitEquiv k m ℓ h (u, v) (finCongr h (Fin.natAdd k j)) = v j := by
  change Fin.append u v (Fin.natAdd k j) = v j
  exact Fin.append_right u v j

/-- Identification of `Fin.castLE` with `finCongr` of `Fin.castAdd`. -/
theorem castLE_eq_finCongr_castAdd (k m ℓ : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ) (i : Fin k) :
    Fin.castLE hk i = finCongr h (Fin.castAdd m i) := by
  ext
  simp

/-- Evaluating `splitEquiv` at a first-block index via `Fin.castLE`. -/
theorem splitEquiv_castLE {α : Type*} (k m ℓ : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ)
    (u : Fin k → α) (v : Fin m → α) (i : Fin k) :
    splitEquiv k m ℓ h (u, v) (Fin.castLE hk i) = u i := by
  rw [castLE_eq_finCongr_castAdd k m ℓ h hk i]
  exact splitEquiv_apply_castAdd k m ℓ h u v i

/-- Membership in `tuples ℓ M` splits into membership on both component tuples. -/
theorem mem_tuples_splitEquiv (k m ℓ M : ℕ) (h : k + m = ℓ)
    (u : Fin k → ℤ) (v : Fin m → ℤ) :
    splitEquiv k m ℓ h (u, v) ∈ tuples ℓ M ↔ u ∈ tuples k M ∧ v ∈ tuples m M := by
  rw [mem_tuples_iff, mem_tuples_iff, mem_tuples_iff]
  constructor
  · intro hx
    constructor
    · intro i
      have h1 := hx (finCongr h (Fin.castAdd m i))
      rw [splitEquiv_apply_castAdd] at h1
      exact h1
    · intro j
      have h1 := hx (finCongr h (Fin.natAdd k j))
      rw [splitEquiv_apply_natAdd] at h1
      exact h1
  · rintro ⟨hu, hv⟩ i
    have h_eq : i = finCongr h ((finCongr h).symm i) := by simp
    rw [h_eq]
    generalize hj : (finCongr h).symm i = j
    induction j using Fin.addCases with
    | left a =>
      rw [splitEquiv_apply_castAdd]
      exact hu a
    | right b =>
      rw [splitEquiv_apply_natAdd]
      exact hv b

/-- The tail congruence condition translates to congruence of the second tuple. -/
theorem splitEquiv_congr_mod (k m ℓ p : ℕ) (h : k + m = ℓ)
    (u : Fin k → ℤ) (v : Fin m → ℤ) (u0 : ZMod p) :
    (∀ i : Fin ℓ, k ≤ i.val → ((splitEquiv k m ℓ h (u, v) i : ℤ) : ZMod p) = u0) ↔
      (∀ j : Fin m, (v j : ZMod p) = u0) := by
  constructor
  · intro hx j
    have hle : k ≤ (finCongr h (Fin.natAdd k j)).val := by
      have : (finCongr h (Fin.natAdd k j)).val = k + j.val := by simp
      omega
    have h1 := hx (finCongr h (Fin.natAdd k j)) hle
    rw [splitEquiv_apply_natAdd] at h1
    exact h1
  · intro hv i hi
    have h_eq : i = finCongr h ((finCongr h).symm i) := by simp
    generalize hj : (finCongr h).symm i = j
    induction j using Fin.addCases with
    | left a =>
      have ha_lt : (finCongr h (Fin.castAdd m a)).val < k := by
        simp [a.isLt]
      have hi_val : i.val < k := by
        conv_lhs => rw [h_eq, hj]
        exact ha_lt
      omega
    | right b =>
      have h_i : i = finCongr h (Fin.natAdd k b) := by rw [h_eq, hj]
      rw [h_i, splitEquiv_apply_natAdd]
      exact hv b

/-- Moment curve mod N. -/
def modCurve (k N : ℕ) (a : ℤ) : Fin k → ZMod N :=
  fun j => (momentCurve k a j : ZMod N)

/-- Curve sum mod N. -/
def F_mod (k ℓ N : ℕ) (x : Fin ℓ → ℤ) : Fin k → ZMod N :=
  ∑ i, modCurve k N (x i)

/-- Coordinate-wise evaluation of `F_mod`. -/
lemma F_mod_apply (k ℓ N : ℕ) (x : Fin ℓ → ℤ) (j : Fin k) :
    F_mod k ℓ N x j = (curveSum k ℓ x j : ZMod N) := by
  simp [F_mod, modCurve, curveSum, momentCurve, Finset.sum_apply]

/-- Curve sum mod N splits additively across `splitEquiv`. -/
theorem F_mod_splitEquiv (k m ℓ N : ℕ) (h : k + m = ℓ) (u : Fin k → ℤ) (v : Fin m → ℤ) :
    F_mod k ℓ N (splitEquiv k m ℓ h (u, v)) =
      (∑ i : Fin k, modCurve k N (u i)) + (∑ j : Fin m, modCurve k N (v j)) := by
  have h1 : ∑ i : Fin ℓ, modCurve k N (splitEquiv k m ℓ h (u, v) i) =
      ∑ j : Fin (k + m), modCurve k N (Fin.append u v j) := by
    rw [← (finCongr h).sum_comp]
    rfl
  rw [F_mod, h1, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Multiplicative factorization of additive characters under `splitEquiv`. -/
theorem addChar_F_mod_splitEquiv (k m ℓ N : ℕ) (h : k + m = ℓ)
    (u : Fin k → ℤ) (v : Fin m → ℤ) (ψ : AddChar (Fin k → ZMod N) ℂ) :
    ψ (F_mod k ℓ N (splitEquiv k m ℓ h (u, v))) =
      ψ (∑ i : Fin k, modCurve k N (u i)) * ψ (∑ j : Fin m, modCurve k N (v j)) := by
  rw [F_mod_splitEquiv, AddChar.map_add_eq_mul]

/-- Product factorization of character sums over a mapped product set. -/
theorem sum_addChar_F_mod_product (k m ℓ N : ℕ) (h : k + m = ℓ)
    (X : Finset (Fin k → ℤ)) (Y : Finset (Fin m → ℤ))
    (ψ : AddChar (Fin k → ZMod N) ℂ) :
    ∑ x ∈ (X ×ˢ Y).map (splitEquiv k m ℓ h).toEmbedding, ψ (F_mod k ℓ N x) =
      (∑ u ∈ X, ψ (∑ i, modCurve k N (u i))) * (∑ v ∈ Y, ψ (∑ j, modCurve k N (v j))) := by
  rw [sum_map]
  simp only [Equiv.coe_toEmbedding]
  rw [sum_product]
  simp_rw [addChar_F_mod_splitEquiv k m ℓ N h _ _ ψ]
  rw [← sum_mul_sum]

/-- Factorization of character sums over independent coordinates in `Fintype.piFinset`. -/
theorem sum_piFinset_modCurve {m k N : ℕ} (T : Finset ℤ)
    (γ : ℤ → Fin k → ZMod N) (ψ : AddChar (Fin k → ZMod N) ℂ) :
    ∑ v ∈ Fintype.piFinset (fun _ : Fin m => T), ψ (∑ j, γ (v j)) =
      (∑ w ∈ T, ψ (γ w)) ^ m := by
  rw [sum_piFinset_addChar_sum, Fintype.card_fin]

/-- Equality of integers bounded in `[0, N - 1]` from equality of their residues mod N. -/
lemma int_eq_of_zmod_eq {N : ℕ} (_hN : 0 < N) {A B : ℤ}
    (hA1 : 0 ≤ A) (hA2 : A ≤ N - 1)
    (hB1 : 0 ≤ B) (hB2 : B ≤ N - 1)
    (h : (A : ZMod N) = (B : ZMod N)) : A = B := by
  have hdvd : (N : ℤ) ∣ (A - B) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, h, sub_self]
  rcases hdvd with ⟨q, hq⟩
  have hdiff1 : A - B ≤ N - 1 := by linarith
  have hdiff2 : -(N - 1 : ℤ) ≤ A - B := by linarith
  rw [hq] at hdiff1 hdiff2
  have hq_zero : q = 0 := by
    by_contra hq_ne
    rcases lt_or_gt_of_ne hq_ne with hq_neg | hq_pos
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  subst hq_zero
  omega

/-- Curve sums of tuples are non-negative. -/
lemma curveSum_nonneg (k ℓ M : ℕ) (x : Fin ℓ → ℤ) (hx : x ∈ tuples ℓ M) (j : Fin k) :
    0 ≤ curveSum k ℓ x j := by
  rw [mem_tuples_iff] at hx
  rw [curveSum_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have : 0 ≤ x i := by linarith [(hx i).1]
  exact pow_nonneg this _

/-- Upper bound on curve sums of tuples. -/
lemma curveSum_le (k ℓ M : ℕ) (x : Fin ℓ → ℤ) (hx : x ∈ tuples ℓ M) (j : Fin k) :
    curveSum k ℓ x j ≤ (ℓ : ℤ) * (M : ℤ) ^ k := by
  rw [mem_tuples_iff] at hx
  rw [curveSum_apply]
  have h_le : ∀ i : Fin ℓ, (x i) ^ (j.val + 1) ≤ (M : ℤ) ^ k := by
    intro i
    have hx0 : 0 ≤ x i := by linarith [(hx i).1]
    have h1 : (x i) ^ (j.val + 1) ≤ (M : ℤ) ^ (j.val + 1) :=
      pow_le_pow_left₀ hx0 (hx i).2 _
    have h2 : (M : ℤ) ^ (j.val + 1) ≤ (M : ℤ) ^ k := by
      have hj : j.val + 1 ≤ k := j.isLt
      by_cases hM0 : M = 0
      · subst hM0
        have := (hx i).1
        have := (hx i).2
        omega
      · exact pow_le_pow_right₀ (by omega) hj
    exact le_trans h1 h2
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin ℓ)) (fun i => (x i) ^ (j.val + 1)) ((M : ℤ) ^ k) (fun i _ => h_le i)
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- Equality of curve sums is equivalent to equality of their images mod N. -/
theorem curveSum_eq_iff_F_mod_eq (k ℓ M : ℕ) (x y : Fin ℓ → ℤ)
    (hx : x ∈ tuples ℓ M) (hy : y ∈ tuples ℓ M) :
    curveSum k ℓ x = curveSum k ℓ y ↔
      F_mod k ℓ (2 * ℓ * M ^ k + 2) x = F_mod k ℓ (2 * ℓ * M ^ k + 2) y := by
  constructor
  · intro h
    ext j
    simp [F_mod_apply, h]
  · intro h
    ext j
    have h_mod : F_mod k ℓ (2 * ℓ * M ^ k + 2) x j = F_mod k ℓ (2 * ℓ * M ^ k + 2) y j := by rw [h]
    rw [F_mod_apply, F_mod_apply] at h_mod
    refine int_eq_of_zmod_eq (by omega) (curveSum_nonneg k ℓ M x hx j) ?_ (curveSum_nonneg k ℓ M y hy j) ?_ h_mod
    · have := curveSum_le k ℓ M x hx j
      have hT : 0 ≤ (ℓ : ℤ) * (M : ℤ) ^ k := by positivity
      have hcast : ((2 * ℓ * M ^ k + 2 : ℕ) : ℤ) - 1 = 2 * ((ℓ : ℤ) * (M : ℤ) ^ k) + 1 := by
        push_cast
        ring
      rw [hcast]
      linarith
    · have := curveSum_le k ℓ M y hy j
      have hT : 0 ≤ (ℓ : ℤ) * (M : ℤ) ^ k := by positivity
      have hcast : ((2 * ℓ * M ^ k + 2 : ℕ) : ℤ) - 1 = 2 * ((ℓ : ℤ) * (M : ℤ) ^ k) + 1 := by
        push_cast
        ring
      rw [hcast]
      linarith

/-- Tuples with pairwise distinct residues on the first k coordinates. -/
def D (k ℓ M p : ℕ) (hk : k ≤ ℓ) : Finset (Fin ℓ → ℤ) :=
  (tuples ℓ M).filter (fun x => ∀ i j : Fin k, i ≠ j → (x (Fin.castLE hk i) : ZMod p) ≠ (x (Fin.castLE hk j) : ZMod p))

/-- k-tuples with pairwise distinct residues mod p. -/
def Dk (k M p : ℕ) : Finset (Fin k → ℤ) :=
  (tuples k M).filter (fun x => ∀ i j : Fin k, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p))

/-- Tuples in `D` whose remaining `ℓ - k` coordinates are all congruent to `u0` mod p. -/
def Du (k ℓ M p : ℕ) (hk : k ≤ ℓ) (u0 : ZMod p) : Finset (Fin ℓ → ℤ) :=
  (D k ℓ M p hk).filter (fun x => ∀ i : Fin ℓ, k ≤ i.val → (x i : ZMod p) = u0)

/-- Integers in `{1, …, M}` congruent to `u0` mod p. -/
def Tu (M p : ℕ) (u0 : ZMod p) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) M).filter (fun v => (v : ZMod p) = u0)

/-- m-tuples with entries in `Tu M p u0`. -/
def tuplesU (m M p : ℕ) (u0 : ZMod p) : Finset (Fin m → ℤ) :=
  Fintype.piFinset fun _ => Tu M p u0

/-- Jtilde restricted to a single residue class `u0`. -/
def Jtilde_u (k ℓ M p : ℕ) (hk : k ≤ ℓ) (u0 : ZMod p) : ℕ :=
  ((Du k ℓ M p hk u0 ×ˢ Du k ℓ M p hk u0).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2)).card

/-- Membership in `D` under `splitEquiv`. -/
theorem mem_D_splitEquiv (k m ℓ M p : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ)
    (u : Fin k → ℤ) (v : Fin m → ℤ) :
    splitEquiv k m ℓ h (u, v) ∈ D k ℓ M p hk ↔ u ∈ Dk k M p ∧ v ∈ tuples m M := by
  simp only [D, Dk, mem_filter, mem_tuples_splitEquiv k m ℓ M h u v]
  simp_rw [splitEquiv_castLE k m ℓ h hk u v]
  tauto

/-- Membership in `Du` under `splitEquiv`. -/
theorem mem_Du_splitEquiv (k m ℓ M p : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ)
    (u : Fin k → ℤ) (v : Fin m → ℤ) (u0 : ZMod p) :
    splitEquiv k m ℓ h (u, v) ∈ Du k ℓ M p hk u0 ↔ u ∈ Dk k M p ∧ v ∈ tuplesU m M p u0 := by
  simp only [Du, mem_filter, mem_D_splitEquiv k m ℓ M p h hk u v]
  rw [splitEquiv_congr_mod k m ℓ p h u v u0]
  have h_tup : v ∈ tuples m M ∧ (∀ j : Fin m, (v j : ZMod p) = u0) ↔ v ∈ tuplesU m M p u0 := by
    simp only [tuples, tuplesU, Tu, Fintype.mem_piFinset, mem_Icc, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩ j
      exact ⟨h1 j, h2 j⟩
    · intro h
      exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  tauto

/-- `D` as the mapped image of `Dk × tuples`. -/
theorem D_eq_map (k m ℓ M p : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ) :
    D k ℓ M p hk = (Dk k M p ×ˢ tuples m M).map (splitEquiv k m ℓ h).toEmbedding := by
  ext x
  rw [mem_map_equiv]
  have h_eq : x = splitEquiv k m ℓ h ((splitEquiv k m ℓ h).symm x) := by
    rw [Equiv.apply_symm_apply]
  conv_lhs => rw [h_eq]
  rcases (splitEquiv k m ℓ h).symm x with ⟨u, v⟩
  rw [mem_D_splitEquiv k m ℓ M p h hk]
  rw [mem_product]

/-- `Du` as the mapped image of `Dk × tuplesU`. -/
theorem Du_eq_map (k m ℓ M p : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ) (u0 : ZMod p) :
    Du k ℓ M p hk u0 = (Dk k M p ×ˢ tuplesU m M p u0).map (splitEquiv k m ℓ h).toEmbedding := by
  ext x
  rw [mem_map_equiv]
  have h_eq : x = splitEquiv k m ℓ h ((splitEquiv k m ℓ h).symm x) := by
    rw [Equiv.apply_symm_apply]
  conv_lhs => rw [h_eq]
  rcases (splitEquiv k m ℓ h).symm x with ⟨u, v⟩
  rw [mem_Du_splitEquiv k m ℓ M p h hk]
  rw [mem_product]

/-- Partition of `Jtilde` into the sum of `Jtilde_u` over disjoint residue classes. -/
theorem Jtilde_eq_sum (k ℓ M p : ℕ) (hk : k ≤ ℓ) (hkl : k < ℓ) (hp : 0 < p) :
    have : NeZero p := ⟨ne_of_gt hp⟩
    Jtilde k ℓ M p hk = ∑ u0 : ZMod p, Jtilde_u k ℓ M p hk u0 := by
  have : NeZero p := ⟨ne_of_gt hp⟩
  have hi0 : ∃ i : Fin ℓ, k ≤ i.val := ⟨⟨k, hkl⟩, le_rfl⟩
  obtain ⟨i0, hi0_le⟩ := hi0
  have h_card : Jtilde k ℓ M p hk =
      ((univ : Finset (ZMod p)).biUnion
        (fun u0 => (Du k ℓ M p hk u0 ×ˢ Du k ℓ M p hk u0).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2))).card := by
    unfold Jtilde
    apply congr_arg Finset.card
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_biUnion, mem_univ, true_and, D, Du]
    constructor
    · rintro ⟨⟨hx, hy⟩, hcurve, hdist_x, hdist_y, u, hu_x, hu_y⟩
      refine ⟨u, ?_⟩
      refine ⟨⟨⟨⟨hx, hdist_x⟩, hu_x⟩, ⟨hy, hdist_y⟩, hu_y⟩, hcurve⟩
    · rintro ⟨u, ⟨⟨⟨hx, hdist_x⟩, hu_x⟩, ⟨hy, hdist_y⟩, hu_y⟩, hcurve⟩
      refine ⟨⟨hx, hy⟩, hcurve, hdist_x, hdist_y, u, hu_x, hu_y⟩
  rw [h_card, card_biUnion]
  · rfl
  · intro u1 _ u2 _ hne
    simp only [Function.onFun, Finset.disjoint_left, mem_filter, mem_product, Du]
    rintro ⟨x, y⟩ ⟨⟨⟨-, hu1_x⟩, -⟩, -⟩ ⟨⟨⟨-, hu2_x⟩, -⟩, -⟩
    have hu1 := hu1_x i0 hi0_le
    have hu2 := hu2_x i0 hi0_le
    rw [← hu1, ← hu2] at hne
    exact hne rfl

/-- Character sum counting formula for `F_mod`. -/
lemma card_filter_F_mod_mul_card_eq (k ℓ N : ℕ) [NeZero N] (S : Finset (Fin ℓ → ℤ)) :
    let G := Fin k → ZMod N
    (((S ×ˢ S).filter (fun xy => F_mod k ℓ N xy.1 = F_mod k ℓ N xy.2)).card : ℝ) * (Fintype.card G : ℝ) =
      ∑ ψ : AddChar G ℂ, ‖∑ x ∈ S, ψ (F_mod k ℓ N x)‖ ^ 2 := by
  intro G
  have h := card_filter_eq_mul_card_eq_sum (G := G) S S (F_mod k ℓ N) (F_mod k ℓ N)
  have h_normSq : ∀ ψ : AddChar G ℂ,
      (∑ x ∈ S, ψ (F_mod k ℓ N x)) * (starRingEnd ℂ) (∑ y ∈ S, ψ (F_mod k ℓ N y)) =
        ((‖∑ x ∈ S, ψ (F_mod k ℓ N x)‖ ^ 2 : ℝ) : ℂ) := by
    intro ψ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h_normSq] at h
  rw [← Complex.ofReal_sum] at h
  have h_lhs : (((S ×ˢ S).filter (fun xy => F_mod k ℓ N xy.1 = F_mod k ℓ N xy.2)).card : ℂ) * (Fintype.card G : ℂ) =
      (((((S ×ˢ S).filter (fun xy => F_mod k ℓ N xy.1 = F_mod k ℓ N xy.2)).card : ℝ) * (Fintype.card G : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_lhs] at h
  exact Complex.ofReal_injective h

/-- The counting set on `D` equals `Jp`. -/
lemma card_filter_D_eq_Jp (k ℓ M p : ℕ) (hk : k ≤ ℓ) :
    let N := 2 * ℓ * M ^ k + 2
    ((D k ℓ M p hk ×ˢ D k ℓ M p hk).filter (fun xy => F_mod k ℓ N xy.1 = F_mod k ℓ N xy.2)).card =
      Jp k ℓ M p hk := by
  intro N
  dsimp [Jp]
  apply congr_arg Finset.card
  ext ⟨x, y⟩
  simp only [mem_filter, mem_product, D]
  constructor
  · rintro ⟨⟨⟨hx, hx_dist⟩, ⟨hy, hy_dist⟩⟩, hF⟩
    have hcurve := (curveSum_eq_iff_F_mod_eq k ℓ M x y hx hy).mpr hF
    exact ⟨⟨hx, hy⟩, hcurve, hx_dist, hy_dist⟩
  · rintro ⟨⟨hx, hy⟩, hcurve, hx_dist, hy_dist⟩
    have hF := (curveSum_eq_iff_F_mod_eq k ℓ M x y hx hy).mp hcurve
    exact ⟨⟨⟨hx, hx_dist⟩, ⟨hy, hy_dist⟩⟩, hF⟩

/-- The counting set on `Du` equals `Jtilde_u`. -/
lemma card_filter_Du_eq_Jtilde_u (k ℓ M p : ℕ) (hk : k ≤ ℓ) (u0 : ZMod p) :
    let N := 2 * ℓ * M ^ k + 2
    ((Du k ℓ M p hk u0 ×ˢ Du k ℓ M p hk u0).filter (fun xy => F_mod k ℓ N xy.1 = F_mod k ℓ N xy.2)).card =
      Jtilde_u k ℓ M p hk u0 := by
  intro N
  dsimp [Jtilde_u]
  apply congr_arg Finset.card
  ext ⟨x, y⟩
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨hx_Du, hy_Du⟩, hF⟩
    have hx : x ∈ tuples ℓ M := (mem_filter.mp (mem_filter.mp hx_Du).1).1
    have hy : y ∈ tuples ℓ M := (mem_filter.mp (mem_filter.mp hy_Du).1).1
    have hcurve := (curveSum_eq_iff_F_mod_eq k ℓ M x y hx hy).mpr hF
    exact ⟨⟨hx_Du, hy_Du⟩, hcurve⟩
  · rintro ⟨⟨hx_Du, hy_Du⟩, hcurve⟩
    have hx : x ∈ tuples ℓ M := (mem_filter.mp (mem_filter.mp hx_Du).1).1
    have hy : y ∈ tuples ℓ M := (mem_filter.mp (mem_filter.mp hy_Du).1).1
    have hF := (curveSum_eq_iff_F_mod_eq k ℓ M x y hx hy).mp hcurve
    exact ⟨⟨hx_Du, hy_Du⟩, hF⟩

/-- Fiberwise partition of `{1, …, M}` into fibers modulo p. -/
lemma sum_Tu_fiberwise {M p : ℕ} (hp : 0 < p) (f : ℤ → ℂ) :
    have : NeZero p := ⟨ne_of_gt hp⟩
    ∑ u0 : ZMod p, ∑ w ∈ Tu M p u0, f w = ∑ w ∈ Finset.Icc (1 : ℤ) M, f w := by
  have : NeZero p := ⟨ne_of_gt hp⟩
  dsimp [Tu]
  have h_maps : Set.MapsTo (fun v : ℤ => (v : ZMod p)) ↑(Finset.Icc (1 : ℤ) M) ↑(univ : Finset (ZMod p)) :=
    fun _ _ => mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to h_maps]

/-- Power-mean inequality for character sums over `Icc 1 M` partitioned into mod-p fibers. -/
lemma norm_S_pow_le (M p m : ℕ) (hm : 1 ≤ m) (hp : 0 < p) (f : ℤ → ℂ) :
    have : NeZero p := ⟨ne_of_gt hp⟩
    ‖∑ w ∈ Finset.Icc (1 : ℤ) M, f w‖ ^ (2 * m) ≤
      (p : ℝ) ^ (2 * m - 1) * ∑ u0 : ZMod p, ‖∑ w ∈ Tu M p u0, f w‖ ^ (2 * m) := by
  have : NeZero p := ⟨ne_of_gt hp⟩
  rw [← sum_Tu_fiberwise hp f]
  have h_pow := norm_sum_pow_le (univ : Finset (ZMod p)) (fun u0 => ∑ w ∈ Tu M p u0, f w) (2 * m - 1)
  have h_card : (univ : Finset (ZMod p)).card = p := by
    rw [card_univ, ZMod.card p]
  have h_exp : 2 * m - 1 + 1 = 2 * m := by omega
  rw [h_card, h_exp] at h_pow
  exact h_pow

/-- Factorization of the character sum over `D`. -/
lemma sum_addChar_D (k m ℓ M p N : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ) (ψ : AddChar (Fin k → ZMod N) ℂ) :
    ∑ x ∈ D k ℓ M p hk, ψ (F_mod k ℓ N x) =
      (∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))) * (∑ w ∈ Finset.Icc (1 : ℤ) M, ψ (modCurve k N w)) ^ m := by
  rw [D_eq_map k m ℓ M p h hk]
  rw [sum_addChar_F_mod_product k m ℓ N h (Dk k M p) (tuples m M) ψ]
  rw [tuples, sum_piFinset_modCurve _ _ ψ]

/-- Factorization of the character sum over `Du`. -/
lemma sum_addChar_Du (k m ℓ M p N : ℕ) (h : k + m = ℓ) (hk : k ≤ ℓ) (u0 : ZMod p) (ψ : AddChar (Fin k → ZMod N) ℂ) :
    ∑ x ∈ Du k ℓ M p hk u0, ψ (F_mod k ℓ N x) =
      (∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))) * (∑ w ∈ Tu M p u0, ψ (modCurve k N w)) ^ m := by
  rw [Du_eq_map k m ℓ M p h hk u0]
  rw [sum_addChar_F_mod_product k m ℓ N h (Dk k M p) (tuplesU m M p u0) ψ]
  rw [tuplesU, sum_piFinset_modCurve _ _ ψ]

/-- Tao's Lemma 19 for `k < ℓ`: restriction of `Jp` to `Jtilde`. -/
theorem Jp_le_Jtilde_of_lt (k ℓ M p : ℕ) (hk : k ≤ ℓ) (hkl : k < ℓ) (hp : 0 < p) :
    (Jp k ℓ M p hk : ℝ) ≤ (p : ℝ) ^ (2 * (ℓ - k) - 1) * Jtilde k ℓ M p hk := by
  set m := ℓ - k
  have hm : 1 ≤ m := by omega
  have h : k + m = ℓ := by omega
  set N := 2 * ℓ * M ^ k + 2
  have : NeZero N := ⟨by omega⟩
  have : NeZero p := ⟨ne_of_gt hp⟩
  let G := Fin k → ZMod N
  have h_norm_D : ∀ ψ : AddChar G ℂ, ‖∑ x ∈ D k ℓ M p hk, ψ (F_mod k ℓ N x)‖ ^ 2 =
      ‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 * ‖∑ w ∈ Finset.Icc (1 : ℤ) M, ψ (modCurve k N w)‖ ^ (2 * m) := by
    intro ψ
    rw [sum_addChar_D k m ℓ M p N h hk ψ, norm_mul, norm_pow, mul_pow, ← pow_mul]
    ring
  have h_norm_Du : ∀ (ψ : AddChar G ℂ) (u0 : ZMod p), ‖∑ x ∈ Du k ℓ M p hk u0, ψ (F_mod k ℓ N x)‖ ^ 2 =
      ‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 * ‖∑ w ∈ Tu M p u0, ψ (modCurve k N w)‖ ^ (2 * m) := by
    intro ψ u0
    rw [sum_addChar_Du k m ℓ M p N h hk u0 ψ, norm_mul, norm_pow, mul_pow, ← pow_mul]
    ring
  have h_le_psi : ∀ ψ : AddChar G ℂ, ‖∑ x ∈ D k ℓ M p hk, ψ (F_mod k ℓ N x)‖ ^ 2 ≤
      (p : ℝ) ^ (2 * m - 1) * ∑ u0 : ZMod p, ‖∑ x ∈ Du k ℓ M p hk u0, ψ (F_mod k ℓ N x)‖ ^ 2 := by
    intro ψ
    rw [h_norm_D ψ]
    simp_rw [h_norm_Du ψ]
    have hS := norm_S_pow_le M p m hm hp (fun w => ψ (modCurve k N w))
    have hA_nonneg : 0 ≤ ‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 := by positivity
    have h_mul := mul_le_mul_of_nonneg_left hS hA_nonneg
    calc
      ‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 * ‖∑ w ∈ Finset.Icc (1 : ℤ) M, ψ (modCurve k N w)‖ ^ (2 * m)
        ≤ ‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 * ((p : ℝ) ^ (2 * m - 1) * ∑ u0 : ZMod p, ‖∑ w ∈ Tu M p u0, ψ (modCurve k N w)‖ ^ (2 * m)) := h_mul
      _ = (p : ℝ) ^ (2 * m - 1) * ∑ u0 : ZMod p, (‖∑ u ∈ Dk k M p, ψ (∑ i, modCurve k N (u i))‖ ^ 2 * ‖∑ w ∈ Tu M p u0, ψ (modCurve k N w)‖ ^ (2 * m)) := by
        rw [mul_left_comm, mul_sum]
  have h_sum_le : ∑ ψ : AddChar G ℂ, ‖∑ x ∈ D k ℓ M p hk, ψ (F_mod k ℓ N x)‖ ^ 2 ≤
      (p : ℝ) ^ (2 * m - 1) * ∑ u0 : ZMod p, ∑ ψ : AddChar G ℂ, ‖∑ x ∈ Du k ℓ M p hk u0, ψ (F_mod k ℓ N x)‖ ^ 2 := by
    refine le_trans (sum_le_sum (fun (ψ : AddChar G ℂ) _ => h_le_psi ψ)) ?_
    rw [← mul_sum, sum_comm]
  have h_LHS : ∑ ψ : AddChar G ℂ, ‖∑ x ∈ D k ℓ M p hk, ψ (F_mod k ℓ N x)‖ ^ 2 =
      (Jp k ℓ M p hk : ℝ) * (Fintype.card G : ℝ) := by
    rw [← card_filter_F_mod_mul_card_eq k ℓ N (D k ℓ M p hk), card_filter_D_eq_Jp]
  have h_RHS : ∀ u0 : ZMod p, ∑ ψ : AddChar G ℂ, ‖∑ x ∈ Du k ℓ M p hk u0, ψ (F_mod k ℓ N x)‖ ^ 2 =
      (Jtilde_u k ℓ M p hk u0 : ℝ) * (Fintype.card G : ℝ) := by
    intro u0
    rw [← card_filter_F_mod_mul_card_eq k ℓ N (Du k ℓ M p hk u0), card_filter_Du_eq_Jtilde_u]
  rw [h_LHS] at h_sum_le
  simp_rw [h_RHS] at h_sum_le
  rw [← sum_mul, ← Nat.cast_sum, ← Jtilde_eq_sum k ℓ M p hk hkl hp] at h_sum_le
  have hG_pos : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos
  have h_final : (Jp k ℓ M p hk : ℝ) * (Fintype.card G : ℝ) ≤
      ((p : ℝ) ^ (2 * m - 1) * (Jtilde k ℓ M p hk : ℝ)) * (Fintype.card G : ℝ) := by
    calc
      (Jp k ℓ M p hk : ℝ) * (Fintype.card G : ℝ)
        ≤ (p : ℝ) ^ (2 * m - 1) * ((Jtilde k ℓ M p hk : ℝ) * (Fintype.card G : ℝ)) := h_sum_le
      _ = ((p : ℝ) ^ (2 * m - 1) * (Jtilde k ℓ M p hk : ℝ)) * (Fintype.card G : ℝ) := by ring
  exact le_of_mul_le_mul_right h_final hG_pos

/-- When `k = ℓ`, `Jtilde` equals `Jp` because the tail condition is vacuously satisfied. -/
theorem Jtilde_eq_Jp_of_eq (k ℓ M p : ℕ) (hk : k ≤ ℓ) (hkl : k = ℓ) (hp : 0 < p) :
    have : NeZero p := ⟨ne_of_gt hp⟩
    Jtilde k ℓ M p hk = Jp k ℓ M p hk := by
  have : NeZero p := ⟨ne_of_gt hp⟩
  dsimp [Jtilde, Jp]
  apply congr_arg Finset.card
  ext ⟨x, y⟩
  simp only [mem_filter, mem_product]
  have hvac : (∃ u : ZMod p, (∀ i : Fin ℓ, k ≤ i.val → (x i : ZMod p) = u) ∧ (∀ i : Fin ℓ, k ≤ i.val → (y i : ZMod p) = u)) ↔ True := by
    simp only [iff_true]
    refine ⟨0, ?_⟩
    constructor <;> { intro i hi; have : i.val < ℓ := i.isLt; omega }
  rw [hvac]
  tauto

/-- Tao's Lemma 19: `Jp ≤ p ^ (2(ℓ - k) - 1) * Jtilde`. -/
theorem Jp_le_Jtilde (k ℓ M p : ℕ) (hk : k ≤ ℓ) (hp : 0 < p) :
    (Jp k ℓ M p hk : ℝ) ≤ (p : ℝ) ^ (2 * (ℓ - k) - 1) * Jtilde k ℓ M p hk := by
  rcases eq_or_lt_of_le hk with rfl | hkl
  · have : NeZero p := ⟨ne_of_gt hp⟩
    have heq := Jtilde_eq_Jp_of_eq k k M p le_rfl rfl hp
    have hexp : 2 * (k - k) - 1 = 0 := by omega
    rw [hexp, pow_zero, one_mul, heq]
  · exact Jp_le_Jtilde_of_lt k ℓ M p hk hkl hp

/-- Variant of Tao's Lemma 19 taking `hk : k < ℓ`. -/
theorem Jp_le_Jtilde_of_lt' (k ℓ M p : ℕ) (hk : k < ℓ) (hp : 0 < p) :
    (Jp k ℓ M p hk.le : ℝ) ≤ (p : ℝ) ^ (2 * (ℓ - k) - 1) * Jtilde k ℓ M p hk.le :=
  Jp_le_Jtilde k ℓ M p hk.le hp

end Erdos1201.MR.Vinogradov
