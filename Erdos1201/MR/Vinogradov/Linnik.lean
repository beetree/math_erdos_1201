import Mathlib

/-!
# Newton's Identities and Linnik's Lemma

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes:
1. `prod_X_sub_C_eq_of_powerSums_eq`: equal power sums of two $k$-tuples force equal polynomials
   $\prod_{i=1}^k (X - x_i) = \prod_{i=1}^k (X - y_i)$ over commutative rings where $1, \dots, k$ are units.
2. `exists_perm_of_powerSums_eq`: Corollary 17 of Tao (254A Notes 5): in $\mathbb{Z}/p^k\mathbb{Z}$ with $p > k$ prime,
   tuples with pairwise distinct reductions modulo $p$ and equal power sums are permutations of each other.
3. `card_linnik_le`: Lemma 18 (Linnik's lemma): bound on the number of integer tuples in $\{1, \dots, M\}^k$ with
   distinct reductions mod $p$ and prescribed power sums mod $p^j$.
-/

namespace Erdos1201.MR.Vinogradov

open Finset.HasAntidiagonal

lemma eval_psum {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.psum (Fin k) R n) = ∑ i : Fin k, x i ^ n := by
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.eval_X]

lemma eval_esymm {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R n) = ∑ t ∈ Finset.powersetCard n Finset.univ, ∏ i ∈ t, x i := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X]

lemma coeff_prod_X_sub_C {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) (j : ℕ) (hj : j ≤ k) :
    (∏ i : Fin k, (Polynomial.X - Polynomial.C (x i))).coeff j =
      (-1) ^ (k - j) * MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R (k - j)) := by
  have hs : (Finset.univ.val.map x).card = k := by simp
  rw [Finset.prod_eq_multiset_prod]
  change (Multiset.map (fun i => Polynomial.X - Polynomial.C (x i)) Finset.univ.val).prod.coeff j = _
  rw [show (fun i => Polynomial.X - Polynomial.C (x i)) = (fun t => Polynomial.X - Polynomial.C t) ∘ x by ext; rfl, ← Multiset.map_map]
  have hvieta := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map x) (k := j) (by rw [hs]; exact hj)
  rw [hs] at hvieta
  rw [hvieta]
  congr 1
  rw [Finset.esymm_map_val]
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X]

lemma natDegree_prod_X_sub_C_le {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) :
    (∏ i : Fin k, (Polynomial.X - Polynomial.C (x i))).natDegree ≤ k := by
  refine (Polynomial.natDegree_prod_le Finset.univ (fun i => Polynomial.X - Polynomial.C (x i))).trans ?_
  have : (∑ i : Fin k, (Polynomial.X - Polynomial.C (x i)).natDegree) ≤ ∑ i : Fin k, 1 :=
    Finset.sum_le_sum fun i _ => Polynomial.natDegree_X_sub_C_le (x i)
  refine this.trans ?_
  simp

lemma coeff_prod_X_sub_C_of_gt {R : Type*} [CommRing R] {k : ℕ} (x : Fin k → R) {j : ℕ} (hj : k < j) :
    (∏ i : Fin k, (Polynomial.X - Polynomial.C (x i))).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (natDegree_prod_X_sub_C_le x |>.trans_lt hj)

lemma eval_esymm_eq_of_powerSums_eq {R : Type*} [CommRing R] {k : ℕ}
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (j : R)) (x y : Fin k → R)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j)
    (m : ℕ) (hm : m ≤ k) :
    MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R m) = MvPolynomial.eval y (MvPolynomial.esymm (Fin k) R m) := by
  induction' m using Nat.strong_induction_on with m ih
  rcases m with _|m
  · simp only [MvPolynomial.esymm_zero, map_one]
  · have hm_pos : 1 ≤ m + 1 := Nat.succ_pos m
    have hu : IsUnit ((m + 1 : ℕ) : R) := hunit (m + 1) hm_pos hm
    have hnewton := MvPolynomial.mul_esymm_eq_sum (Fin k) R (m + 1)
    have hx_eval := congr_arg (MvPolynomial.eval x) hnewton
    have hy_eval := congr_arg (MvPolynomial.eval y) hnewton
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum] at hx_eval hy_eval
    have hsum_eq :
      (∑ a ∈ antidiagonal (m + 1) with a.1 < m + 1,
        (-1 : R) ^ a.1 * MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R a.1) * MvPolynomial.eval x (MvPolynomial.psum (Fin k) R a.2)) =
      (∑ a ∈ antidiagonal (m + 1) with a.1 < m + 1,
        (-1 : R) ^ a.1 * MvPolynomial.eval y (MvPolynomial.esymm (Fin k) R a.1) * MvPolynomial.eval y (MvPolynomial.psum (Fin k) R a.2)) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_filter, mem_antidiagonal] at ha
      have ha1_lt : a.1 < m + 1 := ha.2
      have ha1_le : a.1 ≤ k := by omega
      have ha2_pos : 1 ≤ a.2 := by omega
      have ha2_le : a.2 ≤ k := by omega
      have he : MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R a.1) = MvPolynomial.eval y (MvPolynomial.esymm (Fin k) R a.1) :=
        ih a.1 ha1_lt ha1_le
      have hp : MvPolynomial.eval x (MvPolynomial.psum (Fin k) R a.2) = MvPolynomial.eval y (MvPolynomial.psum (Fin k) R a.2) := by
        rw [eval_psum, eval_psum]
        exact h a.2 ha2_pos ha2_le
      rw [he, hp]
    have h_mul_eq :
      ((m + 1 : ℕ) : R) * MvPolynomial.eval x (MvPolynomial.esymm (Fin k) R (m + 1)) =
      ((m + 1 : ℕ) : R) * MvPolynomial.eval y (MvPolynomial.esymm (Fin k) R (m + 1)) := by
      rw [hx_eval, hy_eval, hsum_eq]
    exact hu.mul_left_cancel h_mul_eq

/-- Over a commutative ring R in which 1, 2, …, k are units, equal power sums p_1..p_k of two k-tuples force equal elementary symmetric polynomials e_1..e_k, hence equal polynomials ∏(X - x_i) = ∏(X - y_i). -/
theorem prod_X_sub_C_eq_of_powerSums_eq {R : Type*} [CommRing R] (k : ℕ)
    (hunit : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (j : R)) (x y : Fin k → R)
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∏ i, (Polynomial.X - Polynomial.C (x i)) = ∏ i, (Polynomial.X - Polynomial.C (y i)) := by
  ext j
  by_cases hj : j ≤ k
  · rw [coeff_prod_X_sub_C x j hj, coeff_prod_X_sub_C y j hj]
    have h_esymm := eval_esymm_eq_of_powerSums_eq hunit x y h (k - j) (by omega)
    rw [h_esymm]
  · have hj_gt : k < j := by omega
    rw [coeff_prod_X_sub_C_of_gt x hj_gt, coeff_prod_X_sub_C_of_gt y hj_gt]

lemma isUnit_natCast_of_lt_prime {p k j : ℕ} (hp : p.Prime) (hj_pos : 1 ≤ j) (hj_lt : j < p) :
    IsUnit (j : ZMod (p ^ k)) := by
  rcases k with _|k
  · rw [pow_zero]; exact isUnit_of_subsingleton _
  · rw [ZMod.isUnit_iff_coprime]
    have hcoprime : Nat.Coprime j p := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hj_pos hj_lt)).symm
    exact hcoprime.pow_right (k + 1)

lemma isUnit_iff_cast_ne_zero {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (a : ZMod (p ^ k)) :
    IsUnit a ↔ (ZMod.cast a : ZMod p) ≠ 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.one_lt_pow (by omega) (Nat.Prime.one_lt hp))⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hk]
  rw [Nat.coprime_comm]
  rw [hp.coprime_iff_not_dvd]
  rw [ZMod.cast_eq_val]
  rw [not_iff_not]
  exact (CharP.cast_eq_zero_iff (ZMod p) p a.val).symm

lemma eq_of_prod_sub_eq_zero {α R : Type*} [CommRing R] [DecidableEq α]
    (s : Finset α) (f : α → R) (c : R) (hprod : ∏ j ∈ s, (c - f j) = 0)
    (j0 : α) (hj0 : j0 ∈ s) (hunit : ∀ j ∈ s, j ≠ j0 → IsUnit (c - f j)) :
    c = f j0 := by
  have hsplit : ∏ j ∈ s, (c - f j) = (c - f j0) * ∏ j ∈ s.erase j0, (c - f j) :=
    (Finset.mul_prod_erase s (fun j => c - f j) hj0).symm
  rw [hsplit] at hprod
  have hu : IsUnit (∏ j ∈ s.erase j0, (c - f j)) := by
    apply Finset.prod_induction _ (fun u => IsUnit u)
    · intro a b ha hb; exact ha.mul hb
    · exact isUnit_one
    · intro j hj
      rw [Finset.mem_erase] at hj
      exact hunit j hj.2 hj.1
  obtain ⟨u, hu_eq⟩ := hu
  have : c - f j0 = 0 := by
    have h1 : (c - f j0) * ↑u = 0 := by rw [hu_eq]; exact hprod
    have h2 := congr_arg (· * (↑u⁻¹ : R)) h1
    simp only [mul_assoc, Units.mul_inv, mul_one, zero_mul] at h2
    exact h2
  exact sub_eq_zero.mp this

/-- Corollary 17: in ZMod (p^k) with p prime, p > k, tuples with pairwise distinct reductions mod p are determined up to permutation by their power sums. -/
theorem exists_perm_of_powerSums_eq (p k : ℕ) (hp : p.Prime) (hpk : k < p)
    (x y : Fin k → ZMod (p ^ k))
    (hx : ∀ i j, i ≠ j → (ZMod.cast (x i) : ZMod p) ≠ (ZMod.cast (x j) : ZMod p))
    (hy : ∀ i j, i ≠ j → (ZMod.cast (y i) : ZMod p) ≠ (ZMod.cast (y j) : ZMod p))
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∃ σ : Equiv.Perm (Fin k), ∀ i, x i = y (σ i) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · exact ⟨1, fun i => Fin.elim0 i⟩
  have hunit : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (j : ZMod (p ^ k)) := by
    intro j hj1 hjk
    exact isUnit_natCast_of_lt_prime hp hj1 (hjk.trans_lt hpk)
  have hpoly := prod_X_sub_C_eq_of_powerSums_eq k hunit x y h
  have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow (by omega) (Nat.Prime.one_lt hp)⟩
  have : Nontrivial (ZMod (p ^ k)) := ZMod.nontrivial (p ^ k)
  have h_root : ∀ i : Fin k, ∏ j : Fin k, (x i - y j) = 0 := by
    intro i
    have heval := congr_arg (Polynomial.eval (x i)) hpoly
    rw [Polynomial.eval_prod, Polynomial.eval_prod] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
    have hzero : ∏ j : Fin k, (x i - x j) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (x i))
    rw [hzero] at heval
    exact heval.symm
  have h_exists_j : ∀ i : Fin k, ∃ j : Fin k, x i = y j := by
    intro i
    have hprod := h_root i
    by_contra! hnone
    have h_all_unit : ∀ j : Fin k, IsUnit (x i - y j) := by
      intro j
      rw [isUnit_iff_cast_ne_zero hp hk]
      intro hcast
      have hcast_sub : (ZMod.cast (x i - y j) : ZMod p) = (ZMod.cast (x i) : ZMod p) - (ZMod.cast (y j) : ZMod p) := by
        exact map_sub (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) (x i) (y j)
      rw [hcast_sub, sub_eq_zero] at hcast
      have hunit_others : ∀ j' ∈ Finset.univ, j' ≠ j → IsUnit (x i - y j') := by
        intro j' _ hj'
        rw [isUnit_iff_cast_ne_zero hp hk]
        intro hcast'
        have hcast'_sub : (ZMod.cast (x i - y j') : ZMod p) = (ZMod.cast (x i) : ZMod p) - (ZMod.cast (y j') : ZMod p) := by
          exact map_sub (ZMod.castHom (dvd_pow_self p (by omega)) (ZMod p)) (x i) (y j')
        rw [hcast'_sub, sub_eq_zero] at hcast'
        have : (ZMod.cast (y j') : ZMod p) = (ZMod.cast (y j) : ZMod p) := by
          rw [← hcast', hcast]
        exact hy j' j hj' this
      have heq := eq_of_prod_sub_eq_zero Finset.univ y (x i) hprod j (Finset.mem_univ j) hunit_others
      exact hnone j heq
    have hprod_unit : IsUnit (∏ j : Fin k, (x i - y j)) := by
      apply Finset.prod_induction _ (fun u => IsUnit u)
      · intro a b ha hb; exact ha.mul hb
      · exact isUnit_one
      · intro j _
        exact h_all_unit j
    rw [hprod] at hprod_unit
    exact not_isUnit_zero hprod_unit
  choose f hf using h_exists_j
  have hf_inj : Function.Injective f := by
    intro i1 i2 hfeq
    by_contra hne
    have hx_ne := hx i1 i2 hne
    have : x i1 = x i2 := by rw [hf i1, hf i2, hfeq]
    apply hx_ne
    rw [this]
  have hf_bij : Function.Bijective f := (Finite.injective_iff_bijective).mp hf_inj
  exact ⟨Equiv.ofBijective f hf_bij, hf⟩

/-- Variant of Corollary 17 stated with `ZMod.castHom` under hypothesis `k ≠ 0`. -/
theorem exists_perm_of_powerSums_eq_hom (p k : ℕ) (hp : p.Prime) (hpk : k < p) (hk : k ≠ 0)
    (x y : Fin k → ZMod (p ^ k))
    (hx : ∀ i j, i ≠ j → (ZMod.castHom (dvd_pow_self p hk) (ZMod p)) (x i) ≠ (ZMod.castHom (dvd_pow_self p hk) (ZMod p)) (x j))
    (hy : ∀ i j, i ≠ j → (ZMod.castHom (dvd_pow_self p hk) (ZMod p)) (y i) ≠ (ZMod.castHom (dvd_pow_self p hk) (ZMod p)) (y j))
    (h : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∃ σ : Equiv.Perm (Fin k), ∀ i, x i = y (σ i) :=
  exists_perm_of_powerSums_eq p k hp hpk x y hx hy h

lemma card_icc_filter_zmod_le (N : ℕ) [NeZero N] (M : ℕ) (r : ZMod N) :
    (((Finset.Icc (1 : ℤ) (M : ℤ)).filter (fun (z : ℤ) => (z : ZMod N) = r)).card) ≤ M / N + 2 := by
  let S := (Finset.Icc (1 : ℤ) (M : ℤ)).filter (fun (z : ℤ) => (z : ZMod N) = r)
  let f : ℤ → ℕ := fun z => (z - 1).toNat / N
  have h_inj : ∀ z1 ∈ S, ∀ z2 ∈ S, f z1 = f z2 → z1 = z2 := by
    intro z1 hz1 z2 hz2 hf
    rw [Finset.mem_filter, Finset.mem_Icc] at hz1 hz2
    have hz1_pos : 0 ≤ z1 - 1 := by omega
    have hz2_pos : 0 ≤ z2 - 1 := by omega
    set n1 := (z1 - 1).toNat
    set n2 := (z2 - 1).toNat
    have hz1_eq : z1 = (n1 : ℤ) + 1 := by
      dsimp [n1]; rw [Int.toNat_of_nonneg hz1_pos]; ring
    have hz2_eq : z2 = (n2 : ℤ) + 1 := by
      dsimp [n2]; rw [Int.toNat_of_nonneg hz2_pos]; ring
    have hmod_eq : ((n1 + 1 : ℕ) : ZMod N) = ((n2 + 1 : ℕ) : ZMod N) := by
      have h1 : (z1 : ZMod N) = r := hz1.2
      have h2 : (z2 : ZMod N) = r := hz2.2
      rw [hz1_eq] at h1
      rw [hz2_eq] at h2
      have h1' : (((n1 : ℤ) + 1 : ℤ) : ZMod N) = ((n1 + 1 : ℕ) : ZMod N) := by push_cast; rfl
      have h2' : (((n2 : ℤ) + 1 : ℤ) : ZMod N) = ((n2 + 1 : ℕ) : ZMod N) := by push_cast; rfl
      rw [h1'] at h1
      rw [h2'] at h2
      rw [h1, h2]
    have hmodeq : n1 + 1 ≡ n2 + 1 [MOD N] := (ZMod.natCast_eq_natCast_iff' (n1 + 1) (n2 + 1) N).mp hmod_eq
    have hmodeq_n : n1 ≡ n2 [MOD N] := Nat.ModEq.add_right_cancel' 1 hmodeq
    have hmod_same : n1 % N = n2 % N := hmodeq_n
    have hdiv_same : n1 / N = n2 / N := hf
    have hn_eq : n1 = n2 := by
      rw [← Nat.div_add_mod n1 N, ← Nat.div_add_mod n2 N, hdiv_same, hmod_same]
    omega
  have h_range : ∀ z ∈ S, f z ∈ Finset.range (M / N + 1) := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_Icc] at hz
    rw [Finset.mem_range]
    apply Nat.lt_succ_of_le
    dsimp [f]
    apply Nat.div_le_div_right
    have : (z - 1).toNat ≤ M := by omega
    exact this
  have h_le := Finset.card_le_card_of_injOn f (fun z hz => h_range z hz) h_inj
  rw [Finset.card_range] at h_le
  exact h_le.trans (by omega)

lemma card_fiber_le (k : ℕ) (N : ℕ) [NeZero N] (M : ℕ) (w : Fin k → ZMod N) :
    ({x ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1 : ℤ) M) | (fun i => (x i : ZMod N)) = w}.card)
      ≤ (M / N + 2) ^ k := by
  have heq : {x ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1 : ℤ) M) | (fun i => (x i : ZMod N)) = w} =
      Fintype.piFinset (fun i : Fin k => (Finset.Icc (1 : ℤ) M).filter (fun (z : ℤ) => (z : ZMod N) = w i)) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
    aesop
  rw [heq, Fintype.card_piFinset]
  have : ∏ i : Fin k, ((Finset.Icc (1 : ℤ) M).filter (fun (z : ℤ) => (z : ZMod N) = w i)).card ≤ ∏ i : Fin k, (M / N + 2) := by
    apply Finset.prod_le_prod'
    intro i _
    exact card_icc_filter_zmod_le N M (w i)
  refine this.trans ?_
  simp

lemma card_perm_fiber_le (k : ℕ) {α : Type*} [DecidableEq α] (w0 : Fin k → α) (S : Finset (Fin k → α))
    (hS : ∀ w ∈ S, ∃ σ : Equiv.Perm (Fin k), ∀ i, w i = w0 (σ i)) :
    S.card ≤ k.factorial := by
  have : S ⊆ (Finset.univ : Finset (Equiv.Perm (Fin k))).image (fun σ => fun i => w0 (σ i)) := by
    intro w hw
    obtain ⟨σ, hσ⟩ := hS w hw
    have heq : w = fun i => w0 (σ i) := funext hσ
    rw [heq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ σ)
  refine (Finset.card_le_card this).trans ?_
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

lemma card_zmod_fiber_le (p k m : ℕ) (hp : p.Prime) (hm : m ≤ k) (c : ZMod (p ^ m)) :
    haveI : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
    haveI : NeZero (p ^ m) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
    ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun z => (ZMod.cast z : ZMod (p ^ m)) = c)).card ≤ p ^ (k - m) := by
  have : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
  have : NeZero (p ^ m) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
  let S := (Finset.univ : Finset (ZMod (p ^ k))).filter (fun z => (ZMod.cast z : ZMod (p ^ m)) = c)
  let f : ZMod (p ^ k) → ℕ := fun z => z.val / p ^ m
  have h_inj : ∀ z1 ∈ S, ∀ z2 ∈ S, f z1 = f z2 → z1 = z2 := by
    intro z1 hz1 z2 hz2 hf
    rw [Finset.mem_filter] at hz1 hz2
    have hz1_mod : z1.val % p ^ m = c.val := by
      have h1 : (z1.val : ZMod (p ^ m)) = c := by
        rw [← hz1.2, ZMod.cast_eq_val]
      rw [← h1, ZMod.val_natCast]
    have hz2_mod : z2.val % p ^ m = c.val := by
      have h2 : (z2.val : ZMod (p ^ m)) = c := by
        rw [← hz2.2, ZMod.cast_eq_val]
      rw [← h2, ZMod.val_natCast]
    have hval_eq : z1.val = z2.val := by
      rw [← Nat.div_add_mod z1.val (p ^ m), ← Nat.div_add_mod z2.val (p ^ m)]
      dsimp [f] at hf
      rw [hf, hz1_mod, hz2_mod]
    exact ZMod.val_injective (p ^ k) hval_eq
  have h_range : ∀ z ∈ S, f z ∈ Finset.range (p ^ (k - m)) := by
    intro z _
    rw [Finset.mem_range]
    dsimp [f]
    apply Nat.div_lt_of_lt_mul
    have : m + (k - m) = k := Nat.add_sub_of_le hm
    rw [← pow_add, this]
    exact ZMod.val_lt z
  have h_le := Finset.card_le_card_of_injOn f (fun z hz => h_range z hz) h_inj
  rw [Finset.card_range] at h_le
  exact h_le

lemma sum_range_rev (k : ℕ) :
    ∑ j : Fin k, (k - (j.val + 1)) = k * (k - 1) / 2 := by
  have h1 : ∑ j : Fin k, (k - (j.val + 1)) = ∑ i ∈ Finset.range k, (k - 1 - i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => by omega
  rw [h1, Finset.sum_range_reflect (fun i => i) k, Finset.sum_range_id k]

lemma cast_sum_pow (p k m : ℕ) (hm : m ≤ k) (x : Fin k → ℤ) :
    (ZMod.cast (∑ i : Fin k, ((x i : ZMod (p ^ k)) ^ m)) : ZMod (p ^ m)) =
      ((∑ i : Fin k, x i ^ m : ℤ) : ZMod (p ^ m)) := by
  have hdvd : p ^ m ∣ p ^ k := Nat.pow_dvd_pow p hm
  have h1 : (ZMod.cast (∑ i : Fin k, ((x i : ZMod (p ^ k)) ^ m)) : ZMod (p ^ m)) =
      (ZMod.castHom hdvd (ZMod (p ^ m))) (∑ i : Fin k, ((x i : ZMod (p ^ k)) ^ m)) := rfl
  rw [h1, map_sum]
  simp only [map_pow]
  have h2 : ∀ i : Fin k, (ZMod.castHom hdvd (ZMod (p ^ m))) (x i : ZMod (p ^ k)) = (x i : ZMod (p ^ m)) := by
    intro i
    change (ZMod.cast (x i : ZMod (p ^ k)) : ZMod (p ^ m)) = (x i : ZMod (p ^ m))
    exact ZMod.cast_intCast hdvd (x i)
  simp_rw [h2]
  push_cast
  rfl

/-- Lemma 18 (Linnik): for p prime with p > k, and any v : Fin k → ℤ, the number of x ∈ {1..M}^k with pairwise distinct reductions mod p and x₁^j + ⋯ + x_k^j ≡ v_j (mod p^j) for all 1 ≤ j ≤ k is at most k! · p^{k(k-1)/2} · (⌈M / p^k⌉ + 1)^k. -/
theorem card_linnik_le (p k M : ℕ) (hp : p.Prime) (hpk : k < p) (v : Fin k → ℤ) :
    (((Fintype.piFinset fun _ : Fin k => Finset.Icc (1 : ℤ) M)).filter (fun x =>
        (∀ i j, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
        ∀ j : Fin k, ((∑ i, x i ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))).card
      ≤ k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hle := Finset.card_filter_le (Fintype.piFinset fun _ : Fin 0 => Finset.Icc (1 : ℤ) M)
      (fun x =>
          (∀ i j, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
          ∀ j : Fin 0, ((∑ i, x i ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))
    have h1 : (Fintype.piFinset fun _ : Fin 0 => Finset.Icc (1 : ℤ) M).card = 1 := by simp
    rw [h1] at hle
    have h2 : (0 : ℕ).factorial * p ^ (0 * (0 - 1) / 2) * (M / p ^ 0 + 2) ^ 0 = 1 := rfl
    rw [h2]
    exact hle
  have : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.one_lt_pow (by omega) hp.one_lt)⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let S := (((Fintype.piFinset fun _ : Fin k => Finset.Icc (1 : ℤ) M)).filter (fun x =>
        (∀ i j, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
        ∀ j : Fin k, ((∑ i, x i ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1)))))
  let phi : (Fin k → ℤ) → (Fin k → ZMod (p ^ k)) := fun x i => (x i : ZMod (p ^ k))
  have hS_le : S.card ≤ (M / p ^ k + 2) ^ k * (Finset.image phi S).card := by
    apply Finset.card_le_mul_card_image
    intro w hw
    have : {a ∈ S | phi a = w} ⊆ {x ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1 : ℤ) M) | (fun i => (x i : ZMod (p ^ k))) = w} := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      have hxS := hx.1
      rw [Finset.mem_filter] at hxS
      exact ⟨hxS.1, hx.2⟩
    exact (Finset.card_le_card this).trans (card_fiber_le k (p ^ k) M w)
  let T := Finset.image phi S
  let psi : (Fin k → ZMod (p ^ k)) → (Fin k → ZMod (p ^ k)) := fun w j => ∑ i, (w i) ^ (j.val + 1)
  have hT_le : T.card ≤ k.factorial * (Finset.image psi T).card := by
    apply Finset.card_le_mul_card_image
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨w0, hw0_mem, rfl⟩ := hu
    rw [Finset.mem_image] at hw0_mem
    obtain ⟨x0, hx0S, rfl⟩ := hw0_mem
    let W := {w ∈ T | psi w = psi (phi x0)}
    have hW_perm : ∀ w ∈ W, ∃ σ : Equiv.Perm (Fin k), ∀ i, w i = (phi x0) (σ i) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hwT := hw.1
      rw [Finset.mem_image] at hwT
      obtain ⟨x, hxS, rfl⟩ := hwT
      rw [Finset.mem_filter] at hxS hx0S
      have hwx : ∀ i j, i ≠ j → (ZMod.cast ((phi x) i) : ZMod p) ≠ (ZMod.cast ((phi x) j) : ZMod p) := by
        intro i j hij
        have hdvd : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
        have h1 : (ZMod.cast ((phi x) i) : ZMod p) = (x i : ZMod p) := ZMod.cast_intCast hdvd (x i)
        have h2 : (ZMod.cast ((phi x) j) : ZMod p) = (x j : ZMod p) := ZMod.cast_intCast hdvd (x j)
        rw [h1, h2]
        exact hxS.2.1 i j hij
      have hwx0 : ∀ i j, i ≠ j → (ZMod.cast ((phi x0) i) : ZMod p) ≠ (ZMod.cast ((phi x0) j) : ZMod p) := by
        intro i j hij
        have hdvd : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
        have h1 : (ZMod.cast ((phi x0) i) : ZMod p) = (x0 i : ZMod p) := ZMod.cast_intCast hdvd (x0 i)
        have h2 : (ZMod.cast ((phi x0) j) : ZMod p) = (x0 j : ZMod p) := ZMod.cast_intCast hdvd (x0 j)
        rw [h1, h2]
        exact hx0S.2.1 i j hij
      have hsums : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, (phi x i) ^ j = ∑ i, (phi x0 i) ^ j := by
        intro j hj1 hjk
        have hj_lt : j - 1 < k := by omega
        let j' : Fin k := ⟨j - 1, hj_lt⟩
        have hj'_eq : j'.val + 1 = j := by
          change (j - 1) + 1 = j
          omega
        have hpsi_eq := congr_fun hw.2 j'
        dsimp [psi] at hpsi_eq
        rw [← hj'_eq]
        exact hpsi_eq
      exact exists_perm_of_powerSums_eq p k hp hpk (phi x) (phi x0) hwx hwx0 hsums
    exact card_perm_fiber_le k (phi x0) W hW_perm
  let U := Finset.image psi T
  have hU_sub : U ⊆ Fintype.piFinset (fun j : Fin k =>
      (Finset.univ : Finset (ZMod (p ^ k))).filter (fun z =>
        (ZMod.cast z : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))) := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨w, hwT, rfl⟩ := hu
    rw [Finset.mem_image] at hwT
    obtain ⟨x, hxS, rfl⟩ := hwT
    rw [Finset.mem_filter] at hxS
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [psi, phi]
    have hj_le : j.val + 1 ≤ k := by omega
    rw [cast_sum_pow p k (j.val + 1) hj_le x]
    exact hxS.2.2 j
  have hU_card : U.card ≤ p ^ (k * (k - 1) / 2) := by
    refine (Finset.card_le_card hU_sub).trans ?_
    rw [Fintype.card_piFinset]
    have h_prod_le : ∏ j : Fin k, ((Finset.univ : Finset (ZMod (p ^ k))).filter (fun z =>
        (ZMod.cast z : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))).card
        ≤ ∏ j : Fin k, p ^ (k - (j.val + 1)) := by
      apply Finset.prod_le_prod'
      intro j _
      have : NeZero (p ^ (j.val + 1)) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
      exact card_zmod_fiber_le p k (j.val + 1) hp (by omega) (v j : ZMod (p ^ (j.val + 1)))
    refine h_prod_le.trans ?_
    rw [Finset.prod_pow_eq_pow_sum, sum_range_rev]
  calc S.card ≤ (M / p ^ k + 2) ^ k * T.card := hS_le
    _ ≤ (M / p ^ k + 2) ^ k * (k.factorial * U.card) := Nat.mul_le_mul_left _ hT_le
    _ ≤ (M / p ^ k + 2) ^ k * (k.factorial * p ^ (k * (k - 1) / 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU_card)
    _ = k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k := by ring

end Erdos1201.MR.Vinogradov
