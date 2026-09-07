/-
The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.PrimeSums
import Erdos1201.SmoothBound
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.PrimeSelection
import Erdos1201.MR.Vinogradov.HolderRestriction
import Erdos1201.MR.Vinogradov.Linnik

noncomputable section

namespace Erdos1201.MR.Vinogradov

open Finset

def linnikSet (k M p : ℕ) (u : ℤ) (w : Fin k → ℤ) : Finset (Fin k → ℤ) :=
  (tuples k M).filter fun x =>
    (∀ i j : Fin k, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
    ∀ j : Fin k, ((∑ i, (x i - u) ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = (w j : ZMod (p ^ (j.val + 1)))

def diffVector (k : ℕ) (x1 y1 : Fin k → ℤ) (p : ℕ) (u : ℤ) : Fin k → ℤ := fun j =>
  ∑ r ∈ Finset.Icc 1 (j.val + 1),
    ((j.val + 1).choose r : ℤ) * ((∑ i : Fin k, (y1 i - u) ^ r - ∑ i : Fin k, (x1 i - u) ^ r) / (p : ℤ) ^ r)

lemma card_linnikSet_le (p k M : ℕ) (hp : p.Prime) (hpk : k < p) (u : ℤ) (v : Fin k → ℤ) :
    (linnikSet k M p u v).card ≤ k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · have hle := Finset.card_filter_le (tuples 0 M)
      (fun x =>
          (∀ i j : Fin 0, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
          ∀ j : Fin 0, ((∑ i, (x i - u) ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))
    have h1 : (tuples 0 M).card = 1 := by simp [tuples]
    rw [h1] at hle
    have h2 : (0 : ℕ).factorial * p ^ (0 * (0 - 1) / 2) * (M / p ^ 0 + 2) ^ 0 = 1 := rfl
    rw [h2]
    exact hle
  have : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.one_lt_pow (by omega) hp.one_lt)⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let S := linnikSet k M p u v
  let phi : (Fin k → ℤ) → (Fin k → ZMod (p ^ k)) := fun x i => (x i : ZMod (p ^ k))
  have hS_le : S.card ≤ (M / p ^ k + 2) ^ k * (Finset.image phi S).card := by
    apply Finset.card_le_mul_card_image
    intro w hw
    have : {a ∈ S | phi a = w} ⊆ {x ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc (1 : ℤ) M) | (fun i => (x i : ZMod (p ^ k))) = w} := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      have hxS := hx.1
      dsimp [S, linnikSet] at hxS
      rw [Finset.mem_filter] at hxS
      exact ⟨hxS.1, hx.2⟩
    exact (Finset.card_le_card this).trans (card_fiber_le k (p ^ k) M w)
  let T := Finset.image phi S
  let psi : (Fin k → ZMod (p ^ k)) → (Fin k → ZMod (p ^ k)) := fun w j => ∑ i, (w i - (u : ZMod (p ^ k))) ^ (j.val + 1)
  have hT_le : T.card ≤ k.factorial * (Finset.image psi T).card := by
    apply Finset.card_le_mul_card_image
    intro u' hu'
    rw [Finset.mem_image] at hu'
    obtain ⟨w0, hw0_mem, rfl⟩ := hu'
    rw [Finset.mem_image] at hw0_mem
    obtain ⟨x0, hx0S, rfl⟩ := hw0_mem
    let W := {w ∈ T | psi w = psi (phi x0)}
    have hW_perm : ∀ w ∈ W, ∃ σ : Equiv.Perm (Fin k), ∀ i, w i = (phi x0) (σ i) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      have hwT := hw.1
      rw [Finset.mem_image] at hwT
      obtain ⟨x, hxS, rfl⟩ := hwT
      dsimp [S, linnikSet] at hxS hx0S
      rw [Finset.mem_filter] at hxS hx0S
      have hdvd : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
      have hcast_diff : ∀ z : ℤ, (ZMod.cast ((z : ZMod (p ^ k)) - (u : ZMod (p ^ k))) : ZMod p) = (z : ZMod p) - (u : ZMod p) := by
        intro z
        have h1 : ((z : ZMod (p ^ k)) - (u : ZMod (p ^ k))) = ((z - u : ℤ) : ZMod (p ^ k)) := by push_cast; rfl
        rw [h1]
        have h2 : (ZMod.cast (((z - u : ℤ) : ZMod (p ^ k))) : ZMod p) = ((z - u : ℤ) : ZMod p) :=
          ZMod.cast_intCast hdvd (z - u)
        rw [h2]
        push_cast
        rfl
      have hwx : ∀ i j, i ≠ j → (ZMod.cast ((phi x i) - (u : ZMod (p ^ k))) : ZMod p) ≠ (ZMod.cast ((phi x j) - (u : ZMod (p ^ k))) : ZMod p) := by
        intro i j hij
        dsimp [phi]
        rw [hcast_diff (x i), hcast_diff (x j)]
        intro heq
        have : (x i : ZMod p) = (x j : ZMod p) := by
          linear_combination heq
        exact hxS.2.1 i j hij this
      have hwx0 : ∀ i j, i ≠ j → (ZMod.cast ((phi x0 i) - (u : ZMod (p ^ k))) : ZMod p) ≠ (ZMod.cast ((phi x0 j) - (u : ZMod (p ^ k))) : ZMod p) := by
        intro i j hij
        dsimp [phi]
        rw [hcast_diff (x0 i), hcast_diff (x0 j)]
        intro heq
        have : (x0 i : ZMod p) = (x0 j : ZMod p) := by
          linear_combination heq
        exact hx0S.2.1 i j hij this
      have hsums : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∑ i, (phi x i - (u : ZMod (p ^ k))) ^ j = ∑ i, (phi x0 i - (u : ZMod (p ^ k))) ^ j := by
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
      obtain ⟨σ, hσ⟩ := exists_perm_of_powerSums_eq p k hp hpk (fun i => phi x i - (u : ZMod (p ^ k))) (fun i => phi x0 i - (u : ZMod (p ^ k))) hwx hwx0 hsums
      refine ⟨σ, fun i => ?_⟩
      have hσi := hσ i
      linear_combination hσi
    exact card_perm_fiber_le k (phi x0) W hW_perm
  let U := Finset.image psi T
  have hU_sub : U ⊆ Fintype.piFinset (fun j : Fin k =>
      (Finset.univ : Finset (ZMod (p ^ k))).filter (fun z =>
        (ZMod.cast z : ZMod (p ^ (j.val + 1))) = (v j : ZMod (p ^ (j.val + 1))))) := by
    intro u' hu'
    rw [Finset.mem_image] at hu'
    obtain ⟨w, hwT, rfl⟩ := hu'
    rw [Finset.mem_image] at hwT
    obtain ⟨x, hxS, rfl⟩ := hwT
    dsimp [S, linnikSet] at hxS
    rw [Finset.mem_filter] at hxS
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [psi, phi]
    have hj_le : j.val + 1 ≤ k := by omega
    have hcast_sub : (∑ i, (phi x i - (u : ZMod (p ^ k))) ^ (j.val + 1)) =
        (∑ i, ((x i - u : ℤ) : ZMod (p ^ k)) ^ (j.val + 1)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      dsimp [phi]
      push_cast
      rfl
    rw [hcast_sub, cast_sum_pow p k (j.val + 1) hj_le (fun i => x i - u)]
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

lemma sum_sub_pow_eq (ℓ : ℕ) (x : Fin ℓ → ℤ) (u : ℤ) (n : ℕ) :
    ∑ i : Fin ℓ, (x i - u) ^ n =
      ∑ r ∈ Finset.range (n + 1), ((n.choose r : ℤ) * (-u) ^ (n - r) * ∑ i : Fin ℓ, (x i) ^ r) := by
  have h1 : ∀ i : Fin ℓ, (x i - u) ^ n = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℤ) * (x i) ^ r * (-u) ^ (n - r) := by
    intro i
    have := add_pow (x i) (-u) n
    rw [sub_eq_add_neg, this]
    refine Finset.sum_congr rfl fun r hr => by ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h2 : (fun i : Fin ℓ => (n.choose r : ℤ) * x i ^ r * (-u) ^ (n - r)) =
      fun i : Fin ℓ => ((n.choose r : ℤ) * (-u) ^ (n - r)) * x i ^ r := by
    ext i
    ring
  rw [h2, Finset.mul_sum]

lemma sum_pow_eq_of_curveSum_eq (k ℓ : ℕ) (x y : Fin ℓ → ℤ) (h : curveSum k ℓ x = curveSum k ℓ y)
    (r : ℕ) (hr : r ≤ k) :
    ∑ i : Fin ℓ, (x i) ^ r = ∑ i : Fin ℓ, (y i) ^ r := by
  rcases r with _|r
  · simp
  · have hr_lt : r < k := by omega
    let j : Fin k := ⟨r, hr_lt⟩
    have hx : curveSum k ℓ x j = ∑ i : Fin ℓ, (x i) ^ (r + 1) := curveSum_apply k ℓ x j
    have hy : curveSum k ℓ y j = ∑ i : Fin ℓ, (y i) ^ (r + 1) := curveSum_apply k ℓ y j
    have heq := congr_fun h j
    rw [hx, hy] at heq
    exact heq

lemma sum_sub_pow_eq_of_curveSum_eq (k ℓ : ℕ) (x y : Fin ℓ → ℤ) (h : curveSum k ℓ x = curveSum k ℓ y)
    (u : ℤ) (n : ℕ) (hn : n ≤ k) :
    ∑ i : Fin ℓ, (x i - u) ^ n = ∑ i : Fin ℓ, (y i - u) ^ n := by
  rw [sum_sub_pow_eq ℓ x u n, sum_sub_pow_eq ℓ y u n]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  have hr_le : r ≤ k := by omega
  rw [sum_pow_eq_of_curveSum_eq k ℓ x y h r hr_le]

lemma sum_splitEquiv {α M : Type*} [AddCommMonoid M] (k m ℓ : ℕ) (h : k + m = ℓ)
    (u : Fin k → α) (v : Fin m → α) (f : α → M) :
    ∑ i : Fin ℓ, f (splitEquiv k m ℓ h (u, v) i) = (∑ i : Fin k, f (u i)) + (∑ j : Fin m, f (v j)) := by
  have h1 : ∑ i : Fin ℓ, f (splitEquiv k m ℓ h (u, v) i) =
      ∑ j : Fin (k + m), f (Fin.append u v j) := by
    rw [← (finCongr h).sum_comp]
    rfl
  rw [h1, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma dvd_sub_of_mem_Tu {M p : ℕ} (hp : 0 < p) (u0 : ZMod p) (z : ℤ) (hz : z ∈ Tu M p u0) :
    let u : ℤ := (u0.val : ℤ)
    (p : ℤ) ∣ (z - u) := by
  intro u
  have : NeZero p := ⟨ne_of_gt hp⟩
  rw [Tu, Finset.mem_filter] at hz
  have hz_mod : (z : ZMod p) = u0 := hz.2
  have hu_mod : (u : ZMod p) = u0 := by
    dsimp [u]
    push_cast
    exact ZMod.natCast_zmod_val u0
  have hdiff : ((z - u : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hz_mod, hu_mod, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (z - u) p).mp hdiff

lemma z_sub_u_eq {M p : ℕ} (hp : 0 < p) (u0 : ZMod p) (z : ℤ) (hz : z ∈ Tu M p u0) :
    let u : ℤ := (u0.val : ℤ)
    z - u = (p : ℤ) * ((z - u) / (p : ℤ) + 1 - 1) := by
  intro u
  have hdvd := dvd_sub_of_mem_Tu hp u0 z hz
  have h1 : (z - u) / (p : ℤ) + 1 - 1 = (z - u) / (p : ℤ) := by omega
  rw [h1, mul_comm]
  exact (Int.ediv_mul_cancel hdvd).symm

lemma tu_shift_mem {M p : ℕ} (hp : 0 < p) (u0 : ZMod p) (z : ℤ) (hz : z ∈ Tu M p u0) :
    let u : ℤ := (u0.val : ℤ)
    (z - u) / (p : ℤ) + 1 ∈ Finset.Icc (1 : ℤ) ((M / p + 1 : ℕ) : ℤ) := by
  intro u
  have : NeZero p := ⟨ne_of_gt hp⟩
  have hdvd := dvd_sub_of_mem_Tu hp u0 z hz
  obtain ⟨q, hq⟩ := hdvd
  rw [Tu, Finset.mem_filter, Finset.mem_Icc] at hz
  have hz1 := hz.1.1
  have hz2 := hz.1.2
  have hu_lt : u0.val < p := ZMod.val_lt u0
  have hu_nonneg : 0 ≤ u := by positivity
  have hu_le : u ≤ (p : ℤ) - 1 := by
    have : (u0.val : ℤ) ≤ (p : ℤ) - 1 := by omega
    exact this
  have hp_pos : 0 < (p : ℤ) := by omega
  have hq_eq : (z - u) / (p : ℤ) = q := by
    rw [hq]
    exact Int.mul_ediv_cancel_left q (by omega)
  rw [hq_eq]
  rw [Finset.mem_Icc]
  constructor
  · have : -(p : ℤ) < z - u := by omega
    rw [hq] at this
    have : -1 < q := by
      nlinarith
    omega
  · have : z - u ≤ (M : ℤ) := by omega
    rw [hq] at this
    have : (p : ℤ) * q ≤ (M : ℤ) := this
    have hq_nonneg : 0 ≤ q := by
      have : -(p : ℤ) < (p : ℤ) * q := by linarith
      nlinarith
    have hq_nat : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq_nonneg
    have : p * q.toNat ≤ M := by
      have : (p : ℤ) * (q.toNat : ℤ) ≤ (M : ℤ) := by rw [hq_nat]; exact this
      exact_mod_cast this
    rw [mul_comm] at this
    have hdiv : q.toNat ≤ M / p := Nat.le_div_iff_mul_le hp |>.mpr this
    have : q ≤ (M / p : ℕ) := by
      have : (q.toNat : ℤ) ≤ ((M / p : ℕ) : ℤ) := by exact_mod_cast hdiv
      rwa [hq_nat] at this
    push_cast
    omega

lemma tu_shift_inj {M p : ℕ} (hp : 0 < p) (u0 : ZMod p) (z1 z2 : ℤ)
    (hz1 : z1 ∈ Tu M p u0) (hz2 : z2 ∈ Tu M p u0)
    (heq : (z1 - (u0.val : ℤ)) / (p : ℤ) + 1 = (z2 - (u0.val : ℤ)) / (p : ℤ) + 1) :
    z1 = z2 := by
  have hdvd1 := dvd_sub_of_mem_Tu hp u0 z1 hz1
  have hdvd2 := dvd_sub_of_mem_Tu hp u0 z2 hz2
  have h1 : (z1 - (u0.val : ℤ)) / (p : ℤ) = (z2 - (u0.val : ℤ)) / (p : ℤ) := by omega
  have hmul1 := Int.ediv_mul_cancel hdvd1
  have hmul2 := Int.ediv_mul_cancel hdvd2
  have : z1 - (u0.val : ℤ) = z2 - (u0.val : ℤ) := by
    rw [← hmul1, ← hmul2, h1]
  omega

lemma sum_pow_sub_u_eq (k m ℓ M p : ℕ) (h : k + m = ℓ) (hp : 0 < p) (u0 : ZMod p)
    (x1 y1 : Fin k → ℤ) (x2 y2 : Fin m → ℤ)
    (hx2 : x2 ∈ tuplesU m M p u0) (hy2 : y2 ∈ tuplesU m M p u0)
    (hcurve : curveSum k ℓ (splitEquiv k m ℓ h (x1, x2)) = curveSum k ℓ (splitEquiv k m ℓ h (y1, y2)))
    (r : ℕ) (hr : r ≤ k) :
    let u : ℤ := (u0.val : ℤ)
    let x' : Fin m → ℤ := fun j => (x2 j - u) / (p : ℤ) + 1
    let y' : Fin m → ℤ := fun j => (y2 j - u) / (p : ℤ) + 1
    (p : ℤ) ^ r * (∑ j : Fin m, (x' j - 1) ^ r - ∑ j : Fin m, (y' j - 1) ^ r) =
      ∑ i : Fin k, (y1 i - u) ^ r - ∑ i : Fin k, (x1 i - u) ^ r := by
  intro u x' y'
  have h_full := sum_sub_pow_eq_of_curveSum_eq k ℓ (splitEquiv k m ℓ h (x1, x2)) (splitEquiv k m ℓ h (y1, y2)) hcurve u r hr
  have hx_split := sum_splitEquiv k m ℓ h x1 x2 (fun z => (z - u) ^ r)
  have hy_split := sum_splitEquiv k m ℓ h y1 y2 (fun z => (z - u) ^ r)
  rw [hx_split, hy_split] at h_full
  have h_rearr : ∑ j : Fin m, (x2 j - u) ^ r - ∑ j : Fin m, (y2 j - u) ^ r =
      ∑ i : Fin k, (y1 i - u) ^ r - ∑ i : Fin k, (x1 i - u) ^ r := by
    omega
  have hx2_mem : ∀ j : Fin m, x2 j ∈ Tu M p u0 := by
    intro j
    rw [tuplesU, Fintype.mem_piFinset] at hx2
    exact hx2 j
  have hy2_mem : ∀ j : Fin m, y2 j ∈ Tu M p u0 := by
    intro j
    rw [tuplesU, Fintype.mem_piFinset] at hy2
    exact hy2 j
  have hx_pow : ∀ j : Fin m, (x2 j - u) ^ r = (p : ℤ) ^ r * (x' j - 1) ^ r := by
    intro j
    have heq := z_sub_u_eq hp u0 (x2 j) (hx2_mem j)
    have h_lin : x2 j - u = (p : ℤ) * (x' j - 1) := heq
    rw [h_lin, mul_pow]
  have hy_pow : ∀ j : Fin m, (y2 j - u) ^ r = (p : ℤ) ^ r * (y' j - 1) ^ r := by
    intro j
    have heq := z_sub_u_eq hp u0 (y2 j) (hy2_mem j)
    have h_lin : y2 j - u = (p : ℤ) * (y' j - 1) := heq
    rw [h_lin, mul_pow]
  simp_rw [hx_pow, hy_pow] at h_rearr
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub] at h_rearr
  exact h_rearr

lemma sum_add_one_pow_sub (m n : ℕ) (x' y' : Fin m → ℤ) :
    ∑ i : Fin m, ((x' i - 1) + 1) ^ n - ∑ i : Fin m, ((y' i - 1) + 1) ^ n =
      ∑ r ∈ Finset.Icc 1 n, ((n.choose r : ℤ) * (∑ i : Fin m, (x' i - 1) ^ r - ∑ i : Fin m, (y' i - 1) ^ r)) := by
  have hx : ∀ i : Fin m, ((x' i - 1) + 1) ^ n = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℤ) * (x' i - 1) ^ r := by
    intro i
    have := add_pow (x' i - 1) 1 n
    simp only [one_pow, mul_one] at this
    rw [this]
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  have hy : ∀ i : Fin m, ((y' i - 1) + 1) ^ n = ∑ r ∈ Finset.range (n + 1), (n.choose r : ℤ) * (y' i - 1) ^ r := by
    intro i
    have := add_pow (y' i - 1) 1 n
    simp only [one_pow, mul_one] at this
    rw [this]
    refine Finset.sum_congr rfl fun r _ => mul_comm _ _
  simp_rw [hx, hy]
  rw [← Finset.sum_sub_distrib]
  have h_sub : (fun i : Fin m => (∑ r ∈ Finset.range (n + 1), (n.choose r : ℤ) * (x' i - 1) ^ r) -
      (∑ r ∈ Finset.range (n + 1), (n.choose r : ℤ) * (y' i - 1) ^ r)) =
      fun i => ∑ r ∈ Finset.range (n + 1), ((n.choose r : ℤ) * (x' i - 1) ^ r - (n.choose r : ℤ) * (y' i - 1) ^ r) := by
    ext i
    rw [Finset.sum_sub_distrib]
  rw [h_sub, Finset.sum_comm]
  have h_range : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext a
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h_range, Finset.sum_insert (by simp)]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, sub_self, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  have h_ring : (fun x : Fin m => (n.choose r : ℤ) * (x' x - 1) ^ r - (n.choose r : ℤ) * (y' x - 1) ^ r) =
      fun x => (n.choose r : ℤ) * ((x' x - 1) ^ r - (y' x - 1) ^ r) := by
    ext x
    ring
  rw [h_ring, ← Finset.mul_sum, Finset.sum_sub_distrib]

lemma curveSum_sub_eq_diffVector (k m ℓ M p : ℕ) (h : k + m = ℓ) (hp : 0 < p) (u0 : ZMod p)
    (x1 y1 : Fin k → ℤ) (x2 y2 : Fin m → ℤ)
    (hx2 : x2 ∈ tuplesU m M p u0) (hy2 : y2 ∈ tuplesU m M p u0)
    (hcurve : curveSum k ℓ (splitEquiv k m ℓ h (x1, x2)) = curveSum k ℓ (splitEquiv k m ℓ h (y1, y2))) :
    let u : ℤ := (u0.val : ℤ)
    let x' : Fin m → ℤ := fun j => (x2 j - u) / (p : ℤ) + 1
    let y' : Fin m → ℤ := fun j => (y2 j - u) / (p : ℤ) + 1
    curveSum k m x' - curveSum k m y' = diffVector k x1 y1 p u := by
  intro u x' y'
  ext j
  rw [Pi.sub_apply, curveSum_apply, curveSum_apply]
  have h_sub := sum_add_one_pow_sub m (j.val + 1) x' y'
  have h_id_x : (fun i : Fin m => ((x' i - 1) + 1) ^ (j.val + 1)) = fun i => (x' i) ^ (j.val + 1) := by
    ext i
    congr 1
    omega
  have h_id_y : (fun i : Fin m => ((y' i - 1) + 1) ^ (j.val + 1)) = fun i => (y' i) ^ (j.val + 1) := by
    ext i
    congr 1
    omega
  rw [h_id_x, h_id_y] at h_sub
  rw [h_sub]
  dsimp [diffVector]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  have hr_le : r ≤ k := by
    have : j.val + 1 ≤ k := j.isLt
    omega
  have hpow := sum_pow_sub_u_eq k m ℓ M p h hp u0 x1 y1 x2 y2 hx2 hy2 hcurve r hr_le
  have hp_ne : (p : ℤ) ^ r ≠ 0 := by
    have : 0 < (p : ℤ) := by omega
    positivity
  have hdiv : (∑ j : Fin m, (x' j - 1) ^ r - ∑ j : Fin m, (y' j - 1) ^ r) =
      (∑ i : Fin k, (y1 i - u) ^ r - ∑ i : Fin k, (x1 i - u) ^ r) / (p : ℤ) ^ r := by
    rw [← hpow]
    exact (Int.mul_ediv_cancel_left _ hp_ne).symm
  rw [hdiv]

lemma x1_mem_linnikSet (k m ℓ M p : ℕ) (h : k + m = ℓ) (hp : p.Prime) (u0 : ZMod p)
    (x1 y1 : Fin k → ℤ) (x2 y2 : Fin m → ℤ)
    (hx1 : x1 ∈ Dk k M p) (hx2 : x2 ∈ tuplesU m M p u0) (hy2 : y2 ∈ tuplesU m M p u0)
    (hcurve : curveSum k ℓ (splitEquiv k m ℓ h (x1, x2)) = curveSum k ℓ (splitEquiv k m ℓ h (y1, y2))) :
    let u : ℤ := (u0.val : ℤ)
    let w : Fin k → ℤ := fun j => ∑ i : Fin k, (y1 i - u) ^ (j.val + 1)
    x1 ∈ linnikSet k M p u w := by
  intro u w
  rw [Dk, Finset.mem_filter] at hx1
  rw [linnikSet, Finset.mem_filter]
  refine ⟨hx1.1, hx1.2, ?_⟩
  intro j
  have : NeZero (p ^ (j.val + 1)) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
  have hj_le : j.val + 1 ≤ k := j.isLt
  have hpow := sum_pow_sub_u_eq k m ℓ M p h hp.pos u0 x1 y1 x2 y2 hx2 hy2 hcurve (j.val + 1) hj_le
  have hdvd : ((p : ℤ) ^ (j.val + 1)) ∣ (∑ i : Fin k, (y1 i - u) ^ (j.val + 1) - ∑ i : Fin k, (x1 i - u) ^ (j.val + 1)) :=
    ⟨_, hpow.symm⟩
  have h_zmod_zero : (((∑ i : Fin k, (y1 i - u) ^ (j.val + 1) - ∑ i : Fin k, (x1 i - u) ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1)))) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ (j.val + 1))).mpr hdvd
  have heq : ((∑ i : Fin k, (y1 i - u) ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) -
      ((∑ i : Fin k, (x1 i - u) ^ (j.val + 1) : ℤ) : ZMod (p ^ (j.val + 1))) = 0 := by
    rw [← Int.cast_sub]
    exact h_zmod_zero
  dsimp [w]
  exact sub_eq_zero.mp (by linear_combination -heq)

lemma nat_cast_div_le (M N : ℕ) [NeZero N] :
    ((M / N : ℕ) : ℝ) ≤ (M : ℝ) / (N : ℝ) := by
  have hpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  rw [le_div_iff₀ hpos]
  have hmul : (M / N) * N ≤ M := Nat.div_mul_le_self M N
  exact_mod_cast hmul

lemma card_Jtilde_u_le (k ℓ M p : ℕ) (hk : k ≤ ℓ) (hp : p.Prime) (hpk : k < p) (u0 : ZMod p) :
    Jtilde_u k ℓ M p hk u0 ≤
      M ^ k * (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k (ℓ - k) (M / p + 1) := by
  set m := ℓ - k
  have h : k + m = ℓ := Nat.add_sub_of_le hk
  let u : ℤ := (u0.val : ℤ)
  let e := splitEquiv (α := ℤ) k m ℓ h
  let ee := Equiv.prodCongr e e
  let S := (Du k ℓ M p hk u0 ×ˢ Du k ℓ M p hk u0).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2)
  let S' := ((Dk k M p ×ˢ tuplesU m M p u0) ×ˢ (Dk k M p ×ˢ tuplesU m M p u0)).filter
    (fun xy => curveSum k ℓ (e xy.1) = curveSum k ℓ (e xy.2))
  have hS_eq : S.card = S'.card := by
    have h_bij : S = S'.map ee.toEmbedding := by
      ext ⟨x, y⟩
      simp only [S, S', ee, e, mem_filter, mem_product, mem_map_equiv,
        Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
      rw [Du_eq_map k m ℓ M p h hk u0]
      simp only [mem_map_equiv, mem_product]
    rw [h_bij, card_map]
  have hS'_le : S'.card ≤ M ^ k * (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k m (M / p + 1) := by
    let f1 : ((Fin k → ℤ) × (Fin m → ℤ)) × ((Fin k → ℤ) × (Fin m → ℤ)) → (Fin k → ℤ) := fun xy => xy.2.1
    have h_maps1 : Set.MapsTo f1 ↑S' ↑(tuples k M) := by
      rintro ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ hxy
      rw [Finset.mem_coe] at hxy
      simp only [S', Finset.mem_filter, Finset.mem_product] at hxy
      rcases hxy with ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, hcurve⟩
      rw [Finset.mem_coe]
      rw [Dk, Finset.mem_filter] at hy1
      exact hy1.1
    rw [card_eq_sum_card_fiberwise h_maps1]
    have h_fiber1 : ∀ y1 ∈ tuples k M,
        (S'.filter (fun xy => f1 xy = y1)).card ≤
          (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k m (M / p + 1) := by
      intro y1 hy1
      let S'1 := S'.filter (fun xy => f1 xy = y1)
      let w : Fin k → ℤ := fun j => ∑ i : Fin k, (y1 i - u) ^ (j.val + 1)
      let L := linnikSet k M p u w
      let f2 : ((Fin k → ℤ) × (Fin m → ℤ)) × ((Fin k → ℤ) × (Fin m → ℤ)) → (Fin k → ℤ) := fun xy => xy.1.1
      have h_maps2 : Set.MapsTo f2 ↑S'1 ↑L := by
        rintro ⟨⟨x1, x2⟩, ⟨y1', y2⟩⟩ hxy
        rw [Finset.mem_coe] at hxy
        simp only [S'1, S', Finset.mem_filter, Finset.mem_product] at hxy
        rcases hxy with ⟨⟨⟨⟨hx1, hx2⟩, ⟨hy1', hy2⟩⟩, hcurve⟩, hy1_eq⟩
        dsimp [f1] at hy1_eq
        cases hy1_eq
        rw [Finset.mem_coe]
        exact x1_mem_linnikSet k m ℓ M p h hp u0 x1 y1 x2 y2 hx1 hx2 hy2 hcurve
      rw [card_eq_sum_card_fiberwise h_maps2]
      have h_fiber2 : ∀ x1 ∈ L, (S'1.filter (fun xy => f2 xy = x1)).card ≤ J k m (M / p + 1) := by
        intro x1 hx1
        let S'2 := S'1.filter (fun xy => f2 xy = x1)
        let T := ((tuples m (M / p + 1)) ×ˢ (tuples m (M / p + 1))).filter
          (fun x'y' => curveSum k m x'y'.1 - curveSum k m x'y'.2 = diffVector k x1 y1 p u)
        let theta : ((Fin k → ℤ) × (Fin m → ℤ)) × ((Fin k → ℤ) × (Fin m → ℤ)) → (Fin m → ℤ) × (Fin m → ℤ) :=
          fun xy => (fun j => (xy.1.2 j - u) / (p : ℤ) + 1, fun j => (xy.2.2 j - u) / (p : ℤ) + 1)
        have h_maps_theta : Set.MapsTo theta ↑S'2 ↑T := by
          rintro ⟨⟨x1', x2⟩, ⟨y1', y2⟩⟩ hxy
          rw [Finset.mem_coe] at hxy
          simp only [S'2, S'1, S', Finset.mem_filter, Finset.mem_product] at hxy
          rcases hxy with ⟨⟨⟨⟨⟨hx1', hx2⟩, ⟨hy1', hy2⟩⟩, hcurve⟩, hy1_eq⟩, hx1_eq⟩
          dsimp [f1] at hy1_eq
          dsimp [f2] at hx1_eq
          cases hy1_eq
          cases hx1_eq
          dsimp [T, theta]
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, mem_tuples_iff, mem_tuples_iff]
          refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩
          · rw [tuplesU, Fintype.mem_piFinset] at hx2
            have hj := tu_shift_mem hp.pos u0 (x2 j) (hx2 j)
            rw [Finset.mem_Icc] at hj
            exact hj
          · rw [tuplesU, Fintype.mem_piFinset] at hy2
            have hj := tu_shift_mem hp.pos u0 (y2 j) (hy2 j)
            rw [Finset.mem_Icc] at hj
            exact hj
          · exact curveSum_sub_eq_diffVector k m ℓ M p h hp.pos u0 x1 y1 x2 y2 hx2 hy2 hcurve
        have h_inj_theta : Set.InjOn theta ↑S'2 := by
          rintro ⟨⟨x1_1, x2_1⟩, ⟨y1_1, y2_1⟩⟩ hxy1 ⟨⟨x1_2, x2_2⟩, ⟨y1_2, y2_2⟩⟩ hxy2 heq
          rw [Finset.mem_coe] at hxy1 hxy2
          simp only [S'2, S'1, S', Finset.mem_filter, Finset.mem_product] at hxy1 hxy2
          rcases hxy1 with ⟨⟨⟨⟨⟨hx1_1_m, hx2_1⟩, ⟨hy1_1_m, hy2_1⟩⟩, hcurve1⟩, hy1_1⟩, hx1_1⟩
          rcases hxy2 with ⟨⟨⟨⟨⟨hx1_2_m, hx2_2⟩, ⟨hy1_2_m, hy2_2⟩⟩, hcurve2⟩, hy1_2⟩, hx1_2⟩
          dsimp [f1] at hy1_1 hy1_2
          dsimp [f2] at hx1_1 hx1_2
          cases hy1_1
          cases hy1_2
          cases hx1_1
          cases hx1_2
          rw [tuplesU, Fintype.mem_piFinset] at hx2_1 hy2_1 hx2_2 hy2_2
          dsimp [theta] at heq
          have h_x' := congr_arg Prod.fst heq
          have h_y' := congr_arg Prod.snd heq
          have h_x2 : x2_1 = x2_2 := by
            ext j
            have := congr_fun h_x' j
            exact tu_shift_inj hp.pos u0 (x2_1 j) (x2_2 j) (hx2_1 j) (hx2_2 j) this
          have h_y2 : y2_1 = y2_2 := by
            ext j
            have := congr_fun h_y' j
            exact tu_shift_inj hp.pos u0 (y2_1 j) (y2_2 j) (hy2_1 j) (hy2_2 j) this
          subst h_x2 h_y2
          rfl
        have h_card_le := card_le_card_of_injOn theta (fun z hz => h_maps_theta hz) h_inj_theta
        have hT_le := card_filter_curveSum_sub_le k m (M / p + 1) (diffVector k x1 y1 p u)
        exact h_card_le.trans hT_le
      have h_sum_le := sum_le_sum (fun x1 hx1 => h_fiber2 x1 hx1)
      rw [sum_const, nsmul_eq_mul] at h_sum_le
      have hL_card := card_linnikSet_le p k M hp hpk u w
      exact h_sum_le.trans (Nat.mul_le_mul_right (J k m (M / p + 1)) hL_card)
    have h_sum_le1 := sum_le_sum (fun y1 hy1 => h_fiber1 y1 hy1)
    rw [sum_const, nsmul_eq_mul] at h_sum_le1
    have h_tup_card := card_tuples k M
    rw [h_tup_card] at h_sum_le1
    rw [mul_assoc]
    exact h_sum_le1
  dsimp [Jtilde_u]
  rw [hS_eq]
  exact hS'_le

theorem Jtilde_le (k ℓ M p : ℕ) (hk : 1 ≤ k) (hkl : k < ℓ) (hp : p.Prime) (hpk : k < p)
    (hpM : (M : ℝ) ^ (1 / (k : ℝ)) < p) (hM : 1 ≤ M) :
    (Jtilde k ℓ M p hkl.le : ℝ) ≤
      (p : ℝ) * M ^ k * (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k (ℓ - k) (M / p + 1) := by
  have _ := hk
  have _ := hpM
  have _ := hM
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨ne_zero_of_lt (Nat.pow_pos hp.pos)⟩
  have heq := Jtilde_eq_sum k ℓ M p hkl.le hkl hp.pos
  have h_le : (Jtilde k ℓ M p hkl.le : ℝ) ≤
      ∑ u0 : ZMod p, ((M ^ k * (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k (ℓ - k) (M / p + 1) : ℕ) : ℝ) := by
    rw [heq]
    push_cast
    refine sum_le_sum fun u0 _ => ?_
    exact_mod_cast card_Jtilde_u_le k ℓ M p hkl.le hp hpk u0
  rw [sum_const, card_univ, ZMod.card p, nsmul_eq_mul] at h_le
  push_cast at h_le
  have h_div_le : ((M / p ^ k : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) ^ k := by
    have h1 := nat_cast_div_le M (p ^ k)
    have h2 : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k := by push_cast; rfl
    rwa [h2] at h1
  have h_add_le : ((M / p ^ k : ℕ) : ℝ) + 2 ≤ (M : ℝ) / (p : ℝ) ^ k + 2 := by linarith
  have h_nonneg : 0 ≤ ((M / p ^ k : ℕ) : ℝ) + 2 := by positivity
  have h_pow_le : (((M / p ^ k : ℕ) : ℝ) + 2) ^ k ≤ ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k :=
    pow_le_pow_left₀ h_nonneg h_add_le k
  have h_linnik_le : ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (((M / p ^ k : ℕ) : ℝ) + 2) ^ k) ≤
      ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) := by
    refine mul_le_mul_of_nonneg_left h_pow_le ?_
    positivity
  have h_final : (p : ℝ) * (M : ℝ) ^ k * (((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (((M / p ^ k : ℕ) : ℝ) + 2) ^ k)) * (J k (ℓ - k) (M / p + 1) : ℝ) ≤
      (p : ℝ) * (M : ℝ) ^ k * (((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k)) * (J k (ℓ - k) (M / p + 1) : ℝ) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left h_linnik_le ?_
    positivity
  calc (Jtilde k ℓ M p hkl.le : ℝ)
    _ ≤ (p : ℝ) * (M : ℝ) ^ k * (((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * (((M / p ^ k : ℕ) : ℝ) + 2) ^ k)) * (J k (ℓ - k) (M / p + 1) : ℝ) := by
      linarith [h_le]
    _ ≤ (p : ℝ) * (M : ℝ) ^ k * (((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k)) * (J k (ℓ - k) (M / p + 1) : ℝ) :=
      h_final
    _ = (p : ℝ) * M ^ k * (k.factorial * p ^ (k * (k - 1) / 2) * (M / p ^ k + 2) ^ k) * J k (ℓ - k) (M / p + 1) := by ring

end Erdos1201.MR.Vinogradov
