import Mathlib

/-!
# Fourier analysis on a finite abelian group: counting solutions of additive equations

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

For a finite abelian group `G` and an additive character `ψ : AddChar G ℂ`, the Fourier
coefficient of `f : G → ℂ` is `fhat f ψ = ∑ a, f a * ψ a`. We prove Parseval's identity, the
counting identity `#{(x, y) ∈ X × Y : F x = F' y} · |G| = ∑_ψ (∑_{x∈X} ψ(F x)) conj(∑_{y∈Y} ψ(F' y))`,
the factorisation of character sums over independent coordinates, and the power-mean
inequality `‖∑ z_u‖^n ≤ |I|^{n-1} ∑ ‖z_u‖^n`. These are the tools for the Hölder restriction
step (Lemma 19 of T. Tao's *254A, Notes 5*) in the proof of Vinogradov's mean value theorem.
-/

namespace Erdos1201.MR.Vinogradov

open Finset

section FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Fourier coefficient of `f` at the character `ψ`. -/
noncomputable def fhat (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ := ∑ a, f a * ψ a

omit [DecidableEq G] in
lemma addChar_mul_conj (ψ : AddChar G ℂ) (a b : G) :
    ψ a * (starRingEnd ℂ) (ψ b) = ψ (a - b) := by
  rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
    sub_eq_add_neg]

/-- Parseval's identity on a finite abelian group. -/
theorem sum_fhat_mul_conj_fhat (f g : G → ℂ) :
    ∑ ψ : AddChar G ℂ, fhat f ψ * (starRingEnd ℂ) (fhat g ψ) =
      (Fintype.card G : ℂ) * ∑ a, f a * (starRingEnd ℂ) (g a) := by
  have hexp : ∀ ψ : AddChar G ℂ, fhat f ψ * (starRingEnd ℂ) (fhat g ψ) =
      ∑ a, ∑ b, (f a * (starRingEnd ℂ) (g b)) * ψ (a - b) := by
    intro ψ
    rw [fhat, fhat, map_sum, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [map_mul, ← addChar_mul_conj ψ a b]
    ring
  calc ∑ ψ : AddChar G ℂ, fhat f ψ * (starRingEnd ℂ) (fhat g ψ)
      = ∑ ψ : AddChar G ℂ, ∑ a, ∑ b, (f a * (starRingEnd ℂ) (g b)) * ψ (a - b) := by
        simp_rw [hexp]
    _ = ∑ a, ∑ b, (f a * (starRingEnd ℂ) (g b)) * ∑ ψ : AddChar G ℂ, ψ (a - b) := by
        rw [sum_comm]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun b _ => ?_
        rw [mul_sum]
    _ = ∑ a, ∑ b, (f a * (starRingEnd ℂ) (g b)) *
          (if a - b = 0 then (Fintype.card G : ℂ) else 0) := by
        simp only [AddChar.sum_apply_eq_ite]
    _ = (Fintype.card G : ℂ) * ∑ a, f a * (starRingEnd ℂ) (g a) := by
        simp only [sub_eq_zero, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
        rw [mul_sum]
        refine sum_congr rfl fun a _ => ?_
        ring

/-- The multiplicity function of `F` on `X`. -/
noncomputable def multiplicity {α : Type*} (X : Finset α) (F : α → G) (c : G) : ℂ :=
  ((X.filter (fun x => F x = c)).card : ℂ)

lemma fhat_multiplicity {α : Type*} (X : Finset α) (F : α → G) (ψ : AddChar G ℂ) :
    fhat (multiplicity X F) ψ = ∑ x ∈ X, ψ (F x) := by
  unfold fhat multiplicity
  rw [← Finset.sum_fiberwise_of_maps_to (s := X) (t := (univ : Finset G)) (g := F)
    (fun _ _ => mem_univ _) (fun x => ψ (F x))]
  refine sum_congr rfl fun c _ => ?_
  have hfib : ∀ x ∈ X.filter (fun x => F x = c), ψ (F x) = ψ c := fun x hx => by
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hfib, sum_const, nsmul_eq_mul]

/-- Counting solutions of `F x = F' y` through characters. -/
theorem card_filter_eq_mul_card_eq_sum {α β : Type*} (X : Finset α) (Y : Finset β)
    (F : α → G) (F' : β → G) :
    (((X ×ˢ Y).filter (fun xy => F xy.1 = F' xy.2)).card : ℂ) * (Fintype.card G : ℂ) =
      ∑ ψ : AddChar G ℂ, (∑ x ∈ X, ψ (F x)) * (starRingEnd ℂ) (∑ y ∈ Y, ψ (F' y)) := by
  classical
  have hconj : ∀ c, (starRingEnd ℂ) (multiplicity Y F' c) = multiplicity Y F' c := by
    intro c
    unfold multiplicity
    exact Complex.conj_natCast _
  have hcount : (((X ×ˢ Y).filter (fun xy => F xy.1 = F' xy.2)).card : ℂ) =
      ∑ c, multiplicity X F c * (starRingEnd ℂ) (multiplicity Y F' c) := by
    simp_rw [hconj]
    have hset : (X ×ˢ Y).filter (fun xy => F xy.1 = F' xy.2) =
        (univ : Finset G).biUnion
          (fun c => (X.filter (fun x => F x = c)) ×ˢ (Y.filter (fun y => F' y = c))) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, mem_biUnion]
      constructor
      · rintro ⟨⟨hx, hy⟩, h⟩
        exact ⟨F x, mem_univ _, ⟨hx, rfl⟩, hy, h.symm⟩
      · rintro ⟨c, -, ⟨hx, hxc⟩, hy, hyc⟩
        exact ⟨⟨hx, hy⟩, by rw [hxc, hyc]⟩
    rw [hset, card_biUnion]
    · push_cast
      refine sum_congr rfl fun c _ => ?_
      unfold multiplicity
      rw [card_product]
      push_cast
      ring
    · intro c _ c' _ hcc'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_product, mem_filter] at h1 h2
      exact hcc' (h1.1.2.symm.trans h2.1.2)
  calc (((X ×ˢ Y).filter (fun xy => F xy.1 = F' xy.2)).card : ℂ) * (Fintype.card G : ℂ)
      = (Fintype.card G : ℂ) *
          ∑ c, multiplicity X F c * (starRingEnd ℂ) (multiplicity Y F' c) := by
        rw [hcount, mul_comm]
    _ = ∑ ψ : AddChar G ℂ, fhat (multiplicity X F) ψ *
          (starRingEnd ℂ) (fhat (multiplicity Y F') ψ) :=
        (sum_fhat_mul_conj_fhat _ _).symm
    _ = ∑ ψ : AddChar G ℂ, (∑ x ∈ X, ψ (F x)) * (starRingEnd ℂ) (∑ y ∈ Y, ψ (F' y)) := by
        simp_rw [fhat_multiplicity]

omit [Fintype G] [DecidableEq G] in
/-- An additive character turns finite sums into products. -/
lemma addChar_map_sum {ι : Type*} (ψ : AddChar G ℂ) (s : Finset ι) (a : ι → G) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert i s hi ih => rw [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]

omit [Fintype G] [DecidableEq G] in
/-- Character sums over independent coordinates factor. -/
theorem sum_piFinset_addChar_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] (t : Finset κ)
    (γ : κ → G) (ψ : AddChar G ℂ) :
    ∑ x ∈ Fintype.piFinset (fun _ : ι => t), ψ (∑ i, γ (x i)) =
      (∑ v ∈ t, ψ (γ v)) ^ Fintype.card ι := by
  have hψ : ∀ x : ι → κ, ψ (∑ i, γ (x i)) = ∏ i, ψ (γ (x i)) := fun x =>
    addChar_map_sum ψ univ (fun i => γ (x i))
  simp_rw [hψ]
  rw [← Finset.prod_univ_sum (fun _ : ι => t) (fun _ v => ψ (γ v))]
  rw [prod_const, card_univ]

/-- Power-mean inequality for finite sums of complex numbers. -/
theorem norm_sum_pow_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (n : ℕ) :
    ‖∑ u ∈ s, z u‖ ^ (n + 1) ≤ (s.card : ℝ) ^ n * ∑ u ∈ s, ‖z u‖ ^ (n + 1) := by
  have h1 : ‖∑ u ∈ s, z u‖ ^ (n + 1) ≤ (∑ u ∈ s, ‖z u‖) ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h2 := pow_sum_div_card_le_sum_pow (s := s) (f := fun u => ‖z u‖)
    (fun u _ => norm_nonneg _) n
  rw [div_le_iff₀ (by positivity)] at h2
  calc ‖∑ u ∈ s, z u‖ ^ (n + 1) ≤ (∑ u ∈ s, ‖z u‖) ^ (n + 1) := h1
    _ ≤ (∑ u ∈ s, ‖z u‖ ^ (n + 1)) * (s.card : ℝ) ^ n := h2
    _ = (s.card : ℝ) ^ n * ∑ u ∈ s, ‖z u‖ ^ (n + 1) := by ring

end FiniteFourier

end Erdos1201.MR.Vinogradov
