import Mathlib
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.PrimeSelection
import Erdos1201.MR.Vinogradov.PrimeSelectionMain

/-!
# Prime selection for the Vinogradov mean value theorem: the pigeonhole step

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module proves Lemma 14 of T. Tao's *254A, Notes 5* in the form used here: given more than
`k ^ 3` primes `p` with `p > M ^ (1/k)`, the number `J k ℓ M` of solutions of the moment-curve
system is at most `|P| · ℓ ^ (2k) · J^{(p)}` for one of these primes plus the number of degenerate
solutions. Solutions are split into degenerate ones (fewer than `k` distinct values on one side,
counted by `card_degenerate_tuples_le`) and nondegenerate ones, which are mapped injectively into
`∐_{p ∈ P} JpSet p × (Fin k ↪ Fin ℓ) × (Fin k ↪ Fin ℓ)` by permuting `k` coordinates with distinct
values to the front and choosing a prime `p ∈ P` not dividing the pair discriminant.
-/

namespace Erdos1201.MR.Vinogradov

open Finset

/-- The solution set counted by `J`. -/
noncomputable def solSet (k ℓ M : ℕ) : Finset ((Fin ℓ → ℤ) × (Fin ℓ → ℤ)) :=
  ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2)

lemma J_eq_card_solSet (k ℓ M : ℕ) : J k ℓ M = (solSet k ℓ M).card := rfl

/-- The solution set counted by `Jp`: the first `k` coordinates on each side are pairwise
distinct modulo `p`. -/
noncomputable def JpSet (k ℓ M p : ℕ) (hk : k ≤ ℓ) : Finset ((Fin ℓ → ℤ) × (Fin ℓ → ℤ)) :=
  ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2 ∧
    (∀ i j : Fin k, i ≠ j → (xy.1 (Fin.castLE hk i) : ZMod p) ≠ (xy.1 (Fin.castLE hk j) : ZMod p)) ∧
    (∀ i j : Fin k, i ≠ j → (xy.2 (Fin.castLE hk i) : ZMod p) ≠ (xy.2 (Fin.castLE hk j) : ZMod p)))

lemma Jp_eq_card_JpSet (k ℓ M p : ℕ) (hk : k ≤ ℓ) : Jp k ℓ M p hk = (JpSet k ℓ M p hk).card := by
  unfold Jp JpSet
  congr 1

/-- Any embedding `Fin k ↪ Fin ℓ` is the restriction of a permutation of `Fin ℓ` to the first `k`
coordinates. -/
lemma exists_perm_extend {k ℓ : ℕ} (hkl : k ≤ ℓ) (f : Fin k ↪ Fin ℓ) :
    ∃ σ : Equiv.Perm (Fin ℓ), ∀ i : Fin k, σ (Fin.castLE hkl i) = f i := by
  classical
  let e : {x : Fin ℓ // x ∈ Set.range (Fin.castLE hkl)} ≃ {x : Fin ℓ // x ∈ Set.range f} :=
    (Equiv.ofInjective (Fin.castLE hkl) (Fin.castLE_injective hkl)).symm.trans
      (Equiv.ofInjective f f.injective)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  have hx : Fin.castLE hkl i ∈ Set.range (Fin.castLE hkl) := Set.mem_range_self i
  rw [Equiv.extendSubtype_apply_of_mem e _ hx]
  simp [e]

/-- The number of embeddings `Fin k ↪ Fin ℓ` is at most `ℓ ^ k`. -/
lemma card_embedding_fin_le (k ℓ : ℕ) : Fintype.card (Fin k ↪ Fin ℓ) ≤ ℓ ^ k := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  exact Nat.descFactorial_le_pow ℓ k

/-- The set of ordered pairs `i < j` in `Fin k × Fin k`. -/
def ltPairs (k : ℕ) : Finset (Fin k × Fin k) := univ.filter (fun ij => ij.1 < ij.2)

lemma two_mul_card_ltPairs_le (k : ℕ) : 2 * (ltPairs k).card ≤ k * (k - 1) := by
  set A := ltPairs k with hA
  set A' := (univ : Finset (Fin k × Fin k)).filter (fun ij => ij.2 < ij.1) with hA'
  set D := (univ : Finset (Fin k × Fin k)).filter (fun ij => ij.1 = ij.2) with hD
  have hA'card : A'.card = A.card := by
    have : A' = A.image Prod.swap := by
      ext ⟨i, j⟩
      simp [hA, hA', ltPairs, Prod.swap]
    rw [this, card_image_of_injective _ Prod.swap_injective]
  have hDcard : D.card = k := by
    have : D = univ.image (fun i : Fin k => (i, i)) := by
      ext ⟨i, j⟩
      simp [hD, eq_comm]
    rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), card_univ,
      Fintype.card_fin]
  have hdisj1 : Disjoint A A' := by
    rw [hA, hA', ltPairs, disjoint_filter]
    intro ij _ h1 h2
    exact lt_asymm h1 h2
  have hdisj2 : Disjoint (A ∪ A') D := by
    rw [disjoint_union_left]
    constructor
    · rw [hA, hD, ltPairs, disjoint_filter]
      intro ij _ h1 h2
      exact absurd h2 (ne_of_lt h1)
    · rw [hA', hD, disjoint_filter]
      intro ij _ h1 h2
      exact absurd h2.symm (ne_of_lt h1)
  have hle : (A ∪ A' ∪ D).card ≤ (univ : Finset (Fin k × Fin k)).card :=
    card_le_card (subset_univ _)
  rw [card_union_eq_card_add_card.mpr hdisj2, card_union_eq_card_add_card.mpr hdisj1, hA'card,
    hDcard, card_univ, Fintype.card_prod, Fintype.card_fin] at hle
  have hk : k * (k - 1) = k * k - k := Nat.mul_sub_one k k
  omega

lemma card_ltPairs_eq_sum (k : ℕ) :
    (ltPairs k).card = ∑ i : Fin k, (univ.filter (fun j : Fin k => i < j)).card := by
  rw [ltPairs, card_filter, ← univ_product_univ, sum_product]
  simp only [card_filter]

lemma natAbs_prod_eq {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  change Int.natAbsHom (∏ i ∈ s, f i) = _
  rw [map_prod]
  rfl

/-- The difference product of a tuple with entries in `[1, M]` is at most `M ^ |ltPairs k|`. -/
lemma diffProd_natAbs_le_pow {k M : ℕ} {x : Fin k → ℤ} (hx : ∀ i, x i ∈ Icc (1 : ℤ) M) :
    (diffProd k x).natAbs ≤ M ^ (ltPairs k).card := by
  have hstep : (diffProd k x).natAbs =
      ∏ i : Fin k, ∏ j ∈ univ.filter (fun j => i < j), (x i - x j).natAbs := by
    rw [diffProd, natAbs_prod_eq]
    refine prod_congr rfl (fun i _ => ?_)
    rw [natAbs_prod_eq]
  rw [hstep, card_ltPairs_eq_sum, ← prod_pow_eq_pow_sum]
  refine prod_le_prod' (fun i _ => ?_)
  calc ∏ j ∈ univ.filter (fun j => i < j), (x i - x j).natAbs
      ≤ ∏ _j ∈ univ.filter (fun j => i < j), M := by
        refine prod_le_prod' (fun j _ => ?_)
        have hi := hx i
        have hj := hx j
        rw [mem_Icc] at hi hj
        omega
    _ = M ^ (univ.filter (fun j => i < j)).card := prod_const M

/-- A tuple taking at least `k` distinct values has `k` coordinates with pairwise distinct values. -/
lemma exists_emb_injective_comp {k ℓ : ℕ} (x : Fin ℓ → ℤ)
    (hx : k ≤ (image x univ).card) :
    ∃ f : Fin k ↪ Fin ℓ, Function.Injective (x ∘ f) := by
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hx
  have hidx : ∀ v ∈ T, ∃ i : Fin ℓ, x i = v := by
    intro v hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hTsub hv)
    exact ⟨i, hi⟩
  choose idx hidx using hidx
  let e : Fin k ↪o ℤ := T.orderEmbOfFin hTcard
  let g : Fin k → Fin ℓ := fun i => idx (e i) (T.orderEmbOfFin_mem hTcard i)
  have hcomp : Function.Injective (x ∘ g) := by
    intro i j hij
    have h1 : x (g i) = e i := hidx _ _
    have h2 : x (g j) = e j := hidx _ _
    apply e.injective
    simp only [Function.comp_apply] at hij
    rw [← h1, ← h2]
    exact hij
  exact ⟨⟨g, hcomp.of_comp⟩, hcomp⟩

/-- A chosen permutation of `Fin ℓ` extending an embedding `Fin k ↪ Fin ℓ`. -/
noncomputable def extPerm {k ℓ : ℕ} (hkl : k ≤ ℓ) (f : Fin k ↪ Fin ℓ) : Equiv.Perm (Fin ℓ) :=
  Classical.choose (exists_perm_extend hkl f)

lemma extPerm_castLE {k ℓ : ℕ} (hkl : k ≤ ℓ) (f : Fin k ↪ Fin ℓ) (i : Fin k) :
    extPerm hkl f (Fin.castLE hkl i) = f i :=
  Classical.choose_spec (exists_perm_extend hkl f) i

/-- The pair discriminant of two tuples with entries in `[1, M]` is at most `M ^ (k (k - 1))`. -/
lemma pairDisc_natAbs_le {k M : ℕ} (hM : 1 ≤ M) {u v : Fin k → ℤ}
    (hu : ∀ i, u i ∈ Icc (1 : ℤ) M) (hv : ∀ i, v i ∈ Icc (1 : ℤ) M) :
    ((pairDisc k u v).natAbs : ℝ) ≤ (M : ℝ) ^ (k * (k - 1)) := by
  have h1 := diffProd_natAbs_le_pow hu
  have h2 := diffProd_natAbs_le_pow hv
  have hmul : (pairDisc k u v).natAbs = (diffProd k u).natAbs * (diffProd k v).natAbs := by
    simp [pairDisc, Int.natAbs_mul]
  have hnat : (pairDisc k u v).natAbs ≤ M ^ (k * (k - 1)) := by
    rw [hmul]
    calc (diffProd k u).natAbs * (diffProd k v).natAbs
        ≤ M ^ (ltPairs k).card * M ^ (ltPairs k).card := Nat.mul_le_mul h1 h2
      _ = M ^ (2 * (ltPairs k).card) := by rw [← pow_add, two_mul]
      _ ≤ M ^ (k * (k - 1)) := Nat.pow_le_pow_right hM (two_mul_card_ltPairs_le k)
  exact_mod_cast hnat

/-- A nondegenerate solution, after moving `k` coordinates with distinct values to the front on
each side, is counted by `Jp` for some prime `p ∈ P`. -/
lemma exists_prime_emb_mem_JpSet (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hM : 1 < M)
    (P : Finset ℕ) (hP_card : k ^ 3 < P.card) (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_gt : ∀ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ))
    (xy : (Fin ℓ → ℤ) × (Fin ℓ → ℤ)) (hxy : xy ∈ solSet k ℓ M)
    (hx : k ≤ (image xy.1 univ).card) (hy : k ≤ (image xy.2 univ).card) :
    ∃ p ∈ P, ∃ f g : Fin k ↪ Fin ℓ,
      (xy.1 ∘ extPerm hkl f, xy.2 ∘ extPerm hkl g) ∈ JpSet k ℓ M p hkl := by
  obtain ⟨f, hf⟩ := exists_emb_injective_comp xy.1 hx
  obtain ⟨g, hg⟩ := exists_emb_injective_comp xy.2 hy
  simp only [solSet, mem_filter, mem_product] at hxy
  obtain ⟨⟨hx1, hx2⟩, hsum⟩ := hxy
  let u : Fin k → ℤ := fun i => xy.1 (extPerm hkl f (Fin.castLE hkl i))
  let v : Fin k → ℤ := fun i => xy.2 (extPerm hkl g (Fin.castLE hkl i))
  have hu_eq : ∀ i, u i = (xy.1 ∘ f) i := fun i => by
    simp only [u, Function.comp_apply, extPerm_castLE]
  have hv_eq : ∀ i, v i = (xy.2 ∘ g) i := fun i => by
    simp only [v, Function.comp_apply, extPerm_castLE]
  have hu_inj : Function.Injective u := by
    intro i j h
    apply hf
    rw [← hu_eq, ← hu_eq]
    exact h
  have hv_inj : Function.Injective v := by
    intro i j h
    apply hg
    rw [← hv_eq, ← hv_eq]
    exact h
  have hD : pairDisc k u v ≠ 0 := pairDisc_ne_zero hu_inj hv_inj
  have hu_mem : ∀ i, u i ∈ Icc (1 : ℤ) M := fun i => by
    rw [mem_Icc]
    exact (mem_tuples_iff ℓ M xy.1).mp hx1 _
  have hv_mem : ∀ i, v i ∈ Icc (1 : ℤ) M := fun i => by
    rw [mem_Icc]
    exact (mem_tuples_iff ℓ M xy.2).mp hx2 _
  have hD_le := pairDisc_natAbs_le (by omega) hu_mem hv_mem
  obtain ⟨p, hpP, hpD⟩ := exists_prime_not_dvd hk hM hD hD_le P hP_card hP_prime hP_gt
  obtain ⟨hu_p, hv_p⟩ := not_dvd_of_not_dvd_pairDisc hpD
  refine ⟨p, hpP, f, g, ?_⟩
  simp only [JpSet, mem_filter, mem_product]
  refine ⟨⟨(mem_tuples_comp_perm ℓ M xy.1 _).mpr hx1, (mem_tuples_comp_perm ℓ M xy.2 _).mpr hx2⟩,
    curveSum_eq_of_comp_perm k ℓ xy.1 xy.2 _ _ hsum, ?_, ?_⟩
  · intro i j hij
    exact hu_p i j hij
  · intro i j hij
    exact hv_p i j hij

/-- The nondegenerate solutions inject into `∐_{p ∈ P} JpSet p × (Fin k ↪ Fin ℓ)²`. -/
lemma card_nondeg_le (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hM : 1 < M)
    (P : Finset ℕ) (hP_card : k ^ 3 < P.card) (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_gt : ∀ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ)) :
    ((solSet k ℓ M).filter
      (fun xy => k ≤ (image xy.1 univ).card ∧ k ≤ (image xy.2 univ).card)).card ≤
      ∑ p ∈ P, Jp k ℓ M p hkl * (ℓ ^ k * ℓ ^ k) := by
  have : Nonempty (Fin k ↪ Fin ℓ) := ⟨Fin.castLEEmb hkl⟩
  set ND := (solSet k ℓ M).filter
    (fun xy => k ≤ (image xy.1 univ).card ∧ k ≤ (image xy.2 univ).card) with hND
  have hex : ∀ xy ∈ ND, ∃ p ∈ P, ∃ f g : Fin k ↪ Fin ℓ,
      (xy.1 ∘ extPerm hkl f, xy.2 ∘ extPerm hkl g) ∈ JpSet k ℓ M p hkl := by
    intro xy hxy
    rw [hND, mem_filter] at hxy
    exact exists_prime_emb_mem_JpSet k ℓ M hk hkl hM P hP_card hP_prime hP_gt xy hxy.1
      hxy.2.1 hxy.2.2
  choose! p hpP f g hmem using hex
  let Φ : (Fin ℓ → ℤ) × (Fin ℓ → ℤ) →
      Σ _ : ℕ, ((Fin ℓ → ℤ) × (Fin ℓ → ℤ)) × ((Fin k ↪ Fin ℓ) × (Fin k ↪ Fin ℓ)) :=
    fun xy => ⟨p xy, ((xy.1 ∘ extPerm hkl (f xy), xy.2 ∘ extPerm hkl (g xy)), (f xy, g xy))⟩
  let TGT := P.sigma (fun q => (JpSet k ℓ M q hkl) ×ˢ
    ((univ : Finset (Fin k ↪ Fin ℓ)) ×ˢ (univ : Finset (Fin k ↪ Fin ℓ))))
  have hmaps : ∀ xy ∈ ND, Φ xy ∈ TGT := by
    intro xy hxy
    simp only [TGT, Φ, mem_sigma, mem_product, mem_univ, and_true]
    exact ⟨hpP xy hxy, hmem xy hxy⟩
  have hinj : Set.InjOn Φ ND := by
    intro xy hxy xy' hxy' h
    simp only [Φ] at h
    obtain ⟨_, hrest⟩ := Sigma.mk.inj_iff.mp h
    have hrest' := eq_of_heq hrest
    obtain ⟨hpair, hfg⟩ := Prod.mk.inj hrest'
    obtain ⟨hf, hg⟩ := Prod.mk.inj hfg
    obtain ⟨h1, h2⟩ := Prod.mk.inj hpair
    rw [hf] at h1
    rw [hg] at h2
    have e1 : xy.1 = xy'.1 := by
      funext j
      have := congr_fun h1 ((extPerm hkl (f xy')).symm j)
      simpa using this
    have e2 : xy.2 = xy'.2 := by
      funext j
      have := congr_fun h2 ((extPerm hkl (g xy')).symm j)
      simpa using this
    exact Prod.ext e1 e2
  have hcard := Finset.card_le_card_of_injOn Φ hmaps hinj
  have hTGT : TGT.card = ∑ q ∈ P, Jp k ℓ M q hkl *
      (Fintype.card (Fin k ↪ Fin ℓ) * Fintype.card (Fin k ↪ Fin ℓ)) := by
    simp only [TGT, card_sigma, card_product, card_univ, Jp_eq_card_JpSet]
  have hemb := card_embedding_fin_le k ℓ
  calc ND.card ≤ TGT.card := hcard
    _ = _ := hTGT
    _ ≤ ∑ q ∈ P, Jp k ℓ M q hkl * (ℓ ^ k * ℓ ^ k) := by
      apply sum_le_sum
      intro q _
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hemb hemb)

/-- The degenerate solutions are at most `2 k^ℓ ℓ^k M^(ℓ + k - 1)`. -/
lemma card_deg_le (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) :
    ((solSet k ℓ M).filter
      (fun xy => ¬ (k ≤ (image xy.1 univ).card ∧ k ≤ (image xy.2 univ).card))).card ≤
      2 * k ^ ℓ * ℓ ^ k * M ^ (ℓ + k - 1) := by
  set DX := (tuples ℓ M).filter (fun x => (image x univ).card < k) with hDX
  have hsub : (solSet k ℓ M).filter
      (fun xy => ¬ (k ≤ (image xy.1 univ).card ∧ k ≤ (image xy.2 univ).card)) ⊆
      (DX ×ˢ tuples ℓ M) ∪ (tuples ℓ M ×ˢ DX) := by
    intro xy hxy
    simp only [solSet, mem_filter, mem_product] at hxy
    obtain ⟨⟨⟨hx1, hx2⟩, -⟩, hneg⟩ := hxy
    rw [mem_union, mem_product, mem_product, hDX, mem_filter, mem_filter]
    rcases not_and_or.mp hneg with h | h
    · exact Or.inl ⟨⟨hx1, not_le.mp h⟩, hx2⟩
    · exact Or.inr ⟨hx1, hx2, not_le.mp h⟩
  have hDXcard : DX.card ≤ k ^ ℓ * ℓ ^ k * M ^ (k - 1) := card_degenerate_tuples_le ℓ M k hk hkl
  calc _ ≤ ((DX ×ˢ tuples ℓ M) ∪ (tuples ℓ M ×ˢ DX)).card := card_le_card hsub
    _ ≤ (DX ×ˢ tuples ℓ M).card + (tuples ℓ M ×ˢ DX).card := card_union_le _ _
    _ = DX.card * M ^ ℓ + M ^ ℓ * DX.card := by rw [card_product, card_product, card_tuples]
    _ ≤ (k ^ ℓ * ℓ ^ k * M ^ (k - 1)) * M ^ ℓ + M ^ ℓ * (k ^ ℓ * ℓ ^ k * M ^ (k - 1)) := by
        gcongr
    _ = 2 * k ^ ℓ * ℓ ^ k * M ^ (ℓ + k - 1) := by
        have : M ^ (k - 1) * M ^ ℓ = M ^ (ℓ + k - 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [← this]
        ring

/-- Tao's Lemma 14 (prime selection), given a supply of more than `k ^ 3` primes in the range:
for one of them, `J ≤ |P| ℓ^{2k} J^{(p)} + 2 k^ℓ ℓ^k M^{ℓ+k-1}`. -/
theorem exists_prime_J_le_of_primes (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hM : 1 < M)
    (P : Finset ℕ) (hP_card : (k : ℝ) ^ 3 < P.card) (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_range : ∀ p ∈ P, (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧
      (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ))) :
    ∃ p ∈ P, (J k ℓ M : ℝ) ≤ (P.card : ℝ) * (ℓ : ℝ) ^ (2 * k) * Jp k ℓ M p hkl +
      2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1) := by
  have hP_card' : k ^ 3 < P.card := by exact_mod_cast hP_card
  have hP_gt : ∀ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ) := by
    intro p hp
    have h := (hP_range p hp).1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpos : 0 ≤ (M : ℝ) ^ (1 / (k : ℝ)) := by positivity
    nlinarith
  have hne : P.Nonempty := by
    rw [← card_pos]
    have : 0 < k ^ 3 := by positivity
    omega
  obtain ⟨p, hpP, hpmax⟩ := exists_max_image P (fun q => Jp k ℓ M q hkl) hne
  refine ⟨p, hpP, ?_⟩
  have hsplit := card_filter_add_card_filter_not (s := solSet k ℓ M)
    (p := fun xy => k ≤ (image xy.1 univ).card ∧ k ≤ (image xy.2 univ).card)
  have hND := card_nondeg_le k ℓ M hk hkl hM P hP_card' hP_prime hP_gt
  have hDeg := card_deg_le k ℓ M hk hkl
  have hsum : ∑ q ∈ P, Jp k ℓ M q hkl * (ℓ ^ k * ℓ ^ k) ≤
      P.card * ℓ ^ (2 * k) * Jp k ℓ M p hkl := by
    calc ∑ q ∈ P, Jp k ℓ M q hkl * (ℓ ^ k * ℓ ^ k)
        ≤ ∑ _q ∈ P, Jp k ℓ M p hkl * (ℓ ^ k * ℓ ^ k) := by
          apply sum_le_sum
          intro q hq
          exact Nat.mul_le_mul_right _ (hpmax q hq)
      _ = P.card * ℓ ^ (2 * k) * Jp k ℓ M p hkl := by
          rw [sum_const, smul_eq_mul, ← pow_add, ← two_mul]
          ring
  have hnat : J k ℓ M ≤ P.card * ℓ ^ (2 * k) * Jp k ℓ M p hkl +
      2 * k ^ ℓ * ℓ ^ k * M ^ (ℓ + k - 1) := by
    rw [J_eq_card_solSet, ← hsplit]
    exact Nat.add_le_add (hND.trans hsum) hDeg
  exact_mod_cast hnat

end Erdos1201.MR.Vinogradov
