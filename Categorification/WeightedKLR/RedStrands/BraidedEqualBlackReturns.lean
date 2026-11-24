/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExitPolynomialMatrix
import Categorification.WeightedKLR.RedStrands.BraidedStendhal

/-!
# Equal-black return relations after killing red dots

For the two-black interval in the proof of Webster, arXiv:1309.3796v2, §6.1,
Lemma 6.8 after (6.21), the ordinary and reversed-middle arms at the right
extreme yield a coupled polynomial relation. In the braided Stendhal algebra,
substituting zero for dots on red strands gives the same two polynomial rows as
in the affine KLR algebra. This calculation precedes the higher-cut ideal.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "B" => BraidedStendhalAlgebra k Q Λ ν
local notation "P" => MvPolynomial (Fin m) k
local notation "π" => ofKLR k Q Λ ν
local notation "T" => toKLR k Q Λ ν

/-- The braided Stendhal basis with only black dots is fixed by first taking
the KLR representative and then killing red dots. -/
theorem ofKLR_toKLR (hQ : KLRSymm Q) (x : B) : π (T x) = x := by
  let rep := TypeA.canWord m
  have hrep t : IsReduced m (rep t) ∧ wordProd m (rep t) = t :=
    ⟨isReduced_canWord m t, wordProd_canWord m t⟩
  have eq : (π).toLinearMap.comp (T).toLinearMap = LinearMap.id := by
    apply (basis hQ rep hrep).ext
    intro b
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply, basis_apply,
      toKLR_ofKLR_std _ _ _ b.2]
  exact LinearMap.congr_fun eq x

private theorem section_word (s : Seq μ) (l : List ℕ) (f : P) :
    T (π (KLR.KLRAlgebra.pol f * (KLR.KLRAlgebra.ψw l * KLR.KLRAlgebra.e s))) =
      KLR.KLRAlgebra.pol (KLRAlgebra.blackSubst (wordProd m l • s) f) *
        (KLR.KLRAlgebra.ψw l * KLR.KLRAlgebra.e s) := by
  let y : R := KLR.KLRAlgebra.ψw l * KLR.KLRAlgebra.e s
  let r := wordProd m l • s
  have hr : KLR.KLRAlgebra.e r * y = y := by
    dsimp only [r, y]
    rw [← mul_assoc, KLR.KLRAlgebra.e_mul_ψw, inv_smul_smul, mul_assoc, KLR.KLRAlgebra.e_mul_self]
  have hy : T (π y) = y := by simp only [y, map_mul, toKLR_ofKLR_ψw, toKLR_ofKLR_e]
  change T (π (KLR.KLRAlgebra.pol f * y)) = _ * y
  calc
    _ = T (π ((KLR.KLRAlgebra.pol f * KLR.KLRAlgebra.e r) * y)) := by rw [mul_assoc, hr]
    _ = _ := by rw [map_mul, map_mul, toKLR_ofKLR_pol_mul_e, hy, mul_assoc, hr]

open KLR.KLRAlgebra in
/-- In the braided Stendhal algebra the two-black return relations are exactly
the multiples of `(∂q, -q, s(q))` after setting red dots to zero. The red at `b`
has weight `Λ r i`; the two black strands to its right both have colour `i`.
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem equalBlack_return_kernel (hQ : KLRSymm Q) (s : Seq μ) (l : List ℕ)
    (b : ℕ) (hb : b + 2 < m) (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (r : Fin ℓ) (i : I)
    (hr : (wordProd m l • s).lbl ⟨b, by omega⟩ = Sum.inr r)
    (hi : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = Sum.inl i)
    (hi' : (wordProd m l • s).lbl ⟨b + 2, hb⟩ = Sum.inl i) (f g h : P) :
    let j := b + 1
    let n := Λ r i
    let black := KLRAlgebra.blackSubst (wordProd m l • s) (k := k)
    π (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s)) = 0 ↔
      ∃ z : P, black f = z * NilHecke.dd k m j (X (⟨j, by omega⟩ : Fin m) ^ n) ∧
        black g = -(z * X (⟨j, by omega⟩ : Fin m) ^ n) ∧
        black h = z * X (⟨j + 1, hb⟩ : Fin m) ^ n := by
  intro j n black
  let t := wordProd m l • s
  have he : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, hb⟩ := hi.trans hi'.symm
  have fix := sadj_smul_eq_self hb he
  have fix₂ (d : ℕ) (t' : Seq μ) : sadj m d • (sadj m d • t') = t' := by
    rw [← mul_smul, TypeA.sadj_mul_self, one_smul]
  have t₀ : wordProd m (b :: b :: l) • s = t := by simp only [wordProd_cons, mul_smul, fix₂, t]
  have t₁ : wordProd m (j :: b :: b :: l) • s = t := by rw [wordProd_cons, mul_smul, t₀, fix]
  have t₂ : wordProd m (b :: b :: j :: l) • s = t := by
    simpa only [wordProd_cons, mul_smul, fix₂] using fix
  have q : exitSquarePolynomial (stendhalQ Q Λ) t b (by omega) = X (⟨j, by omega⟩ : Fin m) ^ n := by
    unfold exitSquarePolynomial
    dsimp only
    rw [hr, hi, ite_eq_right Sum.inr_ne_inl, stendhalQ_inr_inl, map_pow, rename_X]
    rfl
  let x : R := pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
    pol h * (ψw (b :: b :: j :: l) * e s)
  have iff₀ : π x = 0 ↔ T (π x) = 0 := ⟨fun h => by rw [h, map_zero], fun h => by
    simpa only [ofKLR_toKLR hQ, map_zero] using congrArg π h⟩
  change π x = 0 ↔ _
  rw [iff₀]
  simp only [x, map_add, section_word, t₀, t₁, t₂]
  exact KLR.KLRAlgebra.equalBlack_return_kernel (stendhalQ_symm Q Λ hQ) s l b j n (by omega) hb hl hjl he q
    (black f) (black g) (black h)

open KLR.KLRAlgebra in
/-- The additional ideal data for the same calculation modulo a higher ideal
`J`. If membership on the two PBW rows is componentwise membership in coefficient
ideals `H₀`, `H₁`, the return relation is given by the two row polynomials modulo
those ideals. This is a sufficient hypothesis prior to the marked lifting step
of Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem equalBlack_return_mem_iff (s : Seq μ) (l : List ℕ) (b j : ℕ)
    (hb : b + 1 < m) (hj : j + 1 < m)
    (he : (wordProd m l • s).lbl ⟨j, by omega⟩ = (wordProd m l • s).lbl ⟨j + 1, hj⟩)
    (J : TwoSidedIdeal B) (H₀ H₁ : Ideal P)
    (rows : ∀ F G : P, π (pol F * (ψw l * e s) + pol G * (ψw (j :: l) * e s)) ∈ J ↔
      F ∈ H₀ ∧ G ∈ H₁) (f g h : P) :
    let q := exitSquarePolynomial (stendhalQ Q Λ) (wordProd m l • s) b hb
    π (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw (j :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: j :: l) * e s)) ∈ J ↔
      f * q + g * NilHecke.dd k m j q ∈ H₀ ∧ g * swapPol j hj q + h * q ∈ H₁ := by
  intro q
  have expansion := equalBlack_return_expansion (Q := stendhalQ Q Λ) s l b j hb hj he f g h
  dsimp only at expansion
  rw [expansion]
  exact rows _ _

open KLR.KLRAlgebra in
/-- For the standard red parameters, a relation among the three return columns
in the braided Stendhal algebra has a single full-joint coefficient whose two
components are the signed ordinary and reversed-middle upper coefficients.
Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21), before the
higher ideal. -/
theorem exists_equalBlack_cycle_coefficient (hQ : KLRSymm Q) (s : Seq μ) (l : List ℕ)
    (b : ℕ) (hb : b + 2 < m) (hl : IsReduced m l) (hjl : IsReduced m ((b + 1) :: l))
    (r : Fin ℓ) (i : I)
    (hr : (wordProd m l • s).lbl ⟨b, by omega⟩ = Sum.inr r)
    (hi : (wordProd m l • s).lbl ⟨b + 1, by omega⟩ = Sum.inl i)
    (hi' : (wordProd m l • s).lbl ⟨b + 2, hb⟩ = Sum.inl i) (f g h : P)
    (relation : π (pol f * (ψw (b :: b :: l) * e s) + pol g * (ψw ((b + 1) :: b :: b :: l) * e s) +
      pol h * (ψw (b :: b :: (b + 1) :: l) * e s)) = 0) :
    let t := sadj m b • (wordProd m l • s)
    let j := b + 1
    ∃ c : B, c * π (e (sadj m j • t)) = c ∧
      c * π (ψw [b, j] * e t) = -π (pol f * (ψw [b] * e t) + pol g * (ψw [j, b] * e t)) ∧
      c * π (ψw [j] * e t) = π (pol h * (ψw [b] * e t)) := by
  intro t j
  let top := wordProd m l • s
  let black := KLRAlgebra.blackSubst (k := k) top
  have he : top.lbl ⟨j, by omega⟩ = top.lbl ⟨j + 1, hb⟩ := hi.trans hi'.symm
  have hn : top.lbl ⟨b, by omega⟩ ≠ top.lbl ⟨j, by omega⟩ := by rw [hr, hi]; exact Sum.inr_ne_inl
  have hw : stendhalQ Q Λ (top.lbl ⟨b, by omega⟩) (top.lbl ⟨j, by omega⟩) = X 1 ^ Λ r i := by
    rw [hr, hi, stendhalQ_inr_inl]
  have q : exitSquarePolynomial (stendhalQ Q Λ) top b (by omega) = X (⟨j, by omega⟩ : Fin m) ^ Λ r i := by
    unfold exitSquarePolynomial
    dsimp only
    rw [ite_eq_right hn, hw, map_pow, rename_X]
    rfl
  have coefficients := (BraidedStendhalAlgebra.equalBlack_return_kernel hQ s l b hb hl hjl r i hr hi hi' f g h).mp relation
  have affineRelation := (KLR.KLRAlgebra.equalBlack_return_kernel (stendhalQ_symm Q Λ hQ) s l b j (Λ r i)
    (by omega) hb hl hjl he q (black f) (black g) (black h)).mpr coefficients
  obtain ⟨c, fixed, Barm, Darm⟩ := KLR.KLRAlgebra.exists_equalBlack_cycle_coefficient (stendhalQ_symm Q Λ hQ)
    s l b (Λ r i) hb hl hjl he hn hw (black f) (black g) (black h) affineRelation
  have tb : wordProd m [b] • t = top := by
    simp only [wordProd_cons, wordProd_nil, mul_one]
    exact sadj_smul_smul b top
  have tjb : wordProd m [j, b] • t = top := by
    rw [wordProd_cons, mul_smul, tb, sadj_smul_eq_self hb he]
  have subst (w : List ℕ) (hw : wordProd m w • t = top) (u : P) :
      π (pol (black u) * (ψw w * e t)) = π (pol u * (ψw w * e t)) := by
    have lift := section_word (Q := Q) (Λ := Λ) t w u
    rw [hw] at lift
    exact (congrArg π lift.symm).trans (ofKLR_toKLR hQ _)
  refine ⟨π c, ?_, ?_, ?_⟩
  · exact (map_mul π _ _).symm.trans (congrArg π fixed)
  · rw [← map_mul, Barm, map_neg, map_add, subst [b] tb, subst [j, b] tjb, ← map_add]
  · rw [← map_mul, Darm, subst [b] tb]

end Categorification.Stendhal.BraidedStendhalAlgebra
end
