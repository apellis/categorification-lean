/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedParabolicLift

/-!
# Maps out of the last red strand followed by black strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. The block `λ_{ℓ+1} β` of one red strand followed by black strands carries the
quotient map `P₂` onto the cyclotomic quotient `R^{λ_{ℓ+1}}_β` (violated idempotents and red dots
die, and the black diagrams act through the cyclotomic quotient). This file proves the universal
property of `P₂` among multiplicative maps: a multiplicative linear map `G` killing violated
idempotents and red dots, and whose restriction to black diagrams kills the cyclotomic relations,
factors through `P₂`.

## Main results

* `lastRedBlack_hom_ext`: two such maps agreeing on black diagrams agree.
* `exists_lastRedBlack_factor`: the factorization through `P₂`.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (β : Multiset I)
local notation "S" => stendhalQ Q Λ
local notation "rₗ" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
local notation "B₀" => Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β
local notation "K" => KLRAlgebra k S (rₗ + B₀)
local notation "hB" => lastRedBlackWeight (ℓ := ℓ) β
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
local notation "R" => CycKLR k Q λf β
local notation "P₂" => parabolicLastCyclotomic Q Λ β

variable {C : Type*} [Ring C] [Algebra k C]

omit [DecidableEq I] in
private theorem violated_cast {X Y : Multiset (I ⊕ Fin (ℓ+1))} (hμ : X = Y) {t : Seq X}
    (ht : IsViolated t) : IsViolated (Seq.cast hμ t) := by
  subst hμ; exact ht

omit [DecidableEq I] in
private theorem seq_terminal_subsingleton : Subsingleton (Seq rₗ) :=
  ⟨fun s t => Subtype.ext (funext fun a => by
    rw [Multiset.mem_singleton.1 (s.mem a), Multiset.mem_singleton.1 (t.mem a)])⟩

private theorem e_terminal (a : Seq rₗ) : (e a : KLRAlgebra k S rₗ) = 1 := by
  have := seq_terminal_subsingleton (I := I) (ℓ := ℓ)
  rw [← sum_e, Fintype.sum_subsingleton _ a]

omit [DecidableEq I] in
private theorem terminal_first (t : Seq (rₗ + B₀)) (ht : ¬ IsViolated t)
    (c : Fin (rₗ + B₀).card) (hc : c.val = 0) : t.1 c = .inr (Fin.last ℓ) := by
  have hpos : 0 < (rₗ + B₀).card := hc ▸ c.2
  have hr : ¬ (t.lbl ⟨0, hpos⟩).isLeft := fun hl => ht ⟨hpos, hl⟩
  have hceq : c = ⟨0, hpos⟩ := Fin.ext hc
  rcases Multiset.mem_add.1 (t.mem c) with h1 | h1
  · exact Multiset.mem_singleton.1 h1
  · obtain ⟨z, _, hz⟩ := Multiset.mem_map.1 h1
    subst hceq
    rw [Seq.lbl, ← hz] at hr
    simp at hr

omit [DecidableEq I] in
private theorem split_unviolated (t : Seq (rₗ + B₀)) (ht : ¬ IsViolated t) :
    ∃ (a : Seq rₗ) (b : Seq B₀), a.append b = t := by
  have hX : Finset.univ.val.map (t.1 ∘ Seq.posL B₀) = rₗ := by
    have hrep : Finset.univ.val.map (t.1 ∘ Seq.posL B₀) =
        Multiset.replicate 1 (Sum.inr (Fin.last ℓ)) := by
      refine Multiset.eq_replicate.2 ⟨by simp, fun b hb => ?_⟩
      obtain ⟨c, _, rfl⟩ := Multiset.mem_map.1 hb
      have hc : c.val = 0 := by have := c.2; simp at this; omega
      exact terminal_first β t ht _ hc
    simpa using hrep
  have key : ∀ f : Fin (Multiset.card (rₗ + B₀)) → I ⊕ Fin (ℓ+1), Finset.univ.val.map f =
      Finset.univ.val.map (f ∘ Seq.posL B₀) + Finset.univ.val.map (f ∘ Seq.posR rₗ) := by
    intro f
    conv_lhs => rw [← Multiset.map_univ_val_equiv (TypeA.blockEquiv (Seq.card_add' rₗ B₀))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hmap := key t.1
  rw [t.2, hX] at hmap
  refine ⟨⟨t.1 ∘ Seq.posL B₀, hX⟩, ⟨t.1 ∘ Seq.posR rₗ, (add_left_cancel hmap).symm⟩, ?_⟩
  apply Subtype.ext; funext a
  obtain ⟨c, rfl⟩ := (TypeA.blockEquiv (Seq.card_add' rₗ B₀)).surjective a
  cases c with
  | inl x => exact Seq.append_posL _ _ x
  | inr y => exact Seq.append_posR _ _ y

private theorem concat_one_tmul_x_mul {X Y : Multiset (I ⊕ Fin (ℓ+1))} (b : Fin Y.card)
    (t : Seq Y) :
    concat S X Y (1 ⊗ₜ (x b * e t)) = x (Seq.posR X b) * concat S X Y (1 ⊗ₜ e t) := by
  rw [show (1 : KLRAlgebra k S X) ⊗ₜ[k] (x b * e t) =
      ((1 : KLRAlgebra k S X) ⊗ₜ[k] (x b : KLRAlgebra k S Y)) * (1 ⊗ₜ[k] e t) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
    concat_mul, concat_one_tmul_x, mul_assoc, oneConcat_mul_concat]

private theorem concat_one_tmul_ψ_mul {X Y : Multiset (I ⊕ Fin (ℓ+1))} {j : ℕ}
    (hj : j + 1 < Y.card) (t : Seq Y) :
    concat S X Y (1 ⊗ₜ (ψ j * e t)) = ψ (X.card + j) * concat S X Y (1 ⊗ₜ e t) := by
  rw [show (1 : KLRAlgebra k S X) ⊗ₜ[k] (ψ j * e t) =
      ((1 : KLRAlgebra k S X) ⊗ₜ[k] (ψ j : KLRAlgebra k S Y)) * (1 ⊗ₜ[k] e t) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
    concat_mul, concat_one_tmul_ψ hj, mul_assoc, oneConcat_mul_concat]

section Ext

variable {Q Λ β}
variable (G H : KLRAlgebra k (stendhalQ Q Λ) (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β) →ₙₐ[k] C)
  (hG : ∀ t : Seq (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β), IsViolated t → G (e t) = 0)
  (hH : ∀ t : Seq (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β), IsViolated t → H (e t) = 0)
  (hGx : ∀ (a : Fin (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β).card)
    (t : Seq (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β)), (t.1 a).isRight → G (x a * e t) = 0)
  (hHx : ∀ (a : Fin (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β).card)
    (t : Seq (({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
    + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β)), (t.1 a).isRight → H (x a * e t) = 0)
  (hc : ∀ w : KLRAlgebra k (stendhalQ Q Λ) (Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β),
    G (concat (stendhalQ Q Λ) ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
      (Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β) (1 ⊗ₜ w)) =
    H (concat (stendhalQ Q Λ) ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
      (Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β) (1 ⊗ₜ w)))
include hG hH hc

private theorem ext_e (t : Seq (rₗ + B₀)) : G (e t) = H (e t) := by
  by_cases ht : IsViolated t
  · rw [hG t ht, hH t ht]
  · obtain ⟨a, b, rfl⟩ := split_unviolated β t ht
    rw [← concat_e_tmul_e, e_terminal]
    exact hc (e b)

omit hc in
private theorem ext_violated (z : K) (t : Seq (rₗ + B₀)) (ht : IsViolated t) :
    G (z * e t) = H (z * e t) := by
  rw [show z * e t = z * e t * e t by rw [mul_assoc, e_mul_self], map_mul G, map_mul H,
    hG t ht, hH t ht, mul_zero, mul_zero]

include hGx hHx in
private theorem ext_x (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀)) :
    G (x a * e t) = H (x a * e t) := by
  by_cases hr : (t.1 a).isRight
  · rw [hGx a t hr, hHx a t hr]
  by_cases ht : IsViolated t
  · exact ext_violated G H hG hH _ t ht
  have ha0 : a.val ≠ 0 := fun h0 => hr (by rw [terminal_first β t ht a h0]; rfl)
  obtain ⟨a₀, b, rfl⟩ := split_unviolated β t ht
  have := seq_terminal_subsingleton (I := I) (ℓ := ℓ)
  have hlt : a.val - 1 < (B₀).card := by have := a.2; simp at this ⊢; omega
  have hpa : Seq.posR rₗ (⟨a.val - 1, hlt⟩ : Fin (B₀).card) = a := Fin.ext (by simp; omega)
  have hxe : x a * e (a₀.append b) = concat S rₗ B₀ (1 ⊗ₜ (x ⟨a.val - 1, hlt⟩ * e b)) := by
    rw [concat_one_tmul_x_mul, concat_one_tmul_e, hpa, Fintype.sum_subsingleton _ a₀]
  rw [hxe]
  exact hc _

private theorem ext_ψ (j : ℕ) (t : Seq (rₗ + B₀)) :
    G (ψ j * e t) = H (ψ j * e t) := by
  by_cases hj : j + 1 < (rₗ + B₀).card
  swap
  · rw [ψ_eq_zero j (by omega), zero_mul, map_zero, map_zero]
  by_cases ht : IsViolated t
  · exact ext_violated G H hG hH _ t ht
  obtain ⟨a₀, b, rfl⟩ := split_unviolated β t ht
  have := seq_terminal_subsingleton (I := I) (ℓ := ℓ)
  rcases j with _ | j
  · have hb : 0 < (B₀).card := by simp at hj ⊢; omega
    have hs : IsViolated (TypeA.sadj (rₗ + B₀).card 0 • a₀.append b) := by
      refine ⟨by omega, ?_⟩
      rw [lbl_sadj_left hj]
      have h1 : (⟨1, hj⟩ : Fin (rₗ + B₀).card) = Seq.posR rₗ ⟨0, hb⟩ := Fin.ext (by simp)
      rw [Seq.lbl, h1, Seq.append_posR]
      obtain ⟨z, _, hz⟩ := Multiset.mem_map.1 (b.mem ⟨0, hb⟩)
      rw [← hz]; rfl
    rw [ψ_mul_e, map_mul, map_mul, hG _ hs, hH _ hs, zero_mul, zero_mul]
  · have hj' : j + 1 < (B₀).card := by simp at hj ⊢; omega
    have hψe : ψ (j + 1) * e (a₀.append b) = concat S rₗ B₀ (1 ⊗ₜ (ψ j * e b)) := by
      rw [concat_one_tmul_ψ_mul Q Λ hj', concat_one_tmul_e, Fintype.sum_subsingleton _ a₀,
        show Multiset.card rₗ + j = j + 1 by simp [Nat.add_comm]]
    rw [hψe]
    exact hc _

include hGx hHx in
private theorem ext_mul_e (z : K) : ∀ t : Seq (rₗ + B₀), G (z * e t) = H (z * e t) := by
  induction z using KLRAlgebra.klr_induction with
  | hadd u v hu hv => intro t; rw [add_mul, map_add, map_add, hu, hv]
  | hmul u v hu hv =>
    intro t
    have hs : u * v * e t = ∑ s, u * e s * (v * e t) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_e, mul_one, mul_assoc]
    rw [hs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [map_mul G, map_mul H, hu, hv]
  | hr r =>
    intro t
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul,
      ext_e G H hG hH hc t]
  | he s =>
    intro t
    rw [e_mul_e]
    split_ifs
    · exact ext_e G H hG hH hc s
    · rw [map_zero, map_zero]
  | hx a => exact ext_x G H hG hH hGx hHx hc a
  | hψ a => exact ext_ψ G H hG hH hc a

include hGx hHx in
/-- Two multiplicative maps out of the block `λ_{ℓ+1} β` that kill violated idempotents and red
dots, and agree on the black diagrams, are equal. -/
theorem lastRedBlack_hom_ext : G = H := by
  ext z
  rw [← mul_one z, ← sum_e, Finset.mul_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun t _ => ext_mul_e G H hG hH hGx hHx hc z t

end Ext

private theorem lastCyc_e_violated (t : Seq (rₗ + B₀)) (ht : IsViolated t) :
    P₂ (castKLR S hB (e t)) = 0 := by
  rw [castKLR_e, parabolicLastCyclotomic, AlgHom.comp_apply,
    parabolicLastProjection_e_violated _ _ _ _ (violated_cast hB ht), map_zero]

private theorem lastCyc_red_dot (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀))
    (hr : (t.1 a).isRight) : P₂ (castKLR S hB (x a * e t)) = 0 := by
  rw [map_mul, castKLR_x, castKLR_e, parabolicLastCyclotomic, AlgHom.comp_apply,
    parabolicLastProjection_red_dot _ _ _ _ _
      (by rw [Seq.lbl, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self]; exact hr), map_zero]

private def descendSurjective {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (g : A →ₙₐ[k] C) (h : ∀ x y, f x = f y → g x = g y) : B →ₙₐ[k] C := by
  let φ := fun z => g (Function.surjInv hf z)
  have hcomp (z : A) : φ (f z) = g z := h _ _ (Function.surjInv_eq hf _)
  exact {
    toFun := φ
    map_zero' := by rw [← map_zero f, hcomp, map_zero]
    map_add' := by
      intro x y
      obtain ⟨a,rfl⟩ := hf x
      obtain ⟨b,rfl⟩ := hf y
      rw [← map_add, hcomp, hcomp, hcomp, map_add]
    map_mul' := by
      intro x y
      obtain ⟨a,rfl⟩ := hf x
      obtain ⟨b,rfl⟩ := hf y
      rw [← map_mul, hcomp, hcomp, hcomp, map_mul]
    map_smul' := by
      intro c x
      obtain ⟨a,rfl⟩ := hf x
      rw [← map_smul, hcomp, hcomp, map_smul]
      rfl }

private theorem descendSurjective_apply {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (g : A →ₙₐ[k] C) (h : ∀ x y, f x = f y → g x = g y) (z : A) :
    descendSurjective f hf g h (f z) = g z := h _ _ (Function.surjInv_eq hf _)

variable {Q Λ β}

/-- The black diagrams acting through `G` by juxtaposition after the last red strand. -/
private def blackPart (G : K →ₙₐ[k] C) : KLRAlgebra k Q β →ₙₐ[k] C where
  toFun y := G (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β y))
  map_zero' := by rw [map_zero, TensorProduct.tmul_zero, map_zero, map_zero]
  map_add' y z := by rw [map_add, TensorProduct.tmul_add, map_add, map_add]
  map_mul' y z := by
    rw [← map_mul G, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
  map_smul' c y := by
    rw [map_smul, TensorProduct.tmul_smul, map_smul, map_smul]; rfl

/-- **Universal property of the last cyclotomic quotient.** A multiplicative linear map out of
the block `λ_{ℓ+1} β` which kills violated idempotents and red dots, and whose black part kills
the cyclotomic relations `x_1^{λ_{ℓ+1}^{i}} e(i …)`, factors through `P₂`. -/
theorem exists_lastRedBlack_factor (G : K →ₙₐ[k] C)
    (hG : ∀ t : Seq (rₗ + B₀), IsViolated t → G (e t) = 0)
    (hGx : ∀ (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀)), (t.1 a).isRight → G (x a * e t) = 0)
    (hcyc : ∀ b : Seq β,
      G (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β (cycElt Q λf b))) = 0) :
    ∃ G' : R →ₙₐ[k] C, ∀ z, G z = G' (P₂ (castKLR S hB z)) := by
  classical
  have hker : cycIdeal Q λf β ≤ TwoSidedIdeal.ker (blackPart G) := by
    apply TwoSidedIdeal.span_le.2
    rintro _ ⟨b, rfl⟩
    exact (TwoSidedIdeal.mem_ker _).2 (hcyc b)
  let G' : R →ₙₐ[k] C := descendSurjective (CycKLR.mk k Q λf β) CycKLR.mk_surjective
    (blackPart G) (fun x y hxy => sub_eq_zero.mp (by
      rw [← map_sub]
      exact (TwoSidedIdeal.mem_ker _).1 (hker ((CycKLR.mk_eq_mk_iff x y).1 hxy))))
  refine ⟨G', fun z => ?_⟩
  let H : K →ₙₐ[k] C := G'.comp
    ((P₂).comp (castKLR S hB).toAlgHom).toNonUnitalAlgHom
  have hHe : ∀ t : Seq (rₗ + B₀), IsViolated t → H (e t) = 0 := fun t ht => by
    change G' (P₂ (castKLR S hB (e t))) = 0
    rw [lastCyc_e_violated Q Λ β t ht, map_zero]
  have hHx : ∀ (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀)), (t.1 a).isRight →
      H (x a * e t) = 0 := fun a t hr => by
    change G' (P₂ (castKLR S hB (x a * e t))) = 0
    rw [lastCyc_red_dot Q Λ β a t hr, map_zero]
  have hc : ∀ w : KLRAlgebra k S B₀,
      G (concat S rₗ B₀ (1 ⊗ₜ w)) = H (concat S rₗ B₀ (1 ⊗ₜ w)) := fun w => by
    obtain ⟨v, rfl⟩ := (blackSuffixReindex Q Λ β).surjective w
    change blackPart G v = G' (P₂ (castKLR S hB _))
    have hcb := parabolicLastCyclotomic_concat_black Q Λ β v
    change P₂ (castKLR S hB (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β v))) =
      CycKLR.mk k Q λf β v at hcb
    rw [hcb]
    exact (descendSurjective_apply _ _ _ _ v).symm
  exact congrArg (fun F : K →ₙₐ[k] C => F z) (lastRedBlack_hom_ext G H hG hHe hGx hHx hc)

end Categorification.Stendhal
