/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingWords
import Categorification.WeightedKLR.RedStrands.BlockCrossingCut

/-!
# Every exchanged-top diagram is an ordinary stack

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8. For each top loading, choose PBW
words adapted to the bottom endpoints of the strands in its blocks. The upper pieces are
juxtaposed diagrams, with the ordered projector on their lower boundary. Cutting these
words, and then imposing the higher relations, gives surjectivity of the balanced stacking
map. This does not yet show independence of cuts in a linear relation.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MvPolynomial
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "F" => stackBlocks Q Λ L M f β h
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "E₀" => orderedIdem Q Λ botOrd Bs
local notation "rep" => orderedColumnRep Q Λ hQ L M f β h topOrd
local notation "stk" => crossingStack Q Λ hQ L M f β h
local notation "U" => LinearMap.range (LinearMap.restrictScalars k stk)

omit [DecidableEq I] in
private theorem localRedOrder (i : Seq μ) (hi : redWord i = κ₀) : ∀ B ∈ Bs, ∀ a b : Fin B.size,
    (∃ p q, i.lbl p = .inr (B.label a) ∧ i.lbl q = .inr (B.label b) ∧ p < q) → a < b := by
  intro B hB a b ⟨p,q,hp,hq,hpq⟩
  have hne : a ≠ b := by rintro rfl; exact hpq.ne (lbl_inj_of_inr i _ hp hq)
  rcases List.mem_append.1 hB with hB | hB
  · obtain ⟨s,_,rfl⟩ := List.mem_map.1 hB; exact (hne (Subsingleton.elim ..)).elim
  rcases List.mem_cons.1 hB with rfl | hB
  · change a < b
    by_contra! hab
    have hba : b < a := lt_of_le_of_ne hab hne.symm
    have ha2 : a.val < 2 := a.isLt
    have hb2 : b.val < 2 := b.isLt
    have ha : a = 1 := Fin.ext (by change (a : ℕ) = 1; omega)
    have hb : b = 0 := Fin.ext (by change (b : ℕ) = 0; omega)
    subst a; subst b
    exact hpq.not_gt (lt_of_redWord_eq_append hi hq hp)
  · obtain ⟨s,_,rfl⟩ := List.mem_map.1 hB; exact (hne (Subsingleton.elim ..)).elim

/-- Reduced representatives whose upper word is an ordered local diagram whenever the
end loadings match (Webster, proof of Lemma 6.8). -/
theorem exists_reduced_crossing_cut (s : Loadings Bs) (i : Seq μ) (hi : redWord i = κ₀) (w : Perm (Fin m)) :
    ∃ A D, (IsReduced m (A ++ D) ∧ wordProd m (A ++ D) = w) ∧
      (w • i = Seq.cast h (place Bs s) → ∃ x : diagrams Q Λ Bs, x*E₀ = x ∧
        F x = π (e (Seq.cast h (place Bs s)) * ψw A)) := by
  by_cases hw : w • i = Seq.cast h (place Bs s)
  swap
  · exact ⟨[],canWord m w,⟨isReduced_canWord _ _,wordProd_canWord _ _⟩,fun he => (hw he).elim⟩
  let rel := fun a b : Fin ℓ => ∃ p q, i.lbl p = .inr a ∧ i.lbl q = .inr b ∧ p < q
  have ho : OrderedBy (Seq.cast h (place Bs s)) (fun j => (w⁻¹ j).val) rel := by
    rw [← hw]; intro a b r r' hab ha hb
    exact ⟨_,_,ha,hb,hab⟩
  obtain ⟨A,hA,hv,x,hx,hX⟩ := exists_orderedBlock_word_cast Q Λ Bs h s w rel ho
    (localRedOrder L M f β i hi)
  let u := wordProd m A
  have hl : length m (u⁻¹ * w) + length m u = length m w := by
    have H := length_add_of_invSet_subset hv
    rw [inv_inv, ← length_inv (w⁻¹ * wordProd m A), mul_inv_rev, inv_inv, length_inv, length_inv] at H
    exact H
  let D := canWord m (u⁻¹ * w)
  have hD : wordProd m D = u⁻¹ * w := wordProd_canWord _ _
  have hprod : wordProd m (A ++ D) = w := by rw [wordProd_append,hD]; exact mul_inv_cancel_left u w
  refine ⟨A,D,⟨⟨validWord_append.2 ⟨hA.1, validWord_canWord _ _⟩,?_⟩,hprod⟩,
    fun _ => ⟨x,hx,congrArg π hX⟩⟩
  rw [List.length_append, hprod, hA.2, show D.length = length m (u⁻¹ * w) from length_canWord _ _, Nat.add_comm]; exact hl

private theorem loading_mem (s : Loadings Bs) (i : Seq μ) (hi : redWord i = κ₀) (z : R) :
    rep (π (e (Seq.cast h (place Bs s)) * z * e i)) ∈ U := by
  let t := Seq.cast h (place Bs s)
  choose A D hword hcut using exists_reduced_crossing_cut Q Λ L M f β h s i hi
  let ρ := fun w => A w ++ D w
  let G := (rep).comp (π).toLinearMap
  change e t * z * e i ∈ (U).comap G
  apply (show Submodule.span k _ ≤ (U).comap G from Submodule.span_le.2 ?_)
    (mem_span_corner' ρ hword i t (r := e t * z * e i) (by
      rw [← mul_assoc, ← mul_assoc, e_mul_self, mul_assoc _ (e i), e_mul_self]))
  rintro _ ⟨w,d,hw,rfl⟩
  obtain ⟨x,hx,hX⟩ := hcut w hw
  let y : R := ψw (D w) * pol (monomial d 1) * e i
  refine ⟨crossingCut Q Λ hQ L M f β h (x ⊗ₜ π y),?_⟩
  change stk _ = rep (π (ψw (ρ w) * pol (monomial d 1) * e i))
  rw [crossingStack_cut, ← map_mul F, hx, hX, ← map_mul]
  apply congrArg (fun a : R => rep (π a))
  have ht := e_mul_gen (Q := stendhalQ Q Λ) t (ρ w) (monomial d 1) i
  rw [(hword w).2, ← hw, inv_smul_smul, ite_eq_left rfl] at ht
  simpa only [hw,ρ,y,ψw_append,mul_assoc] using ht

private theorem sum_loadings {E : Type*} [AddCommMonoid E] [Module k E] (g : V →ₗ[k] E)
    (W : Submodule k E) (H : ∀ (s : Loadings Bs) (i : Seq μ), redWord i = κ₀ → ∀ w : R,
      g (π (e (Seq.cast h (place Bs s)) * w * e i)) ∈ W) (w : R) :
    g (F 1 * π (w * redIdem k Q Λ κ₀)) ∈ W := by
  let T := g.comp ((LinearMap.mulRight k (π (w * redIdem k Q Λ κ₀))).comp (LinearMap.ofClass F))
  change (1 : diagrams Q Λ Bs) ∈ W.comap T
  apply (show Submodule.span k _ ≤ W.comap T from Submodule.span_le.2 ?_) (one_mem_span_loadingIdem Q Λ Bs)
  rintro _ ⟨s,rfl⟩
  change g (F (loadingIdem Q Λ Bs s) * π (w * redIdem k Q Λ κ₀)) ∈ W
  rw [stackBlocks_loadingIdem, ← map_mul, ← mul_assoc]
  simp only [redIdem,Finset.mul_sum,map_sum]
  exact W.sum_mem fun i hi => H s i (Finset.mem_filter.1 hi).2 w

private theorem rep_project (w : R) : rep (F 1 * π (w * redIdem k Q Λ κ₀)) = rep (π w) := by
  apply Subtype.ext; apply Subtype.ext
  rw [orderedColumnRep_val, orderedColumnRep_val, map_mul π]
  let p := π (redIdem k Q Λ (ν := ν) κ₀)
  have hp : p*p = p := bottomIdempotent Q Λ L M f
  have H (u : diagrams Q Λ Bs) : F u * ((F 1 * (π w * p)) * p) = F u * (π w * p) := by
    rw [mul_assoc (F 1), mul_assoc (π w), hp, ← mul_assoc, ← map_mul, mul_one]
  exact congrArg _ (H _)

/-- **Surjectivity of ordinary stacking** (Webster, arXiv:1309.3796v2, proof of Lemma 6.8).
Every exchanged-top column class is a sum of stacks over the uncrossed block algebra.
No choice of a preimage is asserted to respect the quotient relations. -/
theorem crossingStack_surjective : Function.Surjective stk := by
  intro z
  obtain ⟨y,rfl⟩ := orderedColumnRep_surjective Q Λ hQ L M f β h topOrd z
  obtain ⟨w,rfl⟩ := (show Function.Surjective π from violMk_surjective.comp ofKLR_surjective) y
  change rep (π w) ∈ U
  rw [← rep_project Q Λ hQ L M f β h]
  exact sum_loadings Q Λ L M f β h rep U (loading_mem Q Λ hQ L M f β h) w

end Categorification.Stendhal.RedBlock
