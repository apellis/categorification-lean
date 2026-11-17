/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayer
import Categorification.KLR.Reindex

/-!
# The cyclotomic relation in the last-red layer

Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.37 and Theorem 4.38.
After quotienting by diagrams through smaller right-hand blocks, the pure
black suffix satisfies the cyclotomic relation for the last red weight.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) {ν : Multiset I}
local notation "M" => stendhalWeight (ℓ+1) ν
local notation "S" => stendhalQ Q Λ
local notation "n" => Multiset.card M
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν
local notation "τ" => TensorProductAlgebra.mk Q Λ ν

/-- Map from all red orders to the layer quotient at position `p`. -/
def lastRedLayerProjection (p : Fin n) :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] (smallerSuffixIdeal Q Λ p).ringCon.Quotient :=
  ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k).comp ((τ).comp (orderProjection Q Λ ν))

/-- In the quotient by smaller suffixes the boundary next to the last red
satisfies the monomial cyclotomic relation of its weight. -/
theorem lastRedLayerProjection_dot_pow (p : Fin n) (s : Seq M) (hj : p.val+1<n)
    (i : I) (hr : s.lbl p = .inr (Fin.last ℓ)) (hi : s.lbl ⟨p.val+1,hj⟩ = .inl i) :
    lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.x ⟨p.val+1,hj⟩ ^ Λ (Fin.last ℓ) i *
      StendhalAlgebraAllOrders.e s) = 0 := by
  classical
  let t := TypeA.sadj n p.val • s
  have hz : lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.e t) = 0 := by
    by_cases ht : IsRedOrdered t
    · have he : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e t) = StendhalAlgebra.e t ht :=
        Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem t).trans (ite_eq_left ht))
      change (smallerSuffixIdeal Q Λ p).ringCon.mk' (τ (orderProjection Q Λ ν _)) = 0
      rw [he, ← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      exact TwoSidedIdeal.subset_span ⟨t,ht,⟨p.val+1,hj⟩,Nat.lt_succ_self _, by
        change (TypeA.sadj n p.val • s).lbl _ = _
        rwa [KLRAlgebra.lbl_sadj_right hj],rfl⟩
    · have he : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e t) = 0 := by
        apply Subtype.ext
        exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem t).trans (ite_eq_right ht)
      simp [lastRedLayerProjection, he]
  rw [lastRed_dot_pow_factor Q Λ s p.val hj i hr hi, map_mul, map_mul, hz, mul_zero, zero_mul]

private theorem concat_e_tmul_x_pow_e {J : Type*} [DecidableEq J]
    (P : J → J → MvPolynomial (Fin 2) k) {α β : Multiset J} (a : Seq α) (b : Seq β)
    (z : Fin β.card) (d : ℕ) :
    concat P α β (e a ⊗ₜ (x z ^ d * e b)) = x (Seq.posR α z) ^ d * e (a.append b) := by
  simpa [ψw,TypeA.shiftWord,pol_X] using concat_pol_ψw_e (Q := P) (1 : MvPolynomial _ k)
    (MvPolynomial.X z ^ d) (α := []) (α' := []) (by simp) (by simp) a b

local notation "ι" => (Sum.inl : I → I ⊕ Fin (ℓ+1))
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)

/-- Relabel an ordinary black diagram by the black summand of the augmented labels. -/
def blackSuffixReindex (β : Multiset I) : KLRAlgebra k Q β ≃ₐ[k] KLRAlgebra k S (β.map ι) :=
  reindexEquiv Sum.inl_injective S β

/-- Each defining generator of the final-weight cyclotomic ideal dies under
juxtaposition with a left boundary ending in the last red. -/
theorem suffixConcat_cycElt (p : Fin n) {α : Multiset (I ⊕ Fin (ℓ+1))} {β : Multiset I}
    (h : α + β.map ι = M) (ha : α.card = p.val+1) (a : Seq α)
    (hr : a.lbl ⟨p.val,by omega⟩ = .inr (Fin.last ℓ)) (b : Seq β) :
    suffixConcat Q Λ p h (e a ⊗ₜ blackSuffixReindex Q Λ β (cycElt Q λf b)) = 0 := by
  by_cases hb : 0 < β.card
  · let z : Fin β.card := ⟨0,hb⟩
    let s := Seq.cast h (a.append (Seq.map ι b))
    let c : Fin n := Fin.cast (congrArg Multiset.card h)
      (Seq.posR α (Fin.cast (Multiset.card_map ι β).symm z))
    have hc : c.val = p.val+1 := by simp [c, z, ha]
    have hp : p.val + 1 < n := hc ▸ c.isLt
    have hs : s.lbl p = .inr (Fin.last ℓ) := by
      change (Seq.cast h _).1 p = _
      rw [Seq.cast_apply, Seq.append_apply_lt _ _ _ (by change p.val < α.card; omega)]
      exact hr
    have hi : s.lbl c = .inl (b.lbl z) := by
      change (Seq.cast h _).1 c = _
      simp only [Seq.cast_apply, c, Fin.cast_cast, Fin.cast_eq_self]
      exact (Seq.append_posR a (Seq.map ι b) _).trans (by simp [Seq.map_lbl])
    have H := lastRedLayerProjection_dot_pow Q Λ p s hp (b.lbl z) hs
      (show s.lbl ⟨p.val+1,hp⟩ = .inl (b.lbl z) by rwa [← (Fin.ext hc : c = ⟨_,hp⟩)])
    have H' : lastRedLayerProjection Q Λ p (π (x c ^ Λ (Fin.last ℓ) (b.lbl z) * e s)) = 0 := by
      rw [map_mul, map_pow, show c = ⟨_,hp⟩ from Fin.ext hc]
      exact H
    change lastRedLayerProjection Q Λ p (π (castKLR S h (concat S α (β.map ι) _))) = 0
    have hx : blackSuffixReindex Q Λ β (x z) = x (Fin.cast (Multiset.card_map ι β).symm z) :=
      reindexEquiv_x _ z
    have he : blackSuffixReindex Q Λ β (e b) = e (Seq.map ι b) := reindexEquiv_e _ b
    rw [cycElt_of_pos _ _ _ hb, map_pow, Polynomial.aeval_X, map_mul, map_pow, hx,
      he, concat_e_tmul_x_pow_e, map_mul, map_pow, castKLR_x, castKLR_e]
    exact H'
  · rw [cycElt, dite_eq_right hb, map_zero, TensorProduct.tmul_zero, map_zero]


theorem suffixConcat_mul (p : Fin n) {α β : Multiset (I ⊕ Fin (ℓ+1))}
    (h : α+β=M) (u v : KLRAlgebra k S α ⊗[k] KLRAlgebra k S β) :
    suffixConcat Q Λ p h (u*v) = suffixConcat Q Λ p h u * suffixConcat Q Λ p h v := by
  change lastRedLayerProjection Q Λ p (π (castKLR S h (concat S α β (u*v)))) = _
  rw [concat_mul, map_mul, map_mul, map_mul]
  rfl

/-- Keep the left boundary idempotents ending at the last red, and let the
ordinary KLR algebra act on the black suffix by juxtaposition. -/
def suffixBlack (p : Fin n) {α : Multiset (I ⊕ Fin (ℓ+1))} {β : Multiset I}
    (h : α+β.map ι=M) (ha : α.card = p.val+1) :
    KLRAlgebra k Q β →ₙₐ[k] (smallerSuffixIdeal Q Λ p).ringCon.Quotient := by
  classical
  let U := Finset.univ.filter (fun a : Seq α => a.lbl ⟨p.val, by omega⟩ = .inr (Fin.last ℓ))
  let F := suffixConcat Q Λ p h
  let r := blackSuffixReindex Q Λ β
  exact {
    toFun := fun y => F (eSum S U ⊗ₜ r y)
    map_zero' := by rw [map_zero, TensorProduct.tmul_zero, map_zero]
    map_add' := fun y z => by rw [map_add, TensorProduct.tmul_add, map_add]
    map_mul' := fun y z => by
      rw [map_mul, ← suffixConcat_mul, Algebra.TensorProduct.tmul_mul_tmul, (eSum_idem U).eq]
    map_smul' := fun c y => by rw [map_smul, TensorProduct.tmul_smul, map_smul]; rfl }

/-- The black action factors through the cyclotomic ideal for the last red
weight, including the empty suffix. -/
theorem suffixBlack_cycIdeal_le_ker (p : Fin n) {α : Multiset (I ⊕ Fin (ℓ+1))} {β : Multiset I}
    (h : α+β.map ι=M) (ha : α.card = p.val+1) :
    cycIdeal Q λf β ≤ TwoSidedIdeal.ker (suffixBlack Q Λ p h ha) := by
  classical
  apply TwoSidedIdeal.span_le.2
  rintro _ ⟨b,rfl⟩
  apply (TwoSidedIdeal.mem_ker _).2
  change suffixConcat Q Λ p h (eSum S _ ⊗ₜ blackSuffixReindex Q Λ β _) = 0
  rw [eSum, TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_eq_zero fun a ha' => suffixConcat_cycElt Q Λ p h ha a
    (Finset.mem_filter.mp ha').2 b

private def descendSurjective {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra k A] [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (hf : Function.Surjective f)
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

private theorem descendSurjective_apply {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra k A] [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (g : A →ₙₐ[k] C) (h : ∀ x y, f x = f y → g x = g y) (z : A) :
    descendSurjective f hf g h (f z) = g z := h _ _ (Function.surjInv_eq hf _)

/-- Juxtaposition action of the cyclotomic algebra of the last weight on the
right-hand block, Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38. -/
def suffixCyclotomic (p : Fin n) {α : Multiset (I ⊕ Fin (ℓ+1))} {β : Multiset I}
    (h : α+β.map ι=M) (ha : α.card = p.val+1) :
    CycKLR k Q λf β →ₙₐ[k] (smallerSuffixIdeal Q Λ p).ringCon.Quotient :=
  descendSurjective (CycKLR.mk k Q λf β) CycKLR.mk_surjective (suffixBlack Q Λ p h ha)
    (fun x y hxy => sub_eq_zero.mp (by
      rw [← map_sub]
      exact (TwoSidedIdeal.mem_ker _).1 ((suffixBlack_cycIdeal_le_ker Q Λ p h ha)
        ((CycKLR.mk_eq_mk_iff x y).1 hxy))))

theorem suffixCyclotomic_mk (p : Fin n) {α : Multiset (I ⊕ Fin (ℓ+1))} {β : Multiset I}
    (h : α+β.map ι=M) (ha : α.card = p.val+1) (x : KLRAlgebra k Q β) :
    suffixCyclotomic Q Λ p h ha (CycKLR.mk k Q λf β x) = suffixBlack Q Λ p h ha x :=
  descendSurjective_apply _ _ _ _ _

end Categorification.Stendhal
