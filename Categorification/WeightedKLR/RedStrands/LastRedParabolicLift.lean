/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedDetectedClasses
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.KLR.ConcatAssoc

/-!
# Parabolic representatives for the last-red layer

In Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38, juxtaposition
on the identity shuffle recovers the input to standardization. Moving the
terminal red strand across the parentheses in affine concatenation compares
the two decompositions used to define the layer and parabolic induction.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem assoc_cast_concat {J k : Type*} [DecidableEq J] [CommRing k]
    (S : J → J → MvPolynomial (Fin 2) k) {a b c ab bc v : Multiset J}
    (hl : a+b = ab) (hr : b+c = bc) (hl' : ab+c = v) (hr' : a+bc = v)
    (x : KLRAlgebra k S a) (z : KLRAlgebra k S c) :
    castKLR S hl' (concat S ab c (castKLR S hl (concat S a b (x ⊗ₜ 1)) ⊗ₜ z)) =
      castKLR S hr' (concat S a bc (x ⊗ₜ castKLR S hr (concat S b c (1 ⊗ₜ z)))) := by
  subst ab
  subst bc
  subst v
  change concat S (a+b) c (concat S a b (x ⊗ₜ 1) ⊗ₜ z) =
    castKLR S (add_assoc a b c).symm (concat S a (b+c) (x ⊗ₜ concat S b c (1 ⊗ₜ z)))
  have h := concat_assoc (Q := S) (ν := a) (ν' := b) (ν'' := c) x 1 z
  have H {a b : Multiset J} (e : a=b) (x : KLRAlgebra k S a) :
      castKLR S e.symm (castKLR S e x) = x := by subst b; rfl
  rw [← h,H]

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ)
  {ν θ β : Multiset I}
local notation "S" => stendhalQ Q Λ
local notation "old" => Λ ∘ Fin.castSucc
local notation "μ" => stendhalWeight ℓ θ
local notation "Aₚ" => Multiset.map (addRedColor ℓ) μ
local notation "rₗ" => ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1)))
local notation "PWeight" => stendhalWeight (ℓ+1) θ
local notation "B₀" => Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β
local notation "Aₗ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "L" => TensorProductAlgebra k Q (old) θ
local notation "λf" => (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
local notation "R" => CycKLR k Q λf β
local notation "P₁" => parabolicPrefixProjection Q Λ θ
local notation "P₂" => parabolicLastCyclotomic Q Λ β
local notation "π₀" => StendhalAlgebraAllOrders.ofKLR k Q (old) θ
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q Λ θ
local notation "τ" => TensorProductAlgebra.mk Q Λ θ
local notation "γ" => fun u => τ (orderProjection Q Λ θ (π u))
local notation "rawFirst" => fun u : KLRAlgebra k S Aₚ =>
  castKLR S stendhalWeight_addRed (concat S Aₚ rₗ (u ⊗ₜ 1))

private def relabelEarlier (θ : Multiset I) :
    SeqRelabel k (stendhalQ Q (old)) S (stendhalWeight ℓ θ) ((stendhalWeight ℓ θ).map (addRedColor ℓ)) :=
  let ρ := SeqRelabel.ofInjective (addRedColor_injective (I := I) ℓ) S (stendhalWeight ℓ θ)
  { ρ with Q_eq := fun s a b hab => (ρ.Q_eq s a b hab).trans (by
      cases s.lbl a <;> cases s.lbl b <;> rfl) }

private theorem append_all_raw (v : KLRAlgebra k (stendhalQ Q (old)) μ) :
    (appendRedAllOrders Q Λ θ (π₀ v)).val =
      π (rawFirst (relabelEquiv (relabelEarlier Q Λ θ) v)) := by
  obtain ⟨a,rfl⟩ := KLRAlgebra.mk_surjective v
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  unfold appendRedAllOrders
  erw [RingQuot.liftAlgHom_mkAlgHom_apply]
  let z := relabelEquiv (relabelEarlier Q Λ θ) ((KLRAlgebra.mk k (stendhalQ Q (old)) μ) a)
  change π (castKLR S stendhalWeight_addRed (((blockL Aₚ rₗ).hom S z).val)) =
    π (castKLR S stendhalWeight_addRed (concat S Aₚ rₗ (z ⊗ₜ 1)))
  rw [concat_tmul,map_one,Corner.val_one,Corner.val_mul_E]

private theorem orderProjection_val {m : ℕ} {wts : Fin m → I →₀ ℕ} {θ' : Multiset I}
    (z : StendhalAlgebra k Q wts θ') : orderProjection Q wts θ' z.val = z :=
  Subtype.ext (KLR.Corner.val_mul_E z)

private theorem exists_prefixLift (x : L) : ∃ u : KLRAlgebra k S Aₚ,
    P₁ u = x ∧ γ (rawFirst u) = (appendRed Q Λ θ x).val := by
  obtain ⟨z,rfl⟩ := (show Function.Surjective (TensorProductAlgebra.mk Q (old) θ) from RingCon.mkₐ_surjective _) x
  obtain ⟨v,hv⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨relabelEquiv (relabelEarlier Q Λ θ) v,?_,?_⟩
  · change TensorProductAlgebra.mk Q (old) θ (orderProjection Q (old) θ
      (π₀ ((relabelEquiv (relabelEarlier Q Λ θ)).symm (relabelEquiv (relabelEarlier Q Λ θ) v)))) = _
    rw [AlgEquiv.symm_apply_apply,hv,orderProjection_val]
  · change τ (orderProjection Q Λ θ (π (rawFirst (relabelEquiv (relabelEarlier Q Λ θ) v)))) = _
    rw [← append_all_raw Q Λ v,hv]
    change τ (orderProjection Q Λ θ (appendRedStendhalValue Q Λ θ z).val) = τ (appendRedStendhalValue Q Λ θ z)
    rw [orderProjection_val]

variable (p : Fin (stendhalWeight (ℓ+1) ν).card)
    (h : stendhalWeight (ℓ+1) θ + Multiset.map (Sum.inl : I → I ⊕ Fin (ℓ+1)) β = stendhalWeight (ℓ+1) ν)
    (ha : (stendhalWeight (ℓ+1) θ).card = p.val+1)
local notation "F" => suffixConcat Q Λ p h
local notation "ψL" => lastRedLayerAction Q Λ p h ha
local notation "Layer" => IsIdempotentElem.Corner (lastRedLayerIdem_idem Q Λ p h)
local instance parabolicLayerRing : Ring Layer := _root_.instRingCorner _ _
local instance parabolicLayerTower : IsScalarTower k k Layer where
  smul_assoc a b z := mul_smul a b z

private theorem layer_tensor_one (x : L) :
    ψL (x ⊗ₜ (1 : R)) = prefixTensor Q Λ p h (appendRed Q Λ θ x).val := by
  change (lastRedLayerTensor Q Λ p h ha (x ⊗ₜ (1 : R))).val = _
  rw [lastRedLayerTensor,Algebra.TensorProduct.lift_tmul,map_one,mul_one]
  rfl

private theorem layer_prefixLift (x : L) (u : KLRAlgebra k S PWeight)
    (hu : γ u = (appendRed Q Λ θ x).val) (y : KLRAlgebra k Q β) :
    ψL (x ⊗ₜ CycKLR.mk k Q λf β y) = F (u ⊗ₜ blackSuffixReindex Q Λ β y) := by
  classical
  let D := eSum S (Finset.univ.filter (HasLastRed (ν := θ) (ℓ := ℓ)))
  let v := blackSuffixReindex Q Λ β y
  have hmul (a : KLRAlgebra k S PWeight) (b : KLRAlgebra k S B₀) :
      F (a ⊗ₜ b) = F (a ⊗ₜ 1) * F (1 ⊗ₜ b) := by
    rw [←suffixConcat_mul,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  have hD := lastRedLayerTensor_tmul_mk Q Λ p h ha x (1 : KLRAlgebra k Q β)
  rw [map_one,map_one] at hD
  change ψL (x ⊗ₜ (1 : R)) = prefixTensor Q Λ p h (appendRed Q Λ θ x).val * F (D ⊗ₜ 1) at hD
  change (lastRedLayerTensor Q Λ p h ha _).val = _
  rw [lastRedLayerTensor_tmul_mk]
  change _ * F (D ⊗ₜ v) = F (u ⊗ₜ v)
  rw [hmul D v,←mul_assoc,←hD,layer_tensor_one,←hu,prefixTensor_projection,hmul u v]

/-- Every operator in the last-red layer comes from a parabolic affine
diagram which projects to the prescribed tensor of input operators. Its
action on the identity shuffle therefore recovers precisely those inputs
(Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38). -/
theorem lastRedLayerAction_exists_parabolicLift
    (hTot : Aₚ + Aₗ = stendhalWeight (ℓ+1) ν) (z : L ⊗[k] R) :
    ∃ t : TensorKLR S Aₚ Aₗ, Algebra.TensorProduct.map (P₁) (P₂) t = z ∧
      suffixConcat Q Λ p hTot t = ψL z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    obtain ⟨t,ht,he⟩ := hz
    obtain ⟨t',ht',he'⟩ := hz'
    exact ⟨t+t',by rw [map_add,ht,ht'],by rw [map_add,he,he',map_add]⟩
  | tmul x y =>
    obtain ⟨v,rfl⟩ := CycKLR.mk_surjective y
    obtain ⟨u,hu,he⟩ := exists_prefixLift Q Λ x
    let b := blackSuffixReindex Q Λ β v
    let y' := castKLR S (lastRedBlackWeight (ℓ := ℓ) β) (concat S rₗ B₀ (1 ⊗ₜ b))
    refine ⟨u ⊗ₜ y',?_,?_⟩
    · rw [Algebra.TensorProduct.map_tmul,hu]
      exact congrArg (x ⊗ₜ[k] ·) (parabolicLastCyclotomic_concat_black Q Λ β v)
    · rw [layer_prefixLift Q Λ p h ha x (rawFirst u) he]
      change lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (castKLR S hTot (concat S Aₚ Aₗ (u ⊗ₜ y')))) =
        lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (castKLR S h (concat S PWeight B₀ (rawFirst u ⊗ₜ b))))
      exact congrArg _ (congrArg _ (assoc_cast_concat S stendhalWeight_addRed
        (lastRedBlackWeight (ℓ := ℓ) β) h hTot u b).symm)

/-- On the identity-shuffle copy of the input module, the last-red layer
acts by its two input factors. The parabolic intertwining hypothesis is the
identity-shuffle formula for induced modules. -/
theorem lastRedLayerAction_identityShuffle (hTot : Aₚ + Aₗ = stendhalWeight (ℓ+1) ν)
    {N V : Type*} [AddCommGroup N] [Module k N] [AddCommGroup V] [Module k V]
    (ρ : (smallerSuffixIdeal Q Λ p).ringCon.Quotient →ₐ[k] Module.End k V)
    (σ : L ⊗[k] R →ₐ[k] Module.End k N) (ι : N →ₗ[k] V)
    (hc : ∀ (t : TensorKLR S Aₚ Aₗ) (n : N),
      ρ (suffixConcat Q Λ p hTot t) (ι n) = ι (σ (Algebra.TensorProduct.map (P₁) (P₂) t) n))
    (z : L ⊗[k] R) (n : N) : ρ (ψL z) (ι n) = ι (σ z n) := by
  obtain ⟨t,ht,he⟩ := lastRedLayerAction_exists_parabolicLift Q Λ p h ha hTot z
  rw [← he,hc,ht]

end Categorification.Stendhal
