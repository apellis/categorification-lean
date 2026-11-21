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

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
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

/-- Appending the terminal red strand commutes with cutting by the red-ordered
idempotents. -/
theorem appendRedAllOrders_orderProjection (w : StendhalAlgebraAllOrders k Q (old) θ) :
    orderProjection Q Λ θ (appendRedAllOrders Q Λ θ w).val =
      appendRedStendhalValue Q Λ θ (orderProjection Q (old) θ w) := by
  classical
  apply Subtype.ext
  rw [appendRedStendhalValue_val]
  change (appendRedAllOrders Q Λ θ w).val * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ =
    (appendRedAllOrders Q Λ θ (w * StendhalAlgebraAllOrders.redOrderedIdem k Q (old) θ)).val
  have hE : (appendRedAllOrders Q Λ θ
      (StendhalAlgebraAllOrders.redOrderedIdem k Q (old) θ)).val =
      (appendRedAllOrders Q Λ θ 1).val * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ θ := by
    have h1 : (1 : StendhalAlgebraAllOrders k Q (old) θ) = ∑ s : Seq μ,
        StendhalAlgebraAllOrders.e s := by
      rw [← map_one (StendhalAlgebraAllOrders.ofKLR k Q (old) θ), ← sum_e, map_sum]
      rfl
    rw [h1, StendhalAlgebraAllOrders.redOrderedIdem, map_sum, map_sum, KLR.Corner.val_sum,
      KLR.Corner.val_sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [appendRedAllOrders_e, StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
    exact if_congr (appendRedLoading_ordered_iff s).symm rfl rfl
  rw [map_mul, KLR.Corner.val_mul, hE, ← mul_assoc, map_one, KLR.Corner.val_one,
    KLR.Corner.val_mul_E]

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

/-- Juxtaposing a diagram on the first `ℓ` red strands with the last red strand is appending the
red strand to its image in `T^{λ'}`. -/
theorem tensorOfKLR_concat_one_eq_appendRed (u : KLRAlgebra k S Aₚ) :
    γ (rawFirst u) = (appendRed Q Λ θ (P₁ u)).val := by
  obtain ⟨v,rfl⟩ := (relabelEquiv (relabelEarlier Q Λ θ)).surjective u
  change τ (orderProjection Q Λ θ (π (rawFirst (relabelEquiv (relabelEarlier Q Λ θ) v)))) =
    (appendRed Q Λ θ (TensorProductAlgebra.mk Q (old) θ (orderProjection Q (old) θ
      (π₀ ((relabelEquiv (relabelEarlier Q Λ θ)).symm (relabelEquiv (relabelEarlier Q Λ θ) v)))))).val
  rw [AlgEquiv.symm_apply_apply, ← append_all_raw Q Λ v, appendRedAllOrders_orderProjection]
  rfl

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

section Factorization

variable (hTot : Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ) +
    Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β) =
      stendhalWeight (ℓ+1) ν)
local notation "hB" => lastRedBlackWeight (ℓ := ℓ) β
local notation "K" => KLRAlgebra k S (rₗ + B₀)
local notation "Cₚ" => RingCon.Quotient (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "q" => RingCon.mk' (TwoSidedIdeal.ringCon (smallerSuffixIdeal Q Λ p))
local notation "τν" => TensorProductAlgebra.mk Q Λ ν
local notation "πν" => StendhalAlgebraAllOrders.ofKLR k Q Λ ν

/-- Juxtaposition and the last-red layer agree on a parabolic diagram whose
second block is the terminal red strand followed by black strands. -/
private theorem layer_parabolic (u : KLRAlgebra k S Aₚ) (v : KLRAlgebra k Q β) :
    suffixConcat Q Λ p hTot
        (u ⊗ₜ castKLR S hB (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β v))) =
      ψL (P₁ u ⊗ₜ CycKLR.mk k Q λf β v) := by
  rw [layer_prefixLift Q Λ p h ha (P₁ u) (rawFirst u)
    (tensorOfKLR_concat_one_eq_appendRed Q Λ u)]
  change lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      (castKLR S hTot (concat S Aₚ Aₗ (u ⊗ₜ _)))) =
    lastRedLayerProjection Q Λ p (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      (castKLR S h (concat S PWeight B₀ (rawFirst u ⊗ₜ _))))
  exact congrArg _ (congrArg _ (assoc_cast_concat S stendhalWeight_addRed hB h hTot u _).symm)

/-- Juxtaposition with the unit on the prefix. -/
private def blackG : K →ₗ[k] Cₚ :=
  (suffixConcat Q Λ p hTot).comp ((TensorProduct.mk k _ _ 1).comp (castKLR S hB).toLinearMap)

/-- The last-red layer applied to the last input quotient. -/
private def blackH : K →ₗ[k] Cₚ :=
  ({ toFun := ψL, map_add' := map_add ψL, map_smul' := map_smul ψL } : _ →ₗ[k] Cₚ).comp
    ((TensorProduct.mk k L R 1).comp
    ((P₂).toLinearMap.comp (castKLR S hB).toLinearMap))

local notation "G" => blackG Q Λ p hTot
local notation "H" => blackH Q Λ p h ha

private theorem blackG_apply (z : K) :
    G z = suffixConcat Q Λ p hTot (1 ⊗ₜ castKLR S hB z) := rfl
private theorem blackH_apply (z : K) : H z = ψL (1 ⊗ₜ P₂ (castKLR S hB z)) := rfl

private theorem blackG_mul (a b : K) : G (a*b) = G a * G b := by
  rw [blackG_apply, blackG_apply, blackG_apply, ← suffixConcat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]

private theorem blackH_mul (a b : K) : H (a*b) = H a * H b := by
  rw [blackH_apply, blackH_apply, blackH_apply, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_mul]

private theorem blackG_concat (w : KLRAlgebra k S B₀) :
    G (concat S rₗ B₀ (1 ⊗ₜ w)) = H (concat S rₗ B₀ (1 ⊗ₜ w)) := by
  obtain ⟨v,rfl⟩ := (blackSuffixReindex Q Λ β).surjective w
  rw [blackG_apply, blackH_apply, layer_parabolic Q Λ p h ha hTot, map_one]
  exact congrArg (fun y => ψL ((1 : L) ⊗ₜ[k] y))
    (parabolicLastCyclotomic_concat_black Q Λ β v).symm

omit [DecidableEq I] in
private theorem violated_cast {X Y : Multiset (I ⊕ Fin (ℓ+1))} (hμ : X = Y) {t : Seq X}
    (ht : IsViolated t) : IsViolated (Seq.cast hμ t) := by
  subst hμ; exact ht

omit [DecidableEq I] in
private theorem terminal_red_mem (t : Seq Aₗ) : ∃ c, t.1 c = .inr (Fin.last ℓ) := by
  have hmem : (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ+1)) ∈ Aₗ := by
    simp [stendhalWeight]
  rw [← t.2] at hmem
  obtain ⟨c, _, hc⟩ := Multiset.mem_map.1 hmem
  exact ⟨c, hc⟩

private theorem suffixConcat_e_e (i : Seq Aₚ) (t : Seq Aₗ) :
    suffixConcat Q Λ p hTot (e i ⊗ₜ e t) =
      q (τν (orderProjection Q Λ ν (πν (e (Seq.cast hTot (i.append t)))))) := by
  change q (τν (orderProjection Q Λ ν (πν (castKLR S hTot (concat S Aₚ Aₗ _))))) = _
  rw [concat_e_tmul_e, castKLR_e]

include ha in
private theorem suffixConcat_e_violated (i : Seq Aₚ) (t : Seq Aₗ) (ht : IsViolated t) :
    suffixConcat Q Λ p hTot (e i ⊗ₜ e t) = 0 := by
  rw [suffixConcat_e_e]
  set s := Seq.cast hTot (i.append t) with hsdef
  by_cases hs : IsRedOrdered s
  · have he : orderProjection Q Λ ν (πν (e s)) = StendhalAlgebra.e s hs :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))
    rw [he]
    obtain ⟨c, hc⟩ := terminal_red_mem t
    obtain ⟨h0, hl0⟩ := ht
    have hc0 : c.val ≠ 0 := by
      intro hc0
      have : c = ⟨0, h0⟩ := Fin.ext hc0
      rw [this] at hc
      simp [Seq.lbl, hc] at hl0
    have hcard : (Aₚ).card = p.val := by
      simp [stendhalWeight] at ha ⊢; omega
    let a : Fin (stendhalWeight (ℓ+1) ν).card :=
      Fin.cast (congrArg Multiset.card hTot) (Seq.posR Aₚ c)
    have hpa : p < a := by
      change p.val < (Aₚ).card + c.val
      omega
    have hl : s.lbl a = .inr (Fin.last ℓ) := by
      change (Seq.cast hTot (i.append t)).1 a = _
      simp [a, hc]
    change (smallerSuffixIdeal Q Λ p).ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨s, hs, a, hpa, hl, rfl⟩
  · have he : orderProjection Q Λ ν (πν (e s)) = 0 :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs))
    rw [he, map_zero, map_zero]

include ha in
private theorem blackG_e_violated (t : Seq (rₗ + B₀)) (ht : IsViolated t) : G (e t) = 0 := by
  rw [blackG_apply, castKLR_e, ← sum_e (ν := Aₚ), TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_eq_zero fun i _ =>
    suffixConcat_e_violated Q Λ p ha hTot i _ (violated_cast hB ht)

private theorem blackH_e_violated (t : Seq (rₗ + B₀)) (ht : IsViolated t) : H (e t) = 0 := by
  rw [blackH_apply, castKLR_e, parabolicLastCyclotomic, AlgHom.comp_apply,
    parabolicLastProjection_e_violated _ _ _ _ (violated_cast hB ht), map_zero,
    TensorProduct.tmul_zero, map_zero]

omit [DecidableEq I] in
private theorem seq_terminal_subsingleton : Subsingleton (Seq rₗ) :=
  ⟨fun s t => Subtype.ext (funext fun a => by
    rw [Multiset.mem_singleton.1 (s.mem a), Multiset.mem_singleton.1 (t.mem a)])⟩

private theorem e_terminal (a : Seq rₗ) : (e a : KLRAlgebra k S rₗ) = 1 := by
  have := seq_terminal_subsingleton (I := I) (ℓ := ℓ)
  rw [← sum_e, Fintype.sum_subsingleton _ a]

omit [DecidableEq I] in
/-- In a diagram with a black leftmost terminus... a loading that is not violated starts with
the terminal red strand. -/
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
      exact terminal_first t ht _ hc
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

include ha in
private theorem blackGH_e (t : Seq (rₗ + B₀)) : G (e t) = H (e t) := by
  by_cases ht : IsViolated t
  · rw [blackG_e_violated Q Λ p ha hTot t ht, blackH_e_violated Q Λ p h ha t ht]
  · obtain ⟨a, b, rfl⟩ := split_unviolated t ht
    rw [← concat_e_tmul_e, e_terminal]
    exact blackG_concat Q Λ p h ha hTot (e b)

private theorem concat_one_tmul_x_mul {X Y : Multiset (I ⊕ Fin (ℓ+1))} (b : Fin Y.card)
    (t : Seq Y) : concat S X Y (1 ⊗ₜ (x b * e t)) = x (Seq.posR X b) * concat S X Y (1 ⊗ₜ e t) := by
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

private theorem suffixConcat_red_dot (t : Seq Aₗ) (b : Fin (Aₗ).card) (hb : (t.1 b).isRight) :
    suffixConcat Q Λ p hTot (1 ⊗ₜ (x b * e t)) = 0 := by
  change q (τν (orderProjection Q Λ ν (πν (castKLR S hTot (concat S Aₚ Aₗ _))))) = 0
  rw [concat_one_tmul_x_mul, concat_one_tmul_e, Finset.mul_sum, map_sum, map_sum,
    Finset.sum_eq_zero fun i _ => ?_, map_zero, map_zero, map_zero]
  rw [map_mul, castKLR_x, castKLR_e, map_mul]
  exact StendhalAlgebraAllOrders.x_mul_e_of_red _ _ (by simpa [Seq.lbl] using hb)

private theorem blackG_red_dot (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀))
    (hr : (t.1 a).isRight) : G (x a * e t) = 0 := by
  rw [blackG_apply, map_mul, castKLR_x, castKLR_e]
  exact suffixConcat_red_dot Q Λ p hTot _ _
    (by rw [Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self]; exact hr)

private theorem blackH_red_dot (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀))
    (hr : (t.1 a).isRight) : H (x a * e t) = 0 := by
  rw [blackH_apply, map_mul, castKLR_x, castKLR_e, parabolicLastCyclotomic, AlgHom.comp_apply,
    parabolicLastProjection_red_dot _ _ _ _ _
      (by rw [Seq.lbl, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self]; exact hr), map_zero,
    TensorProduct.tmul_zero, map_zero]

include ha in
private theorem blackGH_violated (z : K) (t : Seq (rₗ + B₀)) (ht : IsViolated t) :
    G (z * e t) = H (z * e t) := by
  rw [show z * e t = z * e t * e t by rw [mul_assoc, e_mul_self], blackG_mul, blackH_mul,
    blackG_e_violated Q Λ p ha hTot t ht, blackH_e_violated Q Λ p h ha t ht, mul_zero, mul_zero]

include ha in
private theorem blackGH_x (a : Fin (rₗ + B₀).card) (t : Seq (rₗ + B₀)) :
    G (x a * e t) = H (x a * e t) := by
  by_cases hr : (t.1 a).isRight
  · rw [blackG_red_dot Q Λ p hTot a t hr, blackH_red_dot Q Λ p h ha a t hr]
  by_cases ht : IsViolated t
  · exact blackGH_violated Q Λ p h ha hTot _ t ht
  have ha0 : a.val ≠ 0 := fun h0 => hr (by rw [terminal_first t ht a h0]; rfl)
  obtain ⟨a₀, b, rfl⟩ := split_unviolated t ht
  have := seq_terminal_subsingleton (I := I) (ℓ := ℓ)
  have hlt : a.val - 1 < (B₀).card := by have := a.2; simp at this ⊢; omega
  have hpa : Seq.posR rₗ (⟨a.val - 1, hlt⟩ : Fin (B₀).card) = a := Fin.ext (by simp; omega)
  have hxe : x a * e (a₀.append b) = concat S rₗ B₀ (1 ⊗ₜ (x ⟨a.val - 1, hlt⟩ * e b)) := by
    rw [concat_one_tmul_x_mul, concat_one_tmul_e, hpa, Fintype.sum_subsingleton _ a₀]
  rw [hxe]
  exact blackG_concat Q Λ p h ha hTot _

include ha in
private theorem blackGH_ψ (j : ℕ) (t : Seq (rₗ + B₀)) :
    G (ψ j * e t) = H (ψ j * e t) := by
  by_cases hj : j + 1 < (rₗ + B₀).card
  swap
  · rw [ψ_eq_zero j (by omega), zero_mul, map_zero, map_zero]
  by_cases ht : IsViolated t
  · exact blackGH_violated Q Λ p h ha hTot _ t ht
  obtain ⟨a₀, b, rfl⟩ := split_unviolated t ht
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
    rw [ψ_mul_e, blackG_mul, blackH_mul, blackG_e_violated Q Λ p ha hTot _ hs,
      blackH_e_violated Q Λ p h ha _ hs, zero_mul, zero_mul]
  · have hj' : j + 1 < (B₀).card := by simp at hj ⊢; omega
    have hψe : ψ (j + 1) * e (a₀.append b) = concat S rₗ B₀ (1 ⊗ₜ (ψ j * e b)) := by
      rw [concat_one_tmul_ψ_mul Q Λ hj', concat_one_tmul_e, Fintype.sum_subsingleton _ a₀,
        show Multiset.card rₗ + j = j + 1 by simp [Nat.add_comm]]
    rw [hψe]
    exact blackG_concat Q Λ p h ha hTot _

include ha in
private theorem blackGH_mul_e (z : K) : ∀ t, G (z * e t) = H (z * e t) := by
  induction z using KLRAlgebra.klr_induction with
  | hadd u v hu hv => intro t; rw [add_mul, map_add, map_add, hu, hv]
  | hmul u v hu hv =>
    intro t
    have hs : u * v * e t = ∑ s, u * e s * (v * e t) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_e, mul_one, mul_assoc]
    rw [hs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [blackG_mul, blackH_mul, hu, hv]
  | hr r =>
    intro t
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul,
      blackGH_e Q Λ p h ha hTot t]
  | he s =>
    intro t
    rw [e_mul_e]
    split_ifs
    · exact blackGH_e Q Λ p h ha hTot s
    · rw [map_zero, map_zero]
  | hx a => exact blackGH_x Q Λ p h ha hTot a
  | hψ a => exact blackGH_ψ Q Λ p h ha hTot a

include ha in
/-- On the black block of the terminal red strand, juxtaposition with the unit on the prefix
equals the last-red layer applied to the last input quotient. -/
private theorem blackG_eq_blackH (z : K) : G z = H z := by
  rw [← mul_one z, ← sum_e, Finset.mul_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun t _ => blackGH_mul_e Q Λ p h ha hTot z t

include ha in
private theorem suffixConcat_tmul_one (u : KLRAlgebra k S Aₚ) :
    suffixConcat Q Λ p hTot (u ⊗ₜ 1) = ψL (P₁ u ⊗ₜ 1) := by
  have hpar := layer_parabolic Q Λ p h ha hTot u 1
  rw [map_one, map_one] at hpar
  have hG1 : G 1 = G (concat S rₗ B₀ (1 ⊗ₜ 1)) := by
    rw [blackG_eq_blackH Q Λ p h ha hTot, blackG_eq_blackH Q Λ p h ha hTot, blackH_apply,
      blackH_apply, map_one, map_one]
    have hc := parabolicLastCyclotomic_concat_black Q Λ β (1 : KLRAlgebra k Q β)
    change P₂ (castKLR S hB (concat S rₗ B₀ (1 ⊗ₜ blackSuffixReindex Q Λ β 1))) =
      CycKLR.mk k Q λf β 1 at hc
    rw [map_one, map_one] at hc
    rw [show P₂ (castKLR S hB (concat S rₗ B₀ (1 ⊗ₜ 1))) = 1 from hc]
  calc suffixConcat Q Λ p hTot (u ⊗ₜ 1)
      = suffixConcat Q Λ p hTot ((u ⊗ₜ 1) * (1 ⊗ₜ castKLR S hB 1)) := by
        rw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
    _ = suffixConcat Q Λ p hTot (u ⊗ₜ 1) * G 1 := by rw [suffixConcat_mul]; rfl
    _ = suffixConcat Q Λ p hTot (u ⊗ₜ 1) * G (concat S rₗ B₀ (1 ⊗ₜ 1)) := by rw [hG1]
    _ = suffixConcat Q Λ p hTot (u ⊗ₜ castKLR S hB (concat S rₗ B₀ (1 ⊗ₜ 1))) := by
        rw [blackG_apply, ← suffixConcat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
    _ = ψL (P₁ u ⊗ₜ 1) := hpar

include ha in
/-- Juxtaposition of a prefix diagram with a terminal-block diagram, followed by the
quotient by smaller suffixes, factors through the last-red layer action
(Webster, arXiv:1309.3796v3, proof of Prop 5.5). -/
theorem suffixConcat_eq_lastRedLayerAction (t : TensorKLR S Aₚ Aₗ) :
    suffixConcat Q Λ p hTot t = ψL (Algebra.TensorProduct.map (P₁) (P₂) t) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha' hb' => rw [map_add, map_add, map_add, ha', hb']
  | tmul u w =>
    obtain ⟨z, rfl⟩ := (castKLR S hB).surjective w
    have hsplit : u ⊗ₜ[k] castKLR S hB z = (u ⊗ₜ[k] 1) * (1 ⊗ₜ[k] castKLR S hB z) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, hsplit, suffixConcat_mul,
      suffixConcat_tmul_one Q Λ p h ha hTot,
      show suffixConcat Q Λ p hTot (1 ⊗ₜ castKLR S hB z) = G z from rfl,
      blackG_eq_blackH Q Λ p h ha hTot, blackH_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Factorization

end Categorification.Stendhal
