/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyRes
import Categorification.KLR.BarK0

/-!
# Restriction of the right projective modules `ₛP`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.19** (second formula, ungraded):
for `s ∈ Seq(ν + ν')`,
`Res_{ν,ν'} (ₛP) ≅ ⊕ ᵢP ⊗ ⱼP`,
the sum over all ways of writing `s` as a shuffle of `i ∈ Seq ν` and `j ∈ Seq ν'`, as right
`R(ν) ⊗ R(ν')`-modules.

Here `ₛP = 1_s R(ν + ν')` and `Res_{ν,ν'} (ₛP) = 1_s R(ν + ν') 1_{ν,ν'}`
(`KLRAlgebra.resRightSub`), a right `R(ν) ⊗ R(ν')`-module through `ι_{ν,ν'}`; the summand
`ᵢP ⊗ ⱼP` is the right ideal `(1_i ⊗ 1_j)(R(ν) ⊗ R(ν'))` (`KLRAlgebra.projPPR`). The
isomorphism (`KLRAlgebra.resProjEquivRight`) sends `(t_u)_u` to `∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)`,
and it intertwines the right actions (`KLRAlgebra.resProjEquivRight_mul`). It is obtained from
the first formula (`KLRAlgebra.resProjEquiv`, `Categorification.KLR.MackeyRes`) by the
antiinvolution `ψ = hflip` (reflection in a horizontal line), which fixes the idempotents `1_s`,
reverses words of crossings and satisfies `ψ(ι(a ⊗ b)) = ι(ψ a ⊗ ψ b)`
(`KLRAlgebra.hflip_concat_tmul_tmul`). The grading shifts `{deg(i, j, s)}` of the paper are not
recorded here.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

/-! ### The flip on `R(ν) ⊗ R(ν')` -/

section TFlip

variable {ν ν' : Multiset I}

variable (Q ν ν') in
/-- `ψ ⊗ ψ` on `R(ν) ⊗ R(ν')`, a `k`-linear antiinvolution. -/
noncomputable def tflip : (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') →ₗ[k]
    (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :=
  TensorProduct.map (hflipEquiv k Q ν).toLinearMap (hflipEquiv k Q ν').toLinearMap

@[simp] theorem tflip_tmul (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν') :
    tflip Q ν ν' (a ⊗ₜ b) = hflip a ⊗ₜ hflip b := rfl

@[simp] theorem tflip_tflip (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    tflip Q ν ν' (tflip Q ν ν' t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [tflip_tmul, tflip_tmul, hflip_hflip, hflip_hflip]
  | add s t hs ht => rw [map_add, map_add, hs, ht]

theorem tflip_mul (t c : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    tflip Q ν ν' (t * c) = tflip Q ν ν' c * tflip Q ν ν' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero, mul_zero]
  | tmul a b =>
    induction c using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero, zero_mul]
    | tmul a' b' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tflip_tmul, tflip_tmul, tflip_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, hflip_mul, hflip_mul]
    | add c c' hc hc' => rw [mul_add, map_add, hc, hc', map_add, add_mul]
  | add s t hs ht => rw [add_mul, map_add, hs, ht, map_add, mul_add]

theorem hflip_concat_eq_tflip (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    hflip (concat Q ν ν' t) = concat Q ν ν' (tflip Q ν ν' t) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, ← hflipEquiv_apply, map_zero, map_zero]
  | tmul a b => rw [hflip_concat_tmul_tmul, tflip_tmul]
  | add s t hs ht => rw [map_add, hflip_add, hs, ht, map_add, map_add]

theorem hflip_oneConcat_eq :
    hflip (oneConcat Q ν ν' : KLRAlgebra k Q (ν + ν')) = oneConcat Q ν ν' := by
  simp only [oneConcat, eSum, hflip_sum, hflip_e]

theorem tflip_e_tmul_e (i : Seq ν) (j : Seq ν') :
    tflip Q ν ν' (e i ⊗ₜ e j) = e i ⊗ₜ e j := by
  rw [tflip_tmul, hflip_e, hflip_e]

end TFlip

/-! ### Right projective modules -/

section Defs

variable {ν ν' : Multiset I}

variable (Q) in
/-- The right projective `R(ν) ⊗ R(ν')`-module `ᵢP ⊗ ⱼP`, as the right ideal
`(1_i ⊗ 1_j)(R(ν) ⊗ R(ν'))` (a `k`-submodule, closed under right multiplication,
`mul_mem_projPPR`). -/
noncomputable def projPPR (i : Seq ν) (j : Seq ν') :
    Submodule k (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') where
  carrier := {t | (e i ⊗ₜ e j) * t = t}
  add_mem' ha hb := by simp only [Set.mem_setOf_eq, mul_add] at *; rw [ha, hb]
  zero_mem' := mul_zero _
  smul_mem' c t ht := by simp only [Set.mem_setOf_eq, mul_smul_comm] at *; rw [ht]

theorem mem_projPPR {i : Seq ν} {j : Seq ν'} {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'} :
    t ∈ projPPR Q i j ↔ (e i ⊗ₜ e j) * t = t := Iff.rfl

theorem mul_mem_projPPR {i : Seq ν} {j : Seq ν'} {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'}
    (ht : t ∈ projPPR Q i j) (c : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    t * c ∈ projPPR Q i j := by
  rw [mem_projPPR, ← mul_assoc, mem_projPPR.1 ht]

theorem tflip_mem_projPP_iff {i : Seq ν} {j : Seq ν'}
    {t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν'} :
    tflip Q ν ν' t ∈ projPP Q i j ↔ t ∈ projPPR Q i j := by
  rw [mem_projPP, mem_projPPR]
  constructor
  · intro h
    have := congrArg (tflip Q ν ν') h
    rwa [tflip_mul, tflip_tflip, tflip_e_tmul_e] at this
  · intro h
    rw [← tflip_e_tmul_e, ← tflip_mul, h]

variable (Q ν ν') in
/-- `Res_{ν,ν'} (ₛP) = 1_s R(ν + ν') 1_{ν,ν'}`, as a `k`-submodule of `R(ν + ν')`. -/
noncomputable def resRightSub (s : Seq (ν + ν')) : Submodule k (KLRAlgebra k Q (ν + ν')) where
  carrier := {r | e s * r = r ∧ r * oneConcat Q ν ν' = r}
  add_mem' ha hb := ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  zero_mem' := ⟨mul_zero _, zero_mul _⟩
  smul_mem' c r hr := ⟨by rw [mul_smul_comm, hr.1], by rw [smul_mul_assoc, hr.2]⟩

theorem mem_resRightSub {s : Seq (ν + ν')} {r : KLRAlgebra k Q (ν + ν')} :
    r ∈ resRightSub Q ν ν' s ↔ e s * r = r ∧ r * oneConcat Q ν ν' = r := Iff.rfl

end Defs

/-! ### Proposition 2.19, second formula -/

section Main

variable {ν ν' : Multiset I} (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)

/-- The map `(t_u)_u ↦ ∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)`. -/
noncomputable def resSumR (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) : KLRAlgebra k Q (ν + ν') :=
  ∑ u, e s * ψw (σ u.1).reverse * concat Q ν ν' (t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')

/-- `ψ` turns right projectives into left ones. -/
noncomputable def flipFam (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2 :=
  fun u => ⟨tflip Q ν ν' (t u), tflip_mem_projPP_iff.2 (t u).2⟩

/-- `ψ` turns left projectives into right ones. -/
noncomputable def unflipFam (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2 :=
  fun u => ⟨tflip Q ν ν' (t u), tflip_mem_projPP_iff.1 (by rw [tflip_tflip]; exact (t u).2)⟩

theorem flipFam_unflipFam (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPP Q u.split.1 u.split.2) :
    flipFam s (unflipFam s t) = t :=
  funext fun _ => Subtype.ext (tflip_tflip _)

theorem unflipFam_flipFam (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    unflipFam s (flipFam s t) = t :=
  funext fun _ => Subtype.ext (tflip_tflip _)

theorem hflip_resSumR (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    hflip (resSumR σ s t) = resSum σ s (flipFam s t) := by
  rw [resSumR, hflip_sum, resSum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hflip_mul, hflip_mul, hflip_e, hflip_ψw, List.reverse_reverse, hflip_concat_eq_tflip,
    resElt]
  rfl

theorem resSumR_mem (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    resSumR σ s t ∈ resRightSub Q ν ν' s := by
  refine ⟨?_, ?_⟩
  · rw [resSumR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← mul_assoc, ← mul_assoc, e_mul_self]
  · rw [resSumR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_assoc, concat_mul_oneConcat]

/-- `(t_u c)_u ↦ (∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)) ι(c)`: the map is right `R(ν) ⊗ R(ν')`-linear. -/
theorem resSumR_mul (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2)
    (c : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    resSumR σ s (fun u => ⟨(t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') * c,
      mul_mem_projPPR (t u).2 c⟩) = resSumR σ s t * concat Q ν ν' c := by
  rw [resSumR, resSumR, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [concat_mul, mul_assoc]

/-- The `k`-linear map `⊕_u ᵢP ⊗ ⱼP → Res_{ν,ν'} (ₛP)`. -/
noncomputable def resProjMapR (s : Seq (ν + ν')) :
    ((u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) →ₗ[k] resRightSub Q ν ν' s where
  toFun t := ⟨resSumR σ s t, resSumR_mem σ s t⟩
  map_add' t t' := by
    refine Subtype.ext ?_
    simp only [resSumR, Pi.add_apply, Submodule.coe_add, map_add, mul_add,
      Finset.sum_add_distrib]
  map_smul' c t := by
    refine Subtype.ext ?_
    simp only [resSumR, Pi.smul_apply, Submodule.coe_smul, map_smul, mul_smul_comm,
      RingHom.id_apply, Finset.smul_sum]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (hσ : ∀ u, IsReduced (Multiset.card (ν + ν')) (σ u) ∧
    wordProd (Multiset.card (ν + ν')) (σ u) = u.1)
  (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b)

include hPQ hP hρ₁ hρ₂ hσ in
theorem resProjMapR_bijective (s : Seq (ν + ν')) :
    Function.Bijective (resProjMapR (Q := Q) σ s) := by
  have hbij := resProjMap_bijective σ hσ hPQ hP ρ₁ ρ₂ hρ₁ hρ₂ s
  constructor
  · intro t t' htt
    have h0 : resSumR σ s t = resSumR σ s t' := congrArg Subtype.val htt
    have h1 := congrArg hflip h0
    rw [hflip_resSumR, hflip_resSumR, ← coe_resProjMap, ← coe_resProjMap] at h1
    have h2 := hbij.1 (Subtype.ext (Subtype.ext h1))
    rw [← unflipFam_flipFam s t, ← unflipFam_flipFam s t', h2]
  · rintro ⟨r, hr1, hr2⟩
    have hm1 : hflip r ∈ projP Q s := by
      rw [mem_projP, ← hflip_e, ← hflip_mul, hr1]
    have hm2 : (⟨hflip r, hm1⟩ : projP Q s) ∈ resSubgroup Q ν ν' (projP Q s) := by
      rw [mem_resSubgroup]
      refine Subtype.ext ?_
      rw [Submodule.coe_smul, smul_eq_mul]
      show oneConcat Q ν ν' * hflip r = hflip r
      rw [← hflip_oneConcat_eq, ← hflip_mul, hr2]
    obtain ⟨t'', ht''⟩ := hbij.2 ⟨⟨hflip r, hm1⟩, hm2⟩
    refine ⟨unflipFam s t'', Subtype.ext ?_⟩
    show resSumR σ s (unflipFam s t'') = r
    have h1 : hflip (resSumR σ s (unflipFam s t'')) = hflip r := by
      rw [hflip_resSumR, flipFam_unflipFam, ← coe_resProjMap, ht'']
    rw [← hflip_hflip (resSumR σ s (unflipFam s t'')), h1, hflip_hflip]

/-- **KL I, Proposition 2.19** (second formula, ungraded): for `s ∈ Seq(ν + ν')`,
`Res_{ν,ν'} (ₛP) ≅ ⊕ ᵢP ⊗ ⱼP`, the sum over all ways of writing `s` as a shuffle of
`i ∈ Seq ν` and `j ∈ Seq ν'` (indexed by the minimal coset representatives `u` with
`u • s = ij`). The isomorphism sends `(t_u)_u` to `∑_u 1_s ψ_{σ(u)^{rev}} ι(t_u)` and is right
`R(ν) ⊗ R(ν')`-linear (`resProjEquivRight_mul`). -/
noncomputable def resProjEquivRight (s : Seq (ν + ν')) :
    ((u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) ≃ₗ[k] resRightSub Q ν ν' s :=
  LinearEquiv.ofBijective (resProjMapR σ s)
    (resProjMapR_bijective σ hPQ hP hσ ρ₁ ρ₂ hρ₁ hρ₂ s)

theorem resProjEquivRight_apply (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2) :
    ((resProjEquivRight σ hPQ hP hσ ρ₁ ρ₂ hρ₁ hρ₂ s t : resRightSub Q ν ν' s) :
      KLRAlgebra k Q (ν + ν')) =
      ∑ u, e s * ψw (σ u.1).reverse *
        concat Q ν ν' (t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :=
  rfl

/-- The isomorphism of Proposition 2.19 (second formula) intertwines the right actions of
`R(ν) ⊗ R(ν')` (on `Res_{ν,ν'} (ₛP)` through `ι_{ν,ν'}`). -/
theorem resProjEquivRight_mul (s : Seq (ν + ν'))
    (t : (u : ShuffleOf ν ν' s) → projPPR Q u.split.1 u.split.2)
    (c : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') :
    ((resProjEquivRight σ hPQ hP hσ ρ₁ ρ₂ hρ₁ hρ₂ s (fun u =>
      ⟨(t u : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') * c, mul_mem_projPPR (t u).2 c⟩) :
        resRightSub Q ν ν' s) : KLRAlgebra k Q (ν + ν')) =
      (resProjEquivRight σ hPQ hP hσ ρ₁ ρ₂ hρ₁ hρ₂ s t : KLRAlgebra k Q (ν + ν')) *
        concat Q ν ν' c :=
  resSumR_mul σ s t c

end Main

end KLRAlgebra

end Categorification.KLR
