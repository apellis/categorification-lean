/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongDotMate
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapEDot
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCapFData

/-!
# `K ∘ 𝔉_i ≅ 𝔉_i ∘ K` and the dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`. The dot on `𝔉_i` is the mate of the dot on `𝔈_i`
(`indDotOfEq`); on induced modules it is right multiplication of the corner by the dot,
`z ⊗ x ↦ z x_n ⊗ x` (`CupCap.indDotOfEq_app`, from
`InductionAlong.conjugateEquiv_symm_resAct_app`). The natural isomorphism `CupCap.capFOrdIso D`,
`c ⊗ (z ⊗ x) ↦ fwd(z c) ⊗ x`, carries the dot on `𝔉_i` to the dot on `𝔉⁺_i` as soon as `bwd`
carries the right action of the dot on the appended strand of `T^{λ⁺}` on the generators
`1 ⊗ c` to the left action of the dot on the appended strand of `T^λ`
(`CupCap.capFOrdIsoOfEq_dot`). This is the hypothesis of the part for `𝔈_i`
(`CupCap.capEOrdIsoOfEq_dot`), with `ι(c)` replaced by `bwd(1 ⊗ c)`.

## Main definitions

* `CupCap.indFunctorIsoOfEq`: induction along pointwise equal maps.
* `CupCap.capFOrdIsoOfEq`: `CupCap.capFOrdIso` with `𝔉_i` on `T^{λ⁺}` given by `blackFOfEq`
  along `plusWeight_assoc`.

## Main results

* `CupCap.indDotOfEq_app`: the dot on induction is right multiplication by the dot.
* `CupCap.capFOrdIso_dot`, `CupCap.capFOrdIsoOfEq_dot`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Induction

variable {A B : Type} [Ring A] [Ring B] {φ φ' : A →ₙ+* B}

theorem intertwines_unit_of_eq (h : ∀ a, φ a = φ' a) : Intertwines φ φ' (φ 1) := fun a => by
  rw [← map_mul, mul_one, h, ← h, ← map_mul, one_mul]

/-- **Induction along pointwise equal maps**: `functor φ ≅ functor φ'`, `z ⊗ n ↦ z φ(1) ⊗ n`. -/
def indFunctorIsoOfEq (h : ∀ a, φ a = φ' a) :
    InductionAlong.functor.{0, 0} φ ≅ InductionAlong.functor.{0, 0} φ' where
  hom := natTrans (intertwines_unit_of_eq h)
  inv := natTrans (intertwines_unit_of_eq fun a => (h a).symm)
  hom_inv_id := by
    rw [natTrans_comp, ← natTrans_unit]
    refine natTrans_eq_of_unit_mul _ _ ?_
    rw [← h 1]
    simp only [← map_mul, one_mul]
  inv_hom_id := by
    rw [natTrans_comp, ← natTrans_unit]
    refine natTrans_eq_of_unit_mul _ _ ?_
    rw [h 1]
    simp only [← map_mul, one_mul]

theorem indFunctorIsoOfEq_hom (h : ∀ a, φ a = φ' a) :
    (indFunctorIsoOfEq h).hom = natTrans (intertwines_unit_of_eq h) :=
  rfl

omit [Ring A] [Ring B] in
/-- A generator of an induced module is its corner element times `1 ⊗ n`. -/
theorem ind_tmul_eq_smul_unitGen {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] (z : Corner φ) (n : N) :
    (Ind.tmul z n : Ind N φ) = z.1 • Ind.tmul (unitGen φ) n := by
  rw [Ind.smul_tmul]
  exact congrArg (Ind.tmul · n) (Subtype.ext z.2.symm)

end Induction

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ)

/-- The cast of the dot on the appended strand commutes with the image of appending. -/
theorem castOp_appendedDot_commute (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (a : (TensorProductAlgebra k Q Λ' μ)ᵐᵒᵖ) :
    castOp Q Λ' h (op (appendedDot Q Λ' i μ)) * appendBlackOpOfEq Q Λ' i h a =
      appendBlackOpOfEq Q Λ' i h a * castOp Q Λ' h (op (appendedDot Q Λ' i μ)) := by
  rw [appendBlackOpOfEq_apply, ← map_mul, ← map_mul, op_appendedDot_commute]

/-- **The dot on `𝔉_i` is right multiplication by the dot**: on induced modules, the mate
`indDotOfEq` of the dot on restriction acts by `z ⊗ x ↦ z x_n ⊗ x`. -/
theorem indDotOfEq_app (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β)
    (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ' μ)ᵐᵒᵖ) :
    (indDotOfEq Q Λ' i h).app N = ModuleCat.ofHom (natMap (N := N)
      (intertwines_of_commute (castOp_appendedDot_commute Q Λ' i h))) :=
  conjugateEquiv_symm_resAct_app (castOp_appendedDot_commute Q Λ' i h) (resDotOfEq Q Λ' i h)
    (fun M => by subst h; rfl) N

/-- `indDotOfEq` as the natural transformation of inductions given by the dot. -/
theorem indDotOfEq_eq_natTrans (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    indDotOfEq Q Λ' i h =
      natTrans.{0, 0} (intertwines_of_commute (castOp_appendedDot_commute Q Λ' i h)) :=
  NatTrans.ext (funext fun N => indDotOfEq_app Q Λ' i h N)

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {ν : Multiset I} {i : I}

set_option hygiene false in
local notation "TA" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "TAᵢ" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)
set_option hygiene false in
local notation "TPp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "TPpᵢ" =>
  TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (((Singleton.singleton i : Multiset I) + ν) + ν₀)
set_option hygiene false in
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
set_option hygiene false in
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
set_option hygiene false in
local notation "aT" => appendBlackTPAOp k Q Λ Λc j hj ν ν₀ i
set_option hygiene false in
local notation "OrdK" => ordTensor TPpᵐᵒᵖ TAᵐᵒᵖ (OpBimodule TA CB)
set_option hygiene false in
local notation "OrdKᵢ" => ordTensor TPpᵢᵐᵒᵖ TAᵢᵐᵒᵖ (OpBimodule TAᵢ CBᵢ)
set_option hygiene false in
local notation "aOp" => appendBlackOp Q Λ i ν
set_option hygiene false in
local notation "Fᵖ" => blackFOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)

omit [DecidableEq I] in
/-- Additive maps out of an induced module agree once they agree on the generators `z ⊗ n`. -/
private theorem indAddHom_ext'' {A B : Type} [Ring A] [Ring B] {φ : A →ₙ+* B} {N : Type}
    [AddCommGroup N] [Module A N] {P : Type*} [AddCommGroup P] {f g : Ind N φ →+ P}
    (h : ∀ z n, f (Ind.tmul z n) = g (Ind.tmul z n)) : f = g :=
  AddMonoidHom.ext fun t => by
    induction t using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z n => exact h z n
    | add s t hs ht => rw [map_add, map_add, hs, ht]

/-! ### The dot on generators -/

theorem indTensorRight_natMap (X : ModuleCat.{0} TAᵐᵒᵖ) {d : TPpᵢᵐᵒᵖ} (hd : Intertwines aT aT d)
    (w : Ind CB aT) (x : X) :
    indTensorRight X (natMap (N := CB) hd w) x = natMap hd (indTensorRight X w x) :=
  DFunLike.congr_fun (indAddHom_ext''
    (f := ((indTensorRight X).flip x).comp (natMap (N := CB) hd).toAddMonoidHom)
    (g := (natMap (N := ((OrdK).obj X : Type)) hd).toAddMonoidHom.comp
      ((indTensorRight X).flip x)) fun _ _ => rfl) w

theorem indDotOfEq_rfl_tmul (X : ModuleCat.{0} TAᵐᵒᵖ) (z : Corner aOp) (x : X) :
    ((indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)).app X).hom (Ind.tmul z x) =
      (Ind.tmul ⟨z.1 * op (appendedDot Q Λ i ν),
        mul_mem_of_intertwines (intertwines_of_commute (op_appendedDot_commute Q Λ i ν)) z⟩ x :
          Ind X aOp) := by
  rw [indDotOfEq_app]
  rfl

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carries the dot to right multiplication by `d`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): if `fwd` carries the left action of the dot
on the appended strand of `T^λ` to right multiplication of the corner by `d`, then
`(K ∘ x) ≫ φ = φ ≫ (d ∘ K)` for `φ = CupCap.capFOrdIso D`. -/
theorem capFOrdIso_dot (D : CapFData k Q Λ Λc j hj ν₀ L ν i) {d : TPpᵢᵐᵒᵖ}
    (hd : Intertwines aT aT d)
    (hfwd : ∀ c : CBᵢ, D.fwd (appendedDot Q Λ i ν • c) = natMap (N := CB) hd (D.fwd c)) :
    (Functor.whiskerRight (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) OrdKᵢ :
        blackF Q Λ i ν ⋙ OrdKᵢ ⟶ blackF Q Λ i ν ⋙ OrdKᵢ) ≫ (capFOrdIso D).hom =
      (capFOrdIso D).hom ≫ Functor.whiskerLeft OrdK (natTrans.{0, 0} hd) := by
  refine NatTrans.ext (funext fun X => ?_)
  refine ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
    (DG.TensorProductOver.addHom_ext fun c t => ?_))
  refine DFunLike.congr_fun (indAddHom_ext''
    (f := (capFOrdFwd D X).comp ((AddMonoidHom.mk' (DG.TensorProductOver.tmul
      (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj X))
      TAᵢᵐᵒᵖ c) (DG.TensorProductOver.tmul_add (A := TAᵢᵐᵒᵖ)
      (M := InDegreeZero (OpBimodule TAᵢ CBᵢ)) (N := InDegreeZero ((blackF Q Λ i ν).obj X))
      c)).comp ((indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)).app X).hom.toAddMonoidHom))
    (g := (natMap (N := ((OrdK).obj X : Type)) hd).toAddMonoidHom.comp
      ((capFOrdFwd D X).comp (AddMonoidHom.mk' (DG.TensorProductOver.tmul
        (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
        (N := InDegreeZero ((blackF Q Λ i ν).obj X)) TAᵢᵐᵒᵖ c)
        (DG.TensorProductOver.tmul_add (A := TAᵢᵐᵒᵖ)
        (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
        (N := InDegreeZero ((blackF Q Λ i ν).obj X)) c)))) fun z x => ?_) t
  change capFOrdFwd D X (DG.TensorProductOver.tmul (M := InDegreeZero (OpBimodule TAᵢ CBᵢ))
      (N := InDegreeZero ((blackF Q Λ i ν).obj X)) TAᵢᵐᵒᵖ (c : CBᵢ)
      (((indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)).app X).hom (Ind.tmul z x))) =
    natMap hd (indTensorRight X (D.fwd (unop z.1 • (c : CBᵢ))) x)
  erw [indDotOfEq_rfl_tmul]
  rw [← indTensorRight_natMap]
  change indTensorRight X (D.fwd ((appendedDot Q Λ i ν * unop z.1) • (c : CBᵢ))) x = _
  rw [mul_smul]
  exact congrArg (fun y => indTensorRight X y x) (hfwd (unop z.1 • (c : CBᵢ)))

/-! ### From `bwd` on the generators `1 ⊗ c` -/

section Data

variable (D : CapFData k Q Λ Λc j hj ν₀ L ν i) {d : TPpᵢᵐᵒᵖ} (hd : Intertwines aT aT d)
  (hbwd : ∀ c : CB, appendedDot Q Λ i ν • D.bwd (Ind.tmul (unitGen aT) c) =
    d • D.bwd (Ind.tmul (unitGen aT) c))

include hbwd in
/-- `bwd` carries right multiplication by `d` to the left action of the dot. -/
theorem CapFData.bwd_natMap (w : Ind CB aT) :
    D.bwd (natMap (N := CB) hd w) = appendedDot Q Λ i ν • D.bwd w :=
  DFunLike.congr_fun (indAddHom_ext''
    (f := D.bwd.comp (natMap (N := CB) hd).toAddMonoidHom)
    (g := (AddMonoidHom.mk' (fun c : CBᵢ => appendedDot Q Λ i ν • c)
      (smul_add (appendedDot Q Λ i ν))).comp D.bwd) fun z c => by
    change D.bwd (Ind.tmul (cornerMul hd z) c) = appendedDot Q Λ i ν • D.bwd (Ind.tmul z c)
    rw [ind_tmul_eq_smul_unitGen (cornerMul hd z), ind_tmul_eq_smul_unitGen z, D.bwd_smul_right,
      D.bwd_smul_right]
    change (z.1 * d) • _ = _
    rw [mul_smul, ← hbwd]
    exact (smul_comm _ _ _).symm) w

include hbwd in
/-- `fwd` carries the left action of the dot to right multiplication by `d`. -/
theorem CapFData.fwd_dot (c : CBᵢ) :
    D.fwd (appendedDot Q Λ i ν • c) = natMap (N := CB) hd (D.fwd c) := by
  have hc : (appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1 * appendedDot Q Λ i ν =
      appendedDot Q Λ i ν * (appendBlack Q Λ i ν : TA →ₙ+* TAᵢ) 1 :=
    appendedDot_commute Q Λ i ν 1
  rw [← D.fwd_unit, smul_smul, hc, ← smul_smul, ← D.bwd_fwd,
    ← D.bwd_natMap hd hbwd, D.fwd_bwd]

end Data

/-! ### With `𝔉_i` on `T^{λ⁺}` given by `blackFOfEq` -/

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` on right modules** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔉_i`), with `𝔉_i` on `T^{λ⁺}` given by `blackFOfEq` along
`plusWeight_assoc`. -/
def capFOrdIsoOfEq (D : CapFData k Q Λ Λc j hj ν₀ L ν i) :
    blackF Q Λ i ν ⋙ OrdKᵢ ≅ OrdK ⋙ Fᵖ :=
  capFOrdIso D ≪≫ Functor.isoWhiskerLeft OrdK
    (indFunctorIsoOfEq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i))

/-- The dot on the appended strand of `T^{λ⁺}`, cast to `({i} + ν) + ν₀`, intertwines appending
with itself. -/
theorem intertwines_capDotPlusOp :
    Intertwines aT aT (capDotPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
      (ν₀ := ν₀) (ν := ν) (i := i)) := fun a => by
  rw [appendBlackTPAOp_eq_ofEq]
  exact (castOp_appendedDot_commute Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i) a).symm

/-- **`K ∘ 𝔉_i ≅ 𝔉_i ∘ K` carries the dot to the dot** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21): if `bwd` carries the right action of the dot on the appended strand of
`T^{λ⁺}` on the generators `1 ⊗ c` to the left action of the dot on the appended strand of
`T^λ`, then `(K ∘ x) ≫ φ = φ ≫ (x ∘ K)` for `φ = CupCap.capFOrdIsoOfEq D`, with `x` the dots
`indDotOfEq` on `𝔉_i` and on `𝔉⁺_i`. -/
theorem capFOrdIsoOfEq_dot (D : CapFData k Q Λ Λc j hj ν₀ L ν i)
    (hbwd : ∀ c : CB, appendedDot Q Λ i ν • D.bwd (Ind.tmul (unitGen aT) c) =
      (capDotPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) (ν := ν)
        (i := i)) • D.bwd (Ind.tmul (unitGen aT) c)) :
    (Functor.whiskerRight (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + ν = _)) OrdKᵢ :
        blackF Q Λ i ν ⋙ OrdKᵢ ⟶ blackF Q Λ i ν ⋙ OrdKᵢ) ≫ (capFOrdIsoOfEq D).hom =
      (capFOrdIsoOfEq D).hom ≫ Functor.whiskerLeft OrdK
        (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) := by
  have hd := intertwines_capDotPlusOp (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν₀ := ν₀) (ν := ν) (i := i)
  have hx := intertwines_unit_of_eq (appendBlackTPAOp_eq_ofEq k Q Λ Λc j hj ν₀ ν i)
  have key := capFOrdIso_dot D hd (D.fwd_dot hd hbwd)
  have h2 : Functor.whiskerLeft OrdK (natTrans.{0, 0} hd) ≫
        Functor.whiskerLeft OrdK (natTrans.{0, 0} hx) =
      Functor.whiskerLeft OrdK (natTrans.{0, 0} hx) ≫ Functor.whiskerLeft OrdK
        (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i)) := by
    have h3 : natTrans.{0, 0} hd ≫ natTrans.{0, 0} hx =
        natTrans.{0, 0} hx ≫ (indDotOfEq Q (plusLabels Λ Λc j hj) i (plusWeight_assoc ν ν₀ i) :
          InductionAlong.functor.{0, 0} (appendBlackOpOfEq Q (plusLabels Λ Λc j hj) i
            (plusWeight_assoc ν ν₀ i)) ⟶ _) := by
      rw [indDotOfEq_eq_natTrans]
      refine (natTrans_comp _ _).trans ((natTrans_eq_of_unit_mul _ _ ?_).trans
        (natTrans_comp _ _).symm)
      rw [hd 1, appendBlackTPAOp_eq_ofEq]
    exact (Functor.whiskerLeft_comp _ _ _).symm.trans
      ((congrArg (Functor.whiskerLeft OrdK) h3).trans (Functor.whiskerLeft_comp _ _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

end Categorification.Stendhal.CupCap
