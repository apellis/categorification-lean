/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleTowerSl2
import Categorification.WeightedKLR.RedStrands.BlackNilHeckeNilpotent
import Categorification.WeightedKLR.RedStrands.AbsoluteSimple
import Categorification.Sl2Categorification.SimpleHead
import Categorification.Sl2Categorification.NilHeckeLift
import Categorification.CategoryTheory.PiShiftLinear
import Categorification.Algebra.InductionAlongLinear
import Categorification.Algebra.DualRightModule
import Categorification.Algebra.ModuleTowerEnd

/-!
# Simple heads of `Eᵢ L` and `Fᵢ L`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.12: for a simple module `L` over `T^λ`, the heads of `Fᵢ L` and `Eᵢ L` are
simple.

The proof is Chuang–Rouquier's (arXiv:math/0407205v2, Proposition 5.20) applied to the weak
`𝔰𝔩₂`-categorification along an `i`-string (`fgStringWeakSl2`):
* `Eᵢ` and `Fᵢ` are `k`-linear (`fgStringE_linear`, `fgStringF_linear`);
* the dot on the newest black strand gives a nil-Hecke action on `Eᵢ` whose dot is nilpotent
  (`fgStringNilHecke`, `fgStringNilHecke_X_pow_eq_zero`), and its mate is one on `Fᵢ`;
* every endomorphism of a simple module is a scalar (`fgString_finrank_end_simple`), by passing
  to the `k`-dual left module (`DualRightModule.exists_scalar_of_dual`) and the absolute
  irreducibility of simple `T^λ`-modules (`exists_scalar_of_simple`).

The main results are `fgString_head_E` and `fgString_head_F`: any two simple quotients of
`Eᵢ U` (resp. `Fᵢ U`) for `U` simple are isomorphic compatibly with the quotient maps.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Limits _root_.Module MulOpposite QuantumGroup QuantumGroup.UDot KL3.Diagram
  DoubleDiagram

universe u

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Linear

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I)

theorem appendBlackOp_scalarCompatible (ν : Multiset I) :
    InductionAlong.ScalarCompatible (k := k) (appendBlackOp Q Λ i ν) := fun c => by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (appendBlackOp_smul Λ i ν c 1).trans (Algebra.smul_def _ _)

instance blackE_additive (ν : Multiset I) : (blackE Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.resFunctor _).Additive

instance blackF_additive (ν : Multiset I) : (blackF Q Λ i ν).Additive :=
  inferInstanceAs (InductionAlong.functor _).Additive

/-- Webster's `Eᵢ` is `k`-linear. -/
theorem blackE_linear (ν : Multiset I) : (blackE Q Λ i ν).Linear k :=
  InductionAlong.resFunctor_linear (appendBlackOp_scalarCompatible Q Λ i ν)

/-- Webster's `Fᵢ` is `k`-linear. -/
theorem blackF_linear (ν : Multiset I) : (blackF Q Λ i ν).Linear k :=
  InductionAlong.functor_linear (appendBlackOp_scalarCompatible Q Λ i ν)

end Linear

section Generic

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  {C : QuantumGroup.CartanDatum I}
  (hQ : KLR.IsRouquierQ C Q) (i : I) (ν₀ : Multiset I)
  [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)]

instance fgStringE_additive : (fgStringE Λ hQ i ν₀).Additive := by
  have : (stringE Q Λ i ν₀).Additive :=
    @PiShift.down_additive (fun m => ModuleCat.{u} (StringAlg (Q := Q) Λ i ν₀ m)) _ _
      (fun m => blackE Q Λ i (stringWeight i ν₀ m))
      (fun m => blackE_additive Q Λ i (stringWeight i ν₀ m))
  infer_instance

instance fgStringF_additive : (fgStringF (k := k) (Q := Q) Λ i ν₀).Additive := by
  have : (stringF Q Λ i ν₀).Additive :=
    @PiShift.up_additive (fun m => ModuleCat.{u} (StringAlg (Q := Q) Λ i ν₀ m)) _ _ _
      (fun m => blackF Q Λ i (stringWeight i ν₀ m))
      (fun m => blackF_additive Q Λ i (stringWeight i ν₀ m))
  infer_instance

omit [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)] in
theorem fgStringE_linear : (fgStringE Λ hQ i ν₀).Linear k := by
  have := fun m => blackE_linear (k := k) Q Λ i (stringWeight i ν₀ m)
  have := PiShift.down_linear (C := fun m => ModuleCat.{u} (StringAlg (Q := Q) Λ i ν₀ m)) k
    fun m => blackE Q Λ i (stringWeight i ν₀ m)
  exact ObjectProperty.lift_linear k _ _ _

omit [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)] in
theorem fgStringF_linear : (fgStringF (k := k) (Q := Q) Λ i ν₀).Linear k := by
  have := fun m => blackF_linear (k := k) Q Λ i (stringWeight i ν₀ m)
  have := PiShift.up_linear (C := fun m => ModuleCat.{u} (StringAlg (Q := Q) Λ i ν₀ m)) k
    fun m => blackF Q Λ i (stringWeight i ν₀ m)
  exact ObjectProperty.lift_linear k _ _ _

/-- The nil-Hecke action on `Eᵢ` on finitely generated modules along the string. -/
def fgStringNilHecke : Sl2.NilHeckeData (fgStringE Λ hQ i ν₀) :=
  Sl2.NilHeckeData.lift (ModuleTower.towerFinite _) _ (stringNilHecke Q Λ i ν₀)

omit [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)] in
include hQ in
/-- The dots on the newest black strand along the string have a uniform nilpotency exponent. -/
theorem exists_appendedDot_pow_eq_zero :
    ∃ N, ∀ m, op (appendedDot Q Λ i (stringWeight i ν₀ m)) ^ N = 0 := by
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hQ i ν₀
  exact InductionAlong.exists_pow_eq_zero_of_subsingleton
    (R := fun m => StringAlg (Q := Q) Λ i ν₀ (m + 1))
    (fun m => op (appendedDot Q Λ i (stringWeight i ν₀ m)))
    (fun m => (isNilpotent_appendedDot Q Λ i (stringWeight i ν₀ m) hQ).op)
    ⟨B, fun m hm => hB (m + 1) (by omega)⟩

omit [∀ m, IsNoetherianRing (StringAlg (Q := Q) Λ i ν₀ m)] in
theorem exists_fgStringNilHecke_X_pow_eq_zero :
    ∃ N, (fgStringNilHecke Λ hQ i ν₀).X ^ N = 0 := by
  obtain ⟨N, hN⟩ := exists_appendedDot_pow_eq_zero Λ hQ i ν₀
  refine ⟨N, Sl2.NilHeckeData.lift_X_pow_eq_zero _ _ _ ?_⟩
  exact InductionAlong.resTowerX_pow_eq_zero _ _ _ hN

include hQ in
/-- **`End(S) = k`** for the simple modules along the string (Chuang–Rouquier,
arXiv:math/0407205v2, §5.2.1), from the absolute irreducibility of simple `T^λ`-modules. -/
theorem fgString_finrank_end_simple [∀ m, IsArtinianRing (StringAlg (Q := Q) Λ i ν₀ m)]
    (S : ModuleTower.FGTower (StringAlg (Q := Q) Λ i ν₀)) [Simple S] :
    Module.finrank k (S ⟶ S) = 1 := by
  refine ModuleTower.finrank_end_simple k (fun m M hM f => ?_) S
  let T := TensorProductAlgebra k Q Λ (stringWeight i ν₀ m)
  let : Module k M := Module.compHom M (algebraMap k Tᵐᵒᵖ)
  have : IsScalarTower k Tᵐᵒᵖ M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite k Tᵐᵒᵖ := tensorProductAlgebra_op_finite Λ hQ _
  have : Nontrivial M := IsSimpleModule.nontrivial Tᵐᵒᵖ M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have : Module.Finite k M := Module.Finite.of_surjective
    ((LinearMap.toSpanSingleton Tᵐᵒᵖ M v).restrictScalars k)
    (IsSimpleModule.toSpanSingleton_surjective Tᵐᵒᵖ hv)
  let := DualRightModule.dualModule k T M
  have := DualRightModule.isScalarTower_dual (k := k) (T := T) (M := M)
  have := DualRightModule.isSimpleModule_dual k T M
  obtain ⟨c, hc⟩ := DualRightModule.exists_scalar_of_dual
    (fun g => exists_scalar_of_simple (M := Module.Dual k M) Λ (stringWeight i ν₀ m) hQ g) f.hom
  exact ⟨c, hc⟩

end Generic

section CL

open CategoryTheory.Idempotents StringDiagrams KLR TwoRep CyclotomicAction InductionAlong

open scoped Classical

variable {I : Type u} {ℓ : ℕ} (i : I) (ν₀ : Multiset I) {Λ : Fin ℓ → I →₀ ℕ}
  {C : CartanDatum I} {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Str" => StringAlg (k := k) (Q := CL.qCL KL) Λ i ν₀

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, u} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C)
      (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)

include hstd hP hwf in
/-- **Webster, arXiv:1309.3796v2, Proposition 5.12, for `Eᵢ`**: for `U` simple, any two simple
quotients of `Eᵢ U` are isomorphic compatibly with the quotient maps, so the head of `Eᵢ U` is
simple. This is Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20, for the weak
`𝔰𝔩₂`-categorification along an `i`-string through `ν₀ ∌ i`. -/
theorem fgString_head_E (hR : KLR.IsRouquierQ C (CL.qCL KL))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀)
    {U : ModuleTower.FGTower Str} (hU : Simple U) {S₁ S₂ : ModuleTower.FGTower Str}
    [Simple S₁] [Simple S₂]
    (q₁ : (fgStringE Λ hR i ν₀).obj U ⟶ S₁)
    (q₂ : (fgStringE Λ hR i ν₀).obj U ⟶ S₂)
    [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ := by
  let A := fgStringWeakSl2 i ν₀ hstd hP hwf hR hi
  have : A.E.Additive := fgStringE_additive Λ hR i ν₀
  have : A.F.Additive := fgStringF_additive (k := k) (Q := CL.qCL KL) Λ i ν₀
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hR i ν₀
  have := ModuleTower.isArtinianObject hB
  have := ModuleTower.isNoetherianObject hB
  have : A.E.Linear k := fgStringE_linear (k := k) Λ hR i ν₀
  have : A.F.Linear k := fgStringF_linear (k := k) (Q := CL.qCL KL) Λ i ν₀
  let DE := fgStringNilHecke Λ hR i ν₀
  let adj := fgStringEFAdj i ν₀ hstd hP hwf hR
  obtain ⟨N, hN⟩ := exists_fgStringNilHecke_X_pow_eq_zero Λ hR i ν₀
  exact A.exists_iso_of_epi_E DE (DE.dual adj) k
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
      (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
    (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S) hU q₁ q₂

include hstd hP hwf in
/-- **Webster, arXiv:1309.3796v2, Proposition 5.12, for `Fᵢ`**: for `U` simple, any two simple
quotients of `Fᵢ U` are isomorphic compatibly with the quotient maps, so the head of `Fᵢ U` is
simple (Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20). -/
theorem fgString_head_F (hR : KLR.IsRouquierQ C (CL.qCL KL))
    [∀ m, IsNoetherianRing (Str m)] [∀ m, IsArtinianRing (Str m)] (hi : i ∉ ν₀)
    {U : ModuleTower.FGTower Str} (hU : Simple U) {S₁ S₂ : ModuleTower.FGTower Str}
    [Simple S₁] [Simple S₂]
    (q₁ : (fgStringF (k := k) (Q := CL.qCL KL) Λ i ν₀).obj U ⟶ S₁)
    (q₂ : (fgStringF (k := k) (Q := CL.qCL KL) Λ i ν₀).obj U ⟶ S₂)
    [Epi q₁] [Epi q₂] :
    ∃ e : S₁ ≅ S₂, q₁ ≫ e.hom = q₂ := by
  let A := fgStringWeakSl2 i ν₀ hstd hP hwf hR hi
  have : A.E.Additive := fgStringE_additive Λ hR i ν₀
  have : A.F.Additive := fgStringF_additive (k := k) (Q := CL.qCL KL) Λ i ν₀
  obtain ⟨B, hB⟩ := exists_subsingleton_stringAlg (k := k) Λ hR i ν₀
  have := ModuleTower.isArtinianObject hB
  have := ModuleTower.isNoetherianObject hB
  have : A.E.Linear k := fgStringE_linear (k := k) Λ hR i ν₀
  have : A.F.Linear k := fgStringF_linear (k := k) (Q := CL.qCL KL) Λ i ν₀
  let DE := fgStringNilHecke Λ hR i ν₀
  let adj := fgStringEFAdj i ν₀ hstd hP hwf hR
  obtain ⟨N, hN⟩ := exists_fgStringNilHecke_X_pow_eq_zero Λ hR i ν₀
  exact A.exists_iso_of_epi_F DE (DE.dual adj) k
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero hN)
    (Sl2.NilHeckeData.isNilpotent_app_of_pow_eq_zero
      (Sl2.NilHeckeData.dual_X_pow_eq_zero DE adj hN))
    (fun S _ => fgString_finrank_end_simple Λ hR i ν₀ S) hU q₁ q₂

end CL

end Categorification.Stendhal
