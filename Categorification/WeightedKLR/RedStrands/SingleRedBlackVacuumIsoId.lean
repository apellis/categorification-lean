/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackVacuumBlockFunctor
import Categorification.WeightedKLR.RedStrands.SingleRedDerivedTensorIsoId

set_option backward.isDefEq.respectTransparency false

/-!
# Endofunctors of `D(T^λ)` fixing the vacuum, through the derived action, one red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22, step (b), for one red strand. `SingleRed.blackVacuumDerivedTensorIsoId`
feeds the vacuum functor `Φ = blackVacuumFunctor C₀` at the block `ν`
(`blackVacuumBlockFunctor`) into `SingleRed.derivedTensorIsoIdOfVacuum`, with `p 𝐢 = u_𝐢 P_∅`
for 1-morphisms `u_𝐢` out of the vacuum region (Webster's `F_𝐢`). Its remaining inputs are
statements about the derived action `blackPresCL` on `C₀` alone:

* `σ`, `eσ`, `hσ`: a strongly equivariant endofunctor of the derived action with `σ(C₀) ≅ C₀`,
  acting on the block `ν` by the given `S'`;
* `cS`: `S'` is a derived tensor product with a dg bimodule;
* `W`: the block `ν` of `u_𝐢 C₀` is `e(𝐢) T^λ_ν` in degree `0`;
* `hgen`: the left multiplications by the dots and crossings between the `e(𝐢) T^λ_ν` are the
  actions of 2-morphisms `u_𝐢 ⟶ u_𝐣` on `C₀`, read through `W`.

The scalars and the idempotents are handled here (`mem_hitSubring_algebraMap`,
`mem_hitSubring_redFirstIdem`), and the conversion from 2-morphisms of the derived action to
morphisms of `Ř^λ-pmod` is Webster's condition of Definition 3.23
(`blackVacuumBlockFunctor_map_vacEvG`).
-/

open CategoryTheory CategoryTheory.Limits MulOpposite

noncomputable section

namespace Categorification

section RightMul

variable {k : Type*} [CommRing k] {T : Type} [Ring T] [Algebra k T]

theorem idemRightMul_algebraMap_of_mul_eq_zero {e f : T} (hf : IsIdempotentElem f)
    (hef : e * f = 0) (r : k) : idemRightMul e f (algebraMap k T r) hf = 0 :=
  LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
    change x * algebraMap k T r * f = 0
    rw [← Algebra.commutes, ← hx]
    rw [mul_assoc, mul_assoc, hef, mul_zero, mul_zero])

theorem idemRightMul_of_mul_eq_zero_right {e f c : T} (hf : IsIdempotentElem f) (hc : c * f = 0) :
    idemRightMul e f c hf = 0 :=
  LinearMap.ext fun ⟨x, _⟩ => Subtype.ext (by
    change x * c * f = 0
    rw [mul_assoc, hc, mul_zero])

theorem idemRightMul_of_mul_eq_zero_left {e f : T} (hf : IsIdempotentElem f) (hef : e * f = 0) :
    idemRightMul e f f hf = 0 :=
  LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
    change x * f * f = 0
    rw [← hx, mul_assoc, mul_assoc, hf.eq, hef, mul_zero])

theorem idemRightMul_self_self {e : T} (he : IsIdempotentElem e) :
    idemRightMul e e e he = LinearMap.id :=
  LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
    change x * e * e = x
    rw [hx, hx])

end RightMul

namespace Stendhal.SingleRed

open KLR KLRAlgebra TwoRep QuantumGroup KL3.Diagram CyclotomicAction DoubleDiagram StringDiagrams
open scoped Classical
open Pseudofunctor.StrongTrans
open DG.DegreeZero
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

universe w u₁

variable {I : Type} {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

/-- **The dots and crossings of `(T^λ_ν)ᵐᵒᵖ`**: the images of the KLR dots and crossings under
`insertRed`. With the scalars and idempotents they generate (`redFirstGenerators`). -/
def redFirstKLRGenerators : Set (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ :=
  Set.range (fun a => op (insertRed Q Λ ν (KLRAlgebra.x a))) ∪
    Set.range (fun j : ℕ => op (insertRed Q Λ ν (KLRAlgebra.ψ j)))

variable {C : CartanDatum I} {hQ : IsRouquierQ C Q}
  {P : Presentation.{0, 0}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{0, 0, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := 1)) 0 :
      I ⊕ Fin 1 → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin 1, (Λ r i : ℤ))
  (hsym : KLRSymm Q)
  (C₀ : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0),
    _root_.DerivedCategory (ModuleCat.{0} (TensorProductAlgebra k Q Λ β.1)ᵐᵒᵖ))
  (hC₀ : ∀ β, β.1 ≠ 0 → IsZero (C₀ β))

set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν

set_option hygiene false in
local notation "𝕊" => (DerivedCategory.singleFunctor (ModuleCat.{0} Tᵐᵒᵖ) 0)

set_option hygiene false in
local notation "𝒟" => DerivedCategory (ModuleCat.{0} Tᵐᵒᵖ)

set_option hygiene false in
local notation "𝒸" => (⟨⟨(blockWeight RD Λ₀ ν : X)⟩⟩ :
  RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat)

set_option hygiene false in
local notation "νb" => (⟨ν, rfl⟩ : WeightBlocks RD Λ₀ (𝒸).as.region)

variable {Q Λ ν}

section Hit

variable (w : Seq ν → (vacRegion hQ RD Λ₀ ⟶ 𝒸))
  (W : ∀ s, (blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb).obj
      (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map (w s)).obj.obj C₀) ≅
    (𝕊).obj (ModuleCat.of Tᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ ν s))))

/-- The vacuum functor at the block `ν` of its own weight space, with target `D(Mod T^λ_ν)`. -/
def blackVacuumNuFunctor :
    ((univCyclotomicPresCLPmod.{0, 0, 0} hQ RD Λ₀ (blackLam_pair hΛ₀)).obj 𝒸).carrier ⥤ 𝒟 :=
  blackVacuumBlockFunctor hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb

instance blackVacuumNuFunctor_additive :
    (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀ (ν := ν)).Additive :=
  blackVacuumBlockFunctor_additive hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb

instance blackVacuumNuFunctor_linear :
    (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀ (ν := ν)).Linear k :=
  blackVacuumBlockFunctor_linear hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb

/-- `κ` for the vacuum functor: `Φ(u_𝐢 P_∅)_ν ≅ e(𝐢) T^λ_ν`, from `W`. -/
def blackVacuumKappa (s : Seq ν) :
    (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀).obj
        (vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) (w s)) ≅
      (𝕊).obj (ModuleCat.of Tᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ ν s))) :=
  blackVacuumBlockWordIso hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb (w s) ≪≫ W s

/-- **The right multiplication by `y` is hit** as soon as, between all `e(𝐢) T`, it is the action
of a 2-morphism of the derived action on `C₀` (Webster's condition of Definition 3.23,
`blackVacuumBlockFunctor_map_vacEvG`). -/
theorem mem_hitSubring_of_twoMorphisms (y : Tᵐᵒᵖ)
    (hy : ∀ a b, ∃ η : w a ⟶ w b,
      (blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb).map
          (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map₂ η).hom.app C₀) =
        (W a).hom ≫ (𝕊).map (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ ν a)
          (redFirstIdem Q Λ ν b) y (redFirstIdem_isIdempotentElem Q Λ ν b))) ≫ (W b).inv) :
    y ∈ hitSubring (redFirstIdem Q Λ ν) (redFirstIdem_isIdempotentElem Q Λ ν)
      (fun _ _ h => redFirstIdem_mul_of_ne Q Λ ν h) (sum_redFirstIdem Q Λ ν)
      (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀)
      (fun s => vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) (w s))
      (blackVacuumKappa hP hwf hΛ₀ hsym C₀ hC₀ w W) := by
  intro a b
  obtain ⟨η, hη⟩ := hy a b
  refine ⟨vacEvG hQ RD Λ₀ (blackLam_pair hΛ₀) η, ?_⟩
  refine (blackVacuumBlockFunctor_map_vacEvG hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb η).trans ?_
  rw [hη]
  simp only [blackVacuumKappa, Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-- **Scalars are hit**: `Φ` is `k`-linear. -/
theorem mem_hitSubring_algebraMap (r : k) :
    op (algebraMap k T r) ∈ hitSubring (redFirstIdem Q Λ ν)
      (redFirstIdem_isIdempotentElem Q Λ ν)
      (fun _ _ h => redFirstIdem_mul_of_ne Q Λ ν h) (sum_redFirstIdem Q Λ ν)
      (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀)
      (fun s => vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) (w s))
      (blackVacuumKappa hP hwf hΛ₀ hsym C₀ hC₀ w W) := by
  intro a b
  have hr : op (algebraMap k T r) = algebraMap k Tᵐᵒᵖ r := rfl
  by_cases hab : a = b
  · subst hab
    refine ⟨r • 𝟙 _, ?_⟩
    have hm : (𝕊).map (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ ν a)
        (redFirstIdem Q Λ ν a) (op (algebraMap k T r)) (redFirstIdem_isIdempotentElem Q Λ ν a))) =
        r • 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_smul]
      congr 1
      ext ⟨x, hx⟩
      simp only [ModuleCat.hom_ofHom, ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply,
        LinearMap.id_apply]
      change x * op (algebraMap k T r) * redFirstIdem Q Λ ν a = op (algebraMap k T r) * x
      rw [hr, ← Algebra.commutes, mul_assoc, hx]
    rw [hm, CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp,
      Linear.comp_smul, Category.id_comp, Iso.hom_inv_id]
  · refine ⟨0, ?_⟩
    rw [hr, idemRightMul_algebraMap_of_mul_eq_zero _ (redFirstIdem_mul_of_ne Q Λ ν hab)]
    simp

/-- **The idempotents are hit**: right multiplication by `e(𝐬)` from `T e(𝐚)` to `T e(𝐛)` is the
identity for `𝐚 = 𝐬 = 𝐛` and zero otherwise. -/
theorem mem_hitSubring_redFirstIdem (s : Seq ν) :
    redFirstIdem Q Λ ν s ∈ hitSubring (redFirstIdem Q Λ ν)
      (redFirstIdem_isIdempotentElem Q Λ ν)
      (fun _ _ h => redFirstIdem_mul_of_ne Q Λ ν h) (sum_redFirstIdem Q Λ ν)
      (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀)
      (fun s => vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) (w s))
      (blackVacuumKappa hP hwf hΛ₀ hsym C₀ hC₀ w W) := by
  intro a b
  by_cases hsb : s = b
  · subst hsb
    by_cases has : a = s
    · subst has
      refine ⟨𝟙 _, ?_⟩
      rw [idemRightMul_self_self, CategoryTheory.Functor.map_id]
      erw [CategoryTheory.Functor.map_id]
      simp
    · refine ⟨0, ?_⟩
      rw [idemRightMul_of_mul_eq_zero_left _ (redFirstIdem_mul_of_ne Q Λ ν has)]
      simp
  · refine ⟨0, ?_⟩
    rw [idemRightMul_of_mul_eq_zero_right _ (redFirstIdem_mul_of_ne Q Λ ν hsb)]
    simp

end Hit

variable [DG.HasDerivedCategory.{0, 0} Tᵐᵒᵖ]
  {Xb : Type} [AddCommGroup Xb] [DG.DGAddCommGroup Xb] [Module Tᵐᵒᵖ Xb] [Module Tᵐᵒᵖᵐᵒᵖ Xb]
  [DG.DGBimodule Tᵐᵒᵖ Tᵐᵒᵖ Xb]

/-- **Webster, arXiv:1309.3796v3, proof of Proposition 7.22 (b), one red strand, through the
derived action**: let `S'` be an additive endofunctor of `D(Mod T^λ_ν)` (right modules) that is
a derived tensor product with a dg bimodule (`cS`), and the block `ν` component (`hσ`) of a
strongly equivariant endofunctor `σ` of the derived action `blackPresCL` (Theorem 4.31) with
`σ(C₀) ≅ C₀` (`eσ`). Suppose that for 1-morphisms `u_𝐢` out of the vacuum region (Webster's
`F_𝐢`) the block `ν` of `u_𝐢 C₀` is `e(𝐢) T^λ_ν` (`W`), and that the left multiplications by the
dots and crossings between them are actions of 2-morphisms on `C₀` (`hgen`). Then `S' ≅ 𝟭`.

The inputs `W`, `hgen` (the derived action on `F_𝐢 T^λ_∅` is the regular action of the
cyclotomic quotient), `σ, eσ, hσ` and `cS` are hypotheses; the route hypothesis `hΛ₀` is that
of `blackRouqFamily`. -/
def blackVacuumDerivedTensorIsoId (S' : 𝒟 ⥤ 𝒟) [S'.Additive]
    (cS : dgDerivedTensor.{0} Tᵐᵒᵖ Tᵐᵒᵖ Xb ⋙ derivedComparison Tᵐᵒᵖ ≅
      derivedComparison Tᵐᵒᵖ ⋙ S')
    (σ : Stendhal.blackPresCL hP hwf hΛ₀ hsym ⟶ Stendhal.blackPresCL hP hwf hΛ₀ hsym)
    (eσ : (σ.app (vacRegion hQ RD Λ₀)).obj.obj C₀ ≅ C₀)
    (hσ : (σ.app 𝒸).obj ⋙ blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb ≅
      blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb ⋙ S')
    (w : Seq ν → (vacRegion hQ RD Λ₀ ⟶ 𝒸))
    (W : ∀ s, (blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb).obj
        (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map (w s)).obj.obj C₀) ≅
      (𝕊).obj (ModuleCat.of Tᵐᵒᵖ (idemLeftIdeal (redFirstIdem Q Λ ν s))))
    (hgen : ∀ y ∈ redFirstKLRGenerators Q Λ ν, ∀ a b, ∃ η : w a ⟶ w b,
      (blackBlockEval hP hwf hΛ₀ hsym 𝒸 νb).map
          (((Stendhal.blackPresCL hP hwf hΛ₀ hsym).map₂ η).hom.app C₀) =
        (W a).hom ≫ (𝕊).map (ModuleCat.ofHom (idemRightMul (redFirstIdem Q Λ ν a)
          (redFirstIdem Q Λ ν b) y (redFirstIdem_isIdempotentElem Q Λ ν b))) ≫ (W b).inv) :
    S' ≅ 𝟭 _ :=
  derivedTensorIsoIdOfVacuum Q Λ ν S' cS (blackVacuumNuFunctor hP hwf hΛ₀ hsym C₀ hC₀)
    (blackVacuumBlockCompIso hP hwf hΛ₀ hsym C₀ hC₀ 𝒸 νb σ eσ S' hσ)
    (fun s => vacImg hQ RD Λ₀ (blackLam_pair hΛ₀) (w s))
    (blackVacuumKappa hP hwf hΛ₀ hsym C₀ hC₀ w W) (by
      rintro y (((⟨r, rfl⟩ | ⟨s, rfl⟩) | hx) | hψ)
      · exact mem_hitSubring_algebraMap hP hwf hΛ₀ hsym C₀ hC₀ w W r
      · exact mem_hitSubring_redFirstIdem hP hwf hΛ₀ hsym C₀ hC₀ w W s
      · exact mem_hitSubring_of_twoMorphisms hP hwf hΛ₀ hsym C₀ hC₀ w W y
          (hgen y (Or.inl hx))
      · exact mem_hitSubring_of_twoMorphisms hP hwf hΛ₀ hsym C₀ hC₀ w W y
          (hgen y (Or.inr hψ)))

end Stendhal.SingleRed

end Categorification
