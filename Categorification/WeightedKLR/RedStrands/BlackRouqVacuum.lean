/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqPresCL
import Categorification.KLR.CyclotomicAction.VacuumUniversal
import Categorification.Algebra.TriangulatedIdempotentComplete
import Categorification.Diagrams.BicatInterpAdmissibleLinear

/-!
# The universal property of `Ř^λ-pmod` applied to the derived action on `D(T^λ)`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Corollary 3.27
(the universal property of `Ř^λ-pmod`, `KLR.CyclotomicAction.vacuumFunctor`), applied to the
module category of Theorem 4.31 (`blackPresCL`, the Cautis–Lauda presentation acting on the
weight spaces of the derived categories `D(T^λ_β)` of right `T^λ`-modules), with `λ = Σ_r λ_r`
(`blackLam`).

* `univScalars_eq_rouquierScalars`: the scalars of `Ř^λ-pmod` and of `blackPresCL` agree, so
  both are module categories over the same presented 2-category.
* `blackPresCL_map₂Linear`: the action is additive and `k`-linear on 2-morphisms.
* `isZero_blackPresCL_map_vacuum`: an object of the weight space at `Λ₀` supported on the empty
  block is killed by every `E_i` (Webster's `E_i` acts by restriction).
* The weight spaces have finite biproducts and are idempotent complete
  (`DerivedCategory.moduleCat_isIdempotentComplete`, Bökstedt–Neeman).
* `blackVacuumFunctor`: for such an object `C₀`, **the strongly equivariant functor
  `Ř^λ-pmod ⟶ D(T^λ)` sending `P_∅` to `C₀`** (`blackVacuumFunctorAppIso`), unique up to an
  isomorphism extending a given one at `P_∅` (`blackVacuumFunctorIso`).
* `blackRegularVacuum`: the object `T^λ_∅` (the algebra with no black strands, as a right module
  over itself, in degree `0`) on the empty block, which satisfies the hypothesis.

The hypotheses are those of `blackPresCL`, including the route hypothesis `hΛ₀` of
`blackRouqFamily`, and the derived categories are taken with morphisms in the universe of the
algebras (`HasDerivedCategory.{u}`; such a model is `DerivedCategory.smallModuleCat`), so that
`D(T^λ)` and `Ř^λ-pmod` live in the same bicategory `LinearCat k`. Webster's category is the
derived category of the graded finite-dimensional modules (the category `𝒱^λ`); here it is the
unbounded ungraded derived category of all right modules, which is idempotent complete by
Bökstedt–Neeman rather than by finiteness.
-/

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR TwoRep QuantumGroup KL3.Diagram CyclotomicAction
  DoubleDiagram StringDiagrams
open scoped Classical ZeroObject

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

noncomputable section

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {hQ : IsRouquierQ C Q}
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{u} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

set_option hygiene false in
local notation "D" β => _root_.DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

variable (hQ RD) in
/-- **The scalars of `Ř^λ-pmod` are those of the derived action**: both are the Kang–Kashiwara
scalars `kkScalars` of `Q`. -/
theorem univScalars_eq_rouquierScalars :
    univScalars hQ RD = rouquierScalars hQ hsym := rfl

variable (Λ) in
/-- The highest weight `λ = Σ_r λ_r` of the tensor product, as a function `I → ℕ`. -/
def blackLam (i : I) : ℕ := ∑ r : Fin ℓ, Λ r i

omit [Field k] in
include hΛ₀ in
theorem blackLam_pair : ∀ i, (blackLam Λ i : ℤ) = RD.pair (RD.iY i) Λ₀ := fun i => by
  rw [hΛ₀, blackLam, Nat.cast_sum]

/-- **The derived action is additive and `k`-linear on 2-morphisms.** -/
theorem blackPresCL_map₂Linear :
    Generated.Map₂Linear (blackPresCL hP hwf hΛ₀ hsym) :=
  ⟨fun φ ψ _ => by
      erw [Diagrams.BicatInterp.admissiblePseudofunctor_map₂_add]
      rfl,
    fun r φ _ => by
      erw [Diagrams.BicatInterp.admissiblePseudofunctor_map₂_smul]
      rfl⟩

omit [Field k] in
/-- An object of a product of categories all of whose components are zero is zero. -/
theorem isZero_pi_of_forall {J : Type*} {E : J → Type*} [∀ j, Category (E j)] {V : ∀ j, E j}
    (hV : ∀ j, IsZero (V j)) : IsZero V where
  unique_to W := ⟨⟨⟨fun j => (hV j).to_ (W j)⟩, fun _ => funext fun j => (hV j).eq_of_src _ _⟩⟩
  unique_from W := ⟨⟨⟨fun j => (hV j).from_ (W j)⟩, fun _ => funext fun j => (hV j).eq_of_tgt _ _⟩⟩

variable (hQ RD Λ₀) in
/-- **A downward strand kills an object supported on the empty block**: Webster's `E_i` acts on
the derived categories by restriction, which vanishes on the block without black strands. -/
theorem isZero_blackPresCL_map_vacuum
    {b : RevBicat (KL3.Diagram.CL.presCL RD k (univScalars hQ RD)).Bicat}
    (x : vacRegion hQ RD Λ₀ ⟶ b) (i : I) (r : X)
    (hx : (LinearCat.revHom x).obj.word = [⟨(false, i), r⟩])
    (C₀ : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0), D β.1)
    (hC₀ : ∀ β, β.1 ≠ 0 → IsZero (C₀ β)) :
    IsZero (((blackPresCL hP hwf hΛ₀ hsym).map x).obj.obj C₀) := by
  obtain ⟨⟨rb⟩⟩ := b
  obtain ⟨⟨st, w'⟩, h1, h2, h3⟩ := x
  change w' = _ at hx
  subst hx
  refine isZero_pi_of_forall fun β => Functor.map_isZero _ (hC₀ _ ?_)
  change ({i} + β.1 : Multiset I) ≠ 0
  exact fun h => Multiset.singleton_ne_zero i (add_eq_zero.1 h).1

omit [Field k] in
/-- The weight spaces of the derived action have finite biproducts. -/
instance blackPresCL_hasFiniteBiproducts
    (c : RevBicat (KL3.Diagram.CL.presCL RD k (rouquierScalars hQ hsym)).Bicat) :
    HasFiniteBiproducts ((blackPresCL hP hwf hΛ₀ hsym).obj c).carrier :=
  have : HasFiniteProducts ((blackPresCL hP hwf hΛ₀ hsym).obj c).carrier :=
    Pi.hasFiniteProducts_of_hasFiniteProducts
      (C := fun β : WeightBlocks RD Λ₀ c.as.region => D β.1)
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **The weight spaces of the derived action are idempotent complete**: they are products of
derived categories of module categories (`DerivedCategory.moduleCat_isIdempotentComplete`,
Bökstedt–Neeman). -/
instance blackPresCL_isIdempotentComplete
    (c : RevBicat (KL3.Diagram.CL.presCL RD k (rouquierScalars hQ hsym)).Bicat) :
    IsIdempotentComplete ((blackPresCL hP hwf hΛ₀ hsym).obj c).carrier :=
  have : ∀ β : WeightBlocks RD Λ₀ c.as.region, IsIdempotentComplete (D β.1) := fun _ =>
    DerivedCategory.moduleCat_isIdempotentComplete.{u} _
  Pi.isIdempotentComplete (C := fun β : WeightBlocks RD Λ₀ c.as.region => D β.1)

section Vacuum

open Pseudofunctor.StrongTrans

variable (C₀ : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0), D β.1)
  (hC₀ : ∀ β, β.1 ≠ 0 → IsZero (C₀ β))

/-- **Webster, arXiv:1309.3796v3, Corollary 3.27, for the derived action of Theorem 4.31**: for
an object `C₀` of the weight space of `D(T^λ)` at `Λ₀` supported on the empty block (so killed
by every `E_i`, `isZero_blackPresCL_map_vacuum`), the strongly equivariant functor
`Ř^λ-pmod ⟶ D(T^λ)`, `λ = Σ_r λ_r`, sending `P_∅` to `C₀` (`blackVacuumFunctorAppIso`).

The hypotheses are those of `blackPresCL`, including the route hypothesis `hΛ₀` of
`blackRouqFamily`; the derived categories have morphisms in `Type u` (as in
`DerivedCategory.smallModuleCat`). -/
def blackVacuumFunctor :
    StronglyEquivariant (univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀))
      (blackPresCL hP hwf hΛ₀ hsym) :=
  vacuumFunctor hQ RD Λ₀ (blackLam_pair hΛ₀) (blackPresCL hP hwf hΛ₀ hsym)
    (blackPresCL_map₂Linear hP hwf hΛ₀ hsym) C₀
    (fun _ x i r hx => isZero_blackPresCL_map_vacuum (hQ := hQ) (RD := RD) (Λ₀ := Λ₀) hP hwf hΛ₀
      hsym x i r hx C₀ hC₀)

/-- The functor `blackVacuumFunctor` sends `P_∅` to `C₀`. -/
def blackVacuumFunctorAppIso :
    ((blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀).app (vacRegion hQ RD Λ₀)).obj.obj
      (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) ≅ C₀ :=
  vacuumFunctorAppIso hQ RD Λ₀ (blackLam_pair hΛ₀) (blackPresCL hP hwf hΛ₀ hsym)
    (blackPresCL_map₂Linear hP hwf hΛ₀ hsym) C₀
    (fun _ x i r hx => isZero_blackPresCL_map_vacuum (hQ := hQ) (RD := RD) (Λ₀ := Λ₀) hP hwf hΛ₀
      hsym x i r hx C₀ hC₀)

/-- **Uniqueness in Corollary 3.27 for the derived action** (Webster, arXiv:1309.3796v3): a
strongly equivariant functor `Ř^λ-pmod ⟶ D(T^λ)` sending `P_∅` to `C₀` is isomorphic to
`blackVacuumFunctor`, by an isomorphism extending the given one at `P_∅`
(`blackVacuumFunctorIso_hom_app`). -/
def blackVacuumFunctorIso
    (β : univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
      blackPresCL hP hwf hΛ₀ hsym)
    (e₀ : (β.app (vacRegion hQ RD Λ₀)).obj.obj (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) ≅ C₀) :
    β ≅ (blackVacuumFunctor hP hwf hΛ₀ hsym C₀ hC₀ :
      univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
        blackPresCL hP hwf hΛ₀ hsym) :=
  vacuumFunctorIso hQ RD Λ₀ _
    (e₀ ≪≫ (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀).symm)

theorem blackVacuumFunctorIso_hom_app
    (β : univCyclotomicPresCLPmod.{u, u, u} hQ RD Λ₀ (blackLam_pair hΛ₀) ⟶
      blackPresCL hP hwf hΛ₀ hsym)
    (e₀ : (β.app (vacRegion hQ RD Λ₀)).obj.obj (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) ≅ C₀) :
    ((blackVacuumFunctorIso hP hwf hΛ₀ hsym C₀ hC₀ β e₀).hom.as.app
        (vacRegion hQ RD Λ₀)).hom.app (univVacuum hQ RD Λ₀ (blackLam_pair hΛ₀)) =
      e₀.hom ≫ (blackVacuumFunctorAppIso hP hwf hΛ₀ hsym C₀ hC₀).inv :=
  vacuumFunctorIso_hom_app hQ RD Λ₀ _ _

end Vacuum

variable (Q Λ RD Λ₀) in
/-- **The object `T^λ_∅`** of the weight space at `Λ₀`: the algebra with no black strands as a
right module over itself, in degree `0`, on the empty block, and zero on the other blocks. -/
def blackRegularVacuum : ∀ β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0), D β.1 := fun β =>
  if h : β.1 = 0 then
    cast (congrArg (fun γ : Multiset I => D γ) h.symm)
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (TensorProductAlgebra k Q Λ 0)ᵐᵒᵖ (TensorProductAlgebra k Q Λ 0)))
  else 0

theorem isZero_blackRegularVacuum (β : WeightBlocks RD Λ₀ (blockWeight RD Λ₀ 0))
    (hβ : β.1 ≠ 0) : IsZero (blackRegularVacuum Q Λ RD Λ₀ β) := by
  unfold blackRegularVacuum
  split_ifs with h
  · exact absurd h hβ
  · exact isZero_zero _

end

end Categorification.Stendhal
