/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global
import Categorification.KLR.CyclotomicRestrictionProjectiveRing
import Categorification.WeightedKLR.Induction.K0

/-!
# Finitely generated projective modules on the cyclotomic weight spaces

An object of the weight space at `x` (a family of `R^Λ(β)`-modules over the blocks `β` of
weight `x`) is *finitely generated projective* (`IsFGProj`) if every component is a finitely
generated projective `R^Λ(β)`-module and only finitely many components are nonzero; these are
the finitely generated projective modules over `⊕_β R^Λ(β)`. The property is closed under
isomorphisms, under cyclotomic induction `globalE` (`isFGProj_globalE`) and, for `Q` with
`KLRSymm Q` and unit constant leading coefficients and monic `a_i`, under cyclotomic restriction
`globalF` (`isFGProj_globalF`, Kang–Kashiwara, arXiv:1102.4677v4, Corollary 4.6, over every
commutative ring). So the action of `𝒰` restricts to the finitely generated projective modules;
for the universal cyclotomic quotient `Ř^λ` these form the category `Ř^λ-pmod` of B. Webster,
arXiv:1309.3796v2, Corollary 3.27.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ : X)

/-- A biproduct of zero objects is zero. -/
theorem isZero_biproduct_of_forall {D : Type*} [Category D] [Preadditive D] {J : Type*}
    {f : J → D} [HasBiproduct f] (h : ∀ j, IsZero (f j)) : IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun j => (h j).eq_of_src _ _

/-- **Finitely generated projective objects of a cyclotomic weight space**: every component is
a finitely generated projective `R^Λ(β)`-module, and only finitely many are nonzero. -/
def IsFGProj (x : X) : ObjectProperty (weightSpace.{u, v, w} Q a RD Λ x) := fun M =>
  (∀ β, Module.Finite (CycKLR k Q a β.1) (M β) ∧ Module.Projective (CycKLR k Q a β.1) (M β)) ∧
    {β | ¬ IsZero (M β)}.Finite

instance isClosedUnderIsomorphisms_isFGProj (x : X) :
    (IsFGProj.{u, v, w} Q a RD Λ x).IsClosedUnderIsomorphisms where
  of_iso {M M'} e hM := by
    refine ⟨fun β => ?_, hM.2.subset fun β hβ h => hβ (h.of_iso (Pi.isoApp e β).symm)⟩
    have := (hM.1 β).1
    have := (hM.1 β).2
    exact ⟨Module.Finite.equiv (Pi.isoApp e β).toLinearEquiv,
      Module.Projective.of_equiv (Pi.isoApp e β).toLinearEquiv⟩


/-- A zero module is finitely generated projective. -/
theorem finite_projective_of_isZero {R : Type*} [Ring R] {N : ModuleCat.{w} R} (h : IsZero N) :
    Module.Finite R N ∧ Module.Projective R N := by
  have := ModuleCat.isZero_iff_subsingleton.1 h
  exact ⟨inferInstance, Module.Projective.of_free⟩

omit [DecidableEq I] in
theorem blockSucc_injective (i : I) {x y : X} (h : x + RD.iX i = y) :
    Function.Injective (blockSucc RD Λ i h) := fun _ _ hββ' =>
  Subtype.ext (add_left_cancel (congrArg Subtype.val hββ'))

/-- **Cyclotomic induction preserves finitely generated projective objects.** -/
theorem isFGProj_globalE (i : I) {x y : X} (h : x + RD.iX i = y)
    {M : weightSpace.{u, v, w} Q a RD Λ x} (hM : IsFGProj Q a RD Λ x M) :
    IsFGProj Q a RD Λ y ((globalE Q a RD Λ i h).obj.obj M) := by
  have hzero : ∀ δ, ¬ IsZero (((globalE Q a RD Λ i h).obj.obj M) δ) →
      ∃ β, ¬ IsZero (M β) ∧ blockSucc RD Λ i h β = δ := by
    intro δ hδ
    by_contra hne
    push Not at hne
    refine hδ (isZero_biproduct_of_forall fun p => ?_)
    by_cases hp : IsZero (M p.1)
    · exact Functor.map_isZero _ hp
    · exact absurd p.2 (hne p.1 hp)
  refine ⟨fun δ => ?_, (hM.2.image (blockSucc RD Λ i h)).subset fun δ hδ => ?_⟩
  · by_cases hδ : IsZero (((globalE Q a RD Λ i h).obj.obj M) δ)
    · exact finite_projective_of_isZero hδ
    obtain ⟨β, -, hβ⟩ := hzero δ hδ
    have : Unique {β // blockSucc RD Λ i h β = δ} := uniqueOfSubsingleton ⟨β, hβ⟩
    let q : {β // blockSucc RD Λ i h β = δ} := default
    have := (hM.1 q.1).1
    have := (hM.1 q.1).2
    let e := (biproductUniqueIso fun p : {β // blockSucc RD Λ i h β = δ} =>
      (indBlock Q a RD Λ i h p.1 δ p.2).obj (M p.1)).toLinearEquiv
    have hf : Module.Finite (CycKLR k Q a δ.1)
        ((indBlock Q a RD Λ i h q.1 δ q.2).obj (M q.1)) := InductionAlong.Ind.finite _ _
    have hp : Module.Projective (CycKLR k Q a δ.1)
        ((indBlock Q a RD Λ i h q.1 δ q.2).obj (M q.1)) := InductionAlong.Ind.projective _ _
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  · obtain ⟨β, hβ, rfl⟩ := hzero δ hδ
    exact ⟨β, hβ, rfl⟩

/-- The restriction embedding of a block successor is `cyclotomicLast`. -/
theorem lastEmb_self (i : I) (β : Multiset I) (h : {i} + β = {i} + β) :
    lastEmb Q a i h = (KLRAlgebra.AbsentColour.cyclotomicLast Q i a β :
      CycKLR k Q a β →ₙ+* CycKLR k Q a ({i} + β)) := by
  ext r
  rfl

/-- **Cyclotomic restriction preserves finitely generated projective objects** (Kang–Kashiwara,
arXiv:1102.4677v4, Corollary 4.6, over every commutative ring). -/
theorem isFGProj_globalF (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    (ha : ∀ j, (a j).Monic) (i : I) {x y : X} (h : x + RD.iX i = y)
    {N : weightSpace.{u, v, w} Q a RD Λ y} (hN : IsFGProj Q a RD Λ y N) :
    IsFGProj Q a RD Λ x ((globalF Q a RD Λ i h).obj.obj N) := by
  refine ⟨fun β => ?_, (hN.2.preimage (blockSucc_injective RD Λ i h).injOn).subset
    fun β hβ hz => hβ (Functor.map_isZero
      (resBlock Q a RD Λ i h β (blockSucc RD Λ i h β) rfl) hz)⟩
  let N' : ModuleCat.{max (max u v) w} (CycKLR k Q a ({i} + β.1)) := N (blockSucc RD Λ i h β)
  have hf : Module.Finite (CycKLR k Q a ({i} + β.1)) N' := (hN.1 (blockSucc RD Λ i h β)).1
  have hp : Module.Projective (CycKLR k Q a ({i} + β.1)) N' := (hN.1 (blockSucc RD Λ i h β)).2
  exact ⟨CycKLR.finite_res_of_ring a β.1 i hQ ha N',
    CycKLR.projective_res_of_ring a β.1 i hsym hQ ha N'⟩

end

end Categorification.KLR.CyclotomicAction
