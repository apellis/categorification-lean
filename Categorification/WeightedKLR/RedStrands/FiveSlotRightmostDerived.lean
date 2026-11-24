/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralPrincipalDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotRightImageEmbedding
import Categorification.WeightedKLR.RedStrands.FiveSlotRightmostTwoBlackCrossing
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Derived concentration at the rightmost five-slot loading

Webster, arXiv:1309.3796v2, Lemma 6.8, (6.21).
The kernel of the second central crossing is a retract of the left-extreme
loading projective. Its inclusion into the central loading factors through
the principal map. The degree-zero mono at the central cut gives the shift
for the crossing image, and the nilHecke splitting gives concentration of
the rightmost loading kernel. The second shift gives the partial standard.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

section Range
universe w
variable {B A M N : Type} [Ring B] [Ring A] [AddCommGroup M] [Module B M] [AddCommGroup N]
  [Module B N]

private def crossingRangeShortComplex (f : M →ₗ[B] N) : ShortComplex (ModuleCat B) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker f).subtype) (ModuleCat.ofHom (LinearMap.ker f).mkQ)
    (by
      rw [← ModuleCat.ofHom_comp, (LinearMap.exact_subtype_mkQ (LinearMap.ker f)).linearMap_comp_eq_zero,
        ModuleCat.ofHom_zero])

private theorem crossingRangeShortComplex_shortExact (f : M →ₗ[B] N) :
    (crossingRangeShortComplex f).ShortExact := by
  let S := crossingRangeShortComplex f
  let : Mono S.f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).subtype_injective
  let : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr (LinearMap.ker f).mkQ_surjective
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
    (LinearMap.exact_subtype_mkQ (LinearMap.ker f))⟩

variable [HasDerivedCategory.{w,0} B] [HasDerivedCategory.{w,0} A]

private abbrev crossingH (F : DerivedCategory.{w,0} B ⥤ DerivedCategory.{w,0} A) (j : ℤ) :=
  degreeZeroModuleFunctor B ⋙ Q ⋙ F ⋙ homologyFunctor ℤ j

/-- The (6.21) shift applied to the range of its crossing map. -/
private theorem crossingRange_homology_vanish (F : DerivedCategory.{w,0} B ⥤ DerivedCategory.{w,0} A)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (f : M →ₗ[B] N)
    (hker : ∀ n : ℤ, n ≠ 0 → IsZero ((crossingH F n).obj (ModuleCat.of B (LinearMap.ker f))))
    (hmid : ∀ n : ℤ, n ≠ 0 → IsZero ((crossingH F n).obj (ModuleCat.of B M)))
    (hzero : Mono ((crossingH F 0).map (ModuleCat.ofHom (LinearMap.ker f).subtype)))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((crossingH F n).obj (ModuleCat.of B (LinearMap.range f))) := by
  let S := crossingRangeShortComplex f
  have hz : IsZero ((crossingH F n).obj S.X₃) := by
    apply isZero_derivedHomology_quotient_of_filtered_kernel F S (crossingRangeShortComplex_shortExact f)
      (L := fun _ : Unit => S.X₁) (m := [()])
      (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _))
      (fun _ _ => hker) hmid hzero n hn
  exact hz.of_iso ((crossingH F n).mapIso f.quotKerEquivRange.toModuleIso.symm)


/-- A split realization of a crossing kernel inside an acyclic module makes
the actual quotient acyclic when the larger inclusion is degree-zero monic. -/
private theorem crossingRange_homology_vanish_of_retract {L : Type} [AddCommGroup L] [Module B L]
    (F : DerivedCategory.{w,0} B ⥤ DerivedCategory.{w,0} A)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (f : M →ₗ[B] N)
    (u : L →ₗ[B] M) (i : LinearMap.ker f →ₗ[B] L) (r : L →ₗ[B] LinearMap.ker f)
    (hcomp : u.comp i = (LinearMap.ker f).subtype) (hsplit : r.comp i = LinearMap.id)
    (hsrc : ∀ n : ℤ, n ≠ 0 → IsZero ((crossingH F n).obj (ModuleCat.of B L)))
    (hmid : ∀ n : ℤ, n ≠ 0 → IsZero ((crossingH F n).obj (ModuleCat.of B M)))
    (hzero : Mono ((crossingH F 0).map (ModuleCat.ofHom u)))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((crossingH F n).obj (ModuleCat.of B (LinearMap.range f))) := by
  have split (j : ℤ) :
      (crossingH F j).map (ModuleCat.ofHom i) ≫ (crossingH F j).map (ModuleCat.ofHom r) = 𝟙 _ := by
    rw [← Functor.map_comp, ← ModuleCat.ofHom_comp, hsplit, ModuleCat.ofHom_id]
    exact CategoryTheory.Functor.map_id _ _
  have hker (j : ℤ) (hj : j ≠ 0) : IsZero ((crossingH F j).obj (ModuleCat.of B (LinearMap.ker f))) := by
    have h := split j
    have hi : (crossingH F j).map (ModuleCat.ofHom i) = 0 := (hsrc j hj).eq_of_tgt _ _
    rw [hi, zero_comp] at h
    exact (IsZero.iff_id_eq_zero _).mpr h.symm
  have hz : Mono ((crossingH F 0).map (ModuleCat.ofHom (LinearMap.ker f).subtype)) := by
    let : IsSplitMono ((crossingH F 0).map (ModuleCat.ofHom i)) :=
      IsSplitMono.mk' ⟨(crossingH F 0).map (ModuleCat.ofHom r), split 0⟩
    rw [← hcomp, ModuleCat.ofHom_comp, Functor.map_comp]
    infer_instance
  exact crossingRange_homology_vanish F f hker hmid hz n hn


/-- The split product sequence gives vanishing on two copies of an acyclic module. -/
private theorem crossingProd_homology_vanish
    (F : DerivedCategory.{w,0} B ⥤ DerivedCategory.{w,0} A)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (n : ℤ)
    (h : IsZero ((crossingH F n).obj (ModuleCat.of B M))) :
    IsZero ((crossingH F n).obj (ModuleCat.of B (M × M))) := by
  have hfil : ModuleFiltration.HasFiltration
      (fun _ : Unit => ModuleCat.of B M) [(), ()] (ModuleCat.of B (M × M)) :=
    ModuleFiltration.HasFiltration.cons (X := ModuleCat.of B M) (Z := ModuleCat.of B M)
      (LinearMap.inl B M M) (LinearMap.snd B M M) [()] ()
      (fun _ _ e => congrArg Prod.fst e) Function.Exact.inl_snd (fun a => ⟨(0,a),rfl⟩)
      (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ⟨LinearEquiv.refl _ _⟩
  exact hfil.isZero_derivedHomology F n (fun _ _ => h)

end Range

end Categorification


noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA CornerEndomorphism MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private def rightIdealLeftMul {B : Type} [Ring B] {f : B} (c : rIdeal f) :
    rIdeal f →ₗ[Bᵐᵒᵖ] rIdeal f where
  toFun a := ⟨c.1 * a.1, by
    change f * (c.1 * a.1) = c.1 * a.1
    rw [← mul_assoc, mem_rIdeal.mp c.2]⟩
  map_add' a b := Subtype.ext (mul_add c.1 a.1 b.1)
  map_smul' s a := Subtype.ext (mul_assoc c.1 a.1 s.unop).symm

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun t => F (e t)
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fixedTopFourExitCut 1
local notation "E₂" => fixedTopFourExitCut 2
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord E₀))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₂))
private theorem sameOrder₀ : redWord E₀ = redWord E₂ := by decide
private theorem sameOrder₁ : redWord E₁ = redWord E₂ := by decide
local notation "f₀" => orderedLoadingIdemAt Q Λ (redWord E₂) E₀ sameOrder₀
local notation "f₁" => orderedLoadingIdemAt Q Λ (redWord E₂) E₁ sameOrder₁
local notation "P₀" => rIdeal f₀
local notation "P₁" => rIdeal f₁
local notation "K₁" => blockLoadingKernel Q Λ E₁ 1 2
local notation "K₂" => blockLoadingKernel Q Λ E₂ 1 2
local notation "u₀" => F (ψw [3,2] * e E₀)
local notation "c₀" => F (ψw [2,1] * e E₁)
local notation "c₁" => F (ψw [3,2,1] * e E₁)
local notation "δ₀" => F (ψ 1 : R)
local notation "x₁" => F (x (⟨1, by decide⟩ : Fin N) : R)
local notation "x₂" => F (x (⟨2, by decide⟩ : Fin N) : R)

private theorem leftExtreme_support (a : P₀) : p E₀ * a.1.1 = a.1.1 := by
  have h := a.2
  change f₀ * a.1 = a.1 at h
  exact congrArg (fun z : T => z.1) h

private theorem central_support (a : P₁) : p E₁ * a.1.1 = a.1.1 := by
  have h := a.2
  change f₁ * a.1 = a.1 at h
  exact congrArg (fun z : T => z.1) h

private def leftExtremeLeftMultiply (c : V) : P₀ →ₗ[Tᵐᵒᵖ] P₀ :=
  rightIdealLeftMul (blockLoadingRep Q Λ E₀ c)

private theorem leftExtremeLeftMultiply_val (c : V) (hc : p E₀ * c = c * p E₀) (a : P₀) :
    (leftExtremeLeftMultiply Q Λ c a).1.1 = c * a.1.1 := by
  change (blockLoadingRep Q Λ E₀ c).1.1 * a.1.1 = _
  have ha : E * a.1.1 = a.1.1 := corner_mul_left _ a.1
  rw [blockLoadingRep_val]
  change p E₀ * c * E * a.1.1 = _
  rw [mul_assoc (p E₀ * c), ha, hc, mul_assoc c, leftExtreme_support Q Λ a]

private def leftExtremeDelta : P₀ →ₗ[Tᵐᵒᵖ] P₀ := leftExtremeLeftMultiply Q Λ δ₀
private def leftExtremeDot : P₀ →ₗ[Tᵐᵒᵖ] P₀ := leftExtremeLeftMultiply Q Λ x₁

private theorem leftExtremeDelta_val (a : P₀) :
    (leftExtremeDelta Q Λ a).1.1 = δ₀ * a.1.1 := by
  apply leftExtremeLeftMultiply_val
  rw [← map_mul, ← map_mul, e_mul_ψ, show sadj N 1 • E₀ = E₀ by decide]

private theorem leftExtremeDot_val (a : P₀) :
    (leftExtremeDot Q Λ a).1.1 = x₁ * a.1.1 := by
  apply leftExtremeLeftMultiply_val
  rw [← map_mul, ← map_mul, x_mul_e]

private theorem leftExtremeDelta_square (a : P₀) : leftExtremeDelta Q Λ (leftExtremeDelta Q Λ a) = 0 := by
  apply Subtype.ext; apply Subtype.ext
  change (leftExtremeDelta Q Λ (leftExtremeDelta Q Λ a)).1.1 = (0 : V)
  rw [leftExtremeDelta_val, leftExtremeDelta_val, ← mul_assoc, ← leftExtreme_support Q Λ a, ← mul_assoc]
  have h : (ψ 1 * ψ 1 * e E₀ : R) = 0 := by
    rw [ψ_sq 1 (by decide : 1+1<N), ite_eq_left (by decide)]
  have hm := congrArg F h
  simp only [map_mul, map_zero] at hm
  rw [hm, zero_mul]

private theorem leftExtremeDelta_contract (a : P₀) (ha : leftExtremeDelta Q Λ a = 0) :
    leftExtremeDelta Q Λ (leftExtremeDot Q Λ a) = a := by
  have h : (ψ 1 * x (⟨1,by decide⟩ : Fin N) * e E₀ -
      x (⟨2,by decide⟩ : Fin N) * ψ 1 * e E₀ : R) = e E₀ := by
    rw [← sub_mul, dot_cross_right 1 (by decide : 1+1<N), ite_eq_left (by decide)]
  have hm := congrArg (fun b : R => F b * a.1.1) h
  have hz := congrArg (fun b : P₀ => b.1.1) ha
  change (leftExtremeDelta Q Λ a).1.1 = (0 : V) at hz
  rw [leftExtremeDelta_val] at hz
  apply Subtype.ext; apply Subtype.ext
  rw [leftExtremeDelta_val, leftExtremeDot_val]
  simpa only [map_mul, map_sub, sub_mul, mul_assoc, leftExtreme_support Q Λ a, hz, mul_zero, sub_zero] using hm

private def leftExtremeToCentral : P₀ →ₗ[Tᵐᵒᵖ] P₁ where
  toFun a := (fiveSlotCentralPrincipalKernelMap Q Λ a).1
  map_add' a b := congrArg Subtype.val (map_add (fiveSlotCentralPrincipalKernelMap Q Λ) a b)
  map_smul' r a := by
    apply Subtype.ext; apply Subtype.ext
    change (fiveSlotCentralPrincipalKernelMap Q Λ ((r • a) : P₀)).1.1.1 =
      (fiveSlotCentralPrincipalKernelMap Q Λ a).1.1.1 * r.unop.1
    calc
      _ = u₀ * ((r • a : P₀).1.1) := fiveSlotCentralPrincipalKernelMap_val Q Λ ((r • a) : P₀)
      _ = (u₀ * a.1.1) * r.unop.1 := (mul_assoc u₀ a.1.1 r.unop.1).symm
      _ = _ := congrArg (· * r.unop.1) (fiveSlotCentralPrincipalKernelMap_val Q Λ a).symm

private theorem leftExtremeToCentral_val (a : P₀) :
    (leftExtremeToCentral Q Λ a).1.1 = u₀ * a.1.1 :=
  fiveSlotCentralPrincipalKernelMap_val Q Λ a

private theorem leftExtremeToCentral_injective (hQ : KLRSymm Q) :
    Function.Injective (leftExtremeToCentral Q Λ) := by
  intro a b h
  apply fiveSlotCentralPrincipalKernelMap_injective_of_cancellation Q Λ
    (fun y hy _ hz => fiveSlotCentral_leftWord_cancel_of_leftSupport Q Λ hQ y hy hz)
  exact Subtype.ext h

section Second
variable (hQ : KLRSymm Q)

private def centralToRightmostSecond : P₁ →ₗ[Tᵐᵒᵖ] K₂ :=
  (fiveSlotRightmostKernel_nilHecke Q Λ).comp (fiveSlotRightmost_firstCentralMap Q Λ hQ)

private theorem centralToRightmostSecond_val (a : P₁) :
    (centralToRightmostSecond Q Λ hQ a).1.1.1 = c₁ * a.1.1 := by
  change (fiveSlotRightmostKernel_nilHecke Q Λ (fiveSlotRightmost_firstCentralMap Q Λ hQ a)).1.1.1 = _
  rw [fiveSlotRightmostKernel_nilHecke_val, fiveSlotRightmost_firstCentralMap_val, ← mul_assoc]
  congr 1
  rw [← map_mul, ψw_cons 3 [2,1], mul_assoc]

private theorem centralToRightmostSecond_kernel_contained :
    LinearMap.ker (centralToRightmostSecond Q Λ hQ) ≤ LinearMap.range (leftExtremeToCentral Q Λ) := by
  intro a ha
  have ha' : centralToRightmostSecond Q Λ hQ a = 0 := ha
  have hz := congrArg (fun z : K₂ => z.1.1.1) ha'
  change (centralToRightmostSecond Q Λ hQ a).1.1.1 = (0 : V) at hz
  rw [centralToRightmostSecond_val] at hz
  obtain ⟨b,hb₁,hb₂,hb⟩ := FiveSlotFlag.fiveSlotRightmost_secondCrossing_kernel_mem_leftExtremeImage
    Q Λ hQ a.1.1 (central_support Q Λ a) (corner_mul_right _ a.1) hz
  let a₀ : P₀ := blockLoadingRep Q Λ E₀ b
  have ha₀ : a₀.1.1 = b := by
    exact (blockLoadingRep_val Q Λ E₀ b).trans ((congrArg (· * E) hb₁).trans hb₂)
  refine ⟨a₀, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  rw [leftExtremeToCentral_val, ha₀]
  exact hb.symm

private theorem centralToRightmostSecond_on_principal (a : P₀) :
    centralToRightmostSecond Q Λ hQ (leftExtremeToCentral Q Λ a) =
      fiveSlotRightmost_firstCentralMap Q Λ hQ
        (leftExtremeToCentral Q Λ (leftExtremeDelta Q Λ a)) := by
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [centralToRightmostSecond_val, leftExtremeToCentral_val,
    fiveSlotRightmost_firstCentralMap_val, leftExtremeToCentral_val, leftExtremeDelta_val]
  have h := FiveSlotFlag.fiveSlotRightmost_secondCrossing_on_leftExtreme Q Λ a.1.1
  rw [map_mul F (ψ 1), mul_assoc δ₀, leftExtreme_support Q Λ a] at h
  have he : c₀ * u₀ = F (ψw [2,1,3,2] * e E₀) := by
    rw [← map_mul]
    have hcut : (e E₁ : R) * (ψw [3,2] * e E₀) = ψw [3,2] * e E₀ := by
      rw [← show wordProd N [3,2] • E₀ = E₁ by decide, ← mul_assoc,
        e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    rw [mul_assoc, hcut, ← mul_assoc, ← ψw_append]
    rfl
  rw [← mul_assoc c₀, he]
  exact h

private theorem centralToRightmostSecond_on_principal_zero (a : P₀) :
    centralToRightmostSecond Q Λ hQ (leftExtremeToCentral Q Λ a) = 0 ↔ leftExtremeDelta Q Λ a = 0 := by
  rw [centralToRightmostSecond_on_principal Q Λ hQ]
  constructor
  · intro h
    apply leftExtremeToCentral_injective Q Λ hQ
    apply fiveSlotRightmost_firstCentralMap_injective Q Λ hQ
    simpa only [map_zero] using h
  · intro h
    simp only [h, map_zero]

private theorem secondCrossing_range_eq_nilHecke_range :
    LinearMap.range (centralToRightmostSecond Q Λ hQ) = LinearMap.range (fiveSlotRightmostKernel_nilHecke Q Λ) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact ⟨fiveSlotRightmost_firstCentralMap Q Λ hQ a, rfl⟩
  · rintro _ ⟨a,rfl⟩
    obtain ⟨b,hb₁,hb₂,hb⟩ :=
      fiveSlotRightmostKernel_crossing_mem_secondImage Q Λ hQ a.1 a.2
    let z : P₁ := blockLoadingRep Q Λ E₁ b
    have hz : z.1.1 = b :=
      (blockLoadingRep_val Q Λ E₁ b).trans ((congrArg (· * E) hb₁).trans hb₂)
    refine ⟨z, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    rw [centralToRightmostSecond_val, fiveSlotRightmostKernel_nilHecke_val, hz]
    exact hb.symm

end Second




section SecondKernelEquiv
variable (hQ : KLRSymm Q)

local notation "g₂" => centralToRightmostSecond Q Λ hQ
local notation "u" => leftExtremeToCentral Q Λ
local notation "d₀" => leftExtremeDelta Q Λ

private def rightmostSecondKernelMap :
    LinearMap.ker d₀ →ₗ[Tᵐᵒᵖ] LinearMap.ker g₂ where
  toFun a := ⟨u a.1, (centralToRightmostSecond_on_principal_zero Q Λ hQ a.1).2 a.2⟩
  map_add' a b := Subtype.ext (map_add u a.1 b.1)
  map_smul' r a := Subtype.ext (map_smul u r a.1)

private theorem rightmostSecondKernelMap_injective :
    Function.Injective (rightmostSecondKernelMap Q Λ hQ) := by
  intro a b h
  have hv : u a.1 = u b.1 :=
    congrArg (fun z : LinearMap.ker g₂ => z.1) h
  exact Subtype.ext (leftExtremeToCentral_injective Q Λ hQ hv)

private theorem rightmostSecondKernelMap_surjective :
    Function.Surjective (rightmostSecondKernelMap Q Λ hQ) := by
  intro a
  have hsource : a.1 ∈ LinearMap.range u :=
    centralToRightmostSecond_kernel_contained Q Λ hQ a.2
  obtain ⟨b, hb⟩ := hsource
  have hz : g₂ (u b) = 0 := hb.symm ▸ a.2
  have hd := (centralToRightmostSecond_on_principal_zero Q Λ hQ b).1 hz
  exact ⟨⟨b, hd⟩, Subtype.ext hb⟩

private def rightmostSecondKernelEquiv :
    LinearMap.ker d₀ ≃ₗ[Tᵐᵒᵖ] LinearMap.ker g₂ :=
  LinearEquiv.ofBijective (rightmostSecondKernelMap Q Λ hQ)
    ⟨rightmostSecondKernelMap_injective Q Λ hQ, rightmostSecondKernelMap_surjective Q Λ hQ⟩

private theorem rightmostSecondKernelEquiv_val (a : LinearMap.ker d₀) :
    (rightmostSecondKernelEquiv Q Λ hQ a).1 = u a.1 := rfl

end SecondKernelEquiv

section Derived
open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
attribute [local instance 1200] Ring.toIntAlgebra

universe w
variable (target : List (Fin 3))
variable [sourceDerived : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₂)).Cornerᵐᵒᵖ]
  [HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν target).Cornerᵐᵒᵖ]
variable (hQ : KLRSymm Q)

local notation "g₂" => centralToRightmostSecond Q Λ hQ
local notation "d₂" => fiveSlotRightmostKernel_nilHecke Q Λ
local notation "u" => leftExtremeToCentral Q Λ
local notation "d₀" => leftExtremeDelta Q Λ

private abbrev rightmostHomologyFun (n : ℤ) :=
  degreeZeroModuleFunctor Tᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
    braidingFunctor.{w} k Q Λ ν (redWord E₂) target ⋙ homologyFunctor ℤ n


private def leftExtremeToCentralHom :
    ModuleCat.of Tᵐᵒᵖ P₀ ⟶ ModuleCat.of Tᵐᵒᵖ P₁ :=
  let : AddCommGroup P₀ := Submodule.addCommGroup P₀
  let : AddCommGroup P₁ := Submodule.addCommGroup P₁
  let : Module Tᵐᵒᵖ P₀ := Submodule.module P₀
  let : Module Tᵐᵒᵖ P₁ := Submodule.module P₁
  ModuleCat.ofHom u

set_option backward.isDefEq.respectTransparency false in
include hQ in
private theorem leftExtremeToCentral_homology_mono
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target)) :
    Mono ((rightmostHomologyFun.{w} Q Λ target 0).map (leftExtremeToCentralHom Q Λ)) := by
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₁)).Cornerᵐᵒᵖ := sourceDerived
  let e := LinearEquiv.ofBijective (fiveSlotCentralPrincipalKernelMap Q Λ)
    ⟨fiveSlotCentralPrincipalKernelMap_injective_of_cancellation Q Λ
      (fun y hy _ hz => fiveSlotCentral_leftWord_cancel_of_leftSupport Q Λ hQ y hy hz),
      fiveSlotCentralPrincipalKernelMap_surjective Q Λ hQ⟩
  have iso : leftExtremeToCentralHom Q Λ = e.toModuleIso.hom ≫ (blockLoadingShortComplex Q Λ E₁ 1 2).f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  let hmono : Mono ((rightmostHomologyFun.{w} Q Λ target 0).map ((blockLoadingShortComplex Q Λ E₁ 1 2).f)) :=
    blockKernelDerivedHomology_mono Q Λ E₁ 1 2 target hbal
  rw [iso, Functor.map_comp]
  infer_instance

private def leftExtremeKernelProjection :
    P₀ →ₗ[Tᵐᵒᵖ] LinearMap.ker d₀ := by
  let f : P₀ →ₗ[Tᵐᵒᵖ] P₀ := LinearMap.id - (leftExtremeDot Q Λ).comp d₀
  refine f.codRestrict _ ?_
  intro a
  change d₀ (a - leftExtremeDot Q Λ (d₀ a)) = 0
  rw [map_sub, leftExtremeDelta_contract Q Λ _ (leftExtremeDelta_square Q Λ a), sub_self]

private theorem leftExtremeKernelProjection_apply (a : LinearMap.ker d₀) :
    leftExtremeKernelProjection Q Λ a.1 = a := by
  apply Subtype.ext
  change a.1 - leftExtremeDot Q Λ (d₀ a.1) = a.1
  rw [show d₀ a.1 = 0 from a.2, map_zero, sub_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem secondCrossing_range_braid_homology_vanish
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target)) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((rightmostHomologyFun.{w} Q Λ target n).obj (ModuleCat.of Tᵐᵒᵖ (LinearMap.range g₂))) := by
  let e := rightmostSecondKernelEquiv Q Λ hQ
  let proj := leftExtremeKernelProjection Q Λ
  let i := (LinearMap.ker d₀).subtype.comp e.symm.toLinearMap
  let r := e.toLinearMap.comp proj
  have hi : (u).comp i = (LinearMap.ker g₂).subtype := by
    apply LinearMap.ext
    intro a
    change u (e.symm a).1 = a.1
    calc
      _ = (e (e.symm a)).1 := (rightmostSecondKernelEquiv_val Q Λ hQ (e.symm a)).symm
      _ = _ := congrArg Subtype.val (e.apply_symm_apply a)
  have hr : r.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro a
    change e (proj ((LinearMap.ker d₀).subtype (e.symm a))) = a
    have h := leftExtremeKernelProjection_apply Q Λ (e.symm a)
    exact (congrArg e h).trans (e.apply_symm_apply a)
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₀)).Cornerᵐᵒᵖ := sourceDerived
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₁)).Cornerᵐᵒᵖ := sourceDerived
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).Additive := by
    unfold braidingFunctor
    infer_instance
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).CommShift ℤ :=
    braidingFunctor_commShift.{w} k Q Λ ν (redWord E₂) target
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).IsTriangulated :=
    braidingFunctor_isTriangulated.{w} k Q Λ ν (redWord E₂) target
  exact crossingRange_homology_vanish_of_retract (braidingFunctor.{w} k Q Λ ν (redWord E₂) target) g₂ u i r hi hr
    (blockLoadingProjective_braid_homology_vanish Q Λ E₀ target)
    (blockLoadingProjective_braid_homology_vanish Q Λ E₁ target)
    (leftExtremeToCentral_homology_mono Q Λ target hQ hbal) n hn

include hQ in
/-- The entire rightmost loading kernel has braid cohomology concentrated
in degree zero, using the ordinary balanced injection at E1. -/
theorem fiveSlotRightmost_kernel_braid_homology_vanish
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((rightmostHomologyFun.{w} Q Λ target n).obj (ModuleCat.of Tᵐᵒᵖ K₂)) := by
  have h := secondCrossing_range_braid_homology_vanish Q Λ target hQ hbal n hn
  have hD : IsZero ((rightmostHomologyFun.{w} Q Λ target n).obj
      (ModuleCat.of Tᵐᵒᵖ (LinearMap.range d₂))) :=
    (secondCrossing_range_eq_nilHecke_range Q Λ hQ) ▸ h
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).Additive := by
    unfold braidingFunctor
    infer_instance
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).CommShift ℤ :=
    braidingFunctor_commShift.{w} k Q Λ ν (redWord E₂) target
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).IsTriangulated :=
    braidingFunctor_isTriangulated.{w} k Q Λ ν (redWord E₂) target
  have hProd := crossingProd_homology_vanish (braidingFunctor.{w} k Q Λ ν (redWord E₂) target) n hD
  let : AddCommGroup (LinearMap.range d₂) := Submodule.addCommGroup (LinearMap.range d₂)
  let : Module Tᵐᵒᵖ (LinearMap.range d₂) := Submodule.module (LinearMap.range d₂)
  let : AddCommGroup K₂ := blockKernelAddGroup Q Λ E₂ 1 2
  let e := (fiveSlotRightmostKernel_equiv_nilHeckeRangeProd Q Λ).toModuleIso
  exact hProd.of_iso ((rightmostHomologyFun.{w} Q Λ target n).mapIso e)

include hQ in
/-- The rightmost partial standard follows by Webster's (6.21) from the two
ordinary balanced injections at the central and rightmost loadings. -/
theorem fiveSlotRightmost_partialStandard_braid_homology_vanish
    (hcentral : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target))
    (hright : Function.Injective (blockKernelTensorInclusion Q Λ E₂ 1 2 target))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((rightmostHomologyFun.{w} Q Λ target n).obj (blockLoadingShortComplex Q Λ E₂ 1 2).X₃) := by
  apply blockPartialStandard_braid_homology_vanish Q Λ E₂ 1 2 target
    (L := fun _ : Unit => ModuleCat.of Tᵐᵒᵖ K₂) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) _ hright n hn
  exact fun _ _ j hj => fiveSlotRightmost_kernel_braid_homology_vanish Q Λ target hQ hcentral j hj

end Derived

end Categorification.Stendhal.BraidedStendhalAlgebra
