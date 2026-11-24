/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.WeightedKLR.RedStrands.FiveSlotSpectatorWeight
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.WeightedKLR.RedStrands.BraidedBimoduleFlip
import Categorification.WeightedKLR.RedStrands.FiveSlotStandardCrossingTest
import Categorification.WeightedKLR.RedStrands.FiveSlotAllTops

/-!
# The principal higher layer at the next retained five-slot top

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21). At the next retained
loading, the principal higher crossing comes from the maximal loading
projective. Quotient factorization makes this a surjection onto the
retained kernel. The dimension shift then applies if the ordinary crossing
and the ordinary balanced kernel inclusion are both injective.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory Equiv MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ
local notation "v₀" => fixedTopFourExitCut 0
local notation "jA" => sadj n₀ 2 • v₀

private theorem order : redWord v₀ = redWord jA := by decide

private theorem higher : adjacentBlockRoot 1 2 jA < adjacentBlockRoot 1 2 v₀ := by
  constructor
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad := h (1 : Fin 3) ()
    have : ¬ adjacentBlockRoot 1 2 v₀ 1 () ≤ adjacentBlockRoot 1 2 jA 1 () := by decide
    exact this bad

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "V" => ViolQuotient k Q Λ ν₀
local notation "π" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord jA))
local notation "C" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord jA))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord jA) v₀ order
local notation "K" => blockLoadingKernel Q Λ jA 1 2

/-- The maximal loading projective maps onto the next retained kernel via the
single crossing in the principal higher ideal. -/
theorem fiveSlotNextRetainedCrossing_surjective (hQ : KLRSymm Q) :
    Function.Surjective (crossingIntoKernelMap Q Λ 1 2 order higher 2) := by
  intro x
  have hcut : π (KLRAlgebra.e jA) * x.1.1.1 = x.1.1.1 := congrArg Subtype.val x.1.2
  obtain ⟨y, hy, hyx⟩ := fiveSlot_jA_higher_exists_leftFactor Q Λ hQ x.1.1.1 x.2 hcut
  let yC : C := ⟨E * y * E, y, rfl⟩
  have hd : IsIdempotentElem d := orderedLoadingIdem_idem Q Λ v₀
  let z : rIdeal d := rIdealProj hd yC
  have hz : z.1.1 = y * E := by
    have hE : d.1 * E = d.1 := corner_mul_right _ d
    change d.1 * (E * y * E) = y * E
    rw [← mul_assoc, ← mul_assoc, hE]
    change π (KLRAlgebra.e v₀) * y * E = y * E
    rw [hy]
  refine ⟨z, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [crossingIntoKernelMap_val Q Λ 1 2 order higher 2 rfl, hz, ← mul_assoc, hyx]
  exact corner_mul_right _ x.1.1


variable (κ : List (Fin 3))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)

/-- If the principal crossing into the next retained kernel is injective,
the kernel is braid-acyclic by the maximal loading projective comparison. -/
theorem fiveSlotNextRetainedKernel_braid_homology_vanish (hQ : KLRSymm Q)
    (hi : Function.Injective (crossingIntoKernelMap Q Λ 1 2 order higher 2))
    [sourceDerived : HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (ModuleCat.of Cᵐᵒᵖ K))))) := by
  let P := rIdeal d
  let G := degreeZeroModuleFunctor Cᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
    braidingFunctor k Q Λ ν₀ (redWord jA) κ ⋙ DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n
  let f := LinearEquiv.ofBijective (crossingIntoKernelMap Q Λ 1 2 order higher 2)
    ⟨hi, fiveSlotNextRetainedCrossing_surjective Q Λ hQ⟩
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord v₀)).Cornerᵐᵒᵖ := sourceDerived
  have hp : IsZero (G.obj (ModuleCat.of Cᵐᵒᵖ P)) :=
    blockLoadingProjective_braid_homology_vanish Q Λ v₀ κ n hn
  exact hp.of_iso (G.mapIso f.toModuleIso.symm)


/-- The next retained partial standard is braid-acyclic once the principal crossing
and the ordinary balanced kernel inclusion are injective. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish (hQ : KLRSymm Q)
    (hcross : Function.Injective (crossingIntoKernelMap Q Λ 1 2 order higher 2))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ jA 1 2 κ))
    [HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ jA 1 2).X₃)))) := by
  refine blockPartialStandard_braid_homology_vanish Q Λ jA 1 2 κ
    (L := fun _ : Unit => ModuleCat.of Cᵐᵒᵖ K) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hbal n hn
  intro _ _ j hj
  exact fiveSlotNextRetainedKernel_braid_homology_vanish Q Λ κ hQ hcross j hj

/-- The next retained kernel vanishes when the spectator weight is at most one. -/
theorem fiveSlotNextRetainedKernel_eq_bot_of_spectatorWeight_le_one
    (h : Λ 0 () ≤ 1) : K = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 jA) (redWord jA) at hx
  rw [fiveSlot_oneBlackBeforePair_upperIdeal_eq_bot_of_spectatorWeight_le_one Q Λ h jA (Or.inr rfl)] at hx
  rw [Submodule.mem_bot]
  apply Subtype.ext; apply Subtype.ext
  exact (TwoSidedIdeal.mem_bot _).1 hx

/-- The next retained partial standard is braid-acyclic at spectator weight at most one. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish_of_spectatorWeight_le_one
    (h : Λ 0 () ≤ 1)
    [HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ jA 1 2).X₃)))) :=
  blockPartialStandard_braid_homology_vanish_of_bot Q Λ jA 1 2 κ
    (fiveSlotNextRetainedKernel_eq_bot_of_spectatorWeight_le_one Q Λ h) n hn

section OrdinaryTest

open KLRAlgebra
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "p" => fun s => π (KLRAlgebra.e s)
local notation "Eord" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (List.finRange 3))

private theorem word : redWord jA = List.finRange 3 := by decide
private theorem highWord : redWord v₀ = List.finRange 3 := order.trans word
private theorem step : sadj (Multiset.card μ) 2 • jA = v₀ := by
  apply Subtype.ext; funext a; fin_cases a <;> decide

private def cornerImage (z : R) : (isIdempotentElem_violRedProj k Q Λ ν₀).Corner :=
  violCornerHom k Q Λ ν₀ (cornerMk (ofKLR k Q Λ ν₀ z))

private theorem cornerImage_idem :
    (cornerImage Q Λ (KLRAlgebra.e v₀)).1 = p v₀ := by
  rw [cornerImage, violCornerHom_val, cornerMk_e_val highWord]
  rfl

private theorem cornerImage_cross :
    (cornerImage Q Λ (ψ 2 * KLRAlgebra.e jA)).1 = π (ψ 2 * KLRAlgebra.e jA) := by
  let eR := redProj k Q Λ ν₀ (List.finRange 3)
  let c := ofKLR k Q Λ ν₀ (ψ 2 * KLRAlgebra.e jA)
  have hc : (ψ 2 * KLRAlgebra.e jA : R) = KLRAlgebra.e v₀ * ψ 2 := by
    rw [e_mul_ψ, ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  let f := ofKLR k Q Λ ν₀
  have hc₁ : c = f (e v₀) * f (ψ 2) := (congrArg f hc).trans (map_mul f _ _)
  have hc₂ : c = f (ψ 2) * f (e jA) := map_mul f _ _
  have hr : f (e jA) * eR = f (e jA) := by
    change f (e jA) * redProj k Q Λ ν₀ (List.finRange 3) = f (e jA)
    rw [e_mul_redProj, ite_eq_left word]
  have hleft : eR * c = c := by
    rw [hc₁]
    exact redProj_mul_e_of_eq highWord _
  have hright : c * eR = c := by rw [hc₂, mul_assoc, hr]
  change violMk k Q Λ ν₀ (eR * c * eR) = _
  rw [hleft, hright]
  rfl

private theorem flipMul (x y : V) : violFlip (x * y) = violFlip y * violFlip x :=
  congrArg MulOpposite.unop (map_mul (violFlipHom k Q Λ ν₀) x y)

private theorem flipE : violFlip Eord = Eord := by
  rw [violFlip_violMk, flip_redProj]

private theorem flipHigh : violFlip (p v₀) = p v₀ := by
  change violFlip (violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (KLRAlgebra.e v₀))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_e]
  rfl

private theorem flipCross :
    violFlip (π (ψ 2 * KLRAlgebra.e v₀)) = π (ψ 2 * KLRAlgebra.e jA) := by
  change violFlip (violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (ψ 2 * KLRAlgebra.e v₀))) = _
  rw [violFlip_violMk, flip_ofKLR, hflip_mul, hflip_e, hflip_ψ, e_mul_ψ,
    ← step, ← mul_smul, TypeA.sadj_mul_self, one_smul]
  rfl

private theorem ordinaryImage (z : R) :
    identityCornerToTensor k Q Λ ν₀ (cornerMk (ofKLR k Q Λ ν₀ z)) = tensorOfKLR Q Λ ν₀ z := by
  apply congrArg (TensorProductAlgebra.mk Q Λ ν₀)
  apply Subtype.ext
  rw [identityCornerHom_val, cornerMk_val, map_mul, map_mul,
    toAllOrders_ofKLR]
  change toAllOrders k Q Λ ν₀ (ofKLR k Q Λ ν₀ (redIdem k Q Λ (List.finRange 3))) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν₀ z *
      toAllOrders k Q Λ ν₀ (ofKLR k Q Λ ν₀ (redIdem k Q Λ (List.finRange 3))) = _
  rw [toAllOrders_redIdem]
  let eR := StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν₀
  let a := StendhalAlgebraAllOrders.ofKLR k Q Λ ν₀ z
  change eR * a * eR = a * eR
  rw [(redOrderedIdem_commute Q Λ ν₀ a).eq, mul_assoc,
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem.eq]

set_option maxHeartbeats 1000000 in
/-- A right multiplication test in the ordinary ordered algebra transports, by
the quotient corner equivalence and diagram flip, to the interior right-projective map. -/
theorem fiveSlotNextRetainedCrossing_injective_of_ordinary_test (hQ : KLRSymm Q)
    (h : ∀ x : TensorProductAlgebra k Q Λ ν₀,
      x * tensorOfKLR Q Λ ν₀ (KLRAlgebra.e v₀) = x →
      x * tensorOfKLR Q Λ ν₀ (ψ 2 * KLRAlgebra.e jA) = 0 →
      x = 0) :
    Function.Injective (crossingIntoKernelMap Q Λ 1 2 order higher 2) := by
  let ρ := TypeA.canWord (Multiset.card μ)
  have hρ : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let q := violCornerEquiv (ν := ν₀) (Λ := Λ) hρ hQ
  let projective := rIdeal (orderedLoadingIdemAt Q Λ (redWord jA) v₀ order)
  let : AddCommGroup projective := Submodule.addCommGroup projective
  let : AddCommGroup (blockLoadingKernel Q Λ jA 1 2) := blockKernelAddGroup Q Λ jA 1 2
  let F := crossingIntoKernelMap Q Λ 1 2 order higher 2
  change Function.Injective F
  suffices hz : ∀ y : projective, F y = 0 → y = 0 by
    intro y z hyz
    have hs : F (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    exact sub_eq_zero.mp (hz (y - z) hs)
  intro y hy
  have hY : Eord * y.1.1 = y.1.1 ∧ y.1.1 * Eord = y.1.1 := by
    have inner := (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord jA))).1 y.1.2
    have hEeq : violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord jA)) = Eord :=
      congrArg (fun order => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ order)) word
    exact ⟨(congrArg (fun z => z * y.1.1) hEeq).symm.trans inner.1,
      (congrArg (fun z => y.1.1 * z) hEeq).symm.trans inner.2⟩
  let fy : (isIdempotentElem_violRedProj k Q Λ ν₀).Corner := ⟨violFlip y.1.1,
    (Subsemigroup.mem_corner_iff (isIdempotentElem_violRedProj k Q Λ ν₀)).2
    ⟨by rw [← flipE Q Λ, ← flipMul Q Λ, hY.2],
     by rw [← flipE Q Λ, ← flipMul Q Λ, hY.1]⟩⟩
  have hf : fy * cornerImage Q Λ (KLRAlgebra.e v₀) = fy := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (KLRAlgebra.e v₀)).1 = violFlip y.1.1
    have hp : p v₀ * y.1.1 = y.1.1 := congrArg Subtype.val y.2
    rw [cornerImage_idem, ← flipHigh Q Λ, ← flipMul Q Λ, hp]
  have hh : fy * cornerImage Q Λ (ψ 2 * KLRAlgebra.e jA) = 0 := by
    apply Subtype.ext
    change violFlip y.1.1 * (cornerImage Q Λ (ψ 2 * KLRAlgebra.e jA)).1 = 0
    have hx : π (ψ 2 * KLRAlgebra.e v₀) * y.1.1 = 0 := by
      change crossingIntoKernelMap Q Λ 1 2 order higher 2 y = 0 at hy
      rw [← crossingIntoKernelMap_val Q Λ 1 2 order higher 2 rfl, hy]
      rfl
    rw [cornerImage_cross, ← flipCross Q Λ, ← flipMul Q Λ, hx]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν₀))
  have himg (z : R) : q (cornerImage Q Λ z) = tensorOfKLR Q Λ ν₀ z :=
    (violCornerEquiv_violCornerHom hρ hQ (cornerMk (ofKLR k Q Λ ν₀ z))).trans (ordinaryImage Q Λ z)
  have hq : q fy = 0 := h (q fy) (by rw [← himg, ← map_mul q, hf])
    (by rw [← himg, ← map_mul q, hh, map_zero])
  have hfy : fy = 0 := q.injective (hq.trans (map_zero q).symm)
  apply Subtype.ext; apply Subtype.ext
  have hhf : violFlip y.1.1 = 0 := congrArg Subtype.val hfy
  exact (violFlip_violFlip y.1.1).symm.trans (by
    rw [hhf]
    exact congrArg MulOpposite.unop (map_zero (violFlipHom k Q Λ ν₀)))

end OrdinaryTest

section Standard

open QuantumGroup KL3.Diagram

variable {F₀ : Type} [Field F₀] {C₀ : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C₀ F₀)

theorem fiveSlotNextRetainedCrossing_standard_injective
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 3 → Unit →₀ ℕ) :
    Function.Injective (crossingIntoKernelMap QL weights 1 2 order higher 2) :=
  fiveSlotNextRetainedCrossing_injective_of_ordinary_test QL weights hQ
    (fiveSlotNextRetained_rightMultiplication_eq_zero hR hQ weights)

set_option quotPrecheck false in
local notation "S₀" weights:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord jA))
set_option quotPrecheck false in
local notation "D₀" weights:arg target:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target)

/-- The retained kernel at the next five-slot loading is projective at standard parameters. -/
theorem fiveSlotNextRetainedKernel_projective_standard
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 3 → Unit →₀ ℕ) :
    Module.Projective (S₀ weights)ᵐᵒᵖ (blockLoadingKernel QL weights jA 1 2) := by
  let d₀ := orderedLoadingIdemAt QL weights (redWord jA) v₀ order
  have hd : IsIdempotentElem d₀ := orderedLoadingIdem_idem QL weights v₀
  have : Module.Projective (S₀ weights)ᵐᵒᵖ (rIdeal d₀) := rIdeal_projective hd
  let e := LinearEquiv.ofBijective (crossingIntoKernelMap QL weights 1 2 order higher 2)
    ⟨fiveSlotNextRetainedCrossing_standard_injective hR hQ weights,
      fiveSlotNextRetainedCrossing_surjective QL weights hQ⟩
  exact Module.Projective.of_equiv e

/-- The only remaining test for the next retained five-slot partial standard
at standard parameters is the full ordinary balanced kernel inclusion. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish_standard
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 3 → Unit →₀ ℕ)
    (target : List (Fin 3))
    (hbal : Function.Injective (blockKernelTensorInclusion QL weights jA 1 2 target))
    [HasDerivedCategory.{w, 0} (S₀ weights)ᵐᵒᵖ] [HasDerivedCategory.{w, 0} (D₀ weights target)ᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (D₀ weights target)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord jA) target).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (S₀ weights)ᵐᵒᵖ).obj
          (blockLoadingShortComplex QL weights jA 1 2).X₃)))) :=
  fiveSlotNextRetainedPartialStandard_braid_homology_vanish QL weights target hQ
    (fiveSlotNextRetainedCrossing_standard_injective hR hQ weights) hbal n hn


/-- The next retained five-slot partial standard is concentrated in degree
zero for the actual exchanged red order at standard parameters. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish_exchanged
    (weights : Fin 3 → Unit →₀ ℕ)
    [HasDerivedCategory.{w, 0} (S₀ weights)ᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} (D₀ weights ([0,2,1] : List (Fin 3)))ᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (D₀ weights ([0,2,1] : List (Fin 3)))ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord jA) [0,2,1]).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (S₀ weights)ᵐᵒᵖ).obj
          (blockLoadingShortComplex QL weights jA 1 2).X₃)))) := by
  have hR : IsRouquierQ C₀ QL :=
    ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hQ : KLRSymm QL := fun i j h => (h (Subsingleton.elim i j)).elim
  exact fiveSlotNextRetainedPartialStandard_braid_homology_vanish_standard hR hQ weights [0,2,1]
    (fiveSlot_blockKernelTensorInclusion_injective_standard_allTops C₀ weights jA (by decide)) n hn

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra
