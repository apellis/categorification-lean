/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralHigher
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence

/-!
# The central five-slot retained kernel

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21). The central retained
kernel is the image of the principal two-crossing map from the maximal
loading projective. Ordinary cancellation identifies this map as an
isomorphism. The full balanced inclusion then gives derived vanishing
on the actual central partial-standard quotient.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA CornerEndomorphism
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
variable {k : Type} [CommRing k]
    (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "t" => fixedTopFourExitCut 1
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord t))
local notation "K" => blockLoadingKernel Q Λ t 1 2
local notation "J" => blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) (redWord t)
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord t))
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "p" => fun s : Seq μ₀ => F (e s)
local notation "c" => F (ψw [3,2] * e v₀)

private theorem commonOrder : redWord v₀ = redWord t := by decide
local notation "d" => orderedLoadingIdemAt Q Λ (redWord t) v₀ commonOrder

private theorem centralPrincipal_mark : c ∈ J := by
  rw [fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ t (Or.inl rfl)]
  have hc : c * p v₀ = c := by rw [← map_mul, mul_assoc, e_mul_self]
  exact hc ▸ TwoSidedIdeal.mul_mem_left _ c _ (TwoSidedIdeal.subset_span (Set.mem_singleton _))

private theorem centralPrincipal_support : (p t) * c = c ∧ c * E = c := by
  constructor
  · have h : (e t : KLRAlgebra k (stendhalQ Q Λ) μ₀) * (ψw [3,2] * e v₀) = ψw [3,2] * e v₀ := by
      rw [← show wordProd n₀ [3,2] • v₀ = t by decide, ← mul_assoc,
        e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    exact (map_mul F _ _).symm.trans (congrArg F h)
  · have he : p v₀ * E = p v₀ := corner_mul_right _ d
    have hc : c * p v₀ = c := by rw [← map_mul, mul_assoc, e_mul_self]
    rw [← hc, mul_assoc, he]

private theorem centralPrincipal_rep : (blockLoadingRep Q Λ t c).1.1 = c :=
  (blockLoadingRep_val Q Λ t c).trans
    ((congrArg (· * E) (centralPrincipal_support Q Λ).1).trans (centralPrincipal_support Q Λ).2)

private def centralPrincipalGenerator : K :=
  ⟨blockLoadingRep Q Λ t c, (centralPrincipal_rep Q Λ).symm ▸ centralPrincipal_mark Q Λ⟩

/-- Multiplication by the two-crossing principal generator into the central retained kernel. -/
def fiveSlotCentralPrincipalKernelMap : rIdeal d →ₗ[Tᵐᵒᵖ] K where
  toFun y := op y.1 • centralPrincipalGenerator Q Λ
  map_add' y z := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 + z.1.1) = _ * y.1.1 + _ * z.1.1
    rw [mul_add]
  map_smul' a y := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change _ * (y.1.1 * a.unop.1) = (_ * y.1.1) * a.unop.1
    rw [mul_assoc]

theorem fiveSlotCentralPrincipalKernelMap_val (y : rIdeal d) :
    (fiveSlotCentralPrincipalKernelMap Q Λ y).1.1.1 = c * y.1.1 := by
  change (blockLoadingRep Q Λ t c).1.1 * y.1.1 = _
  exact congrArg (· * y.1.1) (centralPrincipal_rep Q Λ)

theorem fiveSlotCentralPrincipalKernelMap_surjective (hQ : KLRSymm Q) :
    Function.Surjective (fiveSlotCentralPrincipalKernelMap Q Λ) := by
  intro x
  have hcut : p t * x.1.1.1 = x.1.1.1 := congrArg Subtype.val x.1.2
  obtain ⟨y, hy, hyx⟩ := fiveSlotCentral_higher_exists_leftFactor Q Λ hQ x.1.1.1 x.2 hcut
  let yC : T := ⟨E * y * E, y, rfl⟩
  have hd : IsIdempotentElem d := orderedLoadingIdem_idem Q Λ v₀
  let z : rIdeal d := rIdealProj hd yC
  have hz : z.1.1 = y * E := by
    have hE : d.1 * E = d.1 := corner_mul_right _ d
    change d.1 * (E * y * E) = y * E
    rw [← mul_assoc, ← mul_assoc, hE]
    change p v₀ * y * E = y * E
    rw [hy]
  refine ⟨z, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [fiveSlotCentralPrincipalKernelMap_val Q Λ, hz, ← mul_assoc, hyx]
  exact corner_mul_right _ x.1.1

/-- Cancellation on the ordinary maximal-loading corner makes the principal map injective. -/
theorem fiveSlotCentralPrincipalKernelMap_injective_of_cancellation
    (hcancel : ∀ y : V, p v₀ * y = y → y * E = y → c * y = 0 → y = 0) :
    Function.Injective (fiveSlotCentralPrincipalKernelMap Q Λ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply Subtype.ext
  apply hcancel
  · exact congrArg Subtype.val (x - y).2
  · exact corner_mul_right _ (x - y).1
  · rw [← fiveSlotCentralPrincipalKernelMap_val Q Λ, map_sub, hxy, sub_self]
    rfl

/-- Cancellation on the ordinary maximal-loading corner makes the central kernel projective. -/
theorem fiveSlotCentral_blockLoadingKernel_projective_of_cancellation (hQ : KLRSymm Q)
    (hcancel : ∀ y : V, p v₀ * y = y → y * E = y → c * y = 0 → y = 0) :
    Module.Projective Tᵐᵒᵖ K := by
  have hd : IsIdempotentElem d := orderedLoadingIdem_idem Q Λ v₀
  have : Module.Projective Tᵐᵒᵖ (rIdeal d) := rIdeal_projective hd
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective _
    ⟨fiveSlotCentralPrincipalKernelMap_injective_of_cancellation Q Λ hcancel,
      fiveSlotCentralPrincipalKernelMap_surjective Q Λ hQ⟩)

variable (target : List (Fin 3))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ target)

/-- The central partial standard follows by (6.21) from cancellation in the maximal
ordinary projective and injectivity of the full ordinary balanced inclusion. -/
theorem fiveSlotCentral_partialStandard_braid_homology_vanish_of_cancellation (hQ : KLRSymm Q)
    (hcancel : ∀ y : V, p v₀ * y = y → y * E = y → c * y = 0 → y = 0)
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 target))
    [sourceDerived : HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [HasDerivedCategory.{w, 0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord t) target).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t 1 2).X₃)))) := by
  let e₀ := LinearEquiv.ofBijective (fiveSlotCentralPrincipalKernelMap Q Λ)
    ⟨fiveSlotCentralPrincipalKernelMap_injective_of_cancellation Q Λ hcancel,
      fiveSlotCentralPrincipalKernelMap_surjective Q Λ hQ⟩
  let : HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord v₀)).Cornerᵐᵒᵖ := sourceDerived
  refine blockPartialStandard_braid_homology_vanish Q Λ t 1 2 target
    (L := fun _ : Unit => ModuleCat.of Tᵐᵒᵖ K) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hbal n hn
  intro _ _ j hj
  let G := degreeZeroModuleFunctor Tᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
    braidingFunctor k Q Λ ν₀ (redWord t) target ⋙ DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ j
  have hp : IsZero (G.obj (ModuleCat.of Tᵐᵒᵖ (rIdeal d))) :=
    blockLoadingProjective_braid_homology_vanish Q Λ v₀ target j hj
  exact hp.of_iso (G.mapIso e₀.toModuleIso.symm)

end Categorification.Stendhal.BraidedStendhalAlgebra
