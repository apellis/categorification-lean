/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardTensorRepresented
import Categorification.WeightedKLR.RedStrands.CutStandardBasis
import Categorification.Algebra.TensorRepresentedProjective

/-!
# The bimodule of a partial standardization at a cut is finitely generated projective

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The shuffle
decomposition `𝕊(N) ≅ ⊕_u ε_u N` of the partial standardization at a cut
(`cutStandardShuffleEquiv`) is natural in `N` (`cutStandardShuffleEquiv_cutStandardMap`). For a
functor `F` presented by the partial standardization at a cut along `ι : D → R`
(`CutStandardPresented`), it identifies the bimodule `F(R)` with `⊕_u ι(ε_u) R` as a right
`R`-module, so `F(R)` is finitely generated projective over `R`
(`CutStandardPresented.isFinProj`). This is the projectivity part of the standard basis of a
partial standardization, used in the proof of Lemma 7.19.

## Main results

* `Stendhal.cutStandardShuffleEquiv_cutStandardMap`: naturality of the shuffle decomposition.
* `Stendhal.CutStandardPresented.bimodEquiv`: `F(R) ≅ ⊕_u ι(ε_u) R` as right `R`-modules.
* `Stendhal.CutStandardPresented.isFinProj`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory DG KLR KLRAlgebra TypeA MulOpposite TensorRepresented
open scoped TensorProduct

variable {I k : Type u} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "S" => stendhalQ Q Λ
local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "Sh" => Shuffle (Seq.card_add' α δ)

section Natural

variable {N N' : Type u} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] [AddCommGroup N'] [Module k N']
  [Module (cutFactorAlgebra Q Λ θ β) N'] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']
  (hQ : KLRSymm Q)

/-- The shuffle coordinates of the induced module are natural. -/
theorem indDecomp_cutShuffleMap (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N')
    (y : CutShuffle Q Λ θ β N) (u : Sh) :
    indDecomp (cutStendhalQ_symm Q Λ hQ) (CutInput Q Λ θ β N') (cutShuffleMap Q Λ θ β g y) u =
      cutInputHom Q Λ θ β g (indDecomp (cutStendhalQ_symm Q Λ hQ) (CutInput Q Λ θ β N) y u) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul m n => exact (map_smul (cutInputHom Q Λ θ β g) _ n).symm
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **The shuffle decomposition of the partial standardization at a cut is natural.** -/
theorem cutStandardShuffleEquiv_cutStandardMap (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N')
    (z : CutStandard Q Λ θ β N) (u : Sh) :
    (cutStandardShuffleEquiv Q Λ θ β N' hQ (cutStandardMap Q Λ θ β g z) :
        Sh → CutInput Q Λ θ β N') u =
      cutInputHom Q Λ θ β g
        ((cutStandardShuffleEquiv Q Λ θ β N hQ z : Sh → CutInput Q Λ θ β N) u) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  change (cutStandardShuffleEquiv Q Λ θ β N' hQ (Submodule.mkQ _ (cutShuffleMap Q Λ θ β g y)) :
    Sh → CutInput Q Λ θ β N') u = _
  rw [cutStandardShuffleEquiv_mkQ, cutStandardShuffleEquiv_mkQ, indDecomp_cutShuffleMap Q Λ θ β hQ]
  exact ((cutInputHom Q Λ θ β g).map_smul _ _).symm

end Natural

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

namespace CutStandardPresented

variable {Q Λ θ β} {R : Type u} [Ring R] [Algebra k R] {ι : cutFactorAlgebra Q Λ θ β →ₐ[k] R}
  {A : Type u} [Ring A] [Algebra k A] {F : ModuleCat.{u} R ⥤ ModuleCat.{u} A}
  (H : CutStandardPresented Q Λ θ β ι F) (hQ : KLRSymm Q)

local notation "X" => regular R
local notation "N₀" => CutInput Q Λ θ β (CutRestr Q Λ θ β ι X)

variable (ι) in
/-- The idempotent `ι(ε_u)` of `R` cutting down the shuffle `u`. -/
def shuffleIdem (u : Sh) : R := ι (cutInputMap Q Λ θ β (cutShuffleIdem Q Λ θ β u))

theorem shuffleIdem_idem (u : Sh) : IsIdempotentElem (shuffleIdem ι u) :=
  ((cutShuffleIdem_idem Q Λ θ β u).map (cutInputMap Q Λ θ β)).map ι

theorem cutShuffleIdem_smul (u : Sh) (x : N₀) :
    cutShuffleIdem Q Λ θ β u • x = (shuffleIdem ι u * (show R from x) : R) := rfl

/-- The shuffle coordinates of an element of `F(R)`. -/
def coord (p : Bimod F) (u : Sh) : R :=
  (cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ (H.equiv X p) : Sh → N₀) u

theorem coord_op_smul (b : Rᵐᵒᵖ) (p : Bimod F) (u : Sh) :
    H.coord hQ (b • p) u = H.coord hQ p u * b.unop :=
  (congrArg (fun z => (cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ z :
      Sh → N₀) u) (H.map (rmulReg X (show X from b.unop)) p)).trans
    (cutStandardShuffleEquiv_cutStandardMap Q Λ θ β hQ _ _ u)

theorem coord_mem (p : Bimod F) : H.coord hQ p ∈ idemCoords R (shuffleIdem ι) := fun u =>
  ((cutShuffleIdem_mem_range_iff Q Λ θ β _ u _).1
    ((cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ (H.equiv X p)).2 u
      (Set.mem_univ u))).symm.trans rfl |>.symm

theorem coord_injective : Function.Injective (H.coord hQ) := fun _ _ h =>
  (H.equiv X).injective ((cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ).injective
    (Subtype.ext h))

theorem exists_coord (g : Sh → R) (hg : g ∈ idemCoords R (shuffleIdem ι)) :
    ∃ p, H.coord hQ p = g := by
  have hm : (g : Sh → N₀) ∈ cutShuffleCoords Q Λ θ β (CutRestr Q Λ θ β ι X) := fun u _ =>
    (cutShuffleIdem_mem_range_iff Q Λ θ β _ u _).2 (hg u)
  obtain ⟨z, hz⟩ := (cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ).surjective ⟨g, hm⟩
  refine ⟨(H.equiv X).symm z, ?_⟩
  unfold coord
  rw [AddEquiv.apply_symm_apply, hz]

theorem coord_add (p p' : Bimod F) : H.coord hQ (p + p') = H.coord hQ p + H.coord hQ p' :=
  congrArg Subtype.val ((congrArg (cutStandardShuffleEquiv Q Λ θ β (CutRestr Q Λ θ β ι X) hQ)
    (map_add (H.equiv X) p p')).trans (map_add _ _ _))

variable [F.Additive]

/-- The shuffle coordinates of `F(R)`, as a map of right `R`-modules. -/
def coordLinear : Bimod F →ₗ[Rᵐᵒᵖ] idemCoords R (shuffleIdem ι) where
  toFun p := ⟨H.coord hQ p, H.coord_mem hQ p⟩
  map_add' p p' := Subtype.ext (H.coord_add hQ p p')
  map_smul' b p := Subtype.ext (funext fun u => H.coord_op_smul hQ b p u)

/-- **`F(R) ≅ ⊕_u ι(ε_u) R` as right `R`-modules.** -/
def bimodEquiv : Bimod F ≃ₗ[Rᵐᵒᵖ] idemCoords R (shuffleIdem ι) :=
  LinearEquiv.ofBijective (H.coordLinear hQ)
    ⟨fun _ _ h => H.coord_injective hQ
      (congrArg (fun g : idemCoords R (shuffleIdem ι) => (g : Sh → R)) h), fun g =>
      (H.exists_coord hQ g.1 g.2).elim fun p hp => ⟨p, Subtype.ext hp⟩⟩

include H hQ in
/-- **The bimodule of a functor presented by a partial standardization at a cut is finitely
generated projective** as a right module over `R`. -/
theorem isFinProj : IsFinProj F :=
  have := projective_idemCoords R (shuffleIdem_idem (ι := ι))
  have := finite_idemCoords R (shuffleIdem_idem (ι := ι))
  IsFinProj.of_equiv (H.bimodEquiv hQ).symm

end CutStandardPresented

end Categorification.Stendhal
