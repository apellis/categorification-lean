/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendIota

/-!
# Appending a black strand to `K^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The map `ι : model_ν → model_{{i} + ν}` appending a black
strand `i` at the far right (`CupCap.appendIota`, `CupCap.appendTopIota`) keeps the
bottom-violated parts, so it descends to `K^{λ⁺}_λ`, the model modulo its bottom-violated part
(`CupCap.capModelRightEquiv`). The descended map carries the right action of `T̃^{λ⁺}` to the
right action along appending the strand, and the left action of `T̃^λ` to the left action along
appending the strand. It is built once from any map of models with these properties
(`CupCap.capMapOf`).

## Main definitions

* `CupCap.violQuotMapOf`, `CupCap.capMapOf`: the map of quotients induced by a map of models.
* `CupCap.capIota` (`j < ℓ`), `CupCap.capTopIota` (`j = ℓ`): `ι` on `K^{λ⁺}_λ`.

## Main results

* `CupCap.capMapOf_smul`, `CupCap.capMapOf_capLeftLin`.
* `CupCap.capIota_smul`, `CupCap.capIota_capLeftLin`, `CupCap.capTopIota_smul`,
  `CupCap.capTopIota_capLeftLin`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I} {i : I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "φ⁺" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
local notation "MM" => MidModel j hj Q Λ Λc ν ν₀ L
local notation "MMᵢ" => MidModel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "BV" => midBotViolSub Q Λ Λc j hj ν ν₀ L
local notation "BVᵢ" =>
  midBotViolSub Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "CB" => CapBimodule k Q Λ Λc j hj ν ν₀ L
local notation "CBᵢ" => CapBimodule k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "aB" => appendBlackStendhal Q Λ i ν

section Generic

/-- The map of the models modulo their bottom-violated parts induced by an additive map of the
models that keeps the bottom-violated parts. -/
def violQuotMapOf (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ) : (MM ⧸ BV) →+ (MMᵢ ⧸ BVᵢ) :=
  QuotientAddGroup.map (Submodule.toAddSubgroup BV) (Submodule.toAddSubgroup BVᵢ) f
    (fun y hy => hf y hy)

theorem violQuotMapOf_mk (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ) (y : MM) :
    violQuotMapOf f hf (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y) := rfl

variable (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- The map `K^{λ⁺}_λ → K^{λ⁺}_λ` (from the black weight `ν` to `{i} + ν`) induced by an
additive map of the models that keeps the bottom-violated parts. -/
def capMapOf (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ) : CB →+ CBᵢ :=
  AddMonoidHom.mk' (fun c => (capModelRightEquiv hR' hP hPL hκ).symm
      (violQuotMapOf f hf (capModelRightEquiv hR hP hPL hκ c)))
    (fun c c' => by simp only [map_add])

theorem capModelRightEquiv_capMapOf (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ) (c : CB)
    (y : MM) (hy : capModelRightEquiv hR hP hPL hκ c = Submodule.Quotient.mk y) :
    capModelRightEquiv hR' hP hPL hκ (capMapOf hR hR' hP hPL hκ f hf c) =
      Submodule.Quotient.mk (f y) := by
  change capModelRightEquiv hR' hP hPL hκ ((capModelRightEquiv hR' hP hPL hκ).symm
    (violQuotMapOf f hf (capModelRightEquiv hR hP hPL hκ c))) = _
  rw [LinearEquiv.apply_symm_apply, hy, violQuotMapOf_mk]

/-- The induced map carries the right action of `b` to the right action of `appendBlackPlus(b)`
when the map of models does. -/
theorem capMapOf_smul (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ)
    (hs : ∀ (b : Tpᵐᵒᵖ) (y : MM), f (b • y) = φ⁺ b • f y) (b : Tpᵐᵒᵖ) (c : CB) :
    capMapOf hR hR' hP hPL hκ f hf (b • c) = φ⁺ b • capMapOf hR hR' hP hPL hκ f hf c := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  have hby : capModelRightEquiv hR hP hPL hκ (b • c) = Submodule.Quotient.mk (b • y) := by
    rw [map_smul, ← hy, Submodule.Quotient.mk_smul]
  rw [capModelRightEquiv_capMapOf hR hR' hP hPL hκ f hf _ _ hby, LinearEquiv.map_smul,
    capModelRightEquiv_capMapOf hR hR' hP hPL hκ f hf _ _ hy.symm, hs,
    Submodule.Quotient.mk_smul]

/-- The induced map carries the left action of `z` to the left action of `appendBlack(z)` when
the map of models does. -/
theorem capMapOf_capLeftLin (f : MM →+ MMᵢ) (hf : ∀ y ∈ BV, f y ∈ BVᵢ)
    (hl : ∀ (z : StendhalAlgebra k Q Λ ν) (y : MM),
      f (midLeftAlg L hL hR z y) = midLeftAlg L hL hR' (aB z) (f y))
    (z : StendhalAlgebra k Q Λ ν) (c : CB) :
    capMapOf hR hR' hP hPL hκ f hf (capLeftLin L z c) =
      capLeftLin L (aB z) (capMapOf hR hR' hP hPL hκ f hf c) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (capModelRightEquiv hR hP hPL hκ c)
  apply (capModelRightEquiv hR' hP hPL hκ).injective
  rw [capModelRightEquiv_capMapOf hR hR' hP hPL hκ f hf _ _
      (capModelRightEquiv_capLeftLin hR hP hPL hκ z c y hy.symm),
    capModelRightEquiv_capLeftLin hR' hP hPL hκ (aB z) _ (f y)
      (capModelRightEquiv_capMapOf hR hR' hP hPL hκ f hf c y hy.symm), hl]

end Generic

variable (ν i) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
  (hR' : MidKLRRel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L hL)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

section Mid

variable (h : j < ℓ)

/-- **Appending a black strand to `K^{λ⁺}_λ`**, for `j < ℓ`. -/
def capIota : CB →+ CBᵢ :=
  capMapOf hR hR' hP hPL hκ (AddMonoidHom.mk' (appendIota ν i L h) (appendIota_add ν i h))
    (fun _ hy => appendIota_mem_midBotViolSub ν i h hy)

theorem capModelRightEquiv_capIota (c : CB) (y : MM)
    (hy : capModelRightEquiv hR hP hPL hκ c = Submodule.Quotient.mk y) :
    capModelRightEquiv hR' hP hPL hκ (capIota ν i hR hR' hP hPL hκ h c) =
      Submodule.Quotient.mk (appendIota ν i L h y) :=
  capModelRightEquiv_capMapOf hR hR' hP hPL hκ _ _ c y hy

theorem capIota_smul (b : Tpᵐᵒᵖ) (c : CB) :
    capIota ν i hR hR' hP hPL hκ h (b • c) = φ⁺ b • capIota ν i hR hR' hP hPL hκ h c :=
  capMapOf_smul hR hR' hP hPL hκ _ _ (appendIota_smul ν i h) b c

/-- **`ι` intertwines the left actions of `T̃^λ` on `K^{λ⁺}_λ`**, for `j < ℓ`. -/
theorem capIota_capLeftLin (z : StendhalAlgebra k Q Λ ν) (c : CB) :
    capIota ν i hR hR' hP hPL hκ h (capLeftLin L z c) =
      capLeftLin L (aB z) (capIota ν i hR hR' hP hPL hκ h c) :=
  capMapOf_capLeftLin hR hR' hP hPL hκ _ _ (appendIota_midLeftAlg ν i h hR hR') z c

end Mid

section Top

variable (h : ¬ j < ℓ)

/-- **Appending a black strand to `K^{λ⁺}_λ`**, for `j = ℓ`. -/
def capTopIota : CB →+ CBᵢ :=
  capMapOf hR hR' hP hPL hκ
    (AddMonoidHom.mk' (appendTopIota ν i hP hPL hL hκ h)
      (appendTopIota_add ν i hP hPL hL hκ h))
    (fun _ hy => appendTopIota_mem_midBotViolSub ν i hP hPL hL hκ h hy)

theorem capModelRightEquiv_capTopIota (c : CB) (y : MM)
    (hy : capModelRightEquiv hR hP hPL hκ c = Submodule.Quotient.mk y) :
    capModelRightEquiv hR' hP hPL hκ (capTopIota ν i hR hR' hP hPL hκ h c) =
      Submodule.Quotient.mk (appendTopIota ν i hP hPL hL hκ h y) :=
  capModelRightEquiv_capMapOf hR hR' hP hPL hκ _ _ c y hy

theorem capTopIota_smul (b : Tpᵐᵒᵖ) (c : CB) :
    capTopIota ν i hR hR' hP hPL hκ h (b • c) = φ⁺ b • capTopIota ν i hR hR' hP hPL hκ h c :=
  capMapOf_smul hR hR' hP hPL hκ _ _ (appendTopIota_smul ν i hP hPL hL hκ h) b c

/-- **`ι` intertwines the left actions of `T̃^λ` on `K^{λ⁺}_λ`**, for `j = ℓ`. -/
theorem capTopIota_capLeftLin (z : StendhalAlgebra k Q Λ ν) (c : CB) :
    capTopIota ν i hR hR' hP hPL hκ h (capLeftLin L z c) =
      capLeftLin L (aB z) (capTopIota ν i hR hR' hP hPL hκ h c) :=
  capMapOf_capLeftLin hR hR' hP hPL hκ _ _
    (appendTopIota_midLeftAlg ν i hP hPL hL hκ h hR hR') z c

end Top

end Categorification.Stendhal.CupCap
