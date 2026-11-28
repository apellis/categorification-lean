/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendTopLeft

/-!
# Appending a black strand to the model at the bottom and at the top

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`. The identification `𝔉_i(model_ν) ≅ e' · model_{{i} + ν}`,
composed with the unit `y ↦ 1 ⊗ y`, gives a map `ι : model_ν → model_{{i} + ν}` appending a black
strand `i` at the far right, at the bottom and at the top (`CupCap.appendIota` for `j < ℓ`,
`CupCap.appendTopIota` for `j = ℓ`). It is additive, carries the right action of `T̃^{λ⁺}_ν` to
the right action along appending the strand, carries the left action of `T̃^λ_ν` to the left
action along appending the strand, and keeps the bottom-violated parts.

## Main definitions

* `CupCap.appendIota`, `CupCap.appendTopIota`.

## Main results

* `CupCap.appendIota_smul`, `CupCap.appendIota_midLeftAlg`, `CupCap.appendIota_mem_midBotViolSub`.
* `CupCap.appendTopIota_smul`, `CupCap.appendTopIota_midLeftAlg`,
  `CupCap.appendTopIota_mem_midBotViolSub`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "φ⁺" => appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
local notation "MM" => MidModel j hj Q Λ Λc ν ν₀ L
local notation "MMᵢ" => MidModel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L
local notation "aB" => appendBlackStendhal Q Λ i ν

/-- The unit of induction along appending the strand: `y ↦ 1 ⊗ y`, and it carries the right
action of `b` to the right action of `appendBlackPlus(b)`. -/
theorem tmul_unitGen_smul (b : Tpᵐᵒᵖ) (y : MM) :
    (Ind.tmul (unitGen φ⁺) (b • y) : Ind MM φ⁺) = φ⁺ b • Ind.tmul (unitGen φ⁺) y := by
  rw [← Ind.op_smul_tmul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change φ⁺ 1 * φ⁺ b = φ⁺ b * φ⁺ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

section Mid

variable (L) in
/-- **Appending a black strand to the model**, for `j < ℓ`: `y ↦` the image of `1 ⊗ y` under
`𝔉_i(model_ν) → model_{{i} + ν}`. -/
def appendIota (h : j < ℓ) (y : MM) : MMᵢ :=
  appendMidMap Q Λ Λc j hj ν ν₀ i L h (Ind.tmul (unitGen φ⁺) y)

theorem appendIota_add (h : j < ℓ) (y y' : MM) :
    appendIota ν i L h (y + y') = appendIota ν i L h y + appendIota ν i L h y' := by
  rw [appendIota, Ind.tmul_add, map_add]
  rfl

theorem appendIota_smul (h : j < ℓ) (b : Tpᵐᵒᵖ) (y : MM) :
    appendIota ν i L h (b • y) = φ⁺ b • appendIota ν i L h y := by
  rw [appendIota, tmul_unitGen_smul, map_smul]
  rfl

/-- **`ι` intertwines the actions of `T̃^λ`**, for `j < ℓ`. -/
theorem appendIota_midLeftAlg (h : j < ℓ)
    {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL)
    (z : StendhalAlgebra k Q Λ ν) (y : MM) :
    appendIota ν i L h (midLeftAlg L hL hR z y) =
      midLeftAlg L hL hR' (aB z) (appendIota ν i L h y) := by
  have := appendMidMap_midLeftAlg ν i hL h hR hR' z (Ind.tmul (unitGen φ⁺) y)
  rw [Ind.map_tmul] at this
  exact this

/-- **`ι` keeps the bottom-violated parts**, for `j < ℓ`. -/
theorem appendIota_mem_midBotViolSub (h : j < ℓ) {y : MM}
    (hy : y ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L) :
    appendIota ν i L h y ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L :=
  (mem_appendBotViolSub_iff ν i h _).1 (tmul_mem_appendBotViolSub ν i _ hy)

end Mid

section Top

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **Appending a black strand to the model**, for `j = ℓ`: `y ↦` the image of `1 ⊗ y` under
`𝔉_i(model_ν) ≅ e' · model_{{i} + ν}`, which passes the new strand under the window. -/
def appendTopIota (h : ¬ j < ℓ) (y : MM) : MMᵢ :=
  (appendTopModelEquiv (i := i) hL hP hPL hκ h (Ind.tmul (unitGen φ⁺) y) : MMᵢ)

theorem appendTopIota_add (h : ¬ j < ℓ) (y y' : MM) :
    appendTopIota ν i hP hPL hL hκ h (y + y') =
      appendTopIota ν i hP hPL hL hκ h y + appendTopIota ν i hP hPL hL hκ h y' := by
  rw [appendTopIota, Ind.tmul_add, map_add, Submodule.coe_add]
  rfl

theorem appendTopIota_smul (h : ¬ j < ℓ) (b : Tpᵐᵒᵖ) (y : MM) :
    appendTopIota ν i hP hPL hL hκ h (b • y) = φ⁺ b • appendTopIota ν i hP hPL hL hκ h y := by
  rw [appendTopIota, tmul_unitGen_smul, map_smul, Submodule.coe_smul]
  rfl

/-- On generators: `ι(w ⊗ v) = appendBlackPlus(w) D ⊗ v`. -/
theorem appendTopIota_tmul (h : ¬ j < ℓ) (w : Corner (midOp j hj Q Λ Λc ν ν₀)) (v : L) :
    appendTopIota ν i hP hPL hL hκ h (Ind.tmul w v) =
      Ind.tmul (cornerMulOf (topPassOp_mul_midOp_one ν i h)
        (compMul (midOp j hj Q Λ Λc ν ν₀) φ⁺ (unitGen φ⁺) w)) v :=
  appendTopModelEquiv_tmul_tmul ν i hP hPL hκ h _ w v

/-- **`ι` intertwines the actions of `T̃^λ`**, for `j = ℓ`. -/
theorem appendTopIota_midLeftAlg (h : ¬ j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (z : StendhalAlgebra k Q Λ ν) (y : MM) :
    appendTopIota ν i hP hPL hL hκ h (midLeftAlg L hL hR z y) =
      midLeftAlg L hL hR' (aB z) (appendTopIota ν i hP hPL hL hκ h y) := by
  have := appendTopModelEquiv_midLeftAlg ν i hP hPL hκ h hR hR' z (Ind.tmul (unitGen φ⁺) y)
  rw [Ind.map_tmul] at this
  exact this

/-- **`ι` keeps the bottom-violated parts**, for `j = ℓ`. -/
theorem appendTopIota_mem_midBotViolSub (h : ¬ j < ℓ) {y : MM}
    (hy : y ∈ midBotViolSub Q Λ Λc j hj ν ν₀ L) :
    appendTopIota ν i hP hPL hL hκ h y ∈ midBotViolSub Q Λ Λc j hj νᵢ ν₀ L := by
  have hx := Submodule.mem_map_of_mem
    (f := (appendTopModelEquiv (i := i) hL hP hPL hκ h).toLinearMap)
    (tmul_mem_appendBotViolSub ν i (unitGen φ⁺) hy)
  rw [map_appendTopModelEquiv_appendBotViolSub] at hx
  exact hx

end Top

end Categorification.Stendhal.CupCap
