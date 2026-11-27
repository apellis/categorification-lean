/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeDots

/-!
# A crossing of `λ` acting on the generators of the model

Webster, arXiv:1309.3796v3, §7.3, for a cap after the red strand `λ_j`. A crossing `ψ_p` of `λ`,
acting on the left of the model on an element `Z ⊗ v` with `Z` of top in the window of `s`,
multiplies `Z` by the crossing `ψ_p` on `s` placed above the maximum (`midCrossAt s p`): a
crossing away from `λ_{j+1}`, or a black strand passing under the window and crossing `λ_{j+1}`
(`midKLRAct_ψ_tmul_midGen`, with the three explicit cases).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **A crossing of `λ` on a generator of the model**: for `Z` with top in the window of `s`,
`ψ_p · (Z ⊗ v) = (ψ_p on s, above the maximum) Z ⊗ v`. -/
theorem midKLRAct_ψ_tmul_midGen (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) (Z : Rp) (hZ : E s * Z = Z) (v : L) :
    midKLRAct hR (KLRAlgebra.ψ p) (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (midCrossAt j hj Q Λ Λc ν ν₀ s p * Z))) v := by
  rw [midKLRAct_ψ, midEnd_tmul_midGen L hL, ← map_mul]
  conv_lhs => rw [← hZ, ← mul_assoc, midCross_mul_eSum]

/-- A crossing away from `λ_{j+1}`. -/
theorem midKLRAct_ψ_tmul_midGen_of_far (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (h1 : p + 1 ≠ midPos j s)
    (h2 : p ≠ midPos j s) (Z : Rp) (hZ : E s * Z = Z) (v : L) :
    midKLRAct hR (KLRAlgebra.ψ p) (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀
        (bot (KLRAlgebra.ψ (crossPos (midPos j s) N p) * Z))) v := by
  rw [midKLRAct_ψ_tmul_midGen hR s p Z hZ, midCrossAt_of_far s hp h1 h2, mul_assoc, hZ]

/-- A black strand on the left of `λ_{j+1}` passes under the window and crosses `λ_{j+1}`. -/
theorem midKLRAct_ψ_tmul_midGen_of_left (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (hc : p + 1 = midPos j s) {i₀ : I}
    (hs : s.lbl ⟨p, by omega⟩ = .inl i₀) (Z : Rp) (hZ : E s * Z = Z) (v : L) :
    midKLRAct hR (KLRAlgebra.ψ p) (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Z)) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀
        (bot (KLRAlgebra.ψ (p + N) * underLeft N p * Z))) v := by
  rw [midKLRAct_ψ_tmul_midGen hR s p Z hZ, midCrossAt_of_left s hp hc hs, mul_assoc _ (E s), hZ]

/-- **Step 4, milestone 1: `Θ` on `ψ_p e(s_g) ⊗ v`** is the crossing on `s` above the maximum,
followed by `γ_g`. -/
theorem midLeftAlg_ψ_e_tmul_midGenCorner
    {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}
    (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (g : MidGen j hj ν ν₀) (p : ℕ) (v : L) :
    midLeftAlg L hL hR (topMap k Q Λ ν (KLRAlgebra.ψ p) *
        StendhalAlgebra.e (k := k) (Q := Q) (Λ := Λ) g.s g.hs)
        (Ind.tmul (midGenCorner Q Λ Λc ρ₃ g) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀
        (bot (midCrossAt j hj Q Λ Λc ν ν₀ g.s p * midGenKLR Q Λ Λc ρ₃ g))) v := by
  rw [map_mul, Module.End.mul_apply, midLeftAlg_e_tmul_midGenCorner, midLeftAlg_topMap,
    midGenCorner_eq_midGen, midGenElt,
    midKLRAct_ψ_tmul_midGen hR g.s p _ (midIdem_mul_midGenKLR g)]

end Categorification.Stendhal.CupCap
