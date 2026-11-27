/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeCross
import Categorification.WeightedKLR.Rigidity.CupCapMidRightLoop

/-!
# A black strand crossing `λ_{j+1}` from the left is a left multiple

Webster, arXiv:1309.3796v3, §7.3, for a cap after the red strand `λ_j`: the step of the
surjectivity of the comparison map over the block shuffles that uses the pull-off identity.
Below the cap generators at a loading `s` of `λ`, let the strand of `s` just right of
`λ_{j+1}` be black of colour `i`, and let `s'` be `s` with this strand crossed to the left of
`λ_{j+1}`. For a diagram `Z` whose top has the window just left of that black strand (at
`midPos j s` in `s'`), the diagram `ψ_{c+N} Z` crossing the black strand with `λ_{j+1}` is, in
the model, the crossing `ψ_c` of `T̃^λ` acting on `underRight · Z`, the black strand pulled
under the window to its left, up to the unit scalar of (max1)
(`tmul_midGen_ψ_eq_midKLRAct`). This is the pull-off identity of `L` (`PullOff`) carried along
the right action of `T̃^{λ⁺}` (`rightLoop_midModel_mul`).
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
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀

theorem eSum_insertSet_congr (s : Seq (stendhalWeight ℓ ν)) {n n' : ℕ} (h : n = n')
    (hn : n ≤ m) (hn' : n' ≤ m) : (E s n hn : Rp) = E s n' hn' := by
  subst h; rfl

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The loop on the right of the maximum, below any diagram**: `rightLoop_midModel` multiplied
on the right by a diagram `Z` whose top has the window at `midPos j s` in `s_c • s`. -/
theorem rightLoop_midModel_mul (hP : PullOff k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν))
    (hc1 : midPos j s + 1 < m) (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i) (Z : Rp)
    (hZ : E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) * Z = Z) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) *
        (underLeft N (midPos j s) * underRight N (midPos j s)) * Z))) v :
          MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) * Z)))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have h := congrArg (fun t => (op (bot Z) : (StendhalAlgebra k Q (plusLabels Λ Λc j hj)
    (ν + ν₀))ᵐᵒᵖ) • t) (rightLoop_midModel Q Λ Λc L (hj := hj) hP i s hc1 hs v)
  simp only [Ind.smul_tmul, op_smul_midGen, ← map_mul, mul_assoc] at h
  simp only [hZ] at h
  simpa only [mul_assoc] using h

variable {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **A black strand crossing `λ_{j+1}` from the left is a left multiple** (the pull-off step of
the surjectivity of `midThetaBlock`): for `Z` with top the window at `c = midPos j s` in
`s' = s_c • s`, followed by the black strand of colour `i` and `λ_{j+1}`,
`ψ_{c+N} Z ⊗ v = ψ_c · (underRight · Z ⊗ κ_i⁻¹ v)`, where `ψ_c` is the crossing of `T̃^λ` acting
on the model. -/
theorem tmul_midGen_ψ_eq_midKLRAct (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hP : PullOff k Q Λc ν₀ L) (i : I) (hκ : IsUnit (cupScalar Q ν₀ i))
    (s : Seq (stendhalWeight ℓ ν)) (hc1 : midPos j s + 1 < m)
    (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i) (Z : Rp)
    (hZ : E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) * Z = Z) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) * Z))) v :
        MidModel j hj Q Λ Λc ν ν₀ L) =
      midKLRAct hR (KLRAlgebra.ψ (midPos j s))
        (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (underRight N (midPos j s) * Z)))
          (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (↑hκ.unit⁻¹ : k)) • v)) := by
  set c := midPos j s
  set s' := sadj m c • s
  have hm : midPos j s' = c + 1 := midPos_sadj_right j s hc1 rfl
  have hs' : s'.lbl ⟨c, by omega⟩ = .inl i := lbl_sadj_midPos s hc1 hs
  have hZ' : E s' (midPos j s') (midPos_le j s') * (underRight N c * Z) = underRight N c * Z := by
    rw [eSum_insertSet_congr s' hm (midPos_le j s') (by omega), ← mul_assoc,
      ← underRight_mul_eSum Q Λ Λc s' (q := c) (by omega), mul_assoc, hZ]
  rw [midKLRAct_ψ_tmul_midGen_of_left hR s' (p := c) (by omega) hm.symm hs' _ hZ',
    ← mul_assoc (KLRAlgebra.ψ (c + N) * underLeft N c), mul_assoc (KLRAlgebra.ψ (c + N)),
    rightLoop_midModel_mul hP i s hc1 hs Z hZ, ← smul_assoc, smul_eq_mul, ← op_mul, ← map_mul,
    IsUnit.val_inv_mul, map_one, op_one, one_smul]

end Categorification.Stendhal.CupCap
