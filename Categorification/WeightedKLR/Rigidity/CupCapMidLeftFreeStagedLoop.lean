/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeStagedPass
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftLoop

/-!
# The left loop at an arbitrary position of the maximum

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (staged transparency, step (I1) of the route). In the induced module
`L ⊗ e_{s,n+1} T̃^{λ⁺}` with the black strand of colour `i` at `n` just left of the window, the
strand pulled under the window to the right and back multiplies by the scalar of (max1)
(`posLoopLeft`), from the left pull-off identity of `L`. Hence the passage back and forth is
multiplication by `κ_i` (`posPassRight_posPassLeft`).

## Main results

* `CupCap.intertwinesOn_posBlock`: the window idempotent intertwines the block with the module.
* `CupCap.posLoopLeft`: the loop on the left of the window, from `PullOffLeft`.
* `CupCap.posPassRight_posPassLeft`: `posPassRight ∘ posPassLeft = κ_i`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

variable (j hj Q Λ Λc ν₀) in
/-- The element `e_{s,n} Z` of the corner of the window at position `n` of `s`. -/
def posGen (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) (Z : Tp) :
    Corner (posOp j hj Q Λ Λc ν₀ s n hn) :=
  ⟨op (posStendhal j hj Q Λ Λc ν₀ s n hn 1 * Z), by
    change op (posStendhal j hj Q Λ Λc ν₀ s n hn 1 * Z) * posOp j hj Q Λ Λc ν₀ s n hn 1 = _
    rw [posOp_apply, ← op_mul, unop_one, ← mul_assoc, ← map_mul, one_mul]⟩

theorem posGen_val (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (Z : Tp) :
    (posGen j hj Q Λ Λc ν₀ s n hn Z).1 = op (posStendhal j hj Q Λ Λc ν₀ s n hn 1 * Z) := rfl

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The window idempotent intertwines the block with the induced module**: when the strand of
`s` at `n` is black, the black-prepending map followed by the block map is the diagram on the
window at `n + 1`. -/
theorem intertwinesOn_posBlock (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    IntertwinesOn L ((blockOpMid Q Λ Λc ν₀ i s n hn).comp (prependBlackTildeOp k Q Λc ν₀ i))
      (posOp j hj Q Λ Λc ν₀ s (n + 1) hn)
      (posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn))).1 where
  unit := (posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn))).2
  slide a z v := by
    refine IntertwinesOn.slide_of_eq _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    change op (blockStendhal Q Λ Λc j hj ν₀ i s n hn
        (prependBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) *
          op (posStendhal j hj Q Λ Λc ν₀ s (n + 1) hn 1 * bot (E s (n + 1) hn)) =
      op (posStendhal j hj Q Λ Λc ν₀ s (n + 1) hn 1 * bot (E s (n + 1) hn)) *
        op (posStendhal j hj Q Λ Λc ν₀ s (n + 1) hn (cupMap k Q Λc ν₀ w))
    rw [blockStendhal_prependBlack Q Λ Λc i s hn hs, posStendhal_cupMap', posStendhal_one,
      ← op_mul, ← op_mul]
    congr 1
    simp only [← map_mul, eSum_mul_insertMap, (KLRAlgebra.eSum_idem _).eq,
      insertMap_mul_eSum]

/-- **The loop on the left of the window**, from the left pull-off identity of `L`: with the
black strand of colour `i` at `n` just left of the window at `n + 1`, the strand pulled under the
window to the right and back multiplies by the scalar of (max1). -/
theorem posLoopLeft (hP : PullOffLeft k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) (v : L) :
    (Ind.tmul (posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn *
        (underRight N n * underLeft N n) * E s (n + 1) hn))) v :
          PosModel j hj Q Λ Λc ν₀ s (n + 1) hn L) =
      Ind.tmul (posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn)))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hX := intertwinesOn_posBlock (j := j) (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ)
    (Λc := Λc) L i s hn hs
  have h := congrArg (fun t => (op (bot (E s (n + 1) hn)) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (prependBlackTildeOp k Q Λc ν₀ i) (blockOpMid Q Λ Λc ν₀ i s n hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  have hl := loop_value_mid (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  have hu := unit_value_mid (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  simp only [mul_assoc] at hl hu
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ)) <;>
    simp only [← op_mul, mul_assoc] <;> rw [posStendhal_one]
  · conv_lhs => rw [← hl]
    rfl
  · conv_lhs => rw [← map_mul, (KLRAlgebra.eSum_idem _).eq, ← hu]
    conv_rhs => rw [← mul_assoc, ← map_mul, (KLRAlgebra.eSum_idem _).eq]
    rfl

/-- **Passing back and forth is `κ_i`**: with the black strand of colour `i` at `n` just left of
the window at `n + 1`, passing it under the window to the left and back to the right multiplies
by the scalar of (max1). -/
theorem posPassRight_posPassLeft (hP : PullOffLeft k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (z : Corner (posOp j hj Q Λ Λc ν₀ s (n + 1) hn))
    (v : L) :
    posPassRight L hL s n hn (posPassLeft L hL s n hn (Ind.tmul z v)) =
      Ind.tmul z (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hz : z.1 * op (bot (E s (n + 1) hn)) = z.1 := by
    have h1 : posOp j hj Q Λ Λc ν₀ s (n + 1) hn 1 = op (bot (E s (n + 1) hn)) := by
      rw [posOp_apply, unop_one, posStendhal_one]
    rw [← h1]
    exact z.2
  have hE : z = z.1 • posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn)) := by
    apply Subtype.ext
    change z.1 = z.1 * op (posStendhal j hj Q Λ Λc ν₀ s (n + 1) hn 1 * bot (E s (n + 1) hn))
    rw [posStendhal_one, ← map_mul, (KLRAlgebra.eSum_idem _).eq, hz]
  have hg : (cornerMulOf (intertwinesOn_posPassRightElt hL s hn).unit
      (cornerMulOf (intertwinesOn_posPassLeftElt hL s hn).unit z)) =
      z.1 • posGen j hj Q Λ Λc ν₀ s (n + 1) hn (bot (E s (n + 1) hn *
        (underRight N n * underLeft N n) * E s (n + 1) hn)) := by
    apply Subtype.ext
    change z.1 * op (bot (E s n (Nat.le_of_succ_le hn) * underLeft N n)) *
        op (bot (E s (n + 1) hn * underRight N n)) =
      z.1 * op (posStendhal j hj Q Λ Λc ν₀ s (n + 1) hn 1 * bot (E s (n + 1) hn *
        (underRight N n * underLeft N n) * E s (n + 1) hn))
    rw [posStendhal_one, ← hz]
    simp only [mul_assoc, ← op_mul, ← map_mul]
    congr 3
    have he : ∀ x : Rp, E s (n + 1) hn * (E s (n + 1) hn * x) = E s (n + 1) hn * x := by
      intro x; rw [← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    have he' : ∀ x : Rp, E s n (Nat.le_of_succ_le hn) * (E s n (Nat.le_of_succ_le hn) * x) =
        E s n (Nat.le_of_succ_le hn) * x := by
      intro x; rw [← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    simp only [he, (KLRAlgebra.eSum_idem _).eq,
      underLeft_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) s hn, he']
  simp only [posPassRight, posPassLeft, natMapOn_tmul]
  rw [hg, ← Ind.smul_tmul, posLoopLeft L hP i s hn hs, Ind.smul_tmul, ← hE]

end Categorification.Stendhal.CupCap
