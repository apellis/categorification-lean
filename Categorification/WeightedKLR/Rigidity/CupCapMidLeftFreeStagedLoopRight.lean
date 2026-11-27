/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeStagedLoop
import Categorification.WeightedKLR.Rigidity.CupCapMidRightLoop

/-!
# The right loop at an arbitrary position of the maximum

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (staged transparency, step (I1) of the route). In the induced module
`L ⊗ e_{s,n} T̃^{λ⁺}` with the black strand of colour `i` at `n` just right of the window, the
strand pulled under the window to the left and back multiplies by the scalar of (max1)
(`posLoopRight`), from the pull-off identity of `L`. Hence the passage there and back is
multiplication by `κ_i` (`posPassLeft_posPassRight`).

## Main results

* `CupCap.intertwinesOn_posRightBlock`: the window idempotent intertwines the block with the
  module.
* `CupCap.posLoopRight`: the loop on the right of the window, from `PullOff`.
* `CupCap.posPassLeft_posPassRight`: `posPassLeft ∘ posPassRight = κ_i`.
* `CupCap.posPassRight_bijective`, `CupCap.posPassRightEquiv`: a single passage of a black
  strand under the window is an isomorphism when `κ_i` is a unit.
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
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The window idempotent intertwines the block with the induced module**: when the strand of
`s` at `n` is black, the black-appending map followed by the block map is the diagram on the
window at `n`. -/
theorem intertwinesOn_posRightBlock (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    IntertwinesOn L ((blockOpMid Q Λ Λc ν₀ i s n hn).comp (appendBlackTildeOp k Q Λc ν₀ i))
      (posOp j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn))
      (posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
        (bot (E s n (Nat.le_of_succ_le hn)))).1 where
  unit := (posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
    (bot (E s n (Nat.le_of_succ_le hn)))).2
  slide a z v := by
    refine IntertwinesOn.slide_of_eq _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    change op (blockStendhal Q Λ Λc j hj ν₀ i s n hn
        (appendBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) *
          op (posStendhal j hj Q Λ Λc ν₀ s n _ 1 * bot (E s n (Nat.le_of_succ_le hn))) =
      op (posStendhal j hj Q Λ Λc ν₀ s n _ 1 * bot (E s n (Nat.le_of_succ_le hn))) *
        op (posStendhal j hj Q Λ Λc ν₀ s n _ (cupMap k Q Λc ν₀ w))
    rw [blockStendhal_appendBlack Q Λ Λc i s hn hs, posStendhal_cupMap', posStendhal_one,
      ← op_mul, ← op_mul]
    congr 1
    simp only [← map_mul, eSum_mul_insertMap, (KLRAlgebra.eSum_idem _).eq,
      insertMap_mul_eSum]

/-- **The loop on the right of the window**, from the pull-off identity of `L`: with the black
strand of colour `i` at `n` just right of the window at `n`, the strand pulled under the window
to the left and back multiplies by the scalar of (max1). -/
theorem posLoopRight (hP : PullOff k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hs : s.lbl ⟨n, by omega⟩ = .inl i) (v : L) :
    (Ind.tmul (posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
        (bot (E s n (Nat.le_of_succ_le hn) * (underLeft N n * underRight N n) *
          E s n (Nat.le_of_succ_le hn)))) v :
          PosModel j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn) L) =
      Ind.tmul (posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
        (bot (E s n (Nat.le_of_succ_le hn))))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hX := intertwinesOn_posRightBlock (j := j) (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ)
    (Λc := Λc) L i s hn hs
  have h := congrArg (fun t => (op (bot (E s n (Nat.le_of_succ_le hn))) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (appendBlackTildeOp k Q Λc ν₀ i) (blockOpMid Q Λ Λc ν₀ i s n hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  have hl := loop_value_right (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
    1
  have hu := unit_value_right (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
    1
  simp only [one_mul] at hl hu
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.le_of_succ_le hn))).eq
  have hEE : bot (E s n (Nat.le_of_succ_le hn)) * bot (E s n (Nat.le_of_succ_le hn)) =
      bot (E s n (Nat.le_of_succ_le hn)) := by rw [← map_mul, hE]
  have hc := underLeft_underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s hn
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ)) <;>
    simp only [← op_mul, mul_assoc] <;> rw [posStendhal_one]
  · change op (bot (E s n (Nat.le_of_succ_le hn)) * bot (E s n (Nat.le_of_succ_le hn) *
        (underLeft N n * (underRight N n * E s n (Nat.le_of_succ_le hn))))) =
      op (bot (E s n (Nat.le_of_succ_le hn)) * (bot (E s n (Nat.le_of_succ_le hn)) *
        (blockStendhal Q Λ Λc j hj ν₀ i s n hn
          (appendBlackStendhal Q Λc i ν₀ 1 * pullOffLoop k Q Λc ν₀ i) *
        (blockStendhal Q Λ Λc j hj ν₀ i s n hn 1 * bot (E s n (Nat.le_of_succ_le hn))))))
    congr 1
    simp only [← mul_assoc, hEE]
    rw [hl, ← map_mul]
    congr 1
    simp only [← mul_assoc, hE]
    rw [mul_assoc _ (underLeft N n), ← hc, mul_assoc, hE]
  · change op (bot (E s n (Nat.le_of_succ_le hn)) * bot (E s n (Nat.le_of_succ_le hn))) =
      op (bot (E s n (Nat.le_of_succ_le hn)) * (bot (E s n (Nat.le_of_succ_le hn)) *
        (blockStendhal Q Λ Λc j hj ν₀ i s n hn (appendBlackStendhal Q Λc i ν₀ 1) *
        (blockStendhal Q Λ Λc j hj ν₀ i s n hn 1 * bot (E s n (Nat.le_of_succ_le hn))))))
    congr 1
    simp only [← mul_assoc, hEE]
    rw [hu]

/-- **Passing there and back is `κ_i`**: with the black strand of colour `i` at `n` just right of
the window at `n`, passing it under the window to the right and back to the left multiplies by
the scalar of (max1). -/
theorem posPassLeft_posPassRight (hP : PullOff k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i)
    (z : Corner (posOp j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn))) (v : L) :
    posPassLeft L hL s n hn (posPassRight L hL s n hn (Ind.tmul z v)) =
      Ind.tmul z (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hz : z.1 * op (bot (E s n (Nat.le_of_succ_le hn))) = z.1 := by
    have h1 : posOp j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn) 1 =
        op (bot (E s n (Nat.le_of_succ_le hn))) := by
      rw [posOp_apply, unop_one, posStendhal_one]
    rw [← h1]
    exact z.2
  have hE : z = z.1 • posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
      (bot (E s n (Nat.le_of_succ_le hn))) := by
    apply Subtype.ext
    change z.1 = z.1 * op (posStendhal j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn) 1 *
      bot (E s n (Nat.le_of_succ_le hn)))
    rw [posStendhal_one, ← map_mul, (KLRAlgebra.eSum_idem _).eq, hz]
  have hg : (cornerMulOf (intertwinesOn_posPassLeftElt hL s hn).unit
      (cornerMulOf (intertwinesOn_posPassRightElt hL s hn).unit z)) =
      z.1 • posGen j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn)
        (bot (E s n (Nat.le_of_succ_le hn) * (underLeft N n * underRight N n) *
          E s n (Nat.le_of_succ_le hn))) := by
    apply Subtype.ext
    change z.1 * op (bot (E s (n + 1) hn * underRight N n)) *
        op (bot (E s n (Nat.le_of_succ_le hn) * underLeft N n)) =
      z.1 * op (posStendhal j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn) 1 *
        bot (E s n (Nat.le_of_succ_le hn) * (underLeft N n * underRight N n) *
          E s n (Nat.le_of_succ_le hn)))
    rw [posStendhal_one, ← hz]
    simp only [mul_assoc, ← op_mul, ← map_mul]
    congr 3
    have hc := underLeft_underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s hn
    have hE' := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
      (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.le_of_succ_le hn))).eq
    have hR : underRight N n * E s n (Nat.le_of_succ_le hn) = E s (n + 1) hn * underRight N n :=
      underRight_mul_eSum Q Λ Λc s hn
    have hx1 : ∀ x : Rp, x * E s (n + 1) hn * E s (n + 1) hn = x * E s (n + 1) hn := by
      intro x; rw [mul_assoc, (KLRAlgebra.eSum_idem _).eq]
    have hxn : ∀ x : Rp, x * E s n (Nat.le_of_succ_le hn) * E s n (Nat.le_of_succ_le hn) =
        x * E s n (Nat.le_of_succ_le hn) := by
      intro x; rw [mul_assoc, hE']
    have hUL : ∀ x : Rp, x * underLeft N n * E s (n + 1) hn =
        x * E s n (Nat.le_of_succ_le hn) * underLeft N n := by
      intro x; rw [mul_assoc, underLeft_mul_eSum s hn, ← mul_assoc]
    have hc' : ∀ x : Rp, x * underLeft N n * underRight N n * E s n (Nat.le_of_succ_le hn) =
        x * E s n (Nat.le_of_succ_le hn) * underLeft N n * underRight N n := by
      intro x; simp only [mul_assoc] at hc ⊢; rw [hc]
    simp only [← mul_assoc, hx1, hxn, hUL, hc', hR]
  simp only [posPassRight, posPassLeft, natMapOn_tmul]
  rw [hg, ← Ind.smul_tmul, posLoopRight L hP i s hn hs, Ind.smul_tmul, ← hE]

variable (Q Λc ν₀) in
/-- Multiplication by a scalar of `k` on a right module over the window algebra. -/
def windowScalarEnd (c : k) : L →ₗ[(StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ] L where
  toFun v := op (algebraMap k (StendhalAlgebra k Q Λc ν₀) c) • v
  map_add' v w := smul_add _ v w
  map_smul' a v := by
    change op (algebraMap k _ c) • a • v = a • op (algebraMap k _ c) • v
    rw [smul_smul, smul_smul]
    congr 1
    exact congrArg op (Algebra.commutes c a.unop).symm

theorem windowScalarEnd_apply (c : k) (v : L) :
    windowScalarEnd Q Λc ν₀ L c v = op (algebraMap k (StendhalAlgebra k Q Λc ν₀) c) • v := rfl

theorem windowScalarEnd_mul (c c' : k) :
    windowScalarEnd Q Λc ν₀ L c ∘ₗ windowScalarEnd Q Λc ν₀ L c' =
      windowScalarEnd Q Λc ν₀ L (c' * c) := by
  ext v
  simp only [LinearMap.comp_apply, windowScalarEnd_apply, smul_smul, ← op_mul, ← map_mul]

theorem windowScalarEnd_one : windowScalarEnd Q Λc ν₀ L (1 : k) = LinearMap.id := by
  ext v
  simp [windowScalarEnd_apply]

/-- The induced action of a scalar is invertible when the scalar is a unit. -/
theorem bijective_map_windowScalarEnd {φ : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+* Tpᵐᵒᵖ} {c : k}
    (hc : IsUnit c) : Function.Bijective (Ind.map (φ := φ) (windowScalarEnd Q Λc ν₀ L c)) := by
  obtain ⟨u, rfl⟩ := hc
  have h1 : ∀ a b : k, a * b = 1 → Ind.map (φ := φ) (windowScalarEnd Q Λc ν₀ L a) ∘ₗ
      Ind.map (windowScalarEnd Q Λc ν₀ L b) = LinearMap.id := by
    intro a b hab
    rw [← Ind.map_comp, windowScalarEnd_mul, mul_comm, hab, windowScalarEnd_one, Ind.map_id]
  refine ⟨fun x y hxy => ?_, fun y => ⟨Ind.map (windowScalarEnd Q Λc ν₀ L ↑u⁻¹) y, ?_⟩⟩
  · have := congrArg (Ind.map (φ := φ) (windowScalarEnd Q Λc ν₀ L ↑u⁻¹)) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, h1 _ _ u.inv_mul,
      LinearMap.id_apply, LinearMap.id_apply] at this
  · rw [← LinearMap.comp_apply, h1 _ _ u.mul_inv, LinearMap.id_apply]

/-- **A single passage under the window is an isomorphism** (Webster, arXiv:1309.3796v3, §7.3,
staged transparency, step (I1) of the left projectivity route), when the strand passing is black
of colour `i` and `κ_i` is a unit: its inverse is `κ_i⁻¹` times the passage back. -/
theorem posPassRight_bijective (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (hκ : IsUnit (cupScalar Q ν₀ i)) :
    Function.Bijective (posPassRight (j := j) (hj := hj) (Λ := Λ) L hL s n hn) := by
  have hRL : posPassRight (j := j) (hj := hj) (Λ := Λ) L hL s n hn ∘ₗ
      posPassLeft L hL s n hn =
      Ind.map (windowScalarEnd Q Λc ν₀ L (cupScalar Q ν₀ i)) :=
    Ind.ext fun z v => posPassRight_posPassLeft L hPL hL i s hn hs z v
  have hLR : posPassLeft (j := j) (hj := hj) (Λ := Λ) L hL s n hn ∘ₗ
      posPassRight L hL s n hn =
      Ind.map (windowScalarEnd Q Λc ν₀ L (cupScalar Q ν₀ i)) :=
    Ind.ext fun z v => posPassLeft_posPassRight L hP hL i s hn hs z v
  refine ⟨fun x y hxy => (bijective_map_windowScalarEnd L hκ).1 ?_, fun y => ?_⟩
  · rw [← hLR, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  · obtain ⟨x, hx⟩ := (bijective_map_windowScalarEnd L hκ).2 y
    exact ⟨posPassLeft L hL s n hn x, by rw [← LinearMap.comp_apply, hRL, hx]⟩

/-- The passage of a black strand under the window as an isomorphism of right
`T̃^{λ⁺}`-modules. -/
def posPassRightEquiv (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n + 1 ≤ m)
    (hs : s.lbl ⟨n, by omega⟩ = .inl i) (hκ : IsUnit (cupScalar Q ν₀ i)) :
    PosModel j hj Q Λ Λc ν₀ s n (Nat.le_of_succ_le hn) L ≃ₗ[Tpᵐᵒᵖ]
      PosModel j hj Q Λ Λc ν₀ s (n + 1) hn L :=
  LinearEquiv.ofBijective (posPassRight L hL s n hn)
    (posPassRight_bijective L hP hPL hL i s hn hs hκ)

end Categorification.Stendhal.CupCap
