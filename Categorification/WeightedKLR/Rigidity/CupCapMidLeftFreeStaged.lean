/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent

/-!
# The induced module with the maximum at an arbitrary position of a loading

Webster, arXiv:1309.3796v3, §7.3, toward the left projectivity of `coe^{λ⁺}_λ` asserted after
Lemma 7.19 (staged transparency, step (I1) of the route). For a loading `s` of `λ` and a position
`n ≤ m`, placing a diagram of `R((μ, μ*))` on the window at `n` of `s` (`insertMap s n`) kills
the red dots and the red crossings, so it descends to a nonunital map
`T̃^{(μ,μ*)} → T̃^{λ⁺}` (`posStendhal`). Induction along it is `L ⊗_{T̃^{(μ,μ*)}} e_{s,n} T̃^{λ⁺}`
(`PosModel`): the configuration with the black strands `s_0, …, s_{n-1}` left of the window and the
others right of it.

## Main definitions

* `CupCap.posBot`, `CupCap.posStendhal`: the diagrams on the window at position `n` of `s`.
* `CupCap.posOp`: the same on the opposite rings.
* `CupCap.PosModel`: the induced module.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

theorem insertMap_smul_pos (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (c : k)
    (x : Rc) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn (c • x) =
      c • insertMap (j := j) (hj := hj) Q Λ Λc s n hn x := by
  unfold insertMap
  rw [map_smul]; exact KLR.Corner.val_smul c _

theorem insertMap_zero_pos (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s n hn 0 = 0 := by
  simp [insertMap]

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (j hj Q Λ Λc ν₀) in
/-- The diagrams on the window at position `n` of `s`, in `T̃^{λ⁺}`, before descending. -/
def posBot (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) : Rc →ₙₐ[k] Tp where
  toFun x := botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n hn x)
  map_zero' := by rw [insertMap_zero_pos, map_zero]
  map_add' a b := by rw [insertMap_add, map_add]
  map_mul' a b := by rw [insertMap_mul, map_mul]
  map_smul' c a := by
    change botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n hn (c • a)) =
      c • botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n hn a)
    rw [insertMap_smul_pos, map_smul]

theorem posBot_apply (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    posBot j hj Q Λ Λc ν₀ s n hn x = botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n hn x) :=
  rfl

theorem redRelations_posBot (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    RedRelations (posBot j hj Q Λ Λc ν₀ s n hn) where
  red_dot b w hb := by
    rw [posBot_apply, insertMap_mul, insertMap_x, insertMap_e, mul_assoc, eSum_mul_e_insertSeq,
      botMap, AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_win s hn _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩ rfl,
      Seq.map_lbl]
    obtain ⟨r, hr⟩ : ∃ r, w.lbl b = .inr r := by cases h : w.lbl b <;> simp_all
    exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl
  red_cross p hp w ha hb := by
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    rw [posBot_apply, insertMap_mul, insertMap_ψ s hn hp, insertMap_e, mul_assoc,
      eSum_mul_e_insertSeq, botMap, AlgHom.comp_apply,
      ofKLR_ψ_mul_e_of_red (n + p) (by omega) _ ?_ ?_, map_zero]
    · rw [insertSeq_lbl_win s hn _ ⟨p, by rw [Multiset.card_map]; omega⟩ rfl, Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p, by omega⟩ = .inr r := by
        cases h : w.lbl ⟨p, by omega⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl
    · rw [insertSeq_lbl_win s hn _ ⟨p + 1, by rw [Multiset.card_map]; omega⟩ (by simp; omega),
        Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p + 1, hp⟩ = .inr r := by
        cases h : w.lbl ⟨p + 1, hp⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl

variable (j hj Q Λ Λc ν₀) in
/-- **The diagrams on the window at position `n` of `s`**, as a map `T̃^{(μ,μ*)} → T̃^{λ⁺}`. -/
def posStendhal (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) :
    StendhalAlgebra k Q Λc ν₀ →ₙₐ[k] Tp :=
  stendhalLift (redRelations_posBot (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν₀ := ν₀) s hn)

theorem posStendhal_cupMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    posStendhal j hj Q Λ Λc ν₀ s n hn (cupMap k Q Λc ν₀ x) =
      posBot j hj Q Λ Λc ν₀ s n hn x * posStendhal j hj Q Λ Λc ν₀ s n hn 1 := by
  rw [posStendhal, stendhalLift_topMap]
  rfl

variable (j hj Q Λ Λc ν₀) in
/-- The diagrams on the window at position `n` of `s`, on the opposite rings. -/
def posOp (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) :
    (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+* Tpᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom
    (posStendhal j hj Q Λ Λc ν₀ s n hn))

theorem posOp_apply (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (c : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    posOp j hj Q Λ Λc ν₀ s n hn c = op (posStendhal j hj Q Λ Λc ν₀ s n hn c.unop) := rfl

variable (j hj Q Λ Λc ν₀) in
/-- **The induced module `L ⊗_{T̃^{(μ,μ*)}} e_{s,n} T̃^{λ⁺}`** with the maximum at position `n`
of the loading `s`. -/
abbrev PosModel (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n ≤ m) (L : Type*) [AddCommGroup L]
    [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] : Type _ :=
  Ind L (posOp j hj Q Λ Λc ν₀ s n hn)

end Categorification.Stendhal.CupCap
