/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndDescent
import Categorification.WeightedKLR.Rigidity.CupCapInducedMaps

/-!
# The model of the cap bimodule when the cap is at the right end

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, in the case `j = ℓ`. The model of
`K̃^{λ⁺}_λ` is the module `Y = L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` induced along the map placing a diagram at
the maximum on the last `N` strands of `λ⁺` (`CupCap.endStendhal`). The right action of `T̃^{λ⁺}`
is the module structure of the induced module; `T̃^λ` acts on the left through the diagrams of `λ`
on the first `m` strands (`CupCap.prefixStendhal`), which commute with the diagrams at the maximum.
Together they make `Y` a `T̃^λ`–`T̃^{λ⁺}` bimodule (`CupCap.EndModel.instModuleEnv`).

## Main definitions

* `CupCap.endStendhal`: the diagrams at the maximum on the last `N` strands, on `T̃`.
* `CupCap.EndModel`: the induced module `Y`.
* `CupCap.EndModel.leftAct`, `CupCap.EndModel.rightAct`: the two actions.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section EndKLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (ν ν₀) in
theorem eSum_endSet :
    (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (endSet ν ν₀) :
      KLRAlgebra k _ (stendhalWeight (ℓ + 2) (ν + ν₀))) =
      ∑ s : Seq (stendhalWeight ℓ ν),
        KLRAlgebra.eSum _ (insertSet (j := ℓ) (hj := le_rfl) (ν₀ := ν₀) s m le_rfl) := by
  rw [endSet, KLRAlgebra.eSum, Finset.sum_biUnion]
  · rfl
  · intro s _ s' _ hss'
    refine Finset.disjoint_left.2 fun u hu hu' => hss' ?_
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
    exact ((insertSeq_mem_insertSet (s := s) (s' := s') (t := t)).1 hu').symm

/-- **A diagram at the maximum on the last `N` strands is the sum over the loadings of `λ` of the
diagrams at the maximum below the cap generators.** -/
theorem endMapKLR_eq_sum (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endMapKLR Q Λ Λc ν ν₀ x =
      ∑ s : Seq (stendhalWeight ℓ ν), insertMap (j := ℓ) (hj := le_rfl) Q Λ Λc s m le_rfl x := by
  have h : KLRAlgebra.eSum _ (endSet ν ν₀) * endMapKLR Q Λ Λc ν ν₀ x = endMapKLR Q Λ Λc ν ν₀ x :=
    KLR.Corner.E_mul_val _
  rw [← h, eSum_endSet, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [insertMap_eq_prefix_mul_end, prefixMapKLR_e]

theorem insertMap_smul (s : Seq (stendhalWeight ℓ ν)) (c : k)
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    insertMap (j := ℓ) (hj := le_rfl) Q Λ Λc s m le_rfl (c • x) =
      c • insertMap (j := ℓ) (hj := le_rfl) Q Λ Λc s m le_rfl x := by
  unfold insertMap
  rw [map_smul]; exact KLR.Corner.val_smul c _

end EndKLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section EndDescent

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (ν ν₀) in
/-- The diagrams at the maximum on the last `N` strands of `λ⁺`, in `T̃^{λ⁺}`, before
descending. -/
def endBot :
    KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀) →ₙₐ[k]
      StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) where
  toFun x := botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ x)
  map_zero' := by rw [endMapKLR_eq_sum]; simp [insertMap]
  map_add' a b := by rw [endMapKLR_add, map_add]
  map_mul' a b := by rw [endMapKLR_mul, map_mul]
  map_smul' c a := by
    change botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ (c • a)) =
      c • botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ a)
    rw [endMapKLR_eq_sum, endMapKLR_eq_sum, map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← map_smul, insertMap_smul]

theorem endBot_apply (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endBot Q Λ Λc ν ν₀ x = botMap k Q Λ Λc ℓ le_rfl ν ν₀ (endMapKLR Q Λ Λc ν ν₀ x) := rfl

theorem redRelations_endBot : RedRelations (endBot Q Λ Λc ν ν₀) where
  red_dot b w hb := by
    rw [endBot_apply, endMapKLR_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [insertMap_mul, insertMap_x, insertMap_e, mul_assoc, eSum_mul_e_insertSeq, botMap,
      AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_win s le_rfl _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩ rfl,
      Seq.map_lbl]
    obtain ⟨r, hr⟩ : ∃ r, w.lbl b = .inr r := by cases h : w.lbl b <;> simp_all
    exact (congrArg (fun a => (cupColour (I := I) ℓ le_rfl a).isRight) hr).trans rfl
  red_cross p hp w ha hb := by
    rw [endBot_apply, endMapKLR_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    rw [insertMap_mul, insertMap_ψ s le_rfl hp, insertMap_e, mul_assoc, eSum_mul_e_insertSeq,
      botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red (m + p) (by omega) _ ?_ ?_, map_zero]
    · rw [insertSeq_lbl_win s le_rfl _ ⟨p, by rw [Multiset.card_map]; omega⟩ rfl, Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p, by omega⟩ = .inr r := by
        cases h : w.lbl ⟨p, by omega⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) ℓ le_rfl a).isRight) hr).trans rfl
    · rw [insertSeq_lbl_win s le_rfl _ ⟨p + 1, by rw [Multiset.card_map]; omega⟩ (by simp; omega),
        Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p + 1, hp⟩ = .inr r := by
        cases h : w.lbl ⟨p + 1, hp⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) ℓ le_rfl a).isRight) hr).trans rfl

variable (ν ν₀) in
/-- **The diagrams at the maximum on the last `N` strands of `λ⁺`**, as a map
`T̃^{(μ,μ*)} → T̃^{λ⁺}`. -/
def endStendhal :
    StendhalAlgebra k Q Λc ν₀ →ₙₐ[k] StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) :=
  stendhalLift (redRelations_endBot Q Λ Λc)

theorem endStendhal_eq (z : StendhalAlgebra k Q Λc ν₀) :
    ∃ x, endStendhal Q Λ Λc ν ν₀ z = endBot Q Λ Λc ν ν₀ x := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨x, ?_⟩
  rw [endStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

theorem endStendhal_cupMap (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endStendhal Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ x) =
      endBot Q Λ Λc ν ν₀ x * endStendhal Q Λ Λc ν ν₀ 1 := by
  rw [endStendhal, stendhalLift_topMap]
  rfl

variable (ν ν₀) in
/-- The idempotent cutting the last `N` strands of `λ⁺` to the loadings of the maximum. -/
abbrev endIdem : StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) :=
  botMap k Q Λ Λc ℓ le_rfl ν ν₀ (KLRAlgebra.eSum _ (endSet ν ν₀))

theorem endIdem_mul_endBot (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endIdem Q Λ Λc ν ν₀ * endBot Q Λ Λc ν ν₀ x = endBot Q Λ Λc ν ν₀ x := by
  rw [endBot_apply, ← map_mul, endMapKLR]
  exact congrArg _ (KLR.Corner.E_mul_val _)

theorem endBot_mul_endIdem (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    endBot Q Λ Λc ν ν₀ x * endIdem Q Λ Λc ν ν₀ = endBot Q Λ Λc ν ν₀ x := by
  rw [endBot_apply, ← map_mul, endMapKLR]
  exact congrArg _ (KLR.Corner.val_mul_E _)

theorem commute_prefixBot_endBot (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    Commute (prefixBot Q Λ Λc ν ν₀ a) (endBot Q Λ Λc ν ν₀ x) :=
  commute_prefixBot_endMapKLR Q Λ Λc a x

theorem commute_prefixStendhal_endStendhal (z : StendhalAlgebra k Q Λ ν)
    (c : StendhalAlgebra k Q Λc ν₀) :
    Commute (prefixStendhal Q Λ Λc ν ν₀ z) (endStendhal Q Λ Λc ν ν₀ c) := by
  obtain ⟨a, ha⟩ := prefixStendhal_eq Q Λ Λc (ν₀ := ν₀) z
  obtain ⟨x, hx⟩ := endStendhal_eq Q Λ Λc (ν := ν) c
  rw [ha, hx]
  exact commute_prefixBot_endBot Q Λ Λc a x

/-- The unit of the end block absorbs the left action of `T̃^λ`. -/
theorem prefixStendhal_one_mul_endUnit :
    prefixStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
  obtain ⟨x, hx⟩ := endStendhal_eq Q Λ Λc (ν := ν) (ν₀ := ν₀) 1
  rw [hx, ← endIdem_mul_endBot, ← mul_assoc, prefixStendhal_one_mul_endIdem]

end EndDescent

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "T" => StendhalAlgebra k Q Λ ν

/-- The end block on the opposite rings: induction along it is the model of `K̃`. -/
def endOp : Tcᵐᵒᵖ →ₙ+* Tpᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (endStendhal Q Λ Λc ν ν₀))

theorem endOp_apply (c : Tcᵐᵒᵖ) : endOp Q Λ Λc ν ν₀ c = op (endStendhal Q Λ Λc ν ν₀ c.unop) := rfl

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The model of `K̃^{λ⁺}_λ` for a cap at the right end**: `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}`, induced
along the diagrams at the maximum on the last `N` strands. -/
abbrev EndModel : Type _ := Ind L (endOp Q Λ Λc ν ν₀)

instance : Module k (EndModel Q Λ Λc ν ν₀ L) :=
  Module.compHom _ (algebraMap k Tpᵐᵒᵖ)

theorem algebraMap_smul (c : k) (y : EndModel Q Λ Λc ν ν₀ L) :
    c • y = algebraMap k Tpᵐᵒᵖ c • y := rfl

/-- The element giving the left action of `z ∈ T̃^λ`. -/
def leftElt (z : T) : Tpᵐᵒᵖ :=
  op (endStendhal Q Λ Λc ν ν₀ 1 * prefixStendhal Q Λ Λc ν ν₀ z)

theorem leftElt_intertwines (z : T) :
    Intertwines (endOp Q Λ Λc ν ν₀) (endOp Q Λ Λc ν ν₀) (leftElt Q Λ Λc ν ν₀ z) := fun c => by
  rw [endOp_apply, leftElt, ← op_mul, ← op_mul]
  congr 1
  have h1 : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ c.unop =
      endStendhal Q Λ Λc ν ν₀ c.unop := by rw [← map_mul, one_mul]
  have h2 : endStendhal Q Λ Λc ν ν₀ c.unop * endStendhal Q Λ Λc ν ν₀ 1 =
      endStendhal Q Λ Λc ν ν₀ c.unop := by rw [← map_mul, mul_one]
  rw [mul_assoc, (commute_prefixStendhal_endStendhal Q Λ Λc z c.unop).eq, ← mul_assoc, h1,
    ← mul_assoc, h2]

theorem leftElt_unit (z : T) :
    leftElt Q Λ Λc ν ν₀ z * endOp Q Λ Λc ν ν₀ 1 = leftElt Q Λ Λc ν ν₀ z := by
  rw [endOp_apply, leftElt, ← op_mul]
  congr 1
  rw [unop_one, ← mul_assoc, ← map_mul, one_mul]

theorem intertwinesOn_leftElt (z : T) :
    IntertwinesOn L (endOp Q Λ Λc ν ν₀) (endOp Q Λ Λc ν ν₀) (leftElt Q Λ Λc ν ν₀ z) :=
  IntertwinesOn.of_intertwines (leftElt_intertwines Q Λ Λc ν ν₀ z) (leftElt_unit Q Λ Λc ν ν₀ z)

/-- **The left action of `T̃^λ` on the model**: `z · (y ⊗ v) = (prefix(z) y) ⊗ v`. -/
def leftAct (z : T) : EndModel Q Λ Λc ν ν₀ L →ₗ[Tpᵐᵒᵖ] EndModel Q Λ Λc ν ν₀ L :=
  natMapOn (intertwinesOn_leftElt Q Λ Λc ν ν₀ L z)

theorem leftAct_tmul (z : T) (y : Corner (endOp Q Λ Λc ν ν₀)) (v : L) :
    leftAct Q Λ Λc ν ν₀ L z (Ind.tmul y v) =
      Ind.tmul ⟨y.1 * leftElt Q Λ Λc ν ν₀ z, (cornerMulOf (intertwinesOn_leftElt Q Λ Λc ν ν₀ L
        z).unit y).2⟩ v := rfl

theorem leftAct_one : leftAct Q Λ Λc ν ν₀ L 1 = LinearMap.id := by
  refine Ind.ext fun y v => ?_
  rw [leftAct_tmul, LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  change y.1 * leftElt Q Λ Λc ν ν₀ 1 = y.1
  have hy : y.1 * endOp Q Λ Λc ν ν₀ 1 = y.1 := y.2
  have key : endOp Q Λ Λc ν ν₀ 1 * leftElt Q Λ Λc ν ν₀ 1 = endOp Q Λ Λc ν ν₀ 1 := by
    rw [endOp_apply, leftElt, ← op_mul, unop_one, mul_assoc, prefixStendhal_one_mul_endUnit,
      ← map_mul, one_mul]
  calc y.1 * leftElt Q Λ Λc ν ν₀ 1 = y.1 * endOp Q Λ Λc ν ν₀ 1 * leftElt Q Λ Λc ν ν₀ 1 := by
        rw [hy]
    _ = y.1 := by rw [mul_assoc, key, hy]

theorem leftAct_mul (z z' : T) :
    leftAct Q Λ Λc ν ν₀ L (z * z') =
      (leftAct Q Λ Λc ν ν₀ L z).comp (leftAct Q Λ Λc ν ν₀ L z') := by
  refine Ind.ext fun y v => ?_
  rw [LinearMap.comp_apply, leftAct_tmul, leftAct_tmul, leftAct_tmul]
  congr 1
  apply Subtype.ext
  change y.1 * leftElt Q Λ Λc ν ν₀ (z * z') =
    y.1 * leftElt Q Λ Λc ν ν₀ z' * leftElt Q Λ Λc ν ν₀ z
  rw [mul_assoc, leftElt, leftElt, leftElt, ← op_mul]
  congr 2
  have hc := (commute_prefixStendhal_endStendhal Q Λ Λc z (1 : StendhalAlgebra k Q Λc ν₀)).eq
  have he : endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
    rw [← map_mul, one_mul]
  rw [map_mul, mul_assoc (endStendhal Q Λ Λc ν ν₀ 1) (prefixStendhal Q Λ Λc ν ν₀ z),
    ← mul_assoc (prefixStendhal Q Λ Λc ν ν₀ z), hc]
  simp only [← mul_assoc, he]

instance : IsScalarTower k Tpᵐᵒᵖ (EndModel Q Λ Λc ν ν₀ L) where
  smul_assoc c b y := by
    change (c • b) • y = algebraMap k Tpᵐᵒᵖ c • b • y
    rw [← mul_smul, ← Algebra.smul_def]

instance : SMulCommClass Tpᵐᵒᵖ k (EndModel Q Λ Λc ν ν₀ L) where
  smul_comm b c y := by
    rw [algebraMap_smul, algebraMap_smul, ← mul_smul, ← mul_smul, Algebra.commutes]

instance : SMulCommClass k Tpᵐᵒᵖ (EndModel Q Λ Λc ν ν₀ L) := SMulCommClass.symm _ _ _

theorem leftAct_add (z z' : T) :
    leftAct Q Λ Λc ν ν₀ L (z + z') = leftAct Q Λ Λc ν ν₀ L z + leftAct Q Λ Λc ν ν₀ L z' := by
  refine Ind.ext fun y v => ?_
  rw [LinearMap.add_apply, leftAct_tmul, leftAct_tmul, leftAct_tmul, ← Ind.add_tmul]
  congr 1
  apply Subtype.ext
  change y.1 * leftElt Q Λ Λc ν ν₀ (z + z') =
    y.1 * leftElt Q Λ Λc ν ν₀ z + y.1 * leftElt Q Λ Λc ν ν₀ z'
  rw [← mul_add, leftElt, leftElt, leftElt, ← op_add, map_add, mul_add]

theorem leftAct_smul (c : k) (z : T) (y : EndModel Q Λ Λc ν ν₀ L) :
    leftAct Q Λ Λc ν ν₀ L (c • z) y = c • leftAct Q Λ Λc ν ν₀ L z y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', smul_add]
  | tmul y v =>
    rw [leftAct_tmul, leftAct_tmul, algebraMap_smul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    change y.1 * leftElt Q Λ Λc ν ν₀ (c • z) =
      algebraMap k Tpᵐᵒᵖ c * (y.1 * leftElt Q Λ Λc ν ν₀ z)
    rw [leftElt, leftElt, map_smul, mul_smul_comm, op_smul, mul_smul_comm]
    exact Algebra.smul_def (A := Tpᵐᵒᵖ) c _

/-- The left action of `T̃^λ` on the model, as an algebra map. -/
def leftAlg : T →ₐ[k] Module.End k (EndModel Q Λ Λc ν ν₀ L) where
  toFun z := (leftAct Q Λ Λc ν ν₀ L z).restrictScalars k
  map_one' := by rw [leftAct_one]; rfl
  map_mul' z z' := by rw [leftAct_mul]; rfl
  map_zero' := by
    ext y
    change leftAct Q Λ Λc ν ν₀ L 0 y = 0
    have h := congrArg (· y) (leftAct_add Q Λ Λc ν ν₀ L 0 0)
    simp only [add_zero, LinearMap.add_apply] at h
    simpa using h
  map_add' z z' := by rw [leftAct_add]; rfl
  commutes' c := by
    ext y
    change leftAct Q Λ Λc ν ν₀ L (algebraMap k T c) y = c • y
    rw [Algebra.algebraMap_eq_smul_one, leftAct_smul, leftAct_one, LinearMap.id_apply]

theorem leftAlg_apply (z : T) (y : EndModel Q Λ Λc ν ν₀ L) :
    leftAlg Q Λ Λc ν ν₀ L z y = leftAct Q Λ Λc ν ν₀ L z y := rfl

/-- The right action of `T̃^{λ⁺}` on the model, as an algebra map. -/
def rightAlg : Tpᵐᵒᵖ →ₐ[k] Module.End k (EndModel Q Λ Λc ν ν₀ L) :=
  Algebra.lsmul k k (EndModel Q Λ Λc ν ν₀ L)

/-- **The bimodule structure on the model**. -/
def envAlg : Env k Q Λ Λc ℓ le_rfl ν ν₀ →+* Module.End k (EndModel Q Λ Λc ν ν₀ L) :=
  (Algebra.TensorProduct.lift (leftAlg Q Λ Λc ν ν₀ L) (rightAlg Q Λ Λc ν ν₀ L) fun z b =>
    LinearMap.ext fun y => by
      rw [Module.End.mul_apply, Module.End.mul_apply]
      exact (leftAct Q Λ Λc ν ν₀ L z).map_smul b y).toRingHom

instance instModuleEnv : Module (Env k Q Λ Λc ℓ le_rfl ν ν₀) (EndModel Q Λ Λc ν ν₀ L) :=
  Module.compHom _ (envAlg Q Λ Λc ν ν₀ L)

theorem envMk_smul (a : T) (b : Tp) (y : EndModel Q Λ Λc ν ν₀ L) :
    Env.mk a b • y = leftAct Q Λ Λc ν ν₀ L a (op b • y) := rfl

end Model

end Categorification.Stendhal.CupCap
