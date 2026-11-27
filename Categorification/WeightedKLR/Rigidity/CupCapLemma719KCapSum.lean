/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KGen
import Categorification.WeightedKLR.Rigidity.CupCapSliding
import Categorification.WeightedKLR.Rigidity.CupCapMidGenerators

/-!
# The cap generators at a fixed position, in the reflection of `K^{λ⁺}_λ`

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof. The map `S_+(Z ⊠ L) → K S(Z)` sends
`y ⊠ v` to `(∑_s cap(s, n, v)) ⊗ y`, with the maximum of the cap at the position `n` of the cut.
This file computes how the generators act on the sum `capSum n v = ∑_s cap(s, n, v)` in the
reflection `K^σ` (`ReflectedCap`):

* a dot or a crossing of the top on one side of the maximum, acting from the right, equals the
  shifted dot or crossing acting from the left (`op_x_smul_capSum`, `op_ψ_smul_capSum`; the
  relations `dot` and `cross` of `K̃^{λ⁺}_λ`, Definition 7.15);
* a dot or a crossing at the maximum acting on the coefficient equals the dot or crossing in the
  window of the cap acting from the left (`capSum_box_x`, `capSum_box_ψ`; the relation `box`);
* idempotents act loading by loading (`op_e_smul_capGen`, `eSum_smul_capGen_of_subset`,
  `eSum_smul_capGen_of_disjoint`).

## Main definitions

* `Stendhal.CupCap.capGen`: the cap generator `cap(s, n, v)` in `K^σ`.
* `Stendhal.CupCap.capSum`: the sum over the top loadings.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

set_option hygiene false in
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
set_option hygiene false in
local notation "Tp" => TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "T" => TensorProductAlgebra k Q Λ ν
set_option hygiene false in
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
set_option hygiene false in
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

variable (j hj Q Λ Λc ν ν₀) in
/-- **The cap generator** `cap(s, n, v)` in the reflection of `K^{λ⁺}_λ`. -/
def capGen (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    ReflectedCap j hj Q Λ Λc ν ν₀ L :=
  toRefl (capElt 1 s n v 1)

variable (j hj Q Λ Λc ν ν₀) in
/-- **The sum of the cap generators at the position `n`** over all top loadings. -/
def capSum (n : Fin (m + 1)) (v : L) : ReflectedCap j hj Q Λ Λc ν ν₀ L :=
  ∑ s, capGen j hj Q Λ Λc ν ν₀ s n v

/-- A diagram of `T^λ`, acting from the right, attaches its mirror image above the cap. -/
theorem op_smul_capGen (a : R) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν a)) • capGen j hj Q Λ Λc ν ν₀ s n v =
      toRefl (capElt (1 * topMap k Q Λ ν (hflip a)) s n v 1) := by
  rw [capGen, op_mk_smul_toRefl, one_mul]
  congr 1
  have h := smul_capElt (j := j) (hj := hj) (L := L) (Λc := Λc) (ν₀ := ν₀) (Q := Q) (Λ := Λ)
    (topMap k Q Λ ν (hflip a)) 1 1 s n v 1
  rw [map_one, mul_one, mul_one] at h
  exact h

/-- A diagram of `T^{λ⁺}`, acting from the left, attaches its mirror image below the cap. -/
theorem smul_capGen (b : Rp) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀) (botMap k Q Λ Λc j hj ν ν₀ b) •
        capGen j hj Q Λ Λc ν ν₀ s n v =
      toRefl (capElt 1 s n v (hflip b)) := by
  rw [capGen, mk_smul_toRefl]
  congr 1
  have h := smul_capElt (j := j) (hj := hj) (L := L) (Λc := Λc) (ν₀ := ν₀) (Q := Q) (Λ := Λ)
    1 (hflip b) 1 s n v 1
  rw [mul_one, one_mul] at h
  exact h

/-! ### Dots and crossings of the top -/

/-- **A dot of the top passes below the cap** (the relation `dot`). -/
theorem op_x_smul_capGen (a : Fin m) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.x a))) •
        capGen j hj Q Λ Λc ν ν₀ s n v =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a))) •
        capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [op_smul_capGen, smul_capGen, hflip_x, hflip_x, capElt_dot, mul_one]

theorem op_x_smul_capSum (a : Fin m) (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.x a))) •
        capSum j hj Q Λ Λc ν ν₀ n v =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a))) •
        capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, Finset.smul_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => op_x_smul_capGen a s n v

/-- **A crossing of the top on one side of the maximum passes below the cap** (the relation
`cross`). -/
theorem op_ψ_smul_capGen (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (p : ℕ)
    (hp : p + 1 < n.val ∨ n.val ≤ p) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.ψ p))) •
        capGen j hj Q Λ Λc ν ν₀ s n v =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀
          (KLRAlgebra.ψ (crossPos n (Multiset.card (stendhalWeight 2 ν₀)) p))) •
        capGen j hj Q Λ Λc ν ν₀ (sadj m p • s) n v := by
  rw [op_smul_capGen, smul_capGen, hflip_ψ, hflip_ψ, capElt_cross 1 s n v p hp, mul_one]

theorem op_ψ_smul_capSum (n : Fin (m + 1)) (v : L) (p : ℕ) (hp : p + 1 < n.val ∨ n.val ≤ p) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.ψ p))) •
        capSum j hj Q Λ Λc ν ν₀ n v =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀
          (KLRAlgebra.ψ (crossPos n (Multiset.card (stendhalWeight 2 ν₀)) p))) •
        capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, Finset.smul_sum, Finset.smul_sum]
  simp_rw [op_ψ_smul_capGen _ n v p hp]
  have hb : Function.Bijective (fun s : Seq (stendhalWeight ℓ ν) => sadj m p • s) :=
    Function.Involutive.bijective fun s => sadj_smul_smul p s
  exact Fintype.sum_bijective _ hb _ _ fun _ => rfl

/-! ### Idempotents -/

/-- **An idempotent of the top selects the top loading.** -/
theorem op_e_smul_capGen (u s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.e u))) •
        capGen j hj Q Λ Λc ν ν₀ s n v =
      if u = s then capGen j hj Q Λ Λc ν ν₀ s n v else 0 := by
  rw [op_smul_capGen, hflip_e]
  split_ifs with h
  · rw [h, capElt_idem]
    rfl
  · rw [← capElt_idem, one_mul, ← map_mul, e_mul_e, ite_eq_right_of_eq_false _ _ (eq_false h),
      map_zero, capElt_zero_left]
    exact Submodule.Quotient.mk_zero _

/-- **An idempotent sum below the cap containing all bottom loadings acts by the identity.** -/
theorem eSum_smul_capGen_of_subset (F : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))))
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (hF : insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2) ⊆ F) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.eSum _ F)) • capGen j hj Q Λ Λc ν ν₀ s n v =
      capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [smul_capGen, KLRAlgebra.eSum, hflip_sum]
  simp only [hflip_e]
  rw [← KLRAlgebra.eSum, capElt_eq_eSum_mul, eSum_mul_eSum, Finset.inter_eq_left.2 hF,
    ← mul_one (KLRAlgebra.eSum _ _), ← capElt_eq_eSum_mul]
  rfl

/-- **An idempotent sum below the cap missing all bottom loadings acts by zero.** -/
theorem eSum_smul_capGen_of_disjoint (F : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))))
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (hF : Disjoint (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2)) F) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.eSum _ F)) • capGen j hj Q Λ Λc ν ν₀ s n v = 0 := by
  rw [smul_capGen, KLRAlgebra.eSum, hflip_sum]
  simp only [hflip_e]
  rw [← KLRAlgebra.eSum, capElt_eq_eSum_mul, eSum_mul_eSum, Finset.disjoint_iff_inter_eq_empty.1 hF]
  rw [show KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj)) ∅ = 0 from Finset.sum_empty,
    capElt_zero_right]
  exact Submodule.Quotient.mk_zero _

/-! ### Diagrams at the maximum -/

/-- **A dot at the maximum is the dot in the window of the cap** (the relation `box`). -/
theorem capGen_box_x (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (b : Fin (Multiset.card (stendhalWeight 2 ν₀))) :
    capGen j hj Q Λ Λc ν ν₀ s n (op (cupMap k Q Λc ν₀ (KLRAlgebra.x b)) • v) =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀
          (KLRAlgebra.x ⟨n.val + b.val, add_lt_M (Nat.lt_succ_iff.1 n.2) b⟩)) •
        capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [smul_capGen, hflip_x, capGen, capElt_box, insertMap_x, mul_one, x_mul_eSum,
    ← capElt_eq_eSum_mul]

theorem capSum_box_x (n : Fin (m + 1)) (v : L) (b : Fin (Multiset.card (stendhalWeight 2 ν₀))) :
    capSum j hj Q Λ Λc ν ν₀ n (op (cupMap k Q Λc ν₀ (KLRAlgebra.x b)) • v) =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀
          (KLRAlgebra.x ⟨n.val + b.val, add_lt_M (Nat.lt_succ_iff.1 n.2) b⟩)) •
        capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, capSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => capGen_box_x s n v b

/-- **A crossing at the maximum is the crossing in the window of the cap** (the relation
`box`). -/
theorem capGen_box_ψ (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) {q : ℕ}
    (hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)) :
    capGen j hj Q Λ Λc ν ν₀ s n (op (cupMap k Q Λc ν₀ (KLRAlgebra.ψ q)) • v) =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.ψ (n.val + q))) •
        capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [smul_capGen, hflip_ψ, capGen, capElt_box, insertMap_ψ _ _ hq, mul_one]
  have hE : (KLRAlgebra.ψ (n.val + q) * KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
      (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2)) : Rp) =
      KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2)) *
        KLRAlgebra.ψ (n.val + q) :=
    (insertEmb (j := j) (hj := hj) (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2)).ψ_mul_E
      (by simpa using hq)
  rw [hE, ← capElt_eq_eSum_mul]

theorem capSum_box_ψ (n : Fin (m + 1)) (v : L) {q : ℕ}
    (hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)) :
    capSum j hj Q Λ Λc ν ν₀ n (op (cupMap k Q Λc ν₀ (KLRAlgebra.ψ q)) • v) =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.ψ (n.val + q))) •
        capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, capSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => capGen_box_ψ s n v hq

/-- **An idempotent at the maximum is the idempotent of the inserted loading** (the relation
`box`). -/
theorem capGen_box_e (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (w : Seq (stendhalWeight 2 ν₀)) :
    capGen j hj Q Λ Λc ν ν₀ s n (op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v) =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e (insertSeq s n (Nat.lt_succ_iff.1 n.2)
          (Seq.map (cupColour j hj) w)))) •
        capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [smul_capGen, hflip_e, capGen, capElt_box, insertMap_e, mul_one]

/-- An idempotent sum of the top selects the top loadings in it. -/
theorem op_eSum_smul_capGen (F : Finset (Seq (stendhalWeight ℓ ν))) (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.eSum _ F))) •
        capGen j hj Q Λ Λc ν ν₀ s n v =
      if s ∈ F then capGen j hj Q Λ Λc ν ν₀ s n v else 0 := by
  rw [KLRAlgebra.eSum, map_sum, map_sum, Finset.op_sum, Finset.sum_smul]
  simp_rw [op_e_smul_capGen]
  exact Finset.sum_ite_eq' F s _

/-! ### Linearity in the coefficient -/

theorem capGen_add (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v w : L) :
    capGen j hj Q Λ Λc ν ν₀ s n (v + w) =
      capGen j hj Q Λ Λc ν ν₀ s n v + capGen j hj Q Λ Λc ν ν₀ s n w := by
  rw [capGen, capElt_add_mid]
  exact toRefl_add _ _

theorem capSum_add (n : Fin (m + 1)) (v w : L) :
    capSum j hj Q Λ Λc ν ν₀ n (v + w) =
      capSum j hj Q Λ Λc ν ν₀ n v + capSum j hj Q Λ Λc ν ν₀ n w := by
  simp only [capSum, capGen_add, Finset.sum_add_distrib]

/-- **The scalars act on the cap generators from both sides alike.** -/
theorem op_algebraMap_smul_capGen (c : k) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1))
    (v : L) :
    op (algebraMap k T c) • capGen j hj Q Λ Λc ν ν₀ s n v =
      algebraMap k Tp c • capGen j hj Q Λ Λc ν ν₀ s n v := by
  have ha : algebraMap k T c =
      TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (algebraMap k R c)) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  have hb : algebraMap k Tp c = TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
      (botMap k Q Λ Λc j hj ν ν₀ (algebraMap k Rp c)) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [ha, hb, op_smul_capGen, smul_capGen, hflip_algebraMap, hflip_algebraMap, AlgHom.commutes,
    one_mul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one c, capElt_smul_right]

theorem op_algebraMap_smul_capSum (c : k) (n : Fin (m + 1)) (v : L) :
    op (algebraMap k T c) • capSum j hj Q Λ Λc ν ν₀ n v =
      algebraMap k Tp c • capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, Finset.smul_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => op_algebraMap_smul_capGen c s n v

/-- **An idempotent above the cap selects one top loading.** -/
theorem op_e_smul_capSum (u : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) :
    op (TensorProductAlgebra.mk Q Λ ν (topMap k Q Λ ν (KLRAlgebra.e u))) •
        capSum j hj Q Λ Λc ν ν₀ n v = capGen j hj Q Λ Λc ν ν₀ u n v := by
  rw [capSum, Finset.smul_sum]
  simp only [op_e_smul_capGen, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

variable [Module k L] [IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

theorem capGen_smul (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (c : k) (v : L) :
    capGen j hj Q Λ Λc ν ν₀ s n (c • v) = algebraMap k Tp c • capGen j hj Q Λ Λc ν ν₀ s n v := by
  have hv : c • v = op (cupMap k Q Λc ν₀ (algebraMap k _ c)) • v := by
    rw [AlgHom.commutes, ← MulOpposite.algebraMap_apply]
    exact (_root_.algebraMap_smul _ c v).symm
  have ha : algebraMap k Tp c = TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
      (botMap k Q Λ Λc j hj ν ν₀ (algebraMap k _ c)) := by
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [hv, ha, smul_capGen, hflip_algebraMap, capGen, capElt_box, insertMap_algebraMap, mul_one,
    capElt_smul_right, Algebra.algebraMap_eq_smul_one, capElt_smul_right,
    ← mul_one (KLRAlgebra.eSum _ _), ← capElt_eq_eSum_mul]

theorem capSum_smul (n : Fin (m + 1)) (c : k) (v : L) :
    capSum j hj Q Λ Λc ν ν₀ n (c • v) = algebraMap k Tp c • capSum j hj Q Λ Λc ν ν₀ n v := by
  rw [capSum, capSum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => capGen_smul s n c v

end Categorification.Stendhal.CupCap
