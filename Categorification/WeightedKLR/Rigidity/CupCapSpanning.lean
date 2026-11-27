/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapDiagrams
import Categorification.KLR.StrandCoset
import Categorification.KLR.Prop213
import Categorification.WeightedKLR.RedStrands.StandardModule

/-!
# Spanning `K̃^{λ⁺}_λ` by canonical cap generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
proof of Lemma 7.17 (spanning half, first step).

Webster's spanning set `B''` of `K̃^{λ⁺}_λ` consists of diagrams with the maximum of the cap
inserted directly to the left of the red strand `λ_{j+1}` at the top (the *canonical position*
`capPos s` of the top loading `s`), the element of `L` at the maximum, and, below the cap, only
crossings among the strands left of `λ_{j+1}`. The new point of the proof, compared with the
spanning argument for `T̃^λ` (Lemma 4.16), is that no strand starting left of `λ_{j+1}` needs to
pass right of the maximum of the cap; this is achieved with the relation (max1).

We prove this step: `K̃^{λ⁺}_λ` is spanned, as a left `T̃^λ`-module, by the elements
`cap(s, capPos s, v) · z` with `z` in the subalgebra `R_{<capPos s + N}` of diagrams on the
strands left of `λ_{j+1}` at the bottom (`KLRAlgebra.leftSub`), `N` the number of strands at the
maximum (`CupCap.span_canonical`).

## Hypotheses

* The scalars `κ_i` of (max1) are units (`hκ`); they are products of `±1` and of the leading
  coefficients `t_{i'i}` of the polynomials `Q_{i'i}`, which Webster assumes to be units.
* The coefficient module `L` is supported on loadings whose first strand is the red strand `μ`
  and whose last strand is the red strand `μ*` (`hL`: `v · e(w) = 0` for every other loading
  `w`). Webster's `L = L_μ` (Lemma 7.3) has this property: it is a module over the algebra
  `T^{(μ, μ*)}`, in which a black strand left of `μ` is violated, and the kernel of the
  quotient map onto `L_μ` contains every diagram with a black strand right of `μ*`.

## Main results

* `CupCap.capPos`: the canonical position of the maximum.
* `CupCap.capElt`: the element `a · cap(s, n, v) · b` of `K̃^{λ⁺}_λ`.
* `CupCap.span_canonical`: the spanning statement.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MvPolynomial TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Spanning

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Rp" => KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)

/-! ### Multiplication in `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ` -/

theorem Env.mk_mul_mk (a a' : T) (b b' : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    (Env.mk a b * Env.mk a' b' : Env k Q Λ Λc j hj ν ν₀) = Env.mk (a * a') (b' * b) := by
  have h : ((a ⊗ₜ[k] op b : StendhalAlgebra k Q Λ ν ⊗[k]
      (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) * (a' ⊗ₜ[k] op b')) =
      (a * a') ⊗ₜ[k] op (b' * b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, op_mul]
  exact h

theorem Env.mk_add_left (a a' : T) (b : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    (Env.mk (a + a') b : Env k Q Λ Λc j hj ν ν₀) = Env.mk a b + Env.mk a' b :=
  TensorProduct.add_tmul _ _ _

theorem Env.mk_add_right (a : T) (b b' : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    (Env.mk a (b + b') : Env k Q Λ Λc j hj ν ν₀) = Env.mk a b + Env.mk a b' := by
  have h : (a ⊗ₜ[k] op (b + b') : StendhalAlgebra k Q Λ ν ⊗[k]
      (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) =
      a ⊗ₜ[k] op b + a ⊗ₜ[k] op b' := by
    rw [op_add, TensorProduct.tmul_add]
  exact h

theorem Env.mk_zero_right (a : T) :
    (Env.mk a 0 : Env k Q Λ Λc j hj ν ν₀) = 0 := by
  have h : (a ⊗ₜ[k] op 0 : StendhalAlgebra k Q Λ ν ⊗[k]
      (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) = 0 := by
    rw [op_zero, TensorProduct.tmul_zero]
  exact h

theorem Env.mk_smul_right (a : T) (c : k)
    (b : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    (Env.mk a (c • b) : Env k Q Λ Λc j hj ν ν₀) = Env.mk (c • a) b := by
  have h : (a ⊗ₜ[k] op (c • b) : StendhalAlgebra k Q Λ ν ⊗[k]
      (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) = (c • a) ⊗ₜ[k] op b := by
    rw [op_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact h

/-! ### Elements of `K̃^{λ⁺}_λ` -/

/-- The element `a · cap(s, n, v) · b` of `K̃^{λ⁺}_λ`, for `a ∈ T̃^λ` and a diagram `b` of the KLR
algebra of `λ⁺`. -/
def capElt (a : T) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (b : Rp) :
    CapTilde k Q Λ Λc j hj ν ν₀ L :=
  Submodule.Quotient.mk (act a (botMap k Q Λ Λc j hj ν ν₀ b) (gen (s, n) v))

theorem mk_eq_zero_of_isRel {z : FreeCap k Q Λ Λc j hj ν ν₀ L}
    (h : IsRel k Q Λ Λc j hj ν ν₀ L z) :
    (Submodule.Quotient.mk z : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span h)

theorem smul_capElt (a' : T) (b' : Rp) (a : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    (Env.mk a' (botMap k Q Λ Λc j hj ν ν₀ b') • capElt a s n v b) =
      capElt (a' * a) s n v (b * b') := by
  rw [capElt, capElt, ← Submodule.Quotient.mk_smul, act, act, smul_smul, Env.mk_mul_mk, map_mul]

theorem capElt_add_right (a : T) (s) (n : Fin (m + 1)) (v : L) (b b' : Rp) :
    (capElt a s n v (b + b') : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      capElt a s n v b + capElt a s n v b' := by
  rw [capElt, capElt, capElt, act, act, act, map_add, Env.mk_add_right, add_smul,
    Submodule.Quotient.mk_add]

theorem capElt_add_left (a a' : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    (capElt (a + a') s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      capElt a s n v b + capElt a' s n v b := by
  rw [capElt, capElt, capElt, act, act, act, Env.mk_add_left, add_smul,
    Submodule.Quotient.mk_add]

theorem capElt_zero_right (a : T) (s) (n : Fin (m + 1)) (v : L) :
    (capElt a s n v 0 : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  rw [capElt, act, map_zero, Env.mk_zero_right, zero_smul, Submodule.Quotient.mk_zero]

theorem capElt_smul_right (a : T) (s) (n : Fin (m + 1)) (v : L) (c : k) (b : Rp) :
    (capElt a s n v (c • b) : CapTilde k Q Λ Λc j hj ν ν₀ L) = capElt (c • a) s n v b := by
  rw [capElt, capElt, act, act, map_smul, Env.mk_smul_right]

theorem capElt_sum_right {ι : Type*} (a : T) (s) (n : Fin (m + 1)) (v : L) (S : Finset ι)
    (b : ι → Rp) :
    (capElt a s n v (∑ i ∈ S, b i) : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      ∑ i ∈ S, capElt a s n v (b i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [capElt_zero_right]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, capElt_add_right, ih]

theorem capElt_add_mid (a : T) (s) (n : Fin (m + 1)) (v w : L) (b : Rp) :
    (capElt a s n (v + w) b : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      capElt a s n v b + capElt a s n w b := by
  have h := mk_eq_zero_of_isRel (IsRel.add (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
    (hj := hj) (ν := ν) (ν₀ := ν₀) (s, n) v w)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  have := congrArg (fun z => Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b) • z) h
  simp only [smul_add, ← Submodule.Quotient.mk_smul] at this
  exact this

theorem capElt_zero_mid (a : T) (s) (n : Fin (m + 1)) (b : Rp) :
    (capElt a s n (0 : L) b : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  have h := capElt_add_mid (L := L) a s n 0 0 b
  rw [add_zero] at h
  exact left_eq_add.1 h |>.symm ▸ rfl

/-! ### The relations, in terms of `capElt` -/

theorem mk_smul_eq_of_isRel {z₁ z₂ : FreeCap k Q Λ Λc j hj ν ν₀ L}
    (h : IsRel k Q Λ Λc j hj ν ν₀ L (z₁ - z₂)) (r : Env k Q Λ Λc j hj ν ν₀) :
    (Submodule.Quotient.mk (r • z₁) : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      Submodule.Quotient.mk (r • z₂) := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← smul_sub, Submodule.Quotient.mk_smul,
    mk_eq_zero_of_isRel h, smul_zero]

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem act_act (a a' : T) (b b' : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))
    (z : FreeCap k Q Λ Λc j hj ν ν₀ L) :
    Env.mk a b • act a' b' z = act (a * a') (b' * b) z := by
  rw [act, act, smul_smul, Env.mk_mul_mk]

/-- The top of `cap(s, n, v)` is `s`. -/
theorem capElt_idem (a : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    capElt (a * topMap k Q Λ ν (KLRAlgebra.e s)) s n v b = capElt a s n v b := by
  have := mk_smul_eq_of_isRel (IsRel.idem s n v) (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, one_mul] at this
  exact this

/-- Diagrams on the strands at the maximum act on `L`. -/
theorem capElt_box (a : T) (s) (n : Fin (m + 1)) (v : L) (x : Rc) (b : Rp) :
    capElt a s n (op (cupMap k Q Λc ν₀ x) • v) b =
      capElt a s n v (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) x * b) := by
  have := mk_smul_eq_of_isRel (IsRel.box s n v x) (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, mul_one, ← map_mul] at this
  exact this

/-- A dot on the top passes below the cap. -/
theorem capElt_dot (a : T) (s) (n : Fin (m + 1)) (v : L) (a' : Fin m) (b : Rp) :
    capElt (a * topMap k Q Λ ν (KLRAlgebra.x a')) s n v b =
      capElt a s n v (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a') * b) := by
  have := mk_smul_eq_of_isRel (IsRel.dot s n v a') (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, act_act, one_mul, mul_one, ← map_mul] at this
  exact this

/-- A crossing of the top on one side of the maximum passes below the cap. -/
theorem capElt_cross (a : T) (s) (n : Fin (m + 1)) (v : L) (p : ℕ)
    (hp : p + 1 < n.val ∨ n.val ≤ p) (b : Rp) :
    capElt (a * topMap k Q Λ ν (KLRAlgebra.ψ p)) s n v b =
      capElt a (sadj m p • s) n v (KLRAlgebra.ψ (crossPos n N p) * b) := by
  have := mk_smul_eq_of_isRel (IsRel.cross s n v p hp) (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, act_act, one_mul, mul_one, ← map_mul] at this
  exact this

/-- **(max1)**, in terms of `capElt`. -/
theorem capElt_over (a : T) (s) (n : Fin (m + 1)) (v : L) (i : I) (hn : 0 < n.val)
    (hi : s.lbl ⟨n - 1, by omega⟩ = .inl i) (b : Rp) :
    capElt a s n v (underRight N (n - 1) * b) =
      capElt (a * algebraMap k _ (cupScalar Q ν₀ i)) s ⟨n - 1, by omega⟩ v b := by
  have := mk_smul_eq_of_isRel (IsRel.over s n v i hn hi) (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, act_act, one_mul, mul_one, ← map_mul] at this
  exact this

/-- **(max2)**, in terms of `capElt`. -/
theorem capElt_under (a : T) (s) (n : Fin (m + 1)) (v : L) (i : I) (hn : n.val < m)
    (hi : s.lbl ⟨n, hn⟩ = .inl i) (b : Rp) :
    capElt a s n v (underLeft N n * b) = capElt a s ⟨n + 1, by omega⟩ v b := by
  have := mk_smul_eq_of_isRel (IsRel.under s n v i hn hi) (Env.mk a (botMap k Q Λ Λc j hj ν ν₀ b))
  rw [act_act, mul_one, ← map_mul] at this
  exact this

/-! ### Vanishing by the order of the red strands -/

section Projection

variable {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- An idempotent whose red strands are out of order vanishes in `T̃`. -/
theorem orderProjection_e_of_not {i : Seq (stendhalWeight ℓ' ν')} (h : ¬ IsRedOrdered i) :
    orderProjection Q Λ' ν' (StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (KLRAlgebra.e i)) = 0 := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e i * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν' = 0
  rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  simp [h]

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- Two red strands do not cross. -/
theorem ofKLR_ψ_mul_e_of_red (p : ℕ) (hp : p + 1 < Multiset.card (stendhalWeight ℓ' ν'))
    (i : Seq (stendhalWeight ℓ' ν')) (h₁ : (i.lbl ⟨p, Nat.lt_of_succ_lt hp⟩).isRight)
    (h₂ : (i.lbl ⟨p + 1, hp⟩).isRight) :
    StendhalAlgebraAllOrders.ofKLR k Q Λ' ν' (KLRAlgebra.ψ p * KLRAlgebra.e i) = 0 := by
  rw [map_mul]
  exact StendhalAlgebraAllOrders.ψ_mul_e_of_red p hp i h₁ h₂

end Projection

theorem capElt_zero_left (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    (capElt 0 s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  have h : (Env.mk 0 (botMap k Q Λ Λc j hj ν ν₀ b) : Env k Q Λ Λc j hj ν ν₀) = 0 :=
    TensorProduct.zero_tmul _ _
  rw [capElt, act, h, zero_smul, Submodule.Quotient.mk_zero]

/-- Generators whose top loading has its red strands out of order vanish. -/
theorem capElt_eq_zero_of_top (a : T) {s : Seq (stendhalWeight ℓ ν)} (hs : ¬ IsRedOrdered s)
    (n : Fin (m + 1)) (v : L) (b : Rp) :
    (capElt a s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  rw [← capElt_idem, topMap, AlgHom.comp_apply, orderProjection_e_of_not hs, mul_zero,
    capElt_zero_left]

/-- The bottom of `cap(s, n, v)` is one of the loadings `insertSeq s n w`. -/
theorem capElt_eq_eSum_mul (a : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    (capElt a s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      capElt a s n v (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n
        (Nat.lt_succ_iff.1 n.2)) * b) := by
  have := capElt_box a s n v 1 b
  rw [map_one, op_one, one_smul] at this
  rw [this, insertMap, map_one, Corner.val_one]

/-- Generators all of whose bottom loadings have their red strands out of order vanish. -/
theorem capElt_eq_zero_of_bottom (a : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp)
    (h : ∀ w, ¬ IsRedOrdered (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s n
      (Nat.lt_succ_iff.1 n.2) w)) :
    (capElt a s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  have hE : botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj)
      (ν₀ := ν₀) s n (Nat.lt_succ_iff.1 n.2))) = 0 := by
    rw [KLRAlgebra.eSum, map_sum]
    refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 ht
    rw [botMap, AlgHom.comp_apply, orderProjection_e_of_not (h w)]
  rw [capElt_eq_eSum_mul, capElt, map_mul, hE, zero_mul, ← map_zero (botMap k Q Λ Λc j hj ν ν₀),
    ← capElt, capElt_zero_right]

/-! ### Positions in the bottom loading -/

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem exists_lbl_eq_of_mem {J : Type*} {μ : Multiset J} (t : Seq μ) {c : J} (hc : c ∈ μ) :
    ∃ b, t.lbl b = c := by
  rw [← t.2] at hc
  obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hc
  exact ⟨b, hb⟩

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem insertSeq_lbl_win (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {c : Fin M}
    (b : Fin (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour j hj))))
    (hc : c.val = n + b.val) : (insertSeq s n hn t).lbl c = t.lbl b := by
  have : c = Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inr b)) :=
    Fin.ext (by simp [hc])
  rw [this, insertSeq_lbl_new]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem insertSeq_lbl_lt (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {c : Fin M} (a : Fin m)
    (ha : a.val < n) (hc : c.val = a.val) :
    (insertSeq s n hn t).lbl c = oldColour j hj (s.lbl a) := by
  have : c = Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl a)) :=
    Fin.ext (by simp [hc, ha])
  rw [this, insertSeq_lbl_old]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem insertSeq_lbl_ge (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {c : Fin M} (a : Fin m)
    (ha : n ≤ a.val) (hc : c.val = a.val + N) :
    (insertSeq s n hn t).lbl c = oldColour j hj (s.lbl a) := by
  have : c = Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl a)) :=
    Fin.ext (by simp [hc, show ¬ a.val < n by omega])
  rw [this, insertSeq_lbl_old]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- Each leg of the cap is somewhere in the window of a bottom loading. -/
theorem exists_win_cupRed (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (r : Fin 2) :
    ∃ b, t.lbl b = .inr (cupRed (ℓ := ℓ) j hj r) := by
  refine exists_lbl_eq_of_mem t (Multiset.mem_map.2 ⟨.inr r, ?_, rfl⟩)
  fin_cases r <;> simp [stendhalWeight]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem cupRed_val (r : Fin 2) : (cupRed (ℓ := ℓ) j hj r).val = j + r.val := rfl

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem oldRed_val_of_lt {r : Fin ℓ} (h : r.val < j) : (oldRed j hj r).val = r.val := by
  simp [oldRed, h]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem oldRed_val_of_ge {r : Fin ℓ} (h : j ≤ r.val) : (oldRed j hj r).val = r.val + 2 := by
  simp [oldRed, show ¬ r.val < j by omega]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- A cap right of an old red strand `λ_r` with `r ≥ j` (zero-indexed) gives a loading whose red
strands are out of order. -/
theorem not_isRedOrdered_of_red_left (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (a : Fin m) (ha : a.val < n)
    {r : Fin ℓ} (hr : s.lbl a = .inr r) (hrj : j ≤ r.val) :
    ¬ IsRedOrdered (insertSeq s n hn t) := by
  intro h
  obtain ⟨b, hb⟩ := exists_win_cupRed (ℓ := ℓ) (hj := hj) t 0
  have hbN := b.2
  have hcard := card_plus j hj ν ν₀
  have h1 := insertSeq_lbl_lt s hn t (c := ⟨a.val, by omega⟩) a ha rfl
  have h2 := insertSeq_lbl_win s hn t (c := ⟨n + b.val, by omega⟩) b rfl
  rw [hr] at h1
  rw [hb] at h2
  have := h ⟨a.val, by omega⟩ ⟨n + b.val, by omega⟩ _ _ (Fin.mk_lt_mk.2 (by omega)) h1 h2
  rw [Fin.lt_def, oldRed_val_of_ge hrj, cupRed_val] at this
  simp at this
  omega

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- A cap left of an old red strand `λ_r` with `r < j` (zero-indexed) gives a loading whose red
strands are out of order. -/
theorem not_isRedOrdered_of_red_right (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (a : Fin m) (ha : n ≤ a.val)
    {r : Fin ℓ} (hr : s.lbl a = .inr r) (hrj : r.val < j) :
    ¬ IsRedOrdered (insertSeq s n hn t) := by
  intro h
  obtain ⟨b, hb⟩ := exists_win_cupRed (ℓ := ℓ) (hj := hj) t 0
  have hbN := b.2
  have hcard := card_plus j hj ν ν₀
  have hN : Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) (ℓ := ℓ) j hj)) = N :=
    Multiset.card_map _ _
  have h1 := insertSeq_lbl_ge s hn t (c := ⟨a.val + N, by omega⟩) a ha rfl
  have h2 := insertSeq_lbl_win s hn t (c := ⟨n + b.val, by omega⟩) b rfl
  rw [hr] at h1
  rw [hb] at h2
  have := h ⟨n + b.val, by omega⟩ ⟨a.val + N, by omega⟩ _ _ (Fin.mk_lt_mk.2 (by omega)) h2 h1
  rw [Fin.lt_def, oldRed_val_of_lt hrj, cupRed_val] at this
  simp at this
  omega

/-! ### The canonical position of the maximum -/

variable (ℓ j) in
/-- **The canonical position of the maximum** of the cap for the top loading `s`: the position
of the red strand `λ_{j+1}` (zero-indexed `j`), or the right end if `j = ℓ`. -/
def capPos (s : Seq (stendhalWeight ℓ ν)) : ℕ :=
  if h : j < ℓ then (Classical.choose (exists_lbl_eq_inr s ⟨j, h⟩)).val else m

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capPos_lt {s : Seq (stendhalWeight ℓ ν)} (h : j < ℓ) : capPos ℓ j s < m := by
  simp only [capPos, h, ↓reduceDIte]; exact Fin.is_lt _

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capPos_le (s : Seq (stendhalWeight ℓ ν)) : capPos ℓ j s ≤ m := by
  by_cases h : j < ℓ
  · exact (capPos_lt h).le
  · simp only [capPos, h, ↓reduceDIte, le_refl]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capPos_of_not {s : Seq (stendhalWeight ℓ ν)} (h : ¬ j < ℓ) : capPos ℓ j s = m := by
  simp only [capPos, h, ↓reduceDIte]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem lbl_capPos {s : Seq (stendhalWeight ℓ ν)} (h : j < ℓ) :
    s.lbl ⟨capPos ℓ j s, capPos_lt h⟩ = .inr ⟨j, h⟩ := by
  have hc : capPos ℓ j s = (Classical.choose (exists_lbl_eq_inr s ⟨j, h⟩)).val := by
    simp only [capPos, h, ↓reduceDIte]
  have := Classical.choose_spec (exists_lbl_eq_inr s ⟨j, h⟩)
  rwa [show (⟨capPos ℓ j s, capPos_lt h⟩ : Fin m) = Classical.choose _ from Fin.ext hc]

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem capPos_eq {s : Seq (stendhalWeight ℓ ν)} (h : j < ℓ) {c : Fin m}
    (hc : s.lbl c = .inr ⟨j, h⟩) : capPos ℓ j s = c.val :=
  congrArg Fin.val (lbl_eq_inr_unique (lbl_capPos h) hc)

/-! ### The span of the canonical generators -/

local notation "Z" => KLRAlgebra.leftSub (stendhalQ Q (plusLabels Λ Λc j hj))
  (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (k Q Λ Λc j hj ν ν₀ L) in
/-- **The canonical generators** `a · cap(s, capPos s, v) · z`, with `z` a diagram on the strands
left of `λ_{j+1}` at the bottom: `z ∈ R_{<capPos s + N}`. -/
def canonicalSet : Set (CapTilde k Q Λ Λc j hj ν ν₀ L) :=
  {w | ∃ (a : T) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (z : Rp),
    n.val = capPos ℓ j s ∧ z ∈ Z (n.val + N) ∧ w = capElt a s n v z}

variable (k Q Λ Λc j hj ν ν₀ L) in
/-- The additive subgroup generated by the canonical generators; it is a left `T̃^λ`-submodule
(`canonicalSpan_smul_left`). -/
def canonicalSpan : AddSubgroup (CapTilde k Q Λ Λc j hj ν ν₀ L) :=
  AddSubgroup.closure (canonicalSet k Q Λ Λc j hj ν ν₀ L)

theorem capElt_mem_canonicalSpan {a : T} {s : Seq (stendhalWeight ℓ ν)} {n : Fin (m + 1)}
    (hn : n.val = capPos ℓ j s) (v : L) {z : Rp} (hz : z ∈ Z (n.val + N)) :
    capElt a s n v z ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L :=
  AddSubgroup.subset_closure ⟨a, s, n, v, z, hn, hz, rfl⟩

/-- **Reduction to the canonical position by (max1).** A generator whose maximum lies left of the
canonical position, followed by a diagram on the strands left of the cap, lies in the span of the
canonical generators. -/
theorem capElt_mem_of_le (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (s : Seq (stendhalWeight ℓ ν))
    (v : L) : ∀ (d : ℕ) (a : T) (n : Fin (m + 1)), capPos ℓ j s = n.val + d →
      ∀ z ∈ Z (n.val + N), capElt a s n v z ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L := by
  intro d
  induction d with
  | zero => intro a n hn z hz; exact capElt_mem_canonicalSpan (by omega) v hz
  | succ d ih =>
    intro a n hn z hz
    have hnm : n.val < m := by have := capPos_le (j := j) s; omega
    rcases hs : s.lbl ⟨n.val, hnm⟩ with i | r
    · -- a black strand right of the maximum: pull it under the cap with (max1)
      obtain ⟨u, hu⟩ := hκ i
      have h1 : n.val + 1 < m + 1 := by omega
      have key := capElt_over (a * algebraMap k _ (↑u⁻¹ : k)) s ⟨n.val + 1, h1⟩ v i
        (by simp) (by simpa using hs) z
      simp only [Nat.add_sub_cancel, ← hu, mul_assoc, ← map_mul, Units.inv_mul, map_one,
        mul_one] at key
      rw [show (⟨n.val, _⟩ : Fin (m + 1)) = n from Fin.ext rfl] at key
      rw [← key]
      refine ih _ ⟨n.val + 1, h1⟩ (show capPos ℓ j s = n.val + 1 + d by omega) _ ?_
      refine mul_mem (KLRAlgebra.ψw_mem_leftSub fun p hp => ?_)
        (KLRAlgebra.leftSub_mono (show n.val + N ≤ n.val + 1 + N by omega) hz)
      rw [List.mem_range'_1] at hp
      show p + 1 < n.val + 1 + N
      omega
    · -- a red strand right of the maximum: the generator vanishes
      by_cases hord : IsRedOrdered s
      · have hrj : r.val < j := by
          by_cases hjl : j < ℓ
          · have hne : r ≠ ⟨j, hjl⟩ := by
              rintro rfl
              have := capPos_eq hjl hs
              rw [Fin.val_mk] at this
              omega
            have hpos := lbl_capPos (s := s) hjl
            have := hord ⟨n.val, hnm⟩ ⟨capPos ℓ j s, capPos_lt hjl⟩ r ⟨j, hjl⟩
              (Fin.mk_lt_mk.2 (by omega)) hs hpos
            exact this
          · have := r.2; omega
        rw [capElt_eq_zero_of_bottom _ _ _ _ _ fun w =>
          not_isRedOrdered_of_red_right s _ w ⟨n.val, hnm⟩ le_rfl hs hrj]
        exact zero_mem _
      · rw [capElt_eq_zero_of_top _ hord]
        exact zero_mem _

/-- Every generator whose maximum is left of the canonical position lies in the span of the
canonical generators. -/
theorem capElt_mem_canonicalSpan_of_le (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (a : T)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (hn : n.val ≤ capPos ℓ j s) (v : L)
    {z : Rp} (hz : z ∈ Z (n.val + N)) : capElt a s n v z ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L :=
  capElt_mem_of_le hκ s v (capPos ℓ j s - n.val) a n (by omega) z hz

/-! ### The strands at the maximum -/

theorem two_le_card_stendhalWeight {I' : Type*} (ν₁ : Multiset I') :
    2 ≤ Multiset.card (stendhalWeight 2 ν₁) := by
  simp [stendhalWeight]

/-- A loading of the strands at the maximum whose first strand is `μ` and whose last strand is
`μ*`. -/
def IsCapGood {I' : Type*} (ν₁ : Multiset I') (w : Seq (stendhalWeight 2 ν₁)) : Prop :=
  w.lbl ⟨0, lt_of_lt_of_le (by norm_num) (two_le_card_stendhalWeight ν₁)⟩ = .inr 0 ∧
    w.lbl ⟨Multiset.card (stendhalWeight 2 ν₁) - 1,
      Nat.sub_lt (lt_of_lt_of_le (by norm_num) (two_le_card_stendhalWeight ν₁)) one_pos⟩ = .inr 1

instance {I' : Type*} [DecidableEq I'] (ν₁ : Multiset I') (w : Seq (stendhalWeight 2 ν₁)) :
    Decidable (IsCapGood ν₁ w) := by
  unfold IsCapGood; infer_instance

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem insertMap_e (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (w : Seq (stendhalWeight 2 ν₀)) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn (KLRAlgebra.e w) =
      KLRAlgebra.e (insertSeq s n hn (Seq.map (cupColour j hj) w)) := by
  show (((insertEmb s n hn).hom (stendhalQ Q (plusLabels Λ Λc j hj)))
    (KLRAlgebra.relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc)
      (KLRAlgebra.e w))).val = _
  rw [KLRAlgebra.relabelHom_e, KLRAlgebra.BlockEmb.hom_e, KLRAlgebra.BlockEmb.val_gE]
  simp [KLRAlgebra.eSum, insertEmb, cupRelabel]

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem insertMap_ψ (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < N) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn (KLRAlgebra.ψ p) =
      KLRAlgebra.ψ (n + p) * KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) := by
  show (((insertEmb s n hn).hom (stendhalQ Q (plusLabels Λ Λc j hj)))
    (KLRAlgebra.relabelHom (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc)
      (KLRAlgebra.ψ p))).val = _
  rw [KLRAlgebra.relabelHom_ψ, KLRAlgebra.BlockEmb.hom_ψ,
    KLRAlgebra.BlockEmb.val_gψ _ (by simpa using hp)]
  rfl

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem eSum_insertSet_mul_ψ (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < N) :
    (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) *
      KLRAlgebra.ψ (n + p) : Rp) =
      KLRAlgebra.ψ (n + p) * KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) :=
  ((insertEmb s n hn).ψ_mul_E (Q := stendhalQ Q (plusLabels Λ Λc j hj)) (j := p)
    (by simpa using hp)).symm

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- Crossings among the strands at the maximum, placed in the window. -/
theorem insertMap_ψw (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (ρ : List ℕ)
    (hρ : ∀ p ∈ ρ, p + 1 < N) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn (KLRAlgebra.ψw ρ) =
      KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) *
        KLRAlgebra.ψw (ρ.map (n + ·)) := by
  induction ρ with
  | nil =>
    rw [KLRAlgebra.ψw_nil, insertMap, map_one, Corner.val_one, List.map_nil, KLRAlgebra.ψw_nil,
      mul_one]
  | cons p ρ ih =>
    rw [KLRAlgebra.ψw_cons, insertMap_mul, insertMap_ψ s hn (hρ p (by simp)),
      ih fun q hq => hρ q (by simp [hq]), List.map_cons, KLRAlgebra.ψw_cons,
      ← mul_assoc, mul_assoc (KLRAlgebra.ψ (n + p)),
      (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq,
      ← eSum_insertSet_mul_ψ s hn (hρ p (by simp)), mul_assoc]

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- The crossings `s_q s_{q+1} ⋯ s_{q+l-1}` take the position `q + l` to `q`. -/
theorem wordProd_range'_apply {K : ℕ} (q l : ℕ) (h : q + l < K) :
    wordProd K (List.range' q l) ⟨q + l, h⟩ = ⟨q, Nat.lt_of_le_of_lt (Nat.le_add_right q l) h⟩ := by
  induction l generalizing q with
  | zero => simp [wordProd]
  | succ l ih =>
    rw [List.range'_succ, show wordProd K (q :: List.range' (q + 1) l) =
        sadj K q * wordProd K (List.range' (q + 1) l) by simp [wordProd], Equiv.Perm.mul_apply,
      show (⟨q + (l + 1), h⟩ : Fin K) = ⟨q + 1 + l, by omega⟩ from Fin.ext (by simp; omega),
      ih (q + 1) (by omega)]
    exact sadj_apply_right (by omega)

/-- **Only `μ` and `μ*` leave the box at the ends.** If `L` is supported on loadings whose last
strand is `μ*`, a strand at the maximum other than the last one cannot be pulled to the right of
all the others. -/
theorem smul_window_eq_zero
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (v : L) {q : ℕ} (hq : q + 1 < N) :
    op (cupMap k Q Λc ν₀ (KLRAlgebra.ψw (List.range' q (N - 1 - q)))) • v = 0 := by
  classical
  have hv : v = ∑ w : Seq (stendhalWeight 2 ν₀), op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v := by
    rw [← Finset.sum_smul, ← Finset.op_sum, ← map_sum, KLRAlgebra.sum_e, map_one, op_one,
      one_smul]
  rw [hv, Finset.smul_sum]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : IsCapGood ν₀ w
  · rw [smul_smul, ← op_mul, ← map_mul, KLRAlgebra.e_mul_ψw, map_mul, op_mul, mul_smul]
    refine hL _ _ fun hw' => ?_
    have hlast := hw'.2
    rw [Seq.lbl, Seq.smul_apply, Equiv.Perm.inv_def, Equiv.symm_symm,
      show (⟨N - 1, _⟩ : Fin N) = ⟨q + (N - 1 - q), by omega⟩ from Fin.ext (by simp; omega),
      wordProd_range'_apply] at hlast
    have := lbl_eq_inr_unique hlast hw.2
    rw [Fin.ext_iff] at this
    simp at this
    omega
  · rw [hL w v hw, smul_zero]

theorem capElt_sum_mid {ι : Type*} (a : T) (s) (n : Fin (m + 1)) (S : Finset ι) (v : ι → L)
    (b : Rp) :
    (capElt a s n (∑ i ∈ S, v i) b : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      ∑ i ∈ S, capElt a s n (v i) b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [capElt_zero_mid]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, capElt_add_mid, ih]

/-- Only the bottom loadings with `μ` and `μ*` at the ends of the window contribute. -/
theorem capElt_eq_sum_good
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (a : T) (s) (n : Fin (m + 1)) (v : L) (b : Rp) :
    (capElt a s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      ∑ w ∈ Finset.univ.filter (IsCapGood ν₀), capElt a s n v
        (KLRAlgebra.e (insertSeq s n (Nat.lt_succ_iff.1 n.2) (Seq.map (cupColour j hj) w)) * b) := by
  classical
  have hv : v = ∑ w : Seq (stendhalWeight 2 ν₀), op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v := by
    rw [← Finset.sum_smul, ← Finset.op_sum, ← map_sum, KLRAlgebra.sum_e, map_one, op_one,
      one_smul]
  conv_lhs => rw [hv]
  rw [capElt_sum_mid, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs with hw
  · rw [capElt_box, insertMap_e]
  · rw [hL w v hw, capElt_zero_mid]

/-! ### Vanishing of red crossings below the cap -/

theorem capElt_eq_zero_of_botMap (a : T) (s) (n : Fin (m + 1)) (v : L) {b : Rp}
    (h : botMap k Q Λ Λc j hj ν ν₀ b = 0) :
    (capElt a s n v b : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  have h0 : (capElt a s n v 0 : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := capElt_zero_right a s n v
  rw [capElt, map_zero] at h0
  rw [capElt, h]
  exact h0

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
/-- Two red strands do not cross in `T̃^{λ⁺}`. -/
theorem botMap_e_mul_ψ_of_red (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) {p : ℕ}
    (hp : p + 1 < M) (h₁ : (t.lbl ⟨p, Nat.lt_of_succ_lt hp⟩).isRight)
    (h₂ : (t.lbl ⟨p + 1, hp⟩).isRight) :
    botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e t * KLRAlgebra.ψ p) = 0 := by
  have he : (KLRAlgebra.e t * KLRAlgebra.ψ p : Rp) =
      KLRAlgebra.ψ p * KLRAlgebra.e (sadj M p • t) := by
    rw [KLRAlgebra.ψ_mul_e, KLRAlgebra.sadj_smul_smul]
  have h₁' : ((sadj M p • t).lbl ⟨p, Nat.lt_of_succ_lt hp⟩).isRight := by
    rw [KLRAlgebra.lbl_sadj_left hp]; exact h₂
  have h₂' : ((sadj M p • t).lbl ⟨p + 1, hp⟩).isRight := by
    rw [KLRAlgebra.lbl_sadj_right hp]; exact h₁
  rw [he, botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red p hp _ h₁' h₂', map_zero]

/-! ### Closure under the bottom action -/

variable (k Q Λ Λc j hj ν ν₀ L) in
/-- Right multiplication by `b` preserves the span of the canonical generators. -/
def BotClosed (b : Rp) : Prop :=
  ∀ w ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L,
    Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ b) • w ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L

theorem botClosed_of_gen {b : Rp}
    (h : ∀ (a : T) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) (z : Rp),
      n.val = capPos ℓ j s → z ∈ Z (n.val + N) →
        capElt a s n v (z * b) ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L) :
    BotClosed k Q Λ Λc j hj ν ν₀ L b := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, s, n, v, z, hn, hz, rfl⟩ := hw
    rw [smul_capElt, one_mul]
    exact h a s n v z hn hz
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h₁ => rw [smul_neg]; exact neg_mem h₁

theorem BotClosed.mul {b b' : Rp} (h : BotClosed k Q Λ Λc j hj ν ν₀ L b)
    (h' : BotClosed k Q Λ Λc j hj ν ν₀ L b') : BotClosed k Q Λ Λc j hj ν ν₀ L (b * b') := by
  intro w hw
  have he : (Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (b * b')) : Env k Q Λ Λc j hj ν ν₀) =
      Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ b') * Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ b) := by
    rw [Env.mk_mul_mk, one_mul, map_mul]
  rw [he, mul_smul]
  exact h' _ (h w hw)

theorem BotClosed.add {b b' : Rp} (h : BotClosed k Q Λ Λc j hj ν ν₀ L b)
    (h' : BotClosed k Q Λ Λc j hj ν ν₀ L b') : BotClosed k Q Λ Λc j hj ν ν₀ L (b + b') := by
  intro w hw
  rw [map_add, Env.mk_add_right, add_smul]
  exact add_mem (h w hw) (h' w hw)

theorem botClosed_one : BotClosed k Q Λ Λc j hj ν ν₀ L (1 : Rp) :=
  botClosed_of_gen fun _ _ _ v _ hn hz => by rw [mul_one]; exact capElt_mem_canonicalSpan hn v hz

theorem BotClosed.pow {b : Rp} (h : BotClosed k Q Λ Λc j hj ν ν₀ L b) (d : ℕ) :
    BotClosed k Q Λ Λc j hj ν ν₀ L (b ^ d) := by
  induction d with
  | zero => rw [pow_zero]; exact botClosed_one
  | succ d ih => rw [pow_succ]; exact ih.mul h

theorem botClosed_algebraMap (r : k) : BotClosed k Q Λ Λc j hj ν ν₀ L (algebraMap k Rp r) :=
  botClosed_of_gen fun a s n v z hn hz => by
    rw [← Algebra.commutes, ← Algebra.smul_def, capElt_smul_right]
    exact capElt_mem_canonicalSpan hn v hz

theorem botClosed_e (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :
    BotClosed k Q Λ Λc j hj ν ν₀ L (KLRAlgebra.e t) :=
  botClosed_of_gen fun _ _ _ v _ hn hz =>
    capElt_mem_canonicalSpan hn v (Subalgebra.mul_mem _ hz (KLRAlgebra.e_mem_leftSub _ t))

omit [DecidableEq I] [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem dotPos_val_of_le (n : Fin (m + 1)) (a : Fin m) (ha : n.val ≤ a.val) :
    (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a).val = a.val + N := by
  simp [dotPos, show ¬ a.val < n.val by omega]

/-- A dot below the canonical generators: on a strand left of the box it stays below, on a strand
right of it, it slides up to the top. -/
theorem botClosed_x (c : Fin M) : BotClosed k Q Λ Λc j hj ν ν₀ L (KLRAlgebra.x c) := by
  refine botClosed_of_gen fun a s n v z hn hz => ?_
  by_cases hc : c.val < n.val + N
  · exact capElt_mem_canonicalSpan hn v (Subalgebra.mul_mem _ hz (KLRAlgebra.x_mem_leftSub c hc))
  · rw [(KLRAlgebra.commute_x_of_le hz c (by omega)).eq]
    have hM : M = m + N := by rw [card_plus j hj ν ν₀, Multiset.card_map]
    have hcm : c.val - N < m := by have := c.isLt; omega
    rw [show c = dotPos (j := j) (hj := hj) (ν₀ := ν₀) n ⟨c.val - N, hcm⟩ from
      Fin.ext (by
        rw [dotPos_val_of_le _ _ (by show n.val ≤ c.val - N; omega)]
        show c.val = c.val - N + N
        omega),
      ← capElt_dot]
    exact capElt_mem_canonicalSpan hn v hz

omit [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L] in
theorem le_capPos_sadj {s : Seq (stendhalWeight ℓ ν)} {p : ℕ} (hp : capPos ℓ j s ≤ p) :
    capPos ℓ j s ≤ capPos ℓ j (sadj m p • s) := by
  by_cases hjl : j < ℓ
  · have hc := lbl_capPos (s := s) hjl
    have h : (sadj m p • s).lbl (sadj m p ⟨capPos ℓ j s, capPos_lt hjl⟩) = .inr ⟨j, hjl⟩ := by
      simp only [Seq.lbl, KLRAlgebra.sadj_smul_apply, sadj_sadj_apply]
      exact hc
    rw [capPos_eq hjl h, sadj_val]
    show capPos ℓ j s ≤ if p + 1 < m then swapNat p (capPos ℓ j s) else capPos ℓ j s
    split_ifs
    · rcases swapNat_cases p (capPos ℓ j s) with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ <;> omega
    · exact le_rfl
  · rw [capPos_of_not hjl, capPos_of_not hjl]

/-- A crossing below the canonical generators, other than the one between the last strand of the
box and the strand to its right. -/
theorem capElt_mul_ψ_mem_of_ne (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (a : T)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) {z : Rp}
    (hn : n.val = capPos ℓ j s) (hz : z ∈ Z (n.val + N)) {p : ℕ} (hp : p + 1 ≠ n.val + N) :
    capElt a s n v (z * KLRAlgebra.ψ p) ∈ canonicalSpan k Q Λ Λc j hj ν ν₀ L := by
  by_cases hp1 : p + 1 < n.val + N
  · exact capElt_mem_canonicalSpan hn v (Subalgebra.mul_mem _ hz (KLRAlgebra.ψ_mem_leftSub hp1))
  obtain ⟨z', hz', he⟩ := KLRAlgebra.exists_mul_ψ_eq hz p (by omega)
  rw [he]
  have hc : crossPos n.val N (p - N) = p := by
    simp only [crossPos, show ¬ p - N < n.val by omega, ↓reduceIte]; omega
  have h := capElt_cross a (sadj m (p - N) • s) n v (p - N) (Or.inr (by omega)) z'
  rw [KLRAlgebra.sadj_smul_smul, hc] at h
  rw [← h]
  exact capElt_mem_canonicalSpan_of_le hκ _ _ n (by rw [hn]; exact le_capPos_sadj (by omega)) v hz'

/-- Crossings left of the maximum below a generator slide up to the top. -/
theorem capElt_ψw_mul (n : Fin (m + 1)) (v : L) (b : Rp) (ρ : List ℕ)
    (hρ : ∀ p ∈ ρ, p + 1 < n.val) (a : T) (s : Seq (stendhalWeight ℓ ν)) :
    ∃ (a' : T) (s' : Seq (stendhalWeight ℓ ν)), (∀ c : Fin m, n.val ≤ c.val → s'.lbl c = s.lbl c) ∧
      capElt a s n v (KLRAlgebra.ψw ρ * b) = capElt a' s' n v b := by
  induction ρ generalizing a s with
  | nil => exact ⟨a, s, fun _ _ => rfl, by rw [KLRAlgebra.ψw_nil, one_mul]⟩
  | cons p ρ ih =>
    have hp := hρ p (by simp)
    obtain ⟨a', s', hs', he⟩ := ih (fun q hq => hρ q (by simp [hq]))
      (a * topMap k Q Λ ν (KLRAlgebra.ψ p)) (sadj m p • s)
    refine ⟨a', s', fun c hc => ?_, ?_⟩
    · rw [hs' c hc, KLRAlgebra.lbl_sadj_of_ne s c (by omega) (by omega)]
    · have hcr : crossPos n.val N p = p := by simp [crossPos, show p < n.val by omega]
      have h := capElt_cross a (sadj m p • s) n v p (Or.inl hp) (KLRAlgebra.ψw ρ * b)
      rw [KLRAlgebra.sadj_smul_smul, hcr] at h
      rw [KLRAlgebra.ψw_cons, mul_assoc, ← h, he]

end Spanning

end Categorification.Stendhal.CupCap
