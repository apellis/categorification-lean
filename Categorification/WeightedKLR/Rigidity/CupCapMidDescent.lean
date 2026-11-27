/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapEndModel
import Categorification.WeightedKLR.RedStrands.StandardModule

/-!
# Diagrams at the maximum of a cap at an arbitrary position

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17, for the cap inserted after the red strand
`λ_j` (any `j ≤ ℓ`). Below the cap generators at a loading `s` of `λ`, the maximum is moved to the
right end of the `j`-th black block, just left of the red strand `λ_{j+1}` (at the right end of `s`
when `j = ℓ`); this is the position `CupCap.midPos s`. Placing a diagram of `R((μ, μ*))` on the
window at `midPos s` for every loading `s` (`CupCap.midMapKLR`) is a nonunital map of KLR
algebras, because a loading of `λ⁺` determines the loading of `λ` and the window: the window ends
just before `λ_{j+1}`. It kills the dots on red strands and the crossings of two red strands, so it
descends to `T̃^{(μ,μ*)} → T̃^{λ⁺}` (`CupCap.midStendhal`). For `j = ℓ` it is the map of
`CupCap.endStendhal`.

## Main definitions

* `CupCap.midPos`: the position of the maximum, just before the red strand `λ_{j+1}`.
* `CupCap.midSet`: the bottom loadings of the cap generators at `midPos`.
* `CupCap.midMapKLR`: the diagrams at the maximum, on the window at `midPos`.
* `CupCap.midStendhal`: the same on Stendhal algebras.
* `CupCap.MidModel`: the induced module `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` along it, the right module
  underlying the model of `K̃^{λ⁺}_λ`.

## Main results

* `CupCap.disjoint_insertSet_midPos`: the windows of different loadings are disjoint.
* `CupCap.midMapKLR_mul`: the map is multiplicative.
* `CupCap.redRelations_midBot`: it kills the red dots and the red crossings.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section Position

variable {I : Type*} {ℓ : ℕ} (j : ℕ) {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- **The position of the maximum** below the cap generators at `s`: the position of the red
strand `λ_{j+1}`, at the right end of the `j`-th black block (the right end `m` when `j = ℓ`). -/
def midPos (s : Seq (stendhalWeight ℓ ν)) : ℕ :=
  if h : j < ℓ then ((exists_lbl_eq_inr s ⟨j, h⟩).choose).val else m

theorem midPos_le (s : Seq (stendhalWeight ℓ ν)) : midPos j s ≤ m := by
  unfold midPos
  split_ifs
  · exact (Fin.is_lt _).le
  · exact le_rfl

theorem midPos_of_lt (s : Seq (stendhalWeight ℓ ν)) (h : j < ℓ) :
    ∃ a : Fin m, a.val = midPos j s ∧ s.lbl a = .inr ⟨j, h⟩ := by
  refine ⟨(exists_lbl_eq_inr s ⟨j, h⟩).choose, ?_, (exists_lbl_eq_inr s ⟨j, h⟩).choose_spec⟩
  simp [midPos, h]

theorem midPos_of_not_lt (s : Seq (stendhalWeight ℓ ν)) (h : ¬ j < ℓ) : midPos j s = m := by
  simp [midPos, h]

end Position

section Windows

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

omit [DecidableEq I] in
/-- Equal bottom loadings at the same position come from the same loading of `λ`. -/
theorem eq_of_insertSeq_eq {s s' : Seq (stendhalWeight ℓ ν)} {n : ℕ} (hn : n ≤ m)
    {t t' : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))}
    (h : insertSeq s n hn t = insertSeq s' n hn t') : s = s' := by
  apply Subtype.ext
  funext a
  have := congrArg (fun u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
    u.lbl (Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl a)))) h
  simp only [insertSeq_lbl_old] at this
  exact oldColour_injective j hj this

omit [DecidableEq I] in
theorem eq_of_insertSeq_eq' {s s' : Seq (stendhalWeight ℓ ν)} {n n' : ℕ} (hn : n ≤ m)
    (hn' : n' ≤ m) (hnn : n = n') {t t' : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))}
    (h : insertSeq s n hn t = insertSeq s' n' hn' t') : s = s' := by
  subst hnn
  exact eq_of_insertSeq_eq hn h

/-- The windows at `midPos` of different loadings of `λ` give disjoint sets of bottom
loadings. -/
theorem disjoint_insertSet_midPos {s s' : Seq (stendhalWeight ℓ ν)} (hss' : s ≠ s') :
    Disjoint (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
      (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s' (midPos j s') (midPos_le j s')) := by
  refine Finset.disjoint_left.2 fun u hu hu' => hss' ?_
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hu'
  have hpos : midPos j s = midPos j s' := by
    by_cases h : j < ℓ
    · obtain ⟨a, ha, hla⟩ := midPos_of_lt j s h
      obtain ⟨a', ha', hla'⟩ := midPos_of_lt j s' h
      have h1 := insertSeq_lbl_ge (j := j) (hj := hj) s (midPos_le j s) t
        (c := ⟨a.val + N, by rw [card_plus' (I := I)]; omega⟩) a ha.ge rfl
      have h2 := insertSeq_lbl_ge (j := j) (hj := hj) s' (midPos_le j s') t'
        (c := ⟨a'.val + N, by rw [card_plus' (I := I)]; omega⟩) a' ha'.ge rfl
      rw [hla] at h1
      rw [hla', ht'] at h2
      have := lbl_eq_inr_unique (ℓ := ℓ + 2) h1 h2
      have := congrArg Fin.val this
      simp only at this
      omega
    · rw [midPos_of_not_lt j s h, midPos_of_not_lt j s' h]
  exact eq_of_insertSeq_eq' (midPos_le j s) (midPos_le j s') hpos ht'.symm

end Windows


section MidKLR

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)

/-- The bottom loadings of the cap generators with the maximum at `midPos`. -/
def midSet : Finset (Seq (stendhalWeight (ℓ + 2) (ν + ν₀))) :=
  Finset.univ.biUnion fun s : Seq (stendhalWeight ℓ ν) =>
    insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s)

/-- **A diagram at the maximum below every cap generator with the maximum at `midPos`**: the sum
over the loadings `s` of `λ` of the diagram on the window at `midPos s`. -/
def midMapKLR (x : Rc) : Rp :=
  ∑ s : Seq (stendhalWeight ℓ ν), insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s)
    (midPos_le j s) x

variable {j hj Q Λ Λc ν ν₀}

theorem insertMap_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (x : Rc) :
    (insertMap (j := j) (hj := hj) Q Λ Λc s n hn x *
      KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) : Rp) =
      insertMap Q Λ Λc s n hn x :=
  KLR.Corner.val_mul_E _

theorem insertMap_midPos_mul_of_ne {s s' : Seq (stendhalWeight ℓ ν)} (hss' : s ≠ s')
    (x y : Rc) :
    (insertMap (j := j) (hj := hj) Q Λ Λc s (midPos j s) (midPos_le j s) x *
      insertMap Q Λ Λc s' (midPos j s') (midPos_le j s') y : Rp) = 0 := by
  rw [← insertMap_mul_eSum, ← eSum_mul_insertMap (j := j) (hj := hj) (Q := Q) (Λ := Λ)
    (Λc := Λc) (s := s'), mul_assoc, ← mul_assoc (KLRAlgebra.eSum _ _), KLRAlgebra.eSum_mul_eSum,
    Finset.disjoint_iff_inter_eq_empty.1 (disjoint_insertSet_midPos hss'),
    KLRAlgebra.eSum_empty, zero_mul, mul_zero]

theorem midMapKLR_mul (x y : Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ (x * y) =
      midMapKLR j hj Q Λ Λc ν ν₀ x * midMapKLR j hj Q Λ Λc ν ν₀ y := by
  rw [midMapKLR, midMapKLR, midMapKLR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single s (fun s' _ h => insertMap_midPos_mul_of_ne (Ne.symm h) x y)
    (by simp), insertMap_mul]

theorem midMapKLR_add (x y : Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ (x + y) =
      midMapKLR j hj Q Λ Λc ν ν₀ x + midMapKLR j hj Q Λ Λc ν ν₀ y := by
  simp only [midMapKLR, insertMap_add, Finset.sum_add_distrib]

theorem midMapKLR_smul (c : k) (x : Rc) :
    midMapKLR j hj Q Λ Λc ν ν₀ (c • x) = c • midMapKLR j hj Q Λ Λc ν ν₀ x := by
  simp only [midMapKLR, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold insertMap
  rw [map_smul]; exact KLR.Corner.val_smul c _

theorem midMapKLR_zero : midMapKLR j hj Q Λ Λc ν ν₀ 0 = 0 := by
  simp [midMapKLR, insertMap]

end MidKLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section MidDescent

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)

/-- The diagrams at the maximum at `midPos`, in `T̃^{λ⁺}`, before descending. -/
def midBot : Rc →ₙₐ[k] StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) where
  toFun x := botMap k Q Λ Λc j hj ν ν₀ (midMapKLR j hj Q Λ Λc ν ν₀ x)
  map_zero' := by rw [midMapKLR_zero, map_zero]
  map_add' a b := by rw [midMapKLR_add, map_add]
  map_mul' a b := by rw [midMapKLR_mul, map_mul]
  map_smul' c a := by
    change botMap k Q Λ Λc j hj ν ν₀ (midMapKLR j hj Q Λ Λc ν ν₀ (c • a)) =
      c • botMap k Q Λ Λc j hj ν ν₀ (midMapKLR j hj Q Λ Λc ν ν₀ a)
    rw [midMapKLR_smul, map_smul]

variable {j hj Q Λ Λc ν ν₀}

theorem midBot_apply (x : Rc) :
    midBot j hj Q Λ Λc ν ν₀ x = botMap k Q Λ Λc j hj ν ν₀ (midMapKLR j hj Q Λ Λc ν ν₀ x) := rfl

theorem redRelations_midBot : RedRelations (midBot j hj Q Λ Λc ν ν₀) where
  red_dot b w hb := by
    rw [midBot_apply, midMapKLR, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [insertMap_mul, insertMap_x, insertMap_e, mul_assoc, eSum_mul_e_insertSeq, botMap,
      AlgHom.comp_apply, map_mul]
    change orderProjection _ _ _ (StendhalAlgebraAllOrders.x _ * StendhalAlgebraAllOrders.e _) = 0
    rw [StendhalAlgebraAllOrders.x_mul_e_of_red, map_zero]
    rw [insertSeq_lbl_win s (midPos_le j s) _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩ rfl,
      Seq.map_lbl]
    obtain ⟨r, hr⟩ : ∃ r, w.lbl b = .inr r := by cases h : w.lbl b <;> simp_all
    exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl
  red_cross p hp w ha hb := by
    rw [midBot_apply, midMapKLR, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
    have hs := midPos_le j s
    rw [insertMap_mul, insertMap_ψ s hs hp, insertMap_e, mul_assoc, eSum_mul_e_insertSeq,
      botMap, AlgHom.comp_apply, ofKLR_ψ_mul_e_of_red (midPos j s + p) (by omega) _ ?_ ?_,
      map_zero]
    · rw [insertSeq_lbl_win s hs _ ⟨p, by rw [Multiset.card_map]; omega⟩ rfl, Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p, by omega⟩ = .inr r := by
        cases h : w.lbl ⟨p, by omega⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl
    · rw [insertSeq_lbl_win s hs _ ⟨p + 1, by rw [Multiset.card_map]; omega⟩ (by simp; omega),
        Seq.map_lbl]
      obtain ⟨r, hr⟩ : ∃ r, w.lbl ⟨p + 1, hp⟩ = .inr r := by
        cases h : w.lbl ⟨p + 1, hp⟩ <;> simp_all
      exact (congrArg (fun a => (cupColour (I := I) j hj a).isRight) hr).trans rfl

variable (j hj Q Λ Λc ν ν₀) in
/-- **The diagrams at the maximum at `midPos`**, as a map `T̃^{(μ,μ*)} → T̃^{λ⁺}`. -/
def midStendhal :
    StendhalAlgebra k Q Λc ν₀ →ₙₐ[k] StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) :=
  stendhalLift redRelations_midBot

theorem midStendhal_eq (z : StendhalAlgebra k Q Λc ν₀) :
    ∃ x, midStendhal j hj Q Λ Λc ν ν₀ z = midBot j hj Q Λ Λc ν ν₀ x := by
  obtain ⟨x, hx⟩ := StendhalAlgebraAllOrders.ofKLR_surjective z.val
  refine ⟨x, ?_⟩
  rw [midStendhal, stendhalLift_apply, ← hx, allOrdersLift_ofKLR]

theorem midStendhal_cupMap (x : Rc) :
    midStendhal j hj Q Λ Λc ν ν₀ (cupMap k Q Λc ν₀ x) =
      midBot j hj Q Λ Λc ν ν₀ x * midStendhal j hj Q Λ Λc ν ν₀ 1 := by
  rw [midStendhal, stendhalLift_topMap]
  rfl

end MidDescent

section MidModel

open MulOpposite InductionAlong

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (ν ν₀ : Multiset I)

/-- The diagrams at the maximum at `midPos`, on the opposite rings: induction along it is the
model of `K̃` for a cap after `λ_j`. -/
def midOp : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ →ₙ+*
    (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (midStendhal j hj Q Λ Λc ν ν₀))

theorem midOp_apply (c : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    midOp j hj Q Λ Λc ν ν₀ c = op (midStendhal j hj Q Λ Λc ν ν₀ c.unop) := rfl

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The model of `K̃^{λ⁺}_λ` for a cap after `λ_j`**: `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}`, induced along
the diagrams at the maximum at `midPos`, just before the red strand `λ_{j+1}`. -/
abbrev MidModel : Type _ := Ind L (midOp j hj Q Λ Λc ν ν₀)

end MidModel

end Categorification.Stendhal.CupCap
