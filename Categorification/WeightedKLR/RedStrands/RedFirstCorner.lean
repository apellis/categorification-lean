/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedEquiv
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.WeightedKLR.RedStrands.StandardAction
import Categorification.WeightedKLR.Loadings.Shift
import Categorification.WeightedKLR.Loadings.Tree

/-!
# The red-first corner of `T^λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.6,
Proposition 5.28. Let `e⁰` be the sum of the idempotents of the red-ordered loadings in which
every red strand is left of every black strand, and `P⁰ = e⁰ T^λ`. Then
`End(P⁰) ≅ T^{λ̲} ≅ R^{λ̲}`, where `λ̲ = ∑ λ_r` and `R^{λ̲}` is the cyclotomic KLR algebra.
The proof applies the splitting of a red strand (Corollary 4.21 in v2, `splitRedEquiv`)
repeatedly and ends with one red strand (Proposition 4.20, `SingleRed.cyclotomicEquiv`).

Here `P⁰` is the right module `e⁰ T^λ`, whose endomorphism ring is the corner `e⁰ T^λ e⁰`;
the theorem is stated for the corner.

## Main results

* `IsRedFirst` : every red strand is left of every black strand.
* `redFirstIdem` : the idempotent `e⁰` of `T^λ`.
* `SplitRed.redFirstSplitEquiv` : splitting a red strand identifies the red-first corners.
* `redFirstCornerEquiv` : **Proposition 5.28**, `e⁰ T^λ e⁰ ≅ R^{λ̲}` as rings, for the
  crossing parameters of §2.2.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k]

/-- A loading is red-first when every red strand is left of every black strand. -/
def IsRedFirst {ℓ : ℕ} {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν)) : Prop :=
  ∀ a b, (s.lbl a).isLeft → (s.lbl b).isRight → b < a

namespace SplitRed

variable {ℓ : ℕ} (c : Fin ℓ) {ν : Multiset I}

/-- Splitting a red strand preserves and reflects red-firstness. -/
theorem isRedFirst_splitLoading_iff (s : Seq (stendhalWeight ℓ ν)) :
    IsRedFirst (splitLoading c s) ↔ IsRedFirst s := by
  constructor
  · intro h a b ha hb
    have := h (splitPos c s a) (splitPos c s b)
      (by rw [splitLoading_lbl_splitPos, splitColor_isLeft]; exact ha)
      (by rw [splitLoading_lbl_splitPos, splitColor_isRight]; exact hb)
    exact (splitPos_lt_splitPos_iff c s).1 this
  · intro h x y hx hy
    rcases eq_newPos_or_splitPos c s x with rfl | ⟨a, rfl⟩
    · rw [splitLoading_lbl_newPos] at hx; simp at hx
    rw [splitLoading_lbl_splitPos, splitColor_isLeft] at hx
    rcases eq_newPos_or_splitPos c s y with rfl | ⟨b, rfl⟩
    · have hlt := h a (redPos c s) hx (by rw [lbl_redPos]; rfl)
      have h1 := splitPos_val c s a; have h2 := newPos_val c s
      rw [Fin.lt_def] at hlt ⊢; split_ifs at h1 <;> omega
    · rw [splitLoading_lbl_splitPos, splitColor_isRight] at hy
      exact (splitPos_lt_splitPos_iff c s).2 (h a b hx hy)

/-- A red-ordered red-first loading of `λ'` comes from a loading of `λ`. -/
theorem exists_splitLoading_of_isRedFirst (t : Seq (stendhalWeight (ℓ + 1) ν))
    (ht : IsRedOrdered t) (ht' : IsRedFirst t) :
    ∃ s : Seq (stendhalWeight ℓ ν), splitLoading c s = t := by
  have hcard := card_split ℓ ν
  set p := redPos c.castSucc t
  set q := redPos c.succ t
  have hp : t.lbl p = .inr c.castSucc := lbl_redPos c.castSucc t
  have hq : t.lbl q = .inr c.succ := lbl_redPos c.succ t
  have hcs : c.castSucc < c.succ := Fin.castSucc_lt_succ
  have hpq : p < q := by
    rcases lt_trichotomy p q with h | h | h
    · exact h
    · rw [h, hq] at hp; exact absurd (Sum.inr.inj hp) hcs.ne'
    · exact absurd (ht _ _ _ _ h hq hp) (not_lt.2 hcs.le)
  have hq' : (q : ℕ) = p + 1 := by
    by_contra hne
    have hlt : (p : ℕ) + 1 < q := by rw [Fin.lt_def] at hpq; omega
    set x : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)) := ⟨p + 1, by omega⟩
    have hpx : p < x := by rw [Fin.lt_def]; simp [x]
    have hxq : x < q := by rw [Fin.lt_def]; exact hlt
    rcases hlx : t.lbl x with i | r
    · exact absurd (ht' x q (by rw [hlx]; rfl) (by rw [hq]; rfl)) (not_lt.2 hxq.le)
    · have h1 := ht _ _ _ _ hpx hp hlx
      have h2 := ht _ _ _ _ hxq hlx hq
      rw [Fin.lt_def] at h1 h2; simp at h1 h2; omega
  have hpm : (p : ℕ) < Multiset.card (stendhalWeight ℓ ν) := by
    have := q.2; omega
  obtain ⟨s, hs, -⟩ := exists_splitLoading_eq c t ⟨p, hpm⟩ hp
    (by convert hq using 2; exact Fin.ext hq'.symm)
  exact ⟨s, hs⟩


end SplitRed

section RedFirst

variable (Q : I → I → MvPolynomial (Fin 2) k) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)

/-- The red-first red-ordered loadings. -/
abbrev RedFirstLoading := {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s ∧ IsRedFirst s}

open Classical in
/-- The idempotent `e⁰` of `T̃^λ`: the sum of the idempotents of the red-ordered loadings with
every red strand left of every black strand. -/
def redFirstStendhalIdem : StendhalAlgebra k Q Λ ν :=
  ∑ s : RedFirstLoading (ℓ := ℓ) ν, StendhalAlgebra.e s.1 s.2.1

/-- The idempotent `e⁰` of `T^λ`. -/
def redFirstIdem : TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν (redFirstStendhalIdem Q Λ ν)

/-- `e⁰` is idempotent in `T̃^λ`. -/
theorem isIdempotentElem_redFirstStendhalIdem :
    IsIdempotentElem (redFirstStendhalIdem Q Λ ν) := by
  classical
  unfold redFirstStendhalIdem
  convert WeightedKLR.isIdempotentElem_sum_of_mul_eq
    (d := fun s : RedFirstLoading (ℓ := ℓ) ν => (StendhalAlgebra.e s.1 s.2.1 :
      StendhalAlgebra k Q Λ ν)) (fun s t => ?_)
  rw [StendhalAlgebra.e_mul_e]
  simp only [Subtype.ext_iff]

/-- `e⁰` is idempotent in `T^λ`. -/
theorem isIdempotentElem_redFirstIdem : IsIdempotentElem (redFirstIdem Q Λ ν) :=
  (isIdempotentElem_redFirstStendhalIdem Q Λ ν).map _

end RedFirst

namespace SplitRed

variable (Q : I → I → MvPolynomial (Fin 2) k) {ℓ : ℕ} (c : Fin ℓ) (Λ' : Fin (ℓ + 1) → I →₀ ℕ)
  {ν : Multiset I}

/-- Splitting a red strand sends `e⁰` to `e⁰` in `T̃`. -/
theorem splitStendhalValue_redFirst :
    splitStendhalValue c Q Λ' ν (redFirstStendhalIdem Q (mergeWeights c Λ') ν) =
      redFirstStendhalIdem Q Λ' ν := by
  classical
  unfold redFirstStendhalIdem
  rw [map_sum]
  simp only [splitStendhalValue_e]
  refine Fintype.sum_bijective (fun s => ⟨splitLoading c s.1,
    (isRedOrdered_splitLoading_iff c s.1).2 s.2.1, (isRedFirst_splitLoading_iff c s.1).2 s.2.2⟩)
    ⟨fun s t h => Subtype.ext (splitLoading_injective c (congrArg Subtype.val h)), fun t => ?_⟩
    _ _ (fun s => rfl)
  obtain ⟨s, hs⟩ := exists_splitLoading_of_isRedFirst c t.1 t.2.1 t.2.2
  refine ⟨⟨s, (isRedOrdered_splitLoading_iff c s).1 (hs ▸ t.2.1),
    (isRedFirst_splitLoading_iff c s).1 (hs ▸ t.2.2)⟩, Subtype.ext hs⟩

/-- Splitting a red strand sends `e⁰` to `e⁰` in `T`. -/
theorem splitRed_redFirstIdem :
    (splitRed c Q Λ' (redFirstIdem Q (mergeWeights c Λ') ν)).val = redFirstIdem Q Λ' ν := by
  rw [redFirstIdem, splitRed_mk, splitStendhalValue_redFirst]; rfl

/-- Splitting a red strand identifies the red-first corners. -/
def redFirstSplitEquiv {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q) :
    (isIdempotentElem_redFirstIdem Q (mergeWeights c Λ') ν).Corner ≃+*
      (isIdempotentElem_redFirstIdem Q Λ' ν).Corner :=
  have hb := (isIdempotentElem_redFirstIdem Q (mergeWeights c Λ') ν).map (splitRed c Q Λ')
  have hb' : IsIdempotentElem (splitRed c Q Λ' (redFirstIdem Q (mergeWeights c Λ') ν)).val := by
    rw [splitRed_redFirstIdem]; exact isIdempotentElem_redFirstIdem Q Λ' ν
  ((WeightedKLR.cornerEquivOfEq (splitRedEquiv c Q Λ' hQ).toRingEquiv _ hb rfl).trans
    (WeightedKLR.cornerCornerEquiv hb hb')).trans
    (WeightedKLR.cornerEquivOfEq (RingEquiv.refl _) hb' _ (splitRed_redFirstIdem Q c Λ'))


omit [DecidableEq I] in
/-- Merging two red strands preserves the total weight. -/
theorem sum_mergeWeights : ∑ r, mergeWeights c Λ' r = ∑ r, Λ' r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos c).ne'
  rw [Fin.sum_univ_succAbove _ c, Fin.sum_univ_succAbove Λ' c.succ,
    Fin.sum_univ_succAbove (fun r => Λ' (c.succ.succAbove r)) c, mergeWeights_self,
    succAbove_self]
  simp only [mergeWeights_of_ne _ _ (Fin.succAbove_ne c _)]
  abel

end SplitRed

/-- The corner of the unit idempotent is the whole ring. -/
def cornerOneEquiv {R : Type*} [Ring R] :
    (IsIdempotentElem.one : IsIdempotentElem (1 : R)).Corner ≃+* R where
  toFun x := x.1
  invFun a := ⟨a, (Subsemigroup.mem_corner_iff IsIdempotentElem.one).2 ⟨one_mul a, mul_one a⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

section Base

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

omit [DecidableEq I] in
/-- With one red strand, a loading that is not violated is red-first. -/
theorem isRedFirst_of_not_isViolated [DecidableEq I] {s : Seq (stendhalWeight 1 ν)}
    (hs : ¬ IsViolated s) : IsRedFirst s := by
  intro a b ha hb
  by_contra hab
  have hab : a ≤ b := not_lt.1 hab
  apply hs
  have h0 : 0 < Multiset.card (stendhalWeight 1 ν) := lt_of_le_of_lt (Nat.zero_le _) b.2
  refine ⟨h0, ?_⟩
  rcases h : s.lbl ⟨0, h0⟩ with i | r
  · rfl
  · exfalso
    obtain ⟨r', hr'⟩ := Sum.isRight_iff.1 hb
    have e0 := SplitRed.eq_redPos (ν := ν) 0 (a := ⟨0, h0⟩) (by rw [h, Subsingleton.elim r 0])
    have eb := SplitRed.eq_redPos (ν := ν) 0 (a := b) (by rw [hr', Subsingleton.elim r' 0])
    have hb0 : b = ⟨0, h0⟩ := eb.trans e0.symm
    have ha0 : a = b := Fin.ext (by
      have := Fin.le_def.1 hab; rw [hb0] at this ⊢; simp only at this ⊢; omega)
    rw [ha0, hr'] at ha
    simp at ha

/-- With one red strand, `e⁰ = 1` in `T^λ`. -/
theorem redFirstIdem_eq_one : redFirstIdem Q Λ ν = 1 := by
  classical
  have h1 : (∑ s : {s : Seq (stendhalWeight 1 ν) // IsRedOrdered s},
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s.1 s.2)) = 1 := by
    have h : (∑ s : {s : Seq (stendhalWeight 1 ν) // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 :
        StendhalAlgebra k Q Λ ν) = 1 := by
      apply Subtype.ext
      rw [KLR.Corner.val_sum, KLR.Corner.val_one]
      change (∑ s : {s : Seq (stendhalWeight 1 ν) // IsRedOrdered s},
        StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
      exact (Finset.sum_subtype _ (fun s => by simp) _).symm
    simpa only [map_sum, map_one] using congrArg (TensorProductAlgebra.mk Q Λ ν) h
  rw [← h1, redFirstIdem, redFirstStendhalIdem, map_sum]
  refine Fintype.sum_of_injective (fun s : RedFirstLoading (ℓ := 1) ν => ⟨s.1, s.2.1⟩)
    (fun s t h => Subtype.ext (by simpa using congrArg Subtype.val h)) _ _ (fun t ht => ?_)
    (fun s => rfl)
  by_cases hv : IsViolated t.1
  · change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨_, _, hv, rfl⟩
  · exact absurd ⟨⟨t.1, t.2, isRedFirst_of_not_isViolated ν hv⟩, rfl⟩ ht

/-- One red strand: the red-first corner is the cyclotomic KLR algebra (Webster,
arXiv:1309.3796v2, Proposition 4.20). -/
def redFirstCornerEquivOne :
    (isIdempotentElem_redFirstIdem Q Λ ν).Corner ≃+*
      CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν :=
  ((WeightedKLR.cornerEquivOfEq (RingEquiv.refl _) _ IsIdempotentElem.one
    (redFirstIdem_eq_one Q Λ ν)).trans cornerOneEquiv).trans
    (SingleRed.cyclotomicEquiv Q Λ ν).symm.toRingEquiv

end Base

variable (Q : I → I → MvPolynomial (Fin 2) k) {D : QuantumGroup.CartanDatum I}
  (hQ : IsRouquierQ D Q) (ν : Multiset I)

/-- Induction on the number of red strands for `redFirstCornerEquiv`. -/
def redFirstCornerEquivAux : ∀ (ℓ : ℕ) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (w : I →₀ ℕ),
    ∑ r, Λ r = w → ((isIdempotentElem_redFirstIdem Q Λ ν).Corner ≃+*
      CycKLR k Q (fun i => Polynomial.X ^ w i) ν)
  | 0, Λ, w, h => by
      obtain rfl : Λ 0 = w := by rw [← h, Fin.sum_univ_one]
      exact redFirstCornerEquivOne Q Λ ν
  | ℓ + 1, Λ', w, h => (SplitRed.redFirstSplitEquiv Q 0 Λ' hQ).symm.trans
      (redFirstCornerEquivAux ℓ (SplitRed.mergeWeights 0 Λ') w
        ((SplitRed.sum_mergeWeights 0 Λ').trans h))

/-- **Webster, arXiv:1309.3796v2, Proposition 5.28.** For the crossing parameters of §2.2,
the endomorphism ring `e⁰ T^λ e⁰` of `P⁰ = e⁰ T^λ` is the cyclotomic KLR algebra of the total
weight `∑ λ_r`. -/
def redFirstCornerEquiv {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) :
    (isIdempotentElem_redFirstIdem Q Λ ν).Corner ≃+*
      CycKLR k Q (fun i => Polynomial.X ^ (∑ r, Λ r) i) ν :=
  redFirstCornerEquivAux Q hQ ν ℓ Λ _ rfl

end Categorification.Stendhal
