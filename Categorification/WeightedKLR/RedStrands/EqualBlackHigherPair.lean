/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.MixedJointCycle
import Categorification.WeightedKLR.RedStrands.RightPairQuotientLift

/-!
# The fixed-top equal-black pair in the higher quotient

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and the cut after (6.21).
At the rightmost exit with two equal black strands, the two joint parameters of a
marked right-arm relation differ from those of one common cycle coefficient by
higher elements. The exchanged reds end the red order and red spectators before
them are allowed.
-/
open scoped BigOperators

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ

/-- At the extreme or mixed fixed top, every supported relation in the higher
quotient of the equal-black right pair lifts to the common cycle join.
The distinguished exchanged pair is last in the upper red order. -/
theorem exists_equalBlack_rightPairCycle_at_extreme_or_mixed
    (hQ : KLRSymm Q) (s top : Seq μ) (p : ℕ) (hp : p+2<n) (a b : Fin ℓ) (i : I)
    (atTop : top=s ∨ top=sadj n p • s)
    (L : List (Fin ℓ)) (order : redWord top = L ++ [a,b])
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (hi : s.lbl ⟨p+1,by omega⟩ = .inl i) (hi' : s.lbl ⟨p+2,hp⟩ = .inl i)
    (blacks : ∀ j, (s.lbl j).isLeft → j = ⟨p+1,by omega⟩ ∨ j = ⟨p+2,hp⟩) :
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b top) (redWord top)
    let q := J.ringCon.mk'
    let mq := q.comp (violMk k Q Λ ν).toRingHom
    let P := mq.comp (ofKLR k Q Λ ν).toRingHom
    let t := sadj n p • s
    ∀ x y : J.ringCon.Quotient,
      P (e top)*x*P (e t)=x → P (e top)*y*P (e t)=y →
      x*P (ψw [p]*e s)=y*P (ψw [p,p+1]*e s) →
      ∃ c : J.ringCon.Quotient, P (e top)*c*P (e (sadj n (p+1) • t))=c ∧
        c*P (ψw [p,p+1]*e t)=x ∧ c*P (ψw [p+1]*e t)=y := by
  intro J q mq P t x y hx hy hrel
  let raw := ofKLR k Q Λ ν
  let u := fun j => wordProd n (rightPairWord p j) • s
  have hs : sadj n (p+1) • s = s := sadj_smul_eq_self (by omega) (hi.trans hi'.symm)
  have ut (j : Bool) : u j=t := by
    cases j
    · simp only [u,rightPairWord,wordProd_singleton,t]
    · simp only [u,rightPairWord,wordProd_cons,wordProd_nil,mul_one,mul_smul,hs,t]
  let pair : Bool → J.ringCon.Quotient := fun j => if j then y else -x
  have pairSupport (j : Bool) : P (e top)*pair j*P (e (u j))=pair j := by
    rw [ut j]
    cases j
    · simpa only [pair,Bool.false_eq_true,↓reduceIte,mul_neg,neg_mul] using congrArg Neg.neg hx
    · exact hy
  have pairZero : (∑ j, pair j*P (ψw (rightPairWord p j)*e s))=0 := by
    simp only [Fintype.sum_bool,pair,Bool.false_eq_true,↓reduceIte,rightPairWord,neg_mul,← hrel,add_neg_cancel]
  obtain ⟨c,cut,eval,czero⟩ := exists_rightPairRelation_affine_lift_of_lastPairHigher Q Λ hQ
    s top p hp a b L order hb blacks pair pairSupport pairZero
  have cut' (j : Bool) : raw (e top)*c j*raw (e t)=c j := by
    simpa only [u,ut] using cut j
  have idem (v : Seq μ) : raw (e v)*raw (e v)=raw (e v) := by rw [← map_mul,e_mul_self]
  have left (j : Bool) : raw (e top)*c j=c j := by
    conv_lhs => rw [← cut' j]
    rw [← mul_assoc (raw (e top)),← mul_assoc (raw (e top)),idem,cut']
  have right (j : Bool) : c j*raw (e t)=c j := by
    conv_lhs => rw [← cut' j]
    rw [mul_assoc _ (raw (e t)),idem,cut']
  have signed : c false*raw (ψw [p]*e s)+c true*raw (ψw [p,p+1]*e s)=0 := by
    simpa only [Fintype.sum_bool,rightPairWord,add_comm] using czero
  have empty : IsReduced n [] := by constructor <;> simp [ValidWord,wordProd_nil]
  have single : IsReduced n [p+1] := by
    refine ⟨by simp [ValidWord,show p+1+1<n by omega],?_⟩
    rw [wordProd_singleton,length_sadj (show p+1+1<n by omega)]
    rfl
  have reds (j : Fin n) (h₁ : j ≠ ⟨p+1,by omega⟩) (h₂ : j ≠ ⟨p+2,hp⟩) :
      (s.lbl j).isRight := by
    rcases h : s.lbl j with black | red
    · rcases blacks j (by simp [h]) with h | h
      · exact (h₁ h).elim
      · exact (h₂ h).elim
    · rfl
  have matching := twoBlack_return_permutations s p hp (hi.trans hi'.symm) reds
  have solve : ∃ w, w*raw (e (sadj n (p+1) • t))=w ∧
      w*raw (ψw [p,p+1]*e t) = -(c false) ∧ w*raw (ψw [p+1]*e t)=c true := by
    rcases atTop with h | h
    · subst top
      have cjoint := exists_equalBlack_corner_cycle_coefficient (Q := Q) (Λ := Λ) hQ s []
        p hp empty single b i (by simpa only [wordProd_nil,one_smul] using hb)
        (by simpa only [wordProd_nil,one_smul] using hi)
        (by simpa only [wordProd_nil,one_smul] using hi')
        (by simpa only [wordProd_nil,one_smul] using matching) (c false) (c true)
      simp only [wordProd_nil,one_smul] at cjoint
      exact cjoint (left false) (right false) (left true) (right true) signed
    · subst top
      exact exists_mixedJoint_corner_cycle_coefficient hQ s p hp b i hb hi hi' reds
        (c false) (c true) (left false) (right false) (left true) (right true) signed
  obtain ⟨w,wSupport,wLeft,wRight⟩ := solve
  have evalL : mq (c false) = -x := eval false
  have evalR : mq (c true) = y := eval true
  have eP : ∀ v : Seq μ, P (e v)*P (e v)=P (e v) := by intro v; rw [← map_mul,e_mul_self]
  have leftFixed (z : J.ringCon.Quotient) (hz : P (e top)*z*P (e t)=z) : P (e top)*z=z := by
    have h := congrArg (fun y => P (e top)*y) hz
    change P (e top)*(P (e top)*z*P (e t))=P (e top)*z at h
    rw [← mul_assoc (P (e top)),← mul_assoc (P (e top)),eP,hz] at h
    exact h.symm
  have wCut : mq w*P (e (sadj n (p+1) • t))=mq w := by
    change mq w*mq (raw (e (sadj n (p+1) • t)))=mq w
    rw [← map_mul,wSupport]
  have wL : mq w*P (ψw [p,p+1]*e t)=x := by
    change mq w*mq (raw (ψw [p,p+1]*e t))=x
    rw [← map_mul,wLeft,map_neg,evalL,neg_neg]
  have wR : mq w*P (ψw [p+1]*e t)=y := by
    change mq w*mq (raw (ψw [p+1]*e t))=y
    rw [← map_mul,wRight,evalR]
  refine ⟨P (e top)*mq w, ?_, ?_, ?_⟩
  · rw [← mul_assoc (P (e top)) (P (e top)),eP,mul_assoc,wCut]
  · rw [mul_assoc,wL,leftFixed _ hx]
  · rw [mul_assoc,wR,leftFixed _ hy]

/-- At the fixed right-extreme top, every supported relation in the higher
quotient of the equal-black right pair lifts to the common cycle join.
The distinguished exchanged pair is last in the upper red order. -/
theorem exists_equalBlack_rightPairCycle_after_higher
    (hQ : KLRSymm Q) (s : Seq μ) (p : ℕ) (hp : p+2<n) (a b : Fin ℓ) (i : I)
    (L : List (Fin ℓ)) (order : redWord s = L ++ [a,b])
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (hi : s.lbl ⟨p+1,by omega⟩ = .inl i) (hi' : s.lbl ⟨p+2,hp⟩ = .inl i)
    (blacks : ∀ j, (s.lbl j).isLeft → j = ⟨p+1,by omega⟩ ∨ j = ⟨p+2,hp⟩) :
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b s) (redWord s)
    let q := J.ringCon.mk'
    let mq := q.comp (violMk k Q Λ ν).toRingHom
    let P := mq.comp (ofKLR k Q Λ ν).toRingHom
    let t := sadj n p • s
    ∀ x y : J.ringCon.Quotient,
      P (e s)*x*P (e t)=x → P (e s)*y*P (e t)=y →
      x*P (ψw [p]*e s)=y*P (ψw [p,p+1]*e s) →
      ∃ c : J.ringCon.Quotient, P (e s)*c*P (e (sadj n (p+1) • t))=c ∧
        c*P (ψw [p,p+1]*e t)=x ∧ c*P (ψw [p+1]*e t)=y := by
  exact exists_equalBlack_rightPairCycle_at_extreme_or_mixed Q Λ hQ s s p hp a b i (Or.inl rfl) L order hb hi hi' blacks

/-- The higher-mark condition at the extreme or mixed top admits a supported common-joint
coefficient before taking the higher quotient. This is the coupled input to
`exists_marked_fourExitCycle`. -/
theorem exists_equalBlack_rightPair_markedCycle_at_extreme_or_mixed
    (hQ : KLRSymm Q) (s top : Seq μ) (p : ℕ) (hp : p+2<n) (a b : Fin ℓ) (i : I)
    (atTop : top=s ∨ top=sadj n p • s)
    (L : List (Fin ℓ)) (order : redWord top = L ++ [a,b])
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (hi : s.lbl ⟨p+1,by omega⟩ = .inl i) (hi' : s.lbl ⟨p+2,hp⟩ = .inl i)
    (blacks : ∀ j, (s.lbl j).isLeft → j = ⟨p+1,by omega⟩ ∨ j = ⟨p+2,hp⟩) :
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b top) (redWord top)
    let P := (violMk k Q Λ ν).comp (ofKLR k Q Λ ν)
    let t := sadj n p • s
    let u := sadj n (p+1) • t
    ∀ x y : ViolQuotient k Q Λ ν,
      P (e top)*x*P (e t)=x → P (e top)*y*P (e t)=y →
      y*P (ψw [p,p+1]*e s)-x*P (ψw [p]*e s) ∈ J →
      ∃ z : ViolQuotient k Q Λ ν, P (e top)*z*P (e u)=z ∧
        x-z*P (ψw [p,p+1]*e t) ∈ J ∧ y-z*P (ψw [p+1]*e t) ∈ J := by
  intro J P t u x y hx hy hm
  let q := J.ringCon.mk'
  have vanish (w : ViolQuotient k Q Λ ν) : q w=0 ↔ w ∈ J := by
    change J.ringCon.mk' w=0 ↔ w ∈ J
    rw [← TwoSidedIdeal.mem_ker,TwoSidedIdeal.ker_ringCon_mk']
  have rel : q x*q (P (ψw [p]*e s))=q y*q (P (ψw [p,p+1]*e s)) := by
    symm
    apply sub_eq_zero.mp
    simpa only [map_sub,map_mul] using (vanish _).2 hm
  obtain ⟨c,cCut,cL,cR⟩ := exists_equalBlack_rightPairCycle_at_extreme_or_mixed Q Λ hQ
    s top p hp a b i atTop L order hb hi hi' blacks (q x) (q y)
    (by
      change q (P (e top))*q x*q (P (e t))=q x
      simpa only [map_mul] using congrArg q hx)
    (by
      change q (P (e top))*q y*q (P (e t))=q y
      simpa only [map_mul] using congrArg q hy) rel
  obtain ⟨w,hw⟩ := RingCon.mk'_surjective J.ringCon c
  have hw' : q w=c := hw
  let z := P (e top)*w*P (e u)
  have hq : q z=c := by
    change q (P (e top))*c*q (P (e u))=c at cCut
    simpa only [z,map_mul,hw'] using cCut
  have idem (v : Seq μ) : P (e v)*P (e v)=P (e v) := by rw [← map_mul,e_mul_self]
  refine ⟨z,?_,(vanish _).1 ?_,(vanish _).1 ?_⟩
  · calc
      P (e top)*z*P (e u) = (P (e top)*P (e top))*w*(P (e u)*P (e u)) := by
        simp only [z,mul_assoc]
      _ = z := by rw [idem,idem]
  · rw [map_sub,map_mul,hq]
    exact sub_eq_zero.mpr cL.symm
  · rw [map_sub,map_mul,hq]
    exact sub_eq_zero.mpr cR.symm

/-- The higher-mark condition at the right extreme admits a supported common-joint
coefficient before taking the higher quotient. This is the coupled input to
`exists_marked_fourExitCycle`. -/
theorem exists_equalBlack_rightPair_markedCycle
    (hQ : KLRSymm Q) (s : Seq μ) (p : ℕ) (hp : p+2<n) (a b : Fin ℓ) (i : I)
    (L : List (Fin ℓ)) (order : redWord s = L ++ [a,b])
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (hi : s.lbl ⟨p+1,by omega⟩ = .inl i) (hi' : s.lbl ⟨p+2,hp⟩ = .inl i)
    (blacks : ∀ j, (s.lbl j).isLeft → j = ⟨p+1,by omega⟩ ∨ j = ⟨p+2,hp⟩) :
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b s) (redWord s)
    let P := (violMk k Q Λ ν).comp (ofKLR k Q Λ ν)
    let t := sadj n p • s
    let u := sadj n (p+1) • t
    ∀ x y : ViolQuotient k Q Λ ν,
      P (e s)*x*P (e t)=x → P (e s)*y*P (e t)=y →
      y*P (ψw [p,p+1]*e s)-x*P (ψw [p]*e s) ∈ J →
      ∃ z : ViolQuotient k Q Λ ν, P (e s)*z*P (e u)=z ∧
        x-z*P (ψw [p,p+1]*e t) ∈ J ∧ y-z*P (ψw [p+1]*e t) ∈ J := by
  exact exists_equalBlack_rightPair_markedCycle_at_extreme_or_mixed Q Λ hQ s s p hp a b i (Or.inl rfl) L order hb hi hi' blacks

end Categorification.Stendhal.BraidedStendhalAlgebra

