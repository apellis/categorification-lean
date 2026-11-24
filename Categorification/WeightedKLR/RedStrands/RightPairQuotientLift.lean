/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentExitLift
import Categorification.WeightedKLR.RedStrands.AdjacentBlockSlide
import Categorification.KLR.InductionFree
import Categorification.TypeA.WeakOrder
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel

/-!
# Right-pair relations through the Webster higher quotient

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and the cut after (6.21).
At the rightmost two-black exit, two reduced suffixes generate each column whose
upper loading has a black before the right red. When the pair ends the upper red
order and the two active blacks are the only black strands, this includes the
generators of the higher and globally violated ideals.
-/
open scoped BigOperators

namespace Categorification.TypeA
open Equiv

/-- The two exits from a right red strand to a loading with a black strand on
its left. Words are written in operator order. -/
def rightPairWord (p : ℕ) : Bool → List ℕ
  | false => [p]
  | true => [p,p+1]

private theorem append_rightPairDescent {n r : ℕ} (hr : r+1<n) {w : Perm (Fin n)}
    (h : w ⟨r+1,hr⟩ < w ⟨r,by omega⟩) {u : List ℕ}
    (hu : IsReduced n u) (hprod : wordProd n u = w * sadj n r) :
    IsReduced n (u++[r]) ∧ wordProd n (u++[r])=w := by
  have he : wordProd n (u++[r])=w := by
    rw [wordProd_append, hprod, wordProd_singleton, mul_assoc, sadj_mul_self, mul_one]
  exact ⟨⟨validWord_append.2 ⟨hu.1,by simp [ValidWord,hr]⟩,by
    rw [he,List.length_append,List.length_singleton,hu.2,hprod,length_mul_sadj_of_gt hr h]⟩,he⟩

/-- If either of the next two strands moves left of the distinguished strand,
the permutation admits one of the two right-pair words as a reduced suffix. -/
theorem exists_rightPairWord_suffix {n p : ℕ} (hp : p+2<n) (w : Perm (Fin n))
    (h : w ⟨p+1,by omega⟩ < w ⟨p,by omega⟩ ∨ w ⟨p+2,hp⟩ < w ⟨p,by omega⟩) :
    ∃ (i : Bool) (u : Perm (Fin n)), IsReduced n (canWord n u ++ rightPairWord p i) ∧
      wordProd n (canWord n u ++ rightPairWord p i)=w := by
  have hp₁ : p+1<n := by omega
  by_cases h₁ : w ⟨p+1,hp₁⟩ < w ⟨p,by omega⟩
  · exact ⟨false,w*sadj n p,append_rightPairDescent hp₁ h₁
      (isReduced_canWord _ _) (wordProd_canWord _ _)⟩
  · have h₂ := h.resolve_left h₁
    have h₂₁ : w ⟨p+2,hp⟩ < w ⟨p+1,hp₁⟩ := h₂.trans_le (not_lt.mp h₁)
    let v := w*sadj n (p+1)
    have hv : v ⟨p+1,hp₁⟩ < v ⟨p,by omega⟩ := by
      simp only [v,Perm.mul_apply,sadj_apply_left hp,
        sadj_apply_of_ne (k := p+1) (⟨p,by omega⟩ : Fin n) (by dsimp; omega) (by dsimp; omega)]
      exact h₂
    obtain ⟨hu,he⟩ := append_rightPairDescent hp₁ hv (isReduced_canWord n (v*sadj n p))
      (wordProd_canWord n (v*sadj n p))
    have hfull := append_rightPairDescent hp h₂₁ hu he
    exact ⟨true,v*sadj n p,by simpa only [rightPairWord,List.append_assoc,List.singleton_append] using hfull⟩

end Categorification.TypeA

namespace Categorification.KLR.KLRAlgebra
open KLR TypeA Equiv MvPolynomial

variable {I k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
local notation "n" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- If every strand permutation from the bottom loading to the upper loading
moves one of two distinguished strands left of their common predecessor, the
two right-pair words generate the column. -/
theorem exists_rightPairColumn_coefficients (hQ : KLRSymm Q) (s t : Seq ν) (p : ℕ)
    (hp : p+2<n)
    (h : ∀ w : Perm (Fin n), w • s=t →
      w ⟨p+1,by omega⟩ < w ⟨p,by omega⟩ ∨ w ⟨p+2,hp⟩ < w ⟨p,by omega⟩)
    (z : A) :
    ∃ c : Bool → A, e t*z*e s=∑ i, c i*(ψw (rightPairWord p i)*e s) := by
  classical
  have exits (w : Perm (Fin n)) (hw : w • s=t) := exists_rightPairWord_suffix hp w (h w hw)
  let ρ (w : Perm (Fin n)) := if hw : w • s=t then
    canWord n (exits w hw).choose_spec.choose ++ rightPairWord p (exits w hw).choose
    else canWord n w
  have hρ : IsReducedChoice ρ := by
    intro w
    dsimp only [ρ]
    split_ifs with hw
    · exact (exits w hw).choose_spec.choose_spec
    · exact ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩
  let B := lbasis (k := k) («μ» := ν) hQ ρ hρ
  induction B.mem_span z using Submodule.span_induction with
  | zero => exact ⟨fun _ => 0,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c,hc⟩ := hx
    obtain ⟨d,hd⟩ := hy
    refine ⟨fun i => c i+d i,?_⟩
    simp only [mul_add,add_mul,hc,hd,Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨d,hd⟩ := hx
    refine ⟨fun i => c • d i,?_⟩
    simp only [mul_smul_comm,smul_mul_assoc,hd,Finset.smul_sum]
  | mem _ hx =>
    obtain ⟨⟨s',w,d⟩,rfl⟩ := hx
    rw [show B (s',w,d) = _ from lbasis_apply ..,mul_assoc,mul_assoc _ (e s'),e_mul_e]
    split_ifs with he
    swap
    · exact ⟨fun _ => 0,by simp⟩
    subst s'
    by_cases hw : w • s=t
    · let i := (exits w hw).choose
      let u := (exits w hw).choose_spec.choose
      refine ⟨fun j => if j=i then e t*pol (monomial d 1)*ψw (canWord n u) else 0,?_⟩
      rw [Finset.sum_eq_single i]
      · simp only [ρ,dite_eq_left hw,ψw_append,mul_assoc,ite_true,i,u]
      · intro j _ hj
        simp only [ite_eq_right hj,zero_mul]
      · exact fun hi => (hi (Finset.mem_univ i)).elim
    · have cut := e_mul_pol_ψw_e (Q := Q) (monomial d (1 : k)) (ρ w) s
      rw [(hρ w).2] at cut
      refine ⟨fun _ => 0,?_⟩
      rw [← cut,← mul_assoc,e_mul_e,ite_eq_right (Ne.symm hw),zero_mul]
      simp only [zero_mul,Finset.sum_const_zero]

end Categorification.KLR.KLRAlgebra


namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv
variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ

/-- With two black strands immediately after the red, the right-pair words
generate every column ending with a black before that red. -/
theorem exists_rightPairColumn_coefficients_of_black_before
    {D : Type*} [Ring D] [Algebra k D]
    (φ : KLRAlgebra k (stendhalQ Q Λ) μ →ₐ[k] D) (surj : Function.Surjective φ)
    (hQ : KLRSymm Q) (s t : Seq μ) (p : ℕ) (hp : p+2<n) (b : Fin ℓ)
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (blacks : ∀ a, (s.lbl a).isLeft → a = ⟨p+1,by omega⟩ ∨ a = ⟨p+2,hp⟩)
    (before : ∃ l r, l < r ∧ (t.lbl l).isLeft ∧ t.lbl r = .inr b)
    (z : D) :
    ∃ c : Bool → D, φ (e t)*z*φ (e s)=∑ i, c i*φ (ψw (rightPairWord p i)*e s) := by
  obtain ⟨l,r,hlr,hl,hr⟩ := before
  have fit (w : Perm (Fin n)) (hw : w • s=t) :
      w ⟨p+1,by omega⟩ < w ⟨p,by omega⟩ ∨ w ⟨p+2,hp⟩ < w ⟨p,by omega⟩ := by
    have hbl : (s.lbl (w⁻¹ l)).isLeft := by rwa [← lbl_smul,hw]
    have cancelLeft (z : Fin n) : w⁻¹ (w z)=z := w.symm_apply_apply z
    have cancelRight (z : Fin n) : w (w⁻¹ z)=z := w.apply_symm_apply z
    have hred : t.lbl (w ⟨p,by omega⟩) = .inr b := by
      rw [← hw,lbl_smul,cancelLeft]
      exact hb
    have hr' := lbl_inj_of_inr t b hred hr
    rcases blacks _ hbl with h₁ | h₂
    · left
      rwa [← h₁,cancelRight,hr']
    · right
      rwa [← h₂,cancelRight,hr']
  obtain ⟨a,rfl⟩ := surj z
  obtain ⟨c,hc⟩ := exists_rightPairColumn_coefficients (stendhalQ_symm Q Λ hQ) s t p hp fit a
  exact ⟨fun i => φ (c i), by simpa only [map_mul,map_sum] using congrArg φ hc⟩

omit [DecidableEq I] in
/-- A violated loading has a black strand before every red strand. -/
theorem exists_black_before_red_of_isViolated (t : Seq μ) (b : Fin ℓ)
    (h : IsViolated t) : ∃ l r, l<r ∧ (t.lbl l).isLeft ∧ t.lbl r = .inr b := by
  obtain ⟨hn,hl⟩ := h
  obtain ⟨r,hr⟩ := exists_lbl_eq_inr t b
  let l : Fin n := ⟨0,hn⟩
  have hne : l≠r := fun he => by
    change (t.lbl l).isLeft at hl
    rw [he,hr] at hl
    exact Bool.noConfusion hl
  exact ⟨l,r,lt_of_le_of_ne (by change l.val ≤ r.val; exact Nat.zero_le _) hne,hl,hr⟩

/-- A higher cut at the merged red boundary has a black before the second red. -/
theorem exists_black_before_red_of_adjacentBlockRoot_pos (t : Seq μ) (a b : Fin ℓ)
    (i : I) (h : 0 < adjacentBlockRoot a b t b i) :
    ∃ l r, l<r ∧ (t.lbl l).isLeft ∧ t.lbl r = .inr b := by
  obtain ⟨r,hr⟩ := exists_lbl_eq_inr t b
  have h' : 0 < blockBlackCount t {a,b} i := by
    simpa only [adjacentBlockRoot, or_true, ↓reduceIte] using h
  unfold blockBlackCount at h'
  obtain ⟨l,hl⟩ := Finset.card_pos.mp h'
  obtain ⟨_,hl,hs⟩ := Finset.mem_filter.mp hl
  exact ⟨l,r,hs r b (by simp) hr,by simp [hl],hr⟩

/-- When the distinguished pair is last in the red order, every higher cut
has a black before its final red. Exterior reds before that pair are allowed. -/
theorem exists_black_before_red_of_higherLastPairCut (v : Seq μ) (a b : Fin ℓ)
    (L : List (Fin ℓ)) (order : redWord v = L ++ [a,b]) (α : Fin ℓ → I → ℕ)
    (higher : α < adjacentBlockRoot a b v) :
    ∃ l r, l<r ∧ (v.lbl l).isLeft ∧ v.lbl r = .inr b := by
  by_contra no
  apply higher.not_ge
  intro r i
  obtain ⟨q,hq⟩ := exists_lbl_eq_inr v b
  by_cases pair : r=a ∨ r=b
  · have hz : adjacentBlockRoot a b v b i=0 := by
      by_contra h
      exact no (exists_black_before_red_of_adjacentBlockRoot_pos v a b i (Nat.pos_of_ne_zero h))
    have he : blockBlackCount v {a,b} i=0 := by
      simpa only [adjacentBlockRoot,or_true,↓reduceIte] using hz
    simp only [adjacentBlockRoot,ite_eq_left pair,he,Nat.zero_le]
  · have hr : r ∈ L := by
      have hr := mem_redWord v r
      rw [order,List.mem_append] at hr
      exact hr.resolve_right (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using pair)
    have hp := redWord_pairwise_one v
    rw [order,List.pairwise_append] at hp
    obtain ⟨p,hp'⟩ := exists_lbl_eq_inr v r
    have hpq : p<q := hp.2.2 _ hr _ (by simp) _ _ hp' hq
    have hz : blockBlackCount v {r} i=0 := by
      apply Nat.eq_zero_of_not_pos
      intro hn
      unfold blockBlackCount at hn
      obtain ⟨l,hl⟩ := Finset.card_pos.mp hn
      obtain ⟨_,hl,ht⟩ := Finset.mem_filter.mp hl
      exact no ⟨l,q,(ht p r (by simp) hp').trans hpq,by simp [hl],hq⟩
    simp only [adjacentBlockRoot,ite_eq_right pair,hz,Nat.zero_le]

/-- A relation between the right-pair words lifts across a projection whose kernel
is generated by cuts with a black before the distinguished red. Cutting each lifted
coefficient to its prescribed corners preserves its projection and the relation. -/
theorem exists_rightPairRelation_lift_of_blackBeforeCuts
    {D E : Type*} [Ring D] [Algebra k D] [Ring E]
    (φ : KLRAlgebra k (stendhalQ Q Λ) μ →ₐ[k] D) (surj : Function.Surjective φ)
    (π : D →+* E) (surjπ : Function.Surjective π)
    (S : Set (Seq μ)) (ker : TwoSidedIdeal.ker π = TwoSidedIdeal.span
       ((fun v => φ (e v)) '' S))
    (hQ : KLRSymm Q) (s t : Seq μ) (p : ℕ) (hp : p+2<n) (b : Fin ℓ)
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (blacks : ∀ a, (s.lbl a).isLeft → a = ⟨p+1,by omega⟩ ∨ a = ⟨p+2,hp⟩)
    (before : ∀ v ∈ S, ∃ l r, l<r ∧ (v.lbl l).isLeft ∧ v.lbl r = .inr b)
    (x : Bool → E) :
    let u := fun i => wordProd n (rightPairWord p i) • s
    let leg := fun i => φ (ψw (rightPairWord p i)*e s)
    (∀ i, π (φ (e t))*x i*π (φ (e (u i)))=x i) →
    (∑ i, x i*π (leg i))=0 →
    ∃ c : Bool → D, (∀ i, φ (e t)*c i*φ (e (u i))=c i) ∧
      (∀ i, π (c i)=x i) ∧ (∑ i, c i*leg i)=0 := by
  intro u leg support hzero
  let T := (fun v => φ (e v)) '' S
  have idem (a : D) (ha : a ∈ T) : a*a=a := by
    obtain ⟨v,_,rfl⟩ := ha
    rw [← map_mul,e_mul_self]
  have generate (a : D) (ha : a ∈ T) (z : D) : ∃ c : Bool → D,
      a*z*φ (e s)=∑ i, c i*leg i := by
    obtain ⟨v,hv,rfl⟩ := ha
    exact exists_rightPairColumn_coefficients_of_black_before Q Λ φ surj hQ s v p hp b hb
      blacks (before v hv) z
  have right (i : Bool) : leg i*φ (e s)=leg i := by
    simp only [leg,← map_mul,mul_assoc,e_mul_self]
  obtain ⟨w,hw,he⟩ := exists_exitRelation_lift_of_idempotentSpan π surjπ T ker
    (φ (e s)) leg idem generate right x hzero
  have left (i : Bool) : φ (e (u i))*leg i=leg i := by
    simp only [u,leg,← map_mul]
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  refine ⟨fun i => φ (e t)*w i*φ (e (u i)), fun i => ?_, fun i => ?_, ?_⟩
  · have idm (v : Seq μ) : φ (e v)*φ (e v)=φ (e v) := by rw [← map_mul,e_mul_self]
    calc
      _ = (φ (e t) * φ (e t)) * w i * (φ (e (u i)) * φ (e (u i))) := by
        simp only [mul_assoc]
      _ = _ := by rw [idm, idm]
  · simpa only [map_mul,hw] using support i
  · simp only [mul_assoc, left]
    rw [← Finset.mul_sum,he,mul_zero]

/-- For a pair last in the upper red order, with both black strands next to its
right red at the bottom, a supported relation lifts through both the higher
and globally violated quotients. -/
theorem exists_rightPairRelation_affine_lift_of_lastPairHigher
    (hQ : KLRSymm Q) (s t : Seq μ) (p : ℕ) (hp : p+2<n) (a b : Fin ℓ)
    (L : List (Fin ℓ)) (order : redWord t = L ++ [a,b])
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (blacks : ∀ j, (s.lbl j).isLeft → j = ⟨p+1,by omega⟩ ∨ j = ⟨p+2,hp⟩) :
    let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
    let q := J.ringCon.mk'
    let raw := ofKLR k Q Λ ν
    let m := violMk k Q Λ ν
    let u := fun i => wordProd n (rightPairWord p i) • s
    let leg := fun i => raw (ψw (rightPairWord p i)*e s)
    ∀ x : Bool → J.ringCon.Quotient,
      (∀ i, q (m (raw (e t)))*x i*q (m (raw (e (u i))))=x i) →
      (∑ i, x i*q (m (leg i)))=0 →
      ∃ c : Bool → BraidedStendhalAlgebra k Q Λ ν,
        (∀ i, raw (e t)*c i*raw (e (u i))=c i) ∧
        (∀ i, q (m (c i))=x i) ∧ (∑ i, c i*leg i)=0 := by
  intro J q raw m u leg x support hzero
  let φ := m.comp raw
  have sur : Function.Surjective φ :=
    (violMk_surjective (Q := Q) (Λ := Λ)).comp (ofKLR_surjective (Q := Q) (Λ := Λ))
  let S : Set (Seq μ) := {v | redWord v=redWord t ∧ adjacentBlockRoot a b t<adjacentBlockRoot a b v}
  have hker : TwoSidedIdeal.ker q = TwoSidedIdeal.span ((fun v => φ (e v)) '' S) := by
    change TwoSidedIdeal.ker J.ringCon.mk' = _
    rw [TwoSidedIdeal.ker_ringCon_mk']
    apply congrArg TwoSidedIdeal.span
    ext y
    constructor
    · rintro ⟨v, hv, hh, he⟩
      exact ⟨v, ⟨hv,hh⟩, he.symm⟩
    · rintro ⟨v, ⟨hv,hh⟩, he⟩
      exact ⟨v,hv,hh,he.symm⟩
  obtain ⟨z,zSupport,zEval,zZero⟩ := exists_rightPairRelation_lift_of_blackBeforeCuts Q Λ φ sur
    q (RingCon.mk'_surjective _) S hker hQ s t p hp b hb blacks
    (fun v hv => exists_black_before_red_of_higherLastPairCut v a b L (hv.1.trans order) _ hv.2)
    x support hzero
  let T : Set (Seq μ) := {v | IsViolated v}
  have hker' : TwoSidedIdeal.ker m.toRingHom = TwoSidedIdeal.span ((fun v => raw (e v)) '' T) := by
    change TwoSidedIdeal.ker (violIdeal k Q Λ ν).ringCon.mk' = _
    rw [TwoSidedIdeal.ker_ringCon_mk']
    apply congrArg TwoSidedIdeal.span
    ext y
    constructor
    · rintro ⟨v, hv, he⟩
      exact ⟨v,hv,he.symm⟩
    · rintro ⟨v,hv,he⟩
      exact ⟨v,hv,he.symm⟩
  obtain ⟨c,cSupport,cEval,cZero⟩ := exists_rightPairRelation_lift_of_blackBeforeCuts Q Λ raw
    (ofKLR_surjective (Q := Q) (Λ := Λ)) m.toRingHom (violMk_surjective (Q := Q) (Λ := Λ))
    T hker' hQ s t p hp b hb blacks (fun v hv => exists_black_before_red_of_isViolated v b hv)
    z zSupport zZero
  refine ⟨c,cSupport,fun i => ?_,cZero⟩
  rw [show m (c i)=z i from cEval i, zEval]

end Categorification.Stendhal.BraidedStendhalAlgebra


