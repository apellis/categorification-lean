/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MixedJointKernel
import Categorification.WeightedKLR.RedStrands.BraidedEqualBlackCornerCycle

/-!
# Equal-black right-pair relations at the mixed joint

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
At the mixed fixed top the common-joint description descends through the
red-dot quotient, allowing arbitrary exterior red spectators.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "B" => BraidedStendhalAlgebra k Q Λ ν
local notation "π" => ofKLR k Q Λ ν
local notation "T" => toKLR k Q Λ ν

/-- The five local PBW words used by the mixed and full right-pair corners are reduced. -/
theorem twoBlack_joint_words_reduced {N p : ℕ} (hp : p+2<N) :
    IsReduced N [p] ∧ IsReduced N [p,p+1] ∧ IsReduced N [p+1,p,p+1] ∧
      IsReduced N [p+1] ∧ IsReduced N [p+1,p] := by
  have shift {w : List ℕ} (hw : IsReduced 3 w) : IsReduced N (shiftWord p w) := by
    have empty (k : ℕ) : IsReduced k [] := by simp [TypeA.IsReduced, ValidWord, wordProd]
    have mid := (empty p).append_shiftWord (show p+3=p+3 from rfl) hw
    have total := mid.append_shiftWord (show p+3+(N-(p+3))=N by omega) (empty (N-(p+3)))
    simpa only [List.nil_append,shiftWord,List.map_nil,List.append_nil] using total
  have one : IsReduced 3 [0] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide
  have two : IsReduced 3 [0,1] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide
  have three : IsReduced 3 [1,0,1] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide
  have right : IsReduced 3 [1] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide
  have back : IsReduced 3 [1,0] := by
    refine ⟨by simp [ValidWord], ?_⟩
    rw [length_eq_invCount]
    decide
  simpa [shiftWord] using And.intro (shift one) (And.intro (shift two)
    (And.intro (shift three) (And.intro (shift right) (shift back))))

omit [DecidableEq I] in
/-- The only nonidentity stabilizer of the mixed joint exchanges the
two black endpoints across the red strand. -/
theorem mixedJoint_stabilizer (s : Seq μ) (p : ℕ) (hp : p+2<n)
    (he : s.lbl ⟨p+1,by omega⟩=s.lbl ⟨p+2,hp⟩)
    (red : ∀ a : Fin n, a ≠ ⟨p+1,by omega⟩ → a ≠ ⟨p+2,hp⟩ → (s.lbl a).isRight)
    (w : Perm (Fin n)) :
    w • (sadj n p • s) = sadj n p • s ↔ w=1 ∨ w=wordProd n [p+1,p,p+1] := by
  let swapB := sadj n p
  let D := sadj n (p+1)
  have match' := twoBlack_return_permutations s p hp he red (swapB*w)
  have braid' : swapB*D*swapB=D*swapB*D := sadj_braid hp
  have word : wordProd n [p+1,p,p+1]=swapB*D*swapB := by
    rw [braid']; simp only [wordProd_cons,wordProd_nil,mul_one,mul_assoc,swapB,D]
  have fixed : D • s=s := sadj_smul_eq_self hp he
  constructor
  · intro h
    have back : (swapB*w) • (sadj n p • s)=s := by rw [mul_smul,h]; exact sadj_smul_smul p s
    rcases match'.mp back with h | h
    · left
      have e := congrArg (swapB * ·) h
      simpa only [wordProd_singleton,swapB,← mul_assoc,TypeA.sadj_mul_self,one_mul] using e
    · right
      have e := congrArg (swapB * ·) h
      rw [word]; simpa only [wordProd_cons,wordProd_nil,mul_one,swapB,D,← mul_assoc,TypeA.sadj_mul_self,one_mul] using e
  · rintro (rfl|rfl)
    · exact one_smul _ _
    · rw [word,mul_smul,mul_smul,show swapB • (sadj n p • s)=s from sadj_smul_smul p s,fixed]

/-- Every supported relation at the mixed top of the equal-black right pair
in the braided Stendhal algebra comes from its full joint. -/
theorem exists_mixedJoint_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq μ) (p : ℕ)
    (hp : p+2<n) (r : Fin ℓ) (i : I) (hr : s.lbl ⟨p,by omega⟩=.inr r)
    (hi : s.lbl ⟨p+1,by omega⟩=.inl i) (hi' : s.lbl ⟨p+2,hp⟩=.inl i)
    (red : ∀ a : Fin n, a ≠ ⟨p+1,by omega⟩ → a ≠ ⟨p+2,hp⟩ → (s.lbl a).isRight)
    (x y : B) :
    let t := sadj n p • s
    π (e t)*x=x → x*π (e t)=x → π (e t)*y=y → y*π (e t)=y →
    x*π (ψw [p]*e s)+y*π (ψw [p,p+1]*e s)=0 →
    ∃ c : B, c*π (e (sadj n (p+1) • t))=c ∧ c*π (ψw [p,p+1]*e t) = -x ∧ c*π (ψw [p+1]*e t)=y := by
  intro t hx hx' hy hy' rel
  have he := hi.trans hi'.symm
  have hn : s.lbl ⟨p,by omega⟩ ≠ s.lbl ⟨p+2,hp⟩ := by rw [hr,hi']; exact Sum.inr_ne_inl
  have left (z : B) (hz : π (e t)*z=z) : e t*T z=T z := by
    simpa only [map_mul,toKLR_ofKLR_e] using congrArg T hz
  have right (z : B) (hz : z*π (e t)=z) : T z*e t=T z := by
    simpa only [map_mul,toKLR_ofKLR_e] using congrArg T hz
  have sum := congrArg T rel
  simp only [map_add,map_mul,toKLR_ofKLR_e,toKLR_ofKLR_ψw,map_zero] at sum
  obtain ⟨h₁,h₂,h₃,_⟩ := twoBlack_joint_words_reduced hp
  obtain ⟨c,cut,cB,cD⟩ := KLRAlgebra.exists_mixedJoint_corner_cycle_coefficient
    (stendhalQ_symm Q Λ hQ) s p hp he hn h₁ h₂ h₃ (T x) (T y) (mixedJoint_stabilizer s p hp he red)
    (left x hx) (right x hx') (left y hy) (right y hy') sum
  refine ⟨π c,?_,?_,?_⟩
  · exact (map_mul π _ _).symm.trans (congrArg π cut)
  · rw [← map_mul,cB,map_neg,ofKLR_toKLR hQ]
  · rw [← map_mul,cD,ofKLR_toKLR hQ]

end Categorification.Stendhal.BraidedStendhalAlgebra
