/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.FullJointKernel
import Categorification.WeightedKLR.RedStrands.MixedJointCycle

/-!
# Equal-black right-pair relations at the full joint

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
At the full fixed top the common-joint description descends through the
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

omit [DecidableEq I] in
/-- The two ways to reach the full joint from the mixed loading pass through
the right red/black crossing, with an optional equal-black crossing above. -/
theorem fullJoint_permutations (s : Seq μ) (p : ℕ) (hp : p+2<n)
    (he : s.lbl ⟨p+1,by omega⟩=s.lbl ⟨p+2,hp⟩)
    (red : ∀ a : Fin n, a ≠ ⟨p+1,by omega⟩ → a ≠ ⟨p+2,hp⟩ → (s.lbl a).isRight)
    (w : Perm (Fin n)) :
    let t := sadj n p • s
    w • t=sadj n (p+1) • t ↔ w=wordProd n [p+1] ∨ w=wordProd n [p,p+1] := by
  intro t
  let d := sadj n (p+1)
  have stab := mixedJoint_stabilizer s p hp he red (d*w)
  have word : wordProd n [p+1,p,p+1] = d*(sadj n p*d) := by
    simp only [wordProd_cons,wordProd_nil,mul_one,d]
  constructor
  · intro h
    have back : (d*w) • t=t := by rw [mul_smul,h]; exact sadj_smul_smul (p+1) t
    rcases stab.mp back with h | h
    · left
      have eq := congrArg (d * ·) h
      simpa only [wordProd_singleton,← mul_assoc,d,TypeA.sadj_mul_self,one_mul,mul_one] using eq
    · right
      rw [word] at h
      have eq := congrArg (d * ·) h
      simpa only [wordProd_cons,wordProd_nil,mul_one,← mul_assoc,d,TypeA.sadj_mul_self,one_mul] using eq
  · intro h
    have back : (d*w) • t=t := by
      apply stab.mpr
      rcases h with rfl | rfl
      · left; simp only [wordProd_singleton,d,TypeA.sadj_mul_self]
      · right; simp only [wordProd_cons,wordProd_nil,mul_one,d]
    have eq := congrArg (d • ·) back
    simpa only [mul_smul,d,sadj_smul_smul] using eq

/-- Every supported relation at the full top of the equal-black right pair
in the braided Stendhal algebra comes from its full joint. -/
theorem exists_fullJoint_corner_cycle_coefficient (hQ : KLRSymm Q) (s : Seq μ) (p : ℕ)
    (hp : p+2<n) (r : Fin ℓ) (i : I) (hr : s.lbl ⟨p,by omega⟩=.inr r)
    (hi : s.lbl ⟨p+1,by omega⟩=.inl i) (hi' : s.lbl ⟨p+2,hp⟩=.inl i)
    (red : ∀ a : Fin n, a ≠ ⟨p+1,by omega⟩ → a ≠ ⟨p+2,hp⟩ → (s.lbl a).isRight)
    (x y : B) :
    let t := sadj n p • s
    let F := sadj n (p+1) • t
    π (e F)*x=x → x*π (e t)=x → π (e F)*y=y → y*π (e t)=y →
    x*π (ψw [p]*e s)+y*π (ψw [p,p+1]*e s)=0 →
    ∃ c : B, c*π (e (sadj n (p+1) • t))=c ∧ c*π (ψw [p,p+1]*e t) = -x ∧ c*π (ψw [p+1]*e t)=y := by
  intro t F hx hx' hy hy' rel
  have he := hi.trans hi'.symm
  have hn : s.lbl ⟨p,by omega⟩ ≠ s.lbl ⟨p+2,hp⟩ := by rw [hr,hi']; exact Sum.inr_ne_inl
  have left (z : B) (hz : π (e F)*z=z) : e F*T z=T z := by
    simpa only [map_mul,toKLR_ofKLR_e] using congrArg T hz
  have right (z : B) (hz : z*π (e t)=z) : T z*e t=T z := by
    simpa only [map_mul,toKLR_ofKLR_e] using congrArg T hz
  have sum := congrArg T rel
  simp only [map_add,map_mul,toKLR_ofKLR_e,toKLR_ofKLR_ψw,map_zero] at sum
  obtain ⟨_,hB,h₃,hD,h₂⟩ := twoBlack_joint_words_reduced hp
  obtain ⟨c,cut,cB,cD⟩ := KLRAlgebra.exists_fullJoint_corner_cycle_coefficient
    (stendhalQ_symm Q Λ hQ) s p hp he hn hD hB h₂ h₃ (T x) (T y) (fullJoint_permutations s p hp he red)
    (left x hx) (right x hx') (left y hy) (right y hy') sum
  refine ⟨π c,?_,?_,?_⟩
  · exact (map_mul π _ _).symm.trans (congrArg π cut)
  · rw [← map_mul,cB,map_neg,ofKLR_toKLR hQ]
  · rw [← map_mul,cD,ofKLR_toKLR hQ]

end Categorification.Stendhal.BraidedStendhalAlgebra
