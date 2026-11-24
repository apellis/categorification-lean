/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotStableBottom

/-!
# Flag detection at the left extreme over every bottom

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The two extreme PBW words have the same stable suffix, followed by either
the identity or a black divided difference. When its stable suffix passes
through the left violated edge the whole corner vanishes. In the remaining
cases the two polynomial tests determine the diagram in the violated quotient.
-/

noncomputable section
namespace Categorification.Stendhal.FiveSlotFlag
open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv BraidedStendhalAlgebra

local notation "N" => weight.card
local notation "E₀" => fixedTopFourExitCut 0
local notation "i₁" => (⟨1,by decide⟩ : Fin N)
local notation "i₂" => (⟨2,by decide⟩ : Fin N)
variable {k : Type} [CommRing k]
local notation "P" => MvPolynomial (Fin N) k
variable {D : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k}

/-- The word action of a stable path with unit crossing coefficients. -/
theorem wordComp_of_unitPath
    (hu : ∀ i j, unitLabels i j=true → D i j=1)
    (s : Seq weight) (l : List ℕ) (hl : unitPath s l=true) (p : P) :
    wordComp D l s p=rename (wordProd N l) p := by
  induction l with
  | nil => simp [wordComp,wordProd]
  | cons j l ih =>
    by_cases hj : j+1<N
    · rw [unitPath, dite_eq_left hj,Bool.and_eq_true] at hl
      let t := wordProd N l • s
      have neq : t.lbl ⟨j,by omega⟩ ≠ t.lbl ⟨j+1,hj⟩ := by
        intro h
        have hfalse (c : Unit ⊕ Fin 3) : unitLabels c c=false := by cases c <;> simp [unitLabels]
        change unitPath s l=true ∧ unitLabels (t.lbl _) (t.lbl _)=true at hl
        rw [h,hfalse] at hl
        exact Bool.noConfusion hl.2
      rw [wordComp,dite_eq_left hj,LinearMap.comp_apply,ih hl.1,crossComp,ite_eq_right neq,hu _ _ hl.2,
        map_one,LinearMap.comp_apply,LinearMap.mulLeft_apply,one_mul,AlgHom.toLinearMap_apply,
        rename_rename,wordProd_cons]
      rfl
    · simp only [unitPath,dite_eq_right hj] at hl
      contradiction

variable (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "C₀" => Λ 0 ()
local notation "I₀" => TwoBlackFlag.ideal (k := k) i₁ i₂ C₀ C₀

/-- When a black precedes spectator zero, the stable word has a violated cut. -/
theorem stableBottomWord_killed_of_black_before_spectator (s : Seq weight) (hs : 0 ∉ redsBefore s (firstBlack s)) :
    F (ψw (stableBottomWord s)*e s)=0 := by
  let l := firstBlackWord s
  let t := wordProd N l • s
  have cut : (e t : R)*(ψw l*e s)=ψw l*e s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have kill : F (ψw l*e s)=0 := by
    rw [← cut,map_mul,show F (e t)=0 from violMk_e (firstBlackWord_violated s),zero_mul]
  rw [stableBottomWord,ite_eq_right hs,ψw_append,mul_assoc,map_mul,kill,mul_zero]

/-- A variable-polynomial tested on a supported bottom input. -/
theorem eval_supported_term
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (s t : Seq weight) (l : List ℕ) (ht : wordProd N l • s=t) (f p : P) :
    polyRep hPQ (pol f*(ψw l*e s)) (Pi.single s p) t=f*wordComp D l s p := by
  have cut : opE s (Pi.single s p)=Pi.single s p := by
    funext u
    rw [opE_apply]
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  rw [map_mul,map_mul,polyRep_pol,polyRep_ψw,polyRep_e,Module.End.mul_apply,Module.End.mul_apply,
    cut,opMul_apply,opΨw_single,ht,Pi.single_eq_same]

/-- At the left-extreme cut, membership of the raw polynomial action in the
flag ideal reflects vanishing in the actual diagram quotient for every bottom
loading. Two black tests suffice, and earlier black strands force vanishing. -/
theorem extreme_eq_zero_of_flagEvaluation (hQ : KLRSymm Q)
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (hu : ∀ i j, unitLabels i j=true → D i j=1)
    (s : Seq weight) (z : R) (zl : e E₀*z=z) (zr : z*e s=z)
    (test : ∀ p : P, blackEval E₀ (polyRep hPQ z (Pi.single s p) E₀) ∈ I₀) :
    F z=0 := by
  let l := stableBottomWord s
  let w := wordProd N l
  have top : w • s=E₀ := stableBottomWord_top s
  have flip : sadj N 1 • E₀=E₀ := by decide
  have top' : wordProd N (1::l) • s=E₀ := by rw [wordProd_cons,mul_smul,top,flip]
  have diff : w≠wordProd N (1::l) := by
    intro eq
    have h := congrArg (fun p : Perm (Fin N) => p (firstBlack s)) eq
    change w (firstBlack s)=sadj N 1 (w (firstBlack s)) at h
    rw [show w (firstBlack s)=i₁ from stableBottomWord_first s] at h
    exact (by decide : i₁≠sadj N 1 i₁) h
  obtain ⟨f,g,hfg⟩ := exists_two_corner_coefficients_of_words (stendhalQ_symm Q Λ hQ) s E₀
    l (1::l) (stableBottomWord_reduced s) (stableBottomWord_flip_reduced s) diff
    (stableBottomWord_matching s) z zl zr
  by_cases good : 0 ∈ redsBefore s (firstBlack s)
  · have unit (p : P) := wordComp_of_unitPath hu s l (stableBottomWord_unit s good) p
    have flipped (p : P) : wordComp D (1::l) s p=ddiff i₁ i₂ (rename w p) := by
      rw [wordComp,dite_eq_left (by decide : 1+1<N),LinearMap.comp_apply,top,unit,crossComp,
        ite_eq_left (by decide)]
    have rows (p : P) : blackEval E₀ (f*rename w p+g*ddiff i₁ i₂ (rename w p)) ∈ I₀ := by
      have h := test p
      rw [hfg,map_add (polyRep hPQ),LinearMap.add_apply,Pi.add_apply,
        eval_supported_term Q Λ hPQ s E₀ l top,eval_supported_term Q Λ hPQ s E₀ (1::l) top',unit,flipped] at h
      exact h
    have hne : i₁≠i₂ := by decide
    have dd1 : ddiff i₁ i₂ (1 : P)=0 := ddiff_eq_zero_of_rename_eq hne (map_one _)
    have hf : blackSubst E₀ f∈I₀ := by
      change blackEval E₀ f∈I₀
      simpa only [map_one,dd1,mul_zero,mul_one,add_zero] using rows 1
    have hg : blackSubst E₀ g∈I₀ := by
      have h := rows (X (firstBlack s))
      rw [rename_X,show w (firstBlack s)=i₁ from stableBottomWord_first s,ddiff_X_left hne,mul_one,
        map_add (blackEval E₀),map_mul (blackEval E₀),blackEval_X,ite_eq_left (by decide)] at h
      change blackSubst E₀ f*X i₁+blackSubst E₀ g∈I₀ at h
      exact (add_sub_cancel_left _ _ : (blackSubst E₀ f*X i₁+blackSubst E₀ g)-
         blackSubst E₀ f*X i₁=blackSubst E₀ g) ▸
        (I₀).sub_mem h ((I₀).mul_mem_right (X i₁) hf)
    have kill (a : P) (h : blackSubst E₀ a∈I₀) (v : List ℕ) (hv : wordProd N v • s=E₀) :
        F (pol a*(ψw v*e s))=0 := by
      have cut : (e E₀ : R)*(ψw v*e s)=ψw v*e s := by
        rw [← hv,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
      rw [← cut,← mul_assoc,map_mul,fiveSlotLeftExtreme_flagIdeal_kills_blackSubst Q Λ hQ h,zero_mul]
    rw [hfg,map_add,kill _ hf l top,kill _ hg _ top',add_zero]
  · have z₀ : F (ψw l*e s)=0 := stableBottomWord_killed_of_black_before_spectator Q Λ s good
    have z₁ : F (ψw (1::l)*e s)=0 := by rw [ψw_cons,mul_assoc,map_mul,z₀,mul_zero]
    rw [hfg,map_add,map_mul F (pol f),map_mul F (pol g),z₀,z₁,mul_zero,mul_zero,add_zero]

end Categorification.Stendhal.FiveSlotFlag
