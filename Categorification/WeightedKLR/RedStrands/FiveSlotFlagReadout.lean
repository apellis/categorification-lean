/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagSource
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep

/-!
# Flag polynomial tests on the two central exit words

For Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21), the
ordinary and reversed middle exits read an input polynomial and its black
divided difference. Testing on one and on the first black dot distinguishes
the two upper coefficients. The only remaining input here is descent of the
flag test action through the globally violated quotient.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra PolyRep MvPolynomial TypeA Equiv TwoBlackFlag
variable {k : Type} [CommRing k]
  {D : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k} (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "P" => MvPolynomial (Fin N) k
local notation "bot" => fixedTopFourExitBottom
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "a₁" => (⟨1,by decide⟩ : Fin N)
local notation "a₂" => (⟨2,by decide⟩ : Fin N)
local notation "a₃" => (⟨3,by decide⟩ : Fin N)
local notation "a₄" => (⟨4,by decide⟩ : Fin N)

private theorem cross_one (s : Seq μ₀) (j : ℕ) (h : j+1<N)
    (unequal : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+1,h⟩)
    (unit : D (s.lbl ⟨j,by omega⟩) (s.lbl ⟨j+1,h⟩)=1) (p : P) :
    crossComp D j h s p = rename (sadj N j) p := by
  simp only [crossComp,unequal,↓reduceIte,unit,map_one,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply,one_mul]

private theorem flag_word_three
    (hrb : D (.inr 2) (.inl ())=1) (hbr : D (.inl ()) (.inr 1)=X 1^(Λ 1 ()))
    (hrr : D (.inr 2) (.inr 1)=1) (p : P) :
    wordComp D [2,3,1] bot p = (X a₄)^(Λ 1 ()) * rename (wordProd N [2,3,1]) p := by
  let s₁ := wordProd N [1] • bot
  let s₃ := wordProd N [3,1] • bot
  have h₁ : ∀ z : P, crossComp D 1 (by decide) bot z=rename (sadj N 1) z := by
    apply cross_one bot 1 (by decide) (by decide)
    exact hrb
  have h₃ (z : P) : crossComp D 3 (by decide) s₁ z = X a₄^(Λ 1 ())*rename (sadj N 3) z := by
    have l : s₁.lbl a₃=.inl () := by decide
    have r : s₁.lbl a₄=.inr 1 := by decide
    simp only [crossComp,l,r,reduceCtorEq,↓reduceIte,hbr,map_pow,rename_X,Matrix.cons_val_one,
      Matrix.cons_val_zero,LinearMap.comp_apply,LinearMap.mulLeft_apply,AlgHom.toLinearMap_apply]
  have h₂ : ∀ z : P, crossComp D 2 (by decide) s₃ z = rename (sadj N 2) z := by
    apply cross_one s₃ 2 (by decide) (by decide)
    exact hrr
  simp only [wordComp,show 3+1<N by decide,show 2+1<N by decide,show 1+1<N by decide,
    ↓reduceDIte,LinearMap.comp_apply,LinearMap.id_apply,wordProd_nil,one_smul]
  rw [h₁,h₃,h₂,map_mul,map_pow,rename_X,show sadj N 2 a₄=a₄ by decide,
    rename_rename,rename_rename]
  rfl

private theorem flag_word_four (p : P) :
    wordComp D [2,3,1,2] bot p = wordComp D [2,3,1] bot (ddiff a₂ a₃ p) := by
  have h (z : P) : crossComp D 2 (by decide) bot z = ddiff a₂ a₃ z := by
    rw [crossComp,ite_eq_left (by decide)]
  simp only [wordComp,show 3+1<N by decide,show 2+1<N by decide,show 1+1<N by decide,
    ↓reduceDIte,LinearMap.comp_apply,LinearMap.id_apply,wordProd_nil,one_smul,h]
  rw [show wordProd N [2] • bot=bot by decide,show wordProd N [1,2] • bot=wordProd N [1] • bot by decide,
    show wordProd N [3,1,2] • bot=wordProd N [3,1] • bot by decide]

variable (Q : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "w" => wordProd N [3,2]
local notation "w₁" => wordProd N [2,3,1]
local notation "d₀" => Λ 1 ()+Λ 2 ()
local notation "J₁" => TwoBlackFlag.ideal (k := k) a₁ a₄ (Λ 0 ()) (Λ 0 ()+d₀)
local notation "σ" => fun f : P => swapPol 3 (by decide : 3+1<N) (swapPol 2 (by decide : 2+1<N) f)
local notation "q" => (X a₄ : P)^(Λ 2 ())
local notation "L" => fun (l : List ℕ) => (ψw l*e bot : R)

private theorem tested_term
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (f p : P) (l : List ℕ) (ht : wordProd N l • bot=v₁) :
    polyRep hPQ (pol f*L l) (Pi.single bot p) v₁ = f*wordComp D l bot p := by
  have cut : opE bot (Pi.single bot p)=Pi.single bot p := by
    funext s
    rw [opE_apply]
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  rw [map_mul,map_mul,polyRep_pol,polyRep_ψw,polyRep_e,Module.End.mul_apply,
    Module.End.mul_apply,cut,opMul_apply,opΨw_single,ht,Pi.single_eq_same]

private theorem black_sigma (f : P) :
    blackEval v₁ (σ f)=rename w (blackSubst v₀ f) := by
  have perm : σ f=rename w f := by change rename _ (rename _ f)=_; rw [rename_rename]; rfl
  rw [perm,← show w • v₀=v₁ by decide,blackEval_rename_perm]
  rfl

/-- The ordinary middle exit reads the test polynomial and the reversed
middle exit reads its black divided difference. Both include the dot power
of the first exchanged red. -/
theorem fiveSlotCentral_flagRows_eval
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (hrb : D (.inr 2) (.inl ())=1) (hbr : D (.inl ()) (.inr 1)=X 1^(Λ 1 ()))
    (hrr : D (.inr 2) (.inr 1)=1) (f g p : P) :
    polyRep hPQ (pol f*L [2,3,1]+pol g*L [2,3,1,2]) (Pi.single bot p) v₁ =
      f*((X a₄)^(Λ 1 ())*rename w₁ p)+g*((X a₄)^(Λ 1 ())*rename w₁ (ddiff a₂ a₃ p)) := by
  simp only [map_add,LinearMap.add_apply,Pi.add_apply,tested_term Λ Q hPQ _ _ [2,3,1] (by decide),
    tested_term Λ Q hPQ _ _ [2,3,1,2] (by decide),flag_word_four,flag_word_three Λ hrb hbr hrr]

/-- On this corner it suffices that the oriented KLR polynomial action of
globally violated elements vanish in the upper two-black flag quotient. -/
theorem fiveSlotCentral_rowReflection_of_flagAction
    (hQ : KLRSymm Q)
    (hPQ : ∀ a b, a≠b → stendhalQ Q Λ a b=D b a*rename ![1,0] (D a b))
    (hrb : D (.inr 2) (.inl ())=1) (hbr : D (.inl ()) (.inr 1)=X 1^(Λ 1 ()))
    (hrr : D (.inr 2) (.inr 1)=1)
    (desc : ∀ z : R, F z=0 → ∀ p : P, blackEval v₁ (polyRep hPQ z (Pi.single bot p) v₁) ∈ J₁) :
    FiveSlotCentralRowReflection Q Λ := by
  apply fiveSlotCentral_rowReflection_of_flagTests Q Λ hQ
  intro f g hz
  have terms (p : P) := desc _ hz p
  have eqRows (p : P) :
      blackEval v₁ (σ f*q*((X a₄)^(Λ 1 ())*rename w₁ p)+
        σ g*q*((X a₄)^(Λ 1 ())*rename w₁ (ddiff a₂ a₃ p))) ∈ J₁ := by
    have r := terms p
    rw [fiveSlotCentral_flagRows_eval Λ Q hPQ hrb hbr hrr] at r
    exact r
  have b₁ : blackEval (k := k) v₁ (X a₁)=X a₁ := by rw [blackEval_X,ite_eq_left (by decide)]
  have b₄ : blackEval (k := k) v₁ (X a₄)=X a₄ := by rw [blackEval_X,ite_eq_left (by decide)]
  have diff : a₂ ≠ a₃ := by decide
  have dd1 : ddiff a₂ a₃ (1 : P)=0 := ddiff_eq_zero_of_rename_eq diff (map_one _)
  constructor
  · have r := eqRows 1
    simp only [map_one,dd1,map_zero,mul_one,mul_zero,add_zero,map_mul,map_pow,
      black_sigma,b₄] at r
    convert r using 1
    rw [pow_add]; ring
  · have r := eqRows (X a₂)
    simp only [ddiff_X_left diff,map_one,mul_one,rename_X,show w₁ a₂=a₁ by decide,
      map_add,map_mul,map_pow,black_sigma,b₁,b₄] at r
    convert r using 1
    simp only [map_add,map_mul,rename_X,show w a₁=a₁ by decide,pow_add]
    ring

end Categorification.Stendhal.BraidedStendhalAlgebra
