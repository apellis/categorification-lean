/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralTop

/-!
# The two polynomial rows of the central principal higher ideal

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
Left multiplication from the left extreme to the central top uses the
word `[3,2]`. It multiplies each of the two PBW components on the fixed
exchanged bottom by the weight power of the rightmost black dot.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MvPolynomial Equiv
variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "Sparam" => stendhalQ Q Λ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ₀
local notation "V" => ViolQuotient k Q Λ ν₀
local notation "P" => MvPolynomial (Fin N) k
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "bot" => fixedTopFourExitBottom
local notation "F" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "L" => fun (l : List ℕ) => (ψw l*e bot : R)
local notation "σ" => fun f : P => swapPol 3 (by decide : 3+1<N) (swapPol 2 (by decide : 2+1<N) f)
local notation "q" => (X (⟨4,by decide⟩ : Fin N) : P) ^ (Λ 2 ())
local notation "c" => (ψw [3,2]*e v₀ : R)

private theorem cut_top (w : List ℕ) (v : Seq μ₀) (ht : wordProd N w • bot=v) :
    (e v : R)*L w=L w := by
  rw [← ht,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]

private theorem slide (v : Seq μ₀) (j : ℕ) (hj : j+1<N)
    (ne : v.lbl ⟨j,by omega⟩ ≠ v.lbl ⟨j+1,hj⟩) (f : P) (z : R) (hz : e v*z=z) :
    ψ j*(pol f*z)=pol (swapPol j hj f)*(ψ j*z) := by
  have sk := ψ_mul_pol_mul_e_of_ne (Q := Sparam) j hj ne f
  calc
    _ = (ψ j*pol f*e v)*z := by rw [mul_assoc _ (e v),hz,mul_assoc]
    _ = _ := by rw [sk,mul_assoc _ (e v),hz,mul_assoc]

private theorem slide_two (f : P) (w : List ℕ) (ht : wordProd N w • bot=v₀) :
    c*(pol f*L w)=pol (σ f)*L (3::2::w) := by
  let t := sadj N 2 • v₀
  have cut := e_mul_pol_ψw_e (Q := Sparam) f w bot
  rw [ht,mul_assoc] at cut
  have sk := slide Q Λ v₀ 2 (by decide) (by decide) f (L w) (cut_top Q Λ w v₀ ht)
  have cut' : (e t : R)*(ψ 2*L w)=ψ 2*L w := by
    have H := cut_top Q Λ (2::w) t (by rw [wordProd_cons,mul_smul,ht])
    simpa only [ψw_cons,mul_assoc] using H
  have sk' := slide Q Λ t 3 (by decide) (by decide) (swapPol 2 (by decide) f) (ψ 2*L w) cut'
  rw [mul_assoc _ (e v₀),cut]
  simp only [ψw_cons,ψw_nil,mul_one,mul_assoc]
  rw [sk,sk']

private theorem central_square (w : List ℕ) (hw : wordProd N w • bot=v₁) :
    (ψ 3 : R)*(ψ 3*L w)=pol q*L w := by
  have h := exit_square_word (Q := Sparam) bot w 3 (by decide)
  have hp : exitSquarePolynomial Sparam v₁ 3 (by decide)=q := by
    rw [exitSquarePolynomial,ite_eq_right (by decide),
      show (v₁).lbl ⟨3,by decide⟩=Sum.inr 2 by decide,show (v₁).lbl ⟨4,by decide⟩=Sum.inl () by decide,
      stendhalQ_inr_inl,map_pow,rename_X]
    rfl
  simpa only [hw,hp,ψw_cons,mul_assoc] using h

/-- The two left-extreme rows go to the ordinary and reversed-middle
rows with the same rightmost dot power. Relabelling the two top crossing
positions accounts for all polynomial coefficients. -/
theorem fiveSlotCentral_leftWord_rows (f g : P) :
    c*(pol f*L [3,2,1]+pol g*L [1,3,2,1])=
      pol (σ f*q)*L [2,3,1]+pol (σ g*q)*L [2,3,1,2] := by
  have E := twoBlackNearbyExitWords (Q := Sparam) 1 (by decide) bot (by decide)
  have E' := twoBlackReversedMiddleExitWords (Q₀ := Sparam) 1 (by decide) bot
    (a := 1) (b := 2) (i := ()) (j := ()) rfl rfl rfl rfl (by decide)
  have first : L [3,2,3,2,1]=pol q*L [2,3,1] := by
    have H := congrArg (ψ 3 * ·) E.1
    change ψ 3*L [2,3,2,1]=ψ 3*L [3,2,3,1] at H
    calc
      _ = ψ 3*L [2,3,2,1] := by simp only [ψw_cons,mul_assoc]
      _ = ψ 3*(ψ 3*L [2,3,1]) := by rw [H]; simp only [ψw_cons,mul_assoc]
      _ = _ := central_square Q Λ _ (by decide)
  have second : L [3,2,1,3,2,1]=pol q*L [2,3,1,2] := by
    have H := congrArg (ψ 3 * ·) E'.1
    change ψ 3*L [2,1,3,2,1]=ψ 3*L [3,2,3,1,2] at H
    calc
      _ = ψ 3*L [2,1,3,2,1] := by simp only [ψw_cons,mul_assoc]
      _ = ψ 3*(ψ 3*L [2,3,1,2]) := by rw [H]; simp only [ψw_cons,mul_assoc]
      _ = _ := central_square Q Λ _ (by decide)
  rw [mul_add,slide_two Q Λ f [3,2,1] (by decide),slide_two Q Λ g [1,3,2,1] (by decide),
    first,second,map_mul pol (σ f) q,map_mul pol (σ g) q,mul_assoc (pol (σ f)),mul_assoc (pol (σ g))]

private theorem reduced (l : List ℕ) (hv : ValidWord N l) (hlen : l.length=invCount N (wordProd N l)) : TypeA.IsReduced N l :=
  ⟨hv,by rw [length_eq_invCount]; exact hlen⟩

private theorem extreme_raw_coefficients (hQ : KLRSymm Q) (z : R)
    (hl : e v₀*z=z) (hr : z*e bot=z) :
    ∃ f g : P, z=pol f*L [3,2,1]+pol g*L [1,3,2,1] :=
  exists_two_corner_coefficients_of_words (stendhalQ_symm Q Λ hQ) bot v₀ [3,2,1] [1,3,2,1]
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide))
    (reduced _ (by simp [ValidWord,stendhalWeight]) (by decide))
    (by decide) (by decide +kernel) z hl hr

private theorem extreme_coefficients (hQ : KLRSymm Q) (y : V) (hy : F (e v₀)*y*F (e bot)=y) :
    ∃ f g : P, y=F (pol f*L [3,2,1]+pol g*L [1,3,2,1]) := by
  obtain ⟨z,hz⟩ := (violMk_surjective (Q := Q) (Λ := Λ)).comp
    (ofKLR_surjective (Q := Q) (Λ := Λ)) y
  let r : R := e v₀*z*e bot
  have lift : F r=y := by change F (e v₀*z*e bot)=y; simp only [map_mul]; rw [show F z=y from hz,hy]
  have hL : e v₀*r=r := by simp only [r,← mul_assoc,e_mul_self]
  have hR : r*e bot=r := by simp only [r,mul_assoc,e_mul_self]
  obtain ⟨f,g,hfg⟩ := extreme_raw_coefficients Q Λ hQ r hL hR
  exact ⟨f,g,lift.symm.trans (congrArg F hfg)⟩

/-- On the fixed exchanged bottom the central crossing word is left-cancellative
in the braided Stendhal algebra, for arbitrary red pairings. In the affine
PBW coordinates its only diagonal factor is a power of one variable. -/
theorem fiveSlotCentral_leftWord_cancel_braided (hQ : KLRSymm Q)
    (y : BraidedStendhalAlgebra k Q Λ ν₀)
    (hl : ofKLR k Q Λ ν₀ (e v₀)*y=y) (hr : y*ofKLR k Q Λ ν₀ (e bot)=y)
    (hz : ofKLR k Q Λ ν₀ c*y=0) : y=0 := by
  let G := toKLR k Q Λ ν₀
  have zl : (e v₀ : R)*G y=G y := by
    simpa only [G,map_mul,toKLR_ofKLR_e] using congrArg G hl
  have zr : G y*(e bot : R)=G y := by
    simpa only [G,map_mul,toKLR_ofKLR_e] using congrArg G hr
  have zero : c*G y=0 := by
    simpa only [G,map_mul,map_zero,toKLR_ofKLR_ψw,toKLR_ofKLR_e] using congrArg G hz
  obtain ⟨f,g,hfg⟩ := extreme_raw_coefficients Q Λ hQ (G y) zl zr
  rw [hfg,fiveSlotCentral_leftWord_rows] at zero
  have rows := (top_polynomial_pair_eq_zero_iff_of_words (stendhalQ_symm Q Λ hQ)
    (reduced [2,3,1] (by simp [ValidWord,stendhalWeight]) (by decide))
    (reduced [2,3,1,2] (by simp [ValidWord,stendhalWeight]) (by decide))
    (by decide) bot (σ f*q) (σ g*q)).1 zero
  have erase (a : P) (ha : σ a*q=0) : a=0 := by
    have h : σ a*q=(0 : P)*q := ha.trans (zero_mul _).symm
    rw [X_pow_eq_monomial,monomial_one_mul_cancel_right_iff] at h
    apply rename_injective _ (Equiv.swap _ _).injective
    apply rename_injective _ (Equiv.swap _ _).injective
    simpa only [map_zero] using h
  have z : G y=0 := by rw [hfg,erase f rows.1,erase g rows.2,map_zero,zero_mul,zero_mul,add_zero]
  simpa only [G,ofKLR_toKLR hQ,map_zero] using congrArg (ofKLR k Q Λ ν₀) z

/-- Reflection of zero by the two diagonal PBW rows after killing globally
violated loadings. This is the intermediate condition in the central-top
cancellation argument for Webster, Lemma 6.8 after (6.21). -/
def FiveSlotCentralRowReflection : Prop :=
  ∀ f g : P, F (pol (σ f*q)*L [2,3,1]+pol (σ g*q)*L [2,3,1,2])=0 →
      F (pol f*L [3,2,1]+pol g*L [1,3,2,1])=0

/-- For this exchanged bottom, cancellation on the left-extreme corner
is equivalent to reflection of the zero relation by the specified two
polynomial rows after global violation. -/
theorem fiveSlotCentral_leftWord_cancel_iff (hQ : KLRSymm Q) :
    (∀ y : V, F (e v₀)*y*F (e bot)=y → F c*y=0 → y=0) ↔
    FiveSlotCentralRowReflection Q Λ := by
  constructor
  · intro cancel f g hz
    apply cancel
    · have cut (a : P) (w : List ℕ) (ht : wordProd N w • bot=v₀) :
          (e v₀ : R)*(pol a*L w)*e bot=pol a*L w := by
        have fixed := e_mul_pol_ψw_e (Q := Sparam) a w bot
        rw [ht,mul_assoc] at fixed
        rw [fixed,mul_assoc,mul_assoc,e_mul_self]
      rw [← map_mul,← map_mul,mul_add,add_mul,cut _ _ (by decide),cut _ _ (by decide)]
    · rw [← map_mul,fiveSlotCentral_leftWord_rows,hz]
  · intro reflect y hy hz
    obtain ⟨f,g,rfl⟩ := extreme_coefficients Q Λ hQ y hy
    rw [← map_mul,fiveSlotCentral_leftWord_rows] at hz
    exact reflect f g hz

end Categorification.Stendhal.BraidedStendhalAlgebra
