/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlack

/-!
# Red strands in the double model of a Rouquier family

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25. Let `S` be a Rouquier family with
images `red r` of the red strands, and isomorphisms `F_i I^λ ≅ I^λ F_i` passing an upward black
strand through a red strand (`upIso`). These are the images of the red/up crossings `a`, `b`.
As in Webster's proof, the red/down crossings are their mates: `a′` is the mate of `a` for the
adjunction `E ⊣ F` (`downQuot`, Webster's factorization of `a′` through `E_i F_i`), and `b′`
is the mate of `b` for the adjunction `F ⊣ E` (`downDot`). Together with the images of the
black generators (`blackImg`) this gives generator images of the double signature
(`genImg`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

local notation "T" => signature RD Λ

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁))
  (Sc : CL.CLScalars C k)

/-- **The red/down crossing `a′`** (Webster, arXiv:1309.3796v3, proof of Theorem 4.25): the mate
of the red/up crossing for the adjunction `E ⊣ F`, that is,
`I^λ E_i → E_i F_i I^λ E_i → E_i I^λ F_i E_i → E_i I^λ`. -/
def downQuot (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
    (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃) :
    red r h₂ ≫ S.E i h₁ ⟶ S.E i h₄ ≫ red r h₃ :=
  (mateEquiv (S.adj i h₄) (S.adj i h₁)).symm (upIso r i h₁ h₂ h₃ h₄).hom

/-- **The red/down crossing `b′`** (Webster, arXiv:1309.3796v3, proof of Theorem 4.25): the mate
of the inverse red/up crossing for the adjunction `F ⊣ E`. -/
def downDot (r : Fin ℓ) (i : I) {μ μ₁ μ₂ μ₃ : X} (h₁ : μ + RD.iX i = μ₁)
    (h₂ : μ + Λ r = μ₂) (h₃ : μ₁ + Λ r = μ₃) (h₄ : μ₂ + RD.iX i = μ₃) :
    S.E i h₄ ≫ red r h₃ ⟶ red r h₂ ≫ S.E i h₁ :=
  mateEquiv (S.adjL i h₄) (S.adjL i h₁) (upIso r i h₁ h₂ h₃ h₄).inv

/-- The images of the mixed generators of the double signature. -/
def mixedImg : (g : X × Move I ℓ) → (a b : X) → (T).left g = a → (T).right g = b →
    (hd : (T).ok a ((T).dom g)) → (hde : (T).endR a ((T).dom g) = b) →
    (hc : (T).ok a ((T).cod g)) → (hce : (T).endR a ((T).cod g) = b) →
    ((doubleModel S red).word a ((T).dom g) b hd hde ⟶
      (doubleModel S red).word a ((T).cod g) b hc hce)
  | (z, .black s), a, b, ha, hb, hd, hde, hc, hce => blackImg S red Sc z s a b ha hb hd hde hc hce
  | (_, .redBlack r (true, i)), _, _, _, _, _, _, _, _ => (upIso r i _ _ _ _).hom
  | (_, .blackRed (true, i) r), _, _, _, _, _, _, _, _ => (upIso r i _ _ _ _).inv
  | (_, .blackRed (false, i) r), _, _, _, _, _, _, _, _ => downQuot S red upIso r i _ _ _ _
  | (_, .redBlack r (false, i)), _, _, _, _, _, _, _, _ => downDot S red upIso r i _ _ _ _

/-- **The generator images of the double signature** for a Rouquier family, images of the red
strands and red/up crossings. -/
def genImg : GenImg (doubleModel S red) where
  gen := mixedImg S red upIso Sc

/-- The generator images agree with those of `S` on the black generators. -/
theorem genImg_blackOn : BlackOn Sc (genImg S red upIso Sc) := fun _ _ _ _ _ _ _ _ _ _ => rfl

end Categorification.Stendhal.DoubleDiagram
