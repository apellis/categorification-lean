/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.QStrongRestrict
import Categorification.TwoRep.WordBounded

/-!
# The boundedness hypothesis (BB_w) for `Q`-strong 2-representations

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3. For `sl₂` the hypothesis (BB_w) (`StrongSl2.BBw`,
`Categorification.TwoRep.WordBounded`) bounds below the graded Hom spaces between words in `E`
and `F`; under it CL Proposition 3.9 holds (`StrongSl2.BBw.adjHyp`). For a `Q`-strong
2-representation of `g` (CL Definition 1.2) the hypothesis is the same for words in all the
`E_i 1_λ` and `1_λ F_i`. It restricts to (BB_w) of every `α_i`-string (`QStrong.toStrongSl2`),
since the words of the string are words of the `Q`-strong 2-representation.

## Main declarations

* `QStrong.Word S x y U`: `U : obj x ⟶ obj y` is a composite of identities, `E_i 1_λ` and
  `1_λ F_i`;
* `QStrong.BBw S`: (BB_w) for `S`;
* `QStrong.word_of_toStrongSl2`, `QStrong.BBw.toStrongSl2`: restriction to an `α_i`-string.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open QuantumGroup QuantumGroup.UDot

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

/-- **Words in the `E_i`, `F_i`**: the 1-morphisms `obj x ⟶ obj y` obtained from identities, the
`E_i 1_λ` and the `1_λ F_i` (all labels `i`) by composition, with any bracketing. -/
inductive Word (S : QStrong B C RD k Q) : ∀ x y : X, (S.obj x ⟶ S.obj y) → Prop
  | id (x : X) : Word S x x (𝟙 (S.obj x))
  | E (i : I) {x y : X} (h : x + RD.iX i = y) : Word S x y (S.E i h)
  | F (i : I) {x y : X} (h : x + RD.iX i = y) : Word S y x (S.F i h)
  | comp {x y z : X} {U : S.obj x ⟶ S.obj y} {V : S.obj y ⟶ S.obj z} :
      Word S x y U → Word S y z V → Word S x z (U ≫ V)

/-- **The hypothesis (BB_w)** for a `Q`-strong 2-representation: the graded Hom spaces between
words in the `E_i`, `F_i` with the same source and target are bounded below (`HomBddBelow`;
under `HomFinite` this is the vanishing of `Hom(U, V⟨d⟩)` for `d ≪ 0`, with a bound for each
pair). This is an additional hypothesis, not part of CL Definition 1.2 (see
`StrongSl2.BBw`). -/
def BBw (S : QStrong B C RD k Q) : Prop :=
  ∀ ⦃x y : X⦄ ⦃U V : S.obj x ⟶ S.obj y⦄, S.Word x y U → S.Word x y V → HomBddBelow k U V

variable (S : QStrong B C RD k Q) (i : I) (hi : C.dot i i = 2) (l₀ : X)

/-- A word of the restriction of `S` to the `α_i`-string through `λ₀` is a word of `S`. -/
theorem word_of_toStrongSl2 {r s : ℤ}
    {U : (S.toStrongSl2 i hi l₀).obj r ⟶ (S.toStrongSl2 i hi l₀).obj s}
    (h : (S.toStrongSl2 i hi l₀).Word r s U) :
    S.Word (l₀ + r • RD.iX i) (l₀ + s • RD.iX i) U := by
  induction h with
  | id r => exact Word.id _
  | E r => exact Word.E i (string_add i l₀ r)
  | F r => exact Word.F i (string_add i l₀ r)
  | comp _ _ ih₁ ih₂ => exact Word.comp ih₁ ih₂

variable {S} in
/-- **(BB_w) restricts to the `α_i`-strings**: under (BB_w) for `S`, every restriction of `S` to
an `α_i`-string with `(α_i, α_i) = 2` satisfies (BB_w) in the sense of `StrongSl2.BBw`. -/
theorem BBw.toStrongSl2 (hS : S.BBw) : (S.toStrongSl2 i hi l₀).BBw :=
  fun _ _ _ _ hU hV => hS (word_of_toStrongSl2 S i hi l₀ hU) (word_of_toStrongSl2 S i hi l₀ hV)

end QStrong

end Categorification.TwoRep
