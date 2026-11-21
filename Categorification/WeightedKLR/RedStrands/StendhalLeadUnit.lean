/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.KLR.CyclotomicDiv

/-!
# The Kang–Kashiwara leading-coefficient condition for Stendhal parameters

S.-J. Kang and M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, Theorem 4.5 and Lemma 4.19, split the
restriction of an induced cyclotomic module for a colour `i`. The formal splitting
(`KLR.KLRAlgebra.splitMap`) needs, for every colour `j ≠ i`, that the leading coefficient of
`Q_{j,i}(x, t)` in `t` is a unit constant (`KLR.KLRAlgebra.LeadUnitAt`).

For the parameters `stendhalQ` of Webster's tensor product algebras, arXiv:1309.3796v3,
Definition 4.5, in which red strands are extra colours, this holds at every black colour
`i` as soon as it holds for the black parameters: the red-black parameter `Q_{r,i}` is the
power `t^{λ_r^i}`, with leading coefficient one. The condition fails at red colours, which
is why it is stated for one colour at a time. This is the input used in the proof of
Webster, Proposition 5.5, for the block with a single red strand.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- The leading coefficient in `t` of `t^n` is one. -/
theorem polyInY_X_one_pow (n : ℕ) :
    (polyInY (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) k)).leadingCoeff = Polynomial.C 1 := by
  nontriviality k
  simp [polyInY]

/-- The Kang–Kashiwara condition at a black colour of the Stendhal parameters. -/
theorem leadUnitAt_stendhalQ (i : I) (hQ : LeadUnitAt Q i) :
    LeadUnitAt (stendhalQ Q Λ) (.inl i) := by
  rintro (j | r) h
  · exact hQ j (fun he => h (congrArg Sum.inl he))
  · exact ⟨1, isUnit_one, polyInY_X_one_pow _⟩

end Categorification.Stendhal
