/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Completion
import Categorification.KLR.Unfurling.Intertwine

/-!
# The unfurling homomorphism `γ`

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras* (arXiv:1603.06311v3), §3.3, Lemma label
`lem:gamma-homo`: for an unfurling datum `D` (`π : J → I`, series `ϖ_j`, factorization of `P`),
the formulas with labels `com0new`, `com0newer`, `com0newerer` define an injective homomorphism
`γ : R(ν) → ∏_{ν̃} 𝖱̂(ν̃)` into the graded completions of the unfurled KLR algebras, `ν̃`
running over the weights of `J` with `ν̃.map π = ν`.

This file defines the images of the generators in each factor, as left multiplications on the
output idempotent `e_t` (`t ∈ Seq ν̃`):

* `e_i ↦ ∑_{π ∘ t = i} e_t`;
* `x_a e_{π ∘ t} ↦ ϖ_{t_a}(y_a) e_t`;
* `ψ_j` with top labels `t` of distinct colours `↦ P°_{t_j t_{j+1}}(y_j, y_{j+1}) e_t ψ_j`;
* `ψ_j` with `t_j = t_{j+1}` `↦ h_{t_j}(y_j, y_{j+1})⁻¹ e_t ψ_j`, where
  `ϖ(x) - ϖ(y) = (x - y) h(x, y)` (Webster's `q_a`);
* `ψ_j` with `t_j ≠ t_{j+1}` of the same colour
  `↦ (ϖ_{t_j}(y_j) - ϖ_{t_{j+1}}(y_{j+1}))⁻¹ e_t (1 - ψ_j)` (Webster's `f_{a,b}` terms; the
  sign differs from the printed formula because this library's crossing acts on the polynomial
  representation by `(f - s f) / (x_j - x_{j+1})`, and the two crossing terms of the printed
  formula are combined).
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial TypeA PolyRep KLRAlgebra GradingDatum

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {k : Type*} [Field k]
  {P : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)
  {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map D.π = ν)

/-- The unfurled KLR algebra `𝖱(ν̃)`. -/
abbrev UnfKLR (ν' : Multiset J) : Type _ := KLRAlgebra k (unfQ (k := k) D.arrows) ν'

/-- Its graded completion `𝖱̂(ν̃)`. -/
abbrev UnfCompl (ν' : Multiset J) : Type _ := (unfGrading (k := k) D.arrows).completion ν'

theorem unf_degX_pos : ∀ a, 0 < (unfGrading (k := k) D.arrows).degX a :=
  fun _ => two_pos

/-- `F(y) e_t` in the completion. -/
noncomputable abbrev ser (t : Seq ν') (F : MvPowerSeries (Fin (Multiset.card ν')) k) :
    UnfCompl D ν' :=
  seriesAt (unf_degX_pos D) t F

/-- The embedding `𝖱(ν̃) → 𝖱̂(ν̃)`. -/
noncomputable abbrev toC : UnfKLR D ν' →ₐ[k] UnfCompl D ν' :=
  (unfGrading (k := k) D.arrows).toCompletion

section Positions

variable {j : ℕ} (h : j + 1 < Multiset.card ν)
include h

/-- The left position `j` in `Fin (card ν̃)`. -/
def posL : Fin (Multiset.card ν') := ⟨j, by have := lt_card_of_lt D hν h; omega⟩

/-- The right position `j + 1` in `Fin (card ν̃)`. -/
def posR : Fin (Multiset.card ν') := ⟨j + 1, lt_card_of_lt D hν h⟩

end Positions

theorem constantCoeff_pwDiff_ne_zero (a : J) :
    MvPolynomial.constantCoeff (pwDiff D a) ≠ 0 := by
  rw [constantCoeff_pwDiff]; exact D.pw_coeff_one a

/-- The image of `ψ_j` on the output summand `t`. -/
noncomputable def crossImage {j : ℕ} (h : j + 1 < Multiset.card ν) (t : Seq ν') :
    UnfCompl D ν' :=
  let a := t.lbl (posL D hν h)
  let b := t.lbl (posR D hν h)
  if hc : D.π a = D.π b then
    if hab : a = b then
      ser D t ((↑(rename ![posL D hν h, posR D hν h] (pwDiff D a)) :
          MvPowerSeries (Fin (Multiset.card ν')) k).invOfUnit
        (Units.mk0 _ (constantCoeff_pwDiff_ne_zero D a))) * toC D (ψ j)
    else
      ser D t ((↑(pwAt D.pw a (posL D hν h) - pwAt D.pw b (posR D hν h)) :
          MvPowerSeries (Fin (Multiset.card ν')) k).invOfUnit
        (Units.mk0 ((D.pw a).coeff 0 - (D.pw b).coeff 0)
          (sub_ne_zero.2 fun e => hab (D.pw_coeff_zero_inj a b hc e)))) *
        toC D (e t - ψ j)
  else
    toC D (pol (rename ![posL D hν h, posR D hν h] (D.unit a b)) * e t * ψ j)

/-- The images of the generators of `R(ν)` in the factor `𝖱̂(ν̃)`. -/
noncomputable def genImage : Gen ν → UnfCompl D ν'
  | .idem i => ∑ t with down D.π hν t = i, toC D (e t)
  | .dot a => ∑ t, toC D (pol (pwAt D.pw (t.lbl (Fin.cast (card_eq D.π hν) a))
      (Fin.cast (card_eq D.π hν) a)) * e t)
  | .cross j => if h : j + 1 < Multiset.card ν then ∑ t, crossImage D hν h t else 0

/-- The weights of `J` over `ν`. -/
abbrev Lift (ν : Multiset I) : Type _ := {ν' : Multiset J // ν'.map D.π = ν}

/-- `γ` on the free algebra. -/
noncomputable def freeGamma : FreeAlgebra k (Gen ν) →ₐ[k] ∀ ν' : Lift D ν, UnfCompl D ν'.1 :=
  FreeAlgebra.lift k fun g ν' => genImage D ν'.2 g

end Categorification.KLR.Unfurling
