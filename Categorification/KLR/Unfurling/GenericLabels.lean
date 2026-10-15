/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Generic

/-!
# Generic labels of the unfurled graph carry no arrows

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the strands of the representations used there carry labels
`(i, z_{i,q})` of the unfurled index set `Ĩ` (definition with label `def:tilde-I`) whose
spectral values `z` are algebraically independent over the ground field, and no two of these
labels are joined by an arrow, since `P_{ij}` is nonzero.

This file restricts the datum `ofClosure` on `Ĩ = Σ i, L ∖ {0}`, with series
`ϖ_{(i,u)}(x) = u (1 + x)^{d_i}`, to finitely many such labels, and proves that the restriction
has no arrows. Unlike `ofGeneric` (linear series `z_j + x`), this keeps Webster's series and the
units of the factorization of the full datum.

## Main definitions and results

* `UnfurlingDatum.restrict`: the restriction of a datum along an injective map of labels.
* `UnfurlingDatum.arrows_eq_zero_of_aeval_ne_zero`: there is no arrow from `j` to `j'` when
  `P_{π j', π j}` does not vanish at the constant terms of `ϖ_j`, `ϖ_{j'}`.
* `genericLabel`: the label `(π j, z_j)` of `Ĩ`.
* `genericDatum`: the restriction of `ofClosure` to the labels `genericLabel π z`, for the base
  change of polynomials `P₀` over `k` and values `z` algebraically independent over `k`;
  `genericDatum_arrows`: it has no arrows; `genericDatum_π`, `genericDatum_pw`,
  `genericDatum_unit`: its projection, series and units are those of `ofClosure`.
-/

open MvPolynomial

namespace Categorification.KLR.Unfurling

namespace UnfurlingDatum

variable {I J J' : Type*} {L : Type*} [Field L] {P : I → I → MvPolynomial (Fin 2) L}

/-- The restriction of an unfurling datum along an injective map of labels `ι : J → J'`. -/
def restrict (D : UnfurlingDatum L P J') (ι : J → J') (hι : Function.Injective ι) :
    UnfurlingDatum L P J where
  π := D.π ∘ ι
  pw := D.pw ∘ ι
  pw_coeff_one j := D.pw_coeff_one (ι j)
  pw_coeff_zero_inj _ _ h h0 := hι (D.pw_coeff_zero_inj _ _ h h0)
  arrows j j' := D.arrows (ι j) (ι j')
  arrows_of_eq j j' h := D.arrows_of_eq (ι j) (ι j') h
  unit j j' := D.unit (ι j) (ι j')
  unit_constantCoeff j j' h := D.unit_constantCoeff (ι j) (ι j') h
  factor j j' h := D.factor (ι j) (ι j') h

variable (D : UnfurlingDatum L P J') (ι : J → J') (hι : Function.Injective ι)

@[simp] theorem restrict_π (j : J) : (D.restrict ι hι).π j = D.π (ι j) := rfl

@[simp] theorem restrict_pw (j : J) : (D.restrict ι hι).pw j = D.pw (ι j) := rfl

@[simp] theorem restrict_arrows (j j' : J) :
    (D.restrict ι hι).arrows j j' = D.arrows (ι j) (ι j') := rfl

@[simp] theorem restrict_unit (j j' : J) :
    (D.restrict ι hι).unit j j' = D.unit (ι j) (ι j') := rfl

/-- **No arrow at a nonvanishing point**: if `P_{π j', π j}` does not vanish at the constant
terms of `ϖ_j` and `ϖ_{j'}`, there is no arrow from `j` to `j'` (set `x = y = 0` in the
factorization). -/
theorem arrows_eq_zero_of_aeval_ne_zero {j j' : J'}
    (h : aeval ![(D.pw j).coeff 0, (D.pw j').coeff 0] (P (D.π j') (D.π j)) ≠ 0) :
    D.arrows j j' = 0 := by
  by_cases hπ : D.π j = D.π j'
  · exact D.arrows_of_eq _ _ hπ
  by_contra hn
  apply h
  have hf := congrArg (aeval (0 : Fin 2 → L)) (D.factor j j' hπ)
  have hc : ∀ (p : Polynomial L) (i : Fin 2),
      aeval (0 : Fin 2 → L) (Polynomial.aeval (X i) p) = p.coeff 0 := fun p i => by
    rw [← Polynomial.aeval_algHom_apply, aeval_X, Pi.zero_apply,
      Polynomial.coeff_zero_eq_aeval_zero]
  rw [← AlgHom.comp_apply, comp_aeval] at hf
  simp only [map_mul, map_pow, map_sub, aeval_X, Pi.zero_apply, sub_self, zero_pow hn,
    zero_mul] at hf
  rw [← hf]
  congr 2
  funext i
  fin_cases i <;> simp [hc]

end UnfurlingDatum

section Generic

variable {I J : Type*} {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]

/-- The label `(π j, z_j)` of the unfurled index set `Σ i, L ∖ {0}`, for nonzero values `z`. -/
def genericLabel (π : J → I) (z : J → L) (hz : ∀ j, z j ≠ 0) (j : J) :
    Σ _ : I, {u : L // u ≠ 0} :=
  ⟨π j, z j, hz j⟩

theorem genericLabel_injective (π : J → I) {z : J → L} (hz : ∀ j, z j ≠ 0)
    (hinj : Function.Injective z) : Function.Injective (genericLabel π z hz) := by
  intro j j' h
  simp only [genericLabel, Sigma.mk.injEq] at h
  exact hinj (congrArg Subtype.val (eq_of_heq h.2))

variable (P₀ : I → I → MvPolynomial (Fin 2) k) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : L) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap k L) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j →
    ∃ D, (MvPolynomial.map (algebraMap k L) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)
  (π : J → I) {z : J → L} (hz : AlgebraicIndependent k z)

/-- **The unfurling datum on generic labels** (Webster, arXiv:1603.06311v3, the labels
`(i, z_{i,q})` in the proof of the theorem with label `nondegenerate`): the restriction of
`ofClosure` (series `ϖ_{(i,u)}(x) = u (1 + x)^{d_i}`, for the base change of `P₀`) to the labels
`(π j, z_j)`, `j ∈ J`, with `z` algebraically independent over `k`. -/
noncomputable def genericDatum :
    UnfurlingDatum L (fun i j => MvPolynomial.map (algebraMap k L) (P₀ i j)) J :=
  (UnfurlingDatum.ofClosure d hdpos hd hP hhom).restrict
    (genericLabel π z hz.ne_zero) (genericLabel_injective π hz.ne_zero hz.injective)

@[simp] theorem genericDatum_π (j : J) : (genericDatum P₀ d hdpos hd hP hhom π hz).π j = π j :=
  rfl

theorem genericDatum_pw (j : J) :
    (genericDatum P₀ d hdpos hd hP hhom π hz).pw j =
      Polynomial.C (z j) * (1 + Polynomial.X) ^ d (π j) :=
  rfl

/-- The constant term of `ϖ_j` is `z_j`. -/
@[simp] theorem genericDatum_pw_coeff_zero (j : J) :
    ((genericDatum P₀ d hdpos hd hP hhom π hz).pw j).coeff 0 = z j :=
  UnfurlingDatum.ofClosure_pw_coeff_zero d hdpos hd hP hhom (genericLabel π z hz.ne_zero j)

theorem genericDatum_unit (j j' : J) :
    (genericDatum P₀ d hdpos hd hP hhom π hz).unit j j' =
      (UnfurlingDatum.ofClosure d hdpos hd hP hhom).unit
        (genericLabel π z hz.ne_zero j) (genericLabel π z hz.ne_zero j') :=
  rfl

/-- **Generic labels are joined by no arrow** (Webster, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`): `P_{ij}(z, z') ≠ 0` for independent `z, z'`, provided the
polynomials `P₀ i j` over `k` are nonzero for `i ≠ j`. -/
theorem genericDatum_arrows (hP₀ : ∀ i j, i ≠ j → P₀ i j ≠ 0) (j j' : J) :
    (genericDatum P₀ d hdpos hd hP hhom π hz).arrows j j' = 0 := by
  by_cases hπ : π j = π j'
  · exact UnfurlingDatum.arrows_of_eq _ _ _ hπ
  refine UnfurlingDatum.arrows_eq_zero_of_aeval_ne_zero _ ?_
  rw [genericDatum_pw_coeff_zero, genericDatum_pw_coeff_zero, genericDatum_π, genericDatum_π,
    MvPolynomial.aeval_map_algebraMap]
  exact aeval_ne_zero_of_algebraicIndependent hz (fun e => hπ (congrArg π e))
    (hP₀ _ _ (Ne.symm hπ))

end Generic

end Categorification.KLR.Unfurling
