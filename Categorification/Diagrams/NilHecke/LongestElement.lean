/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.NilHeckeIdempotent
import Categorification.Diagrams.NilHecke.Comparison

/-!
# Crossings along reduced words, and the idempotent `e_n`, diagrammatically

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2, Example 3: for a reduced word `a₁ ⋯ a_r` of `w ∈ S_n` the element
`∂_w = ∂_{a₁} ⋯ ∂_{a_r}` does not depend on the reduced word, it vanishes on non-reduced words,
and `e_n = x_1^{n-1} x_2^{n-2} ⋯ x_{n-1} ∂_{w_0}` (for the longest element `w_0`) is an
idempotent.

The algebraic facts are proved once, in `Categorification.Algebra.NilHecke` and
`Categorification.Algebra.NilHeckeIdempotent`; here they are transported to the endomorphism ring
of `n` strands of the diagrammatic nilHecke category along the comparison isomorphism
`endEquiv k n` (so over an integral domain `k`). The crossings along a word `ρ` are
`ψw n ρ = ψ_{ρ₀} ψ_{ρ₁} ⋯` (products are composition of operators: `ψ_{ρ₀}` is on top), the
image of `∂_ρ = NilHecke.ddw ρ`.

## Main results

* `ψw_eq_of_isReduced` : `ψ_ρ = ψ_σ` for reduced words `ρ`, `σ` of the same permutation;
  `ψw_eq_ψPerm`, with `ψPerm n w` along the canonical reduced word.
* `ψw_eq_zero_of_not_isReduced` : `ψ_ρ = 0` for a non-reduced word `ρ`.
* `ψ_mul_ψw0` : `ψ_j ψ_{w_0} = 0` for every `j`.
* `ψw0_mul_dots_mul_ψw0` : `ψ_{w_0} p ψ_{w_0} = (∂_{w_0} p) ψ_{w_0}`.
* `klIdempotent k n = x^δ ψ_{w_0}` and `klIdempotent' k n = ψ_{w_0} x^δ`, with
  `isIdempotentElem_klIdempotent`, `isIdempotentElem_klIdempotent'` (KL I §2.2, Example 3) and
  `klIdempotent_ne_zero`, `klIdempotent'_ne_zero`.
-/

noncomputable section

namespace Categorification.NilHecke.Diagram

open CategoryTheory StringDiagrams MvPolynomial Equiv TypeA

variable (k : Type*) [CommRing k] [IsDomain k]

/-! ## Crossings along words -/

/-- `ψ_ρ` does not depend on the choice of a reduced word (KL I §2.2, Example 3). -/
theorem ψw_eq_of_isReduced {n : ℕ} {ρ σ : List ℕ} (hρ : IsReduced n ρ) (hσ : IsReduced n σ)
    (h : wordProd n ρ = wordProd n σ) : ψw (k := k) n ρ = ψw n σ := by
  apply (endEquiv k n).injective
  rw [endEquiv_ψw, endEquiv_ψw]
  exact Subtype.ext (ddw_eq_of_isReduced hρ hσ h)

/-- `ψ_ρ = 0` for a word `ρ` in the generators of `S_n` which is not reduced. -/
theorem ψw_eq_zero_of_not_isReduced {n : ℕ} {ρ : List ℕ} (hv : ValidWord n ρ)
    (hr : ¬ IsReduced n ρ) : ψw (k := k) n ρ = 0 := by
  apply (endEquiv k n).injective
  rw [endEquiv_ψw, map_zero]
  exact Subtype.ext (ddw_eq_zero_of_not_isReduced hv hr)

variable (n : ℕ)

/-- The crossings `ψ_w` of a permutation `w ∈ S_n`, along the canonical reduced word. -/
def ψPerm (w : Perm (Fin n)) : End ((pres k).obj (strands n)) := ψw n (canWord n w)

theorem ψw_eq_ψPerm {ρ : List ℕ} (hρ : IsReduced n ρ) : ψw (k := k) n ρ = ψPerm k n (wordProd n ρ) :=
  ψw_eq_of_isReduced k hρ (isReduced_canWord n _) (wordProd_canWord n _).symm

theorem endEquiv_ψPerm (w : Perm (Fin n)) :
    endEquiv k n (ψPerm k n w) = ⟨ddPerm k n w, ddPerm_mem w⟩ :=
  endEquiv_ψw k n _

/-! ## The longest element -/

/-- `ψ_j ψ_{w_0} = 0` for every `j`. -/
theorem ψ_mul_ψw0 (j : ℕ) : ψ k n j * ψw n (w0Word n) = 0 := by
  apply (endEquiv k n).injective
  rw [map_mul, endEquiv_ψ, endEquiv_ψw, map_zero]
  exact Subtype.ext (dd_mul_ddw_w0Word j)

/-- `ψ_{w_0} p ψ_{w_0} = (∂_{w_0} p) ψ_{w_0}` for a polynomial `p` in the dots of the `n`
strands. -/
theorem ψw0_mul_dots_mul_ψw0 (p : MvPolynomial (Fin n) k) :
    ψw n (w0Word n) * dots k n (rename Fin.val p) * ψw n (w0Word n) =
      dots k n (rename Fin.val (ddw (w0Word n) p)) * ψw n (w0Word n) := by
  apply (endEquiv k n).injective
  simp only [map_mul, endEquiv_ψw, endEquiv_dots]
  exact Subtype.ext (ddw_w0Word_mul_mulPoly_mul_ddw_w0Word p)

/-- `x^δ = x_0^{n-1} x_1^{n-2} ⋯ x_{n-2}` in the variables of the dots (the paper's
`x_1^{n-1} ⋯ x_{n-1}`). -/
def xδ : MvPolynomial ℕ k := ∏ j ∈ Finset.range n, X j ^ (n - 1 - j)

omit [IsDomain k] in
theorem rename_xDelta : rename Fin.val (xDelta (k := k) (m := n) n) = xδ k n := by
  rw [xDelta, map_prod]
  simp only [map_pow, rename_X]
  exact Fin.prod_univ_eq_prod_range (fun j => (X j : MvPolynomial ℕ k) ^ (n - 1 - j)) n

/-- The idempotent `e_n = x^δ ψ_{w_0}` of the endomorphism ring of `n` strands (dots above
the crossings; KL I §2.2, Example 3). -/
def klIdempotent : End ((pres k).obj (strands n)) := dots k n (xδ k n) * ψw n (w0Word n)

/-- The idempotent `ψ(e_n) = ψ_{w_0} x^δ` (KL I §2.2, Example 3). -/
def klIdempotent' : End ((pres k).obj (strands n)) := ψw n (w0Word n) * dots k n (xδ k n)

theorem endEquiv_klIdempotent :
    endEquiv k n (klIdempotent k n) = ⟨idemNH k n, idemNH_mem⟩ := by
  rw [klIdempotent, map_mul, ← rename_xDelta, endEquiv_dots, endEquiv_ψw]
  rfl

theorem endEquiv_klIdempotent' :
    endEquiv k n (klIdempotent' k n) = ⟨idemNH' k n, idemNH'_mem⟩ := by
  rw [klIdempotent', map_mul, ← rename_xDelta, endEquiv_dots, endEquiv_ψw]
  rfl

/-- **KL I §2.2, Example 3, diagrammatically**: `e_n = x_1^{n-1} ⋯ x_{n-1} ∂_{w_0}` is an
idempotent of the endomorphism ring of `n` strands. -/
theorem isIdempotentElem_klIdempotent : IsIdempotentElem (klIdempotent k n) := by
  apply (endEquiv k n).injective
  rw [map_mul, endEquiv_klIdempotent]
  exact Subtype.ext (isIdempotentElem_idemNH (k := k) (m := n))

/-- **KL I §2.2, Example 3, diagrammatically**: `ψ(e_n) = ∂_{w_0} x_1^{n-1} ⋯ x_{n-1}` is an
idempotent of the endomorphism ring of `n` strands. -/
theorem isIdempotentElem_klIdempotent' : IsIdempotentElem (klIdempotent' k n) := by
  apply (endEquiv k n).injective
  rw [map_mul, endEquiv_klIdempotent']
  exact Subtype.ext (isIdempotentElem_idemNH' (k := k) (m := n))

theorem xDelta_ne_zero : xDelta (k := k) (m := n) n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (X_ne_zero a)

/-- `e_n ≠ 0`. -/
theorem klIdempotent_ne_zero : klIdempotent k n ≠ 0 := by
  intro h
  have h' := congrArg (fun e => ((endEquiv k n e : nilHecke k n) : Module.End k _)
    (xDelta (k := k) (m := n) n)) h
  simp only [endEquiv_klIdempotent, map_zero, ZeroMemClass.coe_zero, LinearMap.zero_apply,
    idemNH, Module.End.mul_apply, ddw_w0Word_xDelta, mulPoly_apply, mul_one] at h'
  exact xDelta_ne_zero k n h'

/-- `ψ(e_n) ≠ 0`. -/
theorem klIdempotent'_ne_zero : klIdempotent' k n ≠ 0 := by
  intro h
  have h' := congrArg (fun e => ((endEquiv k n e : nilHecke k n) : Module.End k _)
    (1 : MvPolynomial (Fin n) k)) h
  simp only [endEquiv_klIdempotent', map_zero, ZeroMemClass.coe_zero, LinearMap.zero_apply,
    idemNH', Module.End.mul_apply, mulPoly_apply, mul_one, ddw_w0Word_xDelta] at h'
  exact one_ne_zero h'

end Categorification.NilHecke.Diagram

end
