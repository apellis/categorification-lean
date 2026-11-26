/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.Spanning
import Categorification.KLR.InductionFree

/-!
# Spanning `1_j R(ν) 1_i` with the dots on top

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121, Theorem 2.5 (spanning half), with the dots placed above the crossings: for any
choice of reduced words `ρ w`, the elements `x^u ψ_{ρ w} 1_i` with `w • i = j` span
`1_j R(ν) 1_i`. This is the reflection of `KLRAlgebra.mem_span_corner'` in a horizontal line
and needs no hypothesis on `Q`.

## Main results

* `KLRAlgebra.mem_span_corner_dotsTop`.
-/

namespace Categorification.KLR

open TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

namespace KLRAlgebra

local notation "m" => Multiset.card μ

/-- **KL I, Theorem 2.5 (spanning of `1_j R(ν) 1_i`), dots on top**: for any choice of reduced
words `ρ w`, every `r = 1_j r 1_i` lies in the span of the `x^u ψ_{ρ w} 1_i` with
`w • i = j`. -/
theorem mem_span_corner_dotsTop (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (i j : Seq μ)
    {r : KLRAlgebra k Q μ} (hr : e j * r * e i = r) :
    r ∈ Submodule.span k {b : KLRAlgebra k Q μ | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ),
      w • i = j ∧ pol (monomial u 1) * ψw (ρ w) * e i = b} := by
  have hr' : e i * hflip r * e j = hflip r := by
    rw [← hflip_e_mul_mul_e, hr]
  have hmem := mem_span_corner' (revWord ρ) (revWord_spec ρ hρ) j i hr'
  have himg := Submodule.mem_map_of_mem (f := (hflipEquiv k Q μ).toLinearMap) hmem
  rw [Submodule.map_span] at himg
  simp only [LinearEquiv.coe_coe, hflipEquiv_apply, hflip_hflip] at himg
  refine Submodule.span_mono ?_ himg
  rintro _ ⟨_, ⟨w, u, hw, rfl⟩, rfl⟩
  refine ⟨w⁻¹, u, by rw [← hw, inv_smul_smul], ?_⟩
  simp only [hflip_mul, hflip_e, hflip_pol, hflip_ψw, revWord, List.reverse_reverse]
  rw [← mul_assoc (e j), (e_commute_pol _ _).eq, mul_assoc (pol _) (e j), e_mul_ψw, (hρ _).2,
    inv_inv, hw, mul_assoc]

end KLRAlgebra

end Categorification.KLR
