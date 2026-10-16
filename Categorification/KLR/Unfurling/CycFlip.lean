/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Triangular
import Categorification.KLR.Unfurling.CoverDatum

/-!
# The anti-involution `hflip ∘ σ` on the unfurled cyclotomic quotient

The left–right mirror `σ` and the top–bottom flip `hflip` of Khovanov–Lauda I
(arXiv:0803.4121v2, end of §2.1) commute. Their composite is an anti-involution of the KLR
algebra. It does not preserve the cyclotomic ideal in general: it moves the cyclotomic relation
from the first strand to the last. For the unfurled cyclotomic quotient `𝖱^Λ(ν̃) = UnfCyc D ν' M`
with no arrows and pairwise distinct labels, every strand satisfies `y_a^M = 0`
(`cycMk_pol_X_pow`), so the composite descends.

## Main results

* `cycFlip`: the anti-involution of `𝖱^Λ(ν̃)` induced by `hflip ∘ σ`.
* `cycFlip_mk`: `cycFlip (cycMk r) = cycMk (hflip (σ r))`.
* `cycFlip_mul`, `cycFlip_cycFlip`, `cycFlip_injective`.

It is the comparison `ρ` of `UnfurledEval` for the cyclotomic family, where words applied to the
vacuum carry the strands in reverse order (`CyclotomicAction.klrAct_wgen`).
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial KLRAlgebra MulOpposite

variable {I J : Type*} [DecidableEq I] [DecidableEq J] [Fintype J] {k : Type*} [Field k]
  {P : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)
  (harr : ∀ a b, D.arrows a b = 0) {ν' : Multiset J} (hnd : ν'.Nodup) (M : ℕ)

omit [DecidableEq I] [Fintype J] in
include harr hnd in
theorem cycMk_x_pow (a : Fin (Multiset.card ν')) : cycMk D ν' M (x a ^ M) = 0 := by
  rw [← cycMk_pol_X_pow D harr hnd M a, map_pow (pol (k := k)), pol_X]

/-- `hflip ∘ σ` on `𝖱(ν̃)`, followed by the quotient map, as an algebra map to the opposite
algebra of `𝖱^Λ(ν̃)`. -/
noncomputable def flipSigmaOp : UnfKLR D ν' →ₐ[k] (UnfCyc D ν' M)ᵐᵒᵖ :=
  (AlgHom.op (cycMk D ν' M)).comp
    ((flipH k _ ν').toAlgHom.comp (sigma (unfQ_klrSymm D.arrows)).toAlgHom)

omit [DecidableEq I] [Fintype J] in
theorem flipSigmaOp_apply (r : UnfKLR D ν') :
    flipSigmaOp D M r = op (cycMk D ν' M (hflip (sigma (unfQ_klrSymm D.arrows) r))) := rfl

omit [DecidableEq I] [Fintype J] in
include harr hnd in
theorem flipSigmaOp_cycElt (i : Seq ν') :
    flipSigmaOp D M (cycElt (unfQ (k := k) D.arrows) (fun _ => Polynomial.X ^ M) i) = 0 := by
  unfold cycElt
  split_ifs with h
  · rw [Polynomial.aeval_X_pow, map_mul, map_pow, flipSigmaOp_apply D M (x _), sigma_x, hflip_x,
      ← op_pow, ← map_pow, cycMk_x_pow D harr hnd M, op_zero, zero_mul]
  · exact map_zero _

/-- **The anti-involution `hflip ∘ σ` of `𝖱^Λ(ν̃)`** (no arrows, distinct labels). -/
noncomputable def cycFlip : UnfCyc D ν' M →ₗ[k] UnfCyc D ν' M :=
  (opLinearEquiv k).symm.toLinearMap ∘ₗ
    (CycKLR.lift (flipSigmaOp D M) (flipSigmaOp_cycElt D harr hnd M)).toLinearMap

omit [DecidableEq I] [Fintype J] in
theorem cycFlip_mk (r : UnfKLR D ν') :
    cycFlip D harr hnd M (cycMk D ν' M r) =
      cycMk D ν' M (hflip (sigma (unfQ_klrSymm D.arrows) r)) := by
  simp only [cycFlip, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    CycKLR.lift_mk, flipSigmaOp_apply, LinearEquiv.coe_coe, coe_opLinearEquiv_symm, unop_op]

omit [DecidableEq I] [Fintype J] in
theorem cycFlip_mul (y z : UnfCyc D ν' M) :
    cycFlip D harr hnd M (y * z) = cycFlip D harr hnd M z * cycFlip D harr hnd M y := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective y
  obtain ⟨s, rfl⟩ := CycKLR.mk_surjective z
  rw [← map_mul, cycFlip_mk, cycFlip_mk, cycFlip_mk, map_mul, hflip_mul, map_mul]

omit [DecidableEq I] [Fintype J] in
theorem cycFlip_cycFlip (y : UnfCyc D ν' M) : cycFlip D harr hnd M (cycFlip D harr hnd M y) = y := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective y
  rw [cycFlip_mk, cycFlip_mk, hflip_sigma, hflip_hflip, sigma_sigma]

omit [DecidableEq I] [Fintype J] in
theorem cycFlip_injective : Function.Injective (cycFlip D harr hnd M) :=
  Function.LeftInverse.injective (cycFlip_cycFlip D harr hnd M)

end Categorification.KLR.Unfurling
