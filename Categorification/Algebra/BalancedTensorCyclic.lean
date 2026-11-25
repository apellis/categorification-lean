/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensor

/-!
# Balanced tensors with a cyclic summand

Let `M` be a right `A`-module with an `A`-linear projection `π` whose image is the cyclic
module `c A`, and let `ρ a = c a`. If `τ` is an idempotent with `c τ = c`, and the annihilator
of `c` is carried by `τ` into a subspace `H` of `A`, then for `z = τ z` in a left `A`-module `N`,
`c ⊗ z = 0` in `M ⊗_A N` forces `z` into the subspace `H N` spanned by the `h z'`, `h ∈ H`
(`BalancedTensor.mem_span_smul_of_tmul_eq_zero`). This is the identity
`(A / Ann c) ⊗_A N = N / Ann(c) N` on the summand `π M`, made explicit by the map
`x ⊗ z ↦ [τ a z]`, where `π x = c a`.

The summand `π M ⊗_A N` is the image of `c ⊗ N` (`BalancedTensor.exists_mapLeft_eq_tmul`).

This is used in the reduction of Webster, arXiv:1309.3796v2, Proposition 6.9 to two red
strands.
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

namespace BalancedTensor

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  [Algebra k A] {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [SMulCommClass A k N]

/-- The subspace of `N` spanned by `h z`, for `h ∈ H`. -/
def spanSmul (H : Submodule k A) : Submodule k N :=
  Submodule.span k {w | ∃ a ∈ H, ∃ z : N, a • z = w}

variable (τ : A) (H : Submodule k A)

/-- `(a, z) ↦ [τ a z]` in `N / H N`. -/
private def bottomAction : A →ₗ[k] N →ₗ[k] N ⧸ spanSmul (N := N) H :=
  LinearMap.mk₂ k (fun a z => Submodule.Quotient.mk ((τ * a) • z))
    (fun a a' z => by rw [mul_add, add_smul, Submodule.Quotient.mk_add])
    (fun r a z => by rw [mul_smul_comm, smul_assoc, Submodule.Quotient.mk_smul])
    (fun a z z' => by rw [smul_add, Submodule.Quotient.mk_add])
    (fun r a z => by rw [smul_comm, Submodule.Quotient.mk_smul])

variable {τ H} (ρ : A →ₗ[k] M) (hann : ∀ a, ρ a = 0 → τ * a ∈ H)

private def bottomClass : A ⧸ LinearMap.ker ρ →ₗ[k] N →ₗ[k] N ⧸ spanSmul (N := N) H :=
  (LinearMap.ker ρ).liftQ (bottomAction τ H) fun a ha =>
    LinearMap.ext fun z => (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.subset_span ⟨τ * a, hann a ha, z, rfl⟩)

variable (π : M →ₗ[k] M) (hgen : LinearMap.range π ≤ LinearMap.range ρ)

/-- The element `a` with `π x = ρ a`, modulo the kernel of `ρ`. -/
private def coefficient : M →ₗ[k] A ⧸ LinearMap.ker ρ :=
  ρ.quotKerEquivRange.symm.toLinearMap ∘ₗ π.codRestrict (LinearMap.range ρ)
    fun x => hgen (LinearMap.mem_range_self π x)

omit [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] in
private theorem coefficient_eq {x : M} {a : A} (ha : ρ a = π x) :
    coefficient ρ π hgen x = Submodule.Quotient.mk a := by
  change ρ.quotKerEquivRange.symm ⟨π x, _⟩ = _
  simp only [← ha]
  exact LinearMap.quotKerEquivRange_symm_apply_image _ _ _

variable {c : M} (hρ : ∀ a, ρ a = op a • c) (hπ : ∀ (b : A) x, π (op b • x) = op b • π x)

include hρ hπ in
private theorem balanced (x : M) (b : A) (z : N) :
    (bottomClass ρ hann ∘ₗ coefficient ρ π hgen) (op b • x) z =
      (bottomClass ρ hann ∘ₗ coefficient ρ π hgen) x (b • z) := by
  obtain ⟨a, ha⟩ := hgen (LinearMap.mem_range_self π x)
  have hb : ρ (a * b) = π (op b • x) := by
    rw [hπ, ← ha, hρ, hρ, op_mul, mul_smul]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, coefficient_eq ρ π hgen hb,
    coefficient_eq ρ π hgen ha]
  change Submodule.Quotient.mk ((τ * (a * b)) • z) = Submodule.Quotient.mk ((τ * a) • b • z)
  rw [← mul_assoc, mul_smul]

include hann hgen hρ hπ in
/-- **The kernel of tensoring with a cyclic generator.** If `π M = c A`, `c τ = c` for an
idempotent `τ`, and `τ` carries the annihilator of `c` into `H`, then `c ⊗ z = 0` with
`τ z = z` implies `z ∈ H N`. -/
theorem mem_spanSmul_of_tmul_eq_zero (hτ : IsIdempotentElem τ) (hc : ρ τ = c) (hfix : π c = c)
    {z : N} (hz : τ • z = z) (h0 : (tmul c z : BalancedTensor k B A M N) = 0) :
    z ∈ spanSmul (N := N) H := by
  have h1 := congrArg (lift (bottomClass ρ hann ∘ₗ coefficient ρ π hgen)
    (balanced ρ hann π hgen hρ hπ)) h0
  rw [lift_tmul, map_zero, LinearMap.comp_apply,
    coefficient_eq ρ π hgen (show ρ τ = π c by rw [hc, hfix])] at h1
  change Submodule.Quotient.mk ((τ * τ) • z) = 0 at h1
  rwa [hτ.eq, hz, Submodule.Quotient.mk_eq_zero] at h1

include hρ in
omit [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k A N] [SMulCommClass A k N] in
/-- The relations are killed: `c ⊗ h z = 0` for `h ∈ H` when `ρ` kills `H`. -/
theorem tmul_eq_zero_of_mem_spanSmul (hkill : ∀ a ∈ H, ρ a = 0) {z : N}
    (hz : z ∈ spanSmul (N := N) H) : (tmul c z : BalancedTensor k B A M N) = 0 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, ha, z, rfl⟩ := hw
    rw [← op_smul_tmul, ← hρ, hkill a ha, zero_tmul]
  | zero => exact tmul_zero _
  | add x y _ _ hx hy => rw [tmul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [tmul_smul, hx, smul_zero]

include hgen hρ in
omit [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k A N] [SMulCommClass A k N] in
/-- Every element of `π M ⊗_A N` is `c ⊗ z`: for every `w`, the image of `w` under `π ⊗ 1`
is an elementary tensor with `c`. Stated through any additive map `F` out of the tensor. -/
theorem exists_map_eq_tmul {P : Type*} [AddCommGroup P] (F G : BalancedTensor k B A M N →+ P)
    (hFG : ∀ x z, F (tmul x z) = G (tmul (π x) z)) (w : BalancedTensor k B A M N) :
    ∃ z : N, F w = G (tmul c z) := by
  induction w using induction_on with
  | zero => exact ⟨0, by rw [map_zero, tmul_zero, map_zero]⟩
  | tmul x z =>
    obtain ⟨a, ha⟩ := hgen (LinearMap.mem_range_self π x)
    exact ⟨a • z, by rw [hFG, ← ha, hρ, op_smul_tmul]⟩
  | add w w' hw hw' =>
    obtain ⟨z, hz⟩ := hw
    obtain ⟨z', hz'⟩ := hw'
    exact ⟨z + z', by rw [map_add, hz, hz', tmul_add, map_add]⟩

end BalancedTensor

end

end Categorification
