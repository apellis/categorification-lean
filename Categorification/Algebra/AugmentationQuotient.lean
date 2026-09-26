/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Quotients of free modules by an augmentation ideal

Let `R` be a commutative `k`-algebra over a field `k` with an augmentation `ε : R →ₐ[k] k`, and
let `M` be a free `R`-module with basis `b : ι → M`. Then `M / (ker ε) M` is a `k`-vector space
with basis the classes of the `b i` (`augQuotBasis`); in particular
`dim_k M / (ker ε) M = rank_R M` (`finrank_augQuot`).

This is used twice for Khovanov–Lauda I (arXiv:0803.4121v2):

* for `R(ν)` over its center `Sym(ν)` (free of rank `(m!)²`, Corollary 2.10), giving
  `dim_k R'(ν) = (m!)²` for `R'(ν) = R(ν) / Sym⁺(ν) R(ν)` (§2.5, after Proposition 2.12);
* for `k[x_1, …, x_m]` over the symmetric polynomials (Artin's theorem), giving
  `dim_k k[x] / (Sym⁺) = m!` (§2.2, Lemma 2.1).
-/

namespace Categorification

variable {k R M ι : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
  [Module k M] [IsScalarTower k R M]

variable (M) in
/-- The `k`-subspace `(ker ε) M` of `M`. -/
def augSubmodule (ε : R →ₐ[k] k) : Submodule k M :=
  ((RingHom.ker ε) • (⊤ : Submodule R M)).restrictScalars k

theorem mem_augSubmodule {ε : R →ₐ[k] k} {x : M} :
    x ∈ augSubmodule M ε ↔ x ∈ (RingHom.ker ε) • (⊤ : Submodule R M) := Iff.rfl

theorem smul_mem_augSubmodule {ε : R →ₐ[k] k} {r : R} (hr : ε r = 0) (m : M) :
    r • m ∈ augSubmodule M ε := by
  rw [mem_augSubmodule]
  exact Submodule.smul_mem_smul (r := r) (n := m) (RingHom.mem_ker.2 hr) Submodule.mem_top

/-- Induction principle for `(ker ε) M`. -/
theorem augSubmodule_induction {ε : R →ₐ[k] k} {p : M → Prop} {x : M}
    (hx : x ∈ augSubmodule M ε) (smul : ∀ r : R, ε r = 0 → ∀ m : M, p (r • m))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  rw [mem_augSubmodule] at hx
  exact Submodule.smul_induction_on hx (fun r hr m _ => smul r (RingHom.mem_ker.1 hr) m) add

variable (b : Basis ι R M) (ε : R →ₐ[k] k)

/-- The `k`-linear functional `m ↦ ε (b.coord i m)`. -/
noncomputable def augCoord (i : ι) : M →ₗ[k] k :=
  ε.toLinearMap ∘ₗ (b.coord i).restrictScalars k

theorem augCoord_apply (i : ι) (m : M) : augCoord b ε i m = ε (b.repr m i) := rfl

theorem augSubmodule_le_ker_augCoord (i : ι) :
    augSubmodule M ε ≤ LinearMap.ker (augCoord b ε i) := by
  intro x hx
  rw [mem_augSubmodule] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    rw [LinearMap.mem_ker, augCoord_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      RingHom.mem_ker.1 hr, zero_mul]
  · intro x y hx hy
    exact add_mem hx hy

variable [Fintype ι] [DecidableEq ι]

/-- **The augmentation quotient of a free module**: the classes of a basis `b` of `M` over `R`
form a `k`-basis of `M / (ker ε) M`. -/
noncomputable def augQuotBasis : Basis ι k (M ⧸ augSubmodule M ε) :=
  Basis.mk (v := fun i => Submodule.Quotient.mk (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc j
      have h := congrArg ((augSubmodule M ε).liftQ (augCoord b ε j)
        (augSubmodule_le_ker_augCoord b ε j)) hc
      simp only [map_sum, map_smul, Submodule.liftQ_apply, augCoord_apply, Basis.repr_self,
        map_zero] at h
      rw [Finset.sum_eq_single j (fun i _ hij => by
        rw [Finsupp.single_eq_of_ne hij, map_zero, smul_zero])
        (by simp)] at h
      simpa using h)
    (by
      rintro x -
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have heq : m - ∑ i, ε (b.repr m i) • b i =
          ∑ i, (b.repr m i - algebraMap k R (ε (b.repr m i))) • b i := by
        simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul, b.sum_repr]
      have hm : m - ∑ i, ε (b.repr m i) • b i ∈ augSubmodule M ε := by
        rw [heq]
        exact Submodule.sum_mem _ fun i _ => smul_mem_augSubmodule (by simp) _
      have : (Submodule.Quotient.mk m : M ⧸ augSubmodule M ε) = ∑ i, ε (b.repr m i) •
          (Submodule.Quotient.mk (b i) : M ⧸ augSubmodule M ε) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub] at hm
        rw [sub_eq_zero.1 hm, ← Submodule.mkQ_apply, map_sum]
        simp only [map_smul, Submodule.mkQ_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

omit [DecidableEq ι] in
@[simp] theorem augQuotBasis_apply (i : ι) :
    augQuotBasis b ε i = Submodule.Quotient.mk (b i) := by
  simp [augQuotBasis]

omit [DecidableEq ι] in
include b in
/-- `dim_k M / (ker ε) M = rank_R M`. -/
theorem finrank_augQuot : Module.finrank k (M ⧸ augSubmodule M ε) = Fintype.card ι :=
  Module.finrank_eq_card_basis (augQuotBasis b ε)

omit [DecidableEq ι] in
include b in
theorem finiteDimensional_augQuot : FiniteDimensional k (M ⧸ augSubmodule M ε) :=
  Module.Finite.of_basis (augQuotBasis b ε)

end Categorification
