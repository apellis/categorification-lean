/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.UpResolution
import Categorification.Algebra.Graded.Idempotent

/-!
# Resolutions in `C↑` from a positively graded corner

Let `A` be a finite-dimensional graded algebra over a field `k` and `e ∈ A` an idempotent of
degree zero with `A e A = A`, such that the corner `e A e` is nonnegatively graded with degree
zero part `k e`. Then every finite-dimensional graded `A`-module has a graded projective
resolution in `C↑` (Beilinson–Ginzburg–Soergel, *Koszul duality patterns in representation
theory*, §2.12), that is, a resolution `⋯ → P_1 → P_0 → N` with `P_n` vanishing in degrees
`< n - c` for some `c` (`GFin.exists_upResolution_of_corner`).

The resolution is built from the covers `A e ⊗_k e M → M`, `a ⊗ v ↦ a v`: these are surjective
because `A e A = A`, and on the `e`-part of the kernel the lowest degree of `e M` disappears,
because `e A e` has only scalars in degree zero and nothing below. So the lowest degree of the
`e`-part of the `n`-th syzygy grows at least linearly in `n`.

This is the positivity step of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.28: there the corner is the cyclotomic nilHecke algebra
cut down by its primitive idempotent, a cohomology ring of a Grassmannian, which is
nonnegatively graded and one-dimensional in degree zero.

## Main definitions and results

* `GFin.cornerCover he0 M` : the graded projective module `A e ⊗_k e M`.
* `GFin.cornerMap` : the action map `A e ⊗_k e M → M`.
* `GFin.EVanishBelow e M m` : `e M` vanishes in degrees `< m`.
* `GFin.eVanishBelow_cornerKer` : the `e`-part of the kernel vanishes in degrees `≤ m`.
* `GFin.cornerUpResolution` and `GFin.exists_upResolution_of_corner`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Function TensorProduct

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

variable {e : A}

/-- `e M` vanishes in degrees `< m`. -/
def EVanishBelow (e : A) (M : GFin 𝒜) (m : ℤ) : Prop :=
  ∀ j < m, ∀ x ∈ M.grading j, e • x = 0

/-- The graded module `A e ⊗_k e M`, graded by the tensor product grading. -/
def cornerCover (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) : GFin 𝒜 :=
  letI := submoduleDecomposition 𝒜 (leftIdeal_isHomogeneous he0)
  letI := idemDecomposition M.grading he0
  { carrier := leftIdeal e ⊗[k] idemSubspace k M.carrier e
    grading := tensorGrading (Graded.submodule 𝒜 (leftIdeal e)) (idem M.grading e)
    finiteDimensional := inferInstance }

theorem projective_cornerCover (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) :
    Module.Projective A (cornerCover he0 M).carrier :=
  haveI : Module.Projective A (leftIdeal e) :=
    Module.Projective.of_split (leftIdeal e).subtype (leftIdealProj he)
      (leftIdealProj_comp_subtype he)
  show Module.Projective A (leftIdeal e ⊗[k] idemSubspace k M.carrier e) from inferInstance

/-- The action map `A e ⊗_k e M → M`, `a ⊗ v ↦ a v`. -/
def cornerMap (e : A) (M : GFin 𝒜) :
    (leftIdeal e ⊗[k] idemSubspace k M.carrier e) →ₗ[A] M.carrier :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun v => (a : A) • (v : M.carrier)
          map_add' := fun v w => by simp only [Submodule.coe_add, smul_add]
          map_smul' := fun c v => by
            simp only [SetLike.val_smul, RingHom.id_apply]
            exact smul_comm (a : A) c (v : M.carrier) }
      map_add' := fun a b => by
        ext v
        simp only [Submodule.coe_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          add_smul]
      map_smul' := fun a b => by
        ext v
        simp only [SetLike.val_smul, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.smul_apply, mul_smul, RingHom.id_apply] }

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem cornerMap_tmul (M : GFin 𝒜) (a : leftIdeal e)
    (v : idemSubspace k M.carrier e) :
    cornerMap e M (a ⊗ₜ v) = (a : A) • (v : M.carrier) := rfl

theorem cornerMap_preservesGrading (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) :
    PreservesGrading (cornerCover he0 M).grading M.grading (cornerMap e M) := fun _ _ hx =>
  tensorGrading_map_mem _ _ M.grading ((cornerMap e M).restrictScalars k)
    (fun _ _ _ _ ha hn => SetLike.GradedSMul.smul_mem (A := 𝒜) ha hn) hx

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
/-- The cover `A e ⊗_k e M → M` is surjective when `A e A = A`. -/
theorem cornerMap_surjective (he : IsIdempotentElem e)
    (hfull : (1 : A) ∈ Submodule.span A (Set.range fun b : A => e * b)) (M : GFin 𝒜) :
    Surjective (cornerMap e M) := by
  intro n
  have key : ∀ x ∈ Submodule.span A (Set.range fun b : A => e * b),
      x • n ∈ LinearMap.range (cornerMap e M) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      refine ⟨(⟨e, he.eq⟩ : leftIdeal e) ⊗ₜ ⟨e • b • n, smul_mem_idemSubspace he _⟩, ?_⟩
      change e • e • b • n = (e * b) • n
      rw [← mul_smul, he.eq, mul_smul]
    | zero => rw [zero_smul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hx
  obtain ⟨y, hy⟩ := key 1 hfull
  exact ⟨y, by rw [hy, one_smul]⟩

/-- The kernel of `A e ⊗_k e M → M`. -/
abbrev cornerKer (he0 : e ∈ 𝒜 0) (M : GFin 𝒜) : GFin 𝒜 :=
  ker (M := cornerCover he0 M) (cornerMap e M) (cornerMap_preservesGrading he0 M)

/-- `n ↦ e n`, as a map `M → e M`. -/
def eProj (he : IsIdempotentElem e) (M : GFin 𝒜) :
    M.carrier →ₗ[k] idemSubspace k M.carrier e where
  toFun n := ⟨e • n, smul_mem_idemSubspace he n⟩
  map_add' _ _ := Subtype.ext (smul_add _ _ _)
  map_smul' c n := Subtype.ext (smul_comm e c n)

section Positivity

variable (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0)
  (hneg : ∀ i < 0, ∀ a ∈ 𝒜 i, e * a * e = 0)
  (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, e * a * e = c • e)

include hneg hzero in
omit [GradedAlgebra 𝒜] [Module.Finite k A] in
/-- In degrees `≤ m`, where `m` bounds `e M` from below, `e` acts on `A e ⊗_k e M` through the
cover: `e x = e ⊗ e (a x)`. -/
theorem smul_eq_tmul_eProj {M : GFin 𝒜} {m : ℤ} (hM : EVanishBelow e M m) {j : ℤ} (hj : j ≤ m)
    {x : leftIdeal e ⊗[k] idemSubspace k M.carrier e}
    (hx : x ∈ tensorGrading (Graded.submodule 𝒜 (leftIdeal e)) (idem M.grading e) j) :
    e • x = (⟨e, he.eq⟩ : leftIdeal e) ⊗ₜ eProj he M (cornerMap e M x) := by
  induction hx using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j', a, v, hij, ha, hv, rfl⟩ := ht
    change (e • a) ⊗ₜ v =
      (⟨e, he.eq⟩ : leftIdeal e) ⊗ₜ eProj he M ((a : A) • (v : M.carrier))
    have hva : e • (v : M.carrier) = v := v.2
    have hae : (a : A) * e = a := a.2
    by_cases hj' : j' < m
    · have hv0 : v = 0 := Subtype.ext (by rw [← hva]; exact hM j' hj' _ hv)
      subst hv0
      simp only [tmul_zero, ZeroMemClass.coe_zero, smul_zero, map_zero]
    · have hea : e * (a : A) = e * (a : A) * e := by rw [mul_assoc, hae]
      rcases lt_or_eq_of_le (show i ≤ 0 by omega) with hi | hi
      · have h0 : e * (a : A) = 0 := by rw [hea]; exact hneg i hi (a : A) ha
        have hl : e • a = 0 := Subtype.ext h0
        have hr : eProj he M ((a : A) • (v : M.carrier)) = 0 :=
          Subtype.ext (by
            change e • (a : A) • (v : M.carrier) = 0
            rw [← mul_smul, h0, zero_smul])
        rw [hl, hr, zero_tmul, tmul_zero]
      · subst hi
        obtain ⟨c, hc⟩ := hzero (a : A) ha
        have h1 : e * (a : A) = c • e := by rw [hea, hc]
        have hl : e • a = c • (⟨e, he.eq⟩ : leftIdeal e) := Subtype.ext h1
        have hr : eProj he M ((a : A) • (v : M.carrier)) = c • v :=
          Subtype.ext (by
            change e • (a : A) • (v : M.carrier) = c • (v : M.carrier)
            rw [← mul_smul, h1, smul_assoc, hva])
        rw [hl, hr, smul_tmul]
  | zero => simp only [smul_zero, map_zero, tmul_zero]
  | add s t _ _ hs ht => rw [smul_add, hs, ht, map_add, map_add, tmul_add]
  | smul c t _ ht =>
    rw [smul_comm, ht, LinearMap.map_smul_of_tower, map_smul, tmul_smul]

include he hneg hzero in
/-- The `e`-part of the kernel of `A e ⊗_k e M → M` vanishes in degrees `≤ m`. -/
theorem eVanishBelow_cornerKer {M : GFin 𝒜} {m : ℤ} (hM : EVanishBelow e M m) :
    EVanishBelow e (cornerKer he0 M) (m + 1) := by
  intro j hj x hx
  refine Subtype.ext ?_
  have hx0 : cornerMap e M (x.1 : leftIdeal e ⊗[k] idemSubspace k M.carrier e) = 0 := x.2
  have h := smul_eq_tmul_eProj he hneg hzero hM (show j ≤ m by omega)
    (x := (x.1 : leftIdeal e ⊗[k] idemSubspace k M.carrier e)) hx
  rw [hx0, map_zero, tmul_zero] at h
  exact h

/-- `A e ⊗_k e M` vanishes in degrees `< a₀ + m` when `A` vanishes below `a₀` and `e M`
below `m`. -/
theorem cornerCover_grading_eq_bot {M : GFin 𝒜} {m a₀ : ℤ} (hM : EVanishBelow e M m)
    (hA : ∀ i < a₀, 𝒜 i = ⊥) {j : ℤ} (hj : j < a₀ + m) :
    (cornerCover he0 M).grading j = ⊥ := by
  change tensorGrading _ _ j = ⊥
  rw [eq_bot_iff]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, j', a, v, hij, ha, hv, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot]
  by_cases hi : i < a₀
  · have : a = 0 := Subtype.ext (by
      have := ha
      change (a : A) ∈ 𝒜 i at this
      rw [hA i hi] at this
      exact (Submodule.mem_bot k).1 this)
    rw [this, zero_tmul]
  · have hv0 : v = 0 := Subtype.ext (by
      have hva : e • (v : M.carrier) = v := v.2
      rw [← hva]; exact hM j' (by omega) _ hv)
    rw [hv0, tmul_zero]

/-- The syzygies `Ω_0 = M`, `Ω_{n+1} = ker (A e ⊗_k e Ω_n → Ω_n)`. -/
def cornerSyz (M : GFin 𝒜) : ℕ → GFin 𝒜
  | 0 => M
  | n + 1 => cornerKer he0 (cornerSyz M n)

include he hneg hzero in
theorem eVanishBelow_cornerSyz {M : GFin 𝒜} {m : ℤ} (hM : EVanishBelow e M m) (n : ℕ) :
    EVanishBelow e (cornerSyz he0 M n) (m + n) := by
  induction n with
  | zero => simpa [cornerSyz] using hM
  | succ n ih =>
    have := eVanishBelow_cornerKer he he0 hneg hzero ih
    rwa [Nat.cast_succ, ← add_assoc]

variable (hfull : (1 : A) ∈ Submodule.span A (Set.range fun b : A => e * b))

/-- **Resolutions in `C↑` from a positive corner.** If `A e A = A` and `e A e` is nonnegatively
graded with degree zero part `k e`, the covers `A e ⊗_k e Ω_n → Ω_n` form a resolution of `M`
whose `n`-th term vanishes in degrees `< n + a₀ + m` (`A` vanishing below `a₀`, `e M` below
`m`). This is the positivity step of Webster, arXiv:1309.3796v3, proof of Theorem 5.28. -/
def cornerUpResolution {M : GFin 𝒜} {m a₀ : ℤ} (hM : EVanishBelow e M m)
    (hA : ∀ i < a₀, 𝒜 i = ⊥) : UpResolution M (-(a₀ + m)) where
  syz := cornerSyz he0 M
  term n := cornerCover he0 (cornerSyz he0 M n)
  projective n := projective_cornerCover he he0 _
  iso := GradedEquiv.refl _
  ses n := kerShortExact (M := cornerCover he0 _) _ (cornerMap_preservesGrading he0 _)
    (cornerMap_surjective he hfull _)
  vanish n j hj :=
    cornerCover_grading_eq_bot he0 (eVanishBelow_cornerSyz he he0 hneg hzero hM n) hA
      (by omega)

include he he0 hneg hzero hfull in
/-- Every finite-dimensional graded module has a graded projective resolution in `C↑`, when
`A e A = A` for a degree-zero idempotent `e` with `e A e` nonnegatively graded and `(e A e)_0 = k e`
(Webster, arXiv:1309.3796v3, proof of Theorem 5.28, positivity step). -/
theorem exists_upResolution_of_corner (N : GFin 𝒜) : ∃ c, Nonempty (UpResolution N c) := by
  obtain ⟨a₀, _, hA⟩ := exists_bounds (M := A) (ℳ := 𝒜)
  obtain ⟨m, _, hN⟩ := exists_bounds (M := N.carrier) (ℳ := N.grading)
  have hM : EVanishBelow e N m := fun j hj x hx => by
    rw [hN j (Or.inl hj), Submodule.mem_bot] at hx
    rw [hx, smul_zero]
  exact ⟨_, ⟨cornerUpResolution he he0 hneg hzero hfull hM fun i hi => hA i (Or.inl hi)⟩⟩

end Positivity

end GFin

end Categorification.Graded
