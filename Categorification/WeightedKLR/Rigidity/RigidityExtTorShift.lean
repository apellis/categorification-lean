/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DerivedTensorIdempotentCut
import Categorification.Algebra.DerivedTensorProjective
import Categorification.Algebra.DerivedHomologyShift
import DG.Derived.ShortExactTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Tor along a projective resolution whose lower terms are killed

Let `M` be a right `B`-module over a field `k` and `X` a left `B`-module with a projective
resolution `P` of length `N` (`P_{N+1} = 0`). Write `Tor_n(M, X)` for the cohomology in degree
`-n` of the derived tensor product `M ⊗ᴸ_B X`. If `M ⊗ᴸ_B P_n = 0` for every `n < N`, then
dimension shifting along the syzygies of `P` gives `Tor_n(M, X) ≅ Tor_{n-N}(M, P_N)`
(`nonempty_linearEquiv_derivedTensorHomology_top`). This is how Tor out of a standard module is
computed from the resolution of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, §7.1, Proposition 7.6 (Corollary 7.10).

## Main results

* `nonempty_linearEquiv_derivedTensorHomology_shift`: the connecting map of a short exact
  sequence whose middle term has no derived tensor cohomology is an isomorphism.
* `subsingleton_tensorProductOver_of_span`, `isZero_derivedTensorHomology_of_projective_span`:
  a projective module spanned by elements fixed by idempotents that kill `M` has
  `M ⊗ᴸ_B P = 0`.
* `nonempty_linearEquiv_derivedTensorHomology_top`: the dimension shift along the resolution.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

section TorShift

variable {k B : Type} [Field k] [Ring B]
  (M : Type) [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, 0} B] [HasDerivedCategory.{w, 0} k]

variable (k) in
/-- The cohomology in degree `n` of `M ⊗ᴸ_B X`, `X` an ordinary module in degree zero; for
`n = -i` it is `Tor_i(M, X)`. -/
abbrev derivedTensorHomology (n : ℤ) (X : ModuleCat.{0} B) : ModuleCat.{0} k :=
  (homologyFunctor (A := k) k n).obj ((derivedTensor.{w} k B M).obj
    (Q.obj ((degreeZeroModuleFunctor B).obj X)))

noncomputable local instance torShiftSequence :
    (homologyFunctor (A := k) k 0).ShiftSequence ℤ := by
  letI : (DG.HomotopyCategory.homologyFunctor.{0} k k 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} k k ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{0} k) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh k 0) ℤ
    (homologyFunctor k) (homologyFunctorFactorsh k)

/-- An isomorphism of modules induces one of the derived tensor cohomologies. -/
def derivedTensorHomologyLinearEquiv {X Y : ModuleCat.{0} B} (e : X ≅ Y) (n : ℤ) :
    derivedTensorHomology.{w} k M n X ≃ₗ[k] derivedTensorHomology.{w} k M n Y :=
  ((homologyFunctor (A := k) k n).mapIso ((derivedTensor.{w} k B M).mapIso
    ((Q (A := B)).mapIso ((degreeZeroModuleFunctor B).mapIso e)))).toLinearEquiv

/-- **Dimension shift.** For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` such that `M ⊗ᴸ X₂`
has no cohomology, the connecting map `Hⁿ(M ⊗ᴸ X₃) → Hⁿ⁺¹(M ⊗ᴸ X₁)` is an isomorphism. -/
theorem nonempty_linearEquiv_derivedTensorHomology_shift (S : ShortComplex (ModuleCat.{0} B))
    (hS : S.ShortExact) (h₂ : ∀ j : ℤ, IsZero (derivedTensorHomology.{w} k M j S.X₂)) (j : ℤ) :
    Nonempty (derivedTensorHomology.{w} k M j S.X₃ ≃ₗ[k]
      derivedTensorHomology.{w} k M (j + 1) S.X₁) := by
  let F := derivedTensor.{w} k B M
  let S' := S.map (degreeZeroModuleFunctor B)
  have hS' : S'.ShortExact := degreeZeroModuleFunctor_shortExact S hS
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact S' hS'
  let T := F.mapTriangle.obj (Triangle.mk ((Q (A := B)).map S'.f) ((Q (A := B)).map S'.g) δ)
  have hT' : T ∈ distTriang _ := F.map_distinguished _ hT
  let G := homologyFunctor (A := k) k 0
  let φ := G.homologySequenceδ T j (j + 1) rfl
  have hmono : Mono φ :=
    (G.homologySequence_exact₃ T hT' j (j + 1) rfl).mono_g ((h₂ j).eq_of_src _ _)
  have hepi : Epi φ :=
    (G.homologySequence_exact₁ T hT' j (j + 1) rfl).epi_f ((h₂ (j + 1)).eq_of_tgt _ _)
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact ⟨(asIso φ).toLinearEquiv⟩

omit [HasDerivedCategory.{w, 0} B] [HasDerivedCategory.{w, 0} k] in
/-- If every element of `Y` lies in the span of elements `y` with `e • y = y` for idempotents
`e` killing `M`, then `M ⊗_B Y = 0`. -/
theorem subsingleton_tensorProductOver_of_span (Y : Type) [AddCommGroup Y] [Module B Y]
    (hY : ∀ y : Y, y ∈ Submodule.span B {y : Y | ∃ e : B, e • y = y ∧ ∀ m : M, op e • m = 0}) :
    Subsingleton (TensorProductOver B M Y) := by
  have key : ∀ (m : M) (y : Y), TensorProductOver.tmul B m y = 0 := by
    intro m y
    refine (Submodule.span_induction (p := fun y _ => ∀ m : M, TensorProductOver.tmul B m y = 0)
      ?_ ?_ ?_ ?_ (hY y)) m
    · rintro y ⟨e, hy, he⟩ m
      rw [← hy, ← TensorProductOver.op_smul_tmul, he m, TensorProductOver.zero_tmul]
    · exact TensorProductOver.tmul_zero
    · intro x y _ _ hx hy m
      rw [TensorProductOver.tmul_add, hx m, hy m, add_zero]
    · intro b x _ hx m
      rw [← TensorProductOver.op_smul_tmul]
      exact hx (op b • m)
  refine ⟨fun x y => ?_⟩
  have hz : ∀ z : TensorProductOver B M Y, z = 0 := fun z => by
    induction z using TensorProductOver.induction_on with
    | zero => rfl
    | tmul m y => exact key m y
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [hz x, hz y]

/-- A projective module spanned by elements fixed by idempotents killing `M` has no derived
tensor cohomology with `M`. -/
theorem isZero_derivedTensorHomology_of_projective_span (Y : ModuleCat.{0} B) [Projective Y]
    (hY : ∀ y : Y, y ∈ Submodule.span B {y : Y | ∃ e : B, e • y = y ∧ ∀ m : M, op e • m = 0})
    (j : ℤ) : IsZero (derivedTensorHomology.{w} k M j Y) := by
  by_cases hj : j = 0
  · subst hj
    have := subsingleton_tensorProductOver_of_span M Y hY
    have e := ambientDerivedTensorH0Equiv (k := k) (A := B) (N := M) Y
    exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton
  · exact isZero_homology_of_isZero_intHomology k _ j
      (isZero_derivedTensor_homology_of_projective (A := k) (B := B) M Y j hj)

end TorShift

/-! ### Syzygies of a projective resolution -/

section Syzygy

variable {B : Type} [Ring B] {X : ModuleCat.{0} B} (P : ProjectiveResolution X)

/-- The syzygies of a projective resolution: `Ω₀ = ker(P₀ → X)` and
`Ωₙ₊₁ = ker(Pₙ₊₁ → Pₙ)`. -/
def syzygy : ℕ → ModuleCat.{0} B
  | 0 => ModuleCat.of B (LinearMap.ker (P.π.f 0).hom)
  | n + 1 => ModuleCat.of B (LinearMap.ker (P.complex.d (n + 1) n).hom)

/-- The differential `Pₙ₊₁ → Ωₙ`. -/
def toSyzygy : (n : ℕ) → (P.complex.X (n + 1) ⟶ syzygy P n)
  | 0 => ModuleCat.ofHom ((P.complex.d 1 0).hom.codRestrict _ fun x => by
      change (P.π.f 0).hom ((P.complex.d 1 0).hom x) = 0
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, P.complex_d_comp_π_f_zero]
      rfl)
  | n + 1 => ModuleCat.ofHom ((P.complex.d (n + 2) (n + 1)).hom.codRestrict _ fun x => by
      change (P.complex.d (n + 1) n).hom ((P.complex.d (n + 2) (n + 1)).hom x) = 0
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, P.complex.d_comp_d]
      rfl)

theorem toSyzygy_surjective (n : ℕ) : Function.Surjective (toSyzygy P n) := by
  cases n with
  | zero =>
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ x hx
    exact ⟨y, Subtype.ext hy⟩
  | succ n =>
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (P.exact_succ n) x hx
    exact ⟨y, Subtype.ext hy⟩

/-- The short exact sequence `0 → Ωₙ₊₁ → Pₙ₊₁ → Ωₙ → 0`. -/
def syzygySequence (n : ℕ) : ShortComplex (ModuleCat.{0} B) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker (P.complex.d (n + 1) n).hom).subtype :
      syzygy P (n + 1) ⟶ P.complex.X (n + 1)) (toSyzygy P n) (by
    ext ⟨x, hx⟩
    cases n <;> exact Subtype.ext hx)

theorem syzygySequence_shortExact (n : ℕ) : (syzygySequence P n).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      cases n with
      | zero => exact congrArg Subtype.val hx
      | succ n => exact congrArg Subtype.val hx
    · rintro ⟨⟨y, hy⟩, rfl⟩
      cases n <;> exact Subtype.ext hy
  · exact ConcreteCategory.mono_of_injective _ fun a b h => Subtype.ext h
  · exact (ModuleCat.epi_iff_surjective _).mpr (toSyzygy_surjective P n)

/-- The short exact sequence `0 → Ω₀ → P₀ → X → 0`. -/
def syzygyZeroSequence : ShortComplex (ModuleCat.{0} B) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker (P.π.f 0).hom).subtype :
      syzygy P 0 ⟶ P.complex.X 0) (P.π.f 0 : P.complex.X 0 ⟶ X) (by
    ext ⟨x, hx⟩
    exact hx)

theorem syzygyZeroSequence_shortExact : (syzygyZeroSequence P).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨⟨y, hy⟩, rfl⟩; exact hy⟩
  · exact ConcreteCategory.mono_of_injective _ fun a b h => Subtype.ext h
  · change Epi (P.π.f 0)
    infer_instance

/-- If `Pₙ₊₂ = 0`, the differential `Pₙ₊₁ → Ωₙ` is bijective. -/
theorem toSyzygy_bijective (n : ℕ) (hz : IsZero (P.complex.X (n + 2))) :
    Function.Bijective (toSyzygy P n) := by
  refine ⟨fun x y hxy => ?_, toSyzygy_surjective P n⟩
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  rw [← sub_eq_zero]
  have h0 : (toSyzygy P n).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h1 : (P.complex.d (n + 1) n).hom (x - y) = 0 := by
    cases n with
    | zero => exact congrArg Subtype.val h0
    | succ n => exact congrArg Subtype.val h0
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (P.exact_succ n) _ h1
  rw [← hz, Subsingleton.elim z 0, map_zero]

/-- If `P₁ = 0`, the augmentation `P₀ → X` is bijective. -/
theorem π_zero_bijective (hz : IsZero (P.complex.X 1)) : Function.Bijective (P.π.f 0) := by
  refine ⟨fun x y hxy => ?_, (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  have hs := ModuleCat.isZero_iff_subsingleton.mp hz
  rw [← sub_eq_zero]
  have h1 : (P.π.f 0).hom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 P.exact₀ _ h1
  rw [← hz, Subsingleton.elim z 0, map_zero]

end Syzygy

/-! ### The dimension shift along a resolution -/

section Top

variable {k B : Type} [Field k] [Ring B]
  (M : Type) [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]
  [HasDerivedCategory.{w, 0} B] [HasDerivedCategory.{w, 0} k]
  {X : ModuleCat.{0} B} (P : ProjectiveResolution X)

/-- Below the length, the cohomology of `M ⊗ᴸ X` shifts to that of the syzygies. -/
theorem nonempty_linearEquiv_derivedTensorHomology_syzygy {N : ℕ}
    (hP : ∀ n < N, ∀ j : ℤ, IsZero (derivedTensorHomology.{w} k M j (P.complex.X n))) :
    ∀ n < N, ∀ j : ℤ, Nonempty (derivedTensorHomology.{w} k M j X ≃ₗ[k]
      derivedTensorHomology.{w} k M (j + n + 1) (syzygy P n)) := by
  intro n
  induction n with
  | zero =>
    intro hn j
    have h := nonempty_linearEquiv_derivedTensorHomology_shift M (syzygyZeroSequence P)
      (syzygyZeroSequence_shortExact P) (hP 0 hn) j
    rw [show j + ((0 : ℕ) : ℤ) + 1 = j + 1 by simp]
    exact h
  | succ n ih =>
    intro hn j
    obtain ⟨e₁⟩ := ih (by omega) j
    obtain ⟨e₂⟩ := nonempty_linearEquiv_derivedTensorHomology_shift M (syzygySequence P n)
      (syzygySequence_shortExact P n) (hP (n + 1) hn) (j + n + 1)
    have : j + ((n + 1 : ℕ) : ℤ) + 1 = j + n + 1 + 1 := by push_cast; ring
    rw [this]
    exact ⟨e₁.trans e₂⟩

/-- **Dimension shift along a resolution.** If `P_{N+1} = 0` and `M ⊗ᴸ Pₙ = 0` for `n < N`,
then `Hʲ(M ⊗ᴸ X) ≅ Hʲ⁺ᴺ(M ⊗ᴸ P_N)`, i.e. `Tor_i(M, X) ≅ Tor_{i-N}(M, P_N)`. -/
theorem nonempty_linearEquiv_derivedTensorHomology_top (N : ℕ) (hz : IsZero (P.complex.X (N + 1)))
    (hP : ∀ n < N, ∀ j : ℤ, IsZero (derivedTensorHomology.{w} k M j (P.complex.X n))) (j : ℤ) :
    Nonempty (derivedTensorHomology.{w} k M j X ≃ₗ[k]
      derivedTensorHomology.{w} k M (j + N) (P.complex.X N)) := by
  cases N with
  | zero =>
    let e : P.complex.X 0 ≅ X :=
      (LinearEquiv.ofBijective (P.π.f 0).hom (π_zero_bijective P hz)).toModuleIso
    rw [show j + ((0 : ℕ) : ℤ) = j by simp]
    exact ⟨(derivedTensorHomologyLinearEquiv (k := k) M e j).symm⟩
  | succ m =>
    obtain ⟨e₁⟩ := nonempty_linearEquiv_derivedTensorHomology_syzygy M P hP m (by omega) j
    let e : P.complex.X (m + 1) ≅ syzygy P m :=
      (LinearEquiv.ofBijective (toSyzygy P m).hom (toSyzygy_bijective P m hz)).toModuleIso
    have : j + ((m + 1 : ℕ) : ℤ) = j + m + 1 := by push_cast; ring
    rw [this]
    exact ⟨e₁.trans (derivedTensorHomologyLinearEquiv (k := k) M e _).symm⟩

end Top

end Categorification
