/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Module

/-!
# Graded dimension

For a `ℤ`-graded vector space `M = ⨁_d M_d` over a field `k` (a family
`ℳ : ℤ → Submodule k M`) whose pieces are finite-dimensional and vanish in sufficiently negative
degrees, the *graded dimension* is the Laurent series

`gdim M = ∑_d dim_k (M_d) q^d ∈ ℤ((q))`

(Khovanov–Lauda I, arXiv:0803.4121v2, §2.5). If `M` is finite-dimensional, it is a Laurent
polynomial `gdimPoly M ∈ ℤ[q, q⁻¹]`.

## Conventions

* `q` is `HahnSeries.single 1 1` in `LaurentSeries ℤ` and `LaurentPolynomial.T 1` in
  `ℤ[q, q⁻¹]`; `q^a` is `HahnSeries.single a 1`, resp. `T a`.
* With the shift convention of `Graded.shift` (`M{a}_d = M_{d-a}`, grading shifted **up** by
  `a`, as in KL I) we get `gdim (M{a}) = q^a · gdim M` (`gdim_shift`, `gdimPoly_shift`).

## Design

`gdim ℳ` is defined for every family of subspaces: its coefficients are `finrank k (ℳ d)`
whenever their support is bounded below, and it is `0` otherwise. It only depends on the family
`ℳ`, not on a module structure, so it applies equally to graded modules, to graded subspaces such
as `e M`, and to plain graded vector spaces. The hypotheses under which it is meaningful are
bundled in the class `HasGdim ℳ` (all pieces finite-dimensional, grading bounded below).

## Main results

* `coeff_gdim` : `(gdim ℳ).coeff d = dim (ℳ d)`.
* `gdim_shift` : `gdim (shift ℳ a) = q^a * gdim ℳ`.
* `gdim_prod` : `gdim (M ⊕ N) = gdim M + gdim N`.
* `gdim_eq_add_of_exact` : additivity on degree-wise short exact sequences, and its graded-map
  version `gdim_eq_add_of_exact_of_preservesGrading`.
* `gdim_congr`, `gdimPoly_congr` : invariance under degree-preserving isomorphisms.
* `gdim_idem_eq_add_of_exact` : `M ↦ gdim (e M)` is additive on short exact sequences of graded
  modules, for a degree-zero idempotent `e` (used for KL I's characters `gdim (1_i M)`).
* `gdimPoly`, `toLaurentSeries`, `toLaurentSeries_gdimPoly` : the finite-dimensional case, with
  `gdimPoly_shift`, `gdimPoly_prod`, `gdimPoly_eq_add_of_exact_of_preservesGrading`.
* `HasGdim` instances for `shift`, `prod`, `idem`, and `HasGdim.of_finiteDimensional`.
-/

namespace Categorification.Graded

open DirectSum Function Module

/-! ### Laurent polynomials as Laurent series -/

section LaurentSeries

variable {R : Type*} [CommRing R]

/-- The embedding `R[q, q⁻¹] → R((q))` of Laurent polynomials into Laurent series (same
coefficients). -/
def toLaurentSeries : LaurentPolynomial R →+ LaurentSeries R where
  toFun p := ⟨p, p.finite_support.isPWO⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coeff_toLaurentSeries (p : LaurentPolynomial R) (d : ℤ) :
    (toLaurentSeries p).coeff d = p d := rfl

/-- `q^a · p ↦ q^a · p`. -/
theorem toLaurentSeries_T_mul (a : ℤ) (p : LaurentPolynomial R) :
    toLaurentSeries (LaurentPolynomial.T a * p) = HahnSeries.single a 1 * toLaurentSeries p := by
  ext d
  rw [← sub_add_cancel d a, HahnSeries.coeff_single_mul_add, one_mul, coeff_toLaurentSeries,
    coeff_toLaurentSeries, LaurentPolynomial.T,
    AddMonoidAlgebra.single_mul_apply_aux _ _ _ _ (d - a) fun b _ => by
      constructor <;> intro h <;> omega, one_mul]

theorem toLaurentSeries_injective : Injective (toLaurentSeries (R := R)) := fun p p' h =>
  Finsupp.ext fun d => by rw [← coeff_toLaurentSeries, h, coeff_toLaurentSeries]

end LaurentSeries

variable {k M N P : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup P] [Module k P]

/-! ### Graded dimension -/

open scoped Classical in
/-- The graded dimension `∑_d dim_k (ℳ d) q^d` of a `ℤ`-family of subspaces, as a Laurent series.
It is meaningful (see `coeff_gdim`) when the dimensions vanish in sufficiently negative degrees
(e.g. under `HasGdim ℳ`); otherwise it is `0` by convention. -/
noncomputable def gdim (ℳ : ℤ → Submodule k M) : LaurentSeries ℤ :=
  if h : BddBelow (support fun d => (finrank k (ℳ d) : ℤ)) then HahnSeries.ofSuppBddBelow _ h
  else 0

theorem coeff_gdim_of_bddBelow {ℳ : ℤ → Submodule k M}
    (h : BddBelow (support fun d => (finrank k (ℳ d) : ℤ))) (d : ℤ) :
    (gdim ℳ).coeff d = finrank k (ℳ d) := by
  simp [gdim, h]

theorem gdim_of_not_bddBelow {ℳ : ℤ → Submodule k M}
    (h : ¬ BddBelow (support fun d => (finrank k (ℳ d) : ℤ))) : gdim ℳ = 0 := by
  simp [gdim, h]

/-- The graded pieces are finite-dimensional and vanish in sufficiently negative degrees; this is
the setting in which `gdim` is the graded dimension (KL I, §2.5). -/
class HasGdim (ℳ : ℤ → Submodule k M) : Prop where
  finiteDimensional : ∀ d, FiniteDimensional k (ℳ d)
  bddBelow : BddBelow {d | ℳ d ≠ ⊥}

attribute [instance] HasGdim.finiteDimensional

theorem support_finrank_subset (ℳ : ℤ → Submodule k M) :
    (support fun d => (finrank k (ℳ d) : ℤ)) ⊆ {d | ℳ d ≠ ⊥} := by
  intro d hd h
  apply hd
  show ((finrank k (ℳ d) : ℕ) : ℤ) = 0
  rw [h]; simp

theorem HasGdim.bddBelow_support (ℳ : ℤ → Submodule k M) [HasGdim ℳ] :
    BddBelow (support fun d => (finrank k (ℳ d) : ℤ)) :=
  HasGdim.bddBelow.mono (support_finrank_subset ℳ)

@[simp] theorem coeff_gdim (ℳ : ℤ → Submodule k M) [HasGdim ℳ] (d : ℤ) :
    (gdim ℳ).coeff d = finrank k (ℳ d) :=
  coeff_gdim_of_bddBelow (HasGdim.bddBelow_support ℳ) d

/-- A finite-dimensional graded vector space has a graded dimension. -/
theorem HasGdim.of_finiteDimensional (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [FiniteDimensional k M] : HasGdim ℳ where
  finiteDimensional _ := inferInstance
  bddBelow := (Submodule.finite_ne_bot_of_iSupIndep
    (Decomposition.isInternal ℳ).submodule_iSupIndep).bddBelow

/-! ### Shifts -/

theorem bddBelow_shift_iff {S : Set ℤ} (a : ℤ) : BddBelow {d | d - a ∈ S} ↔ BddBelow S := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b - a, fun d hd => by have := hb (show d + a - a ∈ S by simpa using hd); omega⟩
  · rintro ⟨b, hb⟩
    exact ⟨b + a, fun d hd => by have := hb hd; omega⟩

instance (ℳ : ℤ → Submodule k M) [HasGdim ℳ] (a : ℤ) : HasGdim (shift ℳ a) where
  finiteDimensional d := HasGdim.finiteDimensional (d - a)
  bddBelow := (bddBelow_shift_iff (S := {d | ℳ d ≠ ⊥}) a).2 HasGdim.bddBelow

/-- `gdim (M{a}) = q^a gdim M`. -/
theorem gdim_shift (ℳ : ℤ → Submodule k M) (a : ℤ) :
    gdim (shift ℳ a) = HahnSeries.single a 1 * gdim ℳ := by
  have hsupp : (support fun d => (finrank k (shift ℳ a d) : ℤ)) =
      {d | d - a ∈ support fun d => (finrank k (ℳ d) : ℤ)} := rfl
  by_cases h : BddBelow (support fun d => (finrank k (ℳ d) : ℤ))
  · have h' : BddBelow (support fun d => (finrank k (shift ℳ a d) : ℤ)) := by
      rw [hsupp]; exact (bddBelow_shift_iff a).2 h
    ext d
    rw [coeff_gdim_of_bddBelow h', ← sub_add_cancel d a, HahnSeries.coeff_single_mul_add,
      coeff_gdim_of_bddBelow h, one_mul, shift_apply, add_sub_cancel_right]
  · have h' : ¬ BddBelow (support fun d => (finrank k (shift ℳ a d) : ℤ)) := by
      rw [hsupp]; exact fun h'' => h ((bddBelow_shift_iff a).1 h'')
    rw [gdim_of_not_bddBelow h, gdim_of_not_bddBelow h', mul_zero]

/-! ### Additivity -/

/-- Graded dimension is additive if dimensions are additive degree-wise. -/
theorem gdim_eq_add_of_finrank_eq {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {𝒬 : ℤ → Submodule k P} [HasGdim 𝒩]
    (h : ∀ d, finrank k (𝒩 d) = finrank k (ℳ d) + finrank k (𝒬 d)) :
    gdim 𝒩 = gdim ℳ + gdim 𝒬 := by
  have hN := HasGdim.bddBelow_support 𝒩
  have hM : BddBelow (support fun d => (finrank k (ℳ d) : ℤ)) :=
    BddBelow.mono (fun d hd => by
      simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at *; have := h d; omega) hN
  have hQ : BddBelow (support fun d => (finrank k (𝒬 d) : ℤ)) :=
    BddBelow.mono (fun d hd => by
      simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at *; have := h d; omega) hN
  ext d
  rw [HahnSeries.coeff_add, coeff_gdim_of_bddBelow hN, coeff_gdim_of_bddBelow hM,
    coeff_gdim_of_bddBelow hQ, h]
  push_cast; rfl

/-- The linear isomorphism `p.prod q ≃ p × q`. -/
def _root_.Submodule.prodEquivProd {R : Type*} [Semiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    p.prod q ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) [HasGdim ℳ] [HasGdim 𝒩] :
    HasGdim (prod ℳ 𝒩) where
  finiteDimensional d := ((ℳ d).prodEquivProd (𝒩 d)).symm.finiteDimensional
  bddBelow := by
    obtain ⟨a, ha⟩ := HasGdim.bddBelow (ℳ := ℳ)
    obtain ⟨b, hb⟩ := HasGdim.bddBelow (ℳ := 𝒩)
    refine ⟨min a b, fun d hd => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 : ℳ d = ⊥ := by
      by_contra h; have := ha h; omega
    have h2 : 𝒩 d = ⊥ := by
      by_contra h; have := hb h; omega
    exact hd (by rw [prod, h1, h2, Submodule.prod_bot])

theorem finrank_prod_apply (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) [HasGdim ℳ]
    [HasGdim 𝒩] (d : ℤ) : finrank k (prod ℳ 𝒩 d) = finrank k (ℳ d) + finrank k (𝒩 d) := by
  show finrank k ((ℳ d).prod (𝒩 d)) = _
  rw [((ℳ d).prodEquivProd (𝒩 d)).finrank_eq, Module.finrank_prod]

/-- `gdim (M ⊕ N) = gdim M + gdim N`. -/
theorem gdim_prod (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) [HasGdim ℳ] [HasGdim 𝒩] :
    gdim (prod ℳ 𝒩) = gdim ℳ + gdim 𝒩 :=
  gdim_eq_add_of_finrank_eq (finrank_prod_apply ℳ 𝒩)

/-- Dimension is additive on short exact sequences of finite-dimensional spaces. -/
theorem finrank_eq_add_of_exact {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] [FiniteDimensional k V₂]
    {f : V₁ →ₗ[k] V₂} {g : V₂ →ₗ[k] V₃} (hf : Injective f) (hg : Surjective g)
    (hfg : Exact f g) : finrank k V₂ = finrank k V₁ + finrank k V₃ := by
  rw [← g.finrank_range_add_finrank_ker, LinearMap.range_eq_top.2 hg, finrank_top,
    hfg.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf, add_comm]

/-- Graded dimension is additive on degree-wise short exact sequences
`0 → ℳ d → 𝒩 d → 𝒬 d → 0`. -/
theorem gdim_eq_add_of_exact {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {𝒬 : ℤ → Submodule k P} [HasGdim 𝒩] (f : ∀ d, ℳ d →ₗ[k] 𝒩 d) (g : ∀ d, 𝒩 d →ₗ[k] 𝒬 d)
    (hf : ∀ d, Injective (f d)) (hg : ∀ d, Surjective (g d)) (hfg : ∀ d, Exact (f d) (g d)) :
    gdim 𝒩 = gdim ℳ + gdim 𝒬 :=
  gdim_eq_add_of_finrank_eq fun d => finrank_eq_add_of_exact (hf d) (hg d) (hfg d)

section Exact

variable {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {𝒬 : ℤ → Submodule k P}
  [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]
  {f : M →ₗ[k] N} {g : N →ₗ[k] P} (hfgr : PreservesGrading ℳ 𝒩 f)
  (hggr : PreservesGrading 𝒩 𝒬 g)

omit [Decomposition 𝒬] in
include hfgr hggr in
/-- A short exact sequence of degree-preserving maps is exact in each degree. -/
theorem exact_restrict (hfg : Exact f g) (d : ℤ) :
    Exact (f.restrict (p := ℳ d) (q := 𝒩 d) fun _ hx => hfgr hx)
      (g.restrict (p := 𝒩 d) (q := 𝒬 d) fun _ hx => hggr hx) := by
  intro y
  constructor
  · intro hy
    have hy' : g y = 0 := by simpa using congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (hfg y).1 hy'
    refine ⟨⟨_, (decompose ℳ x d).2⟩, Subtype.ext ?_⟩
    simp only [LinearMap.restrict_apply]
    rw [← decompose_map hfgr, hx, decompose_of_mem_same _ y.2]
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (by simpa using (hfg _).2 ⟨x, rfl⟩)

include hggr in
theorem surjective_restrict (hg : Surjective g) (d : ℤ) :
    Surjective (g.restrict (p := 𝒩 d) (q := 𝒬 d) fun _ hx => hggr hx) := by
  intro z
  obtain ⟨y, hy⟩ := hg z
  refine ⟨⟨_, (decompose 𝒩 y d).2⟩, Subtype.ext ?_⟩
  simp only [LinearMap.restrict_apply]
  rw [← decompose_map hggr, hy, decompose_of_mem_same _ z.2]

omit [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬] in
include hfgr in
theorem injective_restrict (hf : Injective f) (d : ℤ) :
    Injective (f.restrict (p := ℳ d) (q := 𝒩 d) fun _ hx => hfgr hx) := fun _ _ h =>
  Subtype.ext (hf (congrArg Subtype.val h))

include hfgr hggr in
/-- Graded dimension is additive on short exact sequences of graded vector spaces (or graded
modules, applied to the underlying `k`-linear maps) with degree-preserving maps. -/
theorem gdim_eq_add_of_exact_of_preservesGrading [HasGdim 𝒩] (hf : Injective f)
    (hg : Surjective g) (hfg : Exact f g) : gdim 𝒩 = gdim ℳ + gdim 𝒬 :=
  gdim_eq_add_of_exact _ _ (injective_restrict hfgr hf) (surjective_restrict hggr hg)
    (exact_restrict hfgr hggr hfg)

end Exact

/-! ### Finite-dimensional graded vector spaces -/

open scoped Classical in
/-- The graded dimension `∑_d dim_k (ℳ d) q^d ∈ ℤ[q, q⁻¹]` of a family of subspaces with
finitely many nonzero dimensions (e.g. a finite-dimensional graded vector space); `0` by
convention otherwise. -/
noncomputable def gdimPoly (ℳ : ℤ → Submodule k M) : LaurentPolynomial ℤ :=
  if h : (support fun d => (finrank k (ℳ d) : ℤ)).Finite then Finsupp.ofSupportFinite _ h else 0

theorem finite_support_finrank (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [FiniteDimensional k M] : (support fun d => (finrank k (ℳ d) : ℤ)).Finite :=
  (Submodule.finite_ne_bot_of_iSupIndep
    (Decomposition.isInternal ℳ).submodule_iSupIndep).subset (support_finrank_subset ℳ)

theorem gdimPoly_apply (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [FiniteDimensional k M] (d : ℤ) : gdimPoly ℳ d = finrank k (ℳ d) := by
  simp [gdimPoly, finite_support_finrank ℳ, Finsupp.ofSupportFinite_coe]

/-- For a finite-dimensional graded vector space, `gdimPoly` and `gdim` agree. -/
theorem toLaurentSeries_gdimPoly (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [FiniteDimensional k M] : toLaurentSeries (gdimPoly ℳ) = gdim ℳ := by
  haveI := HasGdim.of_finiteDimensional ℳ
  ext d
  rw [coeff_toLaurentSeries, gdimPoly_apply, coeff_gdim]

/-- `gdim (M{a}) = q^a gdim M` for finite-dimensional `M`. -/
theorem gdimPoly_shift (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [FiniteDimensional k M]
    (a : ℤ) : gdimPoly (shift ℳ a) = LaurentPolynomial.T a * gdimPoly ℳ := by
  apply toLaurentSeries_injective
  rw [toLaurentSeries_gdimPoly, toLaurentSeries_T_mul, toLaurentSeries_gdimPoly, gdim_shift]

theorem gdimPoly_prod (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) [Decomposition ℳ]
    [Decomposition 𝒩] [FiniteDimensional k M] [FiniteDimensional k N] :
    gdimPoly (prod ℳ 𝒩) = gdimPoly ℳ + gdimPoly 𝒩 := by
  haveI := HasGdim.of_finiteDimensional ℳ
  haveI := HasGdim.of_finiteDimensional 𝒩
  apply toLaurentSeries_injective
  rw [toLaurentSeries_gdimPoly, map_add, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly,
    gdim_prod]

theorem gdimPoly_eq_add_of_exact_of_preservesGrading {ℳ : ℤ → Submodule k M}
    {𝒩 : ℤ → Submodule k N} {𝒬 : ℤ → Submodule k P} [Decomposition ℳ] [Decomposition 𝒩]
    [Decomposition 𝒬] [FiniteDimensional k N] {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (hfgr : PreservesGrading ℳ 𝒩 f) (hggr : PreservesGrading 𝒩 𝒬 g) (hf : Injective f)
    (hg : Surjective g) (hfg : Exact f g) : gdimPoly 𝒩 = gdimPoly ℳ + gdimPoly 𝒬 := by
  haveI := HasGdim.of_finiteDimensional 𝒩
  haveI : FiniteDimensional k M := FiniteDimensional.of_injective f hf
  haveI : FiniteDimensional k P := Module.Finite.of_surjective g hg
  apply toLaurentSeries_injective
  rw [map_add, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly, toLaurentSeries_gdimPoly,
    gdim_eq_add_of_exact_of_preservesGrading hfgr hggr hf hg hfg]

/-! ### Graded subspaces `e M` -/

section Idem

variable {A : Type*} [Ring A] [Algebra k A] [Module A M] [IsScalarTower k A M] [Module A N]
  [IsScalarTower k A N] [Module A P] [IsScalarTower k A P]

instance (ℳ : ℤ → Submodule k M) [HasGdim ℳ] (e : A) : HasGdim (idem ℳ e) where
  finiteDimensional d := FiniteDimensional.of_injective
    (V₂ := ℳ d) ({ toFun := fun x => ⟨((x : idemSubspace k M e) : M), x.2⟩
                   map_add' := fun _ _ => rfl
                   map_smul' := fun _ _ => rfl } : idem ℳ e d →ₗ[k] ℳ d)
    fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  bddBelow := BddBelow.mono (t := {d | ℳ d ≠ ⊥})
    (fun d (hd : idem ℳ e d ≠ ⊥) (hd' : ℳ d = ⊥) => hd <| by
    rw [eq_bot_iff]
    intro x hx
    have : (x : M) ∈ ℳ d := hx
    rw [hd', Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this) HasGdim.bddBelow

/-- An `A`-linear map `M → N` restricts to `e M → e N`. -/
def idemMap (e : A) (f : M →ₗ[A] N) : idemSubspace k M e →ₗ[k] idemSubspace k N e :=
  (f.restrictScalars k).restrict fun m hm => by
    rw [mem_idemSubspace] at hm ⊢
    rw [LinearMap.restrictScalars_apply, ← map_smul, hm]

@[simp] theorem idemMap_apply (e : A) (f : M →ₗ[A] N) (m : idemSubspace k M e) :
    (idemMap e f m : N) = f m := rfl

variable {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {𝒬 : ℤ → Submodule k P}

theorem PreservesGrading.idemMap {e : A} {f : M →ₗ[A] N} (hf : PreservesGrading ℳ 𝒩 f) :
    PreservesGrading (idem ℳ e) (idem 𝒩 e) (idemMap e f) := fun _ _ hx => hf hx

/-- Degree-preserving isomorphisms preserve the dimensions of the graded pieces. -/
theorem finrank_eq_of_gradedEquiv (f : ℳ ≃ᵍ[A] 𝒩) (d : ℤ) :
    finrank k (ℳ d) = finrank k (𝒩 d) :=
  ((f.toLinearEquiv.restrictScalars k).ofSubmodules (ℳ d) (𝒩 d) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact f.map_mem hx
    · intro hy
      exact ⟨f.toLinearEquiv.symm y, f.symm_map_mem' hy, f.toLinearEquiv.apply_symm_apply y⟩)).finrank_eq

theorem gdim_congr (f : ℳ ≃ᵍ[A] 𝒩) : gdim ℳ = gdim 𝒩 := by
  have h : (fun d => (finrank k (ℳ d) : ℤ)) = fun d => (finrank k (𝒩 d) : ℤ) :=
    funext fun d => by rw [finrank_eq_of_gradedEquiv f]
  unfold gdim
  rw [h]

theorem gdimPoly_congr (f : ℳ ≃ᵍ[A] 𝒩) : gdimPoly ℳ = gdimPoly 𝒩 := by
  have h : (fun d => (finrank k (ℳ d) : ℤ)) = fun d => (finrank k (𝒩 d) : ℤ) :=
    funext fun d => by rw [finrank_eq_of_gradedEquiv f]
  unfold gdimPoly
  rw [h]

/-- `M ↦ e M` is exact, so `gdim (e -)` is additive on short exact sequences of graded modules
with degree-preserving maps, for `e` of degree zero. -/
theorem gdim_idem_eq_add_of_exact {𝒜 : ℤ → Submodule k A} [SetLike.GradedMonoid 𝒜]
    [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬] [SetLike.GradedSMul 𝒜 ℳ]
    [SetLike.GradedSMul 𝒜 𝒩] [SetLike.GradedSMul 𝒜 𝒬] [HasGdim 𝒩] {e : A}
    (hidem : IsIdempotentElem e) (he : e ∈ 𝒜 0)
    {f : M →ₗ[A] N} {g : N →ₗ[A] P} (hfgr : PreservesGrading ℳ 𝒩 f)
    (hggr : PreservesGrading 𝒩 𝒬 g) (hf : Injective f) (hg : Surjective g) (hfg : Exact f g) :
    gdim (idem 𝒩 e) = gdim (idem ℳ e) + gdim (idem 𝒬 e) := by
  letI := idemDecomposition ℳ he
  letI := idemDecomposition 𝒩 he
  letI := idemDecomposition 𝒬 he
  refine gdim_eq_add_of_exact_of_preservesGrading hfgr.idemMap hggr.idemMap
    (fun x y h => Subtype.ext (hf (congrArg Subtype.val h))) (fun z => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := hg z
    refine ⟨⟨e • y, smul_mem_idemSubspace hidem y⟩, Subtype.ext ?_⟩
    show g (e • y) = z
    rw [map_smul, hy]
    exact z.2
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hfg y).1 (congrArg Subtype.val hy)
      refine ⟨⟨e • x, smul_mem_idemSubspace hidem x⟩, Subtype.ext ?_⟩
      show f (e • x) = y
      rw [map_smul, hx]
      exact y.2
    · rintro ⟨x, rfl⟩
      exact Subtype.ext ((hfg _).2 ⟨x, rfl⟩)

end Idem

end Categorification.Graded
