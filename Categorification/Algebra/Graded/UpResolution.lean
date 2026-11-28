/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.FiniteResolution
import Categorification.Algebra.Graded.ProjectiveCover
import Categorification.Algebra.Graded.K0Exact

/-!
# Graded projective resolutions in `C↑`

Let `A` be a finite-dimensional graded algebra over a field `k`. Following Beilinson–Ginzburg–
Soergel, *Koszul duality patterns in representation theory* (J. Amer. Math. Soc. 9 (1996)), §2.12,
`C↑(A)` is the category of complexes of graded modules whose degree `j` part in cohomological
degree `i` vanishes for `i ≫ 0` or `i + j ≪ 0`. B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Theorem 5.28, asks for projective resolutions of
simple modules in this category. For a resolution `⋯ → P_1 → P_0 → N` (with `P_n` in
cohomological degree `-n`) the condition says: for some `c`, `P_n` vanishes in degrees `< n - c`.

A resolution is recorded as a chain of short exact sequences `0 → Ω_{n+1} → P_n → Ω_n → 0`
with `Ω_0 ≅ N` (`GFin.UpResolution N c`). This file proves the gluing steps of Webster's proof
of Theorem 5.28 and of Lemma 5.29 for such resolutions.

## Main definitions and results

* `GFin.UpResolution N c` : a resolution of `N` by finitely generated graded projectives `P_n`
  vanishing in degrees `< n - c`.
* `GFin.UpResolution.horseshoe` : an up-resolution of the middle term of a short exact sequence,
  from up-resolutions of the outer terms (Webster, Lemma 5.29, for `C↑`).
* `GFin.UpResolution.ofQuotient` : an up-resolution of `L` from up-resolutions of `K` and `M`,
  for a short exact sequence `0 → K → M → L → 0` (the cone step of Webster's proof).
* `GFin.UpResolution.shift`, `GFin.UpResolution.mono`, `GFin.UpResolution.congr`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Function

universe u

variable {k : Type u} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] [Module.Finite k A]

namespace GFin

section Kernels

/-- The kernel of a degree-preserving map, as a finite-dimensional graded module. -/
abbrev ker {M N : GFin 𝒜} (f : M.carrier →ₗ[A] N.carrier)
    (hf : PreservesGrading M.grading N.grading f) : GFin 𝒜 :=
  letI := submoduleDecomposition M.grading (isHomogeneous_ker hf)
  { carrier := LinearMap.ker f
    grading := submodule M.grading (LinearMap.ker f)
    finiteDimensional := Module.Finite.of_injective
      ((LinearMap.ker f).subtype.restrictScalars k) Subtype.val_injective }

/-- `0 → ker f → M → N → 0` for a surjective degree-preserving `f`. -/
def kerShortExact {M N : GFin 𝒜} (f : M.carrier →ₗ[A] N.carrier)
    (hf : PreservesGrading M.grading N.grading f) (hs : Surjective f) :
    ShortExact (ker f hf) M N where
  f := (LinearMap.ker f).subtype
  g := f
  preservesGrading_f := fun _ _ hx => hx
  preservesGrading_g := hf
  injective := Subtype.val_injective
  surjective := hs
  exact := LinearMap.exact_subtype_ker_map _

/-- Factor a map `h : Z → Y` through an injective degree-preserving `f : X → Y` whose range
contains the range of `h`. -/
def liftOfRange {X Y Z : GFin 𝒜} (f : X.carrier →ₗ[A] Y.carrier) (hinj : Injective f)
    (h : Z.carrier →ₗ[A] Y.carrier) (hr : ∀ z, h z ∈ LinearMap.range f) :
    Z.carrier →ₗ[A] X.carrier :=
  (LinearEquiv.ofInjective f hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ h hr

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem apply_liftOfRange {X Y Z : GFin 𝒜} (f : X.carrier →ₗ[A] Y.carrier) (hinj : Injective f)
    (h : Z.carrier →ₗ[A] Y.carrier) (hr : ∀ z, h z ∈ LinearMap.range f) (z : Z.carrier) :
    f (liftOfRange f hinj h hr z) = h z := by
  have := (LinearEquiv.ofInjective f hinj).apply_symm_apply (LinearMap.codRestrict _ h hr z)
  exact congrArg Subtype.val this

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem preservesGrading_liftOfRange {X Y Z : GFin 𝒜} {f : X.carrier →ₗ[A] Y.carrier}
    (hf : PreservesGrading X.grading Y.grading f) (hinj : Injective f)
    {h : Z.carrier →ₗ[A] Y.carrier} (hh : PreservesGrading Z.grading Y.grading h)
    (hr : ∀ z, h z ∈ LinearMap.range f) :
    PreservesGrading Z.grading X.grading (liftOfRange f hinj h hr) := fun _ z hz =>
  mem_of_injective_of_mem hf hinj (by rw [apply_liftOfRange]; exact hh hz)

end Kernels

/-- Transport a short exact sequence along isomorphisms of its outer terms. -/
def ShortExact.congr {M M' N P P' : GFin 𝒜} (S : ShortExact M N P) (e₁ : M'.Iso M)
    (e₃ : P.Iso P') : ShortExact M' N P' where
  f := S.f ∘ₗ e₁.toLinearEquiv.toLinearMap
  g := e₃.toLinearEquiv.toLinearMap ∘ₗ S.g
  preservesGrading_f _ _ hx := S.preservesGrading_f (e₁.map_mem' hx)
  preservesGrading_g _ _ hx := e₃.map_mem' (S.preservesGrading_g hx)
  injective := S.injective.comp e₁.toLinearEquiv.injective
  surjective := e₃.toLinearEquiv.surjective.comp S.surjective
  exact := by
    intro y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, Set.mem_range]
    rw [LinearEquiv.map_eq_zero_iff, S.exact y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e₁.toLinearEquiv.symm x, by rw [LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩

/-- **A graded projective resolution in `C↑`** (Beilinson–Ginzburg–Soergel §2.12, as used in
Webster, arXiv:1309.3796v3, Theorem 5.28): short exact sequences `0 → Ω_{n+1} → P_n → Ω_n → 0`
with `Ω_0 ≅ N`, each `P_n` finitely generated graded projective and zero in degrees `< n - c`. -/
structure UpResolution (N : GFin 𝒜) (c : ℤ) where
  /-- The syzygies `Ω_n`. -/
  syz : ℕ → GFin 𝒜
  /-- The projective terms `P_n`. -/
  term : ℕ → GFin 𝒜
  /-- Each `P_n` is projective. -/
  projective : ∀ n, Module.Projective A (term n).carrier
  /-- `Ω_0 ≅ N`. -/
  iso : (syz 0).Iso N
  /-- `0 → Ω_{n+1} → P_n → Ω_n → 0`. -/
  ses : ∀ n, ShortExact (syz (n + 1)) (term n) (syz n)
  /-- `P_n` vanishes in degrees `< n - c`. -/
  vanish : ∀ (n : ℕ) (j : ℤ), j < n - c → (term n).grading j = ⊥

namespace UpResolution

variable {N N' : GFin 𝒜} {c c' : ℤ}

/-- A larger constant. -/
def mono (R : UpResolution N c) (h : c ≤ c') : UpResolution N c' where
  syz := R.syz
  term := R.term
  projective := R.projective
  iso := R.iso
  ses := R.ses
  vanish n j hj := R.vanish n j (by omega)

/-- Transport along an isomorphism. -/
def congr (R : UpResolution N c) (e : N.Iso N') : UpResolution N' c where
  syz := R.syz
  term := R.term
  projective := R.projective
  iso := R.iso.trans e
  ses := R.ses
  vanish := R.vanish

/-- The resolution of the first syzygy, `⋯ → P_2 → P_1 → Ω_1`. -/
def tail (R : UpResolution N c) : UpResolution (R.syz 1) (c - 1) where
  syz n := R.syz (n + 1)
  term n := R.term (n + 1)
  projective n := R.projective (n + 1)
  iso := GradedEquiv.refl _
  ses n := R.ses (n + 1)
  vanish n j hj := R.vanish (n + 1) j (by push_cast; omega)

/-- Prepend a projective cover `0 → K → P → N → 0`. -/
def cons {K : GFin 𝒜} {P : GFin 𝒜} [Module.Projective A P.carrier] (S : ShortExact K P N)
    (hP : ∀ j : ℤ, j < -c → P.grading j = ⊥) (R : UpResolution K c) :
    UpResolution N (c + 1) where
  syz
    | 0 => N
    | n + 1 => R.syz n
  term
    | 0 => P
    | n + 1 => R.term n
  projective
    | 0 => inferInstance
    | n + 1 => R.projective n
  iso := GradedEquiv.refl _
  ses
    | 0 => S.congr R.iso (GradedEquiv.refl _)
    | n + 1 => R.ses n
  vanish
    | 0, j, hj => hP j (by omega)
    | n + 1, j, hj => R.vanish n j (by push_cast at hj; omega)

/-- The shift `N{a}`. -/
def shift (R : UpResolution N c) (a : ℤ) : UpResolution (N.shift a) (c - a) where
  syz n := (R.syz n).shift a
  term n := (R.term n).shift a
  projective n := R.projective n
  iso := R.iso.shift a
  ses n := (R.ses n).shift a
  vanish n j hj := R.vanish n (j - a) (by omega)

section Horseshoe

variable {Y' Y Y'' K' K'' : GFin 𝒜} {P' P'' : GFin 𝒜} [Module.Projective A P''.carrier]

/-- The lift `P'' → Y` of the cover `P'' → Y''` in the horseshoe. -/
def horseLift (S : ShortExact Y' Y Y'') (S'' : ShortExact K'' P'' Y'') :
    P''.carrier →ₗ[A] Y.carrier :=
  (exists_lift_of_projective 𝒜 S.preservesGrading_g S.surjective
    S''.preservesGrading_g).choose

omit [Module.Finite k A] in
theorem preservesGrading_horseLift (S : ShortExact Y' Y Y'')
    (S'' : ShortExact K'' P'' Y'') :
    PreservesGrading P''.grading Y.grading (horseLift S S'') :=
  (exists_lift_of_projective 𝒜 S.preservesGrading_g S.surjective
    S''.preservesGrading_g).choose_spec.1

omit [Module.Finite k A] in
theorem g_horseLift (S : ShortExact Y' Y Y'') (S'' : ShortExact K'' P'' Y'')
    (x : P''.carrier) : S.g (horseLift S S'' x) = S''.g x :=
  LinearMap.congr_fun (exists_lift_of_projective 𝒜 S.preservesGrading_g
    S.surjective S''.preservesGrading_g).choose_spec.2 x

/-- The horseshoe map `P' ⊕ P'' → Y`. -/
def horseMap (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : (P'.prod P'').carrier →ₗ[A] Y.carrier :=
  LinearMap.coprod (S.f ∘ₗ S'.g) (horseLift S S'')

omit [Module.Finite k A] in
theorem preservesGrading_horseMap (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') :
    PreservesGrading (P'.prod P'').grading Y.grading (horseMap S S' S'') :=
  fun _ _ hx => add_mem (S.preservesGrading_f (S'.preservesGrading_g hx.1))
    (preservesGrading_horseLift S S'' hx.2)

omit [Module.Finite k A] in
theorem g_horseMap (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') (x : (P'.prod P'').carrier) :
    S.g (horseMap S S' S'' x) = S''.g x.2 := by
  rcases x with ⟨x₁, x₂⟩
  have h0 : S.g (S.f (S'.g x₁)) = 0 := (S.exact _).2 ⟨_, rfl⟩
  change S.g (S.f (S'.g x₁) + horseLift S S'' x₂) = S''.g x₂
  rw [map_add, h0, g_horseLift, zero_add]

omit [Module.Finite k A] in
theorem horseMap_surjective (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : Surjective (horseMap S S' S'') := by
  intro y
  obtain ⟨p'', hp''⟩ := S''.surjective (S.g y)
  have hz : S.g (y - horseLift S S'' p'') = 0 := by rw [map_sub, g_horseLift, hp'', sub_self]
  obtain ⟨y', hy'⟩ := (S.exact _).1 hz
  obtain ⟨p', rfl⟩ := S'.surjective y'
  refine ⟨(p', p''), ?_⟩
  change S.f (S'.g p') + horseLift S S'' p'' = y
  rw [hy', sub_add_cancel]

/-- The kernel of the horseshoe map. -/
abbrev horseKer (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : GFin 𝒜 :=
  ker (horseMap S S' S'') (preservesGrading_horseMap S S' S'')

/-- `0 → horseKer → P' ⊕ P'' → Y → 0`. -/
def horseCover (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') :
    ShortExact (horseKer S S' S'') (P'.prod P'') Y :=
  kerShortExact _ _ (horseMap_surjective S S' S'')

/-- The map `K' → horseKer`, `x ↦ (x, 0)`. -/
def horseIn (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : K'.carrier →ₗ[A] (horseKer S S' S'').carrier :=
  LinearMap.codRestrict _ (LinearMap.inl A _ _ ∘ₗ S'.f) fun x => by
    have h0 : S'.g (S'.f x) = 0 := (S'.exact _).2 ⟨_, rfl⟩
    change S.f (S'.g (S'.f x)) + horseLift S S'' 0 = 0
    rw [h0, map_zero, map_zero, add_zero]

/-- An element of `horseKer` in `P' ⊕ P''`. -/
abbrev hv {S : ShortExact Y' Y Y''} {S' : ShortExact K' P' Y'} {S'' : ShortExact K'' P'' Y''}
    (x : (horseKer S S' S'').carrier) : P'.carrier × P''.carrier :=
  (show LinearMap.ker (horseMap S S' S'') from x).1

omit [Module.Finite k A] in
theorem horseMap_hv {S : ShortExact Y' Y Y''} {S' : ShortExact K' P' Y'}
    {S'' : ShortExact K'' P'' Y''} (x : (horseKer S S' S'').carrier) :
    horseMap S S' S'' (hv x) = 0 :=
  (show LinearMap.ker (horseMap S S' S'') from x).2

omit [Module.Finite k A] in
theorem hv_injective {S : ShortExact Y' Y Y''} {S' : ShortExact K' P' Y'}
    {S'' : ShortExact K'' P'' Y''} : Injective (hv (S := S) (S' := S') (S'' := S'')) :=
  Subtype.val_injective

omit [Module.Finite k A] in
theorem snd_mem_range (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') (x : (horseKer S S' S'').carrier) :
    (hv x).2 ∈ LinearMap.range S''.f := by
  refine (S''.exact _).1 ?_
  rw [← g_horseMap S S' S'', horseMap_hv, map_zero]

/-- The map `horseKer → K''`, `(x', x'') ↦ x''`. -/
def horseOut (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : (horseKer S S' S'').carrier →ₗ[A] K''.carrier :=
  liftOfRange (Z := horseKer S S' S'') S''.f S''.injective
    (LinearMap.snd A _ _ ∘ₗ (LinearMap.ker (horseMap S S' S'')).subtype)
    (snd_mem_range S S' S'')

omit [Module.Finite k A] in
theorem f_horseOut (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') (x : (horseKer S S' S'').carrier) :
    S''.f (horseOut S S' S'' x) = (hv x).2 :=
  apply_liftOfRange _ _ _ _ x

omit [Module.Finite k A] in
theorem hv_horseIn (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') (x : K'.carrier) :
    hv (horseIn S S' S'' x) = (S'.f x, 0) := rfl

/-- `0 → K' → horseKer → K'' → 0`. -/
def horseSES (S : ShortExact Y' Y Y'') (S' : ShortExact K' P' Y')
    (S'' : ShortExact K'' P'' Y'') : ShortExact K' (horseKer S S' S'') K'' where
  f := horseIn S S' S''
  g := horseOut S S' S''
  preservesGrading_f _ _ hx := show (_, _) ∈ (P'.prod P'').grading _ from
    ⟨S'.preservesGrading_f hx, zero_mem _⟩
  preservesGrading_g := preservesGrading_liftOfRange S''.preservesGrading_f S''.injective
    (fun _ x hx => (show hv x ∈ (P'.prod P'').grading _ from hx).2) _
  injective x y h := S'.injective (by
    have := congrArg (fun z => (hv z).1) h
    exact this)
  surjective := by
    intro z
    have hz : S.g (horseLift S S'' (S''.f z)) = 0 := by
      rw [g_horseLift]; exact (S''.exact _).2 ⟨_, rfl⟩
    obtain ⟨y', hy'⟩ := (S.exact _).1 hz
    obtain ⟨p', rfl⟩ := S'.surjective y'
    have hm : horseMap S S' S'' (-p', S''.f z) = 0 := by
      change S.f (S'.g (-p')) + horseLift S S'' (S''.f z) = 0
      rw [map_neg, map_neg, hy', neg_add_cancel]
    refine ⟨(⟨(-p', S''.f z), hm⟩ : LinearMap.ker (horseMap S S' S'')), S''.injective ?_⟩
    rw [f_horseOut]
  exact := by
    intro x
    constructor
    · intro hx
      have h2 : (hv x).2 = 0 := by
        rw [← f_horseOut, hx, map_zero]
      have h1 : S.f (S'.g (hv x).1) = 0 := by
        have h := horseMap_hv x
        have hx' : hv x = ((hv x).1, 0) := Prod.ext rfl h2
        rw [hx'] at h
        change S.f (S'.g (hv x).1) + horseLift S S'' 0 = 0 at h
        rwa [map_zero, add_zero] at h
      rw [← map_zero S.f] at h1
      obtain ⟨y, hy⟩ := (S'.exact _).1 (S.injective h1)
      refine ⟨y, hv_injective ?_⟩
      rw [hv_horseIn, hy]
      exact Prod.ext rfl h2.symm
    · rintro ⟨y, rfl⟩
      apply S''.injective
      rw [f_horseOut, map_zero, hv_horseIn]

/-- The short exact sequences of the horseshoe, step by step. -/
def horseState (S : ShortExact N' N N'') (R' : UpResolution N' c) (R'' : UpResolution N'' c) :
    (n : ℕ) → Σ Y : GFin 𝒜, ShortExact (R'.syz n) Y (R''.syz n)
  | 0 => ⟨N, S.congr R'.iso R''.iso.symm⟩
  | n + 1 =>
    letI := R''.projective n
    ⟨horseKer (horseState S R' R'' n).2 (R'.ses n) (R''.ses n),
      horseSES (horseState S R' R'' n).2 (R'.ses n) (R''.ses n)⟩

/-- **The horseshoe lemma in `C↑`** (Webster, arXiv:1309.3796v3, Lemma 5.29, for resolutions in
`C↑`): up-resolutions of the outer terms of `0 → N' → N → N'' → 0` give one of `N`, with terms
`P'_n ⊕ P''_n`. -/
def horseshoe {N'' : GFin 𝒜} (S : ShortExact N' N N'') (R' : UpResolution N' c)
    (R'' : UpResolution N'' c) : UpResolution N c where
  syz n := (horseState S R' R'' n).1
  term n := (R'.term n).prod (R''.term n)
  projective n := by
    have := R'.projective n
    have := R''.projective n
    exact inferInstanceAs (Module.Projective A ((R'.term n).carrier × (R''.term n).carrier))
  iso := GradedEquiv.refl _
  ses n :=
    letI := R''.projective n
    horseCover (horseState S R' R'' n).2 (R'.ses n) (R''.ses n)
  vanish n j hj := by
    change Submodule.prod ((R'.term n).grading j) ((R''.term n).grading j) = ⊥
    rw [R'.vanish n j hj, R''.vanish n j hj, Submodule.prod_bot]

end Horseshoe

section Quotient

variable {K M L : GFin 𝒜}

/-- The cover `P_0 → M → L`. -/
def quotMap (S : ShortExact K M L) (RM : UpResolution M c) :
    (RM.term 0).carrier →ₗ[A] L.carrier :=
  S.g ∘ₗ RM.iso.toLinearEquiv.toLinearMap ∘ₗ (RM.ses 0).g

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem preservesGrading_quotMap (S : ShortExact K M L) (RM : UpResolution M c) :
    PreservesGrading (RM.term 0).grading L.grading (quotMap S RM) :=
  fun _ _ hx => S.preservesGrading_g (RM.iso.map_mem' ((RM.ses 0).preservesGrading_g hx))

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem quotMap_surjective (S : ShortExact K M L) (RM : UpResolution M c) :
    Surjective (quotMap S RM) :=
  S.surjective.comp (RM.iso.toLinearEquiv.surjective.comp (RM.ses 0).surjective)

/-- The map `P_0 → M` of the resolution of `M`. -/
def coverM (RM : UpResolution M c) : (RM.term 0).carrier →ₗ[A] M.carrier :=
  RM.iso.toLinearEquiv.toLinearMap ∘ₗ (RM.ses 0).g

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem coverM_surjective (RM : UpResolution M c) : Surjective (coverM RM) :=
  RM.iso.toLinearEquiv.surjective.comp (RM.ses 0).surjective

/-- An element of `ker(P_0 → L)` in `P_0`. -/
abbrev qv {S : ShortExact K M L} {RM : UpResolution M c}
    (x : (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier) : (RM.term 0).carrier :=
  (show LinearMap.ker (quotMap S RM) from x).1

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem quotMap_qv {S : ShortExact K M L} {RM : UpResolution M c}
    (x : (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier) :
    S.g (coverM RM (qv x)) = 0 :=
  (show LinearMap.ker (quotMap S RM) from x).2

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem coverM_mem_range (S : ShortExact K M L) (RM : UpResolution M c)
    (x : (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier) :
    coverM RM (qv x) ∈ LinearMap.range S.f :=
  (S.exact _).1 (quotMap_qv x)

/-- The map `ker(P_0 → L) → K`. -/
def quotOut (S : ShortExact K M L) (RM : UpResolution M c) :
    (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier →ₗ[A] K.carrier :=
  liftOfRange (Z := ker (quotMap S RM) (preservesGrading_quotMap S RM)) S.f S.injective
    (coverM RM ∘ₗ (LinearMap.ker (quotMap S RM)).subtype) (coverM_mem_range S RM)

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem f_quotOut (S : ShortExact K M L) (RM : UpResolution M c)
    (x : (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier) :
    S.f (quotOut S RM x) = coverM RM (qv x) :=
  apply_liftOfRange _ _ _ _ x

/-- The map `Ω_1(M) → ker(P_0 → L)`. -/
def quotIn (S : ShortExact K M L) (RM : UpResolution M c) :
    (RM.syz 1).carrier →ₗ[A] (ker (quotMap S RM) (preservesGrading_quotMap S RM)).carrier :=
  LinearMap.codRestrict _ (RM.ses 0).f fun x => by
    have h0 : (RM.ses 0).g ((RM.ses 0).f x) = 0 := ((RM.ses 0).exact _).2 ⟨_, rfl⟩
    change S.g (RM.iso.toLinearEquiv ((RM.ses 0).g ((RM.ses 0).f x))) = 0
    rw [h0, map_zero, map_zero]

omit [GradedAlgebra 𝒜] [Module.Finite k A] in
theorem qv_quotIn (S : ShortExact K M L) (RM : UpResolution M c) (x : (RM.syz 1).carrier) :
    qv (quotIn S RM x) = (RM.ses 0).f x := rfl

/-- `0 → Ω_1(M) → ker(P_0 → L) → K → 0`. -/
def quotSES (S : ShortExact K M L) (RM : UpResolution M c) :
    ShortExact (RM.syz 1) (ker (quotMap S RM) (preservesGrading_quotMap S RM)) K where
  f := quotIn S RM
  g := quotOut S RM
  preservesGrading_f _ _ hx := (RM.ses 0).preservesGrading_f hx
  preservesGrading_g _ x hx := mem_of_injective_of_mem S.preservesGrading_f S.injective (by
    rw [f_quotOut]
    exact RM.iso.map_mem' ((RM.ses 0).preservesGrading_g
      (show qv x ∈ (RM.term 0).grading _ from hx)))
  injective x y h := (RM.ses 0).injective (by
    have := congrArg qv h
    exact this)
  surjective := by
    intro z
    obtain ⟨p, hp⟩ := coverM_surjective RM (S.f z)
    have hm : S.g (coverM RM p) = 0 := by rw [hp]; exact (S.exact _).2 ⟨_, rfl⟩
    refine ⟨(⟨p, hm⟩ : LinearMap.ker (quotMap S RM)), S.injective ?_⟩
    rw [f_quotOut]
    exact hp
  exact := by
    intro x
    constructor
    · intro hx
      have h : coverM RM (qv x) = 0 := by rw [← f_quotOut, hx, map_zero]
      have h' : (RM.ses 0).g (qv x) = 0 := RM.iso.toLinearEquiv.injective (by
        rw [map_zero]; exact h)
      obtain ⟨y, hy⟩ := ((RM.ses 0).exact _).1 h'
      refine ⟨y, ?_⟩
      apply Subtype.val_injective (a₁ := (show LinearMap.ker (quotMap S RM) from quotIn S RM y))
      exact hy
    · rintro ⟨y, rfl⟩
      apply S.injective
      rw [f_quotOut, map_zero, qv_quotIn]
      change RM.iso.toLinearEquiv ((RM.ses 0).g ((RM.ses 0).f y)) = 0
      rw [((RM.ses 0).exact _).2 ⟨_, rfl⟩, map_zero]

/-- **Up-resolutions of quotients** (the cone step in Webster's proof of arXiv:1309.3796v3,
Theorem 5.28): for `0 → K → M → L → 0`, up-resolutions of `K` and `M` give one of `L`. Its terms
are `P_0(M)` and then the terms of the horseshoe of `0 → Ω_1(M) → ker(P_0 → L) → K → 0`. -/
def ofQuotient (S : ShortExact K M L) (RK : UpResolution K c) (RM : UpResolution M c) :
    UpResolution L (c + 1) :=
  haveI := RM.projective 0
  cons (kerShortExact _ _ (quotMap_surjective S RM)) (fun j hj => RM.vanish 0 j (by omega))
    (horseshoe (quotSES S RM) (RM.tail.mono (by omega)) RK)

end Quotient

end UpResolution

end GFin

end Categorification.Graded
