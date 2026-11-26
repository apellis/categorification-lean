/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ExtensionK0
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Extension of scalars along a quotient that is injective in degree zero

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 4.39: the functor `𝔯_N` from `T̃^λ`-modules to `T^{Nλ₀,λ}`-modules is full, and
faithful in each fixed degree once `N` is large. On projective Grothendieck groups only degree
zero matters.

Let `φ : R → S` be a surjective degree-preserving homomorphism of graded algebras over a field,
injective on `R_0`, with `R` locally finite and bounded below (`HasGdim`). Then extension of
scalars `K₀(R) → K₀(S)` is bijective (`extensionK0_bijective`). Surjectivity is
`extensionK0_surjective`. For injectivity, every indecomposable graded projective is `R e {j}`
for an idempotent `e ∈ R_0` (`GProj.IsIndec.exists_iso_ofIdempotent`); its extension is
`S φ(e)`, whose degree-zero endomorphisms `φ(e) S_0 φ(e) = φ(e R_0 e)` are those of `R e`, so it
is indecomposable (`isIndec_ofIdempotent_map`). Isomorphisms between such modules are given by
pairs of elements, which lift to `R` because `φ` is onto and injective in degree zero
(`nonempty_iso_of_map`). So extension sends the basis of indecomposables to unit multiples of
distinct basis vectors.

## Main results

* `leftIdeal_linearMap_apply` : a module map `R e → R e'` is right multiplication by the image
  of `e`.
* `exists_mul_eq_of_iso` : an isomorphism `(R e){a} ≅ R e'` comes from `x ∈ e R_a e'`,
  `y ∈ e' R_{-a} e` with `x y = e`, `y x = e'`.
* `isIndec_ofIdempotent_map`, `nonempty_iso_of_map`.
* `extensionK0_injective`, `extensionK0_bijective`.
-/

noncomputable section
namespace Categorification.Graded

open MulOpposite GProj

universe u

section LeftIdeal

variable {R : Type u} [Ring R]

/-- A module map `R e → R e'` is right multiplication by the image of `e`. -/
theorem leftIdeal_linearMap_apply {e e' : R} (he : IsIdempotentElem e)
    (f : leftIdeal e →ₗ[R] leftIdeal e') (x : leftIdeal e) :
    (f x : R) = (x : R) * (f ⟨e, he.eq⟩ : R) := by
  have hx : x = (x : R) • (⟨e, he.eq⟩ : leftIdeal e) := Subtype.ext x.2.symm
  conv_lhs => rw [hx, map_smul]
  rfl

theorem leftIdeal_eq_bot_of_eq_zero {e : R} (he : e = 0) (x : leftIdeal e) : (x : R) = 0 := by
  obtain ⟨y, hy⟩ := x
  rw [mem_leftIdeal, he, mul_zero] at hy
  exact hy.symm

end LeftIdeal

variable {k : Type*} [Field k] {R S : Type u} [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {𝓡 : ℤ → Submodule k R} {𝓢 : ℤ → Submodule k S} [GradedAlgebra 𝓡] [GradedAlgebra 𝓢]

/-- An isomorphism `(R e){a} ≅ R e'` of graded left ideals is right multiplication by some
`x ∈ e R_a e'` with inverse right multiplication by `y ∈ e' R_{-a} e`. -/
theorem exists_mul_eq_of_iso {e e' : R} {he : IsIdempotentElem e} {he' : IsIdempotentElem e'}
    {he0 : e ∈ 𝓡 0} {he0' : e' ∈ 𝓡 0} {a : ℤ}
    (ψ : ((GProj.ofIdempotent e he he0).shift a).Iso (GProj.ofIdempotent e' he' he0')) :
    ∃ x ∈ 𝓡 a, ∃ y ∈ 𝓡 (-a), x * y = e ∧ y * x = e' ∧ e * x = x ∧ x * e' = x ∧
      e' * y = y ∧ y * e = y := by
  let f : leftIdeal e →ₗ[R] leftIdeal e' := ψ.toLinearEquiv.toLinearMap
  let g : leftIdeal e' →ₗ[R] leftIdeal e := ψ.toLinearEquiv.symm.toLinearMap
  let x : R := (f ⟨e, he.eq⟩ : R)
  let y : R := (g ⟨e', he'.eq⟩ : R)
  have hfg : ∀ z, f (g z) = z := ψ.toLinearEquiv.apply_symm_apply
  have hgf : ∀ z, g (f z) = z := ψ.toLinearEquiv.symm_apply_apply
  have hxa : x ∈ 𝓡 a := by
    have h : (⟨e, he.eq⟩ : leftIdeal e) ∈ ((GProj.ofIdempotent e he he0).shift a).grading a :=
      show (e : R) ∈ 𝓡 (a - a) by rw [sub_self]; exact he0
    exact ψ.map_mem' h
  have hya : y ∈ 𝓡 (-a) := by
    have h : (⟨e', he'.eq⟩ : leftIdeal e') ∈ (GProj.ofIdempotent e' he' he0').grading 0 := he0'
    have h' := ψ.symm_map_mem' h
    change (y : R) ∈ 𝓡 (0 - a) at h'
    simpa using h'
  have hxy : x * y = e := by
    have h := leftIdeal_linearMap_apply he' g (f ⟨e, he.eq⟩)
    rw [hgf] at h
    exact h.symm
  have hyx : y * x = e' := by
    have h := leftIdeal_linearMap_apply he f (g ⟨e', he'.eq⟩)
    rw [hfg] at h
    exact h.symm
  refine ⟨x, hxa, y, hya, hxy, hyx, ?_, (f ⟨e, he.eq⟩).2, ?_, (g ⟨e', he'.eq⟩).2⟩
  · have h := leftIdeal_linearMap_apply he f ⟨e, he.eq⟩
    exact h.symm
  · have h := leftIdeal_linearMap_apply he' g ⟨e', he'.eq⟩
    exact h.symm

variable (φ : R →ₐ[k] S) (hφ : PreservesGrading 𝓡 𝓢 φ.toLinearMap)
  (hs : Function.Surjective φ) (h0 : ∀ x ∈ 𝓡 0, φ x = 0 → x = 0)

include hφ hs in
private theorem exists_preimage_mem {d : ℤ} {z : S} (hz : z ∈ 𝓢 d) : ∃ w ∈ 𝓡 d, φ w = z := by
  rw [grade_eq_map_of_surjective 𝓡 𝓢 φ hφ hs d] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, rfl⟩

omit [GradedAlgebra 𝓡] [GradedAlgebra 𝓢] in
include h0 in
private theorem eq_of_map_eq {x y : R} (hx : x ∈ 𝓡 0) (hy : y ∈ 𝓡 0) (h : φ x = φ y) : x = y :=
  sub_eq_zero.mp (h0 _ (sub_mem hx hy) (by rw [map_sub, h, sub_self]))

include hφ hs h0 in
/-- **Indecomposability is preserved**: if `R e` is indecomposable then so is `S φ(e)`,
since the degree-zero endomorphisms `φ(e) S_0 φ(e)` lift to `e R_0 e`. -/
theorem isIndec_ofIdempotent_map {e : R} (he : IsIdempotentElem e) (he0 : e ∈ 𝓡 0)
    (hP : (GProj.ofIdempotent e he he0).IsIndec R) :
    (GProj.ofIdempotent (φ e) (he.map φ) (hφ he0)).IsIndec S := by
  have hne : e ≠ 0 := by
    intro h
    obtain ⟨u, v, huv⟩ := hP.nontrivial.exists_pair_ne
    exact huv (Subtype.ext ((leftIdeal_eq_bot_of_eq_zero h u).trans
      (leftIdeal_eq_bot_of_eq_zero h v).symm))
  have hφne : φ e ≠ 0 := fun h => hne (h0 e he0 h)
  refine ⟨⟨⟨⟨φ e, (he.map φ).eq⟩, 0, fun h => hφne (congrArg Subtype.val h)⟩⟩, ?_⟩
  intro g' hg hgid
  let g : Module.End S (leftIdeal (φ e)) := g'
  let eb : leftIdeal (φ e) := ⟨φ e, (he.map φ).eq⟩
  set zb : S := (g eb : S) with hzb
  have hg_apply : ∀ x : leftIdeal (φ e), (g x : S) = (x : S) * zb :=
    fun x => leftIdeal_linearMap_apply (he.map φ) g x
  have hzb0 : zb ∈ 𝓢 0 := hg (x := eb) (hφ he0)
  have hzbe : zb * φ e = zb := (g eb).2
  have heZ : φ e * zb = zb := by rw [hzb, ← hg_apply eb]
  have hzbzb : zb * zb = zb := by
    have h := congrArg (fun f : Module.End S (leftIdeal (φ e)) => (f eb : S)) hgid.eq
    change (g (g eb) : S) = (g eb : S) at h
    rw [hg_apply (g eb)] at h
    exact h
  obtain ⟨z₀, hz₀, hz₀φ⟩ := exists_preimage_mem φ hφ hs hzb0
  set z : R := e * z₀ * e with hzdef
  have hz0 : z ∈ 𝓡 0 := by
    have := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem he0 hz₀) he0
    simpa using this
  have hφz : φ z = zb := by rw [hzdef, map_mul, map_mul, hz₀φ, heZ, hzbe]
  have hzz : z * z = z := eq_of_map_eq φ h0 (by simpa using SetLike.GradedMul.mul_mem hz0 hz0)
    hz0 (by rw [map_mul, hφz, hzbzb])
  have hze : z * e = z := by rw [hzdef, mul_assoc, he.eq]
  have hez : e * z = z := by rw [hzdef, ← mul_assoc, ← mul_assoc, he.eq]
  let h : Module.End R (leftIdeal e) :=
    { toFun := fun x => ⟨(x : R) * z, by rw [mem_leftIdeal, mul_assoc, hze]⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun c x => Subtype.ext (mul_assoc _ _ _) }
  have hh : h ∈ endZero R (GProj.ofIdempotent e he he0).grading := by
    intro d x hx
    have := SetLike.GradedMul.mul_mem (show (x.1 : R) ∈ 𝓡 d from hx) hz0
    rw [add_zero] at this
    exact this
  have hhid : IsIdempotentElem h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (x : R) * z * z = (x : R) * z
    rw [mul_assoc, hzz]
  have hgform : ∀ c : S, (∀ x : leftIdeal (φ e), (g x : S) = (x : S) * c) →
      c * φ e = c → (c = 0 → g = 0) ∧ (c = φ e → g = 1) := by
    intro c hc _
    refine ⟨fun hc0 => ?_, fun hc1 => ?_⟩
    · apply LinearMap.ext; intro x; apply Subtype.ext
      rw [hc, hc0, mul_zero]; rfl
    · apply LinearMap.ext; intro x; apply Subtype.ext
      rw [hc, hc1]; exact x.2
  rcases hP.eq_zero_or_eq_one h hh hhid with h1 | h1
  · left
    have hz : z = 0 := by
      have := congrArg (fun f : Module.End R (leftIdeal e) => (f ⟨e, he.eq⟩ : R)) h1
      change e * z = 0 at this
      rwa [hez] at this
    refine (hgform zb hg_apply hzbe).1 ?_
    rw [← hφz, hz, map_zero]
  · right
    have hz : z = e := by
      have := congrArg (fun f : Module.End R (leftIdeal e) => (f ⟨e, he.eq⟩ : R)) h1
      change e * z = e at this
      rwa [hez] at this
    refine (hgform zb hg_apply hzbe).2 ?_
    rw [← hφz, hz]

include hφ hs h0 in
/-- **Isomorphisms lift**: `(S φ(e)){a} ≅ S φ(e')` implies `(R e){a} ≅ R e'`. -/
theorem nonempty_iso_of_map [HasGdim 𝓡] {e e' : R} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (he0 : e ∈ 𝓡 0) (he0' : e' ∈ 𝓡 0) {a : ℤ}
    (ψ : ((GProj.ofIdempotent (φ e) (he.map φ) (hφ he0)).shift a).Iso
      (GProj.ofIdempotent (φ e') (he'.map φ) (hφ he0'))) :
    Nonempty (((GProj.ofIdempotent e he he0).shift a).Iso (GProj.ofIdempotent e' he' he0')) := by
  obtain ⟨xb, hxb, yb, hyb, hxy, hyx, hex, hxe, hey, hye⟩ := exists_mul_eq_of_iso ψ
  obtain ⟨x₀, hx₀, hx₀φ⟩ := exists_preimage_mem φ hφ hs hxb
  obtain ⟨y₀, hy₀, hy₀φ⟩ := exists_preimage_mem φ hφ hs hyb
  set x : R := e * x₀ * e' with hx
  set y : R := e' * y₀ * e with hy
  have hxa : x ∈ 𝓡 a := by
    simpa using SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem he0 hx₀) he0'
  have hya : y ∈ 𝓡 (-a) := by
    simpa using SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem he0' hy₀) he0
  have hφx : φ x = xb := by rw [hx, map_mul, map_mul, hx₀φ, hex, hxe]
  have hφy : φ y = yb := by rw [hy, map_mul, map_mul, hy₀φ, hey, hye]
  have hxy0 : x * y ∈ 𝓡 0 := by simpa using SetLike.GradedMul.mul_mem hxa hya
  have hyx0 : y * x ∈ 𝓡 0 := by simpa using SetLike.GradedMul.mul_mem hya hxa
  have hxy' : x * y = e := eq_of_map_eq φ h0 hxy0 he0 (by rw [map_mul, hφx, hφy, hxy])
  have hyx' : y * x = e' := eq_of_map_eq φ h0 hyx0 he0' (by rw [map_mul, hφx, hφy, hyx])
  have hya' : y ∈ 𝓡 (-a) := hya
  let u := GProj.ofIdempotentShiftIso (𝒜 := 𝓡) hxa hya' hxy' hyx' he he' he0 he0'
  -- `R e ≅ (R e'){-a}`, so `(R e){a} ≅ R e'`.
  have hc : K0.of ((GProj.ofIdempotent e he he0).shift a) =
      K0.of (GProj.ofIdempotent e' he' he0') := by
    rw [← K0.T_smul_of, K0.of_eq_of_iso u, ← K0.T_smul_of, smul_smul, ← LaurentPolynomial.T_add,
      add_neg_cancel, LaurentPolynomial.T_zero, one_smul]
  exact K0.of_eq_of_iff.mp hc

local notation "LP" => LaurentPolynomial ℤ

private theorem of_shift' {𝒜 : ℤ → Submodule k R} (P : GProj 𝒜) (a : ℤ) :
    K0.of (P.shift a) = (LaurentPolynomial.T a : LP) • K0.of P := (K0.T_smul_of a P).symm

variable [HasGdim 𝓡] [Module Rᵐᵒᵖ S] [SMulCommClass S Rᵐᵒᵖ S] [IsScalarTower k Rᵐᵒᵖ S]
  (hmul : ∀ (a : R) (s : S), op a • s = s * φ a)

include hs h0 in
/-- **Extension of scalars is injective on `K₀`** along a surjective graded homomorphism that is
injective in degree zero, for a locally finite, bounded below source (Webster,
arXiv:1309.3796v3, proof of Proposition 4.39: `𝔯_N` is full and faithful in degree zero). -/
theorem extensionK0_injective : Function.Injective (extensionK0 𝓡 𝓢 φ hφ hmul) := by
  have := hasGdim_of_surjective 𝓡 𝓢 φ hφ hs
  classical
  have key : ∀ b : IndecClass 𝓡, ∃ (c : IndecClass 𝓢) (n : ℤ) (e : R)
      (he : IsIdempotentElem e) (he0 : e ∈ 𝓡 0) (j : ℤ),
      Nonempty (b.rep.Iso ((GProj.ofIdempotent e he he0).shift j)) ∧
      Nonempty ((GProj.ofIdempotent (φ e) (he.map φ) (hφ he0)).Iso (c.rep.shift n)) := by
    intro b
    obtain ⟨e, he, he0, j, ⟨u⟩⟩ := b.isIndec_rep.exists_iso_ofIdempotent
    have hind : (GProj.ofIdempotent e he he0).IsIndec R := by
      have h1 := (IsIndec.of_iso u.symm b.isIndec_rep).shift (-j)
      refine IsIndec.of_iso (Q := ((GProj.ofIdempotent e he he0).shift j).shift (-j))
        (GradedEquiv.ofEq (A := R) ?_) h1
      change (GProj.ofIdempotent e he he0).grading =
        shift (shift (GProj.ofIdempotent e he he0).grading j) (-j)
      rw [shift_shift, add_neg_cancel, shift_zero]
    obtain ⟨c, n, ⟨w⟩⟩ := IndecClass.exists_iso_rep_shift
      (isIndec_ofIdempotent_map φ hφ hs h0 he he0 hind)
    exact ⟨c, n, e, he, he0, j, ⟨u⟩, ⟨w⟩⟩
  choose c n e he he0 j hb hc using key
  have himg : ∀ b, extensionK0 𝓡 𝓢 φ hφ hmul (K0.indecBasis 𝓡 b) =
      (LaurentPolynomial.T (j b + n b) : LP) • K0.indecBasis 𝓢 (c b) := by
    intro b
    rw [K0.indecBasis_apply, K0.indecBasis_apply, K0.of_eq_of_iso (hb b).some, of_shift',
      map_smul, extensionK0_ofIdempotent, K0.of_eq_of_iso (hc b).some, of_shift', smul_smul,
      ← LaurentPolynomial.T_add]
  have hinj : Function.Injective c := by
    intro b b' hcc
    have h1 : K0.of ((GProj.ofIdempotent (φ (e b)) ((he b).map φ) (hφ (he0 b))).shift
        (n b' - n b)) = K0.of (GProj.ofIdempotent (φ (e b')) ((he b').map φ) (hφ (he0 b'))) := by
      rw [of_shift', K0.of_eq_of_iso (hc b).some, K0.of_eq_of_iso (hc b').some, of_shift',
        of_shift', smul_smul, ← LaurentPolynomial.T_add, hcc, sub_add_cancel]
    obtain ⟨v⟩ := nonempty_iso_of_map φ hφ hs h0 (he b) (he b') (he0 b) (he0 b')
      (K0.of_eq_of_iff.mp h1).some
    have h2 : K0.of (b'.rep) = K0.of ((b.rep).shift (j b' + (n b' - n b) - j b)) := by
      rw [K0.of_eq_of_iso (hb b').some, of_shift', ← K0.of_eq_of_iso v, of_shift',
        of_shift', K0.of_eq_of_iso (hb b).some, of_shift']
      simp only [smul_smul, ← LaurentPolynomial.T_add]
      congr 2
      ring
    exact (IndecClass.eq_of_iso_rep (K0.of_eq_of_iff.mp h2).some).symm
  refine LinearMap.injective_of_linearIndependent (K0.indecBasis 𝓡).span_eq ?_
  have hfun : (extensionK0 𝓡 𝓢 φ hφ hmul ∘ K0.indecBasis 𝓡) =
      (fun b => unitT (j b + n b)) • (K0.indecBasis 𝓢 ∘ c) := by
    funext b
    rw [Function.comp_apply, himg, Pi.smul_apply', Units.smul_def]
    rfl
  rw [hfun]
  exact ((K0.indecBasis 𝓢).linearIndependent.comp c hinj).units_smul _

include hs h0 in
/-- **Extension of scalars is an isomorphism on `K₀`** along a surjective graded homomorphism
injective in degree zero (Webster, arXiv:1309.3796v3, proof of Proposition 4.39). -/
theorem extensionK0_bijective : Function.Bijective (extensionK0 𝓡 𝓢 φ hφ hmul) :=
  ⟨extensionK0_injective φ hφ hs h0 hmul, extensionK0_surjective 𝓡 𝓢 φ hφ hmul hs⟩

end Categorification.Graded
