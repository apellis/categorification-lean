/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.K0

/-!
# Graded projective modules `A e` from homogeneous idempotents

For an idempotent `e ∈ A` of degree `0` in a `ℤ`-graded algebra `(A, 𝒜)`, the left ideal
`A e = {a | a e = a}` is a homogeneous left ideal and a direct summand of `A`, hence a finitely
generated graded projective module `GProj.ofIdempotent e` (KL I, arXiv:0803.4121v2, §2.5: the
modules `P_i = R(ν) 1_i`, and `P_i = R(ν) ψ(1_i) {-⟨i⟩}` for divided-power sequences).

## Main results

* `Graded.leftIdeal e`, `Graded.leftIdeal_isHomogeneous` : the homogeneous left ideal `A e`.
* `GProj.ofIdempotent e he he0` : `A e` as an object of `A-pmod`.
* `GProj.ofIdempotentShiftIso` and `K0.of_ofIdempotent_eq_T_smul` : if `e = x y` and
  `e' = y x` with `x ∈ 𝒜 d`, `y ∈ 𝒜 (-d)`, then right multiplication by `x` is an isomorphism
  `A e ≅ (A e'){-d}`, so `[A e] = q^{-d} [A e']` in `K₀`.
  (Sanity check: in `A = Mat₂(k)` with `deg E₁₂ = d`, `deg E₂₁ = -d`, `x = E₁₂`, `y = E₂₁`,
  `gdim (A E₁₁) = 1 + q^{-d} = q^{-d} gdim (A E₂₂)`.)
* `GProj.ofIdempotentAddIso` and `K0.of_ofIdempotent_add` : for orthogonal degree-zero
  idempotents `e₁, e₂`, `A (e₁ + e₂) ≅ A e₁ ⊕ A e₂`, so `[A (e₁ + e₂)] = [A e₁] + [A e₂]`.
* `K0.of_ofIdempotent_sum`, `K0.of_regular_eq_sum` : for a finite orthogonal family,
  `[A (∑ eᵢ)] = ∑ [A eᵢ]`; for a complete one, `[A] = ∑ᵢ [A eᵢ]`.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-! ### The left ideal `A e` -/

/-- The left ideal `A e = {a | a e = a}` (for an idempotent `e`, this is `A e`). -/
def leftIdeal (e : A) : Submodule A A where
  carrier := {a | a * e = a}
  add_mem' {a b} ha hb := by simp_all [add_mul]
  zero_mem' := zero_mul e
  smul_mem' c a ha := by simp_all [smul_eq_mul, mul_assoc]

@[simp] theorem mem_leftIdeal {e a : A} : a ∈ leftIdeal e ↔ a * e = a := Iff.rfl

theorem mul_mem_leftIdeal {e : A} (he : IsIdempotentElem e) (a : A) : a * e ∈ leftIdeal e := by
  rw [mem_leftIdeal, mul_assoc, he.eq]

theorem leftIdeal_isHomogeneous [GradedAlgebra 𝒜] {e : A} (he0 : e ∈ 𝒜 0) :
    (leftIdeal e).IsHomogeneous 𝒜 := by
  intro i a ha
  rw [mem_leftIdeal] at ha ⊢
  have := coe_decompose_mul_add_of_right_mem 𝒜 (a := a) (i := i) he0
  rw [add_zero, ha] at this
  exact this.symm

/-- The projection `A → A e`, `a ↦ a e`. -/
def leftIdealProj {e : A} (he : IsIdempotentElem e) : A →ₗ[A] leftIdeal e :=
  LinearMap.codRestrict (leftIdeal e) (LinearMap.toSpanSingleton A A e) fun a =>
    mul_mem_leftIdeal he a

@[simp] theorem leftIdealProj_apply {e : A} (he : IsIdempotentElem e) (a : A) :
    (leftIdealProj he a : A) = a * e := rfl

theorem leftIdealProj_comp_subtype {e : A} (he : IsIdempotentElem e) :
    (leftIdealProj he).comp (leftIdeal e).subtype = LinearMap.id := by
  ext ⟨a, ha⟩
  exact ha

/-- `A e` is a finitely generated graded projective module. -/
def GProj.ofIdempotent [GradedAlgebra 𝒜] (e : A) (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    GProj 𝒜 where
  carrier := leftIdeal e
  grading := Graded.submodule 𝒜 (leftIdeal e)
  decomposition := submoduleDecomposition 𝒜 (leftIdeal_isHomogeneous he0)
  finite := Module.Finite.of_surjective (leftIdealProj he) fun b =>
    ⟨b, Subtype.ext (mem_leftIdeal.1 b.2)⟩
  projective := Module.Projective.of_split (leftIdeal e).subtype (leftIdealProj he)
    (leftIdealProj_comp_subtype he)

variable [GradedAlgebra 𝒜]

@[simp] theorem GProj.mem_ofIdempotent_grading {e : A} {he : IsIdempotentElem e}
    {he0 : e ∈ 𝒜 0} {d : ℤ} {a : leftIdeal e} :
    a ∈ (GProj.ofIdempotent e he he0).grading d ↔ (a : A) ∈ 𝒜 d := Iff.rfl

theorem mem_zero_of_mul {x y : A} {d : ℤ} (hx : x ∈ 𝒜 d) (hy : y ∈ 𝒜 (-d)) : x * y ∈ 𝒜 0 := by
  simpa using SetLike.GradedMul.mul_mem hx hy

/-! ### Equivalent idempotents -/

/-- If `e = x y`, `e' = y x` with `x ∈ 𝒜 d`, `y ∈ 𝒜 (-d)`, then right multiplication by `x`
is a degree-preserving isomorphism `A e ≅ (A e'){-d}`. -/
def leftIdealShiftEquiv {e e' x y : A} {d : ℤ} (hx : x ∈ 𝒜 d) (hy : y ∈ 𝒜 (-d))
    (hxy : x * y = e) (hyx : y * x = e') :
    Graded.submodule 𝒜 (leftIdeal e) ≃ᵍ[A] shift (Graded.submodule 𝒜 (leftIdeal e')) (-d) :=
  GradedEquiv.ofLinearMaps
    (LinearMap.codRestrict (leftIdeal e') ((LinearMap.toSpanSingleton A A x).comp
      (leftIdeal e).subtype) fun a => by
        have ha : (a : A) * e = a := a.2
        show (a : A) * x * e' = (a : A) * x
        rw [← hyx, ← mul_assoc, mul_assoc (a : A) x y, hxy, ha])
    (LinearMap.codRestrict (leftIdeal e) ((LinearMap.toSpanSingleton A A y).comp
      (leftIdeal e').subtype) fun b => by
        have hb : (b : A) * e' = b := b.2
        show (b : A) * y * e = (b : A) * y
        rw [← hxy, ← mul_assoc, mul_assoc (b : A) y x, hyx, hb])
    (fun a => Subtype.ext <| by
      have ha : (a : A) * e = a := a.2
      show (a : A) * x * y = a
      rw [mul_assoc, hxy, ha])
    (fun b => Subtype.ext <| by
      have hb : (b : A) * e' = b := b.2
      show (b : A) * y * x = b
      rw [mul_assoc, hyx, hb])
    (fun n a ha => by
      show (a : A) * x ∈ 𝒜 (n - -d)
      rw [sub_neg_eq_add]
      exact SetLike.GradedMul.mul_mem ha hx)
    (fun n b hb => by
      show (b : A) * y ∈ 𝒜 n
      have hb' : (b : A) ∈ 𝒜 (n - -d) := hb
      simpa using SetLike.GradedMul.mul_mem hb' hy)

/-- The bundled form of `leftIdealShiftEquiv`: `A e ≅ (A e'){-d}` in `A-pmod`. -/
def GProj.ofIdempotentShiftIso {e e' x y : A} {d : ℤ} (hx : x ∈ 𝒜 d) (hy : y ∈ 𝒜 (-d))
    (hxy : x * y = e) (hyx : y * x = e') (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (he0 : e ∈ 𝒜 0) (he0' : e' ∈ 𝒜 0) :
    (GProj.ofIdempotent e he he0).Iso ((GProj.ofIdempotent e' he' he0').shift (-d)) :=
  leftIdealShiftEquiv hx hy hxy hyx

/-! ### Orthogonal decompositions -/

/-- For orthogonal degree-zero idempotents `e₁, e₂` with `e₁ + e₂ = e`,
`A e ≅ A e₁ ⊕ A e₂`, `a ↦ (a e₁, a e₂)`. -/
def leftIdealAddEquiv {e e₁ e₂ : A} (h : e₁ + e₂ = e) (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (he₁0 : e₁ ∈ 𝒜 0) (he₂0 : e₂ ∈ 𝒜 0) :
    Graded.submodule 𝒜 (leftIdeal e) ≃ᵍ[A]
      prod (Graded.submodule 𝒜 (leftIdeal e₁)) (Graded.submodule 𝒜 (leftIdeal e₂)) :=
  GradedEquiv.ofLinearMaps
    (LinearMap.prod ((leftIdealProj he₁).comp (leftIdeal e).subtype)
      ((leftIdealProj he₂).comp (leftIdeal e).subtype))
    (LinearMap.coprod
      (LinearMap.codRestrict (leftIdeal e) (leftIdeal e₁).subtype fun b => by
        have hb : (b : A) * e₁ = b := b.2
        have hb2 : (b : A) * e₂ = 0 := by rw [← hb, mul_assoc, h₁₂, mul_zero]
        show (b : A) * e = b
        rw [← h, mul_add, hb, hb2, add_zero])
      (LinearMap.codRestrict (leftIdeal e) (leftIdeal e₂).subtype fun c => by
        have hc : (c : A) * e₂ = c := c.2
        have hc1 : (c : A) * e₁ = 0 := by rw [← hc, mul_assoc, h₂₁, mul_zero]
        show (c : A) * e = c
        rw [← h, mul_add, hc, hc1, zero_add]))
    (fun a => Subtype.ext <| by
      have ha : (a : A) * e = a := a.2
      show (a : A) * e₁ + (a : A) * e₂ = a
      rw [← mul_add, h, ha])
    (fun ⟨b, c⟩ => by
      have hb : (b : A) * e₁ = b := b.2
      have hc : (c : A) * e₂ = c := c.2
      have hb2 : (b : A) * e₂ = 0 := by rw [← hb, mul_assoc, h₁₂, mul_zero]
      have hc1 : (c : A) * e₁ = 0 := by rw [← hc, mul_assoc, h₂₁, mul_zero]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show ((b : A) + c) * e₁ = b
        rw [add_mul, hb, hc1, add_zero]
      · show ((b : A) + c) * e₂ = c
        rw [add_mul, hc, hb2, zero_add])
    (fun n a ha => ⟨by simpa using SetLike.GradedMul.mul_mem (show (a : A) ∈ 𝒜 n from ha) he₁0,
      by simpa using SetLike.GradedMul.mul_mem (show (a : A) ∈ 𝒜 n from ha) he₂0⟩)
    (fun n bc hbc => add_mem hbc.1 hbc.2)

/-- The bundled form of `leftIdealAddEquiv`: `A e ≅ A e₁ ⊕ A e₂` in `A-pmod`. -/
def GProj.ofIdempotentAddIso {e e₁ e₂ : A} (h : e₁ + e₂ = e) (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (he₁0 : e₁ ∈ 𝒜 0) (he₂0 : e₂ ∈ 𝒜 0) :
    (GProj.ofIdempotent e he he0).Iso
      ((GProj.ofIdempotent e₁ he₁ he₁0).prod (GProj.ofIdempotent e₂ he₂ he₂0)) :=
  leftIdealAddEquiv h he₁ he₂ h₁₂ h₂₁ he₁0 he₂0

/-- `A · 1 ≅ A`. -/
def leftIdealOneEquiv : Graded.submodule 𝒜 (leftIdeal (1 : A)) ≃ᵍ[A] 𝒜 :=
  GradedEquiv.ofLinearMaps (leftIdeal (1 : A)).subtype
    (LinearMap.codRestrict (leftIdeal 1) LinearMap.id fun a => mul_one a)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ _ h => h)

/-- `A · 1 ≅ A` in `A-pmod`. -/
def GProj.ofIdempotentOneIso :
    (GProj.ofIdempotent (1 : A) IsIdempotentElem.one (SetLike.GradedOne.one_mem)).Iso
      (GProj.regular 𝒜) :=
  leftIdealOneEquiv

/-! ### Consequences in `K₀` -/

namespace K0

/-- `[A e] = q^{-d} [A e']` when `e = x y`, `e' = y x`, `deg x = d`, `deg y = -d`. -/
theorem of_ofIdempotent_eq_T_smul {e e' x y : A} {d : ℤ} (hx : x ∈ 𝒜 d) (hy : y ∈ 𝒜 (-d))
    (hxy : x * y = e) (hyx : y * x = e') (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (he0 : e ∈ 𝒜 0) (he0' : e' ∈ 𝒜 0) :
    of (GProj.ofIdempotent e he he0) =
      (LaurentPolynomial.T (-d) : LaurentPolynomial ℤ) • of (GProj.ofIdempotent e' he' he0') := by
  rw [T_smul_of]
  exact of_eq_of_iso (GProj.ofIdempotentShiftIso hx hy hxy hyx he he' he0 he0')

/-- `[A (e₁ + e₂)] = [A e₁] + [A e₂]` for orthogonal degree-zero idempotents. -/
theorem of_ofIdempotent_add {e e₁ e₂ : A} (h : e₁ + e₂ = e) (he₁ : IsIdempotentElem e₁)
    (he₂ : IsIdempotentElem e₂) (h₁₂ : e₁ * e₂ = 0) (h₂₁ : e₂ * e₁ = 0)
    (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (he₁0 : e₁ ∈ 𝒜 0) (he₂0 : e₂ ∈ 𝒜 0) :
    of (GProj.ofIdempotent e he he0) =
      of (GProj.ofIdempotent e₁ he₁ he₁0) + of (GProj.ofIdempotent e₂ he₂ he₂0) := by
  rw [← of_prod]
  exact of_eq_of_iso (GProj.ofIdempotentAddIso h he₁ he₂ h₁₂ h₂₁ he he0 he₁0 he₂0)

/-- `[A (∑_{i ∈ s} eᵢ)] = ∑_{i ∈ s} [A eᵢ]` for a finite orthogonal family of degree-zero
idempotents. -/
theorem of_ofIdempotent_sum {ι : Type*} {e : ι → A} (he : OrthogonalIdempotents e)
    (he0 : ∀ i, e i ∈ 𝒜 0) (s : Finset ι) :
    of (GProj.ofIdempotent (∑ i ∈ s, e i) he.isIdempotentElem_sum (Submodule.sum_mem _
      fun i _ => he0 i)) = ∑ i ∈ s, of (GProj.ofIdempotent (e i) (he.idem i) (he0 i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    set X := GProj.ofIdempotent (∑ i ∈ (∅ : Finset ι), e i) he.isIdempotentElem_sum
      (Submodule.sum_mem _ fun i _ => he0 i)
    have hX : of X = of X + of X := by
      rw [← of_prod]
      exact of_eq_of_iso (GProj.ofIdempotentAddIso (by simp) _ _ (by simp) (by simp) _ _ _ _)
    simpa using hX
  | insert j s hj ih =>
    conv_rhs => rw [Finset.sum_insert hj]
    have hjs : e j * ∑ i ∈ s, e i = 0 := he.mul_sum_of_not_mem hj
    have hsj : (∑ i ∈ s, e i) * e j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i hi => he.ortho (fun h => hj (h ▸ hi))
    rw [of_ofIdempotent_add (Finset.sum_insert hj).symm (he.idem j) he.isIdempotentElem_sum hjs
      hsj _ _ (he0 j) (Submodule.sum_mem _ fun i _ => he0 i), ih]

/-- Equal idempotents give equal classes. -/
theorem of_ofIdempotent_congr {e e' : A} (h : e = e') (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ 𝒜 0) :
    of (GProj.ofIdempotent e he he0) = of (GProj.ofIdempotent e' he' he0') := by
  subst h; rfl

/-- `[A] = ∑ᵢ [A eᵢ]` for a complete orthogonal family of degree-zero idempotents. -/
theorem of_regular_eq_sum {ι : Type*} [Fintype ι] {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) (he0 : ∀ i, e i ∈ 𝒜 0) :
    of (GProj.regular 𝒜) =
      ∑ i, of (GProj.ofIdempotent (e i) (he.idem i) (he0 i)) := by
  rw [← of_ofIdempotent_sum he.toOrthogonalIdempotents he0 Finset.univ,
    ← of_eq_of_iso GProj.ofIdempotentOneIso]
  exact of_ofIdempotent_congr he.complete.symm _ _ _ _

end K0

end Categorification.Graded

end
