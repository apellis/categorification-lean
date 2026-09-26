/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ProjectiveCover

/-!
# Krull–Schmidt for graded projective modules and freeness of `K₀`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, TeX lines 1513–1556:

> The category `R(ν)-mod` is Krull–Schmidt … Each simple `S_b` has a projective cover `P_b` …
> `K₀(R(ν))` is a free `ℤ[q, q⁻¹]`-module with the basis `{[P_b]}_{b ∈ B(ν)}`.

We prove the corresponding statements for any `ℤ`-graded algebra `A` over a field `k` with a
graded dimension (`HasGdim 𝒜`: finite-dimensional graded pieces, vanishing in sufficiently
negative degrees); `R(ν)` is such an algebra (`Categorification.KLR.GradingDatum.hasGdim_grade'`).

## Main results

* `GProj.summand P he hpe` and `GProj.summandIso` : a degree-preserving idempotent `e` of `P`
  splits `P ≅ e P ⊕ (1 - e) P` in `A-pmod`.
* `K0.of_mem_closure_indec` : **existence of Krull–Schmidt decompositions**: the class of every
  finitely generated graded projective module is a sum of classes of indecomposables
  (induction on `dim_k END(P)_0`, which is finite).
* `K0.homRank S` : the additive map `[P] ↦ dim_k Hom(P, S)_0` on `K₀`, for a graded module `S`
  with a graded dimension (e.g. a graded simple module).
* `GProj.IndecClass 𝒜` : indecomposable objects of `A-pmod` up to isomorphism and grading shift,
  with chosen representatives `GProj.IndecClass.rep b`; every indecomposable is `rep b {a}` for a
  unique pair `(b, a)` (`exists_iso_rep_shift`, `eq_of_iso_rep_shift`).
* **Projective covers** (KL I: "each simple `S_b` has a projective cover `P_b`"):
  `IndecClass.exists_cover` (every graded simple module receives a nonzero, hence surjective,
  degree-preserving map from some `rep b {a}`) and `IndecClass.eq_of_cover` (the pair `(b, a)` is
  unique). `IndecClass.top b` is a chosen graded simple top `S_b` of `P_b = rep b`, and
  `IndecClass.exists_gradedEquiv_top_shift`, `IndecClass.eq_of_gradedEquiv_top_shift` show that
  `b ↦ S_b` is a bijection from `IndecClass 𝒜` onto the graded simple modules up to isomorphism
  and shift. So `IndecClass 𝒜` is KL I's index set `B(ν)`.
* `K0.indecBasis 𝒜 : Basis (IndecClass 𝒜) ℤ[q, q⁻¹] (K₀(A))` with `indecBasis b = [rep b]`, and
  `K0.free : Module.Free ℤ[q, q⁻¹] K₀(A)`. **`K₀(A)` is a free `ℤ[q, q⁻¹]`-module with basis the
  classes of the indecomposable graded projectives up to shift.** (Linear independence uses the
  functionals `homRank S`, `S` a graded simple quotient of `rep b`; uniqueness of projective
  covers, `GProj.IsIndec.nonempty_iso`; and shift rigidity,
  `eq_zero_of_gradedEquiv_shift_of_hasGdim`.)
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

namespace GProj

/-! ### Splitting off direct summands -/

section Summand

theorem preservesGrading_one_sub {P : GProj 𝒜} {e : Module.End A P.carrier}
    (hpe : PreservesGrading P.grading P.grading e) :
    PreservesGrading P.grading P.grading (1 - e) := fun _ x hx => by
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact sub_mem hx (hpe hx)

/-- The graded direct summand `e P ⊆ P` cut out by a degree-preserving idempotent `e`. -/
def summand (P : GProj 𝒜) {e : Module.End A P.carrier} (he : IsIdempotentElem e)
    (hpe : PreservesGrading P.grading P.grading e) : GProj 𝒜 where
  carrier := LinearMap.range e
  grading := Graded.submodule P.grading (LinearMap.range e)
  decomposition := submoduleDecomposition P.grading (isHomogeneous_range hpe)
  finite := inferInstance
  projective := Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict
    (LinearMap.ext fun ⟨y, hy⟩ => Subtype.ext (by
      obtain ⟨x, rfl⟩ := hy
      show e (e x) = e x
      rw [← Module.End.mul_apply, he.eq]))

/-- `P ≅ e P ⊕ (1 - e) P` for a degree-preserving idempotent `e`. -/
def summandIso (P : GProj 𝒜) {e : Module.End A P.carrier} (he : IsIdempotentElem e)
    (hpe : PreservesGrading P.grading P.grading e) :
    P.Iso ((P.summand he hpe).prod (P.summand he.one_sub (preservesGrading_one_sub hpe))) :=
  GradedEquiv.ofLinearMaps (M := P.carrier) (N := LinearMap.range e × LinearMap.range (1 - e))
    (LinearMap.prod e.rangeRestrict (1 - e).rangeRestrict)
    (LinearMap.coprod (LinearMap.range e).subtype (LinearMap.range (1 - e)).subtype)
    (fun x => by simp)
    (fun ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ => by
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨b, rfl⟩ := hz
      have h1 : e (e a) = e a := by rw [← Module.End.mul_apply, he.eq]
      have h2 : e ((1 - e) b) = 0 := by
        rw [← Module.End.mul_apply, mul_sub, mul_one, he.eq, sub_self, LinearMap.zero_apply]
      have h3 : e (e b) = e b := by rw [← Module.End.mul_apply, he.eq]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · simp [h1, h2, h3]
      · simp only [LinearMap.prod_apply, Pi.prod, LinearMap.coprod_apply,
          Submodule.coe_subtype, LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
        rw [map_add, LinearMap.sub_apply, Module.End.one_apply, h1, sub_self, zero_add,
          ← Module.End.mul_apply, he.one_sub.eq])
    (fun _ _ hx => ⟨hpe hx, preservesGrading_one_sub hpe hx⟩)
    (fun _ _ hx => add_mem hx.1 hx.2)

theorem nontrivial_summand (P : GProj 𝒜) {e : Module.End A P.carrier} (he : IsIdempotentElem e)
    (hpe : PreservesGrading P.grading P.grading e) (he0 : e ≠ 0) :
    Nontrivial (P.summand he hpe).carrier := by
  obtain ⟨x, hx⟩ : ∃ x, e x ≠ 0 := by
    by_contra h
    push_neg at h
    exact he0 (LinearMap.ext h)
  exact ⟨⟨⟨e x, x, rfl⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩

end Summand

/-! ### Dimension of the degree-zero endomorphism algebra -/

section EndZeroDim

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

set_option synthInstance.maxHeartbeats 200000 in
/-- `(f, g) ↦ φ⁻¹ ∘ (f ⊕ g) ∘ φ : END(P₁)_0 × END(P₂)_0 → END(P)_0` for `φ : P ≅ P₁ ⊕ P₂`. -/
def endZeroProdMap {P P₁ P₂ : GProj 𝒜} (φ : P.Iso (P₁.prod P₂)) :
    endZero A P₁.grading × endZero A P₂.grading →ₗ[k] endZero A P.grading where
  toFun fg := ⟨φ.symm.toLinearEquiv.toLinearMap ∘ₗ
      (LinearMap.prodMap (fg.1 : Module.End A P₁.carrier) (fg.2 : Module.End A P₂.carrier)) ∘ₗ
      φ.toLinearEquiv.toLinearMap, fun _ _ hx =>
    φ.symm.map_mem (show (_, _) ∈ Graded.prod P₁.grading P₂.grading _ from
      ⟨fg.1.2 (φ.map_mem hx).1, fg.2.2 (φ.map_mem hx).2⟩)⟩
  map_add' fg fg' := Subtype.ext (LinearMap.ext fun x => by
    simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, LinearMap.coe_comp,
      LinearEquiv.coe_coe, comp_apply, LinearMap.prodMap_apply, LinearMap.add_apply]
    rw [← map_add]
    rfl)
  map_smul' c fg := Subtype.ext (LinearMap.ext fun x => by
    simp only [Prod.smul_fst, Prod.smul_snd, Subalgebra.coe_smul, LinearMap.coe_comp,
      LinearEquiv.coe_coe, comp_apply, RingHom.id_apply, LinearMap.prodMap_smul,
      LinearMap.smul_apply]
    exact LinearMap.map_smul_of_tower φ.symm.toLinearEquiv.toLinearMap c _)

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem endZeroProdMap_injective {P P₁ P₂ : GProj 𝒜} (φ : P.Iso (P₁.prod P₂)) :
    Injective (endZeroProdMap φ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨f, g⟩ h
  have key : ∀ y : P₁.carrier × P₂.carrier,
      ((f : Module.End A P₁.carrier) y.1, (g : Module.End A P₂.carrier) y.2) = 0 := by
    intro y
    have := LinearMap.congr_fun (congrArg Subtype.val h) (φ.symm y)
    simp only [endZeroProdMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
      LinearEquiv.coe_coe, comp_apply, LinearMap.prodMap_apply, ZeroMemClass.coe_zero,
      LinearMap.zero_apply] at this
    have h2 : φ.toLinearEquiv (φ.symm y) = y := φ.toLinearEquiv.apply_symm_apply y
    erw [h2] at this
    exact φ.symm.toLinearEquiv.injective (this.trans (map_zero _).symm)
  refine Prod.ext (Subtype.ext (LinearMap.ext fun y => ?_)) (Subtype.ext (LinearMap.ext fun y => ?_))
  · exact (Prod.ext_iff.1 (key (y, 0))).1
  · exact (Prod.ext_iff.1 (key (0, y))).2

theorem finrank_endZero_pos {P : GProj 𝒜} [Nontrivial P.carrier] :
    0 < finrank k (endZero A P.grading) := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨1, fun h => ?_⟩
  have h' : (1 : Module.End A P.carrier) = 0 := congrArg Subtype.val h
  exact one_ne_zero h'

/-- `dim END(P₁)_0 + dim END(P₂)_0 ≤ dim END(P)_0` for `P ≅ P₁ ⊕ P₂`. -/
theorem finrank_endZero_add_le {P P₁ P₂ : GProj 𝒜} (φ : P.Iso (P₁.prod P₂)) :
    finrank k (endZero A P₁.grading) + finrank k (endZero A P₂.grading) ≤
      finrank k (endZero A P.grading) := by
  rw [← Module.finrank_prod]
  exact LinearMap.finrank_le_finrank_of_injective (endZeroProdMap_injective φ)

end EndZeroDim

end GProj

/-! ### Existence of Krull–Schmidt decompositions -/

namespace K0

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

open GProj

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- The class of a zero module vanishes. -/
theorem of_eq_zero_of_subsingleton (P : GProj 𝒜) [Subsingleton P.carrier] : of P = 0 := by
  have e : P.Iso (P.prod P) :=
    GradedEquiv.ofLinearMaps (M := P.carrier) (N := P.carrier × P.carrier)
      (LinearMap.prod LinearMap.id LinearMap.id) (LinearMap.fst A P.carrier P.carrier)
      (fun _ => rfl) (fun _ => Subsingleton.elim _ _) (fun _ _ hx => ⟨hx, hx⟩)
      (fun _ _ hx => hx.1)
  have h := of_eq_of_iso e
  rw [of_prod] at h
  simpa using h

/-- **Krull–Schmidt decompositions exist**: the class of every finitely generated graded
projective module is a sum of classes of indecomposable ones. -/
theorem of_mem_closure_indec (P : GProj 𝒜) :
    of P ∈ AddSubmonoid.closure {x : K0 𝒜 | ∃ Q : GProj 𝒜, Q.IsIndec A ∧ x = of Q} := by
  induction h : finrank k (endZero A P.grading) using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hP : Nontrivial P.carrier
    · by_cases hind : ∀ e ∈ endZero A P.grading, IsIdempotentElem e → e = 0 ∨ e = 1
      · exact AddSubmonoid.subset_closure ⟨P, ⟨hP, hind⟩, rfl⟩
      · push_neg at hind
        obtain ⟨e, hpe, he, he0, he1⟩ := hind
        have h1 := P.nontrivial_summand he hpe he0
        have h2 := P.nontrivial_summand he.one_sub (preservesGrading_one_sub hpe)
          (sub_ne_zero.2 (Ne.symm he1))
        have hle := finrank_endZero_add_le (P.summandIso he hpe)
        have hp1 := finrank_endZero_pos (P := P.summand he hpe)
        have hp2 := finrank_endZero_pos
          (P := P.summand he.one_sub (preservesGrading_one_sub hpe))
        rw [of_eq_of_iso (P.summandIso he hpe), of_prod]
        exact add_mem (ih _ (by omega) _ rfl) (ih _ (by omega) _ rfl)
    · rw [not_nontrivial_iff_subsingleton] at hP
      rw [of_eq_zero_of_subsingleton]
      exact zero_mem _

end K0

/-! ### The functionals `[P] ↦ dim_k Hom(P, S)_0` -/

section HomRank

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

theorem preservesGrading_of_mem_homGrade_zero {M N : Type*} [AddCommGroup M] [Module A M]
    [Module k M] [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {f : M →ₗ[A] N}
    (hf : f ∈ homGrade A ℳ 𝒩 0) : PreservesGrading ℳ 𝒩 f := fun e _ hx => by
  simpa using hf hx

theorem mem_homGrade_zero_of_preservesGrading {M N : Type*} [AddCommGroup M] [Module A M]
    [Module k M] [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {f : M →ₗ[A] N}
    (hf : PreservesGrading ℳ 𝒩 f) : f ∈ homGrade A ℳ 𝒩 0 := fun e _ hx => by
  simpa using hf hx

namespace K0

open GProj

variable (S : GMod 𝒜) [HasGdim S.grading]

/-- The additive map `[P] ↦ dim_k Hom(P, S)_0` on `K₀(A)` (for `S` with a graded dimension, e.g.
a graded simple module). -/
def homRank : K0 𝒜 →+ ℤ :=
  QuotientAddGroup.lift (relSubgroup 𝒜)
    (FreeAbelianGroup.lift fun c : IsoClass 𝒜 =>
      Quotient.lift (fun P : GProj 𝒜 => (finrank k (homGrade A P.grading S.grading 0) : ℤ))
        (fun P P' (h : Nonempty (P.Iso P')) =>
          congrArg _ (finrank_homGrade_congr_left h.some 0).symm) c)
    (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, P', rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift.of]
      show (finrank k (homGrade A (P.prod P').grading S.grading 0) : ℤ) -
        finrank k (homGrade A P.grading S.grading 0) -
        finrank k (homGrade A P'.grading S.grading 0) = 0
      haveI := hasGdim_homGrade (A := A) P.grading S.grading
      haveI := hasGdim_homGrade (A := A) P'.grading S.grading
      have h : finrank k (homGrade A (P.prod P').grading S.grading 0) =
          finrank k (homGrade A P.grading S.grading 0) +
            finrank k (homGrade A P'.grading S.grading 0) :=
        finrank_homGrade_prod_left 0
      rw [h]
      push_cast
      ring)

variable {S}

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homRank_of (P : GProj 𝒜) :
    homRank S (of P) = finrank k (homGrade A P.grading S.grading 0) := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk' _ _) = _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift.of]
  rfl

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- `dim Hom(P, S)_0 ≠ 0` iff there is a nonzero degree-preserving map `P → S`. -/
theorem homRank_of_ne_zero_iff (P : GProj 𝒜) :
    homRank S (of P) ≠ 0 ↔
      ∃ f : P.carrier →ₗ[A] S, PreservesGrading P.grading S.grading f ∧ f ≠ 0 := by
  haveI := hasGdim_homGrade (A := A) P.grading S.grading
  rw [homRank_of, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero,
    Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, preservesGrading_of_mem_homGrade_zero f.2, fun h => hf (Subtype.ext h)⟩
  · rintro ⟨f, hf, hf0⟩
    exact ⟨⟨f, mem_homGrade_zero_of_preservesGrading hf⟩, fun h => hf0 (congrArg Subtype.val h)⟩

end K0

end HomRank

/-! ### Indecomposables up to isomorphism and shift -/

namespace GProj

section IndecClass

/-- `P{a} ≅ Q{a'}` implies `P ≅ Q{a' - a}`. -/
def isoShiftSub {P Q : GProj 𝒜} {a a' : ℤ} (e : (P.shift a).Iso (Q.shift a')) :
    P.Iso (Q.shift (a' + -a)) :=
  ((GradedEquiv.ofEq (A := A) (show Graded.shift (Graded.shift P.grading a) (-a) = P.grading by
      rw [shift_shift, add_neg_cancel, shift_zero])).symm.trans (e.shift (-a))).trans
    (GradedEquiv.ofEq (shift_shift Q.grading a' (-a)))

theorem IsIndec.shift {P : GProj 𝒜} (hP : P.IsIndec A) (a : ℤ) : (P.shift a).IsIndec A where
  nontrivial := hP.nontrivial
  eq_zero_or_eq_one e he hide := hP.eq_zero_or_eq_one e (fun d x hx => by
    have h := he (d := d + a) (x := x)
      (show x ∈ P.grading (d + a - a) by rwa [add_sub_cancel_right])
    have h' : e x ∈ P.grading (d + a - a) := h
    rwa [add_sub_cancel_right] at h') hide

variable (𝒜)

/-- The relation "isomorphic up to a grading shift" on indecomposable objects of `A-pmod`. -/
def indecSetoid : Setoid {P : GProj 𝒜 // P.IsIndec A} where
  r P Q := ∃ a : ℤ, Nonempty (P.1.Iso (Q.1.shift a))
  iseqv :=
    ⟨fun P => ⟨0, ⟨(GMod.shiftZeroIso P.1.toGMod).symm⟩⟩,
      fun {P Q} ⟨a, ⟨e⟩⟩ => ⟨-a, ⟨(GradedEquiv.ofEq (A := A)
        (show Graded.shift (Graded.shift Q.1.grading a) (-a) = Q.1.grading by
          rw [shift_shift, add_neg_cancel, shift_zero])).symm.trans (e.symm.shift (-a))⟩⟩,
      fun {P Q R} ⟨a, ⟨e⟩⟩ ⟨b, ⟨f⟩⟩ => ⟨b + a, ⟨e.trans ((f.shift a).trans
        (GradedEquiv.ofEq (shift_shift R.1.grading b a)))⟩⟩⟩

/-- **Indecomposable objects of `A-pmod` up to isomorphism and grading shift.** -/
def IndecClass : Type _ := Quotient (indecSetoid 𝒜)

variable {𝒜}

/-- The chosen representative of an indecomposable class. -/
def IndecClass.rep (b : IndecClass 𝒜) : GProj 𝒜 := b.out.1

theorem IndecClass.isIndec_rep (b : IndecClass 𝒜) : b.rep.IsIndec A := b.out.2

/-- Every indecomposable is a shift of a chosen representative. -/
theorem IndecClass.exists_iso_rep_shift {P : GProj 𝒜} (hP : P.IsIndec A) :
    ∃ (b : IndecClass 𝒜) (a : ℤ), Nonempty (P.Iso (b.rep.shift a)) :=
  ⟨Quotient.mk _ ⟨P, hP⟩, (indecSetoid 𝒜).symm (Quotient.mk_out (s := indecSetoid 𝒜) ⟨P, hP⟩)⟩

theorem IndecClass.eq_of_iso_rep {b b' : IndecClass 𝒜} {a : ℤ} (e : b.rep.Iso (b'.rep.shift a)) :
    b = b' := by
  rw [← Quotient.out_eq b, ← Quotient.out_eq b']
  exact Quotient.sound ⟨a, ⟨e⟩⟩

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- The pair `(b, a)` with `P ≅ rep b {a}` is unique. -/
theorem IndecClass.eq_of_iso_rep_shift {b b' : IndecClass 𝒜} {a a' : ℤ}
    (e : (b.rep.shift a).Iso (b'.rep.shift a')) : b = b' ∧ a = a' := by
  have e' := isoShiftSub e
  obtain rfl := IndecClass.eq_of_iso_rep e'
  haveI := (IndecClass.isIndec_rep b).nontrivial
  have := eq_zero_of_gradedEquiv_shift_of_hasGdim (A := A) b.rep.grading e'
  exact ⟨rfl, by omega⟩

end IndecClass

end GProj

/-! ### Projective covers of graded simple modules -/

namespace GProj

section Covers

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- A nonzero degree-preserving map out of an object of `A-pmod` is nonzero on some
indecomposable direct summand. -/
theorem exists_isIndec_ne_zero {S : Type*} [AddCommGroup S] [Module A S] [Module k S]
    {𝒮 : ℤ → Submodule k S} (P : GProj 𝒜) {f : P.carrier →ₗ[A] S}
    (hf : PreservesGrading P.grading 𝒮 f) (hf0 : f ≠ 0) :
    ∃ Q : GProj 𝒜, Q.IsIndec A ∧
      ∃ g : Q.carrier →ₗ[A] S, PreservesGrading Q.grading 𝒮 g ∧ g ≠ 0 := by
  induction h : finrank k (endZero A P.grading) using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    have hP : Nontrivial P.carrier := by
      by_contra h'
      rw [not_nontrivial_iff_subsingleton] at h'
      exact hf0 (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero,
        LinearMap.zero_apply])
    by_cases hind : ∀ e ∈ endZero A P.grading, IsIdempotentElem e → e = 0 ∨ e = 1
    · exact ⟨P, ⟨hP, hind⟩, f, hf, hf0⟩
    · push_neg at hind
      obtain ⟨e, hpe, he, he0, he1⟩ := hind
      have h1 := P.nontrivial_summand he hpe he0
      have h2 := P.nontrivial_summand he.one_sub (preservesGrading_one_sub hpe)
        (sub_ne_zero.2 (Ne.symm he1))
      obtain ⟨φ⟩ : Nonempty (P.Iso ((P.summand he hpe).prod
          (P.summand he.one_sub (preservesGrading_one_sub hpe)))) := ⟨P.summandIso he hpe⟩
      have hle := finrank_endZero_add_le φ
      have hp1 := finrank_endZero_pos (P := P.summand he hpe)
      have hp2 := finrank_endZero_pos
        (P := P.summand he.one_sub (preservesGrading_one_sub hpe))
      set F := f ∘ₗ φ.symm.toLinearEquiv.toLinearMap
      have hF : PreservesGrading (Graded.prod (P.summand he hpe).grading
          (P.summand he.one_sub (preservesGrading_one_sub hpe)).grading) 𝒮 F :=
        fun _ _ hx => hf (φ.symm.map_mem hx)
      by_cases h₁ : F ∘ₗ LinearMap.inl A _ _ = 0
      · have h₂ : F ∘ₗ LinearMap.inr A _ _ ≠ 0 := by
          intro h₂
          apply hf0
          have hF0 : F = 0 := LinearMap.prod_ext (h₁.trans (LinearMap.zero_comp _).symm)
            (h₂.trans (LinearMap.zero_comp _).symm)
          ext x
          have := LinearMap.congr_fun hF0 (φ.toLinearEquiv x)
          simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at this
          rwa [show φ.symm.toLinearEquiv (φ.toLinearEquiv x) = x from
            φ.toLinearEquiv.symm_apply_apply x] at this
        exact ih _ (by omega) (P.summand he.one_sub (preservesGrading_one_sub hpe))
          (f := F ∘ₗ LinearMap.inr A _ _) (fun _ _ hx => hF ⟨zero_mem _, hx⟩) h₂ rfl
      · exact ih _ (by omega) (P.summand he hpe) (f := F ∘ₗ LinearMap.inl A _ _)
          (fun _ _ hx => hF ⟨hx, zero_mem _⟩) h₁ rfl

/-- **Every graded simple module has a projective cover**: a shift `P_b{a}` of a chosen
indecomposable with a nonzero (hence surjective) degree-preserving map onto it. -/
theorem IndecClass.exists_cover {S : Type*} [AddCommGroup S] [Module A S] [Module k S]
    [IsScalarTower k A S] {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] [SetLike.GradedSMul 𝒜 𝒮]
    (hS : IsGradedSimple 𝒜 𝒮) :
    ∃ (b : IndecClass 𝒜) (a : ℤ) (f : (b.rep.shift a).carrier →ₗ[A] S),
      PreservesGrading (b.rep.shift a).grading 𝒮 f ∧ f ≠ 0 := by
  haveI := hS.nontrivial
  obtain ⟨j, v, hv, hv0⟩ := exists_mem_ne_zero 𝒮
  have hf' : PreservesGrading (Graded.shift 𝒜 j) 𝒮 (LinearMap.toSpanSingleton A S v) :=
    fun d r hr => by
      have : r • v ∈ 𝒮 (d - j + j) := SetLike.GradedSMul.smul_mem (mem_shift.1 hr) hv
      rw [sub_add_cancel] at this
      exact this
  have hf : PreservesGrading ((GProj.regular 𝒜).shift j).grading 𝒮
      (LinearMap.toSpanSingleton A S v) := hf'
  have hf0 : LinearMap.toSpanSingleton A S v ≠ 0 := fun h => hv0 (by
    simpa using LinearMap.congr_fun h 1)
  obtain ⟨Q, hQ, g, hg, hg0⟩ := ((GProj.regular 𝒜).shift j).exists_isIndec_ne_zero hf hf0
  obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_iso_rep_shift hQ
  refine ⟨b, a, g ∘ₗ e.symm.toLinearEquiv.toLinearMap, fun _ _ hx => hg (e.symm.map_mem hx), ?_⟩
  intro h
  apply hg0
  ext x
  have := LinearMap.congr_fun h (e.toLinearEquiv x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at this
  rwa [show e.symm.toLinearEquiv (e.toLinearEquiv x) = x from
    e.toLinearEquiv.symm_apply_apply x] at this

/-- **Uniqueness of projective covers**: the pair `(b, a)` in `IndecClass.exists_cover` is
unique. -/
theorem IndecClass.eq_of_cover {S : Type*} [AddCommGroup S] [Module A S] [Module k S]
    [IsScalarTower k A S] {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮] [SetLike.GradedSMul 𝒜 𝒮]
    (hS : IsGradedSimple 𝒜 𝒮) {b b' : IndecClass 𝒜} {a a' : ℤ}
    {f : (b.rep.shift a).carrier →ₗ[A] S} (hf : PreservesGrading (b.rep.shift a).grading 𝒮 f)
    (hf0 : f ≠ 0) {f' : (b'.rep.shift a').carrier →ₗ[A] S}
    (hf' : PreservesGrading (b'.rep.shift a').grading 𝒮 f') (hf'0 : f' ≠ 0) :
    b = b' ∧ a = a' :=
  IndecClass.eq_of_iso_rep_shift (((IndecClass.isIndec_rep b).shift a).nonempty_iso
    ((IndecClass.isIndec_rep b').shift a') hS hf hf0 hf' hf'0).some

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem IndecClass.exists_top (b : IndecClass 𝒜) :
    ∃ (S : GMod 𝒜) (f : b.rep.carrier →ₗ[A] S), IsGradedSimple 𝒜 S.grading ∧
      PreservesGrading b.rep.grading S.grading f ∧ f ≠ 0 ∧ Module.Finite A S := by
  haveI := (IndecClass.isIndec_rep b).nontrivial
  exact b.rep.exists_isGradedSimple_quotient

/-- The graded simple top `S_b` of the chosen indecomposable `P_b = rep b` (a graded simple
quotient of `P_b`; unique up to isomorphism by `GProj.IsIndec.nonempty_gradedEquiv`). -/
def IndecClass.top (b : IndecClass 𝒜) : GMod 𝒜 := (IndecClass.exists_top b).choose

/-- The projection `P_b → S_b`. -/
def IndecClass.topMap (b : IndecClass 𝒜) : b.rep.carrier →ₗ[A] b.top :=
  (IndecClass.exists_top b).choose_spec.choose

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem IndecClass.isGradedSimple_top (b : IndecClass 𝒜) : IsGradedSimple 𝒜 b.top.grading :=
  (IndecClass.exists_top b).choose_spec.choose_spec.1

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem IndecClass.preservesGrading_topMap (b : IndecClass 𝒜) :
    PreservesGrading b.rep.grading b.top.grading b.topMap :=
  (IndecClass.exists_top b).choose_spec.choose_spec.2.1

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem IndecClass.topMap_ne_zero (b : IndecClass 𝒜) : b.topMap ≠ 0 :=
  (IndecClass.exists_top b).choose_spec.choose_spec.2.2.1

instance IndecClass.finite_top (b : IndecClass 𝒜) : Module.Finite A b.top :=
  (IndecClass.exists_top b).choose_spec.choose_spec.2.2.2

instance IndecClass.hasGdim_top (b : IndecClass 𝒜) : HasGdim b.top.grading :=
  hasGdim_of_finite 𝒜 b.top.grading

/-- **Classification of graded simple modules** (KL I, §2.5): every graded simple module is
isomorphic to `S_b{a}` for some `b` and `a` … -/
theorem IndecClass.exists_gradedEquiv_top_shift {S : Type*} [AddCommGroup S] [Module A S]
    [Module k S] [IsScalarTower k A S] {𝒮 : ℤ → Submodule k S} [Decomposition 𝒮]
    [SetLike.GradedSMul 𝒜 𝒮] (hS : IsGradedSimple 𝒜 𝒮) :
    ∃ (b : IndecClass 𝒜) (a : ℤ), Nonempty (𝒮 ≃ᵍ[A] Graded.shift b.top.grading a) := by
  obtain ⟨b, a, f, hf, hf0⟩ := IndecClass.exists_cover hS
  exact ⟨b, a, ((IndecClass.isIndec_rep b).shift a).nonempty_gradedEquiv hS
    ((IndecClass.isGradedSimple_top b).shift a) hf hf0 (f' := b.topMap)
    (fun _ _ hx => (IndecClass.preservesGrading_topMap b) hx) (IndecClass.topMap_ne_zero b)⟩

/-- … and the pair `(b, a)` is unique: the tops `S_b` are pairwise non-isomorphic up to shift,
and `S_b{a} ≅ S_b{a'}` only for `a = a'`. -/
theorem IndecClass.eq_of_gradedEquiv_top_shift {b b' : IndecClass 𝒜} {a a' : ℤ}
    (e : Graded.shift b.top.grading a ≃ᵍ[A] Graded.shift b'.top.grading a') :
    b = b' ∧ a = a' := by
  have hS' := (IndecClass.isGradedSimple_top b').shift a'
  have hg : PreservesGrading (b.rep.shift a).grading (Graded.shift b'.top.grading a')
      (e.toLinearEquiv.toLinearMap ∘ₗ b.topMap) :=
    fun _ _ hx => e.map_mem ((IndecClass.preservesGrading_topMap b) hx)
  have hg0 : e.toLinearEquiv.toLinearMap ∘ₗ b.topMap ≠ 0 := by
    intro h
    apply IndecClass.topMap_ne_zero b
    ext x
    have := LinearMap.congr_fun h x
    exact e.toLinearEquiv.injective (this.trans (map_zero _).symm)
  exact IndecClass.eq_of_cover hS' hg hg0 (f' := b'.topMap)
    (fun _ _ hx => (IndecClass.preservesGrading_topMap b') hx) (IndecClass.topMap_ne_zero b')

end Covers

end GProj

/-! ### `K₀` is free -/

namespace K0

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

open GProj

variable (𝒜) in
/-- The classes of the chosen indecomposables span `K₀(A)` over `ℤ[q, q⁻¹]`. -/
theorem span_indec :
    Submodule.span (LaurentPolynomial ℤ) (Set.range fun b : IndecClass 𝒜 => of b.rep) = ⊤ := by
  set V := Submodule.span (LaurentPolynomial ℤ) (Set.range fun b : IndecClass 𝒜 => of b.rep)
  have hcl : AddSubmonoid.closure {x : K0 𝒜 | ∃ Q : GProj 𝒜, Q.IsIndec A ∧ x = of Q} ≤
      V.toAddSubmonoid := by
    rw [AddSubmonoid.closure_le]
    rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨b, a, ⟨e⟩⟩ := IndecClass.exists_iso_rep_shift hQ
    rw [SetLike.mem_coe, Submodule.mem_toAddSubmonoid, of_eq_of_iso e, ← T_smul_of]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using K0.induction_on with
  | of P => exact hcl (of_mem_closure_indec P)
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | neg x hx => exact neg_mem hx

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- Expansion of the `ℤ[q, q⁻¹]`-action: an additive map `ψ` sends `(C n T^a) • x` to
`n ψ(q^a x)`. -/
theorem map_C_mul_T_smul {G : Type*} [AddCommGroup G] (ψ : K0 𝒜 →+ G) (n : ℤ) (a : ℤ)
    (x : K0 𝒜) :
    ψ ((LaurentPolynomial.C n * LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) =
      n • ψ ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) := by
  rw [← LaurentPolynomial.smul_eq_C_mul, smul_assoc, map_zsmul]

open scoped Classical in
/-- The key computation for linear independence: for the simple quotient `S` of `rep b₀` and
`ψ = homRank (S{d})`, `ψ(p • [rep b]) = δ_{b b₀} p_d ψ([rep b₀ {d}])`. -/
theorem homRank_smul_of_rep {b₀ : IndecClass 𝒜} {S : GMod 𝒜} [HasGdim S.grading]
    (hS : IsGradedSimple 𝒜 S.grading) {f : b₀.rep.carrier →ₗ[A] S}
    (hf : PreservesGrading b₀.rep.grading S.grading f) (hf0 : f ≠ 0) (d : ℤ)
    [HasGdim (S.shift d).grading] (b : IndecClass 𝒜) (p : LaurentPolynomial ℤ) :
    homRank (S.shift d) (p • of b.rep) =
      if b = b₀ then p d * homRank (S.shift d) (of (b₀.rep.shift d)) else 0 := by
  have hvanish : ∀ a : ℤ, homRank (S.shift d) (of (b.rep.shift a)) ≠ 0 → b = b₀ ∧ a = d := by
    intro a ha
    obtain ⟨g, hg, hg0⟩ := (homRank_of_ne_zero_iff _).1 ha
    have hSd : IsGradedSimple 𝒜 (S.shift d).grading := hS.shift d
    obtain ⟨e⟩ := ((IndecClass.isIndec_rep b).shift a).nonempty_iso
      ((IndecClass.isIndec_rep b₀).shift d) hSd hg hg0
      (f' := f) (fun j x hx => hf (d := j - d) hx) hf0
    exact IndecClass.eq_of_iso_rep_shift e
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, map_add, hp, hq]
    split_ifs
    · rw [← add_mul]
      rfl
    · rw [add_zero]
  | C_mul_T a n =>
    rw [map_C_mul_T_smul, T_smul_of, ← LaurentPolynomial.single_eq_C_mul_T,
      Finsupp.single_apply]
    by_cases hb : b = b₀
    · subst hb
      by_cases ha : a = d
      · subst ha
        simp
      · have : homRank (S.shift d) (of (b.rep.shift a)) = 0 := by
          by_contra h
          exact ha (hvanish a h).2
        simp [this, ha]
    · have : homRank (S.shift d) (of (b.rep.shift a)) = 0 := by
        by_contra h
        exact hb (hvanish a h).1
      simp [this, hb]

variable (𝒜) in
/-- The classes of the chosen indecomposables are linearly independent over `ℤ[q, q⁻¹]`. -/
theorem linearIndependent_indec :
    LinearIndependent (LaurentPolynomial ℤ) fun b : IndecClass 𝒜 => of b.rep := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  ext b₀ d
  haveI := (IndecClass.isIndec_rep b₀).nontrivial
  obtain ⟨S, f, hS, hf, hf0, hfin⟩ := b₀.rep.exists_isGradedSimple_quotient
  haveI : HasGdim S.grading := hasGdim_of_finite 𝒜 S.grading
  haveI : HasGdim (S.shift d).grading := inferInstanceAs (HasGdim (Graded.shift S.grading d))
  have hc₀ : homRank (S.shift d) (of (b₀.rep.shift d)) ≠ 0 :=
    (homRank_of_ne_zero_iff _).2 ⟨f, fun j x hx => hf (d := j - d) hx, hf0⟩
  have h := congrArg (homRank (S.shift d)) hl
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_zero] at h
  simp only [homRank_smul_of_rep hS hf hf0 d] at h
  rw [Finsupp.sum, Finset.sum_ite_eq'] at h
  split_ifs at h with hmem
  · simpa [hc₀] using h
  · simp [Finsupp.not_mem_support_iff.1 hmem]

variable (𝒜) in
/-- **KL I, §2.5: `K₀(A)` is a free `ℤ[q, q⁻¹]`-module**, with basis the classes `[P]` of the
indecomposable finitely generated graded projective modules, one in each isomorphism class up
to grading shift (for `A = R(ν)` these are the projective covers `P_b` of the simples). -/
def indecBasis : Basis (IndecClass 𝒜) (LaurentPolynomial ℤ) (K0 𝒜) :=
  Basis.mk (linearIndependent_indec 𝒜) (span_indec 𝒜).ge

@[simp] theorem indecBasis_apply (b : IndecClass 𝒜) : indecBasis 𝒜 b = of b.rep :=
  Basis.mk_apply _ _ _

/-- **`K₀(A)` is a free `ℤ[q, q⁻¹]`-module.** -/
instance free : Module.Free (LaurentPolynomial ℤ) (K0 𝒜) :=
  Module.Free.of_basis (indecBasis 𝒜)

end K0

end Categorification.Graded
