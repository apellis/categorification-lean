/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Idempotent
import Categorification.Algebra.Graded.HomogeneousBasis

/-!
# The graded `HOM` spaces and the form `gdim HOM(P, Q)` on `K₀`

Let `(A, 𝒜)` be a `ℤ`-graded algebra over a field `k`. For graded `A`-modules `M`, `N`,
Khovanov–Lauda I (arXiv:0803.4121v2, §2.5) consider the graded vector space
`HOM(M, N) = ⨁_d Hom(M, N{d})` of all `A`-linear maps, graded by the degree by which a map
raises degrees. We define its degree-`d` part `homGrade A ℳ 𝒩 d ⊆ (M →ₗ[A] N)`: the maps `f`
with `f(M_e) ⊆ N_{e + d}` for all `e`.

## Main results

* `hasGdim_homGrade` : if `M` is finitely generated and `N` has a graded dimension, then
  `HOM(M, N)` has a graded dimension (a degree-`d` map is determined by its values on
  finitely many homogeneous generators).
* `homGrade` is compatible with degree-preserving isomorphisms (`finrank_homGrade_congr_left`,
  `…_right`), direct sums in either variable (`finrank_homGrade_prod_left`, `…_right`) and
  shifts (`homGrade_shift_left`, `homGrade_shift_right`).
* `homGradeIdemEquiv` : `HOM(A e, M) ≅ e M` (`f ↦ f(e)`) for a degree-zero idempotent `e`,
  so `gdim HOM(A e, M) = gdim (e M)` (`gdim_homGrade_ofIdempotent`).
* `K0.homForm` : **the form `([P], [Q]) ↦ gdim HOM(P, Q)` on `K₀(A)`**, a biadditive map
  `K₀(A) →+ K₀(A) →+ ℤ((q))` (for `HasGdim 𝒜`), which is sesquilinear:
  `(q^a x, y) = q^{-a} (x, y)` and `(x, q^a y) = q^a (x, y)`
  (`homForm_T_smul_left`, `homForm_T_smul_right`), and
  `([A e], [M]) = gdim (e M)` (`homForm_ofIdempotent`).

## Relation to the pairing of KL I

KL I defines `([P], [Q]) = gdim (P^ψ ⊗_{R(ν)} Q)` (equation `eq_bil_pair2`), which is
`ℤ[q, q⁻¹]`-bilinear. For a finitely generated projective `P`, `P^ψ ⊗_{R(ν)} Q ≅
HOM(P̄, Q)` with `P̄ = HOM(P, R(ν))^ψ`, so the paper's form is `(x, y) ↦ homForm (x̄) y`. On the
modules `P_i = R(ν) 1_i` (which satisfy `P̄_i ≅ P_i`, KL I §2.5), both give
`([P_i], [Q]) = gdim (1_i Q)`; in particular `([P_j], [P_i]) = gdim (1_j R(ν) 1_i)` (see
`Categorification.KLR.Pairing`). We do not formalize tensor products of graded modules or the bar
involution here.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function

/-! ### Graded `HOM` spaces -/

section HomGrade

variable {k : Type*} [Field k] (A : Type*) [Ring A] [Algebra k A]
  {M N M' N' : Type*} [AddCommGroup M] [Module A M] [Module k M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  [AddCommGroup M'] [Module A M'] [Module k M']
  [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']

/-- The degree-`d` part `HOM(M, N)_d = Hom(M, N{d})` of `HOM(M, N)`: `A`-linear maps with
`f(M_e) ⊆ N_{e + d}`. -/
def homGrade (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) (d : ℤ) :
    Submodule k (M →ₗ[A] N) where
  carrier := {f | ∀ ⦃e : ℤ⦄ ⦃x : M⦄, x ∈ ℳ e → f x ∈ 𝒩 (e + d)}
  add_mem' hf hg _ _ hx := add_mem (hf hx) (hg hx)
  zero_mem' _ _ _ := zero_mem _
  smul_mem' c _ hf _ _ hx := Submodule.smul_mem _ c (hf hx)

variable {A}

@[simp] theorem mem_homGrade {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {d : ℤ}
    {f : M →ₗ[A] N} : f ∈ homGrade A ℳ 𝒩 d ↔ ∀ ⦃e : ℤ⦄ ⦃x : M⦄, x ∈ ℳ e → f x ∈ 𝒩 (e + d) :=
  Iff.rfl

variable {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N} {ℳ' : ℤ → Submodule k M'}
  {𝒩' : ℤ → Submodule k N'}

/-- `HOM(M{a}, N)_d = HOM(M, N)_{a + d}`. -/
theorem homGrade_shift_left (a d : ℤ) :
    homGrade A (shift ℳ a) 𝒩 d = homGrade A ℳ 𝒩 (a + d) := by
  ext f
  simp only [mem_homGrade, mem_shift]
  constructor
  · intro hf e x hx
    have := hf (e := e + a) (by simpa using hx)
    rwa [show e + a + d = e + (a + d) by ring] at this
  · intro hf e x hx
    have := hf hx
    rwa [show e - a + (a + d) = e + d by ring] at this

/-- `HOM(M, N{a})_d = HOM(M, N)_{d - a}`. -/
theorem homGrade_shift_right (a d : ℤ) :
    homGrade A ℳ (shift 𝒩 a) d = homGrade A ℳ 𝒩 (d - a) := by
  ext f
  simp only [mem_homGrade, mem_shift]
  constructor
  · intro hf e x hx
    have := hf hx
    rwa [show e + d - a = e + (d - a) by ring] at this
  · intro hf e x hx
    have := hf hx
    rwa [show e + (d - a) = e + d - a by ring] at this

/-- Precomposition with a degree-preserving isomorphism `M ≅ M'`. -/
def homGradeCongrLeft (f : ℳ ≃ᵍ[A] ℳ') (d : ℤ) :
    homGrade A ℳ' 𝒩 d ≃ₗ[k] homGrade A ℳ 𝒩 d where
  toFun φ := ⟨(φ : M' →ₗ[A] N).comp f.toLinearEquiv.toLinearMap, fun _ _ hx => φ.2 (f.map_mem hx)⟩
  invFun φ := ⟨(φ : M →ₗ[A] N).comp f.toLinearEquiv.symm.toLinearMap,
    fun _ _ hx => φ.2 (f.symm_map_mem' hx)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext (LinearMap.ext fun x =>
    congrArg (φ : M' →ₗ[A] N) (f.toLinearEquiv.apply_symm_apply x))
  right_inv φ := Subtype.ext (LinearMap.ext fun x =>
    congrArg (φ : M →ₗ[A] N) (f.toLinearEquiv.symm_apply_apply x))

/-- Postcomposition with a degree-preserving isomorphism `N ≅ N'`. -/
def homGradeCongrRight (g : 𝒩 ≃ᵍ[A] 𝒩') (d : ℤ) :
    homGrade A ℳ 𝒩 d ≃ₗ[k] homGrade A ℳ 𝒩' d where
  toFun φ := ⟨g.toLinearEquiv.toLinearMap.comp (φ : M →ₗ[A] N), fun _ _ hx => g.map_mem (φ.2 hx)⟩
  invFun φ := ⟨g.toLinearEquiv.symm.toLinearMap.comp (φ : M →ₗ[A] N'),
    fun _ _ hx => g.symm_map_mem' (φ.2 hx)⟩
  map_add' φ ψ := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c φ := Subtype.ext (LinearMap.ext fun x =>
    show g.toLinearEquiv ((c • (φ : M →ₗ[A] N)) x) = c • g.toLinearEquiv ((φ : M →ₗ[A] N) x) by
      rw [LinearMap.smul_apply, ← algebraMap_smul A c, LinearEquiv.map_smul, algebraMap_smul])
  left_inv φ := Subtype.ext (LinearMap.ext fun x => g.toLinearEquiv.symm_apply_apply _)
  right_inv φ := Subtype.ext (LinearMap.ext fun x => g.toLinearEquiv.apply_symm_apply _)

/-- `HOM(M ⊕ M', N) ≅ HOM(M, N) × HOM(M', N)`. -/
def homGradeProdLeft (d : ℤ) :
    homGrade A (prod ℳ ℳ') 𝒩 d ≃ₗ[k] homGrade A ℳ 𝒩 d × homGrade A ℳ' 𝒩 d where
  toFun φ := (⟨(φ : M × M' →ₗ[A] N).comp (LinearMap.inl A M M'),
      fun _ _ hx => φ.2 (show (_, _) ∈ prod ℳ ℳ' _ from ⟨hx, zero_mem _⟩)⟩,
    ⟨(φ : M × M' →ₗ[A] N).comp (LinearMap.inr A M M'),
      fun _ _ hx => φ.2 (show (_, _) ∈ prod ℳ ℳ' _ from ⟨zero_mem _, hx⟩)⟩)
  invFun φ := ⟨LinearMap.coprod (φ.1 : M →ₗ[A] N) (φ.2 : M' →ₗ[A] N),
    fun _ x hx => by
      rw [LinearMap.coprod_apply]
      exact add_mem (φ.1.2 hx.1) (φ.2.2 hx.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext (LinearMap.ext fun x => by
    simp only [LinearMap.coprod_apply, LinearMap.coe_comp, comp_apply, LinearMap.inl_apply,
      LinearMap.inr_apply]
    rw [← map_add]; simp)
  right_inv φ := Prod.ext (Subtype.ext (LinearMap.ext fun x => by simp))
    (Subtype.ext (LinearMap.ext fun x => by simp))

/-- `HOM(M, N ⊕ N') ≅ HOM(M, N) × HOM(M, N')`. -/
def homGradeProdRight (d : ℤ) :
    homGrade A ℳ (prod 𝒩 𝒩') d ≃ₗ[k] homGrade A ℳ 𝒩 d × homGrade A ℳ 𝒩' d where
  toFun φ := (⟨(LinearMap.fst A N N').comp (φ : M →ₗ[A] N × N'), fun _ _ hx => (φ.2 hx).1⟩,
    ⟨(LinearMap.snd A N N').comp (φ : M →ₗ[A] N × N'), fun _ _ hx => (φ.2 hx).2⟩)
  invFun φ := ⟨LinearMap.prod (φ.1 : M →ₗ[A] N) (φ.2 : M →ₗ[A] N'),
    fun _ _ hx => ⟨φ.1.2 hx, φ.2.2 hx⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext (LinearMap.ext fun x => by simp)
  right_inv φ := Prod.ext (Subtype.ext (LinearMap.ext fun x => by simp))
    (Subtype.ext (LinearMap.ext fun x => by simp))

/-! #### Finiteness -/

variable [Decomposition ℳ]

/-- Evaluation at finitely many homogeneous generators `m_t ∈ M_{deg t}` embeds `HOM(M, N)_d`
into `∏_t N_{deg t + d}`. -/
def homGradeEval {ι : Type*} (m : ι → M) (deg : ι → ℤ) (hm : ∀ t, m t ∈ ℳ (deg t)) (d : ℤ) :
    homGrade A ℳ 𝒩 d →ₗ[k] ((t : ι) → 𝒩 (deg t + d)) where
  toFun φ t := ⟨(φ : M →ₗ[A] N) (m t), φ.2 (hm t)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Decomposition ℳ] in
theorem homGradeEval_injective {ι : Type*} (m : ι → M) (deg : ι → ℤ)
    (hm : ∀ t, m t ∈ ℳ (deg t)) (hspan : Submodule.span A (Set.range m) = ⊤) (d : ℤ) :
    Injective (homGradeEval (A := A) (𝒩 := 𝒩) m deg hm d) := by
  intro φ ψ h
  refine Subtype.ext (LinearMap.ext_on_range hspan fun t => ?_)
  exact congrArg Subtype.val (congrFun h t)

omit [Decomposition ℳ] in
/-- **`HOM(M, N)` has a graded dimension** if `M` is generated by finitely many homogeneous
elements and `N` has a graded dimension. -/
theorem hasGdim_homGrade_of_generators [HasGdim 𝒩] {ι : Type*} [Fintype ι] (m : ι → M)
    (deg : ι → ℤ) (hm : ∀ t, m t ∈ ℳ (deg t)) (hspan : Submodule.span A (Set.range m) = ⊤) :
    HasGdim (homGrade A ℳ 𝒩) where
  finiteDimensional d :=
    FiniteDimensional.of_injective _ (homGradeEval_injective (A := A) m deg hm hspan d)
  bddBelow := by
    obtain ⟨B, hB⟩ := HasGdim.bddBelow (ℳ := 𝒩)
    obtain ⟨D, hD⟩ := (Set.finite_range deg).bddAbove
    refine ⟨B - D, fun d (hd : homGrade A ℳ 𝒩 d ≠ ⊥) => ?_⟩
    by_contra hlt
    push_neg at hlt
    apply hd
    rw [eq_bot_iff]
    intro φ hφ
    rw [Submodule.mem_bot]
    have : homGradeEval (A := A) m deg hm d ⟨φ, hφ⟩ = homGradeEval (A := A) m deg hm d 0 := by
      funext t
      have h1 : 𝒩 (deg t + d) = ⊥ := by
        by_contra h
        have := hB h
        have := hD ⟨t, rfl⟩
        simp only [Set.mem_setOf_eq] at *
        omega
      exact Subtype.ext (by
        have := (homGradeEval (A := A) m deg hm d ⟨φ, hφ⟩ t).2
        rw [(Submodule.eq_bot_iff _).1 h1 _ this]
        simp [homGradeEval])
    exact congrArg Subtype.val (homGradeEval_injective (A := A) m deg hm hspan d this)

variable (ℳ 𝒩) in
/-- **`HOM(M, N)` has a graded dimension for finitely generated `M`** and `N` with a graded
dimension. -/
theorem hasGdim_homGrade [HasGdim 𝒩] [Module.Finite A M] : HasGdim (homGrade A ℳ 𝒩) := by
  obtain ⟨s, hs, hspan⟩ := exists_homogeneous_generators (A := A) ℳ
  rw [Set.image_univ] at hspan
  exact hasGdim_homGrade_of_generators (fun p : s => (p : ℤ × M).2) (fun p => (p : ℤ × M).1)
    (fun p => hs _ p.2) hspan

omit [Decomposition ℳ] in
theorem finrank_homGrade_congr_left (f : ℳ ≃ᵍ[A] ℳ') (d : ℤ) :
    finrank k (homGrade A ℳ' 𝒩 d) = finrank k (homGrade A ℳ 𝒩 d) :=
  (homGradeCongrLeft f d).finrank_eq

omit [Decomposition ℳ] in
theorem finrank_homGrade_congr_right (g : 𝒩 ≃ᵍ[A] 𝒩') (d : ℤ) :
    finrank k (homGrade A ℳ 𝒩 d) = finrank k (homGrade A ℳ 𝒩' d) :=
  (homGradeCongrRight g d).finrank_eq

omit [Decomposition ℳ] in
theorem finrank_homGrade_prod_left (d : ℤ) [FiniteDimensional k (homGrade A ℳ 𝒩 d)]
    [FiniteDimensional k (homGrade A ℳ' 𝒩 d)] :
    finrank k (homGrade A (prod ℳ ℳ') 𝒩 d) =
      finrank k (homGrade A ℳ 𝒩 d) + finrank k (homGrade A ℳ' 𝒩 d) := by
  rw [(homGradeProdLeft d).finrank_eq, Module.finrank_prod]

omit [Decomposition ℳ] in
theorem finrank_homGrade_prod_right (d : ℤ) [FiniteDimensional k (homGrade A ℳ 𝒩 d)]
    [FiniteDimensional k (homGrade A ℳ 𝒩' d)] :
    finrank k (homGrade A ℳ (prod 𝒩 𝒩') d) =
      finrank k (homGrade A ℳ 𝒩 d) + finrank k (homGrade A ℳ 𝒩' d) := by
  rw [(homGradeProdRight d).finrank_eq, Module.finrank_prod]

end HomGrade

/-! ### `HOM(A e, M) ≅ e M` -/

section Idempotent

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] {M : Type*} [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M] {ℳ : ℤ → Submodule k M} [SetLike.GradedSMul 𝒜 ℳ]

/-- `HOM(A e, M)_d ≅ (e M)_d`, `f ↦ f(e)`, for an idempotent `e` of degree `0`. -/
def homGradeIdemEquiv {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (d : ℤ) :
    homGrade A (Graded.submodule 𝒜 (leftIdeal e)) ℳ d ≃ₗ[k] idem ℳ e d where
  toFun φ := ⟨⟨(φ : leftIdeal e →ₗ[A] M) ⟨e, he.eq⟩, by
      show e • _ = _
      rw [← map_smul]
      congr 1
      exact Subtype.ext he.eq⟩, by
      have := φ.2 (e := 0) (x := ⟨e, he.eq⟩) he0
      rwa [zero_add] at this⟩
  invFun m := ⟨(LinearMap.toSpanSingleton A M (m : idemSubspace k M e)).comp
      (leftIdeal e).subtype, fun e' x hx => by
      simp only [LinearMap.coe_comp, comp_apply, Submodule.coe_subtype,
        LinearMap.toSpanSingleton_apply]
      have := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ)
        (show ((x : leftIdeal e) : A) ∈ 𝒜 e' from hx) m.2
      simpa [vadd_eq_add] using this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext (LinearMap.ext fun x => by
    simp only [LinearMap.coe_comp, comp_apply, Submodule.coe_subtype,
      LinearMap.toSpanSingleton_apply]
    rw [← map_smul]
    congr 1
    exact Subtype.ext (mem_leftIdeal.1 x.2))
  right_inv m := Subtype.ext (Subtype.ext (by
    simp only [LinearMap.coe_comp, comp_apply, Submodule.coe_subtype,
      LinearMap.toSpanSingleton_apply]
    exact m.1.2))

omit [GradedAlgebra 𝒜] in
/-- `gdim HOM(A e, M) = gdim (e M)`. -/
theorem gdim_homGrade_ofIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) :
    gdim (homGrade A (Graded.submodule 𝒜 (leftIdeal e)) ℳ) = gdim (idem ℳ e) :=
  gdim_eq_of_finrank_eq fun d => (homGradeIdemEquiv he he0 d).finrank_eq

end Idempotent

/-! ### The form on `K₀` -/

section Form

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] [HasGdim 𝒜]

namespace GProj

variable {𝒜}

instance hasGdim (P : GProj 𝒜) : HasGdim P.grading :=
  Graded.hasGdim_of_finite 𝒜 P.grading

/-- `gdim HOM(P, Q)`. -/
def homGdim (P Q : GProj 𝒜) : LaurentSeries ℤ :=
  gdim (homGrade A P.grading Q.grading)

instance hasGdim_homGrade (P Q : GProj 𝒜) : HasGdim (homGrade A P.grading Q.grading) :=
  Graded.hasGdim_homGrade P.grading Q.grading

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homGdim_congr_left {P P' Q : GProj 𝒜} (f : P.Iso P') :
    homGdim P Q = homGdim P' Q :=
  gdim_eq_of_finrank_eq fun d => (finrank_homGrade_congr_left f d).symm

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homGdim_congr_right {P Q Q' : GProj 𝒜} (g : Q.Iso Q') :
    homGdim P Q = homGdim P Q' :=
  gdim_eq_of_finrank_eq fun d => finrank_homGrade_congr_right g d

theorem homGdim_prod_left (P P' Q : GProj 𝒜) :
    homGdim (P.prod P') Q = homGdim P Q + homGdim P' Q := by
  haveI : HasGdim (homGrade A (P.prod P').grading Q.grading) := hasGdim_homGrade (P.prod P') Q
  exact gdim_eq_add_of_finrank_eq fun d => finrank_homGrade_prod_left d

theorem homGdim_prod_right (P Q Q' : GProj 𝒜) :
    homGdim P (Q.prod Q') = homGdim P Q + homGdim P Q' := by
  haveI : HasGdim (homGrade A P.grading (Q.prod Q').grading) := hasGdim_homGrade P (Q.prod Q')
  exact gdim_eq_add_of_finrank_eq fun d => finrank_homGrade_prod_right d

/-- `gdim` of a reindexed family `d ↦ ℳ (a + d)` is `q^{-a} gdim ℳ`. -/
theorem gdim_comp_add {W : Type*} [AddCommGroup W] [Module k W] (ℳ : ℤ → Submodule k W)
    (a : ℤ) : gdim (fun d => ℳ (a + d)) = HahnSeries.single (-a) 1 * gdim ℳ := by
  rw [← gdim_shift]
  congr 1
  funext d
  rw [shift_apply]
  congr 1
  ring

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homGdim_shift_left (P Q : GProj 𝒜) (a : ℤ) :
    homGdim (P.shift a) Q = HahnSeries.single (-a) 1 * homGdim P Q := by
  unfold homGdim
  rw [← gdim_comp_add]
  congr 1
  funext d
  exact homGrade_shift_left a d

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homGdim_shift_right (P Q : GProj 𝒜) (a : ℤ) :
    homGdim P (Q.shift a) = HahnSeries.single a 1 * homGdim P Q := by
  unfold homGdim
  conv_rhs => rw [← neg_neg a]
  rw [← gdim_comp_add]
  congr 1
  funext d
  rw [show -a + d = d - a by ring]
  exact homGrade_shift_right a d

end GProj

open GProj

namespace K0

/-- For fixed `Q`, the additive map `[P] ↦ gdim HOM(P, Q)` on `K₀`. -/
def homFormRight (Q : GProj 𝒜) : K0 𝒜 →+ LaurentSeries ℤ :=
  QuotientAddGroup.lift (relSubgroup 𝒜)
    (FreeAbelianGroup.lift fun c : IsoClass 𝒜 =>
      Quotient.lift (fun P => homGdim P Q)
        (fun P P' (h : Nonempty (P.Iso P')) => homGdim_congr_left h.some) c)
    (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨P, P', rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift.of]
      show homGdim (P.prod P') Q - homGdim P Q - homGdim P' Q = 0
      rw [homGdim_prod_left]
      abel)

variable {𝒜}

@[simp] theorem homFormRight_of (P Q : GProj 𝒜) : homFormRight 𝒜 Q (of P) = homGdim P Q := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk' _ _) = _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift.of]
  rfl

variable (𝒜) in
/-- `[Q] ↦ ([P] ↦ gdim HOM(P, Q))`. -/
def homFormAux : K0 𝒜 →+ K0 𝒜 →+ LaurentSeries ℤ :=
  QuotientAddGroup.lift (relSubgroup 𝒜)
    (FreeAbelianGroup.lift fun c : IsoClass 𝒜 =>
      Quotient.lift (fun Q => homFormRight 𝒜 Q) (fun Q Q' (h : Nonempty (Q.Iso Q')) =>
        hom_ext fun P => by
        rw [homFormRight_of, homFormRight_of]
        exact homGdim_congr_right h.some) c)
    (by
      rw [relSubgroup, AddSubgroup.closure_le]
      rintro _ ⟨Q, Q', rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, FreeAbelianGroup.lift.of]
      show homFormRight 𝒜 (Q.prod Q') - homFormRight 𝒜 Q - homFormRight 𝒜 Q' = 0
      refine hom_ext fun P => ?_
      simp only [AddMonoidHom.sub_apply, homFormRight_of, homGdim_prod_right,
        AddMonoidHom.zero_apply]
      abel)

theorem homFormAux_of (Q : GProj 𝒜) : homFormAux 𝒜 (of Q) = homFormRight 𝒜 Q := by
  show QuotientAddGroup.lift _ _ _ (QuotientAddGroup.mk' _ _) = _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk, FreeAbelianGroup.lift.of]
  rfl

variable (𝒜) in
/-- **The form `([P], [Q]) ↦ gdim HOM(P, Q)` on `K₀(A)`**, biadditive, with values in
`ℤ((q))`. It is sesquilinear for the `ℤ[q, q⁻¹]`-module structure (`homForm_T_smul_left`,
`homForm_T_smul_right`). KL I's pairing (`eq_bil_pair2`) is `(x, y) ↦ homForm x̄ y`; on the
self-dual projectives `P_i` the two agree. -/
def homForm : K0 𝒜 →+ K0 𝒜 →+ LaurentSeries ℤ := (homFormAux 𝒜).flip

/-- `([P], [Q]) = gdim HOM(P, Q)`. -/
@[simp] theorem homForm_of (P Q : GProj 𝒜) : homForm 𝒜 (of P) (of Q) = homGdim P Q := by
  rw [homForm, AddMonoidHom.flip_apply, homFormAux_of, homFormRight_of]

/-- `(q^a x, y) = q^{-a} (x, y)`. -/
theorem homForm_T_smul_left (a : ℤ) (x y : K0 𝒜) :
    homForm 𝒜 ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • x) y =
      HahnSeries.single (-a) 1 * homForm 𝒜 x y := by
  rw [T_smul]
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of Q => rw [shiftHom_of, homForm_of, homForm_of, homGdim_shift_left]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
    | neg y hy => simp only [map_neg, mul_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, mul_add, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, mul_neg, hx]

/-- `(x, q^a y) = q^a (x, y)`. -/
theorem homForm_T_smul_right (a : ℤ) (x y : K0 𝒜) :
    homForm 𝒜 x ((LaurentPolynomial.T a : LaurentPolynomial ℤ) • y) =
      HahnSeries.single a 1 * homForm 𝒜 x y := by
  rw [T_smul]
  induction x using induction_on with
  | of P =>
    induction y using induction_on with
    | of Q => rw [shiftHom_of, homForm_of, homForm_of, homGdim_shift_right]
    | zero => simp
    | add y y' hy hy' => simp only [map_add, mul_add, hy, hy']
    | neg y hy => simp only [map_neg, mul_neg, hy]
  | zero => simp
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, mul_add, hx, hx']
  | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, mul_neg, hx]

/-- `([A e], [Q]) = gdim (e Q)` for a degree-zero idempotent `e`. -/
theorem homForm_ofIdempotent {e : A} (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (Q : GProj 𝒜) :
    homForm 𝒜 (of (GProj.ofIdempotent e he he0)) (of Q) = gdim (idem Q.grading e) := by
  rw [homForm_of, homGdim]
  exact gdim_homGrade_ofIdempotent he he0

end K0

end Form

end Categorification.Graded
