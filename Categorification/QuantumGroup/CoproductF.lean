/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Coproduct

/-!
# The comultiplication `r` descends to `f`

Lusztig, *Introduction to quantum groups*, 1.2.5 (the radical `ℐ` satisfies
`r(ℐ) ⊆ ℐ ⊗ 'f + 'f ⊗ ℐ`, so `r` induces `r : f → f ⊗ f`); Khovanov–Lauda, arXiv:0803.4121v2,
§3.1 ("The bilinear form and the comultiplication `r` descend to the quotient algebra").

We work over a field `K` with a symmetric pairing `dot`.

## The twisted tensor square of `f`

Let `Φ : 'f ⊗ 'f → f ⊗ f` be `π ⊗ π` (`PreF.toTensorF`, with target Mathlib's
`TensorProduct K f f`). Its kernel `PreF.kerIdeal` — which is `ℐ ⊗ 'f + 'f ⊗ ℐ` — is a
two-sided ideal of the twisted algebra `'f ⊗ 'f` (the twist `v^{|x₂|·|y₁|}` preserves `ℐ`,
because `ℐ` is compatible with the weight grading: `PreF.form_twistBy`). The quotient
`PreF.TwSqF = ('f ⊗ 'f) / ker Φ` is therefore an algebra: the twisted tensor square `f ⊗ f`,
with `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂` (`PreF.mkF_tw_mul_tw`), and
`PreF.twSqFEquiv : f ⊗ f ≃ₗ TensorProduct K f f` identifies its underlying vector space.

## Main results

* `PreF.toTensorF_r_eq_zero` — **Lusztig 1.2.5**: `r(ℐ) ⊆ ker (π ⊗ π) = ℐ ⊗ 'f + 'f ⊗ ℐ`.
  Proof: for `x ∈ ℐ`, contracting `r(x)` with `( -, a)` in the first factor gives an element
  `y ↦ (r x, a ⊗ y) = (x, a y) = 0` of `ℐ`; since the form on `f` is nondegenerate, the
  components of `(π ⊗ π)(r x)` with respect to a basis of the second factor vanish.
* `PreF.rbar` — the algebra homomorphism `r̄ : f → f ⊗ f` with `r̄(π x) = [r x]`
  (`PreF.rbar_π`, `PreF.twSqFEquiv_rbar_π`);
* `PreF.rbar_dpowF` — Lusztig 1.4.2 in `f`:
  `r̄(θ_i^{(a)}) = Σ_{t+t'=a} v_i^{tt'} θ_i^{(t)} ⊗ θ_i^{(t')}`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset TensorProduct
open TwistedMonoidAlgebra (single)
open scoped Classical

/-- A `K`-linear map out of a quotient `R ⧸ J` induced by a `K`-linear map killing `J`. -/
def Ideal.quotLiftₗ {K R M : Type*} [CommRing K] [Ring R] [Algebra K R] (J : Ideal R)
    [J.IsTwoSided] [AddCommGroup M] [Module K M] (g : R →ₗ[K] M) (hg : ∀ x ∈ J, g x = 0) :
    (R ⧸ J) →ₗ[K] M where
  toFun x := Quotient.liftOn' x g fun a b hab => by
    have := hg _ ((Submodule.quotientRel_def _).1 hab)
    rwa [map_sub, sub_eq_zero] at this
  map_add' x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add]
    exact map_add g a b
  map_smul' r x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul]
    exact map_smul g r a

theorem Ideal.quotLiftₗ_mk {K R M : Type*} [CommRing K] [Ring R] [Algebra K R] (J : Ideal R)
    [J.IsTwoSided] [AddCommGroup M] [Module K M] (g : R →ₗ[K] M) (hg : ∀ x ∈ J, g x = 0)
    (x : R) : Ideal.quotLiftₗ J g hg (Ideal.Quotient.mk J x) = g x := rfl

namespace PreF

section CommRing

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ} {c : I → K}

variable (v) in
/-- The weight twist `w ↦ v^{χ(|w|)} w` on `'f`. -/
def twistBy (χ : Multiset I → ℤ) : PreF K I →ₗ[K] PreF K I :=
  linLift fun u => ((v ^ χ (wt u) : Kˣ) : K) • word u

theorem twistBy_word (χ : Multiset I → ℤ) (u : FreeMonoid I) :
    twistBy v χ (word u : PreF K I) = ((v ^ χ (wt u) : Kˣ) : K) • word u :=
  linLift_word _ _

/-- Weight twists are self-adjoint for `( , )`, since distinct weight spaces are orthogonal. -/
theorem form_twistBy (χ : Multiset I → ℤ) (x y : PreF K I) :
    form dot v c (twistBy v χ x) y = form dot v c x (twistBy v χ y) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | smul_word w s =>
      simp only [map_smul, twistBy_word, LinearMap.smul_apply, smul_eq_mul]
      by_cases h : wt u = wt w
      · rw [h]; ring
      · rw [form_eq_zero_of_wt_ne h]; ring

theorem twistBy_mem_radical (χ : Multiset I → ℤ) {x : PreF K I} (hx : x ∈ radical dot v c) :
    twistBy v χ x ∈ radical dot v c := fun y => by rw [form_twistBy, hx]

end CommRing

variable {I : Type*} {K : Type*} [Field K] {dot : I → I → ℤ} {v : Kˣ} {c : I → K}

/-! ### Linear maps on `f` -/

variable (dot v c) in
/-- A linear map out of `f` induced by a linear map out of `'f` killing `ℐ`. -/
def liftF {M : Type*} [AddCommGroup M] [Module K M] (g : PreF K I →ₗ[K] M)
    (hg : ∀ x ∈ radical dot v c, g x = 0) : F dot v c →ₗ[K] M :=
  Ideal.quotLiftₗ (radical dot v c) g hg

theorem liftF_π {M : Type*} [AddCommGroup M] [Module K M] (g : PreF K I →ₗ[K] M)
    (hg : ∀ x ∈ radical dot v c, g x = 0) (x : PreF K I) :
    liftF dot v c g hg (π dot v c x) = g x := rfl

variable (dot v c) in
/-- The weight twist `twistBy v χ` on `f`. -/
def twistF (χ : Multiset I → ℤ) : F dot v c →ₗ[K] F dot v c :=
  liftF dot v c ((π dot v c).toLinearMap ∘ₗ twistBy v χ) fun _ hx =>
    π_eq_zero_iff.2 (twistBy_mem_radical χ hx)

theorem twistF_π_word (χ : Multiset I → ℤ) (u : FreeMonoid I) :
    twistF dot v c χ (π dot v c (word u)) = ((v ^ χ (wt u) : Kˣ) : K) • π dot v c (word u) := by
  rw [twistF, liftF_π, LinearMap.comp_apply, twistBy_word, AlgHom.toLinearMap_apply, map_smul]

/-! ### The map `'f ⊗ 'f → f ⊗ f` and its kernel -/

variable (dot v c) in
/-- `π ⊗ π : 'f ⊗ 'f → f ⊗ f` (target: Mathlib's tensor product of vector spaces). -/
def toTensorF : TwSq K I dot v →ₗ[K] F dot v c ⊗[K] F dot v c :=
  TensorProduct.map (π dot v c).toLinearMap (π dot v c).toLinearMap ∘ₗ
    (tensorEquiv (dot := dot) (v := v)).symm.toLinearMap

theorem tensorEquiv_symm_tw (x y : PreF K I) :
    (tensorEquiv (dot := dot) (v := v)).symm (tw dot v x y) = x ⊗ₜ[K] y := by
  rw [LinearEquiv.symm_apply_eq, tensorEquiv_tmul]

theorem toTensorF_tw (x y : PreF K I) :
    toTensorF dot v c (tw dot v x y) = π dot v c x ⊗ₜ[K] π dot v c y := by
  simp [toTensorF, tensorEquiv_symm_tw]

theorem toTensorF_single (u w : FreeMonoid I) (s : K) :
    toTensorF dot v c (single (u, w) s : TwSq K I dot v) =
      s • (π dot v c (word u) ⊗ₜ[K] π dot v c (word w)) := by
  rw [single_eq_smul_tw, map_smul, toTensorF_tw]

theorem toTensorF_surjective : Function.Surjective (toTensorF dot v c) :=
  (TensorProduct.map_surjective π_surjective π_surjective).comp
    (tensorEquiv (dot := dot) (v := v)).symm.surjective

theorem toTensorF_single_mul (a b : FreeMonoid I) (X : TwSq K I dot v) :
    toTensorF dot v c (single (a, b) 1 * X) =
      TensorProduct.map (LinearMap.mulLeft K (π dot v c (word a)) ∘ₗ
          twistF dot v c (wdot dot (wt b))) (LinearMap.mulLeft K (π dot v c (word b)))
        (toTensorF dot v c X) := by
  have : toTensorF dot v c ∘ₗ LinearMap.mulLeft K (single (a, b) 1 : TwSq K I dot v) =
      TensorProduct.map (LinearMap.mulLeft K (π dot v c (word a)) ∘ₗ
          twistF dot v c (wdot dot (wt b))) (LinearMap.mulLeft K (π dot v c (word b))) ∘ₗ
        toTensorF dot v c := by
    refine twSq_lhom_ext fun u w => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, twSq_single_mul_single,
      toTensorF_single, map_smul, TensorProduct.map_tmul, twistF_π_word, Prod.mk_mul_mk,
      word_mul, map_mul, mul_smul_comm, TensorProduct.smul_tmul', one_smul, mul_one]
  exact LinearMap.congr_fun this X

theorem toTensorF_mul_single (X : TwSq K I dot v) (a b : FreeMonoid I) :
    toTensorF dot v c (X * single (a, b) 1) =
      TensorProduct.map (LinearMap.mulRight K (π dot v c (word a)))
        (LinearMap.mulRight K (π dot v c (word b)) ∘ₗ
          twistF dot v c (fun ν => wdot dot ν (wt a))) (toTensorF dot v c X) := by
  have : toTensorF dot v c ∘ₗ LinearMap.mulRight K (single (a, b) 1 : TwSq K I dot v) =
      TensorProduct.map (LinearMap.mulRight K (π dot v c (word a)))
        (LinearMap.mulRight K (π dot v c (word b)) ∘ₗ
          twistF dot v c (fun ν => wdot dot ν (wt a))) ∘ₗ toTensorF dot v c := by
    refine twSq_lhom_ext fun u w => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, twSq_single_mul_single,
      toTensorF_single, map_smul, TensorProduct.map_tmul, twistF_π_word, Prod.mk_mul_mk,
      word_mul, map_mul, smul_mul_assoc, TensorProduct.tmul_smul, one_smul, mul_one]
  exact LinearMap.congr_fun this X

variable (dot v c) in
/-- The kernel of `π ⊗ π : 'f ⊗ 'f → f ⊗ f`, a two-sided ideal of the twisted algebra
`'f ⊗ 'f`. -/
def kerIdeal : Ideal (TwSq K I dot v) where
  carrier := {X | toTensorF dot v c X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [map_add, hX, hY, add_zero]
  zero_mem' := map_zero _
  smul_mem' Z X hX := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hX ⊢
    induction Z using TwistedMonoidAlgebra.induction_linear with
    | zero => simp
    | add Z Z' h h' => rw [add_mul, map_add, h, h', add_zero]
    | single p r =>
      obtain ⟨a, b⟩ := p
      rw [TwistedMonoidAlgebra.single_eq_smul, smul_mul_assoc, map_smul, toTensorF_single_mul,
        hX, map_zero, smul_zero]

theorem mem_kerIdeal {X : TwSq K I dot v} : X ∈ kerIdeal dot v c ↔ toTensorF dot v c X = 0 :=
  Iff.rfl

instance kerIdeal_isTwoSided : (kerIdeal dot v c).IsTwoSided := by
  refine ⟨fun {X} Z hX => ?_⟩
  rw [mem_kerIdeal] at hX ⊢
  induction Z using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Z Z' h h' => rw [mul_add, map_add, h, h', add_zero]
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [TwistedMonoidAlgebra.single_eq_smul, mul_smul_comm, map_smul, toTensorF_mul_single, hX,
      map_zero, smul_zero]

variable (dot v c) in
/-- The twisted tensor square `f ⊗ f = ('f ⊗ 'f) / ker (π ⊗ π)` (Lusztig 1.2.5). -/
def TwSqF : Type _ := TwSq K I dot v ⧸ kerIdeal dot v c

instance instRingTwSqF : Ring (TwSqF dot v c) := Ideal.Quotient.ring _

instance instAlgebraTwSqF : Algebra K (TwSqF dot v c) := Ideal.Quotient.algebra K

variable (dot v c) in
/-- The quotient map `'f ⊗ 'f → f ⊗ f`. -/
def mkF : TwSq K I dot v →ₐ[K] TwSqF dot v c := Ideal.Quotient.mkₐ K (kerIdeal dot v c)

theorem mkF_eq_zero_iff {X : TwSq K I dot v} :
    mkF dot v c X = 0 ↔ toTensorF dot v c X = 0 :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The twisted multiplication of `f ⊗ f` on words:
`(a ⊗ b)(c ⊗ e) = v^{|b|·|c|} ac ⊗ be`. -/
theorem mkF_tw_mul_tw (a b c' e : FreeMonoid I) :
    mkF dot v c (tw dot v (word a) (word b)) * mkF dot v c (tw dot v (word c') (word e)) =
      ((v ^ wdot dot (wt b) (wt c') : Kˣ) : K) •
        mkF dot v c (tw dot v (word (a * c')) (word (b * e))) := by
  rw [← map_mul, ← map_smul, tw_word, tw_word, tw_word, twSq_single_mul_single,
    TwistedMonoidAlgebra.smul_single]
  simp

variable (dot v c) in
/-- The linear identification `f ⊗ f ≃ TensorProduct K f f`, `[x ⊗ y] ↦ π x ⊗ π y`. -/
def twSqFEquiv : TwSqF dot v c ≃ₗ[K] F dot v c ⊗[K] F dot v c :=
  LinearEquiv.ofBijective (Ideal.quotLiftₗ (kerIdeal dot v c) (toTensorF dot v c) fun _ h => h)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro X hX
      obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective X
      exact Ideal.Quotient.eq_zero_iff_mem.2 hX,
    fun Ξ => by
      obtain ⟨Y, rfl⟩ := toTensorF_surjective (dot := dot) (v := v) (c := c) Ξ
      exact ⟨Ideal.Quotient.mk _ Y, rfl⟩⟩

theorem twSqFEquiv_mkF (X : TwSq K I dot v) :
    twSqFEquiv dot v c (mkF dot v c X) = toTensorF dot v c X := rfl

theorem twSqFEquiv_mkF_tw (x y : PreF K I) :
    twSqFEquiv dot v c (mkF dot v c (tw dot v x y)) = π dot v c x ⊗ₜ[K] π dot v c y :=
  toTensorF_tw x y

/-! ### `r(ℐ) ⊆ ker (π ⊗ π)` -/

variable (c) in
/-- Contraction of the first tensor factor with `( -, a)`: `u ⊗ w ↦ (u, a) w`. -/
def contractL (a : PreF K I) : TwSq K I dot v →ₗ[K] PreF K I :=
  TwistedMonoidAlgebra.lift fun p => form dot v c (word p.1) a • word p.2

theorem form_contractL (a : PreF K I) (X : TwSq K I dot v) (y : PreF K I) :
    form dot v c (contractL c a X) y = pair (form dot v c) X (tw dot v a y) := by
  induction X using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add X X' hX hX' => simp only [map_add, LinearMap.add_apply, hX, hX']
  | single p s =>
    obtain ⟨u, w⟩ := p
    rw [contractL, TwistedMonoidAlgebra.lift_single, pair_single_tw, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]

theorem contractL_r_mem_radical (hdot : ∀ i j, dot i j = dot j i) (a : PreF K I) {x : PreF K I}
    (hx : x ∈ radical dot v c) : contractL c a (r dot v x) ∈ radical dot v c := fun y => by
  rw [form_contractL, ← form_mul_right hdot, hx]

variable (dot v c) in
/-- The functional `z ↦ (z, π a)` on `f`. -/
def formAt (a : PreF K I) : F dot v c →ₗ[K] K :=
  liftF dot v c ((form dot v c).flip a) fun _ hx => hx a

variable (dot v c) in
/-- Contraction `f ⊗ f → f`, `z ⊗ w ↦ (z, π a) w`. -/
def contractF (a : PreF K I) : F dot v c ⊗[K] F dot v c →ₗ[K] F dot v c :=
  (TensorProduct.lid K (F dot v c)).toLinearMap ∘ₗ LinearMap.rTensor (F dot v c) (formAt dot v c a)

theorem contractF_toTensorF (a : PreF K I) (X : TwSq K I dot v) :
    contractF dot v c a (toTensorF dot v c X) = π dot v c (contractL c a X) := by
  induction X using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add X X' hX hX' => rw [map_add, map_add, hX, hX', map_add, map_add]
  | single p s =>
    obtain ⟨u, w⟩ := p
    rw [toTensorF_single, map_smul, contractL, TwistedMonoidAlgebra.lift_single, map_smul,
      map_smul]
    simp [contractF, formAt, liftF_π]

theorem repr_contractF {κ : Type*} [DecidableEq κ] (b : Basis κ K (F dot v c)) (a : PreF K I)
    (Ξ : F dot v c ⊗[K] F dot v c) (k : κ) :
    b.repr (contractF dot v c a Ξ) k =
      formAt dot v c a (TensorProduct.equivFinsuppOfBasisRight b Ξ k) := by
  induction Ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp [contractF, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, mul_comm]
  | add Ξ Ξ' h h' => simp only [map_add, Finsupp.add_apply, h, h']

/-- **Lusztig 1.2.5**: `r` maps the radical `ℐ` into the kernel `ℐ ⊗ 'f + 'f ⊗ ℐ` of
`π ⊗ π : 'f ⊗ 'f → f ⊗ f`. -/
theorem toTensorF_r_eq_zero (hdot : ∀ i j, dot i j = dot j i) {x : PreF K I}
    (hx : x ∈ radical dot v c) : toTensorF dot v c (r dot v x) = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (TensorProduct.equivFinsuppOfBasisRight (M := F dot v c)
    (Basis.ofVectorSpace K (F dot v c)))).1 ?_
  ext k
  rw [Finsupp.zero_apply]
  refine formF_nondegenerate hdot fun z => ?_
  obtain ⟨a, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) z
  have h1 := repr_contractF (Basis.ofVectorSpace K (F dot v c)) a
    (toTensorF dot v c (r dot v x)) k
  rw [contractF_toTensorF, π_eq_zero_iff.2 (contractL_r_mem_radical hdot a hx), map_zero,
    Finsupp.zero_apply] at h1
  obtain ⟨m, hm⟩ := π_surjective (dot := dot) (v := v) (c := c)
    (TensorProduct.equivFinsuppOfBasisRight (M := F dot v c) (Basis.ofVectorSpace K (F dot v c))
      (toTensorF dot v c (r dot v x)) k)
  rw [← hm] at h1 ⊢
  rw [formF_π]
  exact h1.symm

theorem r_mem_kerIdeal (hdot : ∀ i j, dot i j = dot j i) {x : PreF K I}
    (hx : x ∈ radical dot v c) : r dot v x ∈ kerIdeal dot v c :=
  toTensorF_r_eq_zero hdot hx

variable (dot v c) in
/-- **Lusztig 1.2.5**: the comultiplication `r̄ : f → f ⊗ f` induced by `r` (for a symmetric
pairing `dot`), an algebra homomorphism for the twisted multiplication of `f ⊗ f`. -/
def rbar (hdot : ∀ i j, dot i j = dot j i) : F dot v c →ₐ[K] TwSqF dot v c :=
  Ideal.Quotient.liftₐ (radical dot v c) ((mkF dot v c).comp (r dot v)) fun _ hx =>
    Ideal.Quotient.eq_zero_iff_mem.2 (r_mem_kerIdeal hdot hx)

theorem rbar_π (hdot : ∀ i j, dot i j = dot j i) (x : PreF K I) :
    rbar dot v c hdot (π dot v c x) = mkF dot v c (r dot v x) := rfl

theorem twSqFEquiv_rbar_π (hdot : ∀ i j, dot i j = dot j i) (x : PreF K I) :
    twSqFEquiv dot v c (rbar dot v c hdot (π dot v c x)) = toTensorF dot v c (r dot v x) := rfl

theorem rbar_θ (hdot : ∀ i j, dot i j = dot j i) (i : I) :
    twSqFEquiv dot v c (rbar dot v c hdot (π dot v c (θ i))) =
      π dot v c (θ i) ⊗ₜ[K] 1 + 1 ⊗ₜ[K] π dot v c (θ i) := by
  rw [twSqFEquiv_rbar_π, r_θ', map_add, toTensorF_tw, toTensorF_tw, map_one]

/-- **Lusztig 1.4.2 in `f`**:
`r̄(θ_i^{(a)}) = Σ_{t+t'=a} v_i^{tt'} θ_i^{(t)} ⊗ θ_i^{(t')}` in `f ⊗ f`. -/
theorem rbar_dpowF (hdot : ∀ i j, dot i j = dot j i) (i : I) (hev : Even (dot i i)) {a : ℕ}
    (hq : qfact (vi dot v i) a ≠ 0) :
    twSqFEquiv dot v c (rbar dot v c hdot (dpowF dot v c i a)) = ∑ p ∈ antidiagonal a,
      ((vi dot v i ^ ((p.1 : ℤ) * p.2) : Kˣ) : K) •
        (dpowF dot v c i p.1 ⊗ₜ[K] dpowF dot v c i p.2) := by
  rw [dpowF, twSqFEquiv_rbar_π, r_dpow i hev hq, map_sum]
  simp only [map_smul, toTensorF_tw, dpowF]

end PreF

end Categorification.QuantumGroup

end
