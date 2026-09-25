/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.TwistedMonoidAlgebra

/-!
# Lusztig's free algebra `'f` and its twisted comultiplication

Let `I` be a set with a bilinear pairing `dot : I → I → ℤ` (a Cartan datum
`(I, ·)` in the sense of Lusztig, *Introduction to quantum groups*, §1.1.1; only the values
`i · j` are used here), `K` a commutative ring and `v ∈ Kˣ`. Following Lusztig §1.2 and
Khovanov–Lauda, arXiv:0803.4121v2, §3.1:

* `'f` is the free associative `K`-algebra on generators `θ i` (`i ∈ I`). We realise it as
  the monoid algebra `PreF K I = K[FreeMonoid I]` of the free monoid of words; Mathlib's
  `FreeAlgebra.equivMonoidAlgebraFreeMonoid` identifies it with `FreeAlgebra K I`
  (see `PreF.equivFreeAlgebra`). Words `w` give the `K`-basis `PreF.word w`.
* A word `w` has weight `wt w ∈ ℕ[I]`, the multiset of its letters. This is the
  `ℕ[I]`-grading `'f = ⊕_ν 'f_ν` (Lusztig 1.2.1); `wdot` is the bilinear extension of `dot`
  to `ℕ[I]`.
* `'f ⊗ 'f` carries the twisted multiplication (Lusztig 1.2.2; KL I eq. (3.1), where KL's
  `q` is Lusztig's `v⁻¹`)
  `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂`.
  We realise it as the twisted monoid algebra `TwSq K I dot v` of
  `FreeMonoid I × FreeMonoid I`, with basis vectors `single (u, w) 1 = u ⊗ w`.
  `PreF.tensorEquiv` identifies it with Mathlib's `TensorProduct K 'f 'f` as a module,
  sending `x ⊗ₜ y` to `tw x y`.
* `PreF.r : 'f →ₐ[K] 'f ⊗ 'f` is the algebra homomorphism with
  `r (θ i) = θ i ⊗ 1 + 1 ⊗ θ i` (Lusztig 1.2.2).
* `PreF.d i : 'f →ₗ[K] 'f` is the twisted derivation determined by `d i (θ j) = δ_{ij}` and
  `d i (x y) = d i x · y + v^{|x|·i} x · d i y` (a form of Lusztig's `r_i`, 1.2.13). It
  satisfies `r ∘ d i = (d i ⊗ 1) ∘ r` (`PreF.r_d`), the key identity used to construct the
  bilinear form in `Categorification.QuantumGroup.Form`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open TwistedMonoidAlgebra (single single_mul_single)
open scoped Classical

variable {I : Type*}

/-! ### Weights -/

/-- The weight `|w| ∈ ℕ[I]` of a word `w`: the multiset of its letters. -/
def wt (w : FreeMonoid I) : Multiset I := (FreeMonoid.toList w : Multiset I)

@[simp] theorem wt_one : wt (1 : FreeMonoid I) = 0 := rfl

@[simp] theorem wt_mul (u w : FreeMonoid I) : wt (u * w) = wt u + wt w := by
  simp [wt, FreeMonoid.toList_mul]

@[simp] theorem wt_of (i : I) : wt (FreeMonoid.of i) = {i} := rfl

theorem wt_of_mul (i : I) (w : FreeMonoid I) : wt (FreeMonoid.of i * w) = i ::ₘ wt w := by
  simp [wt]

/-- The bilinear extension `μ · ν` to `ℕ[I]` of the pairing `dot : I → I → ℤ`. -/
def wdot (dot : I → I → ℤ) (μ ν : Multiset I) : ℤ :=
  (μ.map fun a => (ν.map (dot a)).sum).sum

section wdot

variable (dot : I → I → ℤ)

@[simp] theorem wdot_zero_left (ν : Multiset I) : wdot dot 0 ν = 0 := by simp [wdot]

@[simp] theorem wdot_zero_right (μ : Multiset I) : wdot dot μ 0 = 0 := by simp [wdot]

theorem wdot_add_left (μ μ' ν : Multiset I) :
    wdot dot (μ + μ') ν = wdot dot μ ν + wdot dot μ' ν := by simp [wdot]

theorem wdot_add_right (μ ν ν' : Multiset I) :
    wdot dot μ (ν + ν') = wdot dot μ ν + wdot dot μ ν' := by
  simp [wdot, Multiset.sum_map_add]

@[simp] theorem wdot_cons_left (a : I) (μ ν : Multiset I) :
    wdot dot (a ::ₘ μ) ν = wdot dot {a} ν + wdot dot μ ν := by
  rw [← Multiset.singleton_add, wdot_add_left]

@[simp] theorem wdot_cons_right (a : I) (μ ν : Multiset I) :
    wdot dot μ (a ::ₘ ν) = wdot dot μ {a} + wdot dot μ ν := by
  rw [← Multiset.singleton_add, wdot_add_right]

@[simp] theorem wdot_singleton (a b : I) : wdot dot {a} {b} = dot a b := by simp [wdot]

theorem wdot_singleton_comm (hdot : ∀ i j, dot i j = dot j i) (a : I) (ν : Multiset I) :
    wdot dot {a} ν = wdot dot ν {a} := by
  induction ν using Multiset.induction_on with
  | empty => simp
  | cons b ν ih => rw [wdot_cons_right, wdot_cons_left, ih, wdot_singleton, wdot_singleton, hdot]

theorem wdot_comm (hdot : ∀ i j, dot i j = dot j i) (μ ν : Multiset I) :
    wdot dot μ ν = wdot dot ν μ := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons a μ ih => rw [wdot_cons_left, wdot_cons_right, ih, wdot_singleton_comm dot hdot, add_comm]

end wdot

/-! ### The free algebra `'f` -/

/-- Lusztig's free algebra `'f` (Lusztig 1.2.1; KL I §3.1): the free associative `K`-algebra
on generators `θ i`, `i ∈ I`, realised as the monoid algebra of the free monoid on `I`. -/
abbrev PreF (K : Type*) [CommRing K] (I : Type*) := MonoidAlgebra K (FreeMonoid I)

namespace PreF

variable {K : Type*} [CommRing K]

/-- The identification of `'f` with Mathlib's free algebra. -/
def equivFreeAlgebra : FreeAlgebra K I ≃ₐ[K] PreF K I := FreeAlgebra.equivMonoidAlgebraFreeMonoid

/-- The basis vector of `'f` given by a word `w = i₁ ⋯ iₙ`, i.e. `θ i₁ ⋯ θ iₙ`. -/
def word (w : FreeMonoid I) : PreF K I := MonoidAlgebra.single w 1

/-- The generator `θ i` of `'f`. -/
def θ (i : I) : PreF K I := word (FreeMonoid.of i)

@[simp] theorem word_one : (word 1 : PreF K I) = 1 := rfl

theorem word_mul (u w : FreeMonoid I) : (word (u * w) : PreF K I) = word u * word w := by
  simp [word, MonoidAlgebra.single_mul_single]

theorem word_of_mul (i : I) (w : FreeMonoid I) :
    (word (FreeMonoid.of i * w) : PreF K I) = θ i * word w := word_mul _ _

theorem single_eq_smul_word (w : FreeMonoid I) (r : K) :
    (MonoidAlgebra.single w r : PreF K I) = r • word w := by
  simp [word, MonoidAlgebra.smul_single']

theorem equivFreeAlgebra_ι (i : I) : equivFreeAlgebra (FreeAlgebra.ι K i) = (θ i : PreF K I) := by
  simp [equivFreeAlgebra, FreeAlgebra.equivMonoidAlgebraFreeMonoid, θ, word]

/-- Linear-combination induction on `'f`. -/
@[elab_as_elim]
theorem induction_linear {motive : PreF K I → Prop} (x : PreF K I) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul_word : ∀ w (r : K), motive (r • word w)) : motive x :=
  Finsupp.induction_linear (motive := motive) x zero add fun w r => by
    have := smul_word w r
    rwa [← single_eq_smul_word] at this

/-- Two linear maps out of `'f` agreeing on words are equal. -/
theorem lhom_ext {N : Type*} [AddCommMonoid N] [Module K N] ⦃φ ψ : PreF K I →ₗ[K] N⦄
    (h : ∀ w, φ (word w) = ψ (word w)) : φ = ψ :=
  Finsupp.lhom_ext (φ := φ) (ψ := ψ) fun w r => by
    change φ (MonoidAlgebra.single w r) = ψ (MonoidAlgebra.single w r)
    rw [single_eq_smul_word, map_smul, map_smul, h]

/-- The linear map out of `'f` sending the word `w` to `f w`. -/
def linLift {N : Type*} [AddCommMonoid N] [Module K N] (f : FreeMonoid I → N) :
    PreF K I →ₗ[K] N :=
  Finsupp.linearCombination K f

@[simp] theorem linLift_word {N : Type*} [AddCommMonoid N] [Module K N]
    (f : FreeMonoid I → N) (w : FreeMonoid I) : linLift (K := K) f (word w) = f w :=
  (Finsupp.linearCombination_single K 1 w).trans (one_smul _ _)

/-- The counit `ε : 'f → K`, the coefficient of the empty word. -/
def counit : PreF K I →ₗ[K] K := linLift fun w => if w = 1 then 1 else 0

@[simp] theorem counit_word (w : FreeMonoid I) :
    counit (word w : PreF K I) = if w = 1 then 1 else 0 := linLift_word _ _

@[simp] theorem counit_one : counit (1 : PreF K I) = 1 := by
  rw [← word_one, counit_word, if_pos rfl]

theorem counit_θ_mul (i : I) (x : PreF K I) : counit (θ i * x) = 0 := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul_word w r =>
    rw [mul_smul_comm, map_smul, ← word_of_mul, counit_word,
      if_neg (by simp [← FreeMonoid.length_eq_zero, FreeMonoid.length_mul]), smul_zero]

/-! ### Supported submodules -/

/-- The submodule of `'f` spanned by the words in `S`. -/
def supp (S : Set (FreeMonoid I)) : Submodule K (PreF K I) := Finsupp.supported K K S

theorem supp_eq_span (S : Set (FreeMonoid I)) :
    (supp S : Submodule K (PreF K I)) = Submodule.span K (word '' S) :=
  Finsupp.supported_eq_span_single K S

theorem word_mem_supp {S : Set (FreeMonoid I)} {w : FreeMonoid I} (h : w ∈ S) :
    (word w : PreF K I) ∈ supp S :=
  Finsupp.single_mem_supported K 1 h

theorem supp_mono {S T : Set (FreeMonoid I)} (h : S ⊆ T) :
    (supp S : Submodule K (PreF K I)) ≤ supp T :=
  Finsupp.supported_mono h

/-- Two linear maps out of `'f` agreeing on the words of `S` agree on `supp S`. -/
theorem eqOn_supp {N : Type*} [AddCommMonoid N] [Module K N] (φ ψ : PreF K I →ₗ[K] N)
    {S : Set (FreeMonoid I)} (h : ∀ w ∈ S, φ (word w) = ψ (word w)) :
    ∀ x ∈ (supp S : Submodule K (PreF K I)), φ x = ψ x := by
  intro x hx
  have : supp S ≤ LinearMap.eqLocus φ ψ := by
    rw [supp_eq_span, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  exact this hx

/-- A linear map sending the words of `S` into `supp T` sends `supp S` into `supp T`. -/
theorem map_supp_le (φ : PreF K I →ₗ[K] PreF K I) {S T : Set (FreeMonoid I)}
    (h : ∀ w ∈ S, φ (word w) ∈ (supp T : Submodule K (PreF K I))) :
    ∀ x ∈ (supp S : Submodule K (PreF K I)), φ x ∈ (supp T : Submodule K (PreF K I)) := by
  intro x hx
  have : supp S ≤ (supp T).comap φ := by
    rw [supp_eq_span, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  exact this hx

/-! ### The twisted tensor square -/

variable (dot : I → I → ℤ) (v : Kˣ)

/-- The 2-cocycle `((u₁, u₂), (w₁, w₂)) ↦ v^{|u₂|·|w₁|}` on pairs of words defining the twisted
multiplication of `'f ⊗ 'f` (Lusztig 1.2.2). -/
def tensorCocycle (K : Type*) [CommRing K] (I : Type*) (dot : I → I → ℤ) (v : Kˣ) :
    TwistCocycle K (FreeMonoid I × FreeMonoid I) where
  τ a b := ((v ^ wdot dot (wt a.2) (wt b.1) : Kˣ) : K)
  one_left a := by simp
  one_right a := by simp
  assoc a b c := by
    simp only [Prod.fst_mul, Prod.snd_mul, wt_mul, wdot_add_left, wdot_add_right]
    rw [← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
    congr 2
    ring

/-- The twisted tensor square `'f ⊗ 'f` (Lusztig 1.2.2; KL I eq. (3.1)): the basis vector
`single (u, w) 1` is `u ⊗ w`, and `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂`. -/
abbrev TwSq (K : Type*) [CommRing K] (I : Type*) (dot : I → I → ℤ) (v : Kˣ) :=
  TwistedMonoidAlgebra (tensorCocycle K I dot v)

variable {dot v}

theorem twSq_single_mul_single (a b : FreeMonoid I × FreeMonoid I) (r s : K) :
    (single a r : TwSq K I dot v) * single b s =
      single (a * b) (((v ^ wdot dot (wt a.2) (wt b.1) : Kˣ) : K) * r * s) :=
  single_mul_single a b r s

theorem twSq_lhom_ext {N : Type*} [AddCommMonoid N] [Module K N]
    ⦃φ ψ : TwSq K I dot v →ₗ[K] N⦄ (h : ∀ u w, φ (single (u, w) 1) = ψ (single (u, w) 1)) :
    φ = ψ :=
  TwistedMonoidAlgebra.lhom_ext fun p => h p.1 p.2

variable (dot v)

/-- The algebra embedding `x ↦ x ⊗ 1`. -/
def inl : PreF K I →ₐ[K] TwSq K I dot v :=
  MonoidAlgebra.lift K (FreeMonoid I) (TwSq K I dot v)
    { toFun := fun w => single (w, 1) 1
      map_one' := rfl
      map_mul' := fun u w => by
        rw [twSq_single_mul_single]
        simp }

/-- The algebra embedding `x ↦ 1 ⊗ x`. -/
def inr : PreF K I →ₐ[K] TwSq K I dot v :=
  MonoidAlgebra.lift K (FreeMonoid I) (TwSq K I dot v)
    { toFun := fun w => single (1, w) 1
      map_one' := rfl
      map_mul' := fun u w => by
        rw [twSq_single_mul_single]
        simp }

variable {dot v}

theorem inl_word (w : FreeMonoid I) :
    inl dot v (word w : PreF K I) = single (w, 1) 1 := by
  simp [inl, word, MonoidAlgebra.lift_single]

theorem inr_word (w : FreeMonoid I) :
    inr dot v (word w : PreF K I) = single (1, w) 1 := by
  simp [inr, word, MonoidAlgebra.lift_single]

variable (dot v)

/-- The tensor `x ⊗ y ∈ 'f ⊗ 'f`, i.e. `(x ⊗ 1)(1 ⊗ y)`. -/
def tw (x y : PreF K I) : TwSq K I dot v := inl dot v x * inr dot v y

variable {dot v}

theorem tw_word (u w : FreeMonoid I) :
    tw dot v (word u : PreF K I) (word w) = single (u, w) 1 := by
  simp [tw, inl_word, inr_word, twSq_single_mul_single]

theorem tw_add_left (x x' y : PreF K I) :
    tw dot v (x + x') y = tw dot v x y + tw dot v x' y := by simp [tw, add_mul]

theorem tw_add_right (x y y' : PreF K I) :
    tw dot v x (y + y') = tw dot v x y + tw dot v x y' := by simp [tw, mul_add]

theorem tw_smul_left (c : K) (x y : PreF K I) :
    tw dot v (c • x) y = c • tw dot v x y := by simp [tw]

theorem tw_smul_right (c : K) (x y : PreF K I) :
    tw dot v x (c • y) = c • tw dot v x y := by simp [tw]

@[simp] theorem tw_zero_left (y : PreF K I) : tw dot v 0 y = 0 := by simp [tw]

@[simp] theorem tw_zero_right (x : PreF K I) : tw dot v x 0 = 0 := by simp [tw]

theorem inl_mul_tw (a x y : PreF K I) :
    inl dot v a * tw dot v x y = tw dot v (a * x) y := by
  simp [tw, mul_assoc]

theorem tw_mul_inr (x y a : PreF K I) :
    tw dot v x y * inr dot v a = tw dot v x (y * a) := by
  simp [tw, mul_assoc]

/-- The twisted tensor square is `TensorProduct K 'f 'f` as a module: `x ⊗ₜ y ↦ tw x y`. -/
def tensorEquiv : TensorProduct K (PreF K I) (PreF K I) ≃ₗ[K] TwSq K I dot v :=
  finsuppTensorFinsupp' K (FreeMonoid I) (FreeMonoid I)

theorem tensorEquiv_tmul (x y : PreF K I) :
    tensorEquiv (x ⊗ₜ[K] y) = tw dot v x y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, hx, hx', tw_add_left]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, hy, hy', tw_add_right]
    | smul_word w s =>
      rw [TensorProduct.smul_tmul_smul, map_smul, tw_smul_left, tw_smul_right, tw_word,
        smul_smul]
      simp only [tensorEquiv, word]
      erw [finsuppTensorFinsupp'_single_tmul_single]
      simp [TwistedMonoidAlgebra.smul_single, single, mul_comm]

variable (dot v)

/-- Lusztig's comultiplication `r : 'f → 'f ⊗ 'f` (Lusztig 1.2.2; KL I §3.1): the algebra
homomorphism, for the twisted multiplication on `'f ⊗ 'f`, with
`r (θ i) = θ i ⊗ 1 + 1 ⊗ θ i`. -/
def r : PreF K I →ₐ[K] TwSq K I dot v :=
  MonoidAlgebra.lift K (FreeMonoid I) (TwSq K I dot v)
    (FreeMonoid.lift fun i => inl dot v (θ i) + inr dot v (θ i))

variable {dot v}

theorem r_θ (i : I) : r dot v (θ i : PreF K I) = inl dot v (θ i) + inr dot v (θ i) := by
  simp [r, θ, word, MonoidAlgebra.lift_single]

theorem r_θ' (i : I) : r dot v (θ i : PreF K I) = tw dot v (θ i) 1 + tw dot v 1 (θ i) := by
  simp [r_θ, tw]

theorem r_word_of_mul (i : I) (w : FreeMonoid I) :
    r dot v (word (FreeMonoid.of i * w) : PreF K I) =
      (inl dot v (θ i) + inr dot v (θ i)) * r dot v (word w) := by
  rw [word_of_mul, map_mul, r_θ]

/-! ### The twisted derivations `d i` -/

variable (dot v) in
/-- `d i` on a word, by recursion on its first letter. -/
def dW (i : I) : List I → PreF K I
  | [] => 0
  | j :: w => (if j = i then word (FreeMonoid.ofList w) else 0) +
      ((v ^ dot j i : Kˣ) : K) • (θ j * dW i w)

variable (dot v) in
/-- The twisted derivation `d i : 'f → 'f` with `d i (θ j) = δ_{ij}` and
`d i (x y) = d i x · y + v^{|x|·i} x · d i y` (compare Lusztig 1.2.13). Explicitly
`d i (j₁ ⋯ jₙ) = Σ_{p : j_p = i} v^{(j₁ + ⋯ + j_{p-1})·i} j₁ ⋯ ĵ_p ⋯ jₙ`. -/
def d (i : I) : PreF K I →ₗ[K] PreF K I :=
  linLift fun w => dW dot v i (FreeMonoid.toList w)

@[simp] theorem d_one (i : I) : d dot v i (1 : PreF K I) = 0 := by
  rw [← word_one, d, linLift_word]; rfl

theorem d_word_of_mul (i j : I) (w : FreeMonoid I) :
    d dot v i (word (FreeMonoid.of j * w) : PreF K I) =
      (if j = i then word w else 0) + ((v ^ dot j i : Kˣ) : K) • (θ j * d dot v i (word w)) := by
  simp only [d, linLift_word, FreeMonoid.toList_of_mul]
  rfl

theorem d_θ_mul (i j : I) (x : PreF K I) :
    d dot v i (θ j * x) =
      (if j = i then x else 0) + ((v ^ dot j i : Kˣ) : K) • (θ j * d dot v i x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [mul_add, map_add, hx, hy, map_add, mul_add, smul_add]
    split_ifs <;> abel
  | smul_word w c =>
    rw [mul_smul_comm, map_smul, ← word_of_mul, d_word_of_mul, map_smul, mul_smul_comm,
      smul_add, smul_comm c]
    split_ifs <;> simp

theorem d_θ (i j : I) : d dot v i (θ j : PreF K I) = if j = i then 1 else 0 := by
  have := d_θ_mul (dot := dot) (v := v) i j 1
  rw [mul_one, d_one, mul_zero, smul_zero, add_zero] at this
  exact this

/-- The twisted Leibniz rule for `d i`, with the left factor a word. -/
theorem d_word_mul (i : I) (u : FreeMonoid I) (y : PreF K I) :
    d dot v i (word u * y) =
      d dot v i (word u) * y + ((v ^ wdot dot (wt u) {i} : Kˣ) : K) • (word u * d dot v i y) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of j u ih =>
    rw [word_of_mul, mul_assoc, d_θ_mul, ih, d_θ_mul, wt_of_mul, wdot_cons_left, wdot_singleton,
      zpow_add, Units.val_mul]
    simp only [mul_add, smul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
    split_ifs <;> simp [add_assoc]

/-- `d i` lowers weights by `i`: every word in the support of `d i w` has weight `|w| - i`. -/
theorem d_word_mem_supp (i : I) (c : FreeMonoid I) :
    d dot v i (word c : PreF K I) ∈ (supp {w | i ::ₘ wt w = wt c} : Submodule K (PreF K I)) := by
  induction c using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of j c ih =>
    rw [d_word_of_mul]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · split_ifs with h
      · exact word_mem_supp (by simp [wt_of_mul, h])
      · exact Submodule.zero_mem _
    · refine map_supp_le (LinearMap.mulLeft K (θ j)) ?_ _ ih
      intro w hw
      simp only [LinearMap.mulLeft_apply, ← word_of_mul]
      refine word_mem_supp ?_
      simp only [Set.mem_setOf_eq, wt_of_mul] at hw ⊢
      rw [Multiset.cons_swap, hw]

/-! ### Formulas in the twisted tensor square -/

theorem inl_θ_mul_single (j : I) (c e : FreeMonoid I) (s : K) :
    inl dot v (θ j : PreF K I) * single (c, e) s =
      (single (FreeMonoid.of j * c, e) s : TwSq K I dot v) := by
  rw [θ, inl_word, twSq_single_mul_single]
  simp

theorem inr_θ_mul_single (j : I) (c e : FreeMonoid I) (s : K) :
    inr dot v (θ j : PreF K I) * single (c, e) s =
      (single (c, FreeMonoid.of j * e) (((v ^ wdot dot {j} (wt c) : Kˣ) : K) * s) :
        TwSq K I dot v) := by
  rw [θ, inr_word, twSq_single_mul_single]
  simp

/-- Commuting `1 ⊗ θ j` past `x ⊗ 1` for `x` homogeneous: if every word `w` in the support of
`x` has `j · |w| = n`, then `(1 ⊗ θ j)(x ⊗ 1) = v^n (x ⊗ 1)(1 ⊗ θ j)`. -/
theorem inr_θ_mul_inl (j : I) (n : ℤ) (x : PreF K I)
    (hx : x ∈ (supp {w | wdot dot {j} (wt w) = n} : Submodule K (PreF K I))) :
    inr dot v (θ j) * inl dot v x = ((v ^ n : Kˣ) : K) • (inl dot v x * inr dot v (θ j)) := by
  refine eqOn_supp (N := TwSq K I dot v)
    ((LinearMap.mulLeft K (inr dot v (θ j))) ∘ₗ (inl dot v).toLinearMap)
    (((v ^ n : Kˣ) : K) • ((LinearMap.mulRight K (inr dot v (θ j))) ∘ₗ (inl dot v).toLinearMap))
    ?_ x hx
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, LinearMap.smul_apply, LinearMap.mulRight_apply, inl_word, θ,
    inr_word, twSq_single_mul_single]
  simp [hw, TwistedMonoidAlgebra.smul_single]

variable (dot v) in
/-- The map `d i ⊗ 1` on `'f ⊗ 'f`. -/
def dL (i : I) : TwSq K I dot v →ₗ[K] TwSq K I dot v :=
  TwistedMonoidAlgebra.lift fun p => tw dot v (d dot v i (word p.1)) (word p.2)

theorem dL_single (i : I) (c e : FreeMonoid I) (s : K) :
    dL dot v i (single (c, e) s : TwSq K I dot v) = s • tw dot v (d dot v i (word c)) (word e) :=
  TwistedMonoidAlgebra.lift_single _ _ _

theorem dL_tw (i : I) (x y : PreF K I) :
    dL dot v i (tw dot v x y) = tw dot v (d dot v i x) y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [tw_add_left, map_add, hx, hx', map_add, tw_add_left]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tw_add_right, map_add, hy, hy', tw_add_right]
    | smul_word w s =>
      rw [tw_smul_left, tw_smul_right, tw_word, map_smul, map_smul, dL_single, map_smul,
        tw_smul_left, tw_smul_right, one_smul]

theorem dL_inl_θ_mul (i j : I) (Y : TwSq K I dot v) :
    dL dot v i (inl dot v (θ j) * Y) =
      (if j = i then Y else 0) + ((v ^ dot j i : Kˣ) : K) • (inl dot v (θ j) * dL dot v i Y) := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' =>
    rw [mul_add, map_add, hY, hY', map_add, mul_add, smul_add]
    split_ifs <;> abel
  | single p s =>
    obtain ⟨c, e⟩ := p
    rw [inl_θ_mul_single, dL_single, dL_single, d_word_of_mul, mul_smul_comm,
      inl_mul_tw, tw_add_left, tw_smul_left, smul_add]
    split_ifs
    · rw [tw_word, smul_comm, TwistedMonoidAlgebra.smul_single, mul_one]
    · simp only [tw_zero_left, smul_zero, zero_add]
      exact smul_comm _ _ _

theorem dL_inr_θ_mul (i j : I) (Y : TwSq K I dot v) :
    dL dot v i (inr dot v (θ j) * Y) =
      ((v ^ dot j i : Kˣ) : K) • (inr dot v (θ j) * dL dot v i Y) := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [mul_add, map_add, hY, hY', map_add, mul_add, smul_add]
  | single p s =>
    obtain ⟨c, e⟩ := p
    rw [inr_θ_mul_single, dL_single, dL_single, mul_smul_comm, tw, tw, ← mul_assoc,
      inr_θ_mul_inl j (wdot dot {j} (wt c) - dot j i)]
    · rw [smul_mul_assoc, mul_assoc, ← map_mul, ← word_of_mul, smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm (((v ^ dot j i : Kˣ) : K)), ← Units.val_mul, ← zpow_add, add_sub_cancel]
    · refine supp_mono ?_ (d_word_mem_supp i c)
      intro w hw
      simp only [Set.mem_setOf_eq] at hw ⊢
      rw [← hw, wdot_cons_right, wdot_singleton]
      ring

/-- The key identity `r ∘ d i = (d i ⊗ 1) ∘ r`. -/
theorem r_d (i : I) (y : PreF K I) :
    r dot v (d dot v i y) = dL dot v i (r dot v y) := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_word w c =>
    rw [map_smul, map_smul, map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one, d_one, map_zero, map_one, TwistedMonoidAlgebra.one_def, dL_single, Prod.fst_one,
        word_one, d_one, tw_zero_left, smul_zero]
    | mul_of j w ih =>
      rw [d_word_of_mul, r_word_of_mul, add_mul, map_add (dL dot v i), dL_inl_θ_mul,
        dL_inr_θ_mul, map_add (r dot v), map_smul, map_mul, r_θ, ← ih, add_mul, smul_add]
      split_ifs <;> simp [add_assoc]

/-! ### The counit on the first tensor factor -/

variable (dot v) in
/-- The map `ε ⊗ 1 : 'f ⊗ 'f → 'f`. -/
def E1 : TwSq K I dot v →ₗ[K] PreF K I :=
  TwistedMonoidAlgebra.lift fun p => if p.1 = 1 then word p.2 else 0

theorem E1_single (c e : FreeMonoid I) (s : K) :
    E1 dot v (single (c, e) s : TwSq K I dot v) = s • (if c = 1 then word e else 0) :=
  TwistedMonoidAlgebra.lift_single _ _ _

theorem E1_tw (x y : PreF K I) : E1 dot v (tw dot v x y) = counit x • y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [tw_add_left, map_add, hx, hx', map_add, add_smul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tw_add_right, map_add, hy, hy', smul_add]
    | smul_word w s =>
      rw [tw_smul_left, tw_smul_right, tw_word, map_smul, map_smul, E1_single, map_smul,
        counit_word, smul_comm s]
      split_ifs <;> simp

theorem of_mul_ne_one (j : I) (c : FreeMonoid I) : FreeMonoid.of j * c ≠ 1 := by
  intro h
  have := congrArg FreeMonoid.length h
  simp [FreeMonoid.length_mul] at this

theorem E1_gen_mul (j : I) (Y : TwSq K I dot v) :
    E1 dot v ((inl dot v (θ j) + inr dot v (θ j)) * Y) = θ j * E1 dot v Y := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [mul_add, map_add, hY, hY', map_add, mul_add]
  | single p s =>
    obtain ⟨c, e⟩ := p
    rw [add_mul, map_add, inl_θ_mul_single, inr_θ_mul_single, E1_single, E1_single,
      E1_single, if_neg (of_mul_ne_one j c), smul_zero, zero_add]
    by_cases hc : c = 1
    · subst hc
      simp [← word_of_mul, mul_smul_comm]
    · simp [hc]

theorem E1_r (y : PreF K I) : E1 dot v (r dot v y) = y := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul_word w c =>
    rw [map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one, map_one, TwistedMonoidAlgebra.one_def, E1_single, Prod.fst_one, Prod.snd_one,
        if_pos rfl, one_smul, word_one]
    | mul_of j w ih => rw [r_word_of_mul, E1_gen_mul, ih, word_of_mul]

end PreF

end Categorification.QuantumGroup

end
