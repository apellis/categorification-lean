/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaCross
import Categorification.Flag.GammaPoly

/-!
# Three strands: polynomials in the dots and the braid relations (KL III (6.20), (6.21))

KL III, arXiv:0807.3250v1, §6.2, Proposition 6.8, eqs. (6.20), (6.21) (TeX
`sln-2008-ArXiv.tex`), i.e. the relations (4.13) and (4.14) of Definition 4.1 for `Γ_N`.

## Generic part

For bimodules `L₁, L₂, L₃, X` (composable) with elements `ξ₁, ξ₂, ξ₃` (the dots of three
strands), the ring `L₁ ⊗ (L₂ ⊗ (L₃ ⊗ X))` receives the ring map `ev3 : k[x₀, x₁, x₂] → …`
(`xᵢ ↦ ξᵢ`, scalars through the left action) and `ι3 : X → …`.

* `span3` : if each `Lᵢ` is spanned by the powers of `ξᵢ` over its right ring (`SpannedBy`), the
  elements `ev3 p · ι3 x` span; `ext3` : bimodule maps agreeing on them agree.
* `locTwo_mul_suffix`, `whiskerLeft_mul_left` : whiskered two-strand maps commute with the other
  strands.
* `DotRules` : the nilHecke-type dot slides `φ ξ_L = τ + ξ'_R φ`, `φ ξ_R = ξ'_L φ − τ`;
  `DotRules.evalL`, `DotRules.evalR` : such a map, on strands `0, 1` resp. `1, 2`, acts on
  `ev3 p · y` by `(∂ p) τ(y) + (s p) φ(y)` (from `eval_twisted`).

## `Γ_N` on three upward strands

* `stepE_spanned` : `Γ(E_c)` is spanned by the powers of its dot over its right ring;
* `crossU_rules` : the dot slides of `crossU` as `DotRules`;
* `crossU_evalL`, `crossU_evalR` : `Γ_N` of the crossing of the strands `0, 1` (resp. `1, 2`) of a
  three-strand path with arbitrary suffix acts on `ev3 p · ι3 x` by the polynomial operators
  `op0`, `op1` of `Categorification.Flag.GammaPoly`;
* `braidL`, `braidR` : `Γ_N(ψ₀ψ₁ψ₀)` and `Γ_N(ψ₁ψ₀ψ₁)` on `E_c E_d E_e 1` (with explicit
  intermediate regions); `braidL_eval`, `braidR_eval`;
* `braid_three` : **the braid relation** `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on `E_c E_d E_e` unless `c = e ≠ d`
  (KL III (4.13), (6.20));
* `braidQ_three` : for `c ≠ d`, `ψ₀ψ₁ψ₀ − ψ₁ψ₀ψ₁ = Q̄_{cd}(ξ₀, ξ₁, ξ₂)` on `E_c E_d E_c`
  (KL III (4.14), (6.21)), with `Q_{cd} = Qf c d` (equal to the signed `Q^τ_{cd}`:
  `Categorification.KL3.Diagram.Signed.braidQ_signed`).

All intermediate regions are assumed to be valid compositions (the path model has no zero
1-morphisms); the degenerate cases, where an intermediate `Γ(E_p 1)` is zero, are not covered.
-/

noncomputable section

namespace Categorification.Flag

universe u

open MvPolynomial

/-! ### Generic lemmas on whiskering -/

section Generic

variable {A B C D E : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]

theorem BRing.assoc_hom_apply (M : BRing A B) (N : BRing B C) (P : BRing C D)
    (y : BRing.TT (M.tensor N) P) : (BRing.assoc M N P).hom y = BRing.assocHom M N P y := rfl

theorem BRing.assoc_inv_apply (M : BRing A B) (N : BRing B C) (P : BRing C D)
    (y : BRing.TT M (N.tensor P)) : (BRing.assoc M N P).inv y = BRing.assocInv M N P y := rfl

theorem whiskerRight_mul_suffix {M M' : BRing A B} (φ : BHom M M') (N : BRing B C)
    (y : (M.tensor N).T) (z : N.T) :
    BHom.whiskerRight φ N (y * BRing.tmul M N 1 z) =
      BHom.whiskerRight φ N y * BRing.tmul M' N 1 z := by
  refine BRing.induction_on (P := fun y => BHom.whiskerRight φ N (y * BRing.tmul M N 1 z) =
    BHom.whiskerRight φ N y * BRing.tmul M' N 1 z) y (by simp) (fun a b => ?_)
    (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BRing.tmul_mul_tmul, mul_one, BHom.whiskerRight_tmul, BHom.whiskerRight_tmul,
      BRing.tmul_mul_tmul, mul_one]
  · beta_reduce at hy hy' ⊢
    rw [add_mul, BHom.map_add, hy, hy', BHom.map_add, add_mul]

/-- A whiskered two-strand map commutes with multiplication by elements of the suffix. -/
theorem locTwo_mul_suffix {D' : Type u} [CommRing D'] {L : BRing A B} {L' : BRing B C}
    {R : BRing A D'} {R' : BRing D' C} (φ : BHom (L.tensor L') (R.tensor R')) (X : BRing C E)
    (y : (L.tensor (L'.tensor X)).T) (z : X.T) :
    locTwo φ X (y * BRing.tmul L (L'.tensor X) 1 (BRing.tmul L' X 1 z)) =
      locTwo φ X y * BRing.tmul R (R'.tensor X) 1 (BRing.tmul R' X 1 z) := by
  show BRing.assocHom R R' X (BHom.whiskerRight φ X (BRing.assocInv L L' X
      (y * BRing.tmul L (L'.tensor X) 1 (BRing.tmul L' X 1 z)))) =
    BRing.assocHom R R' X (BHom.whiskerRight φ X (BRing.assocInv L L' X y)) * _
  rw [map_mul, BRing.assocInv_tmul, ← BRing.one_eq, whiskerRight_mul_suffix, map_mul,
    BRing.one_eq (M := R) (N := R'), BRing.assocHom_tmul]

theorem locTwo_one {D' : Type u} [CommRing D'] {L : BRing A B} {L' : BRing B C}
    {R : BRing A D'} {R' : BRing D' C} (φ : BHom (L.tensor L') (R.tensor R')) (X : BRing C E) :
    locTwo φ X 1 = (BRing.assoc R R' X).hom (BRing.tmul _ X (φ 1) 1) := by
  show (BRing.assoc R R' X).hom (BHom.whiskerRight φ X ((BRing.assoc L L' X).inv 1)) = _
  rw [BRing.assoc_inv_apply, map_one, BRing.one_eq, BHom.whiskerRight_tmul]

/-- Left whiskering commutes with multiplication by elements of the left strand. -/
theorem whiskerLeft_mul_left (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N')
    (y : (M.tensor N).T) (m : M.T) :
    BHom.whiskerLeft M ψ (BRing.tmul M N m 1 * y) = BRing.tmul M N' m 1 * BHom.whiskerLeft M ψ y := by
  refine BRing.induction_on (P := fun y => BHom.whiskerLeft M ψ (BRing.tmul M N m 1 * y) =
    BRing.tmul M N' m 1 * BHom.whiskerLeft M ψ y) y (by simp) (fun a b => ?_)
    (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BRing.tmul_mul_tmul, one_mul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
      BRing.tmul_mul_tmul, one_mul]
  · beta_reduce at hy hy' ⊢
    rw [mul_add, BHom.map_add, hy, hy', BHom.map_add, mul_add]

/-- Left whiskering transports a multiplication rule of the inner map. -/
theorem whiskerLeft_mul_right (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') (w : N.T)
    (w' : N'.T) (hψ : ∀ z, ψ (w * z) = w' * ψ z) (y : (M.tensor N).T) :
    BHom.whiskerLeft M ψ (BRing.tmul M N 1 w * y) = BRing.tmul M N' 1 w' * BHom.whiskerLeft M ψ y := by
  refine BRing.induction_on (P := fun y => BHom.whiskerLeft M ψ (BRing.tmul M N 1 w * y) =
    BRing.tmul M N' 1 w' * BHom.whiskerLeft M ψ y) y (by simp) (fun a b => ?_)
    (fun y y' hy hy' => ?_)
  · beta_reduce
    rw [BRing.tmul_mul_tmul, one_mul, BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul,
      BRing.tmul_mul_tmul, one_mul, hψ]
  · beta_reduce at hy hy' ⊢
    rw [mul_add, BHom.map_add, hy, hy', BHom.map_add, mul_add]

theorem whiskerLeft_one' (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') :
    BHom.whiskerLeft M ψ 1 = BRing.tmul M N' 1 (ψ 1) := by
  rw [BRing.one_eq, BHom.whiskerLeft_tmul]

/-- From an equation of bimodule maps to its values. -/
theorem BHom.congr_apply {M N : BRing A B} {φ ψ : BHom M N} (h : φ = ψ) (y : M.T) :
    φ y = ψ y := by rw [h]

end Generic

/-! ### Three strands: evaluation and spanning -/

section Three

variable {K : Type u} [CommRing K]
variable {A B C D E : Type u} [CommRing A] [Algebra K A] [CommRing B] [CommRing C] [CommRing D]
  [CommRing E]

/-- The three-strand ring `L₁ ⊗ (L₂ ⊗ (L₃ ⊗ X))`. -/
abbrev R3 (L₁ : BRing A B) (L₂ : BRing B C) (L₃ : BRing C D) (X : BRing D E) : BRing A E :=
  L₁.tensor (L₂.tensor (L₃.tensor X))

variable (K) in
/-- **The polynomials in the three dots**: `x₀ ↦ ξ₁ ⊗ 1`, `x₁ ↦ 1 ⊗ ξ₂ ⊗ 1`,
`x₂ ↦ 1 ⊗ 1 ⊗ ξ₃ ⊗ 1`, scalars through the left action. -/
def ev3 (L₁ : BRing A B) (L₂ : BRing B C) (L₃ : BRing C D) (X : BRing D E) (ξ₁ : L₁.T)
    (ξ₂ : L₂.T) (ξ₃ : L₃.T) : MvPolynomial (Fin 3) K →+* (R3 L₁ L₂ L₃ X).T :=
  eval₂Hom ((R3 L₁ L₂ L₃ X).left.comp (algebraMap K A))
    ![BRing.tmul _ _ ξ₁ 1, BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₂ 1),
      BRing.tmul _ _ 1 (BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₃ 1))]

/-- The suffix `X` inside the three-strand ring. -/
def iota3 (L₁ : BRing A B) (L₂ : BRing B C) (L₃ : BRing C D) (X : BRing D E) :
    X.T →+* (R3 L₁ L₂ L₃ X).T :=
  (BRing.inclR L₁ _).comp ((BRing.inclR L₂ _).comp (BRing.inclR L₃ X))

variable (L₁ : BRing A B) (L₂ : BRing B C) (L₃ : BRing C D) (X : BRing D E) (ξ₁ : L₁.T)
  (ξ₂ : L₂.T) (ξ₃ : L₃.T)

theorem iota3_apply (x : X.T) :
    iota3 L₁ L₂ L₃ X x = BRing.tmul _ _ 1 (BRing.tmul _ _ 1 (BRing.tmul _ _ 1 x)) := rfl

theorem ev3_C (c : K) : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.C c) =
    (R3 L₁ L₂ L₃ X).left (algebraMap K A c) := eval₂Hom_C _ _ c

theorem ev3_X0 : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 0) = BRing.tmul _ _ ξ₁ 1 := eval₂Hom_X' _ _ 0
theorem ev3_X1 : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 1) = BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₂ 1) :=
  eval₂Hom_X' _ _ 1
theorem ev3_X2 : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 2) =
    BRing.tmul _ _ 1 (BRing.tmul _ _ 1 (BRing.tmul _ _ ξ₃ 1)) := eval₂Hom_X' _ _ 2

/-- A bimodule is *spanned by the powers of `ξ` over its right ring*. -/
def SpannedBy {P Q : Type u} [CommRing P] [CommRing Q] (L : BRing P Q) (ξ : L.T) : Prop :=
  ∀ m : L.T, ∃ (n : ℕ) (c : Fin n → Q), m = ∑ a : Fin n, L.right (c a) * ξ ^ (a : ℕ)

theorem span_level {P Q R Z : Type u} [CommRing P] [CommRing Q] [CommRing R] [CommRing Z]
    (M : BRing P Q) (N : BRing Q R) (ξ : M.T) (hspan : SpannedBy M ξ) (f : BRing.TT M N →+* Z)
    (S : AddSubgroup Z) (hS : ∀ z ∈ S, f (BRing.tmul M N ξ 1) * z ∈ S)
    (hbase : ∀ n, f (BRing.tmul M N 1 n) ∈ S) (t : BRing.TT M N) : f t ∈ S := by
  have hpow : ∀ (a : ℕ) (z), z ∈ S → f (BRing.tmul M N ξ 1) ^ a * z ∈ S := by
    intro a
    induction a with
    | zero => intro z hz; simpa using hz
    | succ a ih => intro z hz; rw [pow_succ', mul_assoc]; exact hS _ (ih z hz)
  refine BRing.induction_on (P := fun t => f t ∈ S) t (by beta_reduce; rw [map_zero]; exact S.zero_mem)
    (fun m n => ?_)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact S.add_mem hx hy)
  beta_reduce
  obtain ⟨k, c, rfl⟩ := hspan m
  rw [BRing.sum_tmul, map_sum]
  refine S.sum_mem fun a _ => ?_
  rw [BRing.tmul_balance,
    show BRing.tmul M N (ξ ^ (a : ℕ)) (N.left (c a) * n) =
      BRing.tmul M N ξ 1 ^ (a : ℕ) * BRing.tmul M N 1 (N.left (c a) * n) by
      rw [BRing.tmul_pow, one_pow, BRing.tmul_mul_tmul, mul_one, one_mul], map_mul, map_pow]
  exact hpow a _ (hbase _)

variable (K) in
/-- The additive span of the elements `ev3 p · ι3 x`. -/
def gen3 : AddSubgroup (R3 L₁ L₂ L₃ X).T :=
  AddSubgroup.closure {z | ∃ p x, z = ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ p * iota3 L₁ L₂ L₃ X x}

theorem gen3_mul (q : MvPolynomial (Fin 3) K) (z : (R3 L₁ L₂ L₃ X).T)
    (hz : z ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃) :
    ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ q * z ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨p, x, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨q * p, x, by rw [map_mul, mul_assoc]⟩
  | one => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | mul z z' _ _ h h' => rw [mul_add]; exact AddSubgroup.add_mem _ h h'
  | inv z _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h

/-- **Spanning**: if every strand is spanned by the powers of its dot over its right ring, the
elements `ev3 p · ι3 x` span the three-strand ring. -/
theorem span3 (h₁ : SpannedBy L₁ ξ₁) (h₂ : SpannedBy L₂ ξ₂) (h₃ : SpannedBy L₃ ξ₃)
    (t : (R3 L₁ L₂ L₃ X).T) : t ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ := by
  have hmul : ∀ (i : Fin 3) (z), z ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ →
      ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X i) * z ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ :=
    fun i z hz => gen3_mul L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ _ z hz
  have base3 : ∀ x, iota3 L₁ L₂ L₃ X x ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ := fun x =>
    AddSubgroup.subset_closure ⟨1, x, by rw [map_one, one_mul]⟩
  have lev3 : ∀ v, (BRing.inclR L₁ _).comp (BRing.inclR L₂ _) v ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ :=
    span_level L₃ X ξ₃ h₃ _ _ (fun z hz => by
      have := hmul 2 z hz; rwa [ev3_X2] at this) (fun x => base3 x)
  have lev2 : ∀ w, BRing.inclR L₁ _ w ∈ gen3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ :=
    span_level L₂ (L₃.tensor X) ξ₂ h₂ _ _ (fun z hz => by
      have := hmul 1 z hz; rwa [ev3_X1] at this) (fun v => lev3 v)
  exact span_level L₁ (L₂.tensor (L₃.tensor X)) ξ₁ h₁ (RingHom.id _) _ (fun z hz => by
    have := hmul 0 z hz; rwa [ev3_X0] at this) (fun w => lev2 w) t

/-- **Bimodule maps out of the three-strand ring are determined by their values on
`ev3 p · ι3 x`.** -/
theorem ext3 (h₁ : SpannedBy L₁ ξ₁) (h₂ : SpannedBy L₂ ξ₂) (h₃ : SpannedBy L₃ ξ₃)
    {N : BRing A E} (F G : BHom (R3 L₁ L₂ L₃ X) N)
    (h : ∀ p x, F (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ p * iota3 L₁ L₂ L₃ X x) =
      G (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ p * iota3 L₁ L₂ L₃ X x)) : F = G := by
  refine BHom.ext fun t => ?_
  have ht := span3 (K := K) L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ h₁ h₂ h₃ t
  induction ht using AddSubgroup.closure_induction with
  | mem z hz => obtain ⟨p, x, rfl⟩ := hz; exact h p x
  | one => rw [BHom.map_zero, BHom.map_zero]
  | mul z z' _ _ hz hz' => rw [BHom.map_add, BHom.map_add, hz, hz']
  | inv z _ hz => rw [BHom.map_neg, BHom.map_neg, hz]

theorem assoc_hom_one {C' D' : Type u} [CommRing C'] [CommRing D'] (M : BRing A B)
    (N : BRing B C') (P : BRing C' D') :
    (BRing.assoc M N P).hom (BRing.tmul (M.tensor N) P 1 1) = 1 :=
  map_one (BRing.assocHom M N P)

/-- `ev3 (x₁ − x₀)` through the associator. -/
theorem ev3_at01_sub : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (at01 (MvPolynomial.X 1 - MvPolynomial.X 0)) =
    (BRing.assoc L₁ L₂ (L₃.tensor X)).hom
      (BRing.tmul _ _ (BRing.tmul L₁ L₂ 1 ξ₂ - BRing.tmul L₁ L₂ ξ₁ 1) 1) := by
  rw [BRing.sub_tmul, BHom.map_sub, BRing.assoc_hom_tmul, BRing.assoc_hom_tmul, at01, map_sub,
    rename_X, rename_X]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  rw [map_sub, ev3_X1, ev3_X0]
  rfl

/-- `ev3 (x₂ − x₁)` through the associator. -/
theorem ev3_at12_sub : ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (at12 (MvPolynomial.X 1 - MvPolynomial.X 0)) =
    BRing.tmul _ _ 1 ((BRing.assoc L₂ L₃ X).hom
      (BRing.tmul _ _ (BRing.tmul L₂ L₃ 1 ξ₃ - BRing.tmul L₂ L₃ ξ₂ 1) 1)) := by
  rw [BRing.sub_tmul, BHom.map_sub, BRing.assoc_hom_tmul, BRing.assoc_hom_tmul, at12, map_sub,
    rename_X, rename_X]
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
  rw [map_sub, ev3_X2, ev3_X1, BRing.tmul_sub]
  rfl

/-- A whiskered two-strand map on `ι3 x` (strands `0, 1`). -/
theorem locTwo_iota3 {B' : Type u} [CommRing B'] {L₁' : BRing A B'} {L₂' : BRing B' C}
    (F : BHom (L₁.tensor L₂) (L₁'.tensor L₂')) (x : X.T) :
    locTwo F (L₃.tensor X) (iota3 L₁ L₂ L₃ X x) =
      (BRing.assoc L₁' L₂' (L₃.tensor X)).hom (BRing.tmul _ _ (F 1) 1) * iota3 L₁' L₂' L₃ X x := by
  rw [iota3_apply, iota3_apply, ← one_mul (BRing.tmul L₁ (L₂.tensor (L₃.tensor X)) 1 _),
    locTwo_mul_suffix, locTwo_one]

/-- A whiskered two-strand map on `ι3 x` (strands `1, 2`). -/
theorem whiskerLeft_locTwo_iota3 {C' : Type u} [CommRing C'] {L₂' : BRing B C'}
    {L₃' : BRing C' D} (F : BHom (L₂.tensor L₃) (L₂'.tensor L₃')) (x : X.T) :
    BHom.whiskerLeft L₁ (locTwo F X) (iota3 L₁ L₂ L₃ X x) =
      BRing.tmul _ _ 1 ((BRing.assoc L₂' L₃' X).hom (BRing.tmul _ _ (F 1) 1)) *
        iota3 L₁ L₂' L₃' X x := by
  rw [iota3_apply, iota3_apply, BHom.whiskerLeft_tmul,
    ← one_mul (BRing.tmul L₂ (L₃.tensor X) 1 _), locTwo_mul_suffix, locTwo_one,
    BRing.tmul_mul_tmul, one_mul]

end Three

/-! ### Two-strand maps with nilHecke-type dot slides, on three strands -/

section Rules

variable {A B B' C : Type u} [CommRing A] [CommRing B] [CommRing B'] [CommRing C]
  {L₁ : BRing A B} {L₂ : BRing B C} {L₁' : BRing A B'} {L₂' : BRing B' C}

/-- **Dot slides of a two-strand map** `φ : L₁ ⊗ L₂ → L₁' ⊗ L₂'` with correction `τ`:
`φ ξ_L = τ + ξ'_R φ`, `φ ξ_R = ξ'_L φ − τ`, and `τ` intertwines `ξ_L, ξ_R` with `ξ'_L, ξ'_R`
(KL III (4.12), (4.8)–(4.10) for `Γ_N`, `Categorification.Flag.crossU_xiL` etc.). -/
structure DotRules (φ τ : BHom (L₁.tensor L₂) (L₁'.tensor L₂')) (ξ₁ : L₁.T) (ξ₂ : L₂.T)
    (ξ₁' : L₁'.T) (ξ₂' : L₂'.T) : Prop where
  φL : φ.comp (BHom.mulB (BRing.tmul L₁ L₂ ξ₁ 1)) =
    τ + (BHom.mulB (BRing.tmul L₁' L₂' 1 ξ₂')).comp φ
  φR : φ.comp (BHom.mulB (BRing.tmul L₁ L₂ 1 ξ₂)) =
    (BHom.mulB (BRing.tmul L₁' L₂' ξ₁' 1)).comp φ - τ
  τL : τ.comp (BHom.mulB (BRing.tmul L₁ L₂ ξ₁ 1)) = (BHom.mulB (BRing.tmul L₁' L₂' ξ₁' 1)).comp τ
  τR : τ.comp (BHom.mulB (BRing.tmul L₁ L₂ 1 ξ₂)) = (BHom.mulB (BRing.tmul L₁' L₂' 1 ξ₂')).comp τ

variable {φ τ : BHom (L₁.tensor L₂) (L₁'.tensor L₂')} {ξ₁ : L₁.T} {ξ₂ : L₂.T} {ξ₁' : L₁'.T}
  {ξ₂' : L₂'.T}

namespace DotRules

variable (hr : DotRules φ τ ξ₁ ξ₂ ξ₁' ξ₂') {E : Type u} [CommRing E] (Y : BRing C E)
include hr

theorem locL : (locTwo φ Y).comp (BHom.mulB (BRing.tmul L₁ (L₂.tensor Y) ξ₁ 1)) =
    locTwo τ Y + (BHom.mulB (BRing.tmul L₁' (L₂'.tensor Y) 1 (BRing.tmul L₂' Y ξ₂' 1))).comp
      (locTwo φ Y) := by
  have := congrArg (fun F => locTwo F Y) hr.φL
  simp only [locTwo_comp, locTwo_add, locTwo_mulB] at this
  exact this

theorem locR : (locTwo φ Y).comp (BHom.mulB (BRing.tmul L₁ (L₂.tensor Y) 1 (BRing.tmul L₂ Y ξ₂ 1))) =
    (BHom.mulB (BRing.tmul L₁' (L₂'.tensor Y) ξ₁' 1)).comp (locTwo φ Y) - locTwo τ Y := by
  have := congrArg (fun F => locTwo F Y) hr.φR
  simp only [locTwo_comp, locTwo_sub, locTwo_mulB] at this
  exact this

theorem locτL : (locTwo τ Y).comp (BHom.mulB (BRing.tmul L₁ (L₂.tensor Y) ξ₁ 1)) =
    (BHom.mulB (BRing.tmul L₁' (L₂'.tensor Y) ξ₁' 1)).comp (locTwo τ Y) := by
  have := congrArg (fun F => locTwo F Y) hr.τL
  simp only [locTwo_comp, locTwo_mulB] at this
  exact this

theorem locτR : (locTwo τ Y).comp (BHom.mulB (BRing.tmul L₁ (L₂.tensor Y) 1 (BRing.tmul L₂ Y ξ₂ 1))) =
    (BHom.mulB (BRing.tmul L₁' (L₂'.tensor Y) 1 (BRing.tmul L₂' Y ξ₂' 1))).comp (locTwo τ Y) := by
  have := congrArg (fun F => locTwo F Y) hr.τR
  simp only [locTwo_comp, locTwo_mulB] at this
  exact this

end DotRules

end Rules

section Eval

variable {K : Type u} [CommRing K]
variable {A B B' C C' D E : Type u} [CommRing A] [Algebra K A] [CommRing B] [CommRing B']
  [CommRing C] [CommRing C'] [CommRing D] [CommRing E]

/-- **A crossing of the strands `0, 1` on polynomials in the dots**:
`φ(p · y) = (∂₀ p) τ(y) + (s₀ p) φ(y)`. -/
theorem DotRules.evalL {L₁ : BRing A B} {L₂ : BRing B C} {L₁' : BRing A B'} {L₂' : BRing B' C}
    {φ τ : BHom (L₁.tensor L₂) (L₁'.tensor L₂')} {ξ₁ : L₁.T} {ξ₂ : L₂.T} {ξ₁' : L₁'.T}
    {ξ₂' : L₂'.T} (hr : DotRules φ τ ξ₁ ξ₂ ξ₁' ξ₂') (L₃ : BRing C D) (X : BRing D E) (ξ₃ : L₃.T)
    (q : MvPolynomial (Fin 3) K) (y : (R3 L₁ L₂ L₃ X).T) :
    locTwo φ (L₃.tensor X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ q * y) =
      ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃ (dd0 q) * locTwo τ (L₃.tensor X) y +
        ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃ (sw0 q) * locTwo φ (L₃.tensor X) y := by
  have suff : ∀ (F : BHom (L₁.tensor L₂) (L₁'.tensor L₂')) (y : (R3 L₁ L₂ L₃ X).T),
      locTwo F (L₃.tensor X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 2) * y) =
        ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃ (MvPolynomial.X 2) * locTwo F (L₃.tensor X) y := by
    intro F y
    rw [ev3_X2, ev3_X2, mul_comm, locTwo_mul_suffix, mul_comm]
  have h0 : ∀ y, locTwo τ (L₃.tensor X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 0) * y) =
      ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃ (MvPolynomial.X 0) * locTwo τ (L₃.tensor X) y := fun y => by
    rw [ev3_X0, ev3_X0]; exact BHom.congr_apply (hr.locτL (L₃.tensor X)) y
  have h1 : ∀ y, locTwo τ (L₃.tensor X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 1) * y) =
      ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃ (MvPolynomial.X 1) * locTwo τ (L₃.tensor X) y := fun y => by
    rw [ev3_X1, ev3_X1]; exact BHom.congr_apply (hr.locτR (L₃.tensor X)) y
  refine eval_twisted (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃) (ev3 K L₁' L₂' L₃ X ξ₁' ξ₂' ξ₃)
    (locTwo φ (L₃.tensor X)) (locTwo τ (L₃.tensor X)) 0 1 (by decide) (BHom.map_add _)
    (fun i y => ?_) (fun c y => ?_) (fun y => ?_) (fun y => ?_) (fun i hi0 hi1 y => ?_) q y
  · fin_cases i
    · exact h0 y
    · exact h1 y
    · exact suff τ y
  · rw [ev3_C, ev3_C]; exact BHom.map_left _ _ _
  · rw [ev3_X0, ev3_X1]; exact BHom.congr_apply (hr.locL (L₃.tensor X)) y
  · rw [ev3_X1, ev3_X0]; exact BHom.congr_apply (hr.locR (L₃.tensor X)) y
  · fin_cases i
    · exact absurd rfl hi0
    · exact absurd rfl hi1
    · exact suff φ y

/-- **A crossing of the strands `1, 2` on polynomials in the dots**:
`φ(p · y) = (∂₁ p) τ(y) + (s₁ p) φ(y)`. -/
theorem DotRules.evalR {L₁ : BRing A B} {L₂ : BRing B C} {L₃ : BRing C D} {L₂' : BRing B C'}
    {L₃' : BRing C' D} {φ τ : BHom (L₂.tensor L₃) (L₂'.tensor L₃')} {ξ₂ : L₂.T} {ξ₃ : L₃.T}
    {ξ₂' : L₂'.T} {ξ₃' : L₃'.T} (hr : DotRules φ τ ξ₂ ξ₃ ξ₂' ξ₃') (X : BRing D E) (ξ₁ : L₁.T)
    (q : MvPolynomial (Fin 3) K) (y : (R3 L₁ L₂ L₃ X).T) :
    BHom.whiskerLeft L₁ (locTwo φ X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ q * y) =
      ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃' (dd1 q) * BHom.whiskerLeft L₁ (locTwo τ X) y +
        ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃' (sw1 q) * BHom.whiskerLeft L₁ (locTwo φ X) y := by
  have wl : ∀ {F G H : BHom (L₂.tensor (L₃.tensor X)) (L₂'.tensor (L₃'.tensor X))}
      {w : (L₂.tensor (L₃.tensor X)).T} {w' : (L₂'.tensor (L₃'.tensor X)).T},
      F.comp (BHom.mulB w) = G + (BHom.mulB w').comp H → ∀ y,
      BHom.whiskerLeft L₁ F (BRing.tmul _ _ 1 w * y) =
        BHom.whiskerLeft L₁ G y + BRing.tmul _ _ 1 w' * BHom.whiskerLeft L₁ H y := by
    intro F G H w w' h y
    have := congrArg (BHom.whiskerLeft L₁) h
    rw [BHom.whiskerLeft_comp, BHom.whiskerLeft_add, BHom.whiskerLeft_comp, BHom.whiskerLeft_mulB,
      BHom.whiskerLeft_mulB] at this
    exact BHom.congr_apply this y
  have wl' : ∀ {F G : BHom (L₂.tensor (L₃.tensor X)) (L₂'.tensor (L₃'.tensor X))}
      {w : (L₂.tensor (L₃.tensor X)).T} {w' : (L₂'.tensor (L₃'.tensor X)).T},
      F.comp (BHom.mulB w) = (BHom.mulB w').comp G → ∀ y,
      BHom.whiskerLeft L₁ F (BRing.tmul _ _ 1 w * y) =
        BRing.tmul _ _ 1 w' * BHom.whiskerLeft L₁ G y := by
    intro F G w w' h y
    have := congrArg (BHom.whiskerLeft L₁) h
    rw [BHom.whiskerLeft_comp, BHom.whiskerLeft_comp, BHom.whiskerLeft_mulB,
      BHom.whiskerLeft_mulB] at this
    exact BHom.congr_apply this y
  have hφR : ∀ y, BHom.whiskerLeft L₁ (locTwo φ X)
      (BRing.tmul _ _ 1 (BRing.tmul L₂ (L₃.tensor X) 1 (BRing.tmul L₃ X ξ₃ 1)) * y) =
      BRing.tmul _ _ 1 (BRing.tmul L₂' (L₃'.tensor X) ξ₂' 1) *
        BHom.whiskerLeft L₁ (locTwo φ X) y - BHom.whiskerLeft L₁ (locTwo τ X) y := by
    intro y
    have h := hr.locR X
    rw [sub_eq_add_neg, ← BHom.neg_apply]
    rw [show (BHom.mulB (BRing.tmul L₂' (L₃'.tensor X) ξ₂' 1)).comp (locTwo φ X) - locTwo τ X =
      -locTwo τ X + (BHom.mulB (BRing.tmul L₂' (L₃'.tensor X) ξ₂' 1)).comp (locTwo φ X) by
        ext z; simp only [BHom.sub_apply, BHom.add_apply, BHom.neg_apply]; abel] at h
    rw [wl h y, BHom.whiskerLeft_neg, add_comm]
  have g0 : ∀ (F : BHom (L₂.tensor (L₃.tensor X)) (L₂'.tensor (L₃'.tensor X))) y,
      BHom.whiskerLeft L₁ F (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 0) * y) =
        ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃' (MvPolynomial.X 0) * BHom.whiskerLeft L₁ F y := by
    intro F y; rw [ev3_X0, ev3_X0]; exact whiskerLeft_mul_left _ _ _ _
  have t1 : ∀ y, BHom.whiskerLeft L₁ (locTwo τ X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 1) * y) =
      ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃' (MvPolynomial.X 1) * BHom.whiskerLeft L₁ (locTwo τ X) y := by
    intro y; rw [ev3_X1, ev3_X1]; exact wl' (hr.locτL X) y
  have t2 : ∀ y, BHom.whiskerLeft L₁ (locTwo τ X) (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃ (MvPolynomial.X 2) * y) =
      ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃' (MvPolynomial.X 2) * BHom.whiskerLeft L₁ (locTwo τ X) y := by
    intro y; rw [ev3_X2, ev3_X2]; exact wl' (hr.locτR X) y
  refine eval_twisted (ev3 K L₁ L₂ L₃ X ξ₁ ξ₂ ξ₃) (ev3 K L₁ L₂' L₃' X ξ₁ ξ₂' ξ₃')
    (BHom.whiskerLeft L₁ (locTwo φ X)) (BHom.whiskerLeft L₁ (locTwo τ X)) 1 2 (by decide)
    (BHom.map_add _) (fun i y => ?_) (fun c y => ?_) (fun y => ?_) (fun y => ?_)
    (fun i hi0 hi1 y => ?_) q y
  · fin_cases i
    · exact g0 _ y
    · exact t1 y
    · exact t2 y
  · rw [ev3_C, ev3_C]; exact BHom.map_left _ _ _
  · rw [ev3_X1, ev3_X2]; exact wl (hr.locL X) y
  · rw [ev3_X2, ev3_X1]; exact hφR y
  · fin_cases i
    · exact g0 _ y
    · exact absurd rfl hi0
    · exact absurd rfl hi1

end Eval

/-! ### `Γ_N` on three upward strands -/

section GammaN

variable {K : Type u} [Field K] {m : ℕ}

/-- `Γ(E_c 1_r)` is spanned by the powers of its dot over `H_r` (KL III §5.1.1, `eBasisRight`). -/
theorem stepE_spanned (c : Fin m) {r s : Comp m} (h : StepR (true, c) r s) :
    SpannedBy (stepB K (true, c) r s h) (eXi K c r h.2) := by
  intro x
  letI := eRightAlgebra K c r h.2
  refine ⟨_, fun a => (eBasisRight K c r h.2).repr x a, ?_⟩
  conv_lhs => rw [← (eBasisRight K c r h.2).sum_repr x]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Algebra.smul_def, eBasisRight_apply]
  rfl

section Rules

variable (c d : Fin m) {t r₁ r₂ r₁' : Comp m} (h₁ : StepR (true, c) r₁ t)
  (h₂ : StepR (true, d) r₂ r₁) (h₁' : StepR (true, d) r₁' t) (h₂' : StepR (true, c) r₂ r₁')

/-- The dot slides of the uniform crossing `crossU` in the form `DotRules`. -/
theorem crossU_rules : DotRules (crossU K c d h₁ h₂ h₁' h₂') (tauU K c d h₁ h₂ h₁' h₂')
    (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K d r₁' h₁'.2) (eXi K c r₂ h₂'.2) :=
  ⟨crossU_xiL c d h₁ h₂ h₁' h₂', crossU_xiR c d h₁ h₂ h₁' h₂', tauU_xiL c d h₁ h₂ h₁' h₂',
    tauU_xiR c d h₁ h₂ h₁' h₂'⟩

variable {D E : Type u} [CommRing D] [CommRing E]

/-- **`Γ_N` of the crossing of the strands `0, 1`** of a three-strand path acts on polynomials
in the dots by `op0 c d` (divided difference if `c = d`, `F_{cd}(x₀, x₁) · s₀` otherwise). -/
theorem crossU_evalL (L₃ : BRing (H K r₂) D) (X : BRing D E) (ξ₃ : L₃.T)
    (p : MvPolynomial (Fin 3) K) (x : X.T) :
    locTwo (crossU K c d h₁ h₂ h₁' h₂') (L₃.tensor X)
        (ev3 K (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) L₃ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) ξ₃ p *
          iota3 _ _ L₃ X x) =
      ev3 K (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') L₃ X (eXi K d r₁' h₁'.2) (eXi K c r₂ h₂'.2) ξ₃
          (op0 c d p) * iota3 _ _ L₃ X x := by
  rw [(crossU_rules c d h₁ h₂ h₁' h₂').evalL L₃ X ξ₃ p, locTwo_iota3, locTwo_iota3, tauU_one,
    crossU_one]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos hcd, op0, if_pos hcd, BRing.zero_tmul, BHom.map_zero, zero_mul,
      mul_zero, add_zero, assoc_hom_one, one_mul]
  · have hF : ev3 K (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') L₃ X (eXi K d r₁' h₁'.2)
        (eXi K c r₂ h₂'.2) ξ₃ (at01 (Fc K c d)) = (BRing.assoc _ _ _).hom (BRing.tmul _ _
          (if c.castSucc = d.succ then BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2) -
            BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1 else 1) 1) := by
      by_cases hadj : c.castSucc = d.succ
      · rw [if_pos hadj, Fc, if_pos hadj, ev3_at01_sub]
      · rw [if_neg hadj, Fc, if_neg hadj, at01, map_one, map_one]
        exact (map_one (BRing.assocHom _ _ _)).symm
    rw [if_neg hcd, if_neg hcd, op0, if_neg hcd, BRing.zero_tmul, BHom.map_zero, zero_mul,
      mul_zero, zero_add, mS0, map_mul, hF]
    exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

/-- **`Γ_N` of the crossing of the strands `1, 2`** of a three-strand path acts on polynomials
in the dots by `op1 c d`. -/
theorem crossU_evalR {A : Type u} [CommRing A] [Algebra K A] (L₁ : BRing A (H K t)) (ξ₁ : L₁.T)
    (X : BRing (H K r₂) E) (p : MvPolynomial (Fin 3) K) (x : X.T) :
    BHom.whiskerLeft L₁ (locTwo (crossU K c d h₁ h₂ h₁' h₂') X)
        (ev3 K L₁ (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) X ξ₁ (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) p *
          iota3 L₁ _ _ X x) =
      ev3 K L₁ (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') X ξ₁ (eXi K d r₁' h₁'.2) (eXi K c r₂ h₂'.2)
          (op1 c d p) * iota3 L₁ _ _ X x := by
  rw [(crossU_rules c d h₁ h₂ h₁' h₂').evalR X ξ₁ p, whiskerLeft_locTwo_iota3,
    whiskerLeft_locTwo_iota3, tauU_one, crossU_one]
  by_cases hcd : c = d
  · rw [if_pos hcd, if_pos hcd, op1, if_pos hcd, BRing.zero_tmul, BHom.map_zero, BRing.tmul_zero,
      zero_mul, mul_zero, add_zero, assoc_hom_one, ← BRing.one_eq, one_mul]
  · have hF : ev3 K L₁ (stepB K _ _ _ h₁') (stepB K _ _ _ h₂') X ξ₁ (eXi K d r₁' h₁'.2)
        (eXi K c r₂ h₂'.2) (at12 (Fc K c d)) = BRing.tmul _ _ 1 ((BRing.assoc _ _ _).hom
          (BRing.tmul _ _ (if c.castSucc = d.succ then BRing.tmul _ _ 1 (eXi K c r₂ h₂'.2) -
            BRing.tmul _ _ (eXi K d r₁' h₁'.2) 1 else 1) 1)) := by
      by_cases hadj : c.castSucc = d.succ
      · rw [if_pos hadj, Fc, if_pos hadj, ev3_at12_sub]
      · rw [if_neg hadj, Fc, if_neg hadj, at12, map_one, map_one]
        exact (congrArg (BRing.tmul _ _ 1) (assoc_hom_one _ _ _)).symm
    rw [if_neg hcd, if_neg hcd, op1, if_neg hcd, BRing.zero_tmul, BHom.map_zero, BRing.tmul_zero,
      zero_mul, mul_zero, zero_add, mS1, map_mul, hF]
    exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end Rules

section Braid

variable (K) in
/-- `Γ_N(ψ₀ ψ₁ ψ₀)` on `E_c E_d E_e 1_{r₃}` (followed by the suffix `X`), through the intermediate
paths `E_d E_c E_e` (middle region `a₁`) and `E_d E_e E_c` (regions `a₁`, `f₂`), ending at
`E_e E_d E_c` (regions `f₁`, `f₂`). -/
def braidL (c d e : Fin m) {s r₁ r₂ r₃ a₁ f₁ f₂ : Comp m} {E : Type u} [CommRing E]
    (h₁ : StepR (true, c) r₁ s) (h₂ : StepR (true, d) r₂ r₁) (h₃ : StepR (true, e) r₃ r₂)
    (ha₁ : StepR (true, d) a₁ s) (ha₂ : StepR (true, c) r₂ a₁) (hf₂ : StepR (true, e) f₂ a₁)
    (hf₁ : StepR (true, e) f₁ s) (hd₂ : StepR (true, d) f₂ f₁) (hc₃ : StepR (true, c) r₃ f₂)
    (X : BRing (H K r₃) E) :
    BHom (R3 (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) (stepB K _ _ _ h₃) X)
      (R3 (stepB K _ _ _ hf₁) (stepB K _ _ _ hd₂) (stepB K _ _ _ hc₃) X) :=
  (locTwo (crossU K d e ha₁ hf₂ hf₁ hd₂) ((stepB K _ _ _ hc₃).tensor X)).comp
    ((BHom.whiskerLeft (stepB K _ _ _ ha₁) (locTwo (crossU K c e ha₂ h₃ hf₂ hc₃) X)).comp
      (locTwo (crossU K c d h₁ h₂ ha₁ ha₂) ((stepB K _ _ _ h₃).tensor X)))

variable (K) in
/-- `Γ_N(ψ₁ ψ₀ ψ₁)` on `E_c E_d E_e 1_{r₃}`, through `E_c E_e E_d` (middle region `b₂`) and
`E_e E_c E_d` (regions `f₁`, `b₂`), ending at `E_e E_d E_c` (regions `f₁`, `f₂`). -/
def braidR (c d e : Fin m) {s r₁ r₂ r₃ b₂ f₁ f₂ : Comp m} {E : Type u} [CommRing E]
    (h₁ : StepR (true, c) r₁ s) (h₂ : StepR (true, d) r₂ r₁) (h₃ : StepR (true, e) r₃ r₂)
    (hb₂ : StepR (true, e) b₂ r₁) (hb₃ : StepR (true, d) r₃ b₂) (hb₁ : StepR (true, c) b₂ f₁)
    (hf₁ : StepR (true, e) f₁ s) (hd₂ : StepR (true, d) f₂ f₁) (hc₃ : StepR (true, c) r₃ f₂)
    (X : BRing (H K r₃) E) :
    BHom (R3 (stepB K _ _ _ h₁) (stepB K _ _ _ h₂) (stepB K _ _ _ h₃) X)
      (R3 (stepB K _ _ _ hf₁) (stepB K _ _ _ hd₂) (stepB K _ _ _ hc₃) X) :=
  (BHom.whiskerLeft (stepB K _ _ _ hf₁) (locTwo (crossU K c d hb₁ hb₃ hd₂ hc₃) X)).comp
    ((locTwo (crossU K c e h₁ hb₂ hf₁ hb₁) ((stepB K _ _ _ hb₃).tensor X)).comp
      (BHom.whiskerLeft (stepB K _ _ _ h₁) (locTwo (crossU K d e h₂ h₃ hb₂ hb₃) X)))

variable (c d e : Fin m) {s r₁ r₂ r₃ a₁ b₂ f₁ f₂ : Comp m} {E : Type u} [CommRing E]
  (h₁ : StepR (true, c) r₁ s) (h₂ : StepR (true, d) r₂ r₁) (h₃ : StepR (true, e) r₃ r₂)
  (ha₁ : StepR (true, d) a₁ s) (ha₂ : StepR (true, c) r₂ a₁) (hf₂ : StepR (true, e) f₂ a₁)
  (hb₂ : StepR (true, e) b₂ r₁) (hb₃ : StepR (true, d) r₃ b₂) (hb₁ : StepR (true, c) b₂ f₁)
  (hf₁ : StepR (true, e) f₁ s) (hd₂ : StepR (true, d) f₂ f₁) (hc₃ : StepR (true, c) r₃ f₂)
  (X : BRing (H K r₃) E)

theorem braidL_eval (p : MvPolynomial (Fin 3) K) (x : X.T) :
    braidL K c d e h₁ h₂ h₃ ha₁ ha₂ hf₂ hf₁ hd₂ hc₃ X
        (ev3 K _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K e r₃ h₃.2) p *
          iota3 _ _ _ X x) =
      ev3 K _ _ _ X (eXi K e f₁ hf₁.2) (eXi K d f₂ hd₂.2) (eXi K c r₃ hc₃.2)
          (op0 d e (op1 c e (op0 c d p))) * iota3 _ _ _ X x := by
  simp only [braidL, BHom.comp_apply]
  rw [crossU_evalL, crossU_evalR, crossU_evalL]

theorem braidR_eval (p : MvPolynomial (Fin 3) K) (x : X.T) :
    braidR K c d e h₁ h₂ h₃ hb₂ hb₃ hb₁ hf₁ hd₂ hc₃ X
        (ev3 K _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K e r₃ h₃.2) p *
          iota3 _ _ _ X x) =
      ev3 K _ _ _ X (eXi K e f₁ hf₁.2) (eXi K d f₂ hd₂.2) (eXi K c r₃ hc₃.2)
          (op1 c d (op0 c e (op1 d e p))) * iota3 _ _ _ X x := by
  simp only [braidR, BHom.comp_apply]
  rw [crossU_evalR, crossU_evalL, crossU_evalR]

/-- **The braid relation in `Flag_N`** (KL III (4.13), Proposition 6.8 / (6.20)): on
`E_c E_d E_e 1` (with any suffix), `Γ_N(ψ₀ ψ₁ ψ₀) = Γ_N(ψ₁ ψ₀ ψ₁)` unless `c = e ≠ d`. -/
theorem braid_three (hne : ¬(c = e ∧ c ≠ d)) :
    braidL K c d e h₁ h₂ h₃ ha₁ ha₂ hf₂ hf₁ hd₂ hc₃ X =
      braidR K c d e h₁ h₂ h₃ hb₂ hb₃ hb₁ hf₁ hd₂ hc₃ X := by
  refine ext3 (K := K) _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K e r₃ h₃.2)
    (stepE_spanned c h₁) (stepE_spanned d h₂) (stepE_spanned e h₃) _ _ fun p x => ?_
  have hp := braid_poly c d e p
  rw [if_neg hne, sub_eq_zero] at hp
  rw [braidL_eval, braidR_eval, hp]

/-- **The deformed braid relation in `Flag_N`** (KL III (4.14), Proposition 6.8 / (6.21)): for
`c ≠ d`, on `E_c E_d E_c 1` (with any suffix),
`Γ_N(ψ₀ ψ₁ ψ₀) − Γ_N(ψ₁ ψ₀ ψ₁) = Q̄_{cd}(ξ₀, ξ₁, ξ₂)`, where
`Q̄(x₀, x₁, x₂) = (Q(x₀, x₁) − Q(x₂, x₁)) / (x₀ − x₂)` (`KLR.qbar`) and `Q_{cd} = Qf c d`. -/
theorem braidQ_three (hcd : c ≠ d) (h₃ : StepR (true, c) r₃ r₂) (ha₂ : StepR (true, c) r₂ a₁)
    (hb₂ : StepR (true, c) b₂ r₁) (hb₃ : StepR (true, d) r₃ b₂) (X : BRing (H K r₃) E) :
    braidL K c d c h₁ h₂ h₃ ha₁ ha₂ ha₂ h₁ h₂ h₃ X -
        braidR K c d c h₁ h₂ h₃ hb₂ hb₃ hb₂ h₁ h₂ h₃ X =
      BHom.mulB (ev3 K _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2)
        (KLR.qbar (Qf K c d))) := by
  refine ext3 (K := K) _ _ _ X (eXi K c r₁ h₁.2) (eXi K d r₂ h₂.2) (eXi K c r₃ h₃.2)
    (stepE_spanned c h₁) (stepE_spanned d h₂) (stepE_spanned c h₃) _ _ fun p x => ?_
  have hp := braid_poly c d c p
  rw [if_pos ⟨rfl, hcd⟩] at hp
  rw [BHom.sub_apply, braidL_eval, braidR_eval, ← sub_mul, ← map_sub, hp, map_mul, mul_assoc,
    BHom.mulB_apply]

end Braid

end GammaN

end Categorification.Flag

end
