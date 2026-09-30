/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Duality
import Categorification.Algebra.Graded.G0Basis

/-!
# The tensor product description `P^ψ ⊗_A N ≅ HOM(P̄, N)` of KL I's form

Let `(A, 𝒜)` be a `ℤ`-graded algebra over a field `k` with a degree-preserving antiinvolution `ψ`
(`GradedAntiInvolution 𝒜`). Khovanov–Lauda I (arXiv:0803.4121v2, §2.5, TeX lines ~1533–1580)
twist a left `A`-module `M` by `ψ` into a right module `M^ψ` and define

* the pairing `K₀ × G₀ → ℤ((q))`, `([P], [M]) = gdim (P^ψ ⊗_{R(ν)} M)` (equation `eq_bil_pair`),
* the bilinear form on `K₀`, `([P], [Q]) = gdim (P^ψ ⊗_{R(ν)} Q)` (equations `eq_bil_pair2`,
  `eq-bil-ten`).

The library's forms are defined through `HOM` spaces: `K0.homForm` (`([P], [Q]) = gdim HOM(P, Q)`,
sesquilinear), `K0.pform` (`(x, y) = homForm x̄ y`, bilinear) and `pairing`
(`([P], [M]) = gdim HOM(P, M)`). Here we prove the identification with the paper's tensor
product definitions on the nose, for every finitely generated graded projective `P` and every
graded module `N`:

  `P^ψ ⊗_A N ≅ HOM(P̄, N)`, `m ⊗ n ↦ (f ↦ ψ(f(m)) n)`, degree-preserving,

where `P̄ = HOM(P, A)^ψ` (`GProj.dual`). Consequently the paper's form is `pform`, i.e.
`gdim (P^ψ ⊗_A Q) = homForm [P̄] [Q]`, on all of `K₀(A)`: it is `ℤ[q, q⁻¹]`-*bilinear*
(`K0.pform_smul_left`, `K0.pform_smul_right`), while `homForm` is antilinear in the first
variable, `homForm x y = (x̄, y)` (`K0.homForm_eq_pform`).

## Main definitions and results

* `Twist ψ M` : the right `A`-module `M^ψ` (`m · a = ψ(a) m`), graded as `M` (`twistGrading`).
* `TwistTensor ψ M N` : `M^ψ ⊗_A N` (`Categorification.BalancedTensor`), with the induced grading
  `twistTensorGrading ψ ℳ 𝒩` (a `Decomposition`, instance).
* `twistTensorToHom` : the map `M^ψ ⊗_A N → HOM(M̄, N)`, `m ⊗ n ↦ (f ↦ ψ(f(m)) n)`, which is
  degree-preserving (`twistTensorToHom_mem`) and, for `M` finitely generated projective,
  bijective (`twistTensorToHom_bijective`, with explicit inverse from a dual basis).
* `twistTensorGradedEquiv` : **`P^ψ ⊗_A N ≅ HOM(P̄, N)`** as graded `k`-vector spaces, for `P`
  finitely generated projective and `N` any graded module.
* `gdim_twistTensor` : `gdim (P^ψ ⊗_A N) = gdim HOM(P̄, N)`; `hasGdim_twistTensor`.
* `K0.pform_of_eq_gdim_twistTensor` : **`([P], [Q]) = gdim (P^ψ ⊗_A Q)`** for `pform`
  (KL I `eq-bil-ten`), and `K0.homForm_of_eq_gdim_twistTensor` : `homForm [P] [Q] =
  gdim (P̄^ψ ⊗_A Q)`.
* `K0.eq_pform_of_gdim_twistTensor` : **the paper's form on all of `K₀`**: any biadditive
  `F : K₀ × K₀ → ℤ((q))` with `F [P] [Q] = gdim (P^ψ ⊗_A Q)` for all `P`, `Q` is `pform`
  (hence it is `ℤ[q, q⁻¹]`-bilinear and symmetric, and equals `(x, y) ↦ homForm x̄ y`);
  `K0.gdim_twistTensor_comm` : `gdim (P^ψ ⊗_A Q) = gdim (Q^ψ ⊗_A P)`.
* `pairing_bar_of_eq_gdim_twistTensor` : **`gdim (P^ψ ⊗_A M) = pairing [P̄] [M]`** for a
  finite-dimensional graded `M` (KL I `eq_bil_pair`), and `eq_pairing_bar_of_gdim_twistTensor`
  (the paper's pairing on all of `K₀ × G₀` is `(x, y) ↦ pairing x̄ y`).

## Not addressed here

The paper's further remark that `P^ψ ⊗_{R(ν)} Q` is a free graded `Sym(ν)`-module of finite rank
(so that the form takes values in `ℤ[q, q⁻¹] · (ν)_q`) is not treated in this file; for `KLR`
algebras see `Categorification.KLR.TensorForm` for the values on the `P_i`.
-/

universe u v

noncomputable section

namespace Categorification.Graded

open DirectSum Module Function MulOpposite BalancedTensor

/-! ### The twisted right module `M^ψ` -/

section Twist

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-- The right `A`-module `M^ψ`: the left module `M` with the action twisted by `ψ`,
`m · a = ψ(a) m` (KL I, arXiv:0803.4121v2, §2.5). A type synonym for `M`. -/
def Twist (_ψ : GradedAntiInvolution 𝒜) (M : Type*) : Type _ := M

namespace Twist

variable (ψ : GradedAntiInvolution 𝒜) (M : Type*) [AddCommGroup M] [Module A M] [Module k M]

instance : AddCommGroup (Twist ψ M) := inferInstanceAs (AddCommGroup M)
instance : Module k (Twist ψ M) := inferInstanceAs (Module k M)

variable {ψ M}

/-- The identity `M → M^ψ`. -/
def of : M ≃ₗ[k] Twist ψ M := LinearEquiv.refl k M

variable (ψ M) in
instance : SMul Aᵐᵒᵖ (Twist ψ M) := ⟨fun a m => of (ψ (unop a) • of.symm m)⟩

/-- `m · a = ψ(a) m`. -/
@[simp] theorem op_smul_of (a : A) (m : M) : (op a • of m : Twist ψ M) = of (ψ a • m) := rfl

omit [Module A M] in
@[simp] theorem of_symm_of (m : M) : (of.symm (of m : Twist ψ M) : M) = m := rfl

theorem op_smul_def (a : A) (m : Twist ψ M) : op a • m = of (ψ a • of.symm m) := rfl

variable (ψ M) in
instance : Module Aᵐᵒᵖ (Twist ψ M) where
  one_smul m := by
    change of (ψ 1 • of.symm m) = m
    rw [ψ.map_one, one_smul]; rfl
  mul_smul a b m := by
    change of (ψ (unop b * unop a) • of.symm m) = of (ψ (unop a) • of.symm (of (ψ (unop b) •
      of.symm m)))
    rw [ψ.map_mul, mul_smul]; rfl
  smul_zero a := by
    change of (ψ (unop a) • of.symm 0) = 0
    rw [map_zero, smul_zero, map_zero]
  smul_add a m m' := by
    change of (ψ (unop a) • of.symm (m + m')) = of (ψ (unop a) • of.symm m) +
      of (ψ (unop a) • of.symm m')
    rw [map_add, smul_add, map_add]
  add_smul a b m := by
    change of (ψ (unop a + unop b) • of.symm m) = of (ψ (unop a) • of.symm m) +
      of (ψ (unop b) • of.symm m)
    rw [ψ.map_add, add_smul, map_add]
  zero_smul m := by
    change of (ψ 0 • of.symm m) = 0
    rw [ψ.map_zero, zero_smul, map_zero]

variable (ψ M) in
instance [IsScalarTower k A M] : IsScalarTower k Aᵐᵒᵖ (Twist ψ M) where
  smul_assoc c a m := by
    change (of (ψ (unop (c • a)) • of.symm m) : Twist ψ M) = of (c • (ψ (unop a) • of.symm m))
    rw [MulOpposite.unop_smul, ψ.map_smul, smul_assoc]

variable (ψ M) in
instance [IsScalarTower k A M] : SMulCommClass k Aᵐᵒᵖ (Twist ψ M) where
  smul_comm c a m := by
    change (of (c • (ψ (unop a) • of.symm m)) : Twist ψ M) = of (ψ (unop a) • (c • of.symm m))
    rw [smul_comm]

end Twist

variable (ψ : GradedAntiInvolution 𝒜) {M : Type*} [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

/-- The grading of `M^ψ`: that of `M`. -/
def twistGrading (ℳ : ℤ → Submodule k M) : ℤ → Submodule k (Twist ψ M) := ℳ

omit [Module A M] [IsScalarTower k A M] in
variable {ψ} in
@[simp] theorem of_mem_twistGrading {ℳ : ℤ → Submodule k M} {d : ℤ} {m : M} :
    (Twist.of m : Twist ψ M) ∈ twistGrading ψ ℳ d ↔ m ∈ ℳ d := Iff.rfl

omit [Module A M] [IsScalarTower k A M] in
variable {ψ} in
theorem mem_twistGrading {ℳ : ℤ → Submodule k M} {d : ℤ} {m : Twist ψ M} :
    m ∈ twistGrading ψ ℳ d ↔ Twist.of.symm m ∈ ℳ d := Iff.rfl

instance (ℳ : ℤ → Submodule k M) [Decomposition ℳ] : Decomposition (twistGrading ψ ℳ) :=
  inferInstanceAs (Decomposition ℳ)

omit [IsScalarTower k A M] in
/-- The twisted right action on `M^ψ` is graded: `M^ψ_i · A_l ⊆ M^ψ_{i+l}`. -/
theorem op_smul_mem_twistGrading [GradedAlgebra 𝒜] {ℳ : ℤ → Submodule k M}
    [SetLike.GradedSMul 𝒜 ℳ] ⦃i l : ℤ⦄ ⦃m : Twist ψ M⦄ ⦃a : A⦄
    (hm : m ∈ twistGrading ψ ℳ i) (ha : a ∈ 𝒜 l) : op a • m ∈ twistGrading ψ ℳ (i + l) := by
  have h := SetLike.GradedSMul.smul_mem (ψ.mem_grade ha) (mem_twistGrading.1 hm)
  rw [vadd_eq_add, add_comm] at h
  exact mem_twistGrading.2 h

end Twist

/-! ### The graded tensor product `M^ψ ⊗_A N` and the map to `HOM(M̄, N)` -/

section TwistTensor

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  (ψ : GradedAntiInvolution 𝒜)
  {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

variable (M N) in
/-- The balanced tensor product `M^ψ ⊗_A N` (a `k`-vector space). -/
abbrev TwistTensor : Type _ := BalancedTensor k k A (Twist ψ M) N

/-- The grading of `M^ψ ⊗_A N` induced by those of `M` and `N`. -/
def twistTensorGrading (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) :
    ℤ → Submodule k (TwistTensor ψ M N) :=
  balancedGrading k A (twistGrading ψ ℳ) 𝒩

instance [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩] :
    Decomposition (twistTensorGrading ψ ℳ 𝒩) :=
  balancedDecomposition 𝒜 (op_smul_mem_twistGrading ψ)

omit [IsScalarTower k A M] [IsScalarTower k A N] in
variable {ψ} in
theorem tmul_mem_twistTensorGrading {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    {i j : ℤ} {m : M} {n : N} (hm : m ∈ ℳ i) (hn : n ∈ 𝒩 j) :
    (tmul (Twist.of m) n : TwistTensor ψ M N) ∈ twistTensorGrading ψ ℳ 𝒩 (i + j) :=
  tmul_mem_balancedGrading (of_mem_twistGrading.2 hm) hn

omit [IsScalarTower k A M] [IsScalarTower k A N] in
theorem sum_tmul_twist {ι : Type*} (s : Finset ι) (m : ι → Twist ψ M) (n : N) :
    (tmul (∑ i ∈ s, m i) n : TwistTensor ψ M N) = ∑ i ∈ s, tmul (m i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_tmul, ih]

/-- For `m ∈ M`, `n ∈ N`, the `A`-linear map `M̄ → N`, `f ↦ ψ(f(m)) n`. -/
def twistPairingAux (m : M) (n : N) : Dual ψ M →ₗ[A] N where
  toFun f := ψ (f m) • n
  map_add' f f' := by simp [add_smul]
  map_smul' a f := by simp [mul_smul]

omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
@[simp] theorem twistPairingAux_apply (m : M) (n : N) (f : Dual ψ M) :
    twistPairingAux ψ m n f = ψ (f m) • n := rfl

/-- The `k`-bilinear map `M^ψ × N → HOM(M̄, N)`, `(m, n) ↦ (f ↦ ψ(f(m)) n)`. -/
def twistPairing : Twist ψ M →ₗ[k] N →ₗ[k] (Dual ψ M →ₗ[A] N) :=
  LinearMap.mk₂ k (fun m n => twistPairingAux ψ (Twist.of.symm m) n)
    (fun m m' n => LinearMap.ext fun f => by simp [add_smul])
    (fun c m n => LinearMap.ext fun f => by
      change ψ (f (c • Twist.of.symm m)) • n = c • (ψ (f (Twist.of.symm m)) • n)
      rw [show f (c • Twist.of.symm m) = c • f (Twist.of.symm m) from
        LinearMap.map_smul_of_tower (Dual.toHom f) c _, ψ.map_smul, smul_assoc])
    (fun m n n' => LinearMap.ext fun f => by simp)
    (fun c m n => LinearMap.ext fun f => by
      change ψ (f (Twist.of.symm m)) • (c • n) = c • (ψ (f (Twist.of.symm m)) • n)
      rw [smul_comm])

/-- **The comparison map** `M^ψ ⊗_A N → HOM(M̄, N)`, `m ⊗ n ↦ (f ↦ ψ(f(m)) n)`. -/
def twistTensorToHom : TwistTensor ψ M N →ₗ[k] (Dual ψ M →ₗ[A] N) :=
  BalancedTensor.lift (twistPairing ψ) fun m a n => LinearMap.ext fun f => by
    change ψ (f (ψ a • Twist.of.symm m)) • n = ψ (f (Twist.of.symm m)) • (a • n)
    rw [map_smul, smul_eq_mul, ψ.map_mul, ψ.invol, mul_smul]

@[simp] theorem twistTensorToHom_tmul (m : M) (n : N) (f : Dual ψ M) :
    twistTensorToHom ψ (tmul (Twist.of m) n : TwistTensor ψ M N) f = ψ (f m) • n := rfl

/-- The inverse of `twistTensorToHom` built from a dual basis `(x_i, g_i)` of `M`:
`G ↦ ∑ᵢ x_i ⊗ G(g_i)`. -/
def twistTensorOfHom {r : ℕ} (x : Fin r → M) (g : Fin r → (M →ₗ[A] A)) :
    (Dual ψ M →ₗ[A] N) →ₗ[k] TwistTensor ψ M N where
  toFun G := ∑ i, tmul (Twist.of (x i)) (G (Dual.ofHom ψ (g i)))
  map_add' G G' := by simp [tmul_add, Finset.sum_add_distrib]
  map_smul' c G := by simp [tmul_smul, Finset.smul_sum]

variable {ψ} in
theorem twistTensorToHom_ofHom {r : ℕ} {x : Fin r → M} {g : Fin r → (M →ₗ[A] A)}
    (hxg : ∀ m, ∑ i, g i m • x i = m) (G : Dual ψ M →ₗ[A] N) :
    twistTensorToHom ψ (twistTensorOfHom ψ x g G) = G := by
  ext f
  simp only [twistTensorOfHom, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.sum_apply,
    twistTensorToHom_tmul]
  conv_rhs => rw [Dual.eq_sum_of_dualBasis ψ hxg f]
  simp [map_sum, map_smul]

variable {ψ} in
theorem twistTensorOfHom_toHom {r : ℕ} {x : Fin r → M} {g : Fin r → (M →ₗ[A] A)}
    (hxg : ∀ m, ∑ i, g i m • x i = m) (t : TwistTensor ψ M N) :
    twistTensorOfHom ψ x g (twistTensorToHom ψ t) = t := by
  have h : (twistTensorOfHom ψ x g).comp (twistTensorToHom ψ (N := N)) = LinearMap.id := by
    refine BalancedTensor.ext fun m n => ?_
    obtain ⟨m, rfl⟩ := (Twist.of : M ≃ₗ[k] Twist ψ M).surjective m
    have hi : ∀ i, (tmul (Twist.of (x i)) (ψ (g i m) • n) : TwistTensor ψ M N) =
        tmul (Twist.of (g i m • x i)) n := fun i => by
      rw [← op_smul_tmul, Twist.op_smul_of, ψ.invol]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, twistTensorOfHom, LinearMap.coe_mk,
      AddHom.coe_mk, twistTensorToHom_tmul, Dual.ofHom_apply, hi, ← sum_tmul_twist, ← map_sum,
      hxg]
  exact LinearMap.congr_fun h t

theorem twistTensorToHom_bijective [Module.Finite A M] [Module.Projective A M] :
    Bijective (twistTensorToHom ψ (M := M) (N := N)) := by
  obtain ⟨r, x, g, hxg⟩ := exists_dualBasis (A := A) (M := M)
  exact ⟨LeftInverse.injective (twistTensorOfHom_toHom hxg),
    RightInverse.surjective (twistTensorToHom_ofHom hxg)⟩

variable {ψ} in
/-- `twistTensorToHom` is degree-preserving: `(M^ψ ⊗_A N)_d → HOM(M̄, N)_d`. -/
theorem twistTensorToHom_mem {ℳ : ℤ → Submodule k M} {𝒩 : ℤ → Submodule k N}
    [SetLike.GradedSMul 𝒜 𝒩] ⦃d : ℤ⦄ ⦃t : TwistTensor ψ M N⦄
    (ht : t ∈ twistTensorGrading ψ ℳ 𝒩 d) :
    twistTensorToHom ψ t ∈ homGrade A (dualGrading ψ ℳ) 𝒩 d := by
  refine balancedGrading_map_mem _ ((twistTensorToHom ψ).restrictScalars k)
    (fun i j m n hm hn => ?_) ht
  intro e f hf
  have h := SetLike.GradedSMul.smul_mem (ψ.mem_grade (hf (mem_twistGrading.1 hm))) hn
  rw [vadd_eq_add, show i + e + j = e + (i + j) by ring] at h
  exact h

/-- **`M^ψ ⊗_A N ≅ HOM(M̄, N)`** as graded `k`-vector spaces, for `M` finitely generated
projective (KL I, arXiv:0803.4121v2, §2.5). -/
def twistTensorGradedEquiv [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
    [Module.Finite A M] [Module.Projective A M] :
    twistTensorGrading ψ ℳ 𝒩 ≃ᵍ[k] homGrade A (dualGrading ψ ℳ) 𝒩 :=
  letI := (isInternal_homGrade 𝒜 (dualGrading ψ ℳ) 𝒩).chooseDecomposition
  GradedEquiv.ofPreserves (LinearEquiv.ofBijective (twistTensorToHom ψ)
    (twistTensorToHom_bijective ψ)) twistTensorToHom_mem

@[simp] theorem twistTensorGradedEquiv_apply [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M)
    [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩]
    [SetLike.GradedSMul 𝒜 𝒩] [Module.Finite A M] [Module.Projective A M]
    (t : TwistTensor ψ M N) : twistTensorGradedEquiv ψ ℳ 𝒩 t = twistTensorToHom ψ t := rfl

/-- **`gdim (M^ψ ⊗_A N) = gdim HOM(M̄, N)`** for `M` finitely generated projective. -/
theorem gdim_twistTensor [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]
    [Module.Finite A M] [Module.Projective A M] :
    gdim (twistTensorGrading ψ ℳ 𝒩) = gdim (homGrade A (dualGrading ψ ℳ) 𝒩) :=
  gdim_eq_of_finrank_eq (finrank_eq_of_gradedEquiv (twistTensorGradedEquiv ψ ℳ 𝒩))

/-- `M^ψ ⊗_A N` has a graded dimension when `HOM(M̄, N)` does. -/
theorem hasGdim_twistTensor [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule k M) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩]
    [SetLike.GradedSMul 𝒜 𝒩] [Module.Finite A M] [Module.Projective A M]
    [HasGdim (homGrade A (dualGrading ψ ℳ) 𝒩)] : HasGdim (twistTensorGrading ψ ℳ 𝒩) :=
  HasGdim.of_linearEquiv (𝒩 := homGrade A (dualGrading ψ ℳ) 𝒩) fun d =>
    (twistTensorGradedEquiv ψ ℳ 𝒩).toLinearEquiv.ofSubmodules _ _ (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (twistTensorGradedEquiv ψ ℳ 𝒩).map_mem hx
      · intro hy
        exact ⟨_, (twistTensorGradedEquiv ψ ℳ 𝒩).symm_map_mem' hy,
          LinearEquiv.apply_symm_apply _ y⟩)

end TwistTensor

/-! ### KL I's form and pairing through `P^ψ ⊗_A -` -/

section Forms

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜] (ψ : GradedAntiInvolution 𝒜)

namespace GProj

/-- **`gdim (P^ψ ⊗_A N) = gdim HOM(P̄, N)`** for `P` in `A-pmod` and any graded module `N`. -/
theorem gdim_twistTensor (P : GProj 𝒜) (N : GMod 𝒜) :
    gdim (twistTensorGrading ψ P.grading N.grading) =
      gdim (homGrade A (P.dual ψ).grading N.grading) :=
  Graded.gdim_twistTensor ψ P.grading N.grading

instance hasGdim_twistTensor [HasGdim 𝒜] (P Q : GProj 𝒜) :
    HasGdim (twistTensorGrading ψ P.grading Q.grading) :=
  haveI := GProj.hasGdim_homGrade (P.dual ψ) Q
  Graded.hasGdim_twistTensor ψ P.grading Q.grading

end GProj

namespace K0

variable [HasGdim 𝒜]

/-- **KL I, §2.5, equation `eq-bil-ten`**: the bilinear form `pform` is
`([P], [Q]) = gdim (P^ψ ⊗_A Q)`. -/
theorem pform_of_eq_gdim_twistTensor (P Q : GProj 𝒜) :
    pform 𝒜 ψ (of P) (of Q) = gdim (twistTensorGrading ψ P.grading Q.grading) :=
  (pform_of ψ P Q).trans (GProj.gdim_twistTensor ψ P Q.toGMod).symm

/-- The sesquilinear form `homForm` through tensor products:
`homForm [P] [Q] = gdim HOM(P, Q) = gdim (P̄^ψ ⊗_A Q)`. -/
theorem homForm_of_eq_gdim_twistTensor (P Q : GProj 𝒜) :
    homForm 𝒜 (of P) (of Q) = gdim (twistTensorGrading ψ (P.dual ψ).grading Q.grading) := by
  rw [homForm_eq_pform ψ, bar_of, pform_of_eq_gdim_twistTensor]

/-- **KL I's form on all of `K₀`** (arXiv:0803.4121v2, §2.5, `eq_bil_pair2`, `eq-bil-ten`): a
biadditive `F : K₀(A) × K₀(A) → ℤ((q))` with `F([P], [Q]) = gdim (P^ψ ⊗_A Q)` for all `P`, `Q` in
`A-pmod` is `pform`, i.e. `F(x, y) = homForm x̄ y`. In particular it is `ℤ[q, q⁻¹]`-bilinear
(`pform_smul_left`, `pform_smul_right`) and symmetric (`pform_comm`). -/
theorem eq_pform_of_gdim_twistTensor (F : K0 𝒜 →+ K0 𝒜 →+ LaurentSeries ℤ)
    (hF : ∀ P Q : GProj 𝒜, F (of P) (of Q) = gdim (twistTensorGrading ψ P.grading Q.grading)) :
    F = pform 𝒜 ψ :=
  hom_ext fun P => hom_ext fun Q => by rw [hF, pform_of_eq_gdim_twistTensor]

/-- KL I, §2.5: `gdim (P^ψ ⊗_A Q) = gdim (Q^ψ ⊗_A P)` (the form is symmetric). -/
theorem gdim_twistTensor_comm (P Q : GProj 𝒜) :
    gdim (twistTensorGrading ψ P.grading Q.grading) =
      gdim (twistTensorGrading ψ Q.grading P.grading) := by
  rw [← pform_of_eq_gdim_twistTensor, ← pform_of_eq_gdim_twistTensor, pform_comm]

end K0

/-- **KL I, §2.5, equation `eq_bil_pair`**: for `P` in `A-pmod` and `M` finite-dimensional,
`gdim (P^ψ ⊗_A M) = gdim HOM(P̄, M) = pairing [P̄] [M]`. -/
theorem pairing_bar_of_eq_gdim_twistTensor (P : GProj 𝒜) (M : GFin 𝒜) :
    pairing (K0.bar ψ (K0.of P)) (G0.of M) = gdim (twistTensorGrading ψ P.grading M.grading) := by
  rw [K0.bar_of, pairing_of_of]
  exact (GProj.gdim_twistTensor ψ P M.toGMod).symm

/-- **KL I's pairing `K₀ × G₀ → ℤ((q))` on all of `K₀ × G₀`** (`eq_bil_pair`): a biadditive `F` with
`F([P], [M]) = gdim (P^ψ ⊗_A M)` is `(x, y) ↦ pairing x̄ y`. -/
theorem eq_pairing_bar_of_gdim_twistTensor (F : K0 𝒜 →+ G0 𝒜 →+ LaurentSeries ℤ)
    (hF : ∀ (P : GProj 𝒜) (M : GFin 𝒜),
      F (K0.of P) (G0.of M) = gdim (twistTensorGrading ψ P.grading M.grading)) :
    F = pairing.comp (K0.bar ψ) :=
  K0.hom_ext fun P => G0.hom_ext fun M => by
    rw [hF, AddMonoidHom.comp_apply, pairing_bar_of_eq_gdim_twistTensor]

end Forms

end Categorification.Graded
