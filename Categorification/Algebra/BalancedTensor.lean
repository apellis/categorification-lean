/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Balanced tensor products over noncommutative algebras

Mathlib's `TensorProduct` is defined over a commutative base. For the induction functors of
Khovanov–Lauda I (arXiv:0803.4121v2, §2.6: `Ind M = R(ν + ν') 1_{ν,ν'} ⊗_{R(ν) ⊗ R(ν')} M`) we
need the tensor product `M ⊗_A N` of a right module `M` and a left module `N` over a
noncommutative `k`-algebra `A`.

Let `k` be a commutative ring and `A`, `B` be `k`-algebras. Let `M` be a `(B, A)`-bimodule
(a left `B`-module and a right `A`-module, i.e. a `Module Aᵐᵒᵖ M`, with commuting actions, both
compatible with `k`) and `N` a left `A`-module. Then

`BalancedTensor k B A M N = (M ⊗[k] N) ⧸ span_B {(m a) ⊗ n - m ⊗ (a n)}`

is a left `B`-module. We write `tmul m n` for the class of `m ⊗ₜ n`. When only the `k`-module
structure is of interest one takes `B = k`.

## Main definitions and results

* `BalancedTensor.tmul`, `BalancedTensor.op_smul_tmul` (`(m a) ⊗ n = m ⊗ (a n)`),
  `BalancedTensor.induction_on`.
* `BalancedTensor.lift` : the universal property: an `A`-balanced `k`-bilinear map
  `f : M → N → P` (`f (m a) n = f m (a n)`) induces a `k`-linear map `M ⊗_A N → P`
  (`lift_tmul`); it is `B`-linear if `f (b m) n = b f m n` (`liftB`). Maps out of `M ⊗_A N` are
  determined by their values on `tmul m n` (`ext`, `extB`). The relations are also spanned over
  `k` (`rel_restrictScalars`), so no `B`-compatibility is needed for `lift`.
* `BalancedTensor.mapRight g` : functoriality in `N` (for `A`-linear `g`), `mapRight_id`,
  `mapRight_comp`, `congrRight`.
* `BalancedTensor.prodRight` : `M ⊗_A (N × N') ≃ (M ⊗_A N) × (M ⊗_A N')`.
* `BalancedTensor.rid` : `M ⊗_A A ≃ M`, and `BalancedTensor.finsuppRight` :
  `M ⊗_A (X →₀ A) ≃ (X →₀ M)`.
* `BalancedTensor.projective` : if `M` is a projective `B`-module and `N` a projective
  `A`-module then `M ⊗_A N` is a projective `B`-module; `BalancedTensor.finite` : likewise for
  finite generation.

## Design notes

The quotient is taken by a `B`-submodule, so that the `B`-module structure is Mathlib's quotient
structure, and the `k`-module structure is `Submodule.Quotient.module'`; for `B = k` these agree
definitionally with the usual ones (no instance diamond).
-/

namespace Categorification

open scoped TensorProduct
open MulOpposite

noncomputable section

variable (k : Type*) [CommRing k] (B : Type*) [Ring B] [Algebra k B]
  (A : Type*) [Ring A]
  (M : Type*) [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  (N : Type*) [AddCommGroup N] [Module k N] [Module A N]

namespace BalancedTensor

/-- The balancing relations `(m a) ⊗ n - m ⊗ (a n)`. -/
def relSet : Set (M ⊗[k] N) :=
  {t | ∃ (m : M) (a : A) (n : N), t = (op a • m) ⊗ₜ[k] n - m ⊗ₜ[k] (a • n)}

/-- The `B`-submodule of `M ⊗[k] N` spanned by the balancing relations. -/
def rel : Submodule B (M ⊗[k] N) := Submodule.span B (relSet k A M N)

end BalancedTensor

/-- The balanced tensor product `M ⊗_A N` of a `(B, A)`-bimodule `M` and a left `A`-module `N`,
a left `B`-module. -/
def BalancedTensor : Type _ := M ⊗[k] N ⧸ BalancedTensor.rel k B A M N

namespace BalancedTensor

instance : AddCommGroup (BalancedTensor k B A M N) :=
  inferInstanceAs (AddCommGroup (M ⊗[k] N ⧸ rel k B A M N))

instance : Module B (BalancedTensor k B A M N) :=
  inferInstanceAs (Module B (M ⊗[k] N ⧸ rel k B A M N))

instance : Module k (BalancedTensor k B A M N) :=
  inferInstanceAs (Module k (M ⊗[k] N ⧸ rel k B A M N))

instance : IsScalarTower k B (BalancedTensor k B A M N) :=
  inferInstanceAs (IsScalarTower k B (M ⊗[k] N ⧸ rel k B A M N))

/-- The quotient map `M ⊗[k] N → M ⊗_A N`. -/
def mk : M ⊗[k] N →ₗ[B] BalancedTensor k B A M N := Submodule.mkQ _

variable {k B A M N}

/-- The class `m ⊗ n ∈ M ⊗_A N`. -/
def tmul (m : M) (n : N) : BalancedTensor k B A M N := mk k B A M N (m ⊗ₜ n)

theorem mk_tmul (m : M) (n : N) : mk k B A M N (m ⊗ₜ n) = tmul m n := rfl

theorem mk_surjective : Function.Surjective (mk k B A M N) := Submodule.mkQ_surjective _

theorem mk_smul (c : k) (t : M ⊗[k] N) : mk k B A M N (c • t) = c • mk k B A M N t := rfl

/-- The balancing relation `(m a) ⊗ n = m ⊗ (a n)`. -/
theorem op_smul_tmul (m : M) (a : A) (n : N) :
    (tmul (op a • m) n : BalancedTensor k B A M N) = tmul m (a • n) := by
  rw [tmul, tmul, ← sub_eq_zero, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨m, a, n, rfl⟩)

theorem tmul_add (m : M) (n n' : N) :
    (tmul m (n + n') : BalancedTensor k B A M N) = tmul m n + tmul m n' := by
  rw [tmul, TensorProduct.tmul_add, map_add]; rfl

theorem add_tmul (m m' : M) (n : N) :
    (tmul (m + m') n : BalancedTensor k B A M N) = tmul m n + tmul m' n := by
  rw [tmul, TensorProduct.add_tmul, map_add]; rfl

@[simp] theorem tmul_zero (m : M) : (tmul m (0 : N) : BalancedTensor k B A M N) = 0 := by
  rw [tmul, TensorProduct.tmul_zero, map_zero]

@[simp] theorem zero_tmul (n : N) : (tmul (0 : M) n : BalancedTensor k B A M N) = 0 := by
  rw [tmul, TensorProduct.zero_tmul, map_zero]

theorem smul_tmul (c : k) (m : M) (n : N) :
    (tmul (c • m) n : BalancedTensor k B A M N) = c • tmul m n := by
  rw [tmul, ← TensorProduct.smul_tmul', mk_smul]; rfl

theorem tmul_smul (c : k) (m : M) (n : N) :
    (tmul m (c • n) : BalancedTensor k B A M N) = c • tmul m n := by
  rw [tmul, TensorProduct.tmul_smul, mk_smul]; rfl

/-- The `B`-action is on the left factor: `b (m ⊗ n) = (b m) ⊗ n`. -/
theorem smul_tmul' (b : B) (m : M) (n : N) :
    (b • tmul m n : BalancedTensor k B A M N) = tmul (b • m) n := by
  rw [tmul, tmul, ← map_smul, TensorProduct.smul_tmul']

theorem tmul_neg (m : M) (n : N) :
    (tmul m (-n) : BalancedTensor k B A M N) = -tmul m n := by
  rw [tmul, TensorProduct.tmul_neg, map_neg]; rfl

theorem tmul_sub (m : M) (n n' : N) :
    (tmul m (n - n') : BalancedTensor k B A M N) = tmul m n - tmul m n' := by
  rw [tmul, TensorProduct.tmul_sub, map_sub]; rfl

theorem tmul_sum {ι : Type*} (s : Finset ι) (m : M) (n : ι → N) :
    (tmul m (∑ i ∈ s, n i) : BalancedTensor k B A M N) = ∑ i ∈ s, tmul m (n i) := by
  rw [tmul, TensorProduct.tmul_sum, map_sum]; rfl

/-- Induction principle: a property holding for `0` and all `tmul m n` and closed under addition
holds everywhere. -/
@[elab_as_elim]
theorem induction_on {motive : BalancedTensor k B A M N → Prop} (x : BalancedTensor k B A M N)
    (zero : motive 0) (tmul : ∀ m n, motive (tmul m n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  obtain ⟨t, rfl⟩ := mk_surjective x
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero
  | tmul m n => exact tmul m n
  | add s t hs ht => rw [map_add]; exact add _ _ hs ht

/-- The span of `{tmul m n}` is everything. -/
theorem span_tmul_eq_top :
    Submodule.span k {x : BalancedTensor k B A M N | ∃ m n, tmul m n = x} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using induction_on with
  | zero => exact zero_mem _
  | tmul m n => exact Submodule.subset_span ⟨m, n, rfl⟩
  | add x y hx hy => exact add_mem hx hy

/-! ### The relations are spanned over `k` -/

section RestrictScalars

variable [SMulCommClass B Aᵐᵒᵖ M]

theorem smul_mem_relSet (b : B) {t : M ⊗[k] N} (ht : t ∈ relSet k A M N) :
    b • t ∈ relSet k A M N := by
  obtain ⟨m, a, n, rfl⟩ := ht
  refine ⟨b • m, a, n, ?_⟩
  rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm b (op a) m]

variable (k B A M N) in
/-- The `k`-span of the relations, as a `B`-submodule. -/
def relK : Submodule B (M ⊗[k] N) where
  carrier := Submodule.span k (relSet k A M N)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' b t ht := by
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span (smul_mem_relSet b ht)
    | zero => rw [smul_zero]; exact zero_mem _
    | add s t _ _ hs ht => rw [smul_add]; exact add_mem hs ht
    | smul c t _ ht => rw [smul_comm]; exact Submodule.smul_mem _ c ht

variable (k B A M N) in
/-- The relations are spanned by the balancing relations over `k`. -/
theorem rel_restrictScalars :
    (rel k B A M N).restrictScalars k = Submodule.span k (relSet k A M N) := by
  apply le_antisymm
  · intro t ht
    have : rel k B A M N ≤ relK k B A M N :=
      Submodule.span_le.2 fun t ht => Submodule.subset_span ht
    exact this ht
  · exact Submodule.span_le.2 fun t ht => Submodule.subset_span ht

variable {P : Type*} [AddCommGroup P] [Module k P]

/-- **The universal property**: an `A`-balanced `k`-bilinear map `f : M × N → P` induces a
`k`-linear map `M ⊗_A N → P`. -/
def lift (f : M →ₗ[k] N →ₗ[k] P) (hf : ∀ (m : M) (a : A) (n : N), f (op a • m) n = f m (a • n)) :
    BalancedTensor k B A M N →ₗ[k] P :=
  (((rel k B A M N).restrictScalars k).liftQ (TensorProduct.lift f) (by
    rw [rel_restrictScalars, Submodule.span_le]
    rintro _ ⟨m, a, n, rfl⟩
    simp [hf])).comp (Submodule.Quotient.restrictScalarsEquiv k (rel k B A M N)).symm.toLinearMap

@[simp] theorem lift_tmul (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (m : M) (a : A) (n : N), f (op a • m) n = f m (a • n)) (m : M) (n : N) :
    lift f hf (tmul m n : BalancedTensor k B A M N) = f m n := rfl

/-- The universal property, `B`-linear version. -/
def liftB [Module B P] [IsScalarTower k B P] (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (m : M) (a : A) (n : N), f (op a • m) n = f m (a • n))
    (hB : ∀ (b : B) (m : M) (n : N), f (b • m) n = b • f m n) :
    BalancedTensor k B A M N →ₗ[B] P where
  toFun := lift f hf
  map_add' := map_add _
  map_smul' b x := by
    induction x using induction_on with
    | zero => simp
    | tmul m n => rw [smul_tmul', lift_tmul, lift_tmul, hB, RingHom.id_apply]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

@[simp] theorem liftB_tmul [Module B P] [IsScalarTower k B P] (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (m : M) (a : A) (n : N), f (op a • m) n = f m (a • n))
    (hB : ∀ (b : B) (m : M) (n : N), f (b • m) n = b • f m n) (m : M) (n : N) :
    liftB f hf hB (tmul m n : BalancedTensor k B A M N) = f m n := rfl

end RestrictScalars

/-- Maps out of `M ⊗_A N` are determined by their values on the `tmul m n`. -/
theorem ext {P : Type*} [AddCommGroup P] [Module k P] {f g : BalancedTensor k B A M N →ₗ[k] P}
    (h : ∀ m n, f (tmul m n) = g (tmul m n)) : f = g := by
  ext x
  induction x using induction_on with
  | zero => simp
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Maps out of `M ⊗_A N` are determined by their values on the `tmul m n` (`B`-linear
version). -/
theorem extB {P : Type*} [AddCommGroup P] [Module B P] {f g : BalancedTensor k B A M N →ₗ[B] P}
    (h : ∀ m n, f (tmul m n) = g (tmul m n)) : f = g := by
  ext x
  induction x using induction_on with
  | zero => simp
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (k B A M N) in
/-- The `k`-bilinear map `(m, n) ↦ m ⊗ n`. -/
def mkBil : M →ₗ[k] N →ₗ[k] BalancedTensor k B A M N :=
  (TensorProduct.mk k M N).compr₂ ((mk k B A M N).restrictScalars k)

@[simp] theorem mkBil_apply (m : M) (n : N) : mkBil k B A M N m n = tmul m n := rfl

/-! ### Functoriality in the right factor -/

section MapRight

variable [Algebra k A] [IsScalarTower k A N] [SMulCommClass B Aᵐᵒᵖ M]

variable {N' N'' : Type*} [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
  [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- The map `M ⊗_A N → M ⊗_A N'` induced by an `A`-linear map `g : N → N'`. -/
def mapRight (g : N →ₗ[A] N') : BalancedTensor k B A M N →ₗ[B] BalancedTensor k B A M N' :=
  liftB ((mkBil k B A M N').compl₂ (g.restrictScalars k))
    (fun m a n => by simp [op_smul_tmul]) (fun b m n => by simp [smul_tmul'])

@[simp] theorem mapRight_tmul (g : N →ₗ[A] N') (m : M) (n : N) :
    mapRight (k := k) (B := B) g (tmul m n) = tmul m (g n) := rfl

@[simp] theorem mapRight_id :
    mapRight (k := k) (B := B) (M := M) (LinearMap.id : N →ₗ[A] N) = LinearMap.id :=
  extB fun _ _ => rfl

theorem mapRight_comp (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    mapRight (k := k) (B := B) (M := M) (g'.comp g) = (mapRight g').comp (mapRight g) :=
  extB fun _ _ => rfl

/-- `M ⊗_A -` applied to an isomorphism. -/
def congrRight (e : N ≃ₗ[A] N') : BalancedTensor k B A M N ≃ₗ[B] BalancedTensor k B A M N' :=
  LinearEquiv.ofLinear (mapRight e.toLinearMap) (mapRight e.symm.toLinearMap)
    (by rw [← mapRight_comp]; simp) (by rw [← mapRight_comp]; simp)

@[simp] theorem congrRight_tmul (e : N ≃ₗ[A] N') (m : M) (n : N) :
    congrRight (k := k) (B := B) e (tmul m n) = tmul m (e n) := rfl

theorem mapRight_surjective {g : N →ₗ[A] N'} (hg : Function.Surjective g) :
    Function.Surjective (mapRight (k := k) (B := B) (M := M) g) := by
  intro x
  induction x using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul m n =>
    obtain ⟨n, rfl⟩ := hg n
    exact ⟨tmul m n, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

/-! ### Direct sums -/

variable (k B A M N N') in
/-- `M ⊗_A (N × N') ≃ (M ⊗_A N) × (M ⊗_A N')`. -/
def prodRight :
    BalancedTensor k B A M (N × N') ≃ₗ[B]
      BalancedTensor k B A M N × BalancedTensor k B A M N' :=
  LinearEquiv.ofLinear
    (LinearMap.prod (mapRight (LinearMap.fst A N N')) (mapRight (LinearMap.snd A N N')))
    (LinearMap.coprod (mapRight (LinearMap.inl A N N')) (mapRight (LinearMap.inr A N N')))
    (by
      apply LinearMap.prod_ext <;> refine extB fun m n => ?_ <;>
        simp [mapRight_tmul])
    (extB fun m n => by
      obtain ⟨n, n'⟩ := n
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.prod_apply, Pi.prod,
        mapRight_tmul, LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.coprod_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.id_coe, id_eq]
      rw [← tmul_add, Prod.mk_add_mk, add_zero, zero_add])

@[simp] theorem prodRight_tmul (m : M) (n : N × N') :
    prodRight k B A M N N' (tmul m n) = (tmul m n.1, tmul m n.2) := rfl

/-! ### `M ⊗_A A ≃ M` and free modules -/

variable [IsScalarTower k Aᵐᵒᵖ M]

variable (k A M) in
/-- The `k`-bilinear right action `(m, a) ↦ m a`. -/
def rsmul : M →ₗ[k] A →ₗ[k] M :=
  LinearMap.mk₂ k (fun m a => op a • m) (fun m m' a => smul_add _ _ _)
    (fun c m a => (smul_comm c (op a) m).symm)
    (fun m a a' => by simp only [op_add, add_smul])
    (fun c m a => by simp only [op_smul, smul_assoc])

@[simp] theorem rsmul_apply (m : M) (a : A) : rsmul k A M m a = op a • m := rfl

variable (k B A M) in
/-- `M ⊗_A A ≃ M`, `m ⊗ a ↦ m a`. -/
def rid : BalancedTensor k B A M A ≃ₗ[B] M :=
  LinearEquiv.ofLinear
    (liftB (rsmul k A M) (fun m a a' => by simp [op_mul, mul_smul])
      (fun b m a => by simp [smul_comm b (op a) m]))
    { toFun := fun m => tmul m 1
      map_add' := fun m m' => add_tmul m m' 1
      map_smul' := fun b m => (smul_tmul' b m 1).symm }
    (by ext m; simp)
    (extB fun m a => by
      simp only [LinearMap.coe_comp, Function.comp_apply, liftB_tmul, rsmul_apply,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq]
      rw [op_smul_tmul, smul_eq_mul, mul_one])

@[simp] theorem rid_tmul (m : M) (a : A) : rid k B A M (tmul m a) = op a • m := rfl

@[simp] theorem rid_symm_apply (m : M) : (rid k B A M).symm m = tmul m 1 := rfl

variable (k A M) in
/-- The `k`-bilinear map `(m, f) ↦ (x ↦ m f(x))`. -/
def finsuppBil (X : Type*) : M →ₗ[k] (X →₀ A) →ₗ[k] (X →₀ M) :=
  LinearMap.mk₂ k (fun m f => Finsupp.mapRange (fun a => op a • m) (by simp) f)
    (fun m m' f => by ext x; simp) (fun c m f => by ext x; simp [smul_comm c])
    (fun m f f' => by ext x; simp [add_smul]) (fun c m f => by ext x; simp [smul_assoc])

@[simp] theorem finsuppBil_apply {X : Type*} (m : M) (f : X →₀ A) (x : X) :
    finsuppBil k A M X m f x = op (f x) • m := by
  simp [finsuppBil]

variable (k B A M) in
/-- `M ⊗_A (X →₀ A) ≃ (X →₀ M)`, `m ⊗ f ↦ (x ↦ m f(x))`. -/
def finsuppRight (X : Type*) : BalancedTensor k B A M (X →₀ A) ≃ₗ[B] (X →₀ M) :=
  LinearEquiv.ofLinear
    (liftB (finsuppBil k A M X)
      (fun m a f => by ext x; simp [op_mul, mul_smul])
      (fun b m f => by ext x; simp [smul_comm b]))
    (Finsupp.lsum ℕ fun x =>
      { toFun := fun m => tmul m (Finsupp.single x 1)
        map_add' := fun m m' => add_tmul m m' _
        map_smul' := fun b m => (smul_tmul' b m _).symm })
    (by
      apply Finsupp.lhom_ext
      intro x m
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsum_single, LinearMap.coe_mk,
        AddHom.coe_mk, liftB_tmul, finsuppBil_apply, LinearMap.id_coe, id_eq]
      by_cases h : x = y
      · subst h; simp
      · simp [Finsupp.single_apply, h])
    (extB fun m f => by
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hf hg ⊢
        rw [tmul_add, map_add, map_add, hf, hg]
      | single x a =>
        have : finsuppBil k A M X m (Finsupp.single x a) = Finsupp.single x (op a • m) := by
          ext y; by_cases h : x = y
          · subst h; simp
          · simp [Finsupp.single_apply, h]
        simp only [LinearMap.coe_comp, Function.comp_apply, liftB_tmul, this, Finsupp.lsum_single,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq]
        rw [op_smul_tmul, Finsupp.smul_single, smul_eq_mul, mul_one])

end MapRight

/-! ### Projectivity and finite generation -/

section Projective

variable [Algebra k A] [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k A N] [SMulCommClass B Aᵐᵒᵖ M]

/-- If `M` is a projective left `B`-module and `N` a projective left `A`-module, then
`M ⊗_A N` is a projective left `B`-module. -/
theorem projective [Module.Projective B M] [Module.Projective A N] :
    Module.Projective B (BalancedTensor k B A M N) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A N›
  haveI : Module.Projective B (N →₀ M) := by
    classical exact Module.Projective.of_equiv (finsuppLequivDFinsupp B).symm
  haveI : Module.Projective B (BalancedTensor k B A M (N →₀ A)) :=
    Module.Projective.of_equiv (finsuppRight k B A M N).symm
  refine Module.Projective.of_split (mapRight s)
    (mapRight (Finsupp.linearCombination A id)) ?_
  rw [← mapRight_comp, hs, mapRight_id]

/-- If `M` is a finitely generated left `B`-module and `N` a finitely generated left `A`-module,
then `M ⊗_A N` is a finitely generated left `B`-module. -/
theorem finite [Module.Finite B M] [Module.Finite A N] :
    Module.Finite B (BalancedTensor k B A M N) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := N)
  have hsurj : Function.Surjective (Finsupp.linearCombination A (Subtype.val : S → N)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hS]
  exact Module.Finite.of_surjective
    ((mapRight (Finsupp.linearCombination A (Subtype.val : S → N))).comp
      (finsuppRight k B A M S).symm.toLinearMap)
    ((mapRight_surjective hsurj).comp (finsuppRight k B A M S).symm.surjective)

end Projective

end BalancedTensor

end

end Categorification
