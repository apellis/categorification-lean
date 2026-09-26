/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Bimodules given by commutative rings, and their tensor products

The 1-morphisms of the flag 2-category `Flag_N` of Khovanov–Lauda III (arXiv:0807.3250v1,
§5.3, Definition 5.6) are iterated tensor products

  `H_{k^{s_1}} ⊗_{H_{s_2 ⋯ k}} ⋯ ⊗_{H_{s_m k}} H_{k^{s_m}}`

of bimodules `H_{k^{±i}}` which are themselves *commutative rings* receiving ring maps from the
two outer rings (the pullbacks `p_1^*`, `p_2^*`). Such iterated tensor products are again
commutative rings with two ring maps from the outer rings. We formalize this structure:

* `BRing A B`: a commutative ring `T` with ring maps `left : A →+* T` and `right : B →+* T`;
  it is an `(A, B)`-bimodule (`A` acting by `left a * -`, `B` by `right b * -`).
* `BRing.tensor M N` (`M ⊗ N`): for `M : BRing A B`, `N : BRing B C`, the ring
  `M.T ⊗_B N.T` (Mathlib's `Algebra.TensorProduct`, `B` acting on `M.T` through `M.right` and on
  `N.T` through `N.left`), with the outer maps `a ↦ left a ⊗ 1`, `c ↦ 1 ⊗ right c`.
* `BRing.idB A`: the identity bimodule `A`.
* `BHom M N`: bimodule maps (additive maps commuting with both actions), with composition,
  sums, the multiplication maps `mulB x` (a commutative ring acts on itself by bimodule maps),
  and whiskering `whiskerRight φ N : M ⊗ N → M' ⊗ N`, `whiskerLeft M ψ : M ⊗ N → M ⊗ N'`
  (functorial, `whiskerRight_comp`, `whiskerLeft_comp`, and satisfying the interchange law
  `whisker_exchange`).
* `BIso`, the associator `BRing.assoc : (M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)` and the unitors
  `BRing.ridIso : M ⊗ idB B ≅ M`, `BRing.lidIso : idB A ⊗ M ≅ M`.

Maps out of tensor products are built from ring homomorphisms (`liftRingHom`) or from balanced
biadditive maps (`liftAdd`); both are determined by their values on pure tensors
(`BRing.tmul`, `BRing.induction_on`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.Flag

universe u

/-- **A bimodule given by a commutative ring**: a commutative ring `T` with ring maps from `A`
(acting on the left) and `B` (acting on the right). -/
structure BRing (A B : Type u) [CommRing A] [CommRing B] where
  /-- The underlying ring. -/
  T : Type u
  [ring : CommRing T]
  /-- The left action. -/
  left : A →+* T
  /-- The right action. -/
  right : B →+* T

attribute [instance] BRing.ring

namespace BRing

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

/-- `M.T` as a `B`-algebra through the right action. -/
def algR (M : BRing A B) : Algebra B M.T := M.right.toAlgebra

/-- `M.T` as an `A`-algebra through the left action. -/
def algL (M : BRing A B) : Algebra A M.T := M.left.toAlgebra

/-- The identity bimodule `A`. -/
abbrev idB (A : Type u) [CommRing A] : BRing A A := ⟨A, RingHom.id A, RingHom.id A⟩

/-! ### The tensor product -/

section Tensor

variable (M : BRing A B) (N : BRing B C)

/-- The ring `M.T ⊗_B N.T`. -/
def TT : Type u := letI := M.algR; letI := N.algL; M.T ⊗[B] N.T

instance instCommRingTT : CommRing (TT M N) :=
  letI := M.algR; letI := N.algL; Algebra.TensorProduct.instCommRing

/-- The pure tensor `m ⊗ n`. -/
def tmul (m : M.T) (n : N.T) : TT M N := letI := M.algR; letI := N.algL; m ⊗ₜ[B] n

/-- The inclusion `m ↦ m ⊗ 1`, a ring map. -/
def inclL : M.T →+* TT M N :=
  letI := M.algR; letI := N.algL; Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion `n ↦ 1 ⊗ n`, a ring map. -/
def inclR : N.T →+* TT M N :=
  letI := M.algR; letI := N.algL; (Algebra.TensorProduct.includeRight).toRingHom

/-- **The tensor product of bimodules** `M ⊗_B N`. -/
abbrev tensor : BRing A C where
  T := TT M N
  left := (inclL M N).comp M.left
  right := (inclR M N).comp N.right

variable {M N}

theorem inclL_apply (m : M.T) : inclL M N m = tmul M N m 1 := rfl

theorem inclR_apply (n : N.T) : inclR M N n = tmul M N 1 n := rfl

@[simp] theorem tensor_T : (tensor M N).T = TT M N := rfl

theorem tensor_left (a : A) : (tensor M N).left a = tmul M N (M.left a) 1 := rfl

theorem tensor_right (c : C) : (tensor M N).right c = tmul M N 1 (N.right c) := rfl

theorem tmul_mul_tmul (m m' : M.T) (n n' : N.T) :
    tmul M N m n * tmul M N m' n' = tmul M N (m * m') (n * n') :=
  letI := M.algR; letI := N.algL; Algebra.TensorProduct.tmul_mul_tmul m m' n n'

theorem one_eq : (1 : TT M N) = tmul M N 1 1 := rfl

theorem tmul_add (m : M.T) (n n' : N.T) : tmul M N m (n + n') = tmul M N m n + tmul M N m n' :=
  letI := M.algR; letI := N.algL; TensorProduct.tmul_add m n n'

theorem add_tmul (m m' : M.T) (n : N.T) : tmul M N (m + m') n = tmul M N m n + tmul M N m' n :=
  letI := M.algR; letI := N.algL; TensorProduct.add_tmul m m' n

@[simp] theorem tmul_zero (m : M.T) : tmul M N m 0 = 0 :=
  letI := M.algR; letI := N.algL; TensorProduct.tmul_zero N.T m

@[simp] theorem zero_tmul (n : N.T) : tmul M N 0 n = 0 :=
  letI := M.algR; letI := N.algL; TensorProduct.zero_tmul M.T n

theorem tmul_neg (m : M.T) (n : N.T) : tmul M N m (-n) = -tmul M N m n :=
  letI := M.algR; letI := N.algL; TensorProduct.tmul_neg m n

theorem neg_tmul (m : M.T) (n : N.T) : tmul M N (-m) n = -tmul M N m n :=
  letI := M.algR; letI := N.algL; TensorProduct.neg_tmul m n

theorem tmul_sub (m : M.T) (n n' : N.T) : tmul M N m (n - n') = tmul M N m n - tmul M N m n' :=
  letI := M.algR; letI := N.algL; TensorProduct.tmul_sub m n n'

theorem sub_tmul (m m' : M.T) (n : N.T) : tmul M N (m - m') n = tmul M N m n - tmul M N m' n :=
  letI := M.algR; letI := N.algL; TensorProduct.sub_tmul m m' n

theorem sum_tmul {ι : Type*} (S : Finset ι) (f : ι → M.T) (n : N.T) :
    tmul M N (∑ i ∈ S, f i) n = ∑ i ∈ S, tmul M N (f i) n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, add_tmul, ih, Finset.sum_insert ha]

theorem tmul_sum {ι : Type*} (S : Finset ι) (m : M.T) (f : ι → N.T) :
    tmul M N m (∑ i ∈ S, f i) = ∑ i ∈ S, tmul M N m (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, tmul_add, ih, Finset.sum_insert ha]

/-- **The balancing relation** `(m b) ⊗ n = m ⊗ (b n)`. -/
theorem tmul_balance (m : M.T) (b : B) (n : N.T) :
    tmul M N (M.right b * m) n = tmul M N m (N.left b * n) := by
  letI := M.algR; letI := N.algL
  change (b • m) ⊗ₜ[B] n = m ⊗ₜ[B] (b • n)
  exact TensorProduct.smul_tmul b m n

theorem tmul_right_one (b : B) :
    tmul M N (M.right b) 1 = tmul M N 1 (N.left b) := by
  simpa using tmul_balance (M := M) (N := N) 1 b 1

theorem tmul_eq_mul (m : M.T) (n : N.T) : tmul M N m n = tmul M N m 1 * tmul M N 1 n := by
  rw [tmul_mul_tmul, mul_one, one_mul]

theorem tmul_pow (m : M.T) (n : N.T) (e : ℕ) : tmul M N m n ^ e = tmul M N (m ^ e) (n ^ e) :=
  letI := M.algR; letI := N.algL; Algebra.TensorProduct.tmul_pow m n e

/-- Induction on the tensor product: pure tensors and sums. -/
theorem induction_on {P : TT M N → Prop} (t : TT M N) (h0 : P 0)
    (htmul : ∀ m n, P (tmul M N m n)) (hadd : ∀ x y, P x → P y → P (x + y)) : P t := by
  letI := M.algR; letI := N.algL
  exact TensorProduct.induction_on t h0 htmul hadd

/-- Two additive maps out of `M ⊗ N` agreeing on pure tensors agree. -/
theorem addHom_ext {X : Type*} [AddCommGroup X] {f g : TT M N →+ X}
    (h : ∀ m n, f (tmul M N m n) = g (tmul M N m n)) : f = g := by
  ext t
  refine induction_on (P := fun t => f t = g t) t (by simp) h fun x y hx hy => ?_
  beta_reduce at hx hy ⊢
  rw [map_add, map_add, hx, hy]

/-- Two functions out of `M ⊗ N` which are additive and agree on pure tensors agree. -/
theorem fun_ext {X : Type*} [AddCommGroup X] {f g : TT M N → X}
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ m n, f (tmul M N m n) = g (tmul M N m n)) (t : TT M N) : f t = g t := by
  refine induction_on (P := fun t => f t = g t) t ?_ h fun x y hx hy => by
    beta_reduce at hx hy ⊢; rw [hf, hg, hx, hy]
  beta_reduce
  have h1 := hf 0 0; have h2 := hg 0 0
  rw [add_zero] at h1 h2
  rw [left_eq_add.1 h1, left_eq_add.1 h2]

/-- Two ring maps out of `M ⊗ N` agreeing on pure tensors agree. -/
theorem ringHom_ext {X : Type*} [CommRing X] {f g : TT M N →+* X}
    (h : ∀ m n, f (tmul M N m n) = g (tmul M N m n)) : f = g :=
  RingHom.ext fun t => fun_ext (map_add f) (map_add g) h t

/-! #### Maps out of the tensor product -/

/-- **Ring maps out of `M ⊗ N`**: `m ⊗ n ↦ f m * g n`, for ring maps `f`, `g` agreeing on `B`. -/
def liftRingHom {X : Type u} [CommRing X] (f : M.T →+* X) (g : N.T →+* X)
    (h : ∀ b, f (M.right b) = g (N.left b)) : TT M N →+* X :=
  letI := M.algR; letI := N.algL
  letI : Algebra B X := (f.comp M.right).toAlgebra
  (Algebra.TensorProduct.productMap
    { f with commutes' := fun _ => rfl }
    { g with commutes' := fun b => (h b).symm }).toRingHom

theorem liftRingHom_tmul {X : Type u} [CommRing X] (f : M.T →+* X) (g : N.T →+* X)
    (h : ∀ b, f (M.right b) = g (N.left b)) (m : M.T) (n : N.T) :
    liftRingHom f g h (tmul M N m n) = f m * g n := rfl

/-- **Additive maps out of `M ⊗ N`** from balanced biadditive maps. -/
def liftAdd {X : Type*} [AddCommGroup X] (φ : M.T →+ N.T →+ X)
    (h : ∀ m b n, φ (M.right b * m) n = φ m (N.left b * n)) : TT M N →+ X :=
  letI := M.algR; letI := N.algL
  TensorProduct.liftAddHom φ fun b m n => h m b n

theorem liftAdd_tmul {X : Type*} [AddCommGroup X] (φ : M.T →+ N.T →+ X)
    (h : ∀ m b n, φ (M.right b * m) n = φ m (N.left b * n)) (m : M.T) (n : N.T) :
    liftAdd φ h (tmul M N m n) = φ m n := by
  letI := M.algR; letI := N.algL
  exact TensorProduct.liftAddHom_tmul φ _ m n

/-- The tensor product of two additive maps, `f` right `B`-linear and `g` left `B`-linear. -/
def mapAdd {M' : BRing A B} {N' : BRing B C} (f : M.T →+ M'.T) (g : N.T →+ N'.T)
    (hf : ∀ b x, f (M.right b * x) = M'.right b * f x)
    (hg : ∀ b x, g (N.left b * x) = N'.left b * g x) : TT M N →+ TT M' N' :=
  liftAdd
    { toFun := fun m =>
        { toFun := fun n => tmul M' N' (f m) (g n)
          map_zero' := by simp
          map_add' := fun n n' => by rw [map_add, tmul_add] }
      map_zero' := by ext; simp
      map_add' := fun m m' => by ext; simp [add_tmul] }
    (fun m b n => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hf, hg, tmul_balance])

theorem mapAdd_tmul {M' : BRing A B} {N' : BRing B C} (f : M.T →+ M'.T) (g : N.T →+ N'.T)
    (hf : ∀ b x, f (M.right b * x) = M'.right b * f x)
    (hg : ∀ b x, g (N.left b * x) = N'.left b * g x) (m : M.T) (n : N.T) :
    mapAdd f g hf hg (tmul M N m n) = tmul M' N' (f m) (g n) :=
  liftAdd_tmul _ _ m n

end Tensor

end BRing

/-! ### Bimodule maps -/

/-- **A map of `(A, B)`-bimodules** `M → N`. -/
structure BHom {A B : Type u} [CommRing A] [CommRing B] (M N : BRing A B) where
  /-- The underlying function. -/
  toFun : M.T → N.T
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_left : ∀ a x, toFun (M.left a * x) = N.left a * toFun x
  map_right : ∀ b x, toFun (M.right b * x) = N.right b * toFun x

namespace BHom

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable {M N P Q : BRing A B}

instance : CoeFun (BHom M N) (fun _ => M.T → N.T) := ⟨BHom.toFun⟩

@[ext] theorem ext {φ ψ : BHom M N} (h : ∀ x, φ x = ψ x) : φ = ψ := by
  cases φ; cases ψ; congr; funext x; exact h x

/-- The underlying additive map. -/
def toAddHom (φ : BHom M N) : M.T →+ N.T where
  toFun := φ
  map_zero' := by
    have := φ.map_add 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  map_add' := φ.map_add

@[simp] theorem toAddHom_apply (φ : BHom M N) (x : M.T) : φ.toAddHom x = φ x := rfl

@[simp] theorem map_zero (φ : BHom M N) : φ 0 = 0 := φ.toAddHom.map_zero

theorem map_neg (φ : BHom M N) (x : M.T) : φ (-x) = -φ x := φ.toAddHom.map_neg x

theorem map_sub (φ : BHom M N) (x y : M.T) : φ (x - y) = φ x - φ y := φ.toAddHom.map_sub x y

theorem map_sum (φ : BHom M N) {ι : Type*} (s : Finset ι) (f : ι → M.T) :
    φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) :=
  _root_.map_sum φ.toAddHom f s

/-- The identity. -/
protected def id (M : BRing A B) : BHom M M := ⟨id, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

@[simp] theorem id_apply (x : M.T) : BHom.id M x = x := rfl

/-- Composition (`φ` first, then `ψ`). -/
def comp (ψ : BHom N P) (φ : BHom M N) : BHom M P where
  toFun x := ψ (φ x)
  map_add x y := by simp only [φ.map_add, ψ.map_add]
  map_left a x := by simp only [φ.map_left, ψ.map_left]
  map_right b x := by simp only [φ.map_right, ψ.map_right]

@[simp] theorem comp_apply (ψ : BHom N P) (φ : BHom M N) (x : M.T) : ψ.comp φ x = ψ (φ x) := rfl

theorem comp_assoc (χ : BHom P Q) (ψ : BHom N P) (φ : BHom M N) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := rfl

instance : Add (BHom M N) where
  add φ ψ :=
    { toFun := fun x => φ x + ψ x
      map_add := fun x y => by rw [φ.map_add, ψ.map_add]; abel
      map_left := fun a x => by rw [φ.map_left, ψ.map_left, mul_add]
      map_right := fun b x => by rw [φ.map_right, ψ.map_right, mul_add] }

instance : Neg (BHom M N) where
  neg φ :=
    { toFun := fun x => -φ x
      map_add := fun x y => by rw [φ.map_add, neg_add]
      map_left := fun a x => by rw [φ.map_left, mul_neg]
      map_right := fun b x => by rw [φ.map_right, mul_neg] }

instance : Sub (BHom M N) where
  sub φ ψ :=
    { toFun := fun x => φ x - ψ x
      map_add := fun x y => by rw [φ.map_add, ψ.map_add]; abel
      map_left := fun a x => by rw [φ.map_left, ψ.map_left, mul_sub]
      map_right := fun b x => by rw [φ.map_right, ψ.map_right, mul_sub] }

instance : Zero (BHom M N) where
  zero :=
    { toFun := fun _ => 0
      map_add := fun _ _ => (add_zero 0).symm
      map_left := fun _ _ => (mul_zero _).symm
      map_right := fun _ _ => (mul_zero _).symm }

@[simp] theorem zero_apply (x : M.T) : (0 : BHom M N) x = 0 := rfl

@[simp] theorem add_apply (φ ψ : BHom M N) (x : M.T) : (φ + ψ) x = φ x + ψ x := rfl
@[simp] theorem neg_apply (φ : BHom M N) (x : M.T) : (-φ) x = -φ x := rfl
@[simp] theorem sub_apply (φ ψ : BHom M N) (x : M.T) : (φ - ψ) x = φ x - ψ x := rfl

/-- Multiplication by an element of the (commutative) ring `M.T` is a bimodule map. -/
def mulB (m : M.T) : BHom M M where
  toFun x := m * x
  map_add x y := mul_add m x y
  map_left _ _ := mul_left_comm _ _ _
  map_right _ _ := mul_left_comm _ _ _

@[simp] theorem mulB_apply (m x : M.T) : mulB m x = m * x := rfl

theorem mulB_comp_mulB (m m' : M.T) : (mulB m).comp (mulB m') = mulB (m * m') := by
  ext x; simp [mul_assoc]

theorem mulB_one : mulB (1 : M.T) = BHom.id M := by ext x; simp

/-! #### Whiskering -/

variable {D : Type u} [CommRing D]

/-- **Right whiskering** `φ ⊗ 1_N : M ⊗ N → M' ⊗ N`. -/
def whiskerRight {M M' : BRing A B} (φ : BHom M M') (N : BRing B C) :
    BHom (M.tensor N) (M'.tensor N) where
  toFun := BRing.mapAdd φ.toAddHom (AddMonoidHom.id N.T) φ.map_right (fun _ _ => rfl)
  map_add x y := _root_.map_add _ x y
  map_left a x := by
    refine BRing.induction_on (P := fun x => BRing.mapAdd φ.toAddHom (AddMonoidHom.id N.T)
      φ.map_right (fun _ _ => rfl) ((M.tensor N).left a * x) = (M'.tensor N).left a *
      BRing.mapAdd φ.toAddHom (AddMonoidHom.id N.T) φ.map_right (fun _ _ => rfl) x) x (by simp)
      (fun m n => ?_) (fun x y hx hy => ?_)
    · beta_reduce
      rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul, BRing.mapAdd_tmul, BRing.mapAdd_tmul,
        BRing.tensor_left, BRing.tmul_mul_tmul, one_mul]
      simp only [toAddHom_apply, AddMonoidHom.id_apply, φ.map_left]
    · beta_reduce at hx hy ⊢
      rw [mul_add, _root_.map_add, hx, hy, _root_.map_add, mul_add]
  map_right c x := by
    refine BRing.induction_on (P := fun x => BRing.mapAdd φ.toAddHom (AddMonoidHom.id N.T)
      φ.map_right (fun _ _ => rfl) ((M.tensor N).right c * x) = (M'.tensor N).right c *
      BRing.mapAdd φ.toAddHom (AddMonoidHom.id N.T) φ.map_right (fun _ _ => rfl) x) x (by simp)
      (fun m n => ?_) (fun x y hx hy => ?_)
    · beta_reduce
      rw [BRing.tensor_right, BRing.tmul_mul_tmul, one_mul, BRing.mapAdd_tmul, BRing.mapAdd_tmul,
        BRing.tensor_right, BRing.tmul_mul_tmul, one_mul]
      rfl
    · beta_reduce at hx hy ⊢
      rw [mul_add, _root_.map_add, hx, hy, _root_.map_add, mul_add]

theorem whiskerRight_tmul {M M' : BRing A B} (φ : BHom M M') (N : BRing B C) (m : M.T)
    (n : N.T) : whiskerRight φ N (BRing.tmul M N m n) = BRing.tmul M' N (φ m) n :=
  BRing.mapAdd_tmul (M := M) (N := N) (M' := M') (N' := N) φ.toAddHom (AddMonoidHom.id N.T)
    φ.map_right (fun _ _ => rfl) m n

/-- **Left whiskering** `1_M ⊗ ψ : M ⊗ N → M ⊗ N'`. -/
def whiskerLeft (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') :
    BHom (M.tensor N) (M.tensor N') where
  toFun := BRing.mapAdd (AddMonoidHom.id M.T) ψ.toAddHom (fun _ _ => rfl) ψ.map_left
  map_add x y := _root_.map_add _ x y
  map_left a x := by
    refine BRing.induction_on (P := fun x => BRing.mapAdd (AddMonoidHom.id M.T) ψ.toAddHom
      (fun _ _ => rfl) ψ.map_left ((M.tensor N).left a * x) = (M.tensor N').left a *
      BRing.mapAdd (AddMonoidHom.id M.T) ψ.toAddHom (fun _ _ => rfl) ψ.map_left x) x (by simp)
      (fun m n => ?_) (fun x y hx hy => ?_)
    · beta_reduce
      rw [BRing.tensor_left, BRing.tmul_mul_tmul, one_mul, BRing.mapAdd_tmul, BRing.mapAdd_tmul,
        BRing.tensor_left, BRing.tmul_mul_tmul, one_mul]
      rfl
    · beta_reduce at hx hy ⊢
      rw [mul_add, _root_.map_add, hx, hy, _root_.map_add, mul_add]
  map_right c x := by
    refine BRing.induction_on (P := fun x => BRing.mapAdd (AddMonoidHom.id M.T) ψ.toAddHom
      (fun _ _ => rfl) ψ.map_left ((M.tensor N).right c * x) = (M.tensor N').right c *
      BRing.mapAdd (AddMonoidHom.id M.T) ψ.toAddHom (fun _ _ => rfl) ψ.map_left x) x (by simp)
      (fun m n => ?_) (fun x y hx hy => ?_)
    · beta_reduce
      rw [BRing.tensor_right, BRing.tmul_mul_tmul, one_mul, BRing.mapAdd_tmul, BRing.mapAdd_tmul,
        BRing.tensor_right, BRing.tmul_mul_tmul, one_mul]
      simp only [toAddHom_apply, AddMonoidHom.id_apply, ψ.map_right]
    · beta_reduce at hx hy ⊢
      rw [mul_add, _root_.map_add, hx, hy, _root_.map_add, mul_add]

theorem whiskerLeft_tmul (M : BRing A B) {N N' : BRing B C} (ψ : BHom N N') (m : M.T)
    (n : N.T) : whiskerLeft M ψ (BRing.tmul M N m n) = BRing.tmul M N' m (ψ n) :=
  BRing.mapAdd_tmul (M := M) (N := N) (M' := M) (N' := N') (AddMonoidHom.id M.T) ψ.toAddHom
    (fun _ _ => rfl) ψ.map_left m n

/-- Maps out of a tensor product agree if they agree on pure tensors. -/
theorem ext_tensor {M : BRing A B} {N : BRing B C} {P : BRing A C} {φ ψ : BHom (M.tensor N) P}
    (h : ∀ m n, φ (BRing.tmul M N m n) = ψ (BRing.tmul M N m n)) : φ = ψ :=
  ext fun t => BRing.fun_ext φ.map_add ψ.map_add h t

theorem whiskerRight_comp {M M' M'' : BRing A B} (φ : BHom M M') (φ' : BHom M' M'')
    (N : BRing B C) : whiskerRight (φ'.comp φ) N = (whiskerRight φ' N).comp (whiskerRight φ N) :=
  ext_tensor fun m n => by simp only [comp_apply, whiskerRight_tmul]

theorem whiskerLeft_comp (M : BRing A B) {N N' N'' : BRing B C} (ψ : BHom N N')
    (ψ' : BHom N' N'') : whiskerLeft M (ψ'.comp ψ) = (whiskerLeft M ψ').comp (whiskerLeft M ψ) :=
  ext_tensor fun m n => by simp only [comp_apply, whiskerLeft_tmul]

theorem whiskerRight_id (M : BRing A B) (N : BRing B C) :
    whiskerRight (BHom.id M) N = BHom.id (M.tensor N) :=
  ext_tensor fun m n => by rw [whiskerRight_tmul]; rfl

theorem whiskerLeft_id (M : BRing A B) (N : BRing B C) :
    whiskerLeft M (BHom.id N) = BHom.id (M.tensor N) :=
  ext_tensor fun m n => by rw [whiskerLeft_tmul]; rfl

theorem whiskerRight_add {M M' : BRing A B} (φ ψ : BHom M M') (N : BRing B C) :
    whiskerRight (φ + ψ) N = whiskerRight φ N + whiskerRight ψ N :=
  ext_tensor fun m n => by
    simp only [add_apply, whiskerRight_tmul, BRing.add_tmul]

theorem whiskerLeft_add (M : BRing A B) {N N' : BRing B C} (φ ψ : BHom N N') :
    whiskerLeft M (φ + ψ) = whiskerLeft M φ + whiskerLeft M ψ :=
  ext_tensor fun m n => by
    simp only [add_apply, whiskerLeft_tmul, BRing.tmul_add]

theorem whiskerRight_neg {M M' : BRing A B} (φ : BHom M M') (N : BRing B C) :
    whiskerRight (-φ) N = -whiskerRight φ N :=
  ext_tensor fun m n => by simp only [neg_apply, whiskerRight_tmul, BRing.neg_tmul]

theorem whiskerLeft_neg (M : BRing A B) {N N' : BRing B C} (φ : BHom N N') :
    whiskerLeft M (-φ) = -whiskerLeft M φ :=
  ext_tensor fun m n => by simp only [neg_apply, whiskerLeft_tmul, BRing.tmul_neg]

theorem whiskerRight_sub {M M' : BRing A B} (φ ψ : BHom M M') (N : BRing B C) :
    whiskerRight (φ - ψ) N = whiskerRight φ N - whiskerRight ψ N :=
  ext_tensor fun m n => by simp only [sub_apply, whiskerRight_tmul, BRing.sub_tmul]

theorem whiskerLeft_sub (M : BRing A B) {N N' : BRing B C} (φ ψ : BHom N N') :
    whiskerLeft M (φ - ψ) = whiskerLeft M φ - whiskerLeft M ψ :=
  ext_tensor fun m n => by simp only [sub_apply, whiskerLeft_tmul, BRing.tmul_sub]

theorem whiskerRight_zero {M M' : BRing A B} (N : BRing B C) :
    whiskerRight (0 : BHom M M') N = 0 :=
  ext_tensor fun m n => by simp only [zero_apply, whiskerRight_tmul, BRing.zero_tmul]

theorem whiskerLeft_zero (M : BRing A B) {N N' : BRing B C} :
    whiskerLeft M (0 : BHom N N') = 0 :=
  ext_tensor fun m n => by simp only [zero_apply, whiskerLeft_tmul, BRing.tmul_zero]

theorem mulB_sub (x y : M.T) : mulB (x - y) = mulB x - mulB y := by
  ext z; simp [sub_mul]

theorem mulB_add (x y : M.T) : mulB (x + y) = mulB x + mulB y := by
  ext z; simp [add_mul]

theorem whiskerRight_mulB {M : BRing A B} (x : M.T) (N : BRing B C) :
    whiskerRight (mulB x) N = mulB (BRing.tmul M N x 1) :=
  ext_tensor fun m n => by
    rw [whiskerRight_tmul, mulB_apply, mulB_apply, BRing.tmul_mul_tmul, one_mul]

theorem whiskerLeft_mulB (M : BRing A B) {N : BRing B C} (y : N.T) :
    whiskerLeft M (mulB y) = mulB (BRing.tmul M N 1 y) :=
  ext_tensor fun m n => by
    rw [whiskerLeft_tmul, mulB_apply, mulB_apply, BRing.tmul_mul_tmul, one_mul]

/-- **The interchange law** for whiskering. -/
theorem whisker_exchange {M M' : BRing A B} {N N' : BRing B C} (φ : BHom M M') (ψ : BHom N N') :
    (whiskerLeft M' ψ).comp (whiskerRight φ N) = (whiskerRight φ N').comp (whiskerLeft M ψ) :=
  ext_tensor fun m n => by
    simp only [comp_apply, whiskerRight_tmul, whiskerLeft_tmul]

end BHom

/-! ### Isomorphisms, the associator and the unitors -/

/-- An isomorphism of bimodules. -/
structure BIso {A B : Type u} [CommRing A] [CommRing B] (M N : BRing A B) where
  /-- The forward map. -/
  hom : BHom M N
  /-- The inverse map. -/
  inv : BHom N M
  inv_hom : ∀ x, inv (hom x) = x
  hom_inv : ∀ y, hom (inv y) = y

namespace BIso

variable {A B : Type u} [CommRing A] [CommRing B] {M N P : BRing A B}

/-- The identity isomorphism. -/
protected def refl (M : BRing A B) : BIso M M :=
  ⟨BHom.id M, BHom.id M, fun _ => rfl, fun _ => rfl⟩

/-- The inverse isomorphism. -/
protected def symm (e : BIso M N) : BIso N M := ⟨e.inv, e.hom, e.hom_inv, e.inv_hom⟩

/-- Composition of isomorphisms. -/
protected def trans (e : BIso M N) (f : BIso N P) : BIso M P :=
  ⟨f.hom.comp e.hom, e.inv.comp f.inv, fun x => by simp [f.inv_hom, e.inv_hom],
    fun y => by simp [e.hom_inv, f.hom_inv]⟩

/-- An isomorphism given by a ring isomorphism compatible with both actions. -/
def ofRingEquiv (e : M.T ≃+* N.T) (hl : ∀ a, e (M.left a) = N.left a)
    (hr : ∀ b, e (M.right b) = N.right b) : BIso M N where
  hom := ⟨e, map_add e, fun a x => by rw [map_mul, hl], fun b x => by rw [map_mul, hr]⟩
  inv := ⟨e.symm, map_add e.symm,
    fun a x => by rw [map_mul, ← hl, RingEquiv.symm_apply_apply],
    fun b x => by rw [map_mul, ← hr, RingEquiv.symm_apply_apply]⟩
  inv_hom x := e.symm_apply_apply x
  hom_inv y := e.apply_symm_apply y

end BIso

namespace BRing

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

section Assoc

variable (M : BRing A B) (N : BRing B C) (P : BRing C D)

/-- The forward associator as a ring map `(M ⊗ N) ⊗ P → M ⊗ (N ⊗ P)`. -/
def assocHom : TT (M.tensor N) P →+* TT M (N.tensor P) :=
  liftRingHom
    (liftRingHom (inclL M (N.tensor P)) ((inclR M (N.tensor P)).comp (inclL N P))
      (fun b => by
        show inclL M (N.tensor P) (M.right b) = inclR M (N.tensor P) (inclL N P (N.left b))
        rw [inclL_apply, inclL_apply (M := N) (N := P), inclR_apply]
        exact tmul_right_one (M := M) (N := N.tensor P) b))
    ((inclR M (N.tensor P)).comp (inclR N P))
    (fun c => by
      show inclL M (N.tensor P) 1 * inclR M (N.tensor P) (inclL N P (N.right c)) =
        inclR M (N.tensor P) (inclR N P (P.left c))
      rw [map_one, one_mul, inclL_apply (M := N) (N := P), inclR_apply (M := N) (N := P),
        tmul_right_one (M := N) (N := P) c])

/-- The inverse associator as a ring map `M ⊗ (N ⊗ P) → (M ⊗ N) ⊗ P`. -/
def assocInv : TT M (N.tensor P) →+* TT (M.tensor N) P :=
  liftRingHom ((inclL (M.tensor N) P).comp (inclL M N))
    (liftRingHom ((inclL (M.tensor N) P).comp (inclR M N)) (inclR (M.tensor N) P)
      (fun c => by
        show inclL (M.tensor N) P (inclR M N (N.right c)) = inclR (M.tensor N) P (P.left c)
        rw [inclR_apply (M := M) (N := N), inclL_apply, inclR_apply]
        exact tmul_right_one (M := M.tensor N) (N := P) c))
    (fun b => by
      show inclL (M.tensor N) P (inclL M N (M.right b)) =
        inclL (M.tensor N) P (inclR M N (N.left b)) * inclR (M.tensor N) P 1
      rw [map_one, mul_one, inclL_apply (M := M) (N := N), inclR_apply (M := M) (N := N),
        tmul_right_one (M := M) (N := N) b])

variable {M N P}

theorem assocHom_tmul (m : M.T) (n : N.T) (p : P.T) :
    assocHom M N P (tmul (M.tensor N) P (tmul M N m n) p) =
      tmul M (N.tensor P) m (tmul N P n p) := by
  show inclL M (N.tensor P) m * inclR M (N.tensor P) (inclL N P n) *
    inclR M (N.tensor P) (inclR N P p) = _
  rw [inclL_apply, inclR_apply, inclR_apply, inclL_apply, inclR_apply, tmul_mul_tmul, tmul_mul_tmul,
    mul_one, mul_one, one_mul, tmul_mul_tmul, mul_one, one_mul]

theorem assocInv_tmul (m : M.T) (n : N.T) (p : P.T) :
    assocInv M N P (tmul M (N.tensor P) m (tmul N P n p)) =
      tmul (M.tensor N) P (tmul M N m n) p := by
  show inclL (M.tensor N) P (inclL M N m) * (inclL (M.tensor N) P (inclR M N n) *
    inclR (M.tensor N) P p) = _
  rw [inclL_apply, inclL_apply, inclL_apply, inclR_apply, inclR_apply, tmul_mul_tmul, tmul_mul_tmul,
    mul_one, one_mul, one_mul, tmul_mul_tmul, mul_one, one_mul]

variable (M N P)

theorem assocInv_assocHom : (assocInv M N P).comp (assocHom M N P) = RingHom.id _ := by
  refine ringHom_ext fun x p => ?_
  refine induction_on (P := fun x => (assocInv M N P).comp (assocHom M N P)
    (tmul (M.tensor N) P x p) = RingHom.id _ (tmul (M.tensor N) P x p)) x (by simp)
    (fun m n => ?_) (fun x y hx hy => ?_)
  · simp only [RingHom.comp_apply, assocHom_tmul, assocInv_tmul, RingHom.id_apply]
  · beta_reduce at hx hy ⊢
    rw [add_tmul, map_add, hx, hy, ← map_add, ← add_tmul]

theorem assocHom_assocInv : (assocHom M N P).comp (assocInv M N P) = RingHom.id _ := by
  refine ringHom_ext fun m x => ?_
  refine induction_on (P := fun x => (assocHom M N P).comp (assocInv M N P)
    (tmul M (N.tensor P) m x) = RingHom.id _ (tmul M (N.tensor P) m x)) x (by simp)
    (fun n p => ?_) (fun x y hx hy => ?_)
  · simp only [RingHom.comp_apply, assocHom_tmul, assocInv_tmul, RingHom.id_apply]
  · beta_reduce at hx hy ⊢
    rw [tmul_add, map_add, hx, hy, ← map_add, ← tmul_add]

/-- **The associator** `(M ⊗ N) ⊗ P ≅ M ⊗ (N ⊗ P)`. -/
def assoc : BIso ((M.tensor N).tensor P) (M.tensor (N.tensor P)) :=
  BIso.ofRingEquiv (RingEquiv.ofHomInv (assocHom M N P) (assocInv M N P) (assocInv_assocHom M N P)
      (assocHom_assocInv M N P))
    (fun a => by
      show assocHom M N P (tmul _ _ (tmul M N (M.left a) 1) 1) = tmul M _ (M.left a) 1
      rw [assocHom_tmul]; rfl)
    (fun d => by
      show assocHom M N P (tmul _ _ 1 (P.right d)) = tmul M _ 1 (tmul N P 1 (P.right d))
      rw [one_eq (M := M) (N := N), assocHom_tmul])

theorem assoc_hom_tmul (m : M.T) (n : N.T) (p : P.T) :
    (assoc M N P).hom (tmul (M.tensor N) P (tmul M N m n) p) =
      tmul M (N.tensor P) m (tmul N P n p) :=
  assocHom_tmul m n p

theorem assoc_inv_tmul (m : M.T) (n : N.T) (p : P.T) :
    (assoc M N P).inv (tmul M (N.tensor P) m (tmul N P n p)) =
      tmul (M.tensor N) P (tmul M N m n) p :=
  assocInv_tmul m n p

end Assoc

section Unitors

variable (M : BRing A B)

/-- The ring map `M ⊗_B B → M`, `m ⊗ b ↦ m b`. -/
def ridHom : TT M (idB B) →+* M.T := liftRingHom (RingHom.id M.T) M.right (fun _ => rfl)

/-- The ring map `A ⊗_A M → M`, `a ⊗ m ↦ a m`. -/
def lidHom : TT (idB A) M →+* M.T := liftRingHom M.left (RingHom.id M.T) (fun _ => rfl)

theorem ridHom_tmul (m : M.T) (b : B) : ridHom M (tmul M (idB B) m b) = m * M.right b := rfl

theorem lidHom_tmul (a : A) (m : M.T) : lidHom M (tmul (idB A) M a m) = M.left a * m := rfl

theorem inclL_comp_ridHom : (inclL M (idB B)).comp (ridHom M) = RingHom.id _ :=
  ringHom_ext fun m b => by
    rw [RingHom.comp_apply, ridHom_tmul, inclL_apply, RingHom.id_apply, mul_comm, tmul_balance]
    exact congrArg _ (mul_one b)

theorem ridHom_comp_inclL : (ridHom M).comp (inclL M (idB B)) = RingHom.id _ :=
  RingHom.ext fun m => by
    rw [RingHom.comp_apply, inclL_apply, ridHom_tmul, map_one, mul_one, RingHom.id_apply]

theorem inclR_comp_lidHom : (inclR (idB A) M).comp (lidHom M) = RingHom.id _ :=
  ringHom_ext fun a m => by
    rw [RingHom.comp_apply, lidHom_tmul, inclR_apply, RingHom.id_apply,
      ← tmul_balance (M := idB A) (N := M) 1 a m]
    exact congrArg (tmul _ _ · m) (mul_one a)

theorem lidHom_comp_inclR : (lidHom M).comp (inclR (idB A) M) = RingHom.id _ :=
  RingHom.ext fun m => by
    rw [RingHom.comp_apply, inclR_apply, lidHom_tmul, map_one, one_mul, RingHom.id_apply]

/-- **The right unitor** `M ⊗_B B ≅ M`: `m ⊗ b ↦ m b`. -/
def ridIso : BIso (M.tensor (idB B)) M :=
  BIso.ofRingEquiv (RingEquiv.ofHomInv (ridHom M) (inclL M (idB B)) (inclL_comp_ridHom M)
      (ridHom_comp_inclL M))
    (fun a => by
      show ridHom M (tmul M (idB B) (M.left a) 1) = _
      rw [ridHom_tmul, map_one, mul_one])
    (fun b => by
      show ridHom M (tmul M (idB B) 1 b) = _
      rw [ridHom_tmul, one_mul])

/-- **The left unitor** `A ⊗_A M ≅ M`: `a ⊗ m ↦ a m`. -/
def lidIso : BIso ((idB A).tensor M) M :=
  BIso.ofRingEquiv (RingEquiv.ofHomInv (lidHom M) (inclR (idB A) M) (inclR_comp_lidHom M)
      (lidHom_comp_inclR M))
    (fun a => by
      show lidHom M (tmul (idB A) M a 1) = _
      rw [lidHom_tmul, mul_one])
    (fun c => by
      show lidHom M (tmul (idB A) M 1 (M.right c)) = _
      rw [lidHom_tmul, map_one, one_mul])

theorem ridIso_hom_tmul (m : M.T) (b : B) : (ridIso M).hom (tmul M (idB B) m b) = m * M.right b :=
  rfl

theorem ridIso_inv (m : M.T) : (ridIso M).inv m = tmul M (idB B) m 1 := rfl

theorem lidIso_hom_tmul (a : A) (m : M.T) : (lidIso M).hom (tmul (idB A) M a m) = M.left a * m :=
  rfl

theorem lidIso_inv (m : M.T) : (lidIso M).inv m = tmul (idB A) M 1 m := rfl

end Unitors

end BRing

end Categorification.Flag

end
