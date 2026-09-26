/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Tensor

/-!
# External tensor products of modules

For `k`-algebras `A`, `B`, a left `A`-module `P` and a left `B`-module `Q`, the tensor product
`P ⊗[k] Q` is a left `A ⊗[k] B`-module, `(a ⊗ b)(p ⊗ q) = (a p) ⊗ (b q)`. This is the external
tensor product `P ⊠ Q` used by Khovanov–Lauda I (arXiv:0803.4121v2, §2.6, §3.1) to define the
product `[Ind_{ν,ν'} (P ⊠ Q)]` on Grothendieck groups.

Since Mathlib deliberately does not make `Module (A ⊗[k] B) (P ⊗[k] Q)` an instance (it would
create diamonds, e.g. for `P = A`, `Q = B`), we use a type synonym `ExtTensor k P Q`.

## Main definitions and results

* `ExtTensor k P Q`, `ExtTensor.tmul p q`, `ExtTensor.smul_tmul`
  (`(a ⊗ b) • (p ⊗ q) = (a • p) ⊗ (b • q)`).
* `ExtTensor.map f g` (for `A`-linear `f`, `B`-linear `g`), `ExtTensor.congr`,
  `ExtTensor.prodLeft : (P × P') ⊠ Q ≃ P ⊠ Q × P' ⊠ Q`.
* `ExtTensor.finsuppEquiv : (X →₀ A) ⊠ (Y →₀ B) ≃ (X × Y →₀ A ⊗ B)`.
* `ExtTensor.projective`, `ExtTensor.finite` : `P ⊠ Q` is finitely generated projective over
  `A ⊗ B` if `P` and `Q` are.
* Gradings: `ExtTensor.grading 𝒰 𝒱` (the tensor product grading, a `Decomposition`), graded for
  the tensor product grading of `A ⊗ B` (`ExtTensor.gradedSMul`), compatible with shifts
  (`grading_shift_left`, `grading_shift_right`), and preserved by `map` and `prodLeft`.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct

variable (k : Type*) [CommRing k]
  (P : Type*) [AddCommGroup P] [Module k P] (Q : Type*) [AddCommGroup Q] [Module k Q]

/-- The external tensor product `P ⊠ Q`, a type synonym for `P ⊗[k] Q`, carrying the
`A ⊗[k] B`-module structure. -/
def ExtTensor : Type _ := P ⊗[k] Q

namespace ExtTensor

instance : AddCommGroup (ExtTensor k P Q) := inferInstanceAs (AddCommGroup (P ⊗[k] Q))

instance : Module k (ExtTensor k P Q) := inferInstanceAs (Module k (P ⊗[k] Q))

variable {k P Q}

/-- The identification with `P ⊗[k] Q`. -/
def equivTensor : ExtTensor k P Q ≃ₗ[k] P ⊗[k] Q := LinearEquiv.refl k _

/-- `p ⊗ q` as an element of `P ⊠ Q`. -/
def tmul (p : P) (q : Q) : ExtTensor k P Q := p ⊗ₜ[k] q

@[elab_as_elim]
theorem induction_on {motive : ExtTensor k P Q → Prop} (x : ExtTensor k P Q) (zero : motive 0)
    (tmul : ∀ p q, motive (tmul p q)) (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  TensorProduct.induction_on (motive := motive) x zero tmul add

theorem tmul_add (p : P) (q q' : Q) : (tmul p (q + q') : ExtTensor k P Q) = tmul p q + tmul p q' :=
  TensorProduct.tmul_add _ _ _

theorem add_tmul (p p' : P) (q : Q) : (tmul (p + p') q : ExtTensor k P Q) = tmul p q + tmul p' q :=
  TensorProduct.add_tmul _ _ _

/-- The universal property of `P ⊠ Q` as a `k`-module. -/
def lift {M : Type*} [AddCommGroup M] [Module k M] (f : P →ₗ[k] Q →ₗ[k] M) :
    ExtTensor k P Q →ₗ[k] M :=
  TensorProduct.lift f

@[simp] theorem lift_tmul {M : Type*} [AddCommGroup M] [Module k M] (f : P →ₗ[k] Q →ₗ[k] M)
    (p : P) (q : Q) : lift f (tmul p q : ExtTensor k P Q) = f p q := rfl

/-- `p ↦ p ⊗ q` for fixed `q`. -/
def mkRight (q : Q) : P →ₗ[k] ExtTensor k P Q := (TensorProduct.mk k P Q).flip q

@[simp] theorem mkRight_apply (q : Q) (p : P) : mkRight (k := k) q p = tmul p q := rfl

theorem smul_tmul' (c : k) (p : P) (q : Q) :
    c • (tmul p q : ExtTensor k P Q) = tmul (c • p) q :=
  TensorProduct.smul_tmul' _ _ _

theorem tmul_smul (c : k) (p : P) (q : Q) :
    (tmul p (c • q) : ExtTensor k P Q) = c • tmul p q :=
  TensorProduct.tmul_smul _ _ _

@[simp] theorem zero_tmul (q : Q) : (tmul (0 : P) q : ExtTensor k P Q) = 0 :=
  TensorProduct.zero_tmul _ _

@[simp] theorem tmul_zero (p : P) : (tmul p (0 : Q) : ExtTensor k P Q) = 0 :=
  TensorProduct.tmul_zero _ _

section Action

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [Module A P] [IsScalarTower k A P] [Module B Q] [IsScalarTower k B Q]

variable (k P Q) in
/-- The action of `A` on the left factor. -/
def actL : A →ₐ[k] Module.End k (P ⊗[k] Q) where
  toFun a := TensorProduct.map (DistribMulAction.toLinearMap k P a) LinearMap.id
  map_one' := by ext; simp
  map_mul' a a' := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  map_add' a a' := by ext; simp [add_smul, TensorProduct.add_tmul]
  commutes' c := by ext; simp [algebraMap_smul, TensorProduct.smul_tmul']

variable (k P Q) in
/-- The action of `B` on the right factor. -/
def actR : B →ₐ[k] Module.End k (P ⊗[k] Q) where
  toFun b := TensorProduct.map LinearMap.id (DistribMulAction.toLinearMap k Q b)
  map_one' := by ext; simp
  map_mul' b b' := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  map_add' b b' := by ext; simp [add_smul, TensorProduct.tmul_add]
  commutes' c := by ext; simp [algebraMap_smul, TensorProduct.tmul_smul]

variable (k P Q A B) in
/-- The action of `A ⊗[k] B` on `P ⊗[k] Q`. -/
def action : A ⊗[k] B →ₐ[k] Module.End k (P ⊗[k] Q) :=
  Algebra.TensorProduct.lift (actL k P Q) (actR k P Q) fun a b => by
    ext p q; simp [actL, actR]

theorem action_tmul (a : A) (b : B) (p : P) (q : Q) :
    action k P Q A B (a ⊗ₜ b) (p ⊗ₜ q) = (a • p) ⊗ₜ (b • q) := by
  simp [action, actL, actR]

instance : Module (A ⊗[k] B) (ExtTensor k P Q) :=
  Module.compHom (P ⊗[k] Q) (action k P Q A B).toRingHom

theorem smul_def (t : A ⊗[k] B) (x : ExtTensor k P Q) :
    t • x = action k P Q A B t (equivTensor x) := rfl

@[simp] theorem smul_tmul (a : A) (b : B) (p : P) (q : Q) :
    (a ⊗ₜ[k] b) • (tmul p q : ExtTensor k P Q) = tmul (a • p) (b • q) :=
  action_tmul a b p q

instance : IsScalarTower k (A ⊗[k] B) (ExtTensor k P Q) where
  smul_assoc c t x := by
    rw [smul_def, smul_def, map_smul]
    rfl

/-! ### Functoriality -/

variable {P' Q' P'' Q'' : Type*} [AddCommGroup P'] [Module k P'] [Module A P']
  [IsScalarTower k A P'] [AddCommGroup Q'] [Module k Q'] [Module B Q'] [IsScalarTower k B Q']
  [AddCommGroup P''] [Module k P''] [Module A P''] [IsScalarTower k A P'']
  [AddCommGroup Q''] [Module k Q''] [Module B Q''] [IsScalarTower k B Q'']

theorem smul_eq_induction {Z : Type*} [AddCommGroup Z] [Module (A ⊗[k] B) Z]
    {F : ExtTensor k P Q → Z}
    (hadd : ∀ x y, F (x + y) = F x + F y) (h0 : F 0 = 0)
    (htmul : ∀ (a : A) (b : B) (p : P) (q : Q),
      F ((a ⊗ₜ[k] b) • tmul p q) = (a ⊗ₜ[k] b) • F (tmul p q))
    (t : A ⊗[k] B) (x : ExtTensor k P Q) : F (t • x) = t • F x := by
  induction t using TensorProduct.induction_on with
  | zero => rw [zero_smul, zero_smul, h0]
  | tmul a b =>
    induction x using induction_on with
    | zero => rw [smul_zero, h0, smul_zero]
    | tmul p q => exact htmul a b p q
    | add x y hx hy => rw [smul_add, hadd, hx, hy, hadd, smul_add]
  | add s t hs ht => rw [add_smul, hadd, hs, ht, add_smul]

/-- `f ⊠ g` for an `A`-linear `f` and a `B`-linear `g`. -/
def map (f : P →ₗ[A] P') (g : Q →ₗ[B] Q') :
    ExtTensor k P Q →ₗ[A ⊗[k] B] ExtTensor k P' Q' where
  toFun := TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)
  map_add' := map_add _
  map_smul' t x := smul_eq_induction (map_add _) (map_zero _)
    (fun a b p q => by
      rw [smul_tmul]
      show tmul (f (a • p)) (g (b • q)) = (a ⊗ₜ[k] b) • tmul (f p) (g q)
      rw [smul_tmul, map_smul, map_smul]) t x

@[simp] theorem map_tmul (f : P →ₗ[A] P') (g : Q →ₗ[B] Q') (p : P) (q : Q) :
    map (k := k) f g (tmul p q) = tmul (f p) (g q) := rfl

theorem map_id :
    map (k := k) (LinearMap.id : P →ₗ[A] P) (LinearMap.id : Q →ₗ[B] Q) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | zero => simp
  | tmul p q => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem map_comp (f : P →ₗ[A] P') (g : Q →ₗ[B] Q') (f' : P' →ₗ[A] P'') (g' : Q' →ₗ[B] Q'') :
    map (k := k) (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | zero => simp
  | tmul p q => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- `f ⊠ g` for isomorphisms. -/
def congr (f : P ≃ₗ[A] P') (g : Q ≃ₗ[B] Q') :
    ExtTensor k P Q ≃ₗ[A ⊗[k] B] ExtTensor k P' Q' :=
  LinearEquiv.ofLinear (map f.toLinearMap g.toLinearMap) (map f.symm.toLinearMap g.symm.toLinearMap)
    (by rw [← map_comp]; simp [map_id]) (by rw [← map_comp]; simp [map_id])

@[simp] theorem congr_tmul (f : P ≃ₗ[A] P') (g : Q ≃ₗ[B] Q') (p : P) (q : Q) :
    congr (k := k) f g (tmul p q) = tmul (f p) (g q) := rfl

theorem map_surjective {f : P →ₗ[A] P'} {g : Q →ₗ[B] Q'} (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Function.Surjective (map (k := k) f g) := by
  intro y
  induction y using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul p q =>
    obtain ⟨p, rfl⟩ := hf p
    obtain ⟨q, rfl⟩ := hg q
    exact ⟨tmul p q, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

variable (k P P' Q A B) in
/-- `(P × P') ⊠ Q ≃ (P ⊠ Q) × (P' ⊠ Q)`. -/
def prodLeft :
    ExtTensor k (P × P') Q ≃ₗ[A ⊗[k] B] ExtTensor k P Q × ExtTensor k P' Q :=
  LinearEquiv.ofLinear
    (LinearMap.prod (map (LinearMap.fst A P P') LinearMap.id)
      (map (LinearMap.snd A P P') LinearMap.id))
    (LinearMap.coprod (map (LinearMap.inl A P P') LinearMap.id)
      (map (LinearMap.inr A P P') LinearMap.id))
    (by
      apply LinearMap.prod_ext <;> apply LinearMap.ext <;> intro x <;>
      induction x using induction_on with
      | zero => simp
      | tmul p q =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
          LinearMap.inr_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Pi.prod, map_tmul,
          LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_coe, id_eq, zero_tmul, map_zero,
          add_zero, zero_add, map_add]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (by
      apply LinearMap.ext
      intro x
      induction x using induction_on with
      | zero => simp
      | tmul p q =>
        obtain ⟨p, p'⟩ := p
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.prod_apply, Pi.prod,
          map_tmul, LinearMap.coprod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.id_coe, id_eq]
        rw [← add_tmul, Prod.mk_add_mk, add_zero, zero_add]
      | add x y hx hy => rw [map_add, map_add, hx, hy])

@[simp] theorem prodLeft_tmul (p : P × P') (q : Q) :
    prodLeft (k := k) (P := P) (P' := P') (Q := Q) (A := A) (B := B) (tmul p q) =
      (tmul p.1 q, tmul p.2 q) := rfl

variable (k P Q Q' A B) in
/-- `P ⊠ (Q × Q') ≃ (P ⊠ Q) × (P ⊠ Q')`. -/
def prodRight :
    ExtTensor k P (Q × Q') ≃ₗ[A ⊗[k] B] ExtTensor k P Q × ExtTensor k P Q' :=
  LinearEquiv.ofLinear
    (LinearMap.prod (map LinearMap.id (LinearMap.fst B Q Q'))
      (map LinearMap.id (LinearMap.snd B Q Q')))
    (LinearMap.coprod (map LinearMap.id (LinearMap.inl B Q Q'))
      (map LinearMap.id (LinearMap.inr B Q Q')))
    (by
      apply LinearMap.prod_ext <;> apply LinearMap.ext <;> intro x <;>
      induction x using induction_on with
      | zero => simp
      | tmul p q =>
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
          LinearMap.inr_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Pi.prod, map_tmul,
          LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.id_coe, id_eq, tmul_zero, map_zero,
          add_zero, zero_add, map_add]
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (by
      apply LinearMap.ext
      intro x
      induction x using induction_on with
      | zero => simp
      | tmul p q =>
        obtain ⟨q, q'⟩ := q
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.prod_apply, Pi.prod,
          map_tmul, LinearMap.coprod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.id_coe, id_eq]
        rw [← tmul_add, Prod.mk_add_mk, add_zero, zero_add]
      | add x y hx hy => rw [map_add, map_add, hx, hy])

@[simp] theorem prodRight_tmul (p : P) (q : Q × Q') :
    prodRight (k := k) (P := P) (Q := Q) (Q' := Q') (A := A) (B := B) (tmul p q) =
      (tmul p q.1, tmul p q.2) := rfl

variable (k A B) in
/-- `A ⊠ B ≃ A ⊗ B` as left `A ⊗ B`-modules. -/
def selfEquiv : ExtTensor k A B ≃ₗ[A ⊗[k] B] A ⊗[k] B where
  __ := (equivTensor (k := k) (P := A) (Q := B))
  map_smul' t x := by
    refine smul_eq_induction (F := fun x => (equivTensor (k := k) (P := A) (Q := B)) x)
      (map_add _) (map_zero _) ?_ t x
    intro a b p q
    rw [smul_tmul]
    exact (Algebra.TensorProduct.tmul_mul_tmul a p b q).symm

@[simp] theorem selfEquiv_tmul (a : A) (b : B) :
    selfEquiv k A B (tmul a b) = a ⊗ₜ[k] b := rfl

/-! ### Free modules, projectivity, finite generation -/

variable (k A B) in
/-- `(X →₀ A) ⊠ (Y →₀ B) ≃ (X × Y →₀ A ⊗ B)`. -/
def finsuppEquiv (X Y : Type*) :
    ExtTensor k (X →₀ A) (Y →₀ B) ≃ₗ[A ⊗[k] B] (X × Y →₀ A ⊗[k] B) where
  __ := ((equivTensor (k := k) (P := X →₀ A) (Q := Y →₀ B)).trans
    (finsuppTensorFinsupp k k A B X Y))
  map_smul' t x := by
    refine smul_eq_induction (F := fun x => ((equivTensor (k := k) (P := X →₀ A)
      (Q := Y →₀ B)).trans (finsuppTensorFinsupp k k A B X Y)) x) (map_add _) (map_zero _) ?_ t x
    intro a b f g
    ext ⟨i, j⟩
    simp only [smul_tmul, LinearEquiv.trans_apply, Finsupp.smul_apply, smul_eq_mul]
    show finsuppTensorFinsupp k k A B X Y ((a • f) ⊗ₜ (b • g)) (i, j) =
      (a ⊗ₜ b) * finsuppTensorFinsupp k k A B X Y (f ⊗ₜ g) (i, j)
    rw [finsuppTensorFinsupp_apply, finsuppTensorFinsupp_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- If `P` and `Q` are projective, so is `P ⊠ Q`. -/
theorem projective [Module.Projective A P] [Module.Projective B Q] :
    Module.Projective (A ⊗[k] B) (ExtTensor k P Q) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective A P›
  obtain ⟨t, ht⟩ := Module.projective_def'.1 ‹Module.Projective B Q›
  haveI : Module.Projective (A ⊗[k] B) (P × Q →₀ A ⊗[k] B) := inferInstance
  haveI : Module.Projective (A ⊗[k] B) (ExtTensor k (P →₀ A) (Q →₀ B)) :=
    Module.Projective.of_equiv (finsuppEquiv k A B P Q).symm
  refine Module.Projective.of_split (map s t)
    (map (Finsupp.linearCombination A id) (Finsupp.linearCombination B id)) ?_
  rw [← map_comp, hs, ht, map_id]

/-- If `P` and `Q` are finitely generated, so is `P ⊠ Q`. -/
theorem finite [Module.Finite A P] [Module.Finite B Q] :
    Module.Finite (A ⊗[k] B) (ExtTensor k P Q) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := P)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := B) (M := Q)
  have hsurjS : Function.Surjective (Finsupp.linearCombination A (Subtype.val : S → P)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hS]
  have hsurjT : Function.Surjective (Finsupp.linearCombination B (Subtype.val : T → Q)) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_coe_subtype,
      Finset.setOf_mem, hT]
  exact Module.Finite.of_surjective
    ((map (Finsupp.linearCombination A (Subtype.val : S → P))
      (Finsupp.linearCombination B (Subtype.val : T → Q))).comp
      (finsuppEquiv k A B S T).symm.toLinearMap)
    ((map_surjective hsurjS hsurjT).comp (finsuppEquiv k A B S T).symm.surjective)

end Action

/-! ### Gradings -/

section Grading

open Graded DirectSum

variable {ι : Type*} [AddCommMonoid ι] (𝒰 : ι → Submodule k P) (𝒱 : ι → Submodule k Q)

/-- The tensor product grading of `P ⊠ Q`. -/
def grading : ι → Submodule k (ExtTensor k P Q) := tensorGrading 𝒰 𝒱

variable {𝒰 𝒱} in
theorem tmul_mem_grading {i j : ι} {p : P} {q : Q} (hp : p ∈ 𝒰 i) (hq : q ∈ 𝒱 j) :
    tmul p q ∈ grading 𝒰 𝒱 (i + j) :=
  tmul_mem_tensorGrading hp hq

instance [DecidableEq ι] [Decomposition 𝒰] [Decomposition 𝒱] : Decomposition (grading 𝒰 𝒱) :=
  inferInstanceAs (Decomposition (tensorGrading 𝒰 𝒱))

/-- A `k`-linear map out of `P ⊠ Q` sending each `P_i ⊠ Q_j` into `X_{i+j}` is
degree-preserving. -/
theorem grading_map_mem {X : Type*} [AddCommGroup X] [Module k X] (𝒳 : ι → Submodule k X)
    (f : ExtTensor k P Q →ₗ[k] X)
    (hf : ∀ ⦃i j : ι⦄ ⦃p : P⦄ ⦃q : Q⦄, p ∈ 𝒰 i → q ∈ 𝒱 j → f (tmul p q) ∈ 𝒳 (i + j))
    ⦃d : ι⦄ ⦃x : ExtTensor k P Q⦄ (hx : x ∈ grading 𝒰 𝒱 d) : f x ∈ 𝒳 d :=
  tensorGrading_map_mem 𝒰 𝒱 𝒳 (f.comp (equivTensor.symm.toLinearMap)) hf hx

section Shift

variable {ι : Type*} [AddCommGroup ι] (𝒰 : ι → Submodule k P) (𝒱 : ι → Submodule k Q)

theorem grading_shift_left (a : ι) : grading (shift 𝒰 a) 𝒱 = shift (grading 𝒰 𝒱) a :=
  tensorGrading_shift_left 𝒰 𝒱 a

theorem grading_shift_right (a : ι) : grading 𝒰 (shift 𝒱 a) = shift (grading 𝒰 𝒱) a :=
  tensorGrading_shift_right 𝒰 𝒱 a

end Shift

variable {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [Module A P] [IsScalarTower k A P] [Module B Q] [IsScalarTower k B Q]
  (𝒜 : ι → Submodule k A) (ℬ : ι → Submodule k B)

/-- `P ⊠ Q` is a graded `A ⊗ B`-module for the tensor product gradings. -/
instance gradedSMul [SetLike.GradedSMul 𝒜 𝒰] [SetLike.GradedSMul ℬ 𝒱] :
    SetLike.GradedSMul (tensorGrading 𝒜 ℬ) (grading 𝒰 𝒱) where
  smul_mem i j t x ht hx := by
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨i₁, i₂, a, b, rfl, ha, hb, rfl⟩ := ht
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j₁, j₂, p, q, rfl, hp, hq, rfl⟩ := hx
        have hap : a • p ∈ 𝒰 (i₁ + j₁) := SetLike.GradedSMul.smul_mem ha hp
        have hbq : b • q ∈ 𝒱 (i₂ + j₂) := SetLike.GradedSMul.smul_mem hb hq
        have h := tmul_mem_grading (k := k) hap hbq
        rw [vadd_eq_add, add_add_add_comm]
        show (a ⊗ₜ[k] b) • tmul p q ∈ _
        rw [smul_tmul]
        exact h
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul c x _ hx => rw [smul_comm _ c x]; exact Submodule.smul_mem _ c hx
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ hs ht => rw [add_smul]; exact add_mem hs ht
    | smul c t _ ht => rw [smul_assoc]; exact Submodule.smul_mem _ c ht

variable {P' Q' : Type*} [AddCommGroup P'] [Module k P'] [Module A P']
  [IsScalarTower k A P'] [AddCommGroup Q'] [Module k Q'] [Module B Q'] [IsScalarTower k B Q']
  {𝒰 𝒱} {𝒰' : ι → Submodule k P'} {𝒱' : ι → Submodule k Q'}

/-- `f ⊠ g` is degree-preserving if `f` and `g` are. -/
theorem map_preservesGrading {f : P →ₗ[A] P'} {g : Q →ₗ[B] Q'}
    (hf : PreservesGrading 𝒰 𝒰' f) (hg : PreservesGrading 𝒱 𝒱' g) :
    PreservesGrading (grading 𝒰 𝒱) (grading 𝒰' 𝒱') (map (k := k) f g) :=
  fun _ _ hx => grading_map_mem 𝒰 𝒱 _ ((map f g).restrictScalars k)
    (fun _ _ _ _ hp hq => tmul_mem_grading (hf hp) (hg hq)) hx

end Grading

end ExtTensor

end Categorification
