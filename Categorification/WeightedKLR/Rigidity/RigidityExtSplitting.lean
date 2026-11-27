/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.NilHeckeFullSplitting
import Categorification.WeightedKLR.Rigidity.RigidityExtBicone

/-!
# A projective `A e` as a sum of copies of `A e'`

Input for B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
§7.1, Corollary 7.7: the projective `R e(î)` of the expansion `î` of a divided-power word `i` is a
sum of `i!` copies of the projective `R e_i` of the divided-power idempotent (M. Khovanov,
A. Lauda, arXiv:0803.4121v2, §2.5), ungraded and for every `Q`.

* `Graded.IsSplitting.map_mul`: splittings are preserved by additive multiplicative maps.
* `lIdealSplitProj`, `lIdealSplitIncl`, `lIdealBicone`: a splitting `E' = ∑_j a_j b_j`,
  `b_i a_j = δ_{ij} E`, makes `A E'` a biproduct of copies of `A E`.
* `ModuleCat.biconeOfLinear`: a bicone over a constant family of modules from linear maps.
* `lIdealHomEquiv`: `Hom_A(A E, M) ≅ {m | E m = m}`, `k`-linearly.
* `KLRAlgebra.exists_isSplitting_e`: `e(î)` splits through the divided-power idempotent
  `divIdem î bs` in `n_1! ⋯ n_r!` terms.
-/

noncomputable section

namespace Categorification

open CategoryTheory Limits

namespace Graded.IsSplitting

variable {A B : Type*} [Ring A] [Ring B] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E' : A} {E a b : ι → A}

/-- The image of a splitting under an additive multiplicative map. -/
theorem map_mul (h : IsSplitting E' E a b) (φ : A →+ B) (hφ : ∀ x y, φ (x * y) = φ x * φ y) :
    IsSplitting (φ E') (fun j => φ (E j)) (fun j => φ (a j)) (fun j => φ (b j)) where
  mul_eq i j := by
    rw [← hφ, h.mul_eq]
    split_ifs <;> simp
  sum_eq := by simp_rw [← hφ, ← map_sum, h.sum_eq]

/-- The trivial splitting of an idempotent through itself. -/
theorem refl {E : A} (hE : IsIdempotentElem E) :
    IsSplitting E (fun _ : Unit => E) (fun _ => E) (fun _ => E) where
  mul_eq _ _ := by simp [hE.eq]
  sum_eq := by simp [hE.eq]

end Graded.IsSplitting

/-! ### `A E'` as a sum of copies of `A E` -/

section LIdeal

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι] {E' E : A} {a b : ι → A}
  (h : Graded.IsSplitting E' (fun _ => E) a b)

/-- The projection `A E' → A E`, `y ↦ y a_j`. -/
def lIdealSplitProj (j : ι) : lIdeal E' →ₗ[A] lIdeal E where
  toFun y := ⟨y.1 * a j, by
    rw [mem_lIdeal, mul_assoc, ← h.left_mul_a j, ← mul_assoc, y.2]⟩
  map_add' y y' := Subtype.ext (add_mul _ _ _)
  map_smul' r y := Subtype.ext (mul_assoc _ _ _)

/-- The inclusion `A E → A E'`, `w ↦ w b_j`. -/
def lIdealSplitIncl (j : ι) : lIdeal E →ₗ[A] lIdeal E' where
  toFun w := ⟨w.1 * b j, by
    rw [mem_lIdeal, mul_assoc, h.b_mul_right j, ← mul_assoc, w.2]⟩
  map_add' w w' := Subtype.ext (add_mul _ _ _)
  map_smul' r w := Subtype.ext (mul_assoc _ _ _)

theorem lIdealSplitProj_comp_incl (i j : ι) :
    (lIdealSplitProj h j).comp (lIdealSplitIncl h i) = if i = j then LinearMap.id else 0 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  change w.1 * b i * a j = _
  rw [mul_assoc, h.mul_eq]
  split_ifs
  · exact w.2
  · rw [mul_zero]; rfl

theorem sum_lIdealSplitIncl_comp_proj :
    ∑ j, (lIdealSplitIncl h j).comp (lIdealSplitProj h j) = LinearMap.id := by
  refine LinearMap.ext fun y => Subtype.ext ?_
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  change ∑ j, y.1 * a j * b j = y.1
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, h.sum_eq, y.2]

end LIdeal

/-! ### Bicones of modules from linear maps -/

section ModuleBicone

universe u v

variable {R : Type u} [Ring R] {J : Type*} [Fintype J] [DecidableEq J] {X Y : ModuleCat.{v} R}

/-- A bicone over the constant family `Y` with point `X`, from linear maps `ι_j : Y → X`,
`π_j : X → Y` with `π_j ι_i = δ_{ij}`. -/
def moduleBiconeOfLinear (ι : J → (Y →ₗ[R] X)) (π : J → (X →ₗ[R] Y))
    (h : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0) :
    Bicone (fun _ : J => Y) :=
  Bicone.ofConst (fun j => ModuleCat.ofHom (ι j)) (fun j => ModuleCat.ofHom (π j)) fun i j => by
    refine ModuleCat.hom_ext ?_
    change (π j).comp (ι i) = _
    rw [h]
    split_ifs <;> rfl

omit [Fintype J] in
theorem moduleBiconeOfLinear_pt (ι : J → (Y →ₗ[R] X)) (π : J → (X →ₗ[R] Y))
    (h : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0) :
    (moduleBiconeOfLinear ι π h).pt = X := rfl

/-- `moduleBiconeOfLinear` is a bilimit when `∑_j ι_j π_j = 1`. -/
def moduleBiconeOfLinearIsBilimit (ι : J → (Y →ₗ[R] X)) (π : J → (X →ₗ[R] Y))
    (h : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id) : (moduleBiconeOfLinear ι π h).IsBilimit :=
  Bicone.ofConstIsBilimit _ _ _ (by
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_sum]
    change ∑ j, (ι j).comp (π j) = _
    exact htot)

end ModuleBicone

section LIdealBicone

universe u

variable {A : Type u} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι] {E' E : A} {a b : ι → A}
  (h : Graded.IsSplitting E' (fun _ => E) a b)

/-- The bicone exhibiting `A E'` as a sum of copies of `A E`. -/
def lIdealBicone : Bicone (fun _ : ι => ModuleCat.of A (lIdeal E)) :=
  moduleBiconeOfLinear (X := ModuleCat.of A (lIdeal E')) (lIdealSplitIncl h)
    (lIdealSplitProj h) (lIdealSplitProj_comp_incl h)

theorem lIdealBicone_pt : (lIdealBicone h).pt = ModuleCat.of A (lIdeal E') := rfl

/-- `lIdealBicone` is a bilimit. -/
def lIdealBiconeIsBilimit : (lIdealBicone h).IsBilimit :=
  moduleBiconeOfLinearIsBilimit _ _ _ (sum_lIdealSplitIncl_comp_proj h)

end LIdealBicone

/-! ### Maps out of `A E` -/

section Hom

universe u

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] {E : A}
  (hE : IsIdempotentElem E) (M : ModuleCat.{u} A)

/-- The elements of `M` fixed by `E`, as a `k`-subspace. -/
def fixedSubspace (E : A) : Submodule k M where
  carrier := {m | E • m = m}
  add_mem' {x y} hx hy := by
    change E • (x + y) = x + y
    rw [smul_add, hx, hy]
  zero_mem' := smul_zero E
  smul_mem' c x hx := by
    change E • (c • x) = c • x
    rw [smul_comm, hx]

/-- `Hom_A(A E, M) ≅ {m ∈ M | E m = m}`, `f ↦ f(E)`. -/
def lIdealHomEquiv : (ModuleCat.of A (lIdeal E) ⟶ M) ≃ₗ[k] fixedSubspace (k := k) M E where
  toFun f := ⟨f.hom ⟨E, hE.eq⟩, by
    change E • f.hom ⟨E, hE.eq⟩ = f.hom ⟨E, hE.eq⟩
    rw [← LinearMap.map_smul]
    exact congrArg f.hom (Subtype.ext hE.eq)⟩
  invFun m := ModuleCat.ofHom
    { toFun := fun y => (y.1 : A) • (m.1 : M)
      map_add' := fun y y' => add_smul _ _ _
      map_smul' := fun r y => mul_smul _ _ _ }
  left_inv f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    change (y.1 : A) • f.hom ⟨E, hE.eq⟩ = f.hom y
    rw [← LinearMap.map_smul]
    exact congrArg f.hom (Subtype.ext y.2)
  right_inv m := Subtype.ext m.2
  map_add' f g := rfl
  map_smul' c f := rfl

end Hom

/-! ### `e(î)` splits through the divided-power idempotent -/

namespace KLR.KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν

/-- The splitting of `1_{…i⋯i…}` through `1_{…i^{(N)}…}` in `N!` terms. -/
theorem exists_isSplitting_block {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs) :
    ∀ {N : ℕ}, IsBlocks i ((p, N) :: bs) →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → A),
        Graded.IsSplitting (divIdem i bs) (fun _ => divIdem i ((p, N) :: bs)) a b ∧
          Fintype.card ι = N.factorial
  | 0, h => by
    have he : (divIdem i ((p, 0) :: bs) : A) = divIdem i bs := by
      rw [divIdem, divIdem, blocksElt_cons]; simp only; rw [blockElt_zero, one_mul]
    rw [he]
    exact ⟨Unit, inferInstance, inferInstance, _, _,
      Graded.IsSplitting.refl (isIdempotentElem_divIdem hbs), rfl⟩
  | N + 1, h => by
    obtain ⟨ι, _, _, a, b, hS, hc⟩ := exists_isSplitting_block hbs (h.cons_mono (Nat.le_succ N))
    refine ⟨ι × Fin (N + 1), inferInstance, inferInstance, _, _,
      hS.trans (isSplitting_divIdem_succ h) (isIdempotentElem_divIdem h)
        (isIdempotentElem_divIdem hbs), ?_⟩
    rw [Fintype.card_prod, hc, Fintype.card_fin, Nat.factorial_succ, mul_comm]

/-- **`e(î)` splits through `1_i`** (Khovanov–Lauda, arXiv:0803.4121v2, §2.5, ungraded and for
every `Q`): `e(î) = ∑_j a_j b_j` with `b_{j'} a_j = δ_{j' j} 1_i`, in `n_1! ⋯ n_r!` terms. -/
theorem exists_isSplitting_e {t : Seq ν} :
    ∀ {bs : List (ℕ × ℕ)}, IsBlocks t bs →
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → A),
        Graded.IsSplitting (e t) (fun _ => divIdem t bs) a b ∧
          Fintype.card ι = (bs.map fun b => b.2.factorial).prod
  | [], h => by
    rw [divIdem_nil]
    exact ⟨Unit, inferInstance, inferInstance, _, _,
      Graded.IsSplitting.refl (isIdempotentElem_iff.mpr (e_mul_self t)), rfl⟩
  | c :: bs, h => by
    obtain ⟨ι, _, _, a, b, hS, hc⟩ := exists_isSplitting_e h.tail
    obtain ⟨κ, _, _, a', b', hS', hc'⟩ :=
      exists_isSplitting_block (k := k) (Q := Q) (p := c.1) (N := c.2) h.tail h
    refine ⟨ι × κ, inferInstance, inferInstance, _, _,
      hS.trans hS' (isIdempotentElem_divIdem h) (isIdempotentElem_iff.mpr (e_mul_self t)), ?_⟩
    rw [Fintype.card_prod, hc, hc', List.map_cons, List.prod_cons, mul_comm]

end KLR.KLRAlgebra

end Categorification
