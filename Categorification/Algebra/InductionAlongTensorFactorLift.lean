/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorAction
import Categorification.Algebra.InductionAlongAssoc

/-!
# Lifting natural isomorphisms to modules over a tensor product

Let `A₀ → A₁`, `A₀ → B₀`, `B₀ → B₁`, `A₁ → B₁` be maps of `k`-algebras and `C` a further
`k`-algebra. Induction and restriction along the maps `· ⊗ C` of one tensor factor are computed
on first factors by `indLeftFactorEquivB` and `resLeftFactorEquiv`, compatibly with the actions
of `C`. Hence a natural isomorphism between composites of induction and restriction over the
first factor lifts to modules over the tensor product:

* `liftResIndEquiv`: from `Res_α Ind_β M ≅ Ind_δ Res_γ M` to
  `Res_{α ⊗ C} Ind_{β ⊗ C} N ≅ Ind_{δ ⊗ C} Res_{γ ⊗ C} N`;
* `liftResIndProdEquiv`: from `Res_β Ind_β M ≅ Ind_γ Res_γ M ⊕ M^n` to the same statement over
  the tensor product;
* `liftIndResProdEquiv`: from `Ind_γ Res_γ M ≅ Res_β Ind_β M ⊕ M^n` likewise.

These give, on modules over `T^{λ₁} ⊗ T^{λ₂}`, the commutation relations between the functors
`₁Eⱼ` and `₁Fᵢ` of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §5, from those on `T^{λ₁}`-modules (the dimension count in the proof of
Proposition 5.5).
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-- Restriction of an isomorphism of modules. -/
def Res.mapEquiv {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B} {M M' : Type w}
    [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M'] (g : M ≃ₗ[B] M') :
    Res φ M ≃ₗ[A] Res φ M' :=
  LinearEquiv.ofLinearMap (Res.map g.toLinearMap) (Res.map g.symm.toLinearMap)
    (LinearMap.ext fun x => Res.ext (by simp)) (LinearMap.ext fun x => Res.ext (by simp))

@[simp] theorem Res.mapEquiv_val {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B} {M M' : Type w}
    [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B M'] (g : M ≃ₗ[B] M')
    (m : Res φ M) : (Res.mapEquiv g m).val = g m.val := rfl

section LeftFactor

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C]
  {A₀ A₁ B₀ B₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring A₁] [Algebra k A₁] [Ring B₀]
  [Algebra k B₀] [Ring B₁] [Algebra k B₁]

/-! ### The two building blocks -/

section Blocks

variable (α : A₁ →ₙ+* B₁) (ψα : A₁ ⊗[k] C →ₙ+* B₁ ⊗[k] C)
  (hψα : ∀ (a : A₁) (c : C), ψα (a ⊗ₜ c) = α a ⊗ₜ c)
  (β : B₀ →ₙ+* B₁) (hβ : ∀ (c : k) (t : B₀), β (c • t) = c • β t)
  (ψβ : B₀ ⊗[k] C →ₙ+* B₁ ⊗[k] C) (hψβ : ∀ (a : B₀) (c : C), ψβ (a ⊗ₜ c) = β a ⊗ₜ c)
  (N : Type w) [AddCommGroup N] [Module k N] [Module (B₀ ⊗[k] C) N]
  [IsScalarTower k (B₀ ⊗[k] C) N]

/-- First factor of a restriction of an induction:
`(Res_{α ⊗ C} Ind_{β ⊗ C} N)|_{A₁} ≅ Res_α Ind_β (N|_{B₀})`. -/
def resIndLeftFactorEquiv :
    LeftFactorRes k A₁ C (Res ψα (IndK k N ψβ)) ≃ₗ[A₁]
      Res α (Ind (LeftFactorRes k B₀ C N) β) :=
  (resLeftFactorEquiv α ψα hψα (IndK k N ψβ)).trans
    (Res.mapEquiv (indLeftFactorEquivB β hβ ψβ hψβ (N := N)))

theorem resIndLeftFactorEquiv_cAct (c : C) (x : LeftFactorRes k A₁ C (Res ψα (IndK k N ψβ))) :
    resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N (leftFactorCAct c x) =
      Res.map (Ind.map (leftFactorCAct c)) (resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N x) := by
  apply Res.ext
  change indLeftFactorEquivB β hβ ψβ hψβ
      (resLeftFactorEquiv α ψα hψα (IndK k N ψβ) (leftFactorCAct c x)).val = _
  rw [resLeftFactorEquiv_cAct, Res.val_map, indLeftFactorEquivB_cAct]
  rfl

end Blocks

section Blocks'

variable (γ : A₀ →ₙ+* B₀) (ψγ : A₀ ⊗[k] C →ₙ+* B₀ ⊗[k] C)
  (hψγ : ∀ (a : A₀) (c : C), ψγ (a ⊗ₜ c) = γ a ⊗ₜ c)
  (δ : A₀ →ₙ+* A₁) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : A₀ ⊗[k] C →ₙ+* A₁ ⊗[k] C) (hψδ : ∀ (a : A₀) (c : C), ψδ (a ⊗ₜ c) = δ a ⊗ₜ c)
  (N : Type w) [AddCommGroup N] [Module (B₀ ⊗[k] C) N]
  [Module k (Res ψγ N)] [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)]

/-- First factor of an induction of a restriction:
`(Ind_{δ ⊗ C} Res_{γ ⊗ C} N)|_{A₁} ≅ Ind_δ Res_γ (N|_{B₀})`. -/
def indResLeftFactorEquiv :
    LeftFactorRes k A₁ C (IndK k (Res ψγ N) ψδ) ≃ₗ[A₁]
      Ind (Res γ (LeftFactorRes k B₀ C N)) δ :=
  (indLeftFactorEquivB δ hδ ψδ hψδ (N := Res ψγ N)).trans
    (Ind.mapEquiv (resLeftFactorEquiv γ ψγ hψγ N))

theorem indResLeftFactorEquiv_cAct (c : C) (x : LeftFactorRes k A₁ C (IndK k (Res ψγ N) ψδ)) :
    indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N (leftFactorCAct c x) =
      Ind.map (Res.map (leftFactorCAct c)) (indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N x) := by
  change Ind.mapEquiv (resLeftFactorEquiv γ ψγ hψγ N)
      (indLeftFactorEquivB δ hδ ψδ hψδ (leftFactorCAct c x)) = _
  rw [indLeftFactorEquivB_cAct]
  change (Ind.map (resLeftFactorEquiv γ ψγ hψγ N).toLinearMap).comp
      (Ind.map (leftFactorCAct c)) _ =
    (Ind.map (Res.map (leftFactorCAct c))).comp
      (Ind.map (resLeftFactorEquiv γ ψγ hψγ N).toLinearMap) _
  rw [← Ind.map_comp, ← Ind.map_comp]
  congr 2
  exact LinearMap.ext fun y => resLeftFactorEquiv_cAct γ ψγ hψγ N c y

end Blocks'

/-! ### Lifting -/

variable (α : A₁ →ₙ+* B₁) (ψα : A₁ ⊗[k] C →ₙ+* B₁ ⊗[k] C)
  (hψα : ∀ (a : A₁) (c : C), ψα (a ⊗ₜ c) = α a ⊗ₜ c)
  (β : B₀ →ₙ+* B₁) (hβ : ∀ (c : k) (t : B₀), β (c • t) = c • β t)
  (ψβ : B₀ ⊗[k] C →ₙ+* B₁ ⊗[k] C) (hψβ : ∀ (a : B₀) (c : C), ψβ (a ⊗ₜ c) = β a ⊗ₜ c)
  (γ : A₀ →ₙ+* B₀) (ψγ : A₀ ⊗[k] C →ₙ+* B₀ ⊗[k] C)
  (hψγ : ∀ (a : A₀) (c : C), ψγ (a ⊗ₜ c) = γ a ⊗ₜ c)
  (δ : A₀ →ₙ+* A₁) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : A₀ ⊗[k] C →ₙ+* A₁ ⊗[k] C) (hψδ : ∀ (a : A₀) (c : C), ψδ (a ⊗ₜ c) = δ a ⊗ₜ c)

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ Ind_δ Res_γ`** to modules over the tensor
product with `C`. -/
def liftResIndEquiv
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module B₀ M],
      Res α (Ind M β) ≃ₗ[A₁] Ind (Res γ M) δ)
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module B₀ M] [AddCommGroup M'] [Module B₀ M']
      (f : M →ₗ[B₀] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = Ind.map (Res.map f) (Φ M x))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (B₀ ⊗[k] C) N]
    [IsScalarTower k (B₀ ⊗[k] C) N] [Module k (Res ψγ N)]
    [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] :
    Res ψα (IndK k N ψβ) ≃ₗ[A₁ ⊗[k] C] IndK k (Res ψγ N) ψδ :=
  linearEquivOfLeftFactor
    (((resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (LeftFactorRes k B₀ C N))).trans
      (indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).symm)
    (fun c x => by
      apply (indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [indResLeftFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        resIndLeftFactorEquiv_cAct, hΦ])

theorem liftResIndEquiv_apply
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module B₀ M],
      Res α (Ind M β) ≃ₗ[A₁] Ind (Res γ M) δ)
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module B₀ M] [AddCommGroup M'] [Module B₀ M']
      (f : M →ₗ[B₀] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = Ind.map (Res.map f) (Φ M x))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (B₀ ⊗[k] C) N]
    [IsScalarTower k (B₀ ⊗[k] C) N] [Module k (Res ψγ N)]
    [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] (x : Res ψα (IndK k N ψβ)) :
    indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N
        (liftResIndEquiv α ψα hψα β hβ ψβ hψβ γ ψγ hψγ δ hδ ψδ hψδ Φ hΦ N x) =
      Φ (LeftFactorRes k B₀ C N) (resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N x) :=
  LinearEquiv.apply_symm_apply _ _

end LeftFactor

/-! ### Lifting with an extra summand -/

section Prod

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C] {A : Type u} [Ring A]
  [Algebra k A] (n : ℕ)

/-- The first factor of `P ⊕ N^n` is `P|_A ⊕ (N|_A)^n`. -/
def leftFactorProdEquiv (P : Type*) (N : Type w) [AddCommGroup P] [Module (A ⊗[k] C) P]
    [AddCommGroup N] [Module (A ⊗[k] C) N] :
    LeftFactorRes k A C (P × (Fin n → N)) ≃ₗ[A]
      LeftFactorRes k A C P × (Fin n → LeftFactorRes k A C N) where
  toFun x := ((show P × (Fin n → N) from x).1, (show P × (Fin n → N) from x).2)
  invFun y := (show LeftFactorRes k A C (P × (Fin n → N)) from (y.1, y.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftFactorProdEquiv_cAct (P : Type*) (N : Type w) [AddCommGroup P] [Module (A ⊗[k] C) P]
    [AddCommGroup N] [Module (A ⊗[k] C) N] (c : C)
    (x : LeftFactorRes k A C (P × (Fin n → N))) :
    leftFactorProdEquiv n P N (leftFactorCAct c x) =
      (leftFactorCAct c (leftFactorProdEquiv n P N x).1,
        fun s => leftFactorCAct c ((leftFactorProdEquiv n P N x).2 s)) := rfl

variable {A₀ B₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring B₁] [Algebra k B₁]
  (α : A →ₙ+* B₁) (ψα : A ⊗[k] C →ₙ+* B₁ ⊗[k] C)
  (hψα : ∀ (a : A) (c : C), ψα (a ⊗ₜ c) = α a ⊗ₜ c)
  (β : A →ₙ+* B₁) (hβ : ∀ (c : k) (t : A), β (c • t) = c • β t)
  (ψβ : A ⊗[k] C →ₙ+* B₁ ⊗[k] C) (hψβ : ∀ (a : A) (c : C), ψβ (a ⊗ₜ c) = β a ⊗ₜ c)
  (γ : A₀ →ₙ+* A) (ψγ : A₀ ⊗[k] C →ₙ+* A ⊗[k] C)
  (hψγ : ∀ (a : A₀) (c : C), ψγ (a ⊗ₜ c) = γ a ⊗ₜ c)
  (δ : A₀ →ₙ+* A) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : A₀ ⊗[k] C →ₙ+* A ⊗[k] C) (hψδ : ∀ (a : A₀) (c : C), ψδ (a ⊗ₜ c) = δ a ⊗ₜ c)

/-- First factor of `Ind_{δ ⊗ C} Res_{γ ⊗ C} N ⊕ N^n`. -/
def indResProdLeftFactorEquiv (N : Type w) [AddCommGroup N] [Module (A ⊗[k] C) N]
    [Module k (Res ψγ N)] [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] :
    LeftFactorRes k A C (IndK k (Res ψγ N) ψδ × (Fin n → N)) ≃ₗ[A]
      Ind (Res γ (LeftFactorRes k A C N)) δ × (Fin n → LeftFactorRes k A C N) :=
  (leftFactorProdEquiv n _ N).trans (LinearEquiv.prodCongr
    (indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N)
    (LinearEquiv.refl A (Fin n → LeftFactorRes k A C N)))

theorem indResProdLeftFactorEquiv_cAct (N : Type w) [AddCommGroup N] [Module (A ⊗[k] C) N]
    [Module k (Res ψγ N)] [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] (c : C)
    (x : LeftFactorRes k A C (IndK k (Res ψγ N) ψδ × (Fin n → N))) :
    indResProdLeftFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N (leftFactorCAct c x) =
      (Ind.map (Res.map (leftFactorCAct c))
          (indResProdLeftFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N x).1,
        fun s => leftFactorCAct c ((indResProdLeftFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N x).2 s)) :=
  Prod.ext (indResLeftFactorEquiv_cAct γ ψγ hψγ δ hδ ψδ hψδ N c _) rfl

/-- First factor of `Res_{α ⊗ C} Ind_{β ⊗ C} N ⊕ N^n`. -/
def resIndProdLeftFactorEquiv (N : Type w) [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
    [IsScalarTower k (A ⊗[k] C) N] :
    LeftFactorRes k A C (Res ψα (IndK k N ψβ) × (Fin n → N)) ≃ₗ[A]
      Res α (Ind (LeftFactorRes k A C N) β) × (Fin n → LeftFactorRes k A C N) :=
  (leftFactorProdEquiv n _ N).trans (LinearEquiv.prodCongr
    (resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N)
    (LinearEquiv.refl A (Fin n → LeftFactorRes k A C N)))

theorem resIndProdLeftFactorEquiv_cAct (N : Type w) [AddCommGroup N] [Module k N]
    [Module (A ⊗[k] C) N] [IsScalarTower k (A ⊗[k] C) N] (c : C)
    (x : LeftFactorRes k A C (Res ψα (IndK k N ψβ) × (Fin n → N))) :
    resIndProdLeftFactorEquiv n α ψα hψα β hβ ψβ hψβ N (leftFactorCAct c x) =
      (Res.map (Ind.map (leftFactorCAct c))
          (resIndProdLeftFactorEquiv n α ψα hψα β hβ ψβ hψβ N x).1,
        fun s => leftFactorCAct c ((resIndProdLeftFactorEquiv n α ψα hψα β hβ ψβ hψβ N x).2 s)) :=
  Prod.ext (resIndLeftFactorEquiv_cAct α ψα hψα β hβ ψβ hψβ N c _) rfl

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ Ind_δ Res_γ ⊕ id^n`** to modules over the
tensor product with `C`. -/
def liftResIndProdEquiv
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module A M],
      Res α (Ind M β) ≃ₗ[A] Ind (Res γ M) δ × (Fin n → M))
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) =
        (Ind.map (Res.map f) (Φ M x).1, fun s => f ((Φ M x).2 s)))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
    [IsScalarTower k (A ⊗[k] C) N] [Module k (Res ψγ N)]
    [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] :
    Res ψα (IndK k N ψβ) ≃ₗ[A ⊗[k] C] IndK k (Res ψγ N) ψδ × (Fin n → N) :=
  linearEquivOfLeftFactor
    (((resIndLeftFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (LeftFactorRes k A C N))).trans
      (indResProdLeftFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N).symm)
    (fun c x => by
      apply (indResProdLeftFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [indResProdLeftFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        resIndLeftFactorEquiv_cAct, hΦ])

/-- **Lifting a natural isomorphism `Ind_δ Res_γ ≅ Res_α Ind_β ⊕ id^n`** to modules over the
tensor product with `C`. -/
def liftIndResProdEquiv
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module A M],
      Ind (Res γ M) δ ≃ₗ[A] Res α (Ind M β) × (Fin n → M))
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Ind (Res γ M) δ),
      Φ M' (Ind.map (Res.map f) x) =
        (Res.map (Ind.map f) (Φ M x).1, fun s => f ((Φ M x).2 s)))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (A ⊗[k] C) N]
    [IsScalarTower k (A ⊗[k] C) N] [Module k (Res ψγ N)]
    [IsScalarTower k (A₀ ⊗[k] C) (Res ψγ N)] :
    IndK k (Res ψγ N) ψδ ≃ₗ[A ⊗[k] C] Res ψα (IndK k N ψβ) × (Fin n → N) :=
  linearEquivOfLeftFactor
    (((indResLeftFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).trans (Φ (LeftFactorRes k A C N))).trans
      (resIndProdLeftFactorEquiv n α ψα hψα β hβ ψβ hψβ N).symm)
    (fun c x => by
      apply (resIndProdLeftFactorEquiv n α ψα hψα β hβ ψβ hψβ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [resIndProdLeftFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        indResLeftFactorEquiv_cAct, hΦ])

end Prod

end InductionAlong

end

end Categorification
