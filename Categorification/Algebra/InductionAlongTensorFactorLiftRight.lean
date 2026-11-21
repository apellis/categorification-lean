/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorLift

/-!
# Lifting natural isomorphisms to modules over a tensor product: the second factor

The mirror image of `InductionAlongTensorFactorLift`. Let `A₀ → A₁`, `A₀ → B₀`, `B₀ → B₁`,
`A₁ → B₁` be maps of `k`-algebras and `C` a further `k`-algebra. Induction and restriction along
the maps `C ⊗ ·` of the second tensor factor are computed on second factors by
`indRightFactorEquivB` and `resRightFactorEquiv`, compatibly with the actions of `C`. Hence a
natural isomorphism between composites of induction and restriction over the second factor
lifts to modules over `C ⊗ A`:

* `liftResIndEquivRight`: from `Res_α Ind_β M ≅ Ind_δ Res_γ M` to
  `Res_{C ⊗ α} Ind_{C ⊗ β} N ≅ Ind_{C ⊗ δ} Res_{C ⊗ γ} N`;
* `liftResIndProdEquivRight`: from `Res_β Ind_β M ≅ Ind_γ Res_γ M ⊕ M^n` to the same statement
  over the tensor product;
* `liftIndResProdEquivRight`: from `Ind_γ Res_γ M ≅ Res_β Ind_β M ⊕ M^n` likewise.

These give, on modules over `T^{λ'} ⊗ R^{λ_ℓ}`, the commutation relations between the functors
`₂Eⱼ` and `₂Fᵢ` of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Theorem 4.31, in the proof of Proposition 5.5.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

section RightFactor

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C]
  {A₀ A₁ B₀ B₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring A₁] [Algebra k A₁] [Ring B₀]
  [Algebra k B₀] [Ring B₁] [Algebra k B₁]

/-! ### The two building blocks -/

section BlocksRight

variable (α : A₁ →ₙ+* B₁) (ψα : C ⊗[k] A₁ →ₙ+* C ⊗[k] B₁)
  (hψα : ∀ (c : C) (a : A₁), ψα (c ⊗ₜ a) = c ⊗ₜ α a)
  (β : B₀ →ₙ+* B₁) (hβ : ∀ (c : k) (t : B₀), β (c • t) = c • β t)
  (ψβ : C ⊗[k] B₀ →ₙ+* C ⊗[k] B₁) (hψβ : ∀ (c : C) (a : B₀), ψβ (c ⊗ₜ a) = c ⊗ₜ β a)
  (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] B₀) N]
  [IsScalarTower k (C ⊗[k] B₀) N]

/-- Second factor of a restriction of an induction:
`(Res_{C ⊗ α} Ind_{C ⊗ β} N)|_{A₁} ≅ Res_α Ind_β (N|_{B₀})`. -/
def resIndRightFactorEquiv :
    RightFactorRes k A₁ C (Res ψα (IndK k N ψβ)) ≃ₗ[A₁]
      Res α (Ind (RightFactorRes k B₀ C N) β) :=
  (resRightFactorEquiv α ψα hψα (IndK k N ψβ)).trans
    (Res.mapEquiv (indRightFactorEquivB β hβ ψβ hψβ (N := N)))

theorem resIndRightFactorEquiv_cAct (c : C) (x : RightFactorRes k A₁ C (Res ψα (IndK k N ψβ))) :
    resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N (rightFactorCAct c x) =
      Res.map (Ind.map (rightFactorCAct c)) (resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N x) := by
  apply Res.ext
  change indRightFactorEquivB β hβ ψβ hψβ
      (resRightFactorEquiv α ψα hψα (IndK k N ψβ) (rightFactorCAct c x)).val = _
  rw [resRightFactorEquiv_cAct, Res.val_map, indRightFactorEquivB_cAct]
  rfl

end BlocksRight

section BlocksRight'

variable (γ : A₀ →ₙ+* B₀) (ψγ : C ⊗[k] A₀ →ₙ+* C ⊗[k] B₀)
  (hψγ : ∀ (c : C) (a : A₀), ψγ (c ⊗ₜ a) = c ⊗ₜ γ a)
  (δ : A₀ →ₙ+* A₁) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : C ⊗[k] A₀ →ₙ+* C ⊗[k] A₁) (hψδ : ∀ (c : C) (a : A₀), ψδ (c ⊗ₜ a) = c ⊗ₜ δ a)
  (N : Type w) [AddCommGroup N] [Module (C ⊗[k] B₀) N]
  [Module k (Res ψγ N)] [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)]

/-- Second factor of an induction of a restriction:
`(Ind_{C ⊗ δ} Res_{C ⊗ γ} N)|_{A₁} ≅ Ind_δ Res_γ (N|_{B₀})`. -/
def indResRightFactorEquiv :
    RightFactorRes k A₁ C (IndK k (Res ψγ N) ψδ) ≃ₗ[A₁]
      Ind (Res γ (RightFactorRes k B₀ C N)) δ :=
  (indRightFactorEquivB δ hδ ψδ hψδ (N := Res ψγ N)).trans
    (Ind.mapEquiv (resRightFactorEquiv γ ψγ hψγ N))

theorem indResRightFactorEquiv_cAct (c : C) (x : RightFactorRes k A₁ C (IndK k (Res ψγ N) ψδ)) :
    indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N (rightFactorCAct c x) =
      Ind.map (Res.map (rightFactorCAct c)) (indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N x) := by
  change Ind.mapEquiv (resRightFactorEquiv γ ψγ hψγ N)
      (indRightFactorEquivB δ hδ ψδ hψδ (rightFactorCAct c x)) = _
  rw [indRightFactorEquivB_cAct]
  change (Ind.map (resRightFactorEquiv γ ψγ hψγ N).toLinearMap).comp
      (Ind.map (rightFactorCAct c)) _ =
    (Ind.map (Res.map (rightFactorCAct c))).comp
      (Ind.map (resRightFactorEquiv γ ψγ hψγ N).toLinearMap) _
  rw [← Ind.map_comp, ← Ind.map_comp]
  congr 2
  exact LinearMap.ext fun y => resRightFactorEquiv_cAct γ ψγ hψγ N c y

end BlocksRight'

/-! ### Lifting -/

variable (α : A₁ →ₙ+* B₁) (ψα : C ⊗[k] A₁ →ₙ+* C ⊗[k] B₁)
  (hψα : ∀ (c : C) (a : A₁), ψα (c ⊗ₜ a) = c ⊗ₜ α a)
  (β : B₀ →ₙ+* B₁) (hβ : ∀ (c : k) (t : B₀), β (c • t) = c • β t)
  (ψβ : C ⊗[k] B₀ →ₙ+* C ⊗[k] B₁) (hψβ : ∀ (c : C) (a : B₀), ψβ (c ⊗ₜ a) = c ⊗ₜ β a)
  (γ : A₀ →ₙ+* B₀) (ψγ : C ⊗[k] A₀ →ₙ+* C ⊗[k] B₀)
  (hψγ : ∀ (c : C) (a : A₀), ψγ (c ⊗ₜ a) = c ⊗ₜ γ a)
  (δ : A₀ →ₙ+* A₁) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : C ⊗[k] A₀ →ₙ+* C ⊗[k] A₁) (hψδ : ∀ (c : C) (a : A₀), ψδ (c ⊗ₜ a) = c ⊗ₜ δ a)

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ Ind_δ Res_γ`** to modules over the tensor
product `C ⊗ A`. -/
def liftResIndEquivRight
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module B₀ M],
      Res α (Ind M β) ≃ₗ[A₁] Ind (Res γ M) δ)
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module B₀ M] [AddCommGroup M'] [Module B₀ M']
      (f : M →ₗ[B₀] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = Ind.map (Res.map f) (Φ M x))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] B₀) N]
    [IsScalarTower k (C ⊗[k] B₀) N] [Module k (Res ψγ N)]
    [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] :
    Res ψα (IndK k N ψβ) ≃ₗ[C ⊗[k] A₁] IndK k (Res ψγ N) ψδ :=
  linearEquivOfRightFactor
    (((resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (RightFactorRes k B₀ C N))).trans
      (indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).symm)
    (fun c x => by
      apply (indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [indResRightFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        resIndRightFactorEquiv_cAct, hΦ])

theorem liftResIndEquivRight_apply
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module B₀ M],
      Res α (Ind M β) ≃ₗ[A₁] Ind (Res γ M) δ)
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module B₀ M] [AddCommGroup M'] [Module B₀ M']
      (f : M →ₗ[B₀] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) = Ind.map (Res.map f) (Φ M x))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] B₀) N]
    [IsScalarTower k (C ⊗[k] B₀) N] [Module k (Res ψγ N)]
    [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] (x : Res ψα (IndK k N ψβ)) :
    indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N
        (liftResIndEquivRight α ψα hψα β hβ ψβ hψβ γ ψγ hψγ δ hδ ψδ hψδ Φ hΦ N x) =
      Φ (RightFactorRes k B₀ C N) (resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N x) :=
  LinearEquiv.apply_symm_apply _ _

end RightFactor

/-! ### Lifting with an extra summand -/

section ProdRight

variable {k : Type*} [CommRing k] {C : Type u} [Ring C] [Algebra k C] {A : Type u} [Ring A]
  [Algebra k A] (n : ℕ)

/-- The second factor of `P ⊕ N^n` is `P|_A ⊕ (N|_A)^n`. -/
def rightFactorProdEquiv (P : Type*) (N : Type w) [AddCommGroup P] [Module (C ⊗[k] A) P]
    [AddCommGroup N] [Module (C ⊗[k] A) N] :
    RightFactorRes k A C (P × (Fin n → N)) ≃ₗ[A]
      RightFactorRes k A C P × (Fin n → RightFactorRes k A C N) where
  toFun x := ((show P × (Fin n → N) from x).1, (show P × (Fin n → N) from x).2)
  invFun y := (show RightFactorRes k A C (P × (Fin n → N)) from (y.1, y.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem rightFactorProdEquiv_cAct (P : Type*) (N : Type w) [AddCommGroup P] [Module (C ⊗[k] A) P]
    [AddCommGroup N] [Module (C ⊗[k] A) N] (c : C)
    (x : RightFactorRes k A C (P × (Fin n → N))) :
    rightFactorProdEquiv n P N (rightFactorCAct c x) =
      (rightFactorCAct c (rightFactorProdEquiv n P N x).1,
        fun s => rightFactorCAct c ((rightFactorProdEquiv n P N x).2 s)) := rfl

variable {A₀ B₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring B₁] [Algebra k B₁]
  (α : A →ₙ+* B₁) (ψα : C ⊗[k] A →ₙ+* C ⊗[k] B₁)
  (hψα : ∀ (c : C) (a : A), ψα (c ⊗ₜ a) = c ⊗ₜ α a)
  (β : A →ₙ+* B₁) (hβ : ∀ (c : k) (t : A), β (c • t) = c • β t)
  (ψβ : C ⊗[k] A →ₙ+* C ⊗[k] B₁) (hψβ : ∀ (c : C) (a : A), ψβ (c ⊗ₜ a) = c ⊗ₜ β a)
  (γ : A₀ →ₙ+* A) (ψγ : C ⊗[k] A₀ →ₙ+* C ⊗[k] A)
  (hψγ : ∀ (c : C) (a : A₀), ψγ (c ⊗ₜ a) = c ⊗ₜ γ a)
  (δ : A₀ →ₙ+* A) (hδ : ∀ (c : k) (t : A₀), δ (c • t) = c • δ t)
  (ψδ : C ⊗[k] A₀ →ₙ+* C ⊗[k] A) (hψδ : ∀ (c : C) (a : A₀), ψδ (c ⊗ₜ a) = c ⊗ₜ δ a)

/-- Second factor of `Ind_{C ⊗ δ} Res_{C ⊗ γ} N ⊕ N^n`. -/
def indResProdRightFactorEquiv (N : Type w) [AddCommGroup N] [Module (C ⊗[k] A) N]
    [Module k (Res ψγ N)] [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] :
    RightFactorRes k A C (IndK k (Res ψγ N) ψδ × (Fin n → N)) ≃ₗ[A]
      Ind (Res γ (RightFactorRes k A C N)) δ × (Fin n → RightFactorRes k A C N) :=
  (rightFactorProdEquiv n _ N).trans (LinearEquiv.prodCongr
    (indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N)
    (LinearEquiv.refl A (Fin n → RightFactorRes k A C N)))

theorem indResProdRightFactorEquiv_cAct (N : Type w) [AddCommGroup N] [Module (C ⊗[k] A) N]
    [Module k (Res ψγ N)] [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] (c : C)
    (x : RightFactorRes k A C (IndK k (Res ψγ N) ψδ × (Fin n → N))) :
    indResProdRightFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N (rightFactorCAct c x) =
      (Ind.map (Res.map (rightFactorCAct c))
          (indResProdRightFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N x).1,
        fun s => rightFactorCAct c ((indResProdRightFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N x).2 s)) :=
  Prod.ext (indResRightFactorEquiv_cAct γ ψγ hψγ δ hδ ψδ hψδ N c _) rfl

/-- Second factor of `Res_{C ⊗ α} Ind_{C ⊗ β} N ⊕ N^n`. -/
def resIndProdRightFactorEquiv (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
    [IsScalarTower k (C ⊗[k] A) N] :
    RightFactorRes k A C (Res ψα (IndK k N ψβ) × (Fin n → N)) ≃ₗ[A]
      Res α (Ind (RightFactorRes k A C N) β) × (Fin n → RightFactorRes k A C N) :=
  (rightFactorProdEquiv n _ N).trans (LinearEquiv.prodCongr
    (resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N)
    (LinearEquiv.refl A (Fin n → RightFactorRes k A C N)))

theorem resIndProdRightFactorEquiv_cAct (N : Type w) [AddCommGroup N] [Module k N]
    [Module (C ⊗[k] A) N] [IsScalarTower k (C ⊗[k] A) N] (c : C)
    (x : RightFactorRes k A C (Res ψα (IndK k N ψβ) × (Fin n → N))) :
    resIndProdRightFactorEquiv n α ψα hψα β hβ ψβ hψβ N (rightFactorCAct c x) =
      (Res.map (Ind.map (rightFactorCAct c))
          (resIndProdRightFactorEquiv n α ψα hψα β hβ ψβ hψβ N x).1,
        fun s => rightFactorCAct c ((resIndProdRightFactorEquiv n α ψα hψα β hβ ψβ hψβ N x).2 s)) :=
  Prod.ext (resIndRightFactorEquiv_cAct α ψα hψα β hβ ψβ hψβ N c _) rfl

/-- **Lifting a natural isomorphism `Res_α Ind_β ≅ Ind_δ Res_γ ⊕ id^n`** to modules over the
tensor product `C ⊗ A`. -/
def liftResIndProdEquivRight
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module A M],
      Res α (Ind M β) ≃ₗ[A] Ind (Res γ M) δ × (Fin n → M))
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Res α (Ind M β)),
      Φ M' (Res.map (Ind.map f) x) =
        (Ind.map (Res.map f) (Φ M x).1, fun s => f ((Φ M x).2 s)))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
    [IsScalarTower k (C ⊗[k] A) N] [Module k (Res ψγ N)]
    [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] :
    Res ψα (IndK k N ψβ) ≃ₗ[C ⊗[k] A] IndK k (Res ψγ N) ψδ × (Fin n → N) :=
  linearEquivOfRightFactor
    (((resIndRightFactorEquiv α ψα hψα β hβ ψβ hψβ N).trans (Φ (RightFactorRes k A C N))).trans
      (indResProdRightFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N).symm)
    (fun c x => by
      apply (indResProdRightFactorEquiv n γ ψγ hψγ δ hδ ψδ hψδ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [indResProdRightFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        resIndRightFactorEquiv_cAct, hΦ])

/-- **Lifting a natural isomorphism `Ind_δ Res_γ ≅ Res_α Ind_β ⊕ id^n`** to modules over the
tensor product `C ⊗ A`. -/
def liftIndResProdEquivRight
    (Φ : ∀ (M : Type w) [AddCommGroup M] [Module A M],
      Ind (Res γ M) δ ≃ₗ[A] Res α (Ind M β) × (Fin n → M))
    (hΦ : ∀ (M M' : Type w) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
      (f : M →ₗ[A] M') (x : Ind (Res γ M) δ),
      Φ M' (Ind.map (Res.map f) x) =
        (Res.map (Ind.map f) (Φ M x).1, fun s => f ((Φ M x).2 s)))
    (N : Type w) [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
    [IsScalarTower k (C ⊗[k] A) N] [Module k (Res ψγ N)]
    [IsScalarTower k (C ⊗[k] A₀) (Res ψγ N)] :
    IndK k (Res ψγ N) ψδ ≃ₗ[C ⊗[k] A] Res ψα (IndK k N ψβ) × (Fin n → N) :=
  linearEquivOfRightFactor
    (((indResRightFactorEquiv γ ψγ hψγ δ hδ ψδ hψδ N).trans (Φ (RightFactorRes k A C N))).trans
      (resIndProdRightFactorEquiv n α ψα hψα β hβ ψβ hψβ N).symm)
    (fun c x => by
      apply (resIndProdRightFactorEquiv n α ψα hψα β hβ ψβ hψβ N).injective
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rw [resIndProdRightFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        indResRightFactorEquiv_cAct, hΦ])

end ProdRight

end InductionAlong

end

end Categorification
