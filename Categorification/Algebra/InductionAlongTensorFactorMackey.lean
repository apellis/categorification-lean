/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorLift

/-!
# Induction along one tensor factor commutes with restriction along the other

Let `φ : A₀ → A₁` and `χ : C₀ → C₁` be nonunital maps of `k`-algebras. On modules over the
tensor products `Aᵢ ⊗ Cⱼ`, induction along a map `φ ⊗ C` of the first factor commutes with
restriction along a map `A ⊗ χ` of the second factor: for an `A₀ ⊗ C₁`-module `N`,
`Res_{A₁ ⊗ χ} Ind_{φ ⊗ C₁} N ≅ Ind_{φ ⊗ C₀} Res_{A₀ ⊗ χ} N` as `A₁ ⊗ C₀`-modules
(`resIndCrossFactorEquiv`). No flatness is needed: restriction along `A ⊗ χ` is the image of the
idempotent `1 ⊗ χ(1)`, which acts on the first factor through an idempotent endomorphism, and
induction commutes with images of idempotent endomorphisms (`indFixedEquiv`). The mirror
statement, with induction along the second factor and restriction along the first, is
`resIndCrossFactorEquivRight`.

These give the cross-factor commutations `₂Eⱼ ₁Fᵢ ≅ ₁Fᵢ ₂Eⱼ` and `₁Eⱼ ₂Fᵢ ≅ ₂Fᵢ ₁Eⱼ` of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, used in the dimension
count (5.14) of the proof of Proposition 5.5.

## Main definitions

* `fixedSubmodule p`: the fixed points `{n | p n = n}` of an endomorphism `p`.
* `indFixedEquiv`: for an idempotent `p`, the fixed points of `Ind p` are `Ind` of the fixed
  points of `p`; natural in `p` (`indFixedEquiv_natural`).
* `resIndCrossFactorEquiv`, `resIndCrossFactorEquivRight`: the two cross-factor isomorphisms.
-/

namespace Categorification

open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-! ### Fixed points of endomorphisms -/

section Fixed

variable {A : Type*} [Ring A]

/-- The fixed points `{n | p n = n}` of an endomorphism `p`. -/
def fixedSubmodule {N : Type*} [AddCommGroup N] [Module A N] (p : N →ₗ[A] N) :
    Submodule A N where
  carrier := {n | p n = n}
  add_mem' {x y} hx hy := (map_add p x y).trans (congrArg₂ (· + ·) hx hy)
  zero_mem' := map_zero p
  smul_mem' a n h := (map_smul p a n).trans (congrArg (a • ·) h)

theorem fixedSubmodule_apply {N : Type*} [AddCommGroup N] [Module A N] {p : N →ₗ[A] N}
    (x : fixedSubmodule p) : p x.1 = x.1 := x.2

/-- An isomorphism intertwining two endomorphisms restricts to their fixed points. -/
def fixedEquivOfComm {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) (p : X →ₗ[A] X) (q : Y →ₗ[A] Y) (h : ∀ x, e (p x) = q (e x)) :
    fixedSubmodule p ≃ₗ[A] fixedSubmodule q where
  toFun x := ⟨e x.1, show q (e x.1) = e x.1 by rw [← h, fixedSubmodule_apply x]⟩
  invFun y := ⟨e.symm y.1, show p (e.symm y.1) = e.symm y.1 by
    apply e.injective
    rw [h, LinearEquiv.apply_symm_apply, fixedSubmodule_apply y]⟩
  map_add' x y := Subtype.ext (map_add e x.1 y.1)
  map_smul' a x := Subtype.ext (map_smul e a x.1)
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

@[simp] theorem fixedEquivOfComm_val {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (e : X ≃ₗ[A] Y) (p : X →ₗ[A] X) (q : Y →ₗ[A] Y)
    (h : ∀ x, e (p x) = q (e x)) (x : fixedSubmodule p) :
    (fixedEquivOfComm e p q h x).1 = e x.1 := rfl

end Fixed

/-! ### Induction of fixed points -/

section Core

variable {k : Type*} [CommRing k] {A B : Type u} [Ring A] [Ring B] [Algebra k B]
  {φ : A →ₙ+* B} {N N' N'' : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N']
  [Module A N'] [AddCommGroup N''] [Module A N'']

theorem IndK.map_map_apply (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') (x : IndK k N φ) :
    IndK.map g' (IndK.map g x) = IndK.map (k := k) (g'.comp g) x :=
  (LinearMap.congr_fun (Ind.map_comp (φ := φ) g g') x).symm

theorem IndK.map_id_apply (x : IndK k N φ) : IndK.map (k := k) LinearMap.id x = x :=
  LinearMap.congr_fun (Ind.map_id (φ := φ)) x

variable (p : N →ₗ[A] N) (hp : ∀ n, p (p n) = p n)

/-- The retraction of `N` onto the fixed points of an idempotent `p`. -/
def fixedRetract : N →ₗ[A] fixedSubmodule p :=
  LinearMap.codRestrict (fixedSubmodule p) p hp

@[simp] theorem fixedRetract_val (n : N) : (fixedRetract p hp n).1 = p n := rfl

/-- **Induction commutes with images of idempotents**: for an idempotent endomorphism `p` of
`N`, the fixed points of `Ind_φ p` are `Ind_φ` of the fixed points of `p`. -/
def indFixedEquiv :
    fixedSubmodule (IndK.map (k := k) (φ := φ) p) ≃ₗ[B] IndK k (fixedSubmodule p) φ where
  toFun x := IndK.map (fixedRetract p hp) x.1
  invFun y := ⟨IndK.map (fixedSubmodule p).subtype y, show IndK.map p _ = _ by
    rw [IndK.map_map_apply]
    have : p.comp (fixedSubmodule p).subtype = (fixedSubmodule p).subtype :=
      LinearMap.ext fun x => fixedSubmodule_apply x
    rw [this]⟩
  map_add' x y := map_add (IndK.map (k := k) (φ := φ) (fixedRetract p hp)) x.1 y.1
  map_smul' b x := map_smul (IndK.map (k := k) (φ := φ) (fixedRetract p hp)) b x.1
  left_inv x := Subtype.ext (by
    change IndK.map (fixedSubmodule p).subtype (IndK.map (fixedRetract p hp) x.1) = x.1
    rw [IndK.map_map_apply]
    exact fixedSubmodule_apply x)
  right_inv y := by
    change IndK.map (fixedRetract p hp) (IndK.map (fixedSubmodule p).subtype y) = y
    rw [IndK.map_map_apply]
    have : (fixedRetract p hp).comp (fixedSubmodule p).subtype = LinearMap.id :=
      LinearMap.ext fun x => Subtype.ext (fixedSubmodule_apply x)
    rw [this, IndK.map_id_apply]

theorem indFixedEquiv_apply (x : fixedSubmodule (IndK.map (k := k) (φ := φ) p)) :
    indFixedEquiv p hp x = IndK.map (fixedRetract p hp) x.1 := rfl

/-- **Naturality of `indFixedEquiv`** in maps commuting with the idempotents. -/
theorem indFixedEquiv_natural (p' : N' →ₗ[A] N') (hp' : ∀ n, p' (p' n) = p' n)
    (g : N →ₗ[A] N') (hg : ∀ n, g (p n) = p' (g n))
    (gS : fixedSubmodule p →ₗ[A] fixedSubmodule p') (hgS : ∀ x, (gS x).1 = g x.1)
    (x : fixedSubmodule (IndK.map (k := k) (φ := φ) p))
    (x' : fixedSubmodule (IndK.map (k := k) (φ := φ) p')) (hx : x'.1 = IndK.map g x.1) :
    indFixedEquiv p' hp' x' = IndK.map gS (indFixedEquiv p hp x) := by
  rw [indFixedEquiv_apply, indFixedEquiv_apply, hx, IndK.map_map_apply, IndK.map_map_apply]
  have : (fixedRetract p' hp').comp g = gS.comp (fixedRetract p hp) :=
    LinearMap.ext fun n => Subtype.ext (by
      change p' (g n) = (gS (fixedRetract p hp n)).1
      rw [hgS, fixedRetract_val, hg])
  rw [this]

end Core

/-! ### Induction along the first factor, restriction along the second -/

section LeftFactor

variable {k : Type*} [CommRing k] {A₀ A₁ C₀ C₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring A₁]
  [Algebra k A₁] [Ring C₀] [Algebra k C₀] [Ring C₁] [Algebra k C₁]

section CAct

variable {B : Type u} [Ring B] [Algebra k B] {M : Type w} [AddCommGroup M]
  [Module (B ⊗[k] C₁) M]

theorem leftFactorCAct_mul (c c' : C₁) (x : LeftFactorRes k B C₁ M) :
    leftFactorCAct c (leftFactorCAct c' x) = leftFactorCAct (c * c') x := by
  change ((1 : B) ⊗ₜ[k] c) • ((1 : B) ⊗ₜ[k] c') • (show M from x) =
    ((1 : B) ⊗ₜ[k] (c * c')) • (show M from x)
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (χ : C₀ →ₙ+* C₁)

omit [Algebra k C₀] in
theorem leftFactorCAct_idem (x : LeftFactorRes k B C₁ M) :
    leftFactorCAct (χ 1) (leftFactorCAct (χ 1) x) = leftFactorCAct (χ 1) x := by
  rw [leftFactorCAct_mul, ← map_mul, one_mul]

/-- The action of `1 ⊗ χ(c)` on the fixed points of `1 ⊗ χ(1)`. -/
def leftFixedCAct (c : C₀) :
    fixedSubmodule (leftFactorCAct (k := k) (A := B) (N := M) (χ 1)) →ₗ[B]
      fixedSubmodule (leftFactorCAct (k := k) (A := B) (N := M) (χ 1)) :=
  (leftFactorCAct (χ c)).restrict fun x _ => show leftFactorCAct (χ 1) _ = _ by
    rw [leftFactorCAct_mul, ← map_mul, one_mul]

omit [Algebra k C₀] in
theorem leftFixedCAct_val (c : C₀)
    (x : fixedSubmodule (leftFactorCAct (k := k) (A := B) (N := M) (χ 1))) :
    (leftFixedCAct χ c x).1 = leftFactorCAct (χ c) x.1 := rfl

end CAct

section ResRight

variable {B : Type u} [Ring B] [Algebra k B] (χ : C₀ →ₙ+* C₁)
  (ρ : B ⊗[k] C₀ →ₙ+* B ⊗[k] C₁) (hρ : ∀ (b : B) (c : C₀), ρ (b ⊗ₜ c) = b ⊗ₜ χ c)
  (M : Type w) [AddCommGroup M] [Module (B ⊗[k] C₁) M]

include hρ in
theorem rightMap_one : ρ 1 = (1 : B) ⊗ₜ[k] χ 1 := by
  rw [Algebra.TensorProduct.one_def, hρ]

/-- **Restriction along a map of the second factor, on first factors**:
`(Res_{B ⊗ χ} M)|_B` is the image of the idempotent `1 ⊗ χ(1)` on `M|_B`. -/
def resRightLeftFactorEquiv :
    LeftFactorRes k B C₀ (Res ρ M) ≃ₗ[B]
      fixedSubmodule (leftFactorCAct (k := k) (A := B) (N := M) (χ 1)) where
  toFun x := ⟨(show LeftFactorRes k B C₁ M from (show Res ρ M from x).val), by
    change ((1 : B) ⊗ₜ[k] χ 1) • (show Res ρ M from x).val = (show Res ρ M from x).val
    rw [← rightMap_one χ ρ hρ]
    exact (show Res ρ M from x).prop⟩
  invFun y := (show LeftFactorRes k B C₀ (Res ρ M) from Res.mk (show M from y.1) (by
    rw [rightMap_one χ ρ hρ]
    exact y.2))
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext (by
    have hx := (show Res ρ M from x).prop
    rw [rightMap_one χ ρ hρ] at hx
    change ρ (a ⊗ₜ[k] (1 : C₀)) • (show Res ρ M from x).val =
      (a ⊗ₜ[k] (1 : C₁)) • (show Res ρ M from x).val
    rw [hρ]
    conv_rhs => rw [← hx]
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul])
  left_inv x := Res.ext rfl
  right_inv y := Subtype.ext rfl

theorem resRightLeftFactorEquiv_val (x : LeftFactorRes k B C₀ (Res ρ M)) :
    (resRightLeftFactorEquiv χ ρ hρ M x).1 = (show Res ρ M from x).val := rfl

/-- `resRightLeftFactorEquiv` carries the action of `1 ⊗ c` to the action of `1 ⊗ χ(c)`. -/
theorem resRightLeftFactorEquiv_cAct (c : C₀) (x : LeftFactorRes k B C₀ (Res ρ M)) :
    resRightLeftFactorEquiv χ ρ hρ M (leftFactorCAct c x) =
      leftFixedCAct χ c (resRightLeftFactorEquiv χ ρ hρ M x) := Subtype.ext (by
  change ρ ((1 : B) ⊗ₜ[k] c) • (show Res ρ M from x).val =
    ((1 : B) ⊗ₜ[k] χ c) • (show Res ρ M from x).val
  rw [hρ])

end ResRight

variable (φ : A₀ →ₙ+* A₁) (hφ : ∀ (c : k) (t : A₀), φ (c • t) = c • φ t)
  (ψ₀ : A₀ ⊗[k] C₀ →ₙ+* A₁ ⊗[k] C₀) (hψ₀ : ∀ (a : A₀) (c : C₀), ψ₀ (a ⊗ₜ c) = φ a ⊗ₜ c)
  (ψ₁ : A₀ ⊗[k] C₁ →ₙ+* A₁ ⊗[k] C₁) (hψ₁ : ∀ (a : A₀) (c : C₁), ψ₁ (a ⊗ₜ c) = φ a ⊗ₜ c)
  (χ : C₀ →ₙ+* C₁)
  (ρ₀ : A₀ ⊗[k] C₀ →ₙ+* A₀ ⊗[k] C₁) (hρ₀ : ∀ (a : A₀) (c : C₀), ρ₀ (a ⊗ₜ c) = a ⊗ₜ χ c)
  (ρ₁ : A₁ ⊗[k] C₀ →ₙ+* A₁ ⊗[k] C₁) (hρ₁ : ∀ (a : A₁) (c : C₀), ρ₁ (a ⊗ₜ c) = a ⊗ₜ χ c)
  (N : Type w) [AddCommGroup N] [Module k N] [Module (A₀ ⊗[k] C₁) N]
  [IsScalarTower k (A₀ ⊗[k] C₁) N] [Module k (Res ρ₀ N)]
  [IsScalarTower k (A₀ ⊗[k] C₀) (Res ρ₀ N)]

/-- The first factor of the cross-factor isomorphism:
`(Res_{A₁ ⊗ χ} Ind_{φ ⊗ C₁} N)|_{A₁} ≅ (Ind_{φ ⊗ C₀} Res_{A₀ ⊗ χ} N)|_{A₁}`. -/
def resIndCrossLeftFactorEquiv :
    LeftFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁)) ≃ₗ[A₁]
      LeftFactorRes k A₁ C₀ (IndK k (Res ρ₀ N) ψ₀) :=
  ((((resRightLeftFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁)).trans
    (fixedEquivOfComm (indLeftFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (leftFactorCAct (χ 1)))
      (fun x => indLeftFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x))).trans
    (indFixedEquiv (leftFactorCAct (χ 1)) (leftFactorCAct_idem χ))).trans
    (Ind.mapEquiv (resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm)).trans
    (indLeftFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)).symm

theorem resIndCrossLeftFactorEquiv_apply (x : LeftFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁))) :
    indLeftFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)
        (resIndCrossLeftFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N x) =
      IndK.map (resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap
        (indFixedEquiv (k := k) (φ := φ) (leftFactorCAct (χ 1)) (leftFactorCAct_idem χ)
          (fixedEquivOfComm (indLeftFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
            (IndK.map (leftFactorCAct (χ 1)))
            (fun x => indLeftFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
            (resRightLeftFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) x))) :=
  LinearEquiv.apply_symm_apply _ _

theorem resIndCrossLeftFactorEquiv_cAct (c : C₀)
    (x : LeftFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁))) :
    resIndCrossLeftFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N (leftFactorCAct c x) =
      leftFactorCAct c (resIndCrossLeftFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N x) := by
  apply (indLeftFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)).injective
  rw [indLeftFactorEquivB_cAct, resIndCrossLeftFactorEquiv_apply,
    resIndCrossLeftFactorEquiv_apply]
  have key := indFixedEquiv_natural (k := k) (φ := φ) (leftFactorCAct (χ 1))
    (leftFactorCAct_idem χ) (leftFactorCAct (χ 1)) (leftFactorCAct_idem χ)
    (leftFactorCAct (χ c))
    (fun n => by rw [leftFactorCAct_mul, leftFactorCAct_mul, ← map_mul, ← map_mul, one_mul,
      mul_one])
    (leftFixedCAct χ c) (fun _ => rfl)
    (fixedEquivOfComm (indLeftFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (leftFactorCAct (χ 1)))
      (fun x => indLeftFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
      (resRightLeftFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) x))
    (fixedEquivOfComm (indLeftFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (leftFactorCAct (χ 1)))
      (fun x => indLeftFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
      (resRightLeftFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) (leftFactorCAct c x)))
    (by
      rw [fixedEquivOfComm_val, fixedEquivOfComm_val, resRightLeftFactorEquiv_cAct,
        leftFixedCAct_val, indLeftFactorEquivB_cAct])
  rw [key, IndK.map_map_apply, IndK.map_map_apply]
  have h : (resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap.comp (leftFixedCAct χ c) =
      (leftFactorCAct c).comp (resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap :=
    LinearMap.ext fun y => (resRightLeftFactorEquiv χ ρ₀ hρ₀ N).injective (by
      change resRightLeftFactorEquiv χ ρ₀ hρ₀ N
          ((resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm (leftFixedCAct χ c y)) =
        resRightLeftFactorEquiv χ ρ₀ hρ₀ N
          (leftFactorCAct c ((resRightLeftFactorEquiv χ ρ₀ hρ₀ N).symm y))
      rw [resRightLeftFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])
  rw [h]

/-- **Induction along the first factor commutes with restriction along the second**:
`Res_{A₁ ⊗ χ} Ind_{φ ⊗ C₁} N ≅ Ind_{φ ⊗ C₀} Res_{A₀ ⊗ χ} N` as `A₁ ⊗ C₀`-modules, for every
`A₀ ⊗ C₁`-module `N`. This is the cross-factor commutation `₂Eⱼ ₁Fᵢ ≅ ₁Fᵢ ₂Eⱼ` of Webster,
arXiv:1309.3796v3, (5.14). -/
def resIndCrossFactorEquiv :
    Res ρ₁ (IndK k N ψ₁) ≃ₗ[A₁ ⊗[k] C₀] IndK k (Res ρ₀ N) ψ₀ :=
  linearEquivOfLeftFactor (resIndCrossLeftFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N)
    (resIndCrossLeftFactorEquiv_cAct φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N)

end LeftFactor

section RightFactor

variable {k : Type*} [CommRing k] {A₀ A₁ C₀ C₁ : Type u} [Ring A₀] [Algebra k A₀] [Ring A₁]
  [Algebra k A₁] [Ring C₀] [Algebra k C₀] [Ring C₁] [Algebra k C₁]

section CAct

variable {B : Type u} [Ring B] [Algebra k B] {M : Type w} [AddCommGroup M]
  [Module (C₁ ⊗[k] B) M]

theorem rightFactorCAct_mul (c c' : C₁) (x : RightFactorRes k B C₁ M) :
    rightFactorCAct c (rightFactorCAct c' x) = rightFactorCAct (c * c') x := by
  change (c ⊗ₜ[k] (1 : B)) • (c' ⊗ₜ[k] (1 : B)) • (show M from x) =
    ((c * c') ⊗ₜ[k] (1 : B)) • (show M from x)
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (χ : C₀ →ₙ+* C₁)

omit [Algebra k C₀] in
theorem rightFactorCAct_idem (x : RightFactorRes k B C₁ M) :
    rightFactorCAct (χ 1) (rightFactorCAct (χ 1) x) = rightFactorCAct (χ 1) x := by
  rw [rightFactorCAct_mul, ← map_mul, one_mul]

/-- The action of `χ(c) ⊗ 1` on the fixed points of `χ(1) ⊗ 1`. -/
def rightFixedCAct (c : C₀) :
    fixedSubmodule (rightFactorCAct (k := k) (A := B) (N := M) (χ 1)) →ₗ[B]
      fixedSubmodule (rightFactorCAct (k := k) (A := B) (N := M) (χ 1)) :=
  (rightFactorCAct (χ c)).restrict fun x _ => show rightFactorCAct (χ 1) _ = _ by
    rw [rightFactorCAct_mul, ← map_mul, one_mul]

omit [Algebra k C₀] in
theorem rightFixedCAct_val (c : C₀)
    (x : fixedSubmodule (rightFactorCAct (k := k) (A := B) (N := M) (χ 1))) :
    (rightFixedCAct χ c x).1 = rightFactorCAct (χ c) x.1 := rfl

end CAct

section ResRight

variable {B : Type u} [Ring B] [Algebra k B] (χ : C₀ →ₙ+* C₁)
  (ρ : C₀ ⊗[k] B →ₙ+* C₁ ⊗[k] B) (hρ : ∀ (c : C₀) (b : B), ρ (c ⊗ₜ b) = χ c ⊗ₜ b)
  (M : Type w) [AddCommGroup M] [Module (C₁ ⊗[k] B) M]

include hρ in
theorem leftMap_one : ρ 1 = χ 1 ⊗ₜ[k] (1 : B) := by
  rw [Algebra.TensorProduct.one_def, hρ]

/-- **Restriction along a map of the first factor, on second factors**:
`(Res_{χ ⊗ B} M)|_B` is the image of the idempotent `χ(1) ⊗ 1` on `M|_B`. -/
def resLeftRightFactorEquiv :
    RightFactorRes k B C₀ (Res ρ M) ≃ₗ[B]
      fixedSubmodule (rightFactorCAct (k := k) (A := B) (N := M) (χ 1)) where
  toFun x := ⟨(show RightFactorRes k B C₁ M from (show Res ρ M from x).val), by
    change (χ 1 ⊗ₜ[k] (1 : B)) • (show Res ρ M from x).val = (show Res ρ M from x).val
    rw [← leftMap_one χ ρ hρ]
    exact (show Res ρ M from x).prop⟩
  invFun y := (show RightFactorRes k B C₀ (Res ρ M) from Res.mk (show M from y.1) (by
    rw [leftMap_one χ ρ hρ]
    exact y.2))
  map_add' x y := Subtype.ext rfl
  map_smul' a x := Subtype.ext (by
    have hx := (show Res ρ M from x).prop
    rw [leftMap_one χ ρ hρ] at hx
    change ρ ((1 : C₀) ⊗ₜ[k] a) • (show Res ρ M from x).val =
      ((1 : C₁) ⊗ₜ[k] a) • (show Res ρ M from x).val
    rw [hρ]
    conv_rhs => rw [← hx]
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one])
  left_inv x := Res.ext rfl
  right_inv y := Subtype.ext rfl

theorem resLeftRightFactorEquiv_val (x : RightFactorRes k B C₀ (Res ρ M)) :
    (resLeftRightFactorEquiv χ ρ hρ M x).1 = (show Res ρ M from x).val := rfl

/-- `resLeftRightFactorEquiv` carries the action of `c ⊗ 1` to the action of `χ(c) ⊗ 1`. -/
theorem resLeftRightFactorEquiv_cAct (c : C₀) (x : RightFactorRes k B C₀ (Res ρ M)) :
    resLeftRightFactorEquiv χ ρ hρ M (rightFactorCAct c x) =
      rightFixedCAct χ c (resLeftRightFactorEquiv χ ρ hρ M x) := Subtype.ext (by
  change ρ (c ⊗ₜ[k] (1 : B)) • (show Res ρ M from x).val =
    (χ c ⊗ₜ[k] (1 : B)) • (show Res ρ M from x).val
  rw [hρ])

end ResRight

variable (φ : A₀ →ₙ+* A₁) (hφ : ∀ (c : k) (t : A₀), φ (c • t) = c • φ t)
  (ψ₀ : C₀ ⊗[k] A₀ →ₙ+* C₀ ⊗[k] A₁) (hψ₀ : ∀ (c : C₀) (a : A₀), ψ₀ (c ⊗ₜ a) = c ⊗ₜ φ a)
  (ψ₁ : C₁ ⊗[k] A₀ →ₙ+* C₁ ⊗[k] A₁) (hψ₁ : ∀ (c : C₁) (a : A₀), ψ₁ (c ⊗ₜ a) = c ⊗ₜ φ a)
  (χ : C₀ →ₙ+* C₁)
  (ρ₀ : C₀ ⊗[k] A₀ →ₙ+* C₁ ⊗[k] A₀) (hρ₀ : ∀ (c : C₀) (a : A₀), ρ₀ (c ⊗ₜ a) = χ c ⊗ₜ a)
  (ρ₁ : C₀ ⊗[k] A₁ →ₙ+* C₁ ⊗[k] A₁) (hρ₁ : ∀ (c : C₀) (a : A₁), ρ₁ (c ⊗ₜ a) = χ c ⊗ₜ a)
  (N : Type w) [AddCommGroup N] [Module k N] [Module (C₁ ⊗[k] A₀) N]
  [IsScalarTower k (C₁ ⊗[k] A₀) N] [Module k (Res ρ₀ N)]
  [IsScalarTower k (C₀ ⊗[k] A₀) (Res ρ₀ N)]

/-- The second factor of the mirrored cross-factor isomorphism:
`(Res_{χ ⊗ A₁} Ind_{C₁ ⊗ φ} N)|_{A₁} ≅ (Ind_{C₀ ⊗ φ} Res_{χ ⊗ A₀} N)|_{A₁}`. -/
def resIndCrossRightFactorEquiv :
    RightFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁)) ≃ₗ[A₁]
      RightFactorRes k A₁ C₀ (IndK k (Res ρ₀ N) ψ₀) :=
  ((((resLeftRightFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁)).trans
    (fixedEquivOfComm (indRightFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (rightFactorCAct (χ 1)))
      (fun x => indRightFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x))).trans
    (indFixedEquiv (rightFactorCAct (χ 1)) (rightFactorCAct_idem χ))).trans
    (Ind.mapEquiv (resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm)).trans
    (indRightFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)).symm

theorem resIndCrossRightFactorEquiv_apply
    (x : RightFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁))) :
    indRightFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)
        (resIndCrossRightFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N x) =
      IndK.map (resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap
        (indFixedEquiv (k := k) (φ := φ) (rightFactorCAct (χ 1)) (rightFactorCAct_idem χ)
          (fixedEquivOfComm (indRightFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
            (IndK.map (rightFactorCAct (χ 1)))
            (fun x => indRightFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
            (resLeftRightFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) x))) :=
  LinearEquiv.apply_symm_apply _ _

theorem resIndCrossRightFactorEquiv_cAct (c : C₀)
    (x : RightFactorRes k A₁ C₀ (Res ρ₁ (IndK k N ψ₁))) :
    resIndCrossRightFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N (rightFactorCAct c x) =
      rightFactorCAct c
        (resIndCrossRightFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N x) := by
  apply (indRightFactorEquivB φ hφ ψ₀ hψ₀ (N := Res ρ₀ N)).injective
  rw [indRightFactorEquivB_cAct, resIndCrossRightFactorEquiv_apply,
    resIndCrossRightFactorEquiv_apply]
  have key := indFixedEquiv_natural (k := k) (φ := φ) (rightFactorCAct (χ 1))
    (rightFactorCAct_idem χ) (rightFactorCAct (χ 1)) (rightFactorCAct_idem χ)
    (rightFactorCAct (χ c))
    (fun n => by rw [rightFactorCAct_mul, rightFactorCAct_mul, ← map_mul, ← map_mul, one_mul,
      mul_one])
    (rightFixedCAct χ c) (fun _ => rfl)
    (fixedEquivOfComm (indRightFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (rightFactorCAct (χ 1)))
      (fun x => indRightFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
      (resLeftRightFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) x))
    (fixedEquivOfComm (indRightFactorEquivB φ hφ ψ₁ hψ₁ (N := N)) _
      (IndK.map (rightFactorCAct (χ 1)))
      (fun x => indRightFactorEquivB_cAct φ hφ ψ₁ hψ₁ (χ 1) x)
      (resLeftRightFactorEquiv χ ρ₁ hρ₁ (IndK k N ψ₁) (rightFactorCAct c x)))
    (by
      rw [fixedEquivOfComm_val, fixedEquivOfComm_val, resLeftRightFactorEquiv_cAct,
        rightFixedCAct_val, indRightFactorEquivB_cAct])
  rw [key, IndK.map_map_apply, IndK.map_map_apply]
  have h : (resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap.comp (rightFixedCAct χ c) =
      (rightFactorCAct c).comp (resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm.toLinearMap :=
    LinearMap.ext fun y => (resLeftRightFactorEquiv χ ρ₀ hρ₀ N).injective (by
      change resLeftRightFactorEquiv χ ρ₀ hρ₀ N
          ((resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm (rightFixedCAct χ c y)) =
        resLeftRightFactorEquiv χ ρ₀ hρ₀ N
          (rightFactorCAct c ((resLeftRightFactorEquiv χ ρ₀ hρ₀ N).symm y))
      rw [resLeftRightFactorEquiv_cAct, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])
  rw [h]

/-- **Induction along the second factor commutes with restriction along the first**:
`Res_{χ ⊗ A₁} Ind_{C₁ ⊗ φ} N ≅ Ind_{C₀ ⊗ φ} Res_{χ ⊗ A₀} N` as `C₀ ⊗ A₁`-modules, for every
`C₁ ⊗ A₀`-module `N`. This is the cross-factor commutation `₁Eⱼ ₂Fᵢ ≅ ₂Fᵢ ₁Eⱼ` of Webster,
arXiv:1309.3796v3, (5.14). -/
def resIndCrossFactorEquivRight :
    Res ρ₁ (IndK k N ψ₁) ≃ₗ[C₀ ⊗[k] A₁] IndK k (Res ρ₀ N) ψ₀ :=
  linearEquivOfRightFactor (resIndCrossRightFactorEquiv φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N)
    (resIndCrossRightFactorEquiv_cAct φ hφ ψ₀ hψ₀ ψ₁ hψ₁ χ ρ₀ hρ₀ ρ₁ hρ₁ N)

end RightFactor

end InductionAlong

end

end Categorification
