/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorIsoIdOfSummands

set_option backward.isDefEq.respectTransparency false

/-!
# The fullness hypothesis on generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22. In `Categorification.derivedTensorIsoIdOfIdempotents` the fullness hypothesis
asks that every right multiplication `T eₐ → T e_b`, `x ↦ x c e_b`, be the image of a morphism
under the functor `Φ`. For an additive `Φ` the elements `c` with this property form a subring
(`Categorification.hitSubring`, using `idemRightMul_mul`: the right multiplication by `c d`
factors through `⊕ᵤ T eᵤ`), so it suffices to check ring generators
(`Categorification.forall_hit_of_closure`, `Categorification.derivedTensorIsoIdOfGenerators`).
For the cyclotomic quotient these are the idempotents, dots and crossings, so the hypothesis
becomes: the vacuum functor sends the dots and crossings on `F_𝐢 P_∅` to the left
multiplications by them on `e(𝐢) T^λ`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Categorification

variable {T : Type} [Ring T]

section RightMul

variable {ι : Type} (e : ι → T) (he : ∀ a, IsIdempotentElem (e a))
  (horth : ∀ a b, a ≠ b → e a * e b = 0)

/-- `idemRightMul` is additive in the multiplier. -/
theorem idemRightMul_add (a b : ι) (c d : T) :
    idemRightMul (e a) (e b) (c + d) (he b) =
      idemRightMul (e a) (e b) c (he b) + idemRightMul (e a) (e b) d (he b) :=
  LinearMap.ext fun x => Subtype.ext (by simp [idemRightMul, mul_add, add_mul])

/-- `idemRightMul` commutes with negation of the multiplier. -/
theorem idemRightMul_neg (a b : ι) (c : T) :
    idemRightMul (e a) (e b) (-c) (he b) = -idemRightMul (e a) (e b) c (he b) :=
  LinearMap.ext fun x => Subtype.ext (by simp [idemRightMul])

/-- Right multiplication by `0` is `0`. -/
theorem idemRightMul_zero (a b : ι) : idemRightMul (e a) (e b) 0 (he b) = 0 :=
  LinearMap.ext fun x => Subtype.ext (by simp [idemRightMul])

/-- Right multiplication by `1` on `T eₐ` is the identity. -/
theorem idemRightMul_one_self (a : ι) : idemRightMul (e a) (e a) 1 (he a) = LinearMap.id :=
  LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
    change x * 1 * e a = x
    rw [mul_one, hx])

include horth in
/-- Right multiplication by `1` from `T eₐ` to `T e_b` vanishes for `a ≠ b`. -/
theorem idemRightMul_one_of_ne {a b : ι} (h : a ≠ b) : idemRightMul (e a) (e b) 1 (he b) = 0 :=
  LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (by
    change x * 1 * e b = 0
    rw [mul_one, ← hx, mul_assoc, horth a b h, mul_zero])

/-- **Right multiplication by a product factors through `⊕ᵤ T eᵤ`.** -/
theorem idemRightMul_mul [Fintype ι] (hsum : ∑ a, e a = 1) (a b : ι) (c d : T) :
    idemRightMul (e a) (e b) (c * d) (he b) =
      ∑ u, (idemRightMul (e u) (e b) d (he b)).comp (idemRightMul (e a) (e u) c (he u)) := by
  ext ⟨x, hx⟩
  change x * (c * d) * e b = ((∑ u, _ : idemLeftIdeal (e a) →ₗ[T] idemLeftIdeal (e b))
    ⟨x, hx⟩ : T)
  rw [LinearMap.sum_apply, Submodule.coe_sum]
  change _ = ∑ u, x * c * e u * d * e b
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]

end RightMul

section Hit

variable [HasDerivedCategory.{0} (ModuleCat.{0} T)]

set_option hygiene false in
local notation "𝕊" => (DerivedCategory.singleFunctor (ModuleCat.{0} T) 0)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → T) (he : ∀ a, IsIdempotentElem (e a))
  (horth : ∀ a b, a ≠ b → e a * e b = 0) (hsum : ∑ a, e a = 1)
  {P : Type*} [Category P] [Preadditive P] (Φ : P ⥤ DerivedCategory (ModuleCat.{0} T))
  [Φ.Additive] (p : ι → P)
  (κ : ∀ a, Φ.obj (p a) ≅ (𝕊).obj (ModuleCat.of T (idemLeftIdeal (e a))))

/-- **The elements whose right multiplications are hit**: `c` such that for all `a, b` the map
`T eₐ → T e_b`, `x ↦ x c e_b`, is the image under `Φ` of a morphism `pₐ ⟶ p_b` (along `κ`). It is
a subring, so `hsurj` of `derivedTensorIsoIdOfIdempotents` only needs to be checked on ring
generators of `T` (`hitSubring_eq_top_of_closure`). -/
def hitSubring : Subring T where
  carrier := {c | ∀ a b, ∃ g : p a ⟶ p b, Φ.map g =
    (κ a).hom ≫ (𝕊).map (ModuleCat.ofHom (idemRightMul (e a) (e b) c (he b))) ≫ (κ b).inv}
  zero_mem' a b := ⟨0, by
    rw [idemRightMul_zero, Φ.map_zero]
    change 0 = _ ≫ (𝕊).map 0 ≫ _
    simp⟩
  one_mem' a b := by
    by_cases h : a = b
    · subst h
      refine ⟨𝟙 _, ?_⟩
      rw [idemRightMul_one_self e he, Φ.map_id]
      change _ = _ ≫ (𝕊).map (𝟙 _) ≫ _
      simp
    · refine ⟨0, ?_⟩
      rw [idemRightMul_one_of_ne e he horth h, Φ.map_zero]
      change 0 = _ ≫ (𝕊).map 0 ≫ _
      simp
  add_mem' {c d} hc hd a b := by
    obtain ⟨g₁, h₁⟩ := hc a b
    obtain ⟨g₂, h₂⟩ := hd a b
    refine ⟨g₁ + g₂, ?_⟩
    rw [Φ.map_add, h₁, h₂, idemRightMul_add]
    change _ = _ ≫ (𝕊).map (ModuleCat.ofHom _ + ModuleCat.ofHom _) ≫ _
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  neg_mem' {c} hc a b := by
    obtain ⟨g, h⟩ := hc a b
    refine ⟨-g, ?_⟩
    rw [Φ.map_neg, h, idemRightMul_neg]
    change _ = _ ≫ (𝕊).map (-ModuleCat.ofHom _) ≫ _
    rw [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]
    rfl
  mul_mem' {c d} hc hd a b := by
    choose g₁ h₁ using hc
    choose g₂ h₂ using hd
    refine ⟨∑ u, g₁ a u ≫ g₂ u b, ?_⟩
    rw [Φ.map_sum, idemRightMul_mul e he hsum]
    have hs : ModuleCat.ofHom (∑ u, (idemRightMul (e u) (e b) d (he b)).comp
        (idemRightMul (e a) (e u) c (he u))) = ∑ u,
          ModuleCat.ofHom (idemRightMul (e a) (e u) c (he u)) ≫
            ModuleCat.ofHom (idemRightMul (e u) (e b) d (he b)) :=
      ModuleCat.hom_ext (by simp [ModuleCat.hom_sum])
    rw [hs, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Φ.map_comp, h₁, h₂, Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- If ring generators of `T` lie in `hitSubring`, then every right multiplication between the
summands is hit. -/
theorem forall_hit_of_closure {G : Set T} (hG : Subring.closure G = ⊤)
    (hgen : G ⊆ hitSubring e he horth hsum Φ p κ) (a b : ι) (c : T) :
    ∃ g : p a ⟶ p b, Φ.map g =
      (κ a).hom ≫ (𝕊).map (ModuleCat.ofHom (idemRightMul (e a) (e b) c (he b))) ≫ (κ b).inv := by
  have hc : c ∈ hitSubring e he horth hsum Φ p κ := by
    rw [← Subring.closure_le] at hgen
    exact hgen (hG ▸ Subring.mem_top c)
  exact hc a b

end Hit

section Derived

open DG.DegreeZero
open scoped DG.DegreeZero

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

variable [DG.HasDerivedCategory.{0, 0} T] [HasDerivedCategory.{0} (ModuleCat.{0} T)]
  {X : Type} [AddCommGroup X] [DG.DGAddCommGroup X] [Module T X] [Module Tᵐᵒᵖ X]
  [DG.DGBimodule T T X]
  {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → T) (he : ∀ a, IsIdempotentElem (e a))
  (horth : ∀ a b, a ≠ b → e a * e b = 0) (hsum : ∑ a, e a = 1)

set_option hygiene false in
local notation "𝕊" => (DerivedCategory.singleFunctor (ModuleCat.{0} T) 0)

/-- **The generator form of `derivedTensorIsoIdOfIdempotents`**: the fullness hypothesis is only
required for the right multiplications by a set `G` of ring generators of `T` (`hgen`), and `Φ`
is additive on a preadditive category. In Webster's setting `G` consists of the idempotents,
dots and crossings, so `hgen` says that the vacuum functor sends the dots and crossings on
`F_𝐢 P_∅` to the left multiplications by them on `e(𝐢) T^λ`. -/
def derivedTensorIsoIdOfGenerators (S' : DerivedCategory (ModuleCat.{0} T) ⥤
      DerivedCategory (ModuleCat.{0} T)) [S'.Additive]
    (cS : dgDerivedTensor.{0} T T X ⋙ derivedComparison T ≅ derivedComparison T ⋙ S')
    {P : Type*} [Category P] [Preadditive P] (Φ : P ⥤ DerivedCategory (ModuleCat.{0} T))
    [Φ.Additive] (εΦ : Φ ⋙ S' ≅ Φ) (p : ι → P)
    (κ : ∀ a, Φ.obj (p a) ≅ (𝕊).obj (ModuleCat.of T (idemLeftIdeal (e a))))
    {G : Set T} (hG : Subring.closure G = ⊤) (hgen : G ⊆ hitSubring e he horth hsum Φ p κ) :
    S' ≅ 𝟭 _ :=
  derivedTensorIsoIdOfIdempotents e he horth hsum S' cS Φ εΦ p κ
    (forall_hit_of_closure e he horth hsum Φ p κ hG hgen)

end Derived

end Categorification
