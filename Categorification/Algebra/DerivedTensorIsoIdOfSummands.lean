/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DGDerivedTensorIsoIdModuleCat

set_option backward.isDefEq.respectTransparency false

/-!
# Isomorphisms fixing the regular module from isomorphisms on its summands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.22: "it suffices to check `S P_∅ ≅ P_∅`, since any choice of isomorphism induces
isomorphisms between functors". In the bimodule form of this step
(`Categorification.derivedTensorIsoIdOfRegularIsoModuleCat`), the input is an isomorphism
`φ : S(T) ≅ T` commuting with the right multiplications of `T`. This file produces `φ` from the
data that equivariance and fullness provide:

* `biproductEndoIso`, `biproductEndoIso_comm`: isomorphisms `S(Yₐ) ≅ Yₐ` for an additive
  endofunctor `S` give `S(⨁ Y) ≅ ⨁ Y`, commuting with every endomorphism of `⨁ Y` whose matrix
  entries commute with them;
* `summandEndoIso`, `summandEndoIso_comm`: for a functor `Φ : 𝒫 ⥤ 𝒟` with `Φ ⋙ S ≅ Φ`, full on a
  finite family `pₐ`, and `R ≅ ⨁ₐ Φ(pₐ)`, the induced `S(R) ≅ R` commutes with *every*
  endomorphism of `R`;
* `idemLeftIdeal`, `idemRightMul`, `eq_idemRightMul`, `regularLinearEquivPi`: for a complete
  family of orthogonal idempotents `eₐ` of a ring `T`, `T ≅ ⊕ₐ T eₐ`, and every module map
  `T eₐ → T e_b` is a right multiplication (`Hom(T eₐ, T e_b) = eₐ T e_b`);
* **`derivedTensorIsoIdOfSummands`**, **`derivedTensorIsoIdOfIdempotents`**: an endofunctor `S'`
  of `D(Mod T)` presented as a derived tensor product, with `Φ ⋙ S' ≅ Φ` for a functor `Φ`
  whose values on `pₐ` are the summands `T eₐ` and which hits every right multiplication
  between them, is isomorphic to the identity.

In Webster's setting `T = (T^λ)ᵐᵒᵖ` (right `T^λ`-modules), `Φ` is the vacuum functor out of the
category of projectives with `pₐ = F_𝐢 P_∅`, `T eₐ = e(𝐢) T^λ`, and the right multiplications
of `Tᵐᵒᵖ` are the left multiplications of `T^λ`; `hsurj` is the fullness
`Hom(F_𝐢 P_∅, F_𝐣 P_∅) ↠ e(𝐣) T^λ e(𝐢)`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Categorification

section Biproduct

variable {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D] {ι : Type} [Fintype ι]
  (Y : ι → D) (S : D ⥤ D) [S.Additive] (ε : ∀ a, S.obj (Y a) ≅ Y a)

/-- The isomorphism `S(⨁ Y) ≅ ⨁ Y` assembled from isomorphisms `ε a : S(Y a) ≅ Y a`. -/
def biproductEndoIso : S.obj (⨁ Y) ≅ ⨁ Y :=
  S.mapBiproduct Y ≪≫ biproduct.mapIso ε

/-- `biproductEndoIso` commutes with an endomorphism of `⨁ Y` whose matrix entries commute with
the `ε a`. -/
theorem biproductEndoIso_comm (f : ⨁ Y ⟶ ⨁ Y)
    (hε : ∀ a b, S.map (biproduct.ι Y a ≫ f ≫ biproduct.π Y b) ≫ (ε b).hom =
      (ε a).hom ≫ biproduct.ι Y a ≫ f ≫ biproduct.π Y b) :
    S.map f ≫ (biproductEndoIso Y S ε).hom = (biproductEndoIso Y S ε).hom ≫ f := by
  rw [← cancel_epi (biproductEndoIso Y S ε).inv, Iso.inv_hom_id_assoc]
  refine biproduct.hom_ext' _ _ fun a => biproduct.hom_ext _ _ fun b => ?_
  simp only [biproductEndoIso, Iso.trans_inv, Iso.trans_hom, Functor.mapBiproduct_inv,
    Functor.mapBiproduct_hom, biproduct.mapIso_inv, biproduct.mapIso_hom, Category.assoc,
    biproduct.ι_map_assoc, biproduct.ι_desc_assoc, biproduct.map_π]
  have h : (biproduct.lift fun j => S.map (biproduct.π Y j)) ≫ biproduct.π (S.obj ∘ Y) b =
    S.map (biproduct.π Y b) := biproduct.lift_π _ _
  rw [reassoc_of% h, Iso.inv_comp_eq]
  simpa only [Functor.map_comp, Category.assoc] using hε a b

section Image

variable {P : Type*} [Category P] (Φ : P ⥤ D) (εΦ : Φ ⋙ S ≅ Φ) (p : ι → P)
  {R : D} (e : R ≅ ⨁ fun a => Φ.obj (p a))

/-- The isomorphism `S(R) ≅ R` induced by `Φ ⋙ S ≅ Φ` and a decomposition `R ≅ ⨁ₐ Φ(pₐ)`. -/
def summandEndoIso : S.obj R ≅ R :=
  S.mapIso e ≪≫ biproductEndoIso (fun a => Φ.obj (p a)) S (fun a => εΦ.app (p a)) ≪≫ e.symm

/-- If `Φ` is full on the family `p`, then `summandEndoIso` commutes with every endomorphism of
`R`. -/
theorem summandEndoIso_comm
    (hfull : ∀ a b (f : Φ.obj (p a) ⟶ Φ.obj (p b)), ∃ g : p a ⟶ p b, Φ.map g = f)
    (g : R ⟶ R) :
    S.map g ≫ (summandEndoIso S Φ εΦ p e).hom = (summandEndoIso S Φ εΦ p e).hom ≫ g := by
  have hB := biproductEndoIso_comm (fun a => Φ.obj (p a)) S (fun a => εΦ.app (p a))
    (e.inv ≫ g ≫ e.hom) fun a b => by
      obtain ⟨h, hh⟩ := hfull a b (biproduct.ι (fun a => Φ.obj (p a)) a ≫
        (e.inv ≫ g ≫ e.hom) ≫ biproduct.π (fun a => Φ.obj (p a)) b)
      rw [← hh]
      exact εΦ.hom.naturality h
  have h1 : S.map g ≫ S.map e.hom = S.map e.hom ≫ S.map (e.inv ≫ g ≫ e.hom) := by
    simp only [← Functor.map_comp, Iso.hom_inv_id_assoc]
  simp only [summandEndoIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hB]
  simp

end Image

end Biproduct

section Idempotents

variable {T : Type} [Ring T]

/-- The left ideal `T e = {x | x e = x}` of an element `e` (a direct summand of `T` when `e` is
idempotent). -/
def idemLeftIdeal (e : T) : Submodule T T where
  carrier := {x | x * e = x}
  add_mem' {x y} hx hy := by
    change x * e = x at hx; change y * e = y at hy
    change (x + y) * e = x + y
    rw [add_mul, hx, hy]
  zero_mem' := zero_mul e
  smul_mem' r x hx := by
    change x * e = x at hx
    change r * x * e = r * x
    rw [mul_assoc, hx]

@[simp]
theorem mem_idemLeftIdeal {e x : T} : x ∈ idemLeftIdeal e ↔ x * e = x := Iff.rfl

/-- **Right multiplication `x ↦ x c f`** from `T e` to `T f`, a map of left modules. -/
def idemRightMul (e f c : T) (hf : IsIdempotentElem f) : idemLeftIdeal e →ₗ[T] idemLeftIdeal f where
  toFun x := ⟨x * c * f, by rw [mem_idemLeftIdeal, mul_assoc _ f f, hf.eq]⟩
  map_add' x y := Subtype.ext (by simp [add_mul])
  map_smul' r x := Subtype.ext (by simp [mul_assoc])

/-- Every map of left modules `T e → T f` is a right multiplication. -/
theorem eq_idemRightMul {e f : T} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : idemLeftIdeal e →ₗ[T] idemLeftIdeal f) :
    h = idemRightMul e f (h ⟨e, he.eq⟩ : T) hf := by
  ext ⟨x, hx⟩
  have hx' : (⟨x, hx⟩ : idemLeftIdeal e) = x • ⟨e, he.eq⟩ := Subtype.ext hx.symm
  change (h ⟨x, hx⟩ : T) = x * (h ⟨e, he.eq⟩ : T) * f
  rw [hx', map_smul, Submodule.coe_smul, smul_eq_mul, mul_assoc,
    (h ⟨e, he.eq⟩).2]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → T) (he : ∀ a, IsIdempotentElem (e a))
  (horth : ∀ a b, a ≠ b → e a * e b = 0) (hsum : ∑ a, e a = 1)

/-- **`T ≅ ⊕ₐ T eₐ`** for a complete family of orthogonal idempotents. -/
def regularLinearEquivPi : T ≃ₗ[T] ∀ a, idemLeftIdeal (e a) where
  toFun x a := ⟨x * e a, by rw [mem_idemLeftIdeal, mul_assoc, (he a).eq]⟩
  map_add' x y := funext fun a => Subtype.ext (add_mul x y (e a))
  map_smul' r x := funext fun a => Subtype.ext (mul_assoc r x (e a))
  invFun y := ∑ a, (y a : T)
  left_inv x := by
    change ∑ a, x * e a = x
    rw [← Finset.mul_sum, hsum, mul_one]
  right_inv y := funext fun a => Subtype.ext (by
    change (∑ b, (y b : T)) * e a = y a
    rw [Finset.sum_mul, Finset.sum_eq_single a]
    · exact (y a).2
    · intro b _ hb
      rw [← (y b).2, mul_assoc, horth b a hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h)

end Idempotents

section Derived

open DG.DegreeZero
open scoped DG.DegreeZero

attribute [local instance] tensorFunctorSignCommShift homotopyTensorFunctorSignCommShift

variable {T : Type} [Ring T] [DG.HasDerivedCategory.{0, 0} T]
  [HasDerivedCategory.{0} (ModuleCat.{0} T)]
  {X : Type} [AddCommGroup X] [DG.DGAddCommGroup X] [Module T X] [Module Tᵐᵒᵖ X]
  [DG.DGBimodule T T X]

set_option hygiene false in
local notation "𝒟" => DerivedCategory (ModuleCat.{0} T)

set_option hygiene false in
local notation "𝕊" => (DerivedCategory.singleFunctor (ModuleCat.{0} T) 0)

/-- **A derived tensor functor which is the identity on the summands of the regular module, up
to a full functor, is the identity.** Let `S'` be an additive endofunctor of `D(Mod T)` with
`cS : (X ⊗ᴸ_T -) ⋙ E ≅ E ⋙ S'` for the comparison `E`, and `Φ : 𝒫 ⥤ D(Mod T)` with
`εΦ : Φ ⋙ S' ≅ Φ`, full on a finite family `pₐ` (`hfull`) with `T ≅ ⨁ₐ Φ(pₐ)`. Then `S' ≅ 𝟭`. -/
def derivedTensorIsoIdOfSummands (S' : 𝒟 ⥤ 𝒟) [S'.Additive]
    (cS : dgDerivedTensor.{0} T T X ⋙ derivedComparison T ≅ derivedComparison T ⋙ S')
    {P : Type*} [Category P] (Φ : P ⥤ 𝒟) (εΦ : Φ ⋙ S' ≅ Φ) {ι : Type} [Fintype ι]
    (p : ι → P) (hfull : ∀ a b (f : Φ.obj (p a) ⟶ Φ.obj (p b)), ∃ g : p a ⟶ p b, Φ.map g = f)
    (e : regularSingle T ≅ ⨁ fun a => Φ.obj (p a)) : S' ≅ 𝟭 _ :=
  derivedTensorIsoIdOfRegularIsoModuleCat S' cS (summandEndoIso S' Φ εΦ p e)
    fun _ => summandEndoIso_comm S' Φ εΦ p e hfull _

variable {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → T) (he : ∀ a, IsIdempotentElem (e a))
  (horth : ∀ a b, a ≠ b → e a * e b = 0) (hsum : ∑ a, e a = 1)

/-- `T ≅ ⨁ₐ T eₐ` in `D(Mod T)`, for a complete family of orthogonal idempotents. -/
def regularSingleIsoBiproduct :
    regularSingle T ≅ ⨁ fun a => (𝕊).obj (ModuleCat.of T (idemLeftIdeal (e a))) :=
  (𝕊).mapIso ((regularLinearEquivPi e he horth hsum).toModuleIso ≪≫
    (ModuleCat.biproductIsoPi fun a => ModuleCat.of T (idemLeftIdeal (e a))).symm) ≪≫
    (𝕊).mapBiproduct _

/-- **The idempotent form**: as `derivedTensorIsoIdOfSummands`, with `Φ(pₐ) ≅ T eₐ` (`κ`) for a
complete family of orthogonal idempotents `eₐ`, and the fullness hypothesis that every right
multiplication `T eₐ → T e_b`, `x ↦ x c e_b`, is the image of a morphism `pₐ ⟶ p_b` (`hsurj`). For
`T = (T^λ)ᵐᵒᵖ` this is Webster's `Hom(F_𝐢 P_∅, F_𝐣 P_∅) ↠ e(𝐣) T^λ e(𝐢)`. -/
def derivedTensorIsoIdOfIdempotents (S' : 𝒟 ⥤ 𝒟) [S'.Additive]
    (cS : dgDerivedTensor.{0} T T X ⋙ derivedComparison T ≅ derivedComparison T ⋙ S')
    {P : Type*} [Category P] (Φ : P ⥤ 𝒟) (εΦ : Φ ⋙ S' ≅ Φ) (p : ι → P)
    (κ : ∀ a, Φ.obj (p a) ≅ (𝕊).obj (ModuleCat.of T (idemLeftIdeal (e a))))
    (hsurj : ∀ a b (c : T), ∃ g : p a ⟶ p b, Φ.map g =
      (κ a).hom ≫ (𝕊).map (ModuleCat.ofHom (idemRightMul (e a) (e b) c (he b))) ≫ (κ b).inv) :
    S' ≅ 𝟭 _ :=
  derivedTensorIsoIdOfSummands S' cS Φ εΦ p
    (fun a b f => by
      obtain ⟨h, hh⟩ := (𝕊).map_surjective ((κ a).inv ≫ f ≫ (κ b).hom)
      obtain ⟨g, hg⟩ := hsurj a b (h.hom ⟨e a, (he a).eq⟩ : T)
      refine ⟨g, ?_⟩
      have h' : ModuleCat.ofHom (idemRightMul (e a) (e b) (h.hom ⟨e a, (he a).eq⟩ : T) (he b)) =
          h := ModuleCat.hom_ext (eq_idemRightMul (he a) (he b) h.hom).symm
      rw [hg, h', hh]
      simp)
    (regularSingleIsoBiproduct e he horth hsum ≪≫ biproduct.mapIso fun a => (κ a).symm)

end Derived

end Categorification
