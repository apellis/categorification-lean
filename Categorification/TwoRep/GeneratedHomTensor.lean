/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GeneratedAdjunction
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.CategoryTheory.HomCongr

/-!
# The Hom–tensor map of a strongly equivariant functor

Let `β : ℵ₁ ⟶ ℵ₂` be a strongly equivariant functor between 2-representations of `B`, with
`ℵ₁(f) P₀`, `f : a ⟶ c`, full and dense (`Full`, `IsDenseFamily`), so that every
`c ∈ End(β(P₀))` extends to a modification `β ⟶ β` (`homAt`). Suppose that `ℵ₁(a)` is
`L`-linear for a commutative ring `L` and that each `ℵ₁(f)`, `f : a ⟶ a`, is `L`-linear. Then
`L` acts on `End(β(P₀))` through `r ↦ β(r • 𝟙)` (`ActEnd`), and there is a map

`Θ_{M,N} : Hom(M, N) ⊗_L End(β(P₀)) → Hom(β(M), β(N))`, `h ⊗ c ↦ β(h) ≫ c_N`

(`homTensorMap`). This file proves that `Θ_{M,N}` is bijective for all `M`, `N` in `ℵ₁(a)` as
soon as it is bijective for `M = P₀`, `N = ℵ₁(f) P₀`, provided every `f : a ⟶ a` has a right
adjoint (`homTensorMap_bijective`), with the base case `Θ_{P₀,P₀}` for `End(P₀) = L`
(`homTensorMap_bijective_self`).

This is the Hom–tensor form of the full faithfulness in B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v2, Corollary 3.27 (2): the reduction from
`Hom(F_𝐢 P_∅, N)` to `Hom(P_∅, E_𝐢 N)` and from there to `End(P_∅) = Ř^λ_λ`.
-/

namespace Categorification.TwoRep.Generated

open CategoryTheory Bicategory Limits Pseudofunctor.StrongTrans
open scoped TensorProduct

universe w v u w₁ v₁ u₁ w₂

variable {k : Type w} [CommRing k] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {ℵ₁ ℵ₂ : Pseudofunctor B (LinearCat.{w, v, u} k)} {a : B} {P₀ : ℵ₁.obj a}
  (L : Type w₂) [CommRing L] [Linear L (ℵ₁.obj a)]

/-- The action of `L` on `β(P₀)`. -/
noncomputable def scalarEnd (β : ℵ₁ ⟶ ℵ₂) (P₀ : ℵ₁.obj a) : L →+* End ((β.app a).obj.obj P₀) where
  toFun r := (β.app a).obj.map (r • 𝟙 P₀)
  map_one' := by rw [one_smul, CategoryTheory.Functor.map_id]; rfl
  map_mul' r s := by
    change _ = (β.app a).obj.map (s • 𝟙 P₀) ≫ (β.app a).obj.map (r • 𝟙 P₀)
    rw [← Functor.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, mul_smul, smul_comm]
  map_zero' := by rw [zero_smul, Functor.map_zero]
  map_add' r s := by rw [add_smul, Functor.map_add]

/-- `End(β(P₀))` as an `L`-module through `scalarEnd`. -/
def ActEnd (β : ℵ₁ ⟶ ℵ₂) (P₀ : ℵ₁.obj a) : Type v := End ((β.app a).obj.obj P₀)

noncomputable instance (β : ℵ₁ ⟶ ℵ₂) : Ring (ActEnd β P₀) := inferInstanceAs (Ring (End _))

noncomputable instance (β : ℵ₁ ⟶ ℵ₂) : Module L (ActEnd β P₀) :=
  Module.compHom (End ((β.app a).obj.obj P₀)) (scalarEnd L β P₀)

theorem actEnd_smul (β : ℵ₁ ⟶ ℵ₂) (r : L) (c : ActEnd β P₀) :
    r • c = (show (β.app a).obj.obj P₀ ⟶ _ from c) ≫ (β.app a).obj.map (r • 𝟙 P₀) := rfl

variable (hF : Full ℵ₁ P₀) (hD : ∀ c : B, IsDenseFamily (family P₀ c))
  (hL : ∀ (f : a ⟶ a) (r : L) (X : ℵ₁.obj a), (ℵ₁.map f).obj.map (r • 𝟙 X) = r • 𝟙 _)

include hL in
theorem homAt_scalarEnd (β : ℵ₁ ⟶ ℵ₂) (r : L) (N : ℵ₁.obj a) :
    (homAt (scalarEnd L β P₀ r) hF hD a).hom.app N = (β.app a).obj.map (r • 𝟙 N) := by
  let τ : (β.app a).obj ⟶ (β.app a).obj :=
    { app := fun N => (β.app a).obj.map (r • 𝟙 N)
      naturality := fun X Y h => by
        rw [← Functor.map_comp, ← Functor.map_comp, Linear.comp_smul, Linear.smul_comp,
          Category.id_comp, Category.comp_id] }
  have := (hD a).natTrans_ext (α := (homAt (scalarEnd L β P₀ r) hF hD a).hom) (β := τ)
    (fun f => by
      rw [homAt_hom_app]
      change (natApp β f P₀).hom ≫ (ℵ₂.map f).obj.map ((β.app a).obj.map (r • 𝟙 P₀)) ≫
        (natApp β f P₀).inv = (β.app a).obj.map (r • 𝟙 _)
      have N' := (β.naturality f).hom.hom.naturality (r • 𝟙 P₀)
      change (β.app a).obj.map ((ℵ₁.map f).obj.map (r • 𝟙 P₀)) ≫ (natApp β f P₀).hom =
        (natApp β f P₀).hom ≫ (ℵ₂.map f).obj.map ((β.app a).obj.map (r • 𝟙 P₀)) at N'
      rw [← reassoc_of% N', hL, Iso.hom_inv_id, Category.comp_id])
  exact congrArg (fun θ => NatTrans.app θ N) this


theorem homAt_zero {β β' : ℵ₁ ⟶ ℵ₂} (X : ℵ₁.obj a) :
    (homAt (0 : (β.app a).obj.obj P₀ ⟶ (β'.app a).obj.obj P₀) hF hD a).hom.app X = 0 := by
  have := homAt_smul hF hD (0 : k) (0 : (β.app a).obj.obj P₀ ⟶ (β'.app a).obj.obj P₀) X
  rwa [zero_smul, zero_smul] at this

variable (β : ℵ₁ ⟶ ℵ₂)

/-- The pairing `(h, c) ↦ β(h) ≫ c_N`, `c_N` the component at `N` of the modification extending
`c ∈ End(β(P₀))`. -/
noncomputable def homTensorPair (M N : ℵ₁.obj a) :
    (M ⟶ N) →+ ActEnd β P₀ →+ ((β.app a).obj.obj M ⟶ (β.app a).obj.obj N) where
  toFun h :=
    { toFun := fun c => (β.app a).obj.map h ≫ (homAt c hF hD a).hom.app N
      map_zero' := by
        change _ ≫ (homAt (0 : (β.app a).obj.obj P₀ ⟶ _) hF hD a).hom.app N = 0
        rw [homAt_zero, comp_zero]
      map_add' := fun c₀ c₁ => by
        change _ ≫ (homAt (c₀ + c₁ : (β.app a).obj.obj P₀ ⟶ _) hF hD a).hom.app N = _
        erw [homAt_add, Preadditive.comp_add] }
  map_zero' := by ext c; simp
  map_add' h h' := by ext c; simp [Preadditive.add_comp]

include hL in
theorem homTensorPair_smul (M N : ℵ₁.obj a) (r : L) (h : M ⟶ N) (c : ActEnd β P₀) :
    homTensorPair hF hD β M N (r • h) c = homTensorPair hF hD β M N h (r • c) := by
  change (β.app a).obj.map (r • h) ≫ _ =
    (β.app a).obj.map h ≫ (homAt ((show (β.app a).obj.obj P₀ ⟶ _ from c) ≫
      scalarEnd L β P₀ r) hF hD a).hom.app N
  rw [homAt_comp, homAt_scalarEnd L hF hD hL, ← (homAt c hF hD a).hom.naturality,
    ← Category.assoc, ← Functor.map_comp, Linear.comp_smul, Category.comp_id]

/-- **The Hom–tensor map** `Hom(M, N) ⊗_L End(β(P₀)) → Hom(β(M), β(N))`,
`h ⊗ c ↦ β(h) ≫ c_N`. -/
noncomputable def homTensorMap (M N : ℵ₁.obj a) :
    (M ⟶ N) ⊗[L] ActEnd β P₀ →+ ((β.app a).obj.obj M ⟶ (β.app a).obj.obj N) :=
  TensorProduct.liftAddHom (homTensorPair hF hD β M N) (homTensorPair_smul L hF hD hL β M N)

theorem homTensorMap_tmul (M N : ℵ₁.obj a) (h : M ⟶ N) (c : ActEnd β P₀) :
    homTensorMap L hF hD hL β M N (h ⊗ₜ c) =
      (β.app a).obj.map h ≫ (homAt c hF hD a).hom.app N := rfl

theorem homTensorMap_rTensor_rightComp {M N N' : ℵ₁.obj a} (n : N ⟶ N')
    (t : (M ⟶ N) ⊗[L] ActEnd β P₀) :
    homTensorMap L hF hD hL β M N' ((Linear.rightComp L M n).rTensor _ t) =
      homTensorMap L hF hD hL β M N t ≫ (β.app a).obj.map n := by
  induction t with
  | tmul h c =>
    rw [LinearMap.rTensor_tmul, homTensorMap_tmul, homTensorMap_tmul, Linear.rightComp_apply,
      Functor.map_comp, Category.assoc, Category.assoc, (homAt c hF hD a).hom.naturality]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, Preadditive.add_comp]

theorem homTensorMap_rTensor_leftComp {M M' N : ℵ₁.obj a} (m : M' ⟶ M)
    (t : (M ⟶ N) ⊗[L] ActEnd β P₀) :
    homTensorMap L hF hD hL β M' N ((Linear.leftComp L N m).rTensor _ t) =
      (β.app a).obj.map m ≫ homTensorMap L hF hD hL β M N t := by
  induction t with
  | tmul h c =>
    rw [LinearMap.rTensor_tmul, homTensorMap_tmul, homTensorMap_tmul, Linear.leftComp_apply,
      Functor.map_comp, Category.assoc]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, Preadditive.comp_add]


/-- `Θ_{M,N}` is bijective when `N` is a retract of a sum of objects `Y` for which `Θ_{M,Y}` is
bijective. -/
theorem homTensorMap_bijective_of_retract {T : Type*} {P : T → ℵ₁.obj a} {M N : ℵ₁.obj a}
    (d : RetractDecomposition P N)
    (h : ∀ i, Function.Bijective (homTensorMap L hF hD hL β M (P (d.t i)))) :
    Function.Bijective (homTensorMap L hF hD hL β M N) := by
  let e i := AddEquiv.ofBijective _ (h i)
  let ψ : ((β.app a).obj.obj M ⟶ (β.app a).obj.obj N) → (M ⟶ N) ⊗[L] ActEnd β P₀ :=
    fun x => ∑ i, (Linear.rightComp L M (d.p i)).rTensor _ ((e i).symm (x ≫ (β.app a).obj.map (d.q i)))
  have hψ : ∀ x y, ψ (x + y) = ψ x + ψ y := fun x y => by
    simp only [ψ, Preadditive.add_comp, map_add, Finset.sum_add_distrib]
  refine Function.bijective_iff_has_inverse.mpr ⟨ψ, fun t => ?_, fun x => ?_⟩
  · induction t with
    | tmul h' c =>
      have hi : ∀ i, (e i).symm (homTensorMap L hF hD hL β M N (h' ⊗ₜ c) ≫
          (β.app a).obj.map (d.q i)) = (h' ≫ d.q i) ⊗ₜ c := fun i => by
        rw [AddEquiv.symm_apply_eq]
        change _ = homTensorMap L hF hD hL β M _ ((h' ≫ d.q i) ⊗ₜ c)
        rw [homTensorMap_tmul, homTensorMap_tmul, Functor.map_comp, Category.assoc,
          Category.assoc, (homAt c hF hD a).hom.naturality]
      simp only [ψ, hi, LinearMap.rTensor_tmul, Linear.rightComp_apply, Category.assoc,
        ← TensorProduct.sum_tmul, ← Preadditive.comp_sum, d.sum_q_p, Category.comp_id]
    | add t t' ht ht' => rw [map_add, hψ, ht, ht']
  · simp only [ψ, map_sum, homTensorMap_rTensor_rightComp]
    have hi : ∀ i y, homTensorMap L hF hD hL β M (P (d.t i)) ((e i).symm y) = y :=
      fun i y => (e i).apply_symm_apply y
    simp only [hi, Category.assoc, ← Functor.map_comp, ← Preadditive.comp_sum, ← Functor.map_sum,
      d.sum_q_p, CategoryTheory.Functor.map_id, Category.comp_id]

/-- `Θ_{M,N}` is bijective when `M` is a retract of a sum of objects `X` for which `Θ_{X,N}` is
bijective. -/
theorem homTensorMap_bijective_of_retract_left {T : Type*} {P : T → ℵ₁.obj a} {M N : ℵ₁.obj a}
    (d : RetractDecomposition P M)
    (h : ∀ i, Function.Bijective (homTensorMap L hF hD hL β (P (d.t i)) N)) :
    Function.Bijective (homTensorMap L hF hD hL β M N) := by
  let e i := AddEquiv.ofBijective _ (h i)
  let ψ : ((β.app a).obj.obj M ⟶ (β.app a).obj.obj N) → (M ⟶ N) ⊗[L] ActEnd β P₀ :=
    fun x => ∑ i, (Linear.leftComp L N (d.q i)).rTensor _ ((e i).symm ((β.app a).obj.map (d.p i) ≫ x))
  have hψ : ∀ x y, ψ (x + y) = ψ x + ψ y := fun x y => by
    simp only [ψ, Preadditive.comp_add, map_add, Finset.sum_add_distrib]
  refine Function.bijective_iff_has_inverse.mpr ⟨ψ, fun t => ?_, fun x => ?_⟩
  · induction t with
    | tmul h' c =>
      have hi : ∀ i, (e i).symm ((β.app a).obj.map (d.p i) ≫
          homTensorMap L hF hD hL β M N (h' ⊗ₜ c)) = (d.p i ≫ h') ⊗ₜ c := fun i => by
        rw [AddEquiv.symm_apply_eq]
        change _ = homTensorMap L hF hD hL β _ N ((d.p i ≫ h') ⊗ₜ c)
        rw [homTensorMap_tmul, homTensorMap_tmul, Functor.map_comp, Category.assoc]
      simp only [ψ, hi, LinearMap.rTensor_tmul, Linear.leftComp_apply, ← Category.assoc,
        ← TensorProduct.sum_tmul, ← Preadditive.sum_comp, d.sum_q_p, Category.id_comp]
    | add t t' ht ht' => rw [map_add, hψ, ht, ht']
  · simp only [ψ, map_sum, homTensorMap_rTensor_leftComp]
    have hi : ∀ i y, homTensorMap L hF hD hL β (P (d.t i)) N ((e i).symm y) = y :=
      fun i y => (e i).apply_symm_apply y
    simp only [hi, ← Category.assoc, ← Functor.map_comp, ← Preadditive.sum_comp, ← Functor.map_sum,
      d.sum_q_p, CategoryTheory.Functor.map_id, Category.id_comp]


include hL in
theorem map_smul_of_loop (f : a ⟶ a) (r : L) {X Y : ℵ₁.obj a} (h : X ⟶ Y) :
    (ℵ₁.map f).obj.map (r • h) = r • (ℵ₁.map f).obj.map h := by
  have e : r • h = h ≫ (r • 𝟙 Y) := by rw [Linear.comp_smul, Category.comp_id]
  rw [e, Functor.map_comp, hL, Linear.comp_smul, Category.comp_id]

/-- The adjunction isomorphism `Hom(ℵ₁(f) X, N) ≅ Hom(X, ℵ₁(g) N)` as an `L`-linear map. -/
noncomputable def adjHomEquiv {f g : a ⟶ a} (adj : f ⊣ g) (X N : ℵ₁.obj a) :
    ((ℵ₁.map f).obj.obj X ⟶ N) ≃ₗ[L] (X ⟶ (ℵ₁.map g).obj.obj N) :=
  { (mapAdj ℵ₁ adj).homEquiv X N with
    map_add' := fun h h' => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, Functor.map_add,
        Preadditive.comp_add]
    map_smul' := fun r h => by
      simp only [Equiv.toFun_as_coe, Adjunction.homEquiv_unit, RingHom.id_apply]
      rw [map_smul_of_loop L hL, Linear.comp_smul] }

/-- The adjunction isomorphism on the images under `β`. -/
noncomputable def adjHomEquivImage {f g : a ⟶ a} (adj : f ⊣ g) (X N : ℵ₁.obj a) :
    ((β.app a).obj.obj ((ℵ₁.map f).obj.obj X) ⟶ (β.app a).obj.obj N) ≃
      ((β.app a).obj.obj X ⟶ (β.app a).obj.obj ((ℵ₁.map g).obj.obj N)) :=
  ((natApp β f X).homCongr (Iso.refl _)).trans
    (((mapAdj ℵ₂ adj).homEquiv _ _).trans ((Iso.refl _).homCongr (natApp β g N).symm))

include hL in
theorem adjHomEquivImage_homTensorMap {f g : a ⟶ a} (adj : f ⊣ g) (X N : ℵ₁.obj a)
    (t : ((ℵ₁.map f).obj.obj X ⟶ N) ⊗[L] ActEnd β P₀) :
    adjHomEquivImage β adj X N (homTensorMap L hF hD hL β _ N t) =
      homTensorMap L hF hD hL β X _ ((adjHomEquiv L hL adj X N).rTensor _ t) := by
  induction t with
  | tmul h c =>
    have := homEquiv_natApp_map_modification (modificationOfHom c hF hD) adj h
    simp only [adjHomEquivImage, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
      Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.comp_id, homTensorMap_tmul,
      LinearEquiv.rTensor_tmul]
    change (mapAdj ℵ₂ adj).homEquiv _ _ ((natApp β f X).inv ≫ (β.app a).obj.map h ≫
      ((modificationOfHom c hF hD).app a).hom.app N) ≫ _ = _ at *
    rw [this, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  | add t t' ht ht' =>
    have hadd : ∀ x y, adjHomEquivImage β adj X N (x + y) =
        adjHomEquivImage β adj X N x + adjHomEquivImage β adj X N y := fun x y => by
      simp only [adjHomEquivImage, Equiv.trans_apply, Iso.homCongr_apply,
        Adjunction.homEquiv_unit, Preadditive.comp_add, Preadditive.add_comp, Functor.map_add]
    rw [map_add, hadd, ht, ht', map_add, map_add]

/-- **Adjunction step**: for `f ⊣ g`, `Θ_{ℵ₁(f) X, N}` is bijective iff
`Θ_{X, ℵ₁(g) N}` is. -/
theorem homTensorMap_bijective_iff_of_adjunction {f g : a ⟶ a} (adj : f ⊣ g)
    (X N : ℵ₁.obj a) :
    Function.Bijective (homTensorMap L hF hD hL β ((ℵ₁.map f).obj.obj X) N) ↔
      Function.Bijective (homTensorMap L hF hD hL β X ((ℵ₁.map g).obj.obj N)) := by
  rw [← (adjHomEquivImage β adj X N).comp_bijective,
    ← ((adjHomEquiv L hL adj X N).rTensor (ActEnd β P₀)).toEquiv.bijective_comp]
  have : (adjHomEquivImage β adj X N) ∘ homTensorMap L hF hD hL β _ N =
      homTensorMap L hF hD hL β X _ ∘ ((adjHomEquiv L hL adj X N).rTensor (ActEnd β P₀)) :=
    funext fun t => adjHomEquivImage_homTensorMap L hF hD hL β adj X N t
  rw [this]
  rfl

/-- **Base case**: if `L → End(P₀)`, `r ↦ r • 𝟙`, is bijective, `Θ_{P₀,P₀}` is bijective. -/
theorem homTensorMap_bijective_self (hEnd : Function.Bijective (fun r : L => r • 𝟙 P₀)) :
    Function.Bijective (homTensorMap L hF hD hL β P₀ P₀) := by
  let e : L ≃ₗ[L] (P₀ ⟶ P₀) := LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ (𝟙 P₀)) hEnd
  let g : ActEnd β P₀ ≃ₗ[L] (P₀ ⟶ P₀) ⊗[L] ActEnd β P₀ :=
    (TensorProduct.lid L (ActEnd β P₀)).symm.trans (e.rTensor _)
  rw [← g.toEquiv.bijective_comp]
  have : homTensorMap L hF hD hL β P₀ P₀ ∘ g.toEquiv = fun c => c := funext fun c => by
    change homTensorMap L hF hD hL β P₀ P₀ (e 1 ⊗ₜ c) = c
    rw [homTensorMap_tmul]
    change (β.app a).obj.map ((1 : L) • 𝟙 P₀) ≫ _ = _
    rw [one_smul, CategoryTheory.Functor.map_id, Category.id_comp]
    exact homAt_app (show (β.app a).obj.obj P₀ ⟶ _ from c) hF hD
  rw [this]
  exact Function.bijective_id

/-- `Θ_{M,N}` is bijective when both Hom spaces are subsingletons. -/
theorem homTensorMap_bijective_of_subsingleton (M N : ℵ₁.obj a) [Subsingleton (M ⟶ N)]
    [Subsingleton ((β.app a).obj.obj M ⟶ (β.app a).obj.obj N)] :
    Function.Bijective (homTensorMap L hF hD hL β M N) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- `Θ_{M,N'}` is bijective when `Θ_{M,N}` is and `N ≅ N'`. -/
theorem homTensorMap_bijective_of_iso {M N N' : ℵ₁.obj a} (e : N ≅ N')
    (h : Function.Bijective (homTensorMap L hF hD hL β M N)) :
    Function.Bijective (homTensorMap L hF hD hL β M N') :=
  homTensorMap_bijective_of_retract L hF hD hL β (P := fun _ : Unit => N)
    { n := 1, t := fun _ => (), q := fun _ => e.inv, p := fun _ => e.hom
      sum_q_p := by simp } fun _ => h


/-- Hom spaces into `ℵ₁(g) Y` vanish when the left adjoint `ℵ₁(f)` kills the source. -/
theorem subsingleton_hom_of_adjunction {f g : a ⟶ a} (adj : f ⊣ g) {X Y : ℵ₁.obj a}
    (hX : IsZero ((ℵ₁.map f).obj.obj X)) : Subsingleton (X ⟶ (ℵ₁.map g).obj.obj Y) :=
  haveI : Subsingleton ((ℵ₁.map f).obj.obj X ⟶ Y) := ⟨fun _ _ => hX.eq_of_src _ _⟩
  ((mapAdj ℵ₁ adj).homEquiv X Y).symm.subsingleton

/-- The same vanishing for the images under `β`. -/
theorem subsingleton_hom_image_of_adjunction {f g : a ⟶ a} (adj : f ⊣ g) {X Y : ℵ₁.obj a}
    (hX : IsZero ((ℵ₁.map f).obj.obj X)) :
    Subsingleton ((β.app a).obj.obj X ⟶ (β.app a).obj.obj ((ℵ₁.map g).obj.obj Y)) :=
  haveI : Subsingleton ((β.app a).obj.obj ((ℵ₁.map f).obj.obj X) ⟶ (β.app a).obj.obj Y) :=
    ⟨fun _ _ => ((β.app a).obj.map_isZero hX).eq_of_src _ _⟩
  (adjHomEquivImage β adj X Y).symm.subsingleton

/-- **Reduction of the Hom–tensor bijection to `P₀`**: if every endomorphism 1-morphism of `a`
has a right adjoint, and `Θ_{P₀, ℵ₁(f) P₀}` is bijective for every `f : a ⟶ a`, then
`Θ_{M,N}` is bijective for all `M`, `N`. -/
theorem homTensorMap_bijective (hAdj : ∀ f : a ⟶ a, ∃ g : a ⟶ a, Nonempty (f ⊣ g))
    (hBase : ∀ f : a ⟶ a,
      Function.Bijective (homTensorMap L hF hD hL β P₀ ((ℵ₁.map f).obj.obj P₀)))
    (M N : ℵ₁.obj a) : Function.Bijective (homTensorMap L hF hD hL β M N) := by
  refine homTensorMap_bijective_of_retract_left L hF hD hL β ((hD a).decomp M) fun i => ?_
  refine homTensorMap_bijective_of_retract L hF hD hL β ((hD a).decomp N) fun j => ?_
  obtain ⟨g, ⟨adj⟩⟩ := hAdj (((hD a).decomp M).t i)
  rw [homTensorMap_bijective_iff_of_adjunction L hF hD hL β adj]
  exact homTensorMap_bijective_of_iso L hF hD hL β (mapCompApp ℵ₁ _ g P₀) (hBase _)

end Categorification.TwoRep.Generated
