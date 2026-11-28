/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetDerived

/-!
# The weight-preserving part of a map between weight sums

For dg modules `M`, `M'` over `C_A = DG.WeightCategory A`, a cochain
`c : ⨁ k, M⟨k⟩ ⟶ ⨁ k, M'⟨k⟩` of dg `A`-modules has a weight-preserving part
`DG.CatModule.weightPart c : M ⟶ M'`, with components `M⟨k⟩ ⟶ M'⟨k⟩` the `k`-th component of
`c` on the `k`-th summand. It is compatible with the differentials of the Hom complexes and
is a left inverse of forgetting the weights (`DG.CatModule.weightPart_weightSumMapCochain`).

So the Hom complex of dg modules over `C_A` is a retract of the Hom complex of their weight
sums, and morphisms of the homotopy category of dg modules over `C_A` are a retract of
morphisms between the weight sums (`DG.CatModule.homotopic_of_weightSumMap`). This is the
comparison used to transfer properties of the ungraded braiding functors of B. Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 6.15, to the
graded ones of Definition 6.6.
-/

open CategoryTheory DirectSum

universe v u

noncomputable section

namespace DG

namespace CatModule

open WeightCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [InternalGrading A] [BigradedDGRing A]

/-- The action of a morphism `⟨k⟩ ⟶ ⟨l⟩` of `C_A` on `⨁ k, N⟨k⟩`, read in the summand `l`, only
sees the summand `k`. -/
theorem weightSum_smul_apply (N : CatModule.{v} (WeightCategory A)) {k l : ℤ}
    (f : (⟨k⟩ : WeightCategory A) ⟶ ⟨l⟩) (z : N.WeightSum) :
    (f.1 • z) l = f • z k := by
  classical
  induction z using DirectSum.induction_on with
  | zero =>
    rw [weightSum_smul_zero]
    exact (map_zero (N.act f)).symm
  | add x y hx hy =>
    rw [weightSum_smul_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy]
    exact (map_add (N.act f) _ _).symm
  | of j y =>
    by_cases hj : j = k
    · subst hj
      rw [weightSum_smul_of' N f, DirectSum.of_eq_same, DirectSum.of_eq_same]
    · let g : (⟨j⟩ : WeightCategory A) ⟶ ⟨j + (l - k)⟩ := homOfMem f.2 j _ (by ring)
      change (g.1 • weightSumOf N j y) l = _
      rw [weightSum_smul_of' N g, DirectSum.of_eq_of_ne _ _ _ (by omega),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hj)]
      exact (map_zero (N.act f)).symm

variable {M M' M'' : CatModule.{v} (WeightCategory A)}

/-- The weight-preserving part of a cochain between weight sums: its component `M⟨k⟩ ⟶ M'⟨k⟩`
is the `k`-th component of the cochain on the `k`-th summand. -/
def weightPart {n : ℤ} (c : DG.Cochain A M.WeightSum M'.WeightSum n) : Cochain M M' n where
  app k := AddMonoidHom.mk' (fun y => c (weightSumOf M k.as y) k.as) fun y y' => by
    rw [map_add, map_add, DirectSum.add_apply]
  map_mem' {k i x} hx := c.map_mem (DG.DirectSum.of_mem_grading _ _ hx) k.as
  map_smul' {k l i f} hf x := by
    change c (weightSumOf M l.as (f • x)) l.as =
      koszulSign (n * i) • (f • c (weightSumOf M k.as x) k.as)
    have hf' : f.1 ∈ grading i := hf
    rw [← weightSum_smul_of' M f, c.map_smul hf', Units.smul_def, Units.smul_def,
      DFinsupp.smul_apply, weightSum_smul_apply M' f]

@[simp]
theorem weightPart_app {n : ℤ} (c : DG.Cochain A M.WeightSum M'.WeightSum n) (k : ℤ)
    (y : M.obj ⟨k⟩) : (weightPart c).app ⟨k⟩ y = c (weightSumOf M k y) k := rfl

/-- The weight-preserving part of a summed cochain is the cochain. -/
theorem weightPart_weightSumMapCochain {n : ℤ} (h : Cochain M M' n) :
    weightPart (weightSumMapCochain h) = h :=
  Cochain.ext fun k y => by
    change weightSumMapCochain h (weightSumOf M k.as y) k.as = _
    rw [weightSumMapCochain_of, DirectSum.of_eq_same]

theorem weightPart_add {n : ℤ} (c c' : DG.Cochain A M.WeightSum M'.WeightSum n) :
    weightPart (c + c') = weightPart c + weightPart c' :=
  Cochain.ext fun _ _ => DirectSum.add_apply _ _ _

theorem weightPart_δ (n m : ℤ) (c : DG.Cochain A M.WeightSum M'.WeightSum n) :
    weightPart (DG.δ n m c) = CatModule.δ n m (weightPart c) := by
  by_cases hnm : n + 1 = m
  · refine Cochain.ext fun k y => ?_
    rw [CatModule.δ_apply n m hnm]
    change DG.δ n m c (weightSumOf M k.as y) k.as = _
    rw [DG.δ_apply n m hnm, weightSum_d_of, DFinsupp.sub_apply, DG.DirectSum.coe_d_apply,
      Units.smul_def, DFinsupp.smul_apply, Units.smul_def]
    rfl
  · rw [CatModule.δ_shape n m hnm, DG.δ_shape n m hnm]
    exact Cochain.ext fun _ _ => rfl

/-- The weight-preserving part of a morphism of dg `A`-modules between weight sums, as a
morphism of dg modules over `C_A`. -/
def weightPartHom (f : M.WeightSum →ᵈᵍ[A] M'.WeightSum) : M ⟶ M' where
  app k := (weightPart (DG.Cochain.ofHom f)).app k
  map_mem' {k n m} hm := by
    simpa using (weightPart (DG.Cochain.ofHom f)).map_mem hm
  map_d' {k} m := by
    change f (weightSumOf M k.as (d m)) k.as = d (f (weightSumOf M k.as m) k.as)
    rw [← weightSum_d_of, f.map_d, DG.DirectSum.coe_d_apply]
  map_smul' {k l} g m := by
    change f (weightSumOf M l.as (g • m)) l.as = g • f (weightSumOf M k.as m) k.as
    rw [← weightSum_smul_of' M g, map_smul, weightSum_smul_apply M' g]

theorem weightPartHom_app (f : M.WeightSum →ᵈᵍ[A] M'.WeightSum) (k : ℤ) (y : M.obj ⟨k⟩) :
    (weightPartHom f).app ⟨k⟩ y = f (weightSumOf M k y) k := rfl

theorem ofHom_weightPartHom (f : M.WeightSum →ᵈᵍ[A] M'.WeightSum) :
    Cochain.ofHom (weightPartHom f) = weightPart (DG.Cochain.ofHom f) := rfl

/-- The weight-preserving part of the weight sum of a morphism is the morphism. -/
theorem weightPartHom_weightSumMap (φ : M ⟶ M') : weightPartHom (weightSumMap φ) = φ :=
  Cochain.ofHom_injective (by
    rw [ofHom_weightPartHom, ← weightSumMapCochain_ofHom, weightPart_weightSumMapCochain])

/-- The weight-preserving part is compatible with composition on the right with a weight sum. -/
theorem weightPartHom_comp_weightSumMap (f : M'.WeightSum →ᵈᵍ[A] M''.WeightSum) (φ : M ⟶ M') :
    weightPartHom (f.comp (weightSumMap φ)) = φ ≫ weightPartHom f := by
  ext k y
  change f (weightSumMap φ (weightSumOf M k.as y)) k.as = _
  rw [weightSumMap_of]
  rfl

/-- The weight-preserving part is compatible with composition on the left with a weight sum. -/
theorem weightPartHom_weightSumMap_comp (f : M.WeightSum →ᵈᵍ[A] M'.WeightSum) (φ : M' ⟶ M'') :
    weightPartHom ((weightSumMap φ).comp f) = weightPartHom f ≫ φ := by
  ext k y
  change weightSumMap φ (f (weightSumOf M k.as y)) k.as = _
  change (DirectSum.map (fun k => φ.app ⟨k⟩) _) k.as = _
  rw [DirectSum.map_apply]
  rfl

/-- Homotopic morphisms between weight sums have homotopic weight-preserving parts. -/
theorem _root_.DG.Homotopic.weightPartHom {f g : M.WeightSum →ᵈᵍ[A] M'.WeightSum}
    (h : DG.Homotopic f g) :
    Homotopic (CatModule.weightPartHom f) (CatModule.weightPartHom g) := by
  obtain ⟨h⟩ := h
  refine ⟨⟨weightPart h.hom, ?_⟩⟩
  rw [ofHom_weightPartHom, ofHom_weightPartHom, h.ofHom_eq, weightPart_add, weightPart_δ]

/-- **Forgetting the weights is faithful on homotopy classes**: morphisms of dg modules over
`C_A` with homotopic weight sums are homotopic. -/
theorem homotopic_of_weightSumMap {φ ψ : M ⟶ M'}
    (h : DG.Homotopic (weightSumMap φ) (weightSumMap ψ)) : Homotopic φ ψ := by
  have := h.weightPartHom
  rwa [weightPartHom_weightSumMap, weightPartHom_weightSumMap] at this

/-! ### Forgetting the weights as a left adjoint -/

section Adjunction

variable (A) in
/-- The constant dg module `weightConst N`, as a functor of the dg `A`-module `N`. -/
def weightConstFunctor : DGModuleCat.{u} A ⥤ CatModule.{u} (WeightCategory A) where
  obj N := weightConst N
  map {N N'} g :=
    { app := fun _ => g.hom.toLinearMap.toAddMonoidHom
      map_mem' := fun hm => g.hom.map_mem hm
      map_d' := fun m => g.hom.map_d m
      map_smul' := fun f m => by
        change g.hom (f.1 • m) = f.1 • g.hom m
        exact map_smul g.hom f.1 m }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A morphism `M ⟶ weightConst N`, summed over the weights: `⨁ k, M⟨k⟩ ⟶ N`. -/
def weightSumLift {M : CatModule.{u} (WeightCategory A)} {N : DGModuleCat.{u} A}
    (φ : M ⟶ weightConst N) : M.WeightSum →ᵈᵍ[A] N where
  toFun := DirectSum.toAddMonoid fun k => φ.app ⟨k⟩
  map_add' := map_add _
  map_smul' a x := by
    induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
    | zero => simp only [_root_.zero_smul, map_zero]
    | add a a' ha ha' => simp only [_root_.add_smul, map_add, ha, ha', RingHom.id_apply]
    | homogeneous a =>
      induction x using DirectSum.induction_on with
      | zero => simp only [_root_.smul_zero, map_zero, RingHom.id_apply]
      | add x y hx hy => simp only [_root_.smul_add, map_add, hx, hy, RingHom.id_apply]
      | of k y =>
        rw [RingHom.id_apply, weightSum_smul_of M a.2, DirectSum.toAddMonoid_of,
          DirectSum.toAddMonoid_of, φ.map_smul]
        rfl
  map_mem' {n x} hx := by
    classical
    rw [← DirectSum.sum_support_of x, map_sum]
    refine sum_mem fun k _ => ?_
    rw [DirectSum.toAddMonoid_of]
    exact φ.map_mem (hx k)
  map_d' x := by
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | of k y =>
      rw [weightSum_d_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, φ.map_d]

theorem weightSumLift_of {M : CatModule.{u} (WeightCategory A)} {N : DGModuleCat.{u} A}
    (φ : M ⟶ weightConst N) (k : ℤ) (y : M.obj ⟨k⟩) :
    weightSumLift φ (weightSumOf M k y) = φ.app ⟨k⟩ y :=
  DirectSum.toAddMonoid_of (fun k => φ.app ⟨k⟩) k y

variable (A) in
/-- **Forgetting the weights is left adjoint to the constant dg module**:
`(⨁ k, M⟨k⟩ ⟶ N) ≃ (M ⟶ weightConst N)`. -/
def weightForgetAdjunction : weightForget A ⊣ weightConstFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := fun f => weightSumAdjoint f.hom
          invFun := fun φ => DGModuleCat.ofHom (weightSumLift φ)
          left_inv := fun f => DGModuleCat.hom_ext (DGModuleHom.ext fun x => by
            induction x using DirectSum.induction_on with
            | zero => exact (map_zero _).trans (map_zero _).symm
            | add x y hx hy =>
              exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
            | of k y => exact weightSumLift_of _ k y)
          right_inv := fun φ => by
            ext k y
            exact weightSumLift_of φ k.as y }
      homEquiv_naturality_left_symm := fun {M M' N} g φ =>
        DGModuleCat.hom_ext (DGModuleHom.ext fun x => by
        induction x using DirectSum.induction_on with
        | zero => exact (map_zero _).trans (map_zero _).symm
        | add x y hx hy =>
          exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
        | of k y =>
          change weightSumLift (g ≫ φ) (weightSumOf M k y) =
            weightSumLift φ (weightSumMap g (weightSumOf M k y))
          rw [weightSumLift_of, weightSumMap_of]
          exact (weightSumLift_of (N := N) φ k _).symm)
      homEquiv_naturality_right := fun f g => rfl }

theorem weightForgetAdjunction_unit_app (M : CatModule.{u} (WeightCategory A)) (k : ℤ)
    (y : M.obj ⟨k⟩) :
    ((weightForgetAdjunction A).unit.app M).app ⟨k⟩ y = weightSumOf M k y := by
  simp only [weightForgetAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  rfl

/-- The projection of the constant dg module on the weight sum of `M` onto `M`: at the weight
`k`, the `k`-th component. -/
def weightProj (M : CatModule.{u} (WeightCategory A)) :
    (weightConstFunctor A).obj ((weightForget A).obj M) ⟶ M where
  app k := DFinsupp.evalAddMonoidHom k.as
  map_mem' {k n z} hz := hz k.as
  map_d' {k} z := by
    change (d (show M.WeightSum from z)) k.as = d ((show M.WeightSum from z) k.as)
    exact DG.DirectSum.coe_d_apply _ _ _
  map_smul' {k l} g z := weightSum_smul_apply M g z

variable (A) in
/-- The projections `weightProj M`, as a natural transformation. -/
def weightProjNatTrans : weightForget A ⋙ weightConstFunctor A ⟶ 𝟭 _ where
  app := weightProj
  naturality {M M'} φ := by
    ext k z
    change (weightSumMap φ (show M.WeightSum from z)) k.as =
      φ.app k ((show M.WeightSum from z) k.as)
    exact DirectSum.map_apply _ _ _

/-- The projection is a retraction of the unit of the adjunction. -/
@[reassoc (attr := simp)]
theorem unit_app_comp_weightProj (M : CatModule.{u} (WeightCategory A)) :
    (weightForgetAdjunction A).unit.app M ≫ weightProj M = 𝟙 M := by
  ext ⟨k⟩ y
  rw [comp_app, weightForgetAdjunction_unit_app]
  exact DirectSum.of_eq_same _ _

/-- The weight-preserving part of a morphism of weight sums, through the adjunction. -/
theorem unit_app_comp_map_comp_weightProj {M M' : CatModule.{u} (WeightCategory A)}
    (ψ : (weightForget A).obj M ⟶ (weightForget A).obj M') :
    (weightForgetAdjunction A).unit.app M ≫ (weightConstFunctor A).map ψ ≫ weightProj M' =
      weightPartHom ψ.hom := by
  ext ⟨k⟩ y
  rw [comp_app, comp_app, weightForgetAdjunction_unit_app]
  rfl

end Adjunction

end CatModule

end DG
