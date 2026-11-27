/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.WeightForgetDerived
import Categorification.Algebra.DiagramWeightBimodule

/-!
# Forgetting the weights of a graded diagram tensor

For a homogeneous coefficient bimodule `M` with weight decomposition `G`, the dg bimodule
`D = diagramWeightBimodule G` between the weight categories `C_A` and `C_B` has
`D(X, Y) = G(X - Y)`. For a dg module `N` over `C_B`, summing the weights of the coend tensor
`D ⊗_{C_B} N` gives the ordinary tensor of `M` with the weight sum of `N`:

`⨁ n, (D ⊗_{C_B} N)⟨n⟩ ≅ M ⊗_B (⨁ k, N⟨k⟩)`,

naturally in `N` (`Categorification.diagramWeightForgetTensorIso`). This compares the graded
derived tensors used for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Definition 6.6, with the ungraded ones.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite DirectSum
open scoped DG.DegreeZero

universe u

variable {A B M : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M]
  [SMulCommClass A Bᵐᵒᵖ M]
  (G : ℤ → AddSubgroup M)
  (hl : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j+i))
  (X : CatModule.{u} (WeightCategory B))

local notation "D" => diagramWeightBimodule G hl hr

namespace DiagramWeightForget

/-- The underlying coefficient of an element of `D(n, Y)`. -/
def coeff {n : ℤ} {Y : WeightCategory B}
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) : InDegreeZero M :=
  (show G (n - Y.as) from g).val

theorem coeff_add {n : ℤ} {Y : WeightCategory B}
    (g g' : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) :
    coeff G hl hr (g + g') = coeff G hl hr g + coeff G hl hr g' := rfl

/-- `coeff` as an additive map. -/
def coeffHom (n : ℤ) (Y : WeightCategory B) :
    ((D).right ⟨n⟩).obj (DGOpposite.op Y) →+ InDegreeZero M :=
  AddMonoidHom.mk' (coeff G hl hr) (coeff_add G hl hr)

theorem coeff_ract {n : ℤ} {Y Y' : WeightCategory B} (f : Y ⟶ Y')
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y')) :
    coeff G hl hr (CatModule.ract _ f g) = op f.val • coeff G hl hr g := by
  rw [CatBimodule.right_ract]
  rfl

/-- The family `g ⊗ y ↦ g ⊗ y` into the ordinary tensor, at the weight `n`. -/
def forwardFamily (n : ℤ) (Y : WeightCategory B) :
    ((D).right ⟨n⟩).obj (DGOpposite.op Y) →+ X.obj Y →+
      TensorProductOver B (InDegreeZero M) X.WeightSum :=
  ((TensorProductOver.tmulAddHom B (InDegreeZero M) X.WeightSum).compl₂
    (CatModule.weightSumOf X Y.as)).comp (coeffHom G hl hr n Y)

theorem forwardFamily_apply (n : ℤ) (Y : WeightCategory B)
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (y : X.obj Y) :
    forwardFamily G hl hr X n Y g y =
      TensorProductOver.tmul B (coeff G hl hr g) (CatModule.weightSumOf X Y.as y) := rfl

theorem forwardFamily_balanced (n : ℤ) :
    CatTensorProduct.Balanced (forwardFamily G hl hr X n) := by
  intro Y Y' f g y
  rw [forwardFamily_apply, forwardFamily_apply, coeff_ract, TensorProductOver.op_smul_tmul,
    CatModule.weightSum_smul_of']

/-- The comparison at the weight `n`. -/
def forwardAt (n : ℤ) :
    CatTensorProduct ((D).right ⟨n⟩) X →+ TensorProductOver B (InDegreeZero M) X.WeightSum :=
  CatTensorProduct.lift _ (forwardFamily_balanced G hl hr X n)

/-- The comparison `⨁ n, (D ⊗ X)⟨n⟩ → M ⊗_B (⨁ k, X⟨k⟩)`. -/
def forward :
    ((D).tensorObj X).WeightSum →+ TensorProductOver B (InDegreeZero M) X.WeightSum :=
  DirectSum.toAddMonoid (forwardAt G hl hr X)

theorem forward_of (n : ℤ) (t : ((D).tensorObj X).obj ⟨n⟩) :
    forward G hl hr X (CatModule.weightSumOf _ n t) = forwardAt G hl hr X n t :=
  DirectSum.toAddMonoid_of _ _ _

/-- The pure tensor `g ⊗ y` in the summand of weight `n` of `⨁ n, (D ⊗ X)⟨n⟩`. -/
def ofTmul (n : ℤ) (Y : WeightCategory B) (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y))
    (y : X.obj Y) : ((D).tensorObj X).WeightSum :=
  CatModule.weightSumOf _ n (CatTensorProduct.tmul Y g y)

theorem forward_ofTmul (n : ℤ) (Y : WeightCategory B)
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (y : X.obj Y) :
    forward G hl hr X (ofTmul G hl hr X n Y g y) =
      TensorProductOver.tmul B (coeff G hl hr g) (CatModule.weightSumOf X Y.as y) :=
  (forward_of G hl hr X n _).trans
    (CatTensorProduct.lift_tmul _ (forwardFamily_balanced G hl hr X n) Y g y)

theorem ofTmul_ract (n : ℤ) {Y Y' : WeightCategory B} (f : Y ⟶ Y')
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y')) (y : X.obj Y) :
    ofTmul G hl hr X n Y (CatModule.ract _ f g) y = ofTmul G hl hr X n Y' g (f • y) :=
  congrArg (CatModule.weightSumOf ((D).tensorObj X) n) (CatTensorProduct.ract_tmul f g y)

theorem ofTmul_congr {n n' : ℤ} (h : n = n') (Y : WeightCategory B)
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y))
    (g' : ((D).right ⟨n'⟩).obj (DGOpposite.op Y))
    (hg : coeff G hl hr g = coeff G hl hr g') (y : X.obj Y) :
    ofTmul G hl hr X n Y g y = ofTmul G hl hr X n' Y g' y := by
  subst h
  have : g = g' := Subtype.ext hg
  rw [this]

theorem smul_ofTmul {j : ℤ} {a : A} (ha : a ∈ wgrading j) (n : ℤ) (Y : WeightCategory B)
    (g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)) (y : X.obj Y) :
    a • ofTmul G hl hr X n Y g y =
      ofTmul G hl hr X (n + j) Y ((D).lact (WeightCategory.homOfMem ha n (n + j) (by ring)) g) y :=
  (CatModule.weightSum_smul_of _ ha n _).trans
    (congrArg (CatModule.weightSumOf ((D).tensorObj X) (n + j))
      ((D).tensorAct_tmul X _ Y g y))

/-- The coefficient `m ∈ G i` as an element of `D(Y + i, Y)`. -/
def slice (i Y : ℤ) : G i →+ ((D).right ⟨Y + i⟩).obj (DGOpposite.op ⟨Y⟩) where
  toFun m := ⟨m.val, by
    change m.val ∈ G (Y + i - Y)
    rw [show Y + i - Y = i by ring]
    exact m.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeff_slice (i Y : ℤ) (m : G i) : coeff G hl hr (slice G hl hr i Y m) = m.val := rfl

/-- The inverse comparison on the coefficients of weight `i`. -/
def backFamily (i : ℤ) : G i →+ X.WeightSum →+ ((D).tensorObj X).WeightSum :=
  (DirectSum.toAddMonoid fun Y : ℤ =>
    (((CatTensorProduct.tmulAddHom ((D).right ⟨Y + i⟩) X ⟨Y⟩).comp
      (slice G hl hr i Y)).compr₂ (CatModule.weightSumOf ((D).tensorObj X) (Y + i))).flip).flip

variable [DirectSum.Decomposition G]

/-- The inverse comparison, before balancing. -/
def backward' : M →+ X.WeightSum →+ ((D).tensorObj X).WeightSum :=
  (DirectSum.toAddMonoid (backFamily G hl hr X)).comp
    (DirectSum.decomposeAddEquiv G).toAddMonoidHom

theorem backward'_of {i : ℤ} (m : G i) (Y : ℤ) (y : X.obj ⟨Y⟩) :
    backward' G hl hr X (m : M) (CatModule.weightSumOf X Y y) =
      ofTmul G hl hr X (Y + i) ⟨Y⟩ (slice G hl hr i Y m) y := by
  rw [backward', AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_coe, DirectSum.toAddMonoid_of,
    backFamily, AddMonoidHom.flip_apply, DirectSum.toAddMonoid_of]
  rfl

theorem backward'_balanced (b : B) (m : M) (y : X.WeightSum) :
    backward' G hl hr X (op b • m) y = backward' G hl hr X m (b • y) := by
  induction b using DirectSum.Decomposition.inductionOn (wgrading (M := B)) with
  | zero =>
    rw [MulOpposite.op_zero, zero_smul, map_zero, AddMonoidHom.zero_apply, zero_smul, map_zero]
  | add b b' hb hb' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, hb, hb', add_smul, map_add]
  | homogeneous b =>
    rename_i j
    induction m using DirectSum.Decomposition.inductionOn G with
    | zero => rw [_root_.smul_zero, map_zero, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
    | add m m' hm hm' =>
      rw [_root_.smul_add, map_add, AddMonoidHom.add_apply, hm, hm', map_add,
        AddMonoidHom.add_apply]
    | homogeneous m =>
      rename_i i
      induction y using DirectSum.induction_on with
      | zero => rw [_root_.smul_zero, map_zero, map_zero]
      | add y y' hy hy' => rw [_root_.smul_add, map_add, map_add, hy, hy']
      | of k y =>
        have hm' : op (b : B) • (m : M) ∈ G (i + j) := hr b.2 m.2
        rw [show (op (b : B) • (m : M) : M) = ((⟨_, hm'⟩ : G (i + j)) : M) from rfl,
          backward'_of, CatModule.weightSum_smul_of X b.2, backward'_of, ← ofTmul_ract]
        refine ofTmul_congr G hl hr X (by ring) _ _ _ ?_ y
        rw [coeff_ract, coeff_slice, coeff_slice]
        rfl

/-- The inverse comparison `M ⊗_B (⨁ k, X⟨k⟩) → ⨁ n, (D ⊗ X)⟨n⟩`. -/
def backward :
    TensorProductOver B (InDegreeZero M) X.WeightSum →+ ((D).tensorObj X).WeightSum :=
  TensorProductOver.lift (backward' G hl hr X) (backward'_balanced G hl hr X)

theorem backward_tmul_of {i : ℤ} (m : G i) (Y : ℤ) (y : X.obj ⟨Y⟩) :
    backward G hl hr X (TensorProductOver.tmul B (m : M) (CatModule.weightSumOf X Y y)) =
      ofTmul G hl hr X (Y + i) ⟨Y⟩ (slice G hl hr i Y m) y :=
  backward'_of G hl hr X m Y y

theorem backward_forward (s : ((D).tensorObj X).WeightSum) :
    backward G hl hr X (forward G hl hr X s) = s := by
  have h : (backward G hl hr X).comp (forward G hl hr X) = AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext' fun n => ?_
    refine CatTensorProduct.addHom_ext (N := (D).right ⟨n⟩) (M := X) fun Y g y => ?_
    change backward G hl hr X (forward G hl hr X (ofTmul G hl hr X n Y g y)) =
      ofTmul G hl hr X n Y g y
    rw [forward_ofTmul]
    have hg : coeff G hl hr g ∈ G (n - Y.as) := (show G (n - Y.as) from g).property
    rw [show coeff G hl hr g = ((⟨_, hg⟩ : G (n - Y.as)) : M) from rfl, backward_tmul_of]
    exact ofTmul_congr G hl hr X (show Y.as + (n - Y.as) = n by ring) Y _ g rfl y
  exact DFunLike.congr_fun h s

omit [Module A M] [SMulCommClass A Bᵐᵒᵖ M] in
theorem addHom_ext_decomposition {P : Type*} [AddCommGroup P] {f g : M →+ P}
    (h : ∀ i (m : G i), f m = g m) : f = g := by
  ext m
  induction m using DirectSum.Decomposition.inductionOn G with
  | zero => rw [map_zero, map_zero]
  | add m m' hm hm' => rw [map_add, map_add, hm, hm']
  | homogeneous m => exact h _ m

theorem forward_backward (t : TensorProductOver B (InDegreeZero M) X.WeightSum) :
    forward G hl hr X (backward G hl hr X t) = t := by
  have key : ((TensorProductOver.tmulAddHom B (InDegreeZero M) X.WeightSum).compr₂
      ((forward G hl hr X).comp (backward G hl hr X)) : M →+ X.WeightSum →+ _) =
        (TensorProductOver.tmulAddHom B (InDegreeZero M) X.WeightSum : M →+ _) := by
    refine addHom_ext_decomposition G fun i m => DirectSum.addHom_ext fun k y => ?_
    change forward G hl hr X (backward G hl hr X
        (TensorProductOver.tmul B (m : M) (CatModule.weightSumOf X k y))) =
      TensorProductOver.tmul B (m : M) (CatModule.weightSumOf X k y)
    rw [backward_tmul_of, forward_ofTmul, coeff_slice]
    rfl
  have h : (forward G hl hr X).comp (backward G hl hr X) = AddMonoidHom.id _ :=
    TensorProductOver.addHom_ext fun m y => DFunLike.congr_fun (DFunLike.congr_fun key m) y
  exact DFunLike.congr_fun h t

omit [DirectSum.Decomposition G] in
theorem forward_smul (a : A) (s : ((D).tensorObj X).WeightSum) :
    forward G hl hr X (a • s) = a • forward G hl hr X s := by
  induction a using DirectSum.Decomposition.inductionOn (wgrading (M := A)) with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | add a a' ha ha' => rw [add_smul, add_smul, map_add, ha, ha']
  | homogeneous a =>
    rename_i j
    have h : (forward G hl hr X).comp (DistribSMul.toAddMonoidHom _ (a : A)) =
        (DistribSMul.toAddMonoidHom _ (a : A)).comp (forward G hl hr X) := by
      refine DirectSum.addHom_ext' fun n => ?_
      refine CatTensorProduct.addHom_ext (N := (D).right ⟨n⟩) (M := X) fun Y g y => ?_
      change forward G hl hr X ((a : A) • ofTmul G hl hr X n Y g y) =
        (a : A) • forward G hl hr X (ofTmul G hl hr X n Y g y)
      rw [smul_ofTmul G hl hr X a.2, forward_ofTmul, forward_ofTmul]
      rfl
    exact DFunLike.congr_fun h s

omit [DirectSum.Decomposition G] in
theorem coeff_mem {n : ℤ} {Y : WeightCategory B} {i : ℤ}
    {g : ((D).right ⟨n⟩).obj (DGOpposite.op Y)} (hg : g ∈ grading i) :
    coeff G hl hr g ∈ grading i := by
  rcases (InDegreeZero.mem_grading_iff (M := G (n - Y.as))).mp hg with h | h
  · exact (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inl h)
  · exact (InDegreeZero.mem_grading_iff (M := M)).mpr (Or.inr (by rw [h]; rfl))

omit [DirectSum.Decomposition G] in
theorem forward_mem {k : ℤ} {s : ((D).tensorObj X).WeightSum} (hs : s ∈ grading k) :
    forward G hl hr X s ∈ grading k := by
  classical
  rw [← DirectSum.sum_support_of s, map_sum]
  refine sum_mem fun n _ => ?_
  rw [forward_of]
  refine CatTensorProduct.lift_mem _ (forwardFamily_balanced G hl hr X n)
    (fun Y i j g y hg hy => ?_) (hs n)
  rw [forwardFamily_apply]
  exact TensorProductOver.tmul_mem_grading (coeff_mem G hl hr hg)
    (DG.DirectSum.of_mem_grading _ _ hy)

omit [DirectSum.Decomposition G] in
theorem forwardAt_d (n : ℤ) (t : CatTensorProduct ((D).right ⟨n⟩) X) :
    forwardAt G hl hr X n (d t) = d (forwardAt G hl hr X n t) := by
  induction t using CatTensorProduct.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | add t t' ht ht' => rw [d_add, map_add, ht, ht', map_add, d_add]
  | tmul Y g y =>
    have hg : g ∈ grading (0 : ℤ) :=
      (InDegreeZero.mem_grading_iff (M := G (n - Y.as))).mpr (Or.inl rfl)
    have hc : coeff G hl hr g ∈ grading (0 : ℤ) := coeff_mem G hl hr hg
    rw [CatTensorProduct.d_tmul_of_mem Y hg, forwardAt, map_add, map_units_zsmul,
      CatTensorProduct.lift_tmul _ (forwardFamily_balanced G hl hr X n),
      CatTensorProduct.lift_tmul _ (forwardFamily_balanced G hl hr X n),
      CatTensorProduct.lift_tmul _ (forwardFamily_balanced G hl hr X n),
      forwardFamily_apply, forwardFamily_apply, forwardFamily_apply,
      TensorProductOver.d_tmul_of_mem hc, CatModule.weightSum_d_of]
    rfl

omit [DirectSum.Decomposition G] in
theorem forward_d (s : ((D).tensorObj X).WeightSum) :
    forward G hl hr X (d s) = d (forward G hl hr X s) := by
  induction s using DirectSum.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | add s s' hs hs' => rw [d_add, map_add, hs, hs', map_add, d_add]
  | of n t =>
    rw [CatModule.weightSum_d_of, forward_of, forward_of]
    exact forwardAt_d G hl hr X n t

/-- **Forgetting the weights of a diagram tensor**:
`⨁ n, (D ⊗ X)⟨n⟩ ≅ M ⊗_B (⨁ k, X⟨k⟩)` as dg `A`-modules, `g ⊗ y ↦ g ⊗ y`. -/
def tensorWeightSumEquiv :
    ((D).tensorObj X).WeightSum ≃ᵈᵍ[A] TensorProductOver B (InDegreeZero M) X.WeightSum where
  toFun := forward G hl hr X
  map_add' := map_add _
  map_smul' a s := forward_smul G hl hr X a s
  invFun := backward G hl hr X
  left_inv := backward_forward G hl hr X
  right_inv := forward_backward G hl hr X
  map_mem' := forward_mem G hl hr X
  map_d' := forward_d G hl hr X

omit [DirectSum.Decomposition G] in
theorem forward_natural {X' : CatModule.{u} (WeightCategory B)} (φ : X ⟶ X')
    (s : ((D).tensorObj X).WeightSum) :
    forward G hl hr X' (CatModule.weightSumMap ((D).tensorMap φ) s) =
      DGModuleHom.lTensor A (InDegreeZero M) (CatModule.weightSumMap φ)
        (forward G hl hr X s) := by
  have h : (forward G hl hr X').comp
        (CatModule.weightSumMap ((D).tensorMap φ)).toAddMonoidHom =
      (DGModuleHom.lTensor A (InDegreeZero M) (CatModule.weightSumMap φ)).toAddMonoidHom.comp
        (forward G hl hr X) := by
    refine DirectSum.addHom_ext' fun n => ?_
    refine CatTensorProduct.addHom_ext (N := (D).right ⟨n⟩) (M := X) fun Y g y => ?_
    change forward G hl hr X' (CatModule.weightSumMap ((D).tensorMap φ)
        (ofTmul G hl hr X n Y g y)) =
      DGModuleHom.lTensor A (InDegreeZero M) (CatModule.weightSumMap φ)
        (forward G hl hr X (ofTmul G hl hr X n Y g y))
    have e : CatModule.weightSumMap ((D).tensorMap φ) (ofTmul G hl hr X n Y g y) =
        ofTmul G hl hr X' n Y g (φ.app Y y) :=
      (CatModule.weightSumMap_of _ n _).trans
        (congrArg (CatModule.weightSumOf ((D).tensorObj X') n)
          ((D).tensorMap_tmul φ ⟨n⟩ Y g y))
    rw [e, forward_ofTmul, forward_ofTmul, DGModuleHom.lTensor_tmul, CatModule.weightSumMap_of]
  exact DFunLike.congr_fun h s

end DiagramWeightForget

open DiagramWeightForget in
/-- **Forgetting the weights commutes with tensoring by a diagram coefficient**: the weight sum
of `D ⊗_{C_B} X` is `M ⊗_B (⨁ k, X⟨k⟩)`, naturally in `X`. -/
def diagramWeightForgetTensorIso [DirectSum.Decomposition G] :
    (D).tensorFunctor ⋙ CatModule.weightForget A ≅
      CatModule.weightForget B ⋙ DGModuleCat.tensorFunctor A (InDegreeZero M) :=
  NatIso.ofComponents (fun X => DGModuleCat.isoOfDGModuleEquiv (tensorWeightSumEquiv G hl hr X))
    fun {X _} φ => DGModuleCat.hom_ext_apply fun s => forward_natural G hl hr X φ s

end Categorification
