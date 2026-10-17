/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.IntegralScalars
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Base change of the integral KL III presentation

KL III, arXiv:0807.3250v1, Definition 3.1 and §6.4, paragraph
“Simple nondegeneracy observations”. The comparison is obtained from the
presentation relations; it assumes neither freeness nor flatness of a Hom module.
-/

noncomputable section
namespace Categorification.KL3.Diagram.IntegralScalars

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open scoped TensorProduct

universe w u v

variable (k : Type w) [CommRing k] {I : Type u} {C : CartanDatum I}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)

/-- Evaluate a target linear diagram as a tensor of an integral diagram. -/
def tensorLin (a b : Obj (psig RD)) : LinDiagram k a b →ₗ[k]
    k ⊗[ℤ] ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) :=
  Finsupp.linearCombination k (fun g : a ⟶ b => 1 ⊗ₜ[ℤ] (pres RD ℤ).diag g)

@[simp] theorem tensorLin_single {a b : Obj (psig RD)} (g : a ⟶ b) (r : k) :
    tensorLin k RD a b (Finsupp.single g r) = r ⊗ₜ[ℤ] (pres RD ℤ).diag g := by
  change Finsupp.linearCombination k _ (Finsupp.single g r) = _
  rw [Finsupp.linearCombination_single, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp] theorem tensorLin_of {a b : Obj (psig RD)} (g : a ⟶ b) :
    tensorLin k RD a b (LinDiagram.of g) = 1 ⊗ₜ[ℤ] (pres RD ℤ).diag g :=
  tensorLin_single k RD g 1

/-- On integral coefficients this evaluation is the canonical tensor map. -/
theorem tensorLin_coeff {a b : Obj (psig RD)} (f : LinDiagram ℤ a b) :
    tensorLin k RD a b (coeff k f) = 1 ⊗ₜ[ℤ] (pres RD ℤ).lin f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [coeff_zero, map_zero, lin_zero, TensorProduct.tmul_zero]
  | add f g hf hg =>
    rw [coeff_add, map_add, hf, hg, lin_add, TensorProduct.tmul_add]
  | single g n =>
    let d : a ⟶ b := g
    change tensorLin k RD a b (coeff k (Finsupp.single d n)) =
      1 ⊗ₜ[ℤ] (pres RD ℤ).lin (Finsupp.single d n)
    have hsing : (Finsupp.single d n : LinDiagram ℤ a b) = n • LinDiagram.of d := by
      change Finsupp.single d n = n • Finsupp.single d (1 : ℤ)
      rw [Finsupp.smul_single, zsmul_eq_mul, mul_one]
      rfl
    have hz : (pres RD ℤ).lin (Finsupp.single d n) = n • (pres RD ℤ).diag d :=
      (congrArg (pres RD ℤ).lin hsing).trans (map_zsmul ((pres RD ℤ).linMap a b) n _)
    have h1 : (n : k) ⊗ₜ[ℤ] (pres RD ℤ).diag d =
        1 ⊗ₜ[ℤ] (n • (pres RD ℤ).diag d) := by
      rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    exact ((congrArg (tensorLin k RD a b) (coeff_single k d n)).trans
      (tensorLin_single k RD d (n : k))).trans
      (h1.trans (congrArg (fun z => (1 : k) ⊗ₜ[ℤ] z) hz.symm))

/-- The canonical comparison from the scalar extension of an integral Hom. -/
def fromTensor (a b : Obj (psig RD)) :
    k ⊗[ℤ] ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) →ₗ[k]
      ((pres RD k).obj a ⟶ (pres RD k).obj b) :=
  (homMap k RD a b).liftBaseChange k

@[simp] theorem fromTensor_tmul {a b : Obj (psig RD)} (r : k)
    (f : (pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) :
    fromTensor k RD a b (r ⊗ₜ[ℤ] f) = r • homMap k RD a b f :=
  LinearMap.liftBaseChange_tmul _ _ _ _

private theorem integral_whisk_witness (r : (pres RD ℤ).AllRel)
    (f : LinDiagram k r.dom r.cod) (he : coeff k r.rel = f)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) (h : r.dom.WhiskerOK u v) :
    ∃ z : LinDiagram ℤ (r.dom.whisker u v) (r.cod.whisker u v),
      z ∈ (pres RD ℤ).ideal _ _ ∧ coeff k z = LinDiagram.whisker f u v h := by
  refine ⟨LinDiagram.whisker r.rel u v h, (pres RD ℤ).whisker_rel_mem_ideal r u v h, ?_⟩
  exact (coeff_whisker k r.rel u v h).trans (congrArg (fun z => LinDiagram.whisker z u v h) he)

/-- Each whiskered target relation is the scalar image of an integral relation. -/
private theorem exists_integral_whiskRel (r : (pres RD k).AllRel)
    (u : Obj (psig RD)) (v : List (psig RD).Colour) (h : r.dom.WhiskerOK u v) :
    ∃ z : LinDiagram ℤ (r.dom.whisker u v) (r.cod.whisker u v),
      z ∈ (pres RD ℤ).ideal _ _ ∧ coeff k z = LinDiagram.whisker r.rel u v h := by
  cases r with
  | user r =>
    rcases r with (r | (c | c)) | r
    · exact r.elim
    · refine integral_whisk_witness k RD (.user (.inl (.inr (.inl c)))) _ ?_ u v h
      exact (coeff_sub k _ _).trans (congrArg₂ (· - ·) (coeff_of k _) (coeff_of k _))
    · refine integral_whisk_witness k RD (.user (.inl (.inr (.inr c)))) _ ?_ u v h
      exact (coeff_sub k _ _).trans (congrArg₂ (· - ·) (coeff_of k _) (coeff_of k _))
    · exact integral_whisk_witness k RD (.user (.inr r)) _ (coeff_relation k RD r) u v h
  | interchange x hx =>
    exact integral_whisk_witness k RD (.interchange x hx) _ (coeff_interchange k x hx) u v h

private theorem tensorLin_context_of_zero {a b s t : Obj (psig RD)}
    (f : LinDiagram ℤ s t) (hf : f ∈ (pres RD ℤ).ideal s t) (pre : a ⟶ s) (post : t ⟶ b) :
    tensorLin k RD a b (LinDiagram.of pre ≫ coeff k f ≫ LinDiagram.of post) = 0 := by
  have hz : (pres RD ℤ).lin (LinDiagram.of pre ≫ f ≫ LinDiagram.of post) = 0 := by
    rw [← lin_zero (pres RD ℤ), lin_eq_iff, sub_zero]
    exact (pres RD ℤ).comp_mem_ideal _ ((pres RD ℤ).mem_ideal_comp hf _)
  have he : coeff k (LinDiagram.of pre ≫ f ≫ LinDiagram.of post) =
      LinDiagram.of pre ≫ coeff k f ≫ LinDiagram.of post := by
    rw [coeff_comp, coeff_comp, coeff_of, coeff_of]
  rw [← he, tensorLin_coeff, hz, TensorProduct.tmul_zero]

private theorem tensorLin_context_zero {a b s t : Obj (psig RD)}
    (f : LinDiagram ℤ s t) (hf : f ∈ (pres RD ℤ).ideal s t)
    (pre : LinDiagram k a s) (post : LinDiagram k t b) :
    tensorLin k RD a b (pre ≫ coeff k f ≫ post) = 0 := by
  induction pre using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero]
  | add p q hp hq =>
    rw [Preadditive.add_comp, map_add, hp, hq, add_zero]
  | single p r =>
    let d : a ⟶ s := p
    change tensorLin k RD a b ((Finsupp.single d r : LinDiagram k a s) ≫ coeff k f ≫ post) = 0
    have hr : (Finsupp.single d r : LinDiagram k a s) = r • LinDiagram.of d :=
      (Finsupp.smul_single_one d r).symm
    rw [hr, Linear.smul_comp, map_smul]
    suffices hz : tensorLin k RD a b (LinDiagram.of d ≫ coeff k f ≫ post) = 0 by
      rw [hz, smul_zero]
    induction post using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, Limits.comp_zero, map_zero]
    | add p' q' hp hq =>
      rw [Preadditive.comp_add, Preadditive.comp_add, map_add, hp, hq, add_zero]
    | single q c =>
      let e : t ⟶ b := q
      change tensorLin k RD a b (LinDiagram.of d ≫ coeff k f ≫ (Finsupp.single e c : LinDiagram k t b)) = 0
      have hc : (Finsupp.single e c : LinDiagram k t b) = c • LinDiagram.of e :=
        (Finsupp.smul_single_one e c).symm
      rw [hc, Linear.comp_smul, Linear.comp_smul, map_smul, tensorLin_context_of_zero k RD f hf,
        smul_zero]

/-- Evaluation into the tensor product kills every target presentation relation. -/
theorem tensorLin_mem_ideal {a b : Obj (psig RD)} {f : LinDiagram k a b}
    (hf : f ∈ (pres RD k).ideal a b) : tensorLin k RD a b f = 0 := by
  have h : (pres RD k).ideal a b ≤ LinearMap.ker (tensorLin k RD a b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, u, v, hw, pre, post⟩
    obtain ⟨z, hz, he⟩ := exists_integral_whiskRel k RD r u v hw
    change tensorLin k RD _ _ (pre ≫ LinDiagram.whisker r.rel u v hw ≫ post) = 0
    rw [← he]
    exact tensorLin_context_zero k RD z hz pre post
  exact h hf

/-- The inverse comparison descends the diagramwise tensor evaluation. -/
def toTensor (a b : Obj (psig RD)) :
    ((pres RD k).obj a ⟶ (pres RD k).obj b) →ₗ[k]
      k ⊗[ℤ] ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) where
  toFun x := Quot.lift (tensorLin k RD a b) (fun f g h => by
    have h' : (pres RD k).homRel f g := by
      rwa [HomRel.compClosure_eq_self] at h
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact tensorLin_mem_ideal k RD h') x
  map_add' x y := by
    obtain ⟨f, rfl⟩ := (pres RD k).lin_surjective x
    obtain ⟨g, rfl⟩ := (pres RD k).lin_surjective y
    rw [← lin_add]
    exact (tensorLin k RD a b).map_add f g
  map_smul' r x := by
    obtain ⟨f, rfl⟩ := (pres RD k).lin_surjective x
    rw [← lin_smul]
    exact (tensorLin k RD a b).map_smul r f

@[simp] theorem toTensor_lin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    toTensor k RD a b ((pres RD k).lin f) = tensorLin k RD a b f := rfl

@[simp] theorem toTensor_diag {a b : Obj (psig RD)} (f : a ⟶ b) :
    toTensor k RD a b ((pres RD k).diag f) = 1 ⊗ₜ[ℤ] (pres RD ℤ).diag f :=
  tensorLin_of k RD f

private theorem toTensor_fromTensor {a b : Obj (psig RD)}
    (x : k ⊗[ℤ] ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b)) :
    toTensor k RD a b (fromTensor k RD a b x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul r f =>
    obtain ⟨g, rfl⟩ := (pres RD ℤ).lin_surjective f
    rw [fromTensor_tmul, map_smul, homMap_lin, toTensor_lin, tensorLin_coeff,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fromTensor_toTensor {a b : Obj (psig RD)}
    (f : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    fromTensor k RD a b (toTensor k RD a b f) = f := by
  induction f using (pres RD k).hom_induction with
  | diag g => rw [toTensor_diag, fromTensor_tmul, homMap_diag, one_smul]
  | zero => rw [map_zero, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | smul r f hf => rw [map_smul, map_smul, hf]

/-- **Base change of the presented KL Hom module.** This is a consequence of
integrality of the defining relations, independently of nondegeneracy. -/
def homBaseChange (a b : Obj (psig RD)) :
    k ⊗[ℤ] ((pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) ≃ₗ[k]
      ((pres RD k).obj a ⟶ (pres RD k).obj b) :=
  { fromTensor k RD a b with
    invFun := toTensor k RD a b
    left_inv := toTensor_fromTensor k RD
    right_inv := fromTensor_toTensor k RD }

@[simp] theorem homBaseChange_tmul {a b : Obj (psig RD)} (r : k)
    (f : (pres RD ℤ).obj a ⟶ (pres RD ℤ).obj b) :
    homBaseChange k RD a b (r ⊗ₜ[ℤ] f) = r • homMap k RD a b f :=
  fromTensor_tmul k RD r f

@[simp] theorem homBaseChange_tmul_diag {a b : Obj (psig RD)} (g : a ⟶ b) :
    homBaseChange k RD a b (1 ⊗ₜ[ℤ] (pres RD ℤ).diag g) = (pres RD k).diag g := by
  rw [homBaseChange_tmul, homMap_diag, one_smul]

end Categorification.KL3.Diagram.IntegralScalars
