/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorCoproductWords
import Categorification.WeightedKLR.RedStrands.TensorFormAdjunction
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.DirectSumAut
import LieLean.Algebra.QuantumGroup.Modified.TensorQuotientQuasiR

/-!
# The corrected form on ordered tensor products

Webster, arXiv:1309.3796v2, Proposition 4.33. The componentwise product of
one-factor forms pairs the ordinary and bar coproduct actions. Applying the
normalized intertwiner to the second argument identifies their adjoints.
-/

noncomputable section
namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF TensorProduct FirstWeight
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} [Finite I] (hR : R.IsXRegular) {n : ℕ}
private abbrev HW (w : Dom R) := IrreducibleModule R q w.1
local notation "𝕌" => QuantumGroup R q
local notation "τ" => fun (u : 𝕌) => barHom R (rho R q u)

private abbrev Form (M : Type*) [AddCommGroup M] [Module 𝕂 M] := M →ₛₗ[barRingHom] M →ₗ[𝕂] 𝕂

private def singleForm (w : Dom R) : Form (HW w) :=
  LinearMap.mk₂'ₛₗ _ _ (SingleBlack.websterForm w hR)
    (fun _ _ _ => by simp [SingleBlack.websterForm])
    (SingleBlack.websterForm_smul_left w hR)
    (fun _ _ _ => by simp [SingleBlack.websterForm])
    (SingleBlack.websterForm_smul_right w hR)

private def scalarForm : Form 𝕂 :=
  LinearMap.mk₂'ₛₗ _ _ (fun x y => RatFunc.bar x * y)
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp [smul_eq_mul, mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [smul_eq_mul, mul_left_comm])

private def pullForm {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module 𝕂 M] [Module 𝕂 N]
    (B : Form N) (e : M ≃ₗ[𝕂] N) : Form M :=
  (B.compl₂ e.toLinearMap).comp e.toLinearMap

private def productForm {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module 𝕂 M] [Module 𝕂 N]
    (A : Form M) (B : Form N) : Form (M ⊗[𝕂] N) :=
  (TensorProduct.map₂ A B).compr₂ₛₗ (TensorProduct.lid 𝕂 𝕂).toLinearMap

private theorem productForm_tmul {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module 𝕂 M] [Module 𝕂 N] (A : Form M) (B : Form N) (x x' : M) (y y' : N) :
    productForm A B (x ⊗ₜ y) (x' ⊗ₜ y') = A x x' * B y y' := rfl

/-- The componentwise product of the one-factor forms, before the intertwiner acts. -/
def orderedFactorwise : {m : ℕ} → (wt : Fin m → Dom R) → Form (TensorSpace wt)
  | 0, wt => pullForm scalarForm (PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) _)
  | m+1, wt => pullForm (productForm (orderedFactorwise (fun j => wt (Fin.castSucc j)))
      (singleForm hR (wt (Fin.last m)))) (tensorSplitLast wt)

/-- The form obtained by acting on the second vector by the iterated
normalized intertwiner from the ordinary to the bar coproduct. -/
def orderedForm (wt : Fin n → Dom R) : TensorSpace wt →ₛₗ[barRingHom] TensorSpace wt →ₗ[𝕂] 𝕂 :=
  (orderedFactorwise hR wt).compl₂ (tensorCoproductEquiv hR wt).symm.toLinearMap

theorem orderedFactorwise_append (wt : Fin (n+1) → Dom R)
    (x x' : TensorSpace (fun j => wt (Fin.castSucc j))) (y y' : HW (wt (Fin.last n))) :
    orderedFactorwise hR wt (appendTensor wt x y) (appendTensor wt x' y') =
      orderedFactorwise hR _ x x' * SingleBlack.websterForm _ hR y y' := by
  change productForm _ _ ((tensorSplitLast wt) ((tensorSplitLast wt).symm _))
    ((tensorSplitLast wt) ((tensorSplitLast wt).symm _)) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, productForm_tmul]
  rfl

/-- The empty family has the ordinary bar-first scalar form. -/
theorem orderedForm_empty (wt : Fin 0 → Dom R) (x y : TensorSpace wt) :
    let e := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) _
    orderedForm hR wt x y = RatFunc.bar (e x) * e y := rfl

/-- Evaluation on two pure tensors is the product of the individual
Shapovalov pairings before the intertwiner acts. -/
theorem orderedFactorwise_tprod (wt : Fin n → Dom R) (x y : ∀ j, HW (wt j)) :
    orderedFactorwise hR wt (PiTensorProduct.tprod 𝕂 x) (PiTensorProduct.tprod 𝕂 y) =
      ∏ j, SingleBlack.websterForm (wt j) hR (x j) (y j) := by
  induction n with
  | zero =>
    change RatFunc.bar (PiTensorProduct.isEmptyEquiv _ (PiTensorProduct.tprod 𝕂 x)) *
      PiTensorProduct.isEmptyEquiv _ (PiTensorProduct.tprod 𝕂 y) = _
    simp [PiTensorProduct.isEmptyEquiv_apply_tprod]
  | succ m ih =>
    change productForm (orderedFactorwise hR (fun j => wt (Fin.castSucc j))) (singleForm hR _)
      ((tensorSplitLast wt) (PiTensorProduct.tprod 𝕂 x)) ((tensorSplitLast wt) (PiTensorProduct.tprod 𝕂 y)) = _
    rw [tensorSplitLast_tprod, tensorSplitLast_tprod, productForm_tmul, ih, Fin.prod_univ_castSucc]
    rfl

/-- On a prescribed word in the second argument the normalized intertwiner
changes its coproduct to the bar coproduct. -/
theorem orderedForm_word_right (wt : Fin n → Dom R) (x : TensorSpace wt) (w : TensorWord I n) :
    orderedForm hR wt x (tensorWordVector w wt) = orderedFactorwise hR wt x (barTensorWordVector w wt) := by
  change orderedFactorwise hR wt x ((tensorCoproductEquiv hR wt).symm _) = _
  rw [← tensorCoproductEquiv_word hR w wt, LinearEquiv.symm_apply_apply]

/-- The corrected form on a finite ordered family, restricted to the subspace
ending in its highest vector, recovers the form of the shorter family. -/
theorem orderedForm_append_highest (wt : Fin (n+1) → Dom R)
    (x y : TensorSpace (fun j => wt (Fin.castSucc j))) :
    let v := IrreducibleModule.hwv R q (wt (Fin.last n)).1
    orderedForm hR wt (appendTensor wt x v) (appendTensor wt y v) =
      orderedForm hR _ x y := by
  dsimp only
  unfold orderedForm
  simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe]
  rw [show (tensorCoproductEquiv hR wt).symm (appendTensor wt y _) =
      appendTensor wt ((tensorCoproductEquiv hR _).symm y) _ by
    apply (tensorCoproductEquiv hR wt).injective
    rw [LinearEquiv.apply_symm_apply, tensorCoproductEquiv_append, LinearEquiv.apply_symm_apply],
    orderedFactorwise_append, SingleBlack.websterForm_hwv, mul_one]

private abbrev pairRep {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) :
    𝕌 ⊗[𝕂] 𝕌 →ₐ[𝕂] Module.End 𝕂 (M ⊗[𝕂] HW w) :=
  (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp
    (Algebra.TensorProduct.map ρ (Algebra.lsmul 𝕂 𝕂 (HW w)))

private theorem productForm_tmul_adjoint {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ σ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) (B : Form M)
    (h : ∀ u x y, B (ρ u x) y = B x (σ (τ u) y)) (u v : 𝕌)
    (x y : M ⊗[𝕂] HW w) :
    productForm B (singleForm hR w) (pairRep ρ w (u ⊗ₜ v) x) y =
      productForm B (singleForm hR w) x (pairRep σ w (τ u ⊗ₜ τ v) y) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul c d =>
      change B (ρ u a) c * SingleBlack.websterForm w hR (v • b) d =
        B a (σ (τ u) c) * SingleBlack.websterForm w hR b (τ v • d)
      rw [h, SingleBlack.websterForm_adjoint]

private theorem productForm_coproduct_adjoint {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ σ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) (B : Form M)
    (h : ∀ u x y, B (ρ u x) y = B x (σ (τ u) y)) (u : 𝕌) (x y : M ⊗[𝕂] HW w) :
    productForm B (singleForm hR w) (pairRep ρ w (comul R q u) x) y =
      productForm B (singleForm hR w) x (pairRep σ w (barComul R (τ u)) y) := by
  have ht := productForm_tmul_adjoint hR ρ σ w B h
  induction u using QuantumGroup.induction_on generalizing x y with
  | E i =>
    rw [comul_E, TensorAdjointConvention.barComul_tau_E]
    simp only [map_add, LinearMap.add_apply, ht, rho_one, map_one]
  | F i =>
    rw [comul_F, TensorAdjointConvention.barComul_tau_F]
    simp only [map_add, LinearMap.add_apply, ht, rho_one, map_one]
  | K μ => rw [comul_K, TensorAdjointConvention.barComul_tau_K, ht]
  | algebraMap c =>
    dsimp only
    rw [AlgHom.commutes, AlgHom.commutes, rho_algebraMap, barHom_algebraMap, barComul_algebraMap,
      AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smulₛₗ, LinearMap.smul_apply, map_smul]
    rfl
  | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]
  | mul v w hv hw => simp only [rho_mul, map_mul, Module.End.mul_apply, hv, hw]

omit [Finite I] in
private theorem counit_tau (u : 𝕌) : counit R q (τ u) = RatFunc.bar (counit R q u) := by
  induction u using QuantumGroup.induction_on with
  | E i => simp [rhoE, barHom_smul]
  | F i => simp [rhoF, barHom_smul]
  | K μ => simp
  | algebraMap c => simp [barHom_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul x y hx hy => simp only [rho_mul, map_mul, hx, hy, mul_comm]

private theorem orderedFactorwise_adjoint (wt : Fin n → Dom R)
    (u : 𝕌) (x y : TensorSpace wt) :
    orderedFactorwise hR wt (tensorRepresentation wt u x) y =
      orderedFactorwise hR wt x (barTensorRepresentation wt (τ u) y) := by
  induction n generalizing u with
  | zero =>
    change scalarForm _ _ = scalarForm _ _
    simp only [barTensorRepresentation, tensorRepresentation, AlgHom.comp_apply, Algebra.ofId_apply,
      Module.algebraMap_end_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, counit_tau]
    rfl
  | succ m ih =>
    let e := tensorSplitLast wt
    let w := wt (Fin.last m)
    let A := orderedFactorwise hR (fun j => wt (Fin.castSucc j))
    let ρ := tensorRepresentation (fun j => wt (Fin.castSucc j))
    let σ := barTensorRepresentation (fun j => wt (Fin.castSucc j))
    change productForm A (singleForm hR w) (e (e.symm (pairRep ρ w (comul R q u) (e x)))) (e y)
      = productForm A (singleForm hR w) (e x) (e (e.symm (pairRep σ w (barComul R (τ u)) (e y))))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact productForm_coproduct_adjoint hR ρ σ w A (ih _) u (e x) (e y)

/-- Adjointness for the repaired form of Webster, arXiv:1309.3796v2,
Proposition 4.33(2), on every finite ordered family of dominant weights. -/
theorem orderedForm_adjoint (wt : Fin n → Dom R) (u : 𝕌) (x y : TensorSpace wt) :
    orderedForm hR wt (tensorRepresentation wt u x) y =
      orderedForm hR wt x (tensorRepresentation wt (τ u) y) := by
  unfold orderedForm
  simp only [LinearMap.compl₂_apply, LinearEquiv.coe_coe, orderedFactorwise_adjoint]
  congr 1
  apply (tensorCoproductEquiv hR wt).injective
  rw [tensorCoproductEquiv_act, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

section Binary

-- The empty-prefix contraction identifies the ordinary and conjugate
-- one-factor actions with the action on the highest-weight representation.
private def singletonEquiv (wt : Fin 1 → Dom R) : TensorSpace wt ≃ₗ[𝕂] HW (wt (Fin.last 0)) :=
  (tensorSplitLast wt).trans (((PiTensorProduct.isEmptyEquiv (R := 𝕂)
    (s := fun j : Fin 0 => HW (wt j.castSucc)) _).rTensor _).trans (TensorProduct.lid 𝕂 _))

omit [Finite I] in
private theorem singletonEquiv_pairRep (wt : Fin 1 → Dom R) (t : 𝕌 ⊗[𝕂] 𝕌)
    (z : TensorSpace (fun j : Fin 0 => wt j.castSucc) ⊗[𝕂] HW (wt (Fin.last 0))) :
    let e := ((PiTensorProduct.isEmptyEquiv (R := 𝕂)
      (s := fun j : Fin 0 => HW (wt j.castSucc)) _).rTensor _).trans (TensorProduct.lid 𝕂 _)
    let η := (Algebra.TensorProduct.lid 𝕂 𝕌).toAlgHom.comp
      (Algebra.TensorProduct.map (counit R q) (AlgHom.id 𝕂 𝕌))
    e (pairRep (tensorRepresentation (fun j : Fin 0 => wt j.castSucc)) _
      t z) = (η t) • e z := by
  dsimp only
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    | tmul x y =>
      let f := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j : Fin 0 => HW (wt j.castSucc)) _
      change f (counit R q a • x) • (b • y) = (counit R q a • b) • (f x • y)
      rw [map_smul, smul_assoc, smul_assoc, smul_comm b (f x)]

omit [Finite I] in
private theorem counit_barComul (u : 𝕌) :
    (Algebra.TensorProduct.lid 𝕂 𝕌) (Algebra.TensorProduct.map (counit R q)
      (AlgHom.id 𝕂 𝕌) (barComul R u)) = u := by
  induction u using QuantumGroup.induction_on with
  | E i => simp [barComul_E]
  | F i => simp [barComul_F]
  | K μ => simp [barComul_K]
  | algebraMap c => simp [barComul_algebraMap, Algebra.smul_def]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

omit [Finite I] in
private theorem singletonEquiv_act (wt : Fin 1 → Dom R) (u : 𝕌) (x : TensorSpace wt) :
    singletonEquiv wt (tensorRepresentation wt u x) = u • singletonEquiv wt x := by
  let e := tensorSplitLast wt
  let f := ((PiTensorProduct.isEmptyEquiv (R := 𝕂)
    (s := fun j : Fin 0 => HW (wt j.castSucc)) _).rTensor (HW (wt (Fin.last 0)))).trans (TensorProduct.lid 𝕂 _)
  change f (e (e.symm (pairRep _ _ (comul R q u) (e x)))) = _
  rw [e.apply_symm_apply]
  have hc := DFunLike.congr_fun (counit_rTensor_comul R q) u
  change Algebra.TensorProduct.map (counit R q) (AlgHom.id 𝕂 𝕌) (comul R q u) = _ at hc
  rw [singletonEquiv_pairRep, AlgHom.comp_apply, hc]
  exact congrArg (· • singletonEquiv wt x) ((Algebra.TensorProduct.lid 𝕂 𝕌).apply_symm_apply u)

omit [Finite I] in
private theorem singletonEquiv_barAct (wt : Fin 1 → Dom R) (u : 𝕌) (x : TensorSpace wt) :
    singletonEquiv wt (barTensorRepresentation wt u x) = u • singletonEquiv wt x := by
  let e := tensorSplitLast wt
  let f := ((PiTensorProduct.isEmptyEquiv (R := 𝕂)
    (s := fun j : Fin 0 => HW (wt j.castSucc)) _).rTensor (HW (wt (Fin.last 0)))).trans (TensorProduct.lid 𝕂 _)
  change f (e (e.symm (pairRep _ _ (barComul R u) (e x)))) = _
  rw [e.apply_symm_apply]
  change f (pairRep (tensorRepresentation (fun j : Fin 0 => wt j.castSucc)) _ (barComul R u) (e x)) = _
  rw [singletonEquiv_pairRep wt (barComul R u) (e x), AlgHom.comp_apply]
  exact congrArg (· • singletonEquiv wt x) (counit_barComul u)

private theorem singleton_coproductEquiv (wt : Fin 1 → Dom R) (x : TensorSpace wt) :
    tensorCoproductEquiv hR wt x = x := by
  let e := singletonEquiv wt
  let wt₀ := fun j : Fin 0 => wt j.castSucc
  let h₀ := PiTensorProduct.tprod 𝕂 (fun j : Fin 0 => IrreducibleModule.hwv R q (wt₀ j).1)
  let v := IrreducibleModule.hwv R q (wt (Fin.last 0)).1
  let z := appendTensor wt h₀ v
  have hz : e z = v := by
    change TensorProduct.lid 𝕂 _ (((PiTensorProduct.isEmptyEquiv (R := 𝕂)
      (s := fun j : Fin 0 => HW (wt j.castSucc)) _).rTensor _) ((tensorSplitLast wt)
      ((tensorSplitLast wt).symm (h₀ ⊗ₜ v)))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul,
      PiTensorProduct.isEmptyEquiv_apply_tprod, one_smul]
  have hn : tensorCoproductEquiv hR wt z = z := tensorCoproductEquiv_append hR wt h₀
  obtain ⟨u, hu⟩ := IrreducibleModule.exists_smul_hwv_eq (e x)
  have hx : barTensorRepresentation wt u z = x := e.injective (by
    rw [singletonEquiv_barAct, hz]
    exact hu)
  rw [← hx, tensorCoproductEquiv_act, hn]
  apply e.injective
  rw [singletonEquiv_act, singletonEquiv_barAct]

/-- The contraction of the empty initial tensor makes the two ordered
factors into the usual binary tensor product. -/
def orderedBinaryEquiv (wt : Fin 2 → Dom R) :
    TensorSpace wt ≃ₗ[𝕂] HW (wt 0) ⊗[𝕂] HW (wt 1) :=
  (tensorSplitLast wt).trans ((singletonEquiv (fun j => wt j.castSucc)).rTensor _)

omit [Finite I] in
theorem orderedBinaryEquiv_tprod (wt : Fin 2 → Dom R) (x : ∀ j, HW (wt j)) :
    orderedBinaryEquiv wt (PiTensorProduct.tprod 𝕂 x) = x 0 ⊗ₜ[𝕂] x 1 := by
  simp only [orderedBinaryEquiv, singletonEquiv, LinearEquiv.trans_apply, tensorSplitLast_tprod,
    LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul, PiTensorProduct.isEmptyEquiv_apply_tprod, one_smul]
  rfl

private theorem singleton_factorwise (wt : Fin 1 → Dom R) (x y : TensorSpace wt) :
    orderedFactorwise hR wt x y = SingleBlack.websterForm _ hR (singletonEquiv wt x) (singletonEquiv wt y) := by
  obtain ⟨a, rfl⟩ := (tensorSplitLast wt).symm.surjective x
  obtain ⟨b, rfl⟩ := (tensorSplitLast wt).symm.surjective y
  induction a using TensorProduct.inductionOn with
  | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, SingleBlack.websterForm]
  | tmul c d =>
    induction b using TensorProduct.inductionOn with
    | add g k hg hk => simp only [map_add, hg, hk, SingleBlack.websterForm]
    | tmul g k =>
      change orderedFactorwise hR wt (appendTensor wt c d) (appendTensor wt g k) = _
      rw [orderedFactorwise_append]
      simp only [singletonEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul, SingleBlack.websterForm_smul_left,
        SingleBlack.websterForm_smul_right]
      change (RatFunc.bar _ * _) * _ = _
      rw [mul_assoc, mul_left_comm]
      rfl

private theorem binary_factorwise (wt : Fin 2 → Dom R) (x y : TensorSpace wt) :
    orderedFactorwise hR wt x y =
      factorwise hR (wt 0) (wt 1) (orderedBinaryEquiv wt x) (orderedBinaryEquiv wt y) := by
  obtain ⟨a, rfl⟩ := (tensorSplitLast wt).symm.surjective x
  obtain ⟨b, rfl⟩ := (tensorSplitLast wt).symm.surjective y
  induction a using TensorProduct.inductionOn with
  | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd, factorwise]
  | tmul c d =>
    induction b using TensorProduct.inductionOn with
    | add g k hg hk => simp only [map_add, hg, hk, factorwise]
    | tmul g k =>
      change orderedFactorwise hR wt (appendTensor wt c d) (appendTensor wt g k) = _
      rw [orderedFactorwise_append, singleton_factorwise]
      simp only [orderedBinaryEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.rTensor_tmul, factorwise_tmul]
      rfl

private theorem binary_coproductEquiv (wt : Fin 2 → Dom R) (y : TensorSpace wt) :
    orderedBinaryEquiv wt (tensorCoproductEquiv hR wt y) =
      quasiRAct (isPlusLocallyNilpotent_hw (wt 1)) (orderedBinaryEquiv wt y) := by
  let left := fun j : Fin 1 => wt j.castSucc
  let w := wt (Fin.last 1)
  let ρ := tensorRepresentation left
  let : Module 𝕌 (TensorSpace left) := Module.compHom _ ρ.toRingHom
  let : IsScalarTower 𝕂 𝕌 (TensorSpace left) := ⟨fun c u x => by
    change ρ (c • u) x = c • ρ u x
    rw [map_smul, LinearMap.smul_apply]⟩
  let e := tensorSplitLast wt
  let f : TensorSpace left →ₗ[𝕌] HW (wt 0) :=
    { (singletonEquiv left).toLinearMap.toAddMonoidHom with map_smul' := singletonEquiv_act left }
  have hn (z : TensorSpace left ⊗[𝕂] HW w) :
      (singletonEquiv left).rTensor (HW w) (quasiRAct (isPlusLocallyNilpotent_hw w) z) =
        quasiRAct (isPlusLocallyNilpotent_hw w) ((singletonEquiv left).rTensor (HW w) z) :=
    (quasiRAct_map (isPlusLocallyNilpotent_hw w) (isPlusLocallyNilpotent_hw w)
      f (LinearMap.id (R := 𝕌)) z).symm
  have h₁ : tensorCoproductEquiv hR left = LinearEquiv.refl 𝕂 _ :=
    LinearEquiv.ext (singleton_coproductEquiv hR left)
  change (singletonEquiv left).rTensor (HW w) (e (e.symm (quasiRAct (isPlusLocallyNilpotent_hw w)
    ((tensorCoproductEquiv hR left).rTensor (HW w) (e y))))) = _
  rw [e.apply_symm_apply, h₁, LinearEquiv.rTensor_refl, LinearEquiv.refl_apply, hn]
  rfl

/-- For any two dominant weights, contraction of the empty prefix identifies
the ordered form with the two-factor repair of Proposition 4.33. -/
theorem orderedForm_binary (wt : Fin 2 → Dom R) (x y : TensorSpace wt) :
    orderedForm hR wt x y =
      correctedForm hR (wt 0) (wt 1) (orderedBinaryEquiv wt x) (orderedBinaryEquiv wt y) := by
  change orderedFactorwise hR wt x ((tensorCoproductEquiv hR wt).symm y) = _
  rw [binary_factorwise, correctedForm]
  congr 1
  apply (orderedBinaryEquiv wt).symm.injective
  apply (tensorCoproductEquiv hR wt).injective
  apply (orderedBinaryEquiv wt).injective
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, binary_coproductEquiv,
    LinearEquiv.apply_symm_apply]
  exact (quasiRAct_barPair_involutive _ _ (hwBar_smul_U' hR (wt 0)) (hwBar_smul_U' hR (wt 1))
    (isPlusLocallyNilpotent_hw (wt 1)) (hwBar_hwBar hR _) (hwBar_hwBar hR _) _).symm

end Binary
end Categorification.Stendhal.TensorPairing
