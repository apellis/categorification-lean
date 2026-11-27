/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered

/-!
# Symmetry on the prescribed tensor words

For the two words compared in Webster, arXiv:1309.3796v2, Lemma 4.36,
the repaired tensor form is symmetric. The entrywise bar changes the
coproduct on words and the individual contravariant forms are symmetric.
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

/-- The bar involution of `ℚ(v)` as a semilinear map. -/
def scalarBar : 𝕂 →ₛₗ[barRingHom] 𝕂 where
  toFun := RatFunc.bar
  map_add' := map_add _
  map_smul' c x := map_mul _ c x

/-- The bar involution of every tensor factor (the highest-weight bar `hwBar` on each). -/
def entrywiseBar : {m : ℕ} → (wt : Fin m → Dom R) → TensorSpace wt →ₛₗ[barRingHom] TensorSpace wt
  | 0, wt =>
    let e := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) _
    e.symm.toLinearMap.comp (scalarBar.comp e.toLinearMap)
  | m+1, wt =>
    let e := tensorSplitLast wt
    e.symm.toLinearMap.comp ((TensorProduct.map (entrywiseBar (fun j => wt (Fin.castSucc j)))
      (hwBar hR (wt (Fin.last m)))).comp e.toLinearMap)

theorem entrywiseBar_append (wt : Fin (n+1) → Dom R)
    (x : TensorSpace (fun j => wt (Fin.castSucc j))) (y : HW (wt (Fin.last n))) :
    entrywiseBar hR wt (appendTensor wt x y) =
      appendTensor wt (entrywiseBar hR _ x) (hwBar hR _ y) := by
  change (tensorSplitLast wt).symm (TensorProduct.map _ _ ((tensorSplitLast wt)
    ((tensorSplitLast wt).symm (x ⊗ₜ[𝕂] y)))) = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.map_tmul]
  rfl

omit [Finite I] in
private theorem bar_counit (u : 𝕌) : counit R q (barHom R u) = RatFunc.bar (counit R q u) := by
  induction u using QuantumGroup.induction_on with
  | E i => simp
  | F i => simp
  | K μ => simp
  | algebraMap c => simp [barHom_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

private abbrev pairRep {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) :
    𝕌 ⊗[𝕂] 𝕌 →ₐ[𝕂] Module.End 𝕂 (M ⊗[𝕂] HW w) :=
  (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp
    (Algebra.TensorProduct.map ρ (Algebra.lsmul 𝕂 𝕂 (HW w)))

private theorem map_pairRep {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ σ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) (b : M →ₛₗ[barRingHom] M)
    (h : ∀ u x, b (ρ u x) = σ (barHom R u) (b x)) (t : 𝕌 ⊗[𝕂] 𝕌) (z : M ⊗[𝕂] HW w) :
    TensorProduct.map b (hwBar hR w) (pairRep ρ w t z) =
      pairRep σ w (barTensor R t) (TensorProduct.map b (hwBar hR w) z) := by
  induction t using TensorProduct.inductionOn with
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul a c =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      rw [barTensor_tmul]
      change (b (ρ a x)) ⊗ₜ[𝕂] (hwBar hR w (c • y)) =
        (σ (barHom R a) (b x)) ⊗ₜ[𝕂] (barHom R c • hwBar hR w y)
      rw [h, hwBar_smul_U]

theorem entrywiseBar_act (wt : Fin n → Dom R) (u : 𝕌) (x : TensorSpace wt) :
    entrywiseBar hR wt (tensorRepresentation wt u x) =
      barTensorRepresentation wt (barHom R u) (entrywiseBar hR wt x) := by
  induction n generalizing u with
  | zero =>
    simp only [barTensorRepresentation, tensorRepresentation, AlgHom.comp_apply, Algebra.ofId_apply,
      Module.algebraMap_end_apply, map_smulₛₗ, bar_counit]
    rfl
  | succ m ih =>
    let e := tensorSplitLast wt
    let w := wt (Fin.last m)
    let L := fun j => wt (Fin.castSucc j)
    let b := TensorProduct.map (entrywiseBar hR L) (hwBar hR w)
    change e.symm (b (e (e.symm (pairRep (tensorRepresentation L) w (comul R q u) (e x))))) =
      e.symm (pairRep (barTensorRepresentation L) w (barComul R (barHom R u)) (e (e.symm (b (e x)))))
    rw [e.apply_symm_apply, e.apply_symm_apply, barComul_apply, barHom_barHom]
    exact congrArg e.symm (map_pairRep hR _ _ _ _ (ih L) _ _)

theorem entrywiseBar_word : ∀ {m : ℕ} (w : TensorWord I m) (wt : Fin m → Dom R),
    entrywiseBar hR wt (tensorWordVector w wt) = barTensorWordVector w wt
  | _, .empty, wt => by
    let e := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) _
    let z := PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R q (wt j).1)
    apply e.injective
    change e (e.symm (RatFunc.bar (e z))) = e z
    rw [e.apply_symm_apply, show e z = 1 from PiTensorProduct.isEmptyEquiv_apply_tprod _ _, map_one]
  | _, .red w, wt => by
    rw [tensorWordVector, entrywiseBar_append, entrywiseBar_word w, hwBar_hwv]
    rfl
  | _, .black w i a, wt => by
    rw [tensorWordVector, entrywiseBar_act, entrywiseBar_word w, barTensorWordVector]
    simp [qDivPow, barHom_smul, bar_qFactorial]

private theorem factorwise_entrywiseBar_comm (wt : Fin n → Dom R) (x y : TensorSpace wt) :
    orderedFactorwise hR wt x (entrywiseBar hR wt y) =
      orderedFactorwise hR wt y (entrywiseBar hR wt x) := by
  induction n with
  | zero =>
    let e := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) _
    change RatFunc.bar (e x) * e (e.symm (RatFunc.bar (e y))) =
      RatFunc.bar (e y) * e (e.symm (RatFunc.bar (e x)))
    rw [e.apply_symm_apply, e.apply_symm_apply, mul_comm]
  | succ m ih =>
    obtain ⟨a, rfl⟩ := (tensorSplitLast wt).symm.surjective x
    obtain ⟨b, rfl⟩ := (tensorSplitLast wt).symm.surjective y
    induction a using TensorProduct.inductionOn with
    | add c d hc hd => simp only [map_add, LinearMap.add_apply, hc, hd]
    | tmul c d =>
      induction b using TensorProduct.inductionOn with
      | add g k hg hk => simp only [map_add, LinearMap.add_apply, hg, hk]
      | tmul g k =>
        change orderedFactorwise hR wt (appendTensor wt c d) (entrywiseBar hR wt (appendTensor wt g k)) =
          orderedFactorwise hR wt (appendTensor wt g k) (entrywiseBar hR wt (appendTensor wt c d))
        rw [entrywiseBar_append, entrywiseBar_append, orderedFactorwise_append, orderedFactorwise_append,
          ih _ c g]
        congr 1
        simp only [SingleBlack.websterForm, hwBar_hwBar]
        rw [IrreducibleModule.form_comm]

/-- The corrected ordered form is symmetric on all pairs of prescribed
divided-word vectors of Webster, arXiv:1309.3796v2, Lemma 4.36. -/
theorem orderedForm_tensorWord_comm (wt : Fin n → Dom R) (a b : TensorWord I n) :
    orderedForm hR wt (tensorWordVector a wt) (tensorWordVector b wt) =
      orderedForm hR wt (tensorWordVector b wt) (tensorWordVector a wt) := by
  rw [orderedForm_word_right, orderedForm_word_right, ← entrywiseBar_word hR b, ← entrywiseBar_word hR a]
  exact factorwise_entrywiseBar_comm hR wt _ _

end Categorification.Stendhal.TensorPairing
