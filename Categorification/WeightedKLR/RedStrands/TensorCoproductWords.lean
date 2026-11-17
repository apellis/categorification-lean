/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorGenerators
import Categorification.WeightedKLR.RedStrands.TensorShapovalov

/-!
# Changing coproduct on the prescribed tensor words

Webster, arXiv:1309.3796v2, §4.7, uses the normalized quasi-R-matrix before
Proposition 4.33 and defines the prescribed vectors before Lemma 4.36.
Lusztig, *Introduction to Quantum Groups*, §§4.1 and 24.3, gives the
intertwining and inverse identities. Iterating them compares the word
vectors for the two coproducts independently of the pairing.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF TensorProduct
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
    {R : D.RootDatum Y} {n : ℕ}
local notation "𝕌" => LieLean.QuantumGroup R q
private abbrev HW (w : Dom R) := IrreducibleModule R q w.1
private abbrev highestVec (w : Dom R) := IrreducibleModule.hwv R q w.1

private abbrev barCoproduct : 𝕌 →ₐ[𝕂] 𝕌 ⊗[𝕂] 𝕌 :=
  { barComul R with commutes' := barComul_algebraMap R }

private abbrev pairAction {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) :
    𝕌 ⊗[𝕂] 𝕌 →ₐ[𝕂] Module.End 𝕂 (M ⊗[𝕂] HW w) :=
  (Module.endTensorEndAlgHom (R := 𝕂) (S := 𝕂) (A := 𝕂)).comp
    (Algebra.TensorProduct.map ρ (Algebra.lsmul 𝕂 𝕂 (HW w)))

/-- The action on the ordered tensor product through the iterated bar coproduct. -/
def barTensorRepresentation : {m : ℕ} → (wt : Fin m → Dom R) →
    𝕌 →ₐ[𝕂] Module.End 𝕂 (TensorSpace wt)
  | 0, wt => tensorRepresentation wt
  | m+1, wt => ((tensorSplitLast wt).symm.conjAlgEquiv 𝕂).toAlgHom.comp <|
      (pairAction (barTensorRepresentation (fun j => wt (Fin.castSucc j))) (wt (Fin.last m))).comp
        barCoproduct

private structure ModuleBar {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) where
  map : M →+ M
  act : ∀ u x, map (ρ u x) = ρ (barHom R u) (map x)
  invol : Function.Involutive map

private theorem counit_bar (u : 𝕌) :
    counit R q (barHom R u) = RatFunc.bar (counit R q u) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp [barHom_algebraMap]
  | E i => simp
  | F i => simp
  | K μ => simp
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

private def emptyBar (wt : Fin 0 → Dom R) : ModuleBar (tensorRepresentation wt) := by
  let e := PiTensorProduct.isEmptyEquiv (R := 𝕂) (s := fun j => HW (wt j)) (Fin 0)
  refine ⟨(e.symm.toLinearMap.toAddMonoidHom.comp RatFunc.bar.toAddMonoidHom).comp
    e.toLinearMap.toAddMonoidHom, ?_, ?_⟩
  · intro u x
    simp only [tensorRepresentation, AlgHom.comp_apply, Algebra.ofId_apply, Module.algebraMap_end_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, AddEquiv.toAddMonoidHom_eq_coe]
    apply e.injective
    simp [counit_bar, smul_eq_mul]
  · intro x
    change e.symm (RatFunc.bar (e (e.symm (RatFunc.bar (e x))))) = x
    simp

variable [Finite I]

section Binary
variable {M : Type*} [AddCommGroup M] [Module 𝕂 M] [Module (LieLean.QuantumGroup R (RatFunc.X : RatFunc ℚ)) M]
    [IsScalarTower (RatFunc ℚ) (LieLean.QuantumGroup R (RatFunc.X : RatFunc ℚ)) M]
    (w : Dom R) (hR : R.IsXRegular)
local notation "ρ" => (Algebra.lsmul 𝕂 𝕂 M : 𝕌 →ₐ[𝕂] Module.End 𝕂 M)
variable (B : ModuleBar (Algebra.lsmul (RatFunc ℚ) (RatFunc ℚ) M :
    LieLean.QuantumGroup R (RatFunc.X : RatFunc ℚ) →ₐ[RatFunc ℚ] Module.End (RatFunc ℚ) M))
local notation "Θ" => quasiRAct (M₁ := M) (isPlusLocallyNilpotent_hw w)
private abbrev pairBar := barPair B.map (hwBar hR w).toAddMonoidHom B.act (hwBar_smul_U' hR w)
local notation "b" => pairBar w hR B
local notation "actT" => TensorModule.act R q M (HW w)

private def extendBar : ModuleBar ((pairAction ρ w).comp (comul R q)) where
  map := (Θ).toAddMonoidHom.comp b
  act u x := by
    change Θ (b (actT u x)) = actT (barHom R u) (Θ (b x))
    have h := act_quasiRAct_barPair B.map (hwBar hR w).toAddMonoidHom B.act
      (hwBar_smul_U' hR w) (isPlusLocallyNilpotent_hw w) (barHom R u) x
    rw [barHom_barHom] at h
    exact h.symm
  invol x := quasiRAct_barPair_involutive B.map (hwBar hR w).toAddMonoidHom B.act
    (hwBar_smul_U' hR w) (isPlusLocallyNilpotent_hw w) B.invol (hwBar_hwBar hR w) x

private def quasiEquiv : M ⊗[𝕂] HW w ≃ₗ[𝕂] M ⊗[𝕂] HW w := by
  let J := (extendBar w hR B)
  have hb := barPair_barPair B.map (hwBar hR w).toAddMonoidHom B.act (hwBar_smul_U' hR w)
    B.invol (hwBar_hwBar hR w)
  refine LinearEquiv.ofBijective Θ ⟨?_, ?_⟩
  · intro x y e
    have h : J.map (b x) = J.map (b y) := by
      change Θ (b (b x)) = Θ (b (b y)); rwa [hb, hb]
    exact (Function.LeftInverse.injective hb) (J.invol.injective h)
  · intro x
    exact ⟨_, quasiRAct_finsum_barTensor (isPlusLocallyNilpotent_hw w) x⟩

private theorem quasiEquiv_highest (x : M) :
    quasiEquiv w hR B (x ⊗ₜ[𝕂] highestVec w) = x ⊗ₜ[𝕂] highestVec w := by
  change Θ _ = _
  rw [quasiRAct_apply, finsum_eq_single _ 0 fun ν hν => actPair_quasiR_tmul_eq_zero (fun y hy => ?_) _,
    quasiR_zero, map_one, Module.End.one_apply]
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
  rw [AlgHom.toLinearMap_apply, quotientPlus_toQuotient]
  change _ • Submodule.Quotient.mk (VermaModule.hwv R q w.1) = _
  rw [← Submodule.Quotient.mk_smul, VermaModule.plusHom_smul_hwv,
    LusztigF.counit_eq_zero_of_mem hν hv, zero_smul, Submodule.Quotient.mk_zero]

private theorem quasiEquiv_act (u : 𝕌) (z : M ⊗[𝕂] HW w) :
    quasiEquiv w hR B (pairAction ρ w (barComul R u) z) =
      pairAction ρ w (comul R q u) (quasiEquiv w hR B z) :=
  (act_quasiRAct (isPlusLocallyNilpotent_hw w) u z).symm
end Binary


omit [Finite I] in
private theorem rTensor_pairAction {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    (ρ σ : 𝕌 →ₐ[𝕂] Module.End 𝕂 M) (w : Dom R) (e : M ≃ₗ[𝕂] M)
    (he : ∀ u x, e (ρ u x) = σ u (e x))
    (t : 𝕌 ⊗[𝕂] 𝕌) (z : M ⊗[𝕂] HW w) :
    e.rTensor (HW w) (pairAction ρ w t z) = pairAction σ w t (e.rTensor (HW w) z) := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul x y =>
      simp [pairAction, Module.endTensorEndAlgHom_apply, he]

private structure WordComparison (wt : Fin n → Dom R) where
  bar : ModuleBar (tensorRepresentation wt)
  equiv : TensorSpace wt ≃ₗ[𝕂] TensorSpace wt
  intertwines : ∀ u x, equiv (barTensorRepresentation wt u x) = tensorRepresentation wt u (equiv x)

private def extendComparison (wt : Fin (n + 1) → Dom R) (hR : R.IsXRegular)
    (C : WordComparison (fun j => wt (Fin.castSucc j))) : WordComparison wt := by
  let left := fun j : Fin n => wt (Fin.castSucc j)
  let w := wt (Fin.last n)
  let ρ := tensorRepresentation left
  let : Module 𝕌 (TensorSpace left) := Module.compHom _ ρ.toRingHom
  let : IsScalarTower 𝕂 𝕌 (TensorSpace left) := ⟨fun c u x => by
    change ρ (c • u) x = c • ρ u x
    rw [map_smul, LinearMap.smul_apply]⟩
  let e := tensorSplitLast wt
  let B := extendBar w hR C.bar
  refine ⟨⟨(e.symm.toLinearMap.toAddMonoidHom.comp B.map).comp e.toLinearMap.toAddMonoidHom,
      ?_, ?_⟩, e.trans (((C.equiv.rTensor (HW w)).trans (quasiEquiv w hR C.bar)).trans e.symm),
    ?_⟩
  · intro u x
    change e.symm (B.map (e (e.symm (pairAction ρ w (comul R q u) (e x))))) =
      e.symm (pairAction ρ w (comul R q (barHom R u)) (e (e.symm (B.map (e x)))))
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact congrArg e.symm (B.act u (e x))
  · intro x
    change e.symm (B.map (e (e.symm (B.map (e x))))) = x
    rw [e.apply_symm_apply, B.invol, e.symm_apply_apply]
  · intro u x
    change e.symm (quasiEquiv w hR C.bar (C.equiv.rTensor (HW w) (e (e.symm
      (pairAction (barTensorRepresentation left) w (barComul R u) (e x)))))) =
      e.symm (pairAction ρ w (comul R q u) (e (e.symm _)))
    rw [e.apply_symm_apply, e.apply_symm_apply, rTensor_pairAction _ _ _ _ C.intertwines]
    exact congrArg e.symm (quasiEquiv_act w hR C.bar u _)

private def wordComparison (hR : R.IsXRegular) : {m : ℕ} → (wt : Fin m → Dom R) → WordComparison wt
  | 0, wt => ⟨emptyBar wt, LinearEquiv.refl 𝕂 _, fun _ _ => rfl⟩
  | _+1, wt => extendComparison wt hR (wordComparison hR _)

/-- The normalized quasi-R-matrix at each newly appended factor identifies
the iterated bar coproduct with the iterated coproduct. -/
def tensorCoproductEquiv (hR : R.IsXRegular) (wt : Fin n → Dom R) :
    TensorSpace wt ≃ₗ[𝕂] TensorSpace wt := (wordComparison hR wt).equiv

theorem tensorCoproductEquiv_act (hR : R.IsXRegular) (wt : Fin n → Dom R)
    (u : 𝕌) (x : TensorSpace wt) :
    tensorCoproductEquiv hR wt (barTensorRepresentation wt u x) =
      tensorRepresentation wt u (tensorCoproductEquiv hR wt x) :=
  (wordComparison hR wt).intertwines u x

theorem tensorCoproductEquiv_append (hR : R.IsXRegular) (wt : Fin (n + 1) → Dom R)
    (x : TensorSpace (fun j => wt (Fin.castSucc j))) :
    tensorCoproductEquiv hR wt (appendTensor wt x (highestVec (wt (Fin.last n)))) =
      appendTensor wt (tensorCoproductEquiv hR _ x) (highestVec (wt (Fin.last n))) := by
  let left := fun j : Fin n => wt (Fin.castSucc j)
  let ρ := tensorRepresentation left
  let : Module 𝕌 (TensorSpace left) := Module.compHom _ ρ.toRingHom
  let : IsScalarTower 𝕂 𝕌 (TensorSpace left) := ⟨fun c u y => by
    change ρ (c • u) y = c • ρ u y
    rw [map_smul, LinearMap.smul_apply]⟩
  let C := wordComparison hR left
  let w := wt (Fin.last n)
  let e := tensorSplitLast wt
  change e.symm (quasiEquiv w hR C.bar (C.equiv.rTensor (HW w) (e (e.symm
    (x ⊗ₜ[𝕂] highestVec w))))) = e.symm (C.equiv x ⊗ₜ[𝕂] highestVec w)
  rw [e.apply_symm_apply, LinearEquiv.rTensor_tmul]
  exact congrArg e.symm (quasiEquiv_highest w hR C.bar (C.equiv x))

/-- The divided tensor words of §4.7 evaluated with the bar coproduct. -/
def barTensorWordVector : {m : ℕ} → TensorWord I m → (wt : Fin m → Dom R) → TensorSpace wt
  | _, .empty, wt => tensorWordVector .empty wt
  | _, .red w, wt => appendTensor wt (barTensorWordVector w (fun j => wt (Fin.castSucc j)))
      (highestVec (wt (Fin.last _)))
  | _, .black w i a, wt => barTensorRepresentation wt (qDivPow (q ^ D.d i) a (F R q i))
      (barTensorWordVector w wt)

/-- The same linear equivalence simultaneously identifies all prescribed
divided-word vectors in the two coproduct conventions. -/
theorem tensorCoproductEquiv_word (hR : R.IsXRegular) :
    ∀ {m : ℕ} (w : TensorWord I m) (wt : Fin m → Dom R),
      tensorCoproductEquiv hR wt (barTensorWordVector w wt) = tensorWordVector w wt
  | _, .empty, wt => rfl
  | _, .red w, wt => by
    rw [barTensorWordVector, tensorCoproductEquiv_append, tensorCoproductEquiv_word hR w]
    rfl
  | _, .black w i a, wt => by
    rw [barTensorWordVector, tensorCoproductEquiv_act, tensorCoproductEquiv_word hR w]
    rfl

/-- Every finite Laurent-linear relation on the prescribed generators holds for
one choice of coproduct exactly when it holds for the other. -/
theorem barTensorWord_sum_eq_zero_iff (hR : R.IsXRegular) (wt : Fin n → Dom R)
    {J : Type*} (s : Finset J) (c : J → LaurentPolynomial ℤ) (w : J → TensorWord I n) :
    (∑ j ∈ s, c j • barTensorWordVector (w j) wt) = 0 ↔
      (∑ j ∈ s, c j • tensorWordVector (w j) wt) = 0 := by
  rw [← (tensorCoproductEquiv hR wt).map_eq_zero_iff]
  simp only [map_sum, tensor_laurent_smul, map_smul, tensorCoproductEquiv_word]

end Categorification.Stendhal.FirstWeight
