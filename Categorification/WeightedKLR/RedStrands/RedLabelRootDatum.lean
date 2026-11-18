/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorModuleIdentification
import LieLean.Algebra.QuantumGroup.RootDatumHom

/-!
# A weight realization of the red labels

For the projective commutations of Webster, arXiv:1309.3796v2, Lemma 4.35,
the coroot multiplicities printed on the red strands suffice. Coordinate
functionals give independent simple roots, and the extra free summand in
the coroot group realizes any choice of red multiplicities.
-/
noncomputable section
namespace Categorification.Stendhal
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

variable {I : Type*} [DecidableEq I] (C : Categorification.QuantumGroup.CartanDatum I)

private def coordinateDatum : C.toLusztig.RootDatum (I → ℤ) where
  coroot i := C.toLusztig.cartanMatrix i
  root i := Pi.evalAddMonoidHom (fun _ : I => ℤ) i
  root_coroot _ _ := rfl

/-- Auxiliary root datum realizing the black Cartan matrix and the red labels. -/
def redLabelDatum := (coordinateDatum C).freeCoroot

/-- The coordinate functions remain independent for singular Cartan matrices. -/
theorem redLabelDatum_xRegular : (redLabelDatum C).IsXRegular := by
  classical
  rw [LusztigCartanDatum.RootDatum.IsXRegular, linearIndependent_iff']
  intro s c he j hj
  have h := DFunLike.congr_fun he (Pi.single j (1 : ℤ), 0)
  simpa [redLabelDatum, LusztigCartanDatum.RootDatum.freeCoroot, coordinateDatum,
    AddMonoidHom.finsetSum_apply, Pi.single_apply, Finset.sum_ite_eq', hj] using h

/-- A red label gives a dominant weight with the specified coroot coordinates. -/
def redLabelWeight (m : I →₀ ℕ) : Dom (redLabelDatum C) :=
  ⟨((Finsupp.linearCombination ℤ (fun i => (m i : ℤ))).toAddMonoidHom).comp
      (AddMonoidHom.snd _ _), fun i => by
    change 0 ≤ Finsupp.linearCombination ℤ _ (Finsupp.single i 1)
    simp⟩

omit [DecidableEq I] in
@[simp] theorem redLabelWeight_coroot (m : I →₀ ℕ) (i : I) :
    (redLabelWeight C m).1 ((redLabelDatum C).coroot i) = (m i : ℤ) := by
  change Finsupp.linearCombination ℤ _ (Finsupp.single i 1) = _
  simp

end Categorification.Stendhal
