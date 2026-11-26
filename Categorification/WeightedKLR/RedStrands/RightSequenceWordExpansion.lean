/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorClassLowering
import Categorification.WeightedKLR.RedStrands.TensorModuleRaising
import Categorification.WeightedKLR.RedStrands.LoadingWordExpansion

/-!
# The class of a sequence projective in word tensors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Theorem 4.38
and proof of Proposition 5.20. The class `η' [e(t) T^λ]` of a right sequence projective is the
vector read from the loading `t`, so it is a sum of word tensors
`F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}` with monomial coefficients
(`rightTensorModuleEquiv_rightSequence_eq_monoSum`), indexed by `loadingMono`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

/-- The letters of a sequence, as a list. -/
def Seq.toList {ν : Multiset (I ⊕ Fin ℓ)} (t : Seq ν) : List (I ⊕ Fin ℓ) := List.ofFn t.lbl

omit [DecidableEq I] [Finite I] in
theorem Seq.coe_toList {ν : Multiset (I ⊕ Fin ℓ)} (t : Seq ν) :
    ((Seq.toList t : List (I ⊕ Fin ℓ)) : Multiset (I ⊕ Fin ℓ)) = ν := by
  have := t.2
  rw [Fin.univ_val_map] at this
  exact this

omit [DecidableEq I] [Finite I] in
theorem Seq.ofList_toList {ν : Multiset (I ⊕ Fin ℓ)} (t : Seq ν) :
    Seq.ofList (Seq.toList t) (Seq.coe_toList t) = t := by
  apply Subtype.ext
  funext a
  simp only [Seq.ofList, Seq.toList, List.get_eq_getElem, List.getElem_ofFn]
  exact congrArg t.1 (Fin.ext rfl)

/-- **The class of a right sequence projective** (Webster, arXiv:1309.3796v2, Theorem 4.38 and
proof of Proposition 5.20): `η' [e(t) T^λ] = Σ_{(d, u)} v^d F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}`
over the monomials of the loading `t`. -/
theorem rightTensorModuleEquiv_rightSequence_eq_monoSum {ν : Multiset I}
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    (rightTensorModuleEquiv C hQ hR Λ wt hwt
        (DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ Λ) ν
          (K0.of (rightSequenceProj (stendhalGradingDatum Λ hQ.gradingDatum
            (fun i => C.dot i i / 2) (dotDegree C hQ)) t ht))) : TensorSpace wt) =
      monoSum (C := C) wt (loadingMono wt (Seq.toList t)) := by
  have he := Seq.ofList_toList t
  have h := tensorModuleEquiv_loading C hQ hR Λ wt hwt (Seq.toList t) (Seq.coe_toList t)
    (he.symm ▸ ht)
  rw [he, projectedSequenceClass_ordered _ _ _ _ t ht] at h
  rw [rightTensorModuleEquiv_rightSequence, h, loadingVector_eq_monoSum]

end Categorification.Stendhal.FirstWeight
