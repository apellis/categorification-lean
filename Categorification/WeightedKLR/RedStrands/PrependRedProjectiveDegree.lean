/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedDegreeInjective
import Categorification.WeightedKLR.RedStrands.LeftStandardModule

/-!
# Adding a red strand identifies the projectives in a fixed degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23. Adding a red strand of label `λ₀` on the left sends `e(s)` to `e(λ₀ s)`, so it
maps `T̃^λ e(s)` to `T^{(λ₀, λ)} e(λ₀ s)`. It is surjective and preserves degrees, and it is
injective in degree `n` once `⟨α_i^∨, λ₀⟩ · deg x_i > n + 2c`
(`prependRed_eq_zero_of_mem_degree`). Hence the degree-`n` parts of the two projectives have
the same dimension.

## Main results

* `prependRed_e`: `e(s) ↦ e(λ₀ s)`.
* `finrank_lIdeal_grade_prependRed`: `dim (T̃^λ e(s))_n = dim (T^{(λ₀, λ)} e(λ₀ s))_n` for
  large `λ₀`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum _root_.Categorification.Graded _root_.Module

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I)
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "G₀" => restrictFirstRedGrading Q Λ G

/-- Adding the red strand sends `e(s)` to `e(λ₀ s)`. -/
theorem prependRed_e (s : Seq μ) (hs : IsRedOrdered s) :
    prependRed Q Λ ν (StendhalAlgebra.e s hs) =
      seqIdem Q Λ (prependRedLoading s) ((prependRedLoading_ordered_iff s).2 hs) := by
  rw [prependRed_apply]
  change orderedQuotient Q Λ ν
    (prependRedAllOrders Q Λ ν (StendhalAlgebraAllOrders.e s)).val = _
  have h := (prependRedLoading_ordered_iff s).2 hs
  rw [prependRedAllOrders_e, orderedQuotient_e]
  simp only [h, ↓reduceDIte]

/-- `e(s)` is idempotent in `T̃^λ`. -/
theorem stendhalAlgebra_e_mul_self (s : Seq μ) (hs : IsRedOrdered s) :
    (StendhalAlgebra.e s hs * StendhalAlgebra.e s hs : StendhalAlgebra k Q (Λ ∘ Fin.succ) ν) =
      StendhalAlgebra.e s hs := by
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e s * StendhalAlgebraAllOrders.e s =
    StendhalAlgebraAllOrders.e s
  rw [StendhalAlgebraAllOrders.e_mul_e]
  simp

/-- **The projectives agree in a fixed degree** (Webster, arXiv:1309.3796v3, proof of
Corollary 5.23). If the grading of all red orders of `T̃^λ` vanishes below `-c` and
`⟨α_i^∨, λ₀⟩ · deg x_i > n + 2c` for every black label `i`, then `(T̃^λ e(s))_n` and
`(T^{(λ₀, λ)} e(λ₀ s))_n` have the same dimension. -/
theorem finrank_lIdeal_grade_prependRed {c n : ℤ}
    (hc : ∀ m < -c, allOrdersGrade G₀ ν m = ⊥)
    (hΛ : ∀ i ∈ ν, n + 2 * c < Λ 0 i * G.degX (.inl i)) (s : Seq μ) (hs : IsRedOrdered s) :
    finrank k ((lIdeal (StendhalAlgebra.e s hs)).restrictScalars k ⊓ stendhalGrade G₀ ν n :) =
      finrank k ((lIdeal (seqIdem Q Λ (prependRedLoading s)
        ((prependRedLoading_ordered_iff s).2 hs))).restrictScalars k ⊓
          tensorProductGrade G ν n :) := by
  classical
  set hs' := (prependRedLoading_ordered_iff s).2 hs
  set X := (lIdeal (StendhalAlgebra.e s hs)).restrictScalars k ⊓ stendhalGrade G₀ ν n
  set Y := (lIdeal (seqIdem Q Λ (prependRedLoading s) hs')).restrictScalars k ⊓
    tensorProductGrade G ν n
  have hgr : PreservesGrading (stendhalGrade G₀ ν) (tensorProductGrade G ν)
      (prependRed Q Λ ν).toLinearMap := fun _ _ hx => prependRed_mem_grade Q Λ ν G hx
  have hmaps : ∀ x : X, prependRed Q Λ ν x ∈ Y := by
    intro x
    refine ⟨?_, hgr x.2.2⟩
    change _ * _ = _
    rw [← prependRed_e Q Λ ν s hs, ← map_mul]
    exact congrArg _ x.2.1
  let φ : X →ₗ[k] Y := ((prependRed Q Λ ν).toLinearMap.restrictScalars k |>.domRestrict X
    ).codRestrict Y hmaps
  have hinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    exact prependRed_injOn_degree Q Λ ν G₀ hc hΛ x.2.2 y.2.2 (congrArg Subtype.val h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy1, hy2⟩
    obtain ⟨z, hz⟩ := prependRed_surjective Q Λ ν y
    let z' := (decompose (stendhalGrade G₀ ν) z n : StendhalAlgebra k Q (Λ ∘ Fin.succ) ν) *
      StendhalAlgebra.e s hs
    have hz'X : z' ∈ X := by
      refine ⟨?_, ?_⟩
      · change _ * _ = _
        rw [mul_assoc, stendhalAlgebra_e_mul_self]
      · have h := SetLike.GradedMul.mul_mem (decompose (stendhalGrade G₀ ν) z n).2
          (e_mem_stendhalGrade G₀ ν s hs)
        rwa [add_zero] at h
    refine ⟨⟨z', hz'X⟩, Subtype.ext ?_⟩
    change prependRed Q Λ ν z' = y
    have hd := decompose_map hgr z n
    change (decompose (tensorProductGrade G ν) (prependRed Q Λ ν z) n : _) =
      prependRed Q Λ ν (decompose (stendhalGrade G₀ ν) z n) at hd
    rw [map_mul, prependRed_e, ← hd, hz, decompose_of_mem_same _ hy2]
    exact hy1
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq

end Categorification.Stendhal
