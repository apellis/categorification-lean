/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRedInjective
import Categorification.WeightedKLR.RedStrands.Projectives
import Categorification.Algebra.Graded.K0Exact

/-!
# Appending a terminal red strand preserves graded Hom

Webster, arXiv:1309.3796v2, §4.7, proof of Lemma 4.36, case
`κ(ℓ) = κ'(ℓ) = n`. Proposition 4.18 identifies the last-red corner
with the algebra on the earlier red strands. Its double idempotent
components identify degree by degree.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}
    {C : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ C Q)
    (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I)
local notation "A" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) ν
local notation "B" => TensorProductAlgebra k Q Λ ν
local notation "𝒜" => tensorProductGrade (restrictRedGrading Q Λ G) ν
local notation "ℬ" => tensorProductGrade G ν
local notation "σ" => appendRedEquiv Q Λ ν hQ
local notation "u" => TensorProductAlgebra.lastRedIdem Q Λ ν
local notation "hu" => TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν

private def appendLinear : A →ₗ[k] B where
  toFun x := (σ x).val
  map_add' x y := congrArg Subtype.val (map_add (σ) x y)
  map_smul' c x := (congrArg Subtype.val (map_smul (σ) c x)).trans (KLR.Corner.val_smul _ _)

local notation "φ" => appendLinear (Λ := Λ) hQ ν

private theorem append_mul (a b : A) : φ (a * b) = φ a * φ b := congrArg Subtype.val (map_mul (σ) a b)

private def appendCornerPiece (p q : A) (d : ℤ) :
    idem (Graded.submodule 𝒜 (leftIdeal p)) q d ≃ₗ[k]
      idem (Graded.submodule ℬ (leftIdeal (φ p))) (φ q) d := by
  have hg : PreservesGrading 𝒜 ℬ (φ) := fun _ _ hx => appendRed_mem_grade Q Λ ν G hx
  have hinj : Function.Injective (φ) := Subtype.val_injective.comp (σ).injective
  let f : idem (Graded.submodule 𝒜 (leftIdeal p)) q d →ₗ[k]
      idem (Graded.submodule ℬ (leftIdeal (φ p))) (φ q) d :=
    { toFun x := ⟨⟨⟨φ x.val.val.val, (append_mul (Λ := Λ) hQ ν _ _).symm.trans
          (congrArg (φ) x.val.val.property)⟩, Subtype.ext ((append_mul (Λ := Λ) hQ ν _ _).symm.trans
          (congrArg (φ) (congrArg Subtype.val x.val.property)))⟩, hg x.property⟩
      map_add' x y := Subtype.ext (Subtype.ext (Subtype.ext ((φ).map_add _ _)))
      map_smul' c x := Subtype.ext (Subtype.ext (Subtype.ext ((φ).map_smul _ _))) }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext (hinj (congrArg (fun t => t.val.val.val) h))))
  · intro y
    let z : B := y.val.val.val
    have hzq : φ q * z = z := congrArg Subtype.val y.val.property
    have hzp : z * φ p = z := y.val.val.property
    have huq : u * φ q = φ q := ((Subsemigroup.mem_corner_iff hu).mp (σ q).property).1
    have hpu : φ p * u = φ p := ((Subsemigroup.mem_corner_iff hu).mp (σ p).property).2
    have huz : u * z = z := by
      calc
        u * z = u * (φ q * z) := congrArg (u * ·) hzq.symm
        _ = z := by rw [← mul_assoc, huq, hzq]
    have hzu : z * u = z := by
      calc
        z * u = (z * φ p) * u := congrArg (· * u) hzp.symm
        _ = z := by rw [mul_assoc, hpu, hzp]
    let zc : TensorProductAlgebra.lastRedCorner Q Λ ν := ⟨z, (Subsemigroup.mem_corner_iff hu).2 ⟨huz, hzu⟩⟩
    let w : A := (σ).symm zc
    have hw : φ w = z := congrArg Subtype.val ((σ).apply_symm_apply zc)
    have hwp : w * p = w := hinj (by rw [append_mul, hw, hzp])
    have hqw : q * w = w := hinj (by rw [append_mul, hw, hzq])
    have hwd : w ∈ 𝒜 d := mem_of_injective_of_mem hg hinj (hw.symm ▸ y.property)
    exact ⟨⟨⟨⟨w, hwp⟩, Subtype.ext hqw⟩, hwd⟩, Subtype.ext (Subtype.ext (Subtype.ext hw))⟩

private abbrev idemAt (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) : A :=
  TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) ν (StendhalAlgebra.e s hs)

include hQ in
/-- Degreewise Hom invariance in the last-red case of Webster's Lemma 4.36.
The equality holds for all black weights and both ordered endpoints. -/
theorem finrank_homGrade_appendRed (s t : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (ht : IsRedOrdered t) (d : ℤ) :
    Module.finrank k (homGrade B
      (sequenceProj G (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs)).grading
      (sequenceProj G (appendRedLoading t) ((appendRedLoading_ordered_iff t).2 ht)).grading d) =
    Module.finrank k (homGrade A (sequenceProj (restrictRedGrading Q Λ G) s hs).grading
      (sequenceProj (restrictRedGrading Q Λ G) t ht).grading d) := by
  let p : A := idemAt (Λ := Λ) ν t ht
  let q : A := idemAt (Λ := Λ) ν s hs
  have he (j : Seq (stendhalWeight ℓ ν)) (hj : IsRedOrdered j) : IsIdempotentElem (idemAt (Q := Q) (Λ := Λ) ν j hj) := by
    apply IsIdempotentElem.map
    apply Subtype.ext
    change StendhalAlgebraAllOrders.e j * StendhalAlgebraAllOrders.e j =
      (StendhalAlgebraAllOrders.e j : StendhalAlgebraAllOrders k Q (Λ ∘ Fin.castSucc) ν)
    simp [StendhalAlgebraAllOrders.e_mul_e]
  have hq : IsIdempotentElem q := he s hs
  have hq' : IsIdempotentElem (φ q) := (hq.map (σ)).map (KLR.cornerVal hu)
  have h₀ : q ∈ 𝒜 0 := mk_e_mem_tensorProductGrade _ _ s hs
  have h₁ : φ q ∈ ℬ 0 := appendRed_mem_grade Q Λ ν G h₀
  have hpv := appendRed_mk_e Q Λ ν t ht
  have hqv := appendRed_mk_e Q Λ ν s hs
  let es := TensorProductAlgebra.mk Q Λ ν
    (StendhalAlgebra.e (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs))
  let et := TensorProductAlgebra.mk Q Λ ν
    (StendhalAlgebra.e (appendRedLoading t) ((appendRedLoading_ordered_iff t).2 ht))
  change φ q = es at hqv
  change φ p = et at hpv
  change Module.finrank k (homGrade B (Graded.submodule ℬ (leftIdeal es))
    (Graded.submodule ℬ (leftIdeal et)) d) = _
  rw [← hqv, ← hpv]
  exact (homGradeIdemEquiv (ℳ := Graded.submodule ℬ (leftIdeal (φ p))) hq' h₁ d).finrank_eq.trans
    (((appendCornerPiece hQ G ν p q d).finrank_eq.symm).trans
      (homGradeIdemEquiv (ℳ := Graded.submodule 𝒜 (leftIdeal p)) hq h₀ d).finrank_eq.symm)

end Categorification.Stendhal
