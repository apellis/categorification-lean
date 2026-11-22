/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedHeadEmbedding
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv

/-!
# The last red strand of a maximal loading

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, step in the
proof of Proposition 5.17. Let `L` be the simple head at the cut `u` of the last red strand
(`HeadAtCut`). If a two-piece loading `t λ_{ℓ+1} w` with black prefix `θ` acts nonzero on `L`,
then `θ ≤ u.1.1`, since concatenations at cuts whose prefix is not below `u.1.1` kill `L`. If
moreover no red-ordered loading strictly above `t λ_{ℓ+1} w` acts nonzero on `L`, then `L` is a
quotient of the standard module `S_{t λ_{ℓ+1} w}`, which is the standardization of
`S_t ⊠ R e(w)` at the cut `θ`; concatenations at cuts whose prefix is not below `θ` kill it,
while the concatenation at `u` acts nonzero on `L`. Hence `θ = u.1.1`.

## Main results

* `lastRedCutConcat_twoPiece`: `e(t λ_{ℓ+1} w)` is a concatenation at the cut `(θ, β)`.
* `HeadAtCut.prefix_le_of_twoPiece`: `θ ≤ u.1.1` when `e(t λ_{ℓ+1} w)` acts nonzero.
* `HeadAtCut.prefix_eq_of_maximal`: `θ = u.1.1` when moreover `t λ_{ℓ+1} w` is maximal.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded GProj
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {D : QuantumGroup.CartanDatum I}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) {θ β : Multiset I}

local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)

/-- The cut `(θ, β)` of the weight `θ + β`. -/
abbrev twoPieceCut (θ β : Multiset I) : LastRedWeightSplit (θ + β) := ⟨(θ, β), rfl⟩

/-- The idempotent of a two-piece loading is a concatenation at its cut. -/
theorem lastRedCutConcat_twoPiece {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t)
    (w : Seq β) :
    lastRedCutConcat (Q := Q) Λ (θ + β) (twoPieceCut θ β)
      (e (Seq.map (addRedColor ℓ) t) ⊗ₜ e (Seq.map lc (SingleRed.insertWord β w))) =
      seqIdem Q Λ (twoPieceLoading θ β t w) (isRedOrdered_twoPieceLoading ht w) :=
  twoPieceAffine_e Q Λ ht w

variable (G : GradingDatum (stendhalQ Q Λ))

/-- A two-piece loading acting nonzero on a head at the cut `u` has its black prefix below
`u.1.1`. -/
theorem HeadAtCut.prefix_le_of_twoPiece {u : LastRedWeightSplit (θ + β)}
    {b : IndecClass (lastRedFactorGrading Λ (θ + β) G u)}
    {s : IndecClass (tensorProductGrade G (θ + β))} (hs : HeadAtCut Λ (θ + β) G u b s)
    {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (w : Seq β) {x : s.top}
    (hx : seqIdem Q Λ (twoPieceLoading θ β t w) (isRedOrdered_twoPieceLoading ht w) • x ≠ 0) :
    θ ≤ u.1.1 := by
  by_contra hn
  apply hx
  rw [← lastRedCutConcat_twoPiece Λ ht w]
  exact hs.2.1 (twoPieceCut θ β) hn _ x

variable {Λ G} in
/-- **Webster, arXiv:1309.3796v2, step in the proof of Proposition 5.17.** A two-piece loading
which acts nonzero on the head `L` at the cut `u`, and above which no red-ordered loading acts
nonzero on `L`, has the black prefix `u.1.1`. -/
theorem HeadAtCut.prefix_eq_of_maximal (hQ : IsRouquierQ D Q)
    {u : LastRedWeightSplit (θ + β)}
    {b : IndecClass (lastRedFactorGrading Λ (θ + β) G u)}
    {s : IndecClass (tensorProductGrade G (θ + β))} (hs : HeadAtCut Λ (θ + β) G u b s)
    {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (w : Seq β) {x : s.top}
    (hx : seqIdem Q Λ (twoPieceLoading θ β t w) (isRedOrdered_twoPieceLoading ht w) • x ≠ 0)
    (hmax : ∀ (p : Seq (stendhalWeight (ℓ + 1) (θ + β))) (hp : IsRedOrdered p),
      StendhalLT (twoPieceLoading θ β t w) p → ∀ y : s.top, seqIdem Q Λ p hp • y = 0) :
    u.1.1 = θ := by
  refine le_antisymm ?_ (hs.prefix_le_of_twoPiece Λ G ht w hx)
  by_contra hn
  let := tensorProductAlgebra_finite Λ (θ + β) hQ
  let := Module.Finite.trans (R := k) (A := TensorProductAlgebra k Q Λ (θ + β)) (M := s.top)
  let := (IndecClass.isGradedSimple_top s).isSimpleModule
  let := (IndecClass.isGradedSimple_top b).nontrivial
  set tp := twoPieceLoading θ β t w
  have htp := isRedOrdered_twoPieceLoading ht w
  set z := seqIdem Q Λ tp htp • x with hz
  -- `L` is a quotient of `S_{t λ_{ℓ+1} w}`.
  let f := leftStandardLift (Q := Q) (Λ := Λ) tp htp z fun p hp a hlt => by
    rw [← smul_smul]
    exact hmax p hp hlt _
  have hf : f (leftStandardUnit Q Λ tp htp) = z := by
    refine leftStandardLift_unit tp htp z ?_ _
    rw [hz, smul_smul, seqIdem_mul_self]
  let g := f ∘ₗ (twoPieceStandardEquiv Q Λ ht w (IsRouquierQ.klrSymm hQ)).toLinearMap
  have hg : Function.Surjective g := by
    have hrange : LinearMap.range g ≠ ⊥ := by
      intro h0
      apply hx
      have : z ∈ LinearMap.range g := ⟨(twoPieceStandardEquiv Q Λ ht w
        (IsRouquierQ.klrSymm hQ)).symm (leftStandardUnit Q Λ tp htp), by
          change f ((twoPieceStandardEquiv Q Λ ht w (IsRouquierQ.klrSymm hQ))
            ((twoPieceStandardEquiv Q Λ ht w (IsRouquierQ.klrSymm hQ)).symm _)) = z
          rw [LinearEquiv.apply_symm_apply, hf]⟩
      rw [h0] at this
      exact (Submodule.mem_bot _).1 this
    exact LinearMap.range_eq_top.1 ((IsSimpleOrder.eq_bot_or_eq_top _).resolve_left hrange)
  -- The concatenation at `u` fixes the image of the factor simple.
  obtain ⟨t₀, ht₀⟩ := lastRedCutConcat_exists_lift (Q := Q) Λ (θ + β) u
  let F := hs.1.some
  obtain ⟨y, hy⟩ := exists_ne (0 : b.top)
  have hfix := F.intertwines _ 1 ht₀ y
  rw [one_smul] at hfix
  obtain ⟨v, hv⟩ := hg (F.incl y)
  have hzero : lastRedCutConcat (Q := Q) Λ (θ + β) u t₀ • v = 0 :=
    LinearMap.congr_fun (parabolicStandardAction_other_concat_eq_zero Q Λ θ β _
      (IsRouquierQ.klrSymm hQ) u.1.1 u.1.2 u.2 hn t₀) v
  apply hy
  apply F.injective
  rw [map_zero, ← hfix, ← hv, ← map_smul, hzero, map_zero]

end Categorification.Stendhal
