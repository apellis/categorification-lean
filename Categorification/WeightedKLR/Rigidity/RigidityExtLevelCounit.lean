/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtDetection
import Categorification.WeightedKLR.RedStrands.LastRedMaximalLoading

/-!
# The counit of standardization at one split

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Proposition 7.8. Let `Z` be a finite-dimensional module over `T^λ` killed by the loadings whose
last red strand is after position `|θ| + ℓ`. The counit `S(R(Z)) → Z` of the adjunction between
standardization at the split `θ + β` and restriction to the layer of that split
(`levelHomEquiv`) has two properties used in the construction of the resolution of `L_λ`:

* its image contains `e(s) Z` for every loading `s = t λ_ℓ w` of the split `θ + β`;
* it is injective on the vectors `e(s) m` of `S(R(Z))`.

Loadings of another split `θ' + β'` with `θ' ≰ θ` act by zero on standardizations at `θ + β`.

## Main results

* `exists_levelCounit`: the restriction `R(Z)`, finite-dimensional, with its counit.
* `loadingIdem_smul_stdLayerModule_eq_zero`: loadings of other splits kill standardizations.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra CategoryTheory
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)

section Split

variable (θ β : Multiset I)

local notation "P" => LastRedWeightSplit.position (θ + β) (levelSplit θ β) ℓ
local notation "HW" => LastRedWeightSplit.content (θ + β) (levelSplit θ β) ℓ
local notation "HL" => LastRedWeightSplit.length (θ + β) (levelSplit θ β) ℓ
local notation "Jl" => smallerSuffixIdeal Q Λ P
local notation "ψ" => lastRedLayerAction Q Λ P HW HL

omit [DecidableEq I] in
theorem levelSplit_position_val : (P).val = Multiset.card θ + ℓ := by
  simp [LastRedWeightSplit.position, stendhalWeight]

/-- A module killed after the position `|θ| + ℓ` is killed by the ideal of the split. -/
theorem killedByLevel_of_killedAfter {Z : ModuleCat.{0} (TensorProductAlgebra k Q Λ (θ + β))}
    (hZ : KilledAfter Q Λ (Multiset.card θ + ℓ) Z) : KilledByLevel Q Λ θ β Z :=
  fun _ hx z => KilledAfter.smul_eq_zero (p := P)
    (by rw [levelSplit_position_val]; exact hZ) hx z

variable {Q Λ θ β}

/-- The loadings `t λ_ℓ w` of the split `θ + β` are fixed by the layer idempotent. -/
theorem levelAction_one_twoPiece {Z : Type} [AddCommGroup Z] [Module k Z]
    [Module (TensorProductAlgebra k Q Λ (θ + β)) Z]
    [IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β)) Z] (hZ : KilledByLevel Q Λ θ β Z)
    {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t) (w : Seq β) (z : Z) :
    levelAction hZ (ψ 1) (seqIdem Q Λ (twoPieceLoading θ β t w)
      (isRedOrdered_twoPieceLoading ht w) • z) =
      seqIdem Q Λ (twoPieceLoading θ β t w) (isRedOrdered_twoPieceLoading ht w) • z := by
  have hmk := mk_parabolicAffine_concat Q Λ θ β
    (e (Seq.map (addRedColor ℓ) t) ⊗ₜ e (Seq.map lc (SingleRed.insertWord β w)))
  rw [twoPieceAffine_e Q Λ ht w] at hmk
  rw [← levelAction_mk hZ, hmk, ← Module.End.mul_apply, ← map_mul, ← map_mul, one_mul]

end Split

variable (hQ : KLRSymm Q)

omit [DecidableEq I] in
theorem seqCast_rfl {μ : Multiset (I ⊕ Fin (ℓ + 1))} (s : Seq μ) : Seq.cast rfl s = s := rfl

/-- **The counit at one split.** Let `Z` be finite-dimensional and killed after the position
`|θ| + ℓ`. There is a finite-dimensional module `N` over the factor algebra of `θ + β` (the
restriction `R(Z)`) and a map `ε : S(N) → Z` whose image contains `e(s) Z` for the loadings
`s = t λ_ℓ w` of the split, and which is injective on the vectors `e(s) m`. -/
theorem exists_levelCounit {θ β ν : Multiset I} (h : θ + β = ν)
    (Z : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) [FiniteDimensional k Z]
    (hZ : KilledAfter Q Λ (Multiset.card θ + ℓ) Z) :
    ∃ (N : FactorModule Q Λ θ β) (_ : FiniteDimensional k N.carrier)
      (ε : stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩ →ₗ[TensorProductAlgebra k Q Λ ν] Z),
      ∀ (β' : Multiset I) (h' : θ + β' = ν) (t : Seq (stendhalWeight ℓ θ)) (_ht : IsRedOrdered t)
        (w : Seq β') (hs : IsRedOrdered (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h')
          (twoPieceLoading θ β' t w))),
        (∀ z : Z, loadingIdem Q Λ _ hs • z ∈ LinearMap.range ε) ∧
          ∀ m, ε (loadingIdem Q Λ _ hs • m) = 0 → loadingIdem Q Λ _ hs • m = 0 := by
  subst h
  let hK := killedByLevel_of_killedAfter Q Λ θ β hZ
  have : FiniteDimensional k (LevelModule hK) := inferInstanceAs (FiniteDimensional k Z)
  let N : FactorModule Q Λ θ β := ⟨levelRestriction hK⟩
  have hN : FiniteDimensional k N.carrier :=
    inferInstanceAs (FiniteDimensional k (Graded.idemSubspace k (LevelModule hK) _))
  let ε : ParabolicStandardT Q Λ θ β N.carrier hQ →ₗ[TensorProductAlgebra k Q Λ (θ + β)] Z :=
    levelDesc Q Λ θ β hQ hK LinearMap.id
  refine ⟨N, hN, ε, fun β' h' t ht w hs => ?_⟩
  obtain rfl : β = β' := (add_left_cancel h').symm
  let hS := killedByLevel_parabolicStandardT Q Λ θ β hQ N.carrier
  refine ⟨fun z => ?_, fun m hm => ?_⟩
  · let x : levelRestriction hK := ⟨_, levelAction_one_twoPiece hK ht w z⟩
    exact ⟨parabolicStandardTUnit Q Λ θ β hQ x, levelDesc_unit Q Λ θ β hQ hK _ x⟩
  · let y : levelRestriction hS := ⟨_, levelAction_one_twoPiece hS ht w m⟩
    let n := (levelUnitEquiv Q Λ θ β hQ N.carrier).symm y
    have hn : parabolicStandardTUnit Q Λ θ β hQ n = levelVal hS y :=
      congrArg (levelVal hS) ((levelUnitEquiv Q Λ θ β hQ N.carrier).apply_symm_apply y)
    have h0 : n = 0 := by
      apply levelVal_injective hK
      refine ((levelDesc_unit Q Λ θ β hQ hK LinearMap.id n).symm.trans ?_)
      change ε (parabolicStandardTUnit Q Λ θ β hQ n) = 0
      rw [hn]
      exact hm
    change levelVal hS y = 0
    rw [← hn, h0]
    exact parabolicStandardTUnit_zero Q Λ θ β hQ

/-- The idempotent of a loading `t λ_ℓ w` of the split `θ' + β' = ν` is a concatenation at
that split. -/
theorem loadingIdem_cast_twoPiece {θ' β' ν : Multiset I} (h' : θ' + β' = ν)
    {t : Seq (stendhalWeight ℓ θ')} (ht : IsRedOrdered t) (w : Seq β')
    (hs : IsRedOrdered (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h')
      (twoPieceLoading θ' β' t w))) :
    loadingIdem Q Λ _ hs = lastRedCutConcat (Q := Q) Λ ν ⟨(θ', β'), h'⟩
      (e (Seq.map (addRedColor ℓ) t) ⊗ₜ e (Seq.map lc (SingleRed.insertWord β' w))) := by
  subst h'
  exact (lastRedCutConcat_twoPiece Λ ht w).symm

/-- **Other splits act by zero**: the loadings `t λ_ℓ w` of a split `θ' + β'` with `θ' ≰ θ`
kill the standardization of every module over the factor algebra of `θ + β`. -/
theorem loadingIdem_smul_stdLayerModule_eq_zero {ν : Multiset I} (c : StdLayer Q Λ ν)
    {θ' β' : Multiset I} (h' : θ' + β' = ν) (hn : ¬ θ' ≤ c.θ)
    {t : Seq (stendhalWeight ℓ θ')} (ht : IsRedOrdered t) (w : Seq β')
    (hs : IsRedOrdered (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h')
      (twoPieceLoading θ' β' t w))) (m : stdLayerModule Q Λ hQ c) :
    loadingIdem Q Λ _ hs • m = 0 := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  rw [loadingIdem_cast_twoPiece Q Λ h' ht w hs]
  exact LinearMap.congr_fun (parabolicStandardAction_other_concat_eq_zero Q Λ θ β M.carrier hQ
    θ' β' h' hn _) (show ParabolicStandardT Q Λ θ β M.carrier hQ from m)

end Categorification.Stendhal
