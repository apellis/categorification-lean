/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandard
import Categorification.WeightedKLR.RedStrands.ParabolicStandardUnitExt

/-!
# Unit vectors of `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β))`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
proof of Proposition 5.5. For a pair `p = (t, u)` of a sequence `t` of root function `α'` and
a black word `u` of the last block, the vector `[e(t)] ⊠ e(u)` of `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`
(`rootPairUnit`) generates the input module over the factor algebra as `p` varies
(`span_rootPairUnit`), and the isomorphism `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` sends its unit
vector to the unit vector `[e(t λ_{ℓ+1} u)]` of the summand `S_{t λ_{ℓ+1} u}`
(`twoPieceRootStandardEquiv_unit`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (b : Fin (ℓ + 2) → Multiset I)

local notation "θ" => initWeight b
local notation "β" => lastBlock b
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)
local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
set_option quotPrecheck false in
local notation "V" => ParabolicStandardT Q Λ (initWeight b) (lastBlock b)
  (rootSplitInput Q Λ b).carrier hQ

/-- The vector `[e(t)] ⊠ e(u)` of `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`, for `p = (t, u)`. -/
def rootPairUnit (p : RootPair b) : (rootSplitInput Q Λ b).carrier :=
  rootSplitIncl Q Λ b p (twoPieceInputUnit Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2)

theorem rootSplitIncl_mem_span (p : RootPair b) (x : (rootPairInput Q Λ b p).carrier) :
    rootSplitIncl Q Λ b p x ∈ Submodule.span D (Set.range (rootPairUnit Q Λ b)) := by
  induction x using ExtTensor.induction_on with
  | zero =>
    exact (congrArg (· ∈ Submodule.span D (Set.range (rootPairUnit Q Λ b)))
      (map_zero (rootSplitIncl Q Λ b p))).mpr (Submodule.zero_mem _)
  | tmul m y =>
    obtain ⟨c, hc⟩ := twoPieceExt_eq_smul Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2 m y
    have hc' : (show (rootPairInput Q Λ b p).carrier from ExtTensor.tmul m y) =
        parabolicInputMap Q Λ θ β c •
          (show (rootPairInput Q Λ b p).carrier from
            twoPieceInputUnit Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2) := hc
    refine (congrArg (fun z => rootSplitIncl Q Λ b p z ∈
      Submodule.span D (Set.range (rootPairUnit Q Λ b))) hc').mpr ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  | add x y hx hy =>
    exact (congrArg (· ∈ Submodule.span D (Set.range (rootPairUnit Q Λ b)))
      (map_add (rootSplitIncl Q Λ b p) x y)).mpr (Submodule.add_mem _ hx hy)

/-- The vectors `[e(t)] ⊠ e(u)` generate `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)` over the factor algebra. -/
theorem span_rootPairUnit : Submodule.span D (Set.range (rootPairUnit Q Λ b)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun n => ?_
  have hn := LinearMap.congr_fun (sum_rootSplitIncl_proj Q Λ b) n
  rw [LinearMap.sum_apply, LinearMap.id_apply] at hn
  rw [← hn]
  exact Submodule.sum_mem _ fun p _ => rootSplitIncl_mem_span Q Λ b p _

/-- The unit vector `[e(t λ_{ℓ+1} u)]` of the summand `S_{t λ_{ℓ+1} u}`. -/
abbrev rootPairStandardUnit (p : RootPair b) : rootPairStandard Q Λ b p :=
  leftStandardUnit Q Λ (twoPieceLoading θ β p.1.1 p.2)
    (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2)

theorem rootPairSum_single (p : RootPair b) :
    rootPairSum Q Λ hQ b (Pi.single p (rootPairStandardUnit Q Λ b p)) =
      parabolicStandardTUnit Q Λ θ β hQ (rootPairUnit Q Λ b p) := by
  rw [rootPairSum, LinearMap.sum_apply, Finset.sum_eq_single p]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same,
      LinearEquiv.coe_coe, twoPieceStandardEquiv_symm_unit]
    rfl
  · intro q _ hq
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hq,
      LinearEquiv.coe_coe, LinearEquiv.map_zero, LinearMap.map_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **The isomorphism on unit vectors**: `S(S^L_{α'} ⊠ R(β)) ≅ S^L_α` sends the unit vector of
`[e(t)] ⊠ e(u)` to the unit vector of the summand `S_{t λ_{ℓ+1} u}`. -/
theorem twoPieceRootStandardEquiv_symm_single (p : RootPair b) :
    (twoPieceRootStandardEquiv Q Λ hQ b).symm
      (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b)
        (blockRoot b) => leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        (rootPairSeq b p) (rootPairStandardUnit Q Λ b p)) =
      parabolicStandardTUnit Q Λ θ β hQ (rootPairUnit Q Λ b p) := by
  have h : (LinearEquiv.piCongrLeft Tν (fun s : StendhalAlgebra.RootSeq
      (ν := initWeight b + lastBlock b) (blockRoot b) =>
        leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
      (rootPairSeqEquiv b)).symm
      (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b)
        (blockRoot b) => leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        (rootPairSeq b p) (rootPairStandardUnit Q Λ b p)) =
      Pi.single (M := rootPairStandard Q Λ b) p (rootPairStandardUnit Q Λ b p) := by
    funext q
    change Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b)
        (blockRoot b) => leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        (rootPairSeq b p) (rootPairStandardUnit Q Λ b p) (rootPairSeq b q) = _
    by_cases hq : q = p
    · subst hq
      rw [Pi.single_eq_same]
      exact Pi.single_eq_same (M := fun s : StendhalAlgebra.RootSeq
        (ν := initWeight b + lastBlock b) (blockRoot b) =>
          leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) _ _
    · rw [Pi.single_eq_of_ne hq]
      exact Pi.single_eq_of_ne (M := fun s : StendhalAlgebra.RootSeq
        (ν := initWeight b + lastBlock b) (blockRoot b) =>
          leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        (fun h' => hq ((rootPairSeq_bijective b).1 h')) _
  exact (congrArg (rootPairEquivPi Q Λ hQ b).symm h).trans (rootPairSum_single Q Λ hQ b p)

theorem twoPieceRootStandardEquiv_unit (p : RootPair b) :
    twoPieceRootStandardEquiv Q Λ hQ b (parabolicStandardTUnit Q Λ θ β hQ (rootPairUnit Q Λ b p)) =
      Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b)
        (blockRoot b) => leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        (rootPairSeq b p) (rootPairStandardUnit Q Λ b p) := by
  rw [← twoPieceRootStandardEquiv_symm_single, LinearEquiv.apply_symm_apply]

end Categorification.Stendhal
