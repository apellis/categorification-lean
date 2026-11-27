/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandardBlocks
import Categorification.WeightedKLR.RedStrands.TwoPieceLastBlockMap

/-!
# The block actions on `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α`, last block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and proof of Proposition 5.5. The block algebra `R(b_{ℓ+1}) = R(β)` of the last
block acts on `R^{λ_{ℓ+1}}(β)` by right multiplication with the flipped diagram, and on the left
root standard module `S^L_α` through the block diagram of Proposition 5.3 (reflected to left
modules). The isomorphism `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` intertwines the
standardization of the first action with the second (`twoPieceRootStandardEquiv_lastBlock`).
-/

set_option backward.isDefEq.respectTransparency false

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
local notation "α'" => blockRoot (initBlocks b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "πB" => CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)
local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
local notation "S" => stendhalQ Q Λ
local notation "S'" => stendhalQ Q (Λ ∘ Fin.castSucc)
local notation "ρ" => redSubfamilyRelabel Q Λ Fin.castSucc (Fin.castSucc_injective ℓ)
  (initWeight b)
local notation "lc" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)
local notation "L'" => StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := initWeight b)
  (blockRoot (initBlocks b))
local notation "L" => StendhalAlgebra.LeftRootStandard Q Λ (ν := initWeight b + lastBlock b)
  (blockRoot b)
local notation "π" => stendhalTensorProjection (Q := Q) Λ (initWeight b + lastBlock b)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) (initWeight b) (lastBlock b)

/-- `id ⊠ (· y)` on `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`, for `y` in the cyclotomic quotient. -/
def rootSplitRightMap (y : Cyc) :
    (rootSplitInput Q Λ b).carrier →ₗ[D] (rootSplitInput Q Λ b).carrier :=
  ExtTensor.map (k := k) (KMod.map (X := ModuleCat.of Told L') (Y := ModuleCat.of Told L')
    LinearMap.id)
    (KMod.map (X := ModuleCat.of Cyc Cyc) (Y := ModuleCat.of Cyc Cyc)
      (LinearMap.toSpanSingleton Cyc Cyc y))

theorem parabolicLastCyclotomic_lastBlackMap (y : KLRAlgebra k Q β) :
    parabolicLastCyclotomic Q Λ β (lastBlackMap Q Λ β y) = πB y :=
  parabolicLastCyclotomic_concat_black Q Λ β y

/-- `[e(t)] ⊠ e(u) y` as a sum over the vectors `[e(t)] ⊠ e(u')`. -/
theorem rootSplitRightMap_rootPairUnit (a : KLRAlgebra k Q β) (p : RootPair b) :
    rootSplitRightMap Q Λ b (πB (hflip a)) (rootPairUnit Q Λ b p) =
      ∑ u' : Seq β, parabolicInputMap Q Λ θ β (1 ⊗ₜ lastBlackMap Q Λ β (e p.2 * hflip a)) •
        rootPairUnit Q Λ b (p.1, u') := by
  have h1 : rootSplitRightMap Q Λ b (πB (hflip a)) (rootPairUnit Q Λ b p) =
      (show (rootSplitInput Q Λ b).carrier from ExtTensor.tmul (k := k)
        (P := KMod (k := k) (ModuleCat.of Told L')) (Q := KMod (k := k) (ModuleCat.of Cyc Cyc))
        (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
          leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) p.1
          (leftStandardUnit Q (Λ ∘ Fin.castSucc) p.1.1
            (StendhalAlgebra.RootSeq.isRedOrdered _ p.1)))
        (πB (e p.2) * πB (hflip a))) := rfl
  have h2 : πB (e p.2) * πB (hflip a) =
      ∑ u' : Seq β, parabolicLastCyclotomic Q Λ β (lastBlackMap Q Λ β (e p.2 * hflip a)) *
        πB (e u') := by
    rw [← Finset.mul_sum, ← map_sum, sum_e, map_one, mul_one,
      parabolicLastCyclotomic_lastBlackMap, map_mul]
  rw [h1, h2]
  refine (TensorProduct.tmul_sum _ _ _).trans (Finset.sum_congr rfl fun u' _ => ?_)
  rw [parabolicInputMap, Algebra.TensorProduct.map_tmul, map_one]
  refine Eq.trans ?_ (ExtTensor.smul_tmul (k := k) (P := KMod (k := k) (ModuleCat.of Told L'))
    (Q := KMod (k := k) (ModuleCat.of Cyc Cyc)) _ _ _ _).symm
  rw [one_smul]
  rfl

section Last

variable (hα : StendhalAlgebra.RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))

/-- The block action of the last block `R(b_{ℓ+1})` on the left root standard module `S^L_α` of
all `ℓ + 1` red strands. -/
abbrev lastBlockAction (a : KLRAlgebra k Q β) : Module.End Tν L :=
  StendhalAlgebra.rootReflectConj Q Λ hα
    (StendhalAlgebra.rootBlockAction Q Λ (b := b) (blockPrefix_last b) (ℓ + 1)
      (Nat.lt_succ_self (ℓ + 1)) a)

/-- The block diagram of `a` on the last block of all `ℓ + 1` red strands. -/
abbrev lastBlockDiagram (a : KLRAlgebra k Q β) :
    KLRAlgebra k S (stendhalWeight (ℓ + 1) (θ + β)) :=
  ((StendhalAlgebra.blockEmb (b := b) (blockPrefix_last b) (ℓ + 1)
    (Nat.lt_succ_self (ℓ + 1))).hom S
    (KLRAlgebra.reindexEquiv Sum.inl_injective S (b ⟨ℓ + 1, Nat.lt_succ_self (ℓ + 1)⟩) a)).val

theorem lastBlockDiagram_eq (a : KLRAlgebra k Q β) :
    lastBlockDiagram Q Λ b a =
      suffixBlockMap Q Λ θ β (StendhalAlgebra.rootSet θ α') (lastBlackMap Q Λ β a) :=
  (suffixBlockMap_lastBlackMap Q Λ b a).symm

theorem lastBlockDiagram_mul_e (a : KLRAlgebra k Q β) (p : RootPair b)
    (t'' : StendhalAlgebra.RootSeq (ν := θ) α') (u'' : Seq β) :
    π (hflip (lastBlockDiagram Q Λ b a * e (twoPieceLoading θ β p.1.1 p.2))) *
      TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e (twoPieceLoading θ β t''.1 u'')
        (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ t'') u'')) =
      π (castKLR S H (concat S _ _ (relabelEquiv ρ
        (e p.1.1 * eSum S' (StendhalAlgebra.rootSet θ α') * e t''.1) ⊗ₜ
          (e (Seq.map lc (SingleRed.insertWord β p.2)) * lastBlackMap Q Λ β (hflip a) *
            e (Seq.map lc (SingleRed.insertWord β u'')))))) := by
  rw [← stendhalTensorProjection_e, ← map_mul, lastBlockDiagram_eq,
    hflip_suffixBlockMap_mul_e_mul_e, hflip_lastBlackMap]

theorem lastBlockWord_mul_e (a : KLRAlgebra k Q β) (p : RootPair b) (u'' : Seq β) :
    parabolicAffine Q Λ θ β (concat S _ _ (1 ⊗ₜ lastBlackMap Q Λ β (e p.2 * hflip a))) *
      TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e (twoPieceLoading θ β p.1.1 u'')
        (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) u'')) =
      π (castKLR S H (concat S _ _ (relabelEquiv ρ
        (e p.1.1 * eSum S' (StendhalAlgebra.rootSet θ α') * e p.1.1) ⊗ₜ
          (e (Seq.map lc (SingleRed.insertWord β p.2)) * lastBlackMap Q Λ β (hflip a) *
            e (Seq.map lc (SingleRed.insertWord β u'')))))) := by
  rw [← stendhalTensorProjection_e]
  change π (castKLR S _ _) * _ = _
  rw [← map_mul, concat_one_tmul_mul_e, e_mul_eSum, ite_eq_left_of_eq_true _ _ (eq_true p.1.2),
    e_mul_e, ite_eq_left_of_eq_true _ _ (eq_true rfl), map_mul,
    lastBlackMap_e]

/-- **The isomorphism intertwines the block actions of the last block**
(arXiv:1309.3796v3, Proposition 5.3 and proof of Proposition 5.5). -/
theorem twoPieceRootStandardEquiv_lastBlock (a : KLRAlgebra k Q β) :
    (twoPieceRootStandardEquiv Q Λ hQ b).toLinearMap ∘ₗ
        parabolicStandardMapT Q Λ hQ (rootSplitRightMap Q Λ b (πB (hflip a))) =
      lastBlockAction Q Λ b hα a ∘ₗ (twoPieceRootStandardEquiv Q Λ hQ b).toLinearMap := by
  refine parabolicStandardT_ext_span Q Λ θ β hQ (span_rootPairUnit Q Λ b) ?_
  rintro _ ⟨p, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hL : parabolicStandardMapT Q Λ hQ (rootSplitRightMap Q Λ b (πB (hflip a)))
      (parabolicStandardTUnit Q Λ θ β hQ (rootPairUnit Q Λ b p)) =
      parabolicStandardTUnit Q Λ θ β hQ
        (rootSplitRightMap Q Λ b (πB (hflip a)) (rootPairUnit Q Λ b p)) := rfl
  rw [hL, rootSplitRightMap_rootPairUnit, parabolicStandardTUnit_sum']
  simp_rw [parabolicStandardTUnit_smul]
  rw [map_sum]
  simp_rw [map_smul, twoPieceRootStandardEquiv_unit]
  funext s'
  obtain ⟨q, rfl⟩ := (rootPairSeq_bijective b).2 s'
  rw [Finset.sum_apply]
  refine Eq.trans ?_ (rootReflectConj_rootBlockAction_single (blockPrefix_last b) (ℓ + 1)
    (Nat.lt_succ_self (ℓ + 1)) hα a (rootPairSeq b p) (rootPairSeq b q)).symm
  obtain ⟨t'', u''⟩ := q
  rw [Finset.sum_eq_single u'']
  · rw [Pi.smul_apply]
    by_cases ht : p.1 = t''
    · subst ht
      rw [Pi.single_eq_same]
      refine smul_leftStandardUnit_eq _ ?_
      exact (lastBlockWord_mul_e Q Λ b a p u'').trans
        (lastBlockDiagram_mul_e Q Λ b a p p.1 u'').symm
    · rw [Pi.single_eq_of_ne
        (fun h => ht (congrArg Prod.fst ((rootPairSeq_bijective b).1 h)).symm), smul_zero]
      refine (smul_leftStandardUnit_eq_zero _ ?_).symm
      refine (lastBlockDiagram_mul_e Q Λ b a p t'' u'').trans ?_
      rw [e_mul_eSum, ite_eq_left_of_eq_true _ _ (eq_true p.1.2), e_mul_e,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => ht (Subtype.ext h)), map_zero,
        TensorProduct.zero_tmul, map_zero, map_zero, map_zero]
  · intro u' _ hu'
    rw [Pi.smul_apply, Pi.single_eq_of_ne
      (fun h => hu' (congrArg Prod.snd ((rootPairSeq_bijective b).1 h)).symm), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ u'') h

end Last

end Categorification.Stendhal
