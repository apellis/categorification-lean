/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceRootStandardUnit
import Categorification.WeightedKLR.RedStrands.RootReflectUnit
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockMapIdems

/-!
# The block actions on `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α`, first `ℓ + 1` blocks

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and proof of Proposition 5.5. For `j ≤ ℓ`, the block algebra `R(b_j)` acts on
the left root standard module `S^L_{α'}` of the first `ℓ` red strands and on `S^L_α`, through the
block diagrams of Proposition 5.3 (reflected to left modules). The isomorphism
`S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` intertwines the standardization of the first action with
the second (`twoPieceRootStandardEquiv_initBlock`): a diagram on the block `b_j` of the first
`ℓ` red strands, extended by the last red strand and the black words of `b_{ℓ+1}`, is the same
diagram on the block `b_j` of all `ℓ + 1` red strands (`prefixBlockMap_blockEmb`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I}

/-- The class in `T^λ` of a block diagram followed by an idempotent. -/
theorem mk_blockHom_mul_e (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1)
    (a : KLRAlgebra k Q (b ⟨j, hj⟩)) (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    TensorProductAlgebra.mk Q Λ ν
        ((StendhalAlgebra.blockHom Q Λ hb j hj a).val * StendhalAlgebra.e s hs) =
      stendhalTensorProjection (Q := Q) Λ ν
        (((StendhalAlgebra.blockEmb hb j hj).hom (stendhalQ Q Λ)
          (KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ) (b ⟨j, hj⟩) a)).val * e s) := by
  have h1 : (StendhalAlgebra.blockHom Q Λ hb j hj a).val =
      orderProjection Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        ((StendhalAlgebra.blockEmb hb j hj).hom (stendhalQ Q Λ)
          (KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ) (b ⟨j, hj⟩) a)).val) := by
    rw [← StendhalAlgebra.val_val_blockHom]
    exact (Subtype.ext (KLR.Corner.val_mul_E _)).symm
  have h2 : StendhalAlgebra.e s hs =
      orderProjection Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (e s)) :=
    (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))).symm
  rw [h1, h2, ← map_mul, ← map_mul]
  rfl

/-- The reflected block action on a unit vector of `S^L_α`, through the block diagram. -/
theorem rootReflectConj_rootBlockAction_single (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ)
    (hj : j < ℓ + 1) (hα : StendhalAlgebra.RootNonViolated (ν := ν) (blockRoot b))
    (a : KLRAlgebra k Q (b ⟨j, hj⟩)) (s s' : StendhalAlgebra.RootSeq (ν := ν) (blockRoot b)) :
    StendhalAlgebra.rootReflectConj Q Λ hα (StendhalAlgebra.rootBlockAction Q Λ hb j hj a)
      (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := ν) (blockRoot b) =>
        leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))
        s (leftStandardUnit Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s))) s' =
      stendhalTensorProjection (Q := Q) Λ ν
        (hflip (((StendhalAlgebra.blockEmb hb j hj).hom (stendhalQ Q Λ)
          (KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ) (b ⟨j, hj⟩) a)).val *
            e s.1)) • leftStandardUnit Q Λ s'.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s') := by
  rw [StendhalAlgebra.rootBlockAction_apply, StendhalAlgebra.rootReflectConj_rootAction_single,
    mk_blockHom_mul_e, tensorFlip_projection]

/-- Two elements acting on a unit vector agree when they agree after the idempotent. -/
theorem smul_leftStandardUnit_eq {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    {x x' : TensorProductAlgebra k Q Λ ν}
    (h : x * TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) =
      x' * TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)) :
    x • leftStandardUnit Q Λ s hs = x' • leftStandardUnit Q Λ s hs := by
  rw [leftStandardUnit, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext h

theorem smul_leftStandardUnit_eq_zero {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    {x : TensorProductAlgebra k Q Λ ν}
    (h : x * TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) = 0) :
    x • leftStandardUnit Q Λ s hs = 0 := by
  rw [← zero_smul (TensorProductAlgebra k Q Λ ν) (leftStandardUnit Q Λ s hs)]
  exact smul_leftStandardUnit_eq hs (h.trans (zero_mul _).symm)

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (b : Fin (ℓ + 2) → Multiset I)

local notation "θ" => initWeight b
local notation "β" => lastBlock b
local notation "α'" => blockRoot (initBlocks b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)
local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
local notation "S" => stendhalQ Q Λ
local notation "S'" => stendhalQ Q (Λ ∘ Fin.castSucc)
local notation "ρ" => redSubfamilyRelabel Q Λ Fin.castSucc (Fin.castSucc_injective ℓ)
  (initWeight b)
local notation "L'" => StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := initWeight b)
  (blockRoot (initBlocks b))
local notation "L" => StendhalAlgebra.LeftRootStandard Q Λ (ν := initWeight b + lastBlock b)
  (blockRoot b)
set_option quotPrecheck false in
local notation "V" => ParabolicStandardT Q Λ (initWeight b) (lastBlock b)
  (rootSplitInput Q Λ b).carrier hQ

/-- `f ⊠ id` on `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`, for an endomorphism `f` of `S^L_{α'}`. -/
def rootSplitLeftMap (f : Module.End Told L') :
    (rootSplitInput Q Λ b).carrier →ₗ[D] (rootSplitInput Q Λ b).carrier :=
  ExtTensor.map (k := k) (KMod.map (X := ModuleCat.of Told L') (Y := ModuleCat.of Told L') f)
    (KMod.map (X := ModuleCat.of Cyc Cyc) (Y := ModuleCat.of Cyc Cyc) LinearMap.id)

theorem redSubfamilyProjection_relabel' (z : KLRAlgebra k S' (stendhalWeight ℓ θ)) :
    redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ (relabelEquiv ρ z) =
      stendhalTensorProjection (Q := Q) (Λ ∘ Fin.castSucc) θ z := by
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

/-- `(Pr(W) [e(t')]) ⊠ e(u)` is the image of `W ⊗ 1` acting on the vector of `(t', u)`. -/
theorem rootSplit_tmul_smul (W : KLRAlgebra k S (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)))
    (q : RootPair b) :
    (show (rootSplitInput Q Λ b).carrier from ExtTensor.tmul (k := k)
      (P := KMod (k := k) (ModuleCat.of Told L')) (Q := KMod (k := k) (ModuleCat.of Cyc Cyc))
      (redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ W •
        Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
          leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) q.1
          (leftStandardUnit Q (Λ ∘ Fin.castSucc) q.1.1 (StendhalAlgebra.RootSeq.isRedOrdered _ q.1)))
      (CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β (e q.2))) =
      parabolicInputMap Q Λ θ β (W ⊗ₜ 1) • rootPairUnit Q Λ b q := by
  rw [parabolicInputMap, Algebra.TensorProduct.map_tmul, map_one]
  refine Eq.trans ?_ (ExtTensor.smul_tmul (k := k) (P := KMod (k := k) (ModuleCat.of Told L'))
    (Q := KMod (k := k) (ModuleCat.of Cyc Cyc)) _ _ _ _).symm
  rw [one_smul]
  rfl

section Prefix

variable {j : ℕ} (hj : j < ℓ + 1)
  (hα' : StendhalAlgebra.RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα : StendhalAlgebra.RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))

/-- The block action of `R(b_j)` on the left root standard module `S^L_{α'}` of the first `ℓ` red
strands. -/
abbrev initBlockAction (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) : Module.End Told L' :=
  StendhalAlgebra.rootReflectConj Q (Λ ∘ Fin.castSucc) hα'
    (StendhalAlgebra.rootBlockAction Q (Λ ∘ Fin.castSucc) (b := initBlocks b) rfl j hj a)

/-- The block action of `R(b_j)` on the left root standard module `S^L_α` of all `ℓ + 1` red
strands. -/
abbrev fullBlockAction (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) : Module.End Tν L :=
  StendhalAlgebra.rootReflectConj Q Λ hα
    (StendhalAlgebra.rootBlockAction Q Λ (b := b) (blockPrefix_last b) j (by omega) a)

/-- The block diagram of `a` on the block `b_j` of the first `ℓ` red strands. -/
abbrev initBlockDiagram (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) :
    KLRAlgebra k S' (stendhalWeight ℓ θ) :=
  ((StendhalAlgebra.blockEmb (b := initBlocks b) (ν := initWeight b) rfl j hj).hom S'
    (KLRAlgebra.reindexEquiv Sum.inl_injective S' (initBlocks b ⟨j, hj⟩) a)).val

theorem initBlockAction_single (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩))
    (t : StendhalAlgebra.RootSeq (ν := θ) α') :
    initBlockAction Q Λ b hj hα' a
      (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
        leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) t
        (leftStandardUnit Q (Λ ∘ Fin.castSucc) t.1 (StendhalAlgebra.RootSeq.isRedOrdered _ t))) =
      stendhalTensorProjection (Q := Q) (Λ ∘ Fin.castSucc) θ
          (hflip (initBlockDiagram Q Λ b hj a * e t.1)) •
        fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
          leftStandardUnit Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s) := by
  funext s
  rw [Pi.smul_apply]
  exact rootReflectConj_rootBlockAction_single (Λ := Λ ∘ Fin.castSucc) rfl j hj hα' a t s

/-- The element `W = flip(e(t) a)`, relabelled to the first input block of the parabolic
subalgebra. -/
abbrev initBlockWord (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩))
    (t : StendhalAlgebra.RootSeq (ν := θ) α') :
    KLRAlgebra k S (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)) :=
  relabelEquiv ρ (hflip (initBlockDiagram Q Λ b hj a * e t.1))

theorem rootSplitLeftMap_rootPairUnit (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩))
    (p : RootPair b) :
    rootSplitLeftMap Q Λ b (initBlockAction Q Λ b hj hα' a) (rootPairUnit Q Λ b p) =
      ∑ t' : StendhalAlgebra.RootSeq (ν := θ) α',
        parabolicInputMap Q Λ θ β (initBlockWord Q Λ b hj a p.1 ⊗ₜ 1) •
          rootPairUnit Q Λ b (t', p.2) := by
  have h1 : rootSplitLeftMap Q Λ b (initBlockAction Q Λ b hj hα' a) (rootPairUnit Q Λ b p) =
      (show (rootSplitInput Q Λ b).carrier from ExtTensor.tmul (k := k)
        (P := KMod (k := k) (ModuleCat.of Told L')) (Q := KMod (k := k) (ModuleCat.of Cyc Cyc))
        (initBlockAction Q Λ b hj hα' a
          (Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
            leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) p.1
            (leftStandardUnit Q (Λ ∘ Fin.castSucc) p.1.1
              (StendhalAlgebra.RootSeq.isRedOrdered _ p.1))))
        (CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
          (e p.2))) := rfl
  have hy : stendhalTensorProjection (Q := Q) (Λ ∘ Fin.castSucc) θ
      (hflip (initBlockDiagram Q Λ b hj a * e p.1.1)) =
      redSubfamilyProjection Q Λ Fin.castSucc (Fin.castSucc_injective ℓ) θ
        (initBlockWord Q Λ b hj a p.1) := (redSubfamilyProjection_relabel' Q Λ b _).symm
  have hF : (fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
      leftStandardUnit Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) =
      ∑ t' : StendhalAlgebra.RootSeq (ν := θ) α',
        Pi.single (M := fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
          leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) t'
          (leftStandardUnit Q (Λ ∘ Fin.castSucc) t'.1 (StendhalAlgebra.RootSeq.isRedOrdered _ t')) :=
    (Finset.univ_sum_single _).symm
  rw [h1, initBlockAction_single, hy, hF, Finset.smul_sum]
  refine (TensorProduct.sum_tmul _ _ _).trans (Finset.sum_congr rfl fun t' _ => ?_)
  exact rootSplit_tmul_smul Q Λ b (initBlockWord Q Λ b hj a p.1) (t', p.2)

/-- The block diagram of `a` on the block `b_j` of all `ℓ + 1` red strands. -/
abbrev fullBlockDiagram (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) :
    KLRAlgebra k S (stendhalWeight (ℓ + 1) (θ + β)) :=
  ((StendhalAlgebra.blockEmb (b := b) (blockPrefix_last b) j (by omega)).hom S
    (KLRAlgebra.reindexEquiv Sum.inl_injective S (b ⟨j, by omega⟩) a)).val

theorem prefixBlockMap_initBlockDiagram (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) :
    prefixBlockMap Q Λ θ β (initBlockDiagram Q Λ b hj a) = fullBlockDiagram Q Λ b hj a :=
  prefixBlockMap_blockEmb Q Λ b hj a

theorem fullBlockDiagram_mul_e (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩))
    (t t' : StendhalAlgebra.RootSeq (ν := θ) α') (u u' : Seq β) :
    stendhalTensorProjection (Q := Q) Λ (θ + β)
        (hflip (fullBlockDiagram Q Λ b hj a * e (twoPieceLoading θ β t.1 u))) *
      TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e (twoPieceLoading θ β t'.1 u')
        (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ t') u')) =
      if u = u' then
        stendhalTensorProjection (Q := Q) Λ (θ + β)
          (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)
            (concat S _ _ (relabelEquiv ρ (e t.1 * hflip (initBlockDiagram Q Λ b hj a) * e t'.1) ⊗ₜ
              e (Seq.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
                (SingleRed.insertWord β u)))))
      else 0 := by
  rw [← stendhalTensorProjection_e, ← map_mul, ← prefixBlockMap_initBlockDiagram, hflip_mul,
    hflip_e, hflip_prefixBlockMap, e_mul_prefixBlockMap_mul_e]
  split_ifs
  · rfl
  · exact map_zero _

theorem initBlockWord_mul_e (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩))
    (t t' : StendhalAlgebra.RootSeq (ν := θ) α') (u' : Seq β) :
    parabolicAffine Q Λ θ β (concat S _ _ (initBlockWord Q Λ b hj a t ⊗ₜ 1)) *
      TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e (twoPieceLoading θ β t'.1 u')
        (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ t') u')) =
      stendhalTensorProjection (Q := Q) Λ (θ + β)
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β)
          (concat S _ _ (relabelEquiv ρ (e t.1 * hflip (initBlockDiagram Q Λ b hj a) * e t'.1) ⊗ₜ
            e (Seq.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
              (SingleRed.insertWord β u'))))) := by
  rw [← stendhalTensorProjection_e]
  change stendhalTensorProjection (Q := Q) Λ (θ + β) (castKLR S _ _) * _ = _
  rw [← map_mul, concat_tmul_one_mul_e, hflip_mul, hflip_e]

theorem parabolicStandardTUnit_sum' {ι : Type*} (s : Finset ι)
    (f : ι → (rootSplitInput Q Λ b).carrier) :
    parabolicStandardTUnit Q Λ θ β hQ (∑ i ∈ s, f i) =
      (∑ i ∈ s, parabolicStandardTUnit Q Λ θ β hQ (f i) : V) :=
  map_sum (parabolicStandardUnit Q Λ θ β (rootSplitInput Q Λ b).carrier) f s

/-- **The isomorphism intertwines the block actions of the first `ℓ + 1` blocks**
(arXiv:1309.3796v3, Proposition 5.3 and proof of Proposition 5.5). -/
theorem twoPieceRootStandardEquiv_initBlock (a : KLRAlgebra k Q (initBlocks b ⟨j, hj⟩)) :
    (twoPieceRootStandardEquiv Q Λ hQ b).toLinearMap ∘ₗ
        parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (initBlockAction Q Λ b hj hα' a)) =
      fullBlockAction Q Λ b hj hα a ∘ₗ (twoPieceRootStandardEquiv Q Λ hQ b).toLinearMap := by
  refine parabolicStandardT_ext_span Q Λ θ β hQ (span_rootPairUnit Q Λ b) ?_
  rintro _ ⟨p, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hL : parabolicStandardMapT Q Λ hQ (rootSplitLeftMap Q Λ b (initBlockAction Q Λ b hj hα' a))
      (parabolicStandardTUnit Q Λ θ β hQ (rootPairUnit Q Λ b p)) =
      parabolicStandardTUnit Q Λ θ β hQ
        (rootSplitLeftMap Q Λ b (initBlockAction Q Λ b hj hα' a) (rootPairUnit Q Λ b p)) := rfl
  rw [hL, rootSplitLeftMap_rootPairUnit, parabolicStandardTUnit_sum']
  simp_rw [parabolicStandardTUnit_smul]
  rw [map_sum]
  simp_rw [map_smul, twoPieceRootStandardEquiv_unit]
  funext s'
  obtain ⟨q, rfl⟩ := (rootPairSeq_bijective b).2 s'
  rw [Finset.sum_apply]
  refine Eq.trans ?_ (rootReflectConj_rootBlockAction_single (blockPrefix_last b) j (by omega) hα a
    (rootPairSeq b p) (rootPairSeq b q)).symm
  obtain ⟨t', u'⟩ := q
  rw [Finset.sum_eq_single t']
  · rw [Pi.smul_apply]
    by_cases hu : p.2 = u'
    · subst hu
      rw [Pi.single_eq_same]
      refine smul_leftStandardUnit_eq _ ?_
      rw [initBlockWord_mul_e]
      exact (fullBlockDiagram_mul_e Q Λ b hj a p.1 t' p.2 p.2).trans
        (ite_eq_left_of_eq_true _ _ (eq_true rfl)) |>.symm
    · rw [Pi.single_eq_of_ne (fun h => hu (congrArg Prod.snd ((rootPairSeq_bijective b).1 h)).symm),
        smul_zero]
      refine (smul_leftStandardUnit_eq_zero _ ?_).symm
      exact (fullBlockDiagram_mul_e Q Λ b hj a p.1 t' p.2 u').trans
        (ite_eq_right_of_eq_false _ _ (eq_false hu))
  · intro t'' _ ht''
    rw [Pi.smul_apply, Pi.single_eq_of_ne
      (fun h => ht'' (congrArg Prod.fst ((rootPairSeq_bijective b).1 h)).symm), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ t') h

end Prefix

end Categorification.Stendhal
