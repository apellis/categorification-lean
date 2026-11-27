/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFunctor
import Categorification.WeightedKLR.RedStrands.LeftRootStandard
import Categorification.WeightedKLR.RedStrands.TwoPieceBlocks

/-!
# The root standard module of `ℓ + 1` red strands is a standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
proof of Proposition 5.5. Let `b` be a block decomposition for `ℓ + 1` red strands, `θ` the
black weight of its first `ℓ + 1` blocks, `β` that of its last block, and `α'`, `α` the root
functions of the first `ℓ + 1` blocks and of all blocks. Then the left root standard module
`S^L_α` is the standardization of `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)` (`twoPieceRootStandardEquiv`).

The proof decomposes `S^L_{α'} = ⊕_t S_t` and `R^{λ_{ℓ+1}}(β) = ⊕_u R^{λ_{ℓ+1}} e(u)`, uses that
standardization is additive (`ParabolicStandardFunctor`), identifies each summand
`S(S_t ⊠ R e(u))` with `S_{t λ_{ℓ+1} u}` (`twoPieceStandardEquiv`), and reindexes the sequences of
root function `α` by the pairs `(t, u)` (`mem_rootSet_blockRoot_iff`).

## Main definitions

* `parabolicStandardMapT`: the map of standardizations, as a map over `T^λ`.
* `rootSplitProj p`, `rootSplitIncl p`: the projection to and inclusion of the summand
  `S_t ⊠ R e(u)` of `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`, for `p = (t, u)`.
* `twoPieceRootStandardEquiv`: the isomorphism `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (b : Fin (ℓ + 2) → Multiset I)

section Map

variable {θ β : Multiset I} {N N' : Type*}
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']

/-- The map of standardizations `S(g)`, linear over `T^λ_{θ+β}`. -/
def parabolicStandardMapT (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    ParabolicStandardT Q Λ θ β N hQ →ₗ[TensorProductAlgebra k Q Λ (θ + β)]
      ParabolicStandardT Q Λ θ β N' hQ where
  toFun := parabolicStandardMap Q Λ θ β g
  map_add' := map_add _
  map_smul' t z := parabolicStandardMap_action Q Λ θ β hQ g t z

theorem parabolicStandardMapT_apply (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N')
    (z : ParabolicStandardT Q Λ θ β N hQ) :
    parabolicStandardMapT Q Λ hQ g z = parabolicStandardMap Q Λ θ β g z := rfl

variable {N'' : Type*} [AddCommGroup N''] [Module k N''] [Module (parabolicFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'']

theorem parabolicStandardMapT_id :
    parabolicStandardMapT Q Λ hQ (LinearMap.id : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N) =
      LinearMap.id :=
  LinearMap.ext fun x => LinearMap.congr_fun (parabolicStandardMap_id Q Λ θ β (N := N)) x

theorem parabolicStandardMapT_comp (g : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N')
    (g' : N' →ₗ[parabolicFactorAlgebra Q Λ θ β] N'') :
    parabolicStandardMapT Q Λ hQ (g'.comp g) =
      (parabolicStandardMapT Q Λ hQ g').comp (parabolicStandardMapT Q Λ hQ g) :=
  LinearMap.ext fun x => LinearMap.congr_fun (parabolicStandardMap_comp Q Λ θ β g g') x

theorem parabolicStandardMapT_zero :
    parabolicStandardMapT Q Λ hQ (0 : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') = 0 :=
  LinearMap.ext fun x => LinearMap.congr_fun (parabolicStandardMap_zero Q Λ θ β (N := N)) x

theorem parabolicStandardMapT_add (g g' : N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    parabolicStandardMapT Q Λ hQ (g + g') =
      parabolicStandardMapT Q Λ hQ g + parabolicStandardMapT Q Λ hQ g' :=
  LinearMap.ext fun x => LinearMap.congr_fun (parabolicStandardMap_add Q Λ θ β g g') x

theorem parabolicStandardMapT_sum {ι : Type*} (s : Finset ι)
    (g : ι → N →ₗ[parabolicFactorAlgebra Q Λ θ β] N') :
    parabolicStandardMapT Q Λ hQ (∑ i ∈ s, g i) =
      ∑ i ∈ s, parabolicStandardMapT Q Λ hQ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, parabolicStandardMapT_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, parabolicStandardMapT_add, ih]

end Map

local notation "aΛ" => fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i

section Cyc

variable {β : Multiset I}

/-- Right multiplication by `e(u)`, the projection `R^{λ_{ℓ+1}}(β) → R^{λ_{ℓ+1}} e(u)`. -/
def cycRightProj (u : Seq β) :
    CycKLR k Q (aΛ) β →ₗ[CycKLR k Q (aΛ) β] lIdeal (CycKLR.mk k Q (aΛ) β (e u)) where
  toFun c := ⟨c * CycKLR.mk k Q (aΛ) β (e u), by
    rw [mem_lIdeal, mul_assoc, (isIdempotentElem_cyc_e Q Λ β u).eq]⟩
  map_add' c c' := Subtype.ext (add_mul c c' _)
  map_smul' a c := Subtype.ext (mul_assoc a c _)

theorem coe_cycRightProj (u : Seq β) (c : CycKLR k Q (aΛ) β) :
    (cycRightProj Q Λ u c : CycKLR k Q (aΛ) β) = c * CycKLR.mk k Q (aΛ) β (e u) := rfl

theorem cycRightProj_subtype (u u' : Seq β) (c : lIdeal (CycKLR.mk k Q (aΛ) β (e u))) :
    (cycRightProj Q Λ u' (c : CycKLR k Q (aΛ) β) : CycKLR k Q (aΛ) β) =
      if u = u' then (c : CycKLR k Q (aΛ) β) else 0 := by
  rw [coe_cycRightProj, ← c.2, mul_assoc, ← map_mul, e_mul_e]
  split_ifs <;> simp

theorem sum_cycRightProj (c : CycKLR k Q (aΛ) β) :
    ∑ u : Seq β, (cycRightProj Q Λ u c : CycKLR k Q (aΛ) β) = c := by
  simp only [coe_cycRightProj, ← Finset.mul_sum, ← map_sum, sum_e, map_one, mul_one]

end Cyc


/-- Maps out of `X ⊠ Y` agree when they agree on the pure tensors. -/
theorem tensorFactor_linearMap_ext {θ β : Multiset I}
    {X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)}
    {Y : ModuleCat.{0} (CycKLR k Q (aΛ) β)} {Z : Type*} [AddCommGroup Z]
    [Module (parabolicFactorAlgebra Q Λ θ β) Z]
    {f g : (tensorFactor Q Λ X Y).carrier →ₗ[parabolicFactorAlgebra Q Λ θ β] Z}
    (h : ∀ (m : KMod (k := k) X) (c : KMod (k := k) Y),
      f (show (tensorFactor Q Λ X Y).carrier from ExtTensor.tmul m c) =
        g (show (tensorFactor Q Λ X Y).carrier from ExtTensor.tmul m c)) : f = g := by
  apply LinearMap.ext
  intro x
  refine ExtTensor.induction_on (k := k) (P := KMod (k := k) X) (Q := KMod (k := k) Y)
    (motive := fun x => f x = g x) x ?_ h ?_
  · exact (map_zero f).trans (map_zero g).symm
  · intro x y hx hy
    exact ((map_add f x y).trans (congrArg₂ (· + ·) hx hy)).trans (map_add g x y).symm

section Split

local notation "θ" => initWeight b
local notation "β" => lastBlock b
local notation "α'" => blockRoot (initBlocks b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "Cyc" => CycKLR k Q (aΛ) (lastBlock b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)

/-- The input module `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)` of standardization. -/
abbrev rootSplitInput : FactorModule Q Λ θ β :=
  tensorFactor Q Λ (ModuleCat.of Told (StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := θ) α'))
    (ModuleCat.of Cyc Cyc)

/-- The pairs `(t, u)` of a sequence `t` of root function `α'` and a black word `u` of the last
block. -/
abbrev RootPair : Type := StendhalAlgebra.RootSeq (ν := initWeight b) (blockRoot (initBlocks b)) × Seq (lastBlock b)

/-- The summand `S_t ⊠ R^{λ_{ℓ+1}} e(u)` for `p = (t, u)`. -/
abbrev rootPairInput (p : RootPair b) : FactorModule Q Λ θ β :=
  tensorFactor Q Λ (ModuleCat.of Told
    (leftStandard Q (Λ ∘ Fin.castSucc) p.1.1 (StendhalAlgebra.RootSeq.isRedOrdered _ p.1))) (cycProj Q Λ β p.2)

/-- The projection `S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β) → S_t ⊠ R^{λ_{ℓ+1}} e(u)`. -/
def rootSplitProj (p : RootPair b) :
    (rootSplitInput Q Λ b).carrier →ₗ[D] (rootPairInput Q Λ b p).carrier :=
  ExtTensor.map (k := k)
    (KMod.map (X := ModuleCat.of Told (StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := θ) α'))
      (Y := ModuleCat.of Told
        (leftStandard Q (Λ ∘ Fin.castSucc) p.1.1 (StendhalAlgebra.RootSeq.isRedOrdered _ p.1)))
      (LinearMap.proj p.1))
    (KMod.map (X := ModuleCat.of Cyc Cyc) (Y := cycProj Q Λ β p.2) (cycRightProj Q Λ p.2))

/-- The inclusion `S_t ⊠ R^{λ_{ℓ+1}} e(u) → S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)`. -/
def rootSplitIncl (p : RootPair b) :
    (rootPairInput Q Λ b p).carrier →ₗ[D] (rootSplitInput Q Λ b).carrier :=
  ExtTensor.map (k := k)
    (KMod.map (Y := ModuleCat.of Told (StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := θ) α'))
      (X := ModuleCat.of Told
        (leftStandard Q (Λ ∘ Fin.castSucc) p.1.1 (StendhalAlgebra.RootSeq.isRedOrdered _ p.1)))
      (LinearMap.single Told (fun s : StendhalAlgebra.RootSeq (ν := θ) α' =>
        leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) p.1))
    (KMod.map (Y := ModuleCat.of Cyc Cyc) (X := cycProj Q Λ β p.2)
      (lIdeal (CycKLR.mk k Q (aΛ) β (e p.2))).subtype)

set_option quotPrecheck false in
local notation "Mt" => fun s : StendhalAlgebra.RootSeq (ν := initWeight b) (blockRoot (initBlocks b)) =>
  leftStandard Q (Λ ∘ Fin.castSucc) s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)

theorem rootSplitProj_incl (p : RootPair b) :
    (rootSplitProj Q Λ b p).comp (rootSplitIncl Q Λ b p) = LinearMap.id := by
  refine tensorFactor_linearMap_ext Q Λ fun m c => ?_
  refine congrArg₂ ExtTensor.tmul (Pi.single_eq_same (M := Mt) p.1 m) ?_
  exact Subtype.ext ((cycRightProj_subtype Q Λ p.2 p.2 c).trans (ite_eq_left_of_eq_true _ _ (eq_true rfl)))

theorem rootSplitProj_incl_of_ne {p q : RootPair b} (h : p ≠ q) :
    (rootSplitProj Q Λ b q).comp (rootSplitIncl Q Λ b p) = 0 := by
  refine tensorFactor_linearMap_ext Q Λ fun m c => ?_
  rw [LinearMap.zero_apply]
  let c' : lIdeal (CycKLR.mk k Q (aΛ) β (e p.2)) := c
  have e1 : ((rootSplitProj Q Λ b q).comp (rootSplitIncl Q Λ b p))
      (show (rootPairInput Q Λ b p).carrier from ExtTensor.tmul m c) =
      ExtTensor.tmul (k := k)
        (P := KMod (k := k) (ModuleCat.of Told (leftStandard Q (Λ ∘ Fin.castSucc) q.1.1
          (StendhalAlgebra.RootSeq.isRedOrdered _ q.1))))
        (Q := KMod (k := k) (cycProj Q Λ β q.2))
        (Pi.single (M := Mt) p.1 (show Mt p.1 from m) q.1) (cycRightProj Q Λ q.2 (c' : Cyc)) :=
    rfl
  rw [e1]
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => h (Prod.ext h1 h2)
    have : cycRightProj Q Λ q.2 (c' : Cyc) = 0 :=
      Subtype.ext ((cycRightProj_subtype Q Λ p.2 q.2 c').trans
        (ite_eq_right_of_eq_false _ _ (eq_false h2)))
    rw [this]
    exact ExtTensor.tmul_zero _
  · rw [Pi.single_eq_of_ne' h1]
    exact ExtTensor.zero_tmul _

theorem sum_rootSplitIncl_proj :
    ∑ p : RootPair b, (rootSplitIncl Q Λ b p).comp (rootSplitProj Q Λ b p) = LinearMap.id := by
  refine tensorFactor_linearMap_ext Q Λ fun m c => ?_
  rw [LinearMap.sum_apply, Fintype.sum_prod_type, LinearMap.id_apply]
  let m' : (s : StendhalAlgebra.RootSeq (ν := θ) α') → Mt s := m
  let c' : Cyc := c
  have hc : ∑ u : Seq β, (cycRightProj Q Λ u c' : Cyc) = c' := sum_cycRightProj Q Λ c'
  have hm : ∑ t, Pi.single (M := Mt) t (m' t) = m' := Finset.univ_sum_single m'
  have e1 : ∀ t u, ((rootSplitIncl Q Λ b (t, u)).comp (rootSplitProj Q Λ b (t, u)))
      (show (rootSplitInput Q Λ b).carrier from ExtTensor.tmul m c) =
      ExtTensor.tmul (k := k)
        (P := KMod (k := k) (ModuleCat.of Told
          (StendhalAlgebra.LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := θ) α')))
        (Q := KMod (k := k) (ModuleCat.of Cyc Cyc))
        (Pi.single (M := Mt) t (m' t)) (cycRightProj Q Λ u c' : Cyc) := fun _ _ => rfl
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => e1 t u]
  exact (Finset.sum_congr rfl fun t _ => (TensorProduct.tmul_sum _ _ _).symm).trans
    ((TensorProduct.sum_tmul _ _ _).symm.trans (congrArg₂ (TensorProduct.tmul k) hm hc))

local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
set_option quotPrecheck false in
local notation "V" => ParabolicStandardT Q Λ (initWeight b) (lastBlock b)
  (rootSplitInput Q Λ b).carrier hQ

/-- The standard module `S_{t λ_{ℓ+1} u}` of the two-piece loading of `p = (t, u)`. -/
abbrev rootPairStandard (p : RootPair b) : Type :=
  leftStandard Q Λ (twoPieceLoading θ β p.1.1 p.2)
    (isRedOrdered_twoPieceLoading (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2)

/-- The component `S(S^L_{α'} ⊠ R(β)) → S(S_t ⊠ R e(u)) ≅ S_{t λ_{ℓ+1} u}`. -/
def rootPairComponent (p : RootPair b) : V →ₗ[Tν] rootPairStandard Q Λ b p :=
  (twoPieceStandardEquiv Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2 hQ).toLinearMap ∘ₗ
    parabolicStandardMapT Q Λ hQ (rootSplitProj Q Λ b p)

/-- The sum of the inclusions `S_{t λ_{ℓ+1} u} ≅ S(S_t ⊠ R e(u)) → S(S^L_{α'} ⊠ R(β))`. -/
def rootPairSum : ((p : RootPair b) → rootPairStandard Q Λ b p) →ₗ[Tν] V :=
  ∑ p : RootPair b, parabolicStandardMapT Q Λ hQ (rootSplitIncl Q Λ b p) ∘ₗ
    (twoPieceStandardEquiv Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2 hQ).symm.toLinearMap
      ∘ₗ LinearMap.proj p

theorem stdT_proj_incl (q : RootPair b) :
    parabolicStandardMapT Q Λ hQ (rootSplitProj Q Λ b q) ∘ₗ
      parabolicStandardMapT Q Λ hQ (rootSplitIncl Q Λ b q) = LinearMap.id := by
  rw [← parabolicStandardMapT_comp, rootSplitProj_incl]
  exact parabolicStandardMapT_id Q Λ hQ

theorem stdT_proj_incl_of_ne {p q : RootPair b} (h : p ≠ q) :
    parabolicStandardMapT Q Λ hQ (rootSplitProj Q Λ b q) ∘ₗ
      parabolicStandardMapT Q Λ hQ (rootSplitIncl Q Λ b p) = 0 := by
  rw [← parabolicStandardMapT_comp, rootSplitProj_incl_of_ne Q Λ b h]
  exact parabolicStandardMapT_zero Q Λ hQ

theorem stdT_sum_incl_proj :
    ∑ p : RootPair b, parabolicStandardMapT Q Λ hQ (rootSplitIncl Q Λ b p) ∘ₗ
      parabolicStandardMapT Q Λ hQ (rootSplitProj Q Λ b p) = LinearMap.id := by
  simp_rw [← parabolicStandardMapT_comp]
  rw [← parabolicStandardMapT_sum, sum_rootSplitIncl_proj]
  exact parabolicStandardMapT_id Q Λ hQ

theorem rootPairComponent_rootPairSum (w : (p : RootPair b) → rootPairStandard Q Λ b p)
    (q : RootPair b) : rootPairComponent Q Λ hQ b q (rootPairSum Q Λ hQ b w) = w q := by
  simp only [rootPairSum, rootPairComponent, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_eq_single q]
  · have h := LinearMap.congr_fun (stdT_proj_incl Q Λ hQ b q) ((twoPieceStandardEquiv Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ q.1) q.2 hQ).symm (w q))
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [h, LinearEquiv.apply_symm_apply]
  · intro p _ hp
    have h := LinearMap.congr_fun (stdT_proj_incl_of_ne Q Λ hQ b hp) ((twoPieceStandardEquiv Q Λ (StendhalAlgebra.RootSeq.isRedOrdered _ p.1) p.2 hQ).symm (w p))
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h
    rw [h]
    exact LinearEquiv.map_zero _
  · intro h
    exact absurd (Finset.mem_univ q) h

theorem rootPairSum_component (x : V) :
    rootPairSum Q Λ hQ b (fun p => rootPairComponent Q Λ hQ b p x) = x := by
  simp only [rootPairSum, rootPairComponent, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun (stdT_sum_incl_proj Q Λ hQ b) x
  rw [LinearMap.sum_apply, LinearMap.id_apply] at h
  simpa only [LinearMap.comp_apply] using h

/-- `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ ∏_{(t, u)} S_{t λ_{ℓ+1} u}`. -/
def rootPairEquivPi : V ≃ₗ[Tν] ((p : RootPair b) → rootPairStandard Q Λ b p) :=
  LinearEquiv.ofLinearMap (LinearMap.pi fun p => rootPairComponent Q Λ hQ b p) (rootPairSum Q Λ hQ b)
    (LinearMap.ext fun w => funext fun q => rootPairComponent_rootPairSum Q Λ hQ b w q)
    (LinearMap.ext fun x => rootPairSum_component Q Λ hQ b x)

/-- The two-piece loading of a pair, as a sequence of root function `α`. -/
def rootPairSeq (p : RootPair b) :
    StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b) (blockRoot b) :=
  ⟨twoPieceLoading θ β p.1.1 p.2, twoPieceLoading_mem_rootSet b p.1.2 p.2⟩

theorem rootPairSeq_bijective : Function.Bijective (rootPairSeq b) := by
  refine ⟨fun p q h => ?_, fun s => ?_⟩
  · have h' := twoPieceLoading_injective θ β (a₁ := (p.1.1, p.2)) (a₂ := (q.1.1, q.2))
      (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (congrArg Prod.snd h' :)
  · obtain ⟨t, ht, u, hs⟩ := (mem_rootSet_blockRoot_iff b s.1).1 s.2
    exact ⟨(⟨t, ht⟩, u), Subtype.ext hs⟩

/-- The pairs `(t, u)` are the sequences of root function `α`. -/
def rootPairSeqEquiv :
    RootPair b ≃ StendhalAlgebra.RootSeq (ν := initWeight b + lastBlock b) (blockRoot b) :=
  Equiv.ofBijective _ (rootPairSeq_bijective b)

/-- **The root standard module is a standardization** (arXiv:1309.3796v3, proof of
Proposition 5.5): `S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` as left `T^λ`-modules. -/
def twoPieceRootStandardEquiv :
    V ≃ₗ[Tν] StendhalAlgebra.LeftRootStandard Q Λ (ν := initWeight b + lastBlock b) (blockRoot b) :=
  (rootPairEquivPi Q Λ hQ b).trans
    (LinearEquiv.piCongrLeft Tν (fun s : StendhalAlgebra.RootSeq
      (ν := initWeight b + lastBlock b) (blockRoot b) =>
        leftStandard Q Λ s.1 (StendhalAlgebra.RootSeq.isRedOrdered _ s)) (rootPairSeqEquiv b))

end Split

end Categorification.Stendhal
