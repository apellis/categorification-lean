/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongLinear
import Categorification.KLR.CyclotomicAction.Restriction
import Categorification.QuantumGroup.UDotBlock
import Categorification.TwoRep.BlockSum

/-!
# The weight-indexed cyclotomic induction and restriction functors

Fix a root datum and `Λ ∈ X`. A block `R^Λ(β)-mod` has weight `Σ_{i ∈ β} i_X - Λ`, so that
appending a strand of colour `i` raises the weight by `i_X`. The weight space at `x` is the
product of the blocks of weight `x` (`weightSpace`, an object of `TwoRep.LinearCat k`).

`globalE i h : weightSpace x ⟶ weightSpace y`, for `h : x + i_X = y`, is cyclotomic induction
`F_i^Λ` assembled over blocks: its component at `δ` is the sum over the blocks `β` of weight `x`
with `{i} + β = δ` (at most one) of `ind Q a i`. `globalF i h` is restriction blockwise, and
`globalAdj i h : globalE i h ⊣ globalF i h` is assembled from the blockwise adjunctions
`indResAdj`. `globalDot` is the dot on each block. These are the 1-cells, adjunctions and dots of
the cyclotomic Rouquier family of KL III Thm. 1.2 (Kang–Kashiwara, arXiv:1102.4677v4, §4.2).
Ungraded; any commutative ring `k`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits TwoRep QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-! ### Linearity of cyclotomic induction and restriction -/

theorem lastEmb_scalarCompatible (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    InductionAlong.ScalarCompatible (k := k) (lastEmb Q a i h) := fun c => by
  change castCyc Q a h (KLRAlgebra.AbsentColour.cyclotomicLast Q i a β (algebraMap k _ c)) =
    algebraMap k _ c * castCyc Q a h (KLRAlgebra.AbsentColour.cyclotomicLast Q i a β 1)
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, Algebra.smul_def]

instance ind_linear (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (ind.{u, v, w} Q a i h).Linear k :=
  InductionAlong.functor_linear (lastEmb_scalarCompatible Q a i h)

instance res_linear (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    (res.{u, v, w} Q a i h).Linear k :=
  InductionAlong.resFunctor_linear (lastEmb_scalarCompatible Q a i h)

/-! ### Weights of blocks -/

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- The weight `Σ_{i ∈ β} i_X - Λ` of the block `R^Λ(β)-mod`. -/
def blockWeight (β : Multiset I) : X := (β.map RD.iX).sum - Λ

omit [DecidableEq I] in
theorem blockWeight_cons (i : I) (β : Multiset I) :
    blockWeight RD Λ ({i} + β) = blockWeight RD Λ β + RD.iX i := by
  simp only [blockWeight, Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton]
  abel

/-- The blocks of weight `x`. -/
abbrev WeightBlocks (x : X) : Type u := {β : Multiset I // blockWeight RD Λ β = x}

/-- Appending a strand of colour `i`. -/
def blockSucc (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ x) :
    WeightBlocks RD Λ y :=
  ⟨{i} + β.1, by rw [blockWeight_cons, β.2, h]⟩

omit [DecidableEq I] in
@[simp] theorem blockSucc_val (i : I) {x y : X} (h : x + RD.iX i = y)
    (β : WeightBlocks RD Λ x) : (blockSucc RD Λ i h β).1 = {i} + β.1 := rfl

omit [DecidableEq I] in
theorem blockSucc_eq (i : I) {x y : X} {h : x + RD.iX i = y} {β : WeightBlocks RD Λ x}
    {δ : WeightBlocks RD Λ y} (hβ : blockSucc RD Λ i h β = δ) : {i} + β.1 = δ.1 :=
  congrArg Subtype.val hβ

instance (i : I) {x y : X} (h : x + RD.iX i = y) (δ : WeightBlocks RD Λ y) :
    Subsingleton {β : WeightBlocks RD Λ x // blockSucc RD Λ i h β = δ} :=
  ⟨fun β β' => Subtype.ext (Subtype.ext (add_left_cancel
    ((congrArg Subtype.val β.2).trans (congrArg Subtype.val β'.2).symm)))⟩

/-! ### The weight spaces and the global functors -/

/-- **The weight space at `x`**: the product of the blocks `R^Λ(β)-mod` of weight `x`. -/
abbrev weightSpace (x : X) : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k :=
  LinearCat.of k (∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))

/-- The blocks of `globalE`: induction from `β` to `δ = {i} + β`. -/
abbrev indBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ x)
    (δ : WeightBlocks RD Λ y) (hβ : blockSucc RD Λ i h β = δ) :
    ModuleCat.{max (max u v) w} (CycKLR k Q a β.1) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q a δ.1) :=
  ind Q a i (blockSucc_eq RD Λ i hβ)

/-- The blocks of `globalF`: restriction from `δ = {i} + β` to `β`. -/
abbrev resBlock (i : I) {x y : X} (h : x + RD.iX i = y) (β : WeightBlocks RD Λ x)
    (δ : WeightBlocks RD Λ y) (hβ : blockSucc RD Λ i h β = δ) :
    ModuleCat.{max (max u v) w} (CycKLR k Q a δ.1) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q a β.1) :=
  res Q a i (blockSucc_eq RD Λ i hβ)

/-- **Cyclotomic induction `F_i^Λ` on weight spaces**, `x ⟶ x + i_X`. -/
def globalE (i : I) {x y : X} (h : x + RD.iX i = y) :
    weightSpace.{u, v, w} Q a RD Λ x ⟶ weightSpace Q a RD Λ y :=
  LinearCat.LinFun.of (blockSum (blockSucc RD Λ i h) (indBlock Q a RD Λ i h))

/-- **Cyclotomic restriction `E_i^Λ` on weight spaces**, `x + i_X ⟶ x`. -/
def globalF (i : I) {x y : X} (h : x + RD.iX i = y) :
    weightSpace.{u, v, w} Q a RD Λ y ⟶ weightSpace Q a RD Λ x :=
  LinearCat.LinFun.of (blockRes (blockSucc RD Λ i h) (resBlock Q a RD Λ i h))

/-- **The induction–restriction adjunction on weight spaces.** -/
def globalAdj (i : I) {x y : X} (h : x + RD.iX i = y) :
    Bicategory.Adjunction (globalE.{u, v, w} Q a RD Λ i h) (globalF Q a RD Λ i h) :=
  LinearCat.ofAdjunction k (blockAdjunction (blockSucc RD Λ i h)
    fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))

/-- **The dot on weight spaces**: the dot of `ind` on each block. -/
def globalDot (i : I) {x y : X} (h : x + RD.iX i = y) :
    globalE.{u, v, w} Q a RD Λ i h ⟶ globalE Q a RD Λ i h :=
  ObjectProperty.homMk (blockSumMap (blockSucc RD Λ i h)
    fun _ _ hβ => dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))

end

end Categorification.KLR.CyclotomicAction
