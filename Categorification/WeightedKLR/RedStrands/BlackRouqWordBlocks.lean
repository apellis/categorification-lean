/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackVacuumBlockFunctor

set_option backward.isDefEq.respectTransparency false

/-!
# One upward strand of the derived action, block by block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31:
on the weight spaces of the derived categories `D(T^λ_β)`, the 1-morphism `F_i` acts by derived
induction `D(T^λ_β) → D(T^λ_{{i} + β})` on each block (`blackRouqE`, a block sum over the blocks
`β` with `{i} + β = δ`). Since adding a strand is injective on blocks, the block `δ = {i} + β`
of `F_i M` is the derived induction of the block `β` of `M`:

* `blockSuccFibreUnique`: the blocks below `δ` form a one-element type;
* `blackRouqEBlockIso`: `(F_i M)_δ ≅ F_i (M_β)` for `blackRouqE`;
* `blackPresCLMapUpBlockIso`: the same for the derived action `blackPresCL` of a 1-morphism
  whose word is a single upward letter `F_i`.

This is the step of the computation of `F_𝐢 C₀` (the input `W` of
`SingleRed.blackVacuumDerivedTensorIsoId`) that adds one strand.
-/

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR TwoRep QuantumGroup KL3.Diagram CyclotomicAction
  DoubleDiagram StringDiagrams
open scoped Classical ZeroObject

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w u₁

noncomputable section

section Blocks

variable {I : Type u} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ₀ : X)

/-- **The blocks below `δ = {i} + β` form a one-element type**: adding a strand of colour `i`
is injective on blocks. -/
@[instance_reducible]
def blockSuccFibreUnique (i : I) {x y : X} (h : x + RD.iX i = y) {β : WeightBlocks RD Λ₀ x}
    {δ : WeightBlocks RD Λ₀ y} (hβ : blockSucc RD Λ₀ i h β = δ) :
    Unique {a : WeightBlocks RD Λ₀ x // blockSucc RD Λ₀ i h a = δ} where
  default := ⟨β, hβ⟩
  uniq a := Subtype.ext (Subtype.ext (add_left_cancel
    (show ({i} : Multiset I) + a.1.1 = {i} + β.1 from congrArg Subtype.val (a.2.trans hβ.symm))))

end Blocks

variable {I : Type u} {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {hQ : IsRouquierQ C Q}
  [∀ β : Multiset I,
    _root_.HasDerivedCategory.{u} (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)]
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] {RD : UDot.WeightDatum C X Y} {Λ₀ : X}

set_option hygiene false in
local notation "D" β => _root_.DerivedCategory (ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ)

variable (Λ hQ RD Λ₀) in
/-- **The block `δ = {i} + β` of `F_i M`** is the derived induction of the block `β` of `M`
(Webster, arXiv:1309.3796v3, Theorem 4.31, `blackRouqE`). -/
def blackRouqEBlockIso (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ₀ x, D β.1) {β : WeightBlocks RD Λ₀ x}
    {δ : WeightBlocks RD Λ₀ y} (hβ : blockSucc RD Λ₀ i h β = δ) :
    (blackRouqE Λ hQ RD Λ₀ i h).obj.obj M δ ≅
      (derivedFOfEq Λ hQ i (blockSucc_eq RD Λ₀ i hβ)).obj (M β) :=
  letI := blockSuccFibreUnique RD Λ₀ i h hβ
  biproductUniqueIso
    (fun p : {a : WeightBlocks RD Λ₀ x // blockSucc RD Λ₀ i h a = δ} =>
      (derivedFBlock Λ hQ RD Λ₀ i h p.1 δ p.2).obj (M p.1))

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (hΛ₀ : ∀ i, RD.pair (RD.iY i) Λ₀ = ∑ r : Fin ℓ, (Λ r i : ℤ))
  (hsym : KLRSymm Q)

/-- **One upward strand of the derived action at one block**: for a 1-morphism whose word is the
single letter `F_i`, the block `δ = {i} + β` of its action on `M` is the derived induction of the
block `β` of `M` (Webster, arXiv:1309.3796v3, Theorem 4.31). -/
def blackPresCLMapUpBlockIso
    {a b : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat} (x : a ⟶ b) (i : I) (r : X)
    (hx : (LinearCat.revHom x).obj.word = [⟨(true, i), r⟩])
    (M : ((blackPresCL hP hwf hΛ₀ hsym).obj a).carrier) (β : WeightBlocks RD Λ₀ a.as.region)
    (δ : WeightBlocks RD Λ₀ b.as.region) (hβ : ({i} : Multiset I) + β.1 = δ.1) :
    (blackBlockEval hP hwf hΛ₀ hsym b δ).obj (((blackPresCL hP hwf hΛ₀ hsym).map x).obj.obj M) ≅
      (derivedFOfEq Λ hQ i hβ).obj ((blackBlockEval hP hwf hΛ₀ hsym a β).obj M) := by
  obtain ⟨⟨ra⟩⟩ := a
  obtain ⟨⟨rb⟩⟩ := b
  obtain ⟨⟨st, w'⟩, h1, h2, h3⟩ := x
  change w' = _ at hx
  subst hx
  exact blackRouqEBlockIso Λ hQ RD Λ₀ i _ M (Subtype.ext hβ)

end

end Categorification.Stendhal
