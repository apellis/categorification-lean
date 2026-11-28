/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveStdLayerFinite
import Categorification.WeightedKLR.Rigidity.SMoveRouquierRoute
import Categorification.WeightedKLR.Rigidity.SMoveTorAcyclicPi

/-!
# The off-diagonal pairs of the S-move resolutions

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). The two S-move modules are resolved through Proposition 7.8
(`exists_stdResolution`) on two red strands: the left module `L` over `T^{λ_2, λ_3}(ν)` by
terms `X_i`, sums of standard layers `S(M)` with `M` over the factor algebra of a split
`θ + β = ν` with `|β| = i`, and the right module `L'` over `T^{λ_1, λ_2}(ν)` by terms `Y_j`,
sums of standard layers `S(M')` with `|β'| = j`. The Tor of the S-move is computed from the
pairs `(SMove.leftStd X_i)^r`, `SMove.rightStd Y_j`. This file proves the vanishing of Tor for
every pair of summands off the diagonal `(i, j) = (0, |ν|)`:

* `i ≥ 1` (`SMove.torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne_zero`): by the three-block
  associativity (`SMove.leftStdCutLayerIso`, R1) the left summand is the standard layer of a
  split `(0 + θ) + β` at the last red strand; the right summand is the standard layer of the
  split `ν + 0` there (`SMove.rightStdLayerIso`, R2); since `β ≠ 0` the black counts at the
  last red strand differ, and `torAcyclic_reflect_stdLayer_of_ne_of_rouquier` applies.
* `i = 0`, `j < |ν|` (`SMove.torAcyclic_reflect_leftStd_rightStd_stdLayer_zero`): the pair is
  separated at the middle red strand (`θ' ≠ 0`), and
  `SMove.torAcyclic_reflect_leftStd_rightStd_of_ne_of_rouquier` applies.

The summand forms are then summed over the finite sums of the terms (`StdSum`), through
`TorAcyclic.map_pi` and `TorAcyclic.map_pi_coefficient`
(`SMove.torAcyclic_reflect_leftStd_rightStd_stdSum_of_ne`).

Hypotheses: a Rouquier choice of `Q` (`IsRouquierQ`; the route hypotheses `DC` and `hold` of
the underlying Tor lemmas are discharged by it, see `SMoveRouquierRoute`), and
finite-dimensional factor modules, as produced by Proposition 7.8. Tor is over `ℤ`, as in the
other Tor lemmas of the S-move.

## Main results

* `SMove.leftStdStdLayerIso`: `SMove.leftStd S(M) ≅ S(𝕊^{λ_1; λ_2}(P_∅ ⊠ M'))`.
* `SMove.torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne_zero`: the pairs with `i ≥ 1`.
* `SMove.torAcyclic_reflect_leftStd_rightStd_stdLayer_zero`: the pairs with `i = 0`, `j < |ν|`.
* `SMove.torAcyclic_reflect_leftStd_rightStd_stdSum_of_ne`: the same for the sums of the
  terms of the resolutions, for every `(i, j) ≠ (0, |ν|)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR ModuleFiltration Equiv BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped TensorProduct DG.DegreeZero

universe w

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ)

/-- **`SMove.leftStd` of a standard layer** (Webster, arXiv:1309.3796v3, §5.1; §7.3, proof of
Proposition 7.22): for a factor module `M` of the split `θ + β` at the last of the two red
strands `λ_2, λ_3`, `SMove.leftStd S(M)` is the standard layer, at the last of the three red
strands, of the factor module `𝕊^{λ_1; λ_2}(P_∅ ⊠ M')` of the split `(0 + θ) + β`, with `M'`
the cut restriction of `M`. -/
def leftStdStdLayerIso {θ β : Multiset I} (M : FactorModule Q (Λ ∘ Fin.natAdd 1) θ β) :
    (leftStd Q hQ Λ (θ + β)).obj (stdLayerModule Q (Λ ∘ Fin.natAdd 1) hQ ⟨θ, β, rfl, M⟩) ≅
      stdLayerModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ
        ⟨0 + θ, β, leftStdSplit θ β,
          parabolicOfCutModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
            (leftStdMidModule Q hQ Λ θ β (cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M))⟩ :=
  (leftStd Q hQ Λ (θ + β)).mapIso (stdLayerCutIso Q hQ (Λ ∘ Fin.natAdd 1) rfl M) ≪≫
    leftStdCutLayerIso Q hQ Λ θ β (cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M)

section Pairs

variable {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + 1 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)
  [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (ν := ν)
      (List.map (1 : Perm (Fin (1 + 1 + 1))) (List.finRange (1 + 1 + 1))))]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν)]
  [HasDerivedCategory.{w, 0} ℤ]

include hρ in
/-- **The S-move pairs with a black strand on the last red strand of the left term**
(Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, gap (c)): for Rouquier `Q`,
finite-dimensional factor modules `M` of a split `θ + β = ν` at `λ_3` (of `T^{λ_2, λ_3}`) with
`β ≠ 0` and `M'` of a split `θ' + β' = ν` at `λ_2` (of `T^{λ_1, λ_2}`),
`Tor_*^ℤ((SMove.leftStd S(M))^r, SMove.rightStd S(M')) = 0`. -/
theorem torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne_zero
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    {θ β θ' β' : Multiset I} (h : θ + β = ν) (hβ : β ≠ 0)
    (M : FactorModule Q (Λ ∘ Fin.natAdd 1) θ β) [FiniteDimensional k M.carrier]
    (h' : θ' + β' = ν)
    (M' : FactorModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) θ' β')
    [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
        ((leftStd Q hQ Λ ν).obj (stdLayerModule Q (Λ ∘ Fin.natAdd 1) hQ ⟨θ, β, h, M⟩)))
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
        (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
          ⟨θ', β', h', M'⟩)) := by
  subst h
  have hne : 0 + θ ≠ θ + β := fun he => by
    have hc := congrArg Multiset.card he
    rw [Multiset.card_add, Multiset.card_add, Multiset.card_zero, zero_add] at hc
    exact hβ (Multiset.card_eq_zero.mp (by omega))
  have := finiteDimensional_cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M
  have := finiteDimensional_leftStdMidFactor Q hQ hR Λ θ β
    (cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M)
  have := finiteDimensional_stdLayerModule Q
    ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ hR ⟨θ', β', h', M'⟩
  have := finiteDimensional_emptyRightFactor Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (θ + β)
    (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ ⟨θ', β', h', M'⟩)
  have hX := torAcyclic_reflect_stdLayer_of_ne_of_rouquier.{w} Q
    (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ hR (leftStdSplit θ β) (add_zero (θ + β)) hne
    (parabolicOfCutModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      (leftStdMidModule Q hQ Λ θ β (cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M)))
    (parabolicOfCutModule Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1))
      ((emptyRightTensor Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (θ + β)).obj
        (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
          ⟨θ', β', h', M'⟩)))
  refine TorAcyclic.of_iso _
    (rightStdLayerIso Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) (θ + β) _).symm ?_
  exact TorAcyclic.of_coefficient_iso _
    ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).mapIso
      (leftStdStdLayerIso Q hQ Λ M).symm) hX

include hρ in
/-- **The S-move pairs with no black strand on the last red strand of the left term, separated
at the middle red strand** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22,
gap (c)): for Rouquier `Q`, finite-dimensional factor modules `M` of a split `θ + 0 = ν` at
`λ_3` and `M'` of a split `θ' + β' = ν` at `λ_2` with `θ' ≠ 0`,
`Tor_*^ℤ((SMove.leftStd S(M))^r, SMove.rightStd S(M')) = 0`. -/
theorem torAcyclic_reflect_leftStd_rightStd_stdLayer_zero
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
    {θ θ' β' : Multiset I} (h : θ + 0 = ν)
    (M : FactorModule Q (Λ ∘ Fin.natAdd 1) θ 0) [FiniteDimensional k M.carrier]
    (h' : θ' + β' = ν) (hne : θ' ≠ 0)
    (M' : FactorModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) θ' β')
    [FiniteDimensional k M'.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
        ((leftStd Q hQ Λ ν).obj (stdLayerModule Q (Λ ∘ Fin.natAdd 1) hQ ⟨θ, 0, h, M⟩)))
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
        (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
          ⟨θ', β', h', M'⟩)) := by
  subst h
  have := finiteDimensional_cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M
  have hX := torAcyclic_reflect_leftStd_rightStd_of_ne_of_rouquier.{w} Q hQ Λ θ hρ hR
    (cutOfFactorModule Q (Λ ∘ Fin.natAdd 1) M) h' hne M'
  exact TorAcyclic.of_coefficient_iso _
    ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).mapIso
      ((leftStd Q hQ Λ (θ + 0)).mapIso
        (stdLayerCutIso Q hQ (Λ ∘ Fin.natAdd 1) rfl M)).symm) hX

include hρ in
/-- **The S-move pairs of standard layers off the diagonal** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c)): for Rouquier `Q` and finite-dimensional factor modules,
with `|β| = i` black strands on the last red strand of the left layer and `|θ'| = |ν| - j`
black strands left of the last red strand of the right layer, Tor vanishes unless
`(i, j) = (0, |ν|)`. The two cases are
`torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne_zero` and
`torAcyclic_reflect_leftStd_rightStd_stdLayer_zero`. -/
theorem torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) {i j : ℕ}
    (hij : i ≠ 0 ∨ j < Multiset.card ν) (c : StdLayer Q (Λ ∘ Fin.natAdd 1) ν)
    (hc : Multiset.card c.θ + 1 = Multiset.card ν + 1 - i)
    [FiniteDimensional k c.M.carrier]
    (c' : StdLayer Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν)
    (hc' : Multiset.card c'.θ + 1 = Multiset.card ν + 1 - j)
    [FiniteDimensional k c'.M.carrier] :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
        ((leftStd Q hQ Λ ν).obj (stdLayerModule Q (Λ ∘ Fin.natAdd 1) hQ c)))
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj
        (stdLayerModule Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ c')) := by
  obtain ⟨θ, β, h, M⟩ := c
  obtain ⟨θ', β', h', M'⟩ := c'
  have hν := congrArg Multiset.card h
  have hν' := congrArg Multiset.card h'
  rw [Multiset.card_add] at hν hν'
  dsimp only at hc hc' ‹FiniteDimensional k M.carrier› ‹FiniteDimensional k M'.carrier›
  by_cases hβ : β = 0
  · subst hβ
    refine torAcyclic_reflect_leftStd_rightStd_stdLayer_zero.{w} Q hQ Λ hρ hR h M h' ?_ M'
    rintro rfl
    simp only [Multiset.card_zero] at hν hc'
    omega
  · exact torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne_zero.{w} Q hQ Λ hρ hR h hβ M h' M'

include hρ in
/-- **The S-move pairs of resolution terms off the diagonal** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c)): for Rouquier `Q`, let `X` be a term `StdSum` at position
`|ν| + 1 - i` (the `i`-th term of the resolution of Proposition 7.8 over `T^{λ_2, λ_3}(ν)`) and
`Y` a term at position `|ν| + 1 - j` over `T^{λ_1, λ_2}(ν)`. If `(i, j) ≠ (0, |ν|)`, then
`Tor_*^ℤ((SMove.leftStd X)^r, SMove.rightStd Y) = 0`. -/
theorem torAcyclic_reflect_leftStd_rightStd_stdSum_of_ne
    {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) {i j : ℕ}
    (hij : i ≠ 0 ∨ j < Multiset.card ν)
    {X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)}
    (hX : StdSum Q (Λ ∘ Fin.natAdd 1) hQ (Multiset.card ν + 1 - i) X)
    {Y : ModuleCat.{0} (TensorProductAlgebra k Q
      ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) ν)}
    (hY : StdSum Q ((Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ∘ Fin.castSucc) hQ
      (Multiset.card ν + 1 - j) Y) :
    TorAcyclic.{w} (k := ℤ) ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).obj
        ((leftStd Q hQ Λ ν).obj X))
      ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).obj Y) := by
  obtain ⟨J, _, c, hc, hfd, ⟨e⟩⟩ := hX
  obtain ⟨J', _, c', hc', hfd', ⟨e'⟩⟩ := hY
  refine TorAcyclic.of_iso _
    ((rightStd Q hQ (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν).mapIso e').symm ?_
  refine TorAcyclic.of_coefficient_iso _
    ((reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ).mapIso
      ((leftStd Q hQ Λ ν).mapIso e)).symm ?_
  have hF : ModuleExactFunctor (leftStd Q hQ Λ ν ⋙
      reflectOne Q (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) hQ hρ) :=
    (moduleExactFunctor_leftStd Q hQ Λ ν).comp (ModuleExactFunctor.restrictScalars _)
  refine TorAcyclic.map_pi_coefficient _ hF _ fun a => ?_
  refine TorAcyclic.map_pi _ (moduleExactFunctor_rightStd Q hQ
    (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1)) ν) _ fun b => ?_
  have := hfd a
  have := hfd' b
  exact torAcyclic_reflect_leftStd_rightStd_stdLayer_of_ne.{w} Q hQ Λ hρ hR hij (c a) (hc a)
    (c' b) (hc' b)

end Pairs

end Categorification.Stendhal.SMove
