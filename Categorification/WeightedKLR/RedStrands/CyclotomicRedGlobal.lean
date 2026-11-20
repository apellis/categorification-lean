/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPullback

/-!
# Red pullback on the weight spaces of the cyclotomic action

Webster, arXiv:1309.3796v3, §4.6, Theorem 4.25. A red line with label `δ` acts on
the cyclotomic categorification by the functor `I^δ` of pullback along the quotient
`R^{Λ+δ} → R^Λ`. On the weight spaces of the cyclotomic family
(`CyclotomicAction.weightSpace`) a block `β` of weight `x` for `Λ` is the block of
weight `x - δ` for `Λ + δ`, so `I^δ` is block restriction along this identification
(`globalRedPullback`). It commutes with the global restriction functors `F_i`
(`globalRedPullbackResIso`): this is the red/up crossing of Theorem 4.25.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : UDot.WeightDatum C X Y) (Λ δ : X)

omit [DecidableEq I] in
/-- A block of weight `y` for `Λ + δ` is a block of weight `x` for `Λ` when `y + δ = x`. -/
def redBlock {x y : X} (h : y + δ = x) (β : WeightBlocks RD (Λ + δ) y) :
    WeightBlocks RD Λ x :=
  ⟨β.1, by
    obtain ⟨β, hβ⟩ := β
    subst h hβ
    simp only [blockWeight]
    abel⟩

omit [DecidableEq I] in
@[simp] theorem redBlock_val {x y : X} (h : y + δ = x) (β : WeightBlocks RD (Λ + δ) y) :
    (redBlock RD Λ δ h β).1 = β.1 := rfl

instance cyclotomicRedPullback_linear (β : Multiset I) :
    (cyclotomicRedPullback.{u, v, w} Q hab β).Linear k :=
  inferInstance

/-- The blocks of the red pullback. -/
abbrev redPullbackBlock {x y : X} (h : y + δ = x) (β : WeightBlocks RD (Λ + δ) y)
    (γ : WeightBlocks RD Λ x) (hγ : redBlock RD Λ δ h β = γ) :
    ModuleCat.{max (max u v) w} (CycKLR k Q a γ.1) ⥤
      ModuleCat.{max (max u v) w} (CycKLR k Q b β.1) := by
  subst hγ
  exact cyclotomicRedPullback.{u, v, w} Q hab β.1

instance redPullbackBlock_additive {x y : X} (h : y + δ = x)
    (β : WeightBlocks RD (Λ + δ) y) (γ : WeightBlocks RD Λ x) (hγ : redBlock RD Λ δ h β = γ) :
    (redPullbackBlock.{u, v, w} Q hab RD Λ δ h β γ hγ).Additive := by
  subst hγ
  exact inferInstanceAs (cyclotomicRedPullback.{u, v, w} Q hab β.1).Additive

instance redPullbackBlock_linear {x y : X} (h : y + δ = x)
    (β : WeightBlocks RD (Λ + δ) y) (γ : WeightBlocks RD Λ x) (hγ : redBlock RD Λ δ h β = γ) :
    (redPullbackBlock.{u, v, w} Q hab RD Λ δ h β γ hγ).Linear k := by
  subst hγ
  exact cyclotomicRedPullback_linear Q hab β.1

/-- **Red pullback on weight spaces** (Webster, arXiv:1309.3796v3, Theorem 4.25): the
functor `I^δ` from the weight-`x` space for `Λ` to the weight-`y` space for `Λ + δ`,
`y + δ = x`, restricting scalars along the cyclotomic quotient on each block. -/
def globalRedPullback {x y : X} (h : y + δ = x) :
    weightSpace.{u, v, w} Q a RD Λ x ⟶ weightSpace Q b RD (Λ + δ) y :=
  LinearCat.LinFun.of (blockRes (redBlock RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h))

/-- **Red pullback commutes with cyclotomic restriction on weight spaces** (Webster,
arXiv:1309.3796v3, §4.6, proof of Theorem 4.25, the red/up crossing): the functors `I^δ F_i`
and `F_i I^δ` agree, by the blockwise isomorphisms `cyclotomicRedPullbackResIso`. -/
def globalRedPullbackResIso (i : I) {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂)
    (hy : y + RD.iX i = y₂) (h : y + δ = x) (h₂ : y₂ + δ = x₂) :
    globalRedPullback.{u, v, w} Q hab RD Λ δ h₂ ≫ globalF Q b RD (Λ + δ) i hy ≅
      globalF Q a RD Λ i hx ≫ globalRedPullback Q hab RD Λ δ h :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun N => Pi.isoMk fun β =>
      (cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).app (N (redBlock RD Λ δ h₂
        (blockSucc RD (Λ + δ) i hy β))))
    (fun f => by
      funext β
      exact (cyclotomicRedPullbackResIso.{u, v, w} Q hab i rfl).hom.naturality _))

end Categorification.Stendhal
