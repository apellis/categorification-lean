/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Global
import Categorification.TwoRep.BlockSumCrossing
import Categorification.WeightedKLR.RedStrands.CyclotomicRedDotCrossing

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
abbrev redBlock {x y : X} (h : y + δ = x) (β : WeightBlocks RD (Λ + δ) y) :
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


section Crossings

variable (i : I) {x x₂ y y₂ : X} (hx : x + RD.iX i = x₂) (hy : y + RD.iX i = y₂)
  (h : y + δ = x) (h₂ : y₂ + δ = x₂)

omit [DecidableEq I] in
theorem blockSucc_redBlock (β : WeightBlocks RD (Λ + δ) y) :
    blockSucc RD Λ i hx (redBlock RD Λ δ h β) =
      redBlock RD Λ δ h₂ (blockSucc RD (Λ + δ) i hy β) :=
  Subtype.ext rfl

omit [DecidableEq I] in
/-- Each block of `Λ` below `redBlock δ'` comes from a block of `Λ + δ` below `δ'`. -/
theorem fibreMap_redBlock_bijective (δ' : WeightBlocks RD (Λ + δ) y₂) :
    Function.Bijective (fibreMap (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
      (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
      (d' := δ')) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun p => ?_⟩
  refine ⟨⟨⟨p.1.1, ?_⟩, Subtype.ext ?_⟩, Subtype.ext (Subtype.ext rfl)⟩
  · obtain ⟨⟨β, hβ⟩, -⟩ := p
    subst hβ
    simp only [blockWeight] at h ⊢
    rw [sub_add_eq_sub_sub, ← h]
    abel
  · exact (show {i} + p.1.1 = (redBlock RD Λ δ h₂ δ').1 from congrArg Subtype.val p.2)

/-- **The red/down quotient crossing on weight spaces** (Webster, arXiv:1309.3796v3, §4.6,
Theorem 4.25): the transformation `I^δ E_i ⟶ E_i I^δ` given on each block by the cyclotomic
quotient `cyclotomicRedDownQuotient`. -/
def globalRedDownQuotient :
    globalRedPullback.{u, v, w} Q hab RD Λ δ h ≫ globalE Q b RD (Λ + δ) i hy ⟶
      globalE Q a RD Λ i hx ≫ globalRedPullback Q hab RD Λ δ h₂ :=
  ObjectProperty.homMk (blockResCross (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))

variable (d : ℕ) (hi : b i = Polynomial.X ^ d * a i)

/-- **The red/down dot crossing on weight spaces** (Webster, arXiv:1309.3796v3, §4.6,
Theorem 4.25): the transformation `E_i I^δ ⟶ I^δ E_i` given on each block by
`cyclotomicRedDotCrossing`, for `b i = X ^ d * a i`. -/
def globalRedDotCrossing :
    globalE.{u, v, w} Q a RD Λ i hx ≫ globalRedPullback Q hab RD Λ δ h₂ ⟶
      globalRedPullback Q hab RD Λ δ h ≫ globalE Q b RD (Λ + δ) i hy :=
  ObjectProperty.homMk (blockResCrossRev (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    fun _ _ hβ => cyclotomicRedDotCrossing.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ) d hi)

/-- **Bigon on the higher-weight side** (Webster, arXiv:1309.3796v3, (4.2)): the quotient
crossing followed by the dot crossing is the `d`-th power of the dot on `E_i I^δ`, block by
block. -/
theorem globalRedDownQuotient_dotCrossing_app (N : weightSpace.{u, v, w} Q a RD Λ x)
    (δ' : WeightBlocks RD (Λ + δ) y₂) :
    (globalRedDownQuotient Q hab RD Λ δ i hx hy h h₂).hom.app N δ' ≫
        (globalRedDotCrossing Q hab RD Λ δ i hx hy h h₂ d hi).hom.app N δ' =
      (blockSumMap (blockSucc RD (Λ + δ) i hy) (fun _ _ hβ =>
        (End.of (dot.{u, v, w} Q b i (blockSucc_eq RD (Λ + δ) i hβ)) ^ d :
          End (ind Q b i (blockSucc_eq RD (Λ + δ) i hβ))))).app
        ((blockRes (redBlock RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h)).obj N) δ' :=
  blockResCross_blockResCrossRev_app (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => cyclotomicRedDotCrossing.{u, v, w} Q hab i
      (blockSucc_eq RD (Λ + δ) i hβ) d hi)
    (fun d' => (fibreMap_redBlock_bijective RD Λ δ i hx hy h h₂ d').1)
    (fun a' _ hβ => Functor.whiskerLeft (cyclotomicRedPullback.{u, v, w} Q hab a'.1)
      (End.of (dot.{u, v, w} Q b i (blockSucc_eq RD (Λ + δ) i hβ)) ^ d))
    (fun _ _ hβ => cyclotomicRedDownQuotient_dotCrossing.{u, v, w} Q hab i
      (blockSucc_eq RD (Λ + δ) i hβ) d hi) N δ'

/-- **Bigon on the lower-weight side** (Webster, arXiv:1309.3796v3, (4.2)): the dot crossing
followed by the quotient crossing is the `d`-th power of the dot on `I^δ E_i`, block by
block. -/
theorem globalRedDotCrossing_downQuotient_app (N : weightSpace.{u, v, w} Q a RD Λ x)
    (δ' : WeightBlocks RD (Λ + δ) y₂) :
    (globalRedDotCrossing Q hab RD Λ δ i hx hy h h₂ d hi).hom.app N δ' ≫
        (globalRedDownQuotient Q hab RD Λ δ i hx hy h h₂).hom.app N δ' =
      (cyclotomicRedPullback.{u, v, w} Q hab δ'.1).map
        ((blockSumMap (blockSucc RD Λ i hx) (fun _ _ hβ =>
          (End.of (dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ)) ^ d :
            End (ind Q a i (blockSucc_eq RD Λ i hβ))))).app N (redBlock RD Λ δ h₂ δ')) :=
  blockResCrossRev_blockResCross_app (blockSucc RD Λ i hx) (blockSucc RD (Λ + δ) i hy)
    (redBlock RD Λ δ h) (redBlock RD Λ δ h₂) (blockSucc_redBlock RD Λ δ i hx hy h h₂)
    (indBlock Q a RD Λ i hx) (indBlock Q b RD (Λ + δ) i hy)
    (redPullbackBlock Q hab RD Λ δ h) (redPullbackBlock Q hab RD Λ δ h₂)
    (fun _ _ hβ => cyclotomicRedDownQuotient.{u, v, w} Q hab i (blockSucc_eq RD (Λ + δ) i hβ))
    (fun _ _ hβ => cyclotomicRedDotCrossing.{u, v, w} Q hab i
      (blockSucc_eq RD (Λ + δ) i hβ) d hi)
    (fibreMap_redBlock_bijective RD Λ δ i hx hy h h₂)
    (fun _ _ hβ => (End.of (dot.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ)) ^ d :
      End (ind Q a i (blockSucc_eq RD Λ i hβ))))
    (fun _ _ hβ => cyclotomicRedDotCrossing_downQuotient.{u, v, w} Q hab i
      (blockSucc_eq RD (Λ + δ) i hβ) d hi) N δ'

end Crossings

end Categorification.Stendhal
