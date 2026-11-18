/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPullback
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The downward quotient crossing in the cyclotomic action

In Webster, arXiv:1309.3796v2, Theorem 4.25, p. 41, the crossing
`Fᵢ Iλ ⟶ Iλ Fᵢ` is the natural cyclotomic quotient. Bending the black
strand identifies it with the inverse restriction isomorphism (4.5).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra CyclotomicAction CategoryTheory Polynomial InductionAlong

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]}
  (hab : ∀ i, a i ∣ b i) (i : I) {β γ : Multiset I} (h : {i} + β = γ)

private def restrictionSquare :
    TwoSquare (res Q a i h) (cyclotomicRedPullback.{u,v,w} Q hab γ)
      (cyclotomicRedPullback Q hab β) (res Q b i h) :=
  .mk _ _ _ _ (cyclotomicRedPullbackResIso Q hab i h).inv

/-- Crossing a downward black strand past red by taking the cyclotomic quotient
is the left mate of the inverse restriction square. -/
def cyclotomicRedDownQuotient :
    cyclotomicRedPullback.{u,v,w} Q hab β ⋙ ind Q b i h ⟶
      ind Q a i h ⋙ cyclotomicRedPullback Q hab γ :=
  ((mateEquiv (indResAdj Q a i h) (indResAdj Q b i h)).symm
    (restrictionSquare Q hab i h)).natTrans

/-- Taking the right mate recovers the upward restriction crossing oriented
from restriction followed by red pullback to red pullback followed by restriction. -/
theorem cyclotomicRedDownQuotient_mate :
    (mateEquiv (indResAdj Q a i h) (indResAdj Q b i h)
      (.mk _ _ _ _ (cyclotomicRedDownQuotient.{u,v,w} Q hab i h))).natTrans =
        (cyclotomicRedPullbackResIso Q hab i h).inv :=
  congrArg TwoSquare.natTrans ((mateEquiv (indResAdj Q a i h) (indResAdj Q b i h)).apply_symm_apply
    (restrictionSquare Q hab i h))

/-- Sliding the quotient crossing through the unit bend. -/
theorem cyclotomicRedDownQuotient_unit (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    (cyclotomicRedPullback Q hab β).map ((indResAdj Q a i h).unit.app M) ≫
        (cyclotomicRedPullbackResIso Q hab i h).inv.app ((ind Q a i h).obj M) =
      (indResAdj Q b i h).unit.app ((cyclotomicRedPullback Q hab β).obj M) ≫
        (res Q b i h).map ((cyclotomicRedDownQuotient Q hab i h).app M) :=
  unit_mateEquiv_symm (indResAdj Q a i h) (indResAdj Q b i h) (restrictionSquare Q hab i h) M

/-- Sliding the quotient crossing through the counit bend. -/
theorem cyclotomicRedDownQuotient_counit (M : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    (ind Q b i h).map ((cyclotomicRedPullbackResIso Q hab i h).inv.app M) ≫
        (indResAdj Q b i h).counit.app ((cyclotomicRedPullback Q hab γ).obj M) =
      (cyclotomicRedDownQuotient Q hab i h).app ((res Q a i h).obj M) ≫
        (cyclotomicRedPullback Q hab γ).map ((indResAdj Q a i h).counit.app M) :=
  mateEquiv_counit_symm (indResAdj Q a i h) (indResAdj Q b i h) (restrictionSquare Q hab i h) M

/-- Apply the cyclotomic quotient to the algebra factor of the induction bimodule. -/
def cyclotomicRedCornerProjection (z : Corner (lastEmb Q b i h)) : Corner (lastEmb Q a i h) :=
  ⟨cyclotomicRedProjection Q hab γ z.val, by
    have he : cyclotomicRedProjection Q hab γ (lastEmb Q b i h 1) = lastEmb Q a i h 1 := by
      rw [cyclotomicRedProjection_lastEmb, map_one]
    change cyclotomicRedProjection Q hab γ z.val * lastEmb Q a i h 1 = _
    rw [← he, ← map_mul]
    exact congrArg (cyclotomicRedProjection Q hab γ) z.prop⟩

set_option backward.isDefEq.respectTransparency false in
/-- The crossing sends a simple tensor `z ⊗ n` to `π(z) ⊗ n`. -/
theorem cyclotomicRedDownQuotient_tmul (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (z : Corner (lastEmb Q b i h)) (n : M) :
    ((cyclotomicRedDownQuotient Q hab i h).app M)
        (Ind.tmul (N := (cyclotomicRedPullback Q hab β).obj M) z n) =
      Ind.tmul (N := M) (cyclotomicRedCornerProjection Q hab i h z) n := by
  have hu := cyclotomicRedDownQuotient_unit Q hab i h M
  have hgen : ((cyclotomicRedDownQuotient Q hab i h).app M)
      (Ind.tmul (N := (cyclotomicRedPullback Q hab β).obj M) (unitGen (lastEmb Q b i h)) n) =
      Ind.tmul (N := M) (unitGen (lastEmb Q a i h)) n := by
    exact congrArg (fun f => Res.val (M := (cyclotomicRedPullback Q hab γ).obj ((ind Q a i h).obj M))
      (φ := lastEmb Q b i h) (f.hom n)) hu.symm
  have hz : z.val • unitGen (lastEmb Q b i h) = z := Subtype.ext z.prop
  rw [← hz, ← Ind.smul_tmul, map_smul, hgen]
  change cyclotomicRedProjection Q hab γ z.val • Ind.tmul (unitGen (lastEmb Q a i h)) n = _
  rw [Ind.smul_tmul, hz]
  exact congrArg (Ind.tmul · n) (Subtype.ext (cyclotomicRedCornerProjection Q hab i h z).prop)

/-- The quotient on induction bimodules is onto. A lift in the larger algebra
can be multiplied by the last-strand idempotent to lift into the required corner. -/
theorem cyclotomicRedCornerProjection_surjective :
    Function.Surjective (cyclotomicRedCornerProjection Q hab i h) := by
  intro z
  obtain ⟨y, hy⟩ := cyclotomicRedProjection_surjective Q hab γ z.val
  refine ⟨y • unitGen (lastEmb Q b i h), Subtype.ext ?_⟩
  change cyclotomicRedProjection Q hab γ (y * lastEmb Q b i h 1) = z.val
  simp only [map_mul, hy, cyclotomicRedProjection_lastEmb, map_one]
  exact z.prop

set_option backward.isDefEq.respectTransparency false in
/-- Each component of the downward red crossing is a quotient of induced modules. -/
theorem cyclotomicRedDownQuotient_surjective (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    Function.Surjective ((cyclotomicRedDownQuotient Q hab i h).app M) := by
  intro t
  induction t using Ind.induction_on (φ := lastEmb Q a i h) (N := M) with
  | zero => exact ⟨0, map_zero _⟩
  | tmul z n =>
    obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
    exact ⟨_, cyclotomicRedDownQuotient_tmul Q hab i h M y n⟩
  | add s t hs ht =>
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨y, rfl⟩ := ht
    exact ⟨x + y, map_add _ _ _⟩

end Categorification.Stendhal
