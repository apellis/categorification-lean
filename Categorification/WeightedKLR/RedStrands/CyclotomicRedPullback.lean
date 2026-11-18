/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Restriction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Pullback across a red strand and cyclotomic restriction

Webster, arXiv:1309.3796v2, §4.5. In the cyclotomic action a red label increases
the highest weight by restriction of scalars along the natural quotient.
Right-black restriction commutes with this operation. The polynomial form below
allows any pointwise divisibility of cyclotomic parameters over a commutative ring.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra CyclotomicAction CategoryTheory Polynomial

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]}
  (hab : ∀ i, a i ∣ b i)

/-- The weight-lowering cyclotomic projection induced by the identity of the affine algebra.
For a red weight with coroot multiplicities δ, take bᵢ = X^(λᵢ+δᵢ) and aᵢ = X^λᵢ. -/
def cyclotomicRedProjection (hab : ∀ i, a i ∣ b i) (β : Multiset I) : CycKLR k Q b β →ₐ[k] CycKLR k Q a β := by
  apply CycKLR.lift (CycKLR.mk k Q a β)
  intro s
  by_cases h : 0 < β.card
  · rw [cycElt_of_pos Q b s h]
    obtain ⟨c, hc⟩ := hab (s.lbl ⟨0,h⟩)
    let ev : k[X] →ₐ[k] KLRAlgebra k Q β := aeval (x ⟨0, h⟩ : KLRAlgebra k Q β)
    have hm : ev (b (s.lbl ⟨0,h⟩)) = ev c * ev (a (s.lbl ⟨0,h⟩)) := by
      rw [hc, mul_comm (a _) c, map_mul]
    rw [show aeval (x ⟨0,h⟩ : KLRAlgebra k Q β) (b (s.lbl ⟨0,h⟩)) = _ from hm,
      mul_assoc, map_mul, CycKLR.mk_aeval_x_mul_e, mul_zero]
  · simp [cycElt, h]

@[simp] theorem cyclotomicRedProjection_mk {β : Multiset I} (x : KLRAlgebra k Q β) :
    cyclotomicRedProjection Q hab β (CycKLR.mk k Q b β x) = CycKLR.mk k Q a β x :=
  CycKLR.lift_mk _ _ x

theorem cyclotomicRedProjection_surjective (β : Multiset I) :
    Function.Surjective (cyclotomicRedProjection Q hab β) := by
  intro x
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective x
  exact ⟨_, cyclotomicRedProjection_mk Q hab y⟩

/-- Appending a last black strand commutes with the cyclotomic projection. -/
theorem cyclotomicRedProjection_lastEmb (i : I) {β γ : Multiset I} (h : {i} + β = γ)
    (x : CycKLR k Q b β) :
    cyclotomicRedProjection Q hab γ (lastEmb Q b i h x) =
      lastEmb Q a i h (cyclotomicRedProjection Q hab β x) := by
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective x
  simp only [lastEmb_mk, cyclotomicRedProjection_mk]

/-- Pullback of a cyclotomic module across the red label, on one black content. -/
abbrev cyclotomicRedPullback (β : Multiset I) :=
  ModuleCat.restrictScalars.{max u v w} (cyclotomicRedProjection Q hab β).toRingHom

private def pullbackResEquiv (i : I) {β γ : Multiset I} (h : {i} + β = γ)
    (M : ModuleCat.{max u v w} (CycKLR k Q a γ)) :
    ((cyclotomicRedPullback Q hab γ ⋙ res Q b i h).obj M) ≃ₗ[CycKLR k Q b β]
      ((res Q a i h ⋙ cyclotomicRedPullback Q hab β).obj M) := by
  let π := cyclotomicRedProjection Q hab
  have he : π γ (lastEmb Q b i h 1) = lastEmb Q a i h 1 := by
    rw [cyclotomicRedProjection_lastEmb, map_one]
  exact {
    toFun m := InductionAlong.Res.mk (M := M) (m.val : M) (by
      change lastEmb Q a i h 1 • (m.val : M) = _
      rw [← he]
      exact m.prop)
    invFun m := InductionAlong.Res.mk (InductionAlong.Res.val (φ := lastEmb Q a i h) (M := M) m) (by
      change π γ (lastEmb Q b i h 1) • (InductionAlong.Res.val (M := M) (φ := lastEmb Q a i h) m) = _
      rw [he]
      exact InductionAlong.Res.prop (M := M) m)
    left_inv _ := InductionAlong.Res.ext rfl
    right_inv _ := InductionAlong.Res.ext rfl
    map_add' _ _ := InductionAlong.Res.ext rfl
    map_smul' r m := by
      apply InductionAlong.Res.ext
      change π γ (lastEmb Q b i h r) • (m.val : M) = lastEmb Q a i h (π β r) • (m.val : M)
      rw [cyclotomicRedProjection_lastEmb] }

/-- Red pullback commutes naturally with cyclotomic restriction on the last black strand
(Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25, restriction square). -/
def cyclotomicRedPullbackResIso (i : I) {β γ : Multiset I} (h : {i} + β = γ) :
    cyclotomicRedPullback.{u,v,w} Q hab γ ⋙ res Q b i h ≅
      res Q a i h ⋙ cyclotomicRedPullback Q hab β :=
  NatIso.ofComponents (fun M => (pullbackResEquiv Q hab i h M).toModuleIso) fun _ => by
    apply ModuleCat.hom_ext
    ext m
    exact InductionAlong.Res.ext rfl

end Categorification.Stendhal
