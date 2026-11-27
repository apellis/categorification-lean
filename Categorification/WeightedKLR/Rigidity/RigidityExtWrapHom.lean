/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtWrap
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationExt
import Categorification.WeightedKLR.Rigidity.RigidityExtSplitting

/-!
# Maps from the wrap projective to its head

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, input
for Corollary 7.7 (top degree). For two red strands and an idempotent `z₀` of `R^{λ₁}(ν)`, let `L`
be the head of the wrap projective `wrapIdem z₀ · T` of Lemma 7.3: the quotient by the images of
the cut projectives. If every element of `z₀ R^{λ₁}(ν) z₀` is a multiple of `z₀`, the maps from
the left projective of the (reflected) wrap idempotent to `L`, as a left module through the
horizontal reflection, form a line (`finrank_fixedSubspace_flipLeft_wrapHead`).

* `wrapIdem_e`: the wrap idempotent of `e(t)` is the idempotent of the wrap loading of `t`.
* `eq_zero_of_eraseWrap_eq_zero`: erasing both red strands is injective on the corner of the
  last red strand.
-/

noncomputable section

namespace Categorification.Stendhal.TwoRedErase

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ) (ν : Multiset I)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "C" => CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "π" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) ν
local notation "Λ₀" => (Λ ∘ Fin.castSucc : Fin 1 → I →₀ ℕ)

theorem wrapIdem_e (t : Seq ν) :
    wrapIdem Q Λ ν (π (KLRAlgebra.e t)) =
      TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e (wrap ν t) (wrap_ordered ν t)) := by
  rw [wrapIdem, show SingleRed.cyclotomicProjection Q Λ₀ ν (π (KLRAlgebra.e t)) =
    SingleRed.insertRed Q Λ₀ ν (KLRAlgebra.e t) from CycKLR.lift_mk _ _ _, SingleRed.insertRed_e]
  exact appendRed_mk_e (ℓ := 1) Q Λ ν (SingleRed.insertWord ν t) (SingleRed.ordered ν _)

/-- The wrap map as an additive map. -/
def wrapIdemHom : C →+ T where
  toFun := wrapIdem Q Λ ν
  map_zero' := by simp [wrapIdem]
  map_add' x y := by simp [wrapIdem]

theorem wrapIdem_smul (c : k) (z : C) : wrapIdem Q Λ ν (c • z) = c • wrapIdem Q Λ ν z := by
  rw [wrapIdem, wrapIdem, map_smul, map_smul]
  exact KLR.Corner.val_smul _ _

local notation "l" => TensorProductAlgebra.lastRedIdem (ℓ := 1) Q Λ ν

theorem lastRedIdem_mul_wrapIdem_mul (z : C) : l * wrapIdem Q Λ ν z * l = wrapIdem Q Λ ν z := by
  rw [wrapIdem, lastRedIdem_mul_val, val_mul_lastRedIdem]

/-- Erasure is injective on the corner of the last red strand. -/
theorem eq_zero_of_eraseWrap_eq_zero (hR : LastDotRelation Q Λ ν) {y : T} (hy : l * y * l = y)
    (h0 : eraseWrap Q Λ ν hR y = 0) : y = 0 := by
  let yc : TensorProductAlgebra.lastRedCorner (ℓ := 1) Q Λ ν :=
    ⟨y, (Subsemigroup.mem_corner_iff
      (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν)).2
      ⟨by rw [← hy, ← mul_assoc, ← mul_assoc,
            (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).eq],
       by rw [← hy, mul_assoc, (TensorProductAlgebra.isIdempotentElem_lastRedIdem Q Λ ν).eq]⟩⟩
  obtain ⟨u, hu⟩ := appendRed_surjective (ℓ := 1) Q Λ ν yc
  obtain ⟨z, rfl⟩ := SingleRed.cyclotomicProjection_surjective Q Λ₀ ν u
  have hy' : y = wrapIdem Q Λ ν z := (congrArg Subtype.val hu).symm
  rw [hy', wrapIdem, eraseWrap_appendRed_cyclotomicProjection] at h0
  rw [hy', h0]
  exact (wrapIdemHom Q Λ ν).map_zero

theorem tensorFlip_algebraMap (c : k) : tensorFlip (algebraMap k T c) = algebraMap k T c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tensorFlip_one]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-- **Maps from the wrap projective to the head are scalars**: for the head `L` of the wrap
projective `wrapIdem z₀ · T` (the quotient by the images of the cut projectives), the elements of
the left module `flipLeft L` fixed by the reflected wrap idempotent form a line, when every
element of `z₀ R^{λ₁}(ν) z₀` is a multiple of `z₀`. -/
theorem finrank_fixedSubspace_flipLeft_wrapHead (hR : LastDotRelation Q Λ ν) (z₀ : C)
    (hz₀ : IsIdempotentElem z₀) (hne : z₀ ≠ 0)
    (hgen : ∀ y : C, z₀ * y = y → y ≠ 0 → ∃ c : C, y * c = z₀)
    (hscalar : ∀ x : C, z₀ * x * z₀ = x → ∃ c : k, x = c • z₀) :
    Module.finrank k (fixedSubspace (k := k)
      (flipLeft Q Λ ν (rIdeal (wrapIdem Q Λ ν z₀) ⧸ coevaluationTrace (cutIdem Q Λ ν)))
      (tensorFlip (wrapIdem Q Λ ν z₀))) = 1 := by
  set W := wrapIdem Q Λ ν z₀ with hW
  have he : IsIdempotentElem W := by rw [IsIdempotentElem, hW, wrapIdem_mul, hz₀.eq]
  set N := coevaluationTrace (cutIdem Q Λ ν) with hN
  have hsimple : IsSimpleModule Tᵐᵒᵖ (rIdeal W ⧸ N) :=
    (coevaluationTrace_eq_iff_isSimpleModule_wrapIdem Q Λ ν hR z₀ hz₀ hne hgen N).1 rfl
  have hl : ∀ z : C, l * wrapIdem Q Λ ν z = wrapIdem Q Λ ν z := fun z => lastRedIdem_mul_val Q Λ ν _
  have hr : ∀ z : C, wrapIdem Q Λ ν z * l = wrapIdem Q Λ ν z := fun z => val_mul_lastRedIdem Q Λ ν _
  let w₀ : rIdeal W := ⟨W, he.eq⟩
  let q : rIdeal W → flipLeft Q Λ ν (rIdeal W ⧸ N) := fun x => Submodule.Quotient.mk x
  -- the action of `T` on `flipLeft L` through representatives
  have hact : ∀ (a : T) (x : rIdeal W), a • q x = q (op (tensorFlip a) • x) := fun a x => by
    rw [flipLeft_smul]
    rfl
  have hval : ∀ (b : T) (x : rIdeal W), ((op b • x : rIdeal W) : T) = (x : T) * b :=
    fun b x => rfl
  have hv : q w₀ ∈ fixedSubspace (k := k) (flipLeft Q Λ ν (rIdeal W ⧸ N)) (tensorFlip W) := by
    change tensorFlip W • q w₀ = q w₀
    rw [hact, tensorFlip_tensorFlip]
    exact congrArg q (Subtype.ext (show W * W = W from he.eq))
  have hv0 : q w₀ ≠ 0 := by
    intro h0
    have hmem : w₀ ∈ N := (Submodule.Quotient.mk_eq_zero N).1 h0
    have htop : N = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have hx : x = op (x : T) • w₀ := Subtype.ext (by rw [hval]; exact x.2.symm)
      rw [hx]
      exact N.smul_mem _ hmem
    have := IsSimpleModule.nontrivial Tᵐᵒᵖ (rIdeal W ⧸ N)
    obtain ⟨p, p', hpq⟩ := this
    apply hpq
    induction p using Submodule.Quotient.induction_on with
    | H p =>
      induction p' using Submodule.Quotient.induction_on with
      | H p' =>
        rw [Submodule.Quotient.eq, htop]
        exact Submodule.mem_top
  have hfin := (finrank_eq_one_iff_of_nonzero' (K := k) (⟨q w₀, hv⟩ : fixedSubspace (k := k)
    (flipLeft Q Λ ν (rIdeal W ⧸ N)) (tensorFlip W)) (fun h => hv0 (congrArg Subtype.val h))).2
  refine hfin fun m => ?_
  obtain ⟨m, hm⟩ := m
  change tensorFlip W • m = m at hm
  induction m using Submodule.Quotient.induction_on with
  | H x =>
    change tensorFlip W • q x = q x at hm
    rw [hact, tensorFlip_tensorFlip] at hm
    let Φ := eraseWrap Q Λ ν hR
    have hΦW : Φ W = z₀ := eraseWrap_appendRed_cyclotomicProjection Q Λ ν hR z₀
    have hxW : W * (x : T) = x := x.2
    have hΦx : Φ x = z₀ * Φ x := by
      conv_lhs => rw [← hxW]
      rw [map_mul, hΦW]
    have hcorner : l * ((x : T) * W) * l = (x : T) * W := by
      rw [← hxW, mul_assoc l, mul_assoc, mul_assoc, hr, ← mul_assoc, hl]
      exact (mul_assoc _ _ _).symm
    obtain ⟨c, hc⟩ := hscalar (z₀ * Φ x * z₀) (by
      simp only [mul_assoc, hz₀.eq]
      rw [← mul_assoc z₀ z₀, hz₀.eq])
    have hy : (x : T) * W = c • W := by
      rw [← wrapIdem_smul, ← sub_eq_zero]
      apply eq_zero_of_eraseWrap_eq_zero Q Λ ν hR
      · rw [mul_sub, sub_mul, hcorner, lastRedIdem_mul_wrapIdem_mul]
      · rw [map_sub, map_mul, hΦW, show Φ (wrapIdem Q Λ ν (c • z₀)) = c • z₀ from
          eraseWrap_appendRed_cyclotomicProjection Q Λ ν hR _, ← hc, ← hΦx, sub_self]
    refine ⟨c, Subtype.ext ?_⟩
    change algebraMap k T c • q w₀ = q x
    rw [hact, tensorFlip_algebraMap, ← hm]
    refine congrArg q (Subtype.ext ?_)
    rw [hval, hval, hy, Algebra.smul_def, ← Algebra.commutes]

end Categorification.Stendhal.TwoRedErase
