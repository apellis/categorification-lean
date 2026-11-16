/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Leading

/-!
# The identity coefficient of a gallery

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). In the polynomial representation, the operator of a step
across a hyperplane `h` from a full chamber `B` is `f ↦ (α / c) f + (β / c) s(f)`: for a wall,
multiplication by the wall polynomial `Q_e(y_a, y_b)` (when the wall is crossed in the positive
direction) or by `1`; for a diagonal without loop, the divided difference, with identity
coefficient `1 / (X_l - X_r)`; for a diagonal with loop polynomial `P`, the loop crossing, with
identity coefficient `P(X_l, X_r)`. We record the numerator and the denominator of the identity
coefficient of the step (`stepNum`, `stepDen`) and their products along a word (`galNum`,
`galDen`).

Along a minimal gallery the identity coefficient of the composite operator is the product of the
identity coefficients of its steps (`exists_isTwisted_opList_galNum`): the reflection of a newly
crossed diagonal never occurs among the relabellings of the shorter gallery, since these move the
end chamber closer to the start (`exists_isTwisted_opList`).

## Main definitions

* `stepNum`, `stepDen`: the numerator and denominator of the identity coefficient of a step.
* `galNum`, `galDen`: their products along a word.

## Main results

* `exists_isTwisted_opList_galNum`: the identity coefficient of the operator of a good word is
  `galNum / galDen`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable (k) in
/-- The numerator of the identity coefficient of the step across `h` from `B`: the wall
polynomial for a wall crossed positively, the loop factor `P(X_l, X_r)` for a diagonal whose
colour carries the loop polynomial `P`, and `1` otherwise. -/
noncomputable def stepNum (B : FullChamber Γ ν) : Hyp Γ ν → PolyRing ν k
  | .inl wl => if B.1 (.inl wl) = false ∧ (!B.1 (.inl wl)) = true then wl.factor else 1
  | .inr d => match Γ.loop (d.left B).1 with
    | none => 1
    | some P => loopFactor P (d.left B) (d.right B)

variable (k) in
/-- The denominator of the identity coefficient of the step across `h` from `B`: `X_l - X_r`
for a diagonal without loop, `1` otherwise. -/
noncomputable def stepDen (B : FullChamber Γ ν) : Hyp Γ ν → PolyRing ν k
  | .inl _ => 1
  | .inr d => match Γ.loop (d.left B).1 with
    | none => X (d.left B) - X (d.right B)
    | some _ => 1

variable (k) in
/-- The product of the numerators of the identity coefficients of the steps of a word. -/
noncomputable def galNum : FullChamber Γ ν → List (Hyp Γ ν) → PolyRing ν k
  | _, [] => 1
  | C, h :: w => stepNum k C h * galNum (C.flipH h) w

variable (k) in
/-- The product of the denominators of the identity coefficients of the steps of a word. -/
noncomputable def galDen : FullChamber Γ ν → List (Hyp Γ ν) → PolyRing ν k
  | _, [] => 1
  | C, h :: w => stepDen k C h * galDen (C.flipH h) w

omit [IsStrictOrderedRing 𝕜] in
theorem galNum_append (C : FullChamber Γ ν) (a b : List (Hyp Γ ν)) :
    galNum k C (a ++ b) = galNum k C a * galNum k (C.flips a) b := by
  induction a generalizing C with
  | nil => simp [galNum]
  | cons h a ih => simp only [List.cons_append, galNum, flips_cons, ih, mul_assoc]

omit [IsStrictOrderedRing 𝕜] in
theorem galDen_append (C : FullChamber Γ ν) (a b : List (Hyp Γ ν)) :
    galDen k C (a ++ b) = galDen k C a * galDen k (C.flips a) b := by
  induction a generalizing C with
  | nil => simp [galDen]
  | cons h a ih => simp only [List.cons_append, galDen, flips_cons, ih, mul_assoc]

omit [IsStrictOrderedRing 𝕜] in
theorem galNum_singleton (C : FullChamber Γ ν) (h : Hyp Γ ν) :
    galNum k C [h] = stepNum k C h := by
  simp [galNum]

omit [IsStrictOrderedRing 𝕜] in
theorem galDen_singleton (C : FullChamber Γ ν) (h : Hyp Γ ν) :
    galDen k C [h] = stepDen k C h := by
  simp [galDen]

omit [IsStrictOrderedRing 𝕜] in
theorem isRegular_stepDen (C : FullChamber Γ ν) (h : Hyp Γ ν) :
    IsRegular (stepDen k C h) := by
  rcases h with wl | d
  · exact isRegular_one
  · simp only [stepDen]
    split
    · exact isRegular_X_sub_X (Diag.left_ne_right C d)
    · exact isRegular_one

omit [IsStrictOrderedRing 𝕜] in
/-- The denominator of the identity coefficient of a gallery is a non-zero-divisor. -/
theorem isRegular_galDen (C : FullChamber Γ ν) (w : List (Hyp Γ ν)) :
    IsRegular (galDen k C w) := by
  induction w generalizing C with
  | nil => exact isRegular_one
  | cons h w ih => exact (isRegular_stepDen C h).mul (ih _)

/-- **The identity coefficient of a gallery.** The operator of the gallery of a good word `w`
from `C` is twisted with a non-zero-divisor denominator `M`, its coefficient of the identity is
`M * galNum / galDen`, and every other relabelling `x` occurring in it has `x⁻¹ • C.flips w`
separated from `C` by fewer hyperplanes than `C.flips w`. -/
theorem exists_isTwisted_opList_galNum {C : FullChamber Γ ν} {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (opList k Γ C w) M a ∧ a 1 * galDen k C w = M * galNum k C w ∧
      ∀ x, a x ≠ 0 → x ≠ 1 → sepCard C.1 (x⁻¹ • C.flips w).1 < sepCard C.1 (C.flips w).1 := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, fun x => if x = 1 then 1 else 0, isRegular_one, IsTwisted.id, by
      simp [galNum, galDen], fun x hx hx1 => absurd (ite_eq_right_iff.2 fun h => absurd h hx1) hx⟩
  | append_singleton w h ih =>
    obtain ⟨M, a, hM, hT, ha1, hlt⟩ := ih hw.of_append
    set B := C.flips w with hBdef
    obtain ⟨-, hadj, -⟩ := (hw.append : GoodWord B.1 [h]).cons
    set B' := B.flipH h with hB'def
    have hflips : C.flips (w ++ [h]) = B' := by rw [flips_append]; rfl
    have hop : opList k Γ C (w ++ [h]) = stepOp Γ B B' ∘ₗ opList k Γ C w := by
      rw [opList_append]; rfl
    have hhw : h ∉ w := by
      have := List.nodup_append_comm.1 hw.1
      exact (List.nodup_cons.1 this).1
    have hCB : C.1 h = B.1 h := by
      rw [hBdef, flips_val hw.of_append]
      simp [flipSigns, hhw]
    have hcard : sepCard C.1 B'.1 = sepCard C.1 B.1 + 1 := by
      rw [adjacent_iff_eq_flipSign.1 hadj]
      exact sepCard_flipSign_of_eq hCB
    have hle : ∀ x : ColPerm ν, sepCard C.1 (x⁻¹ • B').1 ≤ sepCard C.1 (x⁻¹ • B).1 + 1 := by
      intro x
      rw [adjacent_iff_eq_flipSign.1 (hadj.smul x⁻¹)]
      exact sepCard_flipSign_le _ _ _
    rw [galNum_append, galDen_append, galNum_singleton, galDen_singleton, ← hBdef]
    rw [hflips, hop]
    rcases h with wl | d
    · rw [stepOp_inl hadj, wallOp_eq_mulLeft]
      refine ⟨M, fun x => stepNum k B (.inl wl) * a x, hM, hT.mulLeft _, ?_,
        fun x hx hx1 => ?_⟩
      · simp only [stepDen, mul_one]
        linear_combination stepNum k B (.inl wl) * ha1
      · have hax : a x ≠ 0 := fun h0 => hx (by simp only [h0, mul_zero])
        have := hlt x hax hx1
        have := hle x
        omega
    · set l := d.left B
      set r := d.right B
      have hlr : l ≠ r := Diag.left_ne_right B d
      have hs : (rename ⇑d.refl.1 : PolyRing ν k →ₐ[k] PolyRing ν k) = rename (swap l r) := by
        rw [Diag.swap_left_right B d]
        rfl
      have hB' : B' = d.refl • B := (hadj.refl_smul).symm
      obtain ⟨β, hstep⟩ : ∃ β : PolyRing ν k, ∀ u, stepDen k B (.inr d) * stepOp Γ B B' u =
          stepNum k B (.inr d) * u + β * rename ⇑d.refl.1 u := by
        rw [stepOp_inr hadj, hs]
        rcases hloop : Γ.loop l.1 with _ | P
        · refine ⟨-1, fun u => ?_⟩
          have hl : Γ.loop (d.left B).1 = none := hloop
          simp only [stepDen, stepNum, hl]
          rw [psiOp_of_none hloop, ddiff_spec hlr]
          ring
        · refine ⟨-loopFactor P l r, fun u => ?_⟩
          have hl : Γ.loop (d.left B).1 = some P := hloop
          simp only [stepDen, stepNum, hl]
          rw [psiOp_of_some hloop]
          ring
      have hrefl : d.refl ≠ 1 := by
        intro e
        have := congrArg (fun g : ColPerm ν => g.1 d.fst) e
        simp only [Diag.refl, swap_apply_left] at this
        exact d.fst_ne_snd this.symm
      have hzero : a d.refl⁻¹ = 0 := by
        by_contra hne
        have h1 := hlt _ hne (inv_ne_one.2 hrefl)
        rw [inv_inv, ← hB', hcard] at h1
        omega
      refine ⟨stepDen k B (.inr d) * M * rename ⇑d.refl.1 M, _,
        ((isRegular_stepDen B _).mul hM).mul (isRegular_rename_colPerm hM _),
        hT.step d.refl hstep, ?_, fun y hy hy1 => ?_⟩
      · simp only [mul_one, hzero, map_zero, mul_zero, add_zero]
        linear_combination (stepNum k B (.inr d) * rename ⇑d.refl.1 M *
          stepDen k B (.inr d)) * ha1
      · by_cases hay : a y = 0
        · have hay' : a (d.refl⁻¹ * y) ≠ 0 := fun h0 => hy (by simp only [hay, h0, map_zero,
            mul_zero, add_zero])
          have hsm : y⁻¹ • B' = (d.refl⁻¹ * y)⁻¹ • B := by
            rw [hB', ← mul_smul, mul_inv_rev, inv_inv]
          rw [hsm]
          by_cases hx1 : d.refl⁻¹ * y = 1
          · rw [hx1, inv_one, one_smul]
            omega
          · have := hlt _ hay' hx1
            omega
        · have := hlt y hay hy1
          have := hle y
          omega

end GalleryAlgebra

end Categorification.WeightedKLR
