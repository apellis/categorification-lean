/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Leading
import Categorification.WeightedKLR.Twisted.Realize
import Categorification.WeightedKLR.Twisted.Rep

/-!
# Leading terms of twisted galleries in the polynomial representation

Linear-independence half of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.5, Proposition 2.20 (b), by the argument of Theorem 2.8. The gallery of a
word `w` from a chamber `C` of the arrangement of positions and weights acts in the
representation `twGalleryRep`, from the copy of `C` to the copy of `B = C.flips w`, by the
composite `twOpList k Γ C w` of the operators of its steps. When `w` is good, this operator is
twisted (`exists_isTwisted_twOpList`): after multiplication by a non-zero-divisor it is
`f ↦ ∑ₓ a x · x(f)`, the coefficient of the identity is a non-zero-divisor, and every other
relabelling `x` with `a x ≠ 0` has `x⁻¹ • B` separated from `C` by fewer hyperplanes than `B`.

The step operators across a hyperplane are those of `GalleryBasis.Leading`, read off the side of
the start chamber; in particular a step across a diagonal in the loop block is a divided
difference or a loop crossing as for any other diagonal, so no graph hypothesis is needed.

## Main definitions

* `TwGalleryAlgebra.twOpList k Γ C w`: the operator of the gallery of `w` from `C`.

## Main results

* `TwGalleryAlgebra.twGalleryRep_galList`: the gallery of `w` acts by `twOpList k Γ C w`.
* `TwGalleryAlgebra.exists_isTwisted_twOpList`: its leading-term form for a good word.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv TwChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace TwGalleryAlgebra

variable (k Γ) in
/-- The operator of the gallery of the word `w` from `C`: the operators of its steps, the first
step applied first. -/
noncomputable def twOpList :
    TwChamber Γ ν → List (Hyp Γ ν) → PolyRing ν k →ₗ[k] PolyRing ν k
  | _, [] => LinearMap.id
  | C, h :: w => twOpList (C.flipH h) w ∘ₗ twStepOp Γ C (C.flipH h)

omit [IsStrictOrderedRing 𝕜] in
theorem twOpList_append (C : TwChamber Γ ν) (a b : List (Hyp Γ ν)) :
    twOpList k Γ C (a ++ b) = twOpList k Γ (C.flips a) b ∘ₗ twOpList k Γ C a := by
  induction a generalizing C with
  | nil => exact (LinearMap.comp_id _).symm
  | cons h a ih =>
    simp only [List.cons_append, twOpList, flips_cons, ih, LinearMap.comp_assoc]

theorem twGalleryRep_e (hΓ : Γ.PSymm) (C : TwChamber Γ ν) :
    twGalleryRep k hΓ (e C) = blk k C C LinearMap.id := by
  rw [e, twGalleryRep_mk, twFreeRep, FreeAlgebra.lift_ι_apply]
  rfl

theorem twGalleryRep_t (hΓ : Γ.PSymm) (C C' : TwChamber Γ ν) :
    twGalleryRep k hΓ (t C C') = blk k C C' (twStepOp Γ C C') := by
  rw [t, twGalleryRep_mk, twFreeRep, FreeAlgebra.lift_ι_apply]
  rfl

theorem twGalleryRep_r (hΓ : Γ.PSymm) (g : ColPerm ν) (C : TwChamber Γ ν) :
    twGalleryRep k hΓ (r g C) = blk k C (g • C) (ren g) := by
  rw [r, twGalleryRep_mk, twFreeRep, FreeAlgebra.lift_ι_apply]
  rfl

theorem twGalleryRep_poly (hΓ : Γ.PSymm) (f : PolyRing ν k) :
    twGalleryRep k hΓ (poly f : TwGalleryAlgebra k Γ ν) = diagOp (LinearMap.mulLeft k f) := by
  rw [poly, twGalleryRep_mk, twFreeRep, FreeAlgebra.lift_ι_apply]
  rfl

/-- The gallery of `w` from `C` acts from the copy of `C` to the copy of `C.flips w` by
`twOpList k Γ C w`. -/
theorem twGalleryRep_galList (hΓ : Γ.PSymm) (C : TwChamber Γ ν) (w : List (Hyp Γ ν)) :
    twGalleryRep k hΓ (galList k C w) = blk k C (C.flips w) (twOpList k Γ C w) := by
  induction w generalizing C with
  | nil => exact twGalleryRep_e hΓ C
  | cons h w ih =>
    rw [galList_cons, map_mul, ih, twGalleryRep_t, Module.End.mul_eq_comp, blk_comp_blk]
    rfl

/-- **Leading terms of a twisted gallery.** If the walls' polynomials `Q_e(y_a, y_b)` and the
loop polynomials `P_i(y_a, y_b)` are non-zero-divisors, the operator of the gallery of a good
word `w` from `C` to `B = C.flips w` is twisted with a non-zero-divisor as the coefficient of the
identity, and every other relabelling `x` occurring in it has `x⁻¹ • B` separated from `C` by
fewer hyperplanes than `B`. -/
theorem exists_isTwisted_twOpList (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b))
    {C : TwChamber Γ ν} {w : List (Hyp Γ ν)} (hw : TwGoodWord C.1 w) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (twOpList k Γ C w) M a ∧ IsRegular (a 1) ∧
      ∀ x, a x ≠ 0 → x ≠ 1 → sepCard C.1 (x⁻¹ • C.flips w).1 < sepCard C.1 (C.flips w).1 := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, fun x => if x = 1 then 1 else 0, isRegular_one, IsTwisted.id, ?_,
      fun x hx hx1 => absurd (ite_eq_right_iff.2 fun h => absurd h hx1) hx⟩
    simp only [ite_true]
    exact isRegular_one
  | append_singleton w h ih =>
    obtain ⟨M, a, hM, hT, ha1, hlt⟩ := ih hw.of_append
    set B := C.flips w with hBdef
    obtain ⟨-, hadj, -⟩ := (hw.append : TwGoodWord B.1 [h]).cons
    set B' := B.flipH h with hB'def
    have hflips : C.flips (w ++ [h]) = B' := by rw [flips_append]; rfl
    have hop : twOpList k Γ C (w ++ [h]) = twStepOp Γ B B' ∘ₗ twOpList k Γ C w := by
      rw [twOpList_append]; rfl
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
    rw [hflips, hop]
    rcases h with wl | d
    · -- a wall: multiplication by `Q_e(y_a, y_b)` or by `1`
      rw [twStepOp_inl hadj, wallOp_eq_mulLeft]
      set c : PolyRing ν k := if B.1 (.inl wl) = false ∧ (!B.1 (.inl wl)) = true then wl.factor
        else 1
      have hc : IsRegular c := by
        simp only [c]
        split_ifs
        · exact hW wl
        · exact isRegular_one
      refine ⟨M, fun x => c * a x, hM, hT.mulLeft c, hc.mul ha1, fun x hx hx1 => ?_⟩
      have hax : a x ≠ 0 := fun h0 => hx (by simp only [h0, mul_zero])
      have := hlt x hax hx1
      have := hle x
      omega
    · -- a diagonal: a divided difference or a loop crossing
      set l := d.twLeft B
      set r := d.twRight B
      have hlr : l ≠ r := Diag.twLeft_ne_twRight B d
      have hlab : l.1 = r.1 := by rw [Diag.twLeft_label B d, Diag.twRight_label B d]
      have hs : (rename ⇑d.refl.1 : PolyRing ν k →ₐ[k] PolyRing ν k) = rename (swap l r) := by
        rw [Diag.swap_twLeft_twRight B d]
        rfl
      have hB' : B' = d.refl • B := (hadj.refl_smul).symm
      obtain ⟨c, α, β, hc, hα, hstep⟩ : ∃ c α β : PolyRing ν k, IsRegular c ∧ IsRegular α ∧
          ∀ u, c * twStepOp Γ B B' u = α * u + β * rename ⇑d.refl.1 u := by
        rw [twStepOp_inr hadj, hs]
        rcases hloop : Γ.loop l.1 with _ | P
        · refine ⟨X l - X r, 1, -1, isRegular_X_sub_X hlr, isRegular_one, fun u => ?_⟩
          rw [psiOp_of_none hloop, ddiff_spec hlr]
          ring
        · refine ⟨1, loopFactor P l r, -loopFactor P l r, isRegular_one,
            hL P l r hloop hlr hlab, fun u => ?_⟩
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
      refine ⟨c * M * rename ⇑d.refl.1 M, _, (hc.mul hM).mul (isRegular_rename_colPerm hM _),
        hT.step d.refl hstep, ?_, fun y hy hy1 => ?_⟩
      · simp only [mul_one, hzero, map_zero, mul_zero, add_zero]
        exact (hα.mul (isRegular_rename_colPerm hM _)).mul ha1
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

end TwGalleryAlgebra

end Categorification.WeightedKLR
