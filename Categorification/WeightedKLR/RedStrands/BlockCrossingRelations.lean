/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingSeam
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.BraidedStandardInjective

/-!
# Relations in the ordinary crossing tensor

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8. Push global violations to
the uncrossed red order, then mark a seam above each interior bad loading. The kernel
of balanced stacking is already represented by differences of marked diagrams which
are equal before any of the red-dot, violated or higher quotients. This moves the
remaining question of independence of cuts to the affine algebra.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MvPolynomial
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "X" => diagrams Q Λ Bs
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "Braid" => BraidedStendhalAlgebra k Q Λ ν
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "p" => redIdem k Q Λ (ν := ν) κ₀
local notation "P" => redProj k Q Λ ν κ₀
local notation "E₀" => orderedIdem Q Λ (fun _ => 1) Bs
local notation "E₁" => orderedIdem Q Λ (fun _ => Fin.revPerm) Bs
local notation "G" => affineStackBlocks Q Λ L M f β h
local notation "F" => stackBlocks Q Λ L M f β h
local notation "cl" => crossingSeamClass Q Λ L M f β h hQ
local notation "stack" => crossingSeamStack Q Λ L M f β h
local notation "stk" => crossingStack Q Λ hQ L M f β h
local notation "raw" => ofKLR k Q Λ ν
local notation "secB" => toKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "π" => AlgHom.comp mk raw
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs) κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "U" => Submodule.map stack (LinearMap.ker cl)

private theorem bad_mem {i : Seq μ} (hi : redWord i = κ₀) (hv : q (π (e i)) = 0) (y z : R) :
    G 1 * y * e i * z ∈ U := by
  obtain ⟨u,hu,hc⟩ := exists_zero_crossingSeamClass Q Λ L M f β h hQ (e i)
    ((redIdem_mul_e ..).trans (ite_eq_left hi)) hv y z
  exact ⟨u,hc,hu⟩

private theorem redDots_mem (y : R) : G 1 * (y - secB (raw y)) * p ∈ U := by
  let g := (LinearMap.mulRight k p).comp ((LinearMap.mulLeft k (G 1)).comp
    (LinearMap.id - (secB).toLinearMap.comp (raw).toLinearMap))
  change y ∈ (U).comap g
  let ρ := canWord m
  have hw : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  have W : y ∈ Submodule.span k {b : R | ∃ (w : Perm (Fin m)) (d : Fin m →₀ ℕ) (i : Seq μ),
      ψw (ρ w) * pol (monomial d 1) * e i = b} := by rw [span_eq_top' ρ hw]; trivial
  apply (Submodule.span_le.2 ?_) W
  rintro _ ⟨w,d,i,rfl⟩
  let b : R := ψw (ρ w) * pol (monomial d 1) * e i
  change G 1 * (b - secB (raw b)) * p ∈ U
  by_cases hb : ∀ a, (i.lbl a).isRight → d a = 0
  · rw [show secB (raw b) = b from toKLR_ofKLR_std _ _ _ hb, sub_self, mul_zero, zero_mul]; exact zero_mem _
  push Not at hb
  obtain ⟨a,ha,hd⟩ := hb
  rw [show raw b = 0 from ofKLR_std_eq_zero _ _ _ _ ha hd, map_zero (secB), sub_zero]
  by_cases ho : redWord i = κ₀
  · let v : R := pol (monomial d 1) * e i
    have hv : raw v = 0 := by simpa only [ψw_nil, one_mul] using
      (ofKLR_std_eq_zero (k := k) (Q := Q) (Λ := Λ) [] d i a ha hd)
    have hp : p * v = v := by
      have hc := (e_commute_pol (Q := stendhalQ Q Λ) i (monomial d 1)).eq
      rw [show v = e i * pol (monomial d 1) from hc.symm, ← mul_assoc, redIdem_mul_e, ite_eq_left ho]
    obtain ⟨u,hu,hc⟩ := exists_zero_crossingSeamClass Q Λ L M f β h hQ v hp
      (by simp only [AlgHom.comp_apply, hv, map_zero]) (ψw (ρ w)) p
    exact ⟨u,hc,by simpa only [b, v, mul_assoc] using hu⟩
  · simp only [b, mul_assoc, e_mul_redIdem, ite_eq_right ho, mul_zero, zero_mem]

private theorem sec_order : secB P = p := by
  rw [redProj, redIdem, map_sum, map_sum]; simp only [toKLR_ofKLR_e]

private theorem violated_mem {b : Braid} (hb : mk b = 0) : G 1 * secB b * p ∈ U := by
  let ρ := canWord m
  have hw : IsReducedChoice ρ := fun w => ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  have H := redProj_mul_mem_violSpan hw hQ κ₀ (flip_mem_violIdeal ((violMk_eq_zero_iff _).1 hb))
  suffices H' : ∀ t ∈ violSpan k Q Λ ν κ₀, G 1 * secB (flip t) ∈ U by
    simpa only [flip_mul, BraidedStendhalAlgebra.flip_flip, flip_redProj, map_mul, sec_order, mul_assoc] using H' _ H
  intro t ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨y,i,z,hv,hi,rfl⟩ := ht
    simp only [flip_mul, flip_e, map_mul, toKLR_ofKLR_e]
    simpa only [mul_assoc] using bad_mem Q Λ hQ L M f β h hi
      (show q (mk (raw (e i))) = 0 by rw [violMk_e hv, map_zero (q)]) (secB (flip z)) (secB (flip y))
  | zero => simp only [flip_zero, map_zero, mul_zero, zero_mem]
  | add _ _ _ _ hu hv => simpa only [flip_add, map_add, mul_add] using add_mem hu hv
  | smul c x _ hx => simpa only [flip_smul, map_smul, mul_smul_comm] using (U).smul_mem c hx

private theorem quotient_mem {b : Braid} (hb : mk b ∈ J) : G 1 * secB b * p ∈ U := by
  let T := (LinearMap.mulRight k p).comp ((LinearMap.mulLeft k (G 1)).comp (secB).toLinearMap)
  change b ∈ (U).comap T
  let V := (U).comap T
  have lift (a : Braid) (ha : a ∈ V) (b' : Braid) (hb' : mk b' = mk a) : b' ∈ V := by
    have hz := violated_mem Q Λ hQ L M f β h (b := b'-a) (by rw [map_sub, hb', sub_self])
    exact sub_add_cancel b' a ▸ V.add_mem hz ha
  rw [blockUpperIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hb
  suffices H : ∀ z ∈ AddSubgroup.closure _, ∃ b' ∈ V, mk b' = z by
    obtain ⟨a,ha,he⟩ := H _ hb
    exact lift a ha b he.symm
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨_,⟨a,-,_,⟨i,hi,higher,rfl⟩,rfl⟩,c,-,rfl⟩ := hz
    obtain ⟨a,rfl⟩ := violMk_surjective a
    obtain ⟨c,rfl⟩ := violMk_surjective c
    refine ⟨a * raw (e i) * c, ?_, by simp only [map_mul, AlgHom.comp_apply]⟩
    change G 1 * secB (a * raw (e i) * c) * p ∈ U
    have hv : q (π (e i)) = 0 := by
      change (J).ringCon.mk' _ = 0
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      exact TwoSidedIdeal.subset_span ⟨i,hi,higher,rfl⟩
    simpa only [map_mul, toKLR_ofKLR_e, mul_assoc] using
      bad_mem Q Λ hQ L M f β h hi hv (secB a) (secB c * p)
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x,hx,rfl⟩ := hx; obtain ⟨y,hy,rfl⟩ := hy
    exact ⟨x+y, add_mem hx hy, map_add _ _ _⟩
  | neg _ _ hx => obtain ⟨x,hx,rfl⟩ := hx; exact ⟨-x, neg_mem hx, map_neg _ _⟩

/-- **Lifting the interior ideal** (Webster, arXiv:1309.3796v2, proof of Lemma 6.8).
Every diagram relation introduced by a red dot, a violation of any red order, or a higher
uncrossed loading has a lift to zero in the balanced tensor with the same affine stack
on the juxtaposed-top, uncrossed-bottom column. -/
theorem exists_zero_crossingSeamClass_of_quotient {y : R} (hy : q (π y) = 0) :
    ∃ u, stack u = G 1 * y * p ∧ cl u = 0 := by
  change (J).ringCon.mk' (mk (raw y)) = 0 at hy
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk'] at hy
  have H := (U).add_mem (redDots_mem Q Λ hQ L M f β h y) (quotient_mem Q Λ hQ L M f β h hy)
  rw [← add_mul, ← mul_add, sub_add_cancel] at H
  obtain ⟨u,hc,hu⟩ := H
  exact ⟨u,hu,hc⟩

/-- Forget an uncrossed marked seam with exactly the outer boundary projectors of the
ordinary comparison, but before killing any affine diagrams. -/
def crossingBoundaryStack : X ⊗[k] R →ₗ[k] R :=
  (LinearMap.mulLeft k (G E₁)) ∘ₗ (LinearMap.mulRight k p) ∘ₗ stack

local notation "mult" => crossingBoundaryStack Q Λ L M f β h

private theorem stack_val (t : X ⊗[k] R) : (stk (cl t)).1.1 = q (π (mult t)) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, Submodule.coe_add, ht, hu]
  | tmul x y =>
    change (stk (crossingCut Q Λ hQ L M f β h (x ⊗ₜ π y))).1.1 = _
    rw [crossingStack_cut, orderedColumnRep_val]
    change q (F E₁ * (F x * F E₀ * π y * π p)) = q (π (G E₁ * (G (x * E₀) * y * p)))
    simp only [map_mul]; rfl

private theorem project_twice (y : R) : G E₁ * ((G E₁ * (y*p))*p) = G E₁ * (y*p) := by
  have idem : ∀ row, IsIdempotentElem (orderedIdem Q Λ (fun _ => Fin.revPerm) row) := by
    intro row; induction row with
    | nil => exact one_mul _
    | cons B row ih =>
      change (_ ⊗ₜ[k] _) * (_ ⊗ₜ[k] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, (isIdempotentElem_redProj _).eq, ih.eq]; rfl
  rw [mul_assoc (G E₁) (y*p), mul_assoc y, redIdem_mul_redIdem, ← mul_assoc,
    ← map_mul, (idem Bs).eq]

/-- **Kernel of ordinary stacking in terms of affine changes of seam** (Webster,
arXiv:1309.3796v2, §6.1, proof of Lemma 6.8). Every balanced class in the kernel is the
class of a sum whose affine stack is already zero. In particular the quotient introduces
no additional kernel generators; it remains to identify the classes of affine relations. -/
private theorem lift_kernel (z) (hz : stk z = 0) : z ∈ (LinearMap.ker mult).map cl := by
  ·
    obtain ⟨s,rfl⟩ := crossingCut_surjective Q Λ hQ L M f β h z
    obtain ⟨t,rfl⟩ := TensorProduct.map_surjective (g := (LinearMap.id : X →ₗ[k] X)) Function.surjective_id
      (show Function.Surjective (π).toLinearMap from violMk_surjective.comp ofKLR_surjective) s
    change stk (cl t) = 0 at hz
    have hy : q (π (mult t)) = 0 := (stack_val Q Λ hQ L M f β h t).symm.trans
      (congrArg (fun z => z.1.1) hz)
    obtain ⟨u,hu,hc⟩ := exists_zero_crossingSeamClass_of_quotient Q Λ hQ L M f β h hy
    have hnorm : G 1 * mult t * p = mult t := by
      change G 1 * (G E₁ * (stack t * p)) * p = _
      rw [← mul_assoc (G 1), ← map_mul, one_mul, mul_assoc (G E₁), mul_assoc (stack t), redIdem_mul_redIdem]; rfl
    rw [hnorm] at hu
    refine ⟨t-u, ?_, ?_⟩
    · change mult (t-u) = 0
      rw [map_sub, sub_eq_zero]
      change _ = G E₁ * (stack u * p)
      rw [hu]; exact (project_twice Q Λ L M f β h (stack t)).symm
    · change cl (t-u) = cl t
      rw [map_sub, hc, sub_zero]
/-- **Kernel of ordinary stacking in terms of affine changes of seam** (Webster,
arXiv:1309.3796v2, §6.1, proof of Lemma 6.8). Every balanced class in the kernel is the
class of a sum whose affine stack is already zero. -/
theorem ker_crossingStack_eq_map_ker_boundaryStack :
    LinearMap.ker ((stk).restrictScalars k) = (LinearMap.ker mult).map cl := by
  refine le_antisymm (fun z hz => lift_kernel Q Λ hQ L M f β h z hz) ?_
  rintro _ ⟨t,ht,rfl⟩
  change stk (cl t) = 0
  apply Subtype.ext; apply Subtype.ext
  exact (stack_val Q Λ hQ L M f β h t).trans ((congrArg (fun y : R => q (π y)) ht).trans
    ((congrArg (q) (map_zero (π))).trans (map_zero (q))))

end Categorification.Stendhal.RedBlock
