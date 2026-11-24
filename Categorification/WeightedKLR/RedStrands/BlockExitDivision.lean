/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelExits
import Categorification.WeightedKLR.RedStrands.StendhalDotInjective
import Categorification.KLR.ReturnCrossing

/-!
# Dividing loading ideals at a red–black crossing

Webster, arXiv:1309.3796v2, §6.1, Proposition 6.4 and the kernel test following
(6.21). Use PBW words ending in a specified crossing on every generator of a loading
ideal. The factor left after removing the crossing is still in that ideal. This is
applied first to global violations and then to the higher ideal. The black-dot shift
is injective on the *affine* PBW basis; no dot is cancelled in either quotient.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv MvPolynomial
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun s : KLR.Seq μ => raw (e s)
local notation "ρ" => canWord m
private theorem exitWords {n : ℕ} : IsReducedChoice (canWord n) :=
  fun w => ⟨isReduced_canWord _ w,wordProd_canWord _ w⟩

private theorem affine_black_dot (hQ : KLRSymm Q) (t : KLR.Seq μ) (a : Fin m)
    (ha : (t.lbl a).isLeft) (d : ℕ) (y : A) (hy : y * p t = y) (hz : y * raw (x a) ^ d = 0) : y = 0 := by
  classical
  let B := basis (Λ := Λ) (ν := ν) hQ ρ exitWords
  let addDots (s : KLR.Seq μ) : Fin m →₀ ℕ := if s = t then Finsupp.single a d else 0
  let shift (b : BlackIdx (ℓ := ℓ) ν) : BlackIdx (ℓ := ℓ) ν :=
    ⟨(b.1.1,b.1.2.1,b.1.2.2 + addDots b.1.1), by
      intro q hq
      simp only [Finsupp.coe_add, Pi.add_apply, b.2 _ hq, zero_add, addDots]
      split_ifs with h
      · apply Finsupp.single_eq_of_ne; rintro rfl
        rw [h] at hq; cases hl : t.lbl q <;> simp_all
      · rfl⟩
  have hinj : Function.Injective shift := by
    rintro ⟨⟨s,w,u⟩,h⟩ ⟨⟨s',w',v⟩,h'⟩ he
    have eqv : (s,w,u+addDots s) = (s',w',v+addDots s') := congrArg Subtype.val he
    obtain ⟨rfl,rfl,eq⟩ := Prod.mk.inj eqv |>.imp_right Prod.mk.inj
    exact Subtype.ext (congrArg (fun n => (s,w,n)) (add_right_cancel eq))
  let F := LinearMap.mulRight k (p t * raw (x a) ^ d + (1-p t))
  have bval (b : BlackIdx (ℓ := ℓ) ν) : B b = raw (KLRAlgebra.stdElt ρ b.1) :=
    basis_apply hQ ρ exitWords b
  have image : F ∘ B = B ∘ shift := by
    funext b
    change B b * (p t * raw (x a) ^ d + (1-p t)) = B (shift b)
    rw [mul_add, mul_sub, mul_one, ← mul_assoc, basis_mul_e hQ]
    by_cases h : b.1.1 = t
    · rw [ite_eq_left h, sub_self, add_zero]
      obtain ⟨⟨s,w,u⟩,hu⟩ := b; change s = t at h; subst s
      let b₀ : BlackIdx (ℓ := ℓ) ν := ⟨(t,w,u),hu⟩
      have he := stdElt_mul_e_mul_x_pow (Q := stendhalQ Q Λ) ρ (t,w,u) a d
      rw [Stendhal.stdElt_mul_e] at he
      have hidx : (shift b₀).1 = (t,w,u + Finsupp.single a d) := by simp [shift,b₀,addDots]
      calc B b₀ * raw (x a) ^ d = raw (KLRAlgebra.stdElt ρ (t,w,u) * x a ^ d) := by
             rw [bval b₀,map_mul,map_pow]
           _ = raw (KLRAlgebra.stdElt ρ (shift b₀).1) := congrArg raw (he.trans (congrArg (KLRAlgebra.stdElt ρ) hidx.symm))
           _ = B (shift b₀) := (bval (shift b₀)).symm
    · rw [ite_eq_right h,zero_mul,sub_zero,zero_add]
      apply congrArg B; apply Subtype.ext; simp [shift,addDots,h]
  have inject := LinearMap.injective_of_linearIndependent (f := F) B.span_eq
    (image ▸ B.linearIndependent.comp shift hinj : LinearIndependent k (F ∘ B))
  apply inject
  change y * (p t * raw (x a) ^ d + (1-p t)) = _
  rw [mul_add, ← mul_assoc, hy, hz, mul_sub, mul_one, hy, sub_self, zero_add, map_zero]

variable (s : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (hj : j+1 < (stendhalWeight ℓ ν).card)
local notation "v" => sadj m j • s
local notation "c" => raw (ψ j * e s)

private theorem exit_descent_factor (hQ : KLRSymm Q) (u : KLR.Seq μ)
    (hd : ∀ w : Perm (Fin m), w • s = u → w ⟨j+1,hj⟩ < w ⟨j,by omega⟩) (z : A) :
    ∃ d : A, p u * z * p s = d * c := by
  obtain ⟨y,rfl⟩ := ofKLR_surjective z
  let B := lbasis («μ» := μ) (stendhalQ_symm Q Λ hQ) (descentWord hj) (descentWord_spec hj)
  have H : (e u * y * e s : R) ∈ LinearMap.range (LinearMap.mulRight k (ψ j * e s : R)) := by
    induction B.mem_span y using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add,add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm,smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    | mem z hz =>
      obtain ⟨⟨t,w,n⟩,rfl⟩ := hz
      rw [lbasis_apply,mul_assoc, mul_assoc _ (e t), e_mul_e]
      by_cases ht : t = s
      · subst t; rw [ite_eq_left (rfl : s = s)]
        by_cases hw : w • s = u
        · obtain ⟨l,hl⟩ := exists_descentWord_eq_append hj w (hd w hw)
          refine ⟨e u * pol (monomial n 1) * ψw l, ?_⟩
          simp only [LinearMap.mulRight_apply,hl,ψw_append,ψw_cons,ψw_nil,mul_one,mul_assoc]
        · have cut := e_mul_pol_ψw_e (Q := stendhalQ Q Λ) (monomial n (1 : k)) (descentWord hj w) s
          rw [(descentWord_spec hj w).2] at cut
          rw [← cut, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hw), zero_mul]; exact zero_mem _
      · rw [ite_eq_right ht,mul_zero,mul_zero]; exact zero_mem _
  obtain ⟨d,hd'⟩ := H
  exact ⟨raw d, by simpa only [LinearMap.mulRight_apply,map_mul] using (congrArg raw hd').symm⟩

private theorem affine_cross_cancel (hQ : KLRSymm Q) (i : I) (r : Fin ℓ)
    (hr : s.lbl ⟨j,by omega⟩ = .inr r) (hi : s.lbl ⟨j+1,hj⟩ = .inl i)
    (z : A) (hz : z * c = 0) : z * p v = 0 := by
  have hi' : (v).lbl ⟨j,by omega⟩ = .inl i := by rw [lbl_sadj,sadj_apply_left hj,hi]
  have hr' : (v).lbl ⟨j+1,hj⟩ = .inr r := by rw [lbl_sadj,sadj_apply_right hj,hr]
  have sq := ψ_sq (Q := stendhalQ Q Λ) j hj v
  rw [hi',hr'] at sq
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, ncEval_x2, map_pow, rename_X,
    pol_X, Matrix.cons_val_zero] at sq
  have cr : e s * (ψ j * e v : R) = ψ j * e v := by
    rw [ψ_mul_e j v,sadj_smul_smul,← mul_assoc,e_mul_self]
  have sq' : (ψ j * e s : R) * (ψ j * e v) = e v * x ⟨j,by omega⟩ ^ Λ r i := by
    rw [mul_assoc,cr,← mul_assoc,sq,((show Commute (x ⟨j,by omega⟩ : R) (e v) from x_mul_e _ _).pow_left _).eq]
  apply affine_black_dot Q Λ hQ v ⟨j,by omega⟩ (by simp [hi']) (Λ r i) _
  · rw [mul_assoc,← map_mul,e_mul_self]
  · rw [mul_assoc,← map_pow,← map_mul,← sq',map_mul,← mul_assoc,hz,zero_mul]

/-- For a loading ideal, PBW division by a forced bottom crossing leaves its
coefficient in the *same* ideal. This applies in a surjective diagram quotient,
but the factorization itself is obtained before taking that quotient. -/
theorem exists_exitIdeal_factor {D : Type*} [Ring D] [Algebra k D] (F : A →ₐ[k] D)
    (hs : Function.Surjective F) (hQ : KLRSymm Q) (S : KLR.Seq μ → Prop)
    (hd : ∀ u, S u → ∀ w : Perm (Fin m), w • s = u → w ⟨j+1,hj⟩ < w ⟨j,by omega⟩)
    {z : D} (hz : z ∈ TwoSidedIdeal.span {d | ∃ u, S u ∧ d = F (p u)}) :
    ∃ y ∈ TwoSidedIdeal.span {d | ∃ u, S u ∧ d = F (p u)}, z * F (p s) = y * F c := by
  let J := TwoSidedIdeal.span {d | ∃ u, S u ∧ d = F (p u)}
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hz
  induction hz using AddSubgroup.closure_induction with
  | zero => exact ⟨0,J.zero_mem,by rw [zero_mul,zero_mul]⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x,hx,ex⟩ := hx; obtain ⟨y,hy,ey⟩ := hy
    exact ⟨x+y,J.add_mem hx hy,by rw [add_mul,add_mul,ex,ey]⟩
  | neg _ _ hx => obtain ⟨x,hx,ex⟩ := hx; exact ⟨-x,J.neg_mem hx,by rw [neg_mul,neg_mul,ex]⟩
  | mem _ hz =>
    obtain ⟨_,⟨l,-,_,⟨u,hu,rfl⟩,rfl⟩,b,-,rfl⟩ := hz
    obtain ⟨b,rfl⟩ := hs b
    obtain ⟨d,hd'⟩ := exit_descent_factor Q Λ s j hj hQ u (hd u hu) b
    refine ⟨l * F (p u) * F d,J.mul_mem_right _ _ (J.mul_mem_left _ _ (TwoSidedIdeal.subset_span ⟨u,hu,rfl⟩)),?_⟩
    have ecut : p u * (p u * b * p s) = p u * b * p s := by simp only [← mul_assoc,← map_mul raw,e_mul_self]
    simp only [mul_assoc,← map_mul F]; congr 1; apply congrArg F
    simpa only [mul_assoc] using (ecut.symm.trans (congrArg (p u * ·) hd'))

/-- A forced descent on every globally violated generator lets one remove a
red–black crossing in the violated quotient. The dot cancellation used in its
proof is only in the affine algebra of Proposition 6.4. -/
theorem viol_exit_cross_cancel (hQ : KLRSymm Q) (i : I) (r : Fin ℓ)
    (hr : s.lbl ⟨j,by omega⟩ = .inr r) (hi : s.lbl ⟨j+1,hj⟩ = .inl i)
    (hd : ∀ u : KLR.Seq μ, IsViolated u → ∀ w : Perm (Fin m), w • s = u → w ⟨j+1,hj⟩ < w ⟨j,by omega⟩)
    (z : V) (hz : z * mk c = 0) : z * mk (p v) = 0 := by
  obtain ⟨x,rfl⟩ := violMk_surjective z
  have h : x*c ∈ violIdeal k Q Λ ν := (violMk_eq_zero_iff _).1 (by rw [map_mul,hz])
  obtain ⟨d,hd',he⟩ := exists_exitIdeal_factor Q Λ s j hj (AlgHom.id k A) Function.surjective_id hQ IsViolated hd h
  change x*c*p s = d*c at he
  rw [mul_assoc,← map_mul raw,mul_assoc,e_mul_self] at he
  have h' := affine_cross_cancel Q Λ s j hj hQ i r hr hi (x-d) (by rw [sub_mul,he,sub_self])
  have zero : mk d = 0 := (violMk_eq_zero_iff _).2 hd'
  simpa only [map_mul,map_sub,zero,sub_zero,map_zero] using congrArg mk h'

end Categorification.Stendhal.BraidedStendhalAlgebra
