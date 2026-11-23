/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelCut

/-!
# Marked cuts at the two exits of a red–black–red triple

Webster, arXiv:1309.3796v2, §6.1, Definition 6.3 and the kernel test following
(6.21) in Lemma 6.8. At the exchanged bottom `b i a` there are two two-crossing
exits, with loadings `i a b` and `a b i`. The braid between the exits has no KLR
braid correction (the outer labels are distinct). If the mark is at `i a b`, not
above the braid, changing exits by a return crossing instead costs the red–black
bigon (4.2). These are relations in the balanced tensor of the higher submodule,
not cancellations of the dot power or assertions of injectivity on this column.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ' : List (Fin ℓ))
local notation "E" => redProj k Q Λ ν (redWord t)
local notation "F" => redProj k Q Λ ν κ'
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "B" => RedBlock.crossingSpace (k := k) (mk E) (mk F)
local notation "Z" => BalancedTensor k k T K B
local notation "lower" => blockKernelLowerClass Q Λ t κ'

/-- Act at the seam by the given crossing word in the source ordered corner. -/
def blockSeamWord (w : List ℕ) : T :=
  ⟨mk E * mk (raw (ψw w)) * mk E, mk (raw (ψw w)), rfl⟩

/-- Mark a diagram through a strictly higher loading, without quotienting it out. -/
def blockHigherMark (u : KLR.Seq μ) (hu : redWord u = redWord t)
    (hh : adjacentBlockRoot a b t < adjacentBlockRoot a b u) (z : A) : K :=
  blockKernelUpperClass Q Λ t a b ⟨z * raw (e u), by
    change mk (z * raw (e u)) ∈ blockUpperIdeal k Q Λ ν a b _ _
    rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span ⟨u,hu,hh,rfl⟩)⟩

local notation "act" => fun w => op (blockSeamWord Q Λ t w)
local notation "endAt" => fun (w : List ℕ) (s : KLR.Seq μ) => wordProd m w • s
local notation "leg" => fun (w : List ℕ) (s : KLR.Seq μ) => (ψw w * e s : R)

private theorem end_idem (w : List ℕ) (s : KLR.Seq μ) : (e (endAt w s) : R) * leg w s = leg w s := by
  rw [← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]

private theorem seamWord_lower (u v : List ℕ) (s : KLR.Seq μ)
    (hv : redWord (endAt v s) = redWord t) (y : A) :
    blockSeamWord Q Λ t u • lower (raw (leg v s) * y) = lower (raw (leg (u ++ v) s) * y) := by
  apply Subtype.ext
  have hy : E * raw (leg v s) = raw (leg v s) := by
    have h := congrArg raw (end_idem Q Λ v s)
    rw [map_mul] at h
    calc E * raw (leg v s) = E * (raw (e (endAt v s)) * raw (leg v s)) := congrArg (E * ·) h.symm
         _ = _ := by rw [← mul_assoc, redProj_mul_e, ite_eq_left hv, h]
  change (mk E * mk (raw (ψw u)) * mk E) * mk (E * (raw (leg v s) * y) * F) =
    mk (E * (raw (leg (u ++ v) s) * y) * F)
  have appendLeg : raw (leg (u ++ v) s) = raw (ψw u) * raw (leg v s) := by
    change raw (ψw (u ++ v) * e s) = _
    rw [ψw_append, mul_assoc, map_mul]
  rw [appendLeg, ← map_mul mk, ← map_mul mk, ← map_mul mk]
  simp only [← mul_assoc]
  rw [mul_assoc _ E E, (isIdempotentElem_redProj _).eq, mul_assoc _ E (raw (leg v s)), hy]

/-- Move a whole ordered prefix across the marked seam. Only the loading at the cut
has to be in the source order. The mark stays in `K` and the suffix below `s` is arbitrary. -/
theorem blockKernelWord_slide (x : K) (u v : List ℕ) (s : KLR.Seq μ)
    (hv : redWord (endAt v s) = redWord t) (y : A) :
    (BalancedTensor.tmul (act u • x) (lower (raw (leg v s) * y)) : Z) =
      BalancedTensor.tmul x (lower (raw (leg (u ++ v) s) * y)) := by
  rw [BalancedTensor.op_smul_tmul,seamWord_lower _ _ _ _ _ _ _ hv]

variable (s : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (hj : j+2 < (stendhalWeight ℓ ν).card)
local notation "l" => [j+1,j]
local notation "r" => [j,j+1]

private theorem local_braid (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) : leg ([j] ++ l) s = leg ([j+1] ++ r) s := by
  have hne : s.lbl ⟨j,by omega⟩ ≠ s.lbl ⟨j+2,hj⟩ := by
    intro eq
    have hab : b = a := Sum.inr_injective (hb.symm.trans (eq.trans ha))
    have hp := lbl_inj_of_inr s a (hab ▸ hb) ha
    have := congrArg Fin.val hp; simp at this
  have h := KLRAlgebra.braid (Q := stendhalQ Q Λ) j hj s
  rw [ite_eq_right (fun h => hne h.1), sub_mul, sub_eq_zero] at h
  simpa only [List.singleton_append, ψw_cons, ψw_nil, mul_one, mul_assoc] using h

/-- **Change of exit above a marked prefix** in the tensor of (6.21). At `b i a`
the legs end at different loadings. Balancing to the joint and using the exact braid
changes the cut without forgetting `x`. No common last crossing is chosen. -/
theorem blockKernelBraid_slide (x : K) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (hl : redWord (endAt l s) = redWord t)
    (hr : redWord (endAt r s) = redWord t) (y : A) :
    (BalancedTensor.tmul (act [j] • x) (lower (raw (leg l s) * y)) : Z) =
      BalancedTensor.tmul (act [j+1] • x) (lower (raw (leg r s) * y)) := by
  rw [blockKernelWord_slide _ _ _ _ _ _ _ _ _ _ hl, blockKernelWord_slide _ _ _ _ _ _ _ _ _ _ hr,
    local_braid Q Λ a b s j hj hb ha]

/-- In the projective tensor the joint coefficient is arbitrary. This is the
unmarked braid comparison used to detect independently marked exits in the first
black weight of Webster v2, Lemma 6.8, after (6.21). -/
theorem blockLoadingBraid_slide (u : rIdeal (orderedLoadingIdem Q Λ t)) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (hl : redWord (endAt l s) = redWord t)
    (hr : redWord (endAt r s) = redWord t) (y : A) :
    (BalancedTensor.tmul (act [j] • u) (lower (raw (leg l s) * y)) :
      BalancedTensor k k T (rIdeal (orderedLoadingIdem Q Λ t)) B) =
      BalancedTensor.tmul (act [j+1] • u) (lower (raw (leg r s) * y)) := by
  rw [BalancedTensor.op_smul_tmul,BalancedTensor.op_smul_tmul,seamWord_lower _ _ _ _ _ _ _ hl,
    seamWord_lower _ _ _ _ _ _ _ hr,local_braid Q Λ a b s j hj hb ha]

private theorem exit_bigon (i : I) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a) :
    leg (r ++ r) s = (KLRAlgebra.x ⟨j,by omega⟩ : R) ^ Λ a i * leg l s := by
  let h := endAt l s
  have h₀ : h.lbl ⟨j,by omega⟩ = .inl i := by
    change (sadj m (j+1) • sadj m j • s).lbl _ = _
    simp only [lbl_smul, sadj_inv]
    rw [sadj_apply_of_ne (k := j+1) (⟨j,by omega⟩ : Fin m) (by simp) (by dsimp; omega),
      sadj_apply_left (show j+1 < m by omega), hi]
  have h₁ : h.lbl ⟨j+1,by omega⟩ = .inr a := by
    change (sadj m (j+1) • sadj m j • s).lbl _ = _
    simp only [lbl_smul, sadj_inv]
    rw [sadj_apply_left hj, sadj_apply_of_ne _ (by simp; omega) (by simp), ha]
  have sq := KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) j (by omega) h
  rw [h₀,h₁] at sq
  simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, ncEval_x2, map_pow, MvPolynomial.rename_X,
    pol_X, Matrix.cons_val_zero] at sq
  calc leg (r ++ r) s = ψ j * leg ([j+1] ++ r) s := by simp only [List.cons_append, List.nil_append, ψw_cons, mul_assoc]
       _ = ψ j * ψ j * leg l s := by rw [← local_braid Q Λ a b s j hj hb ha]; simp only [List.singleton_append, ψw_cons, mul_assoc]
       _ = ψ j * ψ j * e h * leg l s := by rw [mul_assoc _ (e h), end_idem]
       _ = _ := by rw [sq, mul_assoc, end_idem]

/-- **Changing a mark at just the left exit**, Webster v2, (4.2), §6.1 and proof
after (6.21). Starting at `i a b` one can return to the joint and use the other exit.
The price is exactly `Λ a i` dots on the black strand on the left leg. The right
coefficient is obtained by acting on the *same kernel element*, even if `a b i`
is not higher. There is no division by the dots. -/
theorem blockKernelBigon_slide (x : K) (i : I) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a)
    (hr : redWord (endAt r s) = redWord t) (y : A) :
    (BalancedTensor.tmul x (lower (raw ((KLRAlgebra.x ⟨j,by omega⟩ : R) ^ Λ a i * leg l s) * y)) : Z) =
      BalancedTensor.tmul (act r • x) (lower (raw (leg r s) * y)) := by
  rw [blockKernelWord_slide _ _ _ _ _ _ _ _ _ _ hr, exit_bigon Q Λ a b s j hj i hb hi ha]

private theorem mark_val (u : KLR.Seq μ) (hu : redWord u = redWord t)
    (hu' : adjacentBlockRoot a b t < adjacentBlockRoot a b u) (z : A) :
    (blockHigherMark Q Λ t a b u hu hu' z).1.1.1 = mk (raw (e t) * z * raw (e u)) := by
  change (blockLoadingRep Q Λ t (mk (z * raw (e u)))).1.1 = _
  rw [blockLoadingRep_val]; simp only [← map_mul mk, mul_assoc, e_mul_redProj, ite_eq_left hu]

private theorem mark_cross (u v : KLR.Seq μ) (c : ℕ) (eq : v = sadj m c • u) (hu : redWord u = redWord t)
    (hv : redWord v = redWord t) (hu' : adjacentBlockRoot a b t < adjacentBlockRoot a b u)
    (hv' : adjacentBlockRoot a b t < adjacentBlockRoot a b v) (z : A) :
    act [c] • blockHigherMark Q Λ t a b v hv hv' z =
      blockHigherMark Q Λ t a b u hu hu' (z * raw (ψ c)) := by
  subst v
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  change (blockHigherMark Q Λ t a b _ hv hv' z).1.1.1 * (mk E * mk (raw (ψw [c])) * mk E) =
    (blockHigherMark Q Λ t a b u hu hu' _).1.1.1
  have xId : raw (e (sadj m c • u)) * raw (ψ c) = raw (ψ c) * raw (e u) :=
    (map_mul raw _ _).symm.trans ((congrArg raw (ψ_mul_e (Q := stendhalQ Q Λ) c u).symm).trans (map_mul raw _ _))
  simp only [mark_val, ← map_mul mk, ψw_cons, ψw_nil, mul_one, ← mul_assoc]
  rw [mul_assoc _ (raw (e (sadj m c • u))) E, e_mul_redProj, ite_eq_left hv,
    mul_assoc _ (raw (e (sadj m c • u))) (raw (ψ c)), xId]
  simp only [mul_assoc, e_mul_redProj, ite_eq_left hu]

/-- Moving a black one place left across a red cannot lower a retained boundary
count. Used at the right exit of the cut following Webster v2, (6.21). -/
theorem adjacentBlockRoot_le_left_cross (u : KLR.Seq μ) (c : ℕ) (hc : c+1 < m) (r₀ : Fin ℓ) (i : I)
    (hr : u.lbl ⟨c,Nat.lt_of_succ_lt hc⟩ = .inr r₀) (hi : u.lbl ⟨c+1,hc⟩ = .inl i) :
    adjacentBlockRoot a b u ≤ adjacentBlockRoot a b (sadj m c • u) := by
  intro label color
  unfold adjacentBlockRoot blockBlackCount
  refine Finset.card_le_card_of_injOn (sadj m c) ?_ (sadj m c).injective.injOn
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, lbl_sadj, TypeA.sadj_sadj_apply] at hx ⊢
  refine ⟨hx.1, fun y r' hr' hy => ?_⟩
  simpa only [TypeA.sadj_sadj_apply] using sadj_lt_sadj hc hr hi hx.1 hy (hx.2 _ r' hr' hy)

/-- **Re-marking the undotted braid from its right exit** (Webster v2, §6.1, proof
after (6.21)). Only `a b i` is assumed strictly higher; moving the black left makes
the joint `a i b` and then the other exit `i a b` higher for the retained cuts.
The two upper factors use these exit idempotents on an arbitrary diagram `z`, not
an assumed common element of the higher submodule. -/
theorem blockKernelHigherExit_slide (i : I) (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a)
    (hr : redWord (endAt r s) = redWord t) (higher : adjacentBlockRoot a b t < adjacentBlockRoot a b (endAt r s))
    (z y : A) : ∃ (hl : redWord (endAt l s) = redWord t) (hh : adjacentBlockRoot a b t < adjacentBlockRoot a b (endAt l s)),
      (BalancedTensor.tmul (blockHigherMark Q Λ t a b (endAt l s) hl hh (z * raw (ψ j)))
        (lower (raw (leg l s) * y)) : Z) = BalancedTensor.tmul
          (blockHigherMark Q Λ t a b (endAt r s) hr higher (z * raw (ψ (j+1)))) (lower (raw (leg r s) * y)) := by
  let v := endAt r s
  let u := sadj m (j+1) • v
  have he : u = sadj m j • endAt l s := by
    simpa only [u,v,wordProd_cons,wordProd_nil,mul_one,mul_smul] using (braid_smul hj s).symm
  have b₁ : v.lbl ⟨j+1,by omega⟩ = .inr b := by
    change (sadj m j • sadj m (j+1) • s).lbl _ = _
    simp only [lbl_sadj, sadj_apply_right (show j+1 < m by omega)]
    rw [sadj_apply_of_ne _ (by simp) (by dsimp; omega), hb]
  have i₂ : v.lbl ⟨j+2,hj⟩ = .inl i := by
    change (sadj m j • sadj m (j+1) • s).lbl _ = _
    simp only [lbl_sadj]; rw [sadj_apply_of_ne (k := j) (⟨j+2,hj⟩ : Fin m) (by simp) (by simp), sadj_apply_right hj, hi]
  have u₀ : u.lbl ⟨j,by omega⟩ = .inr a := by rw [he]; exact (braid_smul_apply_zero hj s).trans ha
  have u₁ : u.lbl ⟨j+1,by omega⟩ = .inl i := by rw [he]; exact (braid_smul_apply_one hj s).trans hi
  have fromU : sadj m j • u = endAt l s := by rw [he, sadj_smul_smul]
  have hu : redWord u = redWord t := (redWord_sadj_smul v hj (by simp [i₂])).trans hr
  have hu' : adjacentBlockRoot a b t < adjacentBlockRoot a b u := higher.trans_le (adjacentBlockRoot_le_left_cross a b v (j+1) hj b i b₁ i₂)
  have hl : redWord (endAt l s) = redWord t := fromU ▸ (redWord_sadj_smul u (by omega) (by simp [u₁])).trans hu
  have hh : adjacentBlockRoot a b t < adjacentBlockRoot a b (endAt l s) :=
    fromU ▸ hu'.trans_le (adjacentBlockRoot_le_left_cross a b u j (by omega) a i u₀ u₁)
  let x := blockHigherMark Q Λ t a b u hu hu' z
  refine ⟨hl,hh,?_⟩
  have H := blockKernelBraid_slide Q Λ t a b κ' s j hj x hb ha hl hr y
  rw [show act [j] • x = _ from mark_cross Q Λ t a b _ u j he hl hu hh hu' z,
    show act [j+1] • x = _ from mark_cross Q Λ t a b v u (j+1) rfl hr hu higher hu' z] at H
  exact H

end Categorification.Stendhal.BraidedStendhalAlgebra
