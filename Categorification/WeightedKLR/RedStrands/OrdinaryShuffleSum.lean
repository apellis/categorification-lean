/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShuffleRecurrence
import Categorification.WeightedKLR.RedStrands.OrdinaryShuffleMasks

/-!
# The ordinary tensor shuffle as a sum over masks

Webster, arXiv:1309.3796v2, §4.6–4.7 and (5.10). After the final red strand,
each ordinary black letter can be assigned to either tensor factor. This is a finite
sum indexed by the subsets of suffix positions, so repeated colours retain their
multiplicity. A left assignment uses the final factor's current weight.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {m : ℕ}

/-- Apply the ordinary lowering operators of a list in loading order. -/
def ordinarySuffixOp {V : Type*} [AddCommGroup V] [Module L V]
    (act : I → Module.End L V) : List I → Module.End L V
  | [] => 1
  | i :: s => ordinarySuffixOp act s * act i

/-- Exponent of a suffix mask, with the current weight of the final factor
updated at every right assignment. -/
def suffixMaskExponent (R : D.RootDatum Y) (μ : Y →+ ℤ) : List (I × Bool) → ℤ
  | [] => 0
  | (i, true) :: t => suffixMaskExponent R (μ - R.root i) t
  | (i, false) :: t => μ (ktilde R i) + suffixMaskExponent R μ t

omit [DecidableEq I] in
/-- The exponent increment for the next letter is zero for the final factor; on the
earlier factor it is the symmetrized coroot pairing with the remaining final weight. -/
theorem suffixMaskExponent_snoc (R : D.RootDatum Y) (μ : Y →+ ℤ) (t : List (I × Bool))
    (i : I) (b : Bool) :
    suffixMaskExponent R μ (t ++ [(i,b)]) = suffixMaskExponent R μ t +
      if b then 0 else (μ - ((maskSubword true t).map R.root).sum) (ktilde R i) := by
  induction t generalizing μ with
  | nil => cases b <;> simp [suffixMaskExponent, maskSubword]
  | cons z t ih =>
    rcases z with ⟨j,c⟩
    cases c <;> cases b <;> simp [suffixMaskExponent, maskSubword, ih, AddMonoidHom.sub_apply,
      AddMonoidHom.add_apply] <;> abel

variable (wt : Fin (m+1) → Dom R)
local notation "wt₀" => fun j : Fin m => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last m)))
local notation "A₀" => fun i => barTensorRepresentation wt₀ (F R v i)
local notation "A₁" => fun i => Algebra.lsmul L L V₁ (F R v i)
local notation "A" => fun i => barTensorRepresentation wt (F R v i)

/-- The contribution from a single suffix mask to the bar coproduct of an ordinary word. -/
def suffixMaskTerm (x : V₀) (y : V₁) (μ : Y →+ ℤ) (t : List (I × Bool)) : TensorSpace wt :=
  v ^ suffixMaskExponent R μ t • appendTensor wt
    (ordinarySuffixOp A₀ (maskSubword false t) x)
    (ordinarySuffixOp A₁ (maskSubword true t) y)

private theorem suffixMaskTerm_false (i : I) (t : List (I × Bool)) (x : V₀) (y : V₁) (μ : Y →+ ℤ) :
    suffixMaskTerm wt x y μ ((i,false)::t) =
      v ^ μ (ktilde R i) • suffixMaskTerm wt (barTensorRepresentation wt₀ (F R v i) x) y μ t := by
  simp [suffixMaskTerm, maskSubword, suffixMaskExponent, ordinarySuffixOp, smul_smul,
    zpow_add₀ (show v ≠ 0 from RatFunc.X_ne_zero)]

private theorem suffixMaskTerm_true (i : I) (t : List (I × Bool)) (x : V₀) (y : V₁) (μ : Y →+ ℤ) :
    suffixMaskTerm wt x y μ ((i,true)::t) =
      suffixMaskTerm wt x (F R v i • y) (μ - R.root i) t := by
  simp [suffixMaskTerm, maskSubword, suffixMaskExponent, ordinarySuffixOp, Algebra.lsmul]

/-- Webster, arXiv:1309.3796v2, (5.10), iterated ordinary lowering on the two factors.
Each term is the tensor of the two masked subwords times its weight monomial. -/
theorem ordinarySuffix_eq_sum_masks (x : V₀) (y : V₁) (μ : Y →+ ℤ)
    (hy : y ∈ weightSpace R v V₁ μ) (s : List I) :
    ordinarySuffixOp A s (appendTensor wt x y) =
      ∑ b : Fin s.length → Bool, suffixMaskTerm wt x y μ (tagMask s b) := by
  classical
  induction s generalizing μ x y with
  | nil => simp [ordinarySuffixOp, suffixMaskTerm, tagMask, maskSubword, suffixMaskExponent]
  | cons i s ih =>
    rw [ordinarySuffixOp, Module.End.mul_apply, barTensorRepresentation_F_append wt i x y hy,
      map_add, map_smul, ih _ _ _ hy, ih _ _ _ (F_smul_mem_weightSpace hy i), Finset.smul_sum]
    let f (b : Fin (s.length+1) → Bool) := suffixMaskTerm wt x y μ (tagMask (i::s) b)
    change _ = ∑ b, f b
    rw [← (Fin.consEquiv (fun _ : Fin (s.length+1) => Bool)).sum_comp f, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Fin.consEquiv, Equiv.coe_fn_mk, f, tagMask_cons,
      suffixMaskTerm_false, suffixMaskTerm_true]
    abel

/-- The earlier tensor word and the ordinary black suffix of a loading after its last red. -/
def lastRedWord : TensorWord I (m+1) → TensorWord I m × List I
  | .red w => (w, [])
  | .black w i n => ((lastRedWord w).1, (lastRedWord w).2 ++ List.replicate n i)

omit [DecidableEq I] in
private theorem suffixOp_append {V : Type*} [AddCommGroup V] [Module L V]
    (act : I → Module.End L V) (s t : List I) :
    ordinarySuffixOp act (s ++ t) = ordinarySuffixOp act t * ordinarySuffixOp act s := by
  induction s with
  | nil => simp [ordinarySuffixOp]
  | cons i s ih => simp [ordinarySuffixOp, ih, mul_assoc]

omit [DecidableEq I] in
private theorem suffixOp_replicate {V : Type*} [AddCommGroup V] [Module L V]
    (act : I → Module.End L V) (i : I) (n : ℕ) :
    ordinarySuffixOp act (List.replicate n i) = act i ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ordinarySuffixOp, ih, pow_succ]

private theorem lastRedWord_apply :
    ∀ w : TensorWord I (m+1), barOrdinaryWord w wt =
      ordinarySuffixOp A (lastRedWord w).2 (appendTensor wt (barOrdinaryWord (lastRedWord w).1 wt₀)
        (IrreducibleModule.hwv R v (wt (Fin.last m)).1))
  | .red w => by simp [barOrdinaryWord, lastRedWord, ordinarySuffixOp]
  | .black w i n => by
    rw [barOrdinaryWord, lastRedWord_apply w, lastRedWord, suffixOp_append, suffixOp_replicate,
      map_pow, Module.End.mul_apply]

/-- The ordinary tensor-word vector in Webster's bar coproduct is the sum over all
assignments of the letters after the last red strand (arXiv:1309.3796v2, (5.10)). -/
theorem barOrdinaryWord_eq_sum_masks (w : TensorWord I (m+1)) :
    barOrdinaryWord w wt =
      ∑ b : Fin (lastRedWord w).2.length → Bool,
        suffixMaskTerm wt (barOrdinaryWord (lastRedWord w).1 wt₀)
          (IrreducibleModule.hwv R v (wt (Fin.last m)).1) (wt (Fin.last m)).1
          (tagMask (lastRedWord w).2 b) := by
  rw [lastRedWord_apply]
  exact ordinarySuffix_eq_sum_masks wt _ _ _ IrreducibleModule.hwv_mem_weightSpace _

end Categorification.Stendhal.FirstWeight
