/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicWordRestriction
import Categorification.WeightedKLR.RedStrands.TensorWordProjectives
import Categorification.WeightedKLR.RedStrands.StendhalCyclotomicParameters
import Categorification.KLR.CyclotomicRepeatedDimension
import LieLean.Algebra.QuantumGroup.CrystalBasis.TensorIntegrable

/-!
# Deleting black letters from an ordered tensor word

Webster, arXiv:1309.3796v2, Lemmas 4.35–4.36 and the vectors before Lemma 4.36.
On ordinary word vectors the coproduct raising operator deletes each occurrence
of its black colour with the quantum integer of the prefix weight. The formula
uses the same marked positions and Laurent coefficients as cyclotomic restriction.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra KL2 KLGamma QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "L" => RatFunc ℚ
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable {I J Y : Type*} [DecidableEq I] [AddCommGroup Y] {C : CartanDatum I}
    {R : C.toLusztig.RootDatum Y} {ℓ n : ℕ}

private def appendHighest (wt : Fin (n+1) → Dom R) :
    TensorSpace (fun j : Fin n => wt j.castSucc) →ₗ[L] TensorSpace wt :=
  (tensorSplitLast wt).symm.toLinearMap.comp ((TensorProduct.mk L _ _).flip
    (IrreducibleModule.hwv R v (wt (Fin.last n)).1))

private theorem E_appendHighest (wt : Fin (n+1) → Dom R) (i : I)
    (x : TensorSpace (fun j : Fin n => wt j.castSucc)) :
    tensorRepresentation wt (E R v i) (appendHighest wt x) =
      appendHighest wt (tensorRepresentation (fun j => wt j.castSucc) (E R v i) x) := by
  change tensorRepresentation wt _ (appendTensor wt x _) = _
  rw [tensorRepresentation_E_append, IrreducibleModule.E_smul_hwv]
  simp only [appendTensor, TensorProduct.tmul_zero, map_zero, add_zero]
  rfl

private def readReverse : (s : List (I ⊕ J)) → {n : ℕ} →
    (wt : Fin n → Dom R) → TensorSpace wt
  | [], 0, wt => tensorWordVector .empty wt
  | [], _+1, _ => 0
  | .inl i :: s, _, wt => tensorRepresentation wt (F R v i) (readReverse s wt)
  | .inr _ :: _, 0, _ => 0
  | .inr _ :: s, _+1, wt => appendHighest wt (readReverse s (fun j => wt j.castSucc))

/-- Read an ordinary loading in strand order, appending a highest vector at
each red letter and applying an ordinary lowering at each black letter. -/
def loadingVector (wt : Fin n → Dom R) (s : List (I ⊕ J)) : TensorSpace wt :=
  readReverse s.reverse wt

private theorem read_black (wt : Fin n → Dom R) (s : List (I ⊕ J)) (i : I) :
    loadingVector wt (s ++ [.inl i]) = tensorRepresentation wt (F R v i) (loadingVector wt s) := by
  simp [loadingVector, readReverse]

private theorem read_red (wt : Fin (n+1) → Dom R) (s : List (I ⊕ J)) (r : J) :
    loadingVector wt (s ++ [.inr r]) =
      appendHighest wt (loadingVector (fun j => wt j.castSucc) s) := by
  simp [loadingVector, readReverse]

private theorem read_relabel {J' : Type*} (f : J → J') (wt : Fin n → Dom R) (s : List (I ⊕ J)) :
    loadingVector wt (s.map (Sum.map id f)) = loadingVector wt s := by
  induction s using List.reverseRecOn generalizing n with
  | nil => cases n <;> rfl
  | append_singleton s z ih =>
    cases z with
    | inl i => simp [read_black, ih]
    | inr r =>
      cases n with
      | zero => simp [loadingVector, readReverse]
      | succ n => simp [read_red, ih]

private theorem read_replicate (wt : Fin n → Dom R) (s : List (I ⊕ J)) (i : I) (a : ℕ) :
    loadingVector wt (s ++ List.replicate a (.inl i)) =
      tensorRepresentation wt (F R v i ^ a) (loadingVector wt s) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ', ← List.append_assoc, read_black, ih, pow_succ', map_mul,
      Module.End.mul_apply]

/-- Reading the expanded blocks of a tensor word gives its prescribed ordinary
word vector, including blocks with zero or repeated letters. -/
theorem loadingVector_expand : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R),
    loadingVector wt (expandDiv w.blocks) = tensorWordUndivided w wt
  | _, .empty, _ => rfl
  | n+1, .red w, wt => by
    have hs : expandDiv w.red.blocks = (expandDiv w.blocks).map (addRedColor n) ++ [.inr (Fin.last n)] := by
      simp [TensorWord.blocks, expandDiv, List.flatMap_map, List.map_flatMap]
    rw [hs, read_red]
    change appendHighest wt (loadingVector _ ((expandDiv w.blocks).map (Sum.map id Fin.castSucc))) = _
    rw [read_relabel, loadingVector_expand w]
    rfl
  | _, .black w i a, wt => by
    have hs : expandDiv (w.black i a).blocks = expandDiv w.blocks ++ List.replicate a (.inl i) := by
      simp [TensorWord.blocks, expandDiv]
    rw [hs, read_replicate, loadingVector_expand w]
    rfl

omit [DecidableEq I] in
private theorem reds_relabel {J' : Type*} (f : J → J') (s : List (I ⊕ J)) :
    (s.map (Sum.map id f)).filterMap Sum.getRight? = (s.filterMap Sum.getRight?).map f := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simpa [List.filterMap, Sum.getRight?] using ih

omit [DecidableEq I] in
/-- The expanded blocks of a tensor word contain each red index once in its
prescribed position in the red subsequence. -/
theorem TensorWord.filterMap_reds : ∀ {n : ℕ} (w : TensorWord I n),
    (expandDiv w.blocks).filterMap Sum.getRight? = List.ofFn id
  | _, .empty => rfl
  | n+1, .red w => by
    have hs : expandDiv w.red.blocks = (expandDiv w.blocks).map (addRedColor n) ++ [.inr (Fin.last n)] := by
      simp [TensorWord.blocks, expandDiv, List.flatMap_map, List.map_flatMap]
    rw [hs, List.filterMap_append, reds_relabel, TensorWord.filterMap_reds w, List.ofFn_succ' (n := n)]
    simp [List.filterMap, Sum.getRight?, List.map_ofFn, List.concat_eq_append]
  | _, .black w i a => by
    have hs : expandDiv (w.black i a).blocks = expandDiv w.blocks ++ List.replicate a (.inl i) := by
      simp [TensorWord.blocks, expandDiv]
    rw [hs, List.filterMap_append, TensorWord.filterMap_reds w]
    simp [List.filterMap_replicate]

private def loadingWeight (wts : J → Dom R) (s : List (I ⊕ J)) : Y →+ ℤ :=
  (s.map (Sum.elim (fun j => -R.root j) (fun r => (wts r).1))).sum

omit [DecidableEq I] in
private theorem reds_snoc {s : List (I ⊕ J)} {r : J} {slot : Fin (n+1) → J}
    (hr : (s ++ [(Sum.inr r : I ⊕ J)]).filterMap Sum.getRight? = List.ofFn slot) :
    s.filterMap Sum.getRight? = List.ofFn (fun j => slot j.castSucc) ∧ r = slot (Fin.last n) := by
  rw [List.ofFn_succ', List.concat_eq_append] at hr
  simpa [List.filterMap, Sum.getRight?, List.append_inj] using hr

private theorem torus_loading (wts : J → Dom R) (s : List (I ⊕ J)) {n : ℕ} (slot : Fin n → J)
    (hr : s.filterMap Sum.getRight? = List.ofFn slot) (a : Y) :
    tensorRepresentation (fun j => wts (slot j)) (K R v a) (loadingVector (fun j => wts (slot j)) s) =
      v ^ (loadingWeight wts s) a • loadingVector (fun j => wts (slot j)) s := by
  induction s using List.reverseRecOn generalizing n a with
  | nil =>
    cases n with
    | zero =>
      simp [tensorRepresentation, loadingWeight]
    | succ n => simp [loadingVector, readReverse]
  | append_singleton s z ih =>
    cases z with
    | inl i =>
      rw [read_black]
      let wt := fun j => wts (slot j)
      let : Module (LieLean.QuantumGroup R v) (TensorSpace wt) :=
        Module.compHom _ (tensorRepresentation wt).toRingHom
      let : IsScalarTower L (LieLean.QuantumGroup R v) (TensorSpace wt) :=
        ⟨fun c u x => by change tensorRepresentation wt (c • u) x = c • tensorRepresentation wt u x
                         rw [map_smul, LinearMap.smul_apply]⟩
      have hw : loadingVector wt s ∈ weightSpace R v (TensorSpace wt) (loadingWeight wts s) :=
        fun y => ih slot (by simpa [List.filterMap, Sum.getRight?] using hr) y
      have H := F_smul_mem_weightSpace hw i a
      change tensorRepresentation wt (K R v a) (tensorRepresentation wt (F R v i) _) =
        v ^ (loadingWeight wts s - R.root i) a • tensorRepresentation wt (F R v i) _ at H
      simpa [loadingWeight, sub_eq_add_neg, wt] using H
    | inr r =>
      cases n with
      | zero => simp [loadingVector, readReverse]
      | succ n =>
        obtain ⟨hs, rfl⟩ := reds_snoc hr
        rw [read_red]
        change tensorRepresentation _ _ (appendTensor _ _ _) = _
        rw [tensorRepresentation_K_append, ih _ hs a, IrreducibleModule.hwv_mem_weightSpace]
        simp [appendTensor, appendHighest, loadingWeight, zpow_add₀ (show v ≠ 0 from RatFunc.X_ne_zero),
          TensorProduct.smul_tmul', smul_smul, mul_comm]
        rw [← TensorProduct.smul_tmul', map_smul]

private theorem commute_black (wt : Fin n → Dom R) (i j : I) (x : TensorSpace wt)
    (μ : Y →+ ℤ) (hx : ∀ a, tensorRepresentation wt (K R v a) x = v ^ μ a • x) :
    tensorRepresentation wt (E R v i) (tensorRepresentation wt (F R v j) x) =
      tensorRepresentation wt (F R v j) (tensorRepresentation wt (E R v i) x) +
      if i = j then qIntZ (v ^ C.toLusztig.d i) (μ (R.coroot i)) • x else 0 := by
  let : Module (LieLean.QuantumGroup R v) (TensorSpace wt) :=
    Module.compHom _ (tensorRepresentation wt).toRingHom
  let : IsScalarTower L (LieLean.QuantumGroup R v) (TensorSpace wt) :=
    ⟨fun c u z => by change tensorRepresentation wt (c • u) z = c • tensorRepresentation wt u z
                     rw [map_smul, LinearMap.smul_apply]⟩
  have hw : x ∈ weightSpace R v (TensorSpace wt) μ := hx
  change E R v i • F R v j • x = F R v j • E R v i • x + _
  rw [add_comm, ← sub_eq_iff_eq_add, ← mul_smul, ← mul_smul, ← sub_smul, E_mul_F_sub]
  by_cases h : i = j
  · subst j
    simp only [↓reduceIte]
    rw [smul_assoc, sub_smul, Kt_smul_of_mem_weightSpace hw,
      K_neg_ktilde_smul_of_mem_weightSpace hw, ← sub_smul, smul_smul, qIntZ, div_eq_inv_mul]
  · simp [h]

private def deleteTerm [DecidableEq J] (wts : J → Dom R) (wt : Fin n → Dom R) (i : I)
    (t : List (I ⊕ J) × (I ⊕ J) × List (I ⊕ J)) : TensorSpace wt :=
  if Sum.inl i = t.2.1 then qIntZ (v ^ C.toLusztig.d i) ((loadingWeight wts t.1) (R.coroot i)) •
    loadingVector wt (t.1 ++ t.2.2) else 0

private theorem raise_loading [DecidableEq J] (wts : J → Dom R) (i : I) (s : List (I ⊕ J))
    {n : ℕ} (slot : Fin n → J) (hr : s.filterMap Sum.getRight? = List.ofFn slot) :
    tensorRepresentation (fun j => wts (slot j)) (E R v i) (loadingVector (fun j => wts (slot j)) s) =
      ((CycKLR.markedWords s).map (deleteTerm wts (fun j => wts (slot j)) i)).sum := by
  induction s using List.reverseRecOn generalizing n with
  | nil =>
    cases n <;> simp [CycKLR.markedWords, loadingVector, readReverse, tensorRepresentation]
  | append_singleton s z ih =>
    rw [CycKLR.markedWords_append, List.map_append, List.sum_append, List.map_map,
      List.map_singleton, List.sum_singleton]
    cases z with
    | inl j =>
      have hs : s.filterMap Sum.getRight? = List.ofFn slot := by
        simpa [List.filterMap, Sum.getRight?] using hr
      rw [read_black, commute_black _ _ _ _ (loadingWeight wts s) (torus_loading wts s slot hs),
        ih slot hs, map_list_sum, List.map_map]
      congr 1
      · apply congrArg List.sum
        apply List.map_congr_left
        intro t _
        by_cases h : Sum.inl i = t.2.1 <;>
          simp [deleteTerm, h, ← List.append_assoc, read_black]
      · simp [deleteTerm]
    | inr r =>
      cases n with
      | zero => simp [List.filterMap, Sum.getRight?, List.ofFn_zero] at hr
      | succ n =>
        obtain ⟨hs, rfl⟩ := reds_snoc hr
        rw [read_red, E_appendHighest, ih _ hs, map_list_sum, List.map_map]
        simp only [deleteTerm, reduceCtorEq, ↓reduceIte, add_zero]
        apply congrArg List.sum
        apply List.map_congr_left
        intro t _
        by_cases h : Sum.inl i = t.2.1 <;>
          simp [deleteTerm, h, ← List.append_assoc, read_red]

omit [DecidableEq I] in
private theorem prefixPair_weight (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hw : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (i : I) (s : List (I ⊕ Fin ℓ)) :
    CycKLR.prefixPair (extendedCartanDatum C Λ) (Sum.elim (fun _ => 0) (fun _ => 1))
      (.inl i) s = (loadingWeight wt s) (R.coroot i) := by
  induction s with
  | nil => simp [CycKLR.prefixPair, loadingWeight]
  | cons a s ih =>
    simp only [CycKLR.prefixPair, Sum.elim_inl, Nat.cast_zero, zero_sub, loadingWeight] at ih ⊢
    simp only [List.map_cons, List.sum_cons, AddMonoidHom.add_apply, neg_add_rev, ih]
    cases a with
    | inl j =>
      simp only [Sum.elim_inl, AddMonoidHom.neg_apply, R.root_coroot]
      change _ + (-C.toLusztig.cartanMatrix i j) = _
      apply add_comm
    | inr r => rw [cover_black_red, neg_neg, hw]; exact add_comm _ _

omit [DecidableEq I] in
private theorem coefficient_eval (i : I) (m : ℤ) :
    qToV (qIntU (qUnitLP ^ di C i) m) = qIntZ (v ^ C.toLusztig.d i) m := by
  rw [CycKLR.qIntU_eval (di_pos C i)]
  have h : di C i = (C.toLusztig.d i : ℤ) := by
    have h₁ := two_mul_di C i
    have h₂ := C.toLusztig.two_mul_d i
    change 2 * (C.toLusztig.d i : ℤ) = C.dot i i at h₂
    omega
  rw [h, zpow_natCast]
  change qIntZ ((v⁻¹) ^ C.toLusztig.d i) m = _
  rw [inv_pow, IntegrableSl2.qIntZ_inv]

/-- Webster, Lemmas 4.35–4.36, raising on an ordered undivided loading. Each matching
black letter contributes the quantum integer of its prefix times the vector with that
letter removed. Positions and Laurent coefficients agree with cyclotomic restriction
of a sequence projective, including the inverse grading parameter. -/
theorem tensorRepresentation_E_loading (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hw : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (i : I) (s : List (I ⊕ Fin ℓ))
    (hr : s.filterMap Sum.getRight? = List.ofFn id) :
    tensorRepresentation wt (E R v i) (loadingVector wt s) =
      ((CycKLR.markedWords s).map (fun t => if Sum.inl i = t.2.1 then
        qToV (qIntU (qUnitLP ^ di (extendedCartanDatum C Λ) (.inl i))
          (CycKLR.prefixPair (extendedCartanDatum C Λ) (Sum.elim (fun _ => 0) (fun _ => 1))
            (.inl i) t.1)) • loadingVector wt (t.1 ++ t.2.2) else 0)).sum := by
  refine (raise_loading wt i s id hr).trans ?_
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  change deleteTerm wt wt i t = if _ then qToV (qIntU (qUnitLP ^ di C i) _) • _ else _
  rw [coefficient_eval, prefixPair_weight Λ wt hw]
  rfl

end Categorification.Stendhal.FirstWeight
