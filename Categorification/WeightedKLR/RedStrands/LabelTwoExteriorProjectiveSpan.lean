/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoOutgoingRows
import Categorification.WeightedKLR.RedStrands.LoadingCutPBW

/-!
# Spanning the complementary exterior projective

Webster, arXiv:1309.3796v2, §8.2, printed page 80. At each of the three
ordered nonviolated loadings, there are two reduced words from the
exterior cut. The black crossing reduces both words to the direct
shuffle on the undotted and first-dot generator span.
-/

namespace Categorification.Stendhal
open KLR TypeA

noncomputable section

local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card μ
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "C" => labelTwoExteriorLeftLoading

private def exteriorWord (j : Fin 6) : List ℕ := ![[], [1], [2], [2,1], [1,2], [1,2,1]] j

private theorem exteriorWord_reduced (j : Fin 6) : IsReduced m (exteriorWord j) := by
  refine ⟨?_,?_⟩
  · intro i hi
    have h : (exteriorWord j).all (fun a => decide (a + 1 < m)) = true := by
      fin_cases j <;> decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp h i hi)
  · rw [length_eq_invCount]
    fin_cases j <;> decide +kernel

private theorem exteriorWord_prod_injective : Function.Injective (fun j : Fin 6 =>
    wordProd m (exteriorWord j)) := by
  have h : ∀ i j : Fin 6, wordProd m (exteriorWord i) = wordProd m (exteriorWord j) → i = j := by
    decide +kernel
  exact fun _ _ => h _ _

/-- Reduced representatives chosen so each endpoint transport either uses the
direct shuffle or begins with the black crossing in the exterior loading. -/
def labelTwoExteriorPBWChoice (w : Equiv.Perm (Fin m)) : List ℕ := by
  classical
  exact if h : ∃ j : Fin 6, wordProd m (exteriorWord j) = w then exteriorWord (Classical.choose h)
    else canWord m w

private theorem labelTwoExteriorPBWChoice_word (j : Fin 6) :
    labelTwoExteriorPBWChoice (wordProd m (exteriorWord j)) = exteriorWord j := by
  classical
  have h : ∃ i : Fin 6, wordProd m (exteriorWord i) = wordProd m (exteriorWord j) := ⟨j,rfl⟩
  unfold labelTwoExteriorPBWChoice
  rw [dite_eq_left h]
  exact congrArg exteriorWord (exteriorWord_prod_injective (Classical.choose_spec h))

theorem labelTwoExteriorPBWChoice_spec (w : Equiv.Perm (Fin m)) :
    IsReduced m (labelTwoExteriorPBWChoice w) ∧ wordProd m (labelTwoExteriorPBWChoice w) = w := by
  classical
  unfold labelTwoExteriorPBWChoice
  split_ifs with h
  · exact ⟨exteriorWord_reduced _, Classical.choose_spec h⟩
  · exact ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩

theorem labelTwoExteriorPBWChoice_left (w : Equiv.Perm (Fin m)) (hw : w • C = C) :
    labelTwoExteriorPBWChoice w = [] ∨ labelTwoExteriorPBWChoice w = [1] := by
  have h : ∀ u : Equiv.Perm (Fin m), u • C = C →
      u = wordProd m (exteriorWord 0) ∨ u = wordProd m (exteriorWord 1) := by decide +kernel
  rcases h w hw with h | h
  · exact Or.inl (h ▸ labelTwoExteriorPBWChoice_word 0)
  · exact Or.inr (h ▸ labelTwoExteriorPBWChoice_word 1)

theorem labelTwoExteriorPBWChoice_middle (w : Equiv.Perm (Fin m)) (hw : w • C = B) :
    labelTwoExteriorPBWChoice w = [2] ∨ labelTwoExteriorPBWChoice w = [2,1] := by
  have h : ∀ u : Equiv.Perm (Fin m), u • C = B →
      u = wordProd m (exteriorWord 2) ∨ u = wordProd m (exteriorWord 3) := by decide +kernel
  rcases h w hw with h | h
  · exact Or.inl (h ▸ labelTwoExteriorPBWChoice_word 2)
  · exact Or.inr (h ▸ labelTwoExteriorPBWChoice_word 3)

theorem labelTwoExteriorPBWChoice_terminal (w : Equiv.Perm (Fin m)) (hw : w • C = A) :
    labelTwoExteriorPBWChoice w = [1,2] ∨ labelTwoExteriorPBWChoice w = [1,2,1] := by
  have h : ∀ u : Equiv.Perm (Fin m), u • C = A →
      u = wordProd m (exteriorWord 4) ∨ u = wordProd m (exteriorWord 5) := by decide +kernel
  rcases h w hw with h | h
  · exact Or.inl (h ▸ labelTwoExteriorPBWChoice_word 4)
  · exact Or.inr (h ▸ labelTwoExteriorPBWChoice_word 5)

end
end Categorification.Stendhal

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card μ
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "H" => KLRAlgebra k S μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "p" => labelTwoLeftExteriorProjector param
local notation "u" => (π X₁ * p)

private theorem proj_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR, map_mul]

private theorem proj_add (a b : H) : π (a + b) = π a + π b := by
  simp only [tensorOfKLR,map_add]

private theorem raw_leftExterior_support :
    (e C * (e C - X₁ * ψ 1 * e C) : H) = e C - X₁ * ψ 1 * e C := by
  rw [mul_sub,e_mul_self]
  have hs : sadj m 1 • C = C := by decide
  have hc : (e C * (ψ 1 * e C) : H) = ψ 1 * e C := by
    rw [ψ_mul_e, hs, ← mul_assoc, e_mul_self]
  congr 1
  calc
    _ = (e C * X₁) * (ψ 1 * e C) := by simp only [mul_assoc]
    _ = X₁ * (ψ 1 * e C) := by rw [e_mul_x, mul_assoc, hc]
    _ = _ := by rw [mul_assoc]

/-- The left exterior loading idempotent fixes the complementary projector. -/
theorem labelTwoLeftExteriorProjector_fixed : π (e C : H) * p = p := by
  unfold labelTwoLeftExteriorProjector
  rw [← proj_mul, raw_leftExterior_support param]

private theorem first_second_proj_dot :
    π X₂ * p = -u := by
  have h := congrArg (· * p) (labelTwo_leftExterior_dot_relations param).1
  rw [proj_mul, proj_add, zero_mul, mul_assoc, labelTwoLeftExteriorProjector_fixed, add_mul, add_comm] at h
  exact eq_neg_iff_add_eq_zero.mpr h

private theorem second_proj_dot_sq :
    π X₂ * (π X₂ * p) = 0 := by
  have h := congrArg (· * p) (labelTwo_leftExterior_dot_relations param).2
  rw [proj_mul, proj_mul, zero_mul, mul_assoc, mul_assoc, labelTwoLeftExteriorProjector_fixed] at h
  exact h

private theorem first_second_commute :
    π X₁ * π X₂ = π X₂ * π X₁ := by
  rw [← proj_mul, ← proj_mul, x_mul_x]

private theorem second_proj_dot_after_first :
    π X₂ * u = 0 := by
  have h := second_proj_dot_sq param
  rw [first_second_proj_dot param, mul_neg, neg_eq_zero] at h
  exact h

private theorem first_proj_dot_sq :
    π X₁ * u = 0 := by
  have h : π X₁ * (π X₂ * p) = 0 := by
    rw [← mul_assoc, first_second_commute param, mul_assoc, second_proj_dot_after_first param]
  rw [first_second_proj_dot param, mul_neg, neg_eq_zero] at h
  exact h

private theorem red_proj_dot (i : Fin m) (hi : (C).lbl i |>.isRight) :
    π (x i : H) * p = 0 := by
  have h := StendhalAlgebraAllOrders.x_mul_e_of_red
    (k := k) (Q := param) (Λ := wt) («ν» := ν) i C hi
  let φ := (TensorProductAlgebra.mk param wt ν).comp (orderProjection param wt ν)
  have ht := congrArg φ h
  have hzero : π (x i * e C : H) = 0 := by
    simp only [φ, AlgHom.comp_apply, StendhalAlgebraAllOrders.x,
      StendhalAlgebraAllOrders.e, map_mul, map_zero] at ht
    simp only [tensorOfKLR, map_mul]
    exact ht
  calc
    _ = π (x i : H) * (π (e C : H) * p) :=
      congrArg (π (x i : H) * ·) (labelTwoLeftExteriorProjector_fixed param).symm
    _ = π (x i * e C : H) * p := by rw [proj_mul, mul_assoc]
    _ = _ := by rw [hzero, zero_mul]

private theorem red_proj_dot_after_first (i : Fin m) (hi : (C).lbl i |>.isRight) :
    π (x i : H) * u = 0 := by
  rw [← mul_assoc, ← proj_mul, x_mul_x, proj_mul, mul_assoc, red_proj_dot param i hi, mul_zero]

private theorem projected_dot_rows (i : Fin m) :
    (∃ a : k, π (x i : H) * p = a • u) ∧ π (x i : H) * u = 0 := by
  fin_cases i
  · exact ⟨⟨0, (red_proj_dot param _ (by decide)).trans (zero_smul k u).symm⟩,
      red_proj_dot_after_first param _ (by decide)⟩
  · exact ⟨⟨1, (one_smul k u).symm⟩, first_proj_dot_sq param⟩
  · exact ⟨⟨-1, (first_second_proj_dot param).trans (neg_one_smul k u).symm⟩,
      second_proj_dot_after_first param⟩
  · exact ⟨⟨0, (red_proj_dot param _ (by decide)).trans (zero_smul k u).symm⟩,
      red_proj_dot_after_first param _ (by decide)⟩

/-- Polynomials on the complementary exterior projector have only the
undotted and first-dot coefficients. -/
theorem exterior_projector_polynomial_span (f : MvPolynomial (Fin m) k) :
    ∃ a b : k, π (pol f : H) * p = a • p + b • u := by
  induction f using MvPolynomial.induction_on with
  | «C» a =>
      refine ⟨a,0,?_⟩
      change π (pol (algebraMap k (MvPolynomial (Fin m) k) a) : H) * p = _
      simp only [tensorOfKLR, AlgHom.commutes, Algebra.smul_def, map_zero, zero_mul, add_zero]
  | add f g hf hg =>
      obtain ⟨a,b,hab⟩ := hf
      obtain ⟨c,d,hcd⟩ := hg
      refine ⟨a+c,b+d,?_⟩
      rw [map_add, proj_add, add_mul, hab, hcd, add_smul, add_smul]
      exact add_add_add_comm _ _ _ _
  | mul_X f i hf =>
      obtain ⟨a,b,hab⟩ := hf
      obtain ⟨⟨c,hc⟩,hd⟩ := projected_dot_rows param i
      refine ⟨0,a*c,?_⟩
      rw [mul_comm f (MvPolynomial.X i), map_mul, pol_X, proj_mul, mul_assoc, hab, mul_add,
        mul_smul_comm, mul_smul_comm, hc, hd, smul_zero, add_zero, zero_smul, zero_add, mul_smul]

/-- The projected black crossing kills the complementary projector. -/
theorem labelTwoLeftExteriorProjector_cross_zero :
    π (ψ 1 : H) * p = 0 := by
  have h := congrArg (π) (labelTwo_complementaryExterior_cross_zero S)
  simp only [tensorOfKLR, map_mul, map_zero] at h
  exact h

/-- On the first dot, the black crossing recovers the projector. -/
theorem labelTwoLeftExteriorProjector_cross_dot :
    π (ψ 1 : H) * u = p := by
  have h := congrArg (π) (labelTwo_complementaryExterior_cross_dot S)
  simp only [tensorOfKLR, map_mul] at h
  exact h

private theorem projected_left_loading (hc : IsRedOrdered C) :
    π (e C : H) = seqIdem param wt C hc := by
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem C).trans (ite_eq_left hc)

private theorem exterior_pbw_row_mul (l : List ℕ) (f : MvPolynomial (Fin m) k) :
    π (ψw l * pol f * e C : H) * p = π (ψw l : H) * (π (pol f : H) * p) := by
  simp only [proj_mul, mul_assoc, labelTwoLeftExteriorProjector_fixed param]

private theorem exterior_edge_row_span (l : List ℕ) (f : MvPolynomial (Fin m) k) :
    π (ψw l * pol f * e C : H) * p ∈
      Submodule.span k ({π (ψw l : H) * p, π (ψw l : H) * u} : Set T) := by
  obtain ⟨a,b,h⟩ := exterior_projector_polynomial_span param f
  rw [exterior_pbw_row_mul, h, mul_add, mul_smul_comm, mul_smul_comm]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert _ _))
  · exact Submodule.smul_mem _ b (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem exterior_edge_cross_row_span (l : List ℕ) (f : MvPolynomial (Fin m) k) :
    π (ψw (l ++ [1]) * pol f * e C : H) * p ∈
      Submodule.span k ({π (ψw l : H) * p, π (ψw l : H) * u} : Set T) := by
  obtain ⟨a,b,h⟩ := exterior_projector_polynomial_span param f
  rw [exterior_pbw_row_mul, ψw_append, ψw_cons, ψw_nil, mul_one, proj_mul, mul_assoc, h,
    mul_add, mul_smul_comm, mul_smul_comm, labelTwoLeftExteriorProjector_cross_zero,
    labelTwoLeftExteriorProjector_cross_dot, smul_zero, zero_add, mul_smul_comm]
  exact Submodule.smul_mem _ b (Submodule.subset_span (Set.mem_insert _ _))

/-- With the two reduced return words at a cut, the outgoing exterior
projective is spanned by the direct shuffle and its first-dot translate. -/
theorem exterior_projector_cut_span
    (s : Seq μ) (hs : IsRedOrdered s) (hc : IsRedOrdered C) (l : List ℕ)
    (hcut : ∀ w : Equiv.Perm (Fin m), w • C = s →
      labelTwoExteriorPBWChoice w = l ∨ labelTwoExteriorPBWChoice w = l ++ [1])
    (z : lIdeal p) :
    ∃ a b : k, seqIdem param wt s hs * z.val =
      a • (π (ψw l : H) * p) + b • (π (ψw l : H) * u) := by
  let D := Submodule.span k ({π (ψw l : H) * p, π (ψw l : H) * u} : Set T)
  have hfix : (seqIdem param wt C hc) • p = p := by
    change seqIdem param wt C hc * p = p
    rw [← projected_left_loading param hc, labelTwoLeftExteriorProjector_fixed param]
  have hmem : (seqIdem param wt s hs * z.val) • p ∈ D :=
    loading_mul_smul_mem_of_projected_PBW (M := T) param wt labelTwoExteriorPBWChoice_spec
      hc hs p hfix D (by
        intro w hw f
        change π (ψw (labelTwoExteriorPBWChoice w) * pol f * e C : H) * p ∈ D
        rcases hcut w hw with h | h
        · rw [h]; exact exterior_edge_row_span param l f
        · rw [h]; exact exterior_edge_cross_row_span param l f) z.val
  change (seqIdem param wt s hs * z.val) * p ∈ D at hmem
  rw [mul_assoc, z.property] at hmem
  change seqIdem param wt s hs * z.val ∈ Submodule.span k
    ({π (ψw l : H) * p, π (ψw l : H) * u} : Set T) at hmem
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a,b,h⟩ := hmem
  exact ⟨a,b,h.symm⟩

end
end Categorification.Stendhal
