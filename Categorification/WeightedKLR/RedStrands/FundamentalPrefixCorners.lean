/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FundamentalCornerEuler

/-! # First-weight Hom polynomials for two fundamental red strands

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36, diagram side. The mixed
crossings generate the two off-diagonal corners, and the middle dot vanishes.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR StendhalAlgebraAllOrders TypeA Categorification.Graded Equiv
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "S" => StendhalAlgebraAllOrders ℚ Q wt ({()} : Multiset Unit)
local notation "ρ" => canWord (Multiset.card μ)
local notation "σ" => sadj (Multiset.card μ) 1
private abbrev load (a : Fin 2) := (FirstWeight.boundaryAt () 2 a).1
private abbrev posB (a : Fin 2) : Fin (Multiset.card μ) := ⟨a.val+1,by change _ < 3; omega⟩
private abbrev permB (a b : Fin 2) : Perm (Fin (Multiset.card μ)) := if a = b then 1 else σ
private abbrev degB (a b : Fin 2) : ℤ := if a = b then 0 else 1
private abbrev V (a : Fin 2) := sequenceProj grading (load a) (FirstWeight.boundaryAt () 2 a).2.1
private abbrev H (a b : Fin 2) := homGrade T (V b).grading (V a).grading
private abbrev Ixs := tensorProductBasisIndices (ν := {()}) wordSpec Q wt
private abbrev box (a : Fin 2) : T := project (e (load a))
private abbrev C : T := project (ψ 1)
private abbrev crossB (a b : Fin 2) : T := if a = b then 1 else C

private theorem wordB (a b : Fin 2) :
    ρ (permB a b) = if a = b then [] else [1] := by
  split_ifs with h
  · exact List.length_eq_zero_iff.mp (by rw [length_canWord,length_one])
  · have hl : (ρ σ).length = 1 := by rw [length_canWord,length_sadj (by decide)]
    obtain ⟨j,hj⟩ := List.length_eq_one_iff.mp hl
    have hv := validWord_canWord (Multiset.card μ) σ j (by simp [hj])
    change j + 1 < 3 at hv
    have he := wordProd_canWord (Multiset.card μ) σ
    rw [hj] at he
    have hjle : j ≤ 1 := by omega
    interval_cases j
    · exact False.elim ((by decide +kernel : wordProd (Multiset.card μ) [0] ≠ σ) he)
    · exact hj

private theorem proj_cross (a : Fin 2) :
    C * box a = box (1-a) * C := by
  have h := congrArg ((project).comp (ofKLR ℚ Q wt {()}))
    (KLRAlgebra.ψ_mul_e (Q := stendhalQ Q wt) 1 (load a))
  have he : σ • load a = load (1-a) := by fin_cases a <;> decide +kernel
  simpa only [he,map_mul,AlgHom.comp_apply,ψ,e] using h

private theorem box_eq (a : Fin 2) : box a =
    TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e (load a) (FirstWeight.boundaryAt () 2 a).2.1) := by
  apply congrArg (TensorProductAlgebra.mk Q wt {()})
  apply Subtype.ext
  change (e (load a) * redOrderedIdem ℚ Q wt {()} : S) = e (load a)
  simp [e_mul_redOrderedIdem,(FirstWeight.boundaryAt () 2 a).2.1]
private theorem box_id (a : Fin 2) : box a * box a = box a := by
  rw [box_eq]; exact (isIdempotentElem_mk_e _ _).eq

private theorem load_zero : load 0 = middle := by decide +kernel
private theorem load_one : load 1 = terminal := by decide +kernel

private theorem triple : C * C * (C * box 1) = 0 := by
  have hm := ψ_sq_black_red (Q := Q) (Λ := wt) 1 (by decide) middle () 1 rfl rfl
  simp only [wt,Finsupp.single_eq_same,pow_one] at hm
  have h0 : C * C * box 0 = 0 := by
    unfold C box
    rw [load_zero]
    rw [← map_mul,← map_mul,hm,middle_dot_zero]
  rw [proj_cross,← mul_assoc]
  change C * C * box 0 * C = 0
  rw [h0,zero_mul]

private theorem bigon : C * C * box 1 = project (x (posB 1) * e terminal) := by
  have ht := ψ_sq_red_black (Q := Q) (Λ := wt) 1 (by decide) terminal () 1 rfl rfl
  simp only [wt,Finsupp.single_eq_same,pow_one] at ht
  unfold C box
  rw [load_one]
  rw [← map_mul,← map_mul,ht]
  rfl

private theorem one_dot (a b : Fin 2) (hab : a = 0 ∨ b = 0) :
    crossB a b * project (x (posB a) * e (load a)) = 0 := by
  fin_cases a <;> fin_cases b
  · change 1 * project (x (posB 0) * e (load 0)) = 0
    rw [one_mul,load_zero]; exact middle_dot_zero
  · change C * project (x (posB 0) * e (load 0)) = 0
    rw [load_zero]
    have hz : project (x (posB 0) * e middle) = 0 := middle_dot_zero
    rw [hz,mul_zero]
  · change C * project (x (posB 1) * e (load 1)) = 0
    rw [load_one]
    rw [← bigon]
    simpa only [mul_assoc] using triple
  · simp at hab

private theorem cross_degree (a : Fin 2) : grading.dψ 1 (load a) = 1 := by
  fin_cases a <;> change 1 * ((wt 1 ()) : ℤ) = 1 <;> simp [wt]

private theorem term_shape (a b : Fin 2) (hab : a = 0 ∨ b = 0)
    (i : Ixs) (hi : hasEndpoints wordSpec (load a) (load b) i) :
    i.1.1 = (load a,permB a b,0) ∧ grading.stdDeg ρ i.1.1 = degB a b := by
  obtain ⟨hb,ht⟩ := hi
  have hu : Multiset.Nodup μ := by simp [stendhalWeight]
  have hw : i.1.1.2.1 = permB a b := by
    apply NonInteracting.smul_left_injective hu (load a)
    rw [hb] at ht
    rw [ht]
    fin_cases a <;> fin_cases b <;> decide +kernel
  let n := i.1.1.2.2 (posB a)
  have hs : i.1.1.2.2 = Finsupp.single (posB a) n := by
    apply Finsupp.support_subset_singleton.mp
    intro p hp
    have hr := i.1.2.2.2.1 p hp
    change (i.1.1.1.lbl p).isLeft = true at hr
    rw [hb] at hr
    have hf : ∀ (a : Fin 2) (p : Fin (Multiset.card μ)), (load a).lbl p |>.isLeft → p = posB a := by decide +kernel
    simpa using hf a p hr
  have ix : i.1.1 = (load a,permB a b,Finsupp.single (posB a) n) := Prod.ext hb (Prod.ext hw hs)
  have hn : n = 0 := by
    by_contra hn
    obtain ⟨r,hr⟩ := Nat.exists_eq_succ_of_ne_zero hn
    apply (tensorProductBasis (ν := {()}) wordSpec Q wt).linearIndependent.ne_zero i
    rw [project_of_term,ix]
    simp only [KLRAlgebra.stdElt, ← MvPolynomial.X_pow_eq_monomial,map_mul,map_pow,KLRAlgebra.pol_X]
    have hc : project (ofKLR ℚ Q wt {()} (KLRAlgebra.ψw (ρ (permB a b)))) = crossB a b := by
      rw [wordB]
      split_ifs <;> simp [KLRAlgebra.ψw,ψ,C]
    rw [hc]
    change crossB a b * project (x (posB a)) ^ n * box a = 0
    have hc' : Commute (project (x (posB a))) (box a) :=
      ((show Commute (KLRAlgebra.x (posB a)) (KLRAlgebra.e (load a) :
        KLRAlgebra ℚ (stendhalQ Q wt) μ) from KLRAlgebra.x_mul_e _ _).map _).map _
    rw [hr,pow_succ',mul_assoc, mul_assoc, (hc'.pow_left r).eq, ← mul_assoc _ (box a), ← mul_assoc]
    have hz := one_dot a b hab
    rw [map_mul] at hz
    rw [hz,zero_mul]
  rw [hn,Finsupp.single_zero] at ix
  refine ⟨ix,?_⟩
  rw [ix]
  simp only [GradingDatum.stdDeg,wordB,map_zero,add_zero]
  by_cases h : a = b <;> simp [h,degB,GradingDatum.degW,wordProd,cross_degree]

private theorem element_nz (a b : Fin 2) (hab : a = 0 ∨ b = 0) :
    crossB a b * box a ≠ 0 := by
  have hn : C * (C * box 1) ≠ 0 := by rw [← mul_assoc,bigon]; exact dot_ne_zero
  have hf : C * box 1 ≠ 0 := fun h => hn (by rw [h,mul_zero])
  have hg : C * box 0 ≠ 0 := by
    intro h
    apply hn
    rw [proj_cross 1,← mul_assoc]
    change C * box 0 * C = 0
    rw [h,zero_mul]
  fin_cases a <;> fin_cases b
  · change 1 * box 0 ≠ 0
    rw [one_mul]
    exact fun h => hg (by rw [h,mul_zero])
  · exact hg
  · exact hf
  · simp at hab

private theorem element_grade (a b : Fin 2) :
    crossB a b * box a ∈ tensorProductGrade grading {()} (degB a b) := by
  by_cases h : a = b
  · simp only [crossB,degB,h,ite_true,one_mul,box_eq]
    exact mk_e_mem_tensorProductGrade _ _ _ _
  simp only [crossB,degB,h,ite_false]
  change project (ψ 1) * project (e (load a)) ∈ _
  rw [← map_mul]
  apply Graded.mem_map_of_mem
  change (ψ 1 * e (load a) * redOrderedIdem ℚ Q wt {()} : S) ∈ allOrdersGrade grading {()} 1
  rw [mul_assoc,e_mul_redOrderedIdem,ite_eq_left (FirstWeight.boundaryAt () 2 a).2.1]
  have he := Graded.mem_map_of_mem _ (ofKLR ℚ Q wt {()}).toLinearMap
    (grading.ψ_mul_e_mem_grade' 1 (load a))
  rw [cross_degree] at he
  change ofKLR ℚ Q wt {()} (_ * _) ∈ allOrdersGrade grading {()} 1 at he
  simpa only [map_mul,ψ,e] using he

private theorem tensorQ : IsRouquierQ (QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) Q where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private theorem rank_pos (a b : Fin 2) (hab : a = 0 ∨ b = 0) :
    0 < Module.finrank ℚ (H a b (degB a b)) := by
  let := tensorProductAlgebra_finite wt {()} tensorQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade grading {()})
  let z := crossB a b * box a
  have hR : z * box a = z := by simp only [z,mul_assoc,box_id]
  have hL : box b * z = z := by
    by_cases hab' : a = b
    · subst b; simp [z,box_id]
    · have hc : b = 1-a := by fin_cases a <;> fin_cases b <;> first | rfl | contradiction
      simp only [z,crossB,hab',ite_false]
      rw [hc,proj_cross,← mul_assoc,box_id]
  have hi : IsIdempotentElem (box b) := box_id b
  have he := homGradeIdemEquiv (ℳ := (V a).grading) hi
    (box_eq b ▸ mk_e_mem_tensorProductGrade grading {()} (load b) (FirstWeight.boundaryAt () 2 b).2.1)
    (degB a b)
  have heq := he.finrank_eq
  rw [box_eq b] at heq
  change 0 < Module.finrank ℚ (homGrade T (Graded.submodule (tensorProductGrade grading {()})
    (leftIdeal (TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e (load b) (FirstWeight.boundaryAt () 2 b).2.1)))) (V a).grading (degB a b))
  rw [heq]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  rw [box_eq a] at hR
  rw [box_eq b] at hL
  refine ⟨⟨⟨⟨z,hR⟩,Subtype.ext hL⟩,element_grade a b⟩,?_⟩
  intro h
  apply element_nz a b hab
  exact congrArg (fun v => (((v.val.val : leftIdeal (TensorProductAlgebra.mk Q wt {()}
    (StendhalAlgebra.e (load a) (FirstWeight.boundaryAt () 2 a).2.1))) : T))) h

private theorem rank_entry (a b : Fin 2) (hab : a = 0 ∨ b = 0) (d : ℤ) :
    Module.finrank ℚ (H a b d) = if d = degB a b then 1 else 0 := by
  have hp (i : Unit ⊕ Fin 2) : 0 < grading.degX i := by cases i <;> exact (by decide : (0 : ℤ) < 2)
  by_cases hd : d = degB a b
  · rw [ite_eq_left hd]
    have hpos := rank_pos a b hab
    suffices hle : Module.finrank ℚ (H a b d) ≤ 1 by subst d; omega
    rw [finrank_homGrade_sequenceProj grading wordSpec hp]
    suffices hs : Subsingleton {i : Ixs | hasEndpoints wordSpec (load a) (load b) i ∧ grading.stdDeg ρ i.1.1 = d} by
      let := hs
      exact Finite.card_le_one_iff_subsingleton.2 hs
    constructor
    rintro ⟨i,hi,_⟩ ⟨j,hj,_⟩
    exact Subtype.ext (Subtype.ext (Subtype.ext ((term_shape a b hab i hi).1.trans
      (term_shape a b hab j hj).1.symm)))
  · rw [ite_eq_right hd,finrank_homGrade_sequenceProj grading wordSpec hp]
    have : IsEmpty {i : Ixs | hasEndpoints wordSpec (load a) (load b) i ∧ grading.stdDeg ρ i.1.1 = d} :=
      ⟨fun ⟨i,hi,he⟩ => hd (he.symm.trans (term_shape a b hab i hi).2)⟩
    exact Nat.card_of_isEmpty

private theorem prefix_poly (a b : Fin 2) (hab : a = 0 ∨ b = 0) :
    gdimPoly (H a b) = LaurentPolynomial.T (degB a b) := by
  classical
  have hf : (Function.support fun d => (Module.finrank ℚ (H a b d) : ℤ)).Finite := by
    apply (Set.finite_singleton (degB a b)).subset
    intro d hd
    by_contra hh
    exact hd (by simp [rank_entry a b hab,show d ≠ degB a b from hh])
  ext d
  simp only [gdimPoly,hf,↓reduceDIte,LaurentPolynomial.T,AddMonoidAlgebra.coeff_single]
  change (Module.finrank ℚ (H a b d) : ℤ) = _
  rw [rank_entry a b hab]
  split_ifs <;> simp_all

/-- The diagrammatic Hom form of Webster, arXiv:1309.3796v2, Lemma 4.36,
on the two sequences in the first lowering weight of the fundamental tensor square. -/
theorem boundaryAt_homGdimPoly (a b : Fin 2) :
    let s := FirstWeight.boundaryAt () 2 a
    let t := FirstWeight.boundaryAt () 2 b
    gdimPoly (homGrade T (sequenceProj grading s.1 s.2.1).grading
      (sequenceProj grading t.1 t.2.1).grading) =
      if a = b then if a = 0 then 1 else 1 + LaurentPolynomial.T 2 else LaurentPolynomial.T 1 := by
  fin_cases a <;> fin_cases b
  · simpa [degB] using prefix_poly 0 0 (Or.inl rfl)
  · exact prefix_poly 1 0 (Or.inr rfl)
  · exact prefix_poly 0 1 (Or.inl rfl)
  · exact boundaryAt_last_homGdimPoly

end Categorification.Stendhal.FundamentalCorner
