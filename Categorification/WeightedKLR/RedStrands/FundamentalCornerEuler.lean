/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FundamentalCorner
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary

/-! # The endomorphism polynomial of the terminal two-fundamental projective

In the tensor square of the type A₁ fundamental representation, the terminal
one-black sequence projective has homogeneous endomorphism basis given by the
identity and a single black dot. This computes the diagram side of Webster,
arXiv:1309.3796v2, §4.7, Lemma 4.36 in the first lowering weight.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR StendhalAlgebraAllOrders TypeA Categorification.Graded Equiv
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local notation "𝕋" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "S" => StendhalAlgebraAllOrders ℚ Q wt ({()} : Multiset Unit)
private abbrev black : Fin (Multiset.card μ) := ⟨2,by decide⟩
local notation "ρ" => canWord (Multiset.card μ)
private theorem wordSpec (w : Perm (Fin (Multiset.card μ))) :
    IsReduced (Multiset.card μ) (ρ w) ∧ wordProd _ (ρ w) = w :=
  ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩

private abbrev Ixs := tensorProductBasisIndices (ν := {()}) wordSpec Q wt
private abbrev basisT := tensorProductBasis (ν := {()}) wordSpec Q wt

private theorem Q_spec : IsRouquierQ (QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) Q where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

/-- Webster's grading with the type A₁ black dot in degree two. -/
def grading := stendhalGradingDatum wt (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit)) (fun _ => 1) (fun _ => rfl)

private theorem pos (a : Unit ⊕ Fin 2) : 0 < grading.degX a := by
  cases a <;> exact (by decide : (0 : ℤ) < 2)

private theorem nilWord : ρ 1 = [] :=
  List.length_eq_zero_iff.mp (by rw [length_canWord,length_one])

private theorem project_of_term (b : Ixs) :
    basisT b = project (ofKLR ℚ Q wt {()} (KLRAlgebra.stdElt ρ b.1.1)) := by
  rw [tensorProductBasis_apply]
  apply congrArg (TensorProductAlgebra.mk Q wt {()})
  apply Subtype.ext
  exact ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).mp
    (stendhalTerm Q wt (fun w => (wordSpec w).2) b.1).2).2.symm

private theorem index_shape (b : Ixs) (hb : hasEndpoints wordSpec terminal terminal b) :
    ∃ n : ℕ, n ≤ 1 ∧ b.1.1 = (terminal, 1, Finsupp.single black n) ∧
      grading.stdDeg ρ b.1.1 = 2 * (n : ℤ) := by
  obtain ⟨hbot,htop⟩ := hb
  have hu : Multiset.Nodup μ := by simp [stendhalWeight]
  have hw : b.1.1.2.1 = 1 :=
    NonInteracting.smul_left_injective hu b.1.1.1 (by rw [one_smul,htop,hbot])
  let n := b.1.1.2.2 black
  have hs : b.1.1.2.2 = Finsupp.single black n := by
    apply Finsupp.support_subset_singleton.mp
    intro a ha
    have hr := b.1.2.2.2.1 a ha
    change (b.1.1.1.lbl a).isLeft = true at hr
    rw [hbot] at hr
    have h : ∀ (a : Fin (Multiset.card μ)), (terminal.lbl a).isLeft → a = black := by decide +kernel
    simpa using h a hr
  have ix : b.1.1 = (terminal,1,Finsupp.single black n) := Prod.ext hbot (Prod.ext hw hs)
  refine ⟨n,?_,ix,?_⟩
  · by_contra! hh
    have hzero : project ((x black : S) ^ n * e terminal) = 0 := by
      obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
      rw [hr,Nat.add_comm,pow_add,mul_assoc,map_mul,dot_sq_zero,mul_zero]
    apply basisT.linearIndependent.ne_zero b
    rw [project_of_term,ix]
    simpa only [KLRAlgebra.stdElt,nilWord,KLRAlgebra.ψw,List.map_nil,List.prod_nil,one_mul,
      ← MvPolynomial.X_pow_eq_monomial, map_mul,map_pow,KLRAlgebra.pol_X, x,e] using hzero
  · rw [ix]
    simp only [GradingDatum.stdDeg,nilWord,GradingDatum.degW,zero_add,Finsupp.weight_single]
    change n • (2 : ℤ) = _
    simp [mul_comm]

local notation "P" => sequenceProj grading terminal terminal_ordered
private abbrev endGrade := homGrade 𝕋 (P).grading (P).grading

private theorem rank_le (d : ℤ) : Module.finrank ℚ (endGrade d) ≤ 1 := by
  rw [finrank_homGrade_sequenceProj grading wordSpec pos]
  suffices h : Subsingleton {b : Ixs | hasEndpoints wordSpec terminal terminal b ∧
      grading.stdDeg ρ b.1.1 = d} by
    let := h
    exact Finite.card_le_one_iff_subsingleton.2 h
  constructor
  rintro ⟨b,hb,hd⟩ ⟨c,hc,he⟩
  obtain ⟨n,_,hn,hnd⟩ := index_shape b hb
  obtain ⟨m,_,hm,hmd⟩ := index_shape c hc
  have hnm : n = m := by omega
  subst m
  exact Subtype.ext (Subtype.ext (Subtype.ext (hn.trans hm.symm)))

private theorem rank_zero_of_ne {d : ℤ} (h₀ : d ≠ 0) (h₂ : d ≠ 2) :
    Module.finrank ℚ (endGrade d) = 0 := by
  rw [finrank_homGrade_sequenceProj grading wordSpec pos]
  have : IsEmpty {b : Ixs | hasEndpoints wordSpec terminal terminal b ∧ grading.stdDeg ρ b.1.1 = d} := by
    constructor
    rintro ⟨b,hb,hd⟩
    obtain ⟨n,hn,_,hnd⟩ := index_shape b hb
    omega
  exact Nat.card_of_isEmpty

private abbrev p : 𝕋 := TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e terminal terminal_ordered)
private abbrev X₂ : 𝕋 := project (x black)

private theorem proj_e : project (e terminal) = p := by
  apply congrArg (TensorProductAlgebra.mk Q wt {()})
  apply Subtype.ext
  change (e terminal * redOrderedIdem ℚ Q wt {()} : S) = e terminal
  simp [e_mul_redOrderedIdem,terminal_ordered]

private theorem hp : IsIdempotentElem p := by
  rw [← proj_e]
  apply IsIdempotentElem.map
  change (e terminal * e terminal : S) = e terminal
  simp [e_mul_e]

private theorem hX : Commute X₂ p := by
  rw [← proj_e]
  apply Commute.map
  exact (show Commute (KLRAlgebra.x black) (KLRAlgebra.e terminal :
    KLRAlgebra ℚ (stendhalQ Q wt) μ) from KLRAlgebra.x_mul_e _ _).map _

private theorem dot_nz : X₂ * p ≠ 0 := by
  rw [← proj_e, ← map_mul]
  exact dot_ne_zero

private theorem dot_grade : X₂ * p ∈ tensorProductGrade grading {()} 2 := by
  rw [← proj_e, ← map_mul]
  apply Graded.mem_map_of_mem
  change (x black * e terminal * redOrderedIdem ℚ Q wt {()} : S) ∈ allOrdersGrade grading {()} 2
  simp only [mul_assoc, e_mul_redOrderedIdem, terminal_ordered, ↓reduceIte]
  have h := Graded.mem_map_of_mem _ (ofKLR ℚ Q wt {()}).toLinearMap
    (grading.x_mul_e_mem_grade black terminal)
  change ofKLR ℚ Q wt {()} (_ * _) ∈ allOrdersGrade grading {()} 2 at h
  simpa only [map_mul,x,e] using h

private theorem rank_pos_of_corner (d : ℤ) {z : 𝕋} (hz : z ∈ tensorProductGrade grading {()} d)
    (hL : p * z = z) (hR : z * p = z) (hnz : z ≠ 0) : 0 < Module.finrank ℚ (endGrade d) := by
  let := tensorProductAlgebra_finite wt {()} Q_spec
  let := HasGdim.of_finiteDimensional (tensorProductGrade grading {()})
  let h := homGradeIdemEquiv (ℳ := (P).grading) hp
    (mk_e_mem_tensorProductGrade grading {()} terminal terminal_ordered) d
  change 0 < Module.finrank ℚ (homGrade 𝕋 (Graded.submodule (tensorProductGrade grading {()}) (leftIdeal p)) (P).grading d)
  rw [h.finrank_eq]
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨⟨⟨z,hR⟩,Subtype.ext hL⟩,hz⟩,?_⟩
  intro h
  exact hnz (congrArg (fun v => (((v.val.val : leftIdeal p) : 𝕋))) h)

/-- The diagonal entry of the graded Hom form for the terminal sequence. -/
theorem terminal_homGdimPoly : gdimPoly (homGrade 𝕋 (P).grading (P).grading) = 1 + LaurentPolynomial.T 2 := by
  classical
  have h0 : 0 < Module.finrank ℚ (endGrade 0) := rank_pos_of_corner 0
    (mk_e_mem_tensorProductGrade grading {()} terminal terminal_ordered) hp.eq hp.eq
    (fun h => dot_nz (by change p = 0 at h; rw [h,mul_zero]))
  have h2 : 0 < Module.finrank ℚ (endGrade 2) := rank_pos_of_corner 2 dot_grade
    (by rw [← mul_assoc, ← hX.eq, mul_assoc,hp.eq])
    (by rw [mul_assoc,hp.eq]) dot_nz
  have he : (Function.support fun j => (Module.finrank ℚ (endGrade j) : ℤ)).Finite := by
    apply (Set.toFinite ({0,2} : Set ℤ)).subset
    intro j hj
    by_contra h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at h
    exact hj (by simp [rank_zero_of_ne h.1 h.2])
  ext d
  simp only [gdimPoly, he, ↓reduceDIte]
  rw [← LaurentPolynomial.T_zero]
  simp only [AddMonoidAlgebra.coeff_add, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single]
  change (Module.finrank ℚ (endGrade d) : ℤ) = _
  by_cases hd : d = 0
  · subst d
    have h := rank_le 0
    norm_num
    omega
  by_cases ht : d = 2
  · subst d
    have h := rank_le 2
    norm_num
    omega
  simp [rank_zero_of_ne hd ht,Ne.symm hd,Ne.symm ht]

/-- The same endomorphism polynomial at the canonical first-weight loading. -/
theorem boundaryAt_last_homGdimPoly :
    let s := FirstWeight.boundaryAt () 2 1
    let V := sequenceProj grading s.1 s.2.1
    gdimPoly (homGrade 𝕋 V.grading V.grading) = 1 + LaurentPolynomial.T 2 := by
  have hw : (FirstWeight.boundaryAt () 2 1).1 = terminal := by decide +kernel
  have hv : ¬ IsViolated terminal := by rintro ⟨h,hv⟩; exact Bool.noConfusion hv
  have he : FirstWeight.boundaryAt () 2 1 = ⟨terminal,terminal_ordered,hv⟩ := Subtype.ext hw
  rw [he]
  exact terminal_homGdimPoly

end Categorification.Stendhal.FundamentalCorner
