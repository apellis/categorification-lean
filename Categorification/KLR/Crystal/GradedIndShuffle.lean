/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Lemma314Graded
import Categorification.KLR.Prop32Mult
import Categorification.KLR.Prop31G0

/-!
# The graded shuffle decomposition for parabolic induction

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Lemma 2.20. For an arbitrary graded module
over the parabolic tensor algebra, the summand of the induced module at the word `s`
indexed by the shuffle `u` is shifted by the crossing degree of the reversed shuffle word
starting at `u • s`. Cutting the shuffle by its source word gives the degree even for
a grading datum with asymmetric crossing degrees.
-/

noncomputable section

namespace Categorification.KLR.GradingDatum

open Categorification.Graded KLRAlgebra TypeA MulOpposite DirectSum
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) {μ ν : Multiset I} (hsym : KLRSymm Q)

local notation "𝒯" => tensorGrading (G.grade μ) (G.grade ν)

/-- Parabolic induction of a finite-dimensional graded module over `R(μ) ⊗ R(ν)`
(Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Proposition 2.16). -/
def indParabolicGFin (N : GFin 𝒯) : GFin (G.grade (μ + ν)) where
  carrier := Ind Q μ ν N.carrier
  grading := G.indGrading μ ν N.grading
  decomposition := balancedDecomposition 𝒯 (fun _ _ _ _ hm ht => G.op_smul_mem_bimodGrading hm ht)
  gradedSMul := gradedSMul_balanced (G.grade (μ + ν))
  finiteDimensional := finiteDimensional_ind hsym N.carrier

/-- Degree of the right shuffle generator with target word `s` (KL I, §2.6, Lemma 2.20). -/
def indShuffleDegree (u : Shuffle (Seq.card_add' μ ν)) (s : Seq (μ + ν)) : ℤ :=
  G.degW (shufWord u).reverse (u.1 • s)

omit [DecidableEq I] in
/-- The induction exponent is the sum of the pairwise crossing degrees. On the output word,
the strand leaving the first parabolic block occurs second in each inversion, hence the
transposition of the arguments of `degΨ` (KL I, arXiv:0803.4121v2, §2.6, Lemma 2.20). -/
theorem indShuffleDegree_eq_maskInv (u : Shuffle (Seq.card_add' μ ν)) (s : Seq (μ + ν)) :
    G.indShuffleDegree u s = QuantumGroup.PreF.maskInv (fun a b => G.degΨ b a) s.1
      (shuffleMask (Seq.card_add' μ ν) u.1) := by
  classical
  rw [indShuffleDegree, G.degW_eq_sum_invSet (isReduced_reverse (shufWord_spec u).1),
    wordProd_reverse, (shufWord_spec u).2]
  calc
    _ = ∑ p ∈ invSet _ u.1, G.degΨ (s.lbl p.2) (s.lbl p.1) := by
      refine Finset.sum_nbij' (fun p => (u.1⁻¹ p.2, u.1⁻¹ p.1)) (fun p => (u.1 p.2, u.1 p.1))
        (fun p hp => ?_) (fun p hp => ?_) (fun p _ => by simp) (fun p _ => by simp) (fun p _ => rfl)
      · rw [mem_invSet] at hp ⊢
        simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using And.intro hp.2 hp.1
      · rw [mem_invSet] at hp ⊢
        simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using And.intro hp.2 hp.1
    _ = _ := by
      rw [QuantumGroup.PreF.maskInv, ← Fintype.sum_prod_type', ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mem_invSet_shuffle _ u.2 a b

/-- The parabolic word idempotent is homogeneous of degree zero. -/
theorem concatIdem_mem_grade (s : Seq (μ + ν)) : concatIdem s ∈ 𝒯 0 := by
  classical
  by_cases hs : s ∈ concatSet μ ν
  · obtain ⟨i, j, rfl⟩ := mem_concatSet.1 hs
    rw [concatIdem_append]
    simpa only [zero_add] using tmul_mem_tensorGrading (ℳ := G.grade μ) (𝒩 := G.grade ν) (G.e_mem_grade i) (G.e_mem_grade j)
  · rw [concatIdem_of_not_mem hs]
    exact Submodule.zero_mem _

private theorem cutShuffle_mem (u : Shuffle (Seq.card_add' μ ν)) (s : Seq (μ + ν)) :
    op (concatIdem (Q := Q) (u.1 • s)) • hatWRevSub u ∈
      G.bimodGrading μ ν (G.indShuffleDegree u s) := by
  change (((op (concatIdem (Q := Q) (u.1 • s)) • hatWRevSub u : IndBimod Q μ ν) : KLRAlgebra k Q (μ + ν))) ∈ G.grade _ _
  rw [coe_op_smul, unop_op, coe_hatWRevSub, hatWRev, mul_assoc, oneConcat_mul_concat,
    concat_concatIdem, ← mul_assoc]
  simpa only [add_zero, indShuffleDegree] using SetLike.GradedMul.mul_mem (A := G.grade (μ + ν))
    (G.ψw_mul_e_mem_grade (shufWord u).reverse (u.1 • s)) (G.oneConcat_mem_grade (ν := μ) (ν' := ν))

variable (N : GFin (tensorGrading (G.grade μ) (G.grade ν))) (s : Seq (μ + ν))

local notation "S" => (Shuffle (Seq.card_add' μ ν))

private instance shuffleSourceDecomp (u : S) :
    Decomposition (Graded.idem N.grading (concatIdem (Q := Q) (u.1 • s))) :=
  idemDecomposition N.grading (G.concatIdem_mem_grade (u.1 • s))

private instance shuffleTargetDecomp :
    Decomposition (Graded.idem (G.indParabolicGFin hsym N).grading (e s : KLRAlgebra k Q (μ + ν))) :=
  idemDecomposition (G.indParabolicGFin hsym N).grading (G.e_mem_grade s)

/-- The graded fixed-word decomposition of parabolic induction
(Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Lemma 2.20). -/
def indShuffleGradedEquiv :
    piGrading (fun u : S => shift (Graded.idem N.grading (concatIdem (Q := Q) (u.1 • s)))
      (G.indShuffleDegree u s)) ≃ᵍ[k]
      Graded.idem (G.indParabolicGFin hsym N).grading (e s : KLRAlgebra k Q (μ + ν)) := by
  refine GradedEquiv.ofPreserves (fixSubIndEquiv hsym N.carrier s).symm ?_
  intro d x hx
  change (indDecomp hsym N.carrier).symm (fun u => (x u : N.carrier)) ∈ G.indGrading μ ν N.grading d
  rw [indDecomp_symm_apply]
  refine Submodule.sum_mem _ fun u _ => ?_
  have hn : (x u : N.carrier) ∈ N.grading (d - G.indShuffleDegree u s) := hx u
  have hh := tmul_mem_balancedGrading (A := TensorKLR Q μ ν) (ℳ := G.bimodGrading μ ν)
    (𝒩 := N.grading) (B := KLRAlgebra k Q (μ + ν))
    (G.cutShuffle_mem u s) hn
  rwa [BalancedTensor.op_smul_tmul, (x u).2, add_sub_cancel] at hh

/-- **Graded Shuffle Lemma** (Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Lemma 2.20):
the graded dimension of each word space in an induced module is the sum of the source
word dimensions, multiplied by the Laurent monomials of their right-shuffle degrees. -/
theorem gdimPoly_ind_shuffle :
    gdimPoly (Graded.idem (G.indParabolicGFin hsym N).grading (e s : KLRAlgebra k Q (μ + ν))) =
      ∑ u : S, LaurentPolynomial.T (G.indShuffleDegree u s) *
        gdimPoly (Graded.idem N.grading (concatIdem (Q := Q) (u.1 • s))) := by
  rw [← gdimPoly_congr (G.indShuffleGradedEquiv hsym N s), gdimPoly_piGrading]
  exact Finset.sum_congr rfl fun u _ => gdimPoly_shift _ _

/-- Shuffle summands with an admissible parabolic source word. All other
source idempotents vanish (KL I, Lemma 2.20). -/
theorem gdimPoly_ind_shuffle_admissible :
    gdimPoly (Graded.idem (G.indParabolicGFin hsym N).grading (e s : KLRAlgebra k Q (μ + ν))) =
      ∑ u : ShuffleOf μ ν s, LaurentPolynomial.T (G.indShuffleDegree u.1 s) *
        gdimPoly (Graded.idem N.grading ((e u.split.1 : KLRAlgebra k Q μ) ⊗ₜ[k] (e u.split.2 : KLRAlgebra k Q ν))) := by
  classical
  rw [G.gdimPoly_ind_shuffle, ← Fintype.sum_subtype_add_sum_subtype
    (fun u : Shuffle (Seq.card_add' μ ν) => u.1 • s ∈ concatSet μ ν)]
  have hzero : ∑ u : {u : Shuffle (Seq.card_add' μ ν) // u.1 • s ∉ concatSet μ ν},
      LaurentPolynomial.T (G.indShuffleDegree u.1 s) *
        gdimPoly (Graded.idem N.grading (concatIdem (Q := Q) (u.1.1 • s))) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [concatIdem_of_not_mem u.2]
    suffices hz : gdimPoly (Graded.idem N.grading (0 : TensorKLR Q μ ν)) = 0 by
      rw [hz, mul_zero]
    let := idemDecomposition N.grading (𝒜 := tensorGrading (G.grade μ) (G.grade ν))
      (Submodule.zero_mem _)
    let : Subsingleton (idemSubspace k N.carrier (0 : TensorKLR Q μ ν)) :=
      ⟨fun x y => Subtype.ext (by
        have hx := mem_idemSubspace.1 x.2
        have hy := mem_idemSubspace.1 y.2
        rw [zero_smul] at hx hy
        exact hx.symm.trans hy)⟩
    ext d
    simp [gdimPoly_apply]
    exact Subsingleton.elim _ _
  rw [hzero, add_zero]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun u _ => ?_
  rw [← ShuffleOf.split_spec u, concatIdem_append]

/-- **KL I, arXiv:0803.4121v2, §2.6, Lemma 2.20.** For an external tensor product the
source dimension factors, and the sum runs over the shuffles compatible with the output word. -/
theorem gdimPoly_ind_shuffle_extTensor (X : GFin (G.grade μ)) (Y : GFin (G.grade ν)) :
    gdimPoly (Graded.idem (G.indParabolicGFin hsym (X.extTensor Y)).grading
      (e s : KLRAlgebra k Q (μ + ν))) =
      ∑ u : ShuffleOf μ ν s, LaurentPolynomial.T (G.indShuffleDegree u.1 s) *
        (gdimPoly (Graded.idem X.grading (e u.split.1 : KLRAlgebra k Q μ)) *
         gdimPoly (Graded.idem Y.grading (e u.split.2 : KLRAlgebra k Q ν))) := by
  classical
  rw [G.gdimPoly_ind_shuffle_admissible]
  refine Finset.sum_congr rfl fun u _ => ?_
  exact congrArg (_ * ·) (gdimPoly_idem_extTensor X Y (e_mul_self _) (e_mul_self _) (G.e_mem_grade _)
    (G.e_mem_grade _))

end Categorification.KLR.GradingDatum
