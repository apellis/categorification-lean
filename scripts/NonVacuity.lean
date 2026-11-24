import Categorification
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Analysis.Real.Sqrt
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule

/-!
# Non-vacuity checks for the headline theorems

Each `example` below applies a headline theorem to a concrete datum and discharges every
hypothesis by proof. If a later change makes a hypothesis set unsatisfiable for these data, or
breaks the statement's shape, this file stops compiling and CI fails. Where cheap, a second
`example` records that the conclusion is not degenerate.

Data: `sl₂` (`UDot.sl2RootDatum`), `sl₃` (`Flag.slRootDatum 2`), a Cartan datum of type `B₂`
(defined below, so that the non-simply-laced case is exercised), and the unfurled datum of one
arrow `false → true` for Kang–Kashiwara Theorem 5.2.

For the Cautis–Lauda condition `(BB_w)` (`TwoRep.StrongSl2.bbw`): the strong `sl₂`
2-representation `TwoRep.Grassmannian.l2` on the cohomology rings of `Gr(0,2)`, `Gr(1,2)`,
`Gr(2,2)` (the categorification of the irreducible representation of highest weight `2`).
`TwoRep.StrongSl2.adjHyp` (CL Prop. 3.9) is not covered: it also needs shift coherence and
idempotent-complete Hom categories, which are not yet established for that bicategory.
-/

open Categorification CategoryTheory QuantumGroup UDot

noncomputable section

namespace NonVacuity

/-! ### Data -/

/-- A Cartan datum of type `B₂`: `0 · 0 = 2`, `1 · 1 = 4`, `0 · 1 = -2`. -/
def cB2 : CartanDatum (Fin 2) where
  dot := ![![2, -2], ![-2, 4]]
  symm := by decide
  dot_self_pos := by decide
  dot_self_even i := by fin_cases i <;> decide
  dot_nonpos := by decide
  dvd_two_mul i j := by fin_cases i <;> fin_cases j <;> decide

/-! ### Khovanov–Lauda I, Theorem 1.1 (`sl₃`) -/

example : Function.Bijective
    (KLR.KLGamma.gammaInt' ℚ (Flag.slGraph 2) (KL.gabberKac (Flag.slGraph 2))) :=
  KLR.KLGamma.theorem_1_1_unconditional ℚ (Flag.slGraph 2)

/-! ### Khovanov–Lauda II, Theorem 8 (`B₂`) -/

example : Function.Bijective (KLR.KL2Gamma.gammaInt2' ℚ cB2 cB2.quantumGabberKac) :=
  KLR.KL2Gamma.theorem_8_unconditional ℚ cB2

/-! ### Quantum Gabber–Kac (`sl₃`, `B₂`) -/

example : (Flag.slCartan 2).QuantumGabberKac := CartanDatum.quantumGabberKac _

example : cB2.QuantumGabberKac := cB2.quantumGabberKac

/-! ### Khovanov–Lauda III, Theorems 1.1–1.2 and nondegeneracy -/

example : KL3.Diagram.CalculusNondeg sl2RootDatum (ZMod 2) := KL3.Diagram.calculusNondeg _ _

example : KL3.Diagram.CalculusNondeg (Flag.slRootDatum 2) ℚ := KL3.Diagram.calculusNondeg _ _

section Gamma

attribute [local instance] KLR.KLGamma.vAlgebra

example := KL3.Diagram.gammaAlg_surjective_unconditional (RD := sl2RootDatum) (k := ℚ)

example := KL3.Diagram.gammaAlg_surjective_unconditional (RD := Flag.slRootDatum 2) (k := ZMod 3)

example := KL3.Diagram.gammaAlg_injective_unconditional sl2RootDatum (ZMod 3)

example : AUD sl2RootDatum vQ ≃+* KL3.Diagram.K0All sl2RootDatum ℚ :=
  KL3.Diagram.gammaAlgEquiv_unconditional sl2RootDatum ℚ

example : AUD (Flag.slRootDatum 2) vQ ≃+* KL3.Diagram.K0All (Flag.slRootDatum 2) (ZMod 2) :=
  KL3.Diagram.gammaAlgEquiv_sl (ZMod 2) 2

end Gamma

/-! ### Kang–Kashiwara, Theorem 5.2 (one arrow `false → true`, level `Λ = ω_false + ω_true`) -/

section KangKashiwara

open KLR.Unfurling

/-- One arrow `false → true`: the unfurled datum of type `A₂`. -/
def arr : Bool → Bool → ℕ := fun a b => if a = false ∧ b = true then 1 else 0

/-- The weight `Λ` with `⟨h_a, Λ⟩ = 1` for both colours. -/
def lam : (Bool → ℤ) × (Bool →₀ ℤ) := (fun _ => 1, 0)

theorem hΛ : ∀ i, ((Polynomial.X : Polynomial ℚ).natDegree : ℤ) =
    (coverWeight arr).pair ((coverWeight arr).iY i) lam := by
  intro i; rw [coverWeight_pair_iY]; simp [lam]

example := KLR.CyclotomicAction.blockLoc (k := ℚ) (Q := unfQ arr) (a := fun _ => Polynomial.X)
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (fun _ => Polynomial.monic_X)
  (coverWeight arr) lam hΛ (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h)
  true (γ := 0) rfl rfl

example := KLR.CyclotomicAction.blockBoundary (k := ℚ) (Q := unfQ arr) (a := fun _ => Polynomial.X)
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (fun _ => Polynomial.monic_X)
  (coverWeight arr) lam hΛ (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h)
  false (β := 0) (by simp) rfl

example (d : ℤ) := KLR.KLRAlgebra.AbsentColour.finrank_appendedCornerGrade
  (unfGrading (k := ℚ) arr) (fun _ => 1) true ({false} : Multiset Bool)
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l)
  (coverWeight arr) lam (by rw [coverWeight_pair_iY]; rfl)
  (fun _ h => unfQ_natDegree_eq_neg_pair arr h) (by simp) default default d

/-- On the two-strand mixed block a second raising of the true colour vanishes. -/
example := KLR.CycKLR.raise_pow_lof_eq_zero (unfGrading (k := ℚ) arr) (fun _ => 1) true
  (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (coverCartan arr)
  2 ({true, false} : Multiset Bool) (by decide)
  (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade (unfGrading (k := ℚ) arr)
    (fun _ => 1) {true, false})))

open KLR.KLRAlgebra in
example : Module.finrank ℚ ↥(KLR.CycKLR.grade (unfGrading (k := ℚ) arr) (fun _ => 1)
    ([false, true] : List Bool) 2 ⊓ KLR.CycKLR.corner ℚ (unfQ arr)
      (fun _ => Polynomial.X ^ (1 : ℕ)) (Seq.ofList [false, true] rfl)
      (Seq.ofList [false, true] rfl)) = 1 := by
  rw [AbsentColour.finrank_diagonalCornerGrade_of_nodup _ _ (coverWeight arr) lam
    (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l)
    (fun _ => by rw [coverWeight_pair_iY]; rfl)
    (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h) _ (by decide) rfl]
  let factor := AbsentColour.diagonalFactor (unfGrading (k := ℚ) arr) (coverWeight arr) lam
  have hf (prior : List Bool) (i : Bool) (n : ℕ)
      (hn : ((coverWeight arr).pair ((coverWeight arr).iY i)
        (lam - (prior.map (coverWeight arr).iX).sum)).toNat = n) :
      factor prior i = ∑ j : Fin n, LaurentPolynomial.T ((j : ℤ) * 2) := by
    subst n
    rfl
  change (factor [] false * (factor [false] true * 1)).coeff 2 = 1
  rw [hf [] false 1 (by rw [coverWeight_pair_iY]; rfl),
    hf [false] true 2 (by rw [coverWeight_pair_iY]; rfl)]
  simp [Fin.sum_univ_two]
  exact Finsupp.single_eq_of_ne (by decide : (2 : ℤ) ≠ 0)

/-- On the single false strand, the true-colour commutator acts by [2]. -/
example := KLR.CycKLR.raise_lower_sub_lower_raise_of_notMem (unfGrading (k := ℚ) arr)
  (fun _ => 1) true ({false} : Multiset Bool) (unfQ_klrSymm arr)
  (fun j l _ => unfQ_leadingCoeff arr j l) (coverWeight arr) lam
  (by rw [coverWeight_pair_iY]; rfl) (fun _ h => unfQ_natDegree_eq_neg_pair arr h)
  (by simp) (by decide)
  (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade (unfGrading (k := ℚ) arr)
    (fun _ => 1) {false})))

/-- Both same-colour summands are compared on a present strand.  At
level three the coroot pairing is one, and at level one it is minus one. -/
example := KLR.CycKLR.positiveCommutatorK0 (unfGrading (k := ℚ) arr) (fun _ => 3)
  true 0 (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (coverWeight arr)
  ((fun _ => 3), 0) (by rw [coverWeight_pair_iY]; rfl)
  (fun _ h => unfQ_natDegree_eq_neg_pair arr h) (by simp only [add_zero, Multiset.map_singleton, Multiset.sum_singleton, map_sub,
      coverWeight_pair_iY, coverWeight_iX, coverCartan_dot_self]; decide)
  (Graded.K0.of (Graded.GProj.regular _))

example := KLR.CycKLR.negativeCommutatorK0 (unfGrading (k := ℚ) arr) (fun _ => 1)
  true 0 (unfQ_klrSymm arr) (fun j l _ => unfQ_leadingCoeff arr j l) (coverWeight arr)
  lam (by rw [coverWeight_pair_iY]; rfl) (fun _ h => unfQ_natDegree_eq_neg_pair arr h)
  (by simp only [add_zero, Multiset.map_singleton, Multiset.sum_singleton, map_sub,
      coverWeight_pair_iY, coverWeight_iX, coverCartan_dot_self]; decide) (Graded.K0.of (Graded.GProj.regular _))

/-- Equal-colour commutator on the regular class one step below level one. -/
example := KLR.CycKLR.raise_lower_sub_lower_raise (unfGrading (k := ℚ) arr)
  (fun _ => 1) true ({true} : Multiset Bool) (unfQ_klrSymm arr)
  (fun j l _ => unfQ_leadingCoeff arr j l) (coverWeight arr) lam
  (by rw [coverWeight_pair_iY]; rfl) (fun _ h => unfQ_natDegree_eq_neg_pair arr h)
  (by decide) (Graded.K0.of (Graded.GProj.regular _))

private def symmetricArrows (a b : Bool) : ℕ := if a = b then 0 else 1

/-- The distinct-colour mate has nonzero crossing degree for the quiver with one arrow in each direction. -/
example : (unfGrading (k := ℚ) symmetricArrows).degΨ true false = 2 := by decide

example := KLR.CycKLR.mixedIndResIso (unfGrading (k := ℚ) symmetricArrows) (fun _ => 2) {false}
  true false (Graded.GMod.regular _) (by decide) (unfQ_klrSymm symmetricArrows)

example := KLR.CycKLR.raise_lower_commute_of_ne (unfGrading (k := ℚ) symmetricArrows) (fun _ => 2) true false
  (unfQ_klrSymm symmetricArrows) (fun s t _ => unfQ_leadingCoeff symmetricArrows s t) (coverCartan symmetricArrows)
  (by decide) (by decide)

/-- The two-colour action on all projective classes for one arrow in
characteristic two, at level one on each colour. -/
private theorem oneArrowParameters :
    KLR.IsRouquierQ (coverCartan arr) (unfQ (k := ZMod 2) arr) where
  symm i j hij := (unfQ_klrSymm arr i j hij).symm
  homogeneous i j hij := by
    rw [coverCartan_dot_self, coverCartan_dot_self, coverCartan_dot_of_ne arr hij]
    have hh := (unfGrading (k := ZMod 2) arr).isWeightedHomogeneous i j hij
    change (unfQ (k := ZMod 2) arr i j).IsWeightedHomogeneous ![(2 : ℤ), 2]
      ((if i = j then -2 else 2 * (arr j i : ℤ)) + (if j = i then -2 else 2 * (arr i j : ℤ))) at hh
    rw [ite_eq_right hij, ite_eq_right hij.symm] at hh
    convert hh using 1
    push_cast
    ring
  unit_coeff i j hij := KLR.isUnit_extremalCoeff _ (unfQ_klrSymm arr)
    (fun a b _ => unfQ_leadingCoeff arr a b) (coverWeight arr)
    (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h) hij

/-- Two distinct words in the same three-strand A₂ block, with a repeated
colour and coefficients in characteristic two. -/
example (d : ℤ) := KLR.CycKLR.finrank_cornerGrade_huShi oneArrowParameters (fun _ => 2)
  (KLR.KLRAlgebra.Seq.ofList [false,true,false] rfl)
  (KLR.KLRAlgebra.Seq.ofList [false,false,true] (by decide)) d

example := KLR.CycKLR.gdimPoly_corner_permutationFormula oneArrowParameters (fun _ => 2)
  (KLR.KLRAlgebra.Seq.ofList [false,true,false] rfl)
  (KLR.KLRAlgebra.Seq.ofList [false,false,true] (by decide))

example := KLR.CycKLR.finrank_corner_permutationFormula oneArrowParameters (fun _ => 2)
  (KLR.KLRAlgebra.Seq.ofList [false,true,false] rfl)
  (KLR.KLRAlgebra.Seq.ofList [false,false,true] (by decide))

/-- At level one on both simple roots, the two choices of the repeated
target occurrence cancel with opposite signed quantum integers. -/
example : KLR.CycKLR.huShiPolynomial (coverCartan arr) (fun _ => 1)
    [false,true,false] [false,false,true] = 0 := by
  open KLR.CycKLR LieLean.QuantumGroup in
    simp [huShiPolynomial,huShiFromRight,markedWords,prefixPair,di,A,coverCartan,arr,qIntU,qNatU]
  left
  change _ + (-(∑ s ∈ Finset.range 1, ↑KLR.qUnitLP ^ (0-s) * (↑KLR.qUnitLP⁻¹ : LaurentPolynomial ℤ)^s)) * _ = 0
  simp

open KLR KLR.CycKLR in
private theorem mixedDegreeNegOne : (huShiPolynomial (coverCartan arr) (fun _ => 2)
    [false,true,false] [false,false,true]).coeff (-1) = 1 := by
  have h : huShiPolynomial (coverCartan arr) (fun _ => 2) [false,true,false] [false,false,true] =
      (LieLean.QuantumGroup.qIntU qUnitLP 2 * (LaurentPolynomial.T 2 *
        (LieLean.QuantumGroup.qIntU qUnitLP 3 * (LaurentPolynomial.T 1 * LieLean.QuantumGroup.qIntU qUnitLP 2)))) := by
    simp [huShiPolynomial,huShiFromRight,markedWords,prefixPair,di,A,coverCartan,arr,
      LieLean.QuantumGroup.qIntU,LieLean.QuantumGroup.qNatU]
  rw [h]
  have h2 : LieLean.QuantumGroup.qIntU qUnitLP 2 = LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) := by
    change LieLean.QuantumGroup.qNatU qUnitLP 2 = _
    rw [qNatU_eq_qint,qint_qUnitLP,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    norm_num
  have h3 : LieLean.QuantumGroup.qIntU qUnitLP 3 = LaurentPolynomial.T 2 + 1 + LaurentPolynomial.T (-2) := by
    change LieLean.QuantumGroup.qNatU qUnitLP 3 = _
    rw [qNatU_eq_qint,qint_qUnitLP,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    norm_num
  rw [h2,h3]
  simp only [add_mul,mul_add,one_mul,← LaurentPolynomial.T_add]
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,LaurentPolynomial.T_apply]
  decide

/-- At level two the same mixed corner has a one-dimensional degree minus
one component over the field with two elements. -/
example :
    let s := KLR.KLRAlgebra.Seq.ofList [false,true,false] rfl
    let t := KLR.KLRAlgebra.Seq.ofList [false,false,true]
      (show (([false,false,true] : List Bool) : Multiset Bool) = ([false,true,false] : List Bool) by decide)
    Module.finrank (ZMod 2) ↥(KLR.CycKLR.grade oneArrowParameters.gradingDatum (fun _ => 2) _ (-1) ⊓
      KLR.CycKLR.corner (ZMod 2) (unfQ arr) (fun _ => Polynomial.X ^ 2) s t) = 1 := by
  have h := KLR.CycKLR.finrank_cornerGrade_huShi oneArrowParameters (fun _ => 2)
    (KLR.KLRAlgebra.Seq.ofList [false,true,false] rfl)
    (KLR.KLRAlgebra.Seq.ofList [false,false,true] (by decide)) (-1)
  rw [KLR.KLRAlgebra.Seq.ofFn_ofList,KLR.KLRAlgebra.Seq.ofFn_ofList,mixedDegreeNegOne] at h
  exact_mod_cast h

/-- Two ordered red strands carry different fundamental colours in type A₂. -/
private def twoRedWeights (r : Fin 2) : Bool →₀ ℕ := Finsupp.single (r == 0) 1

example := Stendhal.blackLower_serre twoRedWeights (coverCartan arr) oneArrowParameters
  (i := false) (j := true) (by decide)

example := Stendhal.blackDividedLower_serre twoRedWeights (coverCartan arr) oneArrowParameters
  (i := false) (j := true) (by decide)

example := Stendhal.blackDividedLower_mul twoRedWeights (coverCartan arr) oneArrowParameters true 2 1

example := Stendhal.FirstWeight.blackDividedLower_tensorWordProjectiveClass twoRedWeights (coverCartan arr)
  oneArrowParameters (.red (.black (.red .empty) false 1)) true 2

private def dividedLevels (r : Fin 2) : Bool →₀ ℕ := Finsupp.single (r == 0) 2

/-- The first level supports its length-two divided block. Right induction
appends black of the second colour; last-red induction retains the block. -/
example := Stendhal.FirstWeight.blackLower_tensorWordProjectiveClass (coverCartan arr)
  oneArrowParameters dividedLevels (.red (.black (.red .empty) true 2)) false
example := Stendhal.FirstWeight.totalLastRedIndK0_tensorWordProjectiveClass (coverCartan arr)
  oneArrowParameters dividedLevels (.black (.red .empty) true 2)

example := Stendhal.blackLower_pow_eq_qfact_smul twoRedWeights (coverCartan arr) oneArrowParameters true 2

example := Stendhal.blackDividedLower_projection twoRedWeights (coverCartan arr) oneArrowParameters
  true 2 ({false} : Multiset Bool) (Graded.K0.of (Graded.GProj.regular _))

example := KLR.CycKLR.projectiveRepresentationX (fun _ => 1) (coverWeight arr) lam
  (fun _ => by rw [coverWeight_pair_iY]; rfl) oneArrowParameters

example := KLR.CycKLR.projectiveRepresentationX_E (fun _ => 1) (coverWeight arr) lam
  (fun _ => by rw [coverWeight_pair_iY]; rfl) oneArrowParameters true

end KangKashiwara

/-! ### Cautis–Lauda, `(BB_w)` (strong `sl₂` 2-representation on `Gr(•,2)`) -/

example : (TwoRep.Grassmannian.l2 ℚ).BBw := TwoRep.StrongSl2.bbw _

/-- The weight-`0` object `H*(Gr(1,2)) = H*(ℙ¹)` is nonzero. -/
example : ¬ Limits.IsZero (𝟙 ((TwoRep.Grassmannian.l2 ℚ).obj 1)) :=
  TwoRep.Grassmannian.not_isZero_id_l2Obj_one

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), Theorem 2.8 -/

/-- A weighted graph on two vertices: one edge `0 → 1` of weight `1` with `Q_e = u - v`, and a
loop of weight `0` at `0` with `P = 1`. -/
def wkGraph : WeightedKLR.WeightedGraph (Fin 2) ℚ ℚ where
  E := Unit
  tail _ := 0
  head _ := 1
  weight _ := 1
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop i := if i = 0 then some 1 else none

-- Centrality of a nonconstant symmetric dot polynomial, including a vertex with a loop.
example :
    WeightedKLR.GalleryAlgebra.poly
        (∑ s : WeightedKLR.Strand (Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 1),
          MvPolynomial.X s : WeightedKLR.PolyRing _ ℚ) ∈
      Subalgebra.center ℚ (WeightedKLR.GalleryAlgebra ℚ wkGraph
        (Finsupp.single 0 2 + Finsupp.single 1 1)) := by
  apply WeightedKLR.GalleryAlgebra.poly_mem_center
  intro g
  simp only [map_sum, MvPolynomial.rename_X]
  exact Equiv.sum_comp g.1 (fun s => MvPolynomial.X s)

example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.exists_basis (k := ℚ) (Γ := wkGraph)
    (ν := ν)
    ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ h₂ _ => by simp [wkGraph] at h₁⟩
    (fun _ h _ => by simp [wkGraph] at h)
    (fun i P h => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simp)
    (fun w => by
      refine IsRegular.of_ne_zero ?_
      simp only [WeightedKLR.Wall.factor, wkGraph, map_sub, MvPolynomial.aeval_X]
      simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2)
    (fun P a b h _ _ => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simpa [WeightedKLR.loopFactor] using isRegular_one)

/-- The straight-line choice: top end points moved by `ε ^ (index + 1)`, representative points
chosen in each full chamber. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.straightBasis (k := ℚ) (Γ := wkGraph)
    (ν := ν)
    ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ h₂ _ => by simp [wkGraph] at h₁⟩
    (fun _ h _ => by simp [wkGraph] at h)
    (fun i P h => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simp)
    (fun w => by
      refine IsRegular.of_ne_zero ?_
      simp only [WeightedKLR.Wall.factor, wkGraph, map_sub, MvPolynomial.aeval_X]
      simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2)
    (fun P a b h _ _ => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simpa [WeightedKLR.loopFactor] using isRegular_one)
    (ρ := fun s => (Fintype.equivFin _ s).val + 1)
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
    (fun _ => Nat.succ_ne_zero _)
    (pt := fun C => C.2.choose) (fun C => C.2.choose_spec)

/-! Webster, Theorem 2.8 under the hypotheses of the paper (`WeightedGraph.Standing`). -/

/-- `u - v` is homogeneous of degree `1` for the degrees `1, 1`, with unit coefficients of `u`
and `v`. -/
theorem isUnitHomogeneous_X_sub_X :
    WeightedKLR.WeightedGraph.IsUnitHomogeneous 1 1 1 1
      (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (MvPolynomial.isWeightedHomogeneous_X ℚ _ 0).sub
      (MvPolynomial.isWeightedHomogeneous_X ℚ _ 1)
  · simp [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]
  · simp [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- `wkGraph` satisfies Webster's standing hypothesis, with `d = 1`. -/
theorem wkGraph_standing : wkGraph.Standing := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun _ => ⟨1, 1, isUnitHomogeneous_X_sub_X⟩, ?_⟩
  intro i P h
  simp only [wkGraph] at h
  split_ifs at h
  obtain rfl := Option.some_injective _ h
  exact ⟨by simp, 1, 1, by simpa using isUnitHomogeneous_X_sub_X⟩

theorem wkGraph_dagger : wkGraph.Dagger :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ _ _ => by simp [wkGraph] at h₁⟩

theorem wkGraph_noZeroLoops : wkGraph.NoZeroLoops := fun _ h _ => by simp [wkGraph] at h

/-- Webster, Theorem 2.8, for Webster's algebra under Webster's hypotheses. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.exists_weightedKLRBasis (k := ℚ)
  (ν := ν) wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-- Webster, Theorem 2.8, for Webster's algebra under Webster's hypotheses, in Webster's indexing
(pairs of chambers, permutations, monomials). -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.exists_weightedKLRChamberBasis (k := ℚ)
  (ν := ν) wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-- Webster's chambers are the rank-ordered full chambers. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.chamberEquiv wkGraph ν

/-- The straight-line choice, in Webster's indexing. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.straightWeightedKLRChamberBasis (k := ℚ)
    (ν := ν) wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (ρ := fun s => (Fintype.equivFin _ s).val + 1)
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
    (fun _ => Nat.succ_ne_zero _)
    (pt := fun C => C.2.choose) (fun C => C.2.choose_spec)

/-- The straight-line choice, for Webster's algebra and for the corners. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.straightWeightedKLRBasis (k := ℚ)
    (ν := ν) wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (ρ := fun s => (Fintype.equivFin _ s).val + 1)
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
    (fun _ => Nat.succ_ne_zero _)
    (pt := fun C => C.2.choose) (fun C => C.2.choose_spec)

example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.cornerBasisOfStanding (k := ℚ)
    (ν := ν) (WeightedKLR.GalleryAlgebra.isChamberSegment_straightSegment wkGraph_dagger
      wkGraph_noZeroLoops (ρ := fun s => (Fintype.equivFin _ s).val + 1)
      (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
      (fun _ => Nat.succ_ne_zero _) (pt := fun C => C.2.choose) (fun C => C.2.choose_spec))
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), the Mackey filtration of §2.4 -/

/-- The shuffle-type filtration of a corner (proof of Webster's Theorem 2.19): for rank-ordered
chambers and the lower set of shuffle types bounded by `μ`, the intrinsic description of the
step by supports in the polynomial representation. -/
example (ν ν' ν₁ : Fin 2 →₀ ℕ) (C D : WeightedKLR.GalleryAlgebra.RankChamber wkGraph ν) (μ : Fin 2 → ℕ)
    (z : WeightedKLR.GalleryAlgebra ℚ wkGraph ν)
    (hz : z ∈ WeightedKLR.GalleryAlgebra.cornerSpace ℚ D.1 C.1) :=
  WeightedKLR.GalleryAlgebra.mem_mackeyFilt_iff (k := ℚ)
    (WeightedKLR.GalleryAlgebra.isChamberSegment_straightSegment wkGraph_dagger
      wkGraph_noZeroLoops (ρ := fun s => (Fintype.equivFin _ s).val + 1)
      (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
      (fun _ => Nat.succ_ne_zero _) (pt := fun C => C.2.choose) (fun C => C.2.choose_spec))
    wkGraph_dagger wkGraph_noZeroLoops
    (fun i P h => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simp)
    (fun w => by
      refine IsRegular.of_ne_zero ?_
      simp only [WeightedKLR.Wall.factor, wkGraph, map_sub, MvPolynomial.aeval_X]
      simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2)
    (fun P a b h _ _ => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simpa [WeightedKLR.loopFactor] using isRegular_one)
    ν' ν₁ C.2 D.2 (isLowerSet_Iic μ) hz

/-- The chamber segments of the filtration examples, for `wkGraph`. -/
theorem wkGraph_isChamberSegment (ν : Fin 2 →₀ ℕ) (C E : WeightedKLR.FullChamber wkGraph ν) :
    WeightedKLR.GalleryAlgebra.IsChamberSegment C E
      (WeightedKLR.GalleryAlgebra.straightSegment (fun s => (Fintype.equivFin _ s).val + 1)
        (fun C => C.2.choose) C E) :=
  WeightedKLR.GalleryAlgebra.isChamberSegment_straightSegment wkGraph_dagger
    wkGraph_noZeroLoops (ρ := fun s => (Fintype.equivFin _ s).val + 1)
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
    (fun _ => Nat.succ_ne_zero _) (pt := fun C => C.2.choose) (fun C => C.2.choose_spec) C E

/-- The regularity hypotheses of the filtration examples, for `wkGraph`. -/
theorem wkGraph_pSymm : wkGraph.PSymm := fun i P h => by
  simp only [wkGraph] at h
  split_ifs at h
  obtain rfl := Option.some_injective _ h
  simp

theorem wkGraph_wallRegular (ν : Fin 2 →₀ ℕ) (w : WeightedKLR.Wall wkGraph ν) :
    IsRegular (w.factor (k := ℚ)) := by
  refine IsRegular.of_ne_zero ?_
  simp only [WeightedKLR.Wall.factor, wkGraph, map_sub, MvPolynomial.aeval_X]
  simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2

theorem wkGraph_loopRegular (ν : Fin 2 →₀ ℕ) (P : MvPolynomial (Fin 2) ℚ)
    (a b : WeightedKLR.Strand ν) (h : wkGraph.loop a.1 = some P) (_ : a ≠ b)
    (_ : a.1 = b.1) : IsRegular (WeightedKLR.loopFactor P a b) := by
  simp only [wkGraph] at h
  split_ifs at h
  obtain rfl := Option.some_injective _ h
  simpa [WeightedKLR.loopFactor] using isRegular_one

open scoped TensorProduct in
/-- The steps of the shuffle-type filtration are sub-bimodules for juxtaposed diagrams
`ι_{ν₁;ν₂}(W_{ν₁} ⊗ W_{ν₂})` on the left and `ι_{ν';ν''}(W_{ν'} ⊗ W_{ν''})` on the right. -/
example (ν₁ ν₂ ν' ν'' : Fin 2 →₀ ℕ) (h : ν₁ + ν₂ = ν' + ν'')
    (C D C' D' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (ν' + ν'')) (μ : Fin 2 → ℕ)
    (u : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁ ⊗[ℚ]
      WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₂)
    (w : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν' ⊗[ℚ]
      WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν'')
    (z : WeightedKLR.GalleryAlgebra ℚ wkGraph (ν' + ν''))
    (hz : z ∈ WeightedKLR.GalleryAlgebra.mackeyFilt ℚ (wkGraph_isChamberSegment _)
      wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
      (wkGraph_loopRegular _) ν' ν₁ D.1 C.1 (Set.Iic μ)) :=
  WeightedKLR.GalleryAlgebra.inductionMap_mul_mul_mem_mackeyFilt _ _ _ _ _ _ h rfl
    C.2 C'.2 D.2 D'.2 (isLowerSet_Iic μ) u w hz

open scoped TensorProduct in
/-- The steps of the Mackey filtration of the whole algebra `W_ν` are sub-bimodules. -/
example (ν₁ ν₂ ν' ν'' : Fin 2 →₀ ℕ) (h : ν₁ + ν₂ = ν' + ν'') (μ : Fin 2 → ℕ)
    (u : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁ ⊗[ℚ]
      WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₂)
    (w : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν' ⊗[ℚ]
      WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν'')
    (x : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν' + ν''))
    (hx : x ∈ WeightedKLR.GalleryAlgebra.bimoduleFilt ℚ (wkGraph_isChamberSegment _)
      wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
      (wkGraph_loopRegular _) ν' ν₁ (Set.Iic μ)) :=
  WeightedKLR.GalleryAlgebra.inductionMap_mul_mul_mem_bimoduleFilt _ _ _ _ _ _ h rfl
    (isLowerSet_Iic μ) u w hx

/-- The subquotient of shuffle type `c` of the Mackey filtration of `Res ∘ Ind` is the middle
balanced tensor product (Webster, proof of Theorem 2.19, step (ii)). -/
example (a b c d : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.middleResIndEquiv (k := ℚ) (a := a) (b := b) (c := c) (d := d)
    wkGraph_dagger wkGraph_noZeroLoops (wkGraph_isChamberSegment _) wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) (isLowerSet_Iic (⇑c)) (Set.mem_Iic.2 le_rfl)
    subset_rfl (isLowerSet_Iio (⇑c)) (fun h => lt_irrefl _ (Set.mem_Iio.1 h))
    (fun _ h₁ h₂ => (lt_or_eq_of_le h₁).resolve_left h₂)

/-- The strict step of shuffle type `μ` of the filtration has a basis. -/
example (ν ν' ν₁ : Fin 2 →₀ ℕ) (C D : WeightedKLR.FullChamber wkGraph ν) (μ : Fin 2 → ℕ) :=
  WeightedKLR.GalleryAlgebra.mackeySubquotientBasis (k := ℚ) (wkGraph_isChamberSegment _)
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
    (wkGraph_loopRegular _) ν' ν₁ D C (Set.sdiff_subset : Set.Iic μ \ {μ} ⊆ Set.Iic μ)

/-- Any minimal gallery gives the basis element `b(g, m)` of Theorem 2.8 modulo shorter basis
elements of the same step of the shuffle-type filtration. -/
example (ν ν' ν₁ : Fin 2 →₀ ℕ) (C D : WeightedKLR.GalleryAlgebra.RankChamber wkGraph ν)
    (μ : Fin 2 → ℕ) (g : WeightedKLR.ColPerm ν)
    (hg : WeightedKLR.shuffleType ν' ν₁ g ∈ Set.Iic μ)
    (w : List (WeightedKLR.Hyp wkGraph ν)) (hw : WeightedKLR.GoodWord C.1.1 w)
    (he : C.1.flips w = g⁻¹ • D.1) (m : WeightedKLR.Strand ν →₀ ℕ) :=
  WeightedKLR.GalleryAlgebra.r_mul_galList_mul_sub_cornerBasis_mem (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) ν' ν₁ C.2 D.2 (isLowerSet_Iic μ) hg hw he m

/-- A juxtaposition is separated by the strands of the first factor, so it is the juxtaposition
of its restrictions. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' : WeightedKLR.FullChamber wkGraph ν')
    (C'' : WeightedKLR.FullChamber wkGraph ν'') :
    WeightedKLR.Juxtapose.chamber C' C'' =
      WeightedKLR.Juxtapose.chamber
        ((WeightedKLR.Juxtapose.leftEmb ν' ν'').restrict (WeightedKLR.Juxtapose.chamber C' C''))
        ((WeightedKLR.Juxtapose.rightEmb ν' ν'').restrict
          (WeightedKLR.Juxtapose.chamber C' C'')) :=
  WeightedKLR.Juxtapose.eq_chamber_of_isSeparated (WeightedKLR.Juxtapose.isSeparated_chamber _ _)

/-- Minimal galleries through the shuffle chambers exist and concatenate to a minimal gallery
from a juxtaposition `C` to a relabelled juxtaposition `g⁻¹ • D`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'') (g : WeightedKLR.ColPerm (ν' + ν'')) :
    ∃ w : List (WeightedKLR.Hyp wkGraph (ν' + ν'')),
      WeightedKLR.GoodWord (WeightedKLR.Juxtapose.chamber C' C'').1 w ∧
        (WeightedKLR.Juxtapose.chamber C' C'').flips w =
          g⁻¹ • WeightedKLR.Juxtapose.chamber D' D'' := by
  have hE := (WeightedKLR.Juxtapose.isSeparated_chamber D' D'').smul g⁻¹
  obtain ⟨a, b, c, ha, hfa, hb, hfb, hc, hfc⟩ :=
    WeightedKLR.FullChamber.exists_goodWord_shuffle wkGraph_dagger wkGraph_noZeroLoops
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' t)) _
      (WeightedKLR.Juxtapose.chamber C' C'') (g⁻¹ • WeightedKLR.Juxtapose.chamber D' D'')
  exact ⟨_, WeightedKLR.FullChamber.goodWord_shuffle
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'') hE ha hfa hb hfb hc hfc⟩

/-- Through the shuffle, the basis element `b(g, m)` of Theorem 2.8 is computed modulo shorter
basis elements of the same step of the filtration, here for juxtaposed `C` and `D`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ)
    (g : WeightedKLR.ColPerm (ν' + ν'')) (hg : WeightedKLR.shuffleType ν' ν' g ∈ Set.Iic μ)
    {a b c : List (WeightedKLR.Hyp wkGraph (ν' + ν''))}
    (ha : WeightedKLR.GoodWord (WeightedKLR.Juxtapose.chamber C' C'').1 a)
    (hfa : (WeightedKLR.Juxtapose.chamber C' C'').flips a =
      WeightedKLR.FullChamber.shuffleBot (fun t => decide (WeightedKLR.Strand.IsLeft ν' t))
        (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
        (WeightedKLR.Juxtapose.chamber C' C''))
    (hb : WeightedKLR.GoodWord (WeightedKLR.FullChamber.shuffleBot
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' t))
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'')).1 b)
    (hfb : (WeightedKLR.FullChamber.shuffleBot
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' t))
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'')).flips b =
        WeightedKLR.FullChamber.shuffleTop
          (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
          (WeightedKLR.Juxtapose.chamber C' C''))
    (hc : WeightedKLR.GoodWord (WeightedKLR.FullChamber.shuffleTop
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'')).1 c)
    (hfc : (WeightedKLR.FullChamber.shuffleTop
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'')).flips c =
        g⁻¹ • WeightedKLR.Juxtapose.chamber D' D'')
    (m : WeightedKLR.Strand (ν' + ν'') →₀ ℕ) :=
  WeightedKLR.GalleryAlgebra.shuffle_sub_cornerBasis_mem (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) ν' ν' hC hD
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'')
    (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') (isLowerSet_Iic μ) hg ha hfa hb hfb hc
    hfc m

open scoped TensorProduct in
/-- A gallery from a juxtaposition along which no strand crosses between the two blocks is the
juxtaposition `ι(a₁ ⊗ a₂)` of galleries of the two factors, here for the empty gallery. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' : WeightedKLR.FullChamber wkGraph ν')
    (C'' : WeightedKLR.FullChamber wkGraph ν'') :=
  WeightedKLR.Juxtapose.exists_galList_eq_galleryTensorHom (k := ℚ) (C' := C') (C'' := C'')
    (WeightedKLR.goodWord_nil _) (by simp)

open scoped TensorProduct in
/-- The bottom piece `a`, with the dots, and the top piece `r g c` of the factorization through
the shuffle lie in the image of the juxtaposition map `ι`, for juxtaposed `C` and `D`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'') (g : WeightedKLR.ColPerm (ν' + ν''))
    (f : WeightedKLR.PolyRing (ν' + ν'') ℚ) : True := by
  obtain ⟨a, b, c, ha, hfa, hb, hfb, hc, hfc⟩ :=
    WeightedKLR.FullChamber.exists_goodWord_shuffle wkGraph_dagger wkGraph_noZeroLoops
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' t))
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'') (g⁻¹ • WeightedKLR.Juxtapose.chamber D' D'')
  have _ := WeightedKLR.GalleryAlgebra.exists_bot_mul_poly_eq_castGallery (k := ℚ)
    (ν'' := ν'') rfl (WeightedKLR.Juxtapose.isSeparated_chamber C' C'') ha hfa f
  have _ := WeightedKLR.GalleryAlgebra.exists_r_mul_top_eq_castGallery (k := ℚ) (ν₂ := ν'')
    rfl (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') g hc hfc
  trivial

/-- The middle piece of the factorization through the shuffle may be replaced by the fixed
minimal gallery `shuffleWord`, modulo shorter basis elements of the same step. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ)
    (g : WeightedKLR.ColPerm (ν' + ν'')) (hg : WeightedKLR.shuffleType ν' ν' g ∈ Set.Iic μ)
    (m : WeightedKLR.Strand (ν' + ν'') →₀ ℕ) : True := by
  obtain ⟨a, b, c, ha, hfa, hb, hfb, hc, hfc⟩ :=
    WeightedKLR.FullChamber.exists_goodWord_shuffle wkGraph_dagger wkGraph_noZeroLoops
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' t))
      (fun t => decide (WeightedKLR.Strand.IsLeft ν' (g.1 t)))
      (WeightedKLR.Juxtapose.chamber C' C'') (g⁻¹ • WeightedKLR.Juxtapose.chamber D' D'')
  have _ := WeightedKLR.GalleryAlgebra.shuffle_sub_shuffleWord_mem (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) ν' ν' hC hD
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'')
    (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') (isLowerSet_Iic μ) hg ha hfa hb hfb hc
    hfc m
  trivial

/-- The factorization of the basis element `b(g, m)` of Theorem 2.8 as `ι(x) ψ_g ι(y)` modulo
shorter basis elements of the same step of the shuffle-type filtration, for juxtaposed `C`
and `D`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ)
    (g : WeightedKLR.ColPerm (ν' + ν'')) (hg : WeightedKLR.shuffleType ν' ν' g ∈ Set.Iic μ)
    (m : WeightedKLR.Strand (ν' + ν'') →₀ ℕ) :=
  WeightedKLR.GalleryAlgebra.exists_cornerBasis_sub_shuffleElt_mem (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) (ν'' := ν'') (ν₂ := ν'') rfl rfl hC hD
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'')
    (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') (isLowerSet_Iic μ) hg m

/-- The same factorization with `x`, `y` in Webster's algebras `W ⊗ W` and the shuffle element
`ψ^W_g` between rank-ordered chambers. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ)
    (g : WeightedKLR.ColPerm (ν' + ν'')) (hg : WeightedKLR.shuffleType ν' ν' g ∈ Set.Iic μ)
    (m : WeightedKLR.Strand (ν' + ν'') →₀ ℕ) :=
  WeightedKLR.GalleryAlgebra.exists_cornerBasis_sub_rankShuffleElt_mem (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) (ν'' := ν'') (ν₂ := ν'') rfl rfl hC hD
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'')
    (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') (isLowerSet_Iic μ) hg m

/-- The subquotient of shuffle type `μ` of the filtration of `e D * W * e C` is spanned by the
images of the maps `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]`, `g` of shuffle type `μ`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ) :=
  WeightedKLR.GalleryAlgebra.iSup_range_shuffleInductionMap (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) (ν'' := ν'') (ν₂ := ν'') rfl rfl hC hD
    (WeightedKLR.Juxtapose.isSeparated_chamber C' C'')
    (WeightedKLR.Juxtapose.isSeparated_chamber D' D'') (Set.Iio μ) (isLowerSet_Iic μ)

/-- Relabellings between rank-ordered chambers are trivial. -/
example (ν : Fin 2 →₀ ℕ) (A : WeightedKLR.FullChamber wkGraph ν) (hA : A.IsRankOrdered)
    (ρ : WeightedKLR.ColPerm ν) (hρ : (ρ • A).IsRankOrdered) : ρ = 1 :=
  WeightedKLR.FullChamber.eq_one_of_isRankOrdered_smul hA hρ

/-- The maps `x ⊗ y ↦ [e D ι(x) ψ^W_g ι(y) e C]` depend only on the strands that `g` sends into
the first block. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' D' : WeightedKLR.FullChamber wkGraph ν')
    (C'' D'' : WeightedKLR.FullChamber wkGraph ν'')
    (hC : (WeightedKLR.Juxtapose.chamber C' C'').IsRankOrdered)
    (hD : (WeightedKLR.Juxtapose.chamber D' D'').IsRankOrdered) (μ : Fin 2 → ℕ)
    (g g' : WeightedKLR.ColPerm (ν' + ν'')) (hg : WeightedKLR.shuffleType ν' ν' g ∈ Set.Iic μ)
    (hg' : WeightedKLR.shuffleType ν' ν' g' ∈ Set.Iic μ)
    (h : ∀ t, (g.1 t).IsLeft ν' ↔ (g'.1 t).IsLeft ν') :=
  WeightedKLR.GalleryAlgebra.shuffleInductionMap_eq_of_isLeft_iff (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) (ν'' := ν'') (ν₂ := ν'') rfl rfl hC hD
    (Set.Iio μ) (isLowerSet_Iic μ) hg hg' h

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), the grading of §2.1 -/

/-- The grading of Webster's standing hypothesis (doubled normalization): a `ℤ`-grading of the
gallery algebra of `wkGraph`, which has a loop of weight `0`. -/
example (ν : Fin 2 →₀ ℕ) :
    GradedAlgebra (wkGraph_standing.gradingDatum.grade (k := ℚ) (𝕜 := ℚ) ν) := inferInstance

/-- The crossing degree at the colour with a loop of weight `0` is the degree of `P_0`. -/
example : wkGraph_standing.gradingDatum.cross 0 =
    2 * wkGraph_standing.symm 0 * ((wkGraph_standing.loopMult 0 : ℤ) - 1) :=
  wkGraph_standing.gradingDatum_cross_of_some (P := 1) (by simp [wkGraph])

/-- The straight-line basis of Theorem 2.8 is homogeneous. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.straightBasisOfStanding_mem_grade
    (k := ℚ) (ν := ν) wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (ρ := fun s => (Fintype.equivFin _ s).val + 1)
    (fun _ _ h => (Fintype.equivFin _).injective (Fin.ext (by simpa using h)))
    (fun _ => Nat.succ_ne_zero _)
    (pt := fun C => C.2.choose) (fun C => C.2.choose_spec)

open scoped TensorProduct in
/-- Webster's map `ι_{ν';ν''}` (§2.4) adds degrees: `ι(1 ⊗ 1)` has degree `0 + 0`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :
    (WeightedKLR.Juxtapose.inductionMap ℚ wkGraph ν' ν'' (1 ⊗ₜ 1)).1 ∈
      wkGraph_standing.gradingDatum.grade (ν' + ν'') (0 + 0) :=
  WeightedKLR.Juxtapose.inductionMap_tmul_mem_grade _
    (Submodule.sum_mem _ fun C _ => wkGraph_standing.gradingDatum.e_mem_grade C)
    (Submodule.sum_mem _ fun C _ => wkGraph_standing.gradingDatum.e_mem_grade C)

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), degree of the Mackey twist (§2.4) -/

/-- An explicit grading datum for `wkGraph` (the values of Webster's standing grading with
`d = 1`): dots of degree `2`, the wall of the edge of degree `1`, the diagonal of colour `0`
(with its loop of weight `0` and `P = 1`) of degree `0`, that of colour `1` of degree `-2`. -/
def wkGrading : WeightedKLR.GradingDatum wkGraph where
  dot _ := 2
  wall _ := 1
  cross i := if i = 0 then 0 else -2
  isWeightedHomogeneous_Q _ := by
    have h0 := MvPolynomial.isWeightedHomogeneous_X ℚ ![(2 : ℤ), 2] 0
    have h1 := MvPolynomial.isWeightedHomogeneous_X ℚ ![(2 : ℤ), 2] 1
    simpa [wkGraph] using h0.sub h1
  cross_of_loop_none i hi := by
    have : i ≠ 0 := fun h => by simp [wkGraph, h] at hi
    simp [this]
  isWeightedHomogeneous_loop i P hP := by
    simp only [wkGraph] at hP
    split_ifs at hP with hi
    obtain rfl := Option.some_injective _ hP
    simpa [hi] using MvPolynomial.isWeightedHomogeneous_one ℚ ![(2 : ℤ), 2]

/-- The exchange degree is symmetric: one strand of colour `0` past one of colour `1`, in either
order, crosses the wall of the edge `0 → 1`, of degree `1`. The non-symmetric form `⟨j, i⟩` of
Webster's §2.4 would give `0` in one of the two orders. -/
example : wkGrading.pairDeg 0 1 = 1 ∧ wkGrading.pairDeg 1 0 = 1 := by
  decide

/-- Two strands of colour `1` cross one diagonal, of degree `-2 = -(α_1 · α_1)`. -/
example : wkGrading.pairDeg 1 1 = -2 := by
  simp [WeightedKLR.GradingDatum.pairDeg, wkGrading, wkGraph]

/-- The degree of the exchange of two juxtaposed blocks (the twist of the Mackey filtration in
the proof of Webster's Theorem 2.19). -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' : WeightedKLR.FullChamber wkGraph ν')
    (C'' : WeightedKLR.FullChamber wkGraph ν'') :=
  WeightedKLR.Juxtapose.segDeg_chamber_swapChamber wkGrading
    (fun C E => (WeightedKLR.GalleryAlgebra.exists_isChamberSegment wkGraph_dagger
      wkGraph_noZeroLoops C E).choose)
    (WeightedKLR.GalleryAlgebra.exists_isChamberSegment wkGraph_dagger wkGraph_noZeroLoops
      (WeightedKLR.Juxtapose.chamber C' C'') (WeightedKLR.Juxtapose.swapChamber C' C'')).choose_spec

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), Propositions 2.11, 2.12, 2.15 -/

/-- The graph `wkGraph` with real weights, for Proposition 2.12. -/
noncomputable def wkGraphReal : WeightedKLR.WeightedGraph (Fin 2) ℝ ℚ :=
  { wkGraph with weight := fun _ => 1 }

example (ν : Fin 2 →₀ ℕ) (B : WeightedKLR.Loading wkGraph ν) :=
  WeightedKLR.familyProjectiveEquiv (k := ℚ) (L := fun _ : Fin 2 => B) (b := 0) (b' := 1)
    (fun _ => Iff.rfl)

example (ν : Fin 2 →₀ ℕ) (B : WeightedKLR.Loading wkGraph ν) :=
  WeightedKLR.one_eq_familyIdemOff_add (k := ℚ) (L := fun _ : Fin 2 => B) (b := 0) 1
    (by decide) (fun _ => Iff.rfl)

example (ν : Fin 2 →₀ ℕ) (B : WeightedKLR.Loading wkGraph ν) :=
  WeightedKLR.familyRemoveEquiv (k := ℚ) (L := fun _ : Fin 2 => B) 1

example (ν : Fin 2 →₀ ℕ) := WeightedKLR.chamberComponentEquiv wkGraphReal ν

example (ν : Fin 2 →₀ ℕ) := WeightedKLR.weightedKLRShiftEquiv (Γ := wkGraph) ℚ ν ![1, 0]

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), Proposition 2.14 -/

/-- A weighted graph without loops: one edge `0 → 1` of weight `1` with `Q_e = u - v`. -/
def wkLooplessGraph : WeightedKLR.WeightedGraph (Fin 2) ℚ ℚ where
  E := Unit
  tail _ := 0
  head _ := 1
  weight _ := 1
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop _ := none

/-- `wkLooplessGraph` satisfies Webster's standing hypothesis, with `d = 1`. -/
theorem wkLooplessGraph_standing : wkLooplessGraph.Standing :=
  ⟨fun _ => 1, fun _ => one_pos, fun _ => ⟨1, 1, isUnitHomogeneous_X_sub_X⟩,
    fun _ _ h => by simp [wkLooplessGraph] at h⟩

theorem wkLooplessGraph_dagger : wkLooplessGraph.Dagger :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ _ _ => by simp [wkLooplessGraph] at h₁⟩

/-- Parallel edges with weights `−1,+1`, over an arbitrary coefficient field.
This is the loop-free graph whose bounded chamber obstructs right-tail detection. -/
def wkParallelGraph (K : Type*) [Field K] : WeightedKLR.WeightedGraph (Fin 2) ℚ K where
  E := Fin 2
  tail _ := 0
  head _ := 1
  weight e := if e = 0 then -1 else 1
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop _ := none

theorem wkParallelGraph_standing (K : Type*) [Field K] : (wkParallelGraph K).Standing := by
  refine ⟨fun _ => 1, fun _ => one_pos, ?_, fun _ _ h => by simp [wkParallelGraph] at h⟩
  intro e
  refine ⟨1, 1, rfl, ?_, ?_, ?_⟩
  · exact (MvPolynomial.isWeightedHomogeneous_X K _ 0).sub
      (MvPolynomial.isWeightedHomogeneous_X K _ 1)
  · simp [wkParallelGraph, MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]
  · simp [wkParallelGraph, MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem wkParallelGraph_dagger (K : Type*) [Field K] : (wkParallelGraph K).Dagger := by
  constructor
  · change ∀ e f : Fin 2, (0 : Fin 2) = 0 → (1 : Fin 2) = 1 →
      (if e = 0 then (-1 : ℚ) else 1) = (if f = 0 then -1 else 1) → e = f
    intro e f _ _ h
    fin_cases e <;> fin_cases f <;> norm_num at *
  · intro e f h _ _
    change (0 : Fin 2) = 1 at h
    exact (by decide : (0 : Fin 2) ≠ 1) h

theorem wkParallelGraph_noLoops (K : Type*) [Field K] :
    ∀ e, (wkParallelGraph K).head e ≠ (wkParallelGraph K).tail e := by
  intro e
  change (1 : Fin 2) ≠ 0
  decide

theorem wkParallelGraph_noZeroLoops (K : Type*) [Field K] :
    (wkParallelGraph K).NoZeroLoops :=
  fun e he => (wkParallelGraph_noLoops K e he).elim

/-- Two strands of each colour, exercising repeated refined colours and diagonals. -/
def wkParallelRepeatedWeight : Fin 2 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 2

example : wkParallelRepeatedWeight 0 = 2 ∧ wkParallelRepeatedWeight 1 = 2 := by
  simp [wkParallelRepeatedWeight]

/-- Webster, Proposition 2.14: the injective homomorphism from the KLR algebra to the weighted
KLR algebra on the evenly spaced loadings, for a graph without loops. -/
example (ν : Multiset (Fin 2)) :=
  WeightedKLR.spacedHom_injective (k := ℚ) (ν := ν) wkLooplessGraph_standing
    wkLooplessGraph_dagger (fun _ => by simp [wkLooplessGraph]) (fun _ => rfl)

/-- Webster, Proposition 2.14, surjectivity, for a graph without loops. -/
example (ν : Multiset (Fin 2)) :=
  WeightedKLR.spacedHom_surjective (k := ℚ) (ν := ν) wkLooplessGraph_standing
    wkLooplessGraph_dagger (fun _ => by simp [wkLooplessGraph]) (fun _ => rfl)

/-- Webster, Proposition 2.14: the KLR algebra is isomorphic to the weighted KLR algebra on the
evenly spaced loadings, for a graph without loops. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  WeightedKLR.spacedEquiv (k := ℚ) (ν := ν) wkLooplessGraph_standing
    wkLooplessGraph_dagger (fun _ => by simp [wkLooplessGraph]) (fun _ => rfl)

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), §2.4, Proposition 2.18 -/

/-- Webster, Proposition 2.18, on idempotents: juxtaposition of full chambers is associative. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) (C₁ : WeightedKLR.FullChamber wkGraph ν₁)
    (C₂ : WeightedKLR.FullChamber wkGraph ν₂) (C₃ : WeightedKLR.FullChamber wkGraph ν₃) :=
  WeightedKLR.Juxtapose.castChamber_chamber_assoc C₁ C₂ C₃

/-- Webster, Proposition 2.18, on algebras: the juxtaposition map `ι` is associative. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.inductionMap_assoc (k := ℚ) (Γ := wkGraph) ν₁ ν₂ ν₃ 1 1 1

open scoped TensorProduct in
/-- Webster, Proposition 2.18, on algebras: `1 ∈ W_0` is a two-sided unit for `ι`. -/
example (ν : Fin 2 →₀ ℕ) (a : WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν) :
    WeightedKLR.castW ℚ wkGraph (add_zero ν) (WeightedKLR.Juxtapose.inductionMap ℚ wkGraph ν 0
        (a ⊗ₜ 1)) = a ∧
      WeightedKLR.castW ℚ wkGraph (zero_add ν) (WeightedKLR.Juxtapose.inductionMap ℚ wkGraph 0 ν
        (1 ⊗ₜ a)) = a :=
  ⟨WeightedKLR.Juxtapose.inductionMap_tmul_one a, WeightedKLR.Juxtapose.inductionMap_one_tmul a⟩

/-- Webster, Proposition 2.18, generation clause: the iterated juxtaposition of the units of the
one-strand algebras is the idempotent of the evenly spaced loading. -/
example : WeightedKLR.juxtUnits ℚ wkGraph [0, 1, 1] =
    WeightedKLR.spacedW ℚ wkGraph (KLR.Seq.ofList [0, 1, 1]) :=
  WeightedKLR.juxtUnits_eq_spacedW [0, 1, 1]

/-- Webster, Proposition 2.18, generation clause: induction of the projectives of evenly spaced
loadings. -/
noncomputable example (i : KLR.Seq ((([0] : List (Fin 2)) : Multiset (Fin 2))))
    (j : KLR.Seq ((([1, 1] : List (Fin 2)) : Multiset (Fin 2)))) :=
  WeightedKLR.indSpacedEquiv ℚ wkGraph i j

/-- Webster, Proposition 2.18, on modules: associativity and units of induction, on the regular
modules. -/
noncomputable example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  (WeightedKLR.Juxtapose.indAssocEquiv ℚ wkGraph ν₁ ν₂ ν₃
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁)
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₂)
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₃),
    WeightedKLR.Juxtapose.indUnitLeftEquiv ℚ wkGraph ν₁
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁),
    WeightedKLR.Juxtapose.indUnitRightEquiv ℚ wkGraph ν₁
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁))

/-- Webster, Theorem 2.19, the algebra structure on `⊕_ν K₀(W_ν)` (ungraded, any commutative
ring): associativity and units of `[P] [Q] = [Ind (P ⊠ Q)]`, on the classes of the regular
modules. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  let x := Categorification.ProjK0.of
    (Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₁))
  let y := Categorification.ProjK0.of
    (Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₂))
  let z := Categorification.ProjK0.of
    (Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν₃))
  And.intro (WeightedKLR.Juxtapose.indK0_assoc ν₁ ν₂ ν₃ x y z)
    (And.intro (WeightedKLR.Juxtapose.indK0_one_left ν₁ x)
      (WeightedKLR.Juxtapose.indK0_one_right ν₁ x))

/-- Webster, Theorem 2.19, the coproduct component on `K₀` (ungraded): restriction of a finitely
generated projective module is finitely generated projective, and
`Δ_{ν';ν''} [W] = [Res W]`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  And.intro
    (WeightedKLR.Juxtapose.res_projective wkGraph ν' ν'' wkGraph_dagger wkGraph_noZeroLoops
      wkGraph_standing (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν' + ν'')))
    (WeightedKLR.Juxtapose.resK0_of wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
      (Categorification.FGProj.regular ℚ
        (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν' + ν''))))

/-- Webster, Proposition 2.18, on modules: coassociativity of restriction, for the regular module
and its transport along `castW`. -/
noncomputable example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  letI : Module (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν₁ + (ν₂ + ν₃)))
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν₁ + ν₂ + ν₃)) :=
    Module.compHom _ (WeightedKLR.castW ℚ wkGraph (add_assoc ν₁ ν₂ ν₃)).symm.toRingEquiv.toRingHom
  WeightedKLR.Juxtapose.resCoassocEquiv ℚ wkGraph ν₁ ν₂ ν₃
    (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν₁ + ν₂ + ν₃))
    (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν₁ + ν₂ + ν₃)) (AddEquiv.refl _)
    (fun d l => by
      change d * l = (WeightedKLR.castW ℚ wkGraph (add_assoc ν₁ ν₂ ν₃)).symm
        (WeightedKLR.castW ℚ wkGraph (add_assoc ν₁ ν₂ ν₃) d) * l
      rw [AlgEquiv.symm_apply_apply])

/-- Webster, Theorem 2.19, coassociativity of the coproduct on `K₀`, on the class of the regular
module. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.resK0_coassoc ν₁ ν₂ ν₃ wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (Categorification.ProjK0.of (Categorification.FGProj.regular ℚ
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph (ν₁ + ν₂ + ν₃))))

/-- Webster, proof of Theorem 2.19, the Mackey identity on `K₀` (ungraded):
`Δ_{ν₁;ν₂}(x · y)` is the sum over shuffle types of the classes of the Mackey pieces, here for
`(ν₁, ν₂) = (ν', ν'')` and for `(ν₁, ν₂) = (ν'', ν')`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  And.intro
    (WeightedKLR.exists_resK0_indK0_eq_sum_tensorK0 (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
      wkGraph_standing (rfl : ν' + ν'' = ν' + ν''))
    (WeightedKLR.exists_resK0_indK0_eq_sum_tensorK0 (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
      wkGraph_standing (add_comm ν'' ν'))

/-- Webster, proof of Theorem 2.19, the Mackey identity on `K₀` (ungraded) with each piece
written as twisted induction of restrictions, `(Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange)
(Δ_{a;b} x ⊠ Δ_{c;d} y)`, for `(ν₁, ν₂) = (ν', ν'')` and for `(ν₁, ν₂) = (ν'', ν')`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  And.intro
    (WeightedKLR.exists_resK0_indK0_eq_sum_twistK0 (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
      wkGraph_standing (rfl : ν' + ν'' = ν' + ν''))
    (WeightedKLR.exists_resK0_indK0_eq_sum_twistK0 (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
      wkGraph_standing (add_comm ν'' ν'))

/-- Webster, proof of Theorem 2.19, the Mackey identity on the classes `[P]`, `[Q]` of
finitely generated projective modules. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  WeightedKLR.exists_resK0_indK0_eq_sum (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
    wkGraph_standing (add_comm ν'' ν')

/-- Webster, Theorem 2.19, multiplicativity of the coproduct, module step (any commutative ring):
`Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)` is induction from the middle parabolic of
`(P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)`, here on the regular modules, and its form on classes. -/
noncomputable example (a b c d : Fin 2 →₀ ℕ) :=
  let R := fun ν : Fin 2 →₀ ℕ =>
    Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν)
  WeightedKLR.Juxtapose.extIndIndEquiv (R a) (R b) (R c) (R d)

/-- The class-level form of the previous example. -/
example (a b c d : Fin 2 →₀ ℕ) :=
  let R := fun ν : Fin 2 →₀ ℕ =>
    Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν)
  WeightedKLR.Juxtapose.middleIndK0_extTensor (Categorification.ProjK0.of (R a))
    (Categorification.ProjK0.of (R b)) (Categorification.ProjK0.of (R c))
    (Categorification.ProjK0.of (R d))

open scoped TensorProduct in
/-- Webster, Theorem 2.19, the twisted product of a shuffle layout on `K₀ ⊗_ℤ K₀` agrees with
twisted induction under the comparison maps (unconditional), for any shuffle layout. -/
example {ν' ν'' ν₁ ν₂ : Fin 2 →₀ ℕ} (L : WeightedKLR.ShuffleLayout ν' ν'' ν₁ ν₂) :=
  let R := fun ν : Fin 2 →₀ ℕ => Categorification.ProjK0.of
    (Categorification.FGProj.regular ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν))
  WeightedKLR.ShuffleLayout.extTensorHom_twistedMulK0 L (R L.a ⊗ₜ[ℤ] R L.b) (R L.c ⊗ₜ[ℤ] R L.d)

/-- Webster, Theorem 2.19, the Mackey formula for the coproduct on `K₀ ⊗_ℤ K₀` (ungraded). The
standing hypotheses are discharged for `wkGraph`; the bijectivity of the comparison maps
`K₀(W_μ) ⊗_ℤ K₀(W_{μ'}) → K₀(W_μ ⊗ W_{μ'})` is not proved in the library and stays a
hypothesis of this example. -/
example (ν' ν'' : Fin 2 →₀ ℕ)
    (hT : ∀ μ μ' : Fin 2 →₀ ℕ, Categorification.ProjK0.ExtTensorBijective ℚ
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph μ)
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph μ')) :=
  WeightedKLR.exists_coproductK0_indK0_eq_sum (k := ℚ) wkGraph_dagger wkGraph_noZeroLoops
    wkGraph_standing (add_comm ν'' ν') hT

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), §2.5, Proposition 2.20 (a) -/

/-- A weighted graph with one edge `e : 0 → 0` from a vertex to itself, of weight `1`, with
`Q_e = u - v`: when the weight of `e` is interpolated through `0`, a strand meets its own
ghost. -/
def wkSelfEdgeGraph : WeightedKLR.WeightedGraph (Fin 2) ℚ ℚ where
  E := Unit
  tail _ := 0
  head _ := 0
  weight _ := 1
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop _ := none

example (ν : Fin 2 →₀ ℕ) :=
  WeightedKLR.twGalleryRep ℚ (Γ := wkSelfEdgeGraph) (ν := ν)
    (fun _ _ h => by simp [wkSelfEdgeGraph] at h)

example (ν : Fin 2 →₀ ℕ) := WeightedKLR.twGalleryRep ℚ (Γ := wkGraph) (ν := ν)
  (fun i P h => by
    simp only [wkGraph] at h
    split_ifs at h
    obtain rfl := Option.some_injective _ h
    exact map_one _)

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), §2.5, Proposition 2.20 (b) -/

/-- Proposition 2.20 (b) for a graph with an edge from a vertex to itself. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.TwGalleryAlgebra.exists_basis (k := ℚ)
    (Γ := wkSelfEdgeGraph) (ν := ν)
    (fun _ _ h => by simp [wkSelfEdgeGraph] at h)
    (fun w => by
      refine IsRegular.of_ne_zero ?_
      simp only [WeightedKLR.Wall.factor, wkSelfEdgeGraph, map_sub, MvPolynomial.aeval_X]
      simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2)
    (fun _ _ _ h _ _ => by simp [wkSelfEdgeGraph] at h)

/-- Proposition 2.20 (b) for the graph of Theorem 2.8, with a loop polynomial. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.TwGalleryAlgebra.exists_basis (k := ℚ) (Γ := wkGraph)
    (ν := ν)
    (fun i P h => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      exact map_one _)
    (fun w => by
      refine IsRegular.of_ne_zero ?_
      simp only [WeightedKLR.Wall.factor, wkGraph, map_sub, MvPolynomial.aeval_X]
      simpa [sub_eq_zero, WeightedKLR.Wall.src, WeightedKLR.Wall.tgt] using w.2.2.2)
    (fun P a b h _ _ => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      simpa [WeightedKLR.loopFactor] using isRegular_one)

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), proof of Theorem 3.5 -/

/-- A weighted graph without loops: one edge `0 → 1` of weight `0` with `Q_e = u - v`. -/
def wkWeightZeroGraph : WeightedKLR.WeightedGraph (Fin 2) ℚ ℚ where
  E := Unit
  tail _ := 0
  head _ := 1
  weight _ := 0
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop _ := none

theorem wkWeightZeroGraph_standing : wkWeightZeroGraph.Standing :=
  ⟨fun _ => 1, fun _ => one_pos, fun _ => ⟨1, 1, isUnitHomogeneous_X_sub_X⟩,
    fun _ _ h => by simp [wkWeightZeroGraph] at h⟩

theorem wkWeightZeroGraph_dagger : wkWeightZeroGraph.Dagger :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ _ _ => by simp [wkWeightZeroGraph] at h₁⟩

/-- Webster, proof of Theorem 3.5: the homomorphism from `T̃^λ` to the chamber algebra of the
Crawley-Boevey graph modulo the dot on the `0`-strand, for two red strands `λ_1 = λ_2 = ω_0`
with weights `ϖ_1 = 0 < ϖ_2 = 1`. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  Stendhal.stTildeHom ν ℚ wkWeightZeroGraph (fun _ : Fin 2 => Finsupp.single 0 1)
    (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ)) wkWeightZeroGraph_dagger
    (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ _ h => Nat.cast_lt.mpr h)
    (fun _ => rfl) wkWeightZeroGraph_standing

/-- Webster, proof of Theorem 3.5: the homomorphism from `T̃^λ` is injective, for the same data. -/
example (ν : Multiset (Fin 2)) :=
  Stendhal.stTildeHom_injective (ν := ν) (k := ℚ) (Γ := wkWeightZeroGraph)
    (Λ := fun _ : Fin 2 => Finsupp.single 0 1)
    (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ)) wkWeightZeroGraph_dagger
    (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ _ h => Nat.cast_lt.mpr h)
    (fun _ => rfl) wkWeightZeroGraph_standing

/-- Webster, Theorem 3.5: `T̃^λ` is isomorphic to the chamber algebra of the Crawley-Boevey graph
modulo the dot on the `0`-strand, for the same data. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  Stendhal.stTildeEquiv ν ℚ wkWeightZeroGraph (fun _ : Fin 2 => Finsupp.single 0 1)
    (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ)) wkWeightZeroGraph_dagger
    (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ _ h => Nat.cast_lt.mpr h)
    (fun _ => rfl) wkWeightZeroGraph_standing

/-- Webster, Theorem 3.6: `T^λ` is isomorphic to that algebra modulo the idempotents of the
chambers whose leftmost strand is black, for the same data. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  Stendhal.stTensorEquiv ν ℚ wkWeightZeroGraph (fun _ : Fin 2 => Finsupp.single 0 1)
    (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ)) wkWeightZeroGraph_dagger
    (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ _ h => Nat.cast_lt.mpr h)
    (fun _ => rfl) wkWeightZeroGraph_standing

/-- Webster, arXiv:1309.3796v2, Proposition 4.16: the Stendhal terms form a basis of `T̃^λ`, for
the same data and a choice of reduced words. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  Stendhal.stendhalBasis (ν := ν) wkWeightZeroGraph (fun _ : Fin 2 => Finsupp.single 0 1)
    wkWeightZeroGraph_dagger (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl)
    (fun _ => rfl) wkWeightZeroGraph_standing
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)

/-- Webster, arXiv:1309.3796v2, Definition 4.6: the violating ideal is spanned by products of
two Stendhal terms through a violated sequence, for the same data. -/
example (ν : Multiset (Fin 2)) (x : Stendhal.StendhalAlgebra ℚ wkWeightZeroGraph.klrQ
    (fun _ : Fin 2 => Finsupp.single 0 1) ν) :=
  Stendhal.mem_violatedIdeal_iff (fun w => (TypeA.exists_reduced _ w).choose_spec) x

/-- Webster, arXiv:1209.2463v4, Theorem 3.6: the same spanning set for the violating ideal of the
reduced weighted KLR algebra, for the same data. -/
example (ν : Multiset (Fin 2)) (x : (Stendhal.stZeroDotIdeal ν ℚ
    (fun _ : Fin 2 => Finsupp.single 0 1) (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ))
    (Γ := wkWeightZeroGraph) (fun _ _ h => Nat.cast_lt.mpr h) (fun _ => rfl)).ringCon.Quotient) :=
  Stendhal.mem_stViolatingIdeal_iff (Γ := wkWeightZeroGraph) wkWeightZeroGraph_dagger
    (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ _ h => Nat.cast_lt.mpr h)
    (fun _ => rfl) wkWeightZeroGraph_standing (fun w => (TypeA.exists_reduced _ w).choose_spec) x

/-- Webster, arXiv:1209.2463v4, proof of Theorem 3.6: a chamber of the Crawley-Boevey graph on
all of `ν̃` is violating exactly when a relabelling of it is a violated Stendhal chamber, for the
same data. -/
example (ν : Multiset (Fin 2)) (C : WeightedKLR.FullChamber
    (wkWeightZeroGraph.crawleyBoeveyIn (fun _ : Fin 2 => Finsupp.single 0 1)
      fun r : Fin 2 => ((r : ℕ) : ℚ))
    (WeightedKLR.WeightedGraph.redWeight (Multiset.toFinsupp ν))) :=
  Stendhal.isViolatingChamber_iff (Λ := fun _ : Fin 2 => Finsupp.single 0 1)
    (fun _ _ h => Nat.cast_lt.mpr h) (fun _ => rfl) C

/-- Webster, arXiv:1209.2463v4, Theorem 3.6: the violating ideal on all chambers is generated by
the dot and the violated Stendhal chambers, for the same data. -/
example (ν : Multiset (Fin 2)) :=
  Stendhal.violatingIdeal_eq_span (ν := ν) (k := ℚ) (Γ := wkWeightZeroGraph)
    (Λ := fun _ : Fin 2 => Finsupp.single 0 1) (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ))
    (fun _ _ h => Nat.cast_lt.mpr h) (fun _ => rfl)

/-- Webster, arXiv:1209.2463v4, Theorem 3.6: the Stendhal corner of the violating ideal on all
chambers is `stViolatingIdeal`, for the same data. -/
example (ν : Multiset (Fin 2)) (x : WeightedKLR.ChamberAlgebra ℚ
    (Stendhal.stFull (ν := ν) (Γ := wkWeightZeroGraph) (fun _ : Fin 2 => Finsupp.single 0 1)
      (ϖ := fun r : Fin 2 => ((r : ℕ) : ℚ)) (fun _ _ h => Nat.cast_lt.mpr h) (fun _ => rfl))) :=
  Stendhal.mkₐ_mem_stViolatingIdeal_iff (fun _ _ h => Nat.cast_lt.mpr h) (fun _ => rfl) x

/-! ### Webster, §2, canonical deformations -/

/-- Standing data for `wkGraph`, with `d = 1` and `c_e = c_ē = 1`. -/
def wkStandingData : wkGraph.StandingData :=
  ⟨fun _ => 1, fun _ => one_pos, fun _ => 1, fun _ => 1, fun _ => isUnitHomogeneous_X_sub_X,
    fun i P h => by
      simp only [wkGraph] at h
      split_ifs at h
      obtain rfl := Option.some_injective _ h
      exact ⟨by simp, 1, 1, by simpa using isUnitHomogeneous_X_sub_X⟩⟩

/-- Webster, §2, the Proposition on canonical deformations: the deformation is free over `S`. -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.free_deform wkStandingData (ν := ν)
  wkGraph_dagger wkGraph_noZeroLoops

/-- The deformation has a parameter: `z_{e,0,0}` (one for the edge, as `c_e = 1`). -/
example : Nonempty wkStandingData.DeformVar :=
  ⟨⟨(), ⟨(⟨0, one_pos⟩, ⟨0, one_pos⟩), by simp [wkStandingData]⟩⟩⟩

/-! ### Webster, §2, steadied quotients -/

/-- The graph on two vertices with no edges. -/
def wkEdgelessGraph : WeightedKLR.WeightedGraph (Fin 2) ℚ ℚ where
  E := Empty
  tail := Empty.elim
  head := Empty.elim
  weight := Empty.elim
  Q := Empty.elim
  loop _ := none

/-- The weight `α₀ + α₁`. -/
abbrev wkNu : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

/-- The loading with the strand of colour `0` at `0` and the strand of colour `1` at `5`. -/
def wkSplitLoading : WeightedKLR.Loading wkEdgelessGraph wkNu where
  pos s := if s.1.1 = 0 then 0 else 5
  admissible := by
    refine ⟨?_, ?_, fun w => w.1.1.elim⟩
    · rintro ⟨⟨i, hi⟩, a⟩ ⟨⟨j, hj⟩, b⟩ h
      have ha : (a : ℕ) = 0 := by
        have := a.2
        fin_cases i <;> simp_all
      have hb : (b : ℕ) = 0 := by
        have := b.2
        fin_cases j <;> simp_all
      fin_cases i <;> fin_cases j <;> simp at h <;>
        · congr
          exact Fin.ext (by omega)
    · rintro ⟨⟨i, hi⟩, a⟩ ⟨⟨j, hj⟩, b⟩ hij hab
      have := a.2
      have := b.2
      simp only [Subtype.mk.injEq] at hij
      subst hij
      fin_cases i <;> simp_all

/-- The charge `c(α₀) = i`, `c(α₁) = 1`. -/
def wkCharge : WeightedKLR.Charge (Fin 2) where
  toFun i := if i = 0 then Complex.I else 1
  mem i := by
    fin_cases i
    · left; simp
    · right; simp

/-- The chamber of `wkSplitLoading` is unsteady for `wkCharge`: it is induced from
`α₀` and `α₁`, and `arg c(α₀) > arg c(α₁)`. -/
theorem wkSplit_isUnsteady : wkSplitLoading.chamber.IsUnsteady wkCharge := by
  refine ⟨Finsupp.single 0 1, by simp, by simp, ?_, ?_, ⟨wkSplitLoading, rfl, ?_⟩⟩
  · intro h
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp at this
  · show Complex.arg (wkCharge.eval (wkNu - Finsupp.single 0 1)) <
      Complex.arg (wkCharge.eval (Finsupp.single 0 1))
    rw [show wkNu - Finsupp.single 0 1 = Finsupp.single 1 1 from add_tsub_cancel_left _ _,
      WeightedKLR.Charge.eval_single, WeightedKLR.Charge.eval_single]
    simp [wkCharge, Complex.arg_I, Real.pi_pos]
  · rintro ⟨⟨i, hi⟩, a⟩ ⟨⟨j, hj⟩, b⟩ ha hb
    have := b.2
    simp only [WeightedKLR.Strand.IsLeft] at ha hb
    have hs : wkEdgelessGraph.sepBound = (0 : ℚ) :=
      Finset.sum_eq_zero fun e _ => (e : Empty).elim
    simp only [wkSplitLoading, hs]
    fin_cases i <;> fin_cases j <;> simp_all

/-- Webster, §2, steadied quotients: the idempotent of an unsteady chamber vanishes in the
steadied quotient. -/
example := WeightedKLR.SteadiedQuotient.mk_chamberIdem (k := ℚ) wkCharge wkSplit_isUnsteady

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), Corollary 2.16 -/

/-- `wkLooplessGraph` is a tree: one edge between two vertices. -/
theorem wkLooplessGraph_isTree : wkLooplessGraph.IsTree := by
  refine ⟨⟨fun _ => by simp [wkLooplessGraph], fun _ => rfl, fun _ _ _ => rfl,
    SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩, ?_⟩
  have h : wkLooplessGraph.simpleGraph.Adj 0 1 :=
    WeightedKLR.WeightedGraph.edgeGraph_adj.2 ⟨by decide, Or.inr ⟨(), trivial, rfl, rfl⟩⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · exact h.reachable
  · exact h.reachable.symm
  · rfl

/-- Webster, Corollary 2.16, first step: over any commutative ring, the weighted KLR algebra of a
forest is a full corner of the weighted KLR algebra on the evenly spaced loadings. -/
example (ν : Multiset (Fin 2)) :=
  wkLooplessGraph_isTree.1.exists_spacedCorner (k := ℚ) (ν := ν)

/-- Webster, Corollary 2.16: for a tree, the weighted KLR algebra is a full corner of the KLR
algebra (Morita equivalence). -/
example (ν : Multiset (Fin 2)) :=
  wkLooplessGraph_isTree.exists_klrCorner (k := ℚ) (ν := ν) wkLooplessGraph_standing

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), §3.1, red strands -/

/-- Webster, Theorem 2.8 for the Crawley-Boevey graph of `wkGraph` with one red strand of weight
`ϖ = 2` for the fundamental weight at the vertex `0`. -/
example (ν : Option (Fin 2) →₀ ℕ) := WeightedKLR.GalleryAlgebra.exists_redBasis (k := ℚ)
  (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) (ν := ν)
  wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing (fun _ _ _ => Subsingleton.elim _ _)

/-- The basis of the reduced quotient for `ν̃ = ν + α_0`. -/
example (ν : Fin 2 →₀ ℕ) : ∃ (ι : Type) (_ : Module.Basis ι ℚ
    (WeightedKLR.GalleryAlgebra.ReducedQuotient ℚ
      (wkGraph.crawleyBoevey (fun _ : Fin 1 => Finsupp.single 0 1) fun _ => (2 : ℚ))
      (WeightedKLR.WeightedGraph.redWeight ν) (WeightedKLR.GalleryAlgebra.zeroStrand ν))),
    True := by
  have hϖ : Function.Injective fun _ : Fin 1 => (2 : ℚ) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨P, hP, -⟩ := WeightedKLR.GalleryAlgebra.exists_span_segGallery (k := ℚ)
    (ν := WeightedKLR.WeightedGraph.redWeight ν)
    (WeightedKLR.WeightedGraph.crawleyBoevey_dagger wkGraph_dagger hϖ)
    (WeightedKLR.WeightedGraph.crawleyBoevey_noZeroLoops
      (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) wkGraph_noZeroLoops)
  exact ⟨_, WeightedKLR.GalleryAlgebra.redReducedBasis ν hP wkGraph_dagger wkGraph_noZeroLoops
    wkGraph_standing hϖ, trivial⟩

/-! Webster, Proposition 2.14 and Corollary 2.16 over a ring that is not a domain (`ZMod 4`). -/

/-- `u - v` over `ZMod 4`, homogeneous of degree `1` with unit coefficients. -/
theorem isUnitHomogeneous_X_sub_X_zmod4 :
    WeightedKLR.WeightedGraph.IsUnitHomogeneous 1 1 1 1
      (MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 4)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact (MvPolynomial.isWeightedHomogeneous_X (ZMod 4) _ 0).sub
      (MvPolynomial.isWeightedHomogeneous_X (ZMod 4) _ 1)
  · simp [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]
  · simp [MvPolynomial.coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- The graph `wkLooplessGraph` over `ZMod 4`. -/
def wkLooplessGraphZMod4 : WeightedKLR.WeightedGraph (Fin 2) ℚ (ZMod 4) where
  E := Unit
  tail _ := 0
  head _ := 1
  weight _ := 1
  Q _ := MvPolynomial.X 0 - MvPolynomial.X 1
  loop _ := none

theorem wkLooplessGraphZMod4_standing : wkLooplessGraphZMod4.Standing :=
  ⟨fun _ => 1, fun _ => one_pos, fun _ => ⟨1, 1, isUnitHomogeneous_X_sub_X_zmod4⟩,
    fun _ _ h => by simp [wkLooplessGraphZMod4] at h⟩

theorem wkLooplessGraphZMod4_dagger : wkLooplessGraphZMod4.Dagger :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ h₁ _ _ => by simp [wkLooplessGraphZMod4] at h₁⟩

theorem wkLooplessGraphZMod4_isTree : wkLooplessGraphZMod4.IsTree := by
  refine ⟨⟨fun _ => by simp [wkLooplessGraphZMod4], fun _ => rfl, fun _ _ _ => rfl,
    SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩, ?_⟩
  have h : wkLooplessGraphZMod4.simpleGraph.Adj 0 1 :=
    WeightedKLR.WeightedGraph.edgeGraph_adj.2 ⟨by decide, Or.inr ⟨(), trivial, rfl, rfl⟩⟩
  refine SimpleGraph.Connected.mk fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · exact h.reachable
  · exact h.reachable.symm
  · rfl

/-- Webster, Proposition 2.14, over `ZMod 4`. -/
noncomputable example (ν : Multiset (Fin 2)) :=
  WeightedKLR.spacedEquiv (k := ZMod 4) (ν := ν) wkLooplessGraphZMod4_standing
    wkLooplessGraphZMod4_dagger (fun _ => by simp [wkLooplessGraphZMod4]) (fun _ => rfl)

/-- Webster, Corollary 2.16, over `ZMod 4`. -/
example (ν : Multiset (Fin 2)) :=
  wkLooplessGraphZMod4_isTree.exists_klrCorner (k := ZMod 4) (ν := ν)
    wkLooplessGraphZMod4_standing

/-- Webster, Theorem 2.19, the coproduct component on `K₀`, over `ZMod 4`: restriction of the
regular module is finitely generated projective. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  And.intro
    (WeightedKLR.Juxtapose.res_projective wkLooplessGraphZMod4 ν' ν'' wkLooplessGraphZMod4_dagger
      (fun _ h _ => by simp [wkLooplessGraphZMod4] at h) wkLooplessGraphZMod4_standing
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 4) wkLooplessGraphZMod4 (ν' + ν'')))
    (WeightedKLR.Juxtapose.res_finite wkLooplessGraphZMod4 ν' ν'' wkLooplessGraphZMod4_dagger
      (fun _ h _ => by simp [wkLooplessGraphZMod4] at h) wkLooplessGraphZMod4_standing
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 4) wkLooplessGraphZMod4 (ν' + ν'')))

/-- Webster, Theorem 2.19, coassociativity of the coproduct on `K₀`, over `ZMod 4`, on the class
of the regular module. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.resK0_coassoc ν₁ ν₂ ν₃ wkLooplessGraphZMod4_dagger
    (fun _ h _ => by simp [wkLooplessGraphZMod4] at h) wkLooplessGraphZMod4_standing
    (Categorification.ProjK0.of (Categorification.FGProj.regular (ZMod 4)
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 4) wkLooplessGraphZMod4
        (ν₁ + ν₂ + ν₃))))

/-- Webster, Theorem 2.8 for the Crawley-Boevey graph of `wkGraph` with the new edge directed
into the new vertex (the orientation of Webster's Theorem 3.5). -/
example (ν : Option (Fin 2) →₀ ℕ) := WeightedKLR.GalleryAlgebra.exists_redBasisIn (k := ℚ)
  (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) (ν := ν)
  wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing (fun _ _ _ => Subsingleton.elim _ _)

/-- The basis of the reduced quotient for `ν̃ = ν + α_0`, new edges into the new vertex. -/
example (ν : Fin 2 →₀ ℕ) : ∃ (ι : Type) (_ : Module.Basis ι ℚ
    (WeightedKLR.GalleryAlgebra.ReducedQuotient ℚ
      (wkGraph.crawleyBoeveyIn (fun _ : Fin 1 => Finsupp.single 0 1) fun _ => (2 : ℚ))
      (WeightedKLR.WeightedGraph.redWeight ν) (WeightedKLR.GalleryAlgebra.zeroStrand ν))),
    True := by
  have hϖ : Function.Injective fun _ : Fin 1 => (2 : ℚ) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨P, hP, -⟩ := WeightedKLR.GalleryAlgebra.exists_span_segGallery (k := ℚ)
    (ν := WeightedKLR.WeightedGraph.redWeight ν)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_dagger wkGraph_dagger hϖ)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_noZeroLoops
      (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) wkGraph_noZeroLoops)
  exact ⟨_, WeightedKLR.GalleryAlgebra.redReducedBasisIn ν hP wkGraph_dagger wkGraph_noZeroLoops
    wkGraph_standing hϖ, trivial⟩

/-- Webster, §3.1: the reduced quotient for `ν̃ = ν + α_0`, new edges into the new vertex, acts
faithfully on the polynomial representation with the dot on the new strand set to zero. -/
example (ν : Fin 2 →₀ ℕ) : Function.Injective
    (WeightedKLR.GalleryAlgebra.reducedRep (k := ℚ)
      (WeightedKLR.WeightedGraph.crawleyBoeveyIn_psymm
        (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ))
        wkGraph_standing.psymm)
      (WeightedKLR.GalleryAlgebra.redWeight_zeroStrand ν)) := by
  have hϖ : Function.Injective fun _ : Fin 1 => (2 : ℚ) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨P, hP, -⟩ := WeightedKLR.GalleryAlgebra.exists_span_segGallery (k := ℚ)
    (ν := WeightedKLR.WeightedGraph.redWeight ν)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_dagger wkGraph_dagger hϖ)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_noZeroLoops
      (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) wkGraph_noZeroLoops)
  exact WeightedKLR.GalleryAlgebra.redReducedRepIn_injective ν hP wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing hϖ

/-- Webster, §3.1: the images of the reduced basis act by linearly independent operators. -/
example (ν : Fin 2 →₀ ℕ) : True := by
  have hϖ : Function.Injective fun _ : Fin 1 => (2 : ℚ) := fun _ _ _ => Subsingleton.elim _ _
  obtain ⟨P, hP, -⟩ := WeightedKLR.GalleryAlgebra.exists_span_segGallery (k := ℚ)
    (ν := WeightedKLR.WeightedGraph.redWeight ν)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_dagger wkGraph_dagger hϖ)
    (WeightedKLR.WeightedGraph.crawleyBoeveyIn_noZeroLoops
      (Λ := fun _ : Fin 1 => Finsupp.single 0 1) (ϖ := fun _ => (2 : ℚ)) wkGraph_noZeroLoops)
  have := WeightedKLR.GalleryAlgebra.linearIndependent_redReducedRepIn ν hP wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing hϖ
  trivial

/-! ### Webster, arXiv:1309.3796v2, Definitions 4.5–4.7 (Stendhal diagrams) -/

/-- The bigon relation (4.2) for one red strand `λ_1 = ϖ_0` over the vertices of `wkGraph`. -/
example (ν : Multiset (Fin 2)) (j : ℕ) (h : j + 1 < Multiset.card (Stendhal.stendhalWeight 1 ν))
    (s : KLR.Seq (Stendhal.stendhalWeight 1 ν))
    (hi : s.lbl ⟨j, by omega⟩ = .inl 0) (hr : s.lbl ⟨j + 1, h⟩ = .inr 0) :=
  Stendhal.StendhalAlgebraAllOrders.ψ_sq_black_red (k := ℚ) (Q := fun _ _ => 1)
    (Λ := fun _ => Finsupp.single 0 1) j h s 0 0 hi hr

/-- `T^λ` for one red strand: a `ℚ`-algebra. -/
example (ν : Multiset (Fin 2)) : Algebra ℚ (Stendhal.TensorProductAlgebra ℚ
    (fun _ _ : Fin 2 => (1 : MvPolynomial (Fin 2) ℚ)) (fun _ : Fin 1 => Finsupp.single 0 1) ν) :=
  inferInstance

/-! Webster §2.4: the juxtaposition map `ι_{ν';ν''}` on Webster's chambers. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.inductionMap_one (k := ℚ) (Γ := wkGraph) (ν' := ν') (ν'' := ν'')

example (ν' ν'' : Fin 2 →₀ ℕ) (c' : WeightedKLR.Chamber wkGraph ν')
    (c'' : WeightedKLR.Chamber wkGraph ν'') :=
  WeightedKLR.Juxtapose.inductionMap_e_tmul_e (k := ℚ) c'.toFull_isRankOrdered
    c''.toFull_isRankOrdered

/-! Webster §2.4, Proposition 2.18 (chamber level): juxtaposition of chambers is associative and
unital. -/
example (ν₁ ν₂ ν₃ : Fin 2 →₀ ℕ) (c₁ : WeightedKLR.Chamber wkGraph ν₁)
    (c₂ : WeightedKLR.Chamber wkGraph ν₂) (c₃ : WeightedKLR.Chamber wkGraph ν₃) :=
  WeightedKLR.Juxtapose.castChamber_chamber_assoc c₁.toFull c₂.toFull c₃.toFull

example (ν : Fin 2 →₀ ℕ) (c : WeightedKLR.Chamber wkGraph ν)
    (c₀ : WeightedKLR.Chamber wkGraph 0) :=
  WeightedKLR.Juxtapose.castChamber_chamber_zero_right c.toFull c₀.toFull

example (ν : Fin 2 →₀ ℕ) (c : WeightedKLR.Chamber wkGraph ν)
    (c₀ : WeightedKLR.Chamber wkGraph 0) :=
  WeightedKLR.Juxtapose.castChamber_chamber_zero_left c₀.toFull c.toFull

/-- Freeness of a corner over the parabolic subalgebra (proof of Webster, Theorem 2.19): for
rank-ordered `C'`, `C''` and `D`, the corner `e D * A * e (C' ∘ C'')` is the direct sum over the
representatives of the tensor products of the corners of the two sides. The regularity hypotheses
of the two sides follow from those of `ν' + ν''` along the strand embeddings. -/
example (ν' ν'' : Fin 2 →₀ ℕ) (C' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph ν')
    (C'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph ν'')
    (D : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (ν' + ν'')) :=
  WeightedKLR.GalleryAlgebra.parabolicCornerEquiv (k := ℚ) (wkGraph_isChamberSegment _)
    (wkGraph_isChamberSegment _) (wkGraph_isChamberSegment _) wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
    (WeightedKLR.GalleryAlgebra.isRegular_factor_of_embedding
      (WeightedKLR.Juxtapose.leftEmb ν' ν'') (wkGraph_wallRegular _))
    (WeightedKLR.GalleryAlgebra.isRegular_factor_of_embedding
      (WeightedKLR.Juxtapose.rightEmb ν' ν'') (wkGraph_wallRegular _))
    (wkGraph_loopRegular _)
    (WeightedKLR.GalleryAlgebra.isRegular_loopFactor_of_embedding
      (WeightedKLR.Juxtapose.leftEmb ν' ν'') (wkGraph_loopRegular _))
    (WeightedKLR.GalleryAlgebra.isRegular_loopFactor_of_embedding
      (WeightedKLR.Juxtapose.rightEmb ν' ν'') (wkGraph_loopRegular _))
    ((WeightedKLR.Juxtapose.isRankOrdered_chamber_iff C'.1 C''.1).2 ⟨C'.2, C''.2⟩) D.2

/-- The juxtaposed corner of `MiddleTensor` is the Mackey subquotient of shuffle type `c`
(Webster, Theorem 2.19), for `S = {μ ≤ c}` and `S' = {μ < c}`. The regularity hypotheses for the
four smaller weights are derived from those of `a + b + (c + d)`. -/
example (a b c d : Fin 2 →₀ ℕ) (L' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + c))
    (L'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (b + d))
    (R' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + b))
    (R'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (c + d)) :=
  WeightedKLR.Juxtapose.middleCornerEquiv (k := ℚ) (wkGraph_isChamberSegment _) wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _) (wkGraph_loopRegular _) L'.2 L''.2
    R'.2 R''.2 (S' := Set.Iio ⇑c) (S := Set.Iic ⇑c) (isLowerSet_Iic _) (Set.mem_Iic.2 le_rfl)
    subset_rfl (fun h => lt_irrefl _ (Set.mem_Iio.1 h))
    (fun _ h h' => (Set.mem_Iic.1 h).eq_or_lt.resolve_right h')

/-- The Iic/Iio form of the corner isomorphism of the Mackey filtration (Webster, Theorem 2.19). -/
example (a b c d : Fin 2 →₀ ℕ) (L' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + c))
    (L'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (b + d))
    (R' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + b))
    (R'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (c + d)) :=
  WeightedKLR.Juxtapose.middleCornerEquivIic (k := ℚ) (wkGraph_isChamberSegment _)
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
    (wkGraph_loopRegular _) L'.2 L''.2 R'.2 R''.2

/-- **Webster, Theorem 2.19, graded**: the juxtaposed corner shifted by
`∑ b_i c_j pairDeg i j` is graded isomorphic to the Mackey subquotient of shuffle type `c`. -/
example (a b c d : Fin 2 →₀ ℕ) (L' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + c))
    (L'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (b + d))
    (R' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (a + b))
    (R'' : WeightedKLR.GalleryAlgebra.RankChamber wkGraph (c + d)) :=
  WeightedKLR.Juxtapose.middleCornerGradedEquivIic (k := ℚ) wkGrading
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) L'.2 L''.2 R'.2 R''.2

/-- The Mackey filtration has finitely many distinct steps. -/
example (ν ν' ν₁ : Fin 2 →₀ ℕ) (D C : WeightedKLR.FullChamber wkGraph ν) :
    (Set.range (WeightedKLR.GalleryAlgebra.mackeyFilt ℚ (wkGraph_isChamberSegment _)
      wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm (wkGraph_wallRegular _)
      (wkGraph_loopRegular _) ν' ν₁ D C)).Finite :=
  WeightedKLR.GalleryAlgebra.finite_range_mackeyFilt _ _ _ _ _ _ ν' ν₁ D C

/-- A subquotient of the Mackey filtration whose occurring shuffle types all lie in `S'`
vanishes; here for `S' = S = ∅`. -/
example (ν ν' ν₁ : Fin 2 →₀ ℕ) (D C : WeightedKLR.FullChamber wkGraph ν) :=
  WeightedKLR.GalleryAlgebra.subsingleton_mackeySubquotient (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) ν' ν₁ D C (S' := ∅) (S := ∅) subset_rfl
    Set.inter_subset_left

/-! ### Webster, weighted KLR algebras (arXiv:1209.2463v4), graded `K₀` (Theorem 2.19) -/

/-- `W_ν` has a graded dimension for the grading of the standing hypothesis (Theorem 2.8). -/
example (ν : Fin 2 →₀ ℕ) := WeightedKLR.GalleryAlgebra.hasGdim_klrGrade (k := ℚ) (ν := ν)
  wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-- Graded induction `Ind (P ⊠ P')` of graded projective modules (Definition 2.17). -/
example (ν' ν'' : Fin 2 →₀ ℕ) (P : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade ν'))
    (P' : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade ν'')) :=
  wkGraph_standing.gradingDatum.indProj P P'

/-- The product on `K₀(W_{ν'}) ⊗_{ℤ[q,q⁻¹]} K₀(W_{ν''})` on generators (Theorem 2.19). -/
example (ν' ν'' : Fin 2 →₀ ℕ) (P : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade ν'))
    (P' : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade ν'')) :=
  wkGraph_standing.gradingDatum.indK0Tensor_of ν' ν'' P P'


/-- Graded restriction `Res_{ν';ν''}` on graded `K₀` (Theorem 2.19), on generators. -/
example (ν' ν'' : Fin 2 →₀ ℕ)
    (L : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade (ν' + ν''))) :=
  wkGraph_standing.gradingDatum.resK0_of (ν' := ν') (ν'' := ν'') wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing L

/-- Additivity of graded `K₀` along a graded short exact sequence, applied to the split sequence
`P → P ⊕ Q → Q` of graded projective `W_ν`-modules. -/
example (ν : Fin 2 →₀ ℕ) (P Q : Graded.GProj (wkGraph_standing.gradingDatum.klrGrade ν)) :
    Graded.K0.of (P.prod Q) = Graded.K0.of P + Graded.K0.of Q :=
  Graded.K0.of_eq_add_of_exact P (P.prod Q) Q (LinearMap.inl _ _ _) (LinearMap.snd _ _ _)
    (fun _ _ hx => Graded.mem_prod.2 ⟨hx, zero_mem _⟩) (fun _ _ hx => (Graded.mem_prod.1 hx).2)
    LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd

/-- The comparison map of the middle parabolic raises degrees by `middleShift`, and the Mackey
subquotient of shuffle type `c` of `Res ∘ Ind` is the shifted middle tensor product as a graded
space (Theorem 2.19). -/
example (a b c d : Fin 2 →₀ ℕ) :=
  WeightedKLR.Juxtapose.middleResIndGradedEquivIic (k := ℚ) (a := a) (b := b) (c := c) (d := d)
    wkGraph_dagger wkGraph_noZeroLoops wkGrading (wkGraph_isChamberSegment _) wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _)

/-- The graded Mackey filtration of `Res_{ν₁;ν₂} Ind_{ν';ν''}` in graded `K₀`, with the pieces
shifted by `middleShift` (Theorem 2.19). -/
example (ν' ν'' ν₁ ν₂ : Fin 2 →₀ ℕ) (h : ν₁ + ν₂ = ν' + ν'') :=
  WeightedKLR.GalleryAlgebra.exists_resInd_balancedTensor_eq_sum_graded (k := ℚ)
    (wkGraph_isChamberSegment _) wkGraph_dagger wkGraph_noZeroLoops wkGraph_pSymm
    (wkGraph_wallRegular _) (wkGraph_loopRegular _) rfl h wkGrading

/-- **Webster, Theorem 2.19, graded Mackey formula**: `Res_{ν₁;ν₂} [Ind (P ⊠ P')]` is the sum over
shuffle types of `q^{middleShift}` times the class of the middle balanced tensor product, for
`(ν₁, ν₂) = (ν'', ν')`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  WeightedKLR.exists_resK0_indK0_eq_sum_graded (k := ℚ) wkGrading wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing (add_comm ν'' ν')

/-- **Webster, Theorem 2.19, graded Mackey formula in twisted form**:
`Res_{ν₁;ν₂}(x · y) = Σ q^{middleShift} (Ind ⊗ Ind)(exchange)(Res x ⊠ Res y)` on graded `K₀`,
for `(ν₁, ν₂) = (ν'', ν')`. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  WeightedKLR.exists_resK0_indK0_eq_sum_twistK0Graded (k := ℚ) wkGrading wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing (add_comm ν'' ν')


/-- Graded induction from the middle parabolic of an external product of external products
(Theorem 2.19): `middleInd ((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)`. -/
example (a b c d : Fin 2 →₀ ℕ) := wkGrading.middleIndK0_extTensor (k := ℚ) a b c d

/-- The graded twisted product of a shuffle layout on generators (Theorem 2.19). -/
example {ν' ν'' ν₁ ν₂ : Fin 2 →₀ ℕ} (L : WeightedKLR.ShuffleLayout ν' ν'' ν₁ ν₂) :=
  L.twistedMulK0Graded_tmul (k := ℚ) wkGrading

/-- Graded dimensions of the `W_ν`, from Theorem 2.8, as a local instance. -/
local instance wkHasGdim (μ : Fin 2 →₀ ℕ) :
    Graded.HasGdim (wkGraph_standing.gradingDatum.klrGrade μ) :=
  WeightedKLR.GalleryAlgebra.hasGdim_klrGrade (k := ℚ) (ν := μ) wkGraph_dagger
    wkGraph_noZeroLoops wkGraph_standing

local instance wkParallelHasGdim (K : Type*) [Field K] (μ : Fin 2 →₀ ℕ) :
    Graded.HasGdim ((wkParallelGraph_standing K).gradingDatum.klrGrade μ) :=
  WeightedKLR.GalleryAlgebra.hasGdim_klrGrade (k := K) (ν := μ)
    (wkParallelGraph_dagger K) (wkParallelGraph_noZeroLoops K) (wkParallelGraph_standing K)

/-- The central finiteness input of A0, on the concrete weighted graph, for every weight. -/
example (ν : Fin 2 →₀ ℕ) :
    Module.Finite (WeightedKLR.GalleryAlgebra.colourSym ℚ ν)
      (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν) :=
  WeightedKLR.GalleryAlgebra.finite_colourSym
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-- The finite-dimensional augmentation quotient used for A0, with all graph hypotheses proved. -/
example (ν : Fin 2 →₀ ℕ) :
    FiniteDimensional ℚ (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν ⧸
      augSubmodule (WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph ν)
        (WeightedKLR.GalleryAlgebra.colourSymAug ℚ ν)) :=
  WeightedKLR.GalleryAlgebra.finiteDimensional_quotient_colourSymAug
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing

/-- A0 for Webster Theorem 2.19: every graded simple top of an indecomposable graded
projective over the concrete weighted algebras is finite-dimensional. This supplies `fdA`, `fdB`. -/
example (ν : Fin 2 →₀ ℕ)
    (b : Graded.GProj.IndecClass (wkGraph_standing.gradingDatum.klrGrade ν)) :
    FiniteDimensional ℚ b.top :=
  WeightedKLR.GradingDatum.finiteDimensional_top
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing b

/-- A0 for Webster Theorem 2.19: finite-dimensional graded simple tops of the tensor algebra,
supplying `fdC` without an absolute-irreducibility assumption. -/
example (ν μ : Fin 2 →₀ ℕ)
    (c : Graded.GProj.IndecClass (Graded.tensorGrading
      (wkGraph_standing.gradingDatum.klrGrade ν) (wkGraph_standing.gradingDatum.klrGrade μ))) :
    FiniteDimensional ℚ c.top :=
  WeightedKLR.GradingDatum.finiteDimensional_top_tensor
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing c

/-- The scalar-endomorphism intermediate result for A at a weight using both colours once.
The graph and the simple-top hypotheses are supplied by proved declarations. -/
example
    (b : Graded.GProj.IndecClass (wkGraph_standing.gradingDatum.klrGrade
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ wkGraph
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)] b.top) :
    ∃ c : ℚ, ∀ m, φ m = c • m := by
  exact WeightedKLR.GradingDatum.exists_eq_smul_of_isGradedSimple_multiplicityFree
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (by intro i; fin_cases i <;> simp) (Graded.GProj.IndecClass.isGradedSimple_top b) φ

/-- The ungraded finite-simple scalar theorem on the parallel-edge graph over `ℚ`,
with two strands of each colour. Finite dimension and nilpotent dots are proved
for the simple top rather than assumed. -/
example
    (b : Graded.GProj.IndecClass ((wkParallelGraph_standing ℚ).gradingDatum.klrGrade
      wkParallelRepeatedWeight))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ (wkParallelGraph ℚ)
      wkParallelRepeatedWeight] b.top) : ∃ c : ℚ, ∀ m, φ m = c • m := by
  have hM := Graded.GProj.IndecClass.isGradedSimple_top b
  have : FiniteDimensional ℚ b.top :=
    WeightedKLR.GradingDatum.finiteDimensional_top (wkParallelGraph_dagger ℚ)
    (wkParallelGraph_noZeroLoops ℚ) (wkParallelGraph_standing ℚ) b
  have := hM.isSimpleModule
  exact WeightedKLR.exists_eq_smul_of_isSimpleModule (wkParallelGraph_dagger ℚ)
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noZeroLoops ℚ) (fun _ => rfl)
    (WeightedKLR.GradingDatum.smulNilpotent_reducedDot_of_isGradedSimple
      (wkParallelGraph_dagger ℚ) (wkParallelGraph_noZeroLoops ℚ)
      (wkParallelGraph_standing ℚ) hM) φ

/-- The same finite-simple theorem in characteristic two, at the repeated weight. -/
example
    (b : Graded.GProj.IndecClass ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade
      wkParallelRepeatedWeight))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 2)
      (wkParallelGraph (ZMod 2)) wkParallelRepeatedWeight] b.top) :
    ∃ c : ZMod 2, ∀ m, φ m = c • m := by
  have hM := Graded.GProj.IndecClass.isGradedSimple_top b
  have : FiniteDimensional (ZMod 2) b.top :=
    WeightedKLR.GradingDatum.finiteDimensional_top (wkParallelGraph_dagger (ZMod 2))
    (wkParallelGraph_noZeroLoops (ZMod 2)) (wkParallelGraph_standing (ZMod 2)) b
  have := hM.isSimpleModule
  exact WeightedKLR.exists_eq_smul_of_isSimpleModule (wkParallelGraph_dagger (ZMod 2))
    (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_noZeroLoops (ZMod 2)) (fun _ => rfl)
    (WeightedKLR.GradingDatum.smulNilpotent_reducedDot_of_isGradedSimple
      (wkParallelGraph_dagger (ZMod 2)) (wkParallelGraph_noZeroLoops (ZMod 2))
      (wkParallelGraph_standing (ZMod 2)) hM) φ

/-- The graded-simple scalar theorem over `ℚ`, with parallel edges and repeated colours. -/
example
    (b : Graded.GProj.IndecClass ((wkParallelGraph_standing ℚ).gradingDatum.klrGrade
      wkParallelRepeatedWeight))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra ℚ (wkParallelGraph ℚ)
      wkParallelRepeatedWeight] b.top) : ∃ c : ℚ, ∀ m, φ m = c • m :=
  WeightedKLR.GradingDatum.exists_eq_smul_of_isGradedSimple (wkParallelGraph_dagger ℚ)
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noZeroLoops ℚ) (fun _ => rfl)
    (Graded.GProj.IndecClass.isGradedSimple_top b) φ

/-- The graded-simple scalar theorem in characteristic two, at the same repeated weight. -/
example
    (b : Graded.GProj.IndecClass ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade
      wkParallelRepeatedWeight))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 2)
      (wkParallelGraph (ZMod 2)) wkParallelRepeatedWeight] b.top) :
    ∃ c : ZMod 2, ∀ m, φ m = c • m :=
  WeightedKLR.GradingDatum.exists_eq_smul_of_isGradedSimple (wkParallelGraph_dagger (ZMod 2))
    (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_noZeroLoops (ZMod 2)) (fun _ => rfl)
    (Graded.GProj.IndecClass.isGradedSimple_top b) φ

/-- All five tensor-comparison fields for two multiplicity-free weights. The supports
overlap, so A0's tensor finiteness is used without assuming their sum multiplicity-free. -/
example : Graded.TensorK0Hyp
    (wkGraph_standing.gradingDatum.klrGrade
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1))
    (wkGraph_standing.gradingDatum.klrGrade
      (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1)) := by
  exact WeightedKLR.GradingDatum.tensorK0Hyp_multiplicityFree
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing
    (by intro i; fin_cases i <;> simp) (by intro i; fin_cases i <;> simp)

/-- All tensor-comparison fields at repeated weights on the loop-free parallel-edge
graph over `ℚ`, with no multiplicity-free assumption. -/
example : Graded.TensorK0Hyp
    ((wkParallelGraph_standing ℚ).gradingDatum.klrGrade wkParallelRepeatedWeight)
    ((wkParallelGraph_standing ℚ).gradingDatum.klrGrade wkParallelRepeatedWeight) :=
  WeightedKLR.GradingDatum.tensorK0Hyp (wkParallelGraph_standing ℚ).gradingDatum
    (wkParallelGraph_dagger ℚ) (wkParallelGraph_standing ℚ) (wkParallelGraph_noZeroLoops ℚ)
    (fun _ => rfl) wkParallelRepeatedWeight wkParallelRepeatedWeight

/-- The same unrestricted tensor-comparison check in characteristic two. -/
example : Graded.TensorK0Hyp
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade wkParallelRepeatedWeight)
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade wkParallelRepeatedWeight) :=
  WeightedKLR.GradingDatum.tensorK0Hyp (wkParallelGraph_standing (ZMod 2)).gradingDatum
    (wkParallelGraph_dagger (ZMod 2)) (wkParallelGraph_standing (ZMod 2))
    (wkParallelGraph_noZeroLoops (ZMod 2)) (fun _ => rfl)
    wkParallelRepeatedWeight wkParallelRepeatedWeight

/-- The conditional graded coproduct formula still applies to the graph with a recorded
loop. Its tensor-comparison hypothesis is explicit in this example. -/
example (ν' ν'' : Fin 2 →₀ ℕ)
    (hT : ∀ μ μ' : Fin 2 →₀ ℕ, Graded.TensorK0Hyp (wkGraph_standing.gradingDatum.klrGrade μ)
      (wkGraph_standing.gradingDatum.klrGrade μ')) :=
  WeightedKLR.exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp (k := ℚ)
    wkGraph_standing.gradingDatum
    wkGraph_dagger wkGraph_noZeroLoops wkGraph_standing (add_comm ν'' ν') hT

/-- Webster Theorem 2.19 on a loop-free graph with parallel edges: the graded coproduct
formula discharges the tensor-comparison input internally, for arbitrary block weights. -/
example (ν' ν'' : Fin 2 →₀ ℕ) :=
  WeightedKLR.exists_coproductK0_indK0_eq_sum_graded (k := ℚ)
    (wkParallelGraph_standing ℚ).gradingDatum (wkParallelGraph_dagger ℚ)
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noZeroLoops ℚ) (fun _ => rfl)
    (add_comm ν'' ν')

/-- The weighted polynomial conditions include a graph with a recorded loop;
Cartan construction deletes that loop. -/
example : KLR.IsRouquierQ wkGraph_standing.cartanDatum wkGraph.klrQ :=
  wkGraph_standing.isRouquierQ

/-- The parallel-edge product satisfies Rouquier's conditions in characteristic two. -/
example : KLR.IsRouquierQ (wkParallelGraph_standing (ZMod 2)).cartanDatum
    (wkParallelGraph (ZMod 2)).klrQ :=
  (wkParallelGraph_standing (ZMod 2)).isRouquierQ

/-- Graded principal-projective induction at two nonzero weights. -/
example := wkGraph_standing.gradingDatum.indK0_ofIdempotent
  (ν := Finsupp.single (0 : Fin 2) 1) (μ := Finsupp.single (1 : Fin 2) 1)
  (e := 1) (e' := 1) IsIdempotentElem.one IsIdempotentElem.one
  (SetLike.one_mem_graded _) (SetLike.one_mem_graded _)

/-- The ordinary sequence idempotent transfers to a homogeneous weighted entry. -/
example := (wkParallelGraph_standing ℚ).gradingDatum.spacedEntryMap_mem_klrGrade
  (wkParallelGraph_standing ℚ) (wkParallelGraph_dagger ℚ)
  (wkParallelGraph_noLoops ℚ) (fun _ => rfl)
  (((wkParallelGraph_standing ℚ).gradingDatum.toKLRGrading
    (wkParallelGraph_noLoops ℚ) (fun _ => rfl)).e_mem_grade (KLR.KLRAlgebra.Seq.ofList [0, 1] rfl))
  (KLR.KLRAlgebra.Seq.ofList [0, 1] rfl) (KLR.KLRAlgebra.Seq.ofList [0, 1] rfl)

/-- A graded Serre window for the parallel-edge polynomial in characteristic two. -/
private abbrev rqC := (wkParallelGraph_standing (ZMod 2)).cartanDatum
private abbrev rqQ := (wkParallelGraph (ZMod 2)).klrQ
private theorem rqHyp : KLR.IsRouquierQ rqC rqQ :=
  (wkParallelGraph_standing (ZMod 2)).isRouquierQ

private abbrev redBlockWeights : Fin 2 → Fin 2 →₀ ℕ := fun r => Finsupp.single r 2
private abbrev redBlockGrade := Stendhal.stendhalGradingDatum redBlockWeights rqHyp.gradingDatum
  (fun i => rqC.dot i i / 2) (fun i => by
    change rqC.dot i i = _
    obtain ⟨n, hn⟩ := rqC.dot_self_even i
    omega)

/-- The external product for two nonempty red blocks in characteristic two. -/
example := Stendhal.blocksK0Equiv redBlockWeights ({0} : Multiset (Fin 2)) rqHyp
  redBlockWeights ({1} : Multiset (Fin 2)) redBlockGrade redBlockGrade

/-- Finiteness in a nonzero characteristic with two red strands and repeated black labels. -/
example := Stendhal.tensorProductAlgebra_finite (fun r : Fin 2 => Finsupp.single r 2)
  ({0, 1, 0} : Multiset (Fin 2)) rqHyp

/-- Two red weights and repeated, interacting black colours in characteristic two. -/
example := Stendhal.span_dividedSequenceProj
  (fun r : Fin 2 => Finsupp.single r 2) rqC rqHyp ({0, 1, 0} : Multiset (Fin 2))

/-- Webster's Proposition 4.32 in characteristic two: two red strands, black labels `0, 1, 0`. -/
example := Stendhal.lastRedBlackEquiv rqQ (fun r : Fin 2 => Finsupp.single r 2) (0 : Fin 2)
  ({1, 0} : Multiset (Fin 2)) rqHyp

/-- The `Eᵢ` part of Webster's Proposition 4.32 over the field `ZMod 2`, same data. -/
example := Stendhal.lastRedBlackMirrorEquiv rqQ (fun r : Fin 2 => Finsupp.single r 2)
  (0 : Fin 2) ({1, 0} : Multiset (Fin 2)) rqHyp

/-- The degree of the crossing in Webster's Proposition 4.32, with Webster's degrees. -/
example := Stendhal.lastRedBlackCrossing_mem_grade rqQ redBlockWeights (0 : Fin 2)
  ({1} : Multiset (Fin 2)) redBlockGrade

/-- Three equal strands vanish at level two, and the third lowering kills the vacuum. -/
example := KLR.CycKLR.subsingleton_replicate_of_lt rqQ (fun _ => 2) 0 3 (by decide)
example := KLR.CycKLR.lower_pow_vacuum_eq_zero (fun _ => 2) rqHyp.gradingDatum 0
  (Graded.K0.of (Graded.GProj.regular _))

/-- Eventual vanishing in a two-colour block for the parallel-edge polynomial
over the field of two elements. -/
example := KLR.CycKLR.eventually_subsingleton_replicate_add (fun _ => 2)
  rqHyp.aeval_zero_first 0 ({1} : Multiset (Fin 2))
example := KLR.CycKLR.lower_locally_nilpotent (fun _ => 2) rqHyp.aeval_zero_first
  rqHyp.gradingDatum 0 (DirectSum.lof (LaurentPolynomial ℤ) _ _ ({1} : Multiset (Fin 2))
    (Graded.K0.of (Graded.GProj.regular _)))

/-- The ordinary induction Serre relation and rational word span for the
parallel-edge polynomial in characteristic two. -/
example := KLR.CycKLR.affine_clsW_serre rqHyp (i := (0 : Fin 2)) (j := 1) (by decide)
example := KLR.CycKLR.lower_serre rqHyp (fun _ => 2) (i := (0 : Fin 2)) (j := 1) (by decide)
example := KLR.CycKLR.span_lowerWordQ rqHyp (fun _ => 2)

/-- Two red weights and two black colours over the field of two elements. -/
example := Stendhal.tensorProductAlgebra_finite
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 2) ({0, 1} : Multiset (Fin 2)) rqHyp
example := Stendhal.tensorProjection_dot_nilpotent
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 2) ({0, 1} : Multiset (Fin 2)) rqHyp ⟨2, by decide⟩

private abbrev rqN := rqC.dij (0 : Fin 2) 1 + 1
private abbrev rqWord : List (Fin 2) := 1 :: List.replicate rqN 0
private abbrev rqWeight : Multiset (Fin 2) := rqWord
private def rqSeq : KLR.Seq rqWeight := KLR.KLRAlgebra.Seq.ofList rqWord rfl
private theorem rq_hp : 0 + rqN < rqWeight.card := by simp [rqWeight, rqWord]
private theorem rq_ht0 : ∀ r : Fin rqWeight.card, (r : ℕ) = 0 → rqSeq.lbl r = 1 := by
  intro r hr
  change (KLR.KLRAlgebra.Seq.ofList rqWord rfl).lbl r = 1
  rw [KLR.KLRAlgebra.Seq.ofList_lbl]
  simp [rqWord, hr]
private theorem rq_ht : ∀ r : Fin rqWeight.card,
    (0 : ℕ) < r → (r : ℕ) ≤ 0 + rqN → rqSeq.lbl r = 0 := by
  intro r hr _
  change (KLR.KLRAlgebra.Seq.ofList rqWord rfl).lbl r = 0
  rw [KLR.KLRAlgebra.Seq.ofList_lbl]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (r : ℕ) = n + 1 := ⟨r - 1, by omega⟩
  simp [rqWord, hn]
private def rqShift (a : ℕ) : ℤ :=
  ∑ b ∈ Finset.range a, KLR.Rouquier.serreDegree rqC 0 1 rqN b
private def rqP (a : ℕ) : Graded.K0 (rqHyp.gradingDatum.grade rqWeight) :=
  if ha : a ≤ rqN then Graded.K0.of (Graded.GProj.ofIdempotent
    (KLR.KLRAlgebra.hflip (KLR.Rouquier.etop rqSeq 0 rqN a))
    (KLR.Rouquier.isIdempotentElem_hflip_etop rq_hp rq_ht0 rq_ht ha)
    (KLR.Rouquier.hflip_etop_mem_grade rq_hp rq_ht0 rq_ht rqHyp.gradingDatum
      (fun _ _ => rfl) ha)) else 0
example : ∑ a ∈ Finset.range (rqN + 1),
    ((-1 : LaurentPolynomial ℤ) ^ a * LaurentPolynomial.T (-rqShift a)) • rqP a = 0 := by
  exact KLR.Rouquier.K0_serre_window rq_hp rq_ht0 rq_ht rqHyp (by decide) rfl rqShift
    (by intro a _; simp only [rqShift, Finset.sum_range_succ, KLR.Rouquier.serreDegree]) rqP
    (by intro a ha; rw [rqP, dite_eq_left ha])


/-- Graded induction is associative on three nonzero-weight regular projectives. -/
example := (wkParallelGraph_standing (ZMod 2)).gradingDatum.indK0_assoc
  (Graded.K0.of (Graded.GProj.regular
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade (Finsupp.single 0 1))))
  (Graded.K0.of (Graded.GProj.regular
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade (Finsupp.single 1 1))))
  (Graded.K0.of (Graded.GProj.regular
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade (Finsupp.single 0 1))))

example := (wkParallelGraph_standing (ZMod 2)).gradingDatum.indK0_one_left
  (Graded.K0.of (Graded.GProj.regular
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade (Finsupp.single 0 1))))

example := (wkParallelGraph_standing (ZMod 2)).gradingDatum.indK0_one_right
  (Graded.K0.of (Graded.GProj.regular
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade (Finsupp.single 1 1))))

/-- The nilHecke factorial decomposition transfers to weighted loading projectives. -/
example := WeightedKLR.GradingDatum.K0_spacedProjSeq_expandDiv
  (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_dagger (ZMod 2))
  (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl) [(0, 2), (1, 1)] rfl

/-- The second divided-power factorial identity holds after scalar extension. -/
example := WeightedKLR.GradingDatum.toK0Q_spacedClsDiv_factorial
  (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_dagger (ZMod 2))
  (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl) 0 2

/-- The normalized weighted Serre relation on the parallel-edge graph in characteristic two. -/
example := WeightedKLR.GradingDatum.spacedClsDiv_serre_mul
  (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_dagger (ZMod 2))
  (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl) (i := 0) (j := 1) (by decide)

private abbrev wkMapS := wkParallelGraph_standing (ZMod 2)
private abbrev wkMapG := wkMapS.gradingDatum
private abbrev wkMapD := wkParallelGraph_dagger (ZMod 2)
private abbrev wkMapNoLoopEdges := wkParallelGraph_noLoops (ZMod 2)
private abbrev wkMapNoZeroLoops := wkParallelGraph_noZeroLoops (ZMod 2)
private theorem wkMapNoLoopPolynomials : ∀ i, (wkParallelGraph (ZMod 2)).loop i = none := fun _ => rfl

/-- Webster Theorem 2.19 on the parallel-edge graph over `ZMod 2`: the simple
quantum generator maps to the regular one-strand projective class. -/
example : wkMapS.quantumGroupMap wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials
    ⟨PreF.π rqC.dot vQ rqC.c (PreF.θ 0), PreF.π_θ_mem_Af 0⟩ =
    DirectSum.of wkMapG.K0fam (Finsupp.single 0 1)
      (Graded.K0.of (Graded.GProj.regular (wkMapG.klrGrade (Finsupp.single 0 1)))) :=
  wkMapS.quantumGroupMap_generator wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials 0

/-- The second divided power has the weighted loading projective class in
characteristic two. -/
example : wkMapS.quantumGroupMap wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials
    ⟨PreF.dpowF rqC.dot vQ rqC.c 0 2, PreF.dpowF_mem_Af 0 2⟩ =
    WeightedKLR.GradingDatum.spacedClsDiv wkMapS wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials [(0, 2)] :=
  wkMapS.quantumGroupMap_dpow wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials 0 2

/-- The two components of total restriction with one strand in each block. -/
example := wkMapG.component_totalCoproduct wkMapD wkMapS wkMapNoZeroLoops
  wkMapNoLoopPolynomials (Finsupp.single 0 1) (Finsupp.single 1 1)

/-- The antipode recursion negates every one-strand class. -/
example := wkMapG.antipodeComponent_of_degree_one wkMapD wkMapS wkMapNoZeroLoops
  wkMapNoLoopPolynomials (ν := Finsupp.single (0 : Fin 2) 1) (by simp)

/-- The zero-black-strand block with two red strands is the coefficient field. -/
example := Stendhal.tensorProductAlgebraZeroEquiv (k := ℚ) wkGraph.klrQ
  (fun i : Fin 2 => Finsupp.single i 1)



section CyclotomicDimensions

private noncomputable def singletonBlackGrading :=
  KLR.klGradingDatum ℚ (⊥ : SimpleGraph (Fin 1))

private noncomputable def twoRedGrading :=
  Stendhal.stendhalGradingDatum (fun _ : Fin 2 => Finsupp.single (0 : Fin 1) 1)
    singletonBlackGrading (fun _ => 1) (fun _ => rfl)

/-- The basis count for two red fundamental weights and one black strand, in every degree. -/
example (d : ℤ) :=
  Stendhal.coeff_gdim_tensorProductGrade (ν := {(0 : Fin 1)})
    (fun w => (TypeA.exists_reduced _ w).choose_spec) twoRedGrading
    (by rintro (i | r) <;> exact (by decide : (0 : ℤ) < 2)) d

/-- A single black strand with cyclotomic relation `x² = 0`, in every degree. -/
example (d : ℤ) :=
  let i := (KLR.Seq.uniqueOfForall (ν := {(0 : Fin 1)}) (i := 0) (by simp)).default
  KLR.CycKLR.coeff_gdim_cornerGrade singletonBlackGrading (fun _ => 2) (by simp)
    (fun a _ b _ hab => (hab (Subsingleton.elim a b)).elim)
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)
    i i 1 (one_smul _ _) d

example := Stendhal.emptyTensorK0Equiv _
  (Stendhal.stendhalGradingDatum (Fin.elim0 : Fin 0 → Fin 1 →₀ ℕ)
    singletonBlackGrading (fun _ => 1) (fun _ => rfl))

example := Stendhal.tensorProductVacuumK0Equiv_regular twoRedGrading

example := KLR.CycKLR.singleK0Equiv_regular singletonBlackGrading (fun _ => 2) 0 (by decide)

example := KLR.CycKLR.projectiveK0_free singletonBlackGrading (fun _ => 2)
  (fun i j hij => (hij (Subsingleton.elim i j)).elim)

example := KLR.CycKLR.singleK0_eq_zero singletonBlackGrading (fun _ => 0) 0 rfl

/-- Repeated adjacent colours in type A₂: the corner from 010 to 100 in the
cyclotomic algebra with level two at both colours. -/
example (d : ℤ) :=
  KLR.CycKLR.finrank_cornerGrade_eq_card_sub_rank
    (KLR.klGradingDatum ℚ (⊤ : SimpleGraph (Fin 2))) (fun _ => 2)
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)
    (KLR.klQ_symm _) (fun _ => (by decide : (0 : ℤ) < 2)) (KLR.KL1.Remark.jii 0 1) (KLR.KL1.Remark.iji 0 1) d

private noncomputable def adjacentPairGrading :=
  KLR.klGradingDatum ℚ (⊤ : SimpleGraph (Fin 2))

/-- Degreewise affine selection at weight twice the first root plus the adjacent root. -/
example (d : ℤ) :=
  KLR.CycKLR.exists_gradePBWBasis (ν := KLR.KL1.Remark.ν₃ 0 1) adjacentPairGrading
    (fun _ => 2) (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) (KLR.klQ_symm _)
    (fun _ => (by decide : (0 : ℤ) < 2)) d

/-- The selected homogeneous representatives also give a basis of the whole algebra. -/
example :=
  KLR.CycKLR.exists_homogeneousPBWBasis (ν := KLR.KL1.Remark.ν₃ 0 1) adjacentPairGrading
    (fun _ => 2) (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) (KLR.klQ_symm _)
    (fun _ => (by decide : (0 : ℤ) < 2))

/-- Representatives with the prescribed endpoints in the corner from 010 to 100. -/
example (d : ℤ) :=
  KLR.CycKLR.exists_cornerGradePBWBasis adjacentPairGrading (fun _ => 2)
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)
    (KLR.klQ_symm _) (fun _ => (by decide : (0 : ℤ) < 2))
    (KLR.KL1.Remark.jii 0 1) (KLR.KL1.Remark.iji 0 1) d

example (d : ℤ) :=
  KLR.CycKLR.coeff_gdim_grade_eq_card_sub_rank (ν := KLR.KL1.Remark.ν₃ 0 1) adjacentPairGrading
    (fun _ => 2) (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) (KLR.klQ_symm _)
    (fun _ => (by decide : (0 : ℤ) < 2)) d

example (d : ℤ) :=
  KLR.CycKLR.coeff_gdim_cornerGrade_eq_card_sub_rank adjacentPairGrading (fun _ => 2)
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)
    (KLR.klQ_symm _) (fun _ => (by decide : (0 : ℤ) < 2))
    (KLR.KL1.Remark.jii 0 1) (KLR.KL1.Remark.iji 0 1) d

private noncomputable def oneRedGrading :=
  Stendhal.stendhalGradingDatum (fun _ : Fin 1 => Finsupp.single (0 : Fin 1) 2)
    singletonBlackGrading (fun _ => 1) (fun _ => rfl)

example (d : ℤ) :=
  let w := (KLR.Seq.uniqueOfForall (ν := {(0 : Fin 1)}) (i := 0) (by simp)).default
  let s := Stendhal.SingleRed.insertWord {(0 : Fin 1)} w
  Stendhal.finrank_homGrade_sequenceProj oneRedGrading (fun u => (TypeA.exists_reduced _ u).choose_spec)
    (by rintro (i | r) <;> exact (by decide : (0 : ℤ) < 2)) s s
    (Stendhal.SingleRed.ordered _ s) (Stendhal.SingleRed.ordered _ s) d

example := Stendhal.SingleRed.cyclotomicEquiv
  (KLR.klQ (k := ℚ) (⊥ : SimpleGraph (Fin 1))) (fun _ : Fin 1 => Finsupp.single (0 : Fin 1) 2)
  ({0, 0} : Multiset (Fin 1))

example := KLR.CycKLR.indK0_vacuum singletonBlackGrading (fun _ => 2) 0

example := KLR.CycKLR.lower_lof singletonBlackGrading (fun _ => 2) 0 ({0} : Multiset (Fin 1))
  (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade singletonBlackGrading (fun _ => 2) {0})))

example := Stendhal.SingleBlack.oneBlackOneRedEquiv_dot (0 : Fin 1)
  (KLR.klQ (k := ℚ) (⊥ : SimpleGraph (Fin 1))) (fun _ : Fin 1 => Finsupp.single (0 : Fin 1) 2)

section AffineTensorPresentation

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "Q₁" => KLR.klQ (k := ℚ) (⊥ : SimpleGraph (Fin 1))
local notation "Λ₁" => (fun _ : Fin 1 => Finsupp.single (0 : Fin 1) 2)
local notation "ν₁" => ({0} : Multiset (Fin 1))
local notation "π₁" => Stendhal.affineTensorProjection (Q := Q₁) Λ₁ ν₁
local notation "eval₁" => AlgEquiv.toAlgHom (Stendhal.SingleBlack.oneBlackOneRedEquiv 0 Q₁ Λ₁)

/-- The one-red, one-black block with black-dot relation `x² = 0`. -/
example : TwoSidedIdeal.ker (π₁).toRingHom = Stendhal.affineTensorIdeal Q₁ Λ₁ ν₁ :=
  Stendhal.ker_affineTensorProjection

private theorem affineProjection_ideal :
    Stendhal.affineTensorIdeal Q₁ Λ₁ ν₁ ≤ TwoSidedIdeal.ker (π₁).toRingHom :=
  le_of_eq Stendhal.ker_affineTensorProjection.symm

/-- The affine projection factors through the one-red, one-black block. -/
example : (Stendhal.affineTensorLift π₁ affineProjection_ideal).comp π₁ = π₁ :=
  Stendhal.affineTensorLift_comp _ _

/-- Evaluating in `ℚ[x]/(x²)` detects the unit of the descended map. -/
example : eval₁ (Stendhal.affineTensorLift π₁ affineProjection_ideal 1) ≠ 0 := by
  have := AdjoinRoot.nontrivial ((Polynomial.X : Polynomial ℚ) ^ Λ₁ 0 0) (by simp)
  rw [map_one, map_one]
  exact one_ne_zero

end AffineTensorPresentation

example := Stendhal.SingleBlack.oneBlackK0Equiv_regular (0 : Fin 1) oneRedGrading
  (by simp : 0 < Finsupp.single (0 : Fin 1) 2 (0 : Fin 1))

example := Stendhal.SingleBlack.oneBlackK0_eq_zero (0 : Fin 1)
  (Stendhal.stendhalGradingDatum (0 : Fin 1 → Fin 1 →₀ ℕ)
    singletonBlackGrading (fun _ => 1) (fun _ => rfl)) rfl

end CyclotomicDimensions

example (x y : wkMapG.K0W) := wkMapG.totalCoproduct_mul wkMapD wkMapS
  wkMapNoZeroLoops wkMapNoLoopPolynomials x y

example (x : wkMapG.K0W) := wkMapG.counitK0_totalCoproduct_left wkMapD wkMapS
  wkMapNoZeroLoops wkMapNoLoopPolynomials x

example (x : wkMapG.K0W) := wkMapG.counitK0_totalCoproduct_right wkMapD wkMapS
  wkMapNoZeroLoops wkMapNoLoopPolynomials x

/-- Both antipode equations for the standing graph over the example field. -/
example := (wkMapS.braidedHopfK0 wkMapD wkMapNoZeroLoops wkMapNoLoopPolynomials).antipode_left

example := (wkMapS.braidedHopfK0 wkMapD wkMapNoZeroLoops wkMapNoLoopPolynomials).antipode_right

example := wkMapS.braidedHopfK0_antipode_single wkMapD wkMapNoZeroLoops
  wkMapNoLoopPolynomials 0 (Graded.K0.of (Graded.GProj.regular
    (wkMapG.klrGrade (Finsupp.single 0 1))))

private noncomputable def cutTestGrading :=
  Stendhal.stendhalGradingDatum (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 1)
    (wkWeightZeroGraph_standing.gradingDatum.toKLRGrading (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl))
    (fun i => wkWeightZeroGraph_standing.symm i) (fun _ => rfl)

/-- At one black strand with two red fundamental weights, use the rank of cut
products to compute the dimension of the violating quotient, in each degree. -/
example (d : ℤ) :=
  Stendhal.finrank_tensorProductGrade_eq_card_sub_rank (ν := {(0 : Fin 2)})
    (fun w => (TypeA.exists_reduced _ w).choose_spec) cutTestGrading
    wkWeightZeroGraph_dagger (fun _ => by simp [wkWeightZeroGraph]) (fun _ => rfl) (fun _ => rfl) wkWeightZeroGraph_standing
    (by
      rintro (i | r)
      · change 0 < 2 * (wkWeightZeroGraph_standing.symm i : ℤ)
        exact mul_pos (by decide) (by exact_mod_cast wkWeightZeroGraph_standing.symm_pos i)
      · exact (by decide : (0 : ℤ) < 2)) d

namespace LastRedCorner

open Stendhal

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private def redCornerQ (_ _ : Unit) : MvPolynomial (Fin 2) ℚ := 0
private def redCornerWeights {n : ℕ} (j : Fin n) : Unit →₀ ℕ :=
  Finsupp.single () (j.val + 1)

example : TensorProductAlgebra ℚ redCornerQ (redCornerWeights (n := 2) ∘ Fin.castSucc)
      (0 : Multiset Unit) ≃ₐ[ℚ] TensorProductAlgebra.lastRedCorner redCornerQ (redCornerWeights (n := 2)) 0 :=
  appendRedVacuumEquiv redCornerQ redCornerWeights

example : TensorProductAlgebra ℚ redCornerQ (redCornerWeights (n := 1) ∘ Fin.castSucc)
      ({()} : Multiset Unit) ≃ₐ[ℚ]
    TensorProductAlgebra.lastRedCorner redCornerQ (redCornerWeights (n := 1)) {()} :=
  appendFirstRedEquiv redCornerQ {()} redCornerWeights


example : Function.Surjective
    (appendRed redCornerQ (redCornerWeights (n := 2)) {()}) :=
  appendRed_surjective redCornerQ redCornerWeights {()}


example (x : StendhalAlgebra ℚ redCornerQ (redCornerWeights (n := 2)) {()}) :
    ∃ v, appendRedStendhalValue redCornerQ redCornerWeights {()} v =
      StendhalAlgebra.lastRedIdem redCornerQ redCornerWeights {()} * x *
        StendhalAlgebra.lastRedIdem redCornerQ redCornerWeights {()} :=
  exists_appendRedStendhalValue redCornerQ redCornerWeights {()} x

end LastRedCorner

namespace FirstBlackProjectives

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private def rbWord : KLR.Seq (Stendhal.stendhalWeight 2 {(0 : Fin 1)}) :=
  KLR.KLRAlgebra.Seq.ofList [.inr 0, .inl 0, .inr 1] (by decide)

private theorem rbOrdered : Stendhal.IsRedOrdered rbWord := by
  unfold Stendhal.IsRedOrdered
  decide

private theorem rbSurvives : ¬ Stendhal.IsViolated rbWord := by
  rintro ⟨h, hv⟩
  exact Bool.noConfusion hv

private def rrWord : KLR.Seq (Stendhal.stendhalWeight 2 {(0 : Fin 1)}) :=
  KLR.KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl 0] (by decide)

private theorem rrOrdered : Stendhal.IsRedOrdered rrWord := by
  unfold Stendhal.IsRedOrdered
  decide

private theorem rrSurvives : ¬ Stendhal.IsViolated rrWord := by
  rintro ⟨h, hv⟩
  exact Bool.noConfusion hv

private noncomputable def firstProjGrading :=
  Stendhal.stendhalGradingDatum (fun _ : Fin 2 => Finsupp.single (0 : Fin 1) 1)
    (KLR.klGradingDatum ℚ (⊥ : SimpleGraph (Fin 1))) (fun _ => 1) (fun _ => rfl)

private theorem firstProjDots (c : Fin 1 ⊕ Fin 2) : 0 < firstProjGrading.degX c := by
  rcases c with x | r <;> exact (by decide : (0 : ℤ) < 2)

private theorem firstProjMultiplicity (_r : Fin 2) : 0 < (Finsupp.single (0 : Fin 1) 1 : Fin 1 →₀ ℕ) 0 := by
  simp

private abbrev firstWords :=
  {s : KLR.Seq (Stendhal.stendhalWeight 2 {(0 : Fin 1)}) // Stendhal.IsRedOrdered s ∧ ¬ Stendhal.IsViolated s}

private def middleWord : firstWords := ⟨rbWord, rbOrdered, rbSurvives⟩
private def rightWord : firstWords := ⟨rrWord, rrOrdered, rrSurvives⟩

example := Stendhal.sequenceProj_rightEquiv firstProjGrading
  (by rintro (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;> rfl) middleWord.1 middleWord.2.1

/-- Two fundamental red strands and one black strand. Both allowable positions give
indecomposables. Their projectives stay distinct after any grading shift. -/
example := Stendhal.FirstWeight.finrank_endZero_sequenceProj firstProjGrading firstProjDots
  firstProjMultiplicity middleWord

example := Stendhal.FundamentalCorner.boundaryAt_last_homGdimPoly

example := Stendhal.FirstWeight.coeff_endPoly_sequenceProj_eq_zero_of_neg firstProjGrading
  firstProjDots rrWord rrOrdered (by decide : (-2 : ℤ) < 0)

example := Stendhal.FirstWeight.sequenceProj_isIndec firstProjGrading firstProjDots
  firstProjMultiplicity rightWord

example (d : ℤ) : IsEmpty ((Stendhal.sequenceProj firstProjGrading middleWord.1 middleWord.2.1).Iso
    ((Stendhal.sequenceProj firstProjGrading rightWord.1 rightWord.2.1).shift d)) := by
  refine ⟨fun F => ?_⟩
  have h := Stendhal.FirstWeight.eq_of_sequenceProj_iso_shift firstProjGrading
    firstProjMultiplicity middleWord rightWord F
  have he := congrArg (fun s : firstWords => s.1.lbl ⟨1, by decide⟩) h
  change (Sum.inl (0 : Fin 1) : Fin 1 ⊕ Fin 2) = .inr 1 at he
  contradiction

example := Stendhal.FirstWeight.exists_iso_sequenceProj_shift firstProjGrading firstProjDots
  firstProjMultiplicity (Stendhal.sequenceProj firstProjGrading middleWord.1 middleWord.2.1)
  (Stendhal.FirstWeight.sequenceProj_isIndec firstProjGrading firstProjDots firstProjMultiplicity middleWord)

example := Stendhal.FirstWeight.sequenceProjIndecEquiv firstProjGrading firstProjDots firstProjMultiplicity

example := Stendhal.FirstWeight.sequenceProjBasis_apply firstProjGrading firstProjDots firstProjMultiplicity middleWord

end FirstBlackProjectives

namespace FirstBlackLattice

open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

private def sl2HighestTwo : Dom sl2RootDatum :=
  ⟨2 • AddMonoidHom.id ℤ, fun _ => by simp [LieLean.QuantumGroup.sl2RootDatum]⟩

private theorem sl2XRegular : sl2RootDatum.IsXRegular := by
  change LinearIndependent ℤ sl2RootDatum.root
  rw [linearIndependent_unique_iff]
  intro h
  have hh := congrArg (fun f : ℤ →+ ℤ => f 1) h
  norm_num at hh

private def redLevelTwo : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

private def redLevelTwoGrading :=
  Stendhal.stendhalGradingDatum redLevelTwo (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit))
    (fun _ => 1) (fun _ => rfl)

example := Stendhal.SingleBlack.oneBlackLatticeEquiv_regular sl2HighestTwo () redLevelTwoGrading
  sl2XRegular (by simp [sl2HighestTwo, redLevelTwo, LieLean.QuantumGroup.sl2RootDatum]) (by simp [redLevelTwo])

example := Stendhal.SingleBlack.oneBlackLatticeEquiv_regular_shift sl2HighestTwo () redLevelTwoGrading
  sl2XRegular (by simp [sl2HighestTwo, redLevelTwo, LieLean.QuantumGroup.sl2RootDatum]) (by simp [redLevelTwo]) 1

end FirstBlackLattice

namespace OneRedEquivalence

private abbrev G := KLR.klGradingDatum ℚ (⊥ : SimpleGraph (Fin 1))
private abbrev Λ := fun _ : Fin 1 => Finsupp.single (0 : Fin 1) 2
private abbrev β : Multiset (Fin 1) := {0, 0}
example := Stendhal.SingleRed.cyclotomicK0Equiv_sequenceProj Λ G (fun _ => 1) (fun _ => rfl) β
  ((KLR.Seq.uniqueOfForall (ν := β) (i := 0) (by simp [β])).default)
example := Stendhal.SingleRed.indK0_cyclotomicK0Equiv Λ G (fun _ => 1) (fun _ => rfl) {0} 0
  (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade G (Λ 0) {0})))
example := Stendhal.SingleRed.totalCyclotomicK0Equiv_lof Λ G (fun _ => 1) (fun _ => rfl) β
  (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade G (Λ 0) β)))
example := Stendhal.SingleRed.blackIndK0_eq_indK0 0 ({0} : Multiset (Fin 1)) Λ G (fun _ => 1) (fun _ => rfl)
example := Stendhal.SingleRed.blackLower_totalCyclotomicK0Equiv 0 Λ G (fun _ => 1) (fun _ => rfl)
  (DirectSum.lof (LaurentPolynomial ℤ) _ _ ({0} : Multiset (Fin 1))
    (Graded.K0.of (Graded.GProj.regular (KLR.CycKLR.grade G (Λ 0) {0}))))

example := Stendhal.SingleRed.blackIndK0_regular_eq_indK0 0 β Λ G (fun _ => 1) (fun _ => rfl)

example := Stendhal.SingleRed.indK0_vacuum Λ G (fun _ => 1) (fun _ => rfl) 0

end OneRedEquivalence

namespace CyclotomicLifting

private abbrev G := KLR.klGradingDatum ℚ (⊥ : SimpleGraph (Fin 1))
private abbrev β : Multiset (Fin 1) := {0, 0}
private def s := (KLR.Seq.uniqueOfForall (ν := β) (i := 0) (by simp [β])).default
example := KLR.CycKLR.quotientK0_ofIdempotent G (fun _ => 2) β
  (KLR.KLRAlgebra.e_mul_self s) (G.e_mem_grade s)
example := KLR.CycKLR.quotientK0_surjective G (fun _ => 2) β
  (KLR.klQ_symm _) (fun _ => (by decide : (0 : ℤ) < 2))
example := KLR.CycKLR.totalQuotientK0_surjective G (fun _ => 2)
  (KLR.klQ_symm _) (fun _ => (by decide : (0 : ℤ) < 2))

end CyclotomicLifting

namespace AffineCoverGrading

open KLR Stendhal


private abbrev G := klGradingDatum (ZMod 2) (⊥ : SimpleGraph Unit)
private abbrev red : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private abbrev H := affineCoverGrading red G (fun _ => 1) (fun _ => rfl)
private abbrev μ := stendhalWeight 2 (0 : Multiset Unit)
private def redPair : Seq μ := KLRAlgebra.Seq.ofList [Sum.inr 0, Sum.inr 1] (by decide)

example : H.degΨ (Sum.inr 0) (Sum.inr 1) = 1 := by decide

example := affineCover_mem_grade red G (fun _ => 1) (fun _ => rfl) (0 : Multiset Unit)
  (H.ψ_mul_e_mem_grade' 0 redPair)

example : affineCoverQ (klQ (k := ZMod 2) (⊥ : SimpleGraph Unit)) red (Sum.inr 0) (Sum.inr 1) ≠ 0 :=
  affineCoverQ_ne_zero red (fun a b h => (h (Subsingleton.elim a b)).elim) _ _ (by decide)

end AffineCoverGrading

namespace CyclotomicHighestWeight

open KLR

private abbrev datum := UDot.sl2RootDatum
private theorem params :
    KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) (fun _ _ => (0 : MvPolynomial (Fin 2) ℚ)) where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private theorem regular : (CycKLR.projectiveRootDatum datum).IsXRegular := by
  change LinearIndependent ℤ (CycKLR.projectiveRootDatum datum).root
  rw [linearIndependent_unique_iff]
  intro h
  have hh := congrArg (fun f : ℤ →+ ℤ => f 1) h
  change (1 : ℤ) * 2 = 0 at hh
  omega

private theorem dominantTwo : ∀ i, ((2 : ℕ) : ℤ) = datum.pair (datum.iY i) 2 := by
  intro i
  change 2 = (1 : ℤ) * 2
  decide

/-- In type A₁ at level two, the regular projective of the empty block gives
the highest vector of the three-dimensional representation. -/
example := CycKLR.gdimPoly_repeated params.gradingDatum (fun _ => 2) () params.klrSymm
  params.polyInY_leading datum 2 (dominantTwo ()) (params.polyInY_degree_pair datum ())
  (by decide) 2

/-- At level two, the two-strand divided projective has the Gaussian
endomorphism polynomial for the top-dimensional Grassmannian index. -/
example := CycKLR.homGdim_repeated_dividedProjective params.gradingDatum (fun _ => 2) ()
  params.klrSymm params.polyInY_leading datum 2 (dominantTwo ())
  (params.polyInY_degree_pair datum ()) (by decide)
  (fun a b => congrArg Neg.neg ((CartanDatum.ofGraph (⊥ : SimpleGraph Unit)).symm a b))
  (fun _ => rfl) 2

example := CycKLR.homGrade_ind_res params.gradingDatum (fun _ => 2) () 0 params.klrSymm
  params.polyInY_leading
  (Graded.GProj.regular (CycKLR.grade params.gradingDatum (fun _ => 2) 0))
  (Graded.GProj.regular (CycKLR.grade params.gradingDatum (fun _ => 2) ({()}+0))) 2

example := CycKLR.projectiveHighestWeightEquiv_vacuum (fun _ => 2) datum 2 dominantTwo params regular

example := CycKLR.projectiveHighestWeightEquiv_F (fun _ => 2) datum 2 dominantTwo params regular ()
  (CycKLR.projectiveVacuum params.gradingDatum (fun _ => 2))

/-- At level two the divided square acts integrally on the highest vector. -/
example := CycKLR.projectiveIntegralEquiv_dividedWordClass params (fun _ => 2) datum 2
  dominantTwo regular [((), 2)]
example := CycKLR.projectiveIntegralEquiv_raise params (fun _ => 2) datum 2 dominantTwo regular ()
  (CycKLR.dividedWordClass params (fun _ => 2) [((), 2)])
example := CycKLR.projectiveIntegralEquiv_lower params (fun _ => 2) datum 2 dominantTwo regular ()
  (CycKLR.dividedWordClass params (fun _ => 2) [((), 1)])

private abbrev level : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev bottom : Multiset Unit := {(), ()}
private abbrev regularLower :=
  Graded.K0.of (Graded.GProj.regular (CycKLR.grade params.gradingDatum (fun _ => 2) bottom))

/-- In the bottom weight of the level-two representation, the all-weight
Euler form computes a pairing with a shifted virtual regular class. -/
example := CycKLR.homForm_eq_websterForm params (fun _ => 2) datum 2 dominantTwo regular bottom
  regularLower (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) • regularLower)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev redGrade := Stendhal.tensorProductGrade
  (Stendhal.stendhalGradingDatum level params.gradingDatum (di (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)))
    (fun i => (two_mul_di (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) i).symm)) bottom

private abbrev redRegular : Graded.K0 redGrade :=
  Graded.K0.of (𝒜 := redGrade) (Graded.GProj.regular redGrade)

/-- The same comparison for the actual one-red, two-black Stendhal algebra. -/
example := Stendhal.SingleRed.homForm_eq_shapovalov params level datum 2
  (fun i => by simpa [level] using dominantTwo i) regular bottom redRegular redRegular

/-- The bottom-weight Hom polynomial is determined even on virtual
differences of shifted projectives. -/
example := Stendhal.SingleRed.existsUnique_eulerPolynomial params level datum 2
  (fun i => by simpa [level] using dominantTwo i) regular bottom
  (redRegular - (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) • redRegular) redRegular

example := Stendhal.SingleRed.homGdimPoly_eq_shapovalov params level datum 2
  (fun i => by simpa [level] using dominantTwo i) regular bottom
  (Graded.GProj.regular redGrade) (Graded.GProj.regular redGrade)

private def dividedRedWord : Stendhal.FirstWeight.TensorWord Unit 2 :=
  ((Stendhal.FirstWeight.TensorWord.empty.red.black () 2).red).black () 1

private def twoTensorFactors : Fin 2 → LieLean.QuantumGroup.GrandLoop.Dom (CycKLR.projectiveRootDatum datum) :=
  fun _ => ⟨datum.pair.flip 2, fun i => (dominantTwo i) ▸ by decide⟩

private abbrev prefixLevels : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev prefixWeight : Fin 1 → LieLean.QuantumGroup.GrandLoop.Dom (CycKLR.projectiveRootDatum datum) :=
  fun _ => twoTensorFactors 0
private abbrev prefixCartan := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev prefixEmptyGrade := Stendhal.stendhalGradingDatum (prefixLevels ∘ Fin.castSucc)
  params.gradingDatum (fun i => prefixCartan.dot i i / 2) (Stendhal.dotDegree prefixCartan params)
private abbrev prefixEmptyBlock := Stendhal.tensorProductGrade prefixEmptyGrade (0 : Multiset Unit)

private theorem prefixTop_nonempty : Nonempty (Graded.GProj.IndecClass prefixEmptyBlock) := by
  let := Stendhal.tensorProductAlgebra_finite (prefixLevels ∘ Fin.castSucc) (0 : Multiset Unit) params
  let := Graded.HasGdim.of_finiteDimensional prefixEmptyBlock
  let B := Graded.K0.indecBasis prefixEmptyBlock
  let H := Stendhal.tensorProductVacuumK0Equiv prefixEmptyGrade
  have h : B.repr (H.symm 1) ≠ 0 := by
    rw [B.repr.map_ne_zero_iff,H.symm.map_ne_zero_iff]
    exact one_ne_zero
  obtain ⟨b,_⟩ := Finsupp.ne_iff.mp h
  exact ⟨b⟩

private abbrev prefixPwt := (Stendhal.stendhalWeight 0 (0 : Multiset Unit)).map (Stendhal.addRedColor 0)
private abbrev prefixDwt := ({Sum.inr (0 : Fin 1)} : Multiset (Unit ⊕ Fin 1))
private def prefixOutput : Seq (prefixPwt + prefixDwt) := KLRAlgebra.Seq.ofList [.inr 0] (by decide)
private abbrev prefixWord := (Stendhal.FirstWeight.TensorWord.empty : Stendhal.FirstWeight.TensorWord Unit 0).red
private theorem prefixOutput_word : List.ofFn prefixOutput.1 = KLRAlgebra.expandDiv prefixWord.blocks := by
  rw [prefixOutput,KLRAlgebra.Seq.ofFn_ofList]
  rfl
private abbrev prefixMask : Fin (Stendhal.FirstWeight.lastRedWord prefixWord).2.length → Bool := fun _ => false
private theorem prefixMask_fits : Stendhal.FirstWeight.fitsLastRedContents
    (α := prefixPwt) (β := prefixDwt) prefixWord prefixMask := by
  constructor <;>
    simp [Stendhal.FirstWeight.lastRedBlackTags,Stendhal.FirstWeight.lastRedWord,
      Stendhal.FirstWeight.tagMask,Stendhal.FirstWeight.maskSubword,prefixWord,
      Stendhal.FirstWeight.TensorWord.blocks,KLRAlgebra.expandDiv,prefixPwt,Stendhal.stendhalWeight,prefixDwt]

/-- At one red strand and black content zero the surviving shuffle tests the
nonzero simple of the empty prefix against its tensor-unit word. -/
example := Stendhal.FirstWeight.prefixStandardTop_mask prefixLevels prefixCartan params prefixWeight regular
  (Stendhal.FirstWeight.exists_emptyTensorWordEquiv prefixCartan params (fun j => prefixWeight (Fin.castSucc j))
    (prefixLevels ∘ Fin.castSucc)).choose
  (Stendhal.FirstWeight.exists_emptyTensorWordEquiv prefixCartan params (fun j => prefixWeight (Fin.castSucc j))
    (prefixLevels ∘ Fin.castSucc)).choose_spec
  0 (Classical.choice prefixTop_nonempty) prefixWord prefixOutput prefixOutput_word
  ((Stendhal.FirstWeight.ordinaryShuffleEquiv prefixWord prefixOutput prefixOutput_word).symm
    ⟨prefixMask,prefixMask_fits⟩)

/-- In the empty tensor unit, the divided word with black multiplicities
zero and two agrees with its projective image. -/
example := (Stendhal.FirstWeight.exists_emptyTensorWordEquiv
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params (R := CycKLR.projectiveRootDatum datum)
  Fin.elim0 Fin.elim0).choose_spec ((Stendhal.FirstWeight.TensorWord.empty.black () 0).black () 2)

/-- The tensor exponent uses both red and black crossings for the tagged suffix. -/
example := Stendhal.FirstWeight.lastRedCrossingSum_eq_suffixMaskExponent
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) (R := CycKLR.projectiveRootDatum datum)
  (Finsupp.single () 2) (datum.pair.flip (2 : ℤ)) (fun i => by cases i; rw [Finsupp.single_eq_same]; rfl)
  [(.inr (0 : Fin 2) : Unit ⊕ Fin 2)] [((),true),((),false),((),false)]

section EmptyInduction
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev noRedFactors : Fin 0 → LieLean.QuantumGroup.GrandLoop.Dom (CycKLR.projectiveRootDatum datum) :=
  Fin.elim0
private abbrev noRedLevels : Fin 0 → Unit →₀ ℕ := Fin.elim0

private abbrev shiftInversion := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair shiftInversion.toRingHom shiftInversion.toRingHom :=
  RingHomInvPair.of_ringEquiv shiftInversion

local notation "vacuumWords" => Stendhal.FirstWeight.exists_emptyTensorWordEquiv
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params noRedFactors noRedLevels

/- With no red factors the comparison exists in all weights. Apply it to
ordinary and divided induction from the nonzero vacuum class. -/
open Stendhal.FirstWeight in
example := map_blackLower _ params noRedLevels noRedFactors (vacuumWords).choose.toLinearMap
  (vacuumWords).choose_spec () (tensorWordProjectiveClass noRedLevels _ params .empty)
open Stendhal.FirstWeight in
example := map_blackDividedLower _ params noRedLevels noRedFactors (vacuumWords).choose.toLinearMap
  (vacuumWords).choose_spec () 2 (tensorWordProjectiveClass noRedLevels _ params .empty)

open Stendhal.FirstWeight in
/-- The rational span of the projective points contains the empty tensor vacuum. -/
example := prefixBasisPoint_span noRedLevels _ params noRedFactors regular (vacuumWords).choose
  (integralWordVector (C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) noRedFactors .empty)

end EmptyInduction

/-- At level two the last red crossing has degree two. Crossing two black
strands assigned to the last factor changes the exponent to minus two. -/
example : (datum.pair.flip (2 : ℤ) - (([] : List Unit).map (CycKLR.projectiveRootDatum datum).root).sum)
    (LieLean.QuantumGroup.ktilde (CycKLR.projectiveRootDatum datum) ()) = 2 := by
  rw [Stendhal.FirstWeight.shuffleExponent_eq_crossings]
  decide
example : (datum.pair.flip (2 : ℤ) - ([(),()].map (CycKLR.projectiveRootDatum datum).root).sum)
    (LieLean.QuantumGroup.ktilde (CycKLR.projectiveRootDatum datum) ()) = -2 := by
  rw [Stendhal.FirstWeight.shuffleExponent_eq_crossings]
  decide

example := Stendhal.FirstWeight.barDividedWordOp_append twoTensorFactors
  (Stendhal.FirstWeight.tensorWordVector Stendhal.FirstWeight.TensorWord.empty.red
    (fun j : Fin 1 => twoTensorFactors j.castSucc))
  _ LieLean.QuantumGroup.IrreducibleModule.hwv_mem_weightSpace [((), 2), ((), 1)]

example := Stendhal.FirstWeight.finrank_le_lastRedPairs (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params (Multiset.replicate 3 ())

/-- Test the expanded loading for three black strands directly on its regular
finite module. This specializes the ordinary idempotent character calculation. -/
private abbrev shuffleLevels : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev shuffleGrading := Stendhal.stendhalGradingDatum shuffleLevels params.gradingDatum
  (fun i => (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)).dot i i / 2)
  (Stendhal.dotDegree (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params)
private def shuffleRegular : Graded.GFin (Stendhal.tensorProductGrade shuffleGrading dividedRedWord.content.toMultiset) :=
  { toGMod := Graded.GMod.regular _
    finiteDimensional := Stendhal.tensorProductAlgebra_finite shuffleLevels _ params }
example := Stendhal.FirstWeight.ordinary_hom_eq_corner shuffleLevels (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))
  params dividedRedWord.content.toMultiset ⟨dividedRedWord,rfl⟩ shuffleRegular

example := Stendhal.FirstWeight.tensorWordProjective_factorial (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params dividedRedWord
example := Stendhal.FirstWeight.tensorWordVector_factorial dividedRedWord twoTensorFactors
example := Stendhal.FirstWeight.span_tensorWordProjective (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params (Multiset.replicate 3 ())


example := Stendhal.FirstWeight.span_tensorWordProjectiveClass (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params

example := Stendhal.FirstWeight.exists_wordEquivAt_iff (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params twoTensorFactors regular (Multiset.replicate 3 ())
example := Stendhal.FirstWeight.exists_tensorWordEquiv_iff (fun _ : Fin 2 => Finsupp.single () 2)
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params twoTensorFactors regular

open Stendhal.FirstWeight
private abbrev oneFactor : Fin 1 → LieLean.QuantumGroup.GrandLoop.Dom (CycKLR.projectiveRootDatum datum) :=
  fun _ => twoTensorFactors 0
private abbrev oneLevel : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev oneBlack : Multiset Unit := {()}
private abbrev oneGrade := Stendhal.stendhalGradingDatum oneLevel params.gradingDatum
  (fun i => (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)).dot i i / 2)
  (Stendhal.dotDegree (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params)
private abbrev oneW := integralTensorWeight oneFactor regular oneBlack.toFinsupp

/-- The full pair count fits the one-dimensional first weight of the
single level-two factor after the empty red prefix. -/
example : Nat.card (Σ u : Stendhal.LastRedWeightSplit oneBlack, Stendhal.LastRedFactorClasses oneLevel oneBlack oneGrade u)
    ≤ Module.finrank (LaurentPolynomial ℤ) oneW := by
  have e : oneW = tensorFirstLattice oneFactor () regular := by
    ext x
    change (_ ∧ tensorWeightProj oneFactor regular (_ - (CycKLR.projectiveRootDatum datum).rootSum oneBlack.toFinsupp) x = x) ↔ _
    simp only [oneBlack,Multiset.toFinsupp_singleton,(CycKLR.projectiveRootDatum datum).rootSum_single,one_smul]
    rfl
  have : Module.Finite (LaurentPolynomial ℤ) oneW := by
    rw [e]
    apply Module.Finite.of_basis (pVectorBasis oneFactor () regular (fun _ => by change 0 < (1 : ℤ) * 2; decide))
  apply lastRedFactorCount_le_of_prefixRelations (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) oneFactor regular oneLevel
    params oneBlack (fun i => by cases i; change (↑((Finsupp.single () 2 : Unit →₀ ℕ) ()) : ℤ) = 1 * 2; simp)
  apply (exists_tensorWordEquiv_iff _ _ _ _ regular).mp
  exact exists_emptyTensorWordEquiv _ params _ _

private abbrev oneFinalMatch : ∀ i, (oneLevel (Fin.last 0) i : ℤ) =
    (oneFactor (Fin.last 0)).1 ((CycKLR.projectiveRootDatum datum).coroot i) := by
  intro i
  cases i
  change (↑((Finsupp.single () 2 : Unit →₀ ℕ) ()) : ℤ) = 1 * 2
  simp

private abbrev initialWeights : Fin 0 → LieLean.QuantumGroup.GrandLoop.Dom (CycKLR.projectiveRootDatum datum) :=
  fun j => oneFactor j.castSucc
private abbrev initialLabels : Fin 0 → Unit →₀ ℕ := oneLevel ∘ Fin.castSucc
private abbrev initialComparison :=
  (exists_emptyTensorWordEquiv (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) params initialWeights initialLabels).choose
private abbrev a1 := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

/-- The simple-top tests separate the level-two first weight after the empty prefix. -/
example := barWeightCoordinates_injective_of_factorTests a1 oneFactor regular oneBlack
  (prefixBasisPoint initialLabels a1 params initialWeights regular initialComparison)
  (cyclotomicBasisPoint a1 (oneLevel (Fin.last 0)) params (oneFactor (Fin.last 0)) oneFinalMatch regular)
  (prefixTopTest initialLabels a1 params initialWeights regular initialComparison)
  (cyclotomicTopTest a1 (oneLevel (Fin.last 0)) params (oneFactor (Fin.last 0)) oneFinalMatch regular)
  (prefixBasisPoint_span initialLabels a1 params initialWeights regular initialComparison)
  (span_cyclotomicBasisPoint a1 (oneLevel (Fin.last 0)) params (oneFactor (Fin.last 0)) oneFinalMatch regular)
  (fun a i => by by_cases h : a = i <;> simpa [h] using
    prefixTopTest_point initialLabels a1 params initialWeights regular initialComparison a i)
  (fun a i => by by_cases h : a = i <;> simpa [h] using
    cyclotomicTopTest_point a1 (oneLevel (Fin.last 0)) params (oneFactor (Fin.last 0)) oneFinalMatch regular a i)

namespace CyclotomicTests

open Stendhal Stendhal.FirstWeight Graded

private abbrev testC := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev oneBlack : Multiset Unit := {()}

private theorem finalWeightAgreement (i : Unit) :
    (shuffleLevels 1 i : ℤ) = (twoTensorFactors 1).1 ((CycKLR.projectiveRootDatum datum).coroot i) := by
  simpa [shuffleLevels, twoTensorFactors, CycKLR.projectiveRootDatum] using dominantTwo i

private def oneBlackSimple : GProj.IndecClass (CycKLR.grade params.gradingDatum (shuffleLevels 1) oneBlack) := by
  let := lastRedFinal_finite params (shuffleLevels 1) oneBlack
  let g := CycKLR.grade params.gradingDatum (shuffleLevels 1) oneBlack
  let := HasGdim.of_finiteDimensional g
  let e := CycKLR.singleK0Equiv params.gradingDatum (shuffleLevels 1) () (by simp [shuffleLevels])
  apply Classical.choice
  by_contra hn
  let : IsEmpty (GProj.IndecClass g) := not_nonempty_iff.mp hn
  have hz : e.symm 1 = 0 := (K0.indecBasis g).repr.injective (Subsingleton.elim _ _)
  exact one_ne_zero (e.symm.injective (hz.trans e.symm.map_zero.symm))

/-- The level-two simple in the one-black block tests its basis point and both
matching and different ordinary words. -/
example := cyclotomicTopTest_point testC (shuffleLevels 1) params (twoTensorFactors 1)
  finalWeightAgreement regular ⟨oneBlack,oneBlackSimple⟩ ⟨oneBlack,oneBlackSimple⟩
example := cyclotomicTopTest_word testC (shuffleLevels 1) params (twoTensorFactors 1)
  finalWeightAgreement regular [()] rfl oneBlackSimple
example := cyclotomicTopTest_word_of_ne testC (shuffleLevels 1) params (twoTensorFactors 1)
  finalWeightAgreement regular [] (by decide) oneBlackSimple
example := span_cyclotomicBasisPoint testC (shuffleLevels 1) params (twoTensorFactors 1) finalWeightAgreement regular

private abbrev finalWord : TensorWord Unit 2 := TensorWord.empty.red.red.black () 1
private abbrev earlierContent := Multiset.map (addRedColor 1) (stendhalWeight 1 (0 : Multiset Unit))
private abbrev finalContent := Multiset.map (Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1))
  (stendhalWeight 1 oneBlack)
private def finalLoading : Seq (earlierContent + finalContent) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl ()] (by decide)
private theorem finalWord_labels : List.ofFn finalLoading.1 = KLRAlgebra.expandDiv finalWord.blocks :=
  KLRAlgebra.Seq.ofFn_ofList _ _

/-- At red-red-black the surviving mask assigns the black strand to the final
factor. The opposite assignment vanishes in its one-black test. -/
example := cyclotomicTopTest_mask shuffleLevels testC params 0 oneBlack twoTensorFactors
  finalWeightAgreement regular oneBlackSimple finalWord finalLoading finalWord_labels
  ((ordinaryShuffleEquiv finalWord finalLoading finalWord_labels).symm
    ⟨fun _ => true, by
      constructor
      · apply (prefixMaskContent_iff finalWord 0 _).mpr
        simp [finalWord,prefixMaskWord,lastRedWord,maskSubword,tagMask,appendOrdinaryBlack,TensorWord.content]
      · apply (finalMaskContent_iff finalWord oneBlack _).mpr
        simp [finalWord,oneBlack,finalMaskLetters,lastRedWord,maskSubword,tagMask]⟩)
example := cyclotomicTopTest_mask_of_ne shuffleLevels testC params oneBlack twoTensorFactors
  finalWeightAgreement regular oneBlackSimple finalWord (fun _ => false) (by
    intro h
    have hh := (finalMaskContent_iff finalWord oneBlack _).mp h
    simp [finalWord,oneBlack,finalMaskLetters,lastRedWord,maskSubword,tagMask] at hh)

end CyclotomicTests

namespace TwoFundamentalLowerings

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop Stendhal.FirstWeight
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
private abbrev D := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev R := CycKLR.projectiveRootDatum datum
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩
private abbrev level : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private def omegaOne : Dom R := ⟨datum.pair.flip 1, fun i => by change 0 ≤ (1 : ℤ) * 1; decide⟩
private abbrev factors (n : ℕ) : Fin n → Dom R := fun _ => omegaOne
private theorem level_eq (r : Fin 2) (i : Unit) : (level r i : ℤ) = ((factors 2) r).1 (R.coroot i) := by
  cases i
  rw [Finsupp.single_eq_same]
  rfl
private abbrev h := IrreducibleModule.hwv R 𝕍 omegaOne.1
private abbrev f := F R 𝕍 () • h
private abbrev vacuum := tensorWordVector (TensorWord.empty (I := Unit)) (factors 0)
private abbrev splitWord := (TensorWord.empty.red.black () 1).red.black () 1
private abbrev dividedWord := TensorWord.empty.red.red.black () 2

private theorem twice_on_factor : F R 𝕍 () • f = 0 := by
  change F R 𝕍 () • (F R 𝕍 () • (Submodule.Quotient.mk (VermaModule.hwv R 𝕍 omegaOne.1))) = 0
  rw [← mul_smul, ← pow_two, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  apply VermaModule.fPowSubmodule_le_maxSubmodule regular hvn_ratFunc omegaOne.2
  apply Submodule.subset_span
  exact ⟨(),rfl⟩

private theorem quantum_one (x : LieLean.QuantumGroup R 𝕍) (q : RatFunc ℚ) :
    qDivPow q 1 x = x := by simp [qDivPow,qFactorial,qInt]

private theorem lower_empty (x : TensorSpace (factors 0)) : tensorRepresentation (factors 0) (F R 𝕍 ()) x = 0 := by
  change (Algebra.ofId (RatFunc ℚ) (Module.End (RatFunc ℚ) (TensorSpace (factors 0)))) (counit R 𝕍 (F R 𝕍 ())) x = 0
  simp

private theorem lower_one_factor (m : IrreducibleModule R 𝕍 omegaOne.1) :
    tensorRepresentation (factors 1) (F R 𝕍 ()) (appendTensor (factors 1) vacuum m) =
      appendTensor (factors 1) vacuum (F R 𝕍 () • m) := by
  rw [tensorRepresentation_F_append,lower_empty]
  simp [appendTensor]

private theorem splitWord_vector :
    tensorWordVector splitWord (factors 2) = appendTensor (factors 2) (appendTensor (factors 1) vacuum f) f := by
  change tensorRepresentation (factors 2) (qDivPow _ 1 _) (appendTensor _ (tensorRepresentation (factors 1)
    (qDivPow _ 1 _) (appendTensor _ vacuum h)) h) = _
  rw [quantum_one,lower_one_factor,tensorRepresentation_F_append,lower_one_factor,twice_on_factor]
  simp [appendTensor]

private theorem append_ne_zero {n : ℕ} {x : TensorSpace (factors n)} (hx : x ≠ 0)
    {y : IrreducibleModule R 𝕍 omegaOne.1} (hy : y ≠ 0) : appendTensor (factors (n+1)) x y ≠ 0 := by
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one (RatFunc ℚ) hy
  intro e
  have he := congrArg (fun z => (TensorProduct.rid (RatFunc ℚ) (TensorSpace (factors n)))
    (φ.lTensor _ (tensorSplitLast (factors (n+1)) z))) e
  exact hx (by simpa [appendTensor,hφ] using he)

private theorem splitWord_vector_ne_zero : tensorWordVector splitWord (factors 2) ≠ 0 := by
  have hvac : vacuum ≠ 0 := by
    intro hz
    have h := congrArg (PiTensorProduct.isEmptyEquiv (Fin 0)) hz
    simp [vacuum, tensorWordVector, PiTensorProduct.isEmptyEquiv_apply_tprod] at h
  have hf := Stendhal.SingleBlack.lower_ne_zero omegaOne () regular (by decide)
  rw [splitWord_vector]
  exact append_ne_zero (append_ne_zero hvac hf) hf

private theorem divided_two_on_factor :
    qDivPow (𝕍 ^ D.toLusztig.d ()) 2 (F R 𝕍 ()) • h = 0 := by
  simp only [qDivPow, smul_assoc, pow_two, mul_smul, twice_on_factor, smul_zero]

private theorem divided_two_on_prefix :
    tensorRepresentation (factors 1) (qDivPow (𝕍 ^ D.toLusztig.d ()) 2 (F R 𝕍 ()))
      (appendTensor (factors 1) vacuum h) = 0 := by
  rw [qDivPow, map_smul, LinearMap.smul_apply, pow_two, map_mul, Module.End.mul_apply,
    lower_one_factor,lower_one_factor,twice_on_factor]
  simp [appendTensor]

set_option maxHeartbeats 650000 in
private theorem dividedWord_vector :
    tensorWordVector dividedWord (factors 2) = tensorWordVector splitWord (factors 2) := by
  change tensorRepresentation (factors 2) (qDivPow _ 2 _) (appendTensor _ (appendTensor _ vacuum h) h) = _
  rw [tensorRepresentation_dividedF_append (factors 2) () 2 (appendTensor (factors 1) vacuum h) h (μ := omegaOne.1) (IrreducibleModule.hwv_mem_weightSpace (R := R)
    (v := 𝕍) (Λ := omegaOne.1)),splitWord_vector]
  rw [show Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(0,2),(1,1),(2,0)} by decide]
  have hc : dividedCoefficient (R := R) omegaOne.1 () 1 1 = 1 := by
    change LaurentPolynomial.T (1 * (1 * 1) + 1 * (1 * -(1 : ℤ))) = (1 : LaurentPolynomial ℤ)
    norm_num
  simp [Finset.sum_insert, divided_two_on_factor, quantum_one, hc]
  rw [divided_two_on_prefix,lower_one_factor]
  simp [appendTensor]

private abbrev identification := tensorModuleEquiv D params regular level (factors 2) level_eq

/-- The two fundamental factors reach the same bottom vector by the separated
lowerings and by the length-two divided block. This vector is nonzero. -/
example : tensorWordProjectiveClass level D params dividedWord =
    tensorWordProjectiveClass level D params splitWord := by
  apply identification.injective
  rw [tensorModuleEquiv_word,tensorModuleEquiv_word]
  exact Subtype.ext dividedWord_vector

example : tensorWordProjectiveClass level D params splitWord ≠ 0 := by
  intro hz
  have ht : integralWordVector (C := D) (factors 2) splitWord = 0 := by
    rw [← tensorModuleEquiv_word D params regular level (factors 2) level_eq, hz, map_zero]
  exact splitWord_vector_ne_zero (congrArg Subtype.val ht)

/-- Ordinary right induction from RBR applies F a second time. Divided
induction of multiplicity two applies F⁽²⁾ directly to the two-red vacuum. -/
example := tensorModuleEquiv_F D params regular level (factors 2) level_eq ()
  (tensorWordProjectiveClass level D params ((TensorWord.empty.red.black () 1).red))
example := tensorModuleEquiv_dividedF D params regular level (factors 2) level_eq () 2
  (tensorWordProjectiveClass level D params TensorWord.empty.red.red)

example := tensorModuleEquiv_lastRed D params regular level (factors 2) level_eq
  (tensorWordProjectiveClass (level ∘ Fin.castSucc) D params (TensorWord.empty.red.black () 1))
example := tensorModuleEquiv_unique D params regular level (factors 2) level_eq identification.toLinearMap
  (tensorModuleEquiv_word D params regular level (factors 2) level_eq)

example := tensorModuleEquiv_E D params regular level (factors 2) level_eq ()
  (tensorWordProjectiveClass level D params splitWord)

/-- The target shift tests the argument order in the graded Hom comparison
on the bottom projective of the two-fundamental tensor product. -/
example := tensorModuleEquiv_homGdimPoly D params regular level (factors 2) level_eq
  splitWord.content.toMultiset (tensorWordProjective level D params splitWord)
  ((tensorWordProjective level D params splitWord).shift 1)

/-- The full Euler form also pairs sums supported in different black contents. -/
example := tensorModuleEquiv_homForm D params regular level (factors 2) level_eq
  (tensorWordProjectiveClass level D params TensorWord.empty.red.red +
    tensorWordProjectiveClass level D params splitWord)
  (-tensorWordProjectiveClass level D params splitWord)

-- Theorem 4.38 and Lemma 4.36 for graded right projectives.
example : rightTensorModuleEquiv D params regular level (factors 2) level_eq
    (rightTensorWordProjectiveClass D params level splitWord) =
      integralWordVector (C := D) (factors 2) splitWord :=
  rightTensorModuleEquiv_word D params regular level (factors 2) level_eq splitWord
example := rightTensorModuleEquiv_unique D params regular level (factors 2) level_eq
  (rightTensorModuleEquiv D params regular level (factors 2) level_eq).toLinearMap
  (rightTensorModuleEquiv_word D params regular level (factors 2) level_eq)
example := rightTensorModuleEquiv_homForm D params regular level (factors 2) level_eq
  (rightTensorWordProjectiveClass D params level TensorWord.empty.red.red)
  (rightTensorWordProjectiveClass D params level splitWord)

/-- Webster, arXiv:1309.3796v2, Cor. 3.22, for the word projective `R^ω e(i)` of `sl₂`. -/
example := cyclotomicWordModule_word D (Finsupp.single () 1) params omegaOne
  (fun i => level_eq 0 i) regular [()] [()] rfl rfl

/-- Webster, arXiv:1309.3796v2, Prop. 5.6 (word characters), for two red strands of weight `ω`
of `sl₂`, each followed by one black strand. -/
example (ν : Multiset Unit) (w : TensorWordAt 2 ν) :=
  iteratedStandard_word D params regular 2 level (fun _ => [()]) (factors 2)
    (fun j i => (level_eq j i).symm) ν w

/-- Webster, arXiv:1309.3796v2, Prop. 5.6 (on the projective group), for the same standard
module. -/
example (ν : Multiset Unit) (x : tensorProjectiveGroup D params level ν) :=
  iteratedStandardTest_eq D params regular 2 level (fun _ => [()]) (factors 2)
    (fun j i => level_eq j i) ν x

end TwoFundamentalLowerings

end CyclotomicHighestWeight

namespace CyclotomicDividedWords

open Categorification.QuantumGroup MvPolynomial

private def C₂ : CartanDatum (Fin 2) where
  dot i j := if i = j then 2 else 0
  symm := by decide
  dot_self_pos := by decide
  dot_self_even i := by fin_cases i <;> decide
  dot_nonpos := by decide
  dvd_two_mul i j := by fin_cases i <;> fin_cases j <;> decide
private def params (i j : Fin 2) : MvPolynomial (Fin 2) ℚ := if i = j then 0 else C 2
private theorem admissible : KLR.IsRouquierQ C₂ params where
  symm i j h := by simp [params, h, h.symm]
  homogeneous i j h := by
    simpa [params, C₂, h] using (isWeightedHomogeneous_C ![(2 : ℤ), 2] (2 : ℚ))
  unit_coeff i j h := by
    simp [params, C₂, CartanDatum.dij, h]

private abbrev blocks : List (Fin 2 × ℕ) := [(0, 2), (1, 1)]
private abbrev β : Multiset (Fin 2) := KLR.KLRAlgebra.expandDiv blocks
example := admissible.gradingDatum.of_expanded_eq_factorial (fun i j => congrArg Neg.neg (C₂.symm i j))
  C₂ (fun _ => rfl) blocks (rfl : (KLR.KLRAlgebra.expandDiv blocks : Multiset _) = β)
example := KLR.CycKLR.span_dividedProjective_of_rouquier C₂ (fun _ => 2) β admissible
example := KLR.CycKLR.of_expanded_eq_factorial admissible.gradingDatum
  (fun i j => congrArg Neg.neg (C₂.symm i j)) C₂ (fun _ => 2) β (fun _ => rfl) blocks rfl
example := KLR.CycKLR.span_total_dividedProjective C₂ (fun _ => 2) admissible

end CyclotomicDividedWords

section RedCornerEquivalence

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Adding a second red weight in a block with repeated and adjacent colours. -/
example := Stendhal.appendRedStendhalValue_injective wkWeightZeroGraph.klrQ
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 2) ({0, 1, 0} : Multiset (Fin 2))
  wkWeightZeroGraph_standing.isRouquierQ

noncomputable example := Stendhal.appendRedEquiv wkWeightZeroGraph.klrQ
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 2) ({0, 1, 0} : Multiset (Fin 2))
  wkWeightZeroGraph_standing.isRouquierQ

/-- Splitting the red weight `2ϖ₀` into `ϖ₀ + ϖ₀`, with repeated and adjacent colours
(Webster, arXiv:1309.3796v3, Proposition 4.21). -/
noncomputable example := Stendhal.SplitRed.splitRedEquiv (0 : Fin 1) wkWeightZeroGraph.klrQ
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 2) 1) (ν := ({0, 1, 0} : Multiset (Fin 2)))
  wkWeightZeroGraph_standing.isRouquierQ

end RedCornerEquivalence

namespace RightBlackInduction
open Categorification KLR.Unfurling Stendhal
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private noncomputable def mult : Fin 2 → Bool →₀ ℕ := fun _ => Finsupp.single true 1
private def arrows (i j : Bool) : ℕ := if i = false ∧ j = true then 1 else 0
private noncomputable def G := stendhalGradingDatum mult (unfGrading (k := ℚ) arrows)
  (fun _ => 1) (fun _ => rfl)

/-- The second right-black induction on the regular projective with one existing black strand
and two red fundamental weights. -/
example := blackIndK0_regular G true ({true} : Multiset Bool)

example := blackLower_lof G true ({true} : Multiset Bool)
  (Graded.K0.of (Graded.GProj.regular (tensorProductGrade G {true})))


noncomputable example := lastRedIndK0 G ({true} : Multiset Bool)

end RightBlackInduction

namespace TwoRedFirstWeight

open Categorification LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open Categorification.Stendhal.FirstWeight LusztigF


private def sl2HighestTwo : Dom sl2RootDatum :=
  ⟨2 • AddMonoidHom.id ℤ, fun _ => by simp [LieLean.QuantumGroup.sl2RootDatum]⟩

private theorem sl2XRegular : sl2RootDatum.IsXRegular := by
  change LinearIndependent ℤ sl2RootDatum.root
  rw [linearIndependent_unique_iff]
  intro h
  have hh := congrArg (fun f : ℤ →+ ℤ => f 1) h
  norm_num at hh

private def twoWeights : Fin 2 → Dom sl2RootDatum := fun _ => sl2HighestTwo

/-- The divided red/black vectors span at every black weight. The first
factor here has highest weight zero and the second has highest weight two. -/
example := span_tensorWordVector (![(⟨0, by simp⟩ : Dom sl2RootDatum), sl2HighestTwo])

example := tensorWordVector (((TensorWord.empty.red.black () 2).red).black () 1) twoWeights

/-- A divided lowering of multiplicity two on the first red factor followed by
one lowering on the entire tensor product agree under the quasi-R equivalence. -/
example := tensorCoproductEquiv_word sl2XRegular
  (((TensorWord.empty.red.black () 2).red).black () 1) twoWeights

example := barTensorWord_sum_eq_zero_iff sl2XRegular twoWeights (Finset.univ : Finset (Fin 2))
  (fun j => LaurentPolynomial.T (j.val : ℤ))
  (fun j => ((TensorWord.empty.red.black () j.val).red).black () (2 - j.val))
example := span_tensorWordVector_content twoWeights sl2XRegular (Finsupp.single () 3)

private def redLevelTwo : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

private def redLevelTwoGrading :=
  Stendhal.stendhalGradingDatum redLevelTwo (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit))
    (fun _ => 1) (fun _ => rfl)

example := tensorWordSequenceProj_red redLevelTwoGrading (TensorWord.empty.red.black () 1)
example := tensorWordSequenceProj_black redLevelTwoGrading TensorWord.empty.red.red ()

private theorem redPos (r : Fin 2) : 0 < redLevelTwo r () := by simp [redLevelTwo]

private theorem weightAgreement (r : Fin 2) :
    (twoWeights r).1 (sl2RootDatum.coroot ()) = (redLevelTwo r () : ℤ) := by
  simp [twoWeights, sl2HighestTwo, redLevelTwo, LieLean.QuantumGroup.sl2RootDatum]

private theorem dotsPos (a : Unit ⊕ Fin 2) : 0 < redLevelTwoGrading.degX a := by
  cases a <;> exact (by decide : (0 : ℤ) < 2)

example := sequenceLatticeEquiv_boundary () twoWeights redLevelTwoGrading
  sl2XRegular weightAgreement dotsPos redPos (1 : Fin 2)

example := sequenceLatticeEquiv_boundary_shift () twoWeights redLevelTwoGrading
  sl2XRegular weightAgreement dotsPos redPos (0 : Fin 2) 1

example : pVector twoWeights () (1 : Fin 2) =
    (RatFunc.X : RatFunc ℚ) ^ (-2 : ℤ) • loweredPure twoWeights () (0 : Fin 2) +
      loweredPure twoWeights () (1 : Fin 2) := by
  have h : Finset.Iic (1 : Fin 2) = Finset.univ := by decide
  rw [pVector_eq_sum, h, Fin.sum_univ_two, tensor_laurent_smul, tensor_laurent_smul]
  have h₀ : prefixCoefficient twoWeights () (1 : Fin 2) (0 : Fin 2) = LaurentPolynomial.T (-2) := by
    rw [prefixCoefficient, Fin.prod_univ_two]
    change LaurentPolynomial.T 0 * LaurentPolynomial.T (-2) = _
    simp
  have h₁ : prefixCoefficient twoWeights () (1 : Fin 2) (1 : Fin 2) = LaurentPolynomial.T 0 := by
    rw [prefixCoefficient, Fin.prod_univ_two]
    change LaurentPolynomial.T 0 * LaurentPolynomial.T 0 = _
    simp
  rw [h₀, h₁, integralLaurentEval_T, integralLaurentEval_T, zpow_zero, one_smul]

end TwoRedFirstWeight

namespace LastRedSuffix


open Stendhal KLR

private def rrbb : Seq (stendhalWeight 2 ({0, 0} : Multiset (Fin 1))) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl 0, .inl 0] (by decide)

private theorem ordered : IsRedOrdered rrbb := by unfold IsRedOrdered; decide

/-- With two fundamental red weights, the final pair of equal black strands
factors through a loading with one black strand after the last red. -/
example := lastRed_boundary_mem_span (fun _ _ : Fin 1 => (0 : MvPolynomial (Fin 2) ℚ))
  (fun _ : Fin 2 => Finsupp.single (0 : Fin 1) 1) rrbb ordered 1 (by decide) 0
  rfl rfl (by simp [stendhalWeight]) (by
    simp only [Finsupp.single_eq_same]
    unfold KLRAlgebra.IsConstOn
    decide)

end LastRedSuffix

namespace OneRedEulerForm

open Categorification LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open Stendhal.SingleBlack

private def highestTwo : Dom sl2RootDatum :=
  ⟨2 • AddMonoidHom.id ℤ, fun _ => by simp [LieLean.QuantumGroup.sl2RootDatum]⟩

private theorem xRegular : sl2RootDatum.IsXRegular := by
  change LinearIndependent ℤ sl2RootDatum.root
  rw [linearIndependent_unique_iff]
  intro h
  have hh := congrArg (fun f : ℤ →+ ℤ => f 1) h
  norm_num at hh

private def levelTwo : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

private def gradingTwo :=
  Stendhal.stendhalGradingDatum levelTwo (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit))
    (fun _ => 1) (fun _ => rfl)

example := regular_homGdimPoly_eq_shapovalov highestTwo xRegular () gradingTwo
  (by simp [highestTwo, levelTwo, LieLean.QuantumGroup.sl2RootDatum]) (by decide)

example := regular_shift_homGdimPoly_eq_shapovalov highestTwo xRegular () gradingTwo
  (by simp [highestTwo, levelTwo, LieLean.QuantumGroup.sl2RootDatum]) (by decide) (by simp [levelTwo]) 1 0

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "Reg" => Categorification.Graded.GProj.regular (Stendhal.tensorProductGrade gradingTwo {()})

/-- A sum of shifted projective classes paired with a virtual negative class. -/
example := homForm_eq_shapovalov () gradingTwo highestTwo xRegular
  (by simp [highestTwo, levelTwo, LieLean.QuantumGroup.sl2RootDatum]) (by decide) (by simp [levelTwo])
  (Categorification.Graded.K0.of Reg + Categorification.Graded.K0.of ((Reg).shift 1))
  (-Categorification.Graded.K0.of Reg)

end OneRedEulerForm

namespace TensorFormConvention

open LieLean.QuantumGroup Stendhal.TensorPairing

example := terminal_homGdimPoly_ne_printedForm
example := correctedForm_adjoint sl2XRegular fundamental fundamental
  (F sl2RootDatum (RatFunc.X : RatFunc ℚ) ()) highestPair loweredPair

example := fundamental_prefix_homGdimPoly_eq_correctedForm 0 1
example := fundamental_prefix_homGdimPoly_eq_correctedForm 1 1

example := fundamental_restriction_eq_E 0
example := fundamental_restriction_eq_E 1

example := printedForm_not_adjoint
example := barCoproduct_loweredPair_norm
example := Stendhal.TensorAdjointConvention.tau_barComul_F_ne_comul_tau_F
example := Stendhal.TensorAdjointConvention.barComul_tau_F LieLean.QuantumGroup.sl2RootDatum ()

private theorem rouquier : KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))
    (KLR.klQ (k := ℚ) (⊥ : SimpleGraph Unit)) := by
  constructor <;> intro i j h <;> exact (h (Subsingleton.elim _ _)).elim

example := Stendhal.projective_blackRes_regular (Λ := fundamentalLabels) () {()}
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) rouquier

example := Stendhal.blackResProj fundamentalGrading () {()}
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) rouquier
  (Categorification.Graded.GProj.regular _)

example := Stendhal.cyclotomicCoverQuotientEquiv
  (Q := KLR.klQ (k := ℚ) (⊥ : SimpleGraph Unit)) fundamentalLabels {()}
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))

example := Stendhal.cyclotomicCoverToTensor_preservesGrading fundamentalLabels
  (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) rouquier {()}

private abbrev loading := Stendhal.FirstWeight.boundaryAt () 1 0

/-- Appending a fundamental strand preserves the degree-two Hom dimension. -/
example := Stendhal.finrank_homGrade_appendRed rouquier fundamentalGrading {()}
  loading.1 loading.1 loading.2.1 loading.2.1 2

example := orderedForm_binary sl2XRegular twoFundamental
  (Stendhal.FirstWeight.pVector twoFundamental () 0) (Stendhal.FirstWeight.pVector twoFundamental () 1)

example := orderedForm_adjoint sl2XRegular twoFundamental (F sl2RootDatum (RatFunc.X : RatFunc ℚ) ())
  (Stendhal.FirstWeight.pVector twoFundamental () 0) (Stendhal.FirstWeight.pVector twoFundamental () 1)

/-- Webster, arXiv:1309.3796v3, Prop 4.33: nondegeneracy of the ordered form. -/
example := Stendhal.TensorPairing.orderedForm_nondegenerate sl2XRegular twoFundamental

/-- Webster, arXiv:1309.3796v3, Prop 4.33: uniqueness, applied to the ordered form itself. -/
example := Stendhal.TensorPairing.orderedForm_unique sl2XRegular
  (fun wt => Stendhal.TensorPairing.orderedForm sl2XRegular wt)
  (fun wt x y => Stendhal.TensorPairing.orderedForm_empty sl2XRegular wt x y)
  (fun wt u x y => Stendhal.TensorPairing.orderedForm_adjoint sl2XRegular wt u x y)
  (fun wt x y => Stendhal.TensorPairing.orderedForm_append_highest sl2XRegular wt x y)
  twoFundamental

end TensorFormConvention

namespace LastRedLayerExample

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
open scoped TensorProduct
open Stendhal KLR

private abbrev Q := fun _ _ : Fin 1 => (0 : MvPolynomial (Fin 2) ℚ)
private abbrev Λ := fun _ : Fin 2 => Finsupp.single (0 : Fin 1) 1
private abbrev α := stendhalWeight 2 (0 : Multiset (Fin 1))
private abbrev β := ({0} : Multiset (Fin 1))
private abbrev μ := stendhalWeight 2 β
private def rr : Seq α := KLRAlgebra.Seq.ofList [.inr 0,.inr 1] (by decide)
private def b : Seq β := KLRAlgebra.Seq.ofList [0] (by decide)
private def p : Fin μ.card := ⟨1,by decide⟩
private theorem h : α + β.map (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 2) = μ := by decide
private def rrb := Seq.cast h (rr.append (Seq.map Sum.inl b))

/-- At red-red-black, the algebra of the single black strand descends to
the final fundamental cyclotomic quotient. -/
example := suffixCyclotomic_mk Q Λ p h (by decide) (KLRAlgebra.x (⟨0,by decide⟩ : Fin β.card))

/-- At the same loading the layer corner is spanned by affine juxtaposition. -/
example (z : TensorProductAlgebra ℚ Q Λ β) := sandwich_mem_range_suffixConcat Q Λ p h
  (by decide) rr (Seq.map Sum.inl b) rrb rrb (by unfold IsRedOrdered; decide)
  (by unfold IsRedOrdered; decide) rfl rfl rfl z

example := lastRedLayerTensor_surjective Q Λ p h (by decide)

/-- With two fundamental red strands and one black strand in each input,
the unit of the two factor algebras lifts to a common parabolic diagram. -/
example := lastRedLayerAction_exists_parabolicLift Q Λ
  (ν := β+β) (θ := β) (β := β) ⟨2,by decide⟩ (by decide) (by decide)
  (parabolicInputWeights_add (ℓ := 1) β β) 1

/-- The vacuum representation of two red strands has a detecting split. -/
example := exists_detecting_lastRedCorner (B := ℚ) (ℓ := 1) (Q := Q) (Λ := Λ) (ν := 0) (tensorProductAlgebraZeroEquiv Q Λ).toAlgHom

example := exists_lastRedLayerIdem_mul_boundary Q Λ rrb (by unfold IsRedOrdered; decide) p rfl

private def blackDegrees : GradingDatum Q where
  degX _ := 2
  degΨ _ _ := -2
  degΨ_self _ := rfl
  isWeightedHomogeneous i j hij := (hij (Subsingleton.elim i j)).elim

private def diagramDegrees := stendhalGradingDatum Λ blackDegrees (fun _ => 1) (fun _ => rfl)

example := lastRedLayerTensor_mem_grade Q Λ diagramDegrees p h (by decide)
  (d := 0+0) (z := 1 ⊗ₜ 1)
  (Categorification.Graded.tmul_mem_tensorGrading SetLike.GradedOne.one_mem SetLike.GradedOne.one_mem)

private theorem parameters : IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph (Fin 1))) Q where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private def redBlackRed : Seq μ := KLRAlgebra.Seq.ofList [.inr 0,.inl 0,.inr 1] (by decide)
private theorem redBlackRed_ordered : IsRedOrdered redBlackRed := by unfold IsRedOrdered; decide

/-- The black strand crosses the second red on both sides of this affine corner. -/
example : ¬ RedsFirst redBlackRed := by
  intro h
  exact (by decide : ¬ true ≤ false)
    (h (show (⟨1, by decide⟩ : Fin μ.card) ≤ ⟨2, by decide⟩ by decide))

example := exists_redsFirst_compression (Λ := Λ) parameters redBlackRed redBlackRed
  redBlackRed_ordered redBlackRed_ordered

private abbrev affine := StendhalAlgebra ℚ Q Λ β
private def scalarAtMiddle : affine →ₐ[ℚ] ℚ :=
  (FirstWeight.boundaryCharacter Q Λ (i := 0) (fun _ => by simp [Λ]) redBlackRed
    redBlackRed_ordered (by unfold IsViolated; decide)).comp (TensorProductAlgebra.mk Q Λ β)

example : scalarAtMiddle (StendhalAlgebra.e redBlackRed redBlackRed_ordered) = 1 := by
  simp [scalarAtMiddle]

example := exists_redsFirst_ideal_element parameters
  (⊤ : TwoSidedIdeal affine) (by
    let := scalarAtMiddle.toRingHom.domain_nontrivial
    exact top_ne_bot)

private def bubbleAtMiddle (a : ℚ) : Polynomial ℚ ⊗[ℚ] affine →ₐ[ℚ] ℚ :=
  Algebra.TensorProduct.productMap (Polynomial.aeval a) scalarAtMiddle

/-- The positive-degree bubble belongs to the zero-evaluation kernel and is
detected by evaluation at one, so this ideal is nonzero and proper. -/
example := exists_redsFirst_tensor_ideal_element parameters
  (TwoSidedIdeal.ker (bubbleAtMiddle 0).toRingHom) (by
    intro h
    let y := (Polynomial.X : Polynomial ℚ) ⊗ₜ[ℚ] (1 : affine)
    have hy (a : ℚ) : bubbleAtMiddle a y = a := by simp [bubbleAtMiddle, y]
    have hm := (TwoSidedIdeal.mem_ker (bubbleAtMiddle 0).toRingHom).2 (hy 0)
    rw [h, TwoSidedIdeal.mem_bot] at hm
    exact one_ne_zero (α := ℚ) ((hy 1).symm.trans (hm ▸ map_zero (bubbleAtMiddle 1))))

/-- In the output red-red-black-black, the final left-assigned black
strand crosses the right red (+1) and the right black (−2). -/
private abbrev shufflePrefixWt := Multiset.map (addRedColor 1) (stendhalWeight 1 β)
private abbrev shuffleFinalWt := Multiset.map (Sum.map (id : Fin 1 → Fin 1)
  (fun _ : Fin 1 => Fin.last 1)) (stendhalWeight 1 β)
private def shuffleWord : KLR.Seq (shufflePrefixWt + shuffleFinalWt) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl 0,.inl 0] (by decide)
private def shuffleAssignment (j : Fin (shufflePrefixWt + shuffleFinalWt).card) : Bool :=
  decide (j.val = 1 ∨ j.val = 2)
private theorem shufflePair : ∃ u : KLRAlgebra.ShuffleOf shufflePrefixWt shuffleFinalWt shuffleWord,
    u.mask = shuffleAssignment :=
  KLRAlgebra.ShuffleOf.exists_mask_eq shuffleAssignment (by decide) (by decide)
private def shuffleExample := shufflePair.choose
private abbrev shuffleCartan := CartanDatum.ofGraph (⊥ : SimpleGraph (Fin 1))

example :
    (stendhalGradingDatum Λ parameters.gradingDatum (fun i => shuffleCartan.dot i i / 2)
      (fun i => (QuantumGroup.UDot.two_mul_di shuffleCartan i).symm)).indShuffleDegree
      shuffleExample.1 shuffleWord = -1 := by
  have hm : shuffleExample.mask = shuffleAssignment := shufflePair.choose_spec
  have hv : ¬ IsViolated shuffleExample.split.2 := by
    rintro ⟨h,hh⟩
    have hs := shuffleExample.ofFn_split_snd
    rw [hm] at hs
    have hx : FreeMonoid.toList (QuantumGroup.PreF.maskWord shuffleWord.1 shuffleAssignment true) =
        [Sum.inr 1,Sum.inl (0 : Fin 1)] := by decide
    rw [hx] at hs
    have he := congrArg (fun l => l[0]?) hs
    simp only [List.getElem?_ofFn,List.getElem?_cons_zero] at he
    simp at he
    obtain ⟨_,he⟩ := he
    change (shuffleExample.split.2.1 ⟨0,h⟩).isLeft at hh
    rw [he] at hh
    contradiction
  have he := lastRed_indShuffleDegree parameters Λ shuffleExample (by unfold IsRedOrdered; decide) hv
  rw [hm] at he
  apply he.trans
  have hl : (List.ofFn fun j => (shuffleWord.lbl j,shuffleAssignment j)) =
      [(.inr 0,false),(.inr 1,true),(.inl 0,true),(.inl 0,false)] := by decide
  rw [hl]
  norm_num [shuffleCrossingSum,lastRedCrossing,Λ]


example := lastRedLayerK0_surjective Q Λ diagramDegrees p h (by decide) parameters

example := lastRedLayerSourceIndecClassEquiv parameters (Λ ∘ Fin.castSucc) (0 : Multiset (Fin 1))
  (Λ 1) β (restrictRedGrading Q Λ diagramDegrees) (restrictBlackGrading Q Λ diagramDegrees)

example := lastRedRankEmbedding Λ β parameters diagramDegrees
example := lastRedK0_rank_le Λ β parameters diagramDegrees

/-- At the highest tensor weight both factors are nonzero scalar algebras. -/
example := lastRedHeadEquiv Λ 0 diagramDegrees parameters (nonempty_lastRedInducedCut_zero Λ diagramDegrees)
example := lastRedK0_rank_eq_of_inducedCut Λ 0 diagramDegrees parameters (nonempty_lastRedInducedCut_zero Λ diagramDegrees)

section StandardCut

open Categorification.Graded

private theorem singleton_block_rank :
    Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade diagramDegrees β)) = 2 := by
  let basis := (FirstWeight.sequenceProjBasis (i := (0 : Fin 1)) diagramDegrees
    (fun a => by cases a <;> exact (by decide : (0 : ℤ) < 2))
    (fun _ => by simp [Λ])).reindex (FirstWeight.boundaryEquiv (0 : Fin 1) 2).symm
  simpa using basis.mk_eq_rank.symm

private abbrev grLast := restrictBlackGrading Q Λ diagramDegrees

private def finalClass : GProj.IndecClass (CycKLR.grade grLast (Λ 1) β) := by
  let Λ₁ := fun _ : Fin 1 => Λ 1
  let := tensorProductAlgebra_finite Λ₁ β parameters
  let e := (SingleRed.cyclotomicEquiv Q Λ₁ β).symm.toLinearEquiv
  let := Module.Finite.of_surjective e.toLinearMap e.surjective
  let g := CycKLR.grade grLast (Λ 1) β
  let := HasGdim.of_finiteDimensional g
  let c := CycKLR.singleK0Equiv grLast (Λ 1) 0 (by simp [Λ])
  apply Classical.choice
  by_contra hn
  let : IsEmpty (GProj.IndecClass g) := not_nonempty_iff.mp hn
  have hz : c.symm 1 = 0 := (K0.indecBasis g).repr.injective (Subsingleton.elim _ _)
  exact one_ne_zero (c.symm.injective (hz.trans c.symm.map_zero.symm))

private def earlierClass : GProj.IndecClass (tensorProductGrade (restrictRedGrading Q Λ diagramDegrees) β) :=
  FirstWeight.sequenceProjIndecEquiv (i := (0 : Fin 1)) (restrictRedGrading Q Λ diagramDegrees)
    (fun a => by cases a <;> exact (by decide : (0 : ℤ) < 2)) (fun r => by simp [Λ])
    (FirstWeight.boundaryAt 0 1 0)

private def splitClass : GProj.IndecClass
    (lastRedFactorGrading Λ (β+β) diagramDegrees ⟨(β,β),rfl⟩) :=
  (lastRedLayerSourceIndecClassEquiv parameters (Λ ∘ Fin.castSucc) β (Λ 1) β
    (restrictRedGrading Q Λ diagramDegrees) grLast).symm (earlierClass, finalClass)

/-- Both possible single-black cuts together contribute two projective shift classes. -/
example : Cardinal.sum (fun u : LastRedWeightSplit β =>
    Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade
      (restrictRedGrading Q Λ diagramDegrees) u.1.1)) *
    Module.rank (LaurentPolynomial ℤ) (K0 (CycKLR.grade grLast (Λ 1) u.1.2))) = 2 :=
  (lastRedK0_rank_eq Λ β diagramDegrees parameters).symm.trans singleton_block_rank

/-- Standardization and its simple head with one black strand in each factor. -/
example := nonempty_lastRedInducedCut Λ (β+β) diagramDegrees parameters.klrSymm
  ⟨(β,β),rfl⟩ splitClass

example := lastRedStandardHeadEmbedding Λ (β+β) diagramDegrees parameters
  ⟨⟨(β,β),rfl⟩, earlierClass, finalClass⟩

example := lastRedStandardHeadEquiv Λ β diagramDegrees parameters

end StandardCut

example := tensorRepresentationLift_comp _ (tensorRepresentationRelations_projection (Q := Q) (Λ := Λ) (ν := β))

/-- The one-dimensional regular module is generated on its full corner. -/
private abbrev scalarBoundary := NonUnitalAlgHom.id ℚ ℚ
private def fullScalarCut : ℚ ≃ₗ[ℚ] boundaryFixed scalarBoundary ℚ where
  toFun x := ⟨x,one_smul _ _⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem fullScalarGen : Submodule.span ℚ {x : ℚ | scalarBoundary 1 • x = x} = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  exact fun x => Submodule.subset_span (one_smul ℚ x)

example : IsSimpleModule ℚ (ℚ ⧸ cornerKernel (scalarBoundary 1) ℚ) := by
  let := IsSimpleModule.congr fullScalarCut.symm
  exact (eq_cornerKernel_iff_simpleQuotient ℚ scalarBoundary fullScalarGen _).mp rfl

example := lastRedShuffle_eq_one (show 1+2=3 from rfl)
  ⟨1, TypeA.isShuffle_one _⟩ (by decide) (by decide)

private def swapTwo : TypeA.Shuffle (show 1+1=2 from rfl) :=
  ⟨TypeA.sadj 2 0, fun _ _ h => (by omega : False).elim, fun _ _ h => (by omega : False).elim⟩

example := shuffle_right_descent (show 1+1=2 from rfl) swapTwo (by decide : 0+1<2)
  (x := 0) (y := 0) (by decide) (by decide)

private abbrev inputLeft := (stendhalWeight 1 (0 : Multiset (Fin 1))).map (addRedColor 1)
private abbrev inputRight := (stendhalWeight 1 β).map (Sum.map (id : Fin 1 → Fin 1) (fun _ : Fin 1 => Fin.last 1))
private def rawRRB : Seq (inputLeft+inputRight) := KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl 0] (by decide)

private def regularCut : Graded.GFin (Graded.tensorGrading
    (tensorProductGrade (restrictRedGrading Q Λ diagramDegrees) (0 : Multiset (Fin 1)))
    (CycKLR.grade (restrictBlackGrading Q Λ diagramDegrees) (Λ 1) β)) := by
  let := lastRedLayerSource_finite parameters (Λ ∘ Fin.castSucc) (0 : Multiset (Fin 1)) (Λ 1) β
  exact {
    carrier := parabolicFactorAlgebra Q Λ (0 : Multiset (Fin 1)) β
    grading := Graded.tensorGrading
      (tensorProductGrade (restrictRedGrading Q Λ diagramDegrees) (0 : Multiset (Fin 1)))
      (CycKLR.grade (restrictBlackGrading Q Λ diagramDegrees) (Λ 1) β)}

example := standardizationFixedEquiv Λ diagramDegrees 0 β parameters.symm regularCut rawRRB
  (by unfold IsRedOrdered; decide)
example := gdimPoly_standardization Λ diagramDegrees 0 β parameters.symm regularCut rawRRB
  (by unfold IsRedOrdered; decide)
private def prefixRegular :
    Graded.GFin (tensorProductGrade (restrictRedGrading Q Λ diagramDegrees) (0 : Multiset (Fin 1))) := by
  let := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) (0 : Multiset (Fin 1)) parameters
  exact {carrier := TensorProductAlgebra ℚ Q (Λ ∘ Fin.castSucc) (0 : Multiset (Fin 1)),
         grading := tensorProductGrade (restrictRedGrading Q Λ diagramDegrees) 0}

private def finalRegular : Graded.GFin (CycKLR.grade (restrictBlackGrading Q Λ diagramDegrees) (Λ 1) β) := by
  let := CycKLR.module_finite (Q := Q) (ν := β) (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (fun i => Polynomial.monic_X_pow (R := ℚ) (Λ 1 i))
  exact {carrier := CycKLR ℚ Q (fun i => Polynomial.X ^ Λ 1 i) β,
         grading := CycKLR.grade (restrictBlackGrading Q Λ diagramDegrees) (Λ 1) β}

example := gdimPoly_standardization_extTensor Λ diagramDegrees 0 β parameters.symm prefixRegular finalRegular rawRRB
  (by unfold IsRedOrdered; decide)

private def oneRed : Seq (stendhalWeight 1 (0 : Multiset (Fin 1))) :=
  KLRAlgebra.Seq.ofList [.inr 0] (by decide)

/-- Webster, arXiv:1309.3796v2, step in the proof of Prop 5.20, at one red strand followed by the final red
strand and one black strand: `S(S_t ⊠ R e(u)) ≅ S_{t λ_2 u}`. -/
example := twoPieceStandardEquiv Q Λ (θ := 0) (t := oneRed) (by unfold IsRedOrdered; decide) b
  parameters.symm

end LastRedLayerExample

namespace MixedBlackRestriction

open Categorification QuantumGroup KLR.Unfurling
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
def arr : Bool → Bool → ℕ := fun a b => if a = false ∧ b = true then 1 else 0

private theorem oneArrowParameters :
    KLR.IsRouquierQ (coverCartan arr) (unfQ (k := ZMod 2) arr) where
  symm i j hij := (unfQ_klrSymm arr i j hij).symm
  homogeneous i j hij := by
    rw [coverCartan_dot_self, coverCartan_dot_self, coverCartan_dot_of_ne arr hij]
    have hh := (unfGrading (k := ZMod 2) arr).isWeightedHomogeneous i j hij
    change (unfQ (k := ZMod 2) arr i j).IsWeightedHomogeneous ![(2 : ℤ), 2]
      ((if i = j then -2 else 2 * (arr j i : ℤ)) + (if j = i then -2 else 2 * (arr i j : ℤ))) at hh
    rw [ite_eq_right hij, ite_eq_right hij.symm] at hh
    convert hh using 1
    push_cast
    ring
  unit_coeff i j hij := KLR.isUnit_extremalCoeff _ (unfQ_klrSymm arr)
    (fun a b _ => unfQ_leadingCoeff arr a b) (coverWeight arr)
    (fun _ _ h => unfQ_natDegree_eq_neg_pair arr h) hij

/-- Two ordered red strands carry different fundamental colours in type A₂. -/
private def twoRedWeights (r : Fin 2) : Bool →₀ ℕ := Finsupp.single (r == 0) 1


private def G := Stendhal.stendhalGradingDatum twoRedWeights (unfGrading (k := ZMod 2) arr)
  (fun _ => 1) (fun _ => rfl)

example := Stendhal.blackResVacuumProj true G (coverCartan arr) oneArrowParameters
  (Graded.GProj.regular _)

example := Stendhal.homGrade_blackInd_blackRes G true ({false} : Multiset Bool)
  (Graded.GProj.regular _) (Graded.GMod.regular _) (-1)


example := Stendhal.mem_range_mixedBlackMap_iff (Q := unfQ (k := ℚ) arr) twoRedWeights
  ({true} : Multiset Bool) true false (unfQ_klrSymm arr) (by decide)
  (Stendhal.mixedBlackCrossing twoRedWeights {true} true false)


private abbrev lowerT := Stendhal.TensorProductAlgebra (ZMod 2) (unfQ arr) twoRedWeights ({false} : Multiset Bool)
private abbrev leftT := Stendhal.TensorProductAlgebra (ZMod 2) (unfQ arr) twoRedWeights ({false} + {false})
private abbrev rightT := Stendhal.TensorProductAlgebra (ZMod 2) (unfQ arr) twoRedWeights ({true} + {false})
private abbrev appendL := Stendhal.appendBlack (unfQ (k := ZMod 2) arr) twoRedWeights false {false}
private abbrev appendR := Stendhal.appendBlack (unfQ (k := ZMod 2) arr) twoRedWeights true {false}
private abbrev mixedG := Stendhal.stendhalGradingDatum twoRedWeights oneArrowParameters.gradingDatum
  (fun a => (coverCartan arr).dot a a / 2) (Stendhal.dotDegree _ oneArrowParameters)

private def lastL : CornerTensor.Left appendL :=
  ⟨appendL 1, by change appendL 1 * appendL 1 = _; rw [← map_mul, mul_one]⟩
private def lastR : CornerTensor.Right appendR (AlgHom.id (ZMod 2) rightT) :=
  ⟨appendR 1, by change appendR 1 * appendR 1 = _; rw [← map_mul, mul_one]⟩

example := Stendhal.mixedBlackMap_tmul_mem_grade twoRedWeights {false} true false (coverCartan arr)
  oneArrowParameters (by decide) lastL lastR (d := 0) (f := 0)
  (Stendhal.appendBlack_mem_grade _ _ _ _ mixedG SetLike.GradedOne.one_mem)
  (Stendhal.appendBlack_mem_grade _ _ _ _ mixedG SetLike.GradedOne.one_mem)

end MixedBlackRestriction

namespace ParabolicInputs

open Categorification Categorification.KLR Categorification.Stendhal
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
private def q := fun _ _ : Unit => (0 : MvPolynomial (Fin 2) ℚ)
private def w := fun _ : Fin 2 => Finsupp.single () 1
private abbrev β : Multiset Unit := {()}
private def s : KLR.Seq (stendhalWeight 1 β) := KLRAlgebra.Seq.ofList [.inr 0, .inl ()] (by decide)
private def bad : KLR.Seq (stendhalWeight 1 β) := KLRAlgebra.Seq.ofList [.inl (), .inr 0] (by decide)
example := parabolicInputWeights_add (ℓ := 1) β β
example := parabolicPrefixProjection_surjective q w β
example := parabolicLastProjection_surjective q w β
example := parabolicLastCyclotomic_surjective q w β
example := redSubfamilyProjection_e q w Fin.castSucc (Fin.castSucc_injective 1) β s (SingleRed.ordered β s)
example := redSubfamilyProjection_e_violated q w Fin.castSucc (Fin.castSucc_injective 1) β bad
  ⟨by decide, by decide⟩
example := redSubfamilyProjection_red_dot q w Fin.castSucc (Fin.castSucc_injective 1) β s
  (⟨0, by decide⟩ : Fin (Multiset.card (stendhalWeight 1 β))) (by decide)
example := parabolicLastCyclotomic_e q w β (KLRAlgebra.Seq.ofList [()] (by decide))
example := parabolicLastCyclotomic_blackDot q w β ⟨0, by decide⟩
private abbrev predMap := addRedColor (I := Unit) 1
private abbrev lastMap := Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
example := parabolicPrefixProjection_e_violated q w β (Seq.map predMap bad) ⟨by decide, by decide⟩
example := parabolicLastProjection_e_violated q w β (Seq.map lastMap bad) ⟨by decide, by decide⟩
example := parabolicPrefixProjection_red_dot q w β (Seq.map predMap s) ⟨0, by decide⟩ (by decide)
example := parabolicLastProjection_red_dot q w β (Seq.map lastMap s) ⟨0, by decide⟩ (by decide)
example := parabolicPrefix_red_lt_last β (Seq.map predMap s) ⟨0, by decide⟩ (r := 0) (by decide)
example := parabolicLast_red_eq_last β (Seq.map lastMap s) ⟨0, by decide⟩ (r := 1) (by decide)
private def three := fun _ : Fin 3 => Finsupp.single () 1
private def outOfOrder : KLR.Seq (stendhalWeight 2 (0 : Multiset Unit)) :=
  KLRAlgebra.Seq.ofList [.inr 1, .inr 0] (by decide)
example := parabolicPrefixProjection_e_unordered q three 0 (Seq.map (addRedColor 2) outOfOrder)
  (by unfold IsRedOrdered; decide)
example := parabolicLast_ordered β (Seq.map lastMap s)
example := parabolicLastCyclotomic_concat_black q w β (KLRAlgebra.x (⟨0, by decide⟩ : Fin β.card))
private abbrev twoBlack : Multiset Unit := {(), ()}
example := parabolicLastCyclotomic_concat_black q w twoBlack (KLRAlgebra.ψ 0)

private abbrev factors := parabolicFactorAlgebra q w (0 : Multiset Unit) β
private theorem qsymm : KLRSymm q := fun _ _ hab => (hab (Subsingleton.elim _ _)).elim

/-- At the cut before the only black strand, the two-factor algebra
acts on the standardization of its regular module. -/
example := parabolicStandardUnit_injective q w (0 : Multiset Unit) β factors qsymm
example := parabolicStandardAction_concat_unit q w (0 : Multiset Unit) β factors qsymm 1 (1 : factors)
example := parabolicStandardAction_concat_mem_range q w (0 : Multiset Unit) β factors qsymm 1
  (parabolicStandardUnit q w (0 : Multiset Unit) β factors (1 : factors))
example := parabolicStandardLayerAction_comp q w (0 : Multiset Unit) β factors qsymm ⟨1,by decide⟩
  (by decide)
example := parabolicStandardAction_other_concat_eq_zero q w (0 : Multiset Unit) β factors qsymm β
  (0 : Multiset Unit) (by simp) (by decide) 1

end ParabolicInputs

namespace GradedParabolicShuffle

open Categorification KLR KLRAlgebra Graded TypeA KLR.Unfurling

/-- One arrow gives asymmetric crossing degrees for this choice of grading. -/
private def arrow (a b : Bool) : ℕ := if a = false ∧ b = true then 1 else 0
private abbrev Q := unfQ (k := ℚ) arrow
private abbrev G := unfGrading (k := ℚ) arrow
private abbrev hsingle (i : Bool) : ∀ a ∈ ({i} : Multiset Bool), a = i :=
  fun _ h => Multiset.mem_singleton.1 h
private def L (i : Bool) : GFin (G.grade ({i} : Multiset Bool)) where
  carrier := KLRRep (hsingle i) Q
  grading := klrGrading (hsingle i) Q G
private abbrev α := ({true} : Multiset Bool)
private abbrev β := ({false} : Multiset Bool)
private def output : Seq (α + β) := ⟨![false, true], by decide⟩

example := G.gdimPoly_ind_shuffle (unfQ_klrSymm arrow) ((L true).extTensor (L false)) output

example := G.gdimPoly_ind_shuffle_extTensor (unfQ_klrSymm arrow) output (L true) (L false)

private def crossing : Shuffle (Seq.card_add' α β) :=
  ⟨Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩, by
    constructor <;> intro x y h <;> have hy : (y : ℕ) < 1 := y.isLt <;> exact False.elim (by omega)⟩

example : G.indShuffleDegree crossing output = 2 := by
  rw [G.indShuffleDegree_eq_maskInv]
  decide

end GradedParabolicShuffle

namespace RationalFactorCoordinates

open Categorification.Stendhal.FirstWeight
private def scalarBasis : Module.Basis Unit ℚ (⊤ : Submodule ℚ ℚ) :=
  (Module.Basis.singleton Unit ℚ).map (Submodule.topEquiv (R := ℚ) (M := ℚ)).symm
example := exists_separatingLatticeCoordinates (K := ℚ) scalarBasis
example := factorTensorTest_separates (F := ℚ) (fun _ : Unit => (1 : ℚ)) (fun _ : Unit => (1 : ℚ))
  (fun _ => LinearMap.id) (fun _ => LinearMap.id) (Function.Embedding.refl (Unit × Unit))
  (fun a b => by simp [Subsingleton.elim a b]) (fun a b => by simp [Subsingleton.elim a b])

end RationalFactorCoordinates

namespace OrdinaryMaskExamples
open Categorification KLR KLRAlgebra Stendhal Stendhal.FirstWeight LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

private abbrev hd : Dom LieLean.QuantumGroup.sl2RootDatum :=
  ⟨2 • AddMonoidHom.id ℤ, fun _ => by simp [LieLean.QuantumGroup.sl2RootDatum]⟩
private def weights : Fin 2 → Dom LieLean.QuantumGroup.sl2RootDatum := fun _ => hd
private abbrev word : TensorWord Unit 2 := ((TensorWord.empty.red.black () 1).red).black () 2

example := barOrdinaryWord_eq_sum_masks weights word

private abbrev pre := ([Sum.inr (0 : Fin 2),.inl ()] : List (Unit ⊕ Fin 2))
private abbrev suf := ([Sum.inl (),.inl ()] : List (Unit ⊕ Fin 2))
private abbrev lastR := (Sum.inr (1 : Fin 2) : Unit ⊕ Fin 2)
private abbrev α : Multiset (Unit ⊕ Fin 2) := ↑(pre ++ [(Sum.inl () : Unit ⊕ Fin 2)] : List _)
private abbrev β := (({lastR} : Multiset _) + {Sum.inl ()})
private def output : Seq (α+β) := Seq.ofList (pre ++ lastR :: suf) (by decide)
private theorem output_eq : List.ofFn output.1 = pre ++ lastR :: suf := by decide
example := sum_lastRedShuffleMasks output pre lastR suf output_eq (by simp [pre,lastR]) (by simp [suf,lastR]) (fun _ => (1:ℤ))
example := ordinaryShuffleEquiv word output (by exact output_eq)
private def firstBit (j : Fin (lastRedWord word).2.length) := decide (j.val = 0)
private def secondBit (j : Fin (lastRedWord word).2.length) := decide (j.val = 1)
/-- Two equal suffix letters give two distinct permutations in the same pair of contents. -/
example : fitsLastRedContents (α := α) (β := β) word firstBit := by
  simp [fitsLastRedContents, word, lastRedBlackTags, lastRedWord, tagMask, maskSubword,
    firstBit, TensorWord.blocks, expandDiv, List.ofFn_succ, α, β, pre, lastR,
    addRedColor, Fin.last, Fin.castSucc]
  rfl
example : fitsLastRedContents (α := α) (β := β) word secondBit := by
  simp [fitsLastRedContents, word, lastRedBlackTags, lastRedWord, tagMask, maskSubword,
    secondBit, TensorWord.blocks, expandDiv, List.ofFn_succ, α, β, pre, lastR,
    addRedColor, Fin.last, Fin.castSucc]
  rfl
example : firstBit ≠ secondBit := fun h => Bool.noConfusion (congrFun h ⟨0,by simp [lastRedWord,word]⟩)
end OrdinaryMaskExamples

namespace ProjectiveCommutatorExamples

open Categorification.Graded Stendhal Stendhal.FirstWeight

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev C := CyclotomicDividedWords.C₂
private abbrev param := CyclotomicDividedWords.admissible
private abbrev labels : Fin 1 → (Fin 2 →₀ ℕ) := fun _ =>
  Finsupp.single 0 2 + Finsupp.single 1 1

private theorem beforeSecond : blackBlockPairing C labels 0 {0} = 0 := by
  simp [blackBlockPairing, labels, A, C, CyclotomicDividedWords.C₂]

private theorem afterSecond : blackBlockPairing C labels 0 {0, 0} = -2 := by
  simp [blackBlockPairing, labels, A, C, CyclotomicDividedWords.C₂]

private abbrev twoLabels : Fin 2 → (Fin 2 →₀ ℕ) := fun _ => labels 0
private def redInterval : RedRun labels twoLabels := .snoc twoLabels .nil

private theorem afterRedInterval : blackBlockPairing C twoLabels 0 0 = 4 := by
  simp [blackBlockPairing, twoLabels, labels]

/-- The intervening red strand raises the pairing from two to four before the
black crossing. All four shifted summands include the final black strand. -/
private abbrev fourCopies := oneUpward_swap_of_nonneg C param 0 0 (GProj.regular _) redInterval
  (.black .nil 1) (by rw [afterRedInterval]; decide)

example := rightTwistWordDecomposition
  (tensorReflection _ (by rintro (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;> rfl)) fourCopies

example := oneUpward_swap_of_nonneg C param 0 {0} (GProj.regular _) (RedRun.nil : RedRun labels labels)
  .nil (by rw [beforeSecond])
example := oneUpward_swap_of_nonpos C param 0 {0, 0} (GProj.regular _) (RedRun.nil : RedRun labels labels)
  .nil (by rw [afterSecond]; decide)
example := oneUpward_swap_ne C param 0 1 (by decide) {0} (GProj.regular _) redInterval
  (.black .nil 0)

/-- The up colour is absent in the empty prefix, on both sides of a different-colour crossing. -/
example := oneUpward_swap_ne C param 0 1 (by decide) 0 (GProj.regular _)
  (RedRun.nil : RedRun labels labels) .nil

end ProjectiveCommutatorExamples

namespace DoubleStendhalBoundaries

open Categorification Categorification.Stendhal Categorification.QuantumGroup.UDot

private def signedBoundary : DoubleBoundary Unit 1 where
  word := [.inl (true, ()), .inr 0, .inl (false, ())]
  redOrder := by decide

private def redWeights :
    Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨3, by intro i; cases i; decide⟩

example : DoubleStendhalTriple sl2RootDatum redWeights 0 3 :=
  ⟨signedBoundary, by decide⟩

example : signedBoundary.word.scanl
    (fun x s => x + DoubleStrand.weight sl2RootDatum (fun r => (redWeights r).1) s) 0 =
    [0, 2, 5, 3] := by decide

example : signedBoundary.IsViolated := ⟨(true, ()), rfl⟩

example : ¬signedBoundary.AllDown := by
  intro h
  exact h () (by simp [signedBoundary])

private def downwardBoundary : DoubleBoundary Unit 1 where
  word := [.inr 0, .inl (false, ())]
  redOrder := by decide

private theorem downwardContent : downwardBoundary.blackContent = ({()} : Multiset Unit) :=
  by decide

private theorem downwardAll : downwardBoundary.AllDown := by
  intro i hi
  cases i
  simp [downwardBoundary] at hi

example :
    ((DoubleBoundary.allDownEquiv ({()} : Multiset Unit))
      ⟨downwardBoundary.toSeq downwardContent,
        downwardBoundary.isRedOrdered_toSeq downwardContent⟩).1.word =
      [.inr 0, .inl (false, ())] := by
  change (List.ofFn (downwardBoundary.toSeq downwardContent).lbl).map DoubleStrand.down = _
  rw [DoubleBoundary.list_toSeq]
  rfl

example : List.ofFn (((DoubleBoundary.allDownEquiv ({()} : Multiset Unit)).symm
    ⟨downwardBoundary, downwardAll, downwardContent⟩).1.lbl) = [.inr 0, .inl ()] := by
  change List.ofFn (downwardBoundary.toSeq downwardContent).lbl = _
  rw [DoubleBoundary.list_toSeq]
  rfl

example : ¬downwardBoundary.IsViolated := by
  rintro ⟨s, hs⟩
  simp [downwardBoundary] at hs

private def redOnly : DoubleStendhalTriple sl2RootDatum redWeights 0 3 :=
  ⟨⟨[.inr 0], by decide⟩, by decide⟩

example := DoubleDiagram.existsUnique_triple_at_cut sl2RootDatum redWeights redOnly
  (DoubleDiagram.moveDiagram sl2RootDatum (fun r => (redWeights r).val) 0 []
    (.black (.cup (true, ()))) [.inr 0])

private abbrev twoReds : Fin 2 → ℤ := fun _ => 1
private def diagrams : StringDiagrams.Presentation.{0, 0}
    (DoubleDiagram.signature sl2RootDatum twoReds) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

example := DoubleDiagram.redUpCrossingIso sl2RootDatum twoReds diagrams 0
  [.inr 0, .inl (false, ())] 1 () [.inl (false, ())]

open CategoryTheory StringDiagrams

private def bubblePresentation :
    Presentation.{0, 0} (DoubleDiagram.signature sl2RootDatum (fun r => (redWeights r).val)) ℚ where
  Rel := Empty
  dom e := e.elim
  cod e := e.elim
  rel e := e.elim

section AllDownGenerators

open DoubleDiagram
open scoped Classical

local notation "content" => ({(), ()} : Multiset Unit)

private def redTwoBlack : DoubleBoundary Unit 1 where
  word := [.inr 0, .inl (false, ()), .inl (false, ())]
  redOrder := rfl

private theorem redTwoBlackContent : redTwoBlack.blackContent = content := by decide

private def orderedRedTwoBlack : {s : KLR.Seq (stendhalWeight 1 content) // IsRedOrdered s} :=
  ⟨redTwoBlack.toSeq redTwoBlackContent, redTwoBlack.isRedOrdered_toSeq redTwoBlackContent⟩

private abbrev secondPos : Fin (stendhalWeight 1 content).card := ⟨1, by decide⟩
private abbrev thirdPos : Fin (stendhalWeight 1 content).card := ⟨2, by decide⟩

private theorem secondBlack : orderedRedTwoBlack.val.lbl secondPos = .inl () := by decide
private theorem thirdBlack : orderedRedTwoBlack.val.lbl thirdPos = .inl () := by decide

example : ¬ IsViolated orderedRedTwoBlack.val := by
  rintro ⟨h, hv⟩
  exact Bool.noConfusion hv

example : downE bubblePresentation orderedRedTwoBlack.val orderedRedTwoBlack orderedRedTwoBlack =
    𝟙 _ := by
  simpa only [KLR.Diagram.MatEnd.single_apply_self] using
    congrFun (congrFun (downE_of_ordered bubblePresentation orderedRedTwoBlack)
      orderedRedTwoBlack) orderedRedTwoBlack

example : downX bubblePresentation secondPos orderedRedTwoBlack orderedRedTwoBlack =
    downBlackDot bubblePresentation orderedRedTwoBlack secondPos () secondBlack :=
  (downX_apply_self bubblePresentation secondPos orderedRedTwoBlack).trans
    (downDot_of_black bubblePresentation orderedRedTwoBlack secondPos () secondBlack)

private theorem blackSwap : orderedRedTwoBlack.val =
    TypeA.sadj (stendhalWeight 1 content).card 1 • orderedRedTwoBlack.val :=
  (KLR.Diagram.sadj_smul_eq_self orderedRedTwoBlack.val (by decide)
    (secondBlack.trans thirdBlack.symm)).symm

example : downΨ bubblePresentation 1 orderedRedTwoBlack orderedRedTwoBlack =
    downCrossLayer bubblePresentation orderedRedTwoBlack orderedRedTwoBlack 1 (by decide) blackSwap
      (.black (.cross false () ())) (by rw [secondBlack, thirdBlack]; rfl) :=
  downCross_of_move bubblePresentation orderedRedTwoBlack orderedRedTwoBlack 1 (by decide)
    blackSwap (.black (.cross false () ())) (by rw [secondBlack, thirdBlack]; rfl)

private abbrev blackQ : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev redExponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 3

example := ordinaryToDownwardMatrix_e bubblePresentation blackQ redExponents (fun _ _ => 1)
  orderedRedTwoBlack.val

example := ordinaryToDownwardMatrix_x bubblePresentation blackQ redExponents (fun _ _ => 1)
  (ν := content) secondPos

example := ordinaryToDownwardMatrix_ψ bubblePresentation blackQ redExponents (fun _ _ => 1)
  (ν := content) 1

example := ordinaryToDownwardMatrix_ofWeights bubblePresentation blackQ (fun _ _ => 1) (ν := content)

example := boundaryRightModuleDownEquiv bubblePresentation content orderedRedTwoBlack

end AllDownGenerators

example : (DoubleDiagram.violatingFunctor bubblePresentation 3).map
    (DoubleDiagram.leftCup bubblePresentation redOnly (true, ()) ≫
      DoubleDiagram.leftCap bubblePresentation redOnly (true, ())) = 0 :=
  DoubleDiagram.map_leftBubble_zero bubblePresentation redOnly (true, ())

example :
    LinearMap.ker ((DoubleDiagram.violatingFunctor bubblePresentation 3).mapLinearMap ℚ
      (X := redOnly) (Y := redOnly)) =
      DoubleViolatingQuotient.ideal ℚ (DoubleDiagram.tripleObj bubblePresentation) redOnly redOnly :=
  DoubleViolatingQuotient.ker_mapLinearMap ℚ (DoubleDiagram.tripleObj bubblePresentation)
    redOnly redOnly

private def redDownUp : DoubleStendhalTriple sl2RootDatum redWeights 0 3 :=
  ⟨⟨[.inr 0, .inl (false, ()), .inl (true, ())], rfl⟩, by decide⟩

/-- The red strand has weight three before the mixed black pair, so the
positive-weight cup/cap terms occur. The boundary itself starts with red. -/
example : ¬redDownUp.val.IsViolated ∧
    (let mixed := DoubleDiagram.addMixedBlackRelations sl2RootDatum (fun r => (redWeights r).val) ℚ
           (fun _ _ => 1) bubblePresentation
     let π := DoubleDiagram.violatingFunctor
           (DoubleDiagram.addRedUpRelations sl2RootDatum (fun r => (redWeights r).val) ℚ mixed) 3
     𝟙 (π.obj redDownUp) ∈ DoubleDiagram.factorSpan ℚ π.obj (fun d => d.val.AllDown) redDownUp redDownUp) := by
  refine ⟨?_, DoubleDiagram.id_mem_allDownFactorSpan bubblePresentation (fun _ _ => 1) redDownUp⟩
  rintro ⟨s, hs⟩
  simp [redDownUp] at hs

end DoubleStendhalBoundaries


namespace DoubleCategoricalFactorExample
open Categorification Categorification.Stendhal Categorification.QuantumGroup.UDot CategoryTheory

private abbrev noReds : Fin 0 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  Fin.elim0
private abbrev weight := fun r => (noReds r).val
private def pres : StringDiagrams.Presentation.{0,0} (DoubleDiagram.signature sl2RootDatum weight) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev rels := DoubleDiagram.addRedUpRelations sl2RootDatum weight ℚ pres
private abbrev project := DoubleDiagram.violatingFunctor (Λ := noReds) rels 0
private def downUp : DoubleStendhalTriple sl2RootDatum noReds 0 0 :=
  ⟨⟨[.inl (false, ()), .inl (true, ())], rfl⟩, by decide⟩

/-- In the empty red family for sl₂, every down/up pair, including in the empty
context, is cut at a violated boundary. The example uses the mixed pair of total weight zero. -/
example : 𝟙 (project.obj downUp) ∈
    DoubleDiagram.factorSpan ℚ project.obj (fun d => d.val.AllDown) downUp downUp := by
  apply DoubleDiagram.id_mem_allDownFactorSpan_of_mixed pres
  intro L R i j b hb
  have hviol : b.val.IsViolated := by
    cases L with
    | nil => exact ⟨(false, j), by simp [hb]⟩
    | cons a L =>
      cases a with
      | inl s => exact ⟨s, by simp [hb]⟩
      | inr r => exact Fin.elim0 r
  have hzero : 𝟙 (project.obj b) = 0 :=
    DoubleViolatingQuotient.id_eq_zero ℚ (DoubleDiagram.tripleObj rels) (x := b) hviol
  rw [hzero]
  exact Submodule.zero_mem _

end DoubleCategoricalFactorExample

namespace DoubleStendhalVacuum

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams

private def noReds : Fin 0 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  Fin.elim0

private def sl2VacuumPresentation : Presentation (signature sl2RootDatum (Subtype.val ∘ noReds)) ℚ where
  Rel := Empty
  dom := Empty.elim
  cod := Empty.elim
  rel i := nomatch i

example : Function.Surjective (algebraMap ℚ (End (vacuumObj sl2VacuumPresentation))) :=
  vacuum_algebraMap_surjective sl2VacuumPresentation

private abbrev relations :=
  addRedUpRelations sl2RootDatum (Subtype.val ∘ noReds) ℚ
    (addMixedBlackRelations sl2RootDatum (Subtype.val ∘ noReds) ℚ (fun _ _ => 1)
      sl2VacuumPresentation)

example : (allDownCompletionInclusion relations (right := (0 : ℤ))).IsEquivalence :=
  allDownCompletionInclusion_isEquivalence_addRelations sl2VacuumPresentation (fun _ _ => 1)

end DoubleStendhalVacuum

namespace MixedBlackExample

open Categorification Categorification.Stendhal Categorification.QuantumGroup StringDiagrams

private abbrev weight : Fin 1 → ℤ := fun _ => 1
private def diagrams : Presentation.{0, 0} (DoubleDiagram.signature UDot.sl2RootDatum weight) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
example := DoubleDiagram.mixedBlack_eq UDot.sl2RootDatum weight (fun _ _ => 1) diagrams
  0 [.inr 0] [] ()
example : (KL3.Diagram.ip UDot.sl2RootDatum ()
    (DoubleDiagram.endWeight UDot.sl2RootDatum weight 0 [.inr 0])).toNat = 1 := by decide
private abbrev weightA₂ : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def diagramsA₂ : Presentation.{0, 0} (DoubleDiagram.signature (Flag.slRootDatum 2) weightA₂) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
example := DoubleDiagram.mixedBlack_ne (Flag.slRootDatum 2) weightA₂
  (fun i j => if i = j then 1 else -1) diagramsA₂ 0 [.inr 0] [] 0 1 (by decide)

example := DoubleDiagram.printedBubble_no_injection_sl2 diagrams

end MixedBlackExample

open Categorification Categorification.QuantumGroup Categorification.KL3.Diagram
namespace DoubleBlackScalarCheck
private abbrev cartan := CartanDatum.ofGraph (⊥ : SimpleGraph Bool)
private noncomputable def two : ℚˣ := Units.mk0 2 (by norm_num)
private noncomputable def params : CL.CLScalars cartan ℚ where
  t i j := if i = j then 1 else two
  r _ := 1
  s _ _ _ _ := 0
  t_self _ := by simp
  t_symm _ _ _ := by simp [eq_comm]
  s_symm _ _ _ _ := rfl
private theorem orthogonal : cartan.dot false true = 0 :=
  CartanDatum.ofGraph_dot_of_not_adj _ (by decide) (by simp)
private theorem webster_square : CL.qCL params false true = MvPolynomial.C 2 := by
  rw [CL.qCL_of_dot_eq_zero params orthogonal]
  rfl
private theorem cl_down_square : CL.qCL params.dual false true = MvPolynomial.C (1/2) := by
  rw [CL.qCL_of_dot_eq_zero params.dual orthogonal]
  congr 1
  norm_num [CL.CLScalars.dual, params, two]
example : CL.qCL params.dual false true ≠ CL.qCL params false true := by
  rw [webster_square, cl_down_square, Ne, MvPolynomial.C_inj]
  norm_num
end DoubleBlackScalarCheck

namespace DoubleVacuumCharacterExample

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams

private def noReds : Fin 0 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  Fin.elim0

private def base : Presentation (signature sl2RootDatum (Subtype.val ∘ noReds)) ℚ where
  Rel := Empty
  dom := Empty.elim
  cod := Empty.elim
  rel i := nomatch i

private instance : IsEmpty base.Rel := inferInstanceAs (IsEmpty Empty)

private abbrev Q := fun _ _ : Unit ⊕ Fin 0 => (0 : MvPolynomial (Fin 2) ℚ)

private abbrev signed := addRedUpRelations sl2RootDatum (Subtype.val ∘ noReds) ℚ
  (addMixedBlackRelations sl2RootDatum (Subtype.val ∘ noReds) ℚ (fun _ _ => 1)
    (addDownRelations sl2RootDatum (Subtype.val ∘ noReds) Q base))

example : Function.Bijective (algebraMap ℚ (End (vacuumObj signed))) :=
  vacuum_algebraMap_bijective base (fun _ _ => 1) Q

example : algebraMap ℚ (End (vacuumObj signed)) 2 ≠ algebraMap ℚ (End (vacuumObj signed)) 3 :=
  (vacuum_algebraMap_bijective base (fun _ _ => 1) Q).injective.ne (by norm_num)


end DoubleVacuumCharacterExample

namespace DoubleContentExample
open Categorification Categorification.Stendhal Categorification.QuantumGroup.UDot CategoryTheory

private def reds : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨3, by intro i; cases i; decide⟩
private abbrev labels := fun r => (reds r).val
private def P : StringDiagrams.Presentation.{0,0} (DoubleDiagram.signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev mixed := DoubleDiagram.addMixedBlackRelations sl2RootDatum labels ℚ (fun _ _ => 1) P
private abbrev project :=
  DoubleDiagram.violatingFunctor (Λ := reds) (DoubleDiagram.addRedUpRelations sl2RootDatum labels ℚ mixed) 1
private def threeBlack : DoubleStendhalTriple sl2RootDatum reds 0 1 :=
  ⟨⟨[.inr 0, .inl (false, ()), .inl (true, ()), .inl (false, ())], rfl⟩, by decide⟩

/-- Two downward strands and one upward strand of the same colour factor through
all-down words with exactly one black strand. -/
example : threeBlack.val.blackContent.card = 3 ∧ 𝟙 (project.obj threeBlack) ∈
    DoubleDiagram.factorSpan ℚ project.obj (fun d => d.val.AllDown ∧ d.val.blackContent = {()})
      threeBlack threeBlack := by
  refine ⟨by decide, DoubleDiagram.id_mem_allDownContentFactorSpan P (fun _ _ => 1) threeBlack {()} ?_⟩
  let s := Finsupp.single () (1 : ℤ)
  change 0 + (s + (-s + (s + 0))) = contentVector {()}
  simp [s, contentVector]

end DoubleContentExample

namespace CyclotomicRedPullbackExample
open Categorification Categorification.Stendhal Polynomial
private abbrev q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev lowerPolynomial : Unit → Polynomial ℚ := fun _ => X
private abbrev upperPolynomial : Unit → Polynomial ℚ := fun _ => X ^ 2
private theorem divisibility (i : Unit) : lowerPolynomial i ∣ upperPolynomial i := ⟨X, by simp [lowerPolynomial, upperPolynomial, pow_two]⟩
example := cyclotomicRedPullbackResIso.{0,0,0} q divisibility () (β := 0) rfl
example := cyclotomicRedProjection_surjective q divisibility {()}
end CyclotomicRedPullbackExample

namespace DoubleEmptyCornerExample
open CategoryTheory StringDiagrams Categorification Categorification.Stendhal.DoubleDiagram Categorification.QuantumGroup.UDot
private def noRedWeights : Fin 0 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  Fin.elim0

private def freeEmptyPresentation : Presentation.{0, 0}
    (signature sl2RootDatum (Subtype.val ∘ noRedWeights)) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

private instance : IsEmpty freeEmptyPresentation.Rel := inferInstanceAs (IsEmpty Empty)

example : Function.Bijective
    (ordinaryToDownwardMatrix freeEmptyPresentation (fun _ _ => 0) Fin.elim0
      (fun _ _ => 1) (ν := (0 : Multiset Unit))) :=
  ordinaryToDownwardMatrix_bijective_empty_red freeEmptyPresentation _ _ _ 0

example : Function.Bijective
    (ordinaryToDownwardMatrix freeEmptyPresentation (fun _ _ => 0) Fin.elim0
      (fun _ _ => 1) (ν := ({()} : Multiset Unit))) :=
  ordinaryToDownwardMatrix_bijective_empty_red freeEmptyPresentation _ _ _ {()}
end DoubleEmptyCornerExample

namespace DoubleStendhalBubbles

open Categorification Categorification.QuantumGroup.UDot Categorification.KL3.Diagram
  Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams

private def redWeight : Fin 1 → ℤ := fun _ => 2

private def base : Presentation (signature sl2RootDatum redWeight) ℚ where
  Rel := Empty
  dom := Empty.elim
  cod := Empty.elim
  rel i := nomatch i

private abbrev bubbles := addBubbleRelations sl2RootDatum redWeight ℚ base
private abbrev placed := blackMorphism sl2RootDatum redWeight bubbles

example : placed 0 [.inr 0] [] (LinDiagram.of (cwReal sl2RootDatum 2 () 0)) = 0 :=
  realBubble_eq_of_le sl2RootDatum redWeight base 0 [.inr 0] [] .counterclockwise () 0 (by decide)

example : placed 0 [.inr 0] [] (LinDiagram.of (cwReal sl2RootDatum 2 () 1)) = 𝟙 _ :=
  realBubble_eq_of_le sl2RootDatum redWeight base 0 [.inr 0] [] .counterclockwise () 1 (by decide)

example : placed (-4) [.inr 0] [] (LinDiagram.of
    (ccwReal sl2RootDatum (endWeight sl2RootDatum redWeight (-4) [.inr 0]) () 1)) = 𝟙 _ :=
  realBubble_eq_of_le sl2RootDatum redWeight base (-4) [.inr 0] [] .clockwise () 1 (by decide)

example : placed 0 [.inr 0] [] (ccwL sl2RootDatum ℚ 2 () (-3)) = 𝟙 _ :=
  bubble_eq_of_le sl2RootDatum redWeight base 0 [.inr 0] [] .clockwise () (-3) (by decide)

example : placed 0 [.inr 0] [] (ccwL sl2RootDatum ℚ 2 () (-4)) = 0 :=
  bubble_eq_of_le sl2RootDatum redWeight base 0 [.inr 0] [] .clockwise () (-4) (by decide)

example :
    ∑ a ∈ Finset.range 2,
      placed 0 [.inr 0] [] (ccwL sl2RootDatum ℚ 2 () (-3 + a)) ≫
        placed 0 [.inr 0] [] (cwL sl2RootDatum ℚ 2 () (1 + (1 - (a : ℤ)))) = 0 :=
  bubbleGrassmannian sl2RootDatum redWeight base 0 [.inr 0] [] () 1

end DoubleStendhalBubbles

namespace DoubleRedCapAndDownLift

open CategoryTheory StringDiagrams
open Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open Categorification.QuantumGroup.UDot

private def weights : Fin 2 → ℤ := fun r => (r.val : ℤ) + 2

private def base : Presentation.{0, 0} (signature sl2RootDatum weights) ℚ where
  Rel := Empty
  dom e := e.elim
  cod e := e.elim
  rel e := e.elim

example :
    (addRedCapRelations sl2RootDatum weights base).diag
      (redCapLeft sl2RootDatum weights 0 [.inr 0] (false, ()) 1 []) =
    (addRedCapRelations sl2RootDatum weights base).diag
      (redCapRight sl2RootDatum weights 0 [.inr 0] (false, ()) 1 []) :=
  redCap_slide sl2RootDatum weights base 0 [.inr 0] (false, ()) 1 []

example :
    (addRedCapRelations sl2RootDatum weights base).diag
      (redCapLeft sl2RootDatum weights 0 [.inr 0] (true, ()) 1 []) =
    (addRedCapRelations sl2RootDatum weights base).diag
      (redCapRight sl2RootDatum weights 0 [.inr 0] (true, ()) 1 []) :=
  redCap_slide sl2RootDatum weights base 0 [.inr 0] (true, ()) 1 []

private def Q : Unit ⊕ Fin 2 → Unit ⊕ Fin 2 → MvPolynomial (Fin 2) ℚ :=
  stendhalQ (fun _ _ => 0) (fun r => Finsupp.single () (r.val + 2))

private def bottom : Obj (KLR.Diagram.sig (Unit ⊕ Fin 2)) :=
  KLR.Diagram.ob [.inr 0, .inr 1, .inl ()]

private def top : Obj (KLR.Diagram.sig (Unit ⊕ Fin 2)) :=
  KLR.Diagram.ob [.inr 0, .inl (), .inr 1]

private def crossing :
    downContextObj sl2RootDatum weights 0 [] [] bottom ⟶
    downContextObj sl2RootDatum weights 0 [] [] top :=
  moveDiagram sl2RootDatum weights 0 [.inr 0] (.redBlack 1 (false, ())) []

example : ∃ f : (KLR.Diagram.pres ℚ Q).obj bottom ⟶ (KLR.Diagram.pres ℚ Q).obj top,
    (downPresentedFunctor sl2RootDatum weights Q base 0 [] []).map f =
      (addDownRelations sl2RootDatum weights Q base).diag crossing := by
  apply exists_downPresentedLift sl2RootDatum weights ℚ 0 Q base crossing
  intro L hL
  change L ∈ [layer sl2RootDatum weights 0 [.inr 0] (.redBlack 1 (false, ())) []] at hL
  obtain rfl := List.mem_singleton.mp hL
  exact ⟨.cross (.inr 1) (.inl ()), rfl⟩

end DoubleRedCapAndDownLift

namespace DoubleProjectiveExample
open scoped Classical
open Categorification Categorification.Stendhal Categorification.QuantumGroup.UDot CategoryTheory

private def reds : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨3, by intro i; cases i; decide⟩
private abbrev labels := fun r => (reds r).val
private def P : StringDiagrams.Presentation.{0,0} (DoubleDiagram.signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev mixed := DoubleDiagram.addMixedBlackRelations sl2RootDatum labels ℚ (fun _ _ => 1) P
private abbrev Q := DoubleDiagram.addRedUpRelations sl2RootDatum labels ℚ mixed
private abbrev ν : Multiset Unit := {()}
private def b : DoubleStendhalTriple sl2RootDatum reds 0 (DoubleDiagram.downRightWeight sl2RootDatum reds ν) :=
  ⟨⟨[.inr 0, .inl (false, ()), .inl (true, ()), .inl (false, ())], rfl⟩, by decide⟩

/-- The boundary has two downward and one upward black strands. Its module is finite
projective over the all-down matrix ring for precisely one black strand. -/
private theorem oneBlack : b.val.signedContent = contentVector ν := by
  let s := Finsupp.single () (1 : ℤ)
  change 0 + (s + (-s + (s + 0))) = contentVector {()}
  simp [s, contentVector]

example := DoubleDiagram.boundaryRightModule_finite_projective P ν (fun _ _ => 1) b oneBlack

end DoubleProjectiveExample

namespace CyclotomicRedCrossingExample
open Categorification Categorification.KLR Categorification.KLR.CyclotomicAction
  Categorification.Stendhal InductionAlong Polynomial CategoryTheory
private abbrev q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev a : Unit → Polynomial ℚ := fun _ => X
private abbrev b : Unit → Polynomial ℚ := fun _ => X ^ 2
private theorem dvdX (i : Unit) : a i ∣ b i := ⟨X, by simp [a, b, pow_two]⟩
private abbrev regular := ModuleCat.of (CycKLR ℚ q a 0) (CycKLR ℚ q a 0)
private theorem edge : {()} + (0 : Multiset Unit) = {()} := by simp

example : Function.Surjective ((cyclotomicRedDownQuotient q dvdX () edge).app regular) :=
  cyclotomicRedDownQuotient_surjective q dvdX () edge regular

example (z : Corner (lastEmb q b () edge)) :
    ((cyclotomicRedDownQuotient q dvdX () edge).app regular)
      (Ind.tmul (N := (cyclotomicRedPullback q dvdX 0).obj regular) z
        (1 : CycKLR ℚ q a 0)) =
    Ind.tmul (N := regular) (cyclotomicRedCornerProjection q dvdX () edge z)
      (1 : CycKLR ℚ q a 0) :=
  cyclotomicRedDownQuotient_tmul q dvdX () edge regular z 1

example := cyclotomicRedDownQuotient_unit q dvdX () edge regular
example := cyclotomicRedDownQuotient_counit q dvdX () edge
  (ModuleCat.of (CycKLR ℚ q a {()}) (CycKLR ℚ q a {()}))

example := singletonRedProjection_dotCrossing q () (fun _ => 1) (fun _ => 1) 1
example := singletonRedDotCrossing_projection q () (fun _ => 1) (fun _ => 1) 1
end CyclotomicRedCrossingExample

namespace DoubleRedCup

open CategoryTheory StringDiagrams
open Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open Categorification.QuantumGroup.UDot

private def weights : Fin 2 → ℤ := fun r => (r.val : ℤ) + 2

private def base : Presentation.{0, 0} (signature sl2RootDatum weights) ℚ where
  Rel := Empty
  dom e := e.elim
  cod e := e.elim
  rel e := e.elim

private def exponents : Fin 2 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 2)

private def Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

private abbrev cupRelations := addRedCupRelations sl2RootDatum weights base

example := redCup_slide sl2RootDatum weights base 0 [.inr 0] (false, ()) 1 []
example := redCup_slide sl2RootDatum weights base 0 [.inr 0] (true, ()) 1 []

example := redDown_bigon_redLeft sl2RootDatum weights Q exponents cupRelations
  0 [.inr 0] 1 () [.inl (true, ())]

example := redDown_bigon_blackLeft sl2RootDatum weights Q exponents cupRelations
  0 [.inr 0] 1 () [.inl (true, ())]

example := redDown_dot_slide_redLeft sl2RootDatum weights Q exponents cupRelations
  0 [.inr 0] 1 () []

example := redDown_dot_slide_blackLeft sl2RootDatum weights Q exponents cupRelations
  0 [.inr 0] 1 () []

end DoubleRedCup

namespace DoubleRedBubble

open Categorification Categorification.QuantumGroup.UDot Categorification.Stendhal
  Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams

private abbrev Λ : Fin 1 → ℤ := fun _ => 2

private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

private def Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

private def base : Presentation (signature sl2RootDatum Λ) ℚ where
  Rel := Empty
  dom := Empty.elim
  cod := Empty.elim
  rel i := nomatch i

private abbrev pres :=
  addDownRelations sl2RootDatum Λ (affineCoverQ Q exponents)
    (addRedUpRelations sl2RootDatum Λ ℚ
      (addRedCapRelations sl2RootDatum Λ (addRedCupRelations sl2RootDatum Λ base)))

example :
    pres.diag (ccwBubbleBeforeRed sl2RootDatum Λ (-1) [] () 0 [] 1) =
      pres.diag (ccwBubbleAfterRed sl2RootDatum Λ (-1) [] () 0 [] 3) := by
  have h := ccwBubble_slide sl2RootDatum Λ (-1) [] () 0 [] Q exponents base 1
  have e : 1 + exponents 0 () = 3 := by norm_num [exponents]
  rw [e] at h
  exact h

end DoubleRedBubble

namespace RedPairingExample

open Categorification KLR KLRAlgebra Stendhal Polynomial QuantumGroup.UDot

private abbrev q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev small : Unit → Polynomial ℚ := fun _ => X ^ 3
private abbrev large : Unit → Polynomial ℚ := fun _ => X ^ 5
private theorem hab (j : Unit) : small j ∣ large j := ⟨X ^ 2, by ring⟩
private theorem hs : KLRSymm q := by intro i j; simp [q]
private theorem hQ : ∀ j l : Unit, j ≠ l → ∃ c : ℚ, IsUnit c ∧
    (polyInY (q j l)).leadingCoeff = C c := fun j l h => (h (Subsingleton.elim j l)).elim

example := singletonRedCrossing_trace q () (fun _ => 3) (fun _ => 2) 1 1
example := redProjection_positive_polynomial q () hab 2 (by ring) hs hQ
  (fun _ => monic_X_pow _) (fun _ => monic_X_pow _) 0 sl2RootDatum 3 5
  (by norm_num [small, sl2RootDatum]) (by norm_num [large, sl2RootDatum])
  (fun j h => (h (Subsingleton.elim _ _)).elim) (by decide) (by decide) 1

end RedPairingExample

namespace CyclotomicRedDotCrossingExample
open Categorification Categorification.KLR Categorification.KLR.CyclotomicAction
  Categorification.Stendhal InductionAlong Polynomial CategoryTheory

private abbrev q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev a : Unit → Polynomial ℚ := fun _ => X ^ 2
private abbrev b : Unit → Polynomial ℚ := fun _ => X ^ 3
private theorem dvdX (j : Unit) : a j ∣ b j := ⟨X, by simp [a, b, pow_succ]⟩
private theorem hi : b () = X ^ 1 * a () := by simp [a, b, pow_succ']
private abbrev β : Multiset Unit := {()}
private abbrev γ : Multiset Unit := {()} + β
private abbrev M := ModuleCat.of (CycKLR ℚ q a β) (CycKLR ℚ q a β)

example := cyclotomicRedDotCrossing.{0,0,0} q dvdX () (β := β) rfl 1 hi

example (z : Corner (lastEmb q b () (β := β) rfl)) :
    (cyclotomicRedDotCrossing q dvdX () (β := β) rfl 1 hi).app M
        (Ind.tmul (N := M) (cyclotomicRedCornerProjection q dvdX () rfl z) (1 : CycKLR ℚ q a β)) =
      Ind.tmul (N := (cyclotomicRedPullback q dvdX β).obj M)
        ((z.val * dotElt q b () (β := β) rfl ^ 1) • unitGen (lastEmb q b () (β := β) rfl))
        (1 : CycKLR ℚ q a β) :=
  cyclotomicRedDotCrossing_tmul q dvdX () rfl 1 hi M z 1

example := cyclotomicRedDotCrossing_downQuotient.{0,0,0} q dvdX () (β := β) rfl 1 hi
example := cyclotomicRedDownQuotient_dotCrossing.{0,0,0} q dvdX () (β := β) rfl 1 hi
example := cyclotomicRedDotCrossing_downQuotient.{0,0,0} q dvdX () (β := 0) rfl 1 hi

end CyclotomicRedDotCrossingExample

namespace TwoRedCornerPolynomials

open Categorification Categorification.KLR Categorification.Stendhal
  Categorification.QuantumGroup LieLean.QuantumGroup LaurentPolynomial

private abbrev C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev fundamental : Unit →₀ ℕ := Finsupp.single () 1
private abbrev Strand := Unit ⊕ (Unit →₀ ℕ)
private abbrev red : Strand := Sum.inr fundamental
private abbrev black : Strand := Sum.inl ()

private theorem twoReds : cornerPolynomial C [red, red] [red, red] = 1 := by
  change cornerPolynomial C ([red] ++ [.inr fundamental]) ([red] ++ [.inr fundamental]) = 1
  rw [cornerPolynomial_terminalRed]
  change cornerPolynomial C ([] ++ [.inr fundamental]) ([] ++ [.inr fundamental]) = 1
  rw [cornerPolynomial_terminalRed, cornerPolynomial_empty]

private abbrev deletionTerm (x : List Strand × Strand × List Strand) : LaurentPolynomial ℤ :=
  if black = x.2.1 then
    cornerDeletionCoeff C () [red, red] x.1 *
      cornerPolynomial C [red, red] (x.1 ++ x.2.2) else 0

private theorem terminalBlack_expand (w : List Strand) :
    cornerPolynomial C [red, red, black] w = ((CycKLR.markedWords w).map deletionTerm).sum := by
  change cornerPolynomial C ([red, red] ++ [.inl ()]) w = _
  rw [cornerPolynomial_terminalBlack, List.attach_map_val (f := deletionTerm)]

private theorem oneRedPair : cornerPrefixPair C () [red] = 1 := by
  simp [cornerPrefixPair, red, fundamental]

private theorem twoRedsPair : cornerPrefixPair C () [red, red] = 2 := by
  norm_num [cornerPrefixPair, red, fundamental]

/-- Both red strands precede the black strand at each endpoint. -/
example : cornerPolynomial C [red, red, black] [red, red, black] = 1 + T 2 := by
  rw [terminalBlack_expand]
  simp [CycKLR.markedWords, deletionTerm, twoReds, black, red]
  simp only [cornerDeletionCoeff, twoRedsPair]
  have hd : UDot.di C () = 1 := rfl
  rw [hd]
  have h : qIntU qUnitLP 2 = T 1 + T (-1) := by
    change qNatU qUnitLP (1 + 1) = _
    rw [qNatU, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [qUnitLP]
  norm_num only [Int.reduceSub, zpow_one, mul_one]
  rw [h, mul_add, ← T_add, ← T_add]
  norm_num [add_comm]

/-- At the second endpoint the black strand is between the two red strands. -/
example : cornerPolynomial C [red, red, black] [red, black, red] = T 1 := by
  rw [terminalBlack_expand]
  simp [CycKLR.markedWords, deletionTerm, twoReds, black, red]
  simp only [cornerDeletionCoeff, twoRedsPair, oneRedPair]
  have hd : UDot.di C () = 1 := rfl
  rw [hd]
  norm_num [qIntU, qNatU]

end TwoRedCornerPolynomials

namespace CornerFieldComparison

open Categorification Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup

open FundamentalCorner
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
private abbrev cartan := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private theorem parameters (k : Type) [Field k] :
    IsRouquierQ cartan (fun _ _ => (0 : MvPolynomial (Fin 2) k)) := by
  constructor <;> intro i j h <;> exact (h (Subsingleton.elim i j)).elim
private theorem rational : IsRouquierQ cartan Q := by
  constructor <;> intro i j h <;> exact (h (Subsingleton.elim i j)).elim
private abbrev t := FirstWeight.boundaryAt () 2 1
private abbrev datum {k : Type} [Field k] {P : Unit → Unit → MvPolynomial (Fin 2) k}
    (h : IsRouquierQ cartan P) :=
  stendhalGradingDatum wt h.gradingDatum (fun i => cartan.dot i i / 2) (dotDegree cartan h)
private theorem rational_degree_two : Module.finrank ℚ (sequenceCornerGrade (datum rational) t.1 t.2.1 t.1 t.2.1 2) = 1 := by
  apply Int.ofNat_inj.mp
  have h : sequenceCornerPoly grading t.1 t.2.1 t.1 t.2.1 = 1 + LaurentPolynomial.T 2 := by
    rw [sequenceCornerPoly_eq_homGdimPoly]
    exact boundaryAt_last_homGdimPoly
  rw [← sequenceCornerPoly_coeff cartan rational wt t.1 t.2.1 t.1 t.2.1 2]
  change (sequenceCornerPoly grading t.1 t.2.1 t.1 t.2.1).coeff 2 = _
  rw [h]
  simp
  change (Finsupp.single (0 : ℤ) (1 : ℤ)) 2 = 0
  exact Finsupp.single_eq_of_ne (by decide)

/-- The terminal one-black corner for two fundamental reds has a degree-two
line over the field of two elements. -/
example : Module.finrank (ZMod 2) (sequenceCornerGrade (datum (parameters (ZMod 2)))
    t.1 t.2.1 t.1 t.2.1 2) = 1 :=
  (finrank_sequenceCornerGrade_eq_of_parameters cartan (parameters (ZMod 2)) rational
    wt t.1 t.2.1 t.1 t.2.1 2).trans rational_degree_two

example := sequenceCornerPoly_eq_wordCornerPoly cartan rational wt
  (FirstWeight.boundaryAt () 2 0).1 (FirstWeight.boundaryAt () 2 0).2.1 t.1 t.2.1

end CornerFieldComparison

namespace RedAbsentCapExample

open Categorification KLR KLRAlgebra Stendhal Polynomial QuantumGroup QuantumGroup.UDot
open KLRAlgebra.AbsentColour

private abbrev cartan := CartanDatum.ofGraph (⊥ : SimpleGraph Bool)
private def datum : WeightDatum cartan (Bool → ℤ) ((Bool → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A cartan i j
  iY i := {toFun := fun z => z i, map_zero' := rfl, map_add' := fun _ _ => rfl}
  pair_iY_iX _ _ := rfl

private abbrev Q (i j : Bool) : MvPolynomial (Fin 2) ℚ := if i = j then 0 else 1
private abbrev a (_ : Bool) : Polynomial ℚ := X
private abbrev b (i : Bool) : Polynomial ℚ := if i then X else X ^ 3
private theorem hab (j : Bool) : a j ∣ b j := by
  cases j
  · exact ⟨X ^ 2, by change X ^ 3 = (X * X ^ 2 : Polynomial ℚ); ring⟩
  · exact dvd_refl _
private theorem sym : KLRSymm Q := by intro i j h; simp [Q, h, h.symm]
private theorem unitCoeff (i j : Bool) (h : i ≠ j) :
    ∃ c : ℚ, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c := by
  exact ⟨1,isUnit_one,by simp [Q, h, polyInY]⟩
private theorem hdeg (j : Bool) (h : j ≠ false) :
    ((polyInY (Q j false)).natDegree : ℤ) = -datum.pair (datum.iY false) (datum.iX j) := by
  cases j
  · exact (h rfl).elim
  · simp [Q, polyInY]
    rfl
private abbrev β : Multiset Bool := {true}
private abbrev r : CycKLR ℚ Q b β := CycKLR.mk ℚ Q b β 1
private abbrev z : Corner Q false b β := cornerEval Q false β b (C r)
private theorem hb (j : Bool) : (b j).Monic := by cases j <;> first | exact monic_X | exact monic_X_pow _

/-- The old block contains a true strand. Raising the false strand from level
one to three inserts two dots into the trace on this nonempty corner. -/
example := redProjection_cyclotomicOppositeCap Q false β hab sym unitCoeff (fun _ => monic_X) hb datum
  (fun _ => 1) (fun _ => 3) (by norm_num [a, datum]) (by norm_num [b, datum]) hdeg
  2 (by change X ^ 3 = (X ^ 2 * X : Polynomial ℚ); ring) z

end RedAbsentCapExample

example := Categorification.Stendhal.TypeA1Cap.strict_lower_cap_ne_zero
example := Categorification.Stendhal.TypeA1Cap.strict_upper_projected_cap

namespace PrintedPitchforks


open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open DisconnectedCounterexample
open StringDiagrams
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "weights" => (Subtype.val ∘ redWeights)
local notation "S" => signature weightDatum weights

private def free : Presentation S ℚ :=
  ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun i => i.elim⟩

example : ¬ ∃ f : TensorProductAlgebra ℚ parameters exponents content →ₐ[ℚ]
    downwardMatrix (Λ := redWeights)
      (addPrintedPitchforkFragment (addBubbleRelations weightDatum weights ℚ free)) content,
    Function.Injective f :=
  printedPitchfork_no_injection (addBubbleRelations weightDatum weights ℚ free)

end PrintedPitchforks

namespace ProjectedCyclotomicCover

open Categorification KLR Stendhal KLRAlgebra CyclotomicAction InductionAlong
open FundamentalCorner

private abbrev C := QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

private theorem hQ : IsRouquierQ C Q :=
  ⟨fun _ _ h => (h (Subsingleton.elim _ _)).elim,
   fun _ _ h => (h (Subsingleton.elim _ _)).elim,
   fun _ _ h => (h (Subsingleton.elim _ _)).elim⟩

/-- The terminal black dot survives with two fundamental red strands and has
a nonzero operator in the extended-Cartan cover. -/
example := exists_projectedCoverVacuumEntry_ne_zero.{0,0,0} wt {()} C hQ _ dot_ne_zero

/-- The same dot is supported on at least one ordinary regular corner. -/
example := exists_regular_corner_ne_zero Q wt {()} dot_ne_zero

private abbrev oneWeight (_ : Fin 1) : Unit →₀ ℕ := Finsupp.single () 1
private abbrev red : Unit ⊕ Fin 1 := .inr 0
private abbrev black : Unit ⊕ Fin 1 := .inl ()

private def mixedSuffix : ColourDotContext red ({red} + 0) (stendhalWeight 1 (0 : Multiset Unit)) := by
  have t := ((ColourDotContext.nil (c := red) ({red} + 0)).ind black (by decide)).res (by decide)
  convert t
  decide

/-- A red dot disappears after subsequent black induction and restriction. -/
example (M : ModuleCat (CycKLR ℚ (cyclotomicCoverQ C oneWeight Q) cyclotomicCoverPolynomial 0)) :
    (functor (cyclotomicCoverToTensor (Q := Q) oneWeight 0 C).toRingHom.toNonUnitalRingHom).map
      ((mixedSuffix.eval _ _).map ((dot _ _ red (β := 0) rfl).app M)) = 0 :=
  cyclotomicCover_project_signedRedDot oneWeight 0 C hQ 0 rfl mixedSuffix M

private abbrev xs : List (DoubleStrand Unit 2) :=
  [.inr 1, .inl (false, ()), .inl (true, ()), .inr 0]

private def reversedWord : SignedCoverWord Unit 2 (stendhalWeight 2 0) xs := by
  have t := ((((SignedCoverWord.nil (I := Unit) (ℓ := 2)).ind (.inr 1)).ind (.inl ())).res ()).ind (.inr 0)
  convert t using 1 <;> decide

/-- Reversed reds bound zero projected modules with black induction and
restriction between them. -/
example (M : ModuleCat (CycKLR ℚ (cyclotomicCoverQ C wt Q) cyclotomicCoverPolynomial 0))
    (z : (functor (cyclotomicCoverToTensor (Q := Q) wt 0 C).toRingHom.toNonUnitalRingHom).obj
      (reversedWord.eval _ _ M)) : z = 0 :=
  cyclotomicCover_project_unorderedSignedWord wt 0 C hQ reversedWord (by decide) M z

end ProjectedCyclotomicCover

namespace DoubleRedTripleExamples
open CategoryTheory StringDiagrams Categorification Categorification.Stendhal
open Categorification.Stendhal.DoubleDiagram Categorification.QuantumGroup.UDot
private def weights : Fin 2 → ℤ := fun r => (r.val : ℤ) + 2
private def base : Presentation.{0, 0} (signature sl2RootDatum weights) ℚ where
  Rel := Empty
  dom e := e.elim
  cod e := e.elim
  rel e := e.elim

example :
    (addRedUpSlideRelations sl2RootDatum weights base).diag
      (redUpSlideMirror sl2RootDatum weights (-1) [.inr 0] 1 (.dot ()) [.inl (false, ())] false) =
    (addRedUpSlideRelations sl2RootDatum weights base).diag
      (redUpSlideMirror sl2RootDatum weights (-1) [.inr 0] 1 (.dot ()) [.inl (false, ())] true) :=
  redUp_slide_mirror sl2RootDatum weights base (-1) [.inr 0] 1 (.dot ()) [.inl (false, ())]

private abbrev slides := addRedUpRelations sl2RootDatum weights ℚ (addRedUpSlideRelations sl2RootDatum weights base)
example :
    slides.diag (middleRedViaLeft sl2RootDatum weights 0 [.inr 0] [] 1 () ()) =
    slides.diag (middleRedViaRight sl2RootDatum weights 0 [.inr 0] [] 1 () ()) :=
  middleRed_triplePoint sl2RootDatum weights 0 [.inr 0] [] 1 () () base
example := redUpWordIso sl2RootDatum weights base (-1) 1 [.inr 0] [(),(),()] [.inl (false, ())]
example := redUp_enclosed_move sl2RootDatum weights base 0 1 [.inr 0] (.cross () ()) []
example := (redUpWordNaturality sl2RootDatum weights base 0 1 [.inr 0] [.inl (false, ())]).app
  (KLR.Diagram.ob [(),(),()])
example := redThroughUpWord_move sl2RootDatum weights base 0 1 [.inr 0] [()] (.cross () ()) [(),()] []

example (f : base.obj (obj sl2RootDatum weights 0
    (([.inr 0,.inl (),.inr 1] : List (Unit ⊕ Fin 2)).map DoubleStrand.down)) ⟶
    base.obj (obj sl2RootDatum weights 0 [.inr 0,.inr 1])) : f = 0 :=
  hom_eq_zero_of_shorter_than_allDown sl2RootDatum weights base 0
    [.inr 0,.inl (),.inr 1] (by decide) f

end DoubleRedTripleExamples

namespace RedPrefixBubble
open Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
  Categorification.QuantumGroup.UDot StringDiagrams

private def reds : Fin 2 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, by decide +revert⟩
private abbrev labels := Subtype.val ∘ reds
private abbrev coeff : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private def base : Presentation (signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev vacuum : DoubleStendhalTriple sl2RootDatum reds 0 2 :=
  ⟨⟨[.inr 0, .inr 1], by decide⟩, by decide +kernel⟩

example := ccwBubble_afterRedPrefix_zero sl2RootDatum () (fun _ _ => (0 : MvPolynomial (Fin 2) ℚ))
  coeff reds base vacuum [0,1] [] rfl 0
example := cwBubble_afterRedPrefix_zero sl2RootDatum () (fun _ _ => (0 : MvPolynomial (Fin 2) ℚ))
  coeff reds base vacuum [0,1] [] rfl 0

end RedPrefixBubble


namespace DoubleBlackAdjunction

open Categorification Categorification.QuantumGroup.UDot Categorification.KL3.Diagram
  Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 1

private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

example := blackSnakeLeft_eq sl2RootDatum weights 0 [.inr 0] (false, ()) [] P
example := blackSnakeRight_eq sl2RootDatum weights 0 [.inr 0, .inl (false, ())] (true, ()) [] P
example := blackCup_dot_slide sl2RootDatum weights 0 [.inr 0] (false, ()) [] P
example := blackCap_dot_slide sl2RootDatum weights 0 [.inr 0, .inl (false, ())] (true, ()) [] P

end DoubleBlackAdjunction

namespace DoubleBlackCurls

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 1

private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

example := blackCurlLeft sl2RootDatum weights (fun _ _ => 1) P 0
  [.inr 0, .inl (false, ())] [] ()
example := blackCurlRight sl2RootDatum weights (fun _ _ => 1) P 0
  [.inr 0, .inl (false, ())] [] ()
example := mixedBlack_opposite_eq sl2RootDatum weights (fun _ _ => 1) P 0
  [.inr 0, .inl (false, ())] [] ()

private abbrev weightsA₂ : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def PA₂ : Presentation (signature (Flag.slRootDatum 2) weightsA₂) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

example := mixedBlack_opposite_ne (Flag.slRootDatum 2) weightsA₂
  (fun i j => if i = j then 1 else -1) PA₂ 0 [.inr 0] [] 0 1 (by decide)

end DoubleBlackCurls

namespace DoubleClockwiseRedBubble

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 1

private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩

private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

example := cwBubble_slide sl2RootDatum weights 0 [] () 0 [.inl (false, ())] Q exponents P 0
example := clockwiseBubble_slide sl2RootDatum weights 0 [] () 0 [.inl (false, ())] Q exponents P 2

end DoubleClockwiseRedBubble

namespace PitchforkCoefficient
open Categorification.Stendhal.DoubleDiagram

private abbrev A := ModuleCat.of ℚ ℚ

example : (2 : ℚ) * (1 / 2) = 1 := by
  let e := 𝟙 A
  have he : 𝟙 A ≠ 0 := by
    intro h
    have h' := congrArg (fun f : A ⟶ A => f.hom 1) h
    exact one_ne_zero (α := ℚ) h'
  apply pitchforkCoefficients_mul_eq_one (q := (2 : ℚ)) e e ((2 : ℚ) • e) e e ((2 : ℚ) • e) e e he
  · norm_num
  · simp [e, two_smul]
  · simp only [e, Category.comp_id, smul_smul]
    norm_num
  · simp [e]
  · simp [e]
  · simp [e, two_smul]
  · simp [e, two_smul]
example := disconnected_downward_quadratics

end PitchforkCoefficient


namespace DoubleRedBraidClosure

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 4
private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 4

example := closeRedBraid_sub sl2RootDatum weights (-2) [] () 0 [] Q exponents P

end DoubleRedBraidClosure

namespace DoubleRedBraidReduction

open CategoryTheory Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 4
private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 4

example := closeRedBraid_left_eq_zero_of_pos sl2RootDatum weights Q exponents P (-2) [] () 0 []
  (by decide)

example := closeRedBraid_right_eq_zero_of_neg sl2RootDatum weights Q exponents P (-2) [] () 0 []
  (by decide)

private abbrev B := addBlackKLRelations sl2RootDatum weights P
private abbrev U := addRedUpRelations sl2RootDatum weights ℚ
  (addRedCapRelations sl2RootDatum weights (addRedCupRelations sl2RootDatum weights B))
private abbrev C := KLR.Diagram.pres ℚ (affineCoverQ Q exponents)
private abbrev close := closeRedBraid sl2RootDatum weights (-2) [] () 0 [] Q exponents U
private abbrev d : Unit ⊕ Fin 1 := .inl ()
private abbrev r : Unit ⊕ Fin 1 := .inr 0

example :
    (∑ j ∈ Finset.range 4,
      close (End.of (C.diag (KLR.Diagram.E0 d r d)) ^ j *
        End.of (C.diag (KLR.Diagram.E2 d r d)) ^ (4 - 1 - j))) = 0 := by
  simpa only [exponents, Finsupp.single_eq_same] using
    closeRedBraid_correction_eq_zero sl2RootDatum weights Q exponents P (-2) [] () 0 []
      (by decide) (by decide)

end DoubleRedBraidReduction

namespace RedBraidCoefficients
open Categorification.Stendhal.DoubleDiagram

example (x y : ℚ) :
    (∑ a ∈ Finset.range 4, (if a = 0 then 0 else if a = 1 then 1 else x) *
      (if 3 - a = 0 then 0 else if 3 - a = 1 then 1 else y)) = y + x := by
  exact closedRedBraidCorrection_neg_two_four
    (fun a => if a = 0 then 0 else if a = 1 then 1 else x)
    (fun a => if a = 0 then 0 else if a = 1 then 1 else y) rfl rfl rfl rfl

end RedBraidCoefficients


namespace FundamentalRedSurjectivity
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private def dominant : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, fun _ => by decide +revert⟩

local notation "S" => signature sl2RootDatum (Subtype.val ∘ dominant)

private def free : Presentation S ℚ :=
  ⟨PEmpty, PEmpty.elim, PEmpty.elim, fun i => i.elim⟩

local notation "B" => fundamentalSingleRedPresentation free
local notation "ordQ" => (fun _ _ : Unit => (0 : MvPolynomial (Fin 2) ℚ))
local notation "exponents" => (fun _ : Fin 1 => Finsupp.single () 1)

example : Function.Surjective (algebraMap ℚ (End (fundamentalSingleRedObj free))) :=
  fundamentalSingleRed_algebraMap_surjective free

example : Function.Surjective (ordinaryToDownwardMatrix (Λ := dominant)
    B ordQ exponents (fun _ _ => 1) (ν := ({()} : Multiset Unit))) :=
  fundamentalSingleRed_ordinaryToDownwardMatrix_surjective free

example : Nontrivial (TensorProductAlgebra ℚ ordQ exponents ({()} : Multiset Unit)) := by
  have h : Nontrivial (AdjoinRoot (Polynomial.X ^ exponents 0 () : Polynomial ℚ)) :=
    AdjoinRoot.nontrivial _ (by simp)
  exact (SingleBlack.oneBlackOneRedEquiv () ordQ exponents).symm.injective.nontrivial


end FundamentalRedSurjectivity

namespace OneRedLoading
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open QuantumGroup QuantumGroup.UDot KL3.Diagram KLR KLRAlgebra

private def w : List (Unit ⊕ Fin 1) := [.inr 0, .inl ()]
private def red : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, fun _ => by decide +revert⟩

private theorem content : (w : Multiset _) = stendhalWeight 1 ({()} : Multiset Unit) := by
  simp [w, stendhalWeight, Finset.univ_unique]
  exact Multiset.cons_swap _ _ 0

private def s : {s : Seq (stendhalWeight 1 ({()} : Multiset Unit)) // IsRedOrdered s} :=
  ⟨Seq.ofList w content, by
    apply (DoubleBoundary.pairwise_red_iff _).mp
    change ((List.ofFn (Seq.ofList w content).1).filterMap Sum.getRight?).Pairwise _
    rw [Seq.ofFn_ofList]; change List.Pairwise _ [0]; simp⟩

example : ∃ (z : List Unit) (h : endWeight sl2RootDatum (Subtype.val ∘ red) 0
      ([.inr 0] ++ blackWord (z.map dn) ++ []) = downRightWeight sl2RootDatum red {()}),
    downTriple sl2RootDatum red s = singleRedTriple sl2RootDatum (z.map dn) h := by
  apply downTriple_eq_singleRedTriple
  rintro ⟨h,hb⟩
  change ((Seq.ofList w content).lbl ⟨0,h⟩).isLeft at hb
  rw [Seq.ofList_lbl] at hb
  exact Bool.noConfusion hb

end OneRedLoading

namespace SingleRedSpanningExamples
open CategoryTheory Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
  Categorification.QuantumGroup.UDot Categorification.KL3.Diagram StringDiagrams

private def reds : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨2, by decide +revert⟩
private abbrev labels := Subtype.val ∘ reds
private abbrev coeff : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev Q := fun (_ _ : Unit) => (0 : MvPolynomial (Fin 2) ℚ)
private def base : Presentation (signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private theorem exponents_agree (i : Unit) :
    (coeff 0 i : ℤ) = sl2RootDatum.pair (sl2RootDatum.iY i) (reds 0).val := by
  cases i
  simp [coeff, reds]
  rfl

private abbrev B := singleRedSpanningPresentation sl2RootDatum reds Q coeff base
private abbrev cut := singleRedTriple (Λd := reds) (right := -2) sl2RootDatum (dns [(),()]) rfl
private abbrev crossing : List (LayerData Unit) := [([], dnShape (.cross () ()), [])]
private theorem crossChain : SChain (dns [(),()]) crossing (dns [(),()]) := ⟨rfl, rfl⟩

example (f : End ((violatingFunctor B (-2)).obj cut)) :=
  singleRed_span_downwardBlack sl2RootDatum reds Q coeff base exponents_agree [(),()] [(),()] rfl rfl f

example := singleRed_span_downwardBlack sl2RootDatum reds Q coeff base exponents_agree
  [(),()] [(),()] rfl rfl
  (singleRedBlackEntry B (dns [(),()]) (dns [(),()]) rfl rfl
    (LinDiagram.of (mkD sl2RootDatum _ crossing crossChain)))


example : Function.Surjective (ordinaryToDownwardMatrix (Λ := reds)
    (singleRedSpanningPresentation sl2RootDatum reds Q coeff base) Q coeff
    (fun _ _ => 1) (ν := ({(), ()} : Multiset Unit))) :=
  singleRed_ordinaryToDownwardMatrix_surjective base Q coeff (fun _ _ => 1) exponents_agree

end SingleRedSpanningExamples


namespace CapPushExample
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams Presentation

private def labels : Fin 1 → ℤ := fun _ => 1
private abbrev S := signature sl2RootDatum labels
private def base : Presentation S ℚ := ⟨Empty, Empty.elim, Empty.elim, fun j => nomatch j⟩
private def down : KL3.Diagram.Letter Unit := (false, ())
private abbrev O := obj sl2RootDatum labels 0
private def c : List (SignedLayer Unit 1) := [([], .black (.cup down), [])]
private def g : List (SignedLayer Unit 1) :=
  [([], .blackRed down.dual 0, [.inl down]), ([.inr 0], .black (.cap down), [])]
private abbrev F := signedLayers sl2RootDatum labels 0 c
private abbrev G := signedLayers sl2RootDatum labels 0 g
private abbrev a := O []
private abbrev a' := O [.inl down, .inl down.dual]
private abbrev b := O [.inl down.dual, .inr 0, .inl down]
private abbrev b' := O [.inr 0]

private theorem hc : Chain a F a' := chain_signedLayers _ _ _ (by
  simp [c, signedChain, Move.bottom, Move.top, KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod])
private theorem hg : Chain b G b' := chain_signedLayers _ _ _ (by
  simp [g, signedChain, Move.bottom, Move.top, KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod])
private theorem ok : SideBySideOK (O []) [] [] a b := ⟨by
  exact colours_ok sl2RootDatum labels 0 [.inl down.dual, .inr 0, .inl down],
  rfl, rfl⟩

example : ∃ d : sbs (O []) [] [] a b ⟶ sbs (O []) [] [] a' b',
    Diagram.layers d = leftLayers (O []) [] [] F b ++ rightLayers (O []) [] [] G a' ∧
    base.diag d ∈ lowerCutSpan base _ _ 2 := by
  let d := Diagram.mk _ ((chain_leftLayers hc ok).append
    (chain_rightLayers hg (ok.chain (G := []) hc rfl)))
  refine ⟨d, rfl, lower_disjoint_blocks base (O []) [] [] hc hg ok (by decide) (by decide) ?_ ?_ d rfl⟩
  · intro L hL
    simp [F, c, signedLayers] at hL
    subst L; decide
  · intro L hL
    simp [G, g, signedLayers] at hL
    rcases hL with rfl | rfl <;> decide

example := cap_dots_collect base 0 [.inr 0] down [] [true, false, true]
example : (addBlackAdjunctionRelations sl2RootDatum labels base).diag
    (dottedSnakeLeft sl2RootDatum labels 0 [.inr 0] down [] 3) =
    (addBlackAdjunctionRelations sl2RootDatum labels base).diag
      (strandDot sl2RootDatum labels 0 [.inr 0] down [] ^ 3) :=
  dottedSnakeLeft_eq sl2RootDatum labels 0 [.inr 0] down [] base 3

end CapPushExample

namespace MixedRedExamples
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open DisconnectedCounterexample
private abbrev weights (_ : Fin 1) (i : Bool) : ℤ := if i then 0 else 2
private def base : Presentation.{0,0} (signature weightDatum weights) ℚ where
  Rel := Empty
  dom e := e.elim
  cod e := e.elim
  rel e := e.elim
private abbrev exponents (_ : Fin 1) : Bool →₀ ℕ := Finsupp.single false 2
private abbrev Q (i j : Bool) : MvPolynomial (Fin 2) ℚ := if i=j then 0 else 1
private abbrev t (_ _ : Bool) : ℚ := 1

example := mixedBlack_halfMate_EF weightDatum weights base 0 [.inr 0] false true [] t
example := mixedBlack_halfMate_FE weightDatum weights base 0 [] true true [.inr 0] t
example := mixedRed_triplePoint_of_downOutside weightDatum weights base 0 [] 0 true false [] .ERF rfl
example := mixedRed_triplePoint_of_ne weightDatum weights 0 [] 0 false true [] Q exponents base t
  (by decide) .left
example := mixedRed_triplePoint_ne weightDatum weights 0 [] 0 false true [] Q exponents base t .FER (by decide)
example := mixedRed_triplePoint_correction weightDatum weights 0 [] 0 false [] Q exponents base t .right

example := mixedRed_triplePoint_sub_mem_crossingFreeSpan weightDatum weights 0 [] 0 false []
  Q exponents base t .right

example := mixedRed_triplePoint_mod_crossingFree weightDatum weights 0 [.inr 0] 0 false []
  Q exponents base t true .RFE

private abbrev localReduction := mixedRed_triplePoint_mod_crossingFree weightDatum weights 0 []
  0 false [] Q exponents base t false .EFR

example := crossingFreeSpan_in_fewerCrossings weightDatum weights 0 _ (𝟙 _) (𝟙 _) (𝟙 _)
  LinearMap.id localReduction

end MixedRedExamples




namespace DoubleRedBraidBubbles
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 4
private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 4

example := closedDotMonomial_eq_bubbles sl2RootDatum weights (-2) [] () 0 [] Q exponents P 1 2

example := normalizedBubble_degreeOne sl2RootDatum weights (-2) [] () 0 [] Q exponents P
  (by decide) (by decide) (by rw [show exponents 0 () = 4 by simp [exponents]]; decide)

end DoubleRedBraidBubbles

namespace RedCapPassExample
open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private def weights : Fin 2 → ℤ := fun r => if r = 0 then 1 else 3
private def exponents : Fin 2 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 0 then 1 else 3)
private def base : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun j => j.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

example := capWithRedPassingLeft_up sl2RootDatum weights 0 [] 0 [.inr 1] Q exponents base ()
example := capWithRedPassingLeft_down sl2RootDatum weights 0 [.inr 0] 1 [] Q exponents base ()
example := capWithRedPassingRight_up sl2RootDatum weights 0 [] 0 [.inr 1] Q exponents base ()
example := capWithRedPassingRight_down sl2RootDatum weights 0 [.inr 0] 1 [] Q exponents base ()
end RedCapPassExample


namespace FirstRedCutExample
open CategoryTheory StringDiagrams Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram Categorification.KL3.Diagram

private def reds : Fin 2 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, by decide +revert⟩
private abbrev labels := Subtype.val ∘ reds
private def P : Presentation (signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev vac : DoubleStendhalTriple sl2RootDatum reds 0 2 :=
  ⟨⟨[.inr 0, .inr 1], by decide⟩, by decide +kernel⟩
private abbrev d := ccwBubbleAt sl2RootDatum labels 0 () [] vac.val.word (List.nil_append _) 2
example : (violatingFunctor P 2).map (InducedCategory.homMk (X := vac) (Y := vac) (P.diag d)) = 0 := by
  apply diagram_eq_zero_of_leftEmptyLayer P vac vac d (L := layer sl2RootDatum labels 0 []
    (.black (.cup (dn ()))) vac.val.word)
  · change _ ∈ Diagram.layers (Diagram.cast _ _ _)
    rw [Diagram.layers_cast]
    have hl := realBubble_layers sl2RootDatum labels 0 [] vac.val.word .counterclockwise () 2
    rw [show Diagram.layers (blackDiagram sl2RootDatum labels 0 [] vac.val.word
        (cwReal sl2RootDatum _ () 2)) = _ from hl]
    simp [BubbleOrientation.cupLetter]
  · rfl
end FirstRedCutExample

namespace RedPrefixBlackSpanningExamples
open CategoryTheory Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
  Categorification.QuantumGroup.UDot Categorification.KL3.Diagram StringDiagrams

private def reds : Fin 3 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨2, by decide +revert⟩
private abbrev labels := Subtype.val ∘ reds
private abbrev coeff : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev Q := fun (_ _ : Unit) => (0 : MvPolynomial (Fin 2) ℚ)
private def base : Presentation (signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private theorem exponents_agree (r : Fin 3) (i : Unit) :
    (coeff r i : ℤ) = sl2RootDatum.pair (sl2RootDatum.iY i) (reds r).val := by
  cases i
  simp [coeff, reds]
  rfl

private abbrev suffix : List (DoubleStrand Unit 3) := [.inl (up ()), .inr 2, .inl (dn ())]
private theorem order : [0, 1] ++ suffix.filterMap DoubleStrand.redLabel = List.finRange 3 := by decide

example (d : LinDiagram ℚ (ob sl2RootDatum 4 (dns [(),()])) (ob sl2RootDatum 4 (dns [(),()]))) :=
  redPrefixBlackEntry_mem_span sl2RootDatum reds Q coeff base [0,1] suffix order exponents_agree
    (right := 2) [(),()] [(),()] rfl rfl d

example := redPrefixBlackEntry_mem_span sl2RootDatum reds Q coeff base [0,1] suffix order exponents_agree
  (right := 6) [] [] rfl rfl (LinDiagram.of (cwReal sl2RootDatum 4 () 4))

private abbrev B := redPrefixSpanningPresentation sl2RootDatum reds Q coeff base

example := redPrefixBlackEntry_mem_span_of_ideal_le sl2RootDatum reds Q coeff base [0,1] suffix order
  exponents_agree B (fun _ _ => le_rfl) (right := 6) [] [] rfl rfl
  (LinDiagram.of (cwReal sl2RootDatum 4 () 4))

end RedPrefixBlackSpanningExamples


namespace SignedCapBlockExample
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

private abbrev Λ : Fin 2 → ℤ := fun r => r.val + 1
private abbrev O := obj sl2RootDatum Λ 0
private abbrev U : List (DoubleStrand Unit 2) := [.inr 0, .inl (dn ()), .inl (up ()), .inr 1]
private abbrev s := O (U ++ [.inl (up ())])
private abbrev t := O ([.inl (up ())] ++ U)

example : ∃ d : s ⟶ t, ForwardPath s d ∧ crossingNumber d = 4 := by
  have h := sweepBlackLeft_chain ([] : List (DoubleStrand Unit 2)) U (up ()) []
  let d := Diagram.mk _ (chain_signedLayers sl2RootDatum Λ 0 h)
  have he : Diagram.layers d = signedLayers sl2RootDatum Λ 0 (sweepBlackLeft [] U (up ()) []) := rfl
  let d' : s ⟶ t := Diagram.cast d (by simp [s, O]) (by simp [t, O])
  have he' : Diagram.layers d' = signedLayers sl2RootDatum Λ 0 (sweepBlackLeft [] U (up ()) []) := by
    simpa [d'] using he
  have hd := ForwardPath.sweepBlackLeft (a := s) (.nil : ForwardPath s (𝟙 s))
    d' [] U (up ()) [] he'
  refine ⟨d', by simpa using hd, ?_⟩
  rw [crossingNumber_of_signedLayers sl2RootDatum Λ 0 d' _ he', sweepBlackLeft_crossings]
  rfl

example : signedCrossings (signedCapBlock [] U (up ()) [] 7) = 4 :=
  signedCapBlock_crossings [] U (up ()) [] 7

private def free : Presentation (signature sl2RootDatum Λ) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun j => nomatch j⟩

example := signedCapBlock_dotLeft sl2RootDatum Λ free 0 [] U (up ()) [] 7

end SignedCapBlockExample

namespace CapInteriorExample
open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private def weights : Fin 2 → ℤ := fun r => if r = 0 then 1 else 3
private def exponents : Fin 2 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 0 then 1 else 3)
private def base : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun j => j.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev scalars : Unit → Unit → ℚ := fun _ _ => 1
local notation "RD" => sl2RootDatum
private abbrev Pm := addRedUpRelations RD weights ℚ (addRedUpSlideRelations RD weights
  (addRedCapRelations RD weights (addRedCupRelations RD weights base)))
private abbrev Pf := addBlackAdjunctionRelations RD weights (addMixedCupPitchforkRelations RD weights Pm scalars)
private abbrev Pc := addDownRelations RD weights (affineCoverQ Q exponents) Pf

example := signedCapBlock_crossInside RD weights Pc 0 [.inr 0] [] [.inl (false, ())] []
  (true, ()) 1 (x := .inr 1) (y := .inl (false, ())) trivial
  (signedCapBraid_redBlack_mixed RD weights base Q exponents scalars 0
    [.inr 0, .inl (false, ())] 1 (true, ()) (false, ()) [.inl (false, ())] (by decide))
end CapInteriorExample

namespace DoubleMarkedRedTransport

open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 1 → ℤ := fun _ => 4
private def P : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 4

example := closePointedRedBraid_left_eq_zero sl2RootDatum weights Q exponents P (-2) [] () 0 []
  1 (by decide)

example := closePointedRedBraid_right_eq_zero sl2RootDatum weights Q exponents P (-2) [] () 0 []
  1 (by decide)

example := pointedRedBraid_convolution_zero sl2RootDatum weights Q exponents P (-2) [] () 0 []
  1 (by decide) (by decide) (by rw [show exponents 0 () = 4 by simp [exponents]]; decide)

example := pointedRedBraid_convolution_zero sl2RootDatum weights Q exponents P (-3) [] () 0 []
  2 (by decide) (by decide) (by rw [show exponents 0 () = 4 by simp [exponents]]; decide)

example (o : BubbleOrientation) (d : ℕ) :
    normalizedBubbleBeforeRed sl2RootDatum weights (-2) [] () 0 [] Q exponents
      (addRedUpSlideRelations sl2RootDatum weights P) o d =
    normalizedBubbleAfterRed sl2RootDatum weights (-2) [] () 0 [] Q exponents
      (addRedUpSlideRelations sl2RootDatum weights P) o d :=
  normalizedBubble_slide sl2RootDatum weights Q exponents P (-2) [] () 0 []
    (by rw [show exponents 0 () = 4 by simp [exponents]]; decide) o d

end DoubleMarkedRedTransport


namespace ViolatingBubbleSweep
open CategoryTheory Categorification Categorification.QuantumGroup.UDot
  Categorification.KL3.Diagram Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private def weights : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨2, fun i => by cases i; decide⟩
private abbrev labels : Fin 1 → ℤ := Subtype.val ∘ weights
private def base : Presentation (signature sl2RootDatum labels) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun i => i.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private def exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev t : Unit → Unit → ℚ := fun _ _ => 1
private abbrev Cap := signedCapKLPresentation sl2RootDatum labels base Q exponents t
private theorem hshift (r : Fin 1) (i : Unit) :
    (exponents r i : ℤ) = ip sl2RootDatum i (labels r) := by
  cases i
  simp [exponents, ip, sl2RootDatum, Function.comp_def, weights]

private abbrev loading : List (DoubleStrand Unit 1) := [.inr 0, .inl (dn ())]
private def bd : BoundaryCategory (RD := sl2RootDatum) (Λ := weights) Cap 0 :=
  ⟨⟨loading, by decide⟩, by decide⟩

private abbrev kl := signedCapKL_reflectedBlack sl2RootDatum labels base Q exponents t

private theorem slides : RedBubbleSlidesLeft sl2RootDatum labels Cap kl 0 loading :=
  signedCapKL_redBubbleSlidesLeft sl2RootDatum labels base Q exponents t 0 loading hshift

example := cutProjection_mem_signedDotSpan (RD := sl2RootDatum) (weights := weights) Cap kl bd
  slides loading [] rfl
  (cwU sl2RootDatum ℚ (endWeight sl2RootDatum labels 0 loading) () 1) (cwU_isBub () 1)

private abbrev V := violatingFunctor (RD := sl2RootDatum) (Λ := weights) Cap 0

example := cutProjection_exterior_mem_signedDotSpan (RD := sl2RootDatum) (weights := weights)
  Cap kl bd slides bd bd (2 • 𝟙 ((V).obj bd) : End ((V).obj bd)) (𝟙 ((V).obj bd))
  (LinearMap.id (R := ℚ) (M := End ((V).obj bd)))
  loading [] rfl (cwU sl2RootDatum ℚ (endWeight sl2RootDatum labels 0 loading) () 1) (cwU_isBub () 1)

example := farLeftBlackCut_project_comp_scalar (RD := sl2RootDatum) (weights := weights)
  Cap kl bd bd bd (2 • 𝟙 bd : End bd) (𝟙 bd)
  (LinearMap.id (R := ℚ) (M := End ((V).obj bd)))
  (cwU sl2RootDatum ℚ (endWeight sl2RootDatum labels 0 []) () 1)

end ViolatingBubbleSweep

namespace CommonCapPresentation
open Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (r : Fin ℓ) (l u : Letter I) (R : List (DoubleStrand I ℓ))

local notation "K" => signedCapKLPresentation RD Λ P Q exponents t
local notation "Braid" => signedCapBraidPresentation RD Λ P Q exponents t
local notation "Pass" => signedCapPassPresentation RD Λ P Q exponents
local notation "red" => (Sum.inr r : DoubleStrand I ℓ)
local notation "black" => (Sum.inl u : DoubleStrand I ℓ)
local notation "source" => L ++ [red, black, Sum.inl l] ++ R
local notation "target" => L ++ [Sum.inl l, black, red] ++ R

example (h : u.1 ≠ l.1) :
    signedDg RD Λ (K) μ source target (signedCapBraidLeft L red black l R) -
      signedDg RD Λ (K) μ source target (signedCapBraidRight L red black l R) ∈
        signedCrossingSpan RD Λ (K) μ source target 2 :=
  signedDg_sub_mem_signedCrossingSpan_of_ideal_le RD Λ (Braid) (K)
    (fun a b => (signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans
      (signedCap_ideal_le_KL RD Λ P Q exponents t a b)) μ source target
    (signedCapBraid_redBlack_mixed RD Λ P Q exponents t μ L r l u R h)

example (i : I) :
    (K).diag (capWithRedPassingLeft RD Λ μ L (false, i) r R) =
      (K).diag (capKeepingRedLeft RD Λ μ L (false, i) r R) :=
  congrArg ((Pass).extension (K) (fun a b =>
    (signedCapPass_ideal_le RD Λ P Q exponents t a b).trans
      (signedCap_ideal_le_KL RD Λ P Q exponents t a b))).map
    (capWithRedPassingLeft_up RD Λ μ L r R Q exponents P i)


end CommonCapPresentation

namespace CapBraidBound
open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private def weights : Fin 2 → ℤ := fun r => if r = 0 then 1 else 3
private def exponents : Fin 2 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 0 then 1 else 3)
private def base : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun j => j.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev scalars : Unit → Unit → ℚ := fun _ _ => 1
local notation "RD" => sl2RootDatum
private abbrev Pc := signedCapKLPresentation RD weights base Q exponents scalars

example := signedCapBlock_crossInside RD weights Pc 0 [.inr 0] [] [.inl (false, ())] []
  (false, ()) 1 (x := .inl (false, ())) (y := .inr 1) trivial
  (signedCapKL_hasCapBraidBound RD weights base Q exponents scalars 0
    [.inr 0, .inl (true, ())] (.inl (false, ())) (.inr 1) (false, ()) [.inl (false, ())] trivial)
end CapBraidBound

namespace AllDownwardMatrixExamples
open Categorification Categorification.Stendhal Categorification.Stendhal.DoubleDiagram
  Categorification.QuantumGroup.UDot StringDiagrams

private def weights : Fin 2 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨2, by decide +revert⟩
private abbrev exponents : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private theorem weight_eq (r : Fin 2) (i : Unit) :
    (exponents r i : ℤ) = sl2RootDatum.pair (sl2RootDatum.iY i) (weights r).val := by
  cases i
  simp [exponents, weights]
  rfl

private def base (k : Type) [CommRing k] :
    Presentation (signature sl2RootDatum (Subtype.val ∘ weights)) k :=
  ⟨Empty, Empty.elim, Empty.elim, fun r => r.elim⟩
private abbrev poly (k : Type) [CommRing k] : Unit → Unit → MvPolynomial (Fin 2) k :=
  fun _ _ => 0

-- Two red strands of weight two and two downward strands of the same colour.
example : Function.Surjective (ordinaryToDownwardMatrix (Λ := weights)
    (signedCapKLPresentation sl2RootDatum (Subtype.val ∘ weights) (base (ZMod 4))
      (poly _) exponents (fun _ _ => 1)) (poly _) exponents (fun _ _ => 1)
    (ν := ({(), ()} : Multiset Unit))) :=
  signedCapKL_ordinaryToDownwardMatrix_surjective (base _) (poly _) exponents _
    (fun _ _ => 1) weight_eq


end AllDownwardMatrixExamples

namespace DistinctRedWeightExamples
open Categorification Categorification.Stendhal.DoubleDiagram CategoryTheory StringDiagrams Categorification.QuantumGroup.UDot

private def weights : Fin 2 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun r => ⟨r.val + 1, by intro i; change 0 ≤ 1 * ((r.val : ℤ) + 1); omega⟩
private abbrev lab := Subtype.val ∘ weights
private def base : Presentation (signature sl2RootDatum lab) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun r => r.elim⟩
private abbrev poly : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev exponents : Fin 2 → Unit →₀ ℕ := corootExponents (Λ := weights) (fun _ => Set.toFinite _)
private abbrev scalars : Unit → Unit → ℚˣ := fun _ _ => 1
private abbrev cap := signedCapKLPresentation sl2RootDatum lab base poly exponents (fun i j => (scalars i j : ℚ))
private abbrev content : Multiset Unit := {()}

example : Function.Surjective (ordinaryToDownwardMatrix_ofWeights cap poly scalars (ν := content)) :=
  signedCapKL_ordinaryToDownwardMatrix_ofWeights_surjective base poly scalars

example : (exponents 0 () : ℤ) = 1 ∧ (exponents 1 () : ℤ) = 2 := by
  simp only [exponents,corootExponents_pair]
  decide

end DistinctRedWeightExamples


namespace SignedCapSuccessorExamples
open Categorification Categorification.QuantumGroup.UDot
  Categorification.Stendhal Categorification.Stendhal.DoubleDiagram StringDiagrams

private abbrev weights : Fin 2 → ℤ := fun r => if r = 0 then 1 else 3
private abbrev exponents : Fin 2 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 0 then 1 else 3)
private def base : Presentation (signature sl2RootDatum weights) ℚ :=
  ⟨Empty, Empty.elim, Empty.elim, fun j => j.elim⟩
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev scalars : Unit → Unit → ℚ := fun _ _ => 1

-- Equal-colour nilHecke dot correction with red strands before and after the dotted black.
example := signedCapBlock_dotInside sl2RootDatum weights base Q exponents scalars 0 []
  [.inr 0] [.inr 1] (false, ()) (false, ()) [] 2

-- The moving leg crosses an upward black of the same colour and two red strands.
example := signedCapBlock_dotRight sl2RootDatum weights base Q exponents scalars 0 []
  [.inr 0, .inl (true, ()), .inr 1] (false, ()) [] 2

example := signedCapBlock_dotRight_nil sl2RootDatum weights base Q exponents scalars 0
  [.inr 0] (true, ()) [.inr 1] 2

-- A red crosses the stationary leg with another black in the sweep and two cap dots.
example := signedCapKL_capBlock_enterLeft sl2RootDatum weights base 0 Q exponents scalars
  [.inr 0] [.inl (false, ())] [] (.inr 1) (false, ()) 2

-- The two sides of the sweep give a red/black bigon and an equal-colour black bigon.
example := signedCapKL_capBlock_crossLast sl2RootDatum weights base 0 Q exponents scalars
  [.inr 0] [.inl (false, ())] [] (false, ()) (.inr 1) 2

example := signedCapKL_capBlock_crossFirst sl2RootDatum weights base 0 Q exponents scalars
  [.inr 0] [.inl (false, ())] [.inr 1] (.inl (false, ())) (false, ()) 2

-- The alternating black legs close to a dotted curl between the two reds.
example := signedCapKL_capBlock_crossBoth sl2RootDatum weights base 0 Q exponents scalars
  [.inr 0] [.inr 1] (true, ()) 2

private abbrev crossingPresentation := signedCapKLPresentation sl2RootDatum weights base Q exponents scalars
private abbrev crossingBoundary := obj sl2RootDatum weights (0 : ℤ) [.inr 0, .inr 1, .inl (false, ())]

example := capSuccessor_allCrossings sl2RootDatum weights base Q exponents scalars
  (LinearMap.id (R := ℚ) (M := crossingPresentation.obj crossingBoundary ⟶
    crossingPresentation.obj crossingBoundary))
  (.inl (true, ())) (.inr 1) trivial [.inr 0] [.inl (false, ()), .inl (false, ())]
  [.inr 0, .inr 1] [.inl (false, ())] (false, ()) []
  (by apply pairPlacement_of_eq; rfl)

end SignedCapSuccessorExamples

noncomputable section CrossingRescaleExamples

open MvPolynomial
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- Crossing scalars `2` between distinct colours of `Bool`. -/
private def twoUnits (a b : Bool) : ℚˣ := if a = b then 1 else Units.mk0 2 (by norm_num)

/-- KLR parameters `4` and `1` between distinct colours, related by `twoUnits`. -/
private def fourQ (a b : Bool) : MvPolynomial (Fin 2) ℚ := if a = b then 0 else C 4
private def oneQ (a b : Bool) : MvPolynomial (Fin 2) ℚ := if a = b then 0 else 1

private theorem twoUnits_self (a : Bool) : twoUnits a a = 1 := by simp [twoUnits]

private theorem fourQ_eq (a b : Bool) (h : a ≠ b) :
    fourQ a b = C ((twoUnits a b * twoUnits b a : ℚˣ) : ℚ) * oneQ a b := by
  simp only [fourQ, oneQ, twoUnits, h, Ne.symm h, ite_false, Units.val_mul, Units.val_mk0, mul_one]
  norm_num

example : KLR.KLRAlgebra ℚ fourQ ({false, true} : Multiset Bool) ≃ₐ[ℚ]
    KLR.KLRAlgebra ℚ oneQ ({false, true} : Multiset Bool) :=
  KLR.KLRAlgebra.rescale twoUnits_self fourQ_eq

example : Stendhal.TensorProductAlgebra ℚ fourQ (fun _ : Fin 1 => Finsupp.single false 1)
      ({true} : Multiset Bool) ≃ₐ[ℚ]
    Stendhal.TensorProductAlgebra ℚ oneQ (fun _ : Fin 1 => Finsupp.single false 1)
      ({true} : Multiset Bool) :=
  Stendhal.tensorRescale _ _ twoUnits_self fourQ_eq

end CrossingRescaleExamples



open Categorification QuantumGroup KLR StringDiagrams Stendhal DoubleDiagram

namespace TensorCornerKL

private abbrev C₁ := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev Λ₁ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

private theorem rouq : IsRouquierQ C₁ (fun _ _ => (0 : MvPolynomial (Fin 2) ℚ)) where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

/-- The double-diagram presentation with no extra relations. -/
private def emptyP : Presentation.{0, 0} (signature (coordinateDatum Λ₁ C₁)
    (redWeight (cyclotomicCoverWeightDatum Λ₁ C₁))) ℚ where
  Rel := Empty
  dom r := r.elim
  cod r := r.elim
  rel r := r.elim

/-- The repaired Lemma 4.29 isomorphism (Webster arXiv:1309.3796v3) in type A₁ with one red
strand of level two. -/
noncomputable example (ν : Multiset Unit) :=
  clToDownwardMatrixKLEquiv (ν := ν) (Λ := Λ₁) (hQ := rouq)
  (fun i j h => (h (Subsingleton.elim i j)).elim) (P := emptyP) (fun r => r.elim)
  (fun r => r.elim)

/-- The repaired Morita equivalence of Theorem 4.30 (Webster arXiv:1309.3796v3) in the same
setting. -/
example (ν : Multiset Unit) :=
  clTensorProduct_moritaEquivalent.{0, 0, 0} (Λ := Λ₁) (hQ := rouq) ν
  (fun i j h => (h (Subsingleton.elim i j)).elim) (P := emptyP) (fun r => r.elim)
  (fun r => r.elim)

/-- The categorical action of Theorem 4.31 (Webster arXiv:1309.3796v3) in the same setting. -/
example (ν : Multiset Unit) :=
  clBlackAction_tensorProduct.{0, 0, 0} (Λ := Λ₁) (hQ := rouq) ν
  (fun i j h => (h (Subsingleton.elim i j)).elim) (P := emptyP) (fun r => r.elim)
  (fun r => r.elim)

/-- The categorical action on cyclotomic KLR algebras of Theorem 3.17 (Webster
arXiv:1309.3796v3) in the same setting. -/
example (ν : Multiset Unit) :=
  clBlackAction_cyclotomic.{0, 0, 0} (hQ := rouq) Λ₁ ν
  (fun i j h => (h (Subsingleton.elim i j)).elim) (P := emptyP) (fun r => r.elim)
  (fun r => r.elim)

/-- The nondegenerate trace on cyclotomic KLR algebras of Theorem 3.18 (Webster
arXiv:1309.3796v3) in the same setting. -/
example (ν : Multiset Unit) :=
  clCyclotomic_trace_nondegenerate.{0, 0, 0} (hQ := rouq) Λ₁ ν
  (fun i j h => (h (Subsingleton.elim i j)).elim) (P := emptyP) (fun r => r.elim)
  (fun r => r.elim)

end TensorCornerKL

namespace BlackActionKL

open Categorification QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams Stendhal
  DoubleDiagram

/-- One red strand of label `1` for `sl₂`. -/
private abbrev fund₁ : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
  fun _ => ⟨1, fun _ => by decide +revert⟩

/-- The signed presentation with no relations. -/
private def emptySigned : Presentation.{0, 0}
    (signature sl2RootDatum (fun r => (fund₁ r).val)) ℚ where
  Rel := Empty
  dom r := r.elim
  cod r := r.elim
  rel r := r.elim

/-- The same presentation with the black Khovanov–Lauda relations imposed. -/
private noncomputable abbrev blackSigned := addBlackKLRelations sl2RootDatum (fun r => (fund₁ r).val) emptySigned

/-- The action of Theorem 4.28 (Webster arXiv:1309.3796v3) of the Khovanov–Lauda 2-category of
`sl₂` on the double tensor product categories for one red strand. -/
noncomputable example :=
  blackActionPseudofunctor (RD := sl2RootDatum) (Λ := fund₁) blackSigned
    (fun r => blackSigned.lin_rel_self (.inr r))

end BlackActionKL

end NonVacuity

namespace NonVacuity.CyclotomicFrobeniusRouquier

open Categorification QuantumGroup QuantumGroup.UDot

/-- The coordinate weight datum `X = ℤ^I`, `Y = Hom(X, ℤ)` of the parallel-edge Cartan datum. -/
private def coordDatum : WeightDatum rqC (Fin 2 → ℤ) ((Fin 2 → ℤ) →+ ℤ) where
  pair := AddMonoidHom.id _
  iX j i := A rqC i j
  iY i := { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
  pair_iY_iX _ _ := rfl

/-- Webster arXiv:1309.3796v2, Theorem 3.18, for Rouquier parameters in characteristic two: two
interacting colours with a double edge, the cyclotomic quotient of weight `(2, 2)` with
`a_i = u²`, black labels `0, 1, 0`. -/
example := KLR.IsRouquierQ.cyclotomic_frobenius rqHyp coordDatum (fun _ => 2)
  (a := fun _ => Polynomial.X ^ 2) (fun _ => Polynomial.monic_X_pow 2)
  (fun _ => by simp [coordDatum]) ({0, 1, 0} : Multiset (Fin 2))

/-- Kang–Kashiwara projectivity over the base ring in characteristic two, for the parallel-edge
Rouquier parameters and `a_i = u²`. -/
example := KLR.CycKLR.projective_base (fun _ => Polynomial.X ^ 2) rqHyp.klrSymm
  rqHyp.polyInY_leading (fun _ => Polynomial.monic_X_pow 2) ({0, 1, 0} : Multiset (Fin 2))

/-- Webster arXiv:1309.3796v2, Corollary 3.26 (flatness), for `λ = (2, 2)`. -/
example := KLR.CyclotomicAction.UnivCyc.flat (lam := fun _ => 2) rqHyp
  ({0, 1, 0} : Multiset (Fin 2))

/-- Webster arXiv:1309.3796v2, Corollary 3.26 (freeness), for `λ = (2, 2)` over `𝔽₂`. -/
example := KLR.CyclotomicAction.UnivCyc.free (lam := fun _ => 2) rqHyp
  ({0, 1, 0} : Multiset (Fin 2))

/-- Webster arXiv:1309.3796v2, Proposition 3.25 (the action), for `λ = (2, 2)`. -/
noncomputable example := KLR.CyclotomicAction.univCyclotomicPresCL (lam := fun _ => 2) rqHyp
  coordDatum (fun _ => 2) (fun _ => by simp [coordDatum])

/-- Webster arXiv:1309.3796v2, Definition 3.23: the identity strongly equivariant functor of the
universal categorification, and Webster's condition for it. -/
noncomputable example := CategoryTheory.Pseudofunctor.StrongTrans.id
  (KLR.CyclotomicAction.univCyclotomicPresCL (lam := fun _ => 2) rqHyp coordDatum (fun _ => 2)
    (fun _ => by simp [coordDatum]))

example := @TwoRep.StronglyEquivariant.webster_condition

/-- Webster arXiv:1309.3796v2, §3.4: `Ř^λ`-modules as a module category over the presentation
over `k`, for `λ = (2, 2)`. -/
noncomputable example := KLR.CyclotomicAction.univCyclotomicPresCLk (lam := fun _ => 2) rqHyp
  coordDatum (fun _ => 2) (fun _ => by simp [coordDatum])

/-- Webster arXiv:1309.3796v2, §3.4: `Ř^λ-pmod` as a module category over the presentation
over `k`, for `λ = (2, 2)`. -/
noncomputable example := KLR.CyclotomicAction.univCyclotomicPresCLPmod (lam := fun _ => 2) rqHyp
  coordDatum (fun _ => 2) (fun _ => by simp [coordDatum])

/-- Webster arXiv:1309.3796v2, Proposition 3.25 (the quotient by `I` at the vacuum), for
`λ = (2, 2)` and `ν = α_0 + α_1 + α_0`. -/
noncomputable example :=
  KLR.CyclotomicAction.vacQuotientEquiv.{0, 0, 0, 0} (lam := fun _ => 2) rqHyp coordDatum
    (fun _ => 2) (fun _ => by simp [coordDatum]) ({0, 1, 0} : Multiset (Fin 2))

private theorem coordHΛ :
    ∀ i : Fin 2, (((fun _ => 2) : Fin 2 → ℕ) i : ℤ) =
      coordDatum.pair (coordDatum.iY i) (fun _ => 2) :=
  fun _ => by simp [coordDatum]

/-- Webster arXiv:1309.3796v2, Corollary 3.27 (1), inputs: evaluation at `P_∅` is full, the
images of `P_∅` are dense in `Ř^λ-pmod`, and `P_∅` itself, killed by every `E_i`, satisfies the
kernel condition, for `λ = (2, 2)`. -/
example := KLR.CyclotomicAction.vacuum_full.{0, 0, 0} rqHyp coordDatum _ coordHΛ

example := KLR.CyclotomicAction.vacuum_isDenseFamily.{0, 0, 0} rqHyp coordDatum _ coordHΛ

example := KLR.CyclotomicAction.vacuum_kerLe.{0, 0, 0} rqHyp coordDatum _ coordHΛ _
  (KLR.CyclotomicAction.univPmod_map₂Linear rqHyp coordDatum _ coordHΛ)
  (KLR.CyclotomicAction.univVacuum rqHyp coordDatum _ coordHΛ)
  (fun _ e i r h => KLR.CyclotomicAction.isZero_univPmod_map_vacuum rqHyp coordDatum _ coordHΛ
    e i r h)

/-- Webster arXiv:1309.3796v2, Corollary 3.27 (1), uniqueness, applied to the identity of
`Ř^λ-pmod` for `λ = (2, 2)`. -/
noncomputable example :=
  KLR.CyclotomicAction.vacuumFunctorIso.{0, 0, 0} rqHyp coordDatum _ coordHΛ
    (β := CategoryTheory.Pseudofunctor.StrongTrans.id
      (KLR.CyclotomicAction.univCyclotomicPresCLPmod rqHyp coordDatum _ coordHΛ))
    (β' := CategoryTheory.Pseudofunctor.StrongTrans.id _) (CategoryTheory.Iso.refl _)

/-- Webster arXiv:1309.3796v2, Corollary 3.27 (1), existence. -/
example := @KLR.CyclotomicAction.vacuumFunctor

/-- Webster arXiv:1309.3796v2, Corollary 3.27 (2), applied to the identity of `Ř^λ-pmod` for
`λ = (2, 2)`. -/
example := KLR.CyclotomicAction.vacuum_homTensorMap_bijective.{0, 0, 0} rqHyp coordDatum _ coordHΛ
  (CategoryTheory.Pseudofunctor.StrongTrans.id
    (KLR.CyclotomicAction.univCyclotomicPresCLPmod rqHyp coordDatum _ coordHΛ))

end NonVacuity.CyclotomicFrobeniusRouquier

namespace NonVacuity.WebsterLabelTwoEndpointTor

open Categorification.Stendhal.SingleRed

private noncomputable def Q (_ _ : Unit) : MvPolynomial (Fin 2) ℚ := 0

/-- The actual one-red endpoint corner in Webster Proposition 8.4. -/
noncomputable example := twoBlackTerminalWebsterCornerEquiv Q

/-- The actual one-red derived tensor pairing in degree zero. -/
noncomputable example := labelTwoEndpointTorZero Q

/-- The actual one-red derived tensor pairing in degree five. -/
example := labelTwoEndpointTor_succ_isZero Q 4

/-- The scalar endpoint corner has no nonzero diagrams in internal degree two. -/
example (G : Categorification.KLR.GradingDatum Q) (d : Unit → ℤ)
    (hd : ∀ j, G.degX j = 2 * d j)
    (z : (twoBlackTerminalWebsterIdem_idempotent Q).Corner) :=
  twoBlackTerminalWebsterCorner_mem_grade_iff Q G d hd 2 z

/-- The actual exterior cut with both black strands in the first factor. -/
noncomputable example (hQ : Categorification.KLR.KLRSymm Q) :=
  labelTwoExteriorStandardCutEquiv Q (labelTwoFirstFactorEquiv Q) hQ

/-- The actual exterior cut with both black strands in the last factor. -/
noncomputable example (hQ : Categorification.KLR.KLRSymm Q) :=
  labelTwoExteriorStandardCutEquiv Q (labelTwoLastFactorEquiv Q) hQ

/-- The full two-black slide vanishes between the complementary cut projectors. -/
example :=
  Categorification.Stendhal.labelTwo_endpointSlide_complement
    (fun (_ _ : Unit ⊕ Fin 2) => (0 : MvPolynomial (Fin 2) ℚ))

/-- The reflected terminal projector has the first dot as its off-diagonal line. -/
example := Categorification.KLR.CycKLR.twoBlackTerminal_reflected_corner_span Q

/-- The red-black map from the rational middle standard into the left exterior projective. -/
noncomputable example := Categorification.Stendhal.labelTwoMiddleToExterior Q

/-- The same crossing descends through the middle dot-sum quotient. -/
noncomputable example := Categorification.Stendhal.labelTwoMiddleExteriorDifferential Q

/-- The incoming crossing on the genuine divided-power standard. -/
noncomputable example := Categorification.Stendhal.labelTwoExteriorMiddleDifferential Q

/-- The two actual exterior crossing differentials have zero composite. -/
example := Categorification.Stendhal.labelTwoExteriorMiddleDifferential_comp_zero Q

noncomputable example := Categorification.Stendhal.labelTwoExteriorStandardComplex Q

/-- The undotted and dotted terminal columns of the actual outgoing map. -/
example := Categorification.Stendhal.labelTwo_outgoing_terminal_diagram_columns Q

/-- The outgoing diagrams at each surviving cut have independent scalar coefficients. -/
example (a b : ℚ) :=
  Categorification.Stendhal.LabelTwoEndpointFlag.outgoing_middle_coefficients_eq_zero Q (a := a) (b := b)

example (a b : ℚ) :=
  Categorification.Stendhal.LabelTwoEndpointFlag.outgoing_terminal_coefficients_eq_zero Q (a := a) (b := b)
example := Categorification.Stendhal.LabelTwo.labelTwoExteriorMiddleDifferential_injective ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoExteriorStandardComplex_mono_first ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoExteriorStandardComplex_exact ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoMiddleQuotientDecomposition ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoLeftExteriorDecomposition ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoOutgoing_degree_two ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoRightExteriorDecomposition ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoIncoming_degree_two ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoNormalizedIncoming_injective ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoNormalizedCrossings_exact ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoShiftedIncoming_preservesGrading ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoShiftedOutgoing_preservesGrading ℚ

example := Categorification.Stendhal.labelTwoExteriorEndComplex_exact Q

example := Categorification.Stendhal.labelTwoExteriorEndComplex_epi Q

example := Categorification.Stendhal.labelTwoExteriorCokernel_simple Q

example := Categorification.Stendhal.LabelTwo.labelTwoExteriorCokernelDecomposition ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoNormalizedAugmentation_exact ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoNormalizedAugmentation_surjective ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoShiftedAugmentation_preservesGrading ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoGradedAugmentation_simple ℚ

example := Categorification.Stendhal.labelTwoExteriorReflectedLineEquiv
  (Categorification.Stendhal.LabelTwo.parameter ℚ)

example := Categorification.Stendhal.labelTwoExteriorReflectedLineGenerator_degree_two ℚ

example := Categorification.Stendhal.LabelTwo.labelTwoLeftExterior_projective ℚ

example := Categorification.Stendhal.labelTwoExteriorCokernel_span Q

end NonVacuity.WebsterLabelTwoEndpointTor

namespace NonVacuity.WebsterLocalization

open Categorification Categorification.QuantumGroup

/-- Webster arXiv:1309.3796v2, Definition 3.28, for `sl₂` over `ℚ`: in `U′` the inverse dot is
a two-sided inverse of the downward dot, and the honest bubbles with negative dot counts are the
images of the fake bubbles. -/
example := KL3.Diagram.invDot_comp_downDot UDot.sl2RootDatum ℚ () 0

example := KL3.Diagram.downDot_comp_invDot UDot.sl2RootDatum ℚ () 0

example := KL3.Diagram.cwNegHonest_eq UDot.sl2RootDatum ℚ 0 () 0

example := KL3.Diagram.ccwNegHonest_eq UDot.sl2RootDatum ℚ 0 () 0

/-- Webster arXiv:1309.3796v2, Lemma 3.29, for `sl₂` over `ℚ`: `B′` spans the 2-morphisms of `U′`
between `E E^∨ 1_λ` and itself at `λ = 1`. -/
example : Submodule.span ℚ (Set.range (KL3.Diagram.twoBL UDot.sl2RootDatum ℚ (1 : ℤ)
    [(true, ()), (false, ())] [(true, ()), (false, ())])) = ⊤ :=
  KL3.Diagram.span_twoBL_eq_top _ _ _

/-- The elements of `B′` with nonnegative exponents are the images of the elements of `B`. -/
example (x : KL3.Diagram.SpanIdx [(true, ())] [(true, ())]) :
    KL3.Diagram.twoBL UDot.sl2RootDatum (ZMod 2) (0 : ℤ) [(true, ())] [(true, ())]
        ⟨x.1, fun a => (x.2.1 a : ℤ), x.2.2⟩ =
      (KL3.Diagram.toLoc UDot.sl2RootDatum (ZMod 2)).map
        (KL3.Diagram.twoB UDot.sl2RootDatum (ZMod 2) 0 [(true, ())] [(true, ())] x) :=
  KL3.Diagram.twoBL_of_nonneg _ _ _ _

/-- Webster arXiv:1309.3796v2, Proposition 3.30, for `sl₂`: the trivial shift and the shift by
`δ = 2` with `a = 0`, `b = 2` (so `a i - b i = -⟨i, δ⟩`) are equivalences of `U′`, and the second
restricts to `U′(0, -2) ≌ U′(2, 0)` over `ZMod 3`. -/
noncomputable example := KL3.Diagram.shiftEquivalence UDot.sl2RootDatum ℚ 0 (fun _ => 0)
  (fun _ => 0) (fun _ => by simp [KL3.Diagram.ip])

noncomputable example := KL3.Diagram.shiftEquivalence UDot.sl2RootDatum ℚ 2 (fun _ => 0)
  (fun _ => 2) (fun _ => by simp [KL3.Diagram.ip, UDot.sl2RootDatum])

noncomputable example := KL3.Diagram.shiftHomEquivalence UDot.sl2RootDatum (ZMod 3) 2
  (fun _ => 0) (fun _ => 2) (fun _ => by simp [KL3.Diagram.ip, UDot.sl2RootDatum]) 0 (-2)

end NonVacuity.WebsterLocalization

namespace NonVacuity.WebsterCupCap

open CategoryTheory DG MulOpposite Categorification.Stendhal.Coevaluation
open scoped DG.DegreeZero TensorProduct

local instance : DG.HasDerivedCategory.{0,0} ℚ := DG.HasDerivedCategory.small ℚ
local instance : DG.HasDerivedCategory.{0,0} ℚᵐᵒᵖ := DG.HasDerivedCategory.small ℚᵐᵒᵖ

example := shiftedCupFunctor ℚ ℚ (Fin 2 → ℚ) (-2)
example := capFunctor ℚ ℚ (Fin 2 → ℚ)

example (f : CupCoefficient ℚ (Fin 2 → ℚ)) (x : Fin 2 → ℚ) :=
  cupTensorHomEquiv_op_tmul ℚ ℚ (Fin 2 → ℚ) (2 : ℚ) f (3 : ℚ) x

end NonVacuity.WebsterCupCap

namespace NonVacuity.CLSpanning

open Categorification Categorification.QuantumGroup Categorification.KL3.Diagram

/-- KL III Prop 3.10 for `U_Q(sl_2)` with the KL scalars, downward and upward strands, at the
weight `1` and `ν = 2 · i`. -/
example : CL.Prop310C UDot.sl2RootDatum ℚ CL.CLScalars.kl (1 : ℤ) {(), ()} :=
  CL.prop310C_kl 1 {(), ()}

example : CL.Prop310UpC UDot.sl2RootDatum ℚ CL.CLScalars.kl (1 : ℤ) {(), ()} :=
  CL.prop310UpC_kl 1 {(), ()}

end NonVacuity.CLSpanning

namespace NonVacuity.CLQGrassmannian

open Categorification Categorification.QuantumGroup Categorification.KL3.Diagram

/-- The infinite Grassmannian relation in `U_Q(sl_2)` with Cautis–Lauda scalars (`r = 1`), at the
weight `1` and degree `2`. -/
example := CLQ.grassmannian_all UDot.sl2RootDatum ℚ CL.CLScalars.kl (1 : ℤ) () 2

end NonVacuity.CLQGrassmannian

namespace NonVacuity.CLQSpanning

open Categorification Categorification.QuantumGroup Categorification.KL3.Diagram

/-- Cautis–Lauda scalars for `sl₃` with nonzero `s`-terms and `r ≠ 1`. -/
private def sl3Scalars : CL.CLScalars (Flag.slCartan 2) ℚ where
  t _ _ := 1
  s _ _ _ _ := 1
  r _ := -1
  t_self _ := rfl
  t_symm _ _ _ := rfl
  s_symm _ _ _ _ := rfl

/-- KL III Prop. 3.10 (upward strands) for `U_Q(sl₃)` with these scalars, for strands of both
colours. -/
example : CL.Prop310UpC (Flag.slRootDatum 2) ℚ sl3Scalars 0 {0, 1} :=
  CL.prop310UpC sl3Scalars 0 {0, 1}

end NonVacuity.CLQSpanning

namespace NonVacuity.SelfDualSimple

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private noncomputable abbrev sdQ : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev sdΛ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private noncomputable abbrev sdT := Stendhal.TensorProductAlgebra ℚ sdQ sdΛ 0

private theorem sdRouquier :
    KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) sdQ where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

/-- With no black strands the tensor product algebra is `ℚ`, a simple module over itself. -/
private instance : IsSimpleModule sdT sdT := by
  let e := Stendhal.tensorProductAlgebraZeroEquiv (k := ℚ) sdQ sdΛ
  refine isSimpleModule_self_iff_isUnit.mpr ⟨e.toEquiv.nontrivial, fun x hx => ?_⟩
  have : e x ≠ 0 := (map_ne_zero_iff e e.injective).mpr hx
  exact (MulEquiv.isUnit_map e.toMulEquiv).mp (isUnit_iff_ne_zero.mpr this)

/-- Webster, arXiv:1309.3796v2, Prop. 5.11, for the vacuum block. -/
example := Stendhal.nonempty_equiv_twistDual (L := sdT) sdΛ 0 sdRouquier

end NonVacuity.SelfDualSimple

namespace NonVacuity.PerfectBasis

open Categorification Categorification.KL3.Diagram

private noncomputable abbrev pbC := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev pbΛ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

private theorem pbRouquier :
    KLR.IsRouquierQ pbC (CL.qCL (CL.CLScalars.kl : CL.CLScalars pbC ℚ)) where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

section
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] Classical.propDecidable

/-- Webster, arXiv:1309.3796v2, Thm. 5.14, along the `()`-string from the empty sequence for
`sl₂` with one red strand. -/
example : True := by
  have := fun m => Stendhal.isNoetherianRing_stringAlg pbΛ pbRouquier () 0 m
  have := fun m => Stendhal.isArtinianRing_stringAlg pbΛ pbRouquier () 0 m
  exact (Stendhal.fgString_isPerfectBasis (k := ℚ) (Λ := pbΛ) () 0 pbRouquier
    (Multiset.notMem_zero ())).elim fun _ _ => trivial

namespace NonVacuity.WebsterOrderedResolution

open Categorification.ModuleFiltration


private abbrev A := ℤ
private abbrev std (_ : Unit) := ModuleCat.of A A
private abbrev e (_ : Unit) : A := 1
private abbrev above (_ _ : Unit) : Prop := False

private def data : OrderedStandardCovers std e above where
  quotient c := (lIdeal (e c)).subtype
  surjective c := fun x => ⟨⟨x, mul_one x⟩, rfl⟩
  projective c := by
    refine Module.Projective.of_split (lIdeal (e c)).subtype (LinearMap.id.codRestrict _
      (fun x => mul_one x)) ?_
    rfl
  kernel c := by
    refine ⟨[], by simp, HasFiltration.zero ?_⟩
    constructor
    intro x y
    apply Subtype.ext
    exact Subtype.ext ((show x.1.1 = 0 from x.2).trans (show y.1.1 = 0 from y.2).symm)

example (n : ℕ) : Subsingleton ((data.projectiveResolution ()).complex.X (n+1)) := by
  obtain ⟨J, lb, inc, hab, hspan⟩ :=
    data.projectiveResolution_loading_support () (fun _ _ _ h _ => h) n
  have h : {y | ∃ j, ∃ z : lIdeal (e (lb j)), inc j z = y} = ∅ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨j, _, _⟩
    exact hab j
  constructor
  intro x y
  have hx : x = 0 := by simpa only [h, Submodule.span_empty, Submodule.mem_bot] using hspan x
  have hy : y = 0 := by simpa only [h, Submodule.span_empty, Submodule.mem_bot] using hspan y
  exact hx.trans hy.symm

end NonVacuity.WebsterOrderedResolution


end

end NonVacuity.PerfectBasis

namespace NonVacuity.WebsterOppositeStandardTor

open Categorification DG DG.DerivedCategory CategoryTheory.Limits
open scoped DG.DegreeZero

local instance : DG.HasDerivedCategory.{0, 0} ℚ := DG.HasDerivedCategory.small ℚ

private abbrev Z := DGModuleCat.of ℚ (InDegreeZero ℚ)

example : IsZero ((homologyFunctor (A := ℚ) ℤ (-1)).obj
    ((derivedTensor ℚ ℚ ℚ).obj (Q.obj Z))) := by
  apply isZero_derivedTensorHomology_of_loading_projective_summands
    (P := Z) (S := Z) (ι := fun _ => Empty) (InDegreeZero.isKProjective (A := ℚ) (M := ℚ)) (𝟙 Z)
    (DGModuleHom.isQuasiIso_id (A := ℚ) (M := InDegreeZero ℚ)) (fun _ a => a.elim) (fun _ a => a.elim)
    (fun _ a => a.elim)
  · intro j hj x hx
    have hx' : x = 0 := ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hj
    subst x
    exact Submodule.zero_mem _
  · intro j _ a
    exact a.elim
  · omega

end NonVacuity.WebsterOppositeStandardTor

namespace NonVacuity.StringParametrization

open Categorification Categorification.KLR

/-- The alternating colour sequence on `Bool` meets every colour infinitely often. -/
theorem alt_hσ : ∀ (a : Bool) (m : ℕ), ∃ r, m ≤ r ∧ decide (r % 2 = 0) = a := by
  intro a m
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> cases a
  · exact ⟨m + 1, by omega, by simp; omega⟩
  · exact ⟨m, le_rfl, by simp [h]⟩
  · exact ⟨m, le_rfl, by simp; omega⟩
  · exact ⟨m + 1, by omega, by simp; omega⟩

example : Function.Injective (strKey (fun r : ℕ => decide (r % 2 = 0))) :=
  strKey_injective alt_hσ

example (ν : Multiset Bool) (L : Type) [AddCommGroup L] [Module ℚ L]
    [Module (KLRAlgebra ℚ (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ)) ν) L]
    [IsScalarTower ℚ (KLRAlgebra ℚ (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ)) ν) L]
    [FiniteDimensional ℚ L]
    [IsSimpleModule (KLRAlgebra ℚ (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ)) ν) L]
    (hnil : ∀ a, SmulNilpotent
      (KLRAlgebra.x a : KLRAlgebra ℚ (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ)) ν) L)
    (s : Seq ν) (hs : KLRAlgebra.IsStrMax (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ))
      (fun r => decide (r % 2 = 0)) ν L s) :
    KLRAlgebra.dimCh (fun _ _ : Bool => (1 : MvPolynomial (Fin 2) ℚ)) ν L s = KLRAlgebra.runsFact s :=
  (KLRAlgebra.isStrMax_aux (P := fun _ _ => 1) (fun _ _ _ => by simp) (fun _ _ _ => one_ne_zero)
    _ ν rfl _ alt_hσ L hnil s hs).1

end NonVacuity.StringParametrization

namespace NonVacuity.StringyClassification

private noncomputable abbrev scQ : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev scΛ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

private theorem scRouquier :
    KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) scQ where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

/-- The standard grading of the `sl₂` KLR algebra with zero crossing parameter. -/
private def scGrading : KLR.GradingDatum scQ where
  degX _ := 2
  degΨ _ _ := -2
  degΨ_self _ := rfl
  isWeightedHomogeneous _ _ h := (h (Subsingleton.elim _ _)).elim

private noncomputable def scG : KLR.GradingDatum (Stendhal.stendhalQ scQ scΛ) :=
  Stendhal.stendhalGradingDatum scΛ scGrading (fun _ => 1) (fun _ => rfl)

/-- Webster, arXiv:1309.3796v2, Prop. 5.17, for `sl₂`, one red strand of weight `ω`, and every
black weight. -/
example (ν : Multiset Unit) :=
  Stendhal.maxLoadClassification (k := ℚ) scRouquier (σ := fun _ => ())
    (fun _ m => ⟨m, le_rfl, rfl⟩) scΛ scG ν

example (ν : Multiset Unit) (p : KLR.Seq (Stendhal.stendhalWeight 1 ν))
    (hp : Stendhal.IsStringy ℚ scQ (fun _ => ()) 1 scΛ ν p) :=
  Stendhal.existsUnique_isMaxLoad_of_isStringy scRouquier (fun _ m => ⟨m, le_rfl, rfl⟩) scΛ scG hp

end NonVacuity.StringyClassification

namespace NonVacuity.StandardSplitting

open Categorification Categorification.Stendhal

/-- Webster, arXiv:1309.3796v2, Prop. 5.18, for the trivial decomposition `e(s) = e(s)` of a
red-ordered loading with one red strand of weight `ω` and one black strand. -/
noncomputable example (s : KLR.Seq (stendhalWeight 1 ({()} : Multiset Unit))) (hs : IsRedOrdered s) :=
  IsSeqDecomp.leftStandardEquiv
    (show IsSeqDecomp (Q := fun _ _ : Unit => (0 : MvPolynomial (Fin 2) ℚ))
        (Λ := fun _ : Fin 1 => Finsupp.single () 1) s hs (fun _ : Unit => seqIdem _ _ s hs) from
      ⟨fun _ => seqIdem_mul_self _ _ s hs, fun i j h => (h (Subsingleton.elim i j)).elim,
        by simp⟩)

end NonVacuity.StandardSplitting

namespace NonVacuity.RedFirstCorner

open Categorification Categorification.Stendhal

private noncomputable abbrev rfQ : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

private theorem rfRouquier :
    KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) rfQ where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

/-- Webster, arXiv:1309.3796v2, Prop. 5.28, for `sl₂`, two red strands of weight `ω`, and every
black weight. -/
noncomputable example (ν : Multiset Unit) :=
  redFirstCornerEquiv rfQ rfRouquier ν (fun _ : Fin 2 => Finsupp.single () 1)

end NonVacuity.RedFirstCorner

namespace NonVacuity.RedBlackCrossing

open Categorification Categorification.KLR Categorification.Stendhal Categorification.KL3.Diagram

private noncomputable abbrev rbC := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

private theorem rbRouquier :
    KLR.IsRouquierQ rbC (CL.qCL (CL.CLScalars.kl : CL.CLScalars rbC ℚ)) where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private theorem rbSymm : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars rbC ℚ)) :=
  fun _ _ h => (h (Subsingleton.elim _ _)).elim

private def rbEmpty : Seq (stendhalWeight 0 ((0 : Multiset Unit) + 0)) :=
  KLRAlgebra.Seq.ofList [] (by decide)

/-- Webster, arXiv:1309.3796v2, Lemma 5.23, for one red strand crossing one black strand of
`sl₂`. -/
example := (IsRedBlackCrossing.crossing (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars rbC ℚ))
  (fun _ : Fin 1 => Finsupp.single () 1) () 0 rbEmpty (by unfold IsRedOrdered; decide)).eq_zero
  rbRouquier rbSymm

/-- Webster, arXiv:1309.3796v2, Thm. 5.27 (3) ⇒ (1), for `sl₂`, two red strands of weight `ω`,
and every black weight: the red-first projective `P⁰` is injective. -/
example (ν : Multiset Unit) :=
  injective_redFirstProjective rbRouquier rbSymm (fun _ : Fin 2 => Finsupp.single () 1) ν

/-- Webster, arXiv:1309.3796v2, Lemma 5.23 (uniqueness in Cor. 5.29), for `sl₂`, two red strands
of weight `ω`, and every black weight: `T^λ` acts faithfully on `P⁰`. -/
example (ν : Multiset Unit) :=
  eq_zero_of_mul_redFirstProjective rbRouquier rbSymm (fun _ : Fin 2 => Finsupp.single () 1) ν

section RedFirstEnd

attribute [local instance 2000] Classical.propDecidable

/-- Webster, arXiv:1309.3796v2, proof of Prop. 5.30, for `sl₂`, two red strands of weight `ω`,
and every black weight: left multiplication by `θ̇_s` is injective on `e(s) T^λ`. -/
example (ν : Multiset Unit) (s : TensorProductAlgebra.OrderedLoading (ℓ := 2) ν) :=
  redShuffleDual_mul_injective rbRouquier rbSymm (baseCrossing_std rbRouquier rbSymm)
    (fun _ : Fin 2 => Finsupp.single () 1) s.1 s.2

/-- Webster, arXiv:1309.3796v2, Prop. 5.30, for `sl₂`, two red strands of weight `ω`, and every
black weight, under the route hypothesis `HasCornerCopresentation e⁰` of Cor. 5.29. -/
noncomputable example (ν : Multiset Unit)
    (hK : HasCornerCopresentation (redFirstIdem (CL.qCL (CL.CLScalars.kl : CL.CLScalars rbC ℚ))
      (fun _ : Fin 2 => Finsupp.single () 1) ν)) :=
  redFirstEndEquiv rbRouquier rbSymm (fun _ : Fin 2 => Finsupp.single () 1) ν hK

end RedFirstEnd

end NonVacuity.RedBlackCrossing

namespace NonVacuity.WebsterCoevaluationWord

open Categorification.Stendhal

private def datum : _root_.CartanDatum Unit ℤ where
  root := fun _ => 2
  coroot := fun _ => LinearMap.id
  coroot_root_self := fun _ => rfl

example : coevaluationWord datum 3 [()] = [(), (), ()] := rfl

example : datum.rootSum (↑(coevaluationWord datum 3 [()]) : Multiset Unit).toFinsupp = 6 := by
  have h : NonnegativeReflectionPath datum 3 [()] :=
    ⟨by change (0 : ℤ) ≤ 3; decide, trivial⟩
  simpa [datum, CartanDatum.reflection_apply] using rootSum_coevaluationWord datum 3 [()] h

end NonVacuity.WebsterCoevaluationWord

namespace NonVacuity.WebsterReducedCoevaluationWord

open Categorification.Stendhal

noncomputable section

private def A : Matrix Unit Unit ℤ := fun _ _ => 2

private theorem generalized : A.IsGeneralizedCartan where
  diag _ := rfl
  offDiag_nonpos i j hij := (hij (Subsingleton.elim i j)).elim
  zero_comm _ _ := Iff.rfl

private abbrev P := Matrix.Realization.std A ℝ
private abbrev weight : P.integralWeights := ⟨P.root (), P.root_mem_integralWeights ()⟩

private theorem dominant : P.IsDominantIntegral weight := by
  intro i
  cases i
  refine ⟨2, ?_⟩
  change P.root () (P.coroot ()) = (2 : ℝ)
  rw [P.root_coroot]
  rfl

private theorem reduced : (P.coxeterSystem generalized).IsReduced ([()] : List Unit).reverse := by
  simp [CoxeterSystem.IsReduced, CoxeterSystem.length_simple]

example : NonnegativeReflectionPath (P.cartanDatum generalized) weight [()] :=
  nonnegativeReflectionPath_of_reduced P generalized weight dominant [()] reduced

example := rootSum_coevaluationWord_of_reduced P generalized weight dominant [()] reduced

example := finrank_classical_coevaluationWeight P generalized weight dominant [()] reduced

private theorem xRegular : LieLean.QuantumGroup.sl2RootDatum.IsXRegular := by
  change LinearIndependent ℤ LieLean.QuantumGroup.sl2RootDatum.root
  rw [linearIndependent_unique_iff]
  intro h
  have hh := congrArg (fun f : ℤ →+ ℤ => f 1) h
  norm_num at hh

/-- The terminal weight space of the highest-weight-two quantum module has dimension one. -/
example := finrank_quantum_coevaluationWeight (R := LieLean.QuantumGroup.sl2RootDatum) P
  xRegular (2 • AddMonoidHom.id ℤ) weight dominant (fun i => by
    cases i
    change P.root () (P.coroot ()) = (2 : ℝ)
    rw [P.root_coroot]
    rfl) [()] reduced

/-- The corresponding Laurent rank of cyclotomic projectives is one at the
terminal weight of the level-two block. -/
example := KLR.CycKLR.finrank_coevaluation_projectiveBlock CyclotomicHighestWeight.params
  (fun _ => 2) CyclotomicHighestWeight.datum 2 CyclotomicHighestWeight.dominantTwo
  CyclotomicHighestWeight.regular P weight dominant (fun i => by
    cases i
    change P.root () (P.coroot ()) = (2 : ℝ)
    rw [P.root_coroot]
    rfl) [()] reduced

/-- There is no weight above the highest weight in the outgoing simple-root direction. -/
example := classical_weightSpace_raise_extremal_eq_bot P generalized (weight : Module.Dual ℝ _) dominant
  1 () (by simp [CoxeterSystem.IsLeftDescent])

/-- The actual level-two divided-power projective at the reflected weight is simple. -/
example := KLR.CycKLR.isSimple_coevaluationProjective CyclotomicHighestWeight.params
  (fun _ => 2) CyclotomicHighestWeight.datum 2 CyclotomicHighestWeight.dominantTwo
  CyclotomicHighestWeight.regular P weight dominant (fun i => by
    cases i
    change P.root () (P.coroot ()) = (2 : ℝ)
    rw [P.root_coroot]
    rfl) [()] reduced

example : coevaluationDividedWord (P.cartanDatum generalized) weight [()] = [((), 2)] := by
  change [((), ((P.cartanDatum generalized).coroot () weight).toNat)] = _
  have h : (P.cartanDatum generalized).coroot () weight = 2 := by
    have h' := P.coroot_cartanDatum_cast generalized () weight
    change (((P.cartanDatum generalized).coroot () weight : ℤ) : ℝ) = P.root () (P.coroot ()) at h'
    rw [P.root_coroot] at h'
    exact_mod_cast h'
  rw [h]
  rfl

/-- The actual complete three-step string scalar at the quantum parameter is one. -/
example := polCoef_endpoint (q := (RatFunc.X : RatFunc ℚ)) RatFunc.X_ne_zero
  LieLean.QuantumGroup.hvn_ratFunc 3

end

end NonVacuity.WebsterReducedCoevaluationWord

namespace NonVacuity.WebsterCoevaluationShift

open Categorification.Stendhal

private def datum : _root_.CartanDatum Unit ℤ where
  root := fun _ => 2
  coroot := fun _ => LinearMap.id
  coroot_root_self := fun _ => rfl

private theorem nonnegative : NonnegativeReflectionPath datum 3 [()] :=
  ⟨by change (0 : ℤ) ≤ 3; decide, trivial⟩

private theorem final : (AddMonoidHom.id ℤ)
    ([()].foldl (fun μ i => datum.reflection i μ) 3) = - (AddMonoidHom.id ℤ) 3 := by
  decide

example : ((coevaluationWord datum 3 [()]).length : ℤ) = 3 :=
  coevaluationWord_length_eq_twice_height datum (AddMonoidHom.id ℤ) (fun _ => rfl)
    3 [()] nonnegative final

example : ((coevaluationWord datum 3 [()]).map (fun _ => (1 : ℤ))).sum = 3 :=
  coevaluationWord_sum_symmetrizers_eq_twice_pairing datum (AddMonoidHom.id ℤ)
    (fun _ => 1) (fun _ => rfl) 3 [()] nonnegative final

end NonVacuity.WebsterCoevaluationShift

namespace NonVacuity.WebsterSingleBlackExtremal

open Categorification.Stendhal

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

example := oneBlack_extremal_projective_simple Q Λ () (by simp [Λ])

end NonVacuity.WebsterSingleBlackExtremal

namespace NonVacuity.WebsterExtremalNorm

open Categorification Categorification.Graded Stendhal Stendhal.SingleBlack

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private def weights : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

private def grading :=
  stendhalGradingDatum weights (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit))
    (fun _ => 1) (fun _ => rfl)

private abbrev block := tensorProductGrade grading ({()} : Multiset Unit)
private abbrev proj := GProj.regular block

private instance : HasGdim block := hasGdim_oneBlack () grading

private theorem rank_one : Module.finrank (LaurentPolynomial ℤ) (K0 block) = 1 := by
  rw [(oneBlackK0Equiv () grading (by simp [weights])).finrank_eq, Module.finrank_self]

private theorem norm_one : proj.homGdim proj = 1 := by
  rw [regular_homGdim () grading]
  rw [show weights 0 () = 1 by simp [weights]]
  simp

example : IsSimpleModule (TensorProductAlgebra ℚ (KLR.klQ (⊥ : SimpleGraph Unit)) weights {()})
    proj.carrier :=
  GProj.isSimpleModule_of_homGdim_eq_one proj rank_one norm_one

example : Nonempty (proj.Iso proj) :=
  GProj.nonempty_iso_of_homGdim_coeff_zero proj proj rank_one norm_one norm_one
    (by rw [norm_one]; simp [HahnSeries.coeff_one])

/-- A shift moves the mixed Hom out of degree zero. -/
example : (proj.homGdim (proj.shift 1)).coeff 0 = 0 := by
  rw [GProj.homGdim_shift_right, norm_one, mul_one]
  simp

end NonVacuity.WebsterExtremalNorm

namespace NonVacuity.WebsterReducedBraid

noncomputable section

open LieLean Matrix.Realization
private def matrixA₂ (i j : Bool) : ℤ := if i = j then 2 else -1

private theorem xRegular {Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum Bool} (R : D.RootDatum Y)
    (hA : D.cartanMatrix = matrixA₂) : R.IsXRegular := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have h (k : Bool) : c false * D.cartanMatrix k false + c true * D.cartanMatrix k true = 0 := by
    have ht := congrArg (fun f : Y →+ ℤ => f (R.coroot k)) hc
    simpa [Fintype.sum_bool, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply, R.root_coroot,
      zsmul_eq_mul, add_comm] using ht
  have a := h false
  have b := h true
  simp [hA, matrixA₂] at a b
  cases j <;> omega

variable (D : LusztigCartanDatum Bool) (hA : D.cartanMatrix = matrixA₂)
local notation "P" => Matrix.Realization.std D.cartanMatrix ℝ
private abbrev wt : (P).integralWeights :=
  ⟨(P).root false + (P).root true, (P).integralWeights.add_mem ((P).root_mem_integralWeights false) ((P).root_mem_integralWeights true)⟩
include hA in
private theorem matchWt (i : Bool) : (wt D : Module.Dual ℝ _) ((P).coroot i) = 1 := by
  change (P).root false ((P).coroot i) + (P).root true ((P).coroot i) = 1
  rw [(P).root_coroot, (P).root_coroot, hA]
  cases i <;> norm_num [matrixA₂]
include hA in
private theorem dominant : (P).IsDominantIntegral (wt D) := fun i => ⟨1, by simpa using matchWt D hA i⟩
local notation "cs" => Matrix.Realization.coxeterSystem (Matrix.Realization.std D.cartanMatrix ℝ) D.isGeneralizedCartan_cartanMatrix
include hA in
private theorem reduced (i : Bool) : (cs).IsReduced ([i, !i, i] : List Bool).reverse := by
  cases i
  · apply (cs).isReduced_alternatingWord true false (k := 3)
    right
    rw [hA]
    decide
  · apply (cs).isReduced_alternatingWord false true (k := 3)
    right
    rw [hA]
    decide

include hA in
private theorem sameBraid : (cs).wordProd ([false,true,false] : List Bool).reverse =
    (cs).wordProd ([true,false,true] : List Bool).reverse := by
  have h := (cs).wordProd_braidWord_eq true false
  have he : D.cartanMatrix.coxeterMatrix true false = 3 := by rw [hA]; decide
  have he' : D.cartanMatrix.coxeterMatrix false true = 3 := by rw [hA]; decide
  rw [show ([false,true,false] : List Bool).reverse = CoxeterSystem.alternatingWord true false 3 from rfl,
    show ([true,false,true] : List Bool).reverse = CoxeterSystem.alternatingWord false true 3 from rfl]
  simpa only [CoxeterSystem.braidWord, he, he'] using h

open Categorification.KLR.Unfurling Categorification.KLR.CycKLR
private abbrev Δ := (coverCartan arr).toLusztig
private theorem hA₂ : Δ.cartanMatrix = matrixA₂ := by
  funext i j
  cases i <;> cases j <;> rfl
private theorem WtMatch (i : Bool) : (wt Δ : Module.Dual ℝ _) ((Matrix.Realization.std Δ.cartanMatrix ℝ).coroot i)
    = (((coverWeight arr).pair.flip lam ((projectiveRootDatum (coverWeight arr)).coroot i) : ℤ) : ℝ) := by
  rw [matchWt Δ hA₂]
  change _ = (((coverWeight arr).pair ((coverWeight arr).iY i) lam : ℤ) : ℝ)
  rw [coverWeight_pair_iY]
  norm_num [lam]
/-- The actual graded cyclotomic projectives agree for the distinct A₂ braid
words 010 and 101, at level one of each colour over the field of two elements. -/
example := coevaluationProjective_iso_of_same_weyl oneArrowParameters (fun _ => 1)
  (coverWeight arr) lam (fun i => by rw [coverWeight_pair_iY]; rfl)
  (xRegular (projectiveRootDatum (coverWeight arr)) hA₂)
  (Matrix.Realization.std Δ.cartanMatrix ℝ) (wt Δ) (dominant Δ hA₂) WtMatch
  [false, true, false] [true, false, true] (reduced Δ hA₂ false) (reduced Δ hA₂ true) (sameBraid Δ hA₂)

end

end NonVacuity.WebsterReducedBraid

namespace NonVacuity.WebsterTerminalCyclotomic

open Categorification.KLR.CycKLR

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

example := terminalCoinvModule_simple (ν := Multiset.replicate 2 ())
  (i := ()) (fun j _ => Subsingleton.elim j ()) Q

example := twoBlack_terminal_relations Q

example := twoBlackTerminalProjective_simple Q
example := Categorification.Stendhal.SingleRed.twoBlackTerminalWebsterProjective_simple Q

end NonVacuity.WebsterTerminalCyclotomic

namespace NonVacuity.WebsterTerminalSymmetric

open KLR KLRAlgebra KLR.CycKLR MvPolynomial NilHecke

private abbrev black := Multiset.replicate 3 ()
private noncomputable abbrev params : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev projection :=
  CycKLR.mk ℚ params (fun _ => (Polynomial.X ^ 3 : Polynomial ℚ)) black

example : projection (pol (esymm (Fin black.card) ℚ 2)) = 0 :=
  terminal_pol_esymm_eq_zero (ν := black) (i := ()) (fun _ _ => Subsingleton.elim _ _) params 2
    (by decide) (by decide)

example (p : MvPolynomial (Fin black.card) ℚ) (hp : p ∈ coinvIdeal ℚ black.card) :
    projection (pol p) = 0 :=
  terminal_pol_eq_zero_of_mem_coinvIdeal (i := ()) (fun _ _ => Subsingleton.elim _ _) params p hp

example := terminalDividedProjective_simple (ν := black) (i := ())
  (fun j _ => Subsingleton.elim j ()) params

end NonVacuity.WebsterTerminalSymmetric

namespace NonVacuity.WebsterSaturatedSingleRed

open Categorification.Stendhal.SingleRed

private abbrev black := Multiset.replicate 3 (0 : Fin 2)
private noncomputable abbrev params : Fin 2 → Fin 2 → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev weights : Fin 1 → Fin 2 →₀ ℕ := fun _ =>
  Finsupp.single 0 3 + Finsupp.single 1 2

private theorem monochromatic : ∀ j ∈ black, j = 0 := by
  intro j hj
  exact (Multiset.mem_replicate.mp hj).2

example := saturatedWebsterProjective_simple monochromatic params weights (by simp [weights, black])

example := saturatedWebsterProjective_projective monochromatic params weights (by simp [weights, black])

end NonVacuity.WebsterSaturatedSingleRed

namespace NonVacuity.WebsterFigureFive

open Categorification Categorification.KLR Categorification.Stendhal
open Categorification.Stendhal.BraidedStendhalAlgebra Equiv MvPolynomial

private abbrev ν : Multiset Unit := {()}
private abbrev μ := stendhalWeight 2 ν
private def t : Seq μ := KLRAlgebra.Seq.ofList [.inr 1, .inr 0, .inl ()] (by decide)
private def s : Seq μ := KLRAlgebra.Seq.ofList [.inr 0, .inl (), .inr 1] (by decide)
private def g : Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2
private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 2 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 2)
private noncomputable def ρ (w : Perm (Fin μ.card)) := (TypeA.exists_reduced _ w).choose
private theorem hρ : TypeA.IsReducedChoice ρ := fun w => (TypeA.exists_reduced _ w).choose_spec
private theorem hQ : KLRSymm Q := fun _ _ _ => rfl
private theorem hb : EdgeBraid (by decide : 0 < μ.card) 1 g s t where
  smul_eq := by
    apply Subtype.ext
    funext x
    change Fin 3 at x
    fin_cases x <;> rfl
  last := rfl
  shift := by
    intro x hx
    change Fin 3 at x
    fin_cases x
    · rfl
    · rfl
    · exact False.elim (hx rfl)

private theorem h1 : 1 < μ.card := by decide

example := figureFiveColumn_hasStandardFiltration (Λ := Λ) (d := 0) hρ hQ h1 rfl rfl hb

private noncomputable def figure5LoadingEquiv :=
  violLoadingStandardEquivBraidCorner (Λ₂ := Λ) (d := 0) hρ hQ h1 rfl rfl hb

example (x : violCorner ℚ Q Λ ν t [1, 0]) :
    (figure5LoadingEquiv (Submodule.Quotient.mk x)).1 =
      violMk ℚ Q Λ ν (ofKLR ℚ Q Λ ν (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t)) * x.1 :=
  violLoadingStandardEquivBraidCorner_mk hρ hQ h1 rfl rfl hb x

open scoped DG.DegreeZero in
/-- Webster, arXiv:1309.3796v2, proof of Proposition 6.9: tensoring the lower loading right
ideal with the braid sends it to the cut, with one black strand and unequal red weights. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [0, 1])ᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [1, 0])ᵐᵒᵖ
  braidingFunctorObjLoadingProjectiveIso (k := ℚ) (Q := Q) (Λ := Λ) (s := s) (κ := [1, 0])
    (show redWord s = [0, 1] from hb.redWord_source_twoRed h1 rfl rfl)

open scoped DG.DegreeZero in
/-- Webster, arXiv:1309.3796v2, Proposition 6.9, Figure 5: the braid of the lower projective
is the swapped loading standard in cohomological degree zero for the same unequal weights. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [0, 1])ᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [1, 0])ᵐᵒᵖ
  braidingFunctorObjFigureFiveIso (Λ₂ := Λ) (d := 0) hρ hQ h1 rfl rfl hb

private def blackWord : Seq ν := KLRAlgebra.Seq.ofList [()] (by decide)
private def vacuumWord : Seq (0 : Multiset Unit) := KLRAlgebra.Seq.ofList [] (by decide)

/-- The lower loading projective is the exterior-projective standardization with last-factor
vacuum, over the right corner of the order `[0, 1]`. -/
noncomputable example :=
  loadingProjectiveEquivExteriorStandardization (Λ₂ := Λ) (σ₂ := 1) (hQ := hQ) (hρ₂ := hρ)
    (add_zero ν) (SingleRed.insertWord ν blackWord) vacuumWord

/-- The upper loading standard is the exterior-projective standardization with first-factor
vacuum, over the right corner of the order `[1, 0]`. -/
noncomputable example :=
  loadingStandardEquivExteriorStandardization (Λ₂ := Λ) (σ₂ := Equiv.swap 0 1)
    (hQ := hQ) (hρ₂ := hρ) (zero_add ν) (SingleRed.insertWord 0 vacuumWord) blackWord

open scoped DG.DegreeZero in
/-- The two-red derived braid interchanges the exterior standardizations for unequal weights
and one black strand, with vacuum last before braiding and first afterward. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [0, 1])ᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) [1, 0])ᵐᵒᵖ
  braidingFunctorObjFigureFiveStandardizationIso (Λ₂ := Λ) hQ hρ blackWord

open QuantumGroup

private abbrev sl₂ := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

private theorem hRouquier : IsRouquierQ sl₂ Q where
  symm i j hij := (hij (Subsingleton.elim i j)).elim
  homogeneous i j hij := (hij (Subsingleton.elim i j)).elim
  unit_coeff i j hij := (hij (Subsingleton.elim i j)).elim

-- The unequal rational red weights are exchanged by the coefficient equivalence.
noncomputable example (c : ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν)
    (List.map (Equiv.swap (0 : Fin 2) 1) (List.finRange 2))) :=
  leftCoefficientEquiv_mem_grade_iff hRouquier (Equiv.swap 0 1) hρ hQ (n := 0) c

private noncomputable abbrev realization := Matrix.Realization.std (UDot.A sl₂) ℂ

private noncomputable def fracΛ : Fin 2 → Unit →₀ ℕ :=
  fun j => Finsupp.single () (if j = 0 then 1 else 3)

private noncomputable def fracWeight (j : Fin 2) :
    Module.Dual ℂ (Matrix.Realization.StdSpace (UDot.A sl₂) ℂ) :=
  ((fracΛ j () : ℂ) / 2) • realization.root ()

private theorem fracWeight_coroot (j : Fin 2) (i : Unit) :
    fracWeight j (realization.coroot i) = (fracΛ j i : ℂ) := by
  cases i
  rw [fracWeight, LinearMap.smul_apply, realization.root_coroot, UDot.A_self, smul_eq_mul]
  push_cast
  ring

private theorem fracWeight_shift :
    weightPairing sl₂ realization (fracWeight 0 - (ν.map realization.root).sum) (fracWeight 1) =
      (-3 / 2 : ℂ) := by
  have hd : UDot.di sl₂ () = 1 := by rfl
  rw [map_sub, LinearMap.sub_apply]
  simp only [ν, Multiset.map_singleton, Multiset.sum_singleton]
  rw [fracWeight, map_smul, LinearMap.smul_apply, weightPairing_root, fracWeight_coroot, hd]
  norm_num [fracΛ, smul_eq_mul]

/-- Webster, arXiv:1309.3796v2, §6.1 Proposition 6.9 and Figure 5, for one black `sl₂` strand
and weights `ω` and `3ω`. The multiplier has degree `3/2`, over the coefficient field `ℚ`. -/
example : ∃ y : violCorner ℚ Q fracΛ ν (figureFiveLower blackWord) [1, 0],
    y.1 = violMk ℚ Q fracΛ ν (ofKLR ℚ Q fracΛ ν
      (KLRAlgebra.ψw (ρ (finRotate μ.card)⁻¹) * KLRAlgebra.e (figureFiveUpper blackWord))) ∧
    y ∈ figureFiveCutGrade sl₂ hRouquier (weightPairing sl₂ realization) fracWeight
      (figureFiveLower blackWord) 1 0 (3 / 2) := by
  have h := figureFive_mem_cutGrade_word (Λ := fracΛ) sl₂ hRouquier realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) hρ blackWord
  rw [fracWeight_shift, neg_div, neg_neg] at h
  exact h

open Categorification.Graded in
/-- The Figure 5 loading comparison in the same `sl₂` example, with internal shift `−3/2`
in Webster's convention and `+3/2` in `Graded.shift`. -/
noncomputable example :
    Categorification.Graded.shift (violLoadingGrade (Λ := fracΛ) sl₂ hRouquier
        (figureFiveUpper blackWord) [1, 0]) (3 / 2 : ℂ)
      ≃ᵍ[(ViolOrderCorner (k := ℚ) (Q := Q) (Λ := fracΛ) (ν := ν) [1, 0])ᵐᵒᵖ]
      figureFiveCutGrade (Λ := fracΛ) sl₂ hRouquier (weightPairing sl₂ realization)
        fracWeight (figureFiveLower blackWord) 1 0 := by
  have e := figureFiveGradedLoadingEquiv_word (Λ := fracΛ) sl₂ hRouquier realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) hρ blackWord
  rw [fracWeight_shift, neg_div, neg_neg] at e
  exact e

open Categorification.Graded in
/-- At the lower endpoint in Webster, arXiv:1309.3796v2, §6.1, Figure 5, the whole degree-zero
piece is respected by the projective comparison, in particular on the loading idempotent. -/
noncomputable example :=
  let v := figureFiveLower blackWord
  let h : redWord v = List.map (1 : Perm (Fin 2)) (List.finRange 2) := by
    exact (redWord_redPerm (1 : Perm (Fin 2)) _).trans (congrArg (List.map (1 : Perm (Fin 2)))
      ((redWord_eq_finRange_iff _).2 (isRedOrdered_seqCast _
        (isRedOrdered_twoPieceLoading (SingleRed.ordered ν _) vacuumWord))))
  let f := violLoadingIdem (k := ℚ) (Q := Q) (Λ := fracΛ) h
  let p : rIdeal f := ⟨f, (isIdempotentElem_violLoadingIdem (Λ := fracΛ) h).eq⟩
  let G := stendhalGradingDatum fracΛ hRouquier.gradingDatum (UDot.di sl₂)
    (fun i => (hRouquier.gradingDatum_degX i).trans (UDot.two_mul_di sl₂ i).symm)
  have hp : p.val.val ∈ violAuxiliaryGrade G 0 :=
    mem_map_of_mem _ (violMk ℚ Q fracΛ ν).toLinearMap
      (mem_map_of_mem _ (ofKLR ℚ Q fracΛ ν).toLinearMap (G.e_mem_grade v))
  (figureFiveLowerProjective_mem_grade_iff (Λ := fracΛ) sl₂ hRouquier hρ blackWord 0 p).2 hp

open Categorification.Graded in
/-- The upper map in Webster, arXiv:1309.3796v2, §6.1, Figure 5, preserves degree zero
on the class of the upper loading idempotent for the same one-strand example. -/
noncomputable example :=
  let σ := Equiv.swap (0 : Fin 2) 1
  let x := SingleRed.insertWord 0 vacuumWord
  let v := figureFiveUpper blackWord
  let κ := List.map σ (List.finRange 2)
  let h : redWord v = κ :=
    (redWord_redPerm σ _).trans (congrArg (List.map σ) ((redWord_eq_finRange_iff _).2
      (isRedOrdered_seqCast (congrArg (stendhalWeight 2) (zero_add ν))
        (isRedOrdered_twoPieceLoading (SingleRed.ordered 0 x) blackWord))))
  let f := violLoadingIdem (k := ℚ) (Q := Q) (Λ := fracΛ) h
  let p : violCorner ℚ Q fracΛ ν v κ := ⟨f.val, mem_violCorner_iff.2
    ⟨congrArg Subtype.val (isIdempotentElem_violLoadingIdem (Λ := fracΛ) h).eq,
      CornerEndomorphism.corner_mul_right (isIdempotentElem_violMk_redProj ℚ Q fracΛ ν κ) f⟩⟩
  let G := stendhalGradingDatum fracΛ hRouquier.gradingDatum (UDot.di sl₂)
    (fun i => (hRouquier.gradingDatum_degX i).trans (UDot.two_mul_di sl₂ i).symm)
  have hp : p.val ∈ violAuxiliaryGrade G 0 :=
    mem_map_of_mem _ (violMk ℚ Q fracΛ ν).toLinearMap
      (mem_map_of_mem _ (ofKLR ℚ Q fracΛ ν).toLinearMap (G.e_mem_grade v))
  loadingStandardEquivExteriorStandardization_mk_mem_grade hRouquier hQ σ hρ
    (zero_add ν) x blackWord p hp

private noncomputable abbrev fracUpperExterior : ModuleCat.{0}
    (ViolOrderCorner (k := ℚ) (Q := Q) (Λ := fracΛ) (ν := ν) [1, 0])ᵐᵒᵖ :=
  exteriorStandardizationRight (Λ₂ := fracΛ) (σ₂ := Equiv.swap 0 1) hQ hρ
    (zero_add ν) (SingleRed.insertWord 0 vacuumWord) blackWord

private noncomputable def fracExteriorToCut :=
  figureFiveExteriorToCut (Λ := fracΛ) sl₂ hRouquier hρ realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord

/-- The Figure 5 cut at degree `3/2` identifies with degree zero in the intrinsic exterior
standardization, over `ℚ`, for one black strand and red weights `ω`, `3ω`. -/
example (x : fracUpperExterior) : fracExteriorToCut.toEquiv x ∈
    figureFiveCutGrade (Λ := fracΛ) sl₂ hRouquier (weightPairing sl₂ realization) fracWeight
      (figureFiveLower blackWord) 1 0 (3 / 2) ↔
    x ∈ figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord 0 := by
  have h := figureFiveExteriorToCut_mem_grade_iff (Λ := fracΛ) sl₂ hRouquier hρ realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord (3 / 2) x
  have hs : (3 / 2 : ℂ) + weightPairing sl₂ realization
      (fracWeight 0 - (ν.map realization.root).sum) (fracWeight 1) = 0 := by
    rw [fracWeight_shift]
    ring
  rwa [hs] at h

/-- In the same example, degree zero is outside the shifted integral coset of the cut. -/
example (x : fracUpperExterior) : fracExteriorToCut.toEquiv x ∈
    figureFiveCutGrade (Λ := fracΛ) sl₂ hRouquier (weightPairing sl₂ realization) fracWeight
      (figureFiveLower blackWord) 1 0 0 ↔ x = 0 := by
  have h := figureFiveExteriorToCut_mem_grade_iff (Λ := fracΛ) sl₂ hRouquier hρ realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord 0 x
  have hs : (0 : ℂ) + weightPairing sl₂ realization
      (fracWeight 0 - (ν.map realization.root).sum) (fracWeight 1) = -3 / 2 := by
    rw [zero_add, fracWeight_shift]
  rw [hs] at h
  refine h.trans ?_
  have hn : ¬ ∃ n : ℤ, (n : ℂ) = -3 / 2 := by
    rintro ⟨n, hn⟩
    have h₂ : ((2 * n : ℤ) : ℂ) = (-3 : ℂ) := by
      push_cast
      linear_combination 2 * hn
    have h₂' : 2 * n = (-3 : ℤ) := by exact_mod_cast h₂
    omega
  have hbot : figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord (-3 / 2) = ⊥ :=
    Function.extend_apply' (f := fun n : ℤ => (n : ℂ)) _ ⊥ _ hn
  rw [hbot]
  exact Submodule.mem_bot ℚ

open scoped DG.DegreeZero in
/-- For one black `sl₂` strand and weights `ω`, `3ω`, over `ℚ`, the Figure 5 diagram
lifts to a balanced tensor of internal degree `3/2` and cochain degree zero. Its image in the
unshifted upper exterior standardization has internal degree zero. -/
example : ∃ x : FigureFiveExteriorTensor (Λ := fracΛ) sl₂ hRouquier hρ blackWord,
    x ∈ figureFiveExteriorTensorGrade (Λ := fracΛ) sl₂ hRouquier hρ
      (weightPairing sl₂ realization) fracWeight blackWord (3 / 2) ∧
    (figureFiveExteriorTensorEquivCut (Λ := fracΛ) sl₂ hRouquier hρ blackWord x).val =
      violMk ℚ Q fracΛ ν (ofKLR ℚ Q fracΛ ν
        (KLRAlgebra.ψw (ρ (finRotate μ.card)⁻¹) * KLRAlgebra.e (figureFiveUpper blackWord))) ∧
    (figureFiveExteriorTensorEquiv (Λ := fracΛ) sl₂ hRouquier hρ
      (weightPairing sl₂ realization) fracWeight realization
      (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
      (weightPairing_isSymm sl₂ realization) blackWord).toLinearEquiv x ∈
      figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord 0 ∧
    x ∈ DG.grading (0 : ℤ) := by
  let ev := figureFiveExteriorTensorEquivCut (Λ := fracΛ) sl₂ hRouquier hρ blackWord
  let gr := figureFiveExteriorTensorEquiv (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight realization
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord
  obtain ⟨y, hy, hg⟩ := figureFive_mem_cutGrade_word (Λ := fracΛ) sl₂ hRouquier realization
    (weightPairing sl₂ realization) fracWeight
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) hρ blackWord
  have hy' : ev (ev.symm y) = y := ev.apply_symm_apply y
  have hx := (figureFiveExteriorTensorEquivCut_mem_grade_iff (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight blackWord (3 / 2) (ev.symm y)).1 (by
      change ev (ev.symm y) ∈ _
      rw [hy']; rwa [fracWeight_shift, neg_div, neg_neg] at hg)
  refine ⟨ev.symm y, hx, (congrArg Subtype.val hy').trans hy, ?_,
    figureFiveExteriorTensor_mem_cochain_zero sl₂ hRouquier hρ blackWord (ev.symm y)⟩
  have h := gr.map_mem' hx
  have hs : (3 / 2 : ℂ) + weightPairing sl₂ realization
      (fracWeight 0 - (ν.map realization.root).sum) (fracWeight 1) = 0 := by
    rw [fracWeight_shift]; ring
  change gr.toLinearEquiv (ev.symm y) ∈ figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ
    blackWord ((3 / 2 : ℂ) + weightPairing sl₂ realization (fracWeight 0 - (ν.map realization.root).sum)
      (fracWeight 1)) at h
  rwa [hs] at h

/-- Degree zero is outside the shifted integral coset of this balanced tensor. -/
example : figureFiveExteriorTensorGrade (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight blackWord 0 = ⊥ := by
  let gr := figureFiveExteriorTensorEquiv (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight realization
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord
  have hn : ¬ ∃ n : ℤ, (n : ℂ) = -3 / 2 := by
    rintro ⟨n, hn⟩
    have h₂ : ((2 * n : ℤ) : ℂ) = (-3 : ℂ) := by
      push_cast
      linear_combination 2 * hn
    have h₂' : 2 * n = (-3 : ℤ) := by exact_mod_cast h₂
    omega
  have hbot : figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord (-3 / 2) = ⊥ :=
    Function.extend_apply' (f := fun n : ℤ => (n : ℂ)) _ ⊥ _ hn
  refine eq_bot_iff.2 fun x hx => (Submodule.mem_bot ℤ).2 (gr.toLinearEquiv.injective ?_)
  let y := gr.toLinearEquiv x
  have h := gr.map_mem' hx
  change y ∈ figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord
    ((0 : ℂ) + weightPairing sl₂ realization (fracWeight 0 - (ν.map realization.root).sum)
      (fracWeight 1)) at h
  rw [zero_add, fracWeight_shift, hbot] at h
  exact ((Submodule.mem_bot ℚ).1 h).trans gr.toLinearEquiv.map_zero.symm

/-- The Figure 5 lower exterior standardization over `ℚ` splits off the regular right
module in every complex internal degree, with last-factor vacuum and red weights `ω`, `3ω`. -/
example (z : ℂ) (x : figureFiveLowerExterior (Λ := fracΛ) sl₂ hRouquier hρ blackWord)
    (hx : x ∈ figureFiveLowerExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord z) :
    figureFiveLowerExteriorInclusion (Λ := fracΛ) sl₂ hRouquier hρ blackWord x ∈
      figureFiveLowerOrderGrade (Λ := fracΛ) sl₂ hRouquier z ∧
    figureFiveLowerExteriorProjection (Λ := fracΛ) sl₂ hRouquier hρ blackWord
      (figureFiveLowerExteriorInclusion (Λ := fracΛ) sl₂ hRouquier hρ blackWord x) = x := by
  obtain ⟨hi, -, hsplit⟩ := figureFiveLowerExterior_graded_retract (Λ := fracΛ) sl₂ hRouquier hρ blackWord
  exact ⟨hi hx, hsplit x⟩

open scoped DG.DegreeZero in
/-- The same one-black lower exterior standardization is K-projective in its weight category. -/
example : DG.CatModule.IsKProjective (figureFiveLowerWeightModule (Λ := fracΛ) sl₂ hRouquier hρ blackWord) :=
  figureFiveLowerWeightModule_isKProjective (Λ := fracΛ) sl₂ hRouquier hρ blackWord

/-- The derived braid on this projective agrees with the ordinary categorical coend. -/
noncomputable example :=
  figureFiveBraidDerivedTensorObjIso (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight blackWord

/-- The two-red derived braid on the lower projective is the shifted upper exterior standard. -/
noncomputable example :=
  figureFiveBraidDerivedExteriorIso (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight realization
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord

/-- After the upper diagram map, the pure coend tensor is evaluated by diagram multiplication. -/
example :=
  figureFiveBraidCoendExteriorIso_hom_tmul (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight realization
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord

private theorem fracWeight_pair :
    weightPairing sl₂ realization (fracWeight 1) (fracWeight 0) = (3 / 2 : ℂ) := by
  have hd : UDot.di sl₂ () = 1 := rfl
  rw [fracWeight, map_smul, LinearMap.smul_apply, weightPairing_root, fracWeight_coroot, hd]
  norm_num [fracΛ, smul_eq_mul]

open scoped DG.DegreeZero in
/-- Internal coordinate `1` of the braid output has degree `3/2`. After the shift `-3/2`
it reads the unshifted degree-zero exterior piece. -/
example :
    (figureFiveShiftedUpperWeightModule (Λ := fracΛ) sl₂ hRouquier hρ
      (weightPairing sl₂ realization) fracWeight realization
      (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
      (weightPairing_isSymm sl₂ realization) blackWord).obj ⟨1⟩ =
      ↥((figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord 0).restrictScalars ℤ) := by
  refine (figureFiveShiftedUpperWeightModule_obj (Λ := fracΛ) sl₂ hRouquier hρ
    (weightPairing sl₂ realization) fracWeight realization
    (fun i w => weightPairing_root sl₂ realization w i) fracWeight_coroot
    (weightPairing_isSymm sl₂ realization) blackWord ⟨1⟩).trans ?_
  have h : ((1 : ℤ) : ℂ) + (2 - weightPairing sl₂ realization (fracWeight 1) (fracWeight 0)) +
      weightPairing sl₂ realization (fracWeight 0 - (ν.map realization.root).sum) (fracWeight 1) = 0 := by
    rw [fracWeight_pair, fracWeight_shift]
    norm_num
  exact congrArg (fun z : ℂ =>
    ↥((figureFiveUpperExteriorGrade (Λ := fracΛ) sl₂ hRouquier hρ blackWord z).restrictScalars ℤ)) h

/-- The entire swapped braid coefficient places auxiliary coordinate one
at Webster degree three halves for the two unequal red weights. -/
example :=
  have h : ((1 : ℤ) : ℂ) + (2 - weightPairing sl₂ realization (fracWeight 1) (fracWeight 0)) =
      (3 / 2 : ℂ) := by rw [fracWeight_pair]; norm_num
  h ▸ twoRedSwapWeight_intAdd (Λ := fracΛ) (ν := ν) sl₂ hRouquier
    (weightPairing sl₂ realization) fracWeight 1 0 1

/-- Swapping the last two of three red strands leaves the first red strand
as a spectator in the normalization of the full coefficient. -/
example :=
  let Ξ : Fin 3 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 1)
  let η : Fin 3 → Module.Dual ℂ (Matrix.Realization.StdSpace (UDot.A sl₂) ℂ) :=
    fun j => ((Ξ j () : ℂ) / 2) • realization.root ()
  adjacentRedSwapWeight_coordinate (Λ := Ξ) (ν := ν) sl₂ hRouquier
    (weightPairing sl₂ realization) η [0] [] 1 2 0 2 1

/-- The normalized three-red swap pieces decompose the full rectangular corner. -/
example :=
  let Ξ : Fin 3 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 1)
  let η : Fin 3 → Module.Dual ℂ (Matrix.Realization.StdSpace (UDot.A sl₂) ℂ) :=
    fun j => ((Ξ j () : ℂ) / 2) • realization.root ()
  adjacentRedSwapWeight_isInternal (Λ := Ξ) (ν := ν) sl₂ hRouquier
    (weightPairing sl₂ realization) η [0] [] 1 2

/-- Reversing three red strands contributes once for each of the three
inverted red pairs to the degree of the full coefficient. -/
example :=
  let Ξ : Fin 3 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 1)
  let η : Fin 3 → Module.Dual ℂ ℂ := fun _ => 0
  let B : LinearMap.BilinForm ℂ (Module.Dual ℂ ℂ) := 0
  have hCard : (redWordInversions ([0, 1, 2] : List (Fin 3)) [2, 1, 0]).card = 3 := by
    decide
  have hoff : redWordOffset B η [0, 1, 2] [2, 1, 0] = 6 := by
    change redWordOffset (0 : LinearMap.BilinForm ℂ (Module.Dual ℂ ℂ)) η
      [0, 1, 2] [2, 1, 0] = 6
    simp only [redWordOffset, LinearMap.zero_apply, sub_zero, Finset.sum_const, hCard]
    norm_num
  have h := redPermutationWeight_intAdd (Λ := Ξ) (ν := ν) sl₂ hRouquier
    B η [0, 1, 2] [2, 1, 0] 0
  show redPermutationWeight (Λ := Ξ) (ν := ν) sl₂ hRouquier B η [0, 1, 2] [2, 1, 0] 6 =
      _ from by simpa only [hoff, Int.cast_zero, zero_add] using h

/-- Two different red pairs are inverted by these successive adjacent
swaps, so their Webster degree offsets add. -/
example :=
  let Ξ : Fin 3 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 1)
  let η : Fin 3 → Module.Dual ℂ (Matrix.Realization.StdSpace (UDot.A sl₂) ℂ) :=
    fun j => ((Ξ j () : ℂ) / 2) • realization.root ()
  redWordOffset_add (weightPairing sl₂ realization) η
    (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    (by decide) (by decide) (by decide) (by decide)

open scoped List in
/-- The inversion condition used in Lemma 6.5 certifies offset addition
along these two consecutive adjacent swaps. -/
example :=
  let Ξ : Fin 3 → Unit →₀ ℕ := fun j => Finsupp.single () (j.val + 1)
  let η : Fin 3 → Module.Dual ℂ (Matrix.Realization.StdSpace (UDot.A sl₂) ℂ) :=
    fun j => ((Ξ j () : ℂ) / 2) • realization.root ()
  redWordOffset_add_of_sublist (weightPairing sl₂ realization) η
    (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private noncomputable abbrev threeRedWeights : Fin 3 → Unit →₀ ℕ :=
  fun j => Finsupp.single () (j.val + 1)

private abbrev threeRedSize := Multiset.card (stendhalWeight 3 ν)

private theorem threeRedWords : TypeA.IsReducedChoice (TypeA.canWord threeRedSize) :=
  fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩

private theorem threeRedLowerNodup : ([0, 1, 2] : List (Fin 3)).Nodup := by decide

private theorem threeRedPerm : ([0, 1, 2] : List (Fin 3)).Perm [1, 0, 2] := by decide

open scoped List in
private theorem threeRedLength :
    ∀ x y : Fin 3, [x, y] <+ [0, 1, 2] → [y, x] <+ [1, 0, 2] → [y, x] <+ [1, 2, 0] := by
  decide

/-- The graded weight coend surjects for two consecutive adjacent swaps. -/
example :=
  braidFactorizationCoend_surjective (I := Unit) (k := ℚ) (Q := Q)
    (Λ := threeRedWeights) (ν := ν) (ρ := TypeA.canWord threeRedSize) sl₂ hRouquier
    threeRedWords (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    threeRedLowerNodup threeRedPerm threeRedLength

/-- The graded factorization is bijective for two consecutive adjacent swaps. -/
example :=
  braidFactorizationCoend_bijective (I := Unit) (k := ℚ) (Q := Q)
    (Λ := threeRedWeights) (ν := ν) (ρ := TypeA.canWord threeRedSize) sl₂ hRouquier
    threeRedWords (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    threeRedLowerNodup threeRedPerm threeRedLength

noncomputable example :=
  braidFactorizationCoendNatIso (I := Unit) (k := ℚ) (Q := Q)
    (Λ := threeRedWeights) (ν := ν) (ρ := TypeA.canWord threeRedSize) sl₂ hRouquier
    threeRedWords (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    threeRedLowerNodup threeRedPerm threeRedLength

noncomputable example :=
  @braidFactorizationDerivedCoendOfResolution Unit (inferInstance : DecidableEq Unit)
    ℚ (inferInstance : Field ℚ) (ℓ := 3) (Q := Q)
    (Λ := threeRedWeights) (ν := ν) (ρ := TypeA.canWord threeRedSize) sl₂ hRouquier
    threeRedWords (lower := [0, 1, 2]) (middle := [1, 0, 2]) (upper := [1, 2, 0])
    threeRedLowerNodup threeRedPerm threeRedLength

noncomputable example :=
  @braidFactorizationDerivedCoendIdentity Unit (inferInstance : DecidableEq Unit)
    ℚ (inferInstance : Field ℚ) (ℓ := 3) (Q := Q)
    (Λ := threeRedWeights) (ν := ν) (ρ := TypeA.canWord threeRedSize) sl₂ hRouquier
    threeRedWords (lower := [0, 1, 2]) (middle := [1, 0, 2])
    threeRedLowerNodup threeRedPerm

end NonVacuity.WebsterFigureFive

namespace NonVacuity.WebsterBlockBraidIndex

open Categorification Categorification.KLR Categorification.Stendhal Equiv TypeA
open scoped BigOperators

private abbrev content : Multiset Bool := {false, true, false}
private abbrev weight := stendhalWeight 3 content
private abbrev m := Multiset.card weight
private theorem six_eq_card : 6 = m := by decide
private def top : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl false, .inr 2, .inl true, .inl false] (by decide)
private def bottom : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl false, .inr 1, .inr 2, .inl true, .inl false] (by decide)
private def sizes (r : Fin 3) : ℕ := r.val
private theorem sizes_card : (∑ r, (sizes r + 1)) = m := by decide
private theorem red_slots (r : Fin 3) : top.lbl (braidBlockPositions sizes sizes_card ⟨r, 0⟩) =
    .inr r := by
  fin_cases r <;> decide
private theorem top_ordered : IsRedOrdered top := (redWord_eq_finRange_iff top).1 (by decide)
private theorem top_nonviolated : ¬ IsViolated top := by
  rintro ⟨_, hv⟩
  change false = true at hv
  cases hv
private def exchange : Perm (Fin 3) := Equiv.swap 0 2
private def phi : Perm (Fin m) := sadj m 1
private theorem bottom_eq : phi⁻¹ • top = bottom := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl
private def bottomRed (r : Fin 3) : Fin m :=
  Fin.cast six_eq_card (if r = 0 then 0 else if r = 1 then 2 else 3)
private def topRed (r : Fin 3) : Fin m :=
  Fin.cast six_eq_card (if r = 0 then 0 else if r = 1 then 1 else 3)
private theorem redPos_bottom (r : Fin 3) : redPos bottom r = bottomRed r := by
  symm
  apply eq_redPos (s := bottom)
  fin_cases r <;> decide
private theorem redPos_top (r : Fin 3) : redPos top r = topRed r := by
  symm
  apply eq_redPos (s := top)
  fin_cases r <;> decide
private theorem phi_eligible : ProjectiveBlockIndex top phi := by
  constructor
  · rw [bottom_eq]
    exact (redWord_eq_finRange_iff bottom).1 (by decide)
  · simp only [bottom_eq, redPos_bottom, redPos_top]
    decide
  · simp only [bottom_eq, redPos_bottom]
    decide

example := exists_braidBlockPositions top top_ordered top_nonviolated

example : redWord (braidBlockPermutation sizes sizes_card exchange • top) = [2, 1, 0] :=
  (redWord_braidBlockPermutation_smul top sizes sizes_card exchange red_slots).trans (by decide)

example := braidColumnIndexOfProjective top sizes sizes_card exchange ⟨phi, phi_eligible⟩

example : (braidColumnBlockIndex sizes sizes_card exchange phi)⁻¹ •
    (braidBlockPermutation sizes sizes_card exchange • top) = bottom := by
  rw [braidColumnBlockIndex_bottom, bottom_eq]

private def wordFirst : List ℕ := [2, 3, 4, 1, 2, 3, 0, 1, 2, 0, 1, 0]
private def wordSecond : List ℕ := [2, 3, 4, 1, 2, 3, 0, 1, 2, 1, 0, 1]
private theorem reducedFirst : IsReduced m wordFirst :=
  ⟨by simp [ValidWord, wordFirst, ← six_eq_card], by rw [length_eq_invCount]; decide⟩
private theorem reducedSecond : IsReduced m wordSecond :=
  ⟨by simp [ValidWord, wordSecond, ← six_eq_card], by rw [length_eq_invCount]; decide⟩
private noncomputable abbrev parameters : Bool → Bool → MvPolynomial (Fin 2) ℚ :=
  fun _ _ => 0
private noncomputable abbrev weights : Fin 3 → Bool →₀ ℕ :=
  fun r => Finsupp.single false (r.val + 1) + Finsupp.single true 1
private def index := braidColumnIndexOfProjective top sizes sizes_card exchange ⟨phi, phi_eligible⟩
private theorem firstProduct : wordProd m wordFirst = index.val := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl
private theorem secondProduct : wordProd m wordSecond = index.val := by
  apply Equiv.ext
  intro x
  fin_cases x <;> rfl

example := braidColumnBlockIndex_wordChange (Q := parameters) (Λ := weights)
  top sizes sizes_card exchange ⟨phi, phi_eligible⟩ reducedFirst reducedSecond firstProduct secondProduct 1

end NonVacuity.WebsterBlockBraidIndex

namespace NonVacuity.WebsterBraidEarlierMixedCut
open Categorification Categorification.KLR Categorification.Stendhal Equiv TypeA
open KLRAlgebra BraidedStendhalAlgebra
open scoped BigOperators

private abbrev content : Multiset Unit := {()}
private abbrev weight := stendhalWeight 3 content
private abbrev m := Multiset.card weight
private theorem four_eq_card : 4 = m := by decide
private def top : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inl ()] (by decide)
private def bottom : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2] (by decide)
private def earlier : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl (), .inr 1, .inr 2] (by decide)
private def sizes (r : Fin 3) : ℕ := if r = 2 then 1 else 0
private theorem sizes_card : (∑ r, (sizes r + 1)) = m := by decide
private def permuteReds : Perm (Fin 3) := Equiv.swap 1 2
private def phi : Perm (Fin m) := sadj m 2
private theorem bottom_eq : phi⁻¹ • top = bottom := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl
private theorem earlier_eq : (phi * sadj m 1)⁻¹ • top = earlier := by
  apply Subtype.ext
  funext a
  fin_cases a <;> rfl
private def topR (r : Fin 3) : Fin m := Fin.cast four_eq_card (Fin.castSucc r)
private def bottomR (r : Fin 3) : Fin m :=
  Fin.cast four_eq_card (if r = 2 then 3 else Fin.castSucc r)
private def earlierR (r : Fin 3) : Fin m :=
  Fin.cast four_eq_card (if r = 0 then 0 else r.succ)
private theorem redPos_top (r : Fin 3) : redPos top r = topR r := by
  symm
  apply eq_redPos (s := top)
  fin_cases r <;> decide
private theorem redPos_bottom (r : Fin 3) : redPos bottom r = bottomR r := by
  symm
  apply eq_redPos (s := bottom)
  fin_cases r <;> decide
private theorem redPos_earlier (r : Fin 3) : redPos earlier r = earlierR r := by
  symm
  apply eq_redPos (s := earlier)
  fin_cases r <;> decide
private theorem phi_eligible : ProjectiveBlockIndex top phi := by
  constructor
  · rw [bottom_eq]
    exact (redWord_eq_finRange_iff bottom).1 (by decide)
  · simp only [bottom_eq, redPos_bottom, redPos_top]
    decide
  · simp only [bottom_eq, redPos_bottom]
    decide
private theorem earlier_eligible : ProjectiveBlockIndex top (phi * sadj m 1) := by
  constructor
  · rw [earlier_eq]
    exact (redWord_eq_finRange_iff earlier).1 (by decide)
  · simp only [earlier_eq, redPos_earlier, redPos_top]
    decide
  · simp only [earlier_eq, redPos_earlier]
    decide
private theorem reduced (w : List ℕ) (hv : ValidWord m w)
    (hl : w.length = invCount m (wordProd m w)) : IsReduced m w :=
  ⟨hv, hl.trans (length_eq_invCount _).symm⟩
private theorem uProduct : wordProd m [2, 1, 2] = braidColumnBlockIndex sizes sizes_card permuteReds phi := by
  apply Equiv.ext
  intro a
  fin_cases a <;> rfl
private theorem vProduct : wordProd m [1, 2] =
    (braidColumnIndexOfProjective top sizes sizes_card permuteReds
      ⟨phi * sadj m 1, earlier_eligible⟩).val := by
  apply Equiv.ext
  intro a
  fin_cases a <;> rfl

private noncomputable abbrev parameters : Unit → Unit → MvPolynomial (Fin 2) ℚ :=
  fun _ _ => 0
private noncomputable abbrev weights : Fin 3 → Unit →₀ ℕ :=
  fun _ => Finsupp.single () 2

private theorem distinct_loadings :
    braidBlockPermutation sizes sizes_card permuteReds • top ≠ phi⁻¹ • top := by decide

example :
    let π := AlgHom.comp (violMk ℚ parameters weights content) (ofKLR ℚ parameters weights content)
    let b := phi⁻¹ • top
    let c := (phi * sadj m 1)⁻¹ • top
    π (ψw [2, 1, 2] * pol 1 * e b) =
      π (ψw [1, 2] * e c) * π (ψ 1 * pol 1 * e b) := by
  intro π b c
  have mixedCut := braidColumnBlockIndex_higher_mixed_cut (Q := parameters) (Λ := weights)
    top sizes sizes_card permuteReds ⟨phi, phi_eligible⟩ (j := 1) (by decide) earlier_eligible
    (r := 1) (i := ()) (by decide) (by decide) (by decide)
    (reduced [2, 1, 2] (by simp [ValidWord, ← four_eq_card]) (by decide))
    (reduced [1, 2] (by simp [ValidWord, ← four_eq_card]) (by decide)) uProduct vProduct 1
  have h := mixedCut.2.2
  have hbot := braidColumnLoadingProjection_map_lowSpan_eq_bot (Q := parameters) (Λ := weights)
    _ _ distinct_loadings (subProds m [2, 1, 2]) 1 le_rfl
  change _ ∈ (lowSpan ℚ (stendhalQ parameters weights) weight (subProds m [2, 1, 2]) 1).map _ at h
  rw [hbot] at h
  apply sub_eq_zero.mp
  simpa only [Submodule.mem_bot] using h

end NonVacuity.WebsterBraidEarlierMixedCut

namespace NonVacuity.BraidedStendhal

open Categorification Categorification.KLR Categorification.Stendhal

private noncomputable abbrev bsQ : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

private theorem bsSymm : KLRSymm bsQ := fun _ _ _ => rfl

/-- The fixed-top ordinary comparison of Webster, arXiv:1309.3796v2, Lemma 6.8. The
middle pair has a black strand between its members, and a singleton block on either side. -/
example :=
  let t : Seq (stendhalWeight 4 ({()} : Multiset Unit)) :=
    KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2, .inr 3] (by decide)
  BraidedStendhalAlgebra.blockTensorEquiv ℚ bsQ
    (fun _ : Fin 4 => Finsupp.single () 1) [0] [3] 2 1 t (by decide)

namespace AdjacentRow
open RedBlock
private abbrev Λ : Fin 4 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private def pair : Fin 2 ↪ Fin 4 :=
  ⟨fun i => ⟨i.val + 1, by omega⟩, fun i j h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
private abbrev β : Multiset Unit := {()}
private abbrev L : List (Fin 4 × Multiset Unit) := [(0,β)]
private abbrev M : List (Fin 4 × Multiset Unit) := [(3,0)]
private abbrev Bs := adjacentRow L M pair β
private theorem weight : weightSum Bs = stendhalWeight 4 (β + β) := by decide
private def top : Loadings Bs :=
  ⟨KLRAlgebra.Seq.ofList [.inr 0,.inl ()] (by decide),
   KLRAlgebra.Seq.ofList [.inr 1,.inl (),.inr 0] (by decide),
   KLRAlgebra.Seq.ofList [.inr 0] (by decide), PUnit.unit⟩
private def bad : Loadings Bs :=
  ⟨top.1,KLRAlgebra.Seq.ofList [.inl (),.inr 1,.inr 0] (by decide),top.2.2⟩

/-- The internal cut is not imposed: the paired reds in exchanged order enclose a black. -/
example := blockTensorLoadingEquiv bsQ Λ L M pair β weight top
  (by rintro (⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | h) <;> contradiction) (by decide)

/-- Moving that black left of both paired reds violates the block, not the global loading.
It annihilates the entire bottom-order column. -/
example : ¬ IsViolated (Seq.cast weight (place Bs bad)) := by rintro ⟨_,h⟩; contradiction
example (z : blockColumn bsQ Λ L M pair β weight) :=
  stackBlocks_violated_mul bsQ Λ L M pair β weight bad (.inr (.inl ⟨by decide,rfl⟩)) z

example := orderedBlockAction bsQ Λ bsSymm (fun _ => 1) L M pair β weight
example := orderedColumn_smulCommClass bsQ Λ bsSymm (fun _ => Fin.revPerm) L M pair β weight

/-- Cut above the uncrossed standardization column. The local crossing exchanges the two
reds with a black between them; the left spectator also carries a black strand. -/
private noncomputable def cross : diagrams bsQ Λ Bs :=
  let t : Seq (stendhalWeight 2 β) := KLRAlgebra.Seq.ofList [.inr 0,.inl (),.inr 1] (by decide)
  let u := BraidedStendhalAlgebra.ofKLR ℚ bsQ (Λ ∘ pair) β
    (KLRAlgebra.ψw [0,1,0] * KLRAlgebra.e t)
  TensorProduct.tmul ℚ 1 (TensorProduct.tmul ℚ u 1)

example := crossingStack_cut bsQ Λ bsSymm L M pair β weight cross 1
example := crossingCut_slide bsQ Λ bsSymm L M pair β weight cross
  (orderedIdem bsQ Λ (fun _ => 1) Bs) 1 (orderedInclusion_one bsQ Λ bsSymm _ Bs).symm 1
example := crossingStack_surjective bsQ Λ bsSymm L M pair β weight

/-- The violation is strictly between two arbitrary diagrams, and its red order is not
that of the uncrossed bottom. The witness is zero in the balanced tensor itself. -/
example (y z : KLRAlgebra ℚ (stendhalQ bsQ Λ) (stendhalWeight 4 (β + β))) :=
  let i : Seq (stendhalWeight 4 (β + β)) := KLRAlgebra.Seq.ofList
    [.inl (), .inr 3, .inr 2, .inl (), .inr 1, .inr 0] (by decide)
  exists_zero_crossingSeamClass_of_quotient bsQ Λ bsSymm L M pair β weight
    (y := y * KLRAlgebra.e i * z) (by
      have hi : IsViolated i := ⟨by decide, rfl⟩
      simp only [map_mul, AlgHom.comp_apply, BraidedStendhalAlgebra.violMk_e hi, mul_zero,
        zero_mul, map_zero])

example := ker_crossingStack_eq_map_ker_boundaryStack bsQ Λ bsSymm L M pair β weight

/-- Read back the balanced tensor of the local crossing with the standard column, with
a black in the pair and another in a spectator. The forward map here is stacking. -/
example (y : BraidedStendhalAlgebra.ViolQuotient ℚ bsQ Λ (β + β)) :
    let t := crossingCut bsQ Λ bsSymm L M pair β weight (TensorProduct.tmul ℚ cross y)
    (crossingStackEquiv bsQ Λ bsSymm L M pair β weight).symm
      (crossingStack bsQ Λ bsSymm L M pair β weight t) = t := by
  intro t; exact (crossingStackEquiv bsQ Λ bsSymm L M pair β weight).symm_apply_apply t

/-- The original unmarked cut kills a violation strictly between arbitrary diagrams. -/
example (y z : BraidedStendhalAlgebra ℚ bsQ Λ (β + β)) :
    let i : Seq (stendhalWeight 4 (β + β)) := KLRAlgebra.Seq.ofList
      [.inl (), .inr 3, .inr 2, .inl (), .inr 1, .inr 0] (by decide)
    crossingDiagramCut bsQ Λ bsSymm L M pair β weight
      (y * BraidedStendhalAlgebra.ofKLR ℚ bsQ Λ (β + β) (KLRAlgebra.e i) * z) = 0 := by
  intro i
  have hi : IsViolated i := ⟨by decide, rfl⟩
  refine Eq.trans ?_ (crossingDiagramCut bsQ Λ bsSymm L M pair β weight).map_zero
  rw [crossingDiagramCut_eq_inverse, crossingDiagramCut_eq_inverse]
  apply congrArg; apply congrArg
  simp only [map_mul, BraidedStendhalAlgebra.violMk_e hi, mul_zero, zero_mul, map_zero]

private abbrev q₄ : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private theorem symm₄ : KLRSymm q₄ := fun _ _ _ => rfl
private def higher : Loadings Bs :=
  ⟨top.1, KLRAlgebra.Seq.ofList [.inl (), .inr 0, .inr 1] (by decide), top.2.2⟩

/-- Over a ring with zero divisors, the cut also kills an interior *higher* loading:
the paired block starts with a black, but the global diagram starts with a red. -/
example (y z : BraidedStendhalAlgebra (ZMod 4) q₄ Λ (β + β)) :
    let i := Seq.cast weight (place Bs higher)
    crossingDiagramCut q₄ Λ symm₄ L M pair β weight
      (y * BraidedStendhalAlgebra.ofKLR (ZMod 4) q₄ Λ (β + β) (KLRAlgebra.e i) * z) = 0 := by
  intro i
  let J := BraidedStendhalAlgebra.blockUpperIdeal (ZMod 4) q₄ Λ (β + β) (pair 0) (pair 1)
    (fun r c => boundaryCount (cut (pair 0) (pair 1) r) c Bs) (L.map Prod.fst ++ pair 0 :: pair 1 :: M.map Prod.fst)
  let q := RingCon.mkₐ (ZMod 4) J.ringCon
  let v := BraidedStendhalAlgebra.violMk (ZMod 4) q₄ Λ (β + β)
  let e := BraidedStendhalAlgebra.ofKLR (ZMod 4) q₄ Λ (β + β) (KLRAlgebra.e i)
  have hz : q (v e) = 0 := by
    change J.ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    apply TwoSidedIdeal.subset_span
    exact ⟨i, by decide, root_lt_of_violated weight (aligned_adjacent L M pair β (by decide)) higher
      (.inr (.inl ⟨by decide, rfl⟩)), rfl⟩
  refine Eq.trans ?_ (crossingDiagramCut q₄ Λ symm₄ L M pair β weight).map_zero
  rw [crossingDiagramCut_eq_inverse, crossingDiagramCut_eq_inverse]; apply congrArg
  apply Subtype.ext; apply Subtype.ext; rw [orderedColumnRep_val, orderedColumnRep_val]
  change q (_ * (v (y*e*z) * _)) = q (_ * (v 0 * _))
  simp only [map_mul v, map_mul q, hz, map_zero v, map_zero q, mul_zero, zero_mul]

section KernelTensor
open BraidedStendhalAlgebra
private abbrev weights : Fin 4 → Unit →₀ ℕ := fun _ => Finsupp.single () 3
private def source : Loadings Bs :=
  ⟨top.1,KLRAlgebra.Seq.ofList [.inr 0,.inl (),.inr 1] (by decide),top.2.2⟩
private abbrev src := Seq.cast weight (place Bs source)
private def uncrossedBottom : Seq (stendhalWeight 4 (β + β)) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inl (),.inr 1,.inr 2,.inl (),.inr 3] (by decide)

example := blockLoading_projective q₄ weights src
example : (crossingSpace (k := ZMod 4)
    (violMk (ZMod 4) q₄ weights (β+β) (redProj (ZMod 4) q₄ weights (β+β) (redWord src)))
    (violMk (ZMod 4) q₄ weights (β+β) (redProj (ZMod 4) q₄ weights (β+β) [0,2,1,3]))).toAddSubgroup =
      braidingBimodule (ZMod 4) q₄ weights (β+β) (redWord src) [0,2,1,3] := rfl

/-- The internal black does not impose a retained cut in the loading presentation. -/
example := ker_blockStandardCover q₄ weights L M pair β weight source (by decide)
  (by rintro (⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | h) <;> contradiction)
example := blockStandardCover_surjective q₄ weights L M pair β weight source (by decide)

/-- A strictly higher generator exists without being globally violated. -/
example : ¬IsViolated (Seq.cast weight (place Bs higher)) ∧
    adjacentBlockRoot (pair 0) (pair 1) src < adjacentBlockRoot (pair 0) (pair 1) (Seq.cast weight (place Bs higher)) := by
  refine ⟨by rintro ⟨_,h⟩; contradiction, lt_of_le_of_ne ?_ ?_⟩
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad : (1 : ℕ) = 2 := congrFun (congrFun h (pair 0)) ()
    contradiction

/-- Cut a violation strictly between two arbitrary diagrams as a zero in the kernel
tensor, not merely in the projective tensor or the standard quotient. -/
example (x y : BraidedStendhalAlgebra (ZMod 4) q₄ weights (β + β)) :=
  let i : Seq (stendhalWeight 4 (β + β)) := KLRAlgebra.Seq.ofList
    [.inl (),.inr 3,.inr 2,.inl (),.inr 1,.inr 0] (by decide)
  exists_zero_blockKernelCut q₄ weights src (pair 0) (pair 1) [0,2,1,3] symm₄
    (x := x * ofKLR (ZMod 4) q₄ weights (β + β) (KLRAlgebra.e i) * y) (by
      have hi : IsViolated i := ⟨by decide,rfl⟩
      simp only [map_mul, violMk_e hi, mul_zero,zero_mul])

example := blockLoadingKernel_eq_idempotentTrace q₄ weights src (pair 0) (pair 1)

/-- The degree-one kernel has affine representatives even when the *exchanged* bottom
pair encloses a black. This does not assert that these representatives have zero class. -/

example := ker_blockKernelTensorInclusion_eq_map q₄ weights src (pair 0) (pair 1)
  (redWord (Seq.cast weight (place Bs top))) symm₄

/-- Over `ZMod 4` with two blacks and two spectators, the class killed in the projective
tensor vanishes in the bottom component with consecutive exchanged reds. -/
example := blockKernelColumnInclusion_injective q₄ weights src (pair 0) (pair 1)
  (TypeA.sadj _ 2 • uncrossedBottom) symm₄ [0] [3] (by decide) uncrossedBottom (by decide)
  2 (by decide) (by decide) (by decide) rfl
private abbrev between := Seq.cast weight (place Bs top)
private abbrev leftExit := TypeA.wordProd (stendhalWeight 4 (β+β)).card [3,2] • between
private abbrev rightExit := TypeA.wordProd (stendhalWeight 4 (β+β)).card [2,3] • between
private abbrev root := adjacentBlockRoot (pair 0) (pair 1) (ν := β+β)

private theorem higherLeft : root src < root leftExit := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h; have bad : (1 : ℕ) = 2 := congrFun (congrFun h (pair 0)) (); contradiction

/-- A mark on the left exit need not extend to the bare right exit or joint. The
correction in this example is a cube, not `1`. -/
example : ¬IsViolated leftExit ∧ root rightExit = root src ∧ weights (pair 0) () = 3 := by
  refine ⟨by rintro ⟨_,h⟩; contradiction, ?_, by simp [weights]⟩
  funext r i; fin_cases r <;> cases i <;> decide

example (y : BraidedStendhalAlgebra (ZMod 4) q₄ weights (β+β)) :=
  blockKernelBigon_slide q₄ weights src (pair 0) (pair 1) [0,2,1,3] between 2 (by decide)
    (blockHigherMark q₄ weights src (pair 0) (pair 1) leftExit (by decide) higherLeft
      (ofKLR (ZMod 4) q₄ weights (β+β) (KLRAlgebra.ψ 2))) () (by decide) (by decide) (by decide) (by decide) y

private def lowTop : Seq (stendhalWeight 4 (β+β)) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl (),.inr 2,.inl (),.inr 3] (by decide)

private theorem cut_idempotent {A : Type*} [Ring A] {p q : A} (hp : p * p = p) (hq : q * q = q) (u : A) :
    p * (p*u*q) * q = p*u*q := by simp only [mul_assoc,hq]; rw [← mul_assoc,hp]

/-- An equal-colour spectator lies to the left of `b i a`. Test the affine
relation on arbitrary upper diagrams in both corners, with their bottom dots. -/
example (u v : BraidedStendhalAlgebra (ZMod 4) q₄ weights (β+β)) :=
  let F := ofKLR (ZMod 4) q₄ weights (β+β)
  let p := fun z : Seq (stendhalWeight 4 (β+β)) => F (KLRAlgebra.e z)
  have sq (z) : p z * p z = p z := by rw [← map_mul F,KLRAlgebra.e_mul_self]
  interleaved_affine_relation_iff q₄ weights between 2 (by decide) symm₄ src
    (Lr := [0]) (Mr := [3]) (by decide) (b := pair 1) (i := ()) (a := pair 0)
    (by decide) (by decide) (by decide) _ _
    (cut_idempotent (sq src) (sq leftExit) u) (cut_idempotent (sq src) (sq rightExit) v)

/-- Here the *right* exit is strictly higher. Both cut classes are re-marked by
the theorem; there is no higher-ideal premise on either exterior diagram. -/
example (z y : BraidedStendhalAlgebra (ZMod 4) q₄ weights (β+β)) :=
  blockKernelHigherExit_slide q₄ weights lowTop (pair 0) (pair 1) [0,2,1,3] between 2 (by decide)
    () (by decide) (by decide) (by decide) (by decide) (by
      refine lt_of_le_of_ne ?_ ?_
      · intro r i; fin_cases r <;> cases i <;> decide
      · intro h; have bad : (0 : ℕ) = 1 := congrFun (congrFun h (pair 0)) (); contradiction) z y

section TwoBlackColours
private abbrev colors : Multiset (Fin 2) := {0,1}
private abbrev param : Fin 2 → Fin 2 → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private abbrev wt : Fin 4 → Fin 2 →₀ ℕ := fun r => if r = pair 0 then
  Finsupp.single 0 2 + Finsupp.single 1 3 else Finsupp.single 0 4 + Finsupp.single 1 4
private def exterior : Seq (stendhalWeight 4 colors) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 2,.inl 0,.inr 1,.inl 1,.inr 3] (by decide)
private def atJoint : Seq (stendhalWeight 4 colors) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl 0,.inr 2,.inl 1,.inr 3] (by decide)

/-- Distinct exterior colour and unequal positive pairings. Test all relations
after killing global violations, not after quotienting by higher loadings. -/
example (u v : ViolQuotient (ZMod 4) param wt colors) :=
  let F := (violMk (ZMod 4) param wt colors).comp (ofKLR (ZMod 4) param wt colors)
  let p := fun z : Seq (stendhalWeight 4 colors) => F (KLRAlgebra.e z)
  have sq (z) : p z * p z = p z := by rw [← map_mul F,KLRAlgebra.e_mul_self]
  let q := fun w => TypeA.wordProd (stendhalWeight 4 colors).card w • exterior
  interleaved_quotient_relation_iff param wt exterior 1 (by decide) (fun _ _ _ => rfl) atJoint
    (Lr := [0]) (Mr := [3]) (by decide) (a := pair 0) (b := pair 1) (i := 0)
    (by decide) (by decide) (by decide) _ _
    (cut_idempotent (sq atJoint) (sq (q [2,1])) u) (cut_idempotent (sq atJoint) (sq (q [1,2])) v)
private def before : Seq (stendhalWeight 4 colors) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inr 2,.inl 0,.inl 1,.inr 3] (by decide)
private def afterPair : Seq (stendhalWeight 4 colors) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 2,.inl 0,.inl 1,.inr 1,.inr 3] (by decide)
private abbrev atLeft := TypeA.wordProd (stendhalWeight 4 colors).card [3,2,1] • afterPair
private abbrev powers (z : ℕ) : ℕ := if z=0 then 2 else 3

/-- Separate black colours give square and cube at the two positions of the left
exit. The upper representative actually takes these blacks past the paired reds. -/
example (y : BraidedStendhalAlgebra (ZMod 4) param wt colors) :=
  blockKernelIntervalBigon_slide param wt before (pair 0) (pair 1) [0,2,1,3]
    (blockHigherMark param wt before (pair 0) (pair 1) atLeft (by decide) (by
      refine lt_of_le_of_ne ?_ ?_
      · intro r i; fin_cases r <;> fin_cases i <;> decide
      · intro h; have bad : (0 : ℕ) = 1 := congrFun (congrFun h (pair 0)) 0; contradiction)
      (ofKLR (ZMod 4) param wt colors (KLRAlgebra.ψw [2,3,1,2])))
    1 2 (by decide) afterPair (by decide) (by decide) powers (by
      intro z hz; rcases (show z=0 ∨ z=1 by omega) with rfl | rfl
      · exact ⟨0,by decide +revert,by simp [powers, wt]⟩
      · exact ⟨1,by decide +revert,by simp [powers, wt]⟩) y

/-- The same exponents annihilate every kernel class at the interleaved bottom,
now on positions 2 and 3 rather than positions 1 and 2. -/
example := ker_blockKernelColumnInclusion_le_ker_dots param wt before (pair 0) (pair 1)
  (fun _ _ _ => rfl) [0] [3] (by decide) before rfl 1 2 (by decide) (by decide) (by decide)
  afterPair (by decide) (by decide) powers (by
    intro z hz; rcases (show z=0 ∨ z=1 by omega) with rfl | rfl
    · exact ⟨0,by decide +revert,by simp [powers, wt]⟩
    · exact ⟨1,by decide +revert,by simp [powers, wt]⟩)

/-- Set only the red moved left to weight zero. The other red and both spectators
still pair positively; the bottom has *two* intervening black strands. -/
example := blockKernelColumnInclusion_injective_of_zero_pairings param (fun r => if r = pair 0 then 0 else wt r)
  before (pair 0) (pair 1) (fun _ _ _ => rfl) [0] [3] (by decide) before rfl 1 2 (by decide)
  (by decide) (by decide) afterPair (by decide) (by decide) (by
    intro z hz; rcases (show z=0 ∨ z=1 by omega) with rfl | rfl
    · exact ⟨0,by decide +revert,by decide⟩
    · exact ⟨1,by decide +revert,by decide⟩)
end TwoBlackColours

/-- With a spectator black, the actual higher tensor is still generated by the
two undotted exits at the interleaved bottom. No vanishing pairing is used. -/
example := exists_interleavedKernelColumn_exits q₄ weights between 2 (by decide) src
  (pair 0) (pair 1) symm₄ (L := [0]) (M := [3]) (by decide) (by decide) (by decide)
  (by decide) (by decide)

/-- The interleaved kernel inclusion with one zero return exponent, two spectator
reds and an exterior black of the same colour. -/
example := interleaved_markedColumn_injective q₄ (fun r => if r = pair 0 then 0 else weights r)
  src between (pair 0) (pair 1) 2 (by decide) symm₄ (Lr := [0]) (Mr := [3])
  (by decide) (i := ()) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))

/-- Both pairings are positive when the joint loading itself is higher. -/
example := interleaved_markedColumn_injective q₄ weights lowTop between (pair 0) (pair 1)
  2 (by decide) symm₄ (Lr := [0]) (Mr := [3]) (by decide) (i := ())
  (by decide) (by decide) (by decide) (by decide) (Or.inl (by
    refine lt_of_le_of_ne ?_ ?_
    · intro r i; fin_cases r <;> cases i <;> decide
    · intro h
      have bad : (0 : ℕ) = 1 := congrFun (congrFun h (pair 0)) ()
      contradiction))

section FirstBlackWeight
private abbrev oneWt : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 0 then 2 else 1)
private def joint : Seq (stendhalWeight 3 β) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inl (),.inr 2] (by decide)
private def exchanged : Seq (stendhalWeight 3 β) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 2,.inl (),.inr 1] (by decide)
private def markedLeft : Seq (stendhalWeight 3 β) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inl (),.inr 1,.inr 2] (by decide)
private def bareRight : Seq (stendhalWeight 3 β) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inr 2,.inl ()] (by decide)
private theorem strictLeft : adjacentBlockRoot 1 2 joint < adjacentBlockRoot 1 2 markedLeft := by
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro he; have bad : (0 : ℕ) = 1 := congrFun (congrFun he 1) (); contradiction

/-- Positive pairings and a left spectator of weight two. The right exit is
not strictly higher, and the left exit is not globally violated. -/
example : adjacentBlockRoot 1 2 bareRight = adjacentBlockRoot 1 2 joint ∧
    ¬IsViolated markedLeft ∧ oneWt 1 () = 1 ∧ oneWt 2 () = 1 := by
  refine ⟨?_,by rintro ⟨_,h⟩; contradiction,by simp [oneWt],by simp [oneWt]⟩
  funext r i; fin_cases r <;> cases i <;> decide

example := firstWeight_blockKernelColumnInclusion_injective () q₄ oneWt 1 2 exchanged joint symm₄

/-- The finite bottom-projector sum assembles the first-weight column tests for
the exchanged red order, including the spectator. -/
example := blockKernelTensorInclusion_injective_of_columns q₄ oneWt joint 1 2
  (redWord exchanged) (fun u _ =>
    firstWeight_blockKernelColumnInclusion_injective () q₄ oneWt 1 2 u joint symm₄)

example := firstWeight_interleavedColumn_presentation () q₄ oneWt 1 2 exchanged 1 joint symm₄
  (by decide) (L := [0]) (M := []) (by decide) (by decide) (by decide) (by decide) (by decide)

example :=
  let g := blockHigherMark q₄ oneWt joint 1 2 markedLeft (by decide) strictLeft
    (ofKLR (ZMod 4) q₄ oneWt β (KLRAlgebra.ψ 1))
  let u := MulOpposite.op (blockSeamWord q₄ oneWt joint [1]) • g
  firstWeight_exit_saturated () q₄ oneWt 1 2 (adjacentBlockRoot 1 2 joint) (redWord joint) bareRight 2
    (by decide) symm₄ (r := 2) (d := ()) (by decide) (by decide) (by decide) u.1.1.1
    ((blockUpperIdeal (ZMod 4) q₄ oneWt β 1 2 (adjacentBlockRoot 1 2 joint) (redWord joint)).mul_mem_right _ _ u.2)

/-- Mark through `c i a b`, then cross to the non-higher joint `c a i b`.
Both exit products factor through the left mark. The conclusion compares
their separately constructed elements of `K ⊗_T B`. -/
example :=
  let g := blockHigherMark q₄ oneWt joint 1 2 markedLeft (by decide) strictLeft
    (ofKLR (ZMod 4) q₄ oneWt β (KLRAlgebra.ψ 1))
  let u := MulOpposite.op (blockSeamWord q₄ oneWt joint [1]) • g
  firstWeight_blockKernel_mixedExit () q₄ oneWt 1 2 exchanged 1 joint (redWord exchanged)
    symm₄ (by decide) (by decide) (by decide) (by decide) (by decide) u.1
    ((blockLoadingKernel q₄ oneWt joint 1 2).smul_mem _ u.2)
    ((blockLoadingKernel q₄ oneWt joint 1 2).smul_mem _ u.2)
end FirstBlackWeight

/-- A spectator black can provide either violation without reversing the
specified `b,i` at positions 2 and 3. This tests the limit of the forced-descent
argument, not failure of the tensor inclusion. -/
private def twoRight : Seq (stendhalWeight 3 (β+β)) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inr 1,.inr 2,.inl (),.inl ()] (by decide)
private abbrev fromRight := TypeA.wordProd (stendhalWeight 3 (β+β)).card
example : IsViolated (fromRight [0,1,2,3] • twoRight) ∧
    ¬fromRight [0,1,2,3] ⟨3,by decide⟩ < fromRight [0,1,2,3] ⟨2,by decide⟩ :=
  ⟨⟨by decide,by decide⟩,by decide⟩
example : adjacentBlockRoot 1 2 twoRight < adjacentBlockRoot 1 2 (fromRight [1,2,3] • twoRight) ∧
    ¬fromRight [1,2,3] ⟨3,by decide⟩ < fromRight [1,2,3] ⟨2,by decide⟩ := by
  refine ⟨lt_of_le_of_ne ?_ ?_,by decide⟩
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro he; have bad : (0 : ℕ) = 1 := congrFun (congrFun he 1) (); contradiction
end KernelTensor
end AdjacentRow

/-- Webster, arXiv:1309.3796v2, Prop. 6.4, for `sl₂`, two red strands of weight `ω` that may
cross, and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.basis (Λ := fun _ : Fin 2 => Finsupp.single () 1) (ν := ν) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)

/-- Webster, arXiv:1309.3796v2, Prop. 6.4 for the bimodule `B̃_w` of the crossing of the two red
strands, for `sl₂` and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.cornerBasis (Λ := fun _ : Fin 2 => Finsupp.single () 1) (ν := ν) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)
    [1, 0] [0, 1]

/-- Webster, arXiv:1309.3796v2, Prop. 4.16 for symmetric `Q`: the Stendhal terms form a basis of
`T̃^λ`, for `sl₂`, two red strands of weight `ω` and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  stendhalBasisOfSymm bsQ (fun _ : Fin 2 => Finsupp.single () 1) (ν := ν) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)

/-- Webster, arXiv:1309.3796v2, Definition 6.3 for `w = e`: `B̃_e ≃ T̃^λ`, for `sl₂`, two red
strands of weight `ω` and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.cornerEquivStendhal (Λ := fun _ : Fin 2 => Finsupp.single () 1)
    (ν := ν) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose) (fun w => (TypeA.exists_reduced _ w).choose_spec)

/-- Webster, arXiv:1309.3796v2, Lemma 6.5 for three red strands of weight `ω`, `sl₂` and every
black weight: `w'` crosses the last two red strands and `w` crosses the first one with the strand
now in the middle, so `ℓ(ww') = ℓ(w) + ℓ(w')` and `B̃_w ⊗ B̃_{w'} ≃ B̃_{ww'}`. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.tensorMultEquivOfPath (Λ := fun _ : Fin 3 => Finsupp.single () 1)
    (ν := ν) (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm
    (κ₂ := [2, 0, 1]) (κ₁ := [0, 2, 1]) (κ₀ := [0, 1, 2])
    (.cross (L := [0]) (M := []) rfl rfl (by decide) (by decide) .refl)

/-- Webster, arXiv:1309.3796v2, Lemma 6.5 with the length condition as inversion sets, for
`sl₂`, three red strands of weight `ω`, `w' = s₁` and `w = s₂ s₁`, and every black weight. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.tensorMult_bijective_of_inversions
    (Λ := fun _ : Fin 3 => Finsupp.single () 1) (ν := ν) (k := ℚ) (Q := bsQ)
    (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm
    (κ₂ := [2, 1, 0]) (κ₁ := [1, 0, 2]) (κ₀ := [0, 1, 2]) (by decide) (by decide) (by decide)

/-- Webster, arXiv:1309.3796v2, Lemma 6.5 for the quotients `B_w` by violated diagrams, in the
same data: multiplication `B_w ⊗ B_{w'} → B_{ww'}` is injective. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_injective
    (Λ := fun _ : Fin 3 => Finsupp.single () 1) (ν := ν) (k := ℚ) (Q := bsQ)
    (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm
    (κ₂ := [2, 1, 0]) (κ₁ := [1, 0, 2]) (κ₀ := [0, 1, 2]) (by decide) (by decide) (by decide)

/-- The same, surjectivity. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_surjective
    (Λ := fun _ : Fin 3 => Finsupp.single () 1) (ν := ν) (k := ℚ) (Q := bsQ)
    (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm
    (κ₂ := [2, 1, 0]) (κ₁ := [1, 0, 2]) (κ₀ := [0, 1, 2]) (by decide) (by decide) (by decide)

/-- Webster, arXiv:1309.3796v2, Proposition 6.7 (the part for `E`, at the level of bimodules over
the quotients by violated diagrams), for `sl₂`, two red strands of weight `ω` and every black
weight: multiplication `βE ⊗ B_w → B_w βE` along the append map is injective. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_injective_append (k := ℚ) bsQ
    (fun _ : Fin 2 => Finsupp.single () 1) () ν bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) [1, 0] [0, 1]

/-- The same, surjectivity. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_surjective_append (k := ℚ) bsQ
    (fun _ : Fin 2 => Finsupp.single () 1) () ν bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) [1, 0] [0, 1]

/-- Webster, arXiv:1309.3796v2, Proposition 6.7 for `𝔉_i` (injectivity, over the opposite
algebras), for `sl₂`, two red strands of weight `ω` and every black weight. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_injective_append_op (k := ℚ) bsQ
    (fun _ : Fin 2 => Finsupp.single () 1) () ν bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) [1, 0] [0, 1]

/-- The same, surjectivity. -/
example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violMk_mult_surjective_append_op (k := ℚ) bsQ
    (fun _ : Fin 2 => Finsupp.single () 1) () ν bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) [1, 0] [0, 1]

/-- Webster, arXiv:1309.3796v2, §6: the quotient bimodule `B_e` is the tensor product algebra
`T^λ` (Definitions 4.6 and 4.7) as rings, for `sl₂`, two red strands of weight `ω` and every
black weight. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violCornerEquiv (Λ := fun _ : Fin 2 => Finsupp.single () 1) (ν := ν)
    (k := ℚ) (Q := bsQ) (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm

/-- Webster, arXiv:1309.3796v2, §6.1: the corner of `B` at the reversed red order
`λ_2, λ_1` is the tensor product algebra of the reordered sequence, for `sl₂`, two red strands of
weight `ω` and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  BraidedStendhalAlgebra.violCornerRedPermTensorEquiv (Λ₀ := fun _ : Fin 2 => Finsupp.single () 1)
    (ν₀ := ν) (k := ℚ) (Q₀ := bsQ) (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) bsSymm (Equiv.swap 0 1)

open scoped DG.DegreeZero in
/-- Webster, arXiv:1309.3796v2, Definition 6.6: the braiding functor `- ⊗ᴸ B(κ', κ)` for
`sl₂`, two red strands of weight `ω` in either order, and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [0, 1]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [1, 0]).Cornerᵐᵒᵖ
  BraidedStendhalAlgebra.braidingFunctor ℚ bsQ (fun _ : Fin 2 => Finsupp.single () 1) ν
    [0, 1] [1, 0]

private theorem bsRouquier :
    KLR.IsRouquierQ (QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) bsQ where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

open scoped DG.DegreeZero in
/-- Webster, arXiv:1309.3796v2, Proposition 6.7 for `𝔈_i`: `𝔈_i ∘ 𝔅(κ', κ) ≅ 𝔅(κ', κ) ∘ 𝔈_i`,
for `sl₂`, two red strands of weight `ω` in either order, and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ({()} + ν) [0, 1]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ({()} + ν) [1, 0]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [0, 1]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [1, 0]).Cornerᵐᵒᵖ
  BraidedStendhalAlgebra.braidingFunctorCompAppendFunctorIso
    (Λ := fun _ : Fin 2 => Finsupp.single () 1) (i := ()) (ν := ν) (κ' := [1, 0]) (κ := [0, 1])
    (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (ρ' := fun w => (TypeA.exists_reduced _ w).choose) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose_spec)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) _ bsRouquier (by decide)

open scoped DG.DegreeZero in
/-- Webster, arXiv:1309.3796v2, Proposition 6.7 for `𝔉_i`: `𝔉_i ∘ 𝔅(κ', κ) ≅ 𝔅(κ', κ) ∘ 𝔉_i`,
for `sl₂`, two red strands of weight `ω` in either order, and every black weight. -/
noncomputable example (ν : Multiset Unit) :=
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ({()} + ν) [0, 1]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ({()} + ν) [1, 0]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [0, 1]).Cornerᵐᵒᵖ
  letI := DG.HasDerivedCategory.standard
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj ℚ bsQ
      (fun _ : Fin 2 => Finsupp.single () 1) ν [1, 0]).Cornerᵐᵒᵖ
  BraidedStendhalAlgebra.braidingFunctorCompAppendFunctorOpIso
    (Λ := fun _ : Fin 2 => Finsupp.single () 1) (i := ()) (ν := ν) (κ' := [1, 0]) (κ := [0, 1])
    (ρ := fun w => (TypeA.exists_reduced _ w).choose)
    (ρ' := fun w => (TypeA.exists_reduced _ w).choose) bsSymm
    (fun w => (TypeA.exists_reduced _ w).choose_spec)
    (fun w => (TypeA.exists_reduced _ w).choose_spec) _ bsRouquier (by decide)

open scoped DG.DegreeZero in
/-- The derived tensor product with an ordinary bimodule (Webster, arXiv:1309.3796v2,
Definition 6.6), for `ℤ` acting on itself. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard ℤ
  derivedTensor ℤ ℤ ℤ

open scoped DG.DegreeZero in
/-- A projective module in degree zero is K-projective (input to Webster, arXiv:1309.3796v2,
proof of Proposition 6.7), for `ℚ` over itself. -/
example : DG.IsKProjective.{0} ℚ (InDegreeZero ℚ) := InDegreeZero.isKProjective (A := ℚ)

open scoped DG.DegreeZero in
/-- Derived tensor products compose when the inner bimodule is K-projective over its target
(input to Webster, arXiv:1309.3796v2, proof of Proposition 6.7), for `ℚ` acting on itself. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard ℚ
  dgDerivedTensorCompIso (A := ℚ) (B := ℚ) (C := ℚ) (InDegreeZero ℚ)
    (InDegreeZero.isKProjective (A := ℚ) (M := ℚ))

open scoped DG.DegreeZero in
/-- Tensoring with a projective module in degree zero preserves acyclicity (input to Webster,
arXiv:1309.3796v2, proof of Proposition 6.7), over the zero ring, where every dg module is
acyclic. -/
example : DG.IsAcyclic
    (DG.TensorProductOver (ZMod 1) (InDegreeZero (ZMod 1)) (InDegreeZero (ZMod 1))) :=
  InDegreeZero.isAcyclic_tensorProductOver (B := ZMod 1) (P := ZMod 1)
    (fun n => ⟨fun a b => by
      induction a using DG.cohomology.induction_on with | h x =>
      induction b using DG.cohomology.induction_on with | h y =>
      rw [Subtype.ext (Subsingleton.elim (α := ZMod 1) x.1 y.1)]⟩)

open scoped DG.DegreeZero in
/-- Tensoring with a projective module in degree zero preserves quasi-isomorphisms (input to
Webster, arXiv:1309.3796v2, proof of Proposition 6.7), for the identity of `ℚ`. -/
example : (DG.DGModuleHom.lTensor ℚ (InDegreeZero ℚ)
    (DG.DGModuleHom.id : InDegreeZero ℚ →ᵈᵍ[ℚ] InDegreeZero ℚ)).IsQuasiIso :=
  haveI : Module.Free ℚᵐᵒᵖ ℚ := Module.Free.of_equiv (MulOpposite.opLinearEquiv ℚᵐᵒᵖ).symm
  InDegreeZero.isQuasiIso_lTensor (A := ℚ) (B := ℚ) (P := ℚ) DG.DGModuleHom.isQuasiIso_id

open scoped DG.DegreeZero in
/-- The derived tensor product with a bimodule projective over its source is computed without
resolutions (input to Webster, arXiv:1309.3796v2, proof of Proposition 6.7), for `ℚ` acting on
itself. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard ℚ
  haveI : Module.Free ℚᵐᵒᵖ ℚ := Module.Free.of_equiv (MulOpposite.opLinearEquiv ℚᵐᵒᵖ).symm
  QCompDerivedTensorIso ℚ ℚ ℚ

open scoped DG.DegreeZero in
/-- Derived tensor products compose without a second resolution when the outer bimodule is
projective over its source (input to Webster, arXiv:1309.3796v2, proof of Proposition 6.7), for
`ℚ` acting on itself. -/
noncomputable example :=
  letI := DG.HasDerivedCategory.standard ℚ
  haveI : Module.Free ℚᵐᵒᵖ ℚ := Module.Free.of_equiv (MulOpposite.opLinearEquiv ℚᵐᵒᵖ).symm
  derivedTensorCompIsoOfProjective (A := ℚ) (B := ℚ) (C := ℚ) ℚ ℚ

end NonVacuity.BraidedStendhal

namespace NonVacuity.WebsterBlockShuffle

open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open RedBlock

private def pair : Fin 2 ↪ Fin 3 := ⟨Fin.succ, Fin.succ_injective _⟩
private abbrev L : List (Fin 3 × Multiset Bool) := [(0,{false})]
private abbrev M : List (Fin 3 × Multiset Bool) := []
private abbrev β : Multiset Bool := {true}
private abbrev row := adjacentRow L M pair β
private theorem wt : weightSum row = stendhalWeight 3 ({false}+β) := by decide
private def localWords : Loadings row :=
  ⟨KLRAlgebra.Seq.ofList [.inr 0,.inl false] (by decide),
   KLRAlgebra.Seq.ofList [.inl true,.inr 0,.inr 1] (by decide),PUnit.unit⟩
private def good : Loadings row :=
  ⟨localWords.1,KLRAlgebra.Seq.ofList [.inr 0,.inl true,.inr 1] (by decide),PUnit.unit⟩
private def interleaved : Seq (weightSum row) :=
  KLRAlgebra.Seq.ofList [.inr 0,.inl true,.inl false,.inr 1,.inr 2] (by decide)
private theorem matched : ShuffleLoading row interleaved localWords := by
  refine ⟨⟨sadj _ 1, ?_⟩, place _ localWords.2, ?_,
    ⟨⟨1, isShuffle_one _⟩, Seq.nil, one_smul _ _, trivial⟩⟩
  · constructor <;> intro a b h <;> fin_cases a <;> fin_cases b <;>
      first | exact False.elim (absurd h (by decide)) | decide
  · apply Subtype.ext; funext x; fin_cases x <;> decide

example : ¬ IsViolated interleaved := by rintro ⟨_,h⟩; contradiction
/-- An interleaving swaps two differently coloured black strands; the first comes from
the paired block, leaving the global leftmost strand red but raising its retained cut. -/
example : Violated row localWords := by
  have order : redWord (Seq.cast wt interleaved) =
      L.map Prod.fst ++ pair 0 :: pair 1 :: M.map Prod.fst := by decide
  apply violated_of_adjacent_shuffleLoading L M pair β wt interleaved localWords matched order
  right
  have aligned := aligned_adjacent L M pair β (order ▸ redWord_nodup _)
  have ok : ¬ Violated row good := by rintro (⟨_,h⟩ | ⟨_,h⟩ | h) <;> contradiction
  have boundary : (fun r i => boundaryCount (cut (pair 0) (pair 1) r) i row) =
      adjacentBlockRoot (pair 0) (pair 1) (Seq.cast wt (place row good)) := by
    funext r i
    exact (count_place_of_not_violated r i good aligned ok).symm
  rw [boundary]
  refine lt_of_le_of_ne ?_ ?_
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro eq
    have bad : (0 : ℕ) = 1 := congrFun (congrFun eq 1) true
    contradiction
private noncomputable abbrev Q : Bool → Bool → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

example := exists_blockStack_quotient_coordinates Q (fun _ => Finsupp.single false 1)
  L M pair β (fun _ _ _ => rfl) wt

example := exists_blockStack_filtered_quotient_coordinates Q (fun _ => Finsupp.single false 1)
  L M pair β (fun _ _ _ => rfl) wt

example := exists_blockColumn_coordinate_embedding Q (fun _ => Finsupp.single false 1)
  L M pair β (fun _ _ _ => rfl) wt

end NonVacuity.WebsterBlockShuffle

namespace NonVacuity.WebsterLoadingPlacement
open Categorification.Stendhal Categorification.Stendhal.RedBlock Categorification.KLR

private abbrev ν : Multiset Unit := {(), (), (), ()}
private def t : Seq (stendhalWeight 4 ν) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl (), .inr 1, .inl (), .inr 2, .inl (), .inr 3, .inl ()]
    (by decide)
private def pair : Fin 2 ↪ Fin 4 where
  toFun i := ⟨i.val + 1, by omega⟩
  inj' i j h := Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))
private theorem ht : ¬ IsViolated t := by
  rintro ⟨hp, hb⟩
  have he : t.lbl ⟨0, hp⟩ = .inr 0 := rfl
  simp [he] at hb
private theorem ho : redWord t = [0] ++ pair 0 :: pair 1 :: [3] := by decide

example := exists_place_adjacent t ht [0] [3] pair ho

end NonVacuity.WebsterLoadingPlacement

namespace NonVacuity.WebsterBraidReflection

open Categorification.Stendhal.BraidedStendhalAlgebra MulOpposite

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 2 → Unit →₀ ℕ :=
  fun j => Finsupp.single () (j.val + 1)
private abbrev ν : Multiset Unit := 0

example (a : (isIdempotentElem_violMk_redProj ℚ Q Λ ν [0, 1]).Corner)
    (b : (isIdempotentElem_violMk_redProj ℚ Q Λ ν [1, 0]).Cornerᵐᵒᵖ)
    (x : braidingBimodule ℚ Q Λ ν [0, 1] [1, 0]) :
    braidingBimoduleFlip [0, 1] [1, 0] (a • x) =
      op (cornerFlip a) • braidingBimoduleFlip [0, 1] [1, 0] x ∧
    braidingBimoduleFlip [0, 1] [1, 0] (b • x) =
      cornerFlip b.unop • braidingBimoduleFlip [0, 1] [1, 0] x :=
  ⟨braidingBimoduleFlip_smul_left [0, 1] [1, 0] a x,
    braidingBimoduleFlip_smul_right [0, 1] [1, 0] b x⟩

end NonVacuity.WebsterBraidReflection

/-! ### Webster, Lemma 6.8 after (6.21), polynomial kernel of two distinct exits -/

noncomputable section
open Categorification.KLR Categorification.TypeA Equiv MvPolynomial
open KLRAlgebra
namespace NonVacuity.ExitPolynomialMatrix

private abbrev ν : Multiset (Fin 3) := {2, 0, 0, 1}
private def Q (a b : Fin 3) : MvPolynomial (Fin 2) ℤ :=
  if a = b then 0 else if a = 0 then X 0 else if b = 0 then X 1 else 1
private theorem hQ : KLRSymm Q := by
  intro a b h
  unfold Q
  rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all
private abbrev P := MvPolynomial (Fin ν.card) ℤ
private abbrev R := KLRAlgebra ℤ Q ν
private def s : Seq ν := KLRAlgebra.Seq.ofList [2, 0, 0, 1] (by decide)
private def middle : List ℕ := [1, 0, 2]
private def w := wordProd ν.card middle
private def ρ (t : Perm (Fin ν.card)) := if t = w then middle else canWord ν.card t
private theorem hw : ρ w = middle := ite_eq_left rfl
private theorem hρ (t) : IsReduced ν.card (ρ t) ∧ wordProd ν.card (ρ t) = t := by
  by_cases h : t = w
  · subst t; rw [hw]
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · simp [ValidWord, middle]
    · rw [length_eq_invCount]; decide
  · simpa only [ρ, ite_eq_right h] using And.intro (isReduced_canWord ν.card t) (wordProd_canWord _ t)
private def leftPos : Fin ν.card := ⟨0, by decide⟩
private theorem blackDot : twoBlackExitPolynomial Q s 0 (by decide) = X leftPos := by
  have ha : (wordProd ν.card [2] • s).lbl ⟨1, by decide⟩ = 0 := by decide
  have hb : (wordProd ν.card [2] • s).lbl ⟨2, by decide⟩ = 1 := by decide
  unfold twoBlackExitPolynomial exitSquarePolynomial
  dsimp only
  rw [ha, hb, ite_eq_right (by decide : (0 : Fin 3) ≠ 1)]
  change rename _ (rename _ (rename _ (X (0 : Fin 2)))) = X leftPos
  simp only [rename_X]
  congr 1
private def upper : Fin 2 → List ℕ := ![[0, 1], []]
private def leg : Fin 2 → List ℕ := ![[0, 1, 2], middle]

example (a : Fin 2 → R) :
    (∑ j : Fin 2, a j * (ψw (leg j) * e s)) = 0 ↔
      ∀ t : Perm (Fin ν.card), (∑ j : Fin 2, ∑ u : Perm (Fin ν.card),
        exitPolynomial hQ ρ hρ (wordProd ν.card (leg j) • s) u (a j) *
          exitPolynomial hQ ρ hρ s t (ψw (ρ u ++ leg j) * e s)) = 0 :=
  exit_relation_polynomial_matrix_iff hQ ρ hρ Finset.univ s leg a

-- At [red, black, black, red] with the two black labels equal, the reduced upper
-- word on the extreme exit and the bare middle exit have polynomial columns
-- X₀ and 1 in the row indexed by w. Every other row vanishes.
example (f : Fin 2 → P) :
    (∑ a : Fin 2, (pol (f a) * ψw (upper a) * e (wordProd ν.card (leg a) • s)) * (ψw (leg a) * e s) : R) = 0 ↔
      f 0 * X leftPos + f 1 = 0 := by
  rw [exit_polynomial_matrix_iff hQ ρ hρ Finset.univ s upper leg f]
  have extreme := twoBlack_extreme_middle (Q := Q) s 0 (by decide) (by decide) (by decide) (by decide)
  rw [blackDot] at extreme
  have plain (t) := exitPolynomial_normal hQ ρ hρ s s t w (1 : P)
  simp only [hw, map_one, one_mul, true_and] at plain
  simp only [Fin.sum_univ_two]
  change (∀ t, f 0 * exitPolynomial hQ ρ hρ s t (ψw ([0, 1] ++ [0, 1, 2]) * e s) +
    f 1 * exitPolynomial hQ ρ hρ s t (ψw middle * e s) = 0) ↔ _
  rw [extreme]
  change (∀ t, f 0 * exitPolynomial hQ ρ hρ s t (pol (X leftPos) * (ψw middle * e s)) +
    f 1 * exitPolynomial hQ ρ hρ s t (ψw middle * e s) = 0) ↔ _
  simp only [exitPolynomial_pol_mul, plain]
  constructor
  · intro h; simpa only [ite_true, mul_one] using h w
  · intro h t; by_cases ht : w = t <;> simp [ht, h]

end NonVacuity.ExitPolynomialMatrix
end

/-! ### Webster, Lemma 6.8 after (6.21), coupled equal-black return columns -/

noncomputable section
open Categorification Categorification.KLR Categorification.TypeA Equiv MvPolynomial
open KLRAlgebra
namespace NonVacuity.EqualBlackReturns

private abbrev I := Unit ⊕ Bool
private abbrev black : I := .inl ()
private abbrev a : I := .inr false
private abbrev b : I := .inr true
private abbrev ν : Multiset I := {b, black, black, a}
private def Q (i j : I) : MvPolynomial (Fin 2) ℤ :=
  if i = j then 0 else if i = black then X 0 else if j = black then X 1 else 1
private theorem hQ : KLRSymm Q := by
  intro i j h
  unfold Q
  rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  by_cases hi : i = black <;> by_cases hj : j = black <;> simp_all
private abbrev P := MvPolynomial (Fin ν.card) ℤ
private abbrev R := KLRAlgebra ℤ Q ν
private def s : Seq ν := KLRAlgebra.Seq.ofList [b, black, black, a] (by decide)
private def l : List ℕ := [0, 1, 2]
private abbrev x₂ : Fin ν.card := ⟨2, by decide⟩
private abbrev x₃ : Fin ν.card := ⟨3, by decide⟩
private theorem weight : exitSquarePolynomial Q (wordProd ν.card l • s) 1 (by decide) = X x₂ := by
  have hb : (wordProd ν.card l • s).lbl ⟨1, by decide⟩ = b := by decide
  have hi : (wordProd ν.card l • s).lbl ⟨2, by decide⟩ = black := by decide
  unfold exitSquarePolynomial
  dsimp only
  rw [hb, hi, ite_eq_right (by decide : b ≠ black)]
  change rename _ (X (1 : Fin 2)) = X x₂
  rw [rename_X]
  rfl
private theorem redL : IsReduced ν.card l := by
  refine ⟨?_, ?_⟩
  · simp [ValidWord, l]
  · rw [length_eq_invCount]; decide
private theorem redJL : IsReduced ν.card (2 :: l) := by
  refine ⟨?_, ?_⟩
  · simp [ValidWord, l]
  · rw [length_eq_invCount]; decide

-- The two right-extreme joint maps are ψ₁ and ψ₁ψ₂. Their three return
-- columns have polynomial kernel generated by (1, −X₂, X₃).
private theorem returns (f g h : P) :
    (pol f * (ψw (1 :: 1 :: l) * e s) + pol g * (ψw (2 :: 1 :: 1 :: l) * e s) +
      pol h * (ψw (1 :: 1 :: 2 :: l) * e s) : R) = 0 ↔
      g = -(f * X x₂) ∧ h = f * X x₃ := by
  have matrix := equalBlack_return_kernel hQ s l 1 2 1 (by decide) (by decide) redL redJL
    (by decide) (by simpa only [pow_one] using weight) f g h
  have ddx : NilHecke.dd ℤ ν.card 2 (X x₂) = (1 : P) := by
    rw [NilHecke.dd_of_lt (by decide : 2 + 1 < ν.card)]
    exact ddiff_X_left (by decide : x₂ ≠ x₃)
  change ( _ = 0 ↔ ∃ z : P, f = z * NilHecke.dd ℤ ν.card 2 (X x₂ ^ 1) ∧
    g = -(z * X x₂ ^ 1) ∧ h = z * X x₃ ^ 1) at matrix
  simpa only [pow_one, ddx, mul_one, exists_eq_left'] using matrix

/-- The generator has a single common coefficient at the full joint. -/
example :
    let t := sadj ν.card 1 • (wordProd ν.card l • s)
    ∃ c : R, c * e (sadj ν.card 2 • t) = c ∧
      c * (ψw [1, 2] * e t) = -(pol (1 : P) * (ψw [1] * e t) +
        pol (-X x₂) * (ψw [2, 1] * e t)) ∧
      c * (ψw [2] * e t) = pol (X x₃) * (ψw [1] * e t) := by
  have hb : (wordProd ν.card l • s).lbl ⟨1, by decide⟩ = b := by decide
  have hi : (wordProd ν.card l • s).lbl x₂ = black := by decide
  apply exists_equalBlack_cycle_coefficient hQ s l 1 1 (by decide) redL redJL (by decide) (by decide)
  · rw [hb, hi, pow_one]
    rfl
  · apply (returns 1 (-X x₂) (X x₃)).2
    simp only [one_mul, and_self]

/-- The fourth return contributes the second independent polynomial relation. -/
example (f g h i : P) :
    (pol f * (ψw (1 :: 1 :: l) * e s) + pol g * (ψw (2 :: 1 :: 1 :: l) * e s) +
      pol h * (ψw (1 :: 1 :: 2 :: l) * e s) + pol i * (ψw (2 :: 1 :: 1 :: 2 :: l) * e s) : R) = 0 ↔
      ∃ u v : P, f = u ∧ g = -(u * X x₂) ∧ h = u * X x₃ + v ∧ i = -(v * X x₂) := by
  have kernel := equalBlack_four_return_kernel hQ s l 1 2 1 (by decide) (by decide) redL redJL
    (by decide) (by simpa only [pow_one] using weight) f g h i
  have ddx : NilHecke.dd ℤ ν.card 2 (X x₂) = (1 : P) := by
    rw [NilHecke.dd_of_lt (by decide : 2 + 1 < ν.card)]
    exact ddiff_X_left (by decide : x₂ ≠ x₃)
  dsimp only at kernel
  simpa only [pow_one, ddx, mul_one] using kernel

end NonVacuity.EqualBlackReturns
end

/-! ### Webster, Lemma 6.8 after (6.21), nonzero overlap after killing red dots -/

noncomputable section
open Categorification Categorification.KLR Categorification.Stendhal Categorification.TypeA MvPolynomial
namespace NonVacuity.BraidedEqualBlackReturns

private abbrev ν : Multiset Unit := {(), ()}
private abbrev μ := stendhalWeight 2 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private def Λ : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private abbrev π := BraidedStendhalAlgebra.ofKLR ℤ Q Λ ν
private abbrev P := MvPolynomial (Fin μ.card) ℤ
private def s : Seq μ := KLR.KLRAlgebra.Seq.ofList [.inr 1, .inl (), .inl (), .inr 0] (by decide)
private def l : List ℕ := [0, 1, 2]
private abbrev x₂ : Fin μ.card := ⟨2, by decide⟩
private abbrev x₃ : Fin μ.card := ⟨3, by decide⟩
private def black := Stendhal.KLRAlgebra.blackSubst (k := ℤ) (wordProd μ.card l • s)
private theorem black₂ : black (X x₂) = X x₂ := by
  unfold black; rw [Stendhal.KLRAlgebra.blackSubst_X, ite_eq_left (by decide)]
private theorem black₃ : black (X x₃) = X x₃ := by
  unfold black; rw [Stendhal.KLRAlgebra.blackSubst_X, ite_eq_left (by decide)]
private abbrev R := KLR.KLRAlgebra ℤ (stendhalQ Q Λ) μ
private abbrev plain : R := KLR.KLRAlgebra.ψw (1 :: 1 :: l) * KLR.KLRAlgebra.e s
private abbrev blackAbove : R := KLR.KLRAlgebra.ψw (2 :: 1 :: 1 :: l) * KLR.KLRAlgebra.e s
private abbrev blackBelow : R := KLR.KLRAlgebra.ψw (1 :: 1 :: 2 :: l) * KLR.KLRAlgebra.e s
open KLR.KLRAlgebra

private theorem symmQ : KLRSymm Q := fun _ _ h => False.elim (h (Subsingleton.elim _ _))
private theorem cardμ : μ.card = 4 := by decide
private theorem rl : IsReduced μ.card l := by
  rw [cardμ]
  refine ⟨?_, ?_⟩
  · simp [ValidWord, l]
  · rw [length_eq_invCount]; decide
private theorem rjl : IsReduced μ.card (2 :: l) := by
  rw [cardμ]
  refine ⟨?_, ?_⟩
  · simp [ValidWord, l]
  · rw [length_eq_invCount]; decide
private theorem hred : (wordProd μ.card l • s).lbl ⟨1, by decide⟩ = Sum.inr 1 := by decide
private theorem hi : (wordProd μ.card l • s).lbl x₂ = Sum.inl () := by decide
private theorem hi' : (wordProd μ.card l • s).lbl x₃ = Sum.inl () := by decide
private theorem n : Λ 1 () = 1 := by simp [Λ]
private theorem relation (f g h : P) :
    π (pol f * plain + pol g * blackAbove + pol h * blackBelow) = 0 ↔
      black g = -(black f * X x₂) ∧ black h = black f * X x₃ := by
  have eq := BraidedStendhalAlgebra.equalBlack_return_kernel (Λ := Λ) symmQ s l 1
    (by decide) rl rjl 1 () hred hi hi' f g h
  dsimp only at eq
  rw [n] at eq
  have ddx : NilHecke.dd ℤ μ.card 2 (X x₂) = (1 : P) := by
    rw [NilHecke.dd_of_lt (by decide : 2 + 1 < μ.card)]
    exact ddiff_X_left (by decide : x₂ ≠ x₃)
  change (_ = 0 ↔ ∃ z : P, black f = z * NilHecke.dd ℤ μ.card 2 (X x₂ ^ 1) ∧
    black g = -(z * X x₂ ^ 1) ∧ black h = z * X x₃ ^ 1) at eq
  simpa only [pow_one, ddx, mul_one, exists_eq_left'] using eq

-- The two joint arms have a nonzero common element after killing red dots.
-- The black-below term equals a combination of two black-above returns.
example : π (pol (X x₃) * blackBelow) ≠ 0 ∧
    π (pol (X x₃) * blackBelow) = -π (plain - pol (X x₂) * blackAbove) := by
  have oneRel := (relation 1 (-X x₂) (X x₃)).2 (by simp only [map_neg, map_one, black₂, black₃, one_mul, and_self])
  have nonzero := (relation 0 0 (X x₃)).1
  constructor
  · intro he
    have hz : π (pol (0 : P) * plain + pol (0 : P) * blackAbove + pol (X x₃) * blackBelow) = 0 := by
      simpa only [map_zero, zero_mul, add_zero, zero_add] using he
    have eq := (nonzero hz).2
    rw [black₃, map_zero, zero_mul] at eq
    exact X_ne_zero x₃ eq
  · rw [map_one, one_mul, map_neg, neg_mul, ← sub_eq_add_neg, map_add] at oneRel
    exact eq_neg_of_add_eq_zero_right oneRel

/-- The nonzero overlap is induced by one coefficient in the red-dot quotient. -/
example :
    let t := sadj μ.card 1 • (wordProd μ.card l • s)
    ∃ c, c * π (e (sadj μ.card 2 • t)) = c ∧
      c * π (ψw [1, 2] * e t) = -π (pol (1 : P) * (ψw [1] * e t) +
        pol (-X x₂) * (ψw [2, 1] * e t)) ∧
      c * π (ψw [2] * e t) = π (pol (X x₃) * (ψw [1] * e t)) := by
  apply BraidedStendhalAlgebra.exists_equalBlack_cycle_coefficient (Λ := Λ) symmQ s l 1
    (by decide) rl rjl 1 () hred hi hi'
  apply (relation 1 (-X x₂) (X x₃)).2
  simp only [map_neg, map_one, black₂, black₃, one_mul, and_self]

private theorem onlyTwo : ∀ w : Equiv.Perm (Fin μ.card),
    w • (sadj μ.card 1 • (wordProd μ.card l • s)) = wordProd μ.card l • s ↔
      w = wordProd μ.card [1] ∨ w = wordProd μ.card [2, 1] :=
  BraidedStendhalAlgebra.twoBlack_return_permutations_of_card_two _ 1 (by decide) (by decide) () hi hi'

-- An extra exterior red keeps the two return permutations at the shifted joint.
private def spectatorTop : Seq (stendhalWeight 3 ν) :=
  KLR.KLRAlgebra.Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inl ()] (by decide)
example (w : Equiv.Perm (Fin (stendhalWeight 3 ν).card)) :
    w • (sadj (stendhalWeight 3 ν).card 2 • spectatorTop) = spectatorTop ↔
      w = wordProd (stendhalWeight 3 ν).card [2] ∨ w = wordProd (stendhalWeight 3 ν).card [3, 2] :=
  BraidedStendhalAlgebra.twoBlack_return_permutations_of_card_two spectatorTop 2 (by decide) (by decide) ()
    (by decide) (by decide) w

/-- Arbitrary upper elements at the four-strand extreme have a common full-joint
coefficient, including after imposing the red-dot relations. -/
example (x y : BraidedStendhalAlgebra ℤ Q Λ ν) :
    let r := wordProd μ.card l • s
    let t := sadj μ.card 1 • r
    π (e r) * x = x → x * π (e t) = x → π (e r) * y = y → y * π (e t) = y →
    x * π (ψw (1 :: l) * e s) + y * π (ψw (1 :: 2 :: l) * e s) = 0 →
    ∃ c, c * π (e (sadj μ.card 2 • t)) = c ∧ c * π (ψw [1, 2] * e t) = -x ∧
      c * π (ψw [2] * e t) = y :=
  BraidedStendhalAlgebra.exists_equalBlack_corner_cycle_coefficient symmQ s l 1 (by decide) rl rjl
    1 () hred hi hi' onlyTwo x y

end NonVacuity.BraidedEqualBlackReturns
end

namespace NonVacuity.WebsterIntervalConcat

open Categorification.KLR Categorification.KLR.KLRAlgebra Categorification.TypeA
open MvPolynomial
open scoped TensorProduct

private abbrev L : Multiset Bool := {false}
private abbrev M : Multiset Bool := {false, true}
private abbrev R : Multiset Bool := {true}
private def l : Seq L := Seq.ofList [false] rfl
private def s : Seq M := Seq.ofList [false, true] rfl
private def r : Seq R := Seq.ofList [true] rfl
private noncomputable def params : Bool → Bool → MvPolynomial (Fin 2) ℤ := fun _ _ => 1

example :
    intervalConcat params l r (ψw [0] * pol (MvPolynomial.X (⟨0, by decide⟩ : Fin M.card)) * e s) =
      ψw [1] * pol (rename (Seq.posR L ∘ Seq.posL R) (MvPolynomial.X (⟨0, by decide⟩ : Fin M.card))) *
        e (l.append (s.append r)) := by
  rw [intervalConcat_apply, concat_interval_ψw_pol_e _ (show ValidWord M.card [0] by simp [ValidWord])]
  rfl

example := range_intervalConcat_eq_span params (by intro a b _; simp [params]) l r
  (canWord M.card) (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)

example (x y : KLRAlgebra ℤ params M) :
    intervalConcat params l r (x * y) = intervalConcat params l r x * intervalConcat params l r y :=
  intervalConcat_mul params l r x y

example : Function.Injective (intervalConcat (β := M) params l r) :=
  intervalConcat_injective params (by intro a b _; simp [params]) l r

end NonVacuity.WebsterIntervalConcat

namespace NonVacuity.WebsterBraidFiltration

open Categorification Categorification.KLR Categorification.Stendhal
  Categorification.Stendhal.BraidedStendhalAlgebra ModuleFiltration MulOpposite

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev Λ : Fin 0 → Unit →₀ ℕ := Fin.elim0
private abbrev ν : Multiset Unit := 0
private abbrev μ := stendhalWeight 0 ν
private theorem card_eq : μ.card = 0 := by simp [μ, stendhalWeight]
private def s : Seq μ := KLRAlgebra.Seq.ofList [] (by simp [μ, stendhalWeight])

private def label : {t : Seq μ // redWord t = [] ∧ ¬ IsViolated t} :=
  ⟨s, by simp [redWord, card_eq], by simp [IsViolated, card_eq]⟩

local notation "C" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := Λ) (ν := ν) []
set_option quotPrecheck false in
local notation "B" => ↥(braidingBimodule ℚ Q Λ ν [] [])
set_option quotPrecheck false in
local notation "S" t:arg => ViolLoadingStandard (k := ℚ) (Q := Q) (Λ := Λ) t []

private theorem rightFiltration :
    HasFiltration (fun t => ModuleCat.of Cᵐᵒᵖ (S t.val)) [label] (ModuleCat.of Cᵐᵒᵖ B) := by
  classical
  have hu (t : Seq μ) : t = s := Subtype.ext (funext (fun i => Fin.elim0 (Fin.cast card_eq i)))
  have hr : redWord s = [] := label.property.1
  have hF : Finset.univ.filter (fun t : Seq μ => redWord t = []) = {s} := by
    ext t
    rw [hu t]
    simp [hr]
  have hp : redProj ℚ Q Λ ν [] = ofKLR ℚ Q Λ ν (KLRAlgebra.e s) := by
    rw [redProj, redIdem, hF, Finset.sum_singleton]
  let e : B ≃ₗ[Cᵐᵒᵖ] violCorner ℚ Q Λ ν s [] :=
    { toFun x := ⟨x.val, mem_violCorner_iff.2 ⟨by rw [← hp]; exact x.property.1, x.property.2⟩⟩
      invFun y := ⟨y.val, ⟨by rw [hp]; exact (mem_violCorner_iff.1 y.property).1,
        (mem_violCorner_iff.1 y.property).2⟩⟩
      left_inv x := Subtype.ext rfl
      right_inv x := Subtype.ext rfl
      map_add' x y := Subtype.ext rfl
      map_smul' a x := Subtype.ext rfl }
  have ht : violStandardUpper (k := ℚ) (Q := Q) (Λ := Λ) s [] = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro y ⟨t, a, hκ, hlt, hy⟩
    exact (hlt.2 (fun r => Fin.elim0 r)).elim
  exact HasFiltration.single (c := label) (e.trans (Submodule.quotEquivOfEqBot _ ht).symm)

/-- Reflection transports the one-step filtration at the empty loading. -/
noncomputable example :=
  hasReflectedStandardFiltration_braidingBimodule [] [] rightFiltration

end NonVacuity.WebsterBraidFiltration

namespace NonVacuity.WebsterKernelTrace

open Categorification.ModuleFiltration

private def labels : Bool → ModuleCat.{0} ℤ
  | false => HasFiltration.zeroObj
  | true => ModuleCat.of ℤ ℤ

private instance : Subsingleton (labels false) := by
  change Subsingleton PUnit
  infer_instance

private theorem filtration : HasFiltration labels ([false] ++ [true]) (labels true) := by
  refine HasFiltration.cons (X := labels true) (Z := labels false) LinearMap.id 0 [true] false
    (fun _ _ h => h) ?_ (fun z => ⟨0, Subsingleton.elim _ z⟩)
    (HasFiltration.single (LinearEquiv.refl ℤ _)) ⟨LinearEquiv.refl ℤ _⟩
  intro y
  exact ⟨fun _ => ⟨y, rfl⟩, fun _ => rfl⟩

example : HasFiltration labels [true]
    (ModuleCat.of ℤ (idempotentTrace {1} (labels true))) := by
  apply filtration.idempotentTrace {1}
  · intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    exact one_mul _
  · intro c hc e he x
    simp only [List.mem_singleton] at hc
    subst c
    exact Subsingleton.elim _ _
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    refine le_antisymm le_top fun x _ => ?_
    exact Submodule.subset_span ⟨1, rfl, x, (one_smul ℤ x).symm⟩

end NonVacuity.WebsterKernelTrace

/-- For two positive-weight reds and a zero-weight spectator, the loading kernel
has one higher partial standard layer for the black before the spectator. -/
example :=
  Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack.kernel_hasHigherFiltration
    (k := ℚ) (fun _ _ => 0)
    (fun r => if r = 2 then 0 else Finsupp.single () 1) (by decide)

/-- The higher partial standard is nonzero when the spectator is also positive. -/
example :=
  Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack.higherPartialStandard_nontrivial
    (k := ℚ) (fun _ _ => 0) (fun _ => Finsupp.single () 1) (fun _ _ _ => rfl)
    (fun _ => by simp)

/-- The higher projective surjects onto the kernel at strictly positive weight. -/
example :=
  Stendhal.BraidedStendhalAlgebra.ThreeRedOneBlack.higherCrossingMap_surjective
    (k := ℚ) (fun _ _ => 0) (fun _ => Finsupp.single () 1)

namespace NonVacuity.WebsterTwoBlackExits

open KLR KLRAlgebra

private abbrev colour := Fin 1 ⊕ Fin 2
private abbrev labels : List colour := [.inr 0, .inl 0, .inl 0, .inr 1]
private def loading : Seq (labels : Multiset colour) := Seq.ofList labels rfl

private noncomputable def Q : colour → colour → MvPolynomial (Fin 2) ℚ :=
  Stendhal.stendhalQ (fun _ _ => 0) (fun _ => Finsupp.single 0 1)

example :
    (ψw [0, 1, 2, 1, 0] * e loading : KLRAlgebra ℚ Q (labels : Multiset colour)) =
      ψw [2, 0, 1, 2, 0] * e loading ∧
    (ψw [2, 1, 0, 1, 2] * e loading : KLRAlgebra ℚ Q (labels : Multiset colour)) =
      ψw [2, 0, 1, 2, 0] * e loading := by
  have bounds : 0 + 3 < (labels : Multiset colour).card := by decide
  have colours : loading.lbl ⟨0, by decide⟩ ≠ loading.lbl ⟨0 + 3, bounds⟩ := by
    change (Sum.inr 0 : colour) ≠ Sum.inr 1
    decide
  exact twoBlackExitWords (Q := Q) 0 bounds loading colours

/-- The planar neighboring joints retain one black strand between the reds. -/
example :=
  twoBlackNearbyExitWords (Q := Q) 0 (by decide) loading
    (show (Sum.inr 0 : colour) ≠ Sum.inr 1 by decide)

/-- Reversing the two middle black strands gives an additional exit whose
comparisons with the two extremes still hold for equal black colours. -/
example :=
  twoBlackReversedMiddleExitWords (Q₀ := Q) 0 (by decide) loading
    (a := 1) (b := 0) (i := 0) (j := 0) rfl rfl rfl rfl (by decide)

/-- The right pivot readout remains valid when the two black colours coincide. -/
example := twoBlackRightPivotLabels loading 0 (by decide)

/-- The four completed comparisons have zero total change on every exit. -/
example :=
  twoBlackExitCycleWords (Q₀ := Q) 0 (by decide) loading
    (a := 1) (b := 0) (i := 0) (j := 0) rfl rfl rfl rfl

end NonVacuity.WebsterTwoBlackExits

namespace NonVacuity.WebsterPivotObstruction
open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open BraidedStendhalAlgebra KLRAlgebra
open MvPolynomial Equiv

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 2 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev Λ : Fin 2 → Unit →₀ ℕ := fun r => if r = 0 then Finsupp.single () 3 else 0
private def v : Seq μ := Seq.ofList [.inr 0, .inr 1, .inl (), .inl ()] (by decide)
private abbrev A := KLRAlgebra ℚ (stendhalQ Q Λ) μ

/-- A right-red crossing and its composition with a black crossing have a
coupled relation in the affine KLR column with a surviving upper idempotent. -/
example :=
  let ρ := canWord μ.card
  let hρ : ∀ w : Perm (Fin μ.card), IsReduced μ.card (ρ w) ∧ wordProd μ.card (ρ w) = w := fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  let B := lbasis (k := ℚ) («μ» := μ) (stendhalQ_symm Q Λ (fun _ _ _ => rfl)) ρ hρ
  let u := sadj μ.card 1 • v
  have h₁ : ρ 1 = [] := List.length_eq_zero_iff.mp
    ((length_canWord _ _).trans (length_one _))
  have hne : (e u : A) ≠ 0 := by
    have he := B.ne_zero (u, 1, 0)
    change lbasis _ ρ hρ (u, 1, 0) ≠ 0 at he
    simpa only [lbasis_apply, h₁, ψw_nil, monomial_zero', map_one, one_mul] using he
  exists_unmarked_twoColumnRelation_of_zeroExponent Q Λ (AlgHom.id ℚ A)
    v 1 (by decide) 1 () rfl rfl (by decide) (⊥ : TwoSidedIdeal A)
    (by simpa only [AlgHom.id_apply, TwoSidedIdeal.mem_bot] using hne)

end NonVacuity.WebsterPivotObstruction

namespace NonVacuity.WebsterCycleMark

open Categorification.Stendhal.BraidedStendhalAlgebra

/-- The cycle changes a nonzero supported tuple into marked coefficients
whilst preserving each of its four arm coefficients. -/
example :=
  let J : TwoSidedIdeal ℤ := ⊥
  have zero : 0 ∈ J := J.zero_mem
  have cancellation (x : ℤ) (_ : 1*x*1=x) (hx : x*1 ∈ J) : x ∈ J := by
    simpa only [mul_one] using hx
  have lift := fourExitPairLift_of_leftInverse J 1 1 1 1 1 1 1 1 1 1
    rfl rfl rfl rfl rfl rfl cancellation
  exists_marked_fourExitCycle J 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
    rfl rfl rfl rfl rfl rfl cancellation cancellation 1 1 (-1) 1 rfl rfl
    (by simpa only [mul_one,sub_self] using zero)
    (by simpa only [mul_one,sub_self] using zero)
    (by simpa only [mul_one,neg_add_cancel] using zero) lift

end NonVacuity.WebsterCycleMark

namespace NonVacuity.WebsterRightPair

open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 4 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev Λ : Fin 4 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private def s : Seq μ := Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inl (), .inr 3] (by decide)
private def v : Seq μ := Seq.ofList [.inl (), .inr 0, .inr 1, .inr 2, .inl (), .inr 3] (by decide)

private theorem blacks (a : Fin μ.card) (h : (s.lbl a).isLeft) :
    a = ⟨3,by decide⟩ ∨ a = ⟨4,by decide⟩ := by
  fin_cases a <;> first | decide | contradiction

/-- Both right factors apply at a genuinely violated generating cut, with
exterior red spectators and coincident black colours. -/
example (z : BraidedStendhalAlgebra ℚ Q Λ ν) :=
  exists_rightPairColumn_coefficients_of_black_before Q Λ (ofKLR ℚ Q Λ ν)
    (ofKLR_surjective (Q := Q) (Λ := Λ)) (fun _ _ _ => rfl) s v 2 (by decide) 2 rfl
    blacks (exists_black_before_red_of_isViolated v 2 ⟨by decide,rfl⟩) z

end

end NonVacuity.WebsterRightPair

namespace NonVacuity.WebsterLastRedPair

open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 3 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private def s : Seq μ := Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inl ()] (by decide)
private def t : Seq μ := Seq.ofList [.inr 0, .inr 1, .inl (), .inr 2, .inl ()] (by decide)

private theorem blacks (a : Fin μ.card) (h : (s.lbl a).isLeft) :
    a = ⟨3,by decide⟩ ∨ a = ⟨4,by decide⟩ := by
  fin_cases a <;> first | decide | contradiction

/-- Check the successive quotient projections at positive weight and repeated
black colours with an exterior red before the exchanged pair. -/
example :=
  exists_rightPairRelation_affine_lift_of_lastPairHigher Q Λ (fun _ _ _ => rfl)
    s t 2 (by decide) 1 2 [0] (by decide) rfl blacks
    (fun _ => 0) (by intro i; rw [mul_zero, zero_mul]) (by simp only [zero_mul, Finset.sum_const_zero])

end

end NonVacuity.WebsterLastRedPair

namespace NonVacuity.WebsterEqualBlackHigherPair

open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 3 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private def s : Seq μ := Seq.ofList [.inr 0, .inr 1, .inr 2, .inl (), .inl ()] (by decide)
private def t : Seq μ := sadj μ.card 2 • s
private def u : Seq μ := sadj μ.card 3 • t
private abbrev A := KLRAlgebra ℤ (stendhalQ Q Λ) μ
private abbrev P := (violMk ℤ Q Λ ν).comp (ofKLR ℤ Q Λ ν)

private theorem blacks (a : Fin μ.card) (h : (s.lbl a).isLeft) :
    a = ⟨3,by decide⟩ ∨ a = ⟨4,by decide⟩ := by
  fin_cases a <;> first | decide | contradiction

private theorem compose_at_cut (left right : List ℕ) :
    (ψw left * e (wordProd μ.card right • s) : A) * (ψw right * e s) =
      ψw (left ++ right) * e s := by
  have he : (e (wordProd μ.card right • s) : A) * (ψw right * e s) = ψw right * e s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  rw [mul_assoc,he,ψw_append,mul_assoc]

/-- Check a supported pair with a common-joint contribution, at positive red
weights and with an exterior red spectator before the pair. -/
private theorem pairAtTop (top : Seq μ) (hTop : top=s ∨ top=t ∨ top=u)
    (order : redWord top = [0] ++ [1,2]) (g : ViolQuotient ℤ Q Λ ν) :
    let w := P (e top) * g * P (e u)
    let J := blockUpperIdeal ℤ Q Λ ν 1 2 (adjacentBlockRoot 1 2 top) (redWord top)
    ∃ z : ViolQuotient ℤ Q Λ ν, P (e top)*z*P (e u)=z ∧
      w*P (ψw [2,3]*e t)-z*P (ψw [2,3]*e t) ∈ J ∧
      w*P (ψw [3]*e t)-z*P (ψw [3]*e t) ∈ J :=
  let w := P (e top) * g * P (e u)
  let x := w * P (ψw [2,3]*e t)
  let y := w * P (ψw [3]*e t)
  have cut (l : List ℕ) :
      P (e top)*(w*P (ψw l*e t))*P (e t)=w*P (ψw l*e t) := by
    have leftFixed : P (e top)*w=w := by
      simp only [w,← mul_assoc,← map_mul,e_mul_self]
    have right : P (ψw l*e t)*P (e t)=P (ψw l*e t) := by
      simp only [← map_mul,mul_assoc,e_mul_self]
    rw [← mul_assoc (P (e top)) w,leftFixed,mul_assoc,right]
  have legs : (ψw [2,3]*e t : A)*(ψw [2]*e s)=(ψw [3]*e t)*(ψw [2,3]*e s) := by
    have h₁ : wordProd μ.card [2] • s=t := by simp only [t,wordProd_singleton]
    have h₂ : wordProd μ.card [2,3] • s=t := by decide
    rw [← h₁,compose_at_cut, h₁,← h₂,compose_at_cut]
    have h := braid (Q := stendhalQ Q Λ) 2 (by decide) s
    have ne : s.lbl ⟨2,by decide⟩ ≠ s.lbl ⟨4,by decide⟩ := by decide
    rw [ite_eq_right (fun h => ne h.1),sub_mul,sub_eq_zero] at h
    simpa only [List.cons_append,List.nil_append,ψw_cons,ψw_nil,mul_one,mul_assoc] using h
  have rel : y*P (ψw [2,3]*e s)-x*P (ψw [2]*e s) ∈
      blockUpperIdeal ℤ Q Λ ν 1 2 (adjacentBlockRoot 1 2 top) (redWord top) := by
    rw [show y*P (ψw [2,3]*e s)=x*P (ψw [2]*e s) by
      simp only [x,y,mul_assoc,← map_mul,legs],sub_self]
    exact TwoSidedIdeal.zero_mem _
  exists_equalBlack_rightPair_markedCycle_at_three_tops Q Λ (fun _ _ _ => rfl)
    s top 2 (by decide) 1 2 () hTop [0] order rfl rfl rfl blacks x y (cut _) (cut _) rel

/-- The right extreme, mixed joint and full joint admit the integral marked lift. -/
example (g : ViolQuotient ℤ Q Λ ν) := pairAtTop s (Or.inl rfl) (by decide) g

example (g : ViolQuotient ℤ Q Λ ν) := pairAtTop t (Or.inr (Or.inl rfl)) (by decide) g

example (g : ViolQuotient ℤ Q Λ ν) := pairAtTop u (Or.inr (Or.inr rfl)) (by decide) g

end

end NonVacuity.WebsterEqualBlackHigherPair

namespace NonVacuity.WebsterFixedTopFourExits

open Categorification.KLR Categorification.Stendhal Categorification.TypeA
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 3 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev B := BraidedStendhalAlgebra ℤ Q Λ ν
private abbrev R := KLRAlgebra ℤ (stendhalQ Q Λ) μ
private abbrev F := ofKLR ℤ Q Λ ν
private abbrev bot := fixedTopFourExitBottom
private abbrev v (i : Fin 4) := fixedTopFourExitCut i
private abbrev jA := sadj μ.card 2 • v 0
private abbrev leg (l : List ℕ) (v : Seq μ) := F (ψw l*e v)

private theorem compose (l w : List ℕ) (s : Seq μ) (hs : wordProd μ.card w • bot=s) :
    leg l s*leg w bot=leg (l++w) bot := by
  have h : (e (wordProd μ.card w • bot) : R)*(ψw w*e bot)=ψw w*e bot := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  simp only [leg,← map_mul,ψw_append,← hs]
  rw [mul_assoc,h,mul_assoc]

/-- A signed neighboring relation at the five-slot fixed top flows through
the descent cascade. -/
example (g : B) :=
  let q := F (e (v 2))*g*F (e jA)
  let x₀ := q*leg [2] (v 0)
  let x₁ := -(q*leg [3] (v 1))
  have cut (l : List ℕ) (s : Seq μ) :
      F (e (v 2))*(q*leg l s)*F (e s)=q*leg l s := by
    have left : F (e (v 2))*q=q := by
      simp only [q,← mul_assoc,← map_mul,e_mul_self]
    simp only [← mul_assoc (F (e (v 2))) q,left,leg,← map_mul,mul_assoc,e_mul_self]
  have edge : leg [2] (v 0)*leg [3,2,1] bot=leg [3] (v 1)*leg [2,3,1] bot := by
    rw [compose _ _ _ (by decide),compose _ _ _ (by decide)]
    exact congrArg F (twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) bot (by decide)).1
  have sum : x₀*leg [3,2,1] bot+x₁*leg [2,3,1] bot+
      (0 : B)*leg [1,2,3] bot+(0 : B)*leg [2,3,1,2] bot=0 := by
    simp only [x₀,x₁,neg_mul,mul_assoc,edge,zero_mul,add_zero,add_neg_cancel]
  exists_fixedTop_fourExitJointPresentation_prefixOne Q Λ (fun _ _ _ => rfl)
    x₀ x₁ 0 0 (cut _ _) (by simpa only [x₁,mul_neg,neg_mul] using congrArg Neg.neg (cut [3] (v 1)))
    (by rw [mul_zero,zero_mul]) (by rw [mul_zero,zero_mul]) sum

private def leftTop : Fin 3 → Seq μ
  | 0 => v 0
  | 1 => sadj μ.card 2 • v 0
  | _ => sadj μ.card 1 • (sadj μ.card 2 • v 0)

/-- The right neighboring braid gives a signed relation at every left top. -/
example (slot : Fin 3) (g : B) :=
  let upper := leftTop slot
  have ht : FiveSlotLeftTop upper := by
    fin_cases slot
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  let q := F (e upper)*g*F (e (sadj μ.card 1 • v 1))
  let x₁ := q*leg [1] (v 1)
  let x₂ := -(q*leg [2] (v 2))
  have cut (l : List ℕ) (s : Seq μ) : F (e upper)*(q*leg l s)*F (e s)=q*leg l s := by
    have left : F (e upper)*q=q := by simp only [q,← mul_assoc,← map_mul,e_mul_self]
    simp only [← mul_assoc (F (e upper)) q,left,leg,← map_mul,mul_assoc,e_mul_self]
  have braid : leg [1] (v 1)*leg [2,3,1] bot=leg [2] (v 2)*leg [1,2,3] bot := by
    rw [compose _ _ _ (by decide),compose _ _ _ (by decide)]
    exact congrArg F (twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) bot (by decide)).2
  have sum : (0 : B)*leg [3,2,1] bot+x₁*leg [2,3,1] bot+x₂*leg [1,2,3] bot+0*leg [2,3,1,2] bot=0 := by
    simp only [x₁,x₂,neg_mul,mul_assoc,braid,zero_mul,zero_add,add_zero,add_neg_cancel]
  exists_fiveSlotLeftTop_fourExitJointPresentation Q Λ (fun _ _ _ => rfl) upper ht
    0 x₁ x₂ 0 (by rw [mul_zero,zero_mul]) (cut _ _)
    (by simpa only [x₂,mul_neg,neg_mul] using congrArg Neg.neg (cut [2] (v 2)))
    (by rw [mul_zero,zero_mul]) sum

example := fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ (v 1) (Or.inl rfl)
example := fiveSlot_oneBlackBeforePair_blockUpperIdeal Q Λ jA (Or.inr rfl)
example := fiveSlotLeftExtreme_blockKernelColumnInclusion_injective Q Λ bot

end

end NonVacuity.WebsterFixedTopFourExits

namespace NonVacuity.WebsterFiniteExitLift

open Categorification.KLR Categorification.TypeA Categorification.Stendhal
open BraidedStendhalAlgebra KLRAlgebra
open scoped BigOperators

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private abbrev Λ : Fin 4 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private def bottom : Seq (stendhalWeight 4 ν) :=
  Seq.ofList [.inr 0, .inl (), .inr 2, .inl (), .inr 1, .inr 3] (by decide)
private def top : Seq (stendhalWeight 4 ν) :=
  Seq.ofList [.inr 0, .inl (), .inr 1, .inl (), .inr 2, .inr 3] (by decide)
private def exits : Bool → List ℕ
  | false => [3,2]
  | true => [2,3]
private abbrev A := BraidedStendhalAlgebra (ZMod 4) Q Λ ν
private abbrev F := ofKLR (ZMod 4) Q Λ ν
private abbrev mk := violMk (ZMod 4) Q Λ ν
private abbrev leg (i : Bool) := F (ψw (exits i) * e bottom)

private theorem generate (v : Seq (stendhalWeight 4 ν)) (hv : redWord v = redWord top) (z : A) :
    ∃ c : Bool → A, F (e v) * z * F (e bottom) = ∑ i, c i * leg i := by
  have ho : redWord v = [0] ++ 1 :: 2 :: [3] := hv.trans (by decide)
  obtain ⟨l,r,he⟩ := exists_interleavedColumn_exits Q Λ bottom 2 (by decide) (fun _ _ _ => rfl)
    (a := 1) (b := 2) (by decide) (by decide) v ho z
  refine ⟨fun i => if i then r else l, ?_⟩
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [add_comm]
  exact he

/-- A violated diagram with a spectator black admits exit coefficients that
individually vanish after imposing the global violation. -/
example (u v : A) :=
  let bad : Seq (stendhalWeight 4 ν) :=
    Seq.ofList [.inl (), .inr 0, .inr 1, .inl (), .inr 2, .inr 3] (by decide)
  exists_violated_finite_exits_of_violated_generation Q Λ bottom top exits (fun _ _ _ => rfl)
    (fun v _ => generate v)
    (u * F (e bad) * v) (by
      have hv : IsViolated bad := ⟨by decide,rfl⟩
      simp only [map_mul,violMk_e hv,mul_zero,zero_mul])

/-- Lift a signed braid relation in the six-strand quotient using the same
ordered exits. -/
example :=
  let d := wordProd (stendhalWeight 4 ν).card [2,3,2] • bottom
  let side := fun i : Bool => wordProd (stendhalWeight 4 ν).card (exits i) • bottom
  let signed := fun i : Bool => if i then
    -(mk (F (e d * ψ 3 * e (side i)))) else mk (F (e d * ψ 2 * e (side i)))
  have hd : d = top := by decide
  have sup (i : Bool) : mk (F (e top)) * signed i * mk (F (e (side i))) = signed i := by
    cases i <;> simp only [signed, Bool.false_eq_true, ↓reduceIte, ← hd, mul_neg, neg_mul] <;>
      simp only [← map_mul, ← mul_assoc (e d), e_mul_self] <;>
      simp only [mul_assoc, e_mul_self]
  have rel : ∑ i, signed i * mk (leg i) = 0 := by
    simp only [Fintype.sum_bool, signed, Bool.false_eq_true, ↓reduceIte, neg_mul, ← map_mul,
      exits, side, ψw_cons, ψw_nil, mul_one]
    have h := braid (Q := stendhalQ Q Λ) 2 (by decide) bottom
    have hl : bottom.lbl ⟨2, by decide⟩ ≠ bottom.lbl ⟨4, by decide⟩ := by decide
    rw [ite_eq_right (fun h => hl h.1), sub_mul, sub_eq_zero] at h
    have le (w : List ℕ) : e (wordProd (stendhalWeight 4 ν).card w • bottom) * ψw w * e bottom =
        (ψw w * e bottom : KLRAlgebra (ZMod 4) (stendhalQ Q Λ) (stendhalWeight 4 ν)) := by
      rw [e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    have left := le [3,2]
    have right := le [2,3]
    simp only [ψw_cons, ψw_nil, mul_one] at left right
    rw [show e d * ψ 2 * e (wordProd (stendhalWeight 4 ν).card [3,2] • bottom) *
        (ψ 3 * ψ 2 * e bottom) = e d * (ψ 2 * ψ 3 * ψ 2 * e bottom) by
          rw [mul_assoc, ← mul_assoc (e (wordProd (stendhalWeight 4 ν).card [3,2] • bottom)), left]
          simp only [mul_assoc],
      show e d * ψ 3 * e (wordProd (stendhalWeight 4 ν).card [2,3] • bottom) *
        (ψ 2 * ψ 3 * e bottom) = e d * (ψ 3 * ψ 2 * ψ 3 * e bottom) by
          rw [mul_assoc, ← mul_assoc (e (wordProd (stendhalWeight 4 ν).card [2,3] • bottom)), right]
          simp only [mul_assoc],
      ← h, neg_add_cancel]
  exists_finiteExitRelation_affine_lift_of_violated_generation Q Λ bottom top exits
    (fun _ _ _ => rfl) (fun v _ => generate v) signed sup rel

end NonVacuity.WebsterFiniteExitLift

namespace NonVacuity.WebsterFiveSlotMarkedJoints

open Categorification.KLR Categorification.Stendhal Categorification.TypeA
open BraidedStendhalAlgebra KLRAlgebra
open scoped BigOperators

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 3 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev V := ViolQuotient ℤ Q Λ ν
private abbrev R := KLRAlgebra ℤ (stendhalQ Q Λ) μ
private abbrev F := (violMk ℤ Q Λ ν).comp (ofKLR ℤ Q Λ ν)
private abbrev s := fixedTopFourExitBottom
private abbrev v (i : Fin 4) := fixedTopFourExitCut i
private abbrev jA := sadj μ.card 2 • v 0
private def fixtureTop : Fin 3 → Seq μ
  | 0 => v 2
  | 1 => sadj μ.card 2 • v 2
  | _ => sadj μ.card 3 • (sadj μ.card 2 • v 2)
private abbrev leg (l : List ℕ) (t : Seq μ) := F (ψw l*e t)

private theorem compose (l w : List ℕ) (t : Seq μ) (ht : wordProd μ.card w • s=t) :
    leg l t*leg w s=leg (l++w) s := by
  have h : (e (wordProd μ.card w • s) : R)*(ψw w*e s)=ψw w*e s := by
    rw [← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  simp only [leg,← map_mul,ψw_append,← ht]
  rw [mul_assoc,h,mul_assoc]

/-- A positive-weight marked relation through the actual higher joint at a
surviving spectator cut. -/
example (slot : Fin 3) (g : V) :=
  let upper := fixtureTop slot
  have ht : FiveSlotRightTop upper := by
    fin_cases slot
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  let J := blockUpperIdeal ℤ Q Λ ν 1 2 (adjacentBlockRoot 1 2 upper) (redWord upper)
  let q := F (e upper)*g*F (e jA)
  let x₀ := q*leg [2] (v 0)
  let x₁ := -(q*leg [3] (v 1))
  let x : Fin 4 → V := ![x₀,x₁,0,0]
  have higher : adjacentBlockRoot 1 2 upper < adjacentBlockRoot 1 2 jA := by
    rw [fiveSlotRightTop_blockRoot upper ht]
    apply lt_of_le_not_ge
    · intro i j
      fin_cases i <;> cases j <;> decide
    · intro le
      exact (by decide : ¬ adjacentBlockRoot 1 2 jA 1 () ≤ adjacentBlockRoot 1 2 (v 2) 1 ())
        (le 1 ())
  have eMark : F (e jA) ∈ J := TwoSidedIdeal.subset_span ⟨jA,by rw [fiveSlotRightTop_redWord upper ht]; decide,higher,rfl⟩
  have qMark : q ∈ J := J.mul_mem_left _ _ eMark
  have mark (i : Fin 4) : x i ∈ J := by
    fin_cases i
    · exact J.mul_mem_right _ _ qMark
    · exact J.neg_mem (J.mul_mem_right _ _ qMark)
    · exact J.zero_mem
    · exact J.zero_mem
  have cut (l : List ℕ) (t : Seq μ) :
      F (e upper)*(q*leg l t)*F (e t)=q*leg l t := by
    have left : F (e upper)*q=q := by
      simp only [q,← mul_assoc,← map_mul,e_mul_self]
    simp only [← mul_assoc (F (e upper)) q,left,leg,← map_mul,mul_assoc,e_mul_self]
  have support (i : Fin 4) :
      F (e upper)*x i*F (e (wordProd μ.card (fiveSlotExitWord i) • s))=x i := by
    have h : wordProd μ.card (fiveSlotExitWord i) • s=v i := by fin_cases i <;> decide
    rw [h]
    fin_cases i
    · exact cut [2] (v 0)
    · change F (e upper)*(-(q*leg [3] (v 1)))*F (e (v 1))=-(q*leg [3] (v 1))
      rw [mul_neg,neg_mul,cut]
    · change F (e upper)*(0 : V)*F (e (v 2))=0
      rw [mul_zero,zero_mul]
    · change F (e upper)*(0 : V)*F (e (v 3))=0
      rw [mul_zero,zero_mul]
  have edge : leg [2] (v 0)*leg [3,2,1] s=leg [3] (v 1)*leg [2,3,1] s := by
    rw [compose _ _ _ (by decide),compose _ _ _ (by decide)]
    exact congrArg F (twoBlackNearbyExitWords (Q := stendhalQ Q Λ) 1 (by decide) s (by decide)).1
  have sum : ∑ i, x i*F (ψw (fiveSlotExitWord i)*e s)=0 := by
    rw [Fin.sum_univ_four]
    change x₀*leg [3,2,1] s+x₁*leg [2,3,1] s+
      (0 : V)*leg [1,2,3] s+0*leg [2,3,1,2] s=0
    simp only [x₀,x₁,neg_mul,mul_assoc,edge,zero_mul,add_zero,add_neg_cancel]
  exists_fiveSlotRightTop_markedExitJoints Q Λ (fun _ _ _ => rfl) upper ht x support mark sum

end

end NonVacuity.WebsterFiveSlotMarkedJoints

namespace NonVacuity.WebsterFirstPairAllBottom

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup BraidedStendhalAlgebra

private noncomputable abbrev C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev Q := Categorification.KL3.Diagram.CL.qCL
  (Categorification.KL3.Diagram.CL.CLScalars.kl : Categorification.KL3.Diagram.CL.CLScalars C ℚ)
private def Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 1)
private def t : Categorification.KLR.Seq (stendhalWeight 3 ({()} + {()} : Multiset Unit)) :=
  ⟨![.inl (), .inr 0, .inr 1, .inr 2, .inl ()], by decide⟩

example := firstPair_blockKernelTensorInclusion_injective_standard_of_twoInterior (k := ℚ) C Λ t
  (by decide) (blockKernelColumnInclusion_injective_of_tensor Q Λ t 0 1 firstPairBottomTwoInterior
    (blockKernelTensorInclusion_injective_of_violated_top Q Λ t 0 1 _ ⟨by decide, by decide⟩))

end NonVacuity.WebsterFirstPairAllBottom

namespace NonVacuity.WebsterFiveSlotCentral

open Categorification.KLR Categorification.Stendhal Categorification.TypeA
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev μ := stendhalWeight 3 ν
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev Q₀ := stendhalQ Q Λ
private abbrev R := KLRAlgebra ℤ Q₀ μ
private abbrev V := ViolQuotient ℤ Q Λ ν
private abbrev F := (violMk ℤ Q Λ ν).comp (ofKLR ℤ Q Λ ν)
private abbrev bot := fixedTopFourExitBottom
private abbrev t := fixedTopFourExitCut 1
private abbrev q := exitSquarePolynomial Q₀ t 1 (by decide)*exitSquarePolynomial Q₀ t 3 (by decide)
private abbrev U : R := ψw [1,3,2,3,1]*e t

/-- The central transposition row on the ordinary middle arm cancels the
product of two positive-weight squares on the reversed arm. -/
example :=
  let y : R := pol (-q)*e t
  let x : Fin 4 → V := ![0,F U,0,F y]
  have cutU : (e t : R)*U*e t=U := by
    have h := e_mul_pol_ψw_e (Q := Q₀) 1 [1,3,2,3,1] t
    rw [show wordProd μ.card [1,3,2,3,1] • t=t by decide,map_one,one_mul] at h
    rw [show e t*U=U by simpa only [U,mul_assoc] using h]
    simp only [U,mul_assoc,e_mul_self]
  have cutY : e t*y*e t=y := by
    have h := e_mul_pol_ψw_e (Q := Q₀) (-q) [] t
    simp only [wordProd_nil,one_smul,ψw_nil,mul_one] at h
    change e t*(pol (-q)*e t)*e t=pol (-q)*e t
    rw [h,mul_assoc,e_mul_self]
  have support (i : Fin 4) :
      F (e t)*x i*F (e (wordProd μ.card (fiveSlotExitWord i) • bot))=x i := by
    have load (j : Fin 4) : wordProd μ.card (fiveSlotExitWord j) • bot=fixedTopFourExitCut j := by fin_cases j <;> decide
    rw [load]
    fin_cases i
    · change F (e t)*(0 : V)*_=0; rw [mul_zero,zero_mul]
    · exact (show F (e t)*F U*F (e t)=F U by simp only [← map_mul,cutU])
    · change F (e t)*(0 : V)*_=0; rw [mul_zero,zero_mul]
    · exact (show F (e t)*F y*F (e t)=F y by simp only [← map_mul,cutY])
  have mat := fiveSlotCentral_middle_matrix_iff (stendhalQ_symm Q Λ (fun _ _ _ => rfl)) 0 1 (-q) 0
  have sumRaw : U*(ψw [2,3,1]*e bot)+y*(ψw [2,3,1,2]*e bot)=0 := by
    simpa only [map_zero,map_one,zero_mul,one_mul,zero_add,add_zero,y,U] using
      mat.2 ⟨rfl,by change 1*q+ -q=0; rw [one_mul,add_neg_cancel]⟩
  have sum : ∑ i, x i*F (ψw (fiveSlotExitWord i)*e bot)=0 := by
    rw [Fin.sum_univ_four]
    change (0 : V)*_+F U*F (ψw [2,3,1]*e bot)+0*_+F y*F (ψw [2,3,1,2]*e bot)=0
    simpa only [zero_mul,zero_add,add_zero,map_mul,map_add,map_zero] using congrArg F sumRaw
  exists_fiveSlot_violQuotient_fourExitJointPresentation Q Λ (fun _ _ _ => rfl)
    t (by decide) x support sum

end

end NonVacuity.WebsterFiveSlotCentral

namespace NonVacuity.WebsterCentralHigher

open Categorification.KLR Categorification.Stendhal Categorification.TypeA
open BraidedStendhalAlgebra KLRAlgebra

noncomputable section

private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (if r=0 then 1 else 2)
private abbrev μ := stendhalWeight 3 ({()} + {()} : Multiset Unit)
private theorem pairing : Λ 0 () ≤ 1 := by simp [Λ]

/-- Both loadings allow arbitrary exchanged-red weights. Here both
exchanged weights are two and the spectator is fundamental. -/
example (s : Seq μ) :=
  fiveSlot_oneBlackBeforePair_columnInclusion_of_spectatorWeight_le_one Q Λ pairing
    (fixedTopFourExitCut 1) s (Or.inl rfl)

example (s : Seq μ) :=
  fiveSlot_oneBlackBeforePair_columnInclusion_of_spectatorWeight_le_one Q Λ pairing
    (sadj μ.card 2 • fixedTopFourExitCut 0) s (Or.inr rfl)

/-- The two rows use distinct polynomials at this positive-weight specialization. -/
example := fiveSlotCentral_leftWord_rows Q Λ 1 (MvPolynomial.X (⟨1,by decide⟩ : Fin μ.card))

/-- The principal crossing word preserves a nonzero PBW class over the
integers even though the globally violated quotient kills this source corner. -/
example :
    let B := ofKLR ℤ Q Λ ({()} + {()})
    B (ψw [3,2]*e (fixedTopFourExitCut 0)) * B (ψw [3,2,1]*e fixedTopFourExitBottom) ≠ 0 := by
  let B := ofKLR ℤ Q Λ ({()} + {()})
  let T := toKLR ℤ Q Λ ({()} + {()})
  let v := fixedTopFourExitCut 0
  let s := fixedTopFourExitBottom
  let y := B (ψw [3,2,1]*e s)
  change B (ψw [3,2]*e v)*y ≠ 0
  intro zero
  have top : (e v : KLRAlgebra ℤ (stendhalQ Q Λ) μ)*(ψw [3,2,1]*e s)=ψw [3,2,1]*e s := by
    rw [← show wordProd μ.card [3,2,1] • s=v by decide,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  have killed : y=0 := fiveSlotCentral_leftWord_cancel_braided Q Λ (fun _ _ _ => rfl) y
    (by change B (e v)*B _=B _; rw [← map_mul,top])
    (by change B _*B (e s)=B _; rw [← map_mul,mul_assoc,e_mul_self]) zero
  have raw : (ψw [3,2,1]*e s : KLRAlgebra ℤ (stendhalQ Q Λ) μ)=0 := by
    simpa only [y,B,T,map_mul,map_zero,toKLR_ofKLR_ψw,toKLR_ofKLR_e] using congrArg T killed
  have red (w : List ℕ) (h : ValidWord μ.card w) (n : w.length=invCount μ.card (wordProd μ.card w)) :
      IsReduced μ.card w := ⟨h,by rw [length_eq_invCount]; exact n⟩
  have rows := top_polynomial_pair_eq_zero_iff_of_words (stendhalQ_symm Q Λ (fun _ _ _ => rfl))
    (red [3,2,1] (by simp [ValidWord,stendhalWeight]) (by decide))
    (red [1,3,2,1] (by simp [ValidWord,stendhalWeight]) (by decide)) (by decide) s 1 0
  exact one_ne_zero (rows.1 (by simpa only [map_zero,map_one,one_mul,zero_mul,add_zero] using raw)).1

example : FiveSlotCentralRowReflection Q Λ :=
  fiveSlotCentral_rowReflection_of_smallSpectator Q Λ (fun _ _ _ => rfl) pairing

/-- The quotient reflection criterion controls the balanced column itself. -/
example := fiveSlotCentral_columnInclusion_of_rowReflection Q Λ (fun _ _ _ => rfl)
  (fiveSlotCentral_rowReflection_of_smallSpectator Q Λ (fun _ _ _ => rfl) pairing)

/-- On the fundamental spectator the complete marked presentation uses the
verified two-row reflection, with its ordinary four-arm support. -/
example := fiveSlotCentral_markedExitJoints_of_row_reflection Q Λ (fun _ _ _ => rfl)
  (fiveSlotCentral_rowReflection_of_smallSpectator Q Λ (fun _ _ _ => rfl) pairing)
  (fun _ => 0) (by intro i; rw [mul_zero,zero_mul]) (fun _ => TwoSidedIdeal.zero_mem _)
  (by simp only [zero_mul,Finset.sum_const_zero])

end

end NonVacuity.WebsterCentralHigher

namespace NonVacuity.WebsterTwoBlackFlag

open Categorification.Stendhal Categorification.KLR BraidedStendhalAlgebra
open MvPolynomial
noncomputable section

/-- The second power reflects membership with distinct positive bounds, even
over a ring containing nonzero nilpotents. -/
example (f : MvPolynomial (Fin 2) (ZMod 4)) :
    f * X (1 : Fin 2)^2 ∈ TwoBlackFlag.ideal 0 1 2 5 ↔ f ∈ TwoBlackFlag.ideal 0 1 2 3 :=
  TwoBlackFlag.mul_second_pow_mem_iff (by decide) (by decide : 2≤3) 2 f

private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 3
private abbrev μ := stendhalWeight 3 ({()} + {()} : Multiset Unit)

/-- At spectator pairing three the complete homogeneous quadratic annihilates
the left-extreme source. -/
example :=
  let a : Fin μ.card := ⟨1,by decide⟩
  let b : Fin μ.card := ⟨2,by decide⟩
  fiveSlotLeftExtreme_flagIdeal_kills Q Λ
    (f := TwoBlackFlag.complete (X a) (X b) 3)
    (by
      change TwoBlackFlag.complete (X a) (X b) 3 ∈ TwoBlackFlag.ideal a b (Λ 0 ()) (Λ 0 ())
      rw [show Λ 0 ()=3 by simp [Λ]]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private abbrev D : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) ℤ
  | .inl _,.inl _ => 0
  | .inl i,.inr r => X 1 ^ Λ r i
  | .inr _,.inl _ => 1
  | .inr r,.inr u => if r=2 ∧ u=1 then 1 else 0

private theorem factor : ∀ a b, a≠b → stendhalQ Q Λ a b = D b a*rename ![1,0] (D a b) := by
  rintro (i | r) (j | u) h
  · exact (h (by cases i; cases j; rfl)).elim
  · simp [stendhalQ,D]
  · simp [stendhalQ,D]
  · fin_cases r <;> fin_cases u <;> simp [stendhalQ,D]

/-- In the integral action, the reversed-middle word differentiates the
first black variable. Both coefficient rows have positive rightward weight. -/
example := fiveSlotCentral_flagRows_eval Λ Q factor rfl rfl (by simp [D])
  1 1 (X (⟨2,by decide⟩ : Fin μ.card))

end
end NonVacuity.WebsterTwoBlackFlag

namespace NonVacuity.WebsterCentralFlagInjection

open Categorification.Stendhal BraidedStendhalAlgebra
noncomputable section

private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun r =>
  Finsupp.single () (if r=0 then 3 else if r=1 then 2 else 1)

/-- The spectator supports both blacks and both exchanged-red crossings
have positive weight. The row reflection and balanced injection hold in
the globally violated quotient over the integers. -/
example : FiveSlotCentralRowReflection Q Λ :=
  fiveSlotCentral_rowReflection Q Λ (fun _ _ _ => rfl)

example : Function.Injective
    (blockKernelColumnInclusion Q Λ (fixedTopFourExitCut 1) 1 2 fixedTopFourExitBottom) :=
  fiveSlotCentral_blockKernelColumnInclusion_injective Q Λ (fun _ _ _ => rfl)

end
end NonVacuity.WebsterCentralFlagInjection
namespace NonVacuity.WebsterFiveSlotFlag

open KLR KLRAlgebra Stendhal Stendhal.FiveSlotFlag Stendhal.BraidedStendhalAlgebra

private abbrev black : Multiset Unit := {()} + {()}
private noncomputable abbrev params : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev weights : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 2)
private def loading : Seq FiveSlotFlag.weight := Seq.ofList [.inr 0, .inl (), .inr 1, .inr 2, .inl ()]
  (by decide)
private abbrev pos : Fin FiveSlotFlag.weight.card := ⟨2, by decide⟩
private noncomputable abbrev redDot : KLRAlgebra ℚ (stendhalQ params weights) FiveSlotFlag.weight :=
  x pos * e loading

example (f : KLR.PolyRep.Pol ℚ FiveSlotFlag.weight) :
    blackEval loading ((KLR.PolyRep.polyRep (flagP_factor params weights)) redDot f loading) ∈
      loadingIdeal weights loading := by
  have hz : violMk ℚ params weights black (ofKLR ℚ params weights black redDot) = 0 := by
    rw [redDot, ofKLR_x_mul_e_of_red _ _ (by decide), map_zero]
  exact eval_mem_flag_of_violMk_eq_zero params weights _ (loadingIdeal_preservesFlags weights)
    (loadingIdeal_eq_top_of_violated weights) hz f loading

end NonVacuity.WebsterFiveSlotFlag

namespace NonVacuity.WebsterFiveSlotKernelColumn

open Categorification.Stendhal BraidedStendhalAlgebra

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2

/-- Injectivity of the actual column tensor inclusion at positive red weights. -/
example := fiveSlot_blockKernelColumnInclusion_injective Q Λ (fun _ _ _ => rfl)

end NonVacuity.WebsterFiveSlotKernelColumn

namespace NonVacuity.WebsterFiveSlotThreeTopKernelColumn

open Categorification.KLR Categorification.Stendhal BraidedStendhalAlgebra
open Categorification.TypeA

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private abbrev μ := stendhalWeight 3 ({()} + {()} : Multiset Unit)
private abbrev extreme := fixedTopFourExitCut 2
private abbrev mixed := sadj μ.card 2 • extreme
private abbrev full := sadj μ.card 3 • mixed

example := fiveSlotRightTop_blockKernelColumnInclusion_injective Q Λ extreme (fun _ _ _ => rfl)
  (Or.inl rfl)

example := fiveSlotRightTop_blockKernelColumnInclusion_injective Q Λ mixed (fun _ _ _ => rfl)
  (Or.inr (Or.inl rfl))

example := fiveSlotRightTop_blockKernelColumnInclusion_injective Q Λ full (fun _ _ _ => rfl)
  (Or.inr (Or.inr rfl))

end NonVacuity.WebsterFiveSlotThreeTopKernelColumn

namespace NonVacuity.WebsterFiveSlotThreeTopDerived

open Categorification.KLR Categorification.Stendhal Categorification.TypeA
open BraidedStendhalAlgebra DG MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1200] Ring.toIntAlgebra

private noncomputable abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => sadj (Multiset.card (stendhalWeight 3 ν₀)) 2 • fixedTopFourExitCut 2
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj ℚ Q Λ ν₀ (redWord t))
local notation "U" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_loading Q Λ fixedTopFourExitBottom)

example [DG.HasDerivedCategory.{0, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{0, 0} Uᵐᵒᵖ] :=
  fiveSlotRightTop_blockKernelColumnDerivedHomology_mono Q Λ t (fun _ _ _ => rfl)
    (Or.inr (Or.inl rfl))

end NonVacuity.WebsterFiveSlotThreeTopDerived

noncomputable section

namespace NonVacuity.WebsterProjectiveKernelBraidAmplitude

open Categorification.KLR Categorification.Stendhal BraidedStendhalAlgebra MvPolynomial DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

private def Q : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private def Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 1)
private def t : Categorification.KLR.Seq (stendhalWeight 3 ({()} : Multiset Unit)) :=
  ⟨![.inr 0, .inr 1, .inr 2, .inl ()], by decide⟩

local instance (order : List (Fin 3)) : DG.HasDerivedCategory.{0, 0}
    (isIdempotentElem_violMk_redProj (ZMod 4) Q Λ ({()} : Multiset Unit) order).Cornerᵐᵒᵖ :=
  DG.HasDerivedCategory.small _

example := blockPartialStandard_braid_homology_vanish_of_projective_kernel_off_two_degrees
  Q Λ t 0 1 [1, 0, 2]
  (firstWeight_blockLoadingKernel_projective () Q Λ 0 1 t (fun _ _ _ => rfl))
  (-2) (by decide) (by decide)

end NonVacuity.WebsterProjectiveKernelBraidAmplitude
end

noncomputable section

namespace NonVacuity.WebsterBlockKernelDerivedNegOne

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup
open BraidedStendhalAlgebra KL3.Diagram DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

private abbrev C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C ℚ)
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 1)
private abbrev ν : Multiset Unit := {()} + {()}

local instance (order : List (Fin 3)) : HasDerivedCategory.{0, 0}
    (isIdempotentElem_violMk_redProj ℚ Q Λ ν order).Cornerᵐᵒᵖ :=
  HasDerivedCategory.small _

example := blockPartialStandard_braid_homology_negOne_vanish Q Λ
  (firstPairOneAfterSpectator true) 0 1 [1, 0, 2]
  (firstPairOneAfter_blockKernelTensorInclusion_injective_standard (k₀ := ℚ) C Λ true)

end NonVacuity.WebsterBlockKernelDerivedNegOne

end

namespace NonVacuity.WebsterFiveSlotBoundedSpectator

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup
open BraidedStendhalAlgebra CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1200] Ring.toIntAlgebra

private noncomputable abbrev C := Categorification.QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
private noncomputable abbrev Q := Categorification.KL3.Diagram.CL.qCL
  (Categorification.KL3.Diagram.CL.CLScalars.kl : Categorification.KL3.Diagram.CL.CLScalars C ℚ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => fixedTopFourExitCut 1
local notation "κ" => ([0,2,1] : List (Fin 3))
local notation "Corner" => fun reds : List (Fin 3) =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj ℚ Q Λ ν₀ reds)

example := fiveSlot_blockKernelTensorInclusion_injective_of_spectatorWeight_le_one
  (k := ℚ) C Λ t (by decide) (by simp [Λ])

example := fiveSlot_blockKernelTensorInclusion_injective_of_spectatorWeight_le_one
  (k := ℚ) C Λ (fixedTopFourExitCut 2) (by decide) (by simp [Λ])

example [DG.HasDerivedCategory.{0, 0} (Corner (redWord t))ᵐᵒᵖ]
    [DG.HasDerivedCategory.{0, 0} (Corner κ)ᵐᵒᵖ] :=
  fiveSlot_blockKernelDerivedHomology_mono_of_spectatorWeight_le_one
    (k := ℚ) C Λ t (by decide) (by simp [Λ])

end NonVacuity.WebsterFiveSlotBoundedSpectator

namespace NonVacuity.WebsterFiveSlotAllBottom

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup
open BraidedStendhalAlgebra

private noncomputable abbrev C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private noncomputable abbrev Q := Categorification.KL3.Diagram.CL.qCL
  (Categorification.KL3.Diagram.CL.CLScalars.kl : Categorification.KL3.Diagram.CL.CLScalars C ℚ)

/-- The full bottom red-order component is injective at standard positive weights. -/
example := fiveSlot_blockKernelTensorInclusion_injective_standard C Λ
  (k := ℚ) (by constructor <;> intro i j h <;> exact (h (Subsingleton.elim i j)).elim)
  (show KLRSymm Q from fun i j h => (h (Subsingleton.elim i j)).elim)

end NonVacuity.WebsterFiveSlotAllBottom

namespace NonVacuity.WebsterFirstPairTwoAfter

open Categorification.KLR Categorification.Stendhal BraidedStendhalAlgebra MvPolynomial

private def Q : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private def Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 1)

example := firstPairTwoAfter_blockKernel_mem_iff_twoFactors Q Λ (fun _ _ _ => rfl)
example := firstPairTwoAfter_nilHecke_kernel Q Λ (fun _ _ _ => rfl)

example := firstPairTwoAfter_equiv_nilHeckeRangeProd Q Λ
example := firstPairTwoAfter_nilHecke_range_iff Q Λ (fun _ _ _ => rfl)

end NonVacuity.WebsterFirstPairTwoAfter

namespace NonVacuity.WebsterFirstPairRightmostZero

open Categorification.KLR Categorification.Stendhal BraidedStendhalAlgebra MvPolynomial

private def params : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private def weights : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (if r = 2 then 0 else 2)

example := firstPairRightmost_partialStandard_isZero_of_zeroSpectator
  params weights (by simp [weights])

end NonVacuity.WebsterFirstPairRightmostZero

namespace NonVacuity.WebsterFirstPairTerminalColumn

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup
open BraidedStendhalAlgebra MvPolynomial

private def Q : Unit → Unit → MvPolynomial (Fin 2) (ZMod 4) := fun _ _ => 0
private def Λ : Fin 3 → Unit →₀ ℕ := fun r => Finsupp.single () (r.val + 1)
private noncomputable abbrev C := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)

example := firstPairOneAfter_terminal_blockKernelColumnInclusion_injective Q Λ
  (fun _ _ _ => rfl) false

example := firstPairOneAfter_blockKernelTensorInclusion_injective_standard (k₀ := ℚ) C Λ true

example := firstPairRightmost_terminal_double_cancel Q Λ (fun _ _ _ => rfl)

end NonVacuity.WebsterFirstPairTerminalColumn

namespace NonVacuity.WebsterFiveSlotAllBottomDerived

open Categorification.KLR Categorification.Stendhal Categorification.QuantumGroup
open BraidedStendhalAlgebra CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1200] Ring.toIntAlgebra

private noncomputable abbrev C := Categorification.QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private noncomputable abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private noncomputable abbrev Q := Categorification.KL3.Diagram.CL.qCL
  (Categorification.KL3.Diagram.CL.CLScalars.kl : Categorification.KL3.Diagram.CL.CLScalars C ℚ)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => fixedTopFourExitCut 2
local notation "κ" => ([0,2,1] : List (Fin 3))
local notation "Corner" => fun reds : List (Fin 3) =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj ℚ Q Λ ν₀ reds)

example [DG.HasDerivedCategory.{0, 0} (Corner (redWord t))ᵐᵒᵖ]
    [DG.HasDerivedCategory.{0, 0} (Corner κ)ᵐᵒᵖ] :=
  fiveSlot_blockKernelDerivedHomology_mono_standard (k := ℚ) C Λ

end NonVacuity.WebsterFiveSlotAllBottomDerived

namespace NonVacuity.WebsterIntervalColumn

open Categorification.KLR Categorification.Stendhal

private abbrev ν : Multiset Bool := {false, true, false}
private def s : Seq (stendhalWeight 3 ν) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl false, .inr 2, .inl true, .inl false, .inr 1] (by decide)
private def t : Seq (stendhalWeight 3 ν) :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl false, .inr 1, .inl true, .inl false, .inr 2] (by decide)
private noncomputable abbrev Q : Bool → Bool → MvPolynomial (Fin 2) ℚ := fun _ _ => 0

example (z : KLRAlgebra ℚ (stendhalQ Q (fun _ : Fin 3 => Finsupp.single true 1))
    (stendhalWeight 3 ν)) :=
  BraidedStendhalAlgebra.mem_span_interval_crossing_column Q (fun _ => Finsupp.single true 1)
    (by intro a b h; simp [Q]) s t (q := ⟨2, by decide⟩) (p := ⟨5, by decide⟩)
    (a := 2) (b := 1) (L := [0]) (M := []) (by decide) (by decide) (by decide) (by decide) z

end NonVacuity.WebsterIntervalColumn

open Categorification.TypeA Equiv
namespace IntervalPBWFixture

private theorem h : 1+(4+1)=6 := rfl
private def u : Perm (Fin 6) := sadj 6 0 * sadj 6 4
private def v : Perm (Fin 4) := wordProd 4 [2,0,1]
private abbrev w := u * intervalPerm h v

private theorem sorted : StrictMono (fun i : Fin 4 => u ⟨1+i.val,by omega⟩) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact False.elim (absurd hij (by decide)) | decide

private theorem split : rightIntervalSplit h w = (u,v) := by
  rw [w, rightIntervalSplit_mul, rightIntervalSplit_of_sorted h u sorted, one_mul]

example : rightIntervalWord h w = canWord 6 u ++ shiftWord 1 (canWord 4 v) := by
  rw [rightIntervalWord,split]

example : length 6 w = 5 := by
  rw [length_rightIntervalSplit h w, split]
  change length 6 u + length 4 v = 5
  rw [length_eq_invCount,length_eq_invCount]
  decide

example : IsReduced 6 (canWord 6 u ++ [3,1,2]) ∧ wordProd 6 (canWord 6 u ++ [3,1,2]) = w := by
  have hr : IsReduced 4 [2,0,1] := by
    constructor
    · simp [ValidWord]
    · rw [length_eq_invCount]; decide
  have hword := rightIntervalSplit_append h w [2,0,1] hr (by rw [split]; rfl)
  rw [split] at hword
  exact hword

end IntervalPBWFixture

noncomputable section
open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open Categorification Categorification.ModuleFiltration
open scoped DG.DegreeZero

namespace NonVacuity.WebsterDerivedBraidFiltration

local instance : HasDerivedCategory.{0, 0} ℤ := HasDerivedCategory.small ℤ

private abbrev X : ModuleCat ℤ := ModuleCat.of ℤ PUnit

private abbrev S : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (𝟙 X) (𝟙 X) (by ext x)

private theorem hS : S.ShortExact := by
  let : Mono S.f := by change Mono (𝟙 X); infer_instance
  let : Epi S.g := by change Epi (𝟙 X); infer_instance
  refine ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr ?_⟩
  intro x
  exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩

example : IsZero ((homologyFunctor ℤ 1).obj ((derivedTensor ℤ ℤ ℤ).obj
    (Q.obj ((degreeZeroModuleFunctor ℤ).obj S.X₃)))) := by
  have hf : HasFiltration (fun _ : Unit => X) [] S.X₁ := .zero inferInstance
  refine isZero_derivedTensorHomology_quotient_of_filtered_kernel (k := ℤ) (M := ℤ) S hS hf
    ?_ ?_ ?_ (AddMonoidHom.id _) ?_ Function.injective_id 1 (by decide)
  · simp
  · intro n _
    apply Functor.map_isZero
    apply Functor.map_isZero
    apply Q.map_isZero
    exact (degreeZeroModuleFunctor ℤ).map_isZero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
  · intro c m
    change m * c = c * m
    exact mul_comm _ _
  · intro m x
    rfl

end NonVacuity.WebsterDerivedBraidFiltration

namespace NonVacuity.WebsterBraidTriangle
open Categorification.Stendhal.BraidedStendhalAlgebra

private abbrev params : Bool → Bool → MvPolynomial (Fin 2) ℤ := fun _ _ => 1
private abbrev weight : Fin 2 → Bool →₀ ℕ := fun _ => 0
private abbrev corner (order : List (Fin 2)) :=
  (isIdempotentElem_violMk_redProj ℤ params weight (0 : Multiset Bool) order).Corner

local instance (order : List (Fin 2)) : HasDerivedCategory.{0, 0} (corner order)ᵐᵒᵖ :=
  HasDerivedCategory.small _

example : (braidingFunctor.{0} ℤ params weight (0 : Multiset Bool) [0, 1] [1, 0]).IsTriangulated :=
  inferInstance

end NonVacuity.WebsterBraidTriangle

namespace NonVacuity.WebsterRightTensor

open DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1200] Ring.toIntAlgebra

local instance : HasDerivedCategory.{0, 0} ℤᵐᵒᵖ := HasDerivedCategory.small ℤᵐᵒᵖ

private abbrev integralModel := DGModuleCat.of ℤᵐᵒᵖ (Categorification.InDegreeZero ℤ)

example :
    Mono ((homologyFunctor (A := ℤᵐᵒᵖ) ℤ 0).map
      ((Categorification.derivedRightTensor ℤ ℤ ℤ).map (Q.map (𝟙 integralModel)))) := by
  let μ := AddMonoidHom.id (Categorification.BalancedTensor ℤ ℤ ℤ ℤ ℤ)
  exact Categorification.mono_derivedRightTensorHomology_of_balanced (k := ℤ) (X := ℤ)
    (fun c n => mul_comm n c) (fun c n => mul_comm n c) (𝟙 integralModel) μ
    (fun _ _ => rfl) Function.injective_id

end NonVacuity.WebsterRightTensor

end

namespace NonVacuity.WebsterCoevaluationTrace

open Categorification Stendhal KLR KLRAlgebra TypeA

local notation "E" => ((1, 0) : ℚ × ℚ)
local notation "F" => ((0, 1) : ℚ × ℚ)
local notation "cut" => (fun _ : Unit => F)

example :
    coevaluationTrace (e := E) cut =
      ⨆ j, ⨆ f : rIdeal (cut j) →ₗ[(ℚ × ℚ)ᵐᵒᵖ] rIdeal E, LinearMap.range f :=
  coevaluationTrace_eq_iSup_range cut (fun _ => by simp [IsIdempotentElem])

example (N : Submodule (ℚ × ℚ)ᵐᵒᵖ (rIdeal E)) :
    N = coevaluationTrace cut ↔ IsSimpleModule (ℚ × ℚ)ᵐᵒᵖ (rIdeal E ⧸ N) := by
  apply coevaluationTrace_eq_iff_simpleQuotient (by simp [IsIdempotentElem])
    cut (RingHom.fst ℚ ℚ) rfl (fun _ => rfl) _ _ N
  · intro x h
    have hx : (x : ℚ × ℚ).2 = 0 := by
      simpa using (congrArg Prod.snd x.property).symm
    have hzero : x = 0 := Subtype.ext (Prod.ext h hx)
    rw [hzero]
    exact Submodule.zero_mem _
  · intro x h
    change (x : ℚ × ℚ).1 ≠ 0 at h
    exact ⟨((x : ℚ × ℚ).1⁻¹, 0), Prod.ext (mul_inv_cancel₀ h) (mul_zero _)⟩

local notation "ν" => ({()} : Multiset Unit)
local notation "μ" => stendhalWeight 2 ν
local notation "Λ" => (fun _ : Fin 2 => Finsupp.single () 1)
local notation "Q" => (fun _ _ : Unit => (0 : MvPolynomial (Fin 2) ℚ))

private def allRight : Seq μ :=
  ⟨![Sum.inr 0, Sum.inr 1, Sum.inl ()], by
    decide⟩

example :
    ∃ z : rIdeal (tensorOfKLR Q Λ ν (e allRight)),
      z ∈ coevaluationTrace
        (fun _ : Unit => tensorOfKLR Q Λ ν (e (sadj (Multiset.card μ) 1 • allRight))) ∧
      z.val = tensorOfKLR Q Λ ν (x ⟨2, by decide⟩ * e allRight) := by
  simpa using bigon_mem_coevaluationTrace Q Λ ν _ allRight 1 (by decide) () 1 rfl rfl () rfl

end NonVacuity.WebsterCoevaluationTrace

namespace NonVacuity.WebsterFundamentalCoevaluation

open Categorification Categorification.Stendhal FundamentalCorner

example : IsSimpleModule (TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit))ᵐᵒᵖ
    (rIdeal terminalIdem ⧸ fundamentalCutTrace) :=
  (fundamentalCutTrace_eq_iff_simpleQuotient fundamentalCutTrace).mp rfl

example : Function.Surjective terminalCoefficient := terminalCoefficient_surjective

end NonVacuity.WebsterFundamentalCoevaluation

namespace NonVacuity.WebsterFundamentalResolution

open CategoryTheory Categorification.Stendhal.FundamentalCorner

example : fundamentalResolution.ShortExact := fundamentalResolution_shortExact

example (x : Abelian.Ext fundamentalTerminalSimple fundamentalTerminalSimple 1) : x = 0 :=
  fundamentalTerminalSimple_ext_eq_zero 1 (by decide) x

end NonVacuity.WebsterFundamentalResolution

namespace NonVacuity.WebsterVacuumBraidColumn

open KLR KLRAlgebra Stendhal Stendhal.BraidedStendhalAlgebra

private abbrev content := stendhalWeight 2 (0 : Multiset Unit)
private def ordered : Seq content := Seq.ofList [.inr 0, .inr 1] (by decide)
private def exchanged : Seq content := Seq.ofList [.inr 1, .inr 0] (by decide)
private noncomputable abbrev params : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev weights : Fin 2 → Unit →₀ ℕ := fun _ => 0

example :
    Module.finrank ℚ (violCorner ℚ params weights 0 exchanged (redWord ordered)) = 1 :=
  finrank_vacuum_braidColumn params weights (fun _ _ _ => rfl) exchanged ordered

example := finrank_vacuum_braidColumn_eq_standard params weights
  (fun _ _ _ => rfl) exchanged ordered

end NonVacuity.WebsterVacuumBraidColumn

namespace NonVacuity.WebsterBraidColumnPBW

open Categorification Categorification.KLR Categorification.Stendhal
open Categorification.Stendhal.BraidedStendhalAlgebra Equiv MvPolynomial

private abbrev content : Multiset Unit := {()}
private abbrev weight := stendhalWeight 3 content
private def top : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl (), .inr 1, .inr 2] (by decide)
private noncomputable abbrev parameters : Unit → Unit → MvPolynomial (Fin 2) ℚ :=
  fun _ _ => 0
private noncomputable abbrev weights : Fin 3 → Unit →₀ ℕ :=
  fun j => Finsupp.single () (j.val + 1)
private noncomputable def reducedWord (w : Perm (Fin weight.card)) :=
  (TypeA.exists_reduced _ w).choose
private theorem reducedChoice : TypeA.IsReducedChoice reducedWord :=
  fun w => (TypeA.exists_reduced _ w).choose_spec
private theorem symmetric : KLRSymm parameters := fun _ _ _ => rfl

example := span_violFixedTopColumn (Λ := weights) symmetric reducedChoice top [0, 2, 1]

end NonVacuity.WebsterBraidColumnPBW

namespace NonVacuity.WebsterGradedFundamentalCup
noncomputable section

open Categorification Categorification.Stendhal Categorification.Stendhal.FundamentalCorner
open DG
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "G" => Graded.oppositeGrade (tensorProductGrade FundamentalCorner.grading ({()} : Multiset Unit))

local instance : InternalGrading Tᵐᵒᵖ := gradedAlgebraInternalGrading G
local instance : BigradedDGRing Tᵐᵒᵖ := gradedAlgebraBigradedDGRing G
local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

local instance : CatModule.HasDerivedCategory.{1,0} (WeightCategory ℚ) :=
  CatModule.HasDerivedCategory.standard (WeightCategory ℚ)

local instance : CatModule.HasDerivedCategory.{1,0} (WeightCategory Tᵐᵒᵖ) :=
  CatModule.HasDerivedCategory.standard (WeightCategory Tᵐᵒᵖ)

example := gradedFundamentalCup
example := gradedFundamentalCap

example : gradedMiddleCharacter (MulOpposite.op middleIdem) = 1 := middleCharacter_middleIdem
example : gradedMiddleCharacter (MulOpposite.op terminalIdem) = 0 := middleCharacter_terminalIdem
example := gradedMiddleSimple_headEquiv
example := normalizedMiddleSimple_line
example : Subsingleton (normalizedMiddleSimple.obj ⟨0⟩) := normalizedMiddleSimple_subsingleton 0 (by decide)
example := gradedMiddleCapCupAdjunction
example := gradedMiddleCup_fieldIso
example := gradedMiddleCap_middleIso
example := gradedMiddleCap_terminal_isZero

example := middleResolution_maps_degree 2
example := middleResolution_exact_terminal 2
example := middleResolution_exact_middle 1
example := middleResolution_augmentation_surjective 0 1 (Or.inl rfl)
example := gradedMiddleComplex_exact ⟨0⟩
example := gradedMiddleComplex_exact ⟨2⟩
example := gradedMiddleCap_shiftedMiddleIso 2
example := gradedMiddleCap_shiftedTerminal_isZero 1
example := gradedMiddleCap_simpleIso
example := gradedMiddleCap_shiftedSimpleIso 1
example := gradedMiddleCupCap_fieldIso
example := gradedMiddleCup_scalarIso (-2)
example := gradedMiddleCupCap_scalarIso 3
example := gradedMiddleCupCap_shiftedScalarIso (-2) 4
example := fundamentalTraceCoefficient_line (-2)
example := fundamentalTraceCoefficient_off_diagonal 1 0 (by decide)
example := gradedFundamentalQuantumTraceIso
example := gradedFundamentalClockwiseCircleIso
example := gradedFundamentalClockwiseCircle_shiftedIso (-2) 4
example := compactScalarLine_class (-1)
example := fundamentalClockwiseCircle_class

end

end NonVacuity.WebsterGradedFundamentalCup
namespace NonVacuity.WebsterCupRHom

open CategoryTheory DG MulOpposite Categorification.Stendhal.Coevaluation
open scoped DG.DegreeZero

local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} ℚᵐᵒᵖ := DG.HasDerivedCategory.standard ℚᵐᵒᵖ
local instance : DG.CatModule.HasDerivedCategory.{1,0} (SingleObj ℚ) :=
  DG.CatModule.HasDerivedCategory.standard (SingleObj ℚ)
local instance : DG.CatModule.HasDerivedCategory.{1,0} (SingleObj ℚᵐᵒᵖ) :=
  DG.CatModule.HasDerivedCategory.standard (SingleObj ℚᵐᵒᵖ)

example := shiftedCupRHomFunctor ℚ ℚ (Fin 2 → ℚ) (-2)
example := capBimoduleCupRHomAdjunction ℚ ℚ (Fin 2 → ℚ)
example := capBimoduleRegularIso ℚ ℚ (Fin 2 → ℚ)
example := cupRHomObjIso ℚ ℚ (Fin 2 → ℚ) (DG.DGModuleCat.of ℚ ℚ)

end NonVacuity.WebsterCupRHom
namespace NonVacuity.WebsterFundamentalCupCap

open Categorification.Stendhal Categorification.Stendhal.FundamentalCorner
open scoped DG.DegreeZero

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)

local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} Tᵐᵒᵖ := DG.HasDerivedCategory.standard Tᵐᵒᵖ

example := terminalQuotientDualEquiv
example := fundamentalCup
example := fundamentalCap

end NonVacuity.WebsterFundamentalCupCap

namespace NonVacuity.WebsterFundamentalCupRegular

open Categorification.Stendhal Categorification.Stendhal.FundamentalCorner
open scoped DG.DegreeZero

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)

local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} Tᵐᵒᵖ := DG.HasDerivedCategory.standard Tᵐᵒᵖ

example := fundamentalCupRegularIso
example := fundamentalCapRegularIso

end NonVacuity.WebsterFundamentalCupRegular

noncomputable section

namespace NonVacuity.WebsterFundamentalDerivedCircle

open CategoryTheory Categorification Categorification.Stendhal FundamentalCorner
open scoped DG.DegreeZero

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)

local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} Tᵐᵒᵖ := DG.HasDerivedCategory.standard Tᵐᵒᵖ

example : fundamentalCap.obj (DG.DerivedCategory.Q.obj (DG.DGModuleCat.of Tᵐᵒᵖ
    (InDegreeZero (rIdeal terminalIdem ⧸ fundamentalCutTrace)))) ≅
    DG.DerivedCategory.Q.obj (DG.DGModuleCat.of ℚ (InDegreeZero ℚ)) :=
  fundamentalCap_terminalSimpleIso

example : (fundamentalCup ⋙ fundamentalCap).obj (DG.DerivedCategory.Q.obj
    (DG.DGModuleCat.of ℚ ℚ)) ≅ (shiftFunctor (DG.DerivedCategory.{1,0} ℚ) (-1)).obj
    (DG.DerivedCategory.Q.obj (DG.DGModuleCat.of ℚ (InDegreeZero ℚ))) :=
  fundamentalCupEvaluationRegularIso

end NonVacuity.WebsterFundamentalDerivedCircle

end

noncomputable section
namespace NonVacuity.WebsterMiddleCutEvaluation
open CategoryTheory CategoryTheory.Limits DG Categorification Categorification.Stendhal FundamentalCorner
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} Tᵐᵒᵖ := DG.HasDerivedCategory.standard Tᵐᵒᵖ
local instance : CatModule.HasDerivedCategory.{1,0} (SingleObj ℚ) :=
  CatModule.HasDerivedCategory.standard (SingleObj ℚ)
local instance : CatModule.HasDerivedCategory.{1,0} (SingleObj Tᵐᵒᵖ) :=
  CatModule.HasDerivedCategory.standard (SingleObj Tᵐᵒᵖ)

example : blackCount middle 1 () = 1 ∧ blackCount terminal 1 () = 0 :=
  ⟨middle_terminal_cuts.2.1, middle_terminal_cuts.2.2.2⟩

example : IsSimpleModule Tᵐᵒᵖ (rIdeal middleIdem ⧸ middleCutTrace) :=
  (middleCutTrace_eq_iff_simpleQuotient middleCutTrace).mp rfl

example := middleQuotientDualEquiv
example := middleCapCupAdjunction
example := middleCup_fieldIso
example := middleAdjointCap_middleIso
example := middleAdjointCap_terminal_isZero
example := middleProjectiveResolution
example := middleAdjointCap_middleSimpleIso
example := middleCupCap_fieldIso

local notation "cap" => Coevaluation.capBimoduleFunctor ℚ T MiddleCoefficient
local notation "headObj" => DG.DerivedCategory.Q.obj
  (DGModuleCat.of Tᵐᵒᵖ (InDegreeZero (rIdeal middleIdem ⧸ middleCutTrace)))

example : DG.DerivedCategory.finrankHomology ℚ (-2) ((cap).obj headObj) = 1 := by
  simpa using middleTor_finrank.{1} 2

example : DG.DerivedCategory.finrankHomology ℚ (-1) ((cap).obj headObj) = 0 := by
  simpa using middleTor_finrank.{1} 1

example : DG.DerivedCategory.finrankHomology ℚ (-1)
    ((middleCup ⋙ (cap)).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ))) = 1 := by
  simpa using middleCupCap_finrank.{1} (-1)

end NonVacuity.WebsterMiddleCutEvaluation

namespace NonVacuity.WebsterFundamentalBraidCorners
open Categorification Categorification.Stendhal Categorification.Stendhal.FundamentalCorner KLR KLRAlgebra

noncomputable section

example : LinearIndependent ℚ terminalBraidClasses :=
  fundamentalBraid_terminal_linearIndependent

example : braidProject (ψ 0 * ψ 1 * e crossedMiddle) ≠ 0 :=
  fundamentalBraid_mixed_ne_zero.2

example : braidProject (e middle) * braidProject (ψw [0,1,0]) * braidProject (e crossedMiddle) = 0 :=
  (fundamentalBraid_middle_middle_zero _).2

example : braidProject (ψ 1) * braidProject (ψ 1 * ψ 0 * e crossedTerminal) =
    terminalBraidClasses 1 :=
  fundamentalBraid_terminal_differentials.1

example : ∃ a b : ℚ, braidProject (e terminal) * braidProject (ψ 0) * braidProject (e crossedTerminal) =
    a • terminalBraidClasses 0 + b • terminalBraidClasses 1 :=
  fundamentalBraid_terminal_span _

end
end NonVacuity.WebsterFundamentalBraidCorners

namespace NonVacuity.WebsterFundamentalBraidWeight
open Categorification QuantumGroup Stendhal Stendhal.FundamentalCorner Stendhal.BraidedStendhalAlgebra

noncomputable section
private abbrev datum := CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
private abbrev realization := Matrix.Realization.std (UDot.A datum) ℂ

example : weightPairing datum realization (braidFundamentalWeight realization)
    (braidFundamentalWeight realization) = 1 / 2 :=
  braidFundamentalWeight_norm realization

example : fundamentalBraidMiddleClass ∈ Graded.shift (figureFiveCutGrade (Λ := wt)
    datum fundamentalBraidParameters (weightPairing datum realization)
    (fun _ => braidFundamentalWeight realization) terminal 1 0) 1 (3 / 2) :=
  (fundamentalBraidMiddleClass_resolutionWeight realization _).mpr rfl

example : fundamentalBraidMiddleClass ∉ Graded.shift (figureFiveCutGrade (Λ := wt)
    datum fundamentalBraidParameters (weightPairing datum realization)
    (fun _ => braidFundamentalWeight realization) terminal 1 0) 1 (0 : ℂ) := by
  rw [fundamentalBraidMiddleClass_resolutionWeight]
  norm_num


example : ∃ z, z ∈ Graded.shift (figureFiveCutGrade (Λ := wt) datum fundamentalBraidParameters
    (weightPairing datum realization) (fun _ => braidFundamentalWeight realization) terminal 1 0) 1 (3 / 2) ∧
    fundamentalBraidCutComplex.g z = 0 ∧ ¬ ∃ y, fundamentalBraidCutComplex.f y = z :=
  (fundamentalBraidHomology_weight_iff realization _).mpr rfl

example : ¬ ∃ z, z ∈ Graded.shift (figureFiveCutGrade (Λ := wt) datum fundamentalBraidParameters
    (weightPairing datum realization) (fun _ => braidFundamentalWeight realization) terminal 1 0) 1 (5 / 2) ∧
    fundamentalBraidCutComplex.g z = 0 ∧ ¬ ∃ y, fundamentalBraidCutComplex.f y = z := by
  intro h
  have he : (5 / 2 : ℂ) = 3 / 2 := (fundamentalBraidHomology_weight_iff realization _).mp h
  norm_num at he


example : (fundamentalBraidWeightComplex realization (5 / 2)).Exact :=
  fundamentalBraidWeightComplex_exact realization (by norm_num)

open CategoryTheory in
noncomputable example : (fundamentalBraidWeightComplex realization (3 / 2)).homology ≅ ModuleCat.of ℚ ℚ :=
  fundamentalBraidWeightComplex_homologyIso realization

end
end NonVacuity.WebsterFundamentalBraidWeight

namespace NonVacuity.WebsterFundamentalBraidHomology
open CategoryTheory Categorification.Stendhal.FundamentalCorner

noncomputable example : fundamentalBraidCutComplex.homology ≅ ModuleCat.of ℚ ℚ :=
  fundamentalBraidCutComplex_homologyIso

example : Function.Injective fundamentalBraidCutComplex.f ∧ Function.Surjective fundamentalBraidCutComplex.g :=
  fundamentalBraidCutComplex_ends

end NonVacuity.WebsterFundamentalBraidHomology

namespace NonVacuity.WebsterFundamentalBraidTensorHomology
open CategoryTheory Categorification.Stendhal.FundamentalCorner

example : Function.Exact braidSourceD₂ braidSourceD₁ ∧
    Function.Surjective braidSourceMiddleAugmentation :=
  ⟨fundamentalBraidSourceResolution.2.2.2.1,fundamentalBraidSourceResolution.2.2.2.2.2⟩

example : Function.Injective fundamentalBraidTensorComplex.f ∧
    Function.Surjective fundamentalBraidTensorComplex.g := fundamentalBraidTensorComplex_ends

noncomputable example : fundamentalBraidTensorComplex.homology ≅
    (ModuleCat.restrictScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℚ ℚ) :=
  fundamentalBraidTensorHomologyIso

end NonVacuity.WebsterFundamentalBraidTensorHomology

namespace NonVacuity.WebsterFundamentalBraidTargetHead
open CategoryTheory Categorification.Stendhal.FundamentalCorner

example : Function.Injective fundamentalBraidRightTensorComplex.f ∧
    Function.Surjective fundamentalBraidRightTensorComplex.g := fundamentalBraidRightTensorComplex_ends

noncomputable example : fundamentalBraidRightTensorComplex.homology ≅ braidTargetMiddleHead :=
  fundamentalBraidRightTensorHomologyIso

end NonVacuity.WebsterFundamentalBraidTargetHead

namespace NonVacuity.WebsterFundamentalBraidDerivedHead
open CategoryTheory DG Categorification Categorification.Stendhal
open BraidedStendhalAlgebra FundamentalCorner
open scoped DG.DegreeZero

local notation "ν" => ({()} : Multiset Unit)
local notation "K" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) (List.finRange 2)
local notation "U" => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ν) [1,0]
noncomputable local instance : DG.HasDerivedCategory.{1,0} Kᵐᵒᵖ := DG.HasDerivedCategory.standard _
noncomputable local instance : DG.HasDerivedCategory.{1,0} Uᵐᵒᵖ := DG.HasDerivedCategory.standard _

noncomputable example :
    (braidingFunctor ℚ Q wt ν (List.finRange 2) [1,0]).obj ((degreeZeroDerivedFunctor Kᵐᵒᵖ).obj braidSourceMiddleHead) ≅
      ((degreeZeroDerivedFunctor Uᵐᵒᵖ).obj braidTargetMiddleHead)⟦(1 : ℤ)⟧ :=
  fundamentalBraidDerivedHeadIso

noncomputable example := fundamentalBraidDerivedHeadHMinusOne.{1}
example := fundamentalBraidDerivedHead_isZero.{1} 0 (by decide)

end NonVacuity.WebsterFundamentalBraidDerivedHead

namespace NonVacuity.WebsterFundamentalBraidGradedSource
open CategoryTheory DG Categorification.Stendhal Categorification.Stendhal.FundamentalCorner

private theorem orderedMiddle : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel

noncomputable example := fundamentalBraidSourceLoadingIso middle orderedMiddle 2

example := fundamentalBraidSourceLoading_isKProjective terminal terminal_ordered 1

example := fundamentalBraidSourceGradedResolution ⟨0⟩

end NonVacuity.WebsterFundamentalBraidGradedSource

namespace NonVacuity.WebsterFundamentalBraidGradedCoend
open CategoryTheory DG Categorification.Stendhal Categorification.Stendhal.FundamentalCorner

noncomputable example := fundamentalBraidGradedCutIso terminal terminal_ordered 1 ⟨0⟩

example := fundamentalBraidGradedCutIso_d₂ ⟨0⟩

example := fundamentalBraidGradedCutIso_d₁ ⟨1⟩

end NonVacuity.WebsterFundamentalBraidGradedCoend

namespace NonVacuity.WebsterFundamentalBraidGradedTensorHomology
open Categorification.Stendhal.FundamentalCorner

example := fundamentalBraidGradedTensorComplex_ends 0

example := fundamentalBraidGradedTensorComplex_exact 1 (by decide)

noncomputable example := fundamentalBraidGradedTensorHomologyIso

end NonVacuity.WebsterFundamentalBraidGradedTensorHomology

namespace NonVacuity.WebsterFundamentalBraidGradedResolutionModel
open CategoryTheory DG Categorification.Stendhal Categorification.Stendhal.FundamentalCorner
open BraidedStendhalAlgebra
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] fundamentalBraidCoendSourceCornerGrades fundamentalBraidCoendTargetCornerGrades
  fundamentalBraidCoendSourceInternal fundamentalBraidCoendTargetInternal
  fundamentalBraidCoendSourceBigraded fundamentalBraidCoendTargetBigraded

local notation "R" κ:arg => ViolOrderCorner (k := ℚ) (Q := Q) (Λ := wt) («ν» := ({()} : Multiset Unit)) κ
local instance fundamentalBraidModelSourceDerived :
    CatModule.HasDerivedCategory.{1,0} (WeightCategory (R (List.finRange 2))ᵐᵒᵖ) :=
  CatModule.HasDerivedCategory.standard _
local instance fundamentalBraidModelTargetDerived :
    CatModule.HasDerivedCategory.{1,0} (WeightCategory (R ([1,0] : List (Fin 2)))ᵐᵒᵖ) :=
  CatModule.HasDerivedCategory.standard _

example := fundamentalBraidGradedResolutionAugmentation_quasiIso

noncomputable example := fundamentalBraidGradedDerivedModelIso.{1}

noncomputable example := fundamentalBraidGradedDerivedHomologyIso.{1}

example := fundamentalBraidGradedDerivedCohomology_isZero.{1} 0 0 (Or.inl (by decide))

example := fundamentalBraidGradedDerivedCohomology_isZero.{1} 1 (-1) (Or.inr (by decide))

noncomputable example := fundamentalBraidGradedHomologyTargetIso

noncomputable example := fundamentalBraidGradedDerivedTargetIso.{1}

end NonVacuity.WebsterFundamentalBraidGradedResolutionModel
end

namespace NonVacuity.WebsterCupRHomRegular

open CategoryTheory DG MulOpposite Categorification.Stendhal.Coevaluation
open scoped DG.DegreeZero

local instance : DG.HasDerivedCategory.{1,0} ℚ := DG.HasDerivedCategory.standard ℚ
local instance : DG.HasDerivedCategory.{1,0} ℚᵐᵒᵖ := DG.HasDerivedCategory.standard ℚᵐᵒᵖ
local instance : DG.CatModule.HasDerivedCategory.{1,0} (SingleObj ℚ) :=
  DG.CatModule.HasDerivedCategory.standard (SingleObj ℚ)
local instance : DG.CatModule.HasDerivedCategory.{1,0} (SingleObj ℚᵐᵒᵖ) :=
  DG.CatModule.HasDerivedCategory.standard (SingleObj ℚᵐᵒᵖ)

example := cupRHomRegularIso ℚ ℚ (Fin 2 → ℚ)
example := cupRHomTensorRegularIso ℚ ℚ (Fin 2 → ℚ)

end NonVacuity.WebsterCupRHomRegular

namespace NonVacuity.WebsterWeightTensor

noncomputable section

open Categorification CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local instance : CatModule.HasDerivedCategory.{1,0} (WeightCategory ℚ) :=
  CatModule.HasDerivedCategory.standard (WeightCategory ℚ)

private theorem leftAction {i j : ℤ} {a m : ℚ}
    (ha : a ∈ wgrading i) (hm : m ∈ DG.grading j) :
    a • m ∈ DG.grading (i+j) :=
  mul_mem_grading ha hm

private theorem rightAction {i j : ℤ} {b m : ℚ}
    (hb : b ∈ wgrading i) (hm : m ∈ DG.grading j) :
    op b • m ∈ DG.grading (j+i) :=
  mul_mem_grading hm hb

example := diagramWeightDerivedTensor (fun j => DG.grading (M := ℚ) j) leftAction rightAction

example := diagramWeightDerivedTensorObjIso (fun j => DG.grading (M := ℚ) j)
  leftAction rightAction (CatModule.isKProjective_representable (⟨0⟩ : WeightCategory ℚ))

private abbrev Rep := CatModule.representable (⟨0⟩ : WeightCategory ℚ)

private abbrev rationalWeightShortComplex : ShortComplex (CatModule (WeightCategory ℚ)) :=
  ShortComplex.mk (0 : CatModule.zero ⟶ Rep) (𝟙 Rep) (by simp)

private theorem rationalWeightShortComplex_shortExact : rationalWeightShortComplex.ShortExact := by
  refine (CatModule.shortExact_iff _).mpr fun X => ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, ?_⟩
  · intro y
    change y = 0 ↔ ∃ x, (0 : CatModule.zero ⟶ Rep).app X x = y
    constructor
    · rintro rfl
      exact ⟨0, map_zero _⟩
    · rintro ⟨x, rfl⟩
      rfl
  · exact Function.surjective_id

example : ObjectProperty.extensionProductIter
    (⊤ : ObjectProperty (CatModule.DerivedCategory.{1,0} (WeightCategory ℚ))) 1
    (CatModule.DerivedCategory.Q.obj Rep) :=
  WeightModuleFiltration.extensionProductIter
    (WeightModuleFiltration.append (L := fun _ : Unit => Rep) () rationalWeightShortComplex
      rationalWeightShortComplex_shortExact
      (WeightModuleFiltration.nil (CatModule.isZero_of_subsingleton _)) ⟨Iso.refl Rep⟩)
    ⊤ (fun _ _ => trivial) (fun _ _ => trivial)

example := diagramWeightDerivedTensorObjIsoOfResolution (fun j => DG.grading (M := ℚ) j)
  leftAction rightAction (𝟙 Rep) (CatModule.isKProjective_representable (⟨0⟩ : WeightCategory ℚ))
  (CatModule.isQuasiIso_id Rep) (by
    let tensor := (diagramWeightBimodule (fun j => DG.grading (M := ℚ) j)
      leftAction rightAction).tensorFunctor
    change CatModule.IsQuasiIso (tensor.map (𝟙 Rep))
    rw [tensor.map_id Rep]
    exact CatModule.isQuasiIso_id _)


example : CatModule.IsQuasiIso (𝟙 ((diagramWeightBimodule
    (fun j => DG.grading (M := ℚ) j) leftAction rightAction).left (⟨0⟩ : WeightCategory ℚ))) := by
  let G := fun j => DG.grading (M := ℚ) j
  let Z : WeightCategory ℚ := ⟨0⟩
  let N := (diagramWeightBimodule G leftAction rightAction).left Z
  exact diagramWeightLeft_isQuasiIso_of_cohomology G leftAction rightAction (Iso.refl N) (𝟙 N)
    (fun X => CatModule.isQuasiIso_id N X 0)
    (fun X n hn => diagramWeightLeft_cohomology_subsingleton G leftAction rightAction X Z hn)


example := diagramWeightDerivedTensorRepresentableIso (fun j => DG.grading (M := ℚ) j)
  leftAction rightAction (⟨1⟩ : WeightCategory ℚ)


example : (diagramWeightDerivedTensor (fun j => DG.grading (M := ℚ) j) leftAction rightAction).Additive :=
  inferInstance


example := diagramWeightTensorShiftNatIso (fun j => DG.grading (M := ℚ) j) leftAction rightAction 1


example : (diagramWeightTensorHomotopy (fun j => DG.grading (M := ℚ) j)
    leftAction rightAction).CommShift ℤ := inferInstance


example := diagramWeightTensorConeIso (fun j => DG.grading (M := ℚ) j)
  leftAction rightAction (𝟙 Rep)

example : (diagramWeightTensorHomotopy (fun j => DG.grading (M := ℚ) j)
    leftAction rightAction).IsTriangulated := inferInstance


example : (diagramWeightDerivedTensor (fun j => DG.grading (M := ℚ) j)
    leftAction rightAction).IsTriangulated := inferInstance

example : CategoryTheory.Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor
    (⟨1⟩ : WeightCategory ℚ) 0).obj
    ((diagramWeightDerivedTensor (fun j => DG.grading (M := ℚ) j) leftAction rightAction).obj
      (CatModule.DerivedCategory.Q.obj Rep))) := by
  let e (Z : WeightCategory ℚ) (_ : PLift (Z.as = 0)) : Z ⟶ Z := 𝟙 Z
  refine diagramWeightDerivedTensor_cohomology_isZero_of_loading_support
    (fun j => DG.grading (M := ℚ) j) leftAction rightAction (𝟙 Rep)
    (CatModule.isKProjective_representable (⟨0⟩ : WeightCategory ℚ)) (CatModule.isQuasiIso_id Rep)
    ⟨1⟩ 0 e ?_ ?_
  · intro Z m _
    by_cases h : Z.as = 0
    · exact AddSubgroup.subset_closure
        ⟨Z, ⟨h⟩, 𝟙 Z, m, by
          change m = Rep.act (𝟙 Z) (Rep.act (𝟙 Z) m)
          rw [Rep.act_id', Rep.act_id']⟩
    · have hm : (m : (⟨0⟩ : WeightCategory ℚ) ⟶ Z) = 0 := by
        apply WeightCategory.hom_ext
        have hmem := WeightCategory.mem_wgrading (show (⟨0⟩ : WeightCategory ℚ) ⟶ Z from m)
        change m.val ∈ DG.grading (M := ℚ) (Z.as - 0) at hmem
        exact ((DG.mem_degreeZeroGrading_iff ℚ).mp hmem).resolve_left (by simpa using h)
      rw [show m = 0 from hm]
      exact zero_mem _
  · intro Z i p
    have hp : p = 0 := by
      apply Subtype.ext
      have hp' : p.val ∈ DG.grading (M := ℚ) (1 - Z.as) := p.property
      have hi := i.down
      exact ((DG.mem_degreeZeroGrading_iff ℚ).mp hp').resolve_left (by omega)
    rw [hp, map_zero]


private abbrev rationalWeightGrading (j : ℤ) := DG.grading (M := ℚ) j

example : ∀ X : WeightCategory ℚ, Function.Exact
    ((diagramWeightLeftLinearMap rationalWeightGrading rationalWeightGrading
      leftAction rightAction leftAction rightAction (⟨0⟩ : WeightCategory ℚ)
      (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (fun _ {_} h => h)).app X)
    ((diagramWeightLeftLinearMap rationalWeightGrading rationalWeightGrading
      leftAction rightAction leftAction rightAction (⟨0⟩ : WeightCategory ℚ)
      (0 : ℚ →ₗ[ℚ] ℚ) (fun _ {_} _ => zero_mem _)).app X) :=
  diagramWeightLeftLinearMap_exact _ _ leftAction rightAction leftAction rightAction _
    (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (fun _ {_} h => h) _ leftAction rightAction
    (0 : ℚ →ₗ[ℚ] ℚ) (fun _ {_} _ => zero_mem _) (by
      intro x
      exact ⟨fun _ => ⟨x, rfl⟩, fun _ => rfl⟩)

private theorem rationalWeightRepresentable_cohomology_one :
    CategoryTheory.Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor
      (⟨0⟩ : WeightCategory ℚ) 1).obj
      ((diagramWeightDerivedTensor rationalWeightGrading leftAction rightAction).obj
        (CatModule.DerivedCategory.Q.obj Rep))) := by
  let X : WeightCategory ℚ := ⟨0⟩
  let M := (diagramWeightBimodule rationalWeightGrading leftAction rightAction).left X
  let D := CatModule.DerivedCategory.cohomologyFunctor X 1
  refine CategoryTheory.Limits.IsZero.of_iso ?_
    (D.mapIso (diagramWeightDerivedTensorRepresentableIso rationalWeightGrading leftAction rightAction X))
  refine CategoryTheory.Limits.IsZero.of_iso ?_
    ((CatModule.DerivedCategory.cohomologyFunctorFactorsh X 1).app
      ((CatModule.HomotopyCategory.quotient _).obj M))
  let H := _root_.HomotopyCategory.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 1
  refine CategoryTheory.Limits.IsZero.of_iso ?_
    (H.mapIso ((CatModule.HomotopyCategory.evalFactors X).app M))
  refine CategoryTheory.Limits.IsZero.of_iso ?_
    ((_root_.HomotopyCategory.homologyFunctorFactors AddCommGrpCat (ComplexShape.up ℤ) 1).app
      ((CatModule.evalComplex X).obj M))
  apply ShortComplex.isZero_homology_of_isZero_X₂
  apply AddCommGrpCat.isZero_of_iff_subsingleton.mpr
  change Subsingleton (DG.grading (M := M.obj X) 1)
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := (InDegreeZero.mem_grading_iff (M := rationalWeightGrading (X.as - X.as))).mp x.property
  have hy := (InDegreeZero.mem_grading_iff (M := rationalWeightGrading (X.as - X.as))).mp y.property
  exact (hx.resolve_left (by decide)).trans (hy.resolve_left (by decide)).symm

example : CategoryTheory.Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor
    (⟨0⟩ : WeightCategory ℚ) 1).obj
    ((diagramWeightDerivedTensor rationalWeightGrading leftAction rightAction).obj
      (CatModule.DerivedCategory.Q.obj Rep))) :=
  WeightModuleFiltration.diagramWeightDerivedTensor_cohomology_isZero _ leftAction rightAction
    (WeightModuleFiltration.append (L := fun _ : Unit => Rep) () rationalWeightShortComplex
      rationalWeightShortComplex_shortExact
      (WeightModuleFiltration.nil (CatModule.isZero_of_subsingleton _)) ⟨Iso.refl Rep⟩)
    ⟨0⟩ 1 (fun _ _ => rationalWeightRepresentable_cohomology_one)

end

end NonVacuity.WebsterWeightTensor

namespace NonVacuity.WebsterWeightCoend

noncomputable section

open Categorification CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

private abbrev QWeight := WeightCategory ℚ
private abbrev G := fun j => DG.grading (M := ℚ) j

private theorem leftAction {i j : ℤ} {a m : ℚ}
    (ha : a ∈ wgrading i) (hm : m ∈ G j) : a • m ∈ G (i + j) :=
  mul_mem_grading ha hm

private theorem rightAction {i j : ℤ} {a m : ℚ}
    (ha : a ∈ wgrading i) (hm : m ∈ G j) : op a • m ∈ G (j + i) :=
  mul_mem_grading hm ha

private def product : ℚ →+ ℚ →+ ℚ where
  toFun x :=
    { toFun := fun y => x * y
      map_zero' := mul_zero _
      map_add' := mul_add x }
  map_zero' := AddMonoidHom.ext fun y => zero_mul y
  map_add' x y := AddMonoidHom.ext fun z => add_mul x y z

private theorem productWeight {i j : ℤ} {x y : ℚ}
    (hx : x ∈ G i) (hy : y ∈ G j) : product x y ∈ G (i + j) :=
  mul_mem_grading hx hy

private theorem productBalanced (b x y : ℚ) : product (op b • x) y = product x (b • y) :=
  mul_assoc x b y

example := CornerTensor.liftAdd (k := ℚ) (1 : ℚ) 1 1 product
  (fun c x y => by change (c * x) * y = x * (c * y); ring)
  (fun x y => by simp)
  (fun x c y => by change (x * (1 * c * 1)) * y = x * ((1 * c * 1) * y); ring)

private theorem unitIdempotent : IsIdempotentElem (1 : ℚ) := by simp [IsIdempotentElem]

private abbrev UnitCorner := cornerBimodule (1 : ℚ) 1

private def projectedProduct : UnitCorner →+ UnitCorner →+ ℚ :=
  ((product.flip).compl₂ (cornerBimodule (1 : ℚ) 1).subtype).comp
    (cornerBimodule (1 : ℚ) 1).subtype

private theorem projectedProduct_balanced (b : unitIdempotent.Corner) (x y : UnitCorner) :
    projectedProduct (b • x) y = projectedProduct x (op b • y) := by
  change y.val * (b.val * x.val) = (y.val * b.val) * x.val
  exact (mul_assoc _ _ _).symm

example := cornerTensorCutLift_tmul (k := ℚ) unitIdempotent unitIdempotent unitIdempotent
  projectedProduct projectedProduct_balanced
  (cornerSandwichAdd unitIdempotent unitIdempotent (1 : ℚ))
  (cornerSandwichAdd unitIdempotent unitIdempotent (1 : ℚ))

example := diagramWeightCoendProduct G G G leftAction rightAction leftAction rightAction
  product productWeight productBalanced (⟨0⟩ : QWeight) (⟨0⟩ : QWeight)

section

open CategoryTheory.Limits CategoryTheory.Pretriangulated

local instance : CatModule.HasDerivedCategory.{1,0} QWeight :=
  CatModule.HasDerivedCategory.standard QWeight

example (X : QWeight) (T : Triangle (CatModule.DerivedCategory QWeight))
    (hT : T ∈ distTriang _) (n : ℤ)
    (h₀ : IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj T.obj₂))
    (h₁ : IsZero ((CatModule.DerivedCategory.cohomologyFunctor X (n + 1)).obj T.obj₂)) :=
  weightCohomologyShiftIso X T hT n h₀ h₁

end

private theorem productLeft (a x y : ℚ) : product (a • x) y = a • product x y :=
  mul_assoc a x y

example := diagramWeightCoendProductHom G G G leftAction rightAction leftAction rightAction
  product productWeight productBalanced (⟨0⟩ : QWeight) leftAction rightAction productLeft

private theorem productRight (c x y : ℚ) : product x (op c • y) = op c • product x y :=
  (mul_assoc x y c).symm

example := diagramWeightCoendProductNatTrans G G G leftAction rightAction leftAction rightAction
  product productWeight productBalanced leftAction rightAction productLeft productRight

private theorem productSpan :
    AddSubgroup.closure (Set.range fun z : ℚ × ℚ => product z.1 z.2) = ⊤ := by
  apply top_unique
  intro z _
  apply AddSubgroup.subset_closure
  exact ⟨(z, 1), mul_one z⟩

example := diagramWeightCoendProduct_surjective G G G leftAction rightAction leftAction rightAction
  product productWeight productBalanced (⟨0⟩ : QWeight) (⟨0⟩ : QWeight) productSpan

example := diagramWeightTensorSlice_leftInverse G G leftAction rightAction leftAction rightAction
  (⟨0⟩ : QWeight) (⟨0⟩ : QWeight)

example (G' H' : ℤ → Submodule ℚ ℚ) (d : ℤ) :=
  Categorification.Graded.balancedTensorIntScalarAddEquiv_map_grade
    (k := ℚ) (A := ℚ) (fun c m : ℚ => mul_comm m c) G' H' d

private def scalarGroundGrade (d : ℤ) : Submodule ℚ ℚ :=
  { carrier := G d
    add_mem' := (G d).add_mem
    zero_mem' := (G d).zero_mem
    smul_mem' := fun c x hx => by
      change c • x ∈ G d
      simpa only [zero_add] using leftAction (i := 0)
        (InDegreeZero.ring_mem_grading_zero c) hx }

local instance instGroundTensorRationalDecomposition :
    DirectSum.Decomposition (fun d => (scalarGroundGrade d).toAddSubgroup) :=
  inferInstanceAs (DirectSum.Decomposition G)

example :=
  diagramWeightTensorGroundGradeEquiv (B := ℚ) scalarGroundGrade scalarGroundGrade
    (fun ha hm => leftAction ha hm) (fun ha hm => rightAction ha hm)
    (fun ha hm => leftAction ha hm) (fun ha hm => rightAction ha hm)
    (fun c m : ℚ => mul_comm m c) (⟨0⟩ : QWeight) (⟨0⟩ : QWeight)

example := diagramWeightTensorOrdinary_range_eq_grade G G leftAction rightAction leftAction rightAction
  (⟨0⟩ : QWeight) (⟨1⟩ : QWeight)

example := diagramWeightOrdinaryProjection_tmul G G leftAction rightAction leftAction rightAction
  (⟨0⟩ : QWeight) (⟨1⟩ : QWeight)
  (⟨1, InDegreeZero.ring_mem_grading_zero (1 : ℚ)⟩ : G 0)
  (⟨1, InDegreeZero.ring_mem_grading_zero (1 : ℚ)⟩ : G 0)

private abbrev rationalCoefficient := diagramWeightBimodule G leftAction rightAction

private abbrev rationalRight := rationalCoefficient.right (⟨0⟩ : QWeight)

private abbrev rationalLeft := rationalCoefficient.left (⟨0⟩ : QWeight)

example :=
  catTensorCohomologyZeroEquivOfQuasiIso (L := rationalRight)
    (fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩)
    (fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩)
    (fun _ {_} _ => InDegreeZero.d_apply _ _)
    (𝟙 rationalLeft) (CatModule.IsQuasiIso.of_isIso _)
    (fun {_ _} g => WeightCategory.mem_grading_iff.mpr
      (InDegreeZero.ring_mem_grading_zero g.val))

example (n : ℤ) :=
  letI := CatModule.HasDerivedCategory.standard QWeight
  localizedWeightCohomologyIso (⟨0⟩ : QWeight) n rationalLeft

example (hK : CatModule.IsKProjective rationalLeft) :=
  letI := CatModule.HasDerivedCategory.standard QWeight
  diagramWeightDerivedTensorH0IsoOfResolution G leftAction rightAction
    (𝟙 rationalLeft) hK (CatModule.IsQuasiIso.of_isIso _)
    (fun _ {_} _ => InDegreeZero.d_apply _ _)
    (fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩)
    (⟨0⟩ : QWeight)

example (n : ℤ) :=
  letI := CatModule.HasDerivedCategory.standard QWeight
  localizedWeightCohomologyIso_naturality (⟨0⟩ : QWeight) n (𝟙 rationalLeft)

example (hK : CatModule.IsKProjective rationalLeft) :=
  letI := CatModule.HasDerivedCategory.standard QWeight
  diagramWeightDerivedTensorObjIso_naturality G leftAction rightAction (𝟙 rationalLeft) hK hK


example (hK : CatModule.IsKProjective rationalLeft) :=
  letI := CatModule.HasDerivedCategory.standard QWeight
  diagramWeightDerivedTensorH0IsoOfResolution_naturality G leftAction rightAction
    (𝟙 rationalLeft) (𝟙 rationalLeft) (𝟙 rationalLeft) hK hK
    (CatModule.IsQuasiIso.of_isIso _) (CatModule.IsQuasiIso.of_isIso _)
    (fun _ {_} _ => InDegreeZero.d_apply _ _) (fun _ {_} _ => InDegreeZero.d_apply _ _)
    (fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩)
    (fun _ => ⟨InDegreeZero.mem_grading_zero, InDegreeZero.d_apply _⟩) (⟨0⟩ : QWeight)

end

end NonVacuity.WebsterWeightCoend

namespace NonVacuity.WebsterGroundTensorHomology

open Categorification DG
open scoped DG.DegreeZero

noncomputable example :=
  letI := HasDerivedCategory.small ℚ
  derivedTensorHomologyIsoOrdinaryLinear (R := ℚ) (A := ℚ) (B := ℚ) (M := ℚ) ℚ

end NonVacuity.WebsterGroundTensorHomology

namespace NonVacuity.WebsterGradedCorner
noncomputable section

open Categorification CategoryTheory DG
open scoped DG.DegreeZero

private abbrev R := MvPolynomial Unit ℚ

private def G : ℤ → Submodule ℚ R :=
  MvPolynomial.weightedHomogeneousSubmodule ℚ (fun _ : Unit => (1 : ℤ))

local instance : GradedAlgebra G := MvPolynomial.weightedGradedAlgebra ℚ _

private theorem h : IsIdempotentElem (1 : R) := by simp [IsIdempotentElem]

private theorem h0 : (1 : R) ∈ G 0 := SetLike.GradedOne.one_mem

noncomputable example := by
  letI := Graded.cornerGradedAlgebra G h h0
  letI := gradedAlgebraInternalGrading (Categorification.Graded.oppositeGrade
    (Graded.cornerGrading G h))
  letI := gradedAlgebraBigradedDGRing (Categorification.Graded.oppositeGrade
    (Graded.cornerGrading G h))
  letI : CatModule.HasDerivedCategory.{1,0} (WeightCategory h.Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard (WeightCategory h.Cornerᵐᵒᵖ)
  exact diagramCornerWeightDerivedRightTensor G h h h0 h0

example := by
  letI := Graded.cornerGradedAlgebra G h h0
  letI := gradedAlgebraInternalGrading (Categorification.Graded.oppositeGrade
    (Graded.cornerGrading G h))
  letI := gradedAlgebraBigradedDGRing (Categorification.Graded.oppositeGrade
    (Graded.cornerGrading G h))
  exact diagramCornerWeightRightCoendProduct G h h h0 h0 h h0
    (⟨0⟩ : WeightCategory h.Cornerᵐᵒᵖ) (⟨0⟩ : WeightCategory h.Cornerᵐᵒᵖ)

end

end NonVacuity.WebsterGradedCorner

namespace NonVacuity.WebsterScalarHom

noncomputable section

open Categorification CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

local instance : InternalGrading ℚ := scalarInternalGrading ℚ
local instance : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local instance : CatModule.HasDerivedCategory.{1,0} (WeightCategory ℚ) :=
  CatModule.HasDerivedCategory.standard (WeightCategory ℚ)

private def weightPiece (j : ℤ) : Submodule ℚ ℚ where
  carrier := (DG.grading (M := ℚ) j : Set ℚ)
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c m hm := by
    change c * m ∈ DG.grading j
    simpa only [zero_add] using mul_mem_grading (InDegreeZero.ring_mem_grading_zero c) hm

private theorem rightAction {i j : ℤ} {b m : ℚ}
    (hb : b ∈ wgrading i) (hm : m ∈ weightPiece j) :
    op b • m ∈ weightPiece (j + i) := by
  change m * b ∈ DG.grading (j + i)
  exact mul_mem_grading (show m ∈ DG.grading j from hm) hb

example := diagramWeightScalar_isKProjective ℚ weightPiece rightAction (⟨0⟩ : WeightCategory ℚ)

example := diagramWeightScalarDerivedHom ℚ weightPiece rightAction

end

end NonVacuity.WebsterScalarHom

namespace NonVacuity.WebsterAuxiliaryBraiding

noncomputable section

open Categorification CategoryTheory DG Stendhal FundamentalCorner BraidedStendhalAlgebra
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν₀" => ({()} : Multiset Unit)
local notation "V" => violAuxiliaryGrade (ν := ν₀) FundamentalCorner.grading
local notation "E" => isIdempotentElem_violMk_redProj ℚ Q wt ν₀
local notation "H" => redProj_mem_violAuxiliaryGrade (ν := ν₀) FundamentalCorner.grading
local notation "S" => fun κ => Categorification.Graded.oppositeGrade (Graded.cornerGrading V (E κ))

example := by
  letI := Graded.cornerGradedAlgebra V (E [1, 0]) (H [1, 0])
  letI := Graded.cornerGradedAlgebra V (E [0, 1]) (H [0, 1])
  letI := gradedAlgebraInternalGrading (S [1, 0])
  letI := gradedAlgebraInternalGrading (S [0, 1])
  letI := gradedAlgebraBigradedDGRing (S [1, 0])
  letI := gradedAlgebraBigradedDGRing (S [0, 1])
  letI : CatModule.HasDerivedCategory.{1,0} (WeightCategory (E [1, 0]).Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard _
  letI : CatModule.HasDerivedCategory.{1,0} (WeightCategory (E [0, 1]).Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard _
  exact auxiliaryGradedBraidingFunctor (ν := ν₀) FundamentalCorner.grading [1, 0] [0, 1]

example := by
  letI := Graded.cornerGradedAlgebra V (E [1, 0]) (H [1, 0])
  letI := Graded.cornerGradedAlgebra V (E [0, 1]) (H [0, 1])
  letI := gradedAlgebraInternalGrading (S [1, 0])
  letI := gradedAlgebraInternalGrading (S [0, 1])
  letI := gradedAlgebraBigradedDGRing (S [1, 0])
  letI := gradedAlgebraBigradedDGRing (S [0, 1])
  letI : CatModule.HasDerivedCategory.{1,0} (WeightCategory (E [1, 0]).Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard _
  letI : CatModule.HasDerivedCategory.{1,0} (WeightCategory (E [0, 1]).Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard _
  let Z : WeightCategory (E [1, 0]).Cornerᵐᵒᵖ := ⟨0⟩
  let X : WeightCategory (E [0, 1]).Cornerᵐᵒᵖ := ⟨0⟩
  let R := CatModule.representable Z
  refine auxiliaryGradedBraiding_cohomology_isZero_of_loading_support
    (ν := ν₀) FundamentalCorner.grading [1, 0] [0, 1] (𝟙 R)
    (CatModule.isKProjective_representable Z) (CatModule.isQuasiIso_id R) X (-1)
    (ι := Empty) (fun i => nomatch i) ?_ (fun i => nomatch i)
  intro W x hx
  have hg : (show (Z ⟶ W) from x) ∈ DG.grading (-1 : ℤ) := hx
  have hd := InDegreeZero.ring_mem_grading_iff.mp (WeightCategory.mem_grading_iff.mp hg)
  have hz : (show (Z ⟶ W) from x) = 0 :=
    WeightCategory.hom_ext (hd.resolve_left (by decide))
  rw [show x = 0 from hz]
  exact zero_mem _

end

end NonVacuity.WebsterAuxiliaryBraiding
namespace NonVacuity.WebsterLabelTwoUnknot

open Categorification.Webster.LabelTwo

example : LinearMap.ker (plus (k := ℤ)) = LinearMap.range minus :=
  ker_plus

example : LinearMap.ker (minus (k := ℤ)) = LinearMap.range plus :=
  ker_minus

noncomputable example := postTensorHomologyZero (k := ℚ)

noncomputable example := postTensorHomologyOdd (k := ℚ) 2 ⟨1,by decide⟩ (by decide)

noncomputable example := postTensorHomologyPositiveEven (k := ℚ) 1
  (by simp) (by decide)

end NonVacuity.WebsterLabelTwoUnknot

namespace NonVacuity.WebsterLabelTwoPolynomialPresentation

open Categorification.Webster.LabelTwo

example : middlePolynomialEquiv ℤ (squareQuotientVariable ℤ 0) = y₁ :=
  middlePolynomialEquiv_variable_zero ℤ

example : middlePolynomialEquiv ℤ (squareQuotientVariable ℤ 1) = y₂ :=
  middlePolynomialEquiv_variable_one ℤ

noncomputable example := specializedQuotientEquiv ℤ

example : Module.finrank ℚ (SquareQuotient ℚ) = 4 := finrank_squareQuotient ℚ

end NonVacuity.WebsterLabelTwoPolynomialPresentation
noncomputable section

namespace NonVacuity.WebsterLabelTwoMiddleDots

open Categorification.Stendhal.LabelTwo

example :
    middleDotQuotientAction ℚ (Ideal.Quotient.mk (middleDotIdeal ℚ)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) = dotEnd ℚ 0 + dotEnd ℚ 1 :=
  middleDotQuotientAction_sum ℚ

example : (dotEnd ℚ 1)^2 = 0 := dotEnd_sq ℚ 1

end NonVacuity.WebsterLabelTwoMiddleDots

end

noncomputable section

namespace NonVacuity.WebsterLabelTwoMiddleEndomorphism

open Categorification.Stendhal.LabelTwo
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

example : Function.Bijective (middleDotQuotientAction ℚ) :=
  (middleEndomorphismEquiv ℚ).bijective

example :
    middleEndomorphismEquiv ℚ (Ideal.Quotient.mk (middleDotIdeal ℚ)
      (MvPolynomial.X 0 + MvPolynomial.X 1)) = dotEnd ℚ 0 + dotEnd ℚ 1 :=
  middleEndomorphismEquiv_sum ℚ

end NonVacuity.WebsterLabelTwoMiddleEndomorphism

end

noncomputable section

namespace NonVacuity.WebsterLabelTwoMiddleFixedComplex

open Categorification Categorification.Stendhal Categorification.Stendhal.LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

example := rightMiddleComplex ℚ

example := rightMiddleDotSumQuotient ℚ

example : Function.Exact (fixedMinus ℚ) (fixedPlus ℚ) := fixedMinusPlus_exact ℚ

example : Function.Exact (fixedPlus ℚ) (fixedMinus ℚ) := fixedPlusMinus_exact ℚ

example :
    fixSub ℚ (StandardDotSumQuotient ℚ)
      (seqIdem (parameter ℚ) weights loading loading_ordered) ≃ₗ[ℚ] DualNumber ℚ :=
  middleCutDotSumEquiv ℚ

example := middleCutDotSum_scalar_mem_grade ℚ

example := middleCutDotSum_epsilon_mem_grade ℚ

example := middleCutDotSum_mem_grade_iff ℚ

open KLR

private abbrev higher : KLR.Seq (stendhalWeight 2 (({()} : Multiset Unit) + {()})) :=
  TypeA.sadj (Multiset.card (stendhalWeight 2 (({()} : Multiset Unit) + {()}))) 2 • loading

private theorem higher_ordered : IsRedOrdered higher := by
  unfold IsRedOrdered
  decide +kernel

example :
    Subsingleton (fixSub ℚ (Standard ℚ) (seqIdem (parameter ℚ) weights higher higher_ordered)) :=
  middleFixed_subsingleton_of_other_loading ℚ higher higher_ordered
    (by decide +kernel) (by decide +kernel)

example : Function.Exact (diagramMinus ℚ) (diagramPlus ℚ) := diagramMinusPlus_exact ℚ

example : Function.Exact (diagramPlus ℚ) (diagramMinus ℚ) := diagramPlusMinus_exact ℚ

example : Function.Exact (diagramPlus ℚ) (diagramMiddleAugmentation ℚ) :=
  diagramMiddleAugmentation_exact ℚ

example (n : ℕ) : (rightMiddleComplex ℚ).ExactAt (n + 1) :=
  rightMiddleComplex_exactAt ℚ n

example : QuasiIso (diagramMiddleToQuotient ℚ) := diagramMiddleToQuotient_quasiIso ℚ

example (a b : fixSub ℚ (Standard ℚ) (seqIdem (parameter ℚ) weights loading loading_ordered)) :
    terminalCutDotSumEquiv ℚ (terminalQuotientMap ℚ ((terminalToTwoMiddle ℚ).symm (a,b))) =
      (fixedAugmentation ℚ a, fixedAugmentation ℚ b) :=
  terminalCutDotSumEquiv_apply ℚ (a,b)

example := incomingDiagram_coordinates ℚ

example := incomingDiagram_translate_coordinates ℚ
example := middleStandardParabolicEquiv ℚ

example : Function.Bijective (testModuleMap ℚ) :=
  ⟨testModuleMap_injective ℚ, testModuleMap_surjective ℚ⟩

example := middleStandardGFin ℚ (labelTwoGradingDatum ℚ)

example :
    (middleStandardGradedEquiv ℚ (labelTwoGradingDatum ℚ)).toLinearEquiv =
      middleStandardParabolicEquiv ℚ :=
  middleStandardGradedEquiv_toLinearEquiv ℚ (labelTwoGradingDatum ℚ)

example := diagramPlus_degree_two ℚ

example := diagramMinus_degree_two ℚ

example := incomingExteriorDiagram_mem_grade ℚ

example := incomingExteriorTranslate_mem_grade ℚ

example := middleDotSumQuotientGFin ℚ

example (d : ℤ) := diagramPlusMinus_exact_in_degree ℚ d

example (d : ℤ) := diagramMinusPlus_exact_in_degree ℚ d

example (d : ℤ) := diagramPlusAugmentation_exact_in_degree ℚ d

example (d : ℤ) := diagramMiddleAugmentationAtDegree_surjective ℚ d

example (d : ℤ) := diagramSumCompanionAugmentation_exact_in_degree ℚ d

example (d : ℤ) := diagramDifferenceCompanionAugmentation_exact_in_degree ℚ d

example := middleEndomorphismFactorEquiv ℚ

example := factorDotSumQuotientEquiv ℚ

example (x : Standard ℚ) := middleDotSumStandardizationEquiv_mk ℚ x

example := middle_higher_eq

example := middle_upperLoadingIdeal_eq_singleton ℚ

example := rightMiddleDotSumQuotient_kills_higher ℚ

example :=
  leftStandardLayer_projective (parameter ℚ) weights loading loading_ordered

open scoped DG.DegreeZero

private abbrev middleAmbientRational :=
  TensorProductAlgebra ℚ (parameter ℚ) weights (({()} : Multiset Unit) + {()})

local instance instLabelTwoMiddleAmbientDerived : DG.HasDerivedCategory.{0, 0} middleAmbientRational :=
  DG.HasDerivedCategory.small _

local instance instLabelTwoMiddleIntegralDerived : DG.HasDerivedCategory.{0, 0} ℤ :=
  DG.HasDerivedCategory.small ℤ

example := exists_middleStandard_supportedResolution ℚ

example := exists_loadingStandard_supportedResolution ℚ ⟨loading, loading_ordered⟩

example := middleStandard_derivedTensorHomology_isZero ℚ (-1) (by decide)

example := relativeMiddleProjectiveResolution ℚ

example := middleStandardTensorEquiv ℚ

example := middleStandardTensorEquiv_plus ℚ

example := middleStandardTensorEquiv_minus ℚ

example := relativeMiddleTorZero ℚ

example (n : ℕ) := relativeMiddleTorPositive ℚ n (by decide)

open scoped DG.DegreeZero in
noncomputable example (n : ℕ) :=
  letI := DG.HasDerivedCategory.standard ℚ
  letI := DG.HasDerivedCategory.standard
    (TensorProductAlgebra ℚ (parameter ℚ) weights (({()} : Multiset Unit) + {()}))
  actualAmbientMiddleToRelativeTorIso ℚ (by decide) n

section

open DG
open scoped DG.DegreeZero

local notation "MiddleT" => TensorProductAlgebra ℚ (parameter ℚ) weights
  (({()} : Multiset Unit) + {()})

local notation "MiddleG" => middleTensorGrade ℚ (labelTwoGradingDatum ℚ)

local instance : InternalGrading MiddleT := gradedAlgebraInternalGrading MiddleG
local instance : BigradedDGRing MiddleT := gradedAlgebraBigradedDGRing MiddleG
local instance : CatModule.HasDerivedCategory.{1,0} (WeightCategory MiddleT) :=
  CatModule.HasDerivedCategory.standard (WeightCategory MiddleT)

example := middleSumWeight_distinguished ℚ

example := middleDifferenceWeight_distinguished ℚ

open CategoryTheory in
example (X : WeightCategory MiddleT) (n : ℤ)
    (h₀ : middleWeightStandardIsZero ℚ (𝟭 (CatModule.DerivedCategory (WeightCategory MiddleT))) X n)
    (h₁ : middleWeightStandardIsZero ℚ (𝟭 (CatModule.DerivedCategory (WeightCategory MiddleT))) X (n + 1)) :=
  middleSumWeightShiftIso ℚ (𝟭 (CatModule.DerivedCategory (WeightCategory MiddleT))) X n h₀ h₁

end

end NonVacuity.WebsterLabelTwoMiddleFixedComplex

end


noncomputable section

namespace NonVacuity.WebsterTerminalLoading

open Categorification CategoryTheory DG MulOpposite
open Categorification.Stendhal Categorification.Stendhal.FundamentalCorner
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local instance instTerminalVanishTestInternalGrading : InternalGrading Tᵐᵒᵖ :=
  gradedAlgebraInternalGrading (Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit)))
local instance instTerminalVanishTestBigradedRing : BigradedDGRing Tᵐᵒᵖ :=
  gradedAlgebraBigradedDGRing (Graded.oppositeGrade (tensorProductGrade grading ({()} : Multiset Unit)))
local instance instTerminalVanishTestScalarInternalGrading : InternalGrading ℚ := scalarInternalGrading ℚ
local instance instTerminalVanishTestScalarBigradedRing : BigradedDGRing ℚ := scalarBigradedDGRing ℚ
local instance instTerminalVanishTestScalarDerived : CatModule.HasDerivedCategory.{1,0} (WeightCategory ℚ) :=
  CatModule.HasDerivedCategory.standard _
local instance instTerminalVanishTestDiagramDerived : CatModule.HasDerivedCategory.{1,0} (WeightCategory Tᵐᵒᵖ) :=
  CatModule.HasDerivedCategory.standard _

example := gradedTerminalStandard_terminalCoefficient_cohomology_isZero
  (⟨0⟩ : WeightCategory ℚ) (n := -1) (by decide)

end NonVacuity.WebsterTerminalLoading

end

open CategoryTheory CategoryTheory.Limits DG
open scoped DG.DegreeZero

noncomputable section
namespace NonVacuity.WebsterActualBraidKernel

open Categorification Categorification.KLR Categorification.Stendhal
open Categorification.Stendhal.BraidedStendhalAlgebra

attribute [local instance 1200] Ring.toIntAlgebra

private abbrev ν : Multiset Bool := 0
private abbrev Q : Bool → Bool → MvPolynomial (Fin 2) ℤ := fun _ _ => 1
private abbrev Λ : Fin 2 → Bool →₀ ℕ := fun _ => 0
private def t : Seq (stendhalWeight 2 ν) :=
  ⟨fun j => Sum.inr (if j.val = 0 then 0 else 1), by decide⟩

private abbrev corner (order : List (Fin 2)) :=
  (isIdempotentElem_violMk_redProj ℤ Q Λ ν order).Corner

local instance (order : List (Fin 2)) : HasDerivedCategory.{0, 0} (corner order)ᵐᵒᵖ :=
  HasDerivedCategory.small _

private theorem root_zero (s : Seq (stendhalWeight 2 ν)) :
    adjacentBlockRoot 0 1 s = 0 := by
  funext r i
  have h (j : Fin (stendhalWeight 2 ν).card) : s.lbl j ≠ Sum.inl i := by
    intro he
    have hs := s.mem j
    change s.lbl j ∈ stendhalWeight 2 ν at hs
    simp [he, stendhalWeight] at hs
  simp [adjacentBlockRoot, blockBlackCount, h]

private theorem kernel_zero : blockLoadingKernel Q Λ t 0 1 = ⊥ := by
  have hupper : blockUpperIdeal ℤ Q Λ ν 0 1 (adjacentBlockRoot 0 1 t) (redWord t) = ⊥ := by
    apply le_antisymm (TwoSidedIdeal.span_le.mpr ?_) bot_le
    rintro _ ⟨s, _, h, _⟩
    rw [root_zero s, root_zero t] at h
    exact (lt_irrefl _ h).elim
  ext x
  change x.val.val ∈ blockUpperIdeal ℤ Q Λ ν 0 1 (adjacentBlockRoot 0 1 t) (redWord t) ↔ _
  rw [hupper, Submodule.mem_bot]
  constructor
  · intro hx
    rw [TwoSidedIdeal.mem_bot] at hx
    exact Subtype.ext (Subtype.ext hx)
  · rintro rfl
    exact (⊥ : TwoSidedIdeal _).zero_mem

example :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (corner [1, 0])ᵐᵒᵖ) ℤ 1).obj
      ((braidingFunctor ℤ Q Λ ν (redWord t) [1, 0]).obj (DG.DerivedCategory.Q.obj
        ((degreeZeroModuleFunctor (corner (redWord t))ᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t 0 1).X₃)))) :=
  blockPartialStandard_braid_homology_vanish_of_bot Q Λ t 0 1 [1, 0] kernel_zero 1 (by decide)

end NonVacuity.WebsterActualBraidKernel
end

noncomputable section
namespace NonVacuity.WebsterFirstPairSpectator

open CategoryTheory CategoryTheory.Limits DG
open scoped DG.DegreeZero
open Categorification Categorification.KLR Categorification.Stendhal
open Categorification.KLR.KLRAlgebra Categorification.TypeA
open Categorification.Stendhal.BraidedStendhalAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

private abbrev ν : Multiset Unit := {()} + {()}
private abbrev Q : Unit → Unit → MvPolynomial (Fin 2) ℤ := fun _ _ => 0
private abbrev Λ : Fin 3 → Unit →₀ ℕ := fun _ => Finsupp.single () 2
private def terminalLoading : Seq (stendhalWeight 3 ν) :=
  ⟨![.inr 0, .inr 1, .inl (), .inl (), .inr 2], by decide⟩

private abbrev corner (order : List (Fin 3)) :=
  (isIdempotentElem_violMk_redProj ℤ Q Λ ν order).Corner

local instance firstPairSpectatorDerived (order : List (Fin 3)) :
    HasDerivedCategory.{0, 0} (corner order)ᵐᵒᵖ := HasDerivedCategory.small _

private theorem terminalLoading_black_lt (p : Fin (stendhalWeight 3 ν).card) (i : Unit)
    (h : terminalLoading.lbl p = Sum.inl i) : p < redPos terminalLoading 2 := by
  have lastRed : terminalLoading.lbl ⟨4, by decide⟩ = Sum.inr 2 := by decide
  rw [← eq_redPos lastRed]
  cases i
  revert p
  decide +kernel

example :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (corner [1, 0, 2])ᵐᵒᵖ) ℤ 1).obj
      ((braidingFunctor ℤ Q Λ ν (redWord terminalLoading) [1, 0, 2]).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (corner (redWord terminalLoading))ᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ terminalLoading 0 1).X₃)))) :=
  firstPair_terminal_partialStandard_braid_homology_vanish Q Λ terminalLoading (by decide)
    terminalLoading_black_lt [1, 0, 2] 1 (by decide)

private abbrev lower := firstPairOneAfterSpectator false
private abbrev upper := sadj (stendhalWeight 3 ν).card 3 • lower
private abbrev F := (violMk ℤ Q Λ ν).comp (ofKLR ℤ Q Λ ν)
private abbrev crossing := F (ψ 3 * e upper)
private abbrev J := blockUpperIdeal ℤ Q Λ ν 0 1 (adjacentBlockRoot 0 1 lower) (redWord lower)

example : ∃ y : ViolQuotient ℤ Q Λ ν, F (e upper) * y = y ∧ crossing * y = crossing := by
  have strict : adjacentBlockRoot 0 1 lower < adjacentBlockRoot 0 1 upper := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 0 1 upper 2 () ≤
        adjacentBlockRoot 0 1 lower 2 ()) (h 2 ())
  have higher : F (e upper) ∈ J := TwoSidedIdeal.subset_span ⟨upper, by decide, strict, rfl⟩
  have support : crossing * F (e upper) = crossing := by
    rw [← map_mul F, mul_assoc, e_mul_self]
  have member : crossing ∈ J := support ▸ TwoSidedIdeal.mul_mem_left _ _ _ higher
  have fixed : F (e lower) * crossing = crossing := by
    rw [← map_mul F]
    apply congrArg F
    have step : sadj (stendhalWeight 3 ν).card 3 • upper = lower := by decide +kernel
    simp only [ψ_mul_e, step, ← mul_assoc, e_mul_self]
  exact firstPairOneAfter_blockKernel_principal Q Λ false (fun _ _ h => (h (Subsingleton.elim _ _)).elim)
    crossing member fixed

end NonVacuity.WebsterFirstPairSpectator
end


namespace NonVacuity.WebsterUnitParameters

noncomputable example :=
  Categorification.Stendhal.tensorProductUnitParameterEquiv
    (k := ℚ) (P := fun _ _ => 0) (P' := fun _ _ => 1)
    (fun _ : Fin 2 => Finsupp.single () 2) ({(), ()} : Multiset Unit)

open Categorification Categorification.KLR Categorification.Stendhal

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

noncomputable example (s : KLR.Seq (stendhalWeight 2 ({(), ()} : Multiset Unit)))
    (hs : IsRedOrdered s) :=
  leftStandardRestrictedEquiv (fun _ : Fin 2 => Finsupp.single () 2)
    (tensorProductUnitParameterEquiv (k := ℚ) (P := fun _ _ => 0) (P' := fun _ _ => 1)
      (fun _ : Fin 2 => Finsupp.single () 2) ({(), ()} : Multiset Unit)).toRingEquiv
    (fun t ht => tensorProductOffDiagonalEquiv_e
      (Q := fun _ : Unit => fun _ => (0 : MvPolynomial (Fin 2) ℚ)) (Q' := fun _ _ => 1)
      (Λ := fun _ : Fin 2 => Finsupp.single () 2)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim) t ht) s hs

end NonVacuity.WebsterUnitParameters

namespace NonVacuity.WebsterGradedTerminalStandard
open Categorification.Stendhal.FundamentalCorner

example := gradedTerminalStandardResolution_isKProjective

example := gradedTerminalStandardResolution_quasiIso

example := terminal_lt_middle

end NonVacuity.WebsterGradedTerminalStandard

namespace NonVacuity.WebsterGradedLeftStandard

open Categorification.Stendhal Categorification.Stendhal.FundamentalCorner

example : leftStandardUnit Q wt terminal terminal_ordered ∈
    gradedLeftStandard grading terminal terminal_ordered 0 :=
  gradedLeftStandard_mkQ_mem grading terminal terminal_ordered _
    (mk_e_mem_tensorProductGrade grading _ terminal terminal_ordered)

end NonVacuity.WebsterGradedLeftStandard

namespace NonVacuity.WebsterIncomparableStandardSupport

open Categorification Categorification.KLR Categorification.Stendhal

private abbrev content : Multiset Bool := {false, true}
private abbrev weight := stendhalWeight 2 content
private def source : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl false, .inr 1, .inl true] (by decide)
private def target : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl true, .inr 1, .inl false] (by decide)
private theorem sourceOrdered : IsRedOrdered source :=
  (redWord_eq_finRange_iff source).1 (by decide)
private theorem targetOrdered : IsRedOrdered target :=
  (redWord_eq_finRange_iff target).1 (by decide)
private theorem targetNotLE : ¬ StendhalLE target source := by
  intro h
  exact (by decide : ¬ blackCount target 1 true ≤ blackCount source 1 true) (h 1 true)
private theorem sourceNotLE : ¬ StendhalLE source target := by
  intro h
  exact (by decide : ¬ blackCount source 1 false ≤ blackCount target 1 false) (h 1 false)
private noncomputable abbrev parameters : Bool → Bool → MvPolynomial (Fin 2) ℚ :=
  fun i j => if i = j then 0 else 1
private noncomputable abbrev weights : Fin 2 → Bool →₀ ℕ :=
  fun _ => Finsupp.single false 2 + Finsupp.single true 2

example : ¬ StendhalLE target source ∧ ¬ StendhalLE source target :=
  ⟨targetNotLE, sourceNotLE⟩

example (v : leftStandard parameters weights source sourceOrdered) :
    seqIdem parameters weights target targetOrdered • v = 0 :=
  seqIdem_smul_leftStandard_eq_zero_of_not_stendhalLE sourceOrdered targetOrdered targetNotLE v

end NonVacuity.WebsterIncomparableStandardSupport

namespace NonVacuity.WebsterOppositeLoadingStandardSupport

open Categorification Categorification.KLR Categorification.Stendhal
open Categorification.Stendhal.BraidedStendhalAlgebra Equiv MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev content : Multiset Bool := {false, true}
private abbrev weight := stendhalWeight 2 content
private abbrev swapReds : Perm (Fin 2) := Equiv.swap 0 1
private abbrev order := List.map swapReds (List.finRange 2)
private def earlier : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl false, .inr 1, .inl true] (by decide)
private def later : Seq weight :=
  KLRAlgebra.Seq.ofList [.inr 0, .inl true, .inr 1, .inl false] (by decide)
private theorem earlierOrdered : IsRedOrdered earlier :=
  (redWord_eq_finRange_iff earlier).1 (by decide)
private theorem laterOrdered : IsRedOrdered later :=
  (redWord_eq_finRange_iff later).1 (by decide)
private theorem laterNotLE : ¬ StendhalLE later earlier := by
  intro h
  exact (by decide : ¬ blackCount later 1 true ≤ blackCount earlier 1 true) (h 1 true)
private noncomputable abbrev parameters : Bool → Bool → MvPolynomial (Fin 2) ℚ :=
  fun i j => if i = j then 0 else 1
private noncomputable abbrev weights : Fin 2 → Bool →₀ ℕ :=
  fun _ => Finsupp.single false 2 + Finsupp.single true 2
private theorem symmetric : KLRSymm parameters := by
  intro i j h
  simp [parameters, h, Ne.symm h]
private noncomputable def reducedWord (w : Perm (Fin weight.card)) :=
  (TypeA.exists_reduced _ w).choose
private theorem reducedChoice : TypeA.IsReducedChoice reducedWord :=
  fun w => (TypeA.exists_reduced _ w).choose_spec

example (v : ViolLoadingStandard (k := ℚ) (Q := parameters) (Λ := weights)
    (Seq.redPerm swapReds earlier) order) :
    op (violLoadingIdem (k := ℚ) (Q := parameters) (Λ := weights)
      (redWord_relabel swapReds laterOrdered)) • v = 0 :=
  violLoadingIdem_smul_violLoadingStandard_eq_zero_of_not_le reducedChoice symmetric
    swapReds earlierOrdered laterOrdered laterNotLE v

end NonVacuity.WebsterOppositeLoadingStandardSupport

noncomputable section

namespace NonVacuity.WebsterWeightComplex

open Categorification CategoryTheory DG
open scoped DG.DegreeZero

local instance instScalarWeightComplexInternalGrading : InternalGrading ℚ := scalarInternalGrading ℚ
local instance instScalarWeightComplexBigradedRing : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

private abbrev source : WeightCategory ℚ := ⟨0⟩

private abbrev weightComplex :=
  preadditiveCoyonedaObj source ⋙ HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)

example : CatModule.IsQuasiIso (diagramWeightModuleOfComplexMap (𝟙 weightComplex)) :=
  diagramWeightModuleOfComplexMap_isQuasiIso _ (fun _ => inferInstance)

end NonVacuity.WebsterWeightComplex

namespace NonVacuity.WebsterWeightComplexProjective

open Categorification CategoryTheory DG
open scoped DG.DegreeZero CatModule

local instance instFixtureInternal : InternalGrading ℚ := scalarInternalGrading ℚ
local instance instFixtureBigraded : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

private abbrev Z : WeightCategory ℚ := ⟨0⟩
private abbrev H := preadditiveCoyonedaObj Z
private abbrev TestScalars := (CategoryTheory.End Z)ᵐᵒᵖ
private abbrev C := ComplexShape.up ℤ
private abbrev testDiagram := H ⋙ HomologicalComplex.single (ModuleCat TestScalars) C 0
private abbrev inner (X : WeightCategory ℚ) :=
  HomologicalComplex.singleObjXSelf C 0 (H.obj X)

private def fixtureCoordinate (X : WeightCategory ℚ) :
    (weightComplexPiece testDiagram 0).obj X ≃+ (Z ⟶ X) :=
  (weightComplexPieceAddEquiv testDiagram 0 X).trans
    (AddEquiv.ofBijective (inner X).hom.hom.toAddMonoidHom
      ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
        (ModuleCat.epi_iff_surjective _).mp inferInstance⟩)

private def representableProjection :
    weightComplexPiece testDiagram 0 ⟶ CatModule.representable Z where
  app X := (fixtureCoordinate X).toAddMonoidHom
  map_mem' {X i x} hx := by
    change fixtureCoordinate X x ∈ DG.grading (M := Z ⟶ X) i
    rcases (weightComplexPiece_mem_grading_iff testDiagram 0 i X x).mp hx with rfl | rfl
    · apply WeightCategory.mem_grading_iff.mpr
      exact InDegreeZero.ring_mem_grading_iff.mpr (Or.inl rfl)
    · rw [map_zero]
      exact zero_mem _
  map_d' {X} x := by
    change fixtureCoordinate X (d x) = d (fixtureCoordinate X x)
    rw [weightComplexPiece_d_eq_zero, map_zero]
    exact (WeightCategory.hom_ext (InDegreeZero.ring_d_apply (fixtureCoordinate X x).val)).symm
  map_smul' {X Y} a x := by
    change (inner Y).hom (weightComplexPieceAddEquiv testDiagram 0 Y
      ((weightComplexPiece testDiagram 0).act a x)) =
      (H.map a) ((inner X).hom (weightComplexPieceAddEquiv testDiagram 0 X x))
    erw [weightComplexPieceAddEquiv_act]
    change (inner Y).hom (((HomologicalComplex.single (ModuleCat TestScalars) C 0).map
      (H.map a)).f 0 (weightComplexPieceAddEquiv testDiagram 0 X x)) = _
    erw [HomologicalComplex.single_map_f_self, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      Iso.inv_hom_id_apply]

example : CatModule.IsKProjective (diagramWeightModuleOfComplex testDiagram) := by
  apply diagramWeightModuleOfComplex_isKProjective
  · intro X n hn
    exact HomologicalComplex.isZero_single_obj_X C 0 (H.obj X) n (by omega)
  · intro n
    cases n with
    | zero =>
      let _ := CatModule.isIso_of_bijective representableProjection (fun X => (fixtureCoordinate X).bijective)
      exact (CatModule.isKProjective_representable Z).of_iso (asIso representableProjection)
    | succ n =>
      let b : ℤ := -((n + 1 : ℕ) : ℤ)
      change CatModule.IsKProjective (weightComplexPiece testDiagram b)
      intro N hN f
      refine CatModule.homotopic_zero_iff_exists.mpr ⟨0, CatModule.Cochain.ext fun X x => ?_⟩
      have hz : CategoryTheory.Limits.IsZero ((testDiagram.obj X).X b) :=
        HomologicalComplex.isZero_single_obj_X C 0 (H.obj X) b (by dsimp [b]; omega)
      have hs := ModuleCat.isZero_iff_subsingleton.mp hz
      have h : x = 0 := (weightComplexPieceAddEquiv testDiagram b X).injective (hs.elim _ _)
      rw [h]
      simp

end NonVacuity.WebsterWeightComplexProjective

end

noncomputable section

namespace NonVacuity.WebsterGradedChainDG

open Categorification CategoryTheory DG
open scoped DG.DegreeZero

local instance instChainRationalInternal : InternalGrading ℚ := scalarInternalGrading ℚ
local instance instChainRationalBigraded : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

private abbrev gradedRational : WeightGradedTerm ℚ where
  obj := ModuleCat.of ℚ ℚ
  grade := wgrading
  decomp := inferInstance
  smul_mem := mul_mem_wgrading

private def periodicMap (n : ℕ) : ℚ →ₗ[ℚ] ℚ :=
  if n % 2 = 0 then 0 else LinearMap.id

private theorem periodicMap_homogeneous (n : ℕ) (j : ℤ) {x : ℚ} (hx : x ∈ wgrading j) :
    periodicMap n x ∈ wgrading j := by
  by_cases h : n % 2 = 0
  · simp [periodicMap, h]
  · simpa [periodicMap, h] using hx

private theorem periodicMap_exact (n : ℕ) : Function.Exact (periodicMap (n+1)) (periodicMap n) := by
  intro x
  by_cases h : n % 2 = 0
  · have hn : (n+1) % 2 ≠ 0 := by omega
    simp [periodicMap, h, hn]
  · have hn : (n+1) % 2 = 0 := by omega
    simp [periodicMap, h, hn, eq_comm]

example := weightDgGradedChainAugmentation_quasiIso (R := ℚ)
  (fun _ => gradedRational) periodicMap (fun n j {_} h => periodicMap_homogeneous n j h)
  (fun n => (periodicMap_exact n).apply_apply_eq_zero) gradedRational LinearMap.id
  (fun _ {_} h => h) (fun x => by simp [periodicMap]) periodicMap_exact
  (by intro x; simp [periodicMap, eq_comm]) Function.surjective_id

end NonVacuity.WebsterGradedChainDG

end

noncomputable section

namespace NonVacuity.WebsterOrderedGradedResolution
open Categorification Categorification.ModuleFiltration DG DirectSum

private abbrev e (_ : Bool) : ℚ := 1
private abbrev above (a b : Bool) : Prop := a = false ∧ b = true
private abbrev P := lIdeal (1 : ℚ)

private def S : Bool → ModuleCat ℚ
  | false => ModuleCat.of ℚ PUnit
  | true => ModuleCat.of ℚ P

private def q : (i : Bool) → lIdeal (e i) →ₗ[ℚ] S i
  | false => 0
  | true => LinearMap.id

private theorem pProjective : Module.Projective ℚ P := by
  refine Module.Projective.of_split P.subtype
    { toFun := fun p => ⟨p, mul_one _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ?_
  ext
  rfl

private def data : OrderedStandardCovers S e above where
  quotient := q
  surjective := by
    intro i x
    cases i with
    | false => exact ⟨0, Subsingleton.elim (α := PUnit) _ x⟩
    | true => exact ⟨x, rfl⟩
  projective _ := pProjective
  kernel := by
    intro i
    cases i with
    | false =>
      refine ⟨[true], ?_, ?_⟩
      · simp only [List.mem_singleton]
        rintro _ rfl
        exact ⟨rfl, rfl⟩
      · apply HasFiltration.single (c := true)
        exact LinearEquiv.ofBijective (LinearMap.ker (q false)).subtype
          ⟨Submodule.injective_subtype _, fun x => ⟨⟨x, rfl⟩, rfl⟩⟩
    | true =>
      refine ⟨[], by simp, HasFiltration.zero ⟨?_⟩⟩
      intro x y
      exact Subtype.ext (show x.val = y.val from x.property.trans y.property.symm)

private theorem mulGrade ⦃a b : ℤ⦄ ⦃x y : ℚ⦄ (hx : x ∈ degreeZeroGrading ℚ a)
    (hy : y ∈ degreeZeroGrading ℚ b) : x * y ∈ degreeZeroGrading ℚ (a+b) := by
  apply (mem_degreeZeroGrading_iff ℚ).mpr
  rcases (mem_degreeZeroGrading_iff ℚ).mp hx with rfl | rfl
  · rcases (mem_degreeZeroGrading_iff ℚ).mp hy with rfl | rfl
    · exact Or.inl (zero_add _)
    · exact Or.inr (mul_zero _)
  · exact Or.inr (zero_mul _)

private theorem eGrade (i : Bool) : e i ∈ degreeZeroGrading ℚ 0 := mem_degreeZeroGrading_zero _ _
private theorem eIdem (i : Bool) : IsIdempotentElem (e i) := one_mul _
private theorem aboveTrans (i j l : Bool) (h : above i j) (h' : above j l) : above i l :=
  ⟨h.1, h'.2⟩
private theorem quotientGrade ⦃n : ℤ⦄ ⦃x : P⦄ (_ : x.val ∈ degreeZeroGrading ℚ n) :
    data.quotient false x ∈ degreeZeroGrading (S false) n :=
  (mem_degreeZeroGrading_iff _).mpr (Or.inr rfl)

private abbrev rankOneScalarGrade := degreeZeroGrading ℚ
private abbrev rankOneStandardGrade := degreeZeroGrading (S false)
private abbrev rankOneDifferential :=
  gradedLoadingResolutionChainMap data false rankOneScalarGrade mulGrade eGrade eIdem
    aboveTrans rankOneStandardGrade quotientGrade

open scoped DG.DegreeZero

local instance instOrderedTransportRationalInternalGrading : InternalGrading ℚ :=
  scalarInternalGrading ℚ

private theorem nonzeroQuotientGrade ⦃j : ℤ⦄ ⦃x : P⦄ (hx : x.val ∈ degreeZeroGrading ℚ j) :
    data.quotient true x ∈ degreeZeroGrading (S true) j := by
  change x ∈ degreeZeroGrading P j
  rcases (mem_degreeZeroGrading_iff ℚ).mp hx with h | h
  · exact (mem_degreeZeroGrading_iff P).mpr (Or.inl h)
  · exact (mem_degreeZeroGrading_iff P).mpr (Or.inr (Subtype.ext h))

example : (data.transport (RingEquiv.refl ℚ)).quotient true
    (⟨1, one_mul 1⟩ : P) ∈
    transportedStandardGrading (RingEquiv.refl ℚ) true (degreeZeroGrading (S true)) 0 :=
  data.transport_quotient_mem_weight (RingEquiv.refl ℚ) true
    (degreeZeroGrading (S true)) (fun h => h) (fun h => nonzeroQuotientGrade h)
    (mem_degreeZeroGrading_zero ℚ 1)

-- The rank-one example has a nonzero higher kernel in degree zero.
example : Function.Exact (rankOneDifferential 0) (data.quotient false) :=
  gradedLoadingResolutionChainMap_augmentation_exact data false rankOneScalarGrade mulGrade eGrade eIdem aboveTrans rankOneStandardGrade quotientGrade

example : Function.Exact (rankOneDifferential 1) (rankOneDifferential 0) :=
  gradedLoadingResolutionChainMap_exact data false rankOneScalarGrade mulGrade eGrade eIdem aboveTrans rankOneStandardGrade quotientGrade 0

example : ∃ x, rankOneDifferential 0 x = (⟨1, one_mul 1⟩ : P) :=
  ((gradedLoadingResolutionChainMap_augmentation_exact data false rankOneScalarGrade mulGrade eGrade
    eIdem aboveTrans rankOneStandardGrade quotientGrade) ⟨1, one_mul 1⟩).mp rfl

open scoped DG.DegreeZero
local instance instOrderedRationalWeight : InternalGrading ℚ := scalarInternalGrading ℚ
local instance instOrderedRationalBigraded : BigradedDGRing ℚ := scalarBigradedDGRing ℚ

example := orderedWeightDgAugmentation_quasiIso data false eGrade eIdem aboveTrans rankOneStandardGrade
  (fun {_ _ _ _} _ _ => (mem_degreeZeroGrading_iff _).mpr
    (Or.inr (Subsingleton.elim (α := PUnit) _ _)))
  quotientGrade

open scoped DG.DegreeZero

local instance instOrderedProjectivityScalarInternalGrading : InternalGrading ℚ :=
  scalarInternalGrading ℚ
local instance instOrderedProjectivityScalarBigradedRing : BigradedDGRing ℚ :=
  scalarBigradedDGRing ℚ

example : CatModule.IsKProjective
    (orderedWeightDgResolution data false eGrade eIdem aboveTrans rankOneStandardGrade quotientGrade) :=
  orderedWeightDgResolution_isKProjective data false eGrade eIdem aboveTrans
    rankOneStandardGrade quotientGrade

local instance instOrderedDerivedRationalWeight :
    CatModule.HasDerivedCategory.{1,0} (WeightCategory ℚ) :=
  CatModule.HasDerivedCategory.standard _

private theorem rightQuotientGrade ⦃j : ℤ⦄ ⦃x : P⦄ (hx : x.val ∈ wgrading j) :
    data.quotient true x ∈ degreeZeroGrading (S true) j := by
  change x ∈ degreeZeroGrading P j
  rcases (mem_degreeZeroGrading_iff ℚ).mp hx with h | h
  · exact (mem_degreeZeroGrading_iff P).mpr (Or.inl h)
  · exact (mem_degreeZeroGrading_iff P).mpr (Or.inr (Subtype.ext h))

private theorem nonzeroStandardSmul {i j : ℤ} {a : ℚ} {x : S true}
    (ha : a ∈ wgrading i) (hx : x ∈ degreeZeroGrading (S true) j) :
    a • x ∈ degreeZeroGrading (S true) (i+j) := by
  rcases (mem_degreeZeroGrading_iff ℚ).mp ha with hi | rfl
  · rcases (mem_degreeZeroGrading_iff _).mp hx with hj | rfl
    · exact (mem_degreeZeroGrading_iff _).mpr (Or.inl (by omega))
    · rw [smul_zero]; exact zero_mem _
  · rw [zero_smul]; exact zero_mem _

private theorem filteredCoefficient : HasFiltration
    (fun _ : Unit => ModuleCat.of ℚᵐᵒᵖ ℚ) [()] (ModuleCat.of ℚᵐᵒᵖ ℚ) :=
  HasFiltration.single (c := ()) (LinearEquiv.refl ℚᵐᵒᵖ ℚ)

private theorem filteredRationalLeft {i j : ℤ} {a x : ℚ}
    (ha : a ∈ wgrading i) (hx : x ∈ DG.grading j) :
    a • x ∈ DG.grading (i+j) := mul_mem_grading ha hx

private theorem filteredRationalRight {i j : ℤ} {b x : ℚ}
    (hb : b ∈ wgrading i) (hx : x ∈ DG.grading j) :
    MulOpposite.op b • x ∈ DG.grading (j+i) := mul_mem_grading hx hb

example := orderedWeightDerivedTensor_cohomology_isZero_of_filtered_loading_support
  data true eGrade eIdem aboveTrans (degreeZeroGrading (S true))
  nonzeroStandardSmul rightQuotientGrade (fun j => DG.grading (M := ℚ) j)
  filteredRationalLeft filteredRationalRight filteredCoefficient
  (by intro i hi; exact False.elim (Bool.noConfusion hi.1))
  (⟨0⟩ : WeightCategory ℚ) (-1) (by decide)

end NonVacuity.WebsterOrderedGradedResolution

namespace NonVacuity.WebsterDirectLeftWeight

open Categorification Categorification.Stendhal Categorification.ModuleFiltration
open KLR DG CategoryTheory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev vacuumParameters : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev vacuumWeights : Fin 0 → Unit →₀ ℕ := Fin.elim0

private def vacuumBlackGrade : GradingDatum vacuumParameters where
  degX _ := 0
  degΨ _ _ := 0
  degΨ_self _ := rfl
  isWeightedHomogeneous a b h := (h (Subsingleton.elim a b)).elim

private def vacuumGrade : GradingDatum (stendhalQ vacuumParameters vacuumWeights) :=
  stendhalGradingDatum vacuumWeights vacuumBlackGrade (fun _ => 0) (fun _ => rfl)

private abbrev vacuumLabel := {t : Seq (stendhalWeight 0 (0 : Multiset Unit)) // IsRedOrdered t}
private abbrev vacuumAlgebra := TensorProductAlgebra ℚ vacuumParameters vacuumWeights (0 : Multiset Unit)
private abbrev vacuumStandard (s : vacuumLabel) :=
  ModuleCat.of vacuumAlgebra (leftStandard vacuumParameters vacuumWeights s.val s.property)
private abbrev vacuumKernel (s : vacuumLabel) :=
  (leftUpper vacuumParameters vacuumWeights s.val s.property).comap
    (lIdeal (seqIdem vacuumParameters vacuumWeights s.val s.property)).subtype

private def vacuumLoading : vacuumLabel := by
  let s : Seq (stendhalWeight 0 (0 : Multiset Unit)) := by
    simpa [stendhalWeight] using (KLR.Seq.nil : Seq (0 : Multiset (Unit ⊕ Fin 0)))
  exact ⟨s, fun _ _ r => r.elim0⟩

private theorem vacuumHigherFiltration (s : vacuumLabel) :
    ∃ m : List vacuumLabel, (∀ t ∈ m, StendhalLT s.val t.val) ∧
      HasFiltration vacuumStandard m (ModuleCat.of vacuumAlgebra (vacuumKernel s)) := by
  have hzero : leftUpper vacuumParameters vacuumWeights s.val s.property = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨t, ht, a, hlt, h⟩
    exact (hlt.2 fun r => r.elim0).elim
  refine ⟨[], by simp, HasFiltration.zero ?_⟩
  constructor
  intro x y
  apply Subtype.ext
  apply Subtype.ext
  have hx : x.val.val ∈ leftUpper vacuumParameters vacuumWeights s.val s.property := x.property
  have hy : y.val.val ∈ leftUpper vacuumParameters vacuumWeights s.val s.property := y.property
  rw [hzero, Submodule.mem_bot] at hx hy
  exact hx.trans hy.symm

example :=
  leftStandardOrderedWeightResolution_isKProjective vacuumGrade vacuumHigherFiltration vacuumLoading

example :=
  leftStandardOrderedWeightAugmentation_quasiIso vacuumGrade vacuumHigherFiltration vacuumLoading

section StandardParameters

open QuantumGroup KL3.Diagram

variable (C : CartanDatum Unit)

private def vacuumKLBlackGrade :
    GradingDatum (CL.qCL (CL.CLScalars.kl : CL.CLScalars C ℚ)) where
  degX _ := 0
  degΨ _ _ := 0
  degΨ_self _ := rfl
  isWeightedHomogeneous a b h := (h (Subsingleton.elim a b)).elim

private def vacuumKLGrade :=
  stendhalGradingDatum vacuumWeights (vacuumKLBlackGrade C) (fun _ => 0) (fun _ => rfl)

private theorem vacuumKLRouquier :
    IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C ℚ)) :=
  ⟨fun a b h => (h (Subsingleton.elim a b)).elim,
    fun a b h => (h (Subsingleton.elim a b)).elim,
    fun a b h => (h (Subsingleton.elim a b)).elim⟩

example :=
  leftStandardOrderedWeightResolution_std_isKProjective vacuumWeights 0
    (vacuumKLGrade C) (vacuumKLRouquier C) vacuumLoading

example :=
  leftStandardOrderedWeightAugmentation_std_quasiIso vacuumWeights 0
    (vacuumKLGrade C) (vacuumKLRouquier C) vacuumLoading

end StandardParameters

end NonVacuity.WebsterDirectLeftWeight

end

noncomputable section

namespace NonVacuity.WebsterReflectedOrderedWeight

open Categorification Categorification.Stendhal Categorification.ModuleFiltration
open KLR DG CategoryTheory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private abbrev vacuumParameters : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
private abbrev vacuumWeights : Fin 0 → Unit →₀ ℕ := Fin.elim0

open QuantumGroup BraidedStendhalAlgebra

private theorem vacuumRouquier : IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))
    vacuumParameters where
  symm i j hij := (hij (Subsingleton.elim i j)).elim
  homogeneous i j hij := (hij (Subsingleton.elim i j)).elim
  unit_coeff i j hij := (hij (Subsingleton.elim i j)).elim

private noncomputable def vacuumWord
    (w : Equiv.Perm (Fin (stendhalWeight 0 (0 : Multiset Unit)).card)) :=
  (TypeA.exists_reduced _ w).choose

private theorem vacuumReduced : TypeA.IsReducedChoice vacuumWord :=
  fun w => (TypeA.exists_reduced _ w).choose_spec

private theorem vacuumSymmetric : KLRSymm vacuumParameters := fun _ _ _ => rfl

private abbrev vacuumLabel := {t : Seq (stendhalWeight 0 (0 : Multiset Unit)) // IsRedOrdered t}
private abbrev vacuumAlgebra := TensorProductAlgebra ℚ vacuumParameters vacuumWeights (0 : Multiset Unit)
private abbrev vacuumStandard (s : vacuumLabel) :=
  ModuleCat.of vacuumAlgebra (leftStandard vacuumParameters vacuumWeights s.val s.property)
private abbrev vacuumKernel (s : vacuumLabel) :=
  (leftUpper vacuumParameters vacuumWeights s.val s.property).comap
    (lIdeal (seqIdem vacuumParameters vacuumWeights s.val s.property)).subtype

private def vacuumLoading : vacuumLabel := by
  let s : Seq (stendhalWeight 0 (0 : Multiset Unit)) := by
    simpa [stendhalWeight] using (KLR.Seq.nil : Seq (0 : Multiset (Unit ⊕ Fin 0)))
  exact ⟨s, fun _ _ r => r.elim0⟩

private theorem vacuumHigherFiltration (s : vacuumLabel) :
    ∃ m : List vacuumLabel, (∀ t ∈ m, StendhalLT s.val t.val) ∧
      HasFiltration vacuumStandard m (ModuleCat.of vacuumAlgebra (vacuumKernel s)) := by
  have hzero : leftUpper vacuumParameters vacuumWeights s.val s.property = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro _ ⟨t, ht, a, hlt, h⟩
    exact (hlt.2 fun r => r.elim0).elim
  refine ⟨[], by simp, HasFiltration.zero ?_⟩
  constructor
  intro x y
  apply Subtype.ext
  apply Subtype.ext
  have hx : x.val.val ∈ leftUpper vacuumParameters vacuumWeights s.val s.property := x.property
  have hy : y.val.val ∈ leftUpper vacuumParameters vacuumWeights s.val s.property := y.property
  rw [hzero, Submodule.mem_bot] at hx hy
  exact hx.trans hy.symm

example :=
  reflectedStandardWeightResolution_isKProjective (Λ := vacuumWeights)
    vacuumRouquier (1 : Equiv.Perm (Fin 0)) vacuumReduced vacuumSymmetric
    vacuumHigherFiltration vacuumLoading

example :=
  reflectedStandardWeightAugmentation_quasiIso (Λ := vacuumWeights)
    vacuumRouquier (1 : Equiv.Perm (Fin 0)) vacuumReduced vacuumSymmetric
    vacuumHigherFiltration vacuumLoading

example := by
  let A := stendhalGradingDatum vacuumWeights vacuumRouquier.gradingDatum
    (UDot.di (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)))
    (fun i => (vacuumRouquier.gradingDatum_degX i).trans (UDot.two_mul_di _ i).symm)
  let G := violAuxiliaryGrade (ν := (0 : Multiset Unit)) A
  let e := isIdempotentElem_violMk_redProj ℚ vacuumParameters vacuumWeights
    (0 : Multiset Unit) []
  letI := Graded.cornerGradedAlgebra G e (redProj_mem_violAuxiliaryGrade A [])
  let S := Graded.oppositeGrade (Graded.cornerGrading G e)
  letI := gradedAlgebraInternalGrading S
  letI := gradedAlgebraBigradedDGRing S
  let D : CatModule.HasDerivedCategory.{1,0} (WeightCategory e.Cornerᵐᵒᵖ) :=
    CatModule.HasDerivedCategory.standard _
  exact @reflectedStandardWeightBraiding_isZero.{1} Unit ℚ _ _ 0 (0 : Multiset Unit)
    vacuumParameters vacuumWeights _ vacuumRouquier (1 : Equiv.Perm (Fin 0))
    vacuumWord vacuumReduced vacuumSymmetric vacuumHigherFiltration vacuumLoading []
    D D (⟨0⟩ : WeightCategory e.Cornerᵐᵒᵖ) 1 (by decide)
    (fun _ ht => (ht.2 fun r => r.elim0).elim)

end NonVacuity.WebsterReflectedOrderedWeight

end

namespace NonVacuity.AmbientDerivedIdempotentCut

open Categorification DG MulOpposite
open scoped DG.DegreeZero
noncomputable section

local instance : HasDerivedCategory.{0,0} ℚ := HasDerivedCategory.small _

example := balancedTensorLeftIdealEquiv (k := ℚ) (M := ℚᵐᵒᵖ)
  (show IsIdempotentElem (1 : ℚ) from one_mul 1)

example := ambientDerivedTensorH0LeftIdealEquiv (k := ℚ) (M := ℚᵐᵒᵖ)
  (fun c m => by
    apply unop_injective
    exact mul_comm m.unop c)
  (show IsIdempotentElem (1 : ℚ) from one_mul 1)

end
end NonVacuity.AmbientDerivedIdempotentCut

namespace NonVacuity.WebsterOutgoingExteriorAmbientTor

open Categorification.Stendhal Categorification.Stendhal.LabelTwo DG
open scoped DG.DegreeZero
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local instance : HasDerivedCategory.{0,0} ℚ := HasDerivedCategory.small _

local instance : HasDerivedCategory.{0,0}
    (TensorProductAlgebra ℚ (parameter ℚ) (fun (_ : Fin 2) => Finsupp.single () 2)
      (Multiset.replicate 2 ())) := HasDerivedCategory.small _

example := outgoingExteriorAmbientHomology_zero ℚ

example := outgoingExteriorAmbientHomology_isZero ℚ (-1) (by decide)

end
end NonVacuity.WebsterOutgoingExteriorAmbientTor

section WebsterDerivedTensorCoefficientFixture
noncomputable section

open Categorification CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

private def twice : ℚ →ₗ[ℚ] ℚ := (2 : ℚ) • LinearMap.id

private theorem twice_op (r x : ℚ) : twice (op r • x) = op r • twice x := by
  change 2 • ((op r) • x) = op r • (2 • x)
  exact smul_comm (2 : ℚ) (op r) x

local instance : DG.HasDerivedCategory.{0,0} ℚ := DG.HasDerivedCategory.small ℚ

example : derivedTensor ℚ ℚ ℚ ⟶ derivedTensor ℚ ℚ ℚ :=
  derivedTensorCoefficientMap twice twice_op

example := ordinaryTensorCoefficientMap_tmul twice twice_op

example : NatTrans.CommShift (derivedTensorCoefficientMap twice twice_op) ℤ :=
  inferInstance

end

end WebsterDerivedTensorCoefficientFixture
