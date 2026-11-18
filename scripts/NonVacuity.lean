import Categorification
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
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noLoops ℚ) (fun _ => rfl)
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
    (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl)
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
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noLoops ℚ) (fun _ => rfl)
    (Graded.GProj.IndecClass.isGradedSimple_top b) φ

/-- The graded-simple scalar theorem in characteristic two, at the same repeated weight. -/
example
    (b : Graded.GProj.IndecClass ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade
      wkParallelRepeatedWeight))
    (φ : b.top →ₗ[WeightedKLR.GalleryAlgebra.WeightedKLRAlgebra (ZMod 2)
      (wkParallelGraph (ZMod 2)) wkParallelRepeatedWeight] b.top) :
    ∃ c : ZMod 2, ∀ m, φ m = c • m :=
  WeightedKLR.GradingDatum.exists_eq_smul_of_isGradedSimple (wkParallelGraph_dagger (ZMod 2))
    (wkParallelGraph_standing (ZMod 2)) (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl)
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
    (wkParallelGraph_dagger ℚ) (wkParallelGraph_standing ℚ) (wkParallelGraph_noLoops ℚ)
    (fun _ => rfl) wkParallelRepeatedWeight wkParallelRepeatedWeight

/-- The same unrestricted tensor-comparison check in characteristic two. -/
example : Graded.TensorK0Hyp
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade wkParallelRepeatedWeight)
    ((wkParallelGraph_standing (ZMod 2)).gradingDatum.klrGrade wkParallelRepeatedWeight) :=
  WeightedKLR.GradingDatum.tensorK0Hyp (wkParallelGraph_standing (ZMod 2)).gradingDatum
    (wkParallelGraph_dagger (ZMod 2)) (wkParallelGraph_standing (ZMod 2))
    (wkParallelGraph_noLoops (ZMod 2)) (fun _ => rfl)
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
    (wkParallelGraph_standing ℚ) (wkParallelGraph_noLoops ℚ) (fun _ => rfl)
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
example := wkMapG.component_totalCoproduct wkMapD wkMapS wkMapNoLoopEdges
  wkMapNoLoopPolynomials (Finsupp.single 0 1) (Finsupp.single 1 1)

/-- The antipode recursion negates every one-strand class. -/
example := wkMapG.antipodeComponent_of_degree_one wkMapD wkMapS wkMapNoLoopEdges
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

example := Stendhal.SingleBlack.oneBlackK0Equiv_regular (0 : Fin 1) oneRedGrading
  (by simp : 0 < Finsupp.single (0 : Fin 1) 2 (0 : Fin 1))

example := Stendhal.SingleBlack.oneBlackK0_eq_zero (0 : Fin 1)
  (Stendhal.stendhalGradingDatum (0 : Fin 1 → Fin 1 →₀ ℕ)
    singletonBlackGrading (fun _ => 1) (fun _ => rfl)) rfl

end CyclotomicDimensions

example (x y : wkMapG.K0W) := wkMapG.totalCoproduct_mul wkMapD wkMapS
  wkMapNoLoopEdges wkMapNoLoopPolynomials x y

example (x : wkMapG.K0W) := wkMapG.counitK0_totalCoproduct_left wkMapD wkMapS
  wkMapNoLoopEdges wkMapNoLoopPolynomials x

example (x : wkMapG.K0W) := wkMapG.counitK0_totalCoproduct_right wkMapD wkMapS
  wkMapNoLoopEdges wkMapNoLoopPolynomials x

/-- Both antipode equations for the standing graph over the example field. -/
example := (wkMapS.braidedHopfK0 wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials).antipode_left

example := (wkMapS.braidedHopfK0 wkMapD wkMapNoLoopEdges wkMapNoLoopPolynomials).antipode_right

example := wkMapS.braidedHopfK0_antipode_single wkMapD wkMapNoLoopEdges
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

example := printedForm_not_adjoint
example := barCoproduct_loweredPair_norm
example := Stendhal.TensorAdjointConvention.tau_barComul_F_ne_comul_tau_F
example := Stendhal.TensorAdjointConvention.barComul_tau_F LieLean.QuantumGroup.sl2RootDatum ()

private theorem rouquier : KLR.IsRouquierQ (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))
    (KLR.klQ (k := ℚ) (⊥ : SimpleGraph Unit)) := by
  constructor <;> intro i j h <;> exact (h (Subsingleton.elim _ _)).elim

private abbrev loading := Stendhal.FirstWeight.boundaryAt () 1 0

/-- Appending a fundamental strand preserves the degree-two Hom dimension. -/
example := Stendhal.finrank_homGrade_appendRed rouquier fundamentalGrading {()}
  loading.1 loading.1 loading.2.1 loading.2.1 2

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

end NonVacuity
