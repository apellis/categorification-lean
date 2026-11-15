import Categorification

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

end NonVacuity
