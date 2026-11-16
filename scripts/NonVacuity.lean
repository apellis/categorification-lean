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

end NonVacuity
