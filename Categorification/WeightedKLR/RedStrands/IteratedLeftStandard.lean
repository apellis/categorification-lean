/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedTwoPieceStandard
import Categorification.WeightedKLR.RedStrands.IteratedStandardCharacter

/-!
# Definition 5.1 standards at row loadings are iterated standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1,
Definition 5.1 and the modules `S_κ^i` before Proposition 5.6. For words `u_1, …, u_ℓ` the row
loading `λ_1 u_1 λ_2 u_2 ⋯ λ_ℓ u_ℓ` (`rowLoading`) places the black strands `u_j` to the right of
the `j`th red strand. The graded left standard module `T e(s) / U_s` at this loading is
isomorphic, as a graded module, to the iterated standardization `iteratedStandard u` of the
cyclotomic word projectives (`rowLoading_gradedEquiv`). Webster identifies the two in the proof
of Proposition 5.6; here the isomorphism is built red strand by red strand from
`twoPieceStandardGradedEquiv`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section Vacuum

variable (Λ₀ : Fin 0 → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ₀))

private theorem leftUpper_vacuum (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) : leftUpper Q Λ₀ s hs = ⊥ := by
  have : IsEmpty (Fin (Multiset.card (stendhalWeight 0 (0 : Multiset I)))) := by
    rw [show Multiset.card (stendhalWeight 0 (0 : Multiset I)) = 0 by simp [stendhalWeight]]
    infer_instance
  refine le_antisymm (Submodule.span_le.2 ?_) bot_le
  rintro _ ⟨t, ht, a, hlt, rfl⟩
  obtain rfl : t = s := Subtype.ext (funext isEmptyElim)
  exact (hlt.2 hlt.1).elim

private theorem lIdeal_vacuum (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) : lIdeal (seqIdem Q Λ₀ s hs) = ⊤ := by
  rw [show seqIdem Q Λ₀ s hs = 1 from vacuum_mk_e Λ₀ s hs]
  exact eq_top_iff.2 fun y _ => mul_one y

/-- With no red strands, the standard module of the empty loading is the regular module. -/
private def vacuumStandardEquiv (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) :
    leftStandard Q Λ₀ s hs ≃ₗ[TensorProductAlgebra k Q Λ₀ 0] TensorProductAlgebra k Q Λ₀ 0 :=
  (Submodule.quotEquivOfEqBot _ (by
    rw [leftUpper_vacuum Λ₀ s hs, Submodule.comap_bot, Submodule.ker_subtype])).trans
    ((LinearEquiv.ofEq _ ⊤ (lIdeal_vacuum Λ₀ s hs)).trans Submodule.topEquiv)

/-- The graded standard module of the empty loading is the vacuum test module. -/
def vacuumStandardGradedEquiv (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) :
    gradedLeftStandard G s hs ≃ᵍ[TensorProductAlgebra k Q Λ₀ 0] (vacuumTest Λ₀ G 0).grading :=
  let := (vacuumTest Λ₀ G 0).decomposition
  let := (vacuumTest Λ₀ G 0).gradedSMul
  leftStandardGradedEquiv G s hs (vacuumStandardEquiv Λ₀ s hs)
    (mk_e_mem_tensorProductGrade G 0 s hs)

end Vacuum

section Row

omit [DecidableEq I] in
/-- The total black content of no words is zero. -/
theorem blockContent_zero (u : Fin 0 → List I) : blockContent u = 0 := by
  simp [blockContent]

omit [DecidableEq I] in
/-- The black content of `u_1, …, u_{n+1}` is that of `u_1, …, u_n` plus that of `u_{n+1}`. -/
theorem blockContent_succ {n : ℕ} (u : Fin (n+1) → List I) :
    blockContent (fun j => u (Fin.castSucc j)) + (u (Fin.last n) : Multiset I) =
      blockContent u := by
  simp [blockContent, Fin.sum_univ_castSucc]

/-- **The row loading** `λ_1 u_1 λ_2 u_2 ⋯ λ_n u_n`: the black strands of the word `u_j` stand
to the right of the `j`th red strand. -/
def rowLoading : (n : ℕ) → (u : Fin n → List I) → Seq (stendhalWeight n (blockContent u))
  | 0, u => Seq.cast (congrArg (stendhalWeight 0) (blockContent_zero u).symm) vacuumSeq
  | n+1, u => Seq.cast (congrArg (stendhalWeight (n+1)) (blockContent_succ u))
      (twoPieceLoading (blockContent fun j => u (Fin.castSucc j)) (u (Fin.last n) : Multiset I)
        (rowLoading n fun j => u (Fin.castSucc j)) (KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl))

omit [DecidableEq I] in
theorem rowLoading_succ {n : ℕ} (u : Fin (n+1) → List I) :
    rowLoading (n+1) u = Seq.cast (congrArg (stendhalWeight (n+1)) (blockContent_succ u))
      (twoPieceLoading (blockContent fun j => u (Fin.castSucc j)) (u (Fin.last n) : Multiset I)
        (rowLoading n fun j => u (Fin.castSucc j))
        (KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl)) := by
  rw [rowLoading]

private theorem nonempty_gradedEquiv_congr {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    (G : GradingDatum (stendhalQ Q Λ)) {N : GFin (tensorProductGrade G ν)}
    {s₁ s₂ : Seq (stendhalWeight ℓ ν)} (h : s₁ = s₂) (hs₁ : IsRedOrdered s₁)
    (hs₂ : IsRedOrdered s₂)
    (e : Nonempty (gradedLeftStandard G s₁ hs₁ ≃ᵍ[TensorProductAlgebra k Q Λ ν] N.grading)) :
    Nonempty (gradedLeftStandard G s₂ hs₂ ≃ᵍ[TensorProductAlgebra k Q Λ ν] N.grading) := by
  subst h
  exact e

omit [DecidableEq I] in
theorem isRedOrdered_rowLoading : ∀ (n : ℕ) (u : Fin n → List I), IsRedOrdered (rowLoading n u)
  | 0, _ => (isRedOrdered_cast_iff _ _).2 vacuumSeq_ordered
  | n+1, _ => (isRedOrdered_cast_iff _ _).2
      (isRedOrdered_twoPieceLoading (isRedOrdered_rowLoading n _) _)

private theorem vacuumTest_gradedEquiv (Λ₀ : Fin 0 → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ₀))
    {ν : Multiset I} (h : 0 = ν) (hs : IsRedOrdered (Seq.cast (congrArg (stendhalWeight 0) h)
      (vacuumSeq (I := I) (ℓ := 0)))) :
    Nonempty (gradedLeftStandard G _ hs ≃ᵍ[TensorProductAlgebra k Q Λ₀ ν]
      (vacuumTest Λ₀ G ν).grading) := by
  subst h
  exact ⟨vacuumStandardGradedEquiv Λ₀ G _ hs⟩

private theorem standardizationTestAt_gradedEquiv {ℓ : ℕ} (Λ : Fin (ℓ+1) → I →₀ ℕ)
    (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
    (X : GFin (tensorProductGrade (restrictRedGrading Q Λ G) θ))
    (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))
    {ν : Multiset I} (h : θ + β = ν) (s : Seq (stendhalWeight (ℓ+1) (θ + β)))
    (hs : IsRedOrdered s) (hs' : IsRedOrdered (Seq.cast (congrArg (stendhalWeight (ℓ+1)) h) s))
    (e : gradedLeftStandard G s hs ≃ᵍ[TensorProductAlgebra k Q Λ (θ + β)]
      (standardizationGFin Λ G θ β hsym (X.extTensor Z)).grading) :
    Nonempty (gradedLeftStandard G _ hs' ≃ᵍ[TensorProductAlgebra k Q Λ ν]
      (standardizationTestAt Λ G θ β hsym X Z ν).grading) := by
  subst h
  have hst : standardizationTestAt Λ G θ β hsym X Z (θ + β) =
      standardizationGFin Λ G θ β hsym (X.extTensor Z) := by
    unfold standardizationTestAt
    simp
  rw [hst]
  exact ⟨e⟩

/-- A graded isomorphism into `M` is one into `M` read over an equal grading. -/
private def sameGradingEquiv {A : Type} [Ring A] [Algebra k A] {g h : ℤ → Submodule k A}
    (eq : g = h) (M : GFin h) {N : Type} [AddCommGroup N] [Module k N] [Module A N]
    {𝒩 : ℤ → Submodule k N} (e : 𝒩 ≃ᵍ[A] M.grading) : 𝒩 ≃ᵍ[A] (sameGrading eq M).grading :=
  e

variable (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)

private theorem rowLoading_gradedEquiv_succ {n : ℕ} (Λ : Fin (n+1) → I →₀ ℕ)
    (u : Fin (n+1) → List I)
    (e : gradedLeftStandard (iteratedGrading C hQ fun j => Λ (Fin.castSucc j))
      (rowLoading n fun j => u (Fin.castSucc j)) (isRedOrdered_rowLoading n _) ≃ᵍ[
        TensorProductAlgebra k Q (fun j => Λ (Fin.castSucc j))
          (blockContent fun j => u (Fin.castSucc j))]
        (iteratedStandard C hQ n (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j))
          (blockContent fun j => u (Fin.castSucc j))).grading) :
    Nonempty (gradedLeftStandard (iteratedGrading C hQ Λ) (rowLoading (n+1) u)
      (isRedOrdered_rowLoading (n+1) u) ≃ᵍ[TensorProductAlgebra k Q Λ (blockContent u)]
        (iteratedStandard C hQ (n+1) Λ u (blockContent u)).grading) := by
  rw [iteratedStandard_succ]
  let t := rowLoading n fun j => u (Fin.castSucc j)
  have ht : IsRedOrdered t := isRedOrdered_rowLoading n _
  let w : Seq (u (Fin.last n) : Multiset I) := KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl
  let X := sameGrading (congrArg (fun g => tensorProductGrade g _)
    (restrictRedGrading_iteratedGrading C hQ Λ))
    (iteratedStandard C hQ n (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j))
      (blockContent fun j => u (Fin.castSucc j)))
  let Z := cyclotomicWordModule C (Λ (Fin.last n)) hQ w
  let θ := blockContent fun j => u (Fin.castSucc j)
  let φ : KMod (k := k) (ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ)
      (leftStandard Q (Λ ∘ Fin.castSucc) t ht)) ≃ₗ[TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ]
        X.carrier := (sameGradingEquiv _ _ e).toLinearEquiv
  let g : KMod (k := k) (cycProj Q Λ _ w) ≃ₗ[CycKLR k Q
      (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last n) i) (u (Fin.last n))] Z.carrier :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hφ : φ (leftStandardUnit Q (Λ ∘ Fin.castSucc) t ht) ∈ X.grading 0 :=
    (sameGradingEquiv _ _ e).map_mem' (leftStandardUnit_mem_zero _ t ht)
  have hg : g (cycUnit Q Λ w) ∈ Z.grading 0 :=
    Graded.mem_map_of_mem _ _ (hQ.gradingDatum.e_mem_grade w)
  refine nonempty_gradedEquiv_congr _ (rowLoading_succ u).symm
    ((isRedOrdered_cast_iff _ _).2 (isRedOrdered_twoPieceLoading ht w)) _ ?_
  exact standardizationTestAt_gradedEquiv Λ (iteratedGrading C hQ Λ) _ _ hQ.klrSymm X Z
    (blockContent_succ u) _ (isRedOrdered_twoPieceLoading ht w) _
    (twoPieceStandardGradedEquiv Λ (iteratedGrading C hQ Λ) hQ.klrSymm ht w X Z φ g hφ hg)

/-- **Definition 5.1 standards at row loadings are the modules `S_κ^i`** (Webster,
arXiv:1309.3796v2, §5.1, before Proposition 5.6): the graded left standard module at the row
loading `λ_1 u_1 ⋯ λ_n u_n` is isomorphic, as a graded module, to the iterated standardization
of the cyclotomic word projectives `R^{λ_j} e(u_j)`. -/
theorem rowLoading_gradedEquiv : ∀ (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I),
    Nonempty (gradedLeftStandard (iteratedGrading C hQ Λ) (rowLoading n u)
      (isRedOrdered_rowLoading n u) ≃ᵍ[TensorProductAlgebra k Q Λ (blockContent u)]
        (iteratedStandard C hQ n Λ u (blockContent u)).grading)
  | 0, Λ, u => vacuumTest_gradedEquiv Λ _ (blockContent_zero u).symm _
  | n+1, Λ, u => (rowLoading_gradedEquiv n _ _).elim (rowLoading_gradedEquiv_succ C hQ Λ u)

end Row

end Categorification.Stendhal.FirstWeight
