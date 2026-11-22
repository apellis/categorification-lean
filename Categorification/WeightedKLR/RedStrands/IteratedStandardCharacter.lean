/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizationWordCharacter
import Categorification.WeightedKLR.RedStrands.CyclotomicWordCharacter
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered
import Categorification.WeightedKLR.RedStrands.TensorCornerEndpoints
import Categorification.WeightedKLR.RedStrands.EmptyTensor

set_option backward.isDefEq.respectTransparency false

/-!
# Word characters of iterated standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5,
Proposition 5.6. Webster's standard module `S_κ^i` is built by iterated standardization from
cyclotomic word projectives `R^{λ_j} e(u_j)`, one for each red strand. Its graded dimension at
the ordinary loading of a tensor word `w` is the componentwise product of Webster's one-factor
forms (Corollary 3.22) between the product `s = F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}` and the
bar-ordinary vector of `w`.

## Main results

* `iteratedStandard`: the standard module `S_κ^i` in each black block.
* `iteratedStandard_of_ne`: it vanishes off the block of its total black content.
* `iteratedStandard_word`: its word character.
* `orderedFactorwise_appendTensor`: the componentwise form with an appended first vector
  factors through the last tensor split.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF FirstWeight
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
private local instance appendFormNeZero : NeZero q := ⟨RatFunc.X_ne_zero⟩
variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} [Finite I] (hR : R.IsXRegular) {n : ℕ}

/-- The componentwise form whose first vector is appended along the last red strand is the
product of the two factor functionals on the last tensor split. -/
theorem orderedFactorwise_appendTensor (wt : Fin (n+1) → Dom R)
    (x : TensorSpace (fun j => wt (Fin.castSucc j)))
    (y : IrreducibleModule R q (wt (Fin.last n)).1)
    (g : IrreducibleModule R q (wt (Fin.last n)).1 →ₗ[𝕂] 𝕂)
    (hg : ∀ y', g y' = SingleBlack.websterForm _ hR y y') (z : TensorSpace wt) :
    orderedFactorwise hR wt (appendTensor wt x y) z =
      factorTensorTest (fun _ : Unit => orderedFactorwise hR _ x) (fun _ : Unit => g) () ()
        (tensorSplitLast wt z) := by
  obtain ⟨t, rfl⟩ := (tensorSplitLast wt).symm.surjective z
  rw [LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [factorTensorTest_tmul, hg]
    exact orderedFactorwise_append hR wt x a y b
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

omit [Finite I] in
/-- With no red strands, the bar-ordinary vector of a word is the empty tensor when the word
has no black letters, and zero otherwise: each `F_i^a` acts through the counit. -/
theorem isEmptyEquiv_barOrdinaryWord (wt : Fin 0 → Dom R) :
    ∀ w : TensorWord I 0, PiTensorProduct.isEmptyEquiv (R := 𝕂)
      (s := fun j => IrreducibleModule R q (wt j).1) (Fin 0) (barOrdinaryWord w wt) =
        if w.content = 0 then 1 else 0
  | .empty => by
    change PiTensorProduct.isEmptyEquiv _ (PiTensorProduct.tprod 𝕂 _) = _
    simp [PiTensorProduct.isEmptyEquiv_apply_tprod, TensorWord.content]
  | .black w i a => by
    have ih := isEmptyEquiv_barOrdinaryWord wt w
    change PiTensorProduct.isEmptyEquiv _ (tensorRepresentation wt (F R q i ^ a)
      (barOrdinaryWord w wt)) = _
    simp only [tensorRepresentation, AlgHom.comp_apply, Algebra.ofId_apply,
      map_pow, counit_F,
      TensorWord.content]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using ih
    · have hne : w.content + Finsupp.single i a ≠ 0 := fun h => by
        have := congrArg (· i) h
        simp at this
        omega
      simp [zero_pow ha.ne', hne]

end Categorification.Stendhal.TensorPairing

namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Vacuum

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ₀ : Fin 0 → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ₀))

/-- With no red strands every red-ordered idempotent of the empty block is the unit. -/
theorem vacuum_mk_e (s : Seq (stendhalWeight 0 (0 : Multiset I))) (hs : IsRedOrdered s) :
    TensorProductAlgebra.mk Q Λ₀ 0 (StendhalAlgebra.e s hs) = 1 := by
  have : IsEmpty (Fin (Multiset.card (stendhalWeight 0 (0 : Multiset I)))) := by
    rw [show Multiset.card (stendhalWeight 0 (0 : Multiset I)) = 0 by simp [stendhalWeight]]
    infer_instance
  obtain rfl : s = vacuumSeq := Subtype.ext (funext isEmptyElim)
  exact vacuumSeq_mk_e Q Λ₀

private theorem finite_vacuum (ν : Multiset I) :
    Module.Finite k (TensorProductAlgebra k Q Λ₀ ν) := by
  by_cases hν : ν = 0
  · subst hν
    let F := tensorProductAlgebraZeroEquiv Q Λ₀
    exact Module.Finite.of_injective F.toLinearEquiv.toLinearMap F.injective
  · obtain rfl : Λ₀ = Fin.elim0 := funext fun j => j.elim0
    let := subsingleton_emptyTensorAlgebra (k := k) Q hν
    exact Module.Finite.of_injective (0 : _ →ₗ[k] k)
      (fun x y _ => Subsingleton.elim x y)

/-- The regular module of the tensor product algebra with no red strands: the coefficient
field in the empty block and zero otherwise (Webster, arXiv:1309.3796v2, Lemma 4.36). -/
def vacuumTest (ν : Multiset I) : GFin (tensorProductGrade G ν) :=
  letI : FiniteDimensional k (GMod.regular (tensorProductGrade G ν)).carrier :=
    finite_vacuum (Q := Q) Λ₀ ν
  { toGMod := GMod.regular (tensorProductGrade G ν) }

private theorem gdimPoly_congr_finrank {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (U : ℤ → Submodule k M) (V : ℤ → Submodule k N)
    (h : ∀ d, Module.finrank k (U d) = Module.finrank k (V d)) : gdimPoly U = gdimPoly V := by
  classical
  let polynomial (f : ℤ → ℤ) : LaurentPolynomial ℤ :=
    if hf : (Function.support f).Finite then .ofCoeff (Finsupp.ofSupportFinite f hf) else 0
  change polynomial _ = polynomial _
  exact congrArg polynomial (funext fun d => congrArg (fun n : ℕ => (n : ℤ)) (h d))

/-- The graded dimension of the vacuum test at a red-ordered idempotent. -/
theorem gdimPoly_vacuumTest (ν : Multiset I) (s : Seq (stendhalWeight 0 ν))
    (hs : IsRedOrdered s) :
    gdimPoly (Graded.idem (vacuumTest Λ₀ G ν).grading
      (TensorProductAlgebra.mk Q Λ₀ ν (StendhalAlgebra.e s hs))) = if ν = 0 then 1 else 0 := by
  obtain rfl : Λ₀ = Fin.elim0 := funext fun j => j.elim0
  by_cases hν : ν = 0
  · subst hν
    rw [vacuum_mk_e, ite_eq_left_iff.mpr (fun h => (h rfl).elim),
      ← sequenceCornerPoly_vacuum (Λ := (Fin.elim0 : Fin 0 → I →₀ ℕ)) G]
    apply gdimPoly_congr_finrank
    intro d
    have hle : tensorProductGrade G (0 : Multiset I) d ≤
        idemSubspace k (TensorProductAlgebra k Q ((Fin.elim0 : Fin 0 → I →₀ ℕ)) 0)
          (1 : TensorProductAlgebra k Q ((Fin.elim0 : Fin 0 → I →₀ ℕ)) 0) :=
      fun z _ => one_smul _ z
    have hc : sequenceCornerGrade G vacuumSeq vacuumSeq_ordered vacuumSeq vacuumSeq_ordered d =
        tensorProductGrade G (0 : Multiset I) d := by
      ext z
      change (z ∈ tensorProductGrade G 0 d ∧ _ ∧ _) ↔ _
      simp only [vacuumSeq_mk_e, one_mul, mul_one, and_self, and_true]
    rw [hc]
    change Module.finrank k (Graded.idem (tensorProductGrade G (0 : Multiset I))
      (1 : TensorProductAlgebra k Q (Fin.elim0 : Fin 0 → I →₀ ℕ) 0) d) = _
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  · rw [ite_eq_right_iff.mpr (fun h => (hν h).elim)]
    let := subsingleton_emptyTensorAlgebra (k := k) Q hν
    have h (d : ℤ) : Module.finrank k
        (Graded.idem (vacuumTest ((Fin.elim0 : Fin 0 → I →₀ ℕ)) G ν).grading
          (TensorProductAlgebra.mk Q ((Fin.elim0 : Fin 0 → I →₀ ℕ)) ν
            (StendhalAlgebra.e s hs)) d) = 0 := by
      have : Subsingleton (Graded.idem (vacuumTest (Fin.elim0 : Fin 0 → I →₀ ℕ) G ν).grading
          (TensorProductAlgebra.mk Q (Fin.elim0 : Fin 0 → I →₀ ℕ) ν (StendhalAlgebra.e s hs)) d) :=
        have : Subsingleton (vacuumTest (Fin.elim0 : Fin 0 → I →₀ ℕ) G ν).carrier :=
          inferInstanceAs (Subsingleton (TensorProductAlgebra k Q (Fin.elim0 : Fin 0 → I →₀ ℕ) ν))
        ⟨fun a b => Subtype.ext (Subtype.ext (Subsingleton.elim _ _))⟩
      exact Module.finrank_zero_of_subsingleton
    simp [gdimPoly, h]
    ext d
    rfl

end Vacuum

section Iterated

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)

/-- The Rouquier grading of the tensor product algebra with red labels `Λ`. -/
abbrev iteratedGrading {n : ℕ} (Λ : Fin n → I →₀ ℕ) : GradingDatum (stendhalQ Q Λ) :=
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

omit [DecidableEq I] in
/-- Omitting the last red strand retains the Rouquier degrees of the earlier strands. -/
theorem restrictRedGrading_iteratedGrading {n : ℕ} (Λ : Fin (n+1) → I →₀ ℕ) :
    restrictRedGrading Q Λ (iteratedGrading C hQ Λ) =
      iteratedGrading C hQ (fun j => Λ (Fin.castSucc j)) := by
  unfold iteratedGrading restrictRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

/-- The same graded module over an equal grading of the algebra. -/
def sameGrading {A : Type*} [Ring A] [Algebra k A] {g h : ℤ → Submodule k A} (e : g = h)
    (M : GFin h) : GFin g where
  carrier := M.carrier
  addCommGroup := M.addCommGroup
  module := M.module
  moduleK := M.moduleK
  isScalarTower := M.isScalarTower
  grading := M.grading
  decomposition := M.decomposition
  gradedSMul := e.symm ▸ M.gradedSMul
  finiteDimensional := M.finiteDimensional

omit [DecidableEq I] in
/-- Changing the grading of the algebra does not change graded dimensions of corners. -/
theorem gdimPoly_idem_sameGrading {A : Type*} [Ring A] [Algebra k A]
    {g h : ℤ → Submodule k A} (e : g = h) (M : GFin h) (x : A) :
    gdimPoly (Graded.idem (sameGrading e M).grading x) = gdimPoly (Graded.idem M.grading x) := by
  subst e
  rfl

/-- The total black content of a family of words. -/
def blockContent {n : ℕ} (u : Fin n → List I) : Multiset I := ∑ j, (u j : Multiset I)

omit [DecidableEq I] in
private theorem symmetricQ (hQ : IsRouquierQ C Q) : KLRSymm Q :=
  fun i j h => (hQ.symm i j h).symm

/-- Webster's standard module `S_κ^i` (arXiv:1309.3796v2, §5, before Proposition 5.6) for
the ordinary words `u_j` on the red strands: the iterated standardization of the cyclotomic
word projectives `R^{λ_j} e(u_j)`, placed in the black block `ν` (zero off the block of the
total content). -/
def iteratedStandard : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (u : Fin n → List I) →
    (ν : Multiset I) → GFin (tensorProductGrade (iteratedGrading C hQ Λ) ν)
  | 0, Λ, _, ν => vacuumTest Λ (iteratedGrading C hQ Λ) ν
  | n+1, Λ, u, ν => standardizationTestAt Λ (iteratedGrading C hQ Λ)
      (blockContent fun j => u (Fin.castSucc j)) (u (Fin.last n)) (symmetricQ C hQ)
      (sameGrading (congrArg (fun g => tensorProductGrade g _)
        (restrictRedGrading_iteratedGrading C hQ Λ))
        (iteratedStandard n (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j)) _))
      (cyclotomicWordModule C (Λ (Fin.last n)) hQ (KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl)) ν

theorem iteratedStandard_succ {n : ℕ} (Λ : Fin (n+1) → I →₀ ℕ) (u : Fin (n+1) → List I)
    (ν : Multiset I) :
    iteratedStandard C hQ (n+1) Λ u ν = standardizationTestAt Λ (iteratedGrading C hQ Λ)
      (blockContent fun j => u (Fin.castSucc j)) (u (Fin.last n)) (symmetricQ C hQ)
      (sameGrading (congrArg (fun g => tensorProductGrade g _)
        (restrictRedGrading_iteratedGrading C hQ Λ))
        (iteratedStandard C hQ n (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j)) _))
      (cyclotomicWordModule C (Λ (Fin.last n)) hQ (KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl))
      ν := by
  rw [iteratedStandard]

/-- The iterated standard module vanishes on black blocks other than its total content. -/
theorem iteratedStandard_of_ne : ∀ (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I)
    {ν : Multiset I} (_ : blockContent u ≠ ν) (w : TensorWordAt n ν),
    gdimPoly (Graded.idem (iteratedStandard C hQ n Λ u ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w)) = 0
  | 0, Λ, u, ν, h, w => by
    rcases w with ⟨w, rfl⟩
    change gdimPoly (Graded.idem (vacuumTest Λ (iteratedGrading C hQ Λ) _).grading
      (TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e w.loading w.blocks_redOrdered))) = 0
    rw [gdimPoly_vacuumTest, ite_eq_right_iff.mpr]
    intro hw
    exact (h (by simp [blockContent, hw])).elim
  | n+1, Λ, u, ν, h, w => by
    refine standardizationTestAt_of_ne Λ (iteratedGrading C hQ Λ) _ _ (symmetricQ C hQ) _ _
      (fun he => h ?_) w
    rw [← he, blockContent, blockContent, Fin.sum_univ_castSucc]

end Iterated

section IteratedCharacter

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF

variable {I : Type} [DecidableEq I] [Finite I] {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
private local instance iteratedVNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩

/-- The tensor product of the ordinary lowering words `F_{u_j} v_{λ_j}`. -/
def wordTensor {n : ℕ} (wt : Fin n → Dom R) (u : Fin n → List I) : TensorSpace wt :=
  PiTensorProduct.tprod 𝕂 fun j =>
    ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 (IrreducibleModule R v (wt j).1) (F R v i)) (u j)
      (IrreducibleModule.hwv R v (wt j).1)

omit [Finite I] in
theorem wordTensor_succ {n : ℕ} (wt : Fin (n+1) → Dom R) (u : Fin (n+1) → List I) :
    wordTensor C wt u = appendTensor wt (wordTensor C (fun j => wt (Fin.castSucc j))
      (fun j => u (Fin.castSucc j)))
      (ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 _ (F R v i)) (u (Fin.last n))
        (IrreducibleModule.hwv R v (wt (Fin.last n)).1)) := by
  rw [appendTensor, LinearEquiv.eq_symm_apply, wordTensor, tensorSplitLast_tprod]
  rfl

/-- **Characters of iterated standard modules** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.6). At the ordinary loading of a tensor word `w`, the graded dimension of
`S_κ^i` is the componentwise form of `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` with the
bar-ordinary vector of `w`. -/
theorem iteratedStandard_word_zero (Λ : Fin 0 → I →₀ ℕ) (u : Fin 0 → List I)
    (wt : Fin 0 → Dom R) (ν : Multiset I) (w : TensorWordAt 0 ν) :
    integralLaurentEval (gdimPoly (Graded.idem (iteratedStandard C hQ 0 Λ u ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w))) =
      TensorPairing.orderedFactorwise hR wt (wordTensor C wt u) (barOrdinaryWord w.1 wt) := by
  rcases w with ⟨w, rfl⟩
  have h0 := gdimPoly_vacuumTest (Q := Q) Λ (iteratedGrading C hQ Λ) _ w.loading
    w.blocks_redOrdered
  have h1 := TensorPairing.isEmptyEquiv_barOrdinaryWord wt w
  change integralLaurentEval (gdimPoly (Graded.idem
    (vacuumTest Λ (iteratedGrading C hQ Λ) _).grading
    (TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e w.loading w.blocks_redOrdered)))) =
    RatFunc.bar (PiTensorProduct.isEmptyEquiv _ (wordTensor C wt u)) *
      PiTensorProduct.isEmptyEquiv _ (barOrdinaryWord w wt)
  rw [h0, h1, wordTensor, PiTensorProduct.isEmptyEquiv_apply_tprod]
  by_cases hw : w.content = 0
  · simp [hw]
  · have hw' : Finsupp.toMultiset w.content ≠ 0 := fun h =>
      hw (by rw [← Finsupp.toMultiset_toFinsupp w.content, h, Multiset.toFinsupp_zero])
    simp [hw, hw']

theorem iteratedStandard_word_succ {n : ℕ} (Λ : Fin (n+1) → I →₀ ℕ) (u : Fin (n+1) → List I)
    (wt : Fin (n+1) → Dom R) (hwt : ∀ i, (wt (Fin.last n)).1 (R.coroot i) = (Λ (Fin.last n) i : ℤ))
    (ih : ∀ (ν : Multiset I) (w : TensorWordAt n ν),
      integralLaurentEval (gdimPoly (Graded.idem (iteratedStandard C hQ n
        (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j)) ν).grading
        (ordinaryLoadingIdem (Q := Q) (fun j => Λ (Fin.castSucc j)) ν w))) =
      TensorPairing.orderedFactorwise hR (fun j => wt (Fin.castSucc j))
        (wordTensor C (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j)))
        (barOrdinaryWord w.1 (fun j => wt (Fin.castSucc j))))
    (ν : Multiset I) (w : TensorWordAt (n+1) ν) :
    integralLaurentEval (gdimPoly (Graded.idem (iteratedStandard C hQ (n+1) Λ u ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w))) =
      TensorPairing.orderedFactorwise hR wt (wordTensor C wt u) (barOrdinaryWord w.1 wt) := by
  let X := sameGrading (congrArg (fun g => tensorProductGrade g _)
    (restrictRedGrading_iteratedGrading C hQ Λ))
    (iteratedStandard C hQ n (fun j => Λ (Fin.castSucc j)) (fun j => u (Fin.castSucc j))
      (blockContent fun j => u (Fin.castSucc j)))
  let Z := cyclotomicWordModule C (Λ (Fin.last n)) hQ
    (KLRAlgebra.Seq.ofList (u (Fin.last n)) rfl)
  let f := TensorPairing.orderedFactorwise hR (fun j => wt (Fin.castSucc j))
    (wordTensor C (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j)))
  let g := websterFormRight C (wt (Fin.last n)) hR
    (ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 _ (F R v i)) (u (Fin.last n))
      (IrreducibleModule.hwv R v (wt (Fin.last n)).1))
  have hX : ∀ p : TensorWordAt n (blockContent fun j => u (Fin.castSucc j)),
      integralLaurentEval (gdimPoly (Graded.idem X.grading
        (ordinaryLoadingIdem (Q := Q) (fun j => Λ (Fin.castSucc j)) _ p))) =
        f (barOrdinaryWord p.1 (fun j => wt (Fin.castSucc j))) := fun p => by
    rw [gdimPoly_idem_sameGrading]
    exact ih _ p
  have key := standardizationTestAt_word_of_wordCharacters Λ C hQ
    (blockContent fun j => u (Fin.castSucc j)) (u (Fin.last n)) X Z wt f g
    hwt hX
    (fun p hp => by
      rw [← ih _ ⟨p, rfl⟩, iteratedStandard_of_ne C hQ _ _ _ (Ne.symm hp)]
      simp)
    (fun s hs => cyclotomicWordModule_word C (Λ (Fin.last n)) hQ (wt (Fin.last n))
      (fun i => (hwt i).symm) hR _ s rfl hs)
    (fun s hs => websterForm_suffix_eq_zero C (wt (Fin.last n)) hR _ s hs) ν w
  rw [wordTensor_succ, TensorPairing.orderedFactorwise_appendTensor hR wt _ _ g
    (fun _ => rfl), iteratedStandard_succ]
  exact key

/-- **Characters of iterated standard modules** (Webster, arXiv:1309.3796v2, proof of
Proposition 5.6). At the ordinary loading of a tensor word `w`, the graded dimension of
`S_κ^i` is the componentwise form of `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` with the
bar-ordinary vector of `w`. -/
theorem iteratedStandard_word (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I)
    (wt : Fin n → Dom R) (hwt : ∀ j i, (wt j).1 (R.coroot i) = (Λ j i : ℤ))
    (ν : Multiset I) (w : TensorWordAt n ν) :
    integralLaurentEval (gdimPoly (Graded.idem (iteratedStandard C hQ n Λ u ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w))) =
      TensorPairing.orderedFactorwise hR wt (wordTensor C wt u) (barOrdinaryWord w.1 wt) := by
  induction n generalizing ν with
  | zero => exact iteratedStandard_word_zero C hQ hR Λ u wt ν w
  | succ n ih =>
    exact iteratedStandard_word_succ C hQ hR Λ u wt (hwt (Fin.last n))
      (fun ν w => ih _ _ _ (fun j => hwt (Fin.castSucc j)) ν w) ν w

end IteratedCharacter

end Categorification.Stendhal.FirstWeight
