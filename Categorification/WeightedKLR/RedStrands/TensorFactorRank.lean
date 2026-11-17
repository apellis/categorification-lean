/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShuffleCriterion
import Categorification.WeightedKLR.RedStrands.SingleRedEulerAdjunction
import Mathlib.RingTheory.Flat.Domain

/-!
# The tensor rank at a last-red split

Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38. The earlier
projective classes and the final cyclotomic classes give distinct pure
tensors for every split of the total black content. Over the fraction field
these vectors remain linearly independent. This supplies the tensor-side
inequality in the comparison by ordinary shuffle characters.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR QuantumGroup QuantumGroup.UDot Categorification.Graded GProj LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF TensorProduct
open scoped TensorProduct
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv

local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

private theorem laurentEval_eq (c : LP) : laurentEval vQ c = integralLaurentEval c := by
  obtain ⟨d,rfl⟩ := (LaurentPolynomial.invert (R := ℤ)).surjective c
  rw [KLGamma.laurentEval_vQ_invert, CycKLR.integralEval_invert]

private theorem rational_independent {M J : Type*} [AddCommGroup M] [Module L M] [Module LP M]
    (h : ∀ (c : LP) (x : M), c • x = integralLaurentEval c • x) {b : J → M}
    (hb : LinearIndependent LP b) : LinearIndependent L b := by
  let := KLGamma.vAlgebra
  let := KLGamma.isFractionRing_vAlgebra
  let : IsScalarTower LP L M := ⟨fun c a x => by
    rw [Algebra.smul_def, mul_smul, h]
    exact congrArg (fun z : L => z • (a • x)) (laurentEval_eq c)⟩
  exact hb.localization L (nonZeroDivisors LP)

private theorem integral_independent {M J : Type*} [AddCommGroup M] [Module L M] [Module LP M]
    (h : ∀ (c : LP) (x : M), c • x = integralLaurentEval c • x) {b : J → M}
    (hb : LinearIndependent L b) : LinearIndependent LP b := by
  rw [linearIndependent_iff'] at hb ⊢
  intro s c hs j hj
  apply integralLaurentEval_injective
  rw [map_zero]
  apply hb s (fun i => integralLaurentEval (c i)) _ j hj
  simpa only [← h] using hs

private theorem semilinear_independent {P V J : Type*} [AddCommMonoid P] [Module LP P]
    [AddCommMonoid V] [Module LP V] (e : P ≃ₛₗ[invLP.toRingHom] V) {b : J → P}
    (hb : LinearIndependent LP b) : LinearIndependent LP (fun j => e (b j)) :=
  hb.map_of_surjective_injectiveₛ invLP e.toAddEquiv.toAddMonoidHom invLP.surjective e.injective e.map_smulₛₗ

private theorem lattice_image_independent {P T J : Type*} [AddCommMonoid P] [Module LP P]
    [AddCommGroup T] [Module LP T] (V : Submodule LP T) (e : P ≃ₛₗ[invLP.toRingHom] V)
    {b : J → P} (hb : LinearIndependent LP b) :
    LinearIndependent LP (fun j => (e (b j) : T)) :=
  (semilinear_independent (P := P) (V := V) e hb).map' V.subtype V.ker_subtype

private theorem indec_image_independent {k A P : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommMonoid P] [Module LP P] (D : ℤ → Submodule k A) [GradedAlgebra D] [HasGdim D]
    (e : K0 D ≃ₛₗ[invLP.toRingHom] P) :
    LinearIndependent LP (fun j : IndecClass D => e (K0.of j.rep)) :=
  semilinear_independent e (K0.linearIndependent_indec D)

private def factorIndex {I : Type} {A B : Multiset I → Type*} {β : Multiset I}
    (p : Σ u : LastRedWeightSplit β, A u.1.1 × B u.1.2) : (Σ α, A α) × (Σ γ, B γ) :=
  (⟨_,p.2.1⟩,⟨_,p.2.2⟩)

private theorem factorIndex_injective {I : Type} {A B : Multiset I → Type*} {β : Multiset I} :
    Function.Injective (factorIndex (A := A) (B := B) (β := β)) := by
  rintro ⟨⟨⟨a,b⟩,h⟩,x,y⟩ ⟨⟨⟨a',b'⟩,h'⟩,x',y'⟩ e
  change (Sigma.mk a x, Sigma.mk b y) = (Sigma.mk a' x', Sigma.mk b' y') at e
  obtain ⟨e,f⟩ := Prod.mk.inj e
  cases e
  cases f
  rfl

private theorem pair_count {M N T A B J : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T] [Module L M] [Module L N] [Module L T]
    [Module LP T] (e : T ≃ₗ[L] M ⊗[L] N) (S : Submodule LP T) [Module.Finite LP S]
    (smulT : ∀ (c : LP) (z : T), c • z = integralLaurentEval c • z)
    (x : A → M) (y : B → N) (hx : LinearIndependent L x) (hy : LinearIndependent L y)
    (j : J → A × B) (hj : Function.Injective j)
    (hmem : ∀ i, e.symm (x (j i).1 ⊗ₜ[L] y (j i).2) ∈ S) : Nat.card J ≤ Module.finrank LP S := by
  classical
  let f (i : J) : S := ⟨_,hmem i⟩
  have hxy := (hx.tmul_of_isDomain hy).map' e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hf : LinearIndependent LP f := LinearIndependent.of_comp S.subtype (integral_independent smulT (hxy.comp j hj))
  have := hf.finite
  let := Fintype.ofFinite J
  simpa [Nat.card_eq_fintype_card] using hf.fintype_card_le_finrank

variable {I : Type} {Y : Type*} [DecidableEq I] [AddCommGroup Y] [Finite I] {ℓ : ℕ}
    (C : CartanDatum I) {R : C.toLusztig.RootDatum Y} (wt : Fin (ℓ+1) → Dom R) (hR : R.IsXRegular)
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "λ₁" => wt (Fin.last ℓ)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v λ₁.1
local notation "W" => integralTensorWeight wt hR

private theorem append_mem_weight {α γ : Multiset I} {x : V₀} {y : V₁}
    (hx : x ∈ integralTensorWeight wt₀ hR α.toFinsupp) (hy : y ∈ hwIntegral λ₁)
    (hw : y ∈ weightSpace R v V₁ (λ₁.1 - R.rootSum γ.toFinsupp)) :
    appendTensor wt x y ∈ W (α+γ).toFinsupp := by
  refine ⟨append_mem_integralTensor wt hx.1 hy, (tensorWeightProj_eq_self_iff wt hR _ _).2 ?_⟩
  intro z
  have hxz := (tensorWeightProj_eq_self_iff wt₀ hR _ _).1 hx.2 z
  rw [← tensorRepresentation_K, tensorRepresentation_K_append, tensorRepresentation_K, hxz, hw z]
  simp only [appendTensor, TensorProduct.smul_tmul_smul, map_smul,
    ← zpow_add₀ (show (RatFunc.X : L) ≠ 0 from RatFunc.X_ne_zero)]
  congr 2
  change _ = ((∑ j, (wt j).1) - R.rootSum (α+γ).toFinsupp) z
  rw [Fin.sum_univ_castSucc, map_add, R.rootSum_add]
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply]
  abel

variable {A B : Multiset I → Type*}

private theorem directSum_independent {R D N : Type*} [CommRing R] [DecidableEq D] [AddCommGroup N] [Module R N]
    (M J : D → Type*) [∀ d, AddCommGroup (M d)] [∀ d, Module R (M d)]
    (f : DirectSum D M →ₗ[R] N) (hf : Function.Injective f) (b : ∀ d, J d → M d)
    (hb : ∀ d, LinearIndependent R (b d)) (g : (Σ d, J d) → N)
    (h : ∀ p : Σ d, J d, f (DirectSum.of M p.1 (b p.1 p.2)) = g p) : LinearIndependent R g := by
  have hs : LinearIndependent R (fun p : Σ d, J d => DFinsupp.single p.1 (b p.1 p.2)) :=
    DFinsupp.linearIndependent_single (R := R) (M := M) b hb
  have h' : f ∘ (fun p : Σ d, J d => DFinsupp.single p.1 (b p.1 p.2)) = g := funext h
  rw [← h']
  exact hs.map' f (LinearMap.ker_eq_bot.mpr hf)

private theorem independent_weight_basis {R T D : Type*} [CommRing R] [AddCommGroup T] [Module R T] [DecidableEq D]
    (U : D → Submodule R T) (S : Submodule R T) (t : DirectSum D (fun d => (U d : Type _)) ≃ₗ[R] S)
    (ht : ∀ d (x : U d), ((t (DirectSum.of (fun d => (U d : Type _)) d x) : S) : T) = x)
    {J : D → Type*} (b : ∀ d, J d → U d) (h : ∀ d, LinearIndependent R (b d)) :
    LinearIndependent R (fun p : Σ d, J d => ((b p.1 p.2) : T)) := by
  let f := S.subtype.comp t.toLinearMap
  exact directSum_independent (R := R) (fun d => (U d : Type _)) J f (S.subtype_injective.comp t.injective) b h _
    (fun p => ht p.1 (b p.1 p.2))

/-- Linearly independent factor families of integral vectors in the specified
weights yield independent vectors for every split of the total black content.
The numerical rank estimate is used on the finite target of a surjection. -/
theorem lastRedPairCount_le_finrank (β : Multiset I)
    (x : (Σ α, A α) → V₀) (y : (Σ γ, B γ) → V₁)
    (hx : ∀ p, x p ∈ integralTensorWeight wt₀ hR p.1.toFinsupp)
    (hy : ∀ p, y p ∈ hwIntegral λ₁) (hw : ∀ p, y p ∈ weightSpace R v V₁ (λ₁.1 - R.rootSum p.1.toFinsupp))
    (hxi : LinearIndependent LP x) (hyi : LinearIndependent LP y)
    [Module.Finite LP (W β.toFinsupp)] :
    Nat.card (Σ u : LastRedWeightSplit β, A u.1.1 × B u.1.2) ≤ Module.finrank LP (W β.toFinsupp) := by
  let j := factorIndex (A := A) (B := B) (β := β)
  apply pair_count (tensorSplitLast wt) (W β.toFinsupp) (tensor_laurent_smul wt) x y
    (rational_independent (tensor_laurent_smul wt₀) hxi) (rational_independent (hw_laurent_smul_eq λ₁) hyi)
    j factorIndex_injective
  intro p
  apply (congrArg (fun γ : Multiset I => W γ.toFinsupp) p.1.2).le
  exact append_mem_weight C wt hR (hx (j p).1) (hy (j p).2) (hw (j p).2)


section LastRed
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) (hQ : IsRouquierQ C Q)
local notation "Λ₀" => Λ ∘ Fin.castSucc
local notation "Λlast" => Λ (Fin.last ℓ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "E" => fun α => tensorProductGrade (restrictRedGrading Q Λ G) α
local notation "F" => fun γ => CycKLR.grade hQ.gradingDatum Λlast γ
local notation "U" => fun α : Multiset I => (integralTensorWeight wt₀ hR (Multiset.toFinsupp α) : Type _)

private def pairingDatum : WeightDatum C (Y →+ ℤ) Y where
  pair := (AddMonoidHom.id (Y →+ ℤ)).flip
  iX := R.root
  iY := R.coroot
  pair_iY_iX := R.root_coroot

omit [Finite I] in
private theorem sum_roots (γ : Multiset I) : (γ.map R.root).sum = R.rootSum γ.toFinsupp := by
  induction γ using Multiset.induction_on with
  | empty => simp
  | cons i s ih => rw [← Multiset.singleton_add, map_add, R.rootSum_add]; simp [ih]

/-- The tensor weight has at least as many independent integral vectors as the
pairs of indecomposable projectives at all earlier/final content splits. Only
the identification of the earlier blocks is an induction hypothesis. The final
factor is identified by the cyclotomic highest-weight theorem. -/
theorem lastRedFactorCount_le_finrank (β : Multiset I)
    (hwt : ∀ i, (Λlast i : ℤ) = λ₁.1 (R.coroot i))
    (pref : ∀ α : Multiset I, K0 (E α) ≃ₛₗ[invLP.toRingHom] U α)
    [Module.Finite LP (W β.toFinsupp)] :
    Nat.card (Σ u : LastRedWeightSplit β, LastRedFactorClasses Λ β G u) ≤ Module.finrank LP (W β.toFinsupp) := by
  classical
  let A (α : Multiset I) := IndecClass (E α)
  let B (γ : Multiset I) := IndecClass (F γ)
  let x₀ (α : Multiset I) (j : A α) : U α := pref α (K0.of j.rep)
  let x (p : Σ α : Multiset I, A α) : V₀ := x₀ p.1 p.2
  let RD := pairingDatum C (R := R)
  let e := CycKLR.projectiveIntegralEquiv hQ Λlast RD λ₁.1 hwt hR
  let ι (γ : Multiset I) := DirectSum.lof LP _ (fun ν => K0 (F ν)) γ
  let y (p : Σ γ : Multiset I, B γ) : V₁ := (e (ι p.1 (K0.of p.2.rep))).val
  have hxi₀ (α : Multiset I) : LinearIndependent LP (x₀ α) := by
    let := tensorProductAlgebra_finite Λ₀ α hQ
    let := HasGdim.of_finiteDimensional (E α)
    exact indec_image_independent (P := U α) (E α) (pref α)
  have hxi : LinearIndependent LP x := independent_weight_basis
    (fun α : Multiset I => integralTensorWeight wt₀ hR α.toFinsupp) (integralTensor wt₀)
    (tensorWeightSumEquiv C wt₀ hR) (tensorWeightSumEquiv_of C wt₀ hR) x₀ hxi₀
  have hQ' : ∀ i j, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff := fun i j hij => by
    obtain ⟨c,hc,he⟩ := hQ.polyInY_leading i j hij
    rw [he]
    exact hc.map Polynomial.C
  have hyi : LinearIndependent LP y := by
    have hh := lattice_image_independent (T := V₁) (hwIntegral λ₁) e
      (CycKLR.projectiveK0Basis hQ.gradingDatum Λlast hQ').linearIndependent
    convert hh using 1
    funext p
    obtain ⟨γ,j⟩ := p
    change (e (ι γ (K0.of j.rep))).val = (e (CycKLR.projectiveK0Basis hQ.gradingDatum Λlast hQ' ⟨γ,j⟩)).val
    rw [CycKLR.projectiveK0Basis_apply]
    rfl
  have hyw (p : Σ γ : Multiset I, B γ) : y p ∈ weightSpace R v V₁ (λ₁.1 - R.rootSum p.1.toFinsupp) := by
    rw [← sum_roots C]
    exact CycKLR.projectiveIntegralEquiv_lof_mem_weightSpace hQ Λlast RD λ₁.1 hwt hR p.1 (K0.of p.2.rep)
  exact lastRedPairCount_le_finrank C wt hR β x y (fun p => (x₀ p.1 p.2).property)
    (fun p => (e _).property) hyw hxi hyi

omit [DecidableEq I] [Finite I] in
private theorem prefixGrading :
    restrictRedGrading Q Λ G =
      stendhalGradingDatum Λ₀ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ) := by
  unfold restrictRedGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

/-- The tensor-side rank bound at the inductive step of the last-red
filtration (Webster §4.7, Theorem 4.38). -/
theorem lastRedFactorCount_le_of_prefixRelations (β : Multiset I)
    (hwt : ∀ i, (Λlast i : ℤ) = λ₁.1 (R.coroot i))
    (earlier : ∀ α : Multiset I, SameWordRelations Λ₀ C hQ wt₀ hR α)
    [Module.Finite LP (W β.toFinsupp)] :
    Nat.card (Σ u : LastRedWeightSplit β, LastRedFactorClasses Λ β G u) ≤ Module.finrank LP (W β.toFinsupp) := by
  apply lastRedFactorCount_le_finrank C wt hR Λ hQ β hwt
  intro α
  rw [prefixGrading]
  exact ((exists_wordEquivAt_iff Λ₀ C hQ wt₀ hR α).2 (earlier α)).choose

/-- For Webster §4.7, the earlier tensor identification and ordinary
shuffle characters imply the divided-word identification after adding the last
factor. All rank comparisons are supplied by the last-red and cyclotomic
theorems. The remaining inputs are separating functionals and their
identification with the ordinary loading characters of finite modules. -/
theorem exists_tensorWordEquiv_of_prefixShuffle
    (hwt : ∀ i, (Λlast i : ℤ) = λ₁.1 (R.coroot i))
    (earlier : ∀ α : Multiset I, SameWordRelations Λ₀ C hQ wt₀ hR α)
    {J : Multiset I → Type*} (S : ∀ β, J β → GFin (tensorProductGrade G β))
    (test : ∀ β, J β → TensorSpace wt →ₗ[L] L)
    (separates : ∀ β, Function.Injective (barWeightCoordinates C wt hR β (test β)))
    (shuffle : ∀ (β : Multiset I) (w : TensorWordAt (ℓ+1) β) j,
      integralLaurentEval (gdimPoly (idem (S β j).grading (ordinaryLoadingIdem (Q := Q) Λ β w))) =
        test β j (barOrdinaryWord w.1 wt)) :
    ∃ e : DirectSum (Multiset I) (fun β => K0 (tensorProductGrade G β)) ≃ₛₗ[invLP.toRingHom] integralTensor wt,
      ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w := by
  apply exists_tensorWordEquiv_of_lastRedShuffle Λ C hQ wt hR S test separates shuffle
  intro β hfinite
  exact lastRedFactorCount_le_of_prefixRelations C wt hR Λ hQ β hwt earlier

end LastRed

end Categorification.Stendhal.FirstWeight
