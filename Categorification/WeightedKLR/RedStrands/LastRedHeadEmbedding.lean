/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerHeadRestriction
import Categorification.WeightedKLR.RedStrands.LastRedRank
import Categorification.WeightedKLR.RedStrands.LastRedParabolicLift

/-!
# Heads of modules induced across the last red strand

Webster, arXiv:1309.3796v2, Theorem 5.8 and Lemma 5.9. An induced
representation recovering the factor simple on its maximal cut has a
simple head on the submodule generated there. The surviving maximal
black prefix and its restriction distinguish the resulting projective
shift classes.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded GProj
open scoped TensorProduct

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {D : QuantumGroup.CartanDatum I}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) (ν : Multiset I) (G : GradingDatum (stendhalQ Q Λ))
    (hQ : IsRouquierQ D Q)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "𝓐" => tensorProductGrade G ν
local notation "Cut" => LastRedWeightSplit ν
local notation "J" => fun u : Cut => smallerSuffixIdeal Q Λ (LastRedWeightSplit.position ν u ℓ)
private abbrev cutQuotient (u : Cut) := ((J) u).ringCon.mkₐ k
local notation "q" => cutQuotient (Q := Q) Λ ν
private abbrev cutLayer (u : Cut) := ((J) u).ringCon.Quotient
local notation "C" => cutLayer (Q := Q) Λ ν
local notation "ψ" => fun u : Cut => lastRedLayerAction Q Λ (LastRedWeightSplit.position ν u ℓ)
  (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ)
/-- Tensor grading of the two block factors on a specified cut. -/
abbrev lastRedFactorGrading (u : Cut) := tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) u.1.1)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) u.1.2)

private abbrev factorAlgebra (u : Cut) := TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) u.1.1 ⊗[k]
  CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) u.1.2

local notation "𝓑" => lastRedFactorGrading Λ ν G

local notation "A₁" => fun θ : Multiset I => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "A₂" => fun β : Multiset I => Multiset.map (Sum.map (id : I → I)
  (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)

omit [DecidableEq I] in
/-- The two input weights of a cut add up to the weight of the block. -/
theorem lastRedCutWeight (u : Cut) :
    (A₁) u.1.1 + (A₂) u.1.2 = stendhalWeight (ℓ+1) ν :=
  (parabolicInputWeights_add (ℓ := ℓ) u.1.1 u.1.2).trans (congrArg (stendhalWeight (ℓ+1)) u.2)

/-- The KLR algebra of the two input weights of a cut. -/
abbrev lastRedCutKLR (u : Cut) :=
  TensorKLR (stendhalQ Q Λ) ((A₁) u.1.1) ((A₂) u.1.2)

/-- Horizontal concatenation at a cut, followed by the projection to the
tensor product algebra. -/
def lastRedCutConcat (u : Cut) : lastRedCutKLR (Q := Q) Λ ν u →ₗ[k] T :=
  (TensorProductAlgebra.mk Q Λ ν).toLinearMap ∘ₗ (orderProjection Q Λ ν).toLinearMap ∘ₗ
    (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).toLinearMap ∘ₗ
      (castKLR (stendhalQ Q Λ) (lastRedCutWeight (ℓ := ℓ) ν u)).toLinearMap ∘ₗ
        concat (stendhalQ Q Λ) ((A₁) u.1.1) ((A₂) u.1.2)

/-- The sector idempotent of a cut lifts to a concatenation. -/
theorem lastRedCutConcat_exists_lift (u : Cut) :
    ∃ t, (q) u (lastRedCutConcat (Q := Q) Λ ν u t) = (ψ) u 1 := by
  obtain ⟨t,_,ht⟩ := lastRedLayerAction_exists_parabolicLift Q Λ (LastRedWeightSplit.position ν u ℓ)
    (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ)
    (lastRedCutWeight (ℓ := ℓ) ν u) 1
  exact ⟨t,ht⟩

/-- Modulo smaller suffixes, a concatenation at a cut acts through the last-red layer on the
images of its two pieces in the factor algebras. -/
theorem lastRedCutConcat_layer (u : Cut) (t : lastRedCutKLR (Q := Q) Λ ν u) :
    (q) u (lastRedCutConcat (Q := Q) Λ ν u t) = (ψ) u (Algebra.TensorProduct.map
      (parabolicPrefixProjection Q Λ u.1.1) (parabolicLastCyclotomic Q Λ u.1.2) t) :=
  suffixConcat_eq_lastRedLayerAction Q Λ (LastRedWeightSplit.position ν u ℓ)
    (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ)
    (lastRedCutWeight (ℓ := ℓ) ν u) t

/-- The representation-theoretic inputs for the standard-module head in
Webster, Theorem 5.8. The maximal cut recovers the specified factor simple.
Every cut whose prefix is outside its dominance bound has a lift of its
idempotent that kills the induced representation. -/
structure LastRedInducedCut (u : Cut) (b : IndecClass ((𝓑) u)) where
  /-- Underlying module of the smaller-suffix layer. -/
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [moduleK : Module k carrier]
  [module : Module ((C) u) carrier]
  [isScalarTower : IsScalarTower k ((C) u) carrier]
  /-- Restriction at the original pair of weights. -/
  recover : Nonempty (b.top ≃ₗ[factorAlgebra (Q := Q) Λ ν u] boundaryFixed ((ψ) u) carrier)
  /-- The original black prefix bounds all surviving black prefixes. -/
  support : ∀ v : Cut, ¬ v.1.1 ≤ u.1.1 → ∀ (t : lastRedCutKLR (Q := Q) Λ ν v) (x : carrier),
    (q) u (lastRedCutConcat Λ ν v t) • x = 0

attribute [instance] LastRedInducedCut.addCommGroup LastRedInducedCut.moduleK
  LastRedInducedCut.module LastRedInducedCut.isScalarTower

/-- A shift class `s` is the head at the cut `u` with factor class `b`: its top
restricts to the top of `b` on the sector of `u`, concatenations at cuts whose
black prefix is not below that of `u` kill it, and so does the ideal of
smaller suffixes. -/
def HeadAtCut (u : Cut) (b : IndecClass ((𝓑) u)) (s : IndecClass 𝓐) : Prop :=
  Nonempty (CornerTopRestriction ((q) u) ((ψ) u) b s) ∧
  (∀ v : Cut, ¬ v.1.1 ≤ u.1.1 → ∀ (t : lastRedCutKLR (Q := Q) Λ ν v) (x : s.top),
    lastRedCutConcat Λ ν v t • x = 0) ∧
  ∀ a ∈ (J) u, ∀ x : s.top, a • x = 0

include hQ in
/-- The head at a cut, obtained from an induced representation, is a subquotient of that
representation: a submodule over the smaller-suffix layer maps onto it, compatibly with the
action of the tensor product algebra. -/
theorem exists_headAtCut_subquotient (u : Cut) (b : IndecClass ((𝓑) u))
    (V : LastRedInducedCut Λ ν G u b) :
    ∃ s, HeadAtCut Λ ν G u b s ∧ ∃ (X : Submodule ((C) u) V.carrier) (g : X →ₗ[k] s.top),
      Function.Surjective g ∧ ∀ (a : T) (x : X), g ((q) u a • x) = a • g x := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) u.1.1 (Λ (Fin.last ℓ)) u.1.2
  let := Module.Finite.trans (R := k) (A := factorAlgebra (Q := Q) Λ ν u) (M := b.top)
  let := (IndecClass.isGradedSimple_top b).isSimpleModule
  obtain ⟨s,hs,hzero,hsub⟩ := exists_cornerHeadRestriction (𝒜 := 𝓐) ((q) u) ((ψ) u) V.carrier
    (RingCon.mkₐ_surjective _) b V.recover.some
  refine ⟨s,⟨hs,fun v h t => hzero _ (V.support v h t),fun a ha => hzero a fun x => ?_⟩,hsub⟩
  have h0 : (q) u a = 0 := by
    rw [← map_zero ((q) u)]
    exact RingCon.eq _ |>.2 ((TwoSidedIdeal.rel_iff _ _ _).2 (by rwa [sub_zero]))
  rw [h0]
  exact zero_smul ((C) u) x

include hQ in
private theorem headAtCut_exists (u : Cut) (b : IndecClass ((𝓑) u)) (V : LastRedInducedCut Λ ν G u b) :
    ∃ s, HeadAtCut Λ ν G u b s :=
  (exists_headAtCut_subquotient Λ ν G hQ u b V).imp fun _ h => h.1

/-- Two heads at cuts with the same top have comparable black prefixes. -/
theorem HeadAtCut.le {u v : Cut} {b : IndecClass ((𝓑) u)} {c : IndecClass ((𝓑) v)}
    {s : IndecClass 𝓐} (hb : HeadAtCut Λ ν G u b s) (hc : HeadAtCut Λ ν G v c s) :
    u.1.1 ≤ v.1.1 := by
  by_contra hn
  obtain ⟨t,ht⟩ : ∃ t, (q) u (lastRedCutConcat (Q := Q) Λ ν u t) = (ψ) u 1 :=
    lastRedCutConcat_exists_lift Λ ν u
  have hz := hc.2.1 u hn t
  let f := hb.1.some
  let := (IndecClass.isGradedSimple_top b).nontrivial
  obtain ⟨x,hx⟩ := exists_ne (0 : b.top)
  have h := f.intertwines _ 1 ht x
  rw [one_smul,hz] at h
  exact hx (f.injective (h.symm.trans f.incl.map_zero.symm))

/-- An idempotent concatenation at the cut of a head acts nonzero on its top exactly when its
image in the factor algebra acts nonzero on the top of the factor class. -/
theorem HeadAtCut.exists_smul_ne_zero_iff {u : Cut} {b : IndecClass ((𝓑) u)}
    {s : IndecClass 𝓐} (hs : HeadAtCut Λ ν G u b s) (X : lastRedCutKLR (Q := Q) Λ ν u)
    (hX : IsIdempotentElem (lastRedCutConcat Λ ν u X)) :
    (∃ x : s.top, lastRedCutConcat Λ ν u X • x ≠ 0) ↔
      ∃ y : b.top, Algebra.TensorProduct.map (parabolicPrefixProjection Q Λ u.1.1)
        (parabolicLastCyclotomic Q Λ u.1.2) X • y ≠ 0 := by
  let F := hs.1.some
  have hq := lastRedCutConcat_layer (Q := Q) Λ ν u X
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨t₀,ht₀⟩ := lastRedCutConcat_exists_lift (Q := Q) Λ ν u
    set a := lastRedCutConcat Λ ν u X
    set c := lastRedCutConcat Λ ν u t₀
    have hmem : c * a - a ∈ (J) u := by
      have h0 : (q) u (c * a - a) = 0 := by
        rw [map_sub, map_mul, ht₀, hq, ← map_mul, one_mul, sub_self]
      have := RingCon.eq _ |>.1 (h0.trans (map_zero ((q) u)).symm)
      simpa using (TwoSidedIdeal.rel_iff _ _ _).1 this
    have hfix : c • (a • x) = a • x := by
      rw [smul_smul, ← sub_eq_zero, ← sub_smul]
      exact hs.2.2 _ hmem x
    obtain ⟨y,hy⟩ := F.fixed c ht₀ _ hfix
    refine ⟨y,fun h0 => hx ?_⟩
    have h := F.intertwines a _ hq y
    rw [h0, map_zero, hy, smul_smul, hX.eq] at h
    exact h
  · rintro ⟨y,hy⟩
    refine ⟨F.incl y,fun h0 => hy (F.injective ?_)⟩
    rw [← F.intertwines _ _ hq y, h0, map_zero]

private theorem headAtCut_cut_eq {u v : Cut} {b : IndecClass ((𝓑) u)}
    {c : IndecClass ((𝓑) v)} {s : IndecClass 𝓐} (hb : HeadAtCut Λ ν G u b s)
    (hc : HeadAtCut Λ ν G v c s) : u = v := by
  have hθ := le_antisymm (hb.le Λ ν G hc) (hc.le Λ ν G hb)
  apply Subtype.ext
  apply Prod.ext hθ
  exact add_left_cancel (show u.1.1 + u.1.2 = u.1.1 + v.1.2 from u.2.trans (hθ ▸ v.2).symm)

include hQ in
/-- A head at a cut determines the cut and the factor class. -/
theorem HeadAtCut.sigma_eq {u v : Cut} {b : IndecClass ((𝓑) u)} {c : IndecClass ((𝓑) v)}
    {s : IndecClass 𝓐} (hb : HeadAtCut Λ ν G u b s) (hc : HeadAtCut Λ ν G v c s) :
    (⟨u,b⟩ : Σ u : Cut, IndecClass ((𝓑) u)) = ⟨v,c⟩ := by
  have huv := headAtCut_cut_eq Λ ν G hb hc
  subst v
  let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) u.1.1 (Λ (Fin.last ℓ)) u.1.2
  let := HasGdim.of_finiteDimensional ((𝓑) u)
  have hbc := CornerTopRestriction.eq ((q) u) ((ψ) u) (RingCon.mkₐ_surjective _) hb.1.some hc.1.some
  cases hbc
  rfl

/-- The reverse shift-class injection, conditional on constructing the
projected induced representations with the recovery and support in
`LastRedInducedCut` (Webster, Theorem 5.8). -/
def lastRedHeadEmbedding
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b)) :
    (Σ u : Cut, LastRedFactorClasses Λ ν G u) ↪ IndecClass 𝓐 := by
  classical
  let chooseHead (z : Σ u : Cut, IndecClass ((𝓑) u)) :=
    (headAtCut_exists Λ ν G hQ z.1 z.2 (induce z.1 z.2).some).choose
  have chosen (z : Σ u : Cut, IndecClass ((𝓑) u)) : HeadAtCut Λ ν G z.1 z.2 (chooseHead z) :=
    (headAtCut_exists Λ ν G hQ z.1 z.2 (induce z.1 z.2).some).choose_spec
  have hinj : Function.Injective chooseHead := by
    intro z z' he
    have hb := chosen z
    rw [he] at hb
    exact HeadAtCut.sigma_eq Λ ν G hQ hb (chosen z')
  let factors := fun u : Cut => (lastRedLayerSourceIndecClassEquiv hQ (Λ ∘ Fin.castSucc) u.1.1
    (Λ (Fin.last ℓ)) u.1.2 (restrictRedGrading Q Λ G) (restrictBlackGrading Q Λ G)).symm.toEmbedding
  exact (Function.Embedding.sigmaMap (Function.Embedding.refl _) factors).trans ⟨chooseHead,hinj⟩

/-- Shift classes of the factor algebra of a cut, as pairs of factor classes. -/
abbrev lastRedFactorEquiv (u : Cut) : IndecClass ((𝓑) u) ≃ LastRedFactorClasses Λ ν G u :=
  lastRedLayerSourceIndecClassEquiv hQ (Λ ∘ Fin.castSucc) u.1.1
    (Λ (Fin.last ℓ)) u.1.2 (restrictRedGrading Q Λ G) (restrictBlackGrading Q Λ G)

/-- The head attached to a cut and a pair of factor classes is the head at that cut. -/
theorem lastRedHeadEmbedding_headAtCut
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b))
    (u : Cut) (x : LastRedFactorClasses Λ ν G u) :
    HeadAtCut Λ ν G u ((lastRedFactorEquiv Λ ν G hQ u).symm x) (lastRedHeadEmbedding Λ ν G hQ induce ⟨u,x⟩) :=
  (headAtCut_exists Λ ν G hQ u _ (induce u _).some).choose_spec

/-- Under the projected-induction hypotheses, taking the standard-module
head is a bijection on shift classes (Webster, Theorem 5.8). -/
def lastRedHeadEquiv
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b)) :
    (Σ u : Cut, LastRedFactorClasses Λ ν G u) ≃ IndecClass 𝓐 := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  let := finite_indec 𝓐
  let f := lastRedHeadEmbedding Λ ν G hQ induce
  let g := lastRedRankEmbedding Λ ν hQ G
  have hs := Finite.surjective_of_injective (f.injective.comp g.injective)
  exact Equiv.ofBijective f ⟨f.injective,fun y => by
    obtain ⟨x,hx⟩ := hs y
    exact ⟨g x,hx⟩⟩

include hQ in
/-- The rank equality in Webster's Theorem 4.38 follows from the induced
representations realizing the maximal cuts in Theorem 5.8. -/
theorem lastRedK0_rank_eq_of_inducedCut
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b)) :
    Module.rank (LaurentPolynomial ℤ) (K0 𝓐) =
    Cardinal.sum (fun u : LastRedWeightSplit ν =>
      Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade (restrictRedGrading Q Λ G) u.1.1)) *
      Module.rank (LaurentPolynomial ℤ) (K0 (CycKLR.grade (restrictBlackGrading Q Λ G)
        (Λ (Fin.last ℓ)) u.1.2))) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  calc
    _ = Cardinal.mk (IndecClass 𝓐) := (K0.indecBasis 𝓐).mk_eq_rank''.symm
    _ = Cardinal.mk (Σ u : Cut, LastRedFactorClasses Λ ν G u) :=
      Cardinal.mk_congr (lastRedHeadEquiv Λ ν G hQ induce).symm
    _ = _ := lastRedFactorClasses_cardinal Λ ν hQ G

/-- A head at a cut is the head attached to that cut and the factor classes of its
top restriction. -/
theorem lastRedHeadEquiv_of_headAtCut
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b))
    {u : Cut} {b : IndecClass ((𝓑) u)} {s : IndecClass 𝓐} (h : HeadAtCut Λ ν G u b s) :
    lastRedHeadEquiv Λ ν G hQ induce ⟨u, lastRedFactorEquiv Λ ν G hQ u b⟩ = s := by
  obtain ⟨⟨v,x⟩,rfl⟩ := (lastRedHeadEquiv Λ ν G hQ induce).surjective s
  have hv := lastRedHeadEmbedding_headAtCut Λ ν G hQ induce v x
  have he := HeadAtCut.sigma_eq Λ ν G hQ h hv
  obtain ⟨rfl,hb⟩ := Sigma.mk.inj_iff.mp he
  cases eq_of_heq hb
  simp

/-- The head attached to a cut by the bijection is the head at that cut. -/
theorem lastRedHeadEquiv_headAtCut
    (induce : ∀ (u : Cut) (b : IndecClass ((𝓑) u)), Nonempty (LastRedInducedCut Λ ν G u b))
    (u : Cut) (x : LastRedFactorClasses Λ ν G u) :
    HeadAtCut Λ ν G u ((lastRedFactorEquiv Λ ν G hQ u).symm x) (lastRedHeadEquiv Λ ν G hQ induce ⟨u,x⟩) :=
  lastRedHeadEmbedding_headAtCut Λ ν G hQ induce u x

end Categorification.Stendhal
