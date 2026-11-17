/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerHeadRestriction
import Categorification.WeightedKLR.RedStrands.LastRedRank

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

open KLR Categorification.Graded GProj
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
  support : ∀ v : Cut, ¬ v.1.1 ≤ u.1.1 →
    ∃ a : T, (q) v a = (ψ) v 1 ∧ ∀ x : carrier, (q) u a • x = 0

attribute [instance] LastRedInducedCut.addCommGroup LastRedInducedCut.moduleK
  LastRedInducedCut.module LastRedInducedCut.isScalarTower

private def HeadAtCut (u : Cut) (b : IndecClass ((𝓑) u)) (s : IndecClass 𝓐) : Prop :=
  Nonempty (CornerTopRestriction ((q) u) ((ψ) u) b s) ∧
  ∀ v : Cut, ¬ v.1.1 ≤ u.1.1 → ∃ a : T, (q) v a = (ψ) v 1 ∧ ∀ x : s.top, a • x=0

include hQ in
private theorem headAtCut_exists (u : Cut) (b : IndecClass ((𝓑) u)) (V : LastRedInducedCut Λ ν G u b) :
    ∃ s, HeadAtCut Λ ν G u b s := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional 𝓐
  let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) u.1.1 (Λ (Fin.last ℓ)) u.1.2
  let := Module.Finite.trans (R := k) (A := factorAlgebra (Q := Q) Λ ν u) (M := b.top)
  let := (IndecClass.isGradedSimple_top b).isSimpleModule
  obtain ⟨s,hs,hzero⟩ := exists_cornerHeadRestriction (𝒜 := 𝓐) ((q) u) ((ψ) u) V.carrier
    (RingCon.mkₐ_surjective _) b V.recover.some
  refine ⟨s,hs,?_⟩
  intro v h
  obtain ⟨a,ha,hv⟩ := V.support v h
  exact ⟨a,ha,hzero a hv⟩

private theorem headAtCut_le {u v : Cut} {b : IndecClass ((𝓑) u)} {c : IndecClass ((𝓑) v)}
    {s : IndecClass 𝓐} (hb : HeadAtCut Λ ν G u b s) (hc : HeadAtCut Λ ν G v c s) :
    u.1.1 ≤ v.1.1 := by
  by_contra hn
  obtain ⟨a,ha,hz⟩ := hc.2 u hn
  let f := hb.1.some
  let := (IndecClass.isGradedSimple_top b).nontrivial
  obtain ⟨x,hx⟩ := exists_ne (0 : b.top)
  have h := f.intertwines a 1 ha x
  rw [one_smul,hz] at h
  exact hx (f.injective (h.symm.trans f.incl.map_zero.symm))

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
    rintro ⟨u,b⟩ ⟨v,c⟩ he
    have hb := chosen ⟨u,b⟩
    rw [he] at hb
    have hc := chosen ⟨v,c⟩
    have hθ := le_antisymm (headAtCut_le Λ ν G hb hc) (headAtCut_le Λ ν G hc hb)
    have huv : u=v := by
      apply Subtype.ext
      apply Prod.ext hθ
      exact add_left_cancel (show u.1.1 + u.1.2 = u.1.1 + v.1.2 from u.2.trans (hθ ▸ v.2).symm)
    subst v
    let := lastRedLayerSource_finite hQ (Λ ∘ Fin.castSucc) u.1.1 (Λ (Fin.last ℓ)) u.1.2
    let := HasGdim.of_finiteDimensional ((𝓑) u)
    have hbc := CornerTopRestriction.eq ((q) u) ((ψ) u) (RingCon.mkₐ_surjective _) hb.1.some hc.1.some
    cases hbc
    rfl
  let factors := fun u : Cut => (lastRedLayerSourceIndecClassEquiv hQ (Λ ∘ Fin.castSucc) u.1.1
    (Λ (Fin.last ℓ)) u.1.2 (restrictRedGrading Q Λ G) (restrictBlackGrading Q Λ G)).symm.toEmbedding
  exact (Function.Embedding.sigmaMap (Function.Embedding.refl _) factors).trans ⟨chooseHead,hinj⟩

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

end Categorification.Stendhal
