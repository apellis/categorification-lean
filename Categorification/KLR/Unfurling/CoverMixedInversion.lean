/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingMixedAssembly
import Categorification.KLR.Unfurling.SpectralRouqFamily

/-!
# Mixed inversion for the cyclotomic and spectral furled families

Webster, arXiv:1603.06311v3, Lemma `lem:g-action`, and Brundan,
arXiv:1501.00350v1, Definition 1.1, (1.7).

Specialize the proved blockwise mixed inversion theorem to `coverRouqFamily`,
`spectralRouqFamily` and `GenericFields.rouqFamily`. Cover mixed inversion,
upward relations, nilpotence and irrelevant-edge vanishing are supplied by the
cyclotomic cover. No furled mixed inversion or same-colour inverse data are inputs.
The polynomial assumptions of the underlying family constructors are unchanged.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
universe u v w u₄
variable {I : Type*} [DecidableEq I] {L : Type v} [Field L]
  {P : I → I → MvPolynomial (Fin 2) L}
  {Jm Jp : Type u} [DecidableEq Jm] [DecidableEq Jp]
  (D : UnfurlingDatum L P (Jm ⊕ Jp)) (Λm : Jm → ℕ) (Λp : Jp → ℕ)
  {C : CartanDatum I} {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X)
  (hΛm : ∀ i, ({a | D.π (.inl a) = i ∧ Λm a ≠ 0} : Set Jm).Finite) (hΛp : ∀ i, ({a | D.π (.inr a) = i ∧ Λp a ≠ 0} : Set Jp).Finite)
  (hD : NoCrossArrows D)
  (hμ : ∀ i, RD.pair (RD.iY i) μ = ∑ᶠ a : {a // D.π a = i}, coverBaseVal Λm Λp a.1)
  (hcover : ∀ (c : Jm ⊕ Jp) (i : I), i ≠ D.π c →
      ∑ᶠ a : {a // D.π a = i}, (((D.arrows a.1 c + D.arrows c a.1 : ℕ)) : ℤ) =
        -RD.pair (RD.iY i) (RD.iX (D.π c)))

/-- Brundan (1.7) for Webster's furled cyclotomic cover (`lem:g-action`), with
all mixed-cover and omitted-path conditions discharged. -/
theorem coverRouqFamily_mixedInversion {Q : I → I → MvPolynomial (Fin 2) L}
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b)) :
    BrundanMixedInversion (coverRouqFamily.{u, v, w} D Λm Λp RD μ hΛm hΛp hD hμ hcover hPQ) := by
  intro i j hij a b c d hj hi' hi hj'
  exact Furling.MixedBlocks.isIso_mixed D hj hi' hi hj'
    (coverProduct_upKLR_unfQ D Λm Λp hD)
    (coverProduct_mixedInversion (arrowsNeg D) Λm (arrowsPos D) Λp)
    (coverProduct_dot_isNilpotent D Λm Λp) (fun _ => rfl)
    (fun β a _ h hr => (coverFurling_isZero D Λm Λp RD μ hΛm hΛp β a h hr).1) hij
end Categorification.KLR.Unfurling

namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep MvPolynomial
universe u v z w u₄
variable {I : Type u} [DecidableEq I] {K : Type v} {L : Type z}
  [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [IsIntegrallyClosedIn K L]
  (P₀ : I → I → MvPolynomial (Fin 2) K) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, (d i : L) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap K L) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j →
    ∃ D, (MvPolynomial.map (algebraMap K L) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)
  {C : CartanDatum I} {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X)
  {A : Type*} [Fintype A]
  (zm : I → A → {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)})
  (zp : I → A → {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)})
  (nm np : I → A → ℕ)
  (hμ : ∀ i, RD.pair (RD.iY i) μ = ∑ q, ((np i q : ℤ) - nm i q))
  (Q : I → I → MvPolynomial (Fin 2) L)
  (hPQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.map (algebraMap K L) (P₀ b a) *
    rename ![1, 0] (MvPolynomial.map (algebraMap K L) (P₀ a b)))
  (hext : ∀ a b, a ≠ b → (Q a b).coeff (Finsupp.single 0 (C.dij a b)) ≠ 0)

/-- Brundan (1.7) for the full spectral-cover family in Webster's `lem:g-action`. -/
theorem spectralRouqFamily_mixedInversion :
    BrundanMixedInversion (spectralRouqFamily.{u, v, z, w} P₀ d hdpos hd hP hhom RD μ
      zm zp nm np hμ Q hPQ hext) :=
  coverRouqFamily_mixedInversion (coverDatum P₀ d hdpos hd hP hhom)
    (coverWeightNeg zm nm) (coverWeightPos zp np) RD μ
    (coverWeightNeg_finite_fibre zm nm) (coverWeightPos_finite_fibre zp np)
    (coverDatum_noCrossArrows P₀ d hdpos hd hP hhom)
    (fun i => (hμ i).trans (coverDatum_finsum_base P₀ d hdpos hd hP hhom zm zp nm np i).symm)
    (coverDatum_finsum_arrows P₀ d hdpos hd hP hhom C RD Q hPQ hext) hPQ
end Categorification.KLR.Unfurling

namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot TwoRep MvPolynomial
universe u v w u₄
variable {I : Type u} [DecidableEq I] (k : Type v) [Field k] (s nb M : ℕ)
  {C : CartanDatum I} {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X)
variable (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s nb))) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, (d i : (L k (I × Slots s nb) (I × Slots s nb))) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap (K k (I × Slots s nb)) (L k (I × Slots s nb) (I × Slots s nb))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j →
    ∃ D, (MvPolynomial.map (algebraMap (K k (I × Slots s nb)) (L k (I × Slots s nb) (I × Slots s nb))) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)
  (Q : I → I → MvPolynomial (Fin 2) (L k (I × Slots s nb) (I × Slots s nb)))
  (hPQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.map (algebraMap (K k (I × Slots s nb)) (L k (I × Slots s nb) (I × Slots s nb))) (P₀ b a) *
    rename ![1, 0] (MvPolynomial.map (algebraMap (K k (I × Slots s nb)) (L k (I × Slots s nb) (I × Slots s nb))) (P₀ a b)))
  (hext : ∀ a b, a ≠ b → (Q a b).coeff (Finsupp.single 0 (C.dij a b)) ≠ 0)

/-- Brundan (1.7) for the generic-field family used in Webster's nondegeneracy proof.
Only the polynomial-cover assumptions of `rouqFamily` remain. -/
theorem rouqFamily_mixedInversion :
    BrundanMixedInversion (rouqFamily.{u, v, w} k s nb M RD μ P₀ d hdpos hd hP hhom Q hPQ hext) :=
  spectralRouqFamily_mixedInversion P₀ d hdpos hd hP hhom RD μ
    (zm k I (Slots s nb)) (zp k I (Slots s nb))
    (negLevel s nb M (fun i => RD.pair (RD.iY i) μ))
    (posLevel s nb M (fun i => RD.pair (RD.iY i) μ))
    (fun i => (sum_level_difference s nb M (fun i => RD.pair (RD.iY i) μ) i).symm) Q hPQ hext
end Categorification.KLR.Unfurling.GenericFields
