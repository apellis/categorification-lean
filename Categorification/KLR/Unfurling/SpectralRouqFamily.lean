/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverRouqFamily
import Categorification.KLR.Unfurling.CoverLabels
import Categorification.KLR.Unfurling.GenericWeights

/-!
# Rouquier families from the full spectral cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
§2.3, Lemma `lem:g-action`, and the representations in the proof of `nondegenerate`.

`spectralRouqFamily` specializes the cyclotomic-cover family to `coverDatum` on the
full closure split into scalars inside/outside an integrally closed subfield. The
splitting theorem proves no cross arrows; the branched-cover theorem proves the
correction-count pairing. Finitely many weighted slots per base colour suffice;
there is no finite-colour or globally finite weight-support assumption.

`GenericFields.rouqFamily` further supplies the two fields, generic spectral labels,
and the strand/bubble/balancing multiplicities. The base-weight identity follows
from `sum_level_difference`, at every weight `μ`.

Polynomial inputs remain explicit: nonzero mapped `P₀`, weighted homogeneity,
`Q = P₀ᵒᵖ P₀`, nonzero extremal coefficients, and positive symmetrizers nonzero
in the coefficient field. The latter is the documented restriction of the
polynomial reparametrization route. No block inverses, mixed-cover isomorphisms,
base-weight or branched-cover pairing identities are assumed by the generic-field
constructor. This module does not assert `UnfurledEval` or nondegeneracy.
-/

noncomputable section
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

/-- Webster's full spectral cover gives a furled Rouquier family; all cover pairing and
inversion conditions are proved. Finitely many slots per colour suffice for arbitrary I. -/
def spectralRouqFamily :=
  coverRouqFamily.{max u z, z, w} (coverDatum P₀ d hdpos hd hP hhom)
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

/-- The furled family at arbitrary base weight, with constructed generic fields, spectral
labels and strand/bubble/balancing multiplicities. Only polynomial-cover inputs remain. -/
def rouqFamily :=
  spectralRouqFamily.{u, max u v, max u v, w} P₀ d hdpos hd hP hhom RD μ
    (zm k I (Slots s nb)) (zp k I (Slots s nb))
    (negLevel s nb M (fun i => RD.pair (RD.iY i) μ))
    (posLevel s nb M (fun i => RD.pair (RD.iY i) μ))
    (fun i => (sum_level_difference s nb M (fun i => RD.pair (RD.iY i) μ) i).symm) Q hPQ hext

end Categorification.KLR.Unfurling.GenericFields
