/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverLabels

/-!
# Cover weights with finite support in each colour

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations.
For a fixed original colour, only finitely many spectral labels carry weight.
This suffices for local finiteness of the relevant edges; global finiteness of
the weight support is not required. `coverFurlingOfFibreFinite` constructs that
furling datum and `coverWeight_fibre_finite` verifies its hypothesis for the
finite-slot weights, for an arbitrary original colour type.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open Categorification.TwoRep
universe u v u₁ u₃
variable {I : Type u₃} {Jm Jp : Type u} [DecidableEq Jm] [DecidableEq Jp]
  {L : Type v} [Field L] {P : I → I → MvPolynomial (Fin 2) L}
  (D : UnfurlingDatum L P (Jm ⊕ Jp)) (Λm : Jm → ℕ) (Λp : Jp → ℕ)

omit [DecidableEq Jm] [DecidableEq Jp] in
/-- Finite weight support in each colour suffices for the edges of the furling datum. -/
theorem coverRel_fibre_finite
    (hΛ : ∀ i, {a | D.π a = i ∧ coverBaseVal Λm Λp a ≠ 0}.Finite)
    (β : Jm ⊕ Jp →₀ ℤ) (i : I) :
    {a | D.π a = i ∧ (coverBaseVal Λm Λp a ≠ 0 ∨ a ∈ β.support ∨ CoverAdj D β a)}.Finite := by
  have hf := ((hΛ i).union β.support.finite_toSet).union
    (β.support.finite_toSet.biUnion fun c _ => D.finite_adjacent c i)
  refine hf.subset fun a ⟨ha, h⟩ => ?_
  rcases h with h | h | ⟨c, hc, -, hac⟩
  · exact Or.inl (Or.inl ⟨ha, h⟩)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Set.mem_biUnion hc ⟨ha, hac⟩)

variable {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (μ : X)

/-- The cover furling needs finite support only within each colour, not globally. -/
def coverFurlingOfFibreFinite
    (hΛ : ∀ i, {a | D.π a = i ∧ coverBaseVal Λm Λp a ≠ 0}.Finite) :
    Furling (coverProdWeight D) RD where
  π := D.π
  base := coverBase Λm Λp
  baseG := μ
  rel := coverRel D Λm Λp
  finite_out β i := (coverRel_fibre_finite D Λm Λp hΛ β i).subset fun a ⟨ha, h⟩ =>
    ⟨ha, coverRel_imp β a h⟩
  finite_in β i := (coverRel_fibre_finite D Λm Λp hΛ β i).subset fun a ⟨ha, h⟩ =>
    ⟨ha, coverRel_sub_imp β a h⟩

/-- With globally finite weights this is exactly the original cover furling. -/
theorem coverFurling_eq_ofFibreFinite
    (hΛm : (Function.support Λm).Finite) (hΛp : (Function.support Λp).Finite)
    (hΛ : ∀ i, {a | D.π a = i ∧ coverBaseVal Λm Λp a ≠ 0}.Finite) :
    coverFurling D Λm Λp RD μ hΛm hΛp =
      coverFurlingOfFibreFinite D Λm Λp RD μ hΛ := rfl

section Weights
variable {K : Type*} [Field K] [Algebra K L] {Q : Type*} [Fintype Q]
  (zm : I → Q → {u : L // u ≠ 0 ∧ u ∈ Set.range (algebraMap K L)})
  (zp : I → Q → {u : L // u ≠ 0 ∧ u ∉ Set.range (algebraMap K L)})
  (nm np : I → Q → ℕ)

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverWeightNeg_fibre_finite (i : I) :
    {a : LabelNeg I K L | a.1 = i ∧ coverWeightNeg zm nm a ≠ 0}.Finite := by
  classical
  have hn : (Function.support (fun j q => if j = i then nm j q else 0)).Finite :=
    (Set.finite_singleton i).subset fun j hj => by
      by_contra hji
      simp only [Set.mem_singleton_iff] at hji
      exact hj (by funext q; simp [hji])
  refine (coverWeightNeg_finite zm (fun j q => if j = i then nm j q else 0) hn).subset ?_
  rintro ⟨j, u⟩ ⟨rfl, ha⟩
  change coverWeightNeg zm (fun j' q => if j' = j then nm j' q else 0) ⟨j, u⟩ ≠ 0
  simpa only [coverWeightNeg, ite_true] using ha

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverWeightPos_fibre_finite (i : I) :
    {a : LabelPos I K L | a.1 = i ∧ coverWeightPos zp np a ≠ 0}.Finite := by
  classical
  have hn : (Function.support (fun j q => if j = i then np j q else 0)).Finite :=
    (Set.finite_singleton i).subset fun j hj => by
      by_contra hji
      simp only [Set.mem_singleton_iff] at hji
      exact hj (by funext q; simp [hji])
  refine (coverWeightPos_finite zp (fun j q => if j = i then np j q else 0) hn).subset ?_
  rintro ⟨j, u⟩ ⟨rfl, ha⟩
  change coverWeightPos zp (fun j' q => if j' = j then np j' q else 0) ⟨j, u⟩ ≠ 0
  simpa only [coverWeightPos, ite_true] using ha
variable (P₀ : I → I → MvPolynomial (Fin 2) K) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : L) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap K L) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D,
    (MvPolynomial.map (algebraMap K L) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverWeight_fibre_finite (i : I) :
    {a | (coverDatum P₀ d hdpos hd hP hhom).π a = i ∧
      coverBaseVal (coverWeightNeg zm nm) (coverWeightPos zp np) a ≠ 0}.Finite := by
  have hm := (coverWeightNeg_fibre_finite zm nm i).image (Sum.inl (β := LabelPos I K L))
  have hp := (coverWeightPos_fibre_finite zp np i).image (Sum.inr (α := LabelNeg I K L))
  refine (hm.union hp).subset ?_
  rintro (a | a) ⟨ha, hn⟩
  · left
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    simpa only [coverBaseVal, neg_ne_zero, Nat.cast_ne_zero] using hn
  · right
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    simpa only [coverBaseVal, Nat.cast_ne_zero] using hn

end Weights
end Categorification.KLR.Unfurling
