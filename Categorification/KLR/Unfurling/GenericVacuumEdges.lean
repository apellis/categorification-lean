/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuum
import Categorification.TwoRep.FurlingBlock

/-!
# Finite-slot products at the generic vacuum

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of `nondegenerate`, “Construction of representations” and “Triviality of a relation”.
The nonzero multiplicities of edges at the zero block are precisely the prescribed
finite-slot multiplicities. `vacuum_prod_out` and `vacuum_prod_in` reindex the two
products used by the categorical vacuum bubble formulas; `vacuum_sum_out` and
`vacuum_sum_in` reindex their degree shifts. Zero-level slots contribute the identity.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open CategoryTheory TwoRep TwoRep.Furling

/-- Reindex weighted products through injective labels, allowing zero multiplicities. -/
@[to_additive /-- Reindex weighted sums through injective labels, allowing zero multiplicities. -/]
theorem prod_pow_sum_ite_labels {E Q J A : Type*} [Fintype E] [Fintype Q]
    [DecidableEq J] [CommMonoid A] (lab : E → J) (hl : Function.Injective lab) (slot : Q → J)
    (m : Q → ℕ) (hc : ∀ q, m q ≠ 0 → ∃ e, lab e = slot q) (f : J → A) :
    (∏ e, f (lab e) ^ (∑ q, if lab e = slot q then m q else 0)) =
      ∏ q, f (slot q) ^ m q := by
  classical
  simp only [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro q _
  by_cases hq : m q = 0
  · simp [hq]
  obtain ⟨e, he⟩ := hc q hq
  rw [Finset.prod_eq_single e]
  · simp [he]
  · intro e' _ hne
    have : lab e' ≠ slot q := fun h => hne (hl (h.trans he.symm))
    simp [this]
  · simp

end Categorification.KLR.Unfurling

namespace Categorification.KLR.Unfurling.GenericFields
open CategoryTheory TwoRep TwoRep.Furling
universe u v w
variable (k : Type v) [Field k] {I : Type u} {C : QuantumGroup.CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (μ : X) (s b M : ℕ)

local notation "Q" => Slots s b
local notation "K₀" => K k (I × Q)
local notation "L₀" => L k (I × Q) (I × Q)
local notation "h" => fun i => RD.pair (RD.iY i) μ
local notation "Λm" => vacuumWeightNeg k s b M h
local notation "Λp" => vacuumWeightPos k s b M h

variable (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b))) (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, ((d i : ℕ) : (L k (I × Slots s b) (I × Slots s b))) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D,
    (MvPolynomial.map (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

local notation "D" => coverDatum P₀ d hdpos hd hP hhom

local notation "nm" => arrowsNeg D
local notation "np" => arrowsPos D
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hd hP hhom
local notation "V" => genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom
local notation "β₀" => genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom
local notation "hb" => coverBase_eq_vacuumBase Λm Λp

open Classical
local notation "J" => LabelNeg I K₀ L₀ ⊕ LabelPos I K₀ L₀
local notation "RDc" => coverProdWeight D

theorem vacuum_pair (a : J) :
    (RDc).pair ((RDc).iY a) ((Φ).wtT β₀.1) = coverBaseVal Λm Λp a := by
  change (RDc).pair ((RDc).iY a) ((Φ).wtT 0) = _
  simp only [Furling.wtT, Finsupp.sum_zero_index, add_zero]
  exact coverProdWeight_pair_base D Λm Λp a

theorem vacuum_negMultiplicity (i : I) (a : J) (ha : (D).π a = i) :
    (-(RDc).pair ((RDc).iY a) ((Φ).wtT β₀.1)).toNat =
      ∑ q, if a = .inl ⟨i, zm k I Q i q⟩ then negLevel s b M h i q else 0 := by
  rw [vacuum_pair]
  rcases a with a | a <;> change a.1 = i at ha <;> subst i
  · simp only [coverBaseVal, neg_neg, Int.toNat_natCast, vacuumWeightNeg, weightNeg,
      coverWeightNeg]
    apply Finset.sum_congr rfl
    intro q _
    have he : ((Sum.inl a : J) = .inl ⟨a.1, zm k I Q a.1 q⟩) ↔ a.2 = zm k I Q a.1 q := by
      constructor
      · intro hh
        exact congrArg (fun a : LabelNeg I K₀ L₀ => a.2) (Sum.inl_injective hh)
      · intro hh
        exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq hh))
    simp only [he]
  · simp [coverBaseVal]

theorem vacuum_posMultiplicity (i : I) (a : J) (ha : (D).π a = i) :
    ((RDc).pair ((RDc).iY a) ((Φ).wtT β₀.1)).toNat =
      ∑ q, if a = .inr ⟨i, zp k I Q i q⟩ then posLevel s b M h i q else 0 := by
  rw [vacuum_pair]
  rcases a with a | a <;> change a.1 = i at ha <;> subst i
  · simp [coverBaseVal]
  · simp only [coverBaseVal, Int.toNat_natCast, vacuumWeightPos, weightPos,
      coverWeightPos]
    apply Finset.sum_congr rfl
    intro q _
    have he : ((Sum.inr a : J) = .inr ⟨a.1, zp k I Q a.1 q⟩) ↔ a.2 = zp k I Q a.1 q := by
      constructor
      · intro hh
        exact congrArg (fun a : LabelPos I K₀ L₀ => a.2) (Sum.inr_injective hh)
      · intro hh
        exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq hh))
    simp only [he]

theorem vacuum_out_slot (i : I) (q : Q) (hq : negLevel s b M h i q ≠ 0) :
    ∃ e : OutEdge Φ i β₀, e.1.lbl = .inl ⟨i, zm k I Q i q⟩ := by
  have hr : (Φ).rel β₀.1 (.inl ⟨i, zm k I Q i q⟩) := by
    apply Or.inl
    simpa only [vacuumWeightNeg, weightNeg_mk] using hq
  exact ⟨⟨outEdge β₀ _ rfl hr, rfl⟩, rfl⟩

theorem vacuum_in_slot (i : I) {l₀ : X} (h₀ : l₀ + RD.iX i = μ)
    (q : Q) (hq : posLevel s b M h i q ≠ 0) :
    ∃ e : InEdge Φ i h₀ β₀, e.1.lbl = .inr ⟨i, zp k I Q i q⟩ := by
  classical
  have hr : (Φ).rel (β₀.1 - Finsupp.single (.inr ⟨i, zp k I Q i q⟩) 1)
      (.inr ⟨i, zp k I Q i q⟩) := by
    apply Or.inl
    simpa only [vacuumWeightPos, weightPos_mk] using hq
  exact ⟨⟨inEdge h₀ β₀ _ rfl hr, inEdge_tgt h₀ β₀ _ rfl hr⟩, rfl⟩

theorem vacuum_out_lbl_injective (i : I) :
    Function.Injective (fun e : OutEdge Φ i β₀ => e.1.lbl) := by
  intro e e' he
  exact Subtype.ext (Edge.ext (e.2.trans e'.2.symm) he)

theorem vacuum_in_lbl_injective (i : I) {l₀ : X} (h₀ : l₀ + RD.iX i = μ) :
    Function.Injective (fun e : InEdge Φ i h₀ β₀ => e.1.lbl) := by
  intro e e' he
  apply Subtype.ext
  apply Edge.ext _ he
  apply Subtype.ext
  rw [src_val_of_tgt h₀ e, src_val_of_tgt h₀ e']
  exact congrArg (fun a => β₀.1 - Finsupp.single a (1 : ℤ)) he

theorem vacuum_prod_out {A : Type*} [CommMonoid A] (i : I) (f : J → A) :
    (∏ e : OutEdge Φ i β₀,
      f e.1.lbl ^ (-(RDc).pair ((RDc).iY e.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      ∏ q, f (.inl ⟨i, zm k I Q i q⟩) ^ negLevel s b M h i q := by
  have hm := fun e : OutEdge Φ i β₀ =>
    vacuum_negMultiplicity k RD μ s b M P₀ d hdpos hd hP hhom i e.1.lbl e.1.π_lbl
  simp only [hm]
  exact prod_pow_sum_ite_labels _
    (vacuum_out_lbl_injective k RD μ s b M P₀ d hdpos hd hP hhom i) _ _
    (vacuum_out_slot k RD μ s b M P₀ d hdpos hd hP hhom i) f

theorem vacuum_prod_in {A : Type*} [CommMonoid A] (i : I) {l₀ : X}
    (h₀ : l₀ + RD.iX i = μ) (f : J → A) :
    (∏ e : InEdge Φ i h₀ β₀,
      f e.1.lbl ^ ((RDc).pair ((RDc).iY e.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      ∏ q, f (.inr ⟨i, zp k I Q i q⟩) ^ posLevel s b M h i q := by
  have hm := fun e : InEdge Φ i h₀ β₀ =>
    vacuum_posMultiplicity k RD μ s b M P₀ d hdpos hd hP hhom i e.1.lbl e.1.π_lbl
  simp only [hm]
  exact prod_pow_sum_ite_labels _
    (vacuum_in_lbl_injective k RD μ s b M P₀ d hdpos hd hP hhom i h₀) _ _
    (vacuum_in_slot k RD μ s b M P₀ d hdpos hd hP hhom i h₀) f

theorem vacuum_sum_out (i : I) :
    (∑ e : OutEdge Φ i β₀,
      (-(RDc).pair ((RDc).iY e.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      ∑ q, negLevel s b M h i q := by
  have hm := fun e : OutEdge Φ i β₀ =>
    vacuum_negMultiplicity k RD μ s b M P₀ d hdpos hd hP hhom i e.1.lbl e.1.π_lbl
  simp only [hm]
  simpa only [smul_eq_mul, mul_one] using sum_nsmul_sum_ite_labels _
    (vacuum_out_lbl_injective k RD μ s b M P₀ d hdpos hd hP hhom i) _ _
    (vacuum_out_slot k RD μ s b M P₀ d hdpos hd hP hhom i) (fun _ => (1 : ℕ))

theorem vacuum_sum_in (i : I) {l₀ : X} (h₀ : l₀ + RD.iX i = μ) :
    (∑ e : InEdge Φ i h₀ β₀,
      ((RDc).pair ((RDc).iY e.1.lbl) ((Φ).wtT β₀.1)).toNat) =
      ∑ q, posLevel s b M h i q := by
  have hm := fun e : InEdge Φ i h₀ β₀ =>
    vacuum_posMultiplicity k RD μ s b M P₀ d hdpos hd hP hhom i e.1.lbl e.1.π_lbl
  simp only [hm]
  simpa only [smul_eq_mul, mul_one] using sum_nsmul_sum_ite_labels _
    (vacuum_in_lbl_injective k RD μ s b M P₀ d hdpos hd hP hhom i h₀) _ _
    (vacuum_in_slot k RD μ s b M P₀ d hdpos hd hP hhom i h₀) (fun _ => (1 : ℕ))

end Categorification.KLR.Unfurling.GenericFields
