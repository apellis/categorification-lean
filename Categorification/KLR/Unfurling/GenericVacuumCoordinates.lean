/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericVacuum
import Categorification.KLR.Unfurling.GenericStrands
import Categorification.KLR.Unfurling.VacuumCorner
import Categorification.TwoRep.FurlingIntertwine

/-!
# Normalized coordinates of the generic vacuum

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations and
triviality of a relation. The negative vacuum functor is evaluated on the positive
regular module. Its rank-zero coordinate passes through the two scalar equivalences;
the positive regular module is not replaced by the negative regular module.
-/

noncomputable section
open CategoryTheory Categorification.TwoRep Categorification.KLR.CyclotomicAction

namespace Categorification.KLR.Unfurling
universe u v
variable {J Jp : Type u} [DecidableEq J] [DecidableEq Jp] {L : Type v} [Field L]
  (n : J → J → ℕ) (Λ : J → ℕ) (np : Jp → Jp → ℕ) (Λp : Jp → ℕ)

/-- The negative vacuum functor applied to the positive regular module. -/
def vacuumModule : weightSpace (unfQ (k := L) n) (fun j => Polynomial.X ^ Λ j)
    (coverWeight n) ((fun j => (Λ j : ℤ)), 0) (-((fun j => (Λ j : ℤ)), 0)) :=
  (vacuumFunctor n Λ np Λp).obj (vacuumRegular np Λp)

/-- The generator is one in the positive rank-zero ring. -/
def vacuumModuleGen : vacuumModule n (L := L) Λ np Λp (vacuumBlock n Λ) :=
  (1 : vacuumRing (L := L) np Λp (vacuumBlock np Λp))

/-- The coordinate from the positive ring to the negative ring, through scalars. -/
def vacuumModuleCoord :
    vacuumModule n (L := L) Λ np Λp (vacuumBlock n Λ) →ₗ[vacuumRing (L := L) n Λ (vacuumBlock n Λ)]
      vacuumRing (L := L) n Λ (vacuumBlock n Λ) where
  toFun x := (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
    (vacuumRingEquiv np Λp (vacuumBlock np Λp) x)
  map_add' x y := by
    change vacuumRing (L := L) np Λp (vacuumBlock np Λp) at x y
    change (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
      (vacuumRingEquiv np Λp (vacuumBlock np Λp) (x + y)) =
        (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
          (vacuumRingEquiv np Λp (vacuumBlock np Λp) x) +
        (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
          (vacuumRingEquiv np Λp (vacuumBlock np Λp) y)
    simp only [map_add]
  map_smul' r x := by
    change vacuumRing (L := L) np Λp (vacuumBlock np Λp) at x
    change (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
      (vacuumRingEquiv np Λp (vacuumBlock np Λp)
        (algebraMap L _ (vacuumRingEquiv n Λ (vacuumBlock n Λ) r) * x)) = _
    simp only [map_mul, AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      AlgEquiv.symm_apply_apply]
    rfl

@[simp] theorem vacuumModuleCoord_gen :
    vacuumModuleCoord n (L := L) Λ np Λp (vacuumModuleGen n Λ np Λp) = 1 := by
  change (vacuumRingEquiv n Λ (vacuumBlock n Λ)).symm
    (vacuumRingEquiv np Λp (vacuumBlock np Λp) 1) = 1
  simp only [map_one]

/-- Literal evaluation equality used by the vacuum word-coordinate API. -/
theorem vacuum_obj_regular :
    (vacuum n (L := L) Λ np Λp).obj.obj (vacuumRegular np Λp) =
      familyObj (unfQ_klrSymm n) (cover_hlead n) (cover_hmonic Λ)
        (cover_hΛ n Λ) (cover_hdeg n) (vacuumModule n Λ np Λp) := rfl

/-- Transport of the rank-zero functor is the specified vacuum, not merely isomorphic. -/
theorem vacuumAt_transport {x} (hx : x = vacuumBase Λ Λp) :
    hx ▸ vacuumAt n (L := L) Λ np Λp hx = vacuum n Λ np Λp := by
  subst x
  rfl

end Categorification.KLR.Unfurling

namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot TwoRep.RouqFamily
universe u v w
variable (k : Type v) [Field k] {I : Type u}

/-- A chosen generic label in the negative component. -/
def negativeStrandLabel (s b : ℕ) (c : I) (q : Fin s) :
    LabelNeg I (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)) :=
  ⟨c, zm k I (Slots s b) c (.inl q)⟩

section Strands
variable {s : ℕ} (b : ℕ) {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s)

/-- The negative labels of the distinct generic strand lift, before inclusion in the cover. -/
def negativeStrandWeight : Multiset
    (LabelNeg I (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) :=
  Finset.univ.val.map (fun q : Fin ν.card =>
    negativeStrandLabel k s b (i.lbl q) (Fin.castLE hs q))

@[simp] theorem negativeStrandWeight_map_inl :
    (negativeStrandWeight k b i hs).map Sum.inl = strandWeight k b i hs := by
  rw [negativeStrandWeight, Multiset.map_map]
  rfl

@[simp] theorem card_negativeStrandWeight :
    (negativeStrandWeight k b i hs).card = ν.card := by
  simp [negativeStrandWeight]

/-- The negative sequence whose inclusion is the generic full-cover strand sequence. -/
def negativeStrandSeq : Seq (negativeStrandWeight k b i hs) :=
  ⟨fun q => negativeStrandLabel k s b (i.lbl (Fin.cast (card_negativeStrandWeight k b i hs) q))
    (Fin.castLE hs (Fin.cast (card_negativeStrandWeight k b i hs) q)), by
    change Finset.univ.val.map ((fun q : Fin ν.card =>
      negativeStrandLabel k s b (i.lbl q) (Fin.castLE hs q)) ∘
        finCongr (card_negativeStrandWeight k b i hs)) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    rfl⟩

theorem negativeStrandSeq_map_inl :
    Seq.cast (negativeStrandWeight_map_inl k b i hs)
      (Seq.map Sum.inl (negativeStrandSeq k b i hs)) = strandSeq k b i hs := by
  apply Subtype.ext
  funext q
  rfl

/-- The concrete negative multiplicity is `M` on the chosen support. -/
theorem negativeStrandWeight_level (M : ℕ) (h : I → ℤ) :
    ∀ a ∈ negativeStrandWeight k b i hs, vacuumWeightNeg k s b M h a = M := by
  intro a ha
  obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp ha
  exact vacuumWeightNeg_strand k s b M h _ _

end Strands

variable {C : CartanDatum I} {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X) (s b M : ℕ)
  (P₀ : I → I → MvPolynomial (Fin 2) (K k (I × Slots s b)))
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
  (hd : ∀ i, (d i : L k (I × Slots s b) (I × Slots s b)) ≠ 0)
  (hP : ∀ i j, i ≠ j → MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b))) (P₀ i j) ≠ 0)
  (hhom : ∀ i j, i ≠ j → ∃ D, (MvPolynomial.map
    (algebraMap (K k (I × Slots s b)) (L k (I × Slots s b) (I × Slots s b)))
      (P₀ i j)).IsWeightedHomogeneous ![d j, d i] D)

local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "D" => coverDatum P₀ d hdpos hd hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "nm" => arrowsNeg D
local notation "np" => arrowsPos D
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hd hP hhom
local notation "β₀" => genericZeroBlock k RD μ s b M P₀ d hdpos hd hP hhom

/-- The product weight of the generic zero block. -/
theorem genericZeroBlock_wtT : (Φ).wtT (β₀).1 = vacuumBase Λm Λp :=
  vacuum_wtT_zero nm Λm np Λp Φ (coverBase_eq_vacuumBase Λm Λp)

/-- The generic zero-block object transports to the rank-zero vacuum functor. -/
theorem genericVacuum_transport :
    Eq.ndrec (motive := fun x => (coverProduct nm (L := L₀) Λm np Λp).obj x)
      (genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom β₀)
      (genericZeroBlock_wtT k RD μ s b M P₀ d hdpos hd hP hhom) =
        vacuum nm (L := L₀) Λm np Λp := by
  let hx := genericZeroBlock_wtT k RD μ s b M P₀ d hdpos hd hP hhom
  have heq : genericVacuum k RD μ s b M P₀ d hdpos hd hP hhom β₀ =
      vacuumAt nm (L := L₀) Λm np Λp hx :=
    furledVacuum_zero nm Λm np Λp Φ (coverBase_eq_vacuumBase Λm Λp)
  exact (congrArg (fun V => Eq.ndrec
    (motive := fun x => (coverProduct nm (L := L₀) Λm np Λp).obj x) V hx) heq).trans
      (vacuumAt_transport nm (L := L₀) Λm np Λp hx)

/-- The actual negative module obtained by evaluating the generic vacuum on the
positive regular module. -/
abbrev genericVacuumModule := vacuumModule nm (L := L₀) Λm np Λp

/-- The normalized generator of the evaluated generic vacuum. -/
abbrev genericVacuumModuleGen := vacuumModuleGen nm (L := L₀) Λm np Λp

/-- The normalized rank-zero coordinate of the evaluated generic vacuum. -/
abbrev genericVacuumModuleCoord := vacuumModuleCoord nm (L := L₀) Λm np Λp

@[simp] theorem genericVacuumModuleCoord_gen :
    genericVacuumModuleCoord k RD μ s b M P₀ d hdpos hd hP hhom
      (genericVacuumModuleGen k RD μ s b M P₀ d hdpos hd hP hhom) = 1 :=
  vacuumModuleCoord_gen nm Λm np Λp

/-- The target block of a negative word based at the generic vacuum. -/
def genericVacuumTargetBlock
    (νm : Multiset (LabelNeg I (K k (I × Slots s b)) L₀)) :
    (Φ).Blk (wtop RD μ ((νm.map Sum.inl).map (D).π)) :=
  ⟨(β₀).1 + Furling.blkSum (νm.map Sum.inl), by
    rw [Furling.wtG_add_blkSum, (β₀).2]
    rfl⟩

/-- The block displacement required by the furled evaluation. -/
theorem genericVacuumTargetBlock_val
    (νm : Multiset (LabelNeg I (K k (I × Slots s b)) L₀)) :
    (β₀).1 + Furling.blkSum (νm.map Sum.inl) =
      (genericVacuumTargetBlock k RD μ s b M P₀ d hdpos hd hP hhom νm).1 := rfl

/-- The negative word changes only the negative component of the product weight. -/
theorem genericVacuumTargetBlock_wtT
    (νm : Multiset (LabelNeg I (K k (I × Slots s b)) L₀)) :
    (Φ).wtT (genericVacuumTargetBlock k RD μ s b M P₀ d hdpos hd hP hhom νm).1 =
      (wtop (coverWeight nm) (-((fun j => (Λm j : ℤ)), 0)) νm,
        ((fun j => (Λp j : ℤ)), 0)) := by
  rw [genericVacuumTargetBlock, Furling.wtT_add_blkSum,
    genericZeroBlock_wtT]
  exact wtop_map_inl _ _ _

/-- Projection of the negative generic strand multiset to the original weight. -/
theorem negativeStrandWeight_map {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s) :
    ((negativeStrandWeight k b i hs).map Sum.inl).map (D).π = ν := by
  rw [negativeStrandWeight_map_inl]
  exact strandWeight_map k b i hs P₀ d hdpos hd hP hhom

/-- Projection of the selected negative sequence is the original sequence. -/
theorem down_negativeStrandSeq {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s) :
    down (D).π (negativeStrandWeight_map k s b P₀ d hdpos hd hP hhom i hs)
      (Seq.map Sum.inl (negativeStrandSeq k b i hs)) = i := by
  apply Subtype.ext
  funext q
  rfl

/-- The chosen generic strands end over the original target weight `wtop RD μ ν`. -/
def genericStrandTargetBlock {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s) :
    (Φ).Blk (wtop RD μ ν) :=
  ⟨(β₀).1 + Furling.blkSum ((negativeStrandWeight k b i hs).map Sum.inl), by
    rw [Furling.wtG_add_blkSum, (β₀).2]
    change wtop RD μ (((negativeStrandWeight k b i hs).map Sum.inl).map (D).π) = _
    rw [negativeStrandWeight_map]⟩

/-- Concrete source/target block displacement for the distinct strand lift. -/
theorem genericStrandTargetBlock_val {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s) :
    (β₀).1 + Furling.blkSum ((negativeStrandWeight k b i hs).map Sum.inl) =
      (genericStrandTargetBlock k RD μ s b M P₀ d hdpos hd hP hhom i hs).1 := rfl

/-- Concrete product target weight for the distinct strand lift. -/
theorem genericStrandTargetBlock_wtT {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s) :
    (Φ).wtT (genericStrandTargetBlock k RD μ s b M P₀ d hdpos hd hP hhom i hs).1 =
      (wtop (coverWeight nm) (-((fun j => (Λm j : ℤ)), 0))
        (negativeStrandWeight k b i hs), ((fun j => (Λp j : ℤ)), 0)) :=
  genericVacuumTargetBlock_wtT k RD μ s b M P₀ d hdpos hd hP hhom _

end Categorification.KLR.Unfurling.GenericFields
