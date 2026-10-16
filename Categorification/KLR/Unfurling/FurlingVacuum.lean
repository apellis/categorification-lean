/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverVacuum
import Categorification.TwoRep.PiBiproduct
import Categorification.KLR.Unfurling.CoverFurling
import Categorification.KLR.Unfurling.VacuumFurlingNilpotent

/-!
# The vacuum concentrated in the zero furling block

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations.

`furledVacuum` is the rank-zero vacuum at the zero block, and zero elsewhere.
Its evaluation is an injective algebra map to the coefficient field, both on
the full endomorphism algebra (`furledVacuumEv`) and on the zero-block component
(`furledVacuumBlockEv`). Both algebras are reduced. The hypotheses `hout`, `hin`
and `hY` of the two vacuum bubble formulas are supplied by `furledVacuum_out`,
`furledVacuum_in`, `furledVacuum_posIn` and `furledVacuum_negOut`.

The furling datum is an explicit input, with base `(-Λm, Λp)`; the construction
does not assume a vacuum or any of its properties. For `coverFurling`, the base
identity is `coverBase_eq_vacuumBase`. No global finiteness assumption on the
colour set or on the support of the weights is used here.
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open Categorification.TwoRep
noncomputable section
namespace Categorification.KLR.Unfurling
universe u v w u₁ u₂
section Biproducts
variable {J : Type u} [DecidableEq J] {L : Type v} [Field L]
variable (n : J → J → ℕ) (Λ : J → ℕ)
instance coverFamily_hasFiniteBiproducts (x) : HasFiniteBiproducts ((coverFamily.{u,v,w} n (L := L) Λ).obj x) := by
  change HasFiniteBiproducts (∀ β : Categorification.KLR.CyclotomicAction.WeightBlocks
    (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x,
    ModuleCat (Categorification.KLR.CycKLR L (unfQ n) (fun j => Polynomial.X ^ Λ j) β.1))
  infer_instance
variable {Jp : Type u} [DecidableEq Jp] (np : Jp → Jp → ℕ) (Λp : Jp → ℕ)
instance coverProduct_hasFiniteBiproducts (x) : HasFiniteBiproducts ((coverProduct.{u,v,w} n (L := L) Λ np Λp).obj x) := by
  change HasFiniteBiproducts
    ((coverFamily.{u,v,w} np (L := L) Λp).obj (-x.2) ⟶ (coverFamily.{u,v,w} n (L := L) Λ).obj x.1)
  infer_instance
end Biproducts
variable {Jm Jp : Type u} [DecidableEq Jm] [DecidableEq Jp] {L : Type v} [Field L]
variable (nm : Jm → Jm → ℕ) (Λm : Jm → ℕ) (np : Jp → Jp → ℕ) (Λp : Jp → ℕ)
abbrev vacuumBase : ((Jm → ℤ) × (Jm →₀ ℤ)) × ((Jp → ℤ) × (Jp →₀ ℤ)) :=
  (-((fun j => (Λm j : ℤ)), 0), ((fun j => (Λp j : ℤ)), 0))

omit [DecidableEq Jm] [DecidableEq Jp] in
theorem coverBase_eq_vacuumBase : coverBase Λm Λp = vacuumBase Λm Λp := by
  ext <;> simp [coverBase]

def vacuumAt {x} (hx : x = vacuumBase Λm Λp) :
    (coverProduct.{u,v,0} nm (L := L) Λm np Λp).obj x := by
  subst hx
  exact vacuum nm Λm np Λp

def vacuumAtEv {x} (hx : x = vacuumBase Λm Λp) :
    End (vacuumAt nm (L := L) Λm np Λp hx) →ₐ[L] L := by
  subst hx
  exact vacuumEv nm Λm np Λp

theorem vacuumAtEv_injective {x} (hx : x = vacuumBase Λm Λp) :
    Function.Injective (vacuumAtEv nm (L := L) Λm np Λp hx) := by
  subst hx
  exact vacuumEv_injective nm Λm np Λp

variable {I : Type*} {C : QuantumGroup.CartanDatum I}
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (Φ : Furling ((coverWeight nm).prod (coverWeight np)) RD)
  (hbase : Φ.base = vacuumBase Λm Λp)

/-- The zero block has the base weight of the furled representation. -/
def vacuumZeroBlock : Φ.Blk Φ.baseG := ⟨0, by simp [Furling.wtG]⟩

def furledVacuum : Φ.obj (coverProduct.{u,v,0} nm (L := L) Λm np Λp) Φ.baseG :=
  fun β => if hβ : β.1 = 0 then
    vacuumAt nm Λm np Λp (by simp [Furling.wtT, hβ, hbase]) else 0

theorem furledVacuum_isZero (β : Φ.Blk Φ.baseG) (hβ : β ≠ vacuumZeroBlock nm np Φ) :
    IsZero (furledVacuum nm (L := L) Λm np Λp Φ hbase β) := by
  have hn : β.1 ≠ 0 := fun h => hβ (Subtype.ext h)
  simp only [furledVacuum, dite_eq_right hn]
  exact isZero_zero _

def vacuumEndTransport {D : Type*} [Category D] [Preadditive D] [Linear L D]
    {V W : D} (h : V = W) : End V →ₐ[L] End W := by
  subst h
  exact AlgHom.id L _

theorem vacuumEndTransport_injective {D : Type*} [Category D] [Preadditive D] [Linear L D]
    {V W : D} (h : V = W) : Function.Injective (vacuumEndTransport (L := L) h) := by
  subst h
  exact Function.injective_id

theorem furledVacuum_zero :
    furledVacuum nm (L := L) Λm np Λp Φ hbase (vacuumZeroBlock nm np Φ) =
    vacuumAt nm Λm np Λp (x := Φ.wtT 0) (by simp [Furling.wtT, hbase]) := by
  simp [furledVacuum, vacuumZeroBlock]

def furledVacuumBlockEv :
    End (furledVacuum nm (L := L) Λm np Λp Φ hbase (vacuumZeroBlock nm np Φ)) →ₐ[L] L :=
  (vacuumAtEv nm Λm np Λp (x := Φ.wtT 0) (by simp [Furling.wtT, hbase])).comp
    (vacuumEndTransport (furledVacuum_zero nm Λm np Λp Φ hbase))

theorem furledVacuumBlockEv_injective :
    Function.Injective (furledVacuumBlockEv nm (L := L) Λm np Λp Φ hbase) :=
  (vacuumAtEv_injective nm Λm np Λp _).comp
    (vacuumEndTransport_injective (L := L) (furledVacuum_zero nm Λm np Λp Φ hbase))

instance furledVacuumBlock_isReduced :
    IsReduced (End (furledVacuum nm (L := L) Λm np Λp Φ hbase (vacuumZeroBlock nm np Φ))) :=
  isReduced_of_injective (furledVacuumBlockEv nm Λm np Λp Φ hbase)
    (furledVacuumBlockEv_injective nm Λm np Λp Φ hbase)

theorem vacuum_isZero_obj {A B : LinearCat.{v, u₁, u₂} L} (F : A ⟶ B)
    (hF : IsZero F) (V : A) : IsZero (F.obj.obj V) := by
  rw [IsZero.iff_id_eq_zero] at hF ⊢
  exact congrArg (fun η : F ⟶ F => η.hom.app V) hF

local notation "RDc" => QuantumGroup.UDot.WeightDatum.prod (coverWeight nm) (coverWeight np)
local notation "β₀" => vacuumZeroBlock nm np Φ
local notation "M" => furledVacuum nm (L := L) Λm np Λp Φ hbase

def furledVacuumEndProjection : End M →ₐ[L] End (M β₀) where
  toFun η := η β₀
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def furledVacuumEv : End M →ₐ[L] L :=
  (furledVacuumBlockEv nm Λm np Λp Φ hbase).comp
    (furledVacuumEndProjection nm Λm np Λp Φ hbase)

theorem furledVacuumEv_injective :
    Function.Injective (furledVacuumEv nm (L := L) Λm np Λp Φ hbase) := by
  intro η θ he
  change furledVacuumBlockEv nm Λm np Λp Φ hbase (η β₀) =
    furledVacuumBlockEv nm Λm np Λp Φ hbase (θ β₀) at he
  have h₀ : η β₀ = θ β₀ := furledVacuumBlockEv_injective nm (L := L) Λm np Λp Φ hbase he
  funext β
  by_cases hb : β = β₀
  · subst β
    exact h₀
  · exact (furledVacuum_isZero nm Λm np Λp Φ hbase β hb).eq_of_src _ _

instance furledVacuum_isReduced : IsReduced (End M) :=
  isReduced_of_injective (furledVacuumEv nm Λm np Λp Φ hbase)
    (furledVacuumEv_injective nm Λm np Λp Φ hbase)

include hbase

theorem vacuum_wtT_zero : Φ.wtT β₀.1 = vacuumBase Λm Λp := by
  simp [vacuumZeroBlock, Furling.wtT, hbase]

theorem vacuum_pair_inl (a : Jm) :
    (RDc).pair ((RDc).iY (.inl a)) (Φ.wtT β₀.1) = -(Λm a : ℤ) := by
  rw [vacuum_wtT_zero nm Λm np Λp Φ hbase]
  simp [vacuumBase, coverWeight]

theorem vacuum_pair_inr (a : Jp) :
    (RDc).pair ((RDc).iY (.inr a)) (Φ.wtT β₀.1) = (Λp a : ℤ) := by
  rw [vacuum_wtT_zero nm Λm np Λp Φ hbase]
  simp [vacuumBase, coverWeight]

open TwoRep.Furling

variable (i : I) {l' : X} (h : Φ.baseG + RD.iX i = l')

theorem furledVacuum_out (p : OutEdge Φ i β₀) :
    ((RDc).pair ((RDc).iY p.1.lbl) (Φ.wtT β₀.1) ≤ 0 ∧
      IsZero (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).E p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX p.1.lbl))).obj.obj
        (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).F p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX p.1.lbl))).obj.obj (M β₀)))) ∨
    IsZero ((Φ.Ea (coverProduct.{u,v,0} nm (L := L) Λm np Λp) h p.1 (p.1.tgt h) rfl).obj (M p.1.src)) := by
  have hw := vacuum_wtT_zero nm Λm np Λp Φ hbase
  rcases he : p.1.lbl with a | a
  · left
    constructor
    · rw [vacuum_pair_inl nm Λm np Λp Φ hbase]
      omega
    · have hz := (coverProduct_vacuum_inl.{u,v,0} nm (L := L) Λm np Λp a
        (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX (.inl a))) (congrArg Prod.fst hw)).2
      exact Functor.map_isZero _ (vacuum_isZero_obj _ hz (M β₀))
  · right
    have hx : (Φ.wtT p.1.src.1).2 = ((fun j => (Λp j : ℤ)), 0) := by
      rw [p.2]
      exact congrArg Prod.snd hw
    have hz := (coverProduct_vacuum_inr.{u,v,0} nm (L := L) Λm np Λp a
      (show Φ.wtT p.1.src.1 + (RDc).iX (.inr a) = Φ.wtT (p.1.tgt h).1 from
        he ▸ Φ.wt_tgt h p.1 rfl) hx).1
    apply vacuum_isZero_obj ((coverProduct.{u,v,0} nm (L := L) Λm np Λp).E p.1.lbl (Φ.wt_tgt h p.1 rfl))
    simpa only [he] using hz

variable {l₀ : X} (h₀ : l₀ + RD.iX i = Φ.baseG)

theorem furledVacuum_posIn (p : PosInEdge Φ i h₀ β₀) :
    IsZero (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).F p.1.1.lbl (rfl : Φ.wtT β₀.1 + (RDc).iX p.1.1.lbl = _)).obj.obj
      (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).E p.1.1.lbl (rfl : Φ.wtT β₀.1 + (RDc).iX p.1.1.lbl = _)).obj.obj (M β₀))) := by
  have hw := vacuum_wtT_zero nm Λm np Λp Φ hbase
  rcases he : p.1.1.lbl with a | a
  · have hp := p.2
    rw [he, vacuum_pair_inl nm Λm np Λp Φ hbase] at hp
    omega
  · have hz := (coverProduct_vacuum_inr.{u,v,0} nm (L := L) Λm np Λp a
      (rfl : Φ.wtT β₀.1 + (RDc).iX (.inr a) = _) (congrArg Prod.snd hw)).1
    exact Functor.map_isZero _ (vacuum_isZero_obj _ hz (M β₀))

theorem furledVacuum_in (p : InEdge Φ i h₀ β₀) :
    (0 ≤ (RDc).pair ((RDc).iY p.1.lbl) (Φ.wtT β₀.1) ∧
      IsZero (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).F p.1.lbl (rfl : Φ.wtT β₀.1 + (RDc).iX p.1.lbl = _)).obj.obj
        (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).E p.1.lbl (rfl : Φ.wtT β₀.1 + (RDc).iX p.1.lbl = _)).obj.obj (M β₀)))) ∨
    IsZero ((Φ.Fa (coverProduct.{u,v,0} nm (L := L) Λm np Λp) h₀ p.1 β₀ p.2).obj (M β₀)) := by
  have hw := vacuum_wtT_zero nm Λm np Λp Φ hbase
  rcases he : p.1.lbl with a | a
  · right
    have hz := (coverProduct_vacuum_inl.{u,v,0} nm (L := L) Λm np Λp a
      (show Φ.wtT p.1.src.1 + (RDc).iX (.inl a) = Φ.wtT β₀.1 from
        he ▸ Φ.wt_tgt h₀ p.1 p.2) (congrArg Prod.fst hw)).2
    apply vacuum_isZero_obj ((coverProduct.{u,v,0} nm (L := L) Λm np Λp).F p.1.lbl (Φ.wt_tgt h₀ p.1 p.2))
    simpa only [he] using hz
  · left
    constructor
    · rw [vacuum_pair_inr nm Λm np Λp Φ hbase]
      omega
    · have hz := (coverProduct_vacuum_inr.{u,v,0} nm (L := L) Λm np Λp a
        (rfl : Φ.wtT β₀.1 + (RDc).iX (.inr a) = _) (congrArg Prod.snd hw)).1
      exact Functor.map_isZero _ (vacuum_isZero_obj _ hz (M β₀))

theorem furledVacuum_negOut (p : NegOutEdge Φ i β₀) :
    IsZero (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).E p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX p.1.1.lbl))).obj.obj
      (((coverProduct.{u,v,0} nm (L := L) Λm np Λp).F p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX p.1.1.lbl))).obj.obj (M β₀))) := by
  have hw := vacuum_wtT_zero nm Λm np Λp Φ hbase
  rcases he : p.1.1.lbl with a | a
  · have hz := (coverProduct_vacuum_inl.{u,v,0} nm (L := L) Λm np Λp a
      (sub_add_cancel (Φ.wtT β₀.1) ((RDc).iX (.inl a))) (congrArg Prod.fst hw)).2
    exact Functor.map_isZero _ (vacuum_isZero_obj _ hz (M β₀))
  · have hp := p.2
    rw [he, vacuum_pair_inr nm Λm np Λp Φ hbase] at hp
    omega

end Categorification.KLR.Unfurling
