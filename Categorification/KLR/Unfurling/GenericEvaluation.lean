/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GenericKLFamily
import Categorification.KLR.Unfurling.GenericStrands
import Categorification.KLR.Unfurling.VacuumEvaluation
import Categorification.KLR.Unfurling.GenericBubbleValues
import Categorification.KLR.Unfurling.GenericVacuumCoordinates

/-!
# Concrete generic evaluation interfaces

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, “Triviality of a relation”.

The generic KL action has the concrete block data used by the vacuum, and its
crossing factors descend to the ground field. Equality transports identify the
projected strand sequence with the original sequence. The positive diagonal
lengths provide the power-series symmetrizer in characteristic zero.

`evaluationFromScalar` constructs the evaluation from the categorical scalar
bubble identity. The normalized coordinates, source/target identifications,
strand support and upward/mixed action relations are all supplied. It does not
assume an evaluation or basis-image formula; the scalar identity remains the
explicit interface to the bubble computation.
-/

noncomputable section
namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory
universe u v w
variable {I : Type u} [DecidableEq I] {C : CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type v} [Field k]

/-- Reindex an evaluation along equality of its original colour weight. -/
def UnfurledEval.reindex {μ : X} {ν ν' : Multiset I} (hν : ν' = ν)
    {t : Seq ν'} {i j : Seq ν} (ht : hν ▸ t = i) {N : ℕ}
    (E : UnfurledEval RD k μ t (hν.symm ▸ j) N) :
    UnfurledEval RD k μ i j N := by
  subst ν
  subst i
  exact E

omit [DecidableEq I] in
/-- Reindexing a projected sequence agrees with its projection to the identified weight. -/
theorem cast_down {J : Type*} (π : J → I) {ν' : Multiset J} {ν : Multiset I}
    (hν : ν'.map π = ν) (t : Seq ν') :
    hν ▸ down π rfl t = down π hν t := by
  subst ν
  rfl

namespace GenericFields
variable (k RD) (μ : X) (s b M : ℕ)
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, (d i : k) ≠ 0)
  (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)
local notation "K₀" => K k (I × Slots s b)
local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "P₀" => klP2 (k := K₀) C KL1.stdOrient
local notation "hdL" => kl_d_ne_zero k s b d hd
local notation "hP" => kl_map_ne_zero k (C := C) s b
local notation "hhom" => kl_map_homogeneous k s b d hsym
local notation "D" => coverDatum P₀ d hdpos hdL hP hhom
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)

/-- The KL family uses the same block data as the generic vacuum. -/
theorem klRouqFamily_data :
    (klRouqFamily k RD μ s b M d hdpos hd hsym).toRouqData =
      Furling.rouqData Φ
        (coverProduct.{max u v, max u v, 0} (arrowsNeg D) (L := L₀) Λm (arrowsPos D) Λp) D :=
  coverRouqFamily_toRouqData D Λm Λp RD μ
    (coverWeightNeg_finite_fibre (zm k I (Slots s b)) _)
    (coverWeightPos_finite_fibre (zp k I (Slots s b)) _)
    (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom)
    (generic_base_pair k RD μ s b M P₀ d hdpos hdL hP hhom)
    (coverDatum_finsum_arrows P₀ d hdpos hdL hP hhom C RD (klQ2 L₀ C)
      (kl_factorization k s b) (kl_extremal k s b)) (kl_factorization k s b)

universe vL vCat uCat
omit [DecidableEq I] in
/-- Transport of a prescribed-data object depends only on its object carrier. -/
theorem dataObj_cast {L : Type vL} [CommRing L]
    (T : RouqFamily (B := LinearCat.{vL, vCat, uCat} L) RD)
    (q : RouqData (B := LinearCat.{vL, vCat, uCat} L) RD)
    (hq : T.toRouqData = q) (V : q.obj μ) :
    T.dataObj q hq μ V =
      cast (congrArg (fun r : RouqData (B := LinearCat.{vL, vCat, uCat} L) RD =>
        (r.obj μ).carrier) hq.symm) V := by
  subst q
  rfl

/-- The transported generic vacuum is the actual KL-family vacuum. -/
theorem kl_dataObj_vacuum :
    (klRouqFamily k RD μ s b M d hdpos hd hsym).dataObj _
      (klRouqFamily_data RD k μ s b M d hdpos hd hsym) μ
      (genericVacuum k RD μ s b M P₀ d hdpos hdL hP hhom) = klVacuum k RD μ s b M d hdpos hd hsym := by
  rw [dataObj_cast]
  exact cast_eq _ _

omit [DecidableEq I] in
/-- Standard KL crossing factors descend to the original coefficient field. -/
theorem kl_factor_ground (i j : I) :
    MvPolynomial.map (algebraMap k K₀) (klP2 (k := k) C KL1.stdOrient i j) = P₀ i j :=
  map_klP2 (C := C) (algebraMap k K₀) KL1.stdOrient i j

omit [DecidableEq I] in
/-- In characteristic zero, the positive diagonal Cartan lengths give an
invertible natural symmetrizer for the spectral power series. -/
theorem exists_symmetrizer_of_charZero [CharZero k] :
    ∃ d : I → ℕ, (∀ i, 0 < d i) ∧ (∀ i, (d i : k) ≠ 0) ∧
      ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i := by
  refine ⟨fun i => (C.dot i i).toNat, ?_, ?_, ?_⟩
  · intro i
    exact KL3.Diagram.dot_self_toNat_pos i
  · intro i
    have hpos : 0 < (C.dot i i).toNat := by
      have := C.dot_self_pos i
      omega
    exact_mod_cast hpos.ne'
  · intro i j _
    rw [Int.toNat_of_nonneg (C.dot_self_pos i).le,
      Int.toNat_of_nonneg (C.dot_self_pos j).le]
    exact mul_comm _ _

end GenericFields
end Categorification.KLR.Unfurling

namespace Categorification.KLR.Unfurling
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory CategoryTheory.Limits CyclotomicAction
universe u v w z
variable {J : Type u} {Jp : Type u} [DecidableEq J] [DecidableEq Jp]
  {L : Type v} [Field L] (n : J → J → ℕ) (Λm : J → ℕ)
  (np : Jp → Jp → ℕ) (Λp : Jp → ℕ)
  {I : Type z} [DecidableEq I] {C : CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {P : I → I → MvPolynomial (Fin 2) L}
  (D : UnfurlingDatum L P (J ⊕ Jp))
  (hprod : RouqFamily.prodQ (unfQ (k := L) n) (unfQ (k := L) np) = unfQ (k := L) D.arrows)
  (Φ : Furling ((coverWeight n).prod (coverWeight np)) RD)
  (hπ : ∀ a, Φ.π a = D.π a)
  {μ : X} (Vg : Φ.obj (coverProduct.{u,v,0} n (L := L) Λm np Λp) μ)
  (β : Φ.Blk μ) {ν : Multiset J}
  (δ : Φ.Blk (wtop RD μ ((ν.map Sum.inl).map D.π)))
  (hδ : β.1 + Furling.blkSum (ν.map Sum.inl) = δ.1)
  (hx : Φ.wtT β.1 = vacuumBase Λm Λp)
  (hy : Φ.wtT δ.1 = (wtop (coverWeight n) (-((fun a => (Λm a : ℤ)),0)) ν,
    ((fun a => (Λp a : ℤ)),0)))
  (hV : Eq.ndrec (motive := fun x => (coverProduct.{u,v,0} n (L := L) Λm np Λp).obj x)
    (Vg β) hx = vacuum n Λm np Λp)
  (G : RouqFamily (B := LinearCat.{v,max u v + 1,max u v + 1} L) RD)
  (hG : G.toRouqData = Furling.rouqData Φ (coverProduct.{u,v,0} n (L := L) Λm np Λp) D)
  (HG : RouqUpKLR G (klQ2 L C)) (MG : BrundanMixedInversion G)
  (H : RouqUpKLR (coverProduct.{u,v,0} n (L := L) Λm np Λp) (unfQ (k := L) D.arrows))
  (hnil : ∀ a {x y} (h : x + ((coverWeight n).prod (coverWeight np)).iX a = y),
    IsNilpotent (End.of ((coverProduct.{u,v,0} n (L := L) Λm np Λp).dot a h)))
  (hzero : ∀ β a {y} (h : Φ.wtT β + ((coverWeight n).prod (coverWeight np)).iX a = y),
    ¬ Φ.rel β a → IsZero ((coverProduct.{u,v,0} n (L := L) Λm np Λp).E a h))
  (harr : ∀ a ∈ ν.map Sum.inl, ∀ b ∈ ν.map Sum.inl, D.arrows a b = 0)
  (hnd : (ν.map (Sum.inl (β := Jp))).Nodup)
  (hPQ : ∀ a b, a ≠ b → klQ2 L C a b = P b a * MvPolynomial.rename ![1,0] (P a b))
  {k : Type*} [Field k] [Algebra k L]
attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

/-- Construct the evaluation from the normalized positive regular vacuum,
with the categorical scalar action and cover identities explicit. -/
def unfurledEvalOfCoverVacuum (M : ℕ) (hM : ∀ a ∈ ν, Λm a = M)
    (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π)) (N : ℕ) (hNM : N ≤ M)
    (bub : KL3.Diagram.PiLam I k →ₐ[k] L)
    (hind : AlgebraicIndependent k (fun p : {p : I × ℕ // p.2 < N} =>
      bub (MvPolynomial.X p.1)))
    (hb : ∀ p : KL3.Diagram.PiLam I k,
      ((G).bubbleMap HG.brundan_kl_restrictScalars MG μ p).hom.app
        (G.dataObj _ hG μ Vg) = bub p • 𝟙 _) :
    UnfurledEval RD k μ (down D.π rfl (Seq.map Sum.inl t)) j N := by
  letI : ∀ x, HasFiniteBiproducts
      (((RouqFamily.homProduct L
        (cyclotomicFamily.{u,v,0} (unfQ_klrSymm (k := L) n) (cover_hlead n)
          (cover_hmonic Λm) (coverWeight n) ((fun a => (Λm a : ℤ)),0)
          (cover_hΛ n Λm) (cover_hdeg n)) (coverFamily.{u,v,0} np Λp)).obj x) : Type _) :=
    fun x => inferInstanceAs (HasFiniteBiproducts
      ((coverProduct.{u,v,0} n (L := L) Λm np Λp).obj x : Type _))
  exact unfurledEvalOfVacuum.{u,v,0,u,w,z,_}
    (k := L) (k₀ := k) (Q := unfQ (k := L) n)
    (a := fun a => (Polynomial.X : Polynomial L) ^ Λm a)
    (Q₂ := unfQ (k := L) np)
    (RD := coverWeight n) (Λ := ((fun a => (Λm a : ℤ)), 0))
    (RD₂ := coverWeight np) (T := coverFamily.{u,v,0} np Λp)
    (μ := -((fun a => (Λm a : ℤ)), 0))
    (Ψ₀ := vacuumModuleCoord n Λm np Λp)
    (unfQ_klrSymm n) (cover_hlead n) (cover_hmonic Λm)
    (cover_hΛ n Λm) (cover_hdeg n)
    (coverFamily_upKLR np Λp) (unfQ_klrSymm np)
    ((fun a => (Λp a : ℤ)),0)
    (vacuumModule n Λm np Λp) (vacuumBlock n Λm).2
    (vacuumModuleGen n Λm np Λp) (vacuumModuleCoord_gen n Λm np Λp)
    (vacuum n Λm np Λp) (vacuumRegular np Λp) (vacuum_obj_regular n Λm np Λp)
    M (fun a ha => congrArg (Polynomial.X ^ ·) (hM a ha)) D hprod
    Φ hπ Vg β δ hδ hx hy hV G hG HG MG H hnil hzero harr hnd hPQ
    t j N hNM bub hind hb
end Categorification.KLR.Unfurling

namespace Categorification.TwoRep.RouqFamily
open QuantumGroup QuantumGroup.UDot CategoryTheory
universe vL vCat uCat u v w
variable {I : Type u} [DecidableEq I] {C : CartanDatum I}
  {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {L : Type vL} [CommRing L]
  {k : Type v} [CommRing k] [Algebra k L]
attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear
/-- A polynomial bubble acts by its chosen scalar on the specified vacuum. -/
def vacuumScalarLaw (T : RouqFamily (B := LinearCat.{vL,vCat,uCat} L) RD)
    (H : RouqUpKLR T (KLR.klQ2 L C)) (M : BrundanMixedInversion T)
    (μ : X) (V : T.obj μ) (bub : KL3.Diagram.PiLam I k →ₐ[k] L) : Prop :=
  ∀ p : KL3.Diagram.PiLam I k,
    (T.bubbleMap H.brundan_kl_restrictScalars M μ p).hom.app V = bub p • 𝟙 _
end Categorification.TwoRep.RouqFamily

namespace Categorification.KLR.Unfurling.GenericFields
open QuantumGroup QuantumGroup.UDot TwoRep CategoryTheory CyclotomicAction
universe u v w
variable {I : Type u} [DecidableEq I] (k : Type v) [Field k]
  {C : CartanDatum I} {X Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (μ : X) (s b M : ℕ)
  (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, (d i : k) ≠ 0)
  (hsym : ∀ i j, C.dot i j ≠ 0 → (d i : ℤ) * C.dot j j = d j * C.dot i i)
local notation "K₀" => K k (I × Slots s b)
local notation "L₀" => L k (I × Slots s b) (I × Slots s b)
local notation "P₀" => klP2 (k := K₀) C KL1.stdOrient
local notation "hdL" => kl_d_ne_zero k s b d hd
local notation "hP" => kl_map_ne_zero k (C := C) s b
local notation "hhom" => kl_map_homogeneous k s b d hsym
local notation "D" => coverDatum P₀ d hdpos hdL hP hhom
local notation "Φ" => genericFurling k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "Λm" => vacuumWeightNeg k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "Λp" => vacuumWeightPos k s b M (fun i => RD.pair (RD.iY i) μ)
local notation "nm" => arrowsNeg D
local notation "np" => arrowsPos D
local notation "G" => klRouqFamily k RD μ s b M d hdpos hd hsym
local notation "HG" => klRouqFamily_upKLR k RD μ s b M d hdpos hd hsym
local notation "MG" => klRouqFamily_mixedInversion k RD μ s b M d hdpos hd hsym
local notation "hG" => klRouqFamily_data RD k μ s b M d hdpos hd hsym
local notation "Vg" => genericVacuum k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "β₀" => genericZeroBlock k RD μ s b M P₀ d hdpos hdL hP hhom
local notation "bub" => vacuumBubbleEval k s b M (fun i => RD.pair (RD.iY i) μ)
attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

/-- Upward KL relations with the scalar structure of the evaluation interface. -/
theorem klEvaluationUpKLR : RouqUpKLR G (klQ2 L₀ C) :=
  klRouqFamily_upKLR k RD μ s b M d hdpos hd hsym

local notation "HE" => klEvaluationUpKLR k RD μ s b M d hdpos hd hsym

/-- The scalar bubble identity at the constructed KL vacuum. -/
def bubbleScalarLaw : Prop :=
  (G).vacuumScalarLaw HE MG μ (klVacuum k RD μ s b M d hdpos hd hsym) bub

private def evaluationFromScalarRawCore {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s)
    (N : ℕ) (hM : N ≤ M) (hbnd : N ≤ b)
    (T : type_of% (G))
    (hT : T.toRouqData = Furling.rouqData Φ
      (coverProduct.{max u v,max u v,0} nm (L := L₀) Λm np Λp) D)
    (HT : RouqUpKLR T (klQ2 L₀ C)) (MT : BrundanMixedInversion T)
    (W : T.obj μ) (hW : T.dataObj _ hT μ Vg = W)
    (hb : T.vacuumScalarLaw HT MT μ W bub)
    (j : Seq (((negativeStrandWeight k b i hs).map Sum.inl).map (D).π)) :
    UnfurledEval RD k μ (down (D).π rfl
      (Seq.map Sum.inl (negativeStrandSeq k b i hs))) j N := by
  classical
  let νm : Multiset (LabelNeg I K₀ L₀) := negativeStrandWeight k b i hs
  let t : Seq νm := negativeStrandSeq k b i hs
  refine unfurledEvalOfCoverVacuum.{max u v, max u v, w, u, v}
    (L := L₀) (k := k) (RD := RD) (ν := νm)
    (P := fun a b => MvPolynomial.map (algebraMap K₀ L₀) (P₀ a b))
    nm Λm np Λp D
    (prodQ_unfQ (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom))
    Φ (fun _ => rfl) Vg β₀
    (genericVacuumTargetBlock k RD μ s b M P₀ d hdpos hdL hP hhom νm)
    (genericVacuumTargetBlock_val k RD μ s b M P₀ d hdpos hdL hP hhom νm)
    (genericZeroBlock_wtT k RD μ s b M P₀ d hdpos hdL hP hhom)
    (genericVacuumTargetBlock_wtT k RD μ s b M P₀ d hdpos hdL hP hhom νm)
    (genericVacuum_transport k RD μ s b M P₀ d hdpos hdL hP hhom)
    T hT HT MT
    (coverProduct_upKLR_unfQ D Λm Λp (coverDatum_noCrossArrows P₀ d hdpos hdL hP hhom))
    (coverProduct_dot_isNilpotent D Λm Λp)
    (fun β a _ h hr => (coverFurling_isZero D Λm Λp RD μ
      (coverWeightNeg_finite_fibre (zm k I (Slots s b)) _)
      (coverWeightPos_finite_fibre (zp k I (Slots s b)) _) β a h hr).1)
    (by
      rw [negativeStrandWeight_map_inl]
      exact strandWeight_arrows k b i hs P₀ d hdpos hdL hP hhom
        (fun a c _ => ⟨_, kl_factor_ground k s b a c⟩))
    (by rw [negativeStrandWeight_map_inl]; exact strandWeight_nodup k b i hs)
    (kl_factorization k s b)
    M (negativeStrandWeight_level k b i hs M _) t j N hM bub
    (vacuumBubbleEval_indep k s b M _ hbnd)
    (fun p => by rw [hW]; exact hb p)

private def evaluationFromScalarRaw {ν : Multiset I} (i : Seq ν) (hs : ν.card ≤ s)
    (N : ℕ) (hM : N ≤ M) (hbnd : N ≤ b)
    (hb : bubbleScalarLaw k RD μ s b M d hdpos hd hsym)
    (j : Seq (((negativeStrandWeight k b i hs).map Sum.inl).map (D).π)) :
    UnfurledEval RD k μ (down (D).π rfl
      (Seq.map Sum.inl (negativeStrandSeq k b i hs))) j N := by
  unfold bubbleScalarLaw at hb
  exact evaluationFromScalarRawCore k RD μ s b M d hdpos hd hsym i hs N hM hbnd G hG HE MG
    (klVacuum k RD μ s b M d hdpos hd hsym)
    (kl_dataObj_vacuum RD k μ s b M d hdpos hd hsym) hb j

/-- Assemble the concrete generic evaluation from its scalar vacuum identity.
All coordinate, support, weight, and action data are constructed here. -/
def evaluationFromScalar {ν : Multiset I} (i j : Seq ν) (hs : ν.card ≤ s)
    (N : ℕ) (hM : N ≤ M) (hbnd : N ≤ b)
    (hb : bubbleScalarLaw k RD μ s b M d hdpos hd hsym) :
    UnfurledEval RD k μ i j N := by
  let t := negativeStrandSeq k b i hs
  have hν := negativeStrandWeight_map k s b P₀ d hdpos hdL hP hhom i hs
  have ht : hν ▸ down (D).π rfl (Seq.map Sum.inl t) = i := by
    rw [cast_down]
    exact down_negativeStrandSeq k s b P₀ d hdpos hdL hP hhom i hs
  exact UnfurledEval.reindex hν ht
    (evaluationFromScalarRaw k RD μ s b M d hdpos hd hsym i hs N hM hbnd
      hb (hν.symm ▸ j))

end Categorification.KLR.Unfurling.GenericFields
