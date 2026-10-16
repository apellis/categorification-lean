/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurledCorner
import Categorification.TwoRep.FurlingKL

/-!
# Evaluation on the summands of a furled word

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action` and the proof of Theorem `nondegenerate`, “Triviality of a relation”.
The positive-word evaluation is transported to the defining Rouquier data, evaluated at
an object and a block, and composed with the actual lift inclusion and projection.
`upCorner_toUEnd` identifies this semilinear map on every KLR element with the completed
cover action of its scalar extension under `gamma`. No basis-image equation is assumed.

`wordHomTransport_klrComplAt` transports the source weight, target weight and evaluation
object together, allowing the blockwise action to be compared with vacuum coordinates.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits KLR KLR.Diagram
open KL3.Diagram
universe wk wL u₁ u₂ v₁ u₃ u₄

namespace RouqFamily
section Data
variable {k : Type wk} [CommRing k] {L : Type wL} [CommRing L] [Algebra k L]
  {I : Type*} [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (T : RouqFamily (B := LinearCat.{wL, v₁, u₂} L) RD)
  (H : RouqUpKLR T (klQ2 L C)) (M : BrundanMixedInversion T)
  (d : RouqData (B := LinearCat.{wL, v₁, u₂} L) RD) (hd : T.toRouqData = d)
  (μ : X) {ν : Multiset I}

/-- Positive-word evaluation in prescribed, equal Rouquier data. -/
def upEvalData {t s : Seq ν} :
    ((pres RD k).obj (ob RD μ (ups (word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (word s)))) →ₛₗ[algebraMap k L]
      (d.wordCell μ t ⟶ d.wordCell μ s) := by
  subst d
  exact T.upEvalSemilinear H M μ

attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

private def scalarKLRAct : KLRAlgebra k (klQ2 k C) ν →ₐ[k] T.WordEnd μ ν :=
  { (RouqFamily.klrAct H μ).toRingHom.comp
      (KLRAlgebra.mapRingHom (algebraMap k L) (fun i j _ => map_klQ2 C _ i j)) with
    commutes' c := by
      change RouqFamily.klrAct H μ (KLRAlgebra.mapRingHom _ _ (algebraMap k _ c)) = _
      rw [KLRAlgebra.mapRingHom_algebraMap, AlgHom.commutes]
      rfl }

private theorem scalarKLRAct_eq : scalarKLRAct (k := k) (ν := ν) T H μ =
    RouqFamily.klrAct (T.upKLR_kl H.brundan_kl_restrictScalars) μ := by
  apply KLRAlgebra.algHom_ext
  · intro i
    change RouqFamily.klrAct H μ (KLRAlgebra.mapRingHom _ _ (KLRAlgebra.e i)) = _
    rw [KLRAlgebra.mapRingHom_e, RouqFamily.klrAct_e, RouqFamily.klrAct_e]
  · intro a
    change RouqFamily.klrAct H μ (KLRAlgebra.mapRingHom _ _ (KLRAlgebra.x a)) = _
    rw [KLRAlgebra.mapRingHom_x, RouqFamily.klrAct_dot, RouqFamily.klrAct_dot]
  · intro j
    change RouqFamily.klrAct H μ (KLRAlgebra.mapRingHom _ _ (KLRAlgebra.ψ j)) = _
    rw [KLRAlgebra.mapRingHom_ψ, RouqFamily.klrAct_cross, RouqFamily.klrAct_cross]

/-- Scalar extension intertwines the presentation evaluation and the KLR action. -/
theorem upEvalSemilinear_toUEnd (r : KLRAlgebra k (klQ2 k C) ν) (t s : Seq ν) :
    T.upEvalSemilinear H M μ (toUEnd RD k μ ν r t s) =
      RouqFamily.klrAct H μ
        (KLRAlgebra.mapRingHom (algebraMap k L) (fun i j _ => map_klQ2 C _ i j) r) t s := by
  have h := congrArg (fun f : KLRAlgebra k (klQ2 k C) ν →ₐ[k] T.WordEnd μ ν => f r t s)
    (T.upAct_comp_toUEnd H.brundan_kl_restrictScalars M μ ν)
  exact h.trans (congrArg (fun f : KLRAlgebra k (klQ2 k C) ν →ₐ[k] T.WordEnd μ ν => f r t s)
    (scalarKLRAct_eq T H μ).symm)

/-- The presentation action of a KLR element on a free-algebra representative after scalar extension. -/
theorem upEvalData_toUEnd_mk (r : KLRAlgebra k (klQ2 k C) ν)
    (a : FreeAlgebra L (KLR.Gen ν))
    (ha : KLRAlgebra.mapRingHom (algebraMap k L) (fun i j _ => map_klQ2 C _ i j) r =
      KLRAlgebra.mk L (klQ2 L C) ν a) (t s : Seq ν) :
    T.upEvalData H M d hd μ (toUEnd RD k μ ν r t s) = d.klrActFree L μ ν a t s := by
  subst d
  change T.upEvalSemilinear H M μ _ = _
  rw [upEvalSemilinear_toUEnd, ha, RouqFamily.klrAct_mk]
end Data

section Transport
variable {L : Type wL} [CommRing L]
  {I : Type*} [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  (S : RouqFamily (B := LinearCat.{wL, v₁, u₂} L) RD)
  {ν : Multiset I} {x y x' y' : X}
  (hx : x = x') (hy : y = y') (e : wtop RD x ν = y) (e' : wtop RD x' ν = y')
  (V : S.obj x) (V' : S.obj x') (hV : hx ▸ V = V')

/-- Transport of evaluated word morphisms along equal weights and objects. -/
def wordHomTransport (t s : Seq ν) :
    ((S.wordCellAt x y e t).obj.obj V ⟶ (S.wordCellAt x y e s).obj.obj V) ≃ₗ[L]
      ((S.wordCellAt x' y' e' t).obj.obj V' ⟶ (S.wordCellAt x' y' e' s).obj.obj V') := by
  subst x' y' V'
  exact LinearEquiv.refl L _

theorem wordHomTransport_klrComplAt
    {Q : I → I → MvPolynomial (Fin 2) L} (H : RouqUpKLR S Q)
    (hnil : ∀ (c : I) {a b : X} (h : a + RD.iX c = b), IsNilpotent (End.of (S.dot c h)))
    (G : GradingDatum Q) (f : G.completion ν) (t s : Seq ν) :
    wordHomTransport S hx hy e e' V V' hV t s
      (((klrComplAt H x y e hnil G f) t s).hom.app V) =
      (((klrComplAt H x' y' e' hnil G f) t s).hom.app V') := by
  subst x' y' V'
  rfl
end Transport
end RouqFamily

namespace Furling
variable {L : Type wL} [Field L]
  {J : Type u₁} {I : Type*} [DecidableEq I] [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc]
  {X Y : Type u₄} [AddCommGroup X] [AddCommGroup Y]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y}
  {Φ : Furling RDc RD}
  (S : RouqFamily (B := LinearCat.{wL, v₁, u₂} L) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  {P : I → I → MvPolynomial (Fin 2) L} {D : Unfurling.UnfurlingDatum L P J}
  (hπ : ∀ a, Φ.π a = D.π a)
  {μ : X} (V : ∀ β : Φ.Blk μ, blkCat Φ S β.1)
  {ν : Multiset I} (δ : Φ.Blk (wtop RD μ ν)) (β : Φ.Blk μ)
  (ν' : Unfurling.Lift D ν) (hδ : β.1 + blkSum ν'.1 = δ.1)

/-- Extract a matrix entry by the lift inclusion and projection at the specified block. -/
def cornerEval (t s : Seq ν'.1) (j : Seq ν) :
    ((rouqData Φ S D).wordCell μ (Unfurling.down D.π ν'.2 t) ⟶
      (rouqData Φ S D).wordCell μ j) →ₗ[L]
    ((S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) t).obj.obj (V β) ⟶
      (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (V β)) where
  toFun f := lgen S hπ μ V δ β ν' hδ t ≫
    (evalBlk Φ S V δ).map f ≫ lproj S V hπ δ β ν' hδ j s
  map_add' f g := by simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c f := by
    simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

variable {S}
  (H : RouqUpKLR S (Unfurling.unfQ (k := L) D.arrows))
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))
  (hzero : ∀ (β : J →₀ ℤ) (a : J) {y : Xc} (h : Φ.wtT β + RDc.iX a = y), ¬ Φ.rel β a →
    IsZero (S.E a h))

include hzero in
/-- The extracted free-algebra action is the completed cover action. -/
theorem cornerEval_free (r : FreeAlgebra L (KLR.Gen ν)) (t s : Seq ν'.1) {j : Seq ν}
    (hs : Unfurling.down D.π ν'.2 s = j) :
    cornerEval S hπ V δ β ν' hδ t s j
      ((rouqData Φ S D).klrActFree L μ ν r (Unfurling.down D.π ν'.2 t) j) =
      actT μ V δ β ν' hδ H hnil r t s := by
  exact lgen_actG_lproj V hπ δ β ν' hδ hzero H hnil r t s hs

variable {k : Type wk} [CommRing k] [Algebra k L]
  (T : RouqFamily (B := LinearCat.{wL, max u₁ v₁, max u₁ u₂} L) RD)
  (hT : T.toRouqData = rouqData Φ S D)
  (HT : RouqUpKLR T (klQ2 L C)) (MT : BrundanMixedInversion T)

/-- Semilinear presentation evaluation between two lift summands. -/
def upCorner (t s : Seq ν'.1) (j : Seq ν) :
    ((pres RD k).obj (ob RD μ (ups (word (Unfurling.down D.π ν'.2 t)))) ⟶
      (pres RD k).obj (ob RD μ (ups (word j)))) →ₛₗ[algebraMap k L]
    ((S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) t).obj.obj (V β) ⟶
      (S.wordCellAt (Φ.wtT β.1) (Φ.wtT δ.1) (wtop_lift μ δ β ν' hδ) s).obj.obj (V β)) :=
  (cornerEval S hπ V δ β ν' hδ t s j).comp
    (T.upEvalData HT MT (rouqData Φ S D) hT μ)

include hzero in
theorem upCorner_toUEnd
    (hPQ : ∀ a b, a ≠ b → klQ2 L C a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (r : KLRAlgebra k (klQ2 k C) ν) (t s : Seq ν'.1) {j : Seq ν}
    (hs : Unfurling.down D.π ν'.2 s = j) :
    upCorner hπ V δ β ν' hδ T hT HT MT t s j
      (toUEnd RD k μ ν r (Unfurling.down D.π ν'.2 t) j) =
      (((RouqFamily.klrComplAt H (Φ.wtT β.1) (Φ.wtT δ.1)
        (wtop_lift μ δ β ν' hδ) hnil (Unfurling.unfGrading (k := L) D.arrows)
        (Unfurling.gamma D hPQ
          (KLRAlgebra.mapRingHom (algebraMap k L) (fun i j _ => map_klQ2 C _ i j) r) ν')) t s).hom.app
            (V β)) := by
  obtain ⟨a, ha⟩ := KLRAlgebra.mk_surjective
    (KLRAlgebra.mapRingHom (algebraMap k L) (fun i j _ => map_klQ2 C _ i j) r)
  change cornerEval S hπ V δ β ν' hδ t s j (T.upEvalData HT MT _ hT μ _) = _
  rw [RouqFamily.upEvalData_toUEnd_mk T HT MT _ hT μ r a ha.symm]
  rw [cornerEval_free hπ V δ β ν' hδ H hnil hzero a t s hs, ← ha, Unfurling.gamma_mk]
  rfl
end Furling
end Categorification.TwoRep
