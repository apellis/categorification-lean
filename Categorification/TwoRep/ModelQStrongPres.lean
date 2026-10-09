/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrongSl2
import Categorification.TwoRep.ModelQStrongZig
import Categorification.TwoRep.ModelQStrongBraidQ
import Categorification.TwoRep.ModelQStrongCyc
import Categorification.Diagrams.CL.Presentation

/-!
# The relations of `U_Q(g)` in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 1.1. This file assembles the relations of `presCL`
(`Categorification.Diagrams.CL.Presentation`) killed by the model of a `Q`-strong
2-representation (`Categorification.TwoRep.ModelQStrong`, `(α_i, α_i) = 2`): the zigzags
(`ModelQStrongZig`), the single-label relations (`ModelQStrongSl2`), the mixed KLR relations
(`ModelQStrongKLR`, `ModelQStrongPoly`, `ModelQStrongBraidQ`) and the right rotation of all
crossings (`ModelQStrongCyc`). The scalars of `presCL` are those of the model, with the dots
normalized (`r_i = 1`) and the KLR polynomials `Q'_{ij}(u, v) = Q_{ij}(r_i u, r_j v)` of the
normalized dots.

The remaining relations of `presCL` are the left rotation of mixed crossings `cycCrossL j i`
(`i ≠ j`, CL §6.3) and the mixed relations `downupEF`, `downupFE` (CL Prop. 6.3). They are
collected in the predicate `QStrong.MixedKilled`; given it, the model respects `presCL`
(`QStrong.respects_presCL`) and descends to a linear functor on the hom categories of `U_Q(g)`
(`QStrong.interpCL`).

## Main results

* `QStrong.MixedKilled`: the three families of mixed relations are killed;
* `QStrong.relationsCL_killed`: every relation of `presCL`, given `MixedKilled`;
* `QStrong.respects_presCL`, `QStrong.interpCL`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable {S : QStrong B C RD k Q} (hsl : ∀ i, C.dot i i = 2) (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh

/-- A relation of `presCL` is killed by the model, read with its own outer regions. -/
def KilledCL (r : Rel RD) : Prop :=
  (freeLift k (interp (genImg (S := S) hsl Sc) (Rel.dom r).start (Rel.dom r).endR).functor).map
    (CL.relationCL RD k Sc r) = 0

/-- **The mixed relations** of `presCL` are killed by the model: the left rotation of mixed
crossings (`cycCrossL j i`, `i ≠ j`; CL `eq_almost_cyclic`, §6.3) and the relations
`downupEF`, `downupFE` (CL §2.4, Prop. 6.3). -/
structure MixedKilled : Prop where
  cycCrossL : ∀ (j i : I), j ≠ i → ∀ μ : X, KilledCL (S := S) hsl Sc (.cycCrossL j i μ)
  downupEF : ∀ (i j : I) (h : i ≠ j) (μ : X), KilledCL (S := S) hsl Sc (.downupEF i j h μ)
  downupFE : ∀ (i j : I) (h : i ≠ j) (μ : X), KilledCL (S := S) hsl Sc (.downupFE i j h μ)

/-- The mixed relations of `presCL`: `cycCrossL j i` for `j ≠ i`, `downupEF`, `downupFE`. -/
def _root_.Categorification.KL3.Diagram.Rel.IsMixed : Rel RD → Prop
  | .cycCrossL j i _ => j ≠ i
  | .downupEF _ _ _ _ => True
  | .downupFE _ _ _ _ => True
  | _ => False

/-- A KL III relation that is also a relation of `presCL` (for `r = 1`, `t_{ii} = 1`). -/
theorem killedCL_of_relation {r : Rel RD} (h : CL.relationCL RD k Sc r = relation k r)
    (hk : (freeLift k (interp (genImg (S := S) hsl Sc) (Rel.dom r).start (Rel.dom r).endR).functor).map
      (relation k r) = 0) : KilledCL (S := S) hsl Sc r := by
  rw [KilledCL, h]; exact hk

set_option maxHeartbeats 2000000 in
/-- `Q`-cyclicity, right rotation, for all labels (`ModelQStrongCyc`), as a relation of
`presCL`. -/
theorem killedCL_cycCrossR (j i : I) (μ : X) : KilledCL (S := S) hsl Sc (.cycCrossR j i μ) := by
  unfold KilledCL
  change (freeLift k (interp (genImg (S := S) hsl Sc) (KL3.Diagram.wt RD μ [dn j, dn i] : X)
    μ).functor).map ((((Sc.t i j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD j i μ) -
      LinDiagram.of (downCross RD j i μ)) = 0
  set_option backward.isDefEq.respectTransparency false in
  rw [Functor.map_sub, Functor.map_smul, freeLift_map_of, freeLift_map_of, sub_eq_zero]
  exact cycCrossR_gen (S := S) hsl Sc j i μ

/-- The KLR relations of `presCL` for scalars `Sc` with `r_i = 1` whose KLR polynomials are those
of the normalized dots. -/
theorem killedCL_klr (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (μ : X) (r : KLR.Diagram.Rel I) : KilledCL (S := S) hsl Sc (.klr μ r) := by
  have hr' : (fun c => (Sc.r c : k)) = fun _ => 1 := by funext c; rw [hr c, Units.val_one]
  rw [KilledCL]
  have he : CL.relationCL RD k Sc (.klr μ r) = upLin RD k μ (KLR.Diagram.relation k
      (fun i j => CL.Rescale.scaleP ![(S.rQ i : k), (S.rQ j : k)] (Q i j)) r) := by
    change upLin RD k μ (CL.relationR k (CL.qCL Sc) (fun c => (Sc.r c : k)) r) = _
    rw [hr', CL.relationR_congr k (Q' := fun i j => CL.Rescale.scaleP
      ![(S.rQ i : k), (S.rQ j : k)] (Q i j)) hQ rfl, CL.relationR_one]
  rw [he]
  rcases r with c | ⟨c, d, h⟩ | c | ⟨c, d, h⟩ | c | ⟨c, d, h⟩ | ⟨c, d, e, h⟩ | ⟨c, d, h⟩
  · exact killed_klr_sqEq (S := S) hsl Sc c μ
  · exact klr_sqNe (S := S) hsl Sc c d h (hQ2 c d h) μ
  · exact killed_klr_slideLEq (S := S) hsl Sc c μ
  · exact killed_klr_slideLNe (S := S) hsl Sc c d h μ
  · exact killed_klr_slideREq (S := S) hsl Sc c μ
  · exact killed_klr_slideRNe (S := S) hsl Sc c d h μ
  · exact killed_klr_braid_gen (S := S) hsl Sc c d e h μ
  · exact klr_braidQ (S := S) hsl Sc c d h (hQ3 c d h) μ

set_option maxHeartbeats 1000000 in
/-- **Every relation of `presCL` other than the mixed ones** is killed by the model, for scalars
`Sc` with `r_i = 1` whose KLR polynomials are those of the normalized dots,
`Q_{ij}^{Sc}(u, v) = Q_{ij}(r_i u, r_j v)` for `i ≠ j`. -/
theorem killedCL_of_not_mixed (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (r : Rel RD) (hmix : ¬ r.IsMixed) : KilledCL (S := S) hsl Sc r := by
  have hri : ∀ c, (((Sc.r c)⁻¹ : kˣ) : k) ^ 2 = 1 := fun c => by
    rw [hr c, inv_one, Units.val_one, one_pow]
  rcases r with ⟨i, μ⟩ | ⟨i, μ⟩ | ⟨i, lam, α, h⟩ | ⟨i, lam, α, h⟩ | ⟨i, lam, h⟩ | ⟨i, lam, h⟩ |
    ⟨i, lam⟩ | ⟨i, μ⟩ | ⟨i, lam⟩ | ⟨i, lam⟩ | ⟨j, i, μ⟩ | ⟨j, i, μ⟩ | ⟨i, j, h, μ⟩ |
    ⟨i, j, h, μ⟩ | ⟨μ, r⟩
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_cycDotR (S := S) hsl Sc i μ)
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_cycDotL (S := S) hsl Sc i μ)
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_cwNeg (S := S) hsl Sc i lam α h)
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_ccwNeg (S := S) hsl Sc i lam α h)
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_cwOne (S := S) hsl Sc i lam h)
  · exact killedCL_of_relation (S := S) hsl Sc rfl (killed_ccwOne (S := S) hsl Sc i lam h)
  · refine killedCL_of_relation (S := S) hsl Sc ?_ (killed_curlR (S := S) hsl Sc i lam)
    change LinDiagram.of (KL3.Diagram.curlR RD i lam) - (Sc.r i : k) • curlRHS RD k i lam =
      LinDiagram.of (KL3.Diagram.curlR RD i lam) - curlRHS RD k i lam
    rw [hr i, Units.val_one, one_smul]
  · refine killedCL_of_relation (S := S) hsl Sc ?_ (killed_curlL (S := S) hsl Sc i μ)
    change LinDiagram.of (KL3.Diagram.curlL RD i μ) - (Sc.r i : k) • curlLHS RD k i μ =
      LinDiagram.of (KL3.Diagram.curlL RD i μ) - curlLHS RD k i μ
    rw [hr i, Units.val_one, one_smul]
  · refine killedCL_of_relation (S := S) hsl Sc ?_ (killed_decompEF (S := S) hsl Sc i lam)
    change LinDiagram.of (𝟙 _) + (((Sc.r i)⁻¹ : kˣ) : k) ^ 2 •
        LinDiagram.of (KL3.Diagram.crossl RD i i lam ≫ KL3.Diagram.crossr RD i i lam) - decompEFSum RD k i lam =
      LinDiagram.of (𝟙 _) + LinDiagram.of (KL3.Diagram.crossl RD i i lam ≫ KL3.Diagram.crossr RD i i lam) -
        decompEFSum RD k i lam
    rw [hri i, one_smul]
  · refine killedCL_of_relation (S := S) hsl Sc ?_ (killed_decompFE (S := S) hsl Sc i lam)
    change LinDiagram.of (𝟙 _) + (((Sc.r i)⁻¹ : kˣ) : k) ^ 2 •
        LinDiagram.of (KL3.Diagram.crossr RD i i lam ≫ KL3.Diagram.crossl RD i i lam) - decompFESum RD k i lam =
      LinDiagram.of (𝟙 _) + LinDiagram.of (KL3.Diagram.crossr RD i i lam ≫ KL3.Diagram.crossl RD i i lam) -
        decompFESum RD k i lam
    rw [hri i, one_smul]
  · exact killedCL_cycCrossR (S := S) hsl Sc j i μ
  · have hji : j = i := not_not.1 hmix
    subst hji
    refine killedCL_of_relation (S := S) hsl Sc ?_ (killed_cycCrossL (S := S) hsl Sc j μ)
    change (((Sc.t j j)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD j j μ) -
        LinDiagram.of (downCross RD j j μ) =
      LinDiagram.of (rotCrossL RD j j μ) - LinDiagram.of (downCross RD j j μ)
    rw [Sc.t_self, inv_one, Units.val_one, one_smul]
  · exact absurd trivial hmix
  · exact absurd trivial hmix
  · exact killedCL_klr (S := S) hsl Sc hr hQ hQ2 hQ3 μ r

/-- **Every relation of `presCL`** is killed by the model, given the mixed relations
(`MixedKilled`). -/
theorem relationsCL_killed (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (hmix : MixedKilled (S := S) hsl Sc) (r : Rel RD) : KilledCL (S := S) hsl Sc r := by
  by_cases hm : r.IsMixed
  · rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨j, i, μ⟩ | ⟨i, j, h, μ⟩ |
      ⟨i, j, h, μ⟩ | _
    all_goals first
      | exact hm.elim
      | exact hmix.cycCrossL j i hm μ
      | exact hmix.downupEF i j h μ
      | exact hmix.downupFE i j h μ
  · exact killedCL_of_not_mixed (S := S) hsl Sc hr hQ hQ2 hQ3 r hm

/-- **The model of a `Q`-strong 2-representation respects `U_Q(g)`** (CL Theorem 1.1, on hom
categories, `(α_i, α_i) = 2`), given the mixed relations: for all outer regions `s₀`, `t₀`, the
interpretation of the free 2-category on the signature of `U` in `K^•(obj t₀, obj s₀)` descends
to `presCL` for the scalars `Sc` (`r_i = 1`, KLR polynomials of the normalized dots). -/
theorem respects_presCL (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (hmix : MixedKilled (S := S) hsl Sc) (s₀ t₀ : X) :
    (CL.presCL RD k Sc).Respects (interp (genImg (S := S) hsl Sc) s₀ t₀).functor := by
  refine respects (genImg (S := S) hsl Sc) (CL.presCL RD k Sc) s₀ t₀ ?_
    (fun g => Signature.IsEven.odd_eq_false g)
  intro i _ _ _ _
  rcases i with (i | c | c) | r
  · exact i.elim
  · change (freeLift k (interp (genImg (S := S) hsl Sc) _ _).functor).map
      (LinDiagram.of (Pivotal.zigL (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id,
      sub_eq_zero]
    exact zigL_eq (S := S) hsl Sc c
  · change (freeLift k (interp (genImg (S := S) hsl Sc) _ _).functor).map
      (LinDiagram.of (Pivotal.zigR (inv RD).toColourDuality c) - LinDiagram.of (𝟙 _)) = 0
    set_option backward.isDefEq.respectTransparency false in
    rw [Functor.map_sub, freeLift_map_of, freeLift_map_of, CategoryTheory.Functor.map_id,
      sub_eq_zero]
    exact zigR_eq (S := S) hsl Sc c
  · exact relationsCL_killed (S := S) hsl Sc hr hQ hQ2 hQ3 hmix r

/-- **The 2-representation of `U_Q(g)` defined by a `Q`-strong 2-representation**, on hom categories (CL Theorem 1.1, `(α_i, α_i) = 2`), given the mixed relations: the
linear functor from the 2-morphisms of `U_Q(g)` between 1-morphisms `t₀ → s₀` to
`K^•(obj t₀, obj s₀)`. -/
def interpCL (hr : ∀ c, Sc.r c = 1)
    (hQ : ∀ c d, c ≠ d →
      CL.qCL Sc c d = CL.Rescale.scaleP ![(S.rQ c : k), (S.rQ d : k)] (Q c d))
    (hQ2 : ∀ c d, c ≠ d → ∀ m ∈ (Q c d).support,
      (m 0 : ℤ) * C.dot c c + (m 1 : ℤ) * C.dot d d = -2 * C.dot c d)
    (hQ3 : ∀ c d, c ≠ d → ∀ m ∈ (KLR.qbar (Q c d)).support, (m 0 : ℤ) * C.dot c c +
      (m 1 : ℤ) * C.dot d d + (m 2 : ℤ) * C.dot c c = -(C.dot c d + C.dot c c + C.dot d c))
    (hmix : MixedKilled (S := S) hsl Sc) (s₀ t₀ : X) :
    (CL.presCL RD k Sc).Presented ⥤
      (S.model.lift.obj (fo (S := psig RD) t₀) ⟶ S.model.lift.obj (fo (S := psig RD) s₀)) :=
  (CL.presCL RD k Sc).lift (respects_presCL (S := S) hsl Sc hr hQ hQ2 hQ3 hmix s₀ t₀)

end QStrong

end Model

end Categorification.TwoRep
