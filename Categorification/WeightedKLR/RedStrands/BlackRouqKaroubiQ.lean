/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqCupQ
import Categorification.TwoRep.StrictPseudofunctorDottedCap

/-!
# Rouquier's invertibility conditions for the image adjunctions in the completed black action

Brundan, arXiv:1501.00350v1, (1.6), (1.8) and (1.9), for the black action of Cautis–Lauda's
`U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) on the additive
idempotent completions of the violating quotients (Webster, arXiv:1309.3796v3, §4.5–4.6,
`blackActionCompletedQ`), with the adjunction `E_i ⊣ F_i` of `blackCompletedAdjunctionQ`.

`blackCompletedSumInvTo_sigmaUpQ` and `blackCompletedSumInvFrom_sigmaUpQ` give the explicit
inverses for the completed action of the diagrams `CLQ.sigmaUpLs`, `CLQ.capUp`, `CLQ.cupUp`.
Here they are restated for the rightward crossing, the dotted caps and the dotted cups built
from the image under `blackActionCompletedQ` of the adjunction `E_i ⊣ F_i`, of a dot and of a
crossing of two downward strands, which is the form used for the local Rouquier data:

* `toNatTrans_blackCompletedSigmaQ`, `toNatTrans_blackCompletedDottedCapQ`,
  `toNatTrans_blackCompletedDottedCupQ`: these 2-morphisms are the completed actions of the
  diagrams, up to the equalities `map_comp` and `map_id`;
* `blackCompletedSigmaSumInvToQ` (`⟨i, ν⟩ ≤ 0`) and `blackCompletedSigmaSumInvFromQ`
  (`0 ≤ ⟨i, ν⟩`): the explicit inverses, at the middle weight `ν`.

The crossing here is the image of the diagram crossing; the sign convention by which the
same-colour crossing acts as `−ψ` enters only when the action is compared with the module side.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep
  Idempotents

universe u v w

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  {sc : KL3.Diagram.CL.CLScalars C k}

/-- The downward strand `F_i` as a 1-morphism of the 1-cell dual of `U_Q(g)`. -/
abbrev downStrandRevQ (k : Type w) [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (i : I)
    {μ ν : X} (h : wt RD μ [(false, i)] = ν) :=
  RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h)

/-- The upward strand `E_i`, the right dual of `downStrandRevQ`, in the 1-cell dual. -/
abbrev downStrandDualRevQ (k : Type w) [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (i : I)
    {μ ν : X} (h : wt RD μ [(false, i)] = ν) :=
  RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
    (downStrandHomQ (k := k) (sc := sc) i h))

/-- The adjunction `E_i ⊣ F_i` of `blackCompletedAdjunctionQ`, in the 1-cell dual. -/
abbrev downStrandAdjQ (k : Type w) [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (i : I)
    {μ ν : X} (h : wt RD μ [(false, i)] = ν) :
    downStrandRevQ k sc i h ⊣ downStrandDualRevQ k sc i h :=
  RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h) ⟨dn i, μ⟩ rfl).right)

variable (P : Presentation (signature RD (fun r => (Λ r).val)) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel,
    P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((CLQ.pres RD k sc).rel r)) = 0)
variable (i : I) {μ ν : X} (h₁ : wt RD μ [(false, i)] = ν) (h₁' : wt RD ν [(true, i)] = μ)

include hP in
/-- The completed black action of `E_i` followed by that of `F_i` is the completed action of
the word `[F_i, E_i]` (`map_comp` of `blackActionCompletedQ`). -/
theorem completionMap_blackAct_dn_up : completionMap (blackAct P [(true, i)] h₁') ⋙
        completionMap (blackAct P [(false, i)] h₁) =
      completionMap (blackAct P [dn i, up i] (wt_dn_up RD i ν)) :=
  (congrArg Cat.Hom.toFunctor ((blackActionCompletedQ sc P hP).map_comp
    (downStrandDualRevQ k sc i h₁) (downStrandRevQ k sc i h₁))).symm

include hP in
/-- The completed black action of the empty word is the identity (`map_id`). -/
theorem completionMap_blackAct_nil (ν : X) : completionMap (blackAct P [] (wt_nil RD ν)) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor ((blackActionCompletedQ sc P hP).map_id ⟨⟨ν⟩⟩)

/-- **The dotted cap in the completed black action**: the cap of the image adjunction after
`m` powers of the image of a dot is the completed action of `CLQ.capUp`. -/
theorem toNatTrans_blackCompletedDottedCapQ
    (x : downStrandRevQ k sc i h₁ ⟶ downStrandRevQ k sc i h₁)
    (hx : homTrQ x = dnDotQ (sc := sc) i μ) (m : ℕ) :
    ((blackActionCompletedQ sc P hP).map _ ◁ powComp ((blackActionCompletedQ sc P hP).map₂ x) m ≫
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
      ).toNatTrans =
    eqToHom (completionMap_blackAct_dn_up P hP i h₁ h₁') ≫
      completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_nil RD ν) (CLQ.capUp RD k sc i ν m)) ≫
      eqToHom (completionMap_blackAct_nil P hP ν) := by
  have e := sp_map₂_dottedCap (blackActionCompletedQ sc P hP) (downStrandAdjQ k sc i h₁) x m
  have e' : ((blackActionCompletedQ sc P hP).map _ ◁
      powComp ((blackActionCompletedQ sc P hP).map₂ x) m ≫
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit) =
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ (downStrandDualRevQ k sc i h₁ ◁ powComp x m ≫
          (downStrandAdjQ k sc i h₁).counit) ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_id _) := by
    rw [e]; simp
  rw [e', Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans]
  have hm : ((blackActionCompletedQ sc P hP).map₂ (downStrandDualRevQ k sc i h₁ ◁ powComp x m ≫
      (downStrandAdjQ k sc i h₁).counit)).toNatTrans =
      completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_nil RD ν)
        (CLQ.capUp RD k sc i ν m)) :=
    congrArg (fun t => completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_nil RD ν) t))
      (homTrQ_capQ i h₁ x hx m)
  rw [hm]

variable {ν₂ : X} (h₂ : wt RD ν [(false, i)] = ν₂) (h₂' : wt RD ν₂ [(true, i)] = ν)

include hP in
/-- The completed black action of `F_i` followed by that of `E_i` is the completed action of
the word `[E_i, F_i]` (`map_comp` of `blackActionCompletedQ`). -/
theorem completionMap_blackAct_up_dn : completionMap (blackAct P [(false, i)] h₂) ⋙
        completionMap (blackAct P [(true, i)] h₂') =
      completionMap (blackAct P [up i, dn i] (wt_up_dn RD i ν)) :=
  (congrArg Cat.Hom.toFunctor ((blackActionCompletedQ sc P hP).map_comp
    (downStrandRevQ k sc i h₂) (downStrandDualRevQ k sc i h₂))).symm

/-- **The dotted cup in the completed black action**: the cup of the image adjunction followed
by `m` powers of the image of a dot is the completed action of `CLQ.cupUp`. -/
theorem toNatTrans_blackCompletedDottedCupQ
    (x : downStrandRevQ k sc i h₂ ⟶ downStrandRevQ k sc i h₂)
    (hx : homTrQ x = dnDotQ (sc := sc) i ν) (m : ℕ) :
    (((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit ≫
      powComp ((blackActionCompletedQ sc P hP).map₂ x) m ▷ (blackActionCompletedQ sc P hP).map _
      ).toNatTrans =
    eqToHom (completionMap_blackAct_nil P hP ν).symm ≫
      completionMap₂ (blackMapQ P hP (wt_nil RD ν) (wt_up_dn RD i ν) (CLQ.cupUp RD k sc i ν m)) ≫
      eqToHom (completionMap_blackAct_up_dn P hP i h₂ h₂').symm := by
  have e := sp_map₂_dottedCup (blackActionCompletedQ sc P hP) (downStrandAdjQ k sc i h₂) x m
  have e' : (((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit ≫
      powComp ((blackActionCompletedQ sc P hP).map₂ x) m ▷ (blackActionCompletedQ sc P hP).map _) =
      eqToHom ((blackActionCompletedQ sc P hP).map_id _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ ((downStrandAdjQ k sc i h₂).unit ≫
          powComp x m ▷ downStrandDualRevQ k sc i h₂) ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _) := by
    rw [e]; simp
  rw [e', Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans]
  have hm : ((blackActionCompletedQ sc P hP).map₂ ((downStrandAdjQ k sc i h₂).unit ≫
      powComp x m ▷ downStrandDualRevQ k sc i h₂)).toNatTrans =
      completionMap₂ (blackMapQ P hP (wt_nil RD ν) (wt_up_dn RD i ν)
        (CLQ.cupUp RD k sc i ν m)) :=
    congrArg (fun t => completionMap₂ (blackMapQ P hP (wt_nil RD ν) (wt_up_dn RD i ν) t))
      (homTrQ_cupQ i h₂ x hx m)
  rw [hm]

/-- **The rightward crossing in the completed black action** (Brundan, (1.6)), built from the
image adjunctions and the image of a crossing of two downward strands, is the completed action
of `CLQ.sigmaUpLs`. -/
theorem toNatTrans_blackCompletedSigmaQ
    (τ : downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂)
    (hτ : homTrQ τ = dnCrossQ (sc := sc) i μ) :
    (RightwardCrossing.sigma
      (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
      (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
      (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
      ).toNatTrans =
    eqToHom (completionMap_blackAct_dn_up P hP i h₁ h₁') ≫
      completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_up_dn RD i ν)
        (NF.dg (CLQ.pres RD k sc) ν [dn i, up i] [up i, dn i] (CLQ.sigmaUpLs i))) ≫
      eqToHom (completionMap_blackAct_up_dn P hP i h₂ h₂').symm := by
  have e := sp_map₂_sigma_mapAdjunction (blackActionCompletedQ sc P hP)
    (downStrandAdjQ k sc i h₁) (downStrandAdjQ k sc i h₂) τ
  have e' : RightwardCrossing.sigma
      (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
      (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
      (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit =
      eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ (RightwardCrossing.sigma
          (downStrandAdjQ k sc i h₂).unit τ (downStrandAdjQ k sc i h₁).counit) ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _) := by
    rw [e]; simp
  rw [e', Cat.Hom.toNatTrans_comp, Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans]
  have hm : ((blackActionCompletedQ sc P hP).map₂ (RightwardCrossing.sigma
      (downStrandAdjQ k sc i h₂).unit τ (downStrandAdjQ k sc i h₁).counit)).toNatTrans =
      completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_up_dn RD i ν)
        (NF.dg (CLQ.pres RD k sc) ν [dn i, up i] [up i, dn i] (CLQ.sigmaUpLs i))) :=
    congrArg (fun t => completionMap₂ (blackMapQ P hP (wt_dn_up RD i ν) (wt_up_dn RD i ν) t))
      (homTrQ_sigma_downStrandQ i h₁ h₂ τ hτ)
  rw [hm]

/-- **Brundan (1.8) in the completed black action, for the image adjunctions** (`⟨i, ν⟩ ≤ 0`):
minus the rightward crossing built from the units and counits of the image of `E_i ⊣ F_i`, with
the dotted caps of the image adjunction, has an explicit inverse. This is
`blackCompletedSumInvTo_sigmaUpQ` transported along `map_comp` and `map_id`. -/
def blackCompletedSigmaSumInvToQ
    (x : downStrandRevQ k sc i h₁ ⟶ downStrandRevQ k sc i h₁)
    (hx : homTrQ x = dnDotQ (sc := sc) i μ)
    (τ : downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂)
    (hτ : homTrQ τ = dnCrossQ (sc := sc) i μ) (hn : ip RD i ν ≤ 0) :
    SumInvTo
      (-(show completionMap (blackAct P [(true, i)] h₁') ⋙
          completionMap (blackAct P [(false, i)] h₁) ⟶
        completionMap (blackAct P [(false, i)] h₂) ⋙ completionMap (blackAct P [(true, i)] h₂')
        from (RightwardCrossing.sigma
      (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
      (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
      (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
      ).toNatTrans))
      (fun m => (show completionMap (blackAct P [(true, i)] h₁') ⋙
          completionMap (blackAct P [(false, i)] h₁) ⟶ 𝟭 _ from
        ((blackActionCompletedQ sc P hP).map _ ◁
          powComp ((blackActionCompletedQ sc P hP).map₂ x) m ≫
        ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
        ).toNatTrans))
      (-ip RD i ν).toNat :=
  ((blackCompletedSumInvTo_sigmaUpQ P hP i ν hn).congr
      (by rw [blackMap_negQ, completionMap₂_neg]) rfl rfl).conj
    (eqToIso (completionMap_blackAct_dn_up P hP i h₁ h₁'))
    (eqToIso (completionMap_blackAct_up_dn P hP i h₂ h₂').symm)
    (eqToIso (completionMap_blackAct_nil P hP ν))
    (by rw [toNatTrans_blackCompletedSigmaQ P hP i h₁ h₁' h₂ h₂' τ hτ]; simp)
    (fun m => by rw [toNatTrans_blackCompletedDottedCapQ P hP i h₁ h₁' x hx m]; simp)

/-- **Brundan (1.9) in the completed black action, for the image adjunctions** (`0 ≤ ⟨i, ν⟩`):
minus the rightward crossing, with the dotted cups of the image adjunction, has an explicit
inverse. This is `blackCompletedSumInvFrom_sigmaUpQ` transported along `map_comp` and
`map_id`. -/
def blackCompletedSigmaSumInvFromQ
    (x : downStrandRevQ k sc i h₂ ⟶ downStrandRevQ k sc i h₂)
    (hx : homTrQ x = dnDotQ (sc := sc) i ν)
    (τ : downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂ ⟶
      downStrandRevQ k sc i h₁ ≫ downStrandRevQ k sc i h₂)
    (hτ : homTrQ τ = dnCrossQ (sc := sc) i μ) (hn : 0 ≤ ip RD i ν) :
    SumInvFrom
      (-(show completionMap (blackAct P [(true, i)] h₁') ⋙
          completionMap (blackAct P [(false, i)] h₁) ⟶
        completionMap (blackAct P [(false, i)] h₂) ⋙ completionMap (blackAct P [(true, i)] h₂')
        from (RightwardCrossing.sigma
      (E₁ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₁))
      (E₂ := (blackActionCompletedQ sc P hP).map (downStrandRevQ k sc i h₂))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit
      (eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _).symm ≫
        (blackActionCompletedQ sc P hP).map₂ τ ≫
        eqToHom ((blackActionCompletedQ sc P hP).map_comp _ _))
      ((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₁)).counit
      ).toNatTrans))
      (fun m => (show 𝟭 _ ⟶ completionMap (blackAct P [(false, i)] h₂) ⋙
          completionMap (blackAct P [(true, i)] h₂') from
        (((blackActionCompletedQ sc P hP).mapAdjunction (downStrandAdjQ k sc i h₂)).unit ≫
          powComp ((blackActionCompletedQ sc P hP).map₂ x) m ▷
            (blackActionCompletedQ sc P hP).map _).toNatTrans))
      (ip RD i ν).toNat :=
  ((blackCompletedSumInvFrom_sigmaUpQ P hP i ν hn).congr
      (by rw [blackMap_negQ, completionMap₂_neg]) rfl rfl).conj
    (eqToIso (completionMap_blackAct_up_dn P hP i h₂ h₂').symm)
    (eqToIso (completionMap_blackAct_dn_up P hP i h₁ h₁'))
    (eqToIso (completionMap_blackAct_nil P hP ν).symm)
    (by rw [toNatTrans_blackCompletedSigmaQ P hP i h₁ h₁' h₂ h₂' τ hτ]; simp)
    (fun m => by rw [toNatTrans_blackCompletedDottedCupQ P hP i h₂ h₂' x hx m]; simp)

end Categorification.Stendhal.DoubleDiagram
