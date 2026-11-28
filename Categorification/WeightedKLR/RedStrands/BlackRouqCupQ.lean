/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqSigmaQ

/-!
# The dotted cup of `E_i ⊣ F_i` for the downward black strands

Brundan, arXiv:1501.00350v1, (1.9), for the downward strands `F_i` of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) with the adjunction
`E_i ⊣ F_i` of `blackCompletedAdjunctionQ` (Webster, arXiv:1309.3796v3, §4.6).

* `homTrQ_cupQ`: the unit of `E_i ⊣ F_i` followed by `m` powers of a 2-morphism whose normal
  form is the dot on the downward strand (`η ≫ x^m ▷ R`) is `CLQ.cupUp` (`m` dots on the
  downward strand of the cup). This is the summand of Rouquier's map for `⟨i, λ⟩ ≥ 0`; the
  summands for `⟨i, λ⟩ ≤ 0` are `homTrQ_capQ`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open CategoryTheory Bicategory StringDiagrams Presentation

namespace Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}

variable (i : I)

/-- **The dotted cup `1 → E_i F_i` as a 2-morphism** (`η ≫ x^m ▷ R`): the unit of `E_i ⊣ F_i`
followed by `m` powers of a 2-morphism whose normal form is the dot on the downward strand is
`CLQ.cupUp` (`m` dots on the downward strand of the cup). -/
theorem homTrQ_cupQ {μ ν : X} (h : wt RD μ [(false, i)] = ν)
    (x : RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h) ⟶
      RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h))
    (hx : homTrQ x = dnDotQ (sc := sc) i μ) (m : ℕ) :
    homTrQ ((RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h)
        ⟨dn i, μ⟩ rfl).right)).unit ≫ powComp x m ▷
      RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
        (downStrandHomQ (k := k) (sc := sc) i h))) = CLQ.cupUp RD k sc i μ m := by
  subst h
  obtain ⟨Dx, hx', hDx⟩ := exists_diag_of_homTrQ_eq hx
  obtain ⟨Du, hu, hDu⟩ : ∃ D, (RevBicat.adjunction ((CLQ.biadjColour RD k sc
      (downStrandHomQ (k := k) i (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).unit =
        (CLQ.pres RD k sc).diag D ∧
      Diagram.layers D = Diagram.layers (Pivotal.cupD (KL3.Diagram.inv RD).toColourDuality
        ((KL3.Diagram.inv RD).dual ⟨dn i, μ⟩)) :=
    ⟨_, rfl, by simp [Diagram.layers_cast, pivotalCupsCaps]⟩
  obtain ⟨Dp, hp, hDp⟩ := RevBicat.powComp_diag (CLQ.pres RD k sc) Dx
    (hDx.trans (by simp only [layers_mkD, layList]; rfl)) m
  obtain ⟨D, hD, hL⟩ := RevBicat.comp_whiskerRight_diag (CLQ.pres RD k sc)
    (G := RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
      (downStrandHomQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _)))) Du Dp
  have e : ((RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i
        (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).unit ≫ powComp x m ▷
      RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
        (downStrandHomQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _))) :
        (CLQ.pres RD k sc).obj _ ⟶ (CLQ.pres RD k sc).obj _) = (CLQ.pres RD k sc).diag D := by
    rw [← hD, ← hu, ← hp, ← hx']
    rfl
  unfold homTrQ
  erw [e]
  rw [CLQ.cupUp, NF.dg_of (by schain)]
  refine RevBicat.diag_conj_eq' (CLQ.pres RD k sc) D _ _ _ ?_
  rw [hL, hDp, hDu]
  simp [cupDotEFLs, Pivotal.cupD, layList, lay, Layer.wl,
    KL3.Diagram.wd, KL3.Diagram.wt, KL3.Diagram.inv, Shape.gen, Shape.dom, List.map_replicate]
  exact Or.inr rfl

end Stendhal.DoubleDiagram

end Categorification
