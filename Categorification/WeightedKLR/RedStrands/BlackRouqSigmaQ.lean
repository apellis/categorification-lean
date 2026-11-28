/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackRestrictionQ
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackNewStrandQ
import Categorification.WeightedKLR.RedStrands.BlackRouqInversionQ
import Categorification.TwoRep.RightwardCrossingPush

/-!
# The rightward crossing of the downward black strands is Cautis–Lauda's sideways crossing

Brundan, arXiv:1501.00350v1, (1.6), for the downward strands `F_i` of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) with the adjunction
`E_i ⊣ F_i` by which the black action of Webster, arXiv:1309.3796v3, §4.6, makes induction left
adjoint to restriction (`blackCompletedAdjunctionQ`).

* `RevBicat.sigma_diag`: in the 1-cell dual of a presented bicategory, the rightward crossing
  built from classes of diagrams is the class of a diagram whose layers are those of the cup
  (whiskered on the right), of the crossing (whiskered on both sides) and of the cap (whiskered
  on the left).
* `homTrQ_sigma_downStrandQ`: the rightward crossing built from the downward crossing of two
  downward strands, with the cup and the cap of `E_i ⊣ F_i`, is the diagram `CLQ.sigmaUpLs`, which
  is Cautis–Lauda's sideways crossing `crossr` (`CLQ.dg_sigmaUpLs`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open CategoryTheory Bicategory StringDiagrams Presentation

namespace RevBicat

section Diag

variable {S : Signature} [S.IsEven] {R : Type*} [CommRing R] (Pr : Presentation S R)

omit [S.IsEven] in
/-- A composite of morphisms that are classes of diagrams is the class of the composite. -/
theorem comp_eq_diag_of {a b c : Obj S} {f : Pr.obj a ⟶ Pr.obj b} {g : Pr.obj b ⟶ Pr.obj c}
    {d : a ⟶ b} {e : b ⟶ c} (hf : f = Pr.diag d) (hg : g = Pr.diag e) :
    f ≫ g = Pr.diag (d ≫ e) := by
  rw [hf, hg, Pr.diag_comp]

omit [S.IsEven] in
/-- Two diagrams with the same layers, the first framed by transports, have the same class. -/
theorem diag_conj_eq' {a b c c' : Obj S} (D₁ : a ⟶ b) (D₂ : c ⟶ c')
    (h₁ : Pr.obj c = Pr.obj a) (h₂ : Pr.obj b = Pr.obj c')
    (hl : Diagram.layers D₁ = Diagram.layers D₂) :
    eqToHom h₁ ≫ Pr.diag D₁ ≫ eqToHom h₂ = Pr.diag D₂ := by
  simpa using Stendhal.DoubleDiagram.diag_conj_eq Pr D₁ D₂ h₁ h₂ rfl rfl hl

theorem eqToHom_eq_diag {a b : RevBicat Pr.Bicat} {x y : a ⟶ b} (h : x = y) :
    eqToHom h = (Pr.diag (eqToHom (congrArg Bicat.Hom.obj h)) : x ⟶ y) := by
  subst h; exact Bicat.id_eq_diag Pr x

/-- **The rightward crossing of classes of diagrams** in `RevBicat Pr.Bicat` is the class of a
diagram with the layers of the cup on the left, the crossing in the middle and the cap on the
right. -/
theorem sigma_diag {a b c : RevBicat Pr.Bicat} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a}
    {R₂ : c ⟶ b} (cup : Bicat.Hom.obj (𝟙 b) ⟶ Bicat.Hom.obj (E₂ ≫ R₂))
    (t : Bicat.Hom.obj (E₁ ≫ E₂) ⟶ Bicat.Hom.obj (E₁ ≫ E₂))
    (cap : Bicat.Hom.obj (R₁ ≫ E₁) ⟶ Bicat.Hom.obj (𝟙 b)) :
    ∃ D : Bicat.Hom.obj (R₁ ≫ E₁) ⟶ Bicat.Hom.obj (E₂ ≫ R₂),
      (TwoRep.RightwardCrossing.sigma (C := RevBicat Pr.Bicat) (E₁ := E₁) (E₂ := E₂) (R₁ := R₁)
        (R₂ := R₂) (Pr.diag cup : 𝟙 b ⟶ E₂ ≫ R₂) (Pr.diag t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
        (Pr.diag cap : R₁ ≫ E₁ ⟶ 𝟙 b) : Pr.obj (Bicat.Hom.obj (R₁ ≫ E₁)) ⟶
          Pr.obj (Bicat.Hom.obj (E₂ ≫ R₂))) = Pr.diag D ∧
      Diagram.layers D = (Diagram.layers cup).map (·.wr (Bicat.Hom.obj (R₁ ≫ E₁)).word) ++
        (Diagram.layers t).map (fun L => (L.wl (Bicat.Hom.obj R₂)).wr (Bicat.Hom.obj R₁).word) ++
        (Diagram.layers cap).map (·.wl (Bicat.Hom.obj (E₂ ≫ R₂))) := by
  refine ⟨?D, ?h1, ?h2⟩
  case h1 =>
    simp only [TwoRep.RightwardCrossing.sigma_eq, RevBicat.whiskerLeft_def,
      RevBicat.whiskerRight_def, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
    simp only [eqToHom_eq_diag]
    simp only [Bicat.whiskerLeft_diag, Bicat.diag_whiskerRight]
    repeat' (first | exact rfl | refine' comp_eq_diag_of Pr rfl ?_)
  case h2 =>
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_rwhisker,
      Diagram.layers_lwhisker, List.map_nil, List.nil_append, List.append_nil, List.map_map,
      List.append_assoc]
    rfl

/-- Powers of the class of a one-layer diagram. -/
theorem powComp_diag {a b : RevBicat Pr.Bicat} {x : a ⟶ b}
    (d : Bicat.Hom.obj x ⟶ Bicat.Hom.obj x) {L : Layer S} (hd : Diagram.layers d = [L]) (m : ℕ) :
    ∃ D : Bicat.Hom.obj x ⟶ Bicat.Hom.obj x,
      (TwoRep.powComp (Pr.diag d : x ⟶ x) m : x ⟶ x) = (Pr.diag D : x ⟶ x) ∧
        Diagram.layers D = List.replicate m L := by
  induction m with
  | zero => exact ⟨𝟙 _, (Pr.diag_id _).symm, rfl⟩
  | succ m ih =>
    obtain ⟨D, hD, hL⟩ := ih
    refine ⟨D ≫ d, ?_, ?_⟩
    · rw [TwoRep.powComp_succ]
      exact comp_eq_diag_of Pr hD rfl
    · rw [Diagram.layers_comp, hL, hd, List.replicate_succ']

/-- A cap after a 2-morphism on its right strand (`R ◁ x ≫ ε`), for classes of diagrams. -/
theorem whiskerLeft_comp_diag {a b : RevBicat Pr.Bicat} {E : a ⟶ b} {G : b ⟶ a}
    (d : Bicat.Hom.obj E ⟶ Bicat.Hom.obj E) (cap : Bicat.Hom.obj (G ≫ E) ⟶ Bicat.Hom.obj (𝟙 b)) :
    ∃ D : Bicat.Hom.obj (G ≫ E) ⟶ Bicat.Hom.obj (𝟙 b),
      ((G ◁ (Pr.diag d : E ⟶ E) ≫ (Pr.diag cap : G ≫ E ⟶ 𝟙 b) : G ≫ E ⟶ 𝟙 b) :
        Pr.obj _ ⟶ Pr.obj _) = Pr.diag D ∧
      Diagram.layers D = (Diagram.layers d).map (·.wr (Bicat.Hom.obj G).word) ++
        Diagram.layers cap := by
  refine ⟨?D, ?h1, ?h2⟩
  case h1 =>
    simp only [RevBicat.whiskerLeft_def, Bicat.diag_whiskerRight]
    repeat' (first | exact rfl | refine' comp_eq_diag_of Pr rfl ?_)
  case h2 =>
    simp only [Diagram.layers_comp, Diagram.layers_rwhisker]

/-- A cup followed by a 2-morphism on its left strand (`η ≫ x ▷ R`), for classes of diagrams. -/
theorem comp_whiskerRight_diag {a b : RevBicat Pr.Bicat} {E : a ⟶ b} {G : b ⟶ a}
    (cup : Bicat.Hom.obj (𝟙 a) ⟶ Bicat.Hom.obj (E ≫ G)) (d : Bicat.Hom.obj E ⟶ Bicat.Hom.obj E) :
    ∃ D : Bicat.Hom.obj (𝟙 a) ⟶ Bicat.Hom.obj (E ≫ G),
      (((Pr.diag cup : 𝟙 a ⟶ E ≫ G) ≫ (Pr.diag d : E ⟶ E) ▷ G : 𝟙 a ⟶ E ≫ G) :
        Pr.obj _ ⟶ Pr.obj _) = Pr.diag D ∧
      Diagram.layers D = Diagram.layers cup ++
        (Diagram.layers d).map (·.wl (Bicat.Hom.obj G)) := by
  refine ⟨?D, ?h1, ?h2⟩
  case h1 =>
    simp only [RevBicat.whiskerRight_def, Bicat.whiskerLeft_diag]
    repeat' (first | exact rfl | refine' comp_eq_diag_of Pr rfl ?_)
  case h2 =>
    simp only [Diagram.layers_comp, Diagram.layers_lwhisker]

end Diag

end RevBicat

namespace Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot KL3.Diagram TwoRep

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k] {sc : KL3.Diagram.CL.CLScalars C k}

section Bicat

variable {l m : (CLQ.pres RD k sc).Bicat} {f g : l ⟶ m}

/-- A 2-morphism whose normal form is the class of a diagram is itself the class of a diagram
with the same layers. -/
theorem exists_diag_of_homTrQ_eq {η : f ⟶ g} {D : ob RD m.region (homLettersQ f) ⟶
      ob RD m.region (homLettersQ g)} (h : homTrQ η = (CLQ.pres RD k sc).diag D) :
    ∃ D' : Bicat.Hom.obj f ⟶ Bicat.Hom.obj g,
      (η : (CLQ.pres RD k sc).obj _ ⟶ (CLQ.pres RD k sc).obj _) = (CLQ.pres RD k sc).diag D' ∧
        Diagram.layers D' = Diagram.layers D := by
  refine ⟨eqToHom (homObj_eqQ f) ≫ D ≫ eqToHom (homObj_eqQ g).symm, ?_, by simp⟩
  have e : (η : (CLQ.pres RD k sc).obj _ ⟶ (CLQ.pres RD k sc).obj _) =
      eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ f)) ≫ homTrQ η ≫
        eqToHom (congrArg (CLQ.pres RD k sc).obj (homObj_eqQ g)).symm := by
    simp [homTrQ]
  rw [e, h, (CLQ.pres RD k sc).eqToHom_obj, (CLQ.pres RD k sc).eqToHom_obj]
  repeat' (first | exact rfl | refine' RevBicat.comp_eq_diag_of _ rfl ?_)

end Bicat

variable (i : I)

/-- **The rightward crossing for `E_i ⊣ F_i` of two downward strands** (Brundan, (1.6)): built
from the cup `1 → E_i F_i` (the unit of `E_i ⊣ F_i`), a 2-morphism `τ` whose normal form is the
downward crossing of the two downward strands, and the cap `F_i E_i → 1` (its counit), it is the
diagram `CLQ.sigmaUpLs` (cup on the left, crossing of the downward strands, cap on the right),
which is Cautis–Lauda's sideways crossing `crossr` (`CLQ.dg_sigmaUpLs`). -/
theorem homTrQ_sigma_downStrandQ {μ ν ν₂ : X} (h₁ : wt RD μ [(false, i)] = ν)
    (h₂ : wt RD ν [(false, i)] = ν₂)
    (τ : RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₁) ≫
        RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₂) ⟶
      RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₁) ≫
        RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₂))
    (hτ : homTrQ τ = dnCrossQ (sc := sc) i μ) :
    homTrQ (RightwardCrossing.sigma (E₁ := RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₁))
        (E₂ := RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₂))
        (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h₂)
          ⟨dn i, ν⟩ rfl).right)).unit τ
        (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h₁)
          ⟨dn i, μ⟩ rfl).right)).counit) =
      NF.dg (CLQ.pres RD k sc) ν [dn i, up i] [up i, dn i] (CLQ.sigmaUpLs i) := by
  subst h₁ h₂
  obtain ⟨Dt, ht, hDt⟩ := exists_diag_of_homTrQ_eq hτ
  obtain ⟨Du, hu, hDu⟩ : ∃ D, (RevBicat.adjunction ((CLQ.biadjColour RD k sc
      (downStrandHomQ (k := k) i (rfl : wt RD (wt RD μ [(false, i)]) [(false, i)] = _))
      ⟨dn i, wt RD μ [(false, i)]⟩ rfl).right)).unit = (CLQ.pres RD k sc).diag D ∧
      Diagram.layers D = Diagram.layers (Pivotal.cupD (KL3.Diagram.inv RD).toColourDuality
        ((KL3.Diagram.inv RD).dual ⟨dn i, wt RD μ [(false, i)]⟩)) :=
    ⟨_, rfl, by simp [Diagram.layers_cast, pivotalCupsCaps]⟩
  obtain ⟨Dc, hc, hDc⟩ : ∃ D, (RevBicat.adjunction ((CLQ.biadjColour RD k sc
      (downStrandHomQ (k := k) i (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).counit =
        (CLQ.pres RD k sc).diag D ∧
      Diagram.layers D = Diagram.layers (Pivotal.capD (KL3.Diagram.inv RD).toColourDuality
        ((KL3.Diagram.inv RD).dual ⟨dn i, μ⟩)) :=
    ⟨_, rfl, by simp [Diagram.layers_cast, pivotalCupsCaps]⟩
  obtain ⟨D, hD, hL⟩ := RevBicat.sigma_diag (CLQ.pres RD k sc) Du Dt Dc
  have e : (RightwardCrossing.sigma
        (E₁ := RevBicat.of (downStrandHomQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _)))
        (E₂ := RevBicat.of (downStrandHomQ (k := k) (sc := sc) i
          (rfl : wt RD (wt RD μ [(false, i)]) [(false, i)] = _)))
        (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i
          (rfl : wt RD (wt RD μ [(false, i)]) [(false, i)] = _)) ⟨dn i, _⟩ rfl).right)).unit τ
        (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i
          (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).counit :
        (CLQ.pres RD k sc).obj _ ⟶ (CLQ.pres RD k sc).obj _) = (CLQ.pres RD k sc).diag D := by
    rw [← hD, ← hu, ← hc, ← ht]
  unfold homTrQ
  rw [e, NF.dg_of (by schain)]
  refine RevBicat.diag_conj_eq' (CLQ.pres RD k sc) D _ _ _ ?_
  rw [hL, hDu, hDc, hDt]
  simp only [layers_mkD]
  simp [CLQ.sigmaUpLs, Pivotal.cupD, Pivotal.capD, layList, lay, Layer.wl, Layer.wr,
    KL3.Diagram.wd, KL3.Diagram.wt, KL3.Diagram.inv, Shape.gen, Shape.dom]
  exact ⟨rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- **The dotted cap `F_i E_i → 1` as a 2-morphism** (`R₁ ◁ x^m ≫ ε₁`): the counit of `E_i ⊣ F_i`
after `m` powers of a 2-morphism whose normal form is the dot on the downward strand is
`CLQ.capUp` (`m` dots on the downward strand of the cap). -/
theorem homTrQ_capQ {μ ν : X} (h₁ : wt RD μ [(false, i)] = ν)
    (x : RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₁) ⟶
      RevBicat.of (downStrandHomQ (k := k) (sc := sc) i h₁))
    (hx : homTrQ x = dnDotQ (sc := sc) i μ) (m : ℕ) :
    homTrQ (RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
        (downStrandHomQ (k := k) (sc := sc) i h₁)) ◁ powComp x m ≫
      (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i h₁)
        ⟨dn i, μ⟩ rfl).right)).counit) = CLQ.capUp RD k sc i ν m := by
  subst h₁
  obtain ⟨Dx, hx', hDx⟩ := exists_diag_of_homTrQ_eq hx
  obtain ⟨Dc, hc, hDc⟩ : ∃ D, (RevBicat.adjunction ((CLQ.biadjColour RD k sc
      (downStrandHomQ (k := k) i (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).counit =
        (CLQ.pres RD k sc).diag D ∧
      Diagram.layers D = Diagram.layers (Pivotal.capD (KL3.Diagram.inv RD).toColourDuality
        ((KL3.Diagram.inv RD).dual ⟨dn i, μ⟩)) :=
    ⟨_, rfl, by simp [Diagram.layers_cast, pivotalCupsCaps]⟩
  obtain ⟨Dp, hp, hDp⟩ := RevBicat.powComp_diag (CLQ.pres RD k sc) Dx
    (hDx.trans (by simp only [layers_mkD, layList]; rfl)) m
  obtain ⟨D, hD, hL⟩ := RevBicat.whiskerLeft_comp_diag (CLQ.pres RD k sc)
    (G := RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
      (downStrandHomQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _)))) Dp Dc
  have e : (RevBicat.of ((CLQ.pres RD k sc).dualHom (KL3.Diagram.inv RD).pivotal
        (downStrandHomQ (k := k) (sc := sc) i (rfl : wt RD μ [(false, i)] = _))) ◁ powComp x m ≫
      (RevBicat.adjunction ((CLQ.biadjColour RD k sc (downStrandHomQ (k := k) i
        (rfl : wt RD μ [(false, i)] = _)) ⟨dn i, μ⟩ rfl).right)).counit :
        (CLQ.pres RD k sc).obj _ ⟶ (CLQ.pres RD k sc).obj _) = (CLQ.pres RD k sc).diag D := by
    rw [← hD, ← hc, ← hp, ← hx']
    rfl
  unfold homTrQ
  erw [e]
  rw [CLQ.capUp, NF.dg_of (by schain)]
  refine RevBicat.diag_conj_eq' (CLQ.pres RD k sc) D _ _ _ ?_
  rw [hL, hDp, hDc]
  simp [dotCapFELs, Pivotal.capD, layList, lay, Layer.wr,
    KL3.Diagram.wd, KL3.Diagram.wt, KL3.Diagram.inv, Shape.gen, Shape.dom, List.map_replicate]
  exact Or.inr rfl

end Stendhal.DoubleDiagram

end Categorification
