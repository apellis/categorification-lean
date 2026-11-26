/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissiblePull
import Categorification.TwoRep.RouqFullCL
import Categorification.WeightedKLR.RedStrands.DoubleBlackRelabel

/-!
# Black double diagrams in a Rouquier family

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25. For a Rouquier family `S` and images
of the red strands, the double signature has the model in which a black strand acts as in the
model of the Khovanov–Lauda signature, after relabelling it by its dual: an upward black strand
`i` acts by `F_i`, a downward one by `E_i` (`doubleModel`). The black generators act by the
images of the corresponding KL generators (`blackImg`; `BlackOn`).

If the Cautis–Lauda presentation with scalars `Sc` acts through `S` and is the presentation of
Khovanov–Lauda III, the reflected KL relations imposed on double diagrams (Definition 4.24) act
by zero for all generator images that are black on the black generators
(`admissibleMap_blackMirror_rel`). The proof relabels the reflected relations as KL relations
reflected with inverted orientations (`blackMirrorLinear_eq`), which vanish in `U`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w₁ v₁ u₁ w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

local notation "T" => signature RD Λ

section HEq

variable {S : Signature} {B : Type*} [Bicategory B] {k : Type*} [CommRing k]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

/-- Generator images over two models with the same objects and equal strand images that agree
up to heterogeneous equality have the same admissible interpretation. -/
theorem admissibleMap_eq_zero_of_strand_heq {obj : S.Region → B}
    {s₁ s₂ : (c : S.Colour) → (x y : S.Region) → S.colourTgt c = x → S.colourSrc c = y →
      (obj x ⟶ obj y)} (h : s₁ = s₂) {G₁ : GenImg (⟨obj, s₁⟩ : Model S B)}
    {G₂ : GenImg (⟨obj, s₂⟩ : Model S B)}
    (hG : ∀ g a b ha hb hd hde hc hce,
      G₁.gen g a b ha hb hd hde hc hce ≍ G₂.gen g a b ha hb hd hde hc hce)
    {s t : S.Region} {a b : Obj S} (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b)
    (hf : admissibleMap G₂ ha hb f = 0) : admissibleMap G₁ ha hb f = 0 := by
  subst h
  obtain rfl : G₁ = G₂ := by
    cases G₁; cases G₂; congr
    funext g a b ha hb hd hde hc hce
    exact eq_of_heq (hG g a b ha hb hd hde hc hce)
  exact hf

/-- Admissible interpretations vanish on a retyped linear combination if they vanish on it. -/
theorem admissibleMap_cast_eq_zero {M : Model S B} (G : GenImg M) {s t : S.Region}
    {a b a' b' : Obj S} (f : LinDiagram k a b) (ea : a = a') (eb : b = b')
    (ha : Cond s t a') (hb : Cond s t b') (hf : admissibleMap G (ea ▸ ha) (eb ▸ hb) f = 0) :
    admissibleMap G ha hb (LinDiagram.cast f ea eb) = 0 := by
  subst ea eb
  rw [LinDiagram.cast_rfl]
  exact hf

end HEq

section Model

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))

theorem up_step {z x y : X} (i : I) (hx : z + DoubleStrand.weight RD Λ (.inl (true, i)) = x)
    (hy : z = y) : y + RD.iX i = x := by
  subst hx hy; simp [DoubleStrand.weight]

theorem down_step {z x y : X} (i : I) (hx : z + DoubleStrand.weight RD Λ (.inl (false, i)) = x)
    (hy : z = y) : x + RD.iX i = y := by
  subst hx hy; simp [DoubleStrand.weight]

theorem red_step {z x y : X} (r : Fin ℓ) (hx : z + DoubleStrand.weight RD Λ (.inr r) = x)
    (hy : z = y) : y + Λ r = x := by
  subst hx hy; rfl

/-- The image of a double strand: an upward black strand `i` acts by `F_i`, a downward one by
`E_i`, a red strand `r` by the given image. -/
def doubleStrandImg : (c : X × DoubleStrand I ℓ) → (x y : X) → (T).colourTgt c = x →
    (T).colourSrc c = y → (S.obj x ⟶ S.obj y)
  | (_, .inl (true, i)), _, _, hx, hy => S.F i (up_step i hx hy)
  | (_, .inl (false, i)), _, _, hx, hy => S.E i (down_step i hx hy)
  | (_, .inr r), _, _, hx, hy => red r (red_step r hx hy)

/-- **The model of the double signature** given by a Rouquier family and images of the red
strands. -/
def doubleModel : Model T B where
  obj := S.obj
  strandAt := doubleStrandImg S red

/-- The pullback of the double model along the relabelling is the KL model. -/
theorem doubleModel_pull_strand :
    ((doubleModel S red).pull (blackRelabel RD Λ).toColourMap).strandAt = S.strandImg := by
  funext c x y hx hy
  obtain ⟨⟨_ | _, i⟩, r⟩ := c <;> rfl

end Model

section Gen

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (Sc : CL.CLScalars C k)

omit [AdditiveWhiskering B] in
/-- The upward crossing depends only on its outer regions. -/
theorem cross_heq (i j : I) {a b c d a₂ b₂ c₂ d₂ : X} (ha : a = a₂) (hd : d = d₂)
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d) (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d)
    (h₁' : a₂ + RD.iX j = b₂) (h₂' : b₂ + RD.iX i = d₂) (h₃' : a₂ + RD.iX i = c₂)
    (h₄' : c₂ + RD.iX j = d₂) :
    S.cross i j h₁ h₂ h₃ h₄ ≍ S.cross i j h₁' h₂' h₃' h₄' := by
  subst ha hd
  obtain rfl := h₁.symm.trans h₁'
  obtain rfl := h₃.symm.trans h₃'
  rfl

/-- The downward crossing depends only on its outer regions. -/
theorem crossDn_heq (i j : I) {a n n' b a₂ n₂ n₂' b₂ : X} (ha : a = a₂) (hb : b = b₂)
    (hj : n' + RD.iX j = b) (hi : a + RD.iX i = n') (hi' : n + RD.iX i = b)
    (hj' : a + RD.iX j = n) (hj₂ : n₂' + RD.iX j = b₂) (hi₂ : a₂ + RD.iX i = n₂')
    (hi₂' : n₂ + RD.iX i = b₂) (hj₂' : a₂ + RD.iX j = n₂) :
    S.crossDn Sc i j hj hi hi' hj' ≍ S.crossDn Sc i j hj₂ hi₂ hi₂' hj₂' := by
  subst ha hb
  obtain rfl := hi.symm.trans hi₂
  obtain rfl := hj'.symm.trans hj₂'
  rfl

omit [AdditiveWhiskering B] in
/-- The unit of `E ⊣ F` depends only on its left region. -/
theorem adj_unit_heq (i : I) {x y x₂ y₂ : X} (hx : x = x₂)
    (h : x + RD.iX i = y) (h' : x₂ + RD.iX i = y₂) :
    (S.adj i h).unit ≍ (S.adj i h').unit := by
  subst hx; obtain rfl := h.symm.trans h'; rfl

/-- The unit of `F ⊣ E` depends only on its left region. -/
theorem adjL_unit_heq (i : I) {x y x₂ y₂ : X} (hy : y = y₂)
    (h : x + RD.iX i = y) (h' : x₂ + RD.iX i = y₂) :
    (S.adjL i h).unit ≍ (S.adjL i h').unit := by
  subst hy; obtain rfl := add_right_cancel (h.trans h'.symm); rfl

omit [AdditiveWhiskering B] in
/-- The counit of `E ⊣ F` depends only on its region. -/
theorem adj_counit_heq (i : I) {x y x₂ y₂ : X} (hy : y = y₂)
    (h : x + RD.iX i = y) (h' : x₂ + RD.iX i = y₂) :
    (S.adj i h).counit ≍ (S.adj i h').counit := by
  subst hy; obtain rfl := add_right_cancel (h.trans h'.symm); rfl

/-- The counit of `F ⊣ E` depends only on its region. -/
theorem adjL_counit_heq (i : I) {x y x₂ y₂ : X} (hx : x = x₂)
    (h : x + RD.iX i = y) (h' : x₂ + RD.iX i = y₂) :
    (S.adjL i h).counit ≍ (S.adjL i h').counit := by
  subst hx; obtain rfl := h.symm.trans h'; rfl

/-- The images of the black generators of the double signature: those of the KL generators
with dual labels between the same regions. -/
def blackImg : (z : X) → (s : Shape I) → (a b : X) → (T).left (z, .black s) = a →
    (T).right (z, .black s) = b → (hd : (T).ok a ((T).dom (z, .black s))) →
    (hde : (T).endR a ((T).dom (z, .black s)) = b) → (hc : (T).ok a ((T).cod (z, .black s))) →
    (hce : (T).endR a ((T).cod (z, .black s)) = b) →
    ((doubleModel S red).word a ((T).dom (z, .black s)) b hd hde ⟶
      (doubleModel S red).word a ((T).cod (z, .black s)) b hc hce)
  | _, .dot (true, i), _, _, _, _, _, _, _, _ => S.dotDn i _
  | _, .dot (false, i), _, _, _, _, _, _, _, _ => S.dot i _
  | _, .cross true i j, _, _, _, _, _, _, _, _ => S.crossDn Sc i j _ _ _ _
  | _, .cross false i j, _, _, _, _, _, _, _, _ => S.cross i j _ _ _ _
  | _, .cup (true, i), _, _, _, _, _, hde, _, _ => by
      subst hde
      exact (S.adj i _).unit
  | _, .cup (false, i), _, _, _, _, _, hde, _, _ => by
      subst hde
      exact (S.adjL i _).unit
  | _, .cap (true, i), _, _, _, _, _, _, _, hce => by
      subst hce
      exact (S.adj i _).counit
  | _, .cap (false, i), _, _, _, _, _, _, _, hce => by
      subst hce
      exact (S.adjL i _).counit

theorem blackImg_cup_up (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {y : X}
    (h : a + RD.iX i = y) :
    blackImg S red Sc z (.cup (true, i)) a b ha hb hd hde hc hce ≍ (S.adj i h).unit := by
  subst hde; exact adj_unit_heq S i rfl _ h

theorem blackImg_cup_dn (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x : X}
    (h : x + RD.iX i = a) :
    blackImg S red Sc z (.cup (false, i)) a b ha hb hd hde hc hce ≍ (S.adjL i h).unit := by
  subst hde; exact adjL_unit_heq S i rfl _ h

theorem blackImg_cap_up (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {x : X}
    (h : x + RD.iX i = b) :
    blackImg S red Sc z (.cap (true, i)) a b ha hb hd hde hc hce ≍ (S.adj i h).counit := by
  subst hce; exact adj_counit_heq S i rfl _ h

theorem blackImg_cap_dn (z : X) (i : I) {a b : X} (ha hb hd hde hc hce) {y : X}
    (h : b + RD.iX i = y) :
    blackImg S red Sc z (.cap (false, i)) a b ha hb hd hde hc hce ≍ (S.adjL i h).counit := by
  subst hce; exact adjL_counit_heq S i rfl _ h

theorem genImg_cup_up (i : I) (r : X) {a b : X} (ha hb hd hde hc hce) {x : X}
    (h : x + RD.iX i = a) :
    (S.genImg Sc).gen (.cup ⟨(true, i), r⟩) a b ha hb hd hde hc hce ≍ (S.adjL i h).unit := by
  subst hde; exact adjL_unit_heq S i rfl _ h

theorem genImg_cup_dn (i : I) (r : X) {a b : X} (ha hb hd hde hc hce) {y : X}
    (h : a + RD.iX i = y) :
    (S.genImg Sc).gen (.cup ⟨(false, i), r⟩) a b ha hb hd hde hc hce ≍ (S.adj i h).unit := by
  subst hde; exact adj_unit_heq S i rfl _ h

theorem genImg_cap_up (i : I) (r : X) {a b : X} (ha hb hd hde hc hce) {y : X}
    (h : b + RD.iX i = y) :
    (S.genImg Sc).gen (.cap ⟨(true, i), r⟩) a b ha hb hd hde hc hce ≍ (S.adjL i h).counit := by
  subst hce; exact adjL_counit_heq S i rfl _ h

theorem genImg_cap_dn (i : I) (r : X) {a b : X} (ha hb hd hde hc hce) {x : X}
    (h : x + RD.iX i = b) :
    (S.genImg Sc).gen (.cap ⟨(false, i), r⟩) a b ha hb hd hde hc hce ≍ (S.adj i h).counit := by
  subst hce; exact adj_counit_heq S i rfl _ h

variable {S red} in
/-- Generator images of the double signature that are those of `S` on the black generators. -/
def BlackOn (G : GenImg (doubleModel S red)) : Prop :=
  ∀ z s a b ha hb hd hde hc hce,
    G.gen (z, .black s) a b ha hb hd hde hc hce = blackImg S red Sc z s a b ha hb hd hde hc hce

end Gen

section Relations

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
  (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)

include H M hr hq in
/-- The admissible interpretation of the KL model of a Rouquier family kills every linear
combination of diagrams that vanishes in the Cautis–Lauda presentation. -/
theorem admissibleMap_genImg_eq_zero [DecidableEq I] {s t : X} {a b : Obj (psig RD)}
    (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b)
    (hf : (CL.presCL RD k Sc).lin f = 0) : admissibleMap (S.genImg Sc) ha hb f = 0 := by
  have h := ((CL.presCL RD k Sc).lin_eq_iff f 0).1 (by rw [hf, Presentation.lin_zero])
  rw [sub_zero] at h
  exact S.presCL_ideal Sc H M hr hq ha hb f h

/-- A double object that is the relabelling of a reflected well-formed KL object gives the
boundary condition of the reflected KL object. -/
theorem cond_thetaObj {s t : X} {a : Obj (psig RD)} (hwf : a.WF)
    (h : Cond s t ((blackRelabel RD Λ).obj (thetaObj a))) : Cond s t (thetaObj a) := by
  have hθ : (thetaObj a).WF :=
    (Sig.ok_word (RD := RD) _ _ (Omega.ok_word (RD := RD) a.start a.word hwf).1).1
  refine ⟨h.2.2 ▸ hθ, ?_, h.2.2⟩
  exact (endR_map' (blackRelabel RD Λ).toColourMap s (thetaObj a).word).symm.trans h.2.1

variable (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))

include H M hr hq in
/-- **The reflected KL relations act by zero** on double diagrams, for generator images that
are those of a Rouquier family on the black generators, when the Cautis–Lauda presentation
with the scalars `Sc` is the presentation of KL III. -/
theorem admissibleMap_blackMirror_rel [DecidableEq I] (hSc : CL.presCL RD k Sc = pres RD k)
    {G : GenImg (doubleModel S red)} (hG : BlackOn Sc G) (r : (pres RD k).Rel) {s t : X}
    (ha : Cond s t ((blackMirror RD Λ).obj ((pres RD k).dom r)))
    (hb : Cond s t ((blackMirror RD Λ).obj ((pres RD k).cod r))) :
    admissibleMap G ha hb (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0 := by
  have hwa := pres_dom_wf (k := k) r
  have hwb := pres_cod_wf (k := k) r
  rw [blackMirrorLinear_eq RD Λ hwa hwb]
  refine admissibleMap_cast_eq_zero G _ _ _ ha hb ?_
  have ha' := cond_thetaObj hwa ((blackMirror_obj_eq RD Λ hwa) ▸ ha)
  have hb' := cond_thetaObj hwb ((blackMirror_obj_eq RD Λ hwb) ▸ hb)
  refine admissibleMap_pull_eq_zero (blackRelabel RD Λ) G ha' hb' _ ?_
  refine admissibleMap_eq_zero_of_strand_heq (doubleModel_pull_strand S red)
    (G₂ := S.genImg Sc) ?_ ha' hb' _ ?_
  · intro g a b ha hb hd hde hc hce
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (heq_of_eq (hG _ _ _ _ _ _ _ _ _ _)).trans ?_
    rcases g with (⟨⟨⟨_ | _, i⟩, r⟩⟩ | ⟨_ | _, i, j, ν⟩) | ⟨⟨_ | _, i⟩, r⟩ | ⟨⟨_ | _, i⟩, r⟩
    · exact HEq.rfl
    · exact HEq.rfl
    · obtain rfl : ν = b := hde
      exact crossDn_heq S Sc i j rfl rfl _ _ _ _ _ _ _ _
    · obtain rfl : ν = b := hde
      exact cross_heq S i j rfl rfl _ _ _ _ _ _ _ _
    · exact (blackImg_cup_up S red Sc _ i _ _ _ _ _ _ (RouqFamily.dn_reg i rfl ha)).trans
        (genImg_cup_dn S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cup_dn S red Sc _ i _ _ _ _ _ _ (RouqFamily.up_reg i rfl ha)).trans
        (genImg_cup_up S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cap_up S red Sc _ i _ _ _ _ _ _ (RouqFamily.dn_reg i hde rfl)).trans
        (genImg_cap_dn S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cap_dn S red Sc _ i _ _ _ _ _ _ (RouqFamily.up_reg i hde rfl)).trans
        (genImg_cap_up S Sc i r _ _ _ _ _ _ _).symm
  · refine admissibleMap_genImg_eq_zero S Sc H M hr hq ha' hb' _ ?_
    rw [hSc]
    exact lin_thetaLin_eq_zero (Presentation.lin_rel_self _ r)

end Relations

end Categorification.Stendhal.DoubleDiagram
