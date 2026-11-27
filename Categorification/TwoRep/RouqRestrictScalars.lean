/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqRestrictSig
import Categorification.TwoRep.RouqFullCL

/-!
# Restricting a Rouquier family with general Cautis–Lauda scalars

For a restriction datum `D` from `RD` (Cartan datum `C`) to `W` (Cartan datum `C'`) whose colour
map preserves the symmetrized pairing, the Cautis–Lauda scalars `Sc` of `C'` restrict to scalars
`D.scalars hdot Sc` of `C` (`t_ij = Sc.t (e i) (e j)`, and so on). Pulled back along the
relabelling `D.sigMap`, the generator images of a Rouquier family `S` for `W` with scalars `Sc`
agree with those of `S.restrict D` with the restricted scalars (`RestrictData.pull_eq_zeroQ`),
so the admissible interpretation of `S` kills the relabelled relations of `U_{Sc|}(g)` for `RD`
(`RestrictData.presCL_rel_restrict`). At Khovanov–Lauda scalars on the image of `e` these are
`RestrictData.pull_eq_zero` and `RestrictData.pres_rel_restrict`.

This is used for Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for general black
parameters.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory QuantumGroup UDot KL3.Diagram StringDiagrams
  Diagrams.BicatInterp

universe u₁

variable {I I' : Type*} {C : CartanDatum I} {C' : CartanDatum I'} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {W : WeightDatum C' X Y}

namespace RestrictData

variable (D : RestrictData RD W) (hdot : ∀ i j, C'.dot (D.e i) (D.e j) = C.dot i j)

/-- The Cautis–Lauda scalars of `C'` restricted along the colour map of `D`. -/
def scalars {k : Type*} [CommRing k] (Sc : CL.CLScalars C' k) : CL.CLScalars C k where
  t i j := Sc.t (D.e i) (D.e j)
  s i j := Sc.s (D.e i) (D.e j)
  r i := Sc.r (D.e i)
  t_self i := Sc.t_self _
  t_symm i j h := Sc.t_symm _ _ (by rw [hdot]; exact h)
  s_symm i j := Sc.s_symm _ _

@[simp] theorem scalars_t {k : Type*} [CommRing k] (Sc : CL.CLScalars C' k) (i j : I) :
    (D.scalars hdot Sc).t i j = Sc.t (D.e i) (D.e j) := rfl

@[simp] theorem scalars_s {k : Type*} [CommRing k] (Sc : CL.CLScalars C' k) (i j : I) :
    (D.scalars hdot Sc).s i j = Sc.s (D.e i) (D.e j) := rfl

@[simp] theorem scalars_r {k : Type*} [CommRing k] (Sc : CL.CLScalars C' k) (i : I) :
    (D.scalars hdot Sc).r i = Sc.r (D.e i) := rfl

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  (S : RouqFamily (B := B) W)

variable [AdditiveWhiskering B] {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]

/-- The downward crossings of the restriction with the restricted scalars are those of the
family. -/
theorem crossDn_restrictQ (Sc : CL.CLScalars C' k)
    (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b) (hi : a + RD.iX i = n')
    (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    (S.restrict D).crossDn (D.scalars hdot Sc) i j hj hi hi' hj' =
      S.crossDn Sc (D.e i) (D.e j) (D.step j hj) (D.step i hi) (D.step i hi') (D.step j hj') := by
  simp only [RouqFamily.crossDn, RouqFamily.restrict_adjL, scalars_t]
  rfl

/-- **The relabelling of the generator images, for general scalars.** A linear combination of
KL diagrams of `RD` killed by the admissible interpretation of `S.restrict D` with the restricted
scalars is killed by that of the pullback of `S` with the scalars `Sc` along `D.sigMap`. -/
theorem pull_eq_zeroQ (Sc : CL.CLScalars C' k)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b)
    (hf : admissibleMap ((S.restrict D).genImg (D.scalars hdot Sc)) ha hb f = 0) :
    admissibleMap ((S.genImg Sc).pull D.sigMap) ha hb f = 0 := by
  refine genImg_eq_of_strand (D.strand_pull S) ?_ ha hb f hf
  intro g a b ha hb hd hde hc hce
  rcases g with (⟨⟨⟨_ | _, i⟩, r⟩⟩ | ⟨_ | _, i, j, ν⟩) | ⟨⟨_ | _, i⟩, r⟩ | ⟨⟨_ | _, i⟩, r⟩
  · dsimp only [GenImg.pull, RouqFamily.genImg]
    rw [D.dotDn_restrict S]
    rfl
  · rfl
  · subst hde
    dsimp only [GenImg.pull, RouqFamily.genImg]
    rw [D.crossDn_restrictQ hdot S Sc]
    rw [S.crossDn_cast Sc _ _ (D.sh_letter_add (false, i) ν).symm
      (D.sh_letter_add (false, j) ν).symm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl
  · subst hde
    dsimp only [RouqFamily.genImg, RouqFamily.restrict]
    rw [S.cross_cast _ _ (D.sh_letter_add (true, j) ν).symm
      (D.sh_letter_add (true, i) ν).symm]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    rfl
  · subst hde
    rfl
  · subst hde
    dsimp only [RouqFamily.genImg]
    rw [RouqFamily.restrict_adjL]
    rfl
  · subst hce
    dsimp only [GenImg.pull, RouqFamily.genImg, RouqFamily.restrict, RestrictData.sigMap,
      RestrictData.gen, RestrictData.col, RestrictData.letter]
    exact S.adj_counit_region _ _ _ (by rw [D.dual_col]; rfl) _ _ _
  · subst hce
    dsimp only [GenImg.pull, RouqFamily.genImg, RestrictData.sigMap,
      RestrictData.gen, RestrictData.col, RestrictData.letter]
    rw [RouqFamily.restrict_adjL]
    exact S.adjL_counit_region _ _ _ (by rw [D.dual_col]; rfl) _ _ _

omit [AdditiveWhiskering B] in
/-- Brundan's polynomials of `Sc` on the image of `e` are those of the restricted scalars. -/
theorem brundanQ_restrictQ (Sc : CL.CLScalars C' k) (i j : I) :
    brundanQ Sc (D.e i) (D.e j) = brundanQ (D.scalars hdot Sc) i j := by
  have hd (a b : I) : C'.dij (D.e a) (D.e b) = C.dij a b := by
    simp only [QuantumGroup.CartanDatum.dij, hdot]
  unfold brundanQ
  rw [hdot, hd, hd]
  rfl

section Relations

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

/-- **The relabelled relations of `U_{Sc|}(g)` hold for `S`.** For a Rouquier family `S` for `W`
with Brundan's upward relations for `Sc`, `r = 1` and invertible mixed crossings, the admissible
interpretation of `S` with scalars `Sc` kills the relabelling along `D` of every defining
relation of the Cautis–Lauda presentation for `RD` with the restricted scalars. -/
theorem presCL_rel_restrict [DecidableEq I] [DecidableEq I'] (Sc : CL.CLScalars C' k)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (D.e i) (D.e j) p q = 0)
    (r : (CL.presCL RD k (D.scalars hdot Sc)).Rel) {s t : X}
    (ha : Cond (S := psig RD) s t ((CL.presCL RD k (D.scalars hdot Sc)).dom r))
    (hb : Cond (S := psig RD) s t ((CL.presCL RD k (D.scalars hdot Sc)).cod r)) :
    admissibleMap (S.genImg Sc) (Cond.map D.sigMap ha) (Cond.map D.sigMap hb)
      (D.sigMap.toLayerMap.lin ((CL.presCL RD k (D.scalars hdot Sc)).rel r)) = 0 :=
  admissibleMap_pull_eq_zero D.sigMap (S.genImg Sc) ha hb _
    (D.pull_eq_zeroQ hdot S Sc ha hb _ ((S.restrict D).presCL_rel (D.scalars hdot Sc)
      (RouqUpKLR.restrict S D H fun i j _ => D.brundanQ_restrictQ hdot Sc i j)
      (BrundanMixedInversion.restrict S D M) (fun _ => hr _) hq r ha hb))

end Relations

end RestrictData

end Categorification.TwoRep
