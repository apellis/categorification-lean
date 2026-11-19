/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqRestrict
import Categorification.Diagrams.BicatInterpAdmissiblePull
import Categorification.TwoRep.RouqUpWords

/-!
# The relabelling of KL diagrams along a restriction datum

For a restriction datum `D` from a weight datum `RD` of `C` to a weight datum `W` of `C'`
(`RestrictData`), the letters `(ε, i) ↦ (ε, e i)` and the regions `x ↦ o + x` relabel the
KL III signature of `RD` into that of `W` (`RestrictData.sigMap`). Pulled back along this
relabelling, the generator images of a Rouquier family `S` for `W` with scalars `Sc` agree with
those of the restricted family `S.restrict D` with the Khovanov–Lauda scalars, up to the
identifications of the boundary words (`RestrictData.pull_eq_zero`). With Khovanov–Lauda scalars
on the image of `e`, the admissible interpretation of `S` therefore kills the relabelled
relations of KL III's `U` (`RestrictData.pres_rel_restrict`).

This is used for Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29: the black part of the
cyclotomic action of the enlarged Cartan datum.
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

variable (D : RestrictData RD W)

/-- The relabelling of regions `x ↦ o + x`. -/
def shift (x : X) : X := D.o + x

/-- The relabelling of letters `(ε, i) ↦ (ε, e i)`. -/
def letter (l : Letter I) : Letter I' := (l.1, D.e l.2)

@[simp] theorem letter_dual (l : Letter I) : D.letter l.dual = (D.letter l).dual := rfl

theorem sh_letter (l : Letter I) : sh W (D.letter l) = sh RD l := by
  simp [sh, letter, D.iX]

theorem sh_letter_add (l : Letter I) (x : X) :
    sh W (D.letter l) + (D.o + x) = D.o + (sh RD l + x) := by
  rw [sh_letter]; abel

/-- The relabelling of strand colours `⟨l, r⟩ ↦ ⟨(ε, e i), o + r⟩`. -/
def col (c : Col I X) : Col I' X := ⟨D.letter c.l, D.o + c.r⟩

theorem src_col (c : Col I X) :
    (psig W).colourSrc (D.col c) = D.shift ((psig RD).colourSrc c) :=
  D.sh_letter_add c.l c.r

theorem dual_col (c : Col I X) : (inv W).dual (D.col c) = D.col ((inv RD).dual c) := by
  rw [inv_dual, inv_dual]
  exact Col.ext rfl (D.sh_letter_add c.l c.r)

/-- The relabelling of generators. -/
def gen : (psig RD).Gen → (psig W).Gen
  | .gen (.dot c) => .gen (.dot (D.col c))
  | .gen (.cross s i j ν) => .gen (.cross s (D.e i) (D.e j) (D.o + ν))
  | .cup c => .cup (D.col c)
  | .cap c => .cap (D.col c)

theorem gen_left (g : (psig RD).Gen) :
    (psig W).left (D.gen g) = D.shift ((psig RD).left g) := by
  rcases g with (⟨c⟩ | ⟨s, i, j, ν⟩) | c | c
  · exact D.src_col c
  · show sh W (D.letter (s, i)) + (sh W (D.letter (s, j)) + (D.o + ν)) =
      D.o + (sh RD (s, i) + (sh RD (s, j) + ν))
    rw [D.sh_letter_add, D.sh_letter_add]
  · exact D.src_col c
  · rfl

theorem gen_right (g : (psig RD).Gen) :
    (psig W).right (D.gen g) = D.shift ((psig RD).right g) := by
  rcases g with (⟨c⟩ | ⟨s, i, j, ν⟩) | c | c
  · rfl
  · rfl
  · exact D.src_col c
  · rfl

theorem gen_dom (g : (psig RD).Gen) :
    (psig W).dom (D.gen g) = ((psig RD).dom g).map D.col := by
  rcases g with (⟨c⟩ | ⟨s, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨D.letter (s, i), sh W (D.letter (s, j)) + (D.o + ν)⟩ : Col I' X),
      ⟨D.letter (s, j), D.o + ν⟩] =
        [⟨D.letter (s, i), D.o + (sh RD (s, j) + ν)⟩, ⟨D.letter (s, j), D.o + ν⟩]
    rw [D.sh_letter_add]
  · rfl
  · show [(inv W).dual (D.col c), D.col c] = [D.col ((inv RD).dual c), D.col c]
    rw [D.dual_col]

theorem gen_cod (g : (psig RD).Gen) :
    (psig W).cod (D.gen g) = ((psig RD).cod g).map D.col := by
  rcases g with (⟨c⟩ | ⟨s, i, j, ν⟩) | c | c
  · rfl
  · show [(⟨D.letter (s, j), sh W (D.letter (s, i)) + (D.o + ν)⟩ : Col I' X),
      ⟨D.letter (s, i), D.o + ν⟩] =
        [⟨D.letter (s, j), D.o + (sh RD (s, i) + ν)⟩, ⟨D.letter (s, i), D.o + ν⟩]
    rw [D.sh_letter_add]
  · show [D.col c, (inv W).dual (D.col c)] = [D.col c, D.col ((inv RD).dual c)]
    rw [D.dual_col]
  · rfl

/-- **The relabelling of KL III diagrams** along a restriction datum. -/
def sigMap : SigMap (psig RD) (psig W) where
  region := D.shift
  colour := D.col
  colourSrc := D.src_col
  colourTgt _ := rfl
  gen := D.gen
  dom := D.gen_dom
  cod := D.gen_cod
  left := D.gen_left
  right := D.gen_right

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  (S : RouqFamily (B := B) W)

variable [AdditiveWhiskering B] {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]

/-- The downward dots of the restriction are those of the family. -/
theorem dotDn_restrict (i : I) {x y : X} (h : x + RD.iX i = y) :
    (S.restrict D).dotDn i h = S.dotDn (D.e i) (D.step i h) := by
  rw [RouqFamily.dotDn, RouqFamily.dotDn, RouqFamily.restrict_adjL]
  rfl

/-- With Khovanov–Lauda scalars on the image of `e`, the downward crossings of the
restriction are those of the family. -/
theorem crossDn_restrict (Sc : CL.CLScalars C' k) (ht : ∀ i j, Sc.t (D.e i) (D.e j) = 1)
    (i j : I) {a n n' b : X} (hj : n' + RD.iX j = b) (hi : a + RD.iX i = n')
    (hi' : n + RD.iX i = b) (hj' : a + RD.iX j = n) :
    (S.restrict D).crossDn (CL.CLScalars.kl : CL.CLScalars C k) i j hj hi hi' hj' =
      S.crossDn Sc (D.e i) (D.e j) (D.step j hj) (D.step i hi) (D.step i hi') (D.step j hj') := by
  simp only [RouqFamily.crossDn, RouqFamily.restrict_adjL, ht, CL.CLScalars.kl_t, inv_one]
  rfl

omit [AdditiveWhiskering B] in
/-- Transporting an upward crossing along equalities of its two middle regions. -/
theorem _root_.Categorification.TwoRep.RouqFamily.cross_cast (i j : I') {a b c d b' c' : X}
    (hb : b = b') (hc : c = c') (h₁ : a + W.iX j = b) (h₂ : b + W.iX i = d)
    (h₃ : a + W.iX i = c) (h₄ : c + W.iX j = d) :
    S.cross i j h₁ h₂ h₃ h₄ = eqToHom (by subst hb hc; rfl) ≫
      S.cross i j (hb ▸ h₁) (hb ▸ h₂) (hc ▸ h₃) (hc ▸ h₄) ≫ eqToHom (by subst hb hc; rfl) := by
  subst hb hc; simp

/-- Transporting a downward crossing along equalities of its two middle regions. -/
theorem _root_.Categorification.TwoRep.RouqFamily.crossDn_cast (Sc : CL.CLScalars C' k)
    (i j : I') {a n n' b m m' : X} (hn : n = m) (hn' : n' = m') (hj : n' + W.iX j = b)
    (hi : a + W.iX i = n') (hi' : n + W.iX i = b) (hj' : a + W.iX j = n) :
    S.crossDn Sc i j hj hi hi' hj' = eqToHom (by subst hn hn'; rfl) ≫
      S.crossDn Sc i j (hn' ▸ hj) (hn' ▸ hi) (hn ▸ hi') (hn ▸ hj') ≫
        eqToHom (by subst hn hn'; rfl) := by
  subst hn hn'; simp

/-- The counit of a left adjunction depends on the inner region only up to transport. -/
theorem _root_.Categorification.TwoRep.RouqFamily.adjL_counit_region (i : I') {x y y' : X}
    {P Q : S.obj x ⟶ S.obj x} (h : x + W.iX i = y) (h' : x + W.iX i = y') (hy : y = y')
    (e₁ : P = S.E i h ≫ S.F i h) (e₂ : P = S.E i h' ≫ S.F i h') (e₃ : 𝟙 _ = Q) :
    eqToHom e₁ ≫ (S.adjL i h).counit ≫ eqToHom e₃ =
      eqToHom e₂ ≫ (S.adjL i h').counit ≫ eqToHom e₃ := by
  subst hy; rfl

omit [AdditiveWhiskering B] in
/-- The counit of an adjunction depends on the inner region only up to transport. -/
theorem _root_.Categorification.TwoRep.RouqFamily.adj_counit_region (i : I') {x y y' : X}
    {P Q : S.obj x ⟶ S.obj x} (h : y + W.iX i = x) (h' : y' + W.iX i = x) (hy : y = y')
    (e₁ : P = S.F i h ≫ S.E i h) (e₂ : P = S.F i h' ≫ S.E i h') (e₃ : 𝟙 _ = Q) :
    eqToHom e₁ ≫ (S.adj i h).counit ≫ eqToHom e₃ =
      eqToHom e₂ ≫ (S.adj i h').counit ≫ eqToHom e₃ := by
  subst hy; rfl

omit [AdditiveWhiskering B] in
/-- The strand images of the pulled-back model are those of the restriction. -/
theorem strand_pull : (S.model.pull D.sigMap.toColourMap).strandAt =
    (S.restrict D).model.strandAt := by
  funext c x y hx hy
  rcases c with ⟨⟨_ | _, i⟩, r⟩ <;> rfl

/-- **The relabelling of the generator images.** With Khovanov–Lauda scalars on the image of
`e`, a linear combination of KL III diagrams of `RD` killed by the admissible interpretation of
`S.restrict D` is killed by that of the pullback of `S` along `D.sigMap`. -/
theorem pull_eq_zero (Sc : CL.CLScalars C' k) (ht : ∀ i j, Sc.t (D.e i) (D.e j) = 1)
    {s t : X} {a b : Obj (psig RD)} (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b)
    (hf : admissibleMap ((S.restrict D).genImg (CL.CLScalars.kl : CL.CLScalars C k)) ha hb f = 0) :
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
    rw [D.crossDn_restrict S Sc ht]
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

section Relations

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- With Khovanov–Lauda scalars on the image of `e`, Brundan's polynomials of `Sc` on the image
of `e` are the Khovanov–Lauda ones. -/
theorem brundanQ_restrict (Sc : CL.CLScalars C' k)
    (hdot : ∀ i j, C'.dot (D.e i) (D.e j) = C.dot i j) (ht : ∀ i j, Sc.t (D.e i) (D.e j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (D.e i) (D.e j) p q = 0) (i j : I) :
    brundanQ Sc (D.e i) (D.e j) = brundanQ (CL.CLScalars.kl : CL.CLScalars C k) i j := by
  have hd (a b : I) : C'.dij (D.e a) (D.e b) = C.dij a b := by
    simp only [QuantumGroup.CartanDatum.dij, hdot]
  unfold brundanQ
  rw [hdot, hd, hd, ht, ht]
  split_ifs
  · rfl
  congr 1
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  rw [hs i j p q (Finset.mem_range.mp hp) (Finset.mem_range.mp hq), CL.CLScalars.kl_s]

/-- **The relabelled KL III relations hold for `S`.** For a Rouquier family `S` for `W` with
Brundan's upward relations and invertible mixed crossings, the admissible interpretation of `S`
with scalars `Sc` kills the relabelling along `D` of every defining relation of KL III's `U` for
`RD`, provided `Sc` has Khovanov–Lauda scalars on the image of `e`. -/
theorem pres_rel_restrict (Sc : CL.CLScalars C' k)
    (hdot : ∀ i j, C'.dot (D.e i) (D.e j) = C.dot i j) (ht : ∀ i j, Sc.t (D.e i) (D.e j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (D.e i) (D.e j) p q = 0)
    (H : BrundanUpKLR S Sc)
    (M : BrundanMixedInversion S) (r : (pres RD k).Rel) {s t : X}
    (ha : Cond (S := psig RD) s t ((pres RD k).dom r))
    (hb : Cond (S := psig RD) s t ((pres RD k).cod r)) :
    admissibleMap (S.genImg Sc) (Cond.map D.sigMap ha) (Cond.map D.sigMap hb)
      (D.sigMap.toLayerMap.lin ((pres RD k).rel r)) = 0 :=
  admissibleMap_pull_eq_zero D.sigMap (S.genImg Sc) ha hb _
    (D.pull_eq_zero S Sc ht ha hb _ ((S.restrict D).pres_rel_kl k
      (RouqUpKLR.restrict S D H fun i j _ => D.brundanQ_restrict Sc hdot ht hs i j)
      (BrundanMixedInversion.restrict S D M) r ha hb))

end Relations

end RestrictData

end Categorification.TwoRep
