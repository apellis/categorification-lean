/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import Categorification.Diagrams.KL3.Relations
import StringDiagrams.LayerMap.Generators
import StringDiagrams.LayerMap.Local
import StringDiagrams.Biadjunction.Zigzag

/-!
# Double Stendhal diagrams in the 2-category of an enlarged Cartan datum

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29 (arXiv:1309.3796v2, §4.5,
Lemma 4.28). A red strand labelled by a dominant weight behaves as an upward
strand of an extra vertex. Let `C'` be a Cartan datum on `I ⊕ Fin ℓ` whose
restriction to `I` is `C`, with a weight datum `W`. Reflecting a double diagram
in a vertical axis, reversing the orientation of every black strand and making
every red strand an upward strand of its own vertex gives a diagram of the KL
2-category of `C'`: black moves become dots, crossings, cups and caps, and
mixed crossings become upward or sideways crossings. Region weights `μ` become
`o - μ` for a chosen base weight `o`.

This file constructs the induced functor from any presentation on double
diagrams into any presentation on the KL signature of `W`, given that the
relations of the source map to zero. The image of each move may be rescaled by
a scalar; `coverSign` is the rescaling by `-1` on same-colour black crossings
used for the comparison with the Cautis–Lauda presentation. The relation checks for the Cautis–Lauda
presentation are separate.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v v'

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j)

/-- The weight datum of `C` obtained by restricting `W` to the black vertices. -/
def blackDatum : WeightDatum C X Y where
  pair := W.pair
  iX j := W.iX (.inl j)
  iY i := W.iY (.inl i)
  pair_iY_iX i j := by rw [W.pair_iY_iX, hC, hC]

/-- A red strand changes the region weight by minus the root of its vertex. -/
def redWeight (r : Fin ℓ) : X := -W.iX (.inr r)

/-- The strand of the enlarged datum attached to a double strand: black
orientations are reversed and red strands point upward. -/
def coverLetter : DoubleStrand I ℓ → Letter (I ⊕ Fin ℓ)
  | .inl s => (!s.1, .inl s.2)
  | .inr r => (true, .inr r)

variable (o : X)

/-- The colour of the reflected strand: its right region is the image of the
region on the left of the double strand. -/
def coverColour (c : X × DoubleStrand I ℓ) : Col (I ⊕ Fin ℓ) X :=
  ⟨coverLetter c.2, o - c.1⟩

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

include hC in
theorem sh_coverLetter (s : DoubleStrand I ℓ) :
    sh W (coverLetter s) = -DoubleStrand.weight RD Λ s := by
  cases s with
  | inl s =>
    simp only [coverLetter, sh, DoubleStrand.weight, sgn_not, neg_smul]
    rfl
  | inr r => simp [coverLetter, sh, DoubleStrand.weight, redWeight, sgn]

/-- The reflected word of a double boundary. -/
def coverWord (w : List (DoubleStrand I ℓ)) : List (Letter (I ⊕ Fin ℓ)) :=
  (w.map coverLetter).reverse

@[simp] theorem coverWord_nil : coverWord ([] : List (DoubleStrand I ℓ)) = [] := rfl

theorem coverWord_append (u v : List (DoubleStrand I ℓ)) :
    coverWord (u ++ v) = coverWord v ++ coverWord u := by
  simp [coverWord]

include hC in
theorem wt_coverWord (μ : X) (w : List (DoubleStrand I ℓ)) :
    wt W (o - μ) (coverWord w) = o - endWeight RD Λ μ w := by
  induction w generalizing μ with
  | nil => simp [coverWord, endWeight]
  | cons a w ih =>
    have h : coverWord (a :: w) = coverWord w ++ [coverLetter a] := by simp [coverWord]
    rw [h, wt_append, wt_cons, wt_nil, sh_coverLetter W hC, endWeight_cons,
      show -DoubleStrand.weight RD Λ a + (o - μ) = o - (μ + DoubleStrand.weight RD Λ a) by abel,
      ih]

include hC in
theorem coverColours (μ : X) (w : List (DoubleStrand I ℓ)) :
    ((colours RD Λ μ w).map (coverColour o)).reverse = wd W (o - μ) (coverWord w) := by
  induction w generalizing μ with
  | nil => rfl
  | cons a w ih =>
    have h : coverWord (a :: w) = coverWord w ++ [coverLetter a] := by simp [coverWord]
    rw [h, wd_append, colours, List.map_cons, List.reverse_cons, ih, wd_cons, wd_nil,
      wt_cons, wt_nil, sh_coverLetter W hC,
      show -DoubleStrand.weight RD Λ a + (o - μ) = o - (μ + DoubleStrand.weight RD Λ a) by abel]
    rfl

/-- The double signature with reflected labels: colours are those of the KL
signature of `W`, generators are double moves. -/
def coverSignature : Signature where
  Region := X
  Colour := Col (I ⊕ Fin ℓ) X
  colourSrc c := sh W c.l + c.r
  colourTgt c := c.r
  Gen := X × Move I ℓ
  dom g := ((colours RD Λ g.1 g.2.bottom).map (coverColour o)).reverse
  cod g := ((colours RD Λ g.1 g.2.top).map (coverColour o)).reverse
  left g := o - endWeight RD Λ g.1 g.2.bottom
  right g := o - g.1

instance : (coverSignature W hC o).IsEven := ⟨fun _ => rfl⟩

/-- Reflection of double diagrams onto the reflected signature. -/
def coverMirror : SigMirror (signature RD Λ) (coverSignature W hC o) where
  region := fun μ : X => o - μ
  colour := coverColour o
  colourSrc c := by
    change sh W (coverLetter c.2) + (o - c.1) = o - (c.1 + DoubleStrand.weight RD Λ c.2)
    rw [sh_coverLetter W hC]; abel
  colourTgt _ := rfl
  gen := id
  dom _ := rfl
  cod _ := rfl
  left _ := rfl
  right _ := rfl

/-- The reflected signature carries the colours of the KL signature unchanged. -/
def coverColourMap : ColourMap (coverSignature W hC o) (psig W) where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  word := id
  word_eq w := (List.map_id w).symm

local notation "κ" => coverColourMap W hC o

theorem genDom_cover (g : (coverSignature W hC o).Gen) :
    LocalMap.genDom κ g = ob W (o - g.1) (coverWord g.2.bottom) :=
  Obj.ext (wt_coverWord W hC o _ _).symm (coverColours W hC o _ _)

theorem genCod_cover (g : X × Move I ℓ) :
    LocalMap.genCod κ g = ob W (o - g.1) (coverWord g.2.top) := by
  refine Obj.ext ?_ (coverColours W hC o _ _)
  change o - endWeight RD Λ g.1 g.2.bottom = wt W (o - g.1) (coverWord g.2.top)
  rw [wt_coverWord W hC o, Move.endWeight_top]

omit [AddCommGroup Y] in
/-- The KL diagram of a reflected double move with right region `ν`. -/
def coverMove (ν : X) : (m : Move I ℓ) → ob W ν (coverWord m.bottom) ⟶ ob W ν (coverWord m.top)
  | .black (.dot l) => mkD W ν [([], .dot (!l.1, .inl l.2), [])] ⟨rfl, rfl⟩
  | .black (.cross ε i j) => mkD W ν [([], .cross (!ε) (.inl j) (.inl i), [])] ⟨rfl, rfl⟩
  | .black (.cup l) => mkD W ν [([], .cup (l.1, .inl l.2), [])]
      ⟨rfl, by simp [coverWord, coverLetter, Move.top, Letter.dual]⟩
  | .black (.cap l) => mkD W ν [([], .cap (l.1, .inl l.2), [])]
      ⟨by simp [coverWord, coverLetter, Move.bottom, Letter.dual], rfl⟩
  | .blackRed (false, j) r => mkD W ν [([], .cross true (.inr r) (.inl j), [])] ⟨rfl, rfl⟩
  | .blackRed (true, j) r => crossl W (.inr r) (.inl j) ν
  | .redBlack r (false, j) => mkD W ν [([], .cross true (.inl j) (.inr r), [])] ⟨rfl, rfl⟩
  | .redBlack r (true, j) => crossr W (.inr r) (.inl j) ν

variable {k : Type w} [CommRing k]

/-- The scalar attached to a double move by the comparison with the
Cautis–Lauda presentation: `-1` on a crossing of two black strands of the same
colour, `1` on every other move. Webster's black crossings and the reflected
crossings of the enlarged 2-category differ by this sign on equal colours. -/
def coverSign [DecidableEq I] : Move I ℓ → k
  | .black (.cross _ i j) => if i = j then -1 else 1
  | _ => 1

@[simp] theorem coverSign_cross_self [DecidableEq I] (ε : Bool) (i : I) :
    coverSign (k := k) (ℓ := ℓ) (.black (.cross ε i i)) = -1 := by simp [coverSign]

theorem coverSign_cross_of_ne [DecidableEq I] (ε : Bool) {i j : I} (h : i ≠ j) :
    coverSign (k := k) (ℓ := ℓ) (.black (.cross ε i j)) = 1 := by simp [coverSign, h]

/-- The image of a reflected double move in a presentation on the KL signature,
rescaled by the weight `σ` of the move. -/
def coverImage (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)
    (g : (coverSignature W hC o).Gen) :
    Q.obj (LocalMap.genDom κ g) ⟶ Q.obj (LocalMap.genCod κ g) :=
  σ g.2 • (eqToHom (congrArg Q.obj (genDom_cover W hC o g)) ≫
    Q.diag (coverMove W (o - g.1) g.2) ≫ eqToHom (congrArg Q.obj (genCod_cover W hC o g)).symm)

/-- The relations of reflected double diagrams that hold after inserting the
KL diagrams of the moves into `Q`. -/
def coverKernel (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k) :
    Presentation.{w, max u v w} (coverSignature W hC o) k where
  Rel := Σ (a b : Obj (coverSignature W hC o)), {f : LinDiagram k a b //
    (freeLift k (LocalMap.ofGen κ (coverImage W hC o Q σ)).functor).map f = 0}
  dom r := r.1
  cod r := r.2.1
  rel r := r.2.2.1

/-- The functor from reflected double diagrams to `Q` defined by the KL diagrams of the moves. -/
def coverKernelFunctor (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k) :
    (coverKernel W hC o Q σ).Presented ⥤ Q.Presented :=
  LocalMap.liftGen κ (coverImage W hC o Q σ) (coverKernel W hC o Q σ)
    (fun g => LocalMap.parity_of_isEven κ (coverImage W hC o Q σ) g) (fun r => r.2.2.2)

local notation "M" => coverMirror W hC o

/-- The image of a double linear combination in `Q`: reflect it, then insert
the KL diagram of every move. -/
abbrev coverLin (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)
    {a b : Obj (signature RD Λ)}
    (f : LinDiagram k a b) : Q.obj ((coverColourMap W hC o).obj ((M).obj a)) ⟶
      Q.obj ((coverColourMap W hC o).obj ((M).obj b)) :=
  (freeLift k (LocalMap.ofGen κ (coverImage W hC o Q σ)).functor).map ((M).toLayerMap.lin f)

/-- **Double diagrams in the KL 2-category of the enlarged datum.** Reflection
in a vertical axis followed by the KL diagrams of the moves defines a functor
from any presentation `P` on double diagrams whose relations hold in `Q`. -/
def coverFunctor (P : Presentation.{w, max u v} (signature RD Λ) k)
    (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k) (hwf : P.WFDom)
    (hP : ∀ r, coverLin W hC o Q σ (P.rel r) = 0) :
    P.Presented ⥤ Q.Presented :=
  (M).lift P (Q := coverKernel W hC o Q σ) (χ := fun _ => 1) (fun _ => rfl) hwf (fun r => by
      rw [LayerMap.freeLift_toPresented_one]
      exact (coverKernel W hC o Q σ).lin_rel_self ⟨_, _, ⟨(M).toLayerMap.lin (P.rel r), hP r⟩⟩) ⋙
    coverKernelFunctor W hC o Q σ

section CoverLin

omit [AddCommGroup Y] in
/-- The linear extension of a functor, applied to the image of a linear
combination under a layer map, is the linear extension of the composite. -/
theorem freeLift_map_layerLin {S S' : Signature} {D : Type*} [Category D] [Preadditive D]
    [Linear k D] (φ : LayerMap S S') (H : Obj S' ⥤ D) {a b : Obj S} (f : LinDiagram k a b) :
    (freeLift k H).map (φ.lin f) = (freeLift k (φ.functor ⋙ H)).map f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [LayerMap.lin, Finsupp.mapDomain_zero, Functor.map_zero, Functor.map_zero]
  | add f g hf hg => rw [LayerMap.lin_add, Functor.map_add, Functor.map_add, hf, hg]
  | single d r =>
    rw [LayerMap.lin, Finsupp.mapDomain_single, freeLift_map_single, freeLift_map_single]
    rfl

variable (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)

theorem coverLin_comp {a b c : Obj (signature RD Λ)} (f : LinDiagram k a b)
    (g : LinDiagram k b c) :
    coverLin W hC o Q σ (f ≫ g) = coverLin W hC o Q σ f ≫ coverLin W hC o Q σ g := by
  simp only [coverLin, freeLift_map_layerLin, Functor.map_comp]

theorem coverLin_add {a b : Obj (signature RD Λ)} (f g : LinDiagram k a b) :
    coverLin W hC o Q σ (f + g) = coverLin W hC o Q σ f + coverLin W hC o Q σ g := by
  simp only [coverLin, freeLift_map_layerLin, Functor.map_add]

theorem coverLin_smul {a b : Obj (signature RD Λ)} (r : k) (f : LinDiagram k a b) :
    coverLin W hC o Q σ (r • f) = r • coverLin W hC o Q σ f := by
  simp only [coverLin, freeLift_map_layerLin, Functor.map_smul]

theorem coverLin_id (a : Obj (signature RD Λ)) :
    coverLin W hC o Q σ (𝟙 (Free.of k a)) = 𝟙 _ := by
  rw [coverLin, freeLift_map_layerLin]
  exact (freeLift k _).map_id _

end CoverLin

section CoverFunctor

theorem coverFunctor_obj
    (P : Presentation.{w, max u v} (signature (blackDatum W hC) (redWeight W)) k)
    (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k) (hwf : P.WFDom)
    (hP : ∀ r, coverLin W hC o Q σ (P.rel r) = 0)
    (a : Obj (signature (blackDatum W hC) (redWeight W))) :
    (coverFunctor W hC o P Q σ hwf hP).obj (P.obj a) =
      Q.obj ((coverColourMap W hC o).obj ((coverMirror W hC o).obj a)) := rfl

/-- On a linear combination of diagrams the cover functor is the mirrored
image followed by the generator images in `Q`. -/
theorem coverFunctor_lin
    (P : Presentation.{w, max u v} (signature (blackDatum W hC) (redWeight W)) k)
    (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k) (hwf : P.WFDom)
    (hP : ∀ r, coverLin W hC o Q σ (P.rel r) = 0)
    {a b : Obj (signature (blackDatum W hC) (redWeight W))} (f : LinDiagram k a b) :
    (coverFunctor W hC o P Q σ hwf hP).map (P.lin f) = coverLin W hC o Q σ f := by
  unfold coverFunctor coverKernelFunctor
  rw [Functor.comp_map, SigMirror.lift_lin, LayerMap.freeLift_toPresented_one,
    LocalMap.liftGen_lin]

end CoverFunctor

end Categorification.Stendhal.DoubleDiagram
