/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigmaOmega
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentation

/-!
# Black double diagrams as Khovanov–Lauda diagrams

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25. A black strand of a double diagram
with label `l` separates the same regions as a Khovanov–Lauda strand with the opposite
orientation `l*`: in the double signature the region on the right of `l` is the region on its
left plus `l_X`, in the KL signature it is the region on its left minus `l_X`. Relabelling each
strand by its dual is a map of signatures from the KL signature to the double signature that
keeps every region (`blackRelabel`).

The black relations of the double diagrams are the reflections of the KL relations in a vertical
axis (`blackMirror`). Reflecting and inverting orientations in the KL signature (`thetaD`) and
then relabelling gives the same diagrams (`blackMirror_map_eq`, `blackMirrorLinear_eq`): the
reflected KL relations are the relabelled images of the KL relations reflected with inverted
orientations, which vanish in `U` (`KL3.Diagram.lin_thetaLin_eq_zero`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
  {ℓ : ℕ} (Λ : Fin ℓ → X)

local notation "S" => psig RD
local notation "T" => signature RD Λ

theorem weight_inl (l : Letter I) : DoubleStrand.weight (ℓ := ℓ) RD Λ (.inl l) = sh RD l := rfl

/-- The double strand with the opposite label, between the same regions as a KL strand. -/
abbrev relabelColour (c : Col I X) : X × DoubleStrand I ℓ := (sh RD c.l + c.r, .inl c.l.dual)

/-- The double black generator between the same regions as a KL generator, with every strand
relabelled by its dual. -/
abbrev relabelGen (g : (S).Gen) : (T).Gen := ((S).left g, .black (Omega.shape (shapeOf RD g)))

/-- **Relabelling a KL diagram as a black double diagram**: each strand gets the dual label, and
every region is kept. -/
def blackRelabel : SigMap S T where
  region := id
  colour := relabelColour RD
  colourSrc _ := rfl
  colourTgt c := by
    change sh RD c.l + c.r + sh RD c.l.dual = c.r
    rw [sh_dual]; abel
  gen := relabelGen RD Λ
  dom g := by
    rcases g with (⟨⟨l, r⟩⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
    · rfl
    · change [((sh RD (ε, i) + (sh RD (ε, j) + ν) : X), (.inl (!ε, i) : DoubleStrand I ℓ)),
        (sh RD (ε, i) + (sh RD (ε, j) + ν) + sh RD (!ε, i), .inl (!ε, j))] =
        [(sh RD (ε, i) + (sh RD (ε, j) + ν), .inl (!ε, i)), (sh RD (ε, j) + ν, .inl (!ε, j))]
      rw [show ((!ε, i) : Letter I) = Letter.dual (ε, i) from rfl, sh_dual]
      congr 3; abel
    · rfl
    · change [((r : X), (.inl l.dual.dual : DoubleStrand I ℓ)),
        (r + sh RD l.dual.dual, .inl l.dual)] =
        [(sh RD l.dual + (sh RD l + r), .inl l.dual.dual), (sh RD l + r, .inl l.dual)]
      rw [Letter.dual_dual, ← add_assoc, sh_dual_add_sh, zero_add, add_comm]
  cod g := by
    rcases g with (⟨⟨l, r⟩⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
    · rfl
    · change [((sh RD (ε, i) + (sh RD (ε, j) + ν) : X), (.inl (!ε, j) : DoubleStrand I ℓ)),
        (sh RD (ε, i) + (sh RD (ε, j) + ν) + sh RD (!ε, j), .inl (!ε, i))] =
        [(sh RD (ε, j) + (sh RD (ε, i) + ν), .inl (!ε, j)), (sh RD (ε, i) + ν, .inl (!ε, i))]
      rw [show ((!ε, j) : Letter I) = Letter.dual (ε, j) from rfl, sh_dual]
      simp only [List.cons.injEq, Prod.mk.injEq, and_true]
      constructor <;> abel
    · change [((sh RD l + r : X), (.inl l.dual : DoubleStrand I ℓ)),
        (sh RD l + r + sh RD l.dual, .inl l.dual.dual)] =
        [(sh RD l + r, .inl l.dual), (sh RD l.dual + (sh RD l + r), .inl l.dual.dual)]
      rw [add_comm (sh RD l + r)]
    · rfl
  left _ := rfl
  right g := by
    rcases g with (⟨⟨l, r⟩⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
    · change sh RD l + r + (sh RD l.dual + 0) = r
      rw [sh_dual]; abel
    · change sh RD (ε, i) + (sh RD (ε, j) + ν) + (sh RD (!ε, i) + (sh RD (!ε, j) + 0)) = ν
      rw [show ((!ε, i) : Letter I) = Letter.dual (ε, i) from rfl,
        show ((!ε, j) : Letter I) = Letter.dual (ε, j) from rfl, sh_dual, sh_dual]
      abel
    · change sh RD l + r + 0 = sh RD l + r
      exact add_zero _
    · change r + (sh RD l.dual.dual + (sh RD l.dual + 0)) = r
      rw [Letter.dual_dual, sh_dual]; abel

local notation "ρ" => blackRelabel RD Λ

theorem relabelColour_col_col (c : Col I X) :
    relabelColour (ℓ := ℓ) RD (Sig.col (RD := RD) (Omega.col c)) = (c.r, .inl c.l) := by
  obtain ⟨l, r⟩ := c
  change ((sh RD l.dual + -(sh RD l.dual + -r) : X), (.inl l.dual.dual : DoubleStrand I ℓ)) = _
  rw [Letter.dual_dual]
  congr 1; abel

theorem relabel_word_theta (w : List (Col I X)) :
    (Sig.word RD (Omega.word w)).map (relabelColour (ℓ := ℓ) RD) =
      (w.map fun c => ((c.r, .inl c.l) : X × DoubleStrand I ℓ)).reverse := by
  simp only [Sig.word, Omega.word, List.map_reverse, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => relabelColour_col_col RD c

theorem relabelGen_theta (g : (S).Gen) :
    relabelGen RD Λ (Sig.gen (Omega.gen g)) =
      ((S).right g, .black (Sig.shape (shapeOf RD g))) := by
  rcases g with (⟨⟨l, r⟩⟩ | ⟨ε, i, j, ν⟩) | ⟨l, r⟩ | ⟨l, r⟩
  · change ((sh RD l.dual + -(sh RD l.dual + -r) : X), Move.black (Shape.dot l.dual.dual)) =
      (r, .black (.dot l))
    rw [Letter.dual_dual]; congr 1; abel
  · change ((sh RD (!ε, j) + (sh RD (!ε, i) + -(sh RD (!ε, i) + (sh RD (!ε, j) + -ν))) : X),
      Move.black (Shape.cross (!!ε) j i)) = (ν, .black (.cross ε j i))
    rw [Bool.not_not]; congr 1; abel
  · change ((sh RD l.dual.dual + - -r : X), Move.black (Shape.cup l.dual.dual.dual)) =
      (sh RD l + r, .black (.cup l.dual))
    rw [Letter.dual_dual, neg_neg]
  · change ((- -r : X), Move.black (Shape.cap l.dual.dual.dual)) = (r, .black (.cap l.dual))
    rw [Letter.dual_dual, neg_neg]

/-- On well-formed objects, reflecting a KL object and relabelling it with inverted orientations
is its reflection as a double object. -/
theorem blackMirror_obj_eq {a : Obj S} (ha : a.WF) :
    (ρ).obj (thetaObj a) = (blackMirror RD Λ).obj a := by
  refine Obj.ext ?_ ?_
  · change -Sig.eR (RD := RD) (-Omega.rX a.start) (Omega.word a.word) = a.endR
    have h := (Omega.ok_word (RD := RD) a.start a.word ha).2
    unfold Sig.eR at h ⊢
    rw [h, neg_neg]
    rfl
  · exact relabel_word_theta RD (ℓ := ℓ) a.word

/-- On valid layers, reflecting a KL layer and relabelling it with inverted orientations is its
reflection as a double layer. -/
theorem blackMirror_layer_eq {L : Layer S} (hv : L.Valid) :
    (ρ).layer (Sig.rlay (Omega.rlay L)) = (blackMirror RD Λ).layer L := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · change -Sig.eR (RD := RD) ((S).right (Omega.gen L.gen)) (Omega.word L.right) =
      (S).endR ((S).right L.gen) L.right
    have h := (Omega.ok_word (RD := RD) _ _ hv.right_ok).2
    rw [Omega.gen_right]
    unfold Sig.eR at h ⊢
    rw [h, neg_neg]
  · exact relabel_word_theta RD (ℓ := ℓ) L.right
  · exact relabelGen_theta RD Λ L.gen
  · exact relabel_word_theta RD (ℓ := ℓ) L.left

/-- **The reflection of a KL diagram as a double diagram** is the relabelling of its reflection
with inverted orientations. -/
theorem blackMirror_map_eq {a b : Obj S} (ha : a.WF) (d : a ⟶ b) :
    (blackMirror RD Λ).toLayerMap.map d =
      Diagram.cast ((ρ).toLayerMap.map (thetaD d)) (blackMirror_obj_eq RD Λ ha)
        (blackMirror_obj_eq RD Λ ((Diagram.chain d).wf ha)) := by
  apply Diagram.ext
  rw [Diagram.layers_cast, LayerMap.layers_map, LayerMap.layers_map, layers_thetaD, List.map_map]
  refine List.map_congr_left fun L hL => ?_
  exact (blackMirror_layer_eq RD Λ (Sig.chain_mem (Diagram.chain d) hL).1).symm

variable {k : Type w} [CommRing k]

/-- **The reflection of a linear combination of KL diagrams as a double one** is the
relabelling of its reflection with inverted orientations. -/
theorem blackMirrorLinear_eq {a b : Obj S} (ha : a.WF) (hb : b.WF) (f : LinDiagram k a b) :
    blackMirrorLinear RD Λ f =
      LinDiagram.cast ((ρ).toLayerMap.lin (thetaLin k f)) (blackMirror_obj_eq RD Λ ha)
        (blackMirror_obj_eq RD Λ hb) := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
  | zero => simp [LayerMap.lin, LinDiagram.cast]
  | add f g hf hg => rw [map_add, hf, hg, map_add, LayerMap.lin_add, LinDiagram.cast_add]
  | single d c =>
    change Finsupp.mapDomain _ (Finsupp.single d c) =
      LinDiagram.cast (Finsupp.mapDomain _ (Finsupp.mapDomain thetaD (Finsupp.single d c))) _ _
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
      LinDiagram.cast_single, blackMirror_map_eq RD Λ ha d]

end Categorification.Stendhal.DoubleDiagram
