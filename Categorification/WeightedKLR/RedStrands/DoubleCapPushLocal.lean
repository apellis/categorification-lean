/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPush
import Categorification.WeightedKLR.RedStrands.DoubleBlackAdjunction
import StringDiagrams.InterchangeLayers

/-!
# Lowering disjoint excursions and collecting cap dots

The interchange step of the geometric spanning argument in Webster,
arXiv:1309.3796v2, Lemma 4.28, lowers a cup past a disjoint cap. The proof
allows arbitrary blocks of critical points on the two disjoint intervals.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams Presentation

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)

local notation "S" => signature RD Λ

/-- The local span of diagrams whose intermediate and final cuts have fewer
than the specified number of upward strands. -/
def lowerCutSpan (a b : Obj S) (n : ℕ) : Submodule k (P.obj a ⟶ P.obj b) :=
  Submodule.span k {x | ∃ d : a ⟶ b, (∀ L ∈ Diagram.layers d, cutHeight L.cod < n) ∧ x = P.diag d}

private def wordHeight (s : List (S).Colour) : ℕ := upCount (s.map Prod.snd)

private theorem wordHeight_append (s t : List (S).Colour) :
    wordHeight (RD := RD) (Λ := Λ) (s ++ t) = wordHeight (RD := RD) (Λ := Λ) s + wordHeight (RD := RD) (Λ := Λ) t := by
  simp only [wordHeight, List.map_append, upCount, List.countP_append]

local notation "wh" => wordHeight (RD := RD) (Λ := Λ)

private theorem sbs_height (u : Obj S) (m v : List (S).Colour) (a b : Obj S) :
    cutHeight (sbs u m v a b) = cutHeight u + cutHeight a + wh m + cutHeight b +
      wh v := by
  change wh (u.word ++ a.word ++ m ++ b.word ++ v) = _
  simp only [wordHeight_append]
  rfl

private theorem whisker_height (L : Layer S) (u : Obj S) (v : List (S).Colour) :
    cutHeight (L.whisker u v).cod = cutHeight u + cutHeight L.cod + wh v := by
  rw [Layer.whisker_cod]
  change wh (u.word ++ L.cod.word ++ v) = _
  simp only [wordHeight_append]
  rfl

private theorem right_height (M : Layer S) (u a : Obj S) (m v : List (S).Colour) :
    cutHeight (M.whisker ⟨u.start, u.word ++ a.word ++ m⟩ v).cod =
      cutHeight u + cutHeight a + wh m + cutHeight M.cod + wh v := by
  rw [whisker_height]
  change wh (u.word ++ a.word ++ m) + _ + _ = _
  simp only [wordHeight_append]
  rfl

private theorem left_height (M : Layer S) (u b : Obj S) (m v : List (S).Colour) :
    cutHeight (M.whisker u (m ++ b.word ++ v)).cod =
      cutHeight u + cutHeight M.cod + wh m + cutHeight b + wh v := by
  rw [whisker_height, wordHeight_append, wordHeight_append]
  change _ + (wh m + cutHeight b + wh v) = _
  omega

/-- A block on the left which gains upward strands commutes past a block on the
right which loses them. Provided neither block overshoots its higher endpoint,
interchanging the blocks strictly lowers the maximum. Both blocks may contain
black/red crossings and dots. -/
theorem lower_disjoint_blocks (u : Obj S) (m v : List (S).Colour) {a a' b b' : Obj S}
    {F G : List (Layer S)} (hF : Chain a F a') (hG : Chain b G b')
    (valid : SideBySideOK u m v a b)
    (rise : cutHeight a < cutHeight a') (fall : cutHeight b' < cutHeight b)
    (hfl : ∀ L ∈ F, cutHeight L.cod ≤ cutHeight a')
    (hgl : ∀ L ∈ G, cutHeight L.cod ≤ cutHeight b)
    (d : sbs u m v a b ⟶ sbs u m v a' b')
    (hd : Diagram.layers d = leftLayers u m v F b ++ rightLayers u m v G a') :
    P.diag d ∈ lowerCutSpan P _ _ (cutHeight (sbs u m v a' b)) := by
  have hG' := chain_rightLayers hG valid
  have hF' := chain_leftLayers hF (valid.chain (F := []) rfl hG)
  let e := Diagram.mk _ (hG'.append hF')
  have eqv : P.diag d = P.diag e := P.diag_interchange_layers_of_even u m v hF hG
    (fun _ _ _ _ => Or.inl rfl) valid d e hd rfl
  apply Submodule.subset_span
  refine ⟨e, ?_, eqv⟩
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · obtain ⟨M,hM,rfl⟩ := List.mem_map.mp hL
    rw [right_height, sbs_height]
    have := hgl M hM
    omega
  · obtain ⟨M,hM,rfl⟩ := List.mem_map.mp hL
    rw [left_height, sbs_height]
    have := hfl M hM
    omega

/-- The reflected disjoint excursion, with the cup block on the right and the
cap block on the left. -/
theorem lower_disjoint_blocks_mirror (u : Obj S) (m v : List (S).Colour) {a a' b b' : Obj S}
    {F G : List (Layer S)} (hF : Chain a F a') (hG : Chain b G b')
    (valid : SideBySideOK u m v a b)
    (fall : cutHeight a' < cutHeight a) (rise : cutHeight b < cutHeight b')
    (hfl : ∀ L ∈ F, cutHeight L.cod ≤ cutHeight a)
    (hgl : ∀ L ∈ G, cutHeight L.cod ≤ cutHeight b')
    (d : sbs u m v a b ⟶ sbs u m v a' b')
    (hd : Diagram.layers d = rightLayers u m v G a ++ leftLayers u m v F b') :
    P.diag d ∈ lowerCutSpan P _ _ (cutHeight (sbs u m v a b')) := by
  have hF' := chain_leftLayers hF valid
  have hG' := chain_rightLayers hG (valid.chain (G := []) hF rfl)
  let e := Diagram.mk _ (hF'.append hG')
  have eqv : P.diag e = P.diag d := P.diag_interchange_layers_of_even u m v hF hG
    (fun _ _ _ _ => Or.inl rfl) valid e d rfl hd
  apply Submodule.subset_span
  refine ⟨e, ?_, eqv.symm⟩
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · obtain ⟨M,hM,rfl⟩ := List.mem_map.mp hL
    rw [left_height, sbs_height]
    have := hfl M hM
    omega
  · obtain ⟨M,hM,rfl⟩ := List.mem_map.mp hL
    rw [right_height, sbs_height]
    have := hgl M hM
    omega

/-- Use a local lower-cut expansion between fixed prefix and suffix diagrams.
The statement allows any linear projection, including passage to the violating
quotient in `LowersMaximalExcursions`. -/
theorem lowerCutSpan_in_context {a b c d : Obj S} (pre : a ⟶ b) (post : c ⟶ d) (n : ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] (π : (P.obj a ⟶ P.obj d) →ₗ[k] V)
    {f : P.obj b ⟶ P.obj c} (hf : f ∈ lowerCutSpan P b c n) :
    π (P.diag pre ≫ f ≫ P.diag post) ∈ Submodule.span k
      {x | ∃ low : List (Layer S), ∃ hl : Chain a (Diagram.layers pre ++ low ++ Diagram.layers post) d,
        (∀ L ∈ low, cutHeight L.cod < n) ∧ x = π (P.diag (Diagram.mk _ hl))} := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e,he,rfl⟩ := hg
    apply Submodule.subset_span
    refine ⟨Diagram.layers e, ((Diagram.chain pre).append (Diagram.chain e)).append
      (Diagram.chain post), he, ?_⟩
    rw [← P.diag_comp, ← P.diag_comp]
    apply congrArg π
    apply congrArg P.diag
    apply Diagram.ext
    simp
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.add_comp, Preadditive.comp_add, map_add]
    exact Submodule.add_mem _ hf hg
  | smul r f _ hf =>
    rw [Linear.smul_comp, Linear.comp_smul, map_smul]
    exact Submodule.smul_mem _ r hf

section Dots

variable (μ : X) (L : List (DoubleStrand I ℓ)) (l : KL3.Diagram.Letter I) (R : List (DoubleStrand I ℓ))
local notation "P₁" => addBlackAdjunctionRelations RD Λ P
local notation "Dl" => blackPairDotLeft RD Λ μ L l R
local notation "Dr" => blackPairDotRight RD Λ μ L l R
local notation "cap" => blackCap RD Λ μ L l R

private theorem pairDots_comm : (P₁).diag Dl ≫ (P₁).diag Dr = (P₁).diag Dr ≫ (P₁).diag Dl := by
  let η := endWeight RD Λ μ L
  let ξ := endWeight RD Λ η [.inl l]
  let θ := endWeight RD Λ ξ [.inl l.dual]
  rw [← (P₁).diag_comp, ← (P₁).diag_comp]
  apply (P₁).diag_interchange_of_layers_of_even μ (colours RD Λ μ L) [] (colours RD Λ θ R)
    (η, .black (.dot l)) (ξ, .black (.dot l.dual)) (.inl rfl)
  all_goals
    simp [blackPairDotLeft, blackPairDotRight, moveDiagram, layer, signature, ξ, η, θ,
      colours_append, Move.bottom, Move.top, KL3.Diagram.Shape.dom,
      KL3.Diagram.Shape.cod, colours, endWeight, add_assoc]

/-- A cap decorated with `n` dots on its right leg. -/
def dottedBlackCap : ℕ → ((P₁).obj (obj RD Λ μ (L ++ [.inl l, .inl l.dual] ++ R)) ⟶
    (P₁).obj (obj RD Λ μ (L ++ R)))
  | 0 => (P₁).diag cap
  | n+1 => (P₁).diag Dr ≫ dottedBlackCap n

private theorem left_dot_dottedBlackCap (n : ℕ) :
    (P₁).diag Dl ≫ dottedBlackCap P μ L l R n = dottedBlackCap P μ L l R (n+1) := by
  induction n with
  | zero =>
    simpa only [dottedBlackCap, blackCapDotLeft, blackCapDotRight, Presentation.diag_comp] using
      blackCap_dot_slide RD Λ μ L l R P
  | succ n ih =>
    change (P₁).diag Dl ≫ (P₁).diag Dr ≫ _ = (P₁).diag Dr ≫ _
    rw [← Category.assoc, pairDots_comm P μ L l R, Category.assoc, ih]

/-- An arbitrary interleaving of dots on the two legs of a cap is equal to
the same number on the right leg, for either cap orientation and with arbitrary
red and black exterior words. The list is read from the bottom toward the cap. -/
theorem cap_dots_collect (sides : List Bool) :
    (sides.foldr (fun left f => (if left then (P₁).diag Dl else (P₁).diag Dr) ≫ f)
      ((P₁).diag cap)) = dottedBlackCap P μ L l R sides.length := by
  induction sides with
  | nil => rfl
  | cons left sides ih =>
    simp only [List.foldr_cons, ih, List.length_cons]
    cases left with
    | false => rfl
    | true => exact left_dot_dottedBlackCap P μ L l R sides.length

end Dots
end Categorification.Stendhal.DoubleDiagram
