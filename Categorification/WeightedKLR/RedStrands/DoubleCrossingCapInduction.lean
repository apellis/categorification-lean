/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapPush
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedTriple
import StringDiagrams.InterchangeLayers

/-!
# Crossing-count induction for signed cap elimination

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28 uses the KL spanning argument.
The induction uses every actual crossing once, including a red/black crossing.
A path of dots, crossings and cups allows each mixed black crossing as the
three-layer mate of an upward crossing. The only local straightening needed
by the induction is a cap immediately following such a path. Error terms may
be arbitrary signed diagrams with strictly fewer crossings. The evaluation
of a path may already factor through the violating quotient.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}

local notation "S" => signature RD Λ

/-- The crossing generators of the actual signed presentation. -/
def Move.isCrossing : Move I ℓ → Bool
  | .black (.cross ..) | .blackRed .. | .redBlack .. => true
  | _ => false

/-- Number of crossings in the given raw diagram, including red/black crossings. -/
def crossingNumber {a b : Obj S} (d : a ⟶ b) : ℕ :=
  (Diagram.layers d).countP fun L => L.gen.2.isCrossing

theorem crossingNumber_comp {a b c : Obj S} (f : a ⟶ b) (g : b ⟶ c) :
    crossingNumber (f ≫ g) = crossingNumber f + crossingNumber g := by
  simp [crossingNumber, List.countP_append]

private theorem crossingNumber_cap {a b : Obj S} (f : a ⟶ b) (L : Layer S)
    (hf : Diagram.layers f = [L]) (hc : L.gen.2.IsCap) : crossingNumber f = 0 := by
  have hh : L.gen.2.isCrossing = false := by
    cases e : L.gen.2 with
    | black g => cases g <;> simp_all [Move.IsCap, Move.isCrossing]
    | blackRed | redBlack => simp_all [Move.IsCap]
  simp [crossingNumber, hf, hh]

/-- Each mixed black crossing represented by the upward mate has one actual crossing. -/
theorem crossingNumber_upwardMate {a b : Obj S} (g : a ⟶ b) (left right : List (DoubleStrand I ℓ))
    (i j : I) (o : MixedBlackOrder)
    (hg : Diagram.layers g = signedLayers RD Λ a.start (upwardMateLayers left i j right o)) :
    crossingNumber g = 1 := by
  unfold crossingNumber
  rw [hg]
  cases o <;> rfl

private theorem height_pos_of_up {w : List (DoubleStrand I ℓ)} {i : I}
    (μ : X) (h : Sum.inl (true,i) ∈ w) : 0 < cutHeight (obj RD Λ μ w) := by
  simp only [cutHeight, obj, forget_colours, upCount, List.countP_pos_iff]
  exact ⟨_,h,rfl⟩

private theorem height_pos_of_upwardMate {a b : Obj S} (g : a ⟶ b)
    (left right : List (DoubleStrand I ℓ)) (i j : I) (o : MixedBlackOrder)
    (hg : Diagram.layers g = signedLayers RD Λ a.start (upwardMateLayers left i j right o)) :
    0 < cutHeight b := by
  have hc := Diagram.chain g
  rw [hg] at hc
  cases o <;>
    have he := hc.2.2.2.2.2.2 <;>
    change (layer RD Λ a.start _ _ _).cod = b at he <;>
    rw [← he, layer_cod] <;>
    apply height_pos_of_up (i := i) <;>
    simp [Move.top, KL3.Diagram.Shape.cod]

/-- The cap-free moves of the KL spanning argument in the signed calculus.
A sideways black crossing has its actual cup, upward crossing and cap layers.
Its upper boundary contains an upward strand. -/
inductive ForwardPath (a : Obj S) : {b : Obj S} → (a ⟶ b) → Prop
  | nil : ForwardPath a (𝟙 a)
  | single {b c} {d : a ⟶ b} (hd : ForwardPath a d) (g : b ⟶ c) (L : Layer S)
      (hl : Diagram.layers g = [L]) (hn : ¬ L.gen.2.IsCap) : ForwardPath a (d ≫ g)
  | mate {b c} {d : a ⟶ b} (hd : ForwardPath a d) (g : b ⟶ c)
      (left right : List (DoubleStrand I ℓ)) (i j : I) (o : MixedBlackOrder)
      (hg : Diagram.layers g = signedLayers RD Λ b.start (upwardMateLayers left i j right o))
      : ForwardPath a (d ≫ g)

/-- At an all-down target none of the sideways macros or caps can occur. -/
theorem ForwardPath.no_caps {a b : Obj S} {d : a ⟶ b} (hd : ForwardPath a d)
    (hb : cutHeight b = 0) : ∀ L ∈ Diagram.layers d, ¬ L.gen.2.IsCap := by
  induction hd with
  | nil => simp
  | single hd g L hl hn ih =>
    have hc := Diagram.chain g
    rw [hl] at hc
    obtain ⟨_, hsrc, hdst⟩ := hc
    have ht : cutHeight L.cod = 0 := by rw [show L.cod = _ from hdst, hb]
    have hs := (layer_height_change L).2.not.mpr hn
    have hzero : cutHeight L.dom = 0 := by omega
    rw [hsrc] at hzero
    intro M hm
    simp only [Diagram.layers_comp, hl, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih hzero M hm
    · exact hn
  | mate hd g left right i j o hg ih =>
    have := height_pos_of_upwardMate g left right i j o hg
    omega

section Spans
variable (k : Type w) [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
  {a t : Obj (signature RD Λ)} (E : (a ⟶ t) → V)

/-- The span of forward paths with at most `n` crossings, observed after
composing with an arbitrary fixed continuation. -/
def forwardSpan {b : Obj S} (post : b ⟶ t) (n : ℕ) : Submodule k V :=
  Submodule.span k {x | ∃ d : a ⟶ b, ForwardPath a d ∧ crossingNumber d ≤ n ∧ x = E (d ≫ post)}

/-- Raw error terms in the smaller crossing filtration degree. -/
def fewerCrossings {b : Obj S} (post : b ⟶ t) (n : ℕ) : Submodule k V :=
  Submodule.span k {x | ∃ d : a ⟶ b, crossingNumber d < n ∧ x = E (d ≫ post)}

/-- The last-cap step, modulo diagrams of strictly smaller crossing count.
It is tested only on a forward prefix. A continuation is included so bubble
or violated-boundary relations can be used in the quotient. -/
def PushesTerminalCaps : Prop :=
  ∀ {b c : Obj S} (d : a ⟶ b), ForwardPath a d → ∀ (g : b ⟶ c) (L : Layer S),
    Diagram.layers g = [L] → L.gen.2.IsCap → ∀ post : c ⟶ t,
      E ((d ≫ g) ≫ post) ∈ forwardSpan k E post (crossingNumber d) ⊔
        fewerCrossings k E post (crossingNumber d)

private theorem forwardSpan_mono {b : Obj S} (post : b ⟶ t) {c n : ℕ} (h : c ≤ n) :
    forwardSpan k E post c ≤ forwardSpan k E post n := by
  apply Submodule.span_mono
  rintro _ ⟨d,hd,hc,rfl⟩
  exact ⟨d,hd,hc.trans h,rfl⟩

/-- Global elimination by strong induction on crossing count and induction on
the number of actual signed layers at fixed count. -/
theorem mem_forwardSpan_of_terminalCaps (push : PushesTerminalCaps k E) {b : Obj S}
    (d : a ⟶ b) (post : b ⟶ t) : E (d ≫ post) ∈ forwardSpan k E post (crossingNumber d) := by
  suffices H : ∀ n {b : Obj S} (d : a ⟶ b), crossingNumber d ≤ n → ∀ post : b ⟶ t,
      E (d ≫ post) ∈ forwardSpan k E post (crossingNumber d) by
    exact H _ d le_rfl post
  intro n
  induction n using Nat.strong_induction_on with
  | _ n low =>
    intro b d
    obtain ⟨ls,h⟩ := d
    induction ls using List.reverseRecOn generalizing b with
    | nil =>
      obtain rfl := (show a = b from h)
      intro _ post
      exact Submodule.subset_span ⟨𝟙 a, .nil, le_rfl, rfl⟩
    | append_singleton ls L ih =>
      obtain ⟨hp,hg⟩ := Chain.of_append h
      let p := Diagram.mk ls hp
      let g := Diagram.mk [L] hg
      change crossingNumber (p ≫ g) ≤ n → ∀ post, E ((p ≫ g) ≫ post) ∈ _
      intro hbound post
      rw [crossingNumber_comp] at hbound
      have hprefix := ih hp (by change crossingNumber p ≤ n; omega) (g ≫ post)
      rw [Category.assoc]
      refine Submodule.span_le.mpr ?_ hprefix
      rintro _ ⟨f,hf,hc,rfl⟩
      change crossingNumber f ≤ crossingNumber p at hc
      rw [← Category.assoc]
      by_cases cap : L.gen.2.IsCap
      · apply (show forwardSpan k E post (crossingNumber f) ⊔ fewerCrossings k E post (crossingNumber f)
            ≤ forwardSpan k E post (crossingNumber (p ≫ g)) from ?_) (push f hf g L rfl cap post)
        rw [crossingNumber_comp, crossingNumber_cap g L rfl cap, Nat.add_zero]
        refine sup_le (forwardSpan_mono k E post hc) (Submodule.span_le.mpr ?_)
        rintro _ ⟨e,he,rfl⟩
        exact forwardSpan_mono k E post (he.le.trans hc)
          (low (crossingNumber e) (by omega) e le_rfl post)
      · apply Submodule.subset_span
        exact ⟨f ≫ g, .single hf g L rfl cap, by
          change crossingNumber (f ≫ g) ≤ crossingNumber (p ≫ g)
          rw [crossingNumber_comp, crossingNumber_comp]; omega, rfl⟩

end Spans

section Matrices
variable {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k) {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "labels" => (Subtype.val ∘ weights)
local notation "W" => fun s : Ord => obj RD labels 0 (List.map DoubleStrand.down (word (Subtype.val s)))

/-- It suffices to straighten terminal caps on forward paths, counting strictly
smaller-crossing errors before the continuation, in each signed violating entry. -/
theorem downwardDiagramSpan_eq_top_of_terminalCaps (s t : Ord)
    (push : PushesTerminalCaps k (fun d : W s ⟶ W t => signedDownEntry P s t (P.diag d))) :
    downwardDiagramSpan P s t = ⊤ := by
  apply downwardDiagramSpan_eq_top_of_diagrams
  intro d
  have H := mem_forwardSpan_of_terminalCaps k _ push d (𝟙 _)
  rw [Category.comp_id] at H
  refine Submodule.span_le.mpr ?_ H
  rintro _ ⟨f,hf,_,rfl⟩
  rw [Category.comp_id]
  exact downward_of_no_caps P s t f (hf.no_caps (cutHeight_down ..))

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (scalars : I → I → kˣ)
local notation "P₁" => addRedUpRelations RD labels k
  (addMixedBlackRelations RD labels k scalars (addDownRelations RD labels (affineCoverQ Q exponents) P))

/-- The multi-red ordinary matrix map is surjective under the local cap-push
hypothesis on forward prefixes in its signed presentation. -/
theorem ordinaryToDownwardMatrix_surjective_of_terminalCaps
    (h : ∀ s t : Ord, PushesTerminalCaps k (fun d : W s ⟶ W t => signedDownEntry (P₁) s t ((P₁).diag d))) :
    Function.Surjective (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)) := by
  intro M
  apply mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
  intro s t
  rw [downwardDiagramSpan_eq_top_of_terminalCaps (P₁) s t (h s t)]
  exact Submodule.mem_top

end Matrices

end Categorification.Stendhal.DoubleDiagram
