/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBlock

/-!
# Induction on the moves below a signed cap

The inner induction for Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
tracks a dotted cap over an intervening word. Its two step obligations
are a preceding elementary non-cap move or a preceding sideways black crossing.
At an all-down source the initial block has no possible input.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}
local notation "S" => signature RD Λ
local notation "B" => DoubleStrand I ℓ

/-- Appending the crossing of one black cap leg with one signed strand
is a forward step in either orientation. -/
theorem ForwardPath.crossBlackLeft {a b c : Obj S} {p : a ⟶ b} (hp : ForwardPath a p)
    (g : b ⟶ c) (L : List B) (x : B) (l : Letter I) (R : List B)
    (hg : Diagram.layers g = signedLayers RD Λ b.start (DoubleDiagram.crossBlackLeft L x l R)) :
    ForwardPath a (p ≫ g) := by
  cases x with
  | inr r => exact .single hp g _ hg (fun h => h)
  | inl x =>
    obtain ⟨ε,i⟩ := x; obtain ⟨δ,j⟩ := l
    cases ε <;> cases δ
    · exact .single hp g _ hg (fun h => h)
    · exact .mate hp g L R j i .FE hg
    · exact .mate hp g L R i j .EF hg
    · exact .single hp g _ hg (fun h => h)

/-- Sweeping a black cap leg across any intervening word preserves forward paths. -/
theorem ForwardPath.sweepBlackLeft {a b c : Obj S} {p : a ⟶ b} (hp : ForwardPath a p)
    (g : b ⟶ c) (L U : List B) (l : Letter I) (R : List B)
    (hg : Diagram.layers g = signedLayers RD Λ b.start (DoubleDiagram.sweepBlackLeft L U l R)) :
    ForwardPath a (p ≫ g) := by
  induction U generalizing b c L with
  | nil =>
    have he := Diagram.chain g
    rw [hg] at he
    subst c
    have e : g = 𝟙 b := Diagram.ext hg
    simpa [e] using hp
  | cons x U ih =>
    let A := signedLayers RD Λ b.start (DoubleDiagram.sweepBlackLeft (L ++ [x]) U l R)
    let D := signedLayers RD Λ b.start (DoubleDiagram.crossBlackLeft L x l (U ++ R))
    have he : Diagram.layers g = A ++ D := by
      simpa [A, D, DoubleDiagram.sweepBlackLeft, signedLayers] using hg
    have hc := Diagram.chain g
    rw [he] at hc
    obtain ⟨ha,hd⟩ := Chain.of_append hc
    let f := Diagram.mk A ha
    let d := Diagram.mk D hd
    have eqv : g = f ≫ d := Diagram.ext he
    rw [eqv, ← Category.assoc]
    apply (ih hp f (L ++ [x]) rfl).crossBlackLeft d L x l (U ++ R)
    rw [ha.start_eq]
    rfl

variable (k : Type w) [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
  {a t : Obj (signature RD Λ)} (E : (a ⟶ t) → V)

/-- Resolve the cap over a whole word, including dots, modulo lower crossing
degree. Both endpoints of the physical cap block are determined by the list. -/
def ResolvesSignedCapBlocks {b : Obj S} (f : a ⟶ b) : Prop :=
  ∀ {c : Obj S} (g : b ⟶ c) (L U : List B) (l : Letter I) (R : List B) (d : ℕ),
    b = obj RD Λ b.start (L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R) →
    Diagram.layers g = signedLayers RD Λ b.start (signedCapBlock L U l R d) →
    ∀ post : c ⟶ t, E ((f ≫ g) ≫ post) ∈ forwardSpan k E post (crossingNumber f + U.length) ⊔
      fewerCrossings k E post (crossingNumber f + U.length)

/-- Move a forward block from the continuation into the filtered forward span.
The crossing budget increases by exactly its crossing count. -/
theorem forwardSpan_comp {b c : Obj S} (g : b ⟶ c) (post : c ⟶ t) (n : ℕ)
    (step : ∀ f : a ⟶ b, ForwardPath a f → ForwardPath a (f ≫ g)) :
    forwardSpan k E (g ≫ post) n ≤ forwardSpan k E post (n + crossingNumber g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,hc,rfl⟩
  apply Submodule.subset_span
  exact ⟨f ≫ g, step f hf, by rw [crossingNumber_comp]; omega, by rw [Category.assoc]⟩

/-- A strict crossing-count improvement remains strict when the same block
is appended on top. -/
theorem fewerCrossings_comp {b c : Obj S} (g : b ⟶ c) (post : c ⟶ t) (n : ℕ) :
    fewerCrossings k E (g ≫ post) n ≤ fewerCrossings k E post (n + crossingNumber g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hc,rfl⟩
  exact Submodule.subset_span ⟨f ≫ g, by rw [crossingNumber_comp]; omega, by rw [Category.assoc]⟩

/-- Use one local block exchange in the inner induction. The preceding move
is replaced, above the cap, by a forward block `g`. Local errors of strictly
smaller crossing count are absorbed; the replacement may use a different
intervening word and a different number of dots. -/
theorem capBlock_push_of_exchange {b c e : Obj S} (p : a ⟶ b) (ih : ResolvesSignedCapBlocks k E p)
    (block : b ⟶ c) (L U : List B) (l : Letter I) (R : List B) (d : ℕ)
    (hs : b = obj RD Λ b.start (L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R))
    (hb : Diagram.layers block = signedLayers RD Λ b.start (signedCapBlock L U l R d))
    (g : c ⟶ e) (step : ∀ f : a ⟶ c, ForwardPath a f → ForwardPath a (f ≫ g))
    (post : e ⟶ t) (n : ℕ) (budget : crossingNumber p + U.length + crossingNumber g ≤ n)
    (x : V) (exchange : x - E ((p ≫ block) ≫ g ≫ post) ∈ fewerCrossings k E post n) :
    x ∈ forwardSpan k E post n ⊔ fewerCrossings k E post n := by
  let F (m : ℕ) := forwardSpan k E post m ⊔ fewerCrossings k E post m
  have mono {m : ℕ} (hm : m ≤ n) : F m ≤ F n := by
    apply sup_le_sup <;> apply Submodule.span_mono
    · rintro _ ⟨f,hf,hc,rfl⟩; exact ⟨f,hf,hc.trans hm,rfl⟩
    · rintro _ ⟨f,hc,rfl⟩; exact ⟨f,hc.trans_le hm,rfl⟩
  have moved := (sup_le_sup (forwardSpan_comp k E g post (crossingNumber p + U.length) step)
    (fewerCrossings_comp k E g post (crossingNumber p + U.length)))
    (ih block L U l R d hs hb (g ≫ post))
  have h := Submodule.add_mem (F n) (Submodule.mem_sup_right exchange) (mono budget moved)
  simpa only [sub_add_cancel] using h

/-- The right entrance of a cap block is the first crossing in the sweep
through the longer word. This includes both black orientations and a red strand. -/
theorem signedCapBlock_enterRight (L U : List B) (x : B) (l : Letter I) (R : List B) (d : ℕ) :
    crossBlackLeft ((L ++ [.inl l.dual]) ++ U) x l R ++ signedCapBlock L U l (x :: R) d =
      signedCapBlock L (U ++ [x]) l R d := by
  rw [signedCapBlock_append]
  simp [sweepBlackLeft]

/-- The right-entrance position in the cap-push induction requires no local
equation: use the induction hypothesis on the same cap with a longer interior. -/
theorem capBlock_push_enterRight {b c e : Obj S} (p : a ⟶ b) (ih : ResolvesSignedCapBlocks k E p)
    (move : b ⟶ c) (block : c ⟶ e) (L U : List B) (x : B) (l : Letter I) (R : List B) (d : ℕ)
    (hs : b = obj RD Λ b.start (L ++ [.inl l.dual] ++ (U ++ [x]) ++ [.inl l] ++ R))
    (hm : Diagram.layers move = signedLayers RD Λ b.start (crossBlackLeft ((L ++ [.inl l.dual]) ++ U) x l R))
    (hb : Diagram.layers block = signedLayers RD Λ c.start (signedCapBlock L U l (x :: R) d))
    (post : e ⟶ t) :
    E (((p ≫ move) ≫ block) ≫ post) ∈ forwardSpan k E post (crossingNumber (p ≫ move) + U.length) ⊔
      fewerCrossings k E post (crossingNumber (p ≫ move) + U.length) := by
  have hnum : crossingNumber move = 1 :=
    (crossingNumber_of_signedLayers RD Λ b.start move _ hm).trans (crossBlackLeft_crossings ..)
  have hex : Diagram.layers (move ≫ block) =
      signedLayers RD Λ b.start (signedCapBlock L (U ++ [x]) l R d) := by
    rw [Diagram.layers_comp, hm, hb, (Diagram.chain move).start_eq, ← signedCapBlock_enterRight]
    simp [signedLayers]
  have H := ih (move ≫ block) L (U ++ [x]) l R d hs hex post
  rw [Category.assoc p move block, crossingNumber_comp, hnum]
  simpa only [List.length_append, List.length_singleton, Nat.add_right_comm, Nat.add_assoc, Nat.add_comm] using H

/-- For a fixed all-down source, terminal-cap reduction follows from the
successor cases of the cap-block induction. The initial forward path and the
passage back to individual caps are discharged here. -/
theorem pushesTerminalCaps_of_capBlock_steps (ha : cutHeight a = 0)
    (single : ∀ {b c : Obj S} (p : a ⟶ b), ForwardPath a p → ResolvesSignedCapBlocks k E p →
      ∀ (g : b ⟶ c) (M : Layer S), Diagram.layers g = [M] → ¬ M.gen.2.IsCap →
        ResolvesSignedCapBlocks k E (p ≫ g))
    (mate : ∀ {b c : Obj S} (p : a ⟶ b), ForwardPath a p → ResolvesSignedCapBlocks k E p →
      ∀ (g : b ⟶ c) (L R : List B) (i j : I) (o : MixedBlackOrder),
        Diagram.layers g = signedLayers RD Λ b.start (upwardMateLayers L i j R o) →
        ResolvesSignedCapBlocks k E (p ≫ g)) : PushesTerminalCaps k E := by
  have H {b : Obj S} {p : a ⟶ b} (hp : ForwardPath a p) : ResolvesSignedCapBlocks k E p := by
    induction hp with
    | nil =>
      intro c g L U l R d hb _ post
      have h0 := (congrArg cutHeight hb).symm
      rw [ha] at h0
      simp only [cutHeight, obj, forget_colours, upCount, List.countP_eq_zero] at h0
      obtain ⟨ε,i⟩ := l
      cases ε with
      | false =>
        have := h0 (.inl (true,i)) (by simp [Letter.dual])
        contradiction
      | true =>
        have := h0 (.inl (true,i)) (by simp)
        contradiction
    | single hp g M hm hn ih => exact single _ hp ih g M hm hn
    | mate hp g L R i j o hm ih => exact mate _ hp ih g L R i j o hm
  intro b c p hp g M hg hc post
  obtain ⟨l, hm⟩ : ∃ l, M.gen.2 = .black (.cap l) := by
    cases e : M.gen.2 with
    | black s => cases s <;> simp_all [Move.IsCap]
    | blackRed | redBlack => simp_all [Move.IsCap]
  have hh := Diagram.chain g
  rw [hg] at hh
  obtain ⟨valid,hb,_⟩ := hh
  let L := M.left.map Prod.snd
  let R := M.right.map Prod.snd
  have e : layer RD Λ b.start L (.black (.cap l)) R = M := by
    rw [← hb, ← hm]
    exact recover_signed_layer RD Λ M valid
  have src := congrArg Layer.dom e
  rw [layer_dom, hb] at src
  have hs : b = obj RD Λ b.start (L ++ [.inl l.dual] ++ [] ++ [.inl l] ++ R) := by
    simpa [Move.bottom, Shape.dom, List.append_assoc] using src.symm
  have hg' : Diagram.layers g = signedLayers RD Λ b.start (signedCapBlock L [] l R 0) := by
    change _ = [layer RD Λ b.start L (.black (.cap l)) ([] ++ R)]
    rw [List.nil_append, e, hg]
  exact H hp g L [] l R 0 hs hg' post

end Categorification.Stendhal.DoubleDiagram
