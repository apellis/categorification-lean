/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRedUpWord
import Categorification.WeightedKLR.RedStrands.DoubleInterchange
import StringDiagrams.InterchangeLayers

/-!
# Moving a red past a black generator inside an upward word

In Webster, arXiv:1309.3796v2, §4.5, Definition 4.24, (4.4c,d) move the
upward black generator through red. Interchange with spectator strands
permits the move in the interior of an arbitrary upward block.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (r : Fin ℓ)

local notation "S" => signature RD Λ
local notation "B" => DoubleStrand I ℓ
private abbrev E (i : I) : B := .inl (true, i)
private abbrev R (r : Fin ℓ) : B := .inr r

private def crossingLayers (u : List B) (s : List I) (v : List B) : List (Layer S) :=
  match s with
  | [] => []
  | i :: t => layer RD Λ μ u (.redBlack r (true, i)) (upBlackWord t ++ v) ::
      crossingLayers (u ++ [E i]) t v

local notation "travel" => crossingLayers RD Λ μ r
local notation "loc" => layer RD Λ μ

private theorem layers_redThrough (u : List B) (s : List I) (v : List B) :
    Diagram.layers (redThroughUpWord RD Λ μ r u s v) = travel u s v := by
  induction s generalizing u with
  | nil => simp [redThroughUpWord, crossingLayers]
  | cons i s ih =>
    simp [redThroughUpWord, crossingLayers, moveDiagram, ih, E]

private theorem travel_append (u : List B) (p q : List I) (v : List B) :
    travel u (p ++ q) v = travel u p (upBlackWord q ++ v) ++ travel (u ++ upBlackWord p) q v := by
  induction p generalizing u with
  | nil => simp [crossingLayers, upBlackWord]
  | cons i p ih =>
    simp [crossingLayers, upBlackWord, ih, E, List.append_assoc]

/-- Replacement of signed layers by other layers with the same endpoints and
class. The input is an arbitrary typed occurrence of the displayed sequence. -/
private def Replaces (L K : List (Layer S)) : Prop :=
  ∀ {a b : Obj S} (f : a ⟶ b), Diagram.layers f = L →
    ∃ g : a ⟶ b, Diagram.layers g = K ∧ P.diag f = P.diag g

private theorem Replaces.frame {A K : List (Layer S)}
    (h : Replaces RD Λ P A K) (pre post : List (Layer S)) :
    Replaces RD Λ P (pre ++ A ++ post) (pre ++ K ++ post) := by
  intro a b f hf
  obtain ⟨hF, hpost⟩ := (hf ▸ Diagram.chain f).of_append
  obtain ⟨hpre, hA⟩ := hF.of_append
  obtain ⟨g, hg, he⟩ := h (Diagram.mk A hA) rfl
  let z := Diagram.mk pre hpre ≫ g ≫ Diagram.mk post hpost
  refine ⟨z, by simp [z, hg, List.append_assoc], ?_⟩
  have h' : f = Diagram.mk pre hpre ≫ Diagram.mk A hA ≫ Diagram.mk post hpost := by
    apply Diagram.ext
    simp [hf, List.append_assoc]
  rw [h']
  simp only [z, Presentation.diag_comp, he]

private theorem replaces_of_diag {a b : Obj S} (f g : a ⟶ b) (hn : Diagram.layers f ≠ [])
    (h : P.diag f = P.diag g) : Replaces RD Λ P (Diagram.layers f) (Diagram.layers g) := by
  intro c d f' hf
  have hf' := hf ▸ Diagram.chain f'
  have hs : c = a := by
    generalize he : Diagram.layers f = ls at hn hf' ⊢
    have hchain : Chain a ls b := he ▸ Diagram.chain f
    cases ls with
    | nil => contradiction
    | cons L ls => exact hf'.2.1.symm.trans hchain.2.1
  subst c
  obtain rfl : d = b := hf'.target_eq.symm.trans (Diagram.chain f).target_eq
  exact ⟨g, rfl, (P.diag_eq_of_layers_eq hf).trans h⟩

private theorem swap_separated (u : List B) (g : Move I ℓ) (m : List B)
    (h : Move I ℓ) (v : List B) :
    Replaces RD Λ P
      [loc u g (m ++ h.bottom ++ v), loc (u ++ g.top ++ m) h v]
      [loc (u ++ g.bottom ++ m) h v, loc u g (m ++ h.top ++ v)] := by
  let f := separatedLeft RD Λ μ u g m v h.bottom ≫ separatedRight RD Λ μ u m h v g.top
  let d := separatedRight RD Λ μ u m h v g.bottom ≫ separatedLeft RD Λ μ u g m v h.top
  have he : P.diag f = P.diag d := by
    simpa only [f, d, Presentation.diag_comp] using
      separatedMoves_comm RD Λ P μ u g m h v
  have hv : Replaces RD Λ P (Diagram.layers f) (Diagram.layers d) := replaces_of_diag RD Λ P f d (by simp [f, separatedLeft, separatedRight, moveDiagram]) he
  intro a b z hz
  apply hv z
  simpa [f, separatedLeft, separatedRight, moveDiagram, List.append_assoc] using hz

private theorem swap_separated_reverse (u : List B) (g : Move I ℓ) (m : List B)
    (h : Move I ℓ) (v : List B) :
    Replaces RD Λ P
      [loc (u ++ g.bottom ++ m) h v, loc u g (m ++ h.top ++ v)]
      [loc u g (m ++ h.bottom ++ v), loc (u ++ g.top ++ m) h v] := by
  let f := separatedLeft RD Λ μ u g m v h.bottom ≫ separatedRight RD Λ μ u m h v g.top
  let d := separatedRight RD Λ μ u m h v g.bottom ≫ separatedLeft RD Λ μ u g m v h.top
  have he : P.diag f = P.diag d := by
    simpa only [f, d, Presentation.diag_comp] using separatedMoves_comm RD Λ P μ u g m h v
  have hv : Replaces RD Λ P (Diagram.layers d) (Diagram.layers f) :=
    replaces_of_diag RD Λ P d f (by simp [d, separatedLeft, separatedRight, moveDiagram]) he.symm
  intro a b z hz
  apply hv z
  simpa [d, separatedLeft, separatedRight, moveDiagram, List.append_assoc] using hz

private theorem slide_through_left_word (u : List B) (p : List I) (m : List B) (g : Move I ℓ) (v : List B) :
    Replaces RD Λ P
      (loc (u ++ [R r] ++ upBlackWord p ++ m) g v :: travel u p (m ++ g.top ++ v))
      (travel u p (m ++ g.bottom ++ v) ++ [loc (u ++ upBlackWord p ++ [R r] ++ m) g v]) := by
  induction p generalizing u with
  | nil =>
    intro a b f hf
    exact ⟨f, by simpa [crossingLayers, upBlackWord, List.append_assoc] using hf, rfl⟩
  | cons i p ih =>
    let s : Move I ℓ := .redBlack r (true, i)
    let z := travel (u ++ [E i]) p (m ++ g.top ++ v)
    let l := loc u s (upBlackWord p ++ (m ++ g.bottom ++ v))
    have h₁ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P (swap_separated_reverse RD Λ P μ u s (upBlackWord p ++ m) g v) [] z
    have h₂ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P (ih (u ++ [E i])) [l] []
    intro a b f hf
    obtain ⟨d, hd, hfd⟩ := h₁ f (by simpa [crossingLayers, upBlackWord, R, E, s, z, Move.bottom,
      List.append_assoc] using hf)
    obtain ⟨e, he, hde⟩ := h₂ d (by simpa [s, l, z, E, R, Move.top, List.append_assoc] using hd)
    exact ⟨e, by simpa [crossingLayers, upBlackWord, E, R, s, l, List.append_assoc] using he, hfd.trans hde⟩

private theorem slide_through_right_word (u : List B) (g : Move I ℓ) (m : List B) (q : List I) (v : List B) :
    Replaces RD Λ P
      (loc u g (m ++ [R r] ++ upBlackWord q ++ v) :: travel (u ++ g.top ++ m) q v)
      (travel (u ++ g.bottom ++ m) q v ++ [loc u g (m ++ upBlackWord q ++ [R r] ++ v)]) := by
  induction q generalizing m with
  | nil =>
    intro a b f hf
    exact ⟨f, by simpa [crossingLayers, upBlackWord, List.append_assoc] using hf, rfl⟩
  | cons i q ih =>
    let s : Move I ℓ := .redBlack r (true, i)
    let z := travel ((u ++ g.top ++ m) ++ [E i]) q v
    let l := loc (u ++ g.bottom ++ m) s (upBlackWord q ++ v)
    have h₁ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P (swap_separated RD Λ P μ u g m s (upBlackWord q ++ v)) [] z
    have h₂ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P (ih (m ++ [E i])) [l] []
    intro a b f hf
    obtain ⟨d, hd, hfd⟩ := h₁ f (by simpa [crossingLayers, upBlackWord, R, E, s, z, Move.bottom,
      List.append_assoc] using hf)
    obtain ⟨e, he, hde⟩ := h₂ d (by simpa [s, l, z, E, R, Move.top, List.append_assoc] using hd)
    exact ⟨e, by simpa [crossingLayers, upBlackWord, E, R, s, l, List.append_assoc] using he, hfd.trans hde⟩

private theorem up_append (p q : List I) :
    upBlackWord (ℓ := ℓ) (p ++ q) = upBlackWord p ++ upBlackWord q := List.map_append ..

private theorem black_bottom (g : UpBlackMove I) :
    (Move.black (ℓ := ℓ) g.shape).bottom = upBlackWord g.dom := by cases g <;> rfl

private theorem black_top (g : UpBlackMove I) :
    (Move.black (ℓ := ℓ) g.shape).top = upBlackWord g.cod := by cases g <;> rfl

local notation "T" => addRedUpSlideRelations RD Λ P

private abbrev SlideLaw := ∀ (u : List B) (g : UpBlackMove I) (v : List B),
  P.diag (redUpSlide RD Λ μ u r g v false) = P.diag (redUpSlide RD Λ μ u r g v true)

private theorem cross_active (hs : SlideLaw RD Λ P μ r) (u : List B) (g : UpBlackMove I) (v : List B) :
    Replaces RD Λ P
      (loc (u ++ [R r]) (.black g.shape) v :: travel u g.cod v)
      (travel u g.dom v ++ [loc u (.black g.shape) (R r :: v)]) := by
  let f := redUpSlide RD Λ μ u r g v false
  let d := redUpSlide RD Λ μ u r g v true
  have hn : Diagram.layers f ≠ [] := by
    simp [f, redUpSlide, upBlackMoveDiagram, moveDiagram]
  have hv : Replaces RD Λ P (Diagram.layers f) (Diagram.layers d) :=
    replaces_of_diag RD Λ P f d hn (hs u g v)
  intro a b z hz
  obtain ⟨z', hz', he⟩ := hv z (by simpa [f, redUpSlide, upBlackMoveDiagram, moveDiagram,
    R, layers_redThrough] using hz)
  exact ⟨z', by simpa [d, redUpSlide, upBlackMoveDiagram, moveDiagram, R, layers_redThrough] using hz', he⟩

private theorem cross_inside (hs : SlideLaw RD Λ P μ r) (u : List B) (p : List I) (g : UpBlackMove I) (q : List I) (v : List B) :
    Replaces RD Λ P
      (loc (u ++ [R r] ++ upBlackWord p) (.black g.shape) (upBlackWord q ++ v) ::
        travel u (p ++ g.cod ++ q) v)
      (travel u (p ++ g.dom ++ q) v ++ [loc (u ++ upBlackWord p) (.black g.shape) (upBlackWord q ++ R r :: v)]) := by
  let u' := u ++ upBlackWord p
  let v' := upBlackWord q ++ v
  let τ₁ := travel u p (upBlackWord g.dom ++ v')
  let τ₂ := travel u' g.dom v'
  let σ₂ := travel u' g.cod v'
  let σ₃ := travel (u' ++ upBlackWord g.cod) q v
  have h₁ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P
    (slide_through_left_word RD Λ P μ r u p [] (.black g.shape) v') [] (σ₂ ++ σ₃)
  have h₂ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P (cross_active RD Λ P μ r hs u' g v') τ₁ σ₃
  have h₃ : Replaces RD Λ P _ _ := Replaces.frame RD Λ P
    (slide_through_right_word RD Λ P μ r u' (.black g.shape) [] q v) (τ₁ ++ τ₂) []
  intro a b f hf
  obtain ⟨f₁, hf₁, he₁⟩ := h₁ f (by simpa [v', u', σ₂, σ₃, travel_append, up_append, black_top,
    List.append_assoc] using hf)
  obtain ⟨f₂, hf₂, he₂⟩ := h₂ f₁ (by simpa [τ₁, u', σ₂, black_bottom, List.append_assoc] using hf₁)
  obtain ⟨f₃, hf₃, he₃⟩ := h₃ f₂ (by simpa [τ₂, σ₃, v', black_top, List.append_assoc] using hf₂)
  exact ⟨f₃, by simpa [τ₁, τ₂, u', v', travel_append, up_append, black_bottom,
    List.append_assoc] using hf₃, he₁.trans (he₂.trans he₃)⟩

/-- An upward KLR generator acting inside the word, with spectator strands on each side. -/
def upWordMove (u : List B) (p : List I) (g : UpBlackMove I) (q : List I) (v : List B) :
    obj RD Λ μ (u ++ upBlackWord (p ++ g.dom ++ q) ++ v) ⟶
      obj RD Λ μ (u ++ upBlackWord (p ++ g.cod ++ q) ++ v) :=
  Diagram.cast (upBlackMoveDiagram RD Λ μ (u ++ upBlackWord p) g (upBlackWord q ++ v))
    (by simp [up_append, List.append_assoc]) (by simp [up_append, List.append_assoc])

private theorem word_move_of_slides (hs : SlideLaw RD Λ P μ r) (u : List B) (p : List I) (g : UpBlackMove I) (q : List I) (v : List B) :
    P.diag (upWordMove RD Λ μ (u ++ [R r]) p g q v) ≫
      P.diag (redThroughUpWord RD Λ μ r u (p ++ g.cod ++ q) v) =
    P.diag (redThroughUpWord RD Λ μ r u (p ++ g.dom ++ q) v) ≫
      P.diag (Diagram.cast (upWordMove RD Λ μ u p g q (R r :: v))
        (by simp [List.append_assoc]) (by simp [List.append_assoc])) := by
  rw [← P.diag_comp, ← P.diag_comp]
  let f := upWordMove RD Λ μ (u ++ [R r]) p g q v ≫ redThroughUpWord RD Λ μ r u (p ++ g.cod ++ q) v
  obtain ⟨d, hd, hf⟩ := cross_inside RD Λ P μ r hs u p g q v f (by
    simp [f, upWordMove, upBlackMoveDiagram, moveDiagram, layers_redThrough, List.append_assoc])
  apply hf.trans (P.diag_eq_of_layers_eq ?_)
  rw [hd]
  simp [upWordMove, upBlackMoveDiagram, moveDiagram, layers_redThrough, List.append_assoc]

/-- Webster's (4.4c,d) and distant interchange give the red slide past a dot or
crossing acting anywhere inside an arbitrarily long upward word. -/
theorem redThroughUpWord_move (u : List B) (p : List I) (g : UpBlackMove I) (q : List I) (v : List B) :
    (T).diag (upWordMove RD Λ μ (u ++ [R r]) p g q v) ≫
      (T).diag (redThroughUpWord RD Λ μ r u (p ++ g.cod ++ q) v) =
    (T).diag (redThroughUpWord RD Λ μ r u (p ++ g.dom ++ q) v) ≫
      (T).diag (Diagram.cast (upWordMove RD Λ μ u p g q (R r :: v))
        (by simp [List.append_assoc]) (by simp [List.append_assoc])) :=
  word_move_of_slides RD Λ (T) μ r (fun u g v => redUp_slide RD Λ P μ u r g v) u p g q v

/-- Read an upward KLR diagram with a red strand fixed just to its left. -/
def upLeftRed (u v : List B) : Interpretation (KLR.Diagram.sig I) P.Presented where
  obj a := P.obj (obj RD Λ μ (u ++ [.inr r] ++ upBlackWord a.word ++ v))
  layer L _ := P.diag (upWordMove RD Λ μ (u ++ [.inr r]) L.left L.gen L.right v)

/-- Read the same diagram with red fixed just to its right. -/
def upRightRed (u v : List B) : Interpretation (KLR.Diagram.sig I) P.Presented where
  obj a := P.obj (obj RD Λ μ (u ++ upBlackWord a.word ++ [.inr r] ++ v))
  layer L _ := P.diag (Diagram.cast (upWordMove RD Λ μ u L.left L.gen L.right (.inr r :: v))
    (by simp [List.append_assoc, Layer.dom, KLR.Diagram.sig]) (by simp [List.append_assoc, Layer.cod, KLR.Diagram.sig]))

private def wordNatOfSlides (hs : SlideLaw RD Λ P μ r) (u v : List B) :
    (upLeftRed RD Λ P μ r u v).functor ⟶ (upRightRed RD Λ P μ r u v).functor where
  app a := P.diag (redThroughUpWord RD Λ μ r u a.word v)
  naturality {a b} f := by
    let F := upLeftRed RD Λ P μ r u v
    let G := upRightRed RD Λ P μ r u v
    let x (a : Obj (KLR.Diagram.sig I)) : F.obj a ⟶ G.obj a :=
      P.diag (redThroughUpWord RD Λ μ r u a.word v)
    obtain ⟨ls, h⟩ := f
    change F.mapChain a ls b h ≫ x b = x a ≫ G.mapChain a ls b h
    induction ls generalizing a with
    | nil => cases h; simp [Interpretation.mapChain]
    | cons L ls ih =>
      obtain ⟨hv, rfl, hrest⟩ := h
      have he : F.layer L hv ≫ x L.cod = x L.dom ≫ G.layer L hv :=
        word_move_of_slides RD Λ P μ r hs u L.left L.gen L.right v
      simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp]
      rw [Category.assoc, ih hrest, ← Category.assoc, he, Category.assoc]

/-- A red strand moves past any upward KLR diagram, including diagrams with arbitrarily
many crossings and spectator strands. This iterates the two slides in Webster,
arXiv:1309.3796v2, §4.5, Definition 4.24, (4.4c,d). -/
def redUpWordNaturality (u v : List B) :
    (upLeftRed RD Λ (T) μ r u v).functor ⟶ (upRightRed RD Λ (T) μ r u v).functor :=
  wordNatOfSlides RD Λ (T) μ r (fun u g v => redUp_slide RD Λ P μ u r g v) u v

/-- In the presence of (4.4e) the red slide past an entire upward KLR diagram is
invertible, so both traversals surrounding the diagram can be removed. -/
def redUpWordNaturalIso (u v : List B) :
    let P' := addRedUpRelations RD Λ k (T)
    (upLeftRed RD Λ P' μ r u v).functor ≅ (upRightRed RD Λ P' μ r u v).functor := by
  let P' := addRedUpRelations RD Λ k (T)
  have hs : SlideLaw RD Λ P' μ r := fun l g t =>
    P'.diag_eq_of_rel (.inl (.inr ⟨μ, l, r, g, t, false⟩)) rfl
  exact NatIso.ofComponents (fun a => redUpWordIso RD Λ (T) μ r u a.word v)
    (fun d => (wordNatOfSlides RD Λ P' μ r hs u v).naturality d)

/-- Removing both red traversals surrounding an arbitrary upward KLR diagram, the
repeated-crossing reduction in Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28
for a red strand and an upward block. -/
theorem redUp_clear_diagram (u v : List B) {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    let P' := addRedUpRelations RD Λ k (T)
    P'.diag (redThroughUpWord RD Λ μ r u a.word v) ≫ (upRightRed RD Λ P' μ r u v).functor.map d ≫
      P'.diag (upWordThroughRed RD Λ μ r u b.word v) =
    (upLeftRed RD Λ P' μ r u v).functor.map d := by
  let e := redUpWordNaturalIso RD Λ P μ r u v
  change e.hom.app a ≫ _ ≫ e.inv.app b = _
  rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end Categorification.Stendhal.DoubleDiagram
