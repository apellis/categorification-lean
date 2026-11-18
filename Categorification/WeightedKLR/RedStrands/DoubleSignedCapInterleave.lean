/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBlock
import StringDiagrams.InterchangeLayers

/-!
# Interchange and the signed crossing filtration

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, using the cap-block step of
Khovanov–Lauda III, arXiv:0807.3250v1, Proposition 3.11. Interchange of
disjoint signed blocks moves whole sideways crossings. The crossing
filtration transports the correction of a braid through surrounding layers.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams Presentation

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

local notation "B" => DoubleStrand I ℓ
local notation "S" => signature RD Λ

/-- Extend the two contexts of every signed layer. -/
def signedWhisk (L R : List B) (ls : List (SignedLayer I ℓ)) : List (SignedLayer I ℓ) :=
  ls.map fun (a, g, b) => (L ++ a, g, b ++ R)

theorem signedChain_whisk (L R : List B) {s t : List B} {ls : List (SignedLayer I ℓ)}
    (h : signedChain s ls t) : signedChain (L ++ s ++ R) (signedWhisk L R ls) (L ++ t ++ R) := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨a,g,b⟩ := x
    rcases h with ⟨rfl, h⟩
    refine ⟨by simp [List.append_assoc], ?_⟩
    simpa only [signedWhisk, List.append_assoc] using ih h

private theorem signedChain_endWeight {s t : List B} {ls : List (SignedLayer I ℓ)}
    (h : signedChain s ls t) (μ : X) : endWeight RD Λ μ s = endWeight RD Λ μ t := by
  induction ls generalizing s with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨a,g,b⟩ := x
    rcases h with ⟨rfl, h⟩
    refine Eq.trans ?_ (ih h)
    simp only [endWeight_append, g.endWeight_top]

private theorem signedChain_layerWeight {s t : List B} {ls : List (SignedLayer I ℓ)}
    (h : signedChain s ls t) (μ : X) {a b : List B} {g : Move I ℓ} (hm : (a,g,b) ∈ ls) :
    endWeight RD Λ μ s = endWeight RD Λ μ (a ++ g.bottom ++ b) := by
  induction ls generalizing s with
  | nil => simp at hm
  | cons x ls ih =>
    obtain ⟨u,g',v⟩ := x
    rcases h with ⟨rfl, h⟩
    rcases List.mem_cons.mp hm with hx | hx
    · cases hx; rfl
    · refine Eq.trans ?_ (ih h hx)
      simp only [endWeight_append, g'.endWeight_top]

private theorem signedLayers_whisk (μ : X) (L R : List B) {s t : List B} {ls : List (SignedLayer I ℓ)}
    (h : signedChain s ls t) :
    signedLayers RD Λ μ (signedWhisk L R ls) =
      (signedLayers RD Λ (endWeight RD Λ μ L) ls).map (·.whisker (obj RD Λ μ L)
        (colours RD Λ (endWeight RD Λ μ (L ++ s)) R)) := by
  unfold signedWhisk signedLayers
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  rintro ⟨a,g,b⟩ hm
  have hweight := signedChain_layerWeight RD Λ h (endWeight RD Λ μ L) hm
  simp only [endWeight_append] at hweight
  apply Layer.ext
  · rfl
  · simp [layer, Layer.whisker, obj, colours_append]
  · simp [layer, Layer.whisker, endWeight_append]
  · simp [layer, Layer.whisker, endWeight_append, colours_append, hweight]

/-- Interchange of disjoint signed blocks, including a sideways crossing with
its three actual layers. -/
theorem signedDg_interchange (P : Presentation.{w,max u v} S k) (μ : X) (L R : List B)
    {a a' b b' : List B} {F G : List (SignedLayer I ℓ)}
    (hF : signedChain a F a') (hG : signedChain b G b') :
    signedDg RD Λ P μ (L ++ a ++ b ++ R) (L ++ a' ++ b' ++ R)
        (signedWhisk L (b ++ R) F ++ signedWhisk (L ++ a') R G) =
      signedDg RD Λ P μ (L ++ a ++ b ++ R) (L ++ a' ++ b' ++ R)
        (signedWhisk (L ++ a) R G ++ signedWhisk L (b' ++ R) F) := by
  have hl := (signedChain_whisk L (b ++ R) hF).append
    (by simpa only [List.append_assoc] using signedChain_whisk (L ++ a') R hG)
  have hr := (signedChain_whisk (L ++ a) R hG).append
    (by simpa only [List.append_assoc] using signedChain_whisk L (b' ++ R) hF)
  have hl' : signedChain (L ++ a ++ b ++ R)
      (signedWhisk L (b ++ R) F ++ signedWhisk (L ++ a') R G) (L ++ a' ++ b' ++ R) :=
    by simpa only [List.append_assoc] using hl
  have hr' : signedChain (L ++ a ++ b ++ R)
      (signedWhisk (L ++ a) R G ++ signedWhisk L (b' ++ R) F) (L ++ a' ++ b' ++ R) :=
    by simpa only [List.append_assoc] using hr
  let p := obj RD Λ μ L
  let η := endWeight RD Λ μ L
  let θ := endWeight RD Λ η a
  let τ := colours RD Λ (endWeight RD Λ θ b) R
  let A := obj RD Λ η a
  let A' := obj RD Λ η a'
  let B₀ := obj RD Λ θ b
  let B₁ := obj RD Λ θ b'
  have hA : endWeight RD Λ η a = endWeight RD Λ η a' := signedChain_endWeight RD Λ hF η
  have hB : endWeight RD Λ θ b = endWeight RD Λ θ b' := signedChain_endWeight RD Λ hG θ
  have e₀ : sbs p [] τ A B₀ = obj RD Λ μ (L ++ a ++ b ++ R) := by
    refine Obj.ext ?_ ?_
    · rfl
    · simp [p, A, B₀, τ, θ, η, obj, colours_append, List.append_assoc]
  have e₁ : sbs p [] τ A' B₁ = obj RD Λ μ (L ++ a' ++ b' ++ R) := by
    refine Obj.ext ?_ ?_
    · rfl
    · have he := hA
      change endWeight RD Λ (endWeight RD Λ μ L) a = _ at he
      have hb := hB
      simp [p, A', B₁, τ, θ, η, obj, colours_append, ← he, ← hb,
        List.append_assoc]
  have side : SideBySideOK p [] τ A B₀ := by
    refine ⟨?_, ?_, ?_⟩
    · change (S).ok _ (sbs p [] τ A B₀).word
      rw [e₀]
      exact colours_ok ..
    · exact colours_endR ..
    · exact colours_endR ..
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ hl')
  let g := Diagram.mk _ (chain_signedLayers RD Λ μ hr')
  have eqv : P.diag (Diagram.cast f e₀.symm e₁.symm) = P.diag (Diagram.cast g e₀.symm e₁.symm) := by
    apply P.diag_interchange_layers_of_even p [] τ
      (chain_signedLayers RD Λ η hF) (chain_signedLayers RD Λ θ hG) (fun _ _ _ _ => Or.inl rfl) side
    · simp only [f, Diagram.layers_cast, Diagram.layers_mk, signedLayers, List.map_append]
      change signedLayers RD Λ μ (signedWhisk L (b ++ R) F) ++
        signedLayers RD Λ μ (signedWhisk (L ++ a') R G) = _
      rw [signedLayers_whisk RD Λ μ L _ hF, signedLayers_whisk RD Λ μ _ R hG]
      simp [p, τ, θ, η, obj, colours_append, endWeight_append, ← hA, List.append_assoc, signedLayers]
    · simp only [g, Diagram.layers_cast, Diagram.layers_mk, signedLayers, List.map_append]
      change signedLayers RD Λ μ (signedWhisk (L ++ a) R G) ++
        signedLayers RD Λ μ (signedWhisk L (b' ++ R) F) = _
      rw [signedLayers_whisk RD Λ μ _ R hG, signedLayers_whisk RD Λ μ L _ hF]
      simp [p, τ, θ, η, obj, colours_append, endWeight_append, ← hB, List.append_assoc, signedLayers]
  rw [signedDg_of RD Λ P μ hl', signedDg_of RD Λ P μ hr']
  apply P.castHom_injective e₀.symm e₁.symm
  simpa only [Presentation.castHom_diag] using eqv


/-- A pair of neighbouring strands may cross if at least one is black. -/
def CanCross (x y : B) : Prop :=
  match x, y with
  | .inr _, .inr _ => False
  | _, _ => True

/-- The physical layers of a signed crossing; the unused red/red case is empty. -/
def signedCrossLayers (L : List B) (x : B) : B → List B → List (SignedLayer I ℓ)
  | .inl l, R => crossBlackLeft L x l R
  | .inr r, R => match x with
    | .inl l => [(L, .blackRed l r, R)]
    | .inr _ => []

theorem signedCrossLayers_chain (L : List B) {x y : B} (h : CanCross x y) (R : List B) :
    signedChain (L ++ [x,y] ++ R) (signedCrossLayers L x y R) (L ++ [y,x] ++ R) := by
  cases y with
  | inl l => exact crossBlackLeft_chain L x l R
  | inr r =>
    cases x with
    | inl l => simp [signedCrossLayers, signedChain, Move.bottom, Move.top]
    | inr z => exact False.elim h

theorem signedCrossLayers_crossings (L : List B) {x y : B} (h : CanCross x y) (R : List B) :
    signedCrossings (signedCrossLayers L x y R) = 1 := by
  cases y with
  | inl l => exact crossBlackLeft_crossings L x l R
  | inr r =>
    cases x with
    | inl l => rfl
    | inr z => exact False.elim h

private theorem crossBlackLeft_whisk (L R a b : List B) (x : B) (l : Letter I) :
    signedWhisk L R (crossBlackLeft a x l b) = crossBlackLeft (L ++ a) x l (b ++ R) := by
  cases x with
  | inr r => rfl
  | inl x =>
    obtain ⟨ε, i⟩ := x
    obtain ⟨δ, j⟩ := l
    cases ε <;> cases δ <;> simp [signedWhisk, crossBlackLeft, upwardMateLayers, List.append_assoc]

/-- Extend the exterior words of a signed crossing. -/
theorem signedCrossLayers_whisk (L R a b : List B) (x y : B) :
    signedWhisk L R (signedCrossLayers a x y b) = signedCrossLayers (L ++ a) x y (b ++ R) := by
  cases y with
  | inl l => exact crossBlackLeft_whisk L R a b x l
  | inr r => cases x <;> rfl

/-- Whiskering a sweep extends its exterior words. -/
theorem sweepBlackLeft_whisk (L R a b S₀ : List B) (l : Letter I) :
    signedWhisk L R (sweepBlackLeft a S₀ l b) = sweepBlackLeft (L ++ a) S₀ l (b ++ R) := by
  induction S₀ generalizing a with
  | nil => rfl
  | cons x S₀ ih =>
    simp only [sweepBlackLeft]
    rw [show signedWhisk L R (_ ++ _) = signedWhisk L R _ ++ signedWhisk L R _ from List.map_append,
      ih, crossBlackLeft_whisk]
    simp only [List.append_assoc]

/-- The crossing filtration on the image of the raw signed Hom. -/
def signedCrossingSpan (P : Presentation.{w,max u v} S k) (μ : X) (s t : List B) (n : ℕ) :
    Submodule k (P.obj (obj RD Λ μ s) ⟶ P.obj (obj RD Λ μ t)) :=
  Submodule.span k {f | ∃ d : obj RD Λ μ s ⟶ obj RD Λ μ t, crossingNumber d ≤ n ∧ f = P.diag d}

/-- Composing with two fixed segments shifts the bound by their crossing numbers. -/
theorem signedCrossingSpan_comp (P : Presentation.{w,max u v} S k) (μ : X)
    {s a b t : List B} (pre : obj RD Λ μ s ⟶ obj RD Λ μ a) (post : obj RD Λ μ b ⟶ obj RD Λ μ t)
    {n : ℕ} {f : P.obj (obj RD Λ μ a) ⟶ P.obj (obj RD Λ μ b)}
    (hf : f ∈ signedCrossingSpan RD Λ P μ a b n) :
    P.diag pre ≫ f ≫ P.diag post ∈ signedCrossingSpan RD Λ P μ s t
      (crossingNumber pre + n + crossingNumber post) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd, rfl⟩ := hg
    apply Submodule.subset_span
    refine ⟨(pre ≫ d) ≫ post, ?_, ?_⟩
    · simpa only [crossingNumber_comp] using Nat.add_le_add_right (Nat.add_le_add_left hd _) _
    · rw [Presentation.diag_comp, Presentation.diag_comp, Category.assoc]
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.add_comp, Preadditive.comp_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [Linear.smul_comp, Linear.comp_smul]
    exact Submodule.smul_mem _ a hf

/-- Compose a bounded correction with a raw exterior diagram and project it
to the strict lower crossing filtration for the original composite. -/
theorem signedCrossingSpan_in_fewerCrossings (P : Presentation.{w,max u v} S k) (μ : X)
    {s t : List B} {a b c : Obj S} (pre : a ⟶ obj RD Λ μ s) (post : obj RD Λ μ t ⟶ b)
    (tail : b ⟶ c) {M : Type*} [AddCommGroup M] [Module k M]
    (π : (P.obj a ⟶ P.obj c) →ₗ[k] M) {n m : ℕ}
    {f : P.obj (obj RD Λ μ s) ⟶ P.obj (obj RD Λ μ t)}
    (hf : f ∈ signedCrossingSpan RD Λ P μ s t n)
    (hm : crossingNumber pre + n + crossingNumber post < m) :
    π (P.diag pre ≫ f ≫ P.diag (post ≫ tail)) ∈
      fewerCrossings k (fun d => π (P.diag d)) tail m := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨e, he, rfl⟩ := hg
    apply Submodule.subset_span
    refine ⟨(pre ≫ e) ≫ post, ?_, ?_⟩
    · simp only [crossingNumber_comp]
      omega
    · simp [Presentation.diag_comp, Category.assoc]
  | zero => simp
  | add f g _ _ hf hg =>
    rw [Preadditive.add_comp, Preadditive.comp_add, map_add]
    exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [Linear.smul_comp, Linear.comp_smul, map_smul]
    exact Submodule.smul_mem _ c hf

/-- Insert a filtration-bounded difference at a specified level of a signed diagram. -/
theorem signedDg_replace_span (P : Presentation.{w,max u v} S k) (μ : X)
    {s a b t : List B} {pre F G post : List (SignedLayer I ℓ)}
    (hp : signedChain s pre a) (hf : signedChain a F b) (hg : signedChain a G b)
    (ht : signedChain b post t) {n : ℕ}
    (he : signedDg RD Λ P μ a b F - signedDg RD Λ P μ a b G ∈ signedCrossingSpan RD Λ P μ a b n) :
    signedDg RD Λ P μ s t (pre ++ F ++ post) - signedDg RD Λ P μ s t (pre ++ G ++ post) ∈
      signedCrossingSpan RD Λ P μ s t (signedCrossings pre + n + signedCrossings post) := by
  let d := Diagram.mk _ (chain_signedLayers RD Λ μ hp)
  let e := Diagram.mk _ (chain_signedLayers RD Λ μ ht)
  have h := signedCrossingSpan_comp RD Λ P μ d e he
  rw [crossingNumber_of_signedLayers RD Λ μ d pre rfl,
    crossingNumber_of_signedLayers RD Λ μ e post rfl] at h
  rw [Preadditive.sub_comp, Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
    ← signedDg_of RD Λ P μ hp, ← signedDg_of RD Λ P μ ht,
    signedDg_comp RD Λ P μ hp hf, signedDg_comp RD Λ P μ hp hg,
    signedDg_comp RD Λ P μ (hp.append hf) ht, signedDg_comp RD Λ P μ (hp.append hg) ht] at h
  exact h

/-- The `s₀s₁s₀` braid on a signed pair and a terminal black strand. -/
def signedCapBraidLeft (L : List B) (x y : B) (l : Letter I) (R : List B) : List (SignedLayer I ℓ) :=
  signedCrossLayers L x y (.inl l :: R) ++ crossBlackLeft (L ++ [y]) x l R ++
    crossBlackLeft L y l (x :: R)

/-- The `s₁s₀s₁` braid on a signed pair and a terminal black strand. -/
def signedCapBraidRight (L : List B) (x y : B) (l : Letter I) (R : List B) : List (SignedLayer I ℓ) :=
  crossBlackLeft (L ++ [x]) y l R ++ crossBlackLeft L x l (y :: R) ++
    signedCrossLayers (L ++ [.inl l]) x y R

theorem signedCapBraidLeft_chain (L : List B) {x y : B} (hxy : CanCross x y) (l : Letter I) (R : List B) :
    signedChain (L ++ [x,y,.inl l] ++ R) (signedCapBraidLeft L x y l R) (L ++ [.inl l,y,x] ++ R) := by
  have h₁ := signedCrossLayers_chain L hxy (.inl l :: R)
  have h₂ := crossBlackLeft_chain (L ++ [y]) x l R
  have h₃ := crossBlackLeft_chain L y l (x :: R)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ h₃ ⊢
  exact (h₁.append h₂).append h₃

theorem signedCapBraidRight_chain (L : List B) {x y : B} (hxy : CanCross x y) (l : Letter I) (R : List B) :
    signedChain (L ++ [x,y,.inl l] ++ R) (signedCapBraidRight L x y l R) (L ++ [.inl l,y,x] ++ R) := by
  have h₁ := crossBlackLeft_chain (L ++ [x]) y l R
  have h₂ := crossBlackLeft_chain L x l (y :: R)
  have h₃ := signedCrossLayers_chain (L ++ [.inl l]) hxy R
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ h₃ ⊢
  exact (h₁.append h₂).append h₃

/-- Extend the exterior words of a cap block. -/
theorem signedCapBlock_whisk (L R p q U : List B) (l : Letter I) (d : ℕ) :
    signedWhisk L R (signedCapBlock p U l q d) = signedCapBlock (L ++ p) U l (q ++ R) d := by
  rw [signedCapBlock, signedCapBlock]
  simp only [show ∀ (F G : List (SignedLayer I ℓ)),
    signedWhisk L R (F ++ G) = signedWhisk L R F ++ signedWhisk L R G from fun _ _ => List.map_append,
    sweepBlackLeft_whisk, List.append_assoc]
  simp [signedWhisk, capLegDots, List.map_replicate, List.append_assoc]

end Categorification.Stendhal.DoubleDiagram
