/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffixQ
import Categorification.WeightedKLR.RedStrands.DoubleDiagramRewriting

/-!
# Bubble slides across a black boundary strand

Khovanov--Lauda, arXiv:0807.3250v1, §3.1.2, Propositions 3.3 and 3.4 and
their rotations, as used in §3.2.2, Lemma 3.9. Webster, arXiv:1309.3796v2,
§4.5, proof of Lemma 4.28, uses the slides to move bubbles to the far left.
Vertical reflection sends the KL III left-to-right slide to the physical
right-to-left slide, for either orientation of the black strand.

This is the version of `DoubleBlackBubbleSlide` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k] (sc : CL.CLScalars C k)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X) (L R : List (DoubleStrand I ℓ)) (l : Letter I)

local notation "K" => CLQ.pres RD k sc
local notation "ν" => endWeight RD Λ μ L
local notation "w₀" => (L ++ blackWord [l] ++ R)

/-- Reflect the black one-strand endomorphism into an arbitrary signed context. -/
abbrev blackLetterHomQ :
    End ((K).obj (ob RD ν [l])) →ₗ[k] End (P.obj (obj RD Λ μ w₀)) :=
  blackRectangleHomQ RD Λ sc μ L R [l] P hP [l] rfl rfl

local notation "F" => blackLetterHomQ RD Λ sc P hP μ L R l

/-- The span of dots on the black strand composed with elements of the bubble
algebra in the region physically to its left. -/
def blackBubbleLeftSpanQ : Submodule k (End (P.obj (obj RD Λ μ w₀))) :=
  Submodule.span k {f | ∃ (a : ℕ) (γ : End ((K).obj (ob RD ν []))),
    CLQ.IsBub RD k sc ν γ ∧ f = F (NF.dotsU (CLQ.pres RD k sc) ν l a) ≫ F (NF.bubRU (CLQ.pres RD k sc) ν l γ)}

/-- The reflected slide from KL III, arXiv:0807.3250v1, Propositions 3.3 and 3.4
and their rotations. A physical right bubble moves to the left of an up or
down black strand in any signed context. The strand acquires only dots. -/
theorem blackBubbleRight_mem_leftSpanQ {β : End ((K).obj (ob RD (wt RD ν [l]) []))}
    (hβ : CLQ.IsBub RD k sc (wt RD ν [l]) β) :
    F (NF.bubLU (CLQ.pres RD k sc) ν l β) ∈ blackBubbleLeftSpanQ RD Λ sc P hP μ L R l := by
  have h : CLQ.slideSetR RD k sc ν l ≤ (blackBubbleLeftSpanQ RD Λ sc P hP μ L R l).comap F := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, γ, hγ, rfl⟩
    change F (NF.dotsU (CLQ.pres RD k sc) ν l a ≫ NF.bubRU (CLQ.pres RD k sc) ν l γ) ∈ blackBubbleLeftSpanQ RD Λ sc P hP μ L R l
    have hm : F (NF.dotsU (CLQ.pres RD k sc) ν l a ≫ NF.bubRU (CLQ.pres RD k sc) ν l γ) =
        F (NF.dotsU (CLQ.pres RD k sc) ν l a) ≫ F (NF.bubRU (CLQ.pres RD k sc) ν l γ) :=
      blackRectangleHom_compQ RD Λ sc μ L R [l] P hP [l] [l] rfl rfl rfl _ _
    rw [hm]
    exact Submodule.subset_span ⟨a, γ, hγ, rfl⟩
  exact h (CLQ.bubLU_mem_slideSetR_gen ν l hβ)

private theorem signedChain_reflectQ {s t : List (Letter I)} {A : List (LayerData I)}
    (hA : SChain s A t) :
    signedChain (L ++ blackWord s ++ R)
      (A.map fun x => (L ++ blackWord x.2.2, .black (Sig.shape x.2.1), blackWord x.1 ++ R))
      (L ++ blackWord t ++ R) := by
  induction A generalizing s with
  | nil => exact congrArg (fun x => L ++ blackWord x ++ R) hA
  | cons x A ih =>
    rcases hA with ⟨rfl, h⟩
    refine ⟨?_, ?_⟩
    · simp [blackWord, List.reverse_append, List.append_assoc, Move.bottom, Sig.shape_dom]
    · simpa [blackWord, List.reverse_append, List.append_assoc, Move.top, Sig.shape_cod] using ih h

/-- A pure black layer list reflects to the corresponding signed layer list. -/
theorem blackLetterHom_dgQ (A : List (LayerData I)) (hA : SChain [l] A [l]) :
    F (NF.dg (CLQ.pres RD k sc) ν [l] [l] A) =
      signedDg RD Λ P μ w₀ w₀
        (A.map fun x => (L ++ blackWord x.2.2, .black (Sig.shape x.2.1), blackWord x.1 ++ R)) := by
  let d := mkD RD ν A hA
  have hm : F ((K).diag d) = P.diag (blackDiagram RD Λ μ L R d) := by
    have he := blackRectangleHom_linQ RD Λ sc μ L R [l] P hP [l] rfl rfl (LinDiagram.of d)
    rw [Presentation.lin_of, blackLinear_of, Presentation.lin_of] at he
    exact he
  rw [NF.dg_of hA, hm]
  symm
  exact signedDg_eq_diag_of_layers RD Λ P μ (signedChain_reflectQ L R hA) (blackDiagram RD Λ μ L R d)
    (by rw [layers_blackDiagram_mkD]; simp only [signedLayers, List.map_map, Function.comp_def])

/-- Dots in the one-strand rectangle are actual signed dots. -/
theorem blackLetterHom_dotsUQ (a : ℕ) :
    F (NF.dotsU (CLQ.pres RD k sc) ν l a) =
      signedDg RD Λ P μ w₀ w₀ (List.replicate a (L, .black (.dot l), R)) := by
  rw [NF.dotsU, blackLetterHom_dgQ RD Λ sc P hP μ L R l _ (by schain)]
  simp [blackWord]

-- In raw layer lists, the mirrored KL context on the right becomes the
-- physical prefix, and the mirrored context on the left becomes the suffix.

/-- A closed black diagram on the physical right appears after the black
letter in every signed layer. -/
theorem blackLetterHom_bubLU_dgQ (A : List (LayerData I)) (hA : SChain [] A []) :
    F (NF.bubLU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) (wt RD ν [l]) [] [] A)) =
      signedDg RD Λ P μ w₀ w₀
        (A.map fun x => (L ++ [.inl l] ++ blackWord x.2.2, .black (Sig.shape x.2.1),
          blackWord x.1 ++ R)) := by
  have hw : SChain [l] (A.map (whL [] [l])) [l] := hA.whisk [] [l]
  rw [show NF.bubLU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) (wt RD ν [l]) [] [] A) =
      NF.dg (CLQ.pres RD k sc) ν [l] [l] (A.map (whL [] [l])) from NF.plcL_dg (CLQ.pres RD k sc) ν [] [l] [] [] A,
    blackLetterHom_dgQ RD Λ sc P hP μ L R l _ hw]
  simp [List.map_map, Function.comp_def, whL, blackWord, List.append_assoc]

/-- A closed black diagram on the physical left appears before the black
letter in every signed layer. -/
theorem blackLetterHom_bubRU_dgQ (A : List (LayerData I)) (hA : SChain [] A []) :
    F (NF.bubRU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) ν [] [] A)) =
      signedDg RD Λ P μ w₀ w₀
        (A.map fun x => (L ++ blackWord x.2.2, .black (Sig.shape x.2.1),
          blackWord x.1 ++ [.inl l] ++ R)) := by
  have hw : SChain [l] (A.map (whL [l] [])) [l] := hA.whisk [l] []
  rw [show NF.bubRU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) ν [] [] A) =
      NF.dg (CLQ.pres RD k sc) ν [l] [l] (A.map (whL [l] [])) from NF.plcL_dg (CLQ.pres RD k sc) ν [l] [] [] [] A,
    blackLetterHom_dgQ RD Λ sc P hP μ L R l _ hw]
  simp [List.map_map, Function.comp_def, whL, blackWord, List.append_assoc]

section Cut

variable (w : List (DoubleStrand I ℓ)) (hw : L ++ R = w)

include hw in
private theorem blackCut_objQ :
    obj RD Λ μ (L ++ blackWord [] ++ R) = obj RD Λ μ w :=
  congrArg (obj RD Λ μ) (by simpa [blackWord] using hw)

local notation "e" => blackCut_objQ RD Λ μ L R w hw
local notation "F₀" => blackRectangleHomQ RD Λ sc μ L R [] P hP [] rfl rfl

/-- Insert an endomorphism of the empty black word at a specified cut of a
signed boundary. The operation is linear over the coefficient ring. -/
def blackCutHomQ : End ((K).obj (ob RD ν [])) →ₗ[k] End (P.obj (obj RD Λ μ w)) :=
  (P.castLinearEquiv e e).toLinearMap.comp (F₀)

local notation "G" => blackCutHomQ RD Λ sc P hP μ L R w hw

/-- The cut map takes a raw linear combination to its reflected signed image. -/
theorem blackCutHom_linQ (b : LEnd RD k (ob RD ν [])) :
    G ((K).lin b) = P.lin (LinDiagram.cast (blackLinear RD Λ k μ L R b) e e) := by
  change P.castHom e e (F₀ ((K).lin b)) = _
  rw [show F₀ ((K).lin b) = P.lin (blackLinear RD Λ k μ L R b) from
    blackRectangleHom_linQ RD Λ sc μ L R [] P hP [] rfl rfl b]
  rw [Presentation.lin_cast, Presentation.castHom]

/-- Insertion into a cut preserves composition of bubbles. -/
theorem blackCutHom_compQ (b c : End ((K).obj (ob RD ν []))) :
    G (b ≫ c) = G b ≫ G c := by
  change P.castHom e e (F₀ (b ≫ c)) = P.castHom e e (F₀ b) ≫ P.castHom e e (F₀ c)
  have hb : F₀ (b ≫ c) = F₀ b ≫ F₀ c :=
    blackRectangleHom_compQ RD Λ sc μ L R [] P hP [] [] rfl rfl rfl b c
  rw [hb, Presentation.castHom_comp]

/-- Insertion of the empty diagram is the identity on the signed boundary. -/
theorem blackCutHom_idQ : G (𝟙 _) = 𝟙 _ := by
  change P.castHom e e (F₀ (𝟙 _)) = _
  rw [show F₀ (𝟙 _) = 𝟙 _ from blackRectangleHom_idQ RD Λ sc μ L R [] P hP rfl]
  simp [Presentation.castHom]

/-- The bubble algebra acts by endomorphisms at an arbitrary signed cut. -/
def blackCutAlgHomQ : CLQ.EndOne RD k sc ν →ₐ[k] End (P.obj (obj RD Λ μ w)) where
  toFun b := G b.val
  map_zero' := map_zero G
  map_add' b c := map_add G b.val c.val
  map_one' := blackCutHom_idQ RD Λ sc P hP μ L R w hw
  map_mul' b c := by
    change G (c.val ≫ b.val) = G c.val ≫ G b.val
    exact blackCutHom_compQ RD Λ sc P hP μ L R w hw c.val b.val
  commutes' r := by
    rw [CLQ.EndOne.val_algebraMap, map_smul, blackCutHom_idQ, Algebra.algebraMap_eq_smul_one]
    rfl

/-- The algebra action at a cut is the same map on the underlying endomorphism. -/
theorem blackCutAlgHom_applyQ (b : CLQ.EndOne RD k sc ν) :
    blackCutAlgHomQ RD Λ sc P hP μ L R w hw b = G b.val := rfl

/-- Insertion identifies closed pure black layer lists with their signed
reflection at the cut. -/
theorem blackCutHom_dgQ (A : List (LayerData I)) (hA : SChain [] A []) :
    G (NF.dg (CLQ.pres RD k sc) ν [] [] A) = signedDg RD Λ P μ w w
      (A.map fun x => (L ++ blackWord x.2.2, .black (Sig.shape x.2.1), blackWord x.1 ++ R)) := by
  let d := mkD RD ν A hA
  let f := Diagram.cast (blackDiagram RD Λ μ L R d) e e
  rw [NF.dg_of hA, ← Presentation.lin_of, blackCutHom_linQ, blackLinear_of, LinDiagram.cast_of,
    Presentation.lin_of]
  have hc : L ++ blackWord [] ++ R = w := by simpa [blackWord] using hw
  have hs := signedChain_reflectQ L R hA
  have hs' : signedChain w
      (A.map fun x => (L ++ blackWord x.2.2, .black (Sig.shape x.2.1), blackWord x.1 ++ R)) w := by
    rw [← hc]
    exact hs
  symm
  exact signedDg_eq_diag_of_layers RD Λ P μ hs' f (by
    dsimp only [f, d]
    rw [Diagram.layers_cast, layers_blackDiagram_mkD]
    simp only [signedLayers, List.map_map, Function.comp_def])

end Cut

private theorem blackLetter_rightCutWeightQ :
    wt RD ν [l] = endWeight RD Λ μ (L ++ [.inl l]) := by
  rw [endWeight_append, ← endWeight_blackWord RD Λ ν [l]]
  rfl

/-- The image of the KL bubble to the right of its strand equals insertion
at the physical cut immediately before the signed black strand. -/
theorem blackLetterHom_bubRU_cutQ (β : End ((K).obj (ob RD ν []))) :
    F (NF.bubRU (CLQ.pres RD k sc) ν l β) =
      blackCutHomQ RD Λ sc P hP μ L ([.inl l] ++ R) w₀ (by simp [blackWord, List.append_assoc]) β := by
  let G := blackCutHomQ RD Λ sc P hP μ L ([.inl l] ++ R) w₀ (by simp [blackWord, List.append_assoc])
  have h : (F).comp (NF.plcL (CLQ.pres RD k sc) ν [l] [] [] []) = G := by
    apply CLQ.hom_ext_dg RD k sc ν
    intro A hA
    change F (NF.bubRU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) ν [] [] A)) = G (NF.dg (CLQ.pres RD k sc) ν [] [] A)
    rw [blackLetterHom_bubRU_dgQ RD Λ sc P hP μ L R l A hA]
    simpa only [List.append_assoc] using
      (blackCutHom_dgQ RD Λ sc P hP μ L ([.inl l] ++ R) w₀
        (by simp [blackWord, List.append_assoc]) A hA).symm
  exact DFunLike.congr_fun h β

/-- The image of the KL bubble to the left of its strand equals insertion
at the physical cut immediately after the signed black strand. -/
theorem blackLetterHom_bubLU_cutQ (β : End ((K).obj (ob RD (wt RD ν [l]) []))) :
    F (NF.bubLU (CLQ.pres RD k sc) ν l β) =
      blackCutHomQ RD Λ sc P hP μ (L ++ [.inl l]) R w₀ (by simp [blackWord])
        (CLQ.wtTransport RD k sc (blackLetter_rightCutWeightQ RD Λ μ L l) β) := by
  let G := blackCutHomQ RD Λ sc P hP μ (L ++ [.inl l]) R w₀ (by simp [blackWord])
  let e := blackLetter_rightCutWeightQ RD Λ μ L l
  have h : (F).comp (NF.plcL (CLQ.pres RD k sc) ν [] [l] [] []) = G.comp (CLQ.wtTransportL (RD := RD) (k := k) e) := by
    apply CLQ.hom_ext_dg RD k sc (wt RD ν [l])
    intro A hA
    change F (NF.bubLU (CLQ.pres RD k sc) ν l (NF.dg (CLQ.pres RD k sc) (wt RD ν [l]) [] [] A)) =
      G (CLQ.wtTransport RD k sc e (NF.dg (CLQ.pres RD k sc) (wt RD ν [l]) [] [] A))
    rw [blackLetterHom_bubLU_dgQ RD Λ sc P hP μ L R l A hA, CLQ.wtTransport_dg]
    exact (blackCutHom_dgQ RD Λ sc P hP μ (L ++ [.inl l]) R w₀ _ A hA).symm
  exact DFunLike.congr_fun h β

private theorem wtTransport_symm_cancelQ {x y : X} (e : x = y)
    (β : End ((K).obj (ob RD y []))) :
    CLQ.wtTransport RD k sc e (CLQ.wtTransport RD k sc e.symm β) = β := by
  subst y
  simp [CLQ.wtTransport]

/-- Move a bubble algebra element across a single physical black strand
towards the left. Each resulting term is a string of dots on that strand
followed by a bubble algebra element at the preceding cut. -/
theorem blackCutBubble_mem_leftSpanQ {w : List (DoubleStrand I ℓ)} (hw : L ++ [.inl l] ++ R = w)
    (β : End ((K).obj (ob RD (endWeight RD Λ μ (L ++ [.inl l])) [])))
    (hβ : CLQ.IsBub RD k sc (endWeight RD Λ μ (L ++ [.inl l])) β) :
    blackCutHomQ RD Λ sc P hP μ (L ++ [.inl l]) R w hw β ∈
      Submodule.span k {f | ∃ (a : ℕ) (γ : End ((K).obj (ob RD ν []))), CLQ.IsBub RD k sc ν γ ∧
        f = signedDg RD Λ P μ w w (List.replicate a (L, .black (.dot l), R)) ≫
          blackCutHomQ RD Λ sc P hP μ L ([.inl l] ++ R) w (by rw [← hw, List.append_assoc]) γ} := by
  subst w
  let e := blackLetter_rightCutWeightQ RD Λ μ L l
  have h := wtTransport_symm_cancelQ RD (k := k) sc e β
  have hs := blackBubbleRight_mem_leftSpanQ RD Λ sc P hP μ L R l (CLQ.IsBub.wtTransport e.symm hβ)
  rw [blackLetterHom_bubLU_cutQ, h] at hs
  apply (show blackBubbleLeftSpanQ RD Λ sc P hP μ L R l ≤ _ from ?_) hs
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, γ, hγ, rfl⟩
  apply Submodule.subset_span
  exact ⟨a, γ, hγ, by
    rw [blackLetterHom_dotsUQ, blackLetterHom_bubRU_cutQ]
    rfl⟩

end Categorification.Stendhal.DoubleDiagram
