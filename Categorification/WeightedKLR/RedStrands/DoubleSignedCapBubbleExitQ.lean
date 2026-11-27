/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCup
import Categorification.WeightedKLR.RedStrands.DoubleSignedBubbleSweepQ

/-!
# Eliminating the closed cup in the cap sweep

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. The cup creating
both cap endpoints closes to a real bubble. Moving this bubble to the far
left leaves dot diagrams, which preserve the forward path and crossing bound.
The red transport and far-left scalar evaluation are expressed for the
presentation and projection being used.

This is the version of `DoubleSignedCapBubbleExit` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X) (w : List (DoubleStrand I ℓ))

local notation "cut" => blackCutHomQ RD Λ sc P hP μ
local notation "T" => P.obj (obj RD Λ μ w)
local notation "D" => signedDg RD Λ P μ w w
local notation "K" => CLQ.pres RD k sc

/-- The block which closes its creating cup is in the projected span of dot
diagrams, with arbitrary signed strands on either side of the bubble. This
uses red bubble transport and scalar far-left evaluation as inputs for the
chosen projection in Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. -/
theorem signedCapBlock_cupBubble_mem_dotSpanQ {V : Type*} [AddCommGroup V] [Module k V]
    (π : End T →ₗ[k] V) (hred : RedBubbleSlidesLeftQ RD Λ sc P hP μ w)
    (hleft : ∀ γ, CLQ.IsBub RD k sc (endWeight RD Λ μ []) γ →
      ∃ c : k, ∀ f : End T, π (f ≫ cut [] w w rfl γ) = c • π f)
    (L R : List (DoubleStrand I ℓ)) (hw : L ++ R = w) (s : BubbleOrientation) (i : I) (d : ℕ) :
    π (D ((L,.black (.cup (s.cupLetter i)),R) :: signedCapBlock L [] (s.cupLetter i).dual R d)) ∈
      Submodule.span k {g | ∃ A, signedChain w A w ∧ (∀ x ∈ A, IsBlackDotLayer x) ∧ g = π (D A)} := by
  let ν := endWeight RD Λ μ L
  let b := s.beforeReflection RD ν i d
  have hb : CLQ.IsBub RD k sc ν ((K).lin (LinDiagram.of b)) := by
    cases s with
    | clockwise =>
      simpa only [b,BubbleOrientation.beforeReflection,NF.lin_ccwReal] using
        CLQ.dg_ccwLs_isBub (RD := RD) (k := k) (lam := ν) i d
    | counterclockwise =>
      simpa only [b,BubbleOrientation.beforeReflection,NF.lin_cwReal] using
        CLQ.dg_cwLs_isBub (RD := RD) (k := k) (lam := ν) i d
  have hs := blackCutHom_project_mem_signedDotSpanQ RD Λ sc P hP μ w π hred hleft L R hw _ hb
  rw [blackCutHom_linQ,blackLinear_of,LinDiagram.cast_of,Presentation.lin_of] at hs
  rw [signedCapBlock_cupBubble RD Λ P μ L R hw s i d]
  exact hs


/-- In the cap induction a cup which creates both cap endpoints resolves directly
in the forward span with the crossing budget of the prefix. The projection may
carry any chosen continuation and kill the violated intermediate boundaries. -/
theorem capBlock_push_cupBubbleQ {a t : Obj (signature RD Λ)} {V : Type*}
    [AddCommGroup V] [Module k V] (π : (P.obj a ⟶ P.obj t) →ₗ[k] V)
    (p : a ⟶ obj RD Λ μ w) (hp : ForwardPath a p) (tail : obj RD Λ μ w ⟶ t)
    (hred : RedBubbleSlidesLeftQ RD Λ sc P hP μ w)
    (hleft : ∀ γ, CLQ.IsBub RD k sc (endWeight RD Λ μ []) γ →
      ∃ c : k, ∀ f : End T,
        π (P.diag p ≫ (f ≫ cut [] w w rfl γ) ≫ P.diag tail) = c • π (P.diag p ≫ f ≫ P.diag tail))
    (L R : List (DoubleStrand I ℓ)) (hw : L ++ R = w) (s : BubbleOrientation) (i : I) (d : ℕ) :
    π (P.diag p ≫ D ((L,.black (.cup (s.cupLetter i)),R) ::
        signedCapBlock L [] (s.cupLetter i).dual R d) ≫ P.diag tail) ∈
      forwardSpan k (fun f => π (P.diag f)) tail (crossingNumber p) := by
  let E : End T →ₗ[k] V := π.comp ((Linear.leftComp k (P.obj t) (P.diag p)).comp
    (Linear.rightComp k T (P.diag tail)))
  have h := signedCapBlock_cupBubble_mem_dotSpanQ RD Λ sc P hP μ w E hred hleft L R hw s i d
  apply (show _ ≤ forwardSpan k (fun f => π (P.diag f)) tail (crossingNumber p) from ?_) h
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨A,hA,hd,rfl⟩
  let g := Diagram.mk _ (chain_signedLayers RD Λ μ hA)
  apply Submodule.subset_span
  refine ⟨p ≫ g, hp.postcompose_blackDots RD Λ μ g A rfl hd, ?_, ?_⟩
  · rw [crossingNumber_comp, crossingNumber_of_blackDots RD Λ μ g A rfl hd, Nat.add_zero]
  · change π (P.diag p ≫ D A ≫ P.diag tail) = _
    change π (P.diag p ≫ D A ≫ P.diag tail) = π (P.diag ((p ≫ g) ≫ tail))
    rw [signedDg_of RD Λ P μ hA, P.diag_comp, P.diag_comp, Category.assoc]

end Categorification.Stendhal.DoubleDiagram
