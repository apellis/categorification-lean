/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffixQ
import Categorification.Diagrams.KL3.SpanningSetLocal
import Categorification.Diagrams.CLQ.SpanningSetLocal

/-!
# The black Reidemeister III move in a signed cap sweep

Khovanov–Lauda III, arXiv:0807.3250v1, proof of Proposition 3.11.
Reflected black diagrams preserve crossing count. The Reidemeister III
step modulo lower terms therefore holds in a black rectangle, even when
both exterior words contain red strands, as used in Webster v2, Lemma 4.28.

This is the version of `DoubleSignedCapBraidBlack` in which the black strands carry the relations of
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
  (μ : X) (L R : List (DoubleStrand I ℓ))

local notation "η" => endWeight RD Λ μ L
local notation "rightWeight" => fun s : List (Letter I) => endWeight RD Λ μ (L ++ blackWord s)

private theorem blackDiagram_crossingNumber {s t : List (Letter I)} {A : List (LayerData I)}
    (h : SChain s A t) : crossingNumber (blackDiagram RD Λ μ L R (mkD RD η A h)) = ccnt A := by
  rw [crossingNumber, layers_blackDiagram_mkD, List.countP_map, ccnt]
  apply congrArg (fun f : LayerData I → Bool => A.countP f)
  funext x
  obtain ⟨_,g,_⟩ := x
  cases g <;> rfl

/-- A black KL linear combination with bounded crossing number keeps that
bound under reflection into a signed rectangle. -/
theorem blackRectangleHom_mem_signedCrossingSpanQ {s t : List (Letter I)} {τ : X}
    (hs : (rightWeight) s = τ) (ht : (rightWeight) t = τ) {n : ℕ} {f}
    (hf : f ∈ CLQ.LeL RD k sc η s t n) :
    blackRectangleHomQ RD Λ sc μ L R s P hP t hs ht f ∈
      signedCrossingSpan RD Λ P μ (L ++ blackWord s ++ R) (L ++ blackWord t ++ R) n := by
  classical
  let F := blackRectangleHomQ RD Λ sc μ L R s P hP t hs ht
  change F f ∈ _
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, hA, rfl⟩ := hz
    by_cases hm : SChain s A t
    · dsimp only [F]
      rw [NF.dg_of hm, ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of, Presentation.lin_of]
      exact Submodule.subset_span ⟨_, (blackDiagram_crossingNumber RD Λ μ L R hm).le.trans hA, rfl⟩
    · rw [NF.dg_of_not hm, map_zero]
      exact Submodule.zero_mem _
  | zero => simp
  | add f g _ _ hf hg =>
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [map_smul]
    exact Submodule.smul_mem _ a hf

section Braid

variable (x y z : Letter I)

local notation "rawSource" => ([z,y,x] : List (Letter I))
local notation "rawTarget" => ([x,y,z] : List (Letter I))
local notation "Xb" => (Sum.inl x : DoubleStrand I ℓ)
local notation "Yb" => (Sum.inl y : DoubleStrand I ℓ)
local notation "Zb" => (Sum.inl z : DoubleStrand I ℓ)
local notation "A" => (L ++ [Xb,Yb,Zb] ++ R)
local notation "B" => (L ++ [Zb,Yb,Xb] ++ R)
local notation "D" => signedDg RD Λ P μ A B

include hP

/-- The two three-crossing words in a signed rectangle of black strands agree
modulo at most two crossings. The surrounding words can contain red strands. -/
theorem signedCapBraid_blackQ :
    (D) (signedCapBraidLeft L Xb Yb z R) - (D) (signedCapBraidRight L Xb Yb z R) ∈
      signedCrossingSpan RD Λ P μ A B 2 := by
  classical
  have ht : (rightWeight) rawTarget = (rightWeight) rawSource := by
    simp [blackWord, endWeight, add_assoc, add_comm]
  let F := blackRectangleHomQ RD Λ sc μ L R rawSource P hP rawTarget rfl ht
  have e₁ : F (NF.dg (CLQ.pres RD k sc) η rawSource rawTarget (r3L z y x)) = (D) (signedCapBraidRight L Xb Yb z R) := by
    dsimp only [F]
    rw [NF.dg_of (sChain_r3L z y x), ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of,
      Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCapBraidRight_chain L (show CanCross Xb Yb from trivial) z R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨a,i⟩ := x
    obtain ⟨b,j⟩ := y
    obtain ⟨c,k'⟩ := z
    cases a <;> cases b <;> cases c <;>
      simp [r3L, xLay, whL, crosslL, crossrL, signedLayers, signedCapBraidRight,
        signedCrossLayers, crossBlackLeft, upwardMateLayers, blackWord, Sig.shape, List.append_assoc]
  have e₂ : F (NF.dg (CLQ.pres RD k sc) η rawSource rawTarget (r3R z y x)) = (D) (signedCapBraidLeft L Xb Yb z R) := by
    dsimp only [F]
    rw [NF.dg_of (sChain_r3R z y x), ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of,
      Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCapBraidLeft_chain L (show CanCross Xb Yb from trivial) z R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨a,i⟩ := x
    obtain ⟨b,j⟩ := y
    obtain ⟨c,k'⟩ := z
    cases a <;> cases b <;> cases c <;>
      simp [r3R, xLay, whL, crosslL, crossrL, signedLayers, signedCapBraidLeft,
        signedCrossLayers, crossBlackLeft, upwardMateLayers, blackWord, Sig.shape, List.append_assoc]
  have h := blackRectangleHom_mem_signedCrossingSpanQ RD Λ sc P hP μ L R (s := rawSource) (t := rawTarget)
    rfl ht (CLQ.r3 (RD := RD) (k := k) η z y x)
  change F (_ - _) ∈ signedCrossingSpan RD Λ P μ A B 2 at h
  rw [map_sub, e₁, e₂] at h
  simpa only [neg_sub] using Submodule.neg_mem _ h

end Braid

end Categorification.Stendhal.DoubleDiagram
