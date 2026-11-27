/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackPhysicalSpan
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlackQ

/-!
# Black crossing bounds in physical layer order

The symmetry of KL III, arXiv:0807.3250v1, §3.3.2 reflects the word,
changes the region weight, and multiplies a diagram by a sign for its
equal-colour crossings. Applying this symmetry before the black rectangle
map preserves crossing bounds in the physical order of Webster,
arXiv:1309.3796v2, §4.5, Lemma 4.28.

This is the version of `DoubleBlackPhysicalSpan` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)

private theorem ccnt_sls (ls : List (LayerData I)) : ccnt (Sig.sls ls) = ccnt ls := by
  unfold ccnt Sig.sls
  rw [List.countP_map]
  apply List.countP_congr
  rintro ⟨L,g,R⟩ _
  cases g <;> rfl

private theorem sig_leLQ [DecidableEq I] {ν η : X} {s t : List (Letter I)} {n : ℕ} {f}
    (hs : η = -wt RD ν s) (ht : η = -wt RD ν t) (hf : f ∈ CLQ.LeL RD k sc ν s t n) :
    (CLQ.sigUQ RD k sc).map f ∈ (CLQ.LeL RD k sc η s.reverse t.reverse n).map
      (CLQ.TRQ RD k sc (Sig.trO ν η s hs) (Sig.trO ν η t ht)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ls,hn,rfl⟩ := hf
    by_cases h : SChain s ls t
    · rw [CLQ.sigUQ_dg ν η s.reverse t.reverse ls h hs rfl rfl, ← map_smul]
      exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (CLQ.dg_mem_leL (by rwa [ccnt_sls])))
    · rw [NF.dg_of_not h, Functor.map_zero]
      exact Submodule.zero_mem _
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [Functor.map_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [Functor.map_smul]; exact Submodule.smul_mem _ a hf

/-- A bound on the crossing number of a raw black diagram survives horizontal
reflection, including the sign on equal-colour crossings and the negated
regional weight from KL III, arXiv:0807.3250v1, §3.3.2. -/
theorem reflected_dg_mem_LeLQ {ν η : X} {s t : List (Letter I)} {n : ℕ} (ls : List (LayerData I))
    (h : SChain s ls t) (hs : η = -wt RD ν s) (hf : NF.dg (CLQ.pres RD k sc) ν s t ls ∈ CLQ.LeL RD k sc ν s t n) :
    NF.dg (CLQ.pres RD k sc) η s.reverse t.reverse (Sig.sls ls) ∈ CLQ.LeL RD k sc η s.reverse t.reverse n := by
  classical
  have ht : η = -wt RD ν t := hs.trans (by rw [SChain.wt_eq RD ν h])
  have H := sig_leLQ RD sc hs ht hf
  rw [CLQ.sigUQ_dg ν η s.reverse t.reverse ls h hs rfl rfl] at H
  have HH := Submodule.smul_mem _ ((Sig.sgnS ls : ℤ) : k) H
  rw [smul_smul, ← Int.cast_mul, sgnS_sq, Int.cast_one, one_smul] at HH
  exact (CLQ.TRQ_mem_map_iff (Sig.trO ν η s hs) (Sig.trO ν η t ht)).mp HH

variable (Λ : Fin ℓ → X) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X) (L R : List (DoubleStrand I ℓ))

private theorem shape_twice (g : Shape I) : Sig.shape (Sig.shape g) = g := by
  cases g <;> simp [Sig.shape]

private theorem physicalBlackLayers_chain {s t : List (Letter I)} (ls : List (LayerData I))
    (hl : SChain s ls t) : signedChain (L ++ s.map Sum.inl ++ R) (physicalBlackLayers L R ls) (L ++ t.map Sum.inl ++ R) := by
    induction ls generalizing s with
    | nil => cases hl; rfl
    | cons a as ih =>
      obtain ⟨u,g,v⟩ := a
      obtain ⟨rfl,hg⟩ := hl
      refine ⟨by simp [Move.bottom,List.map_append,List.append_assoc],?_⟩
      simpa only [physicalBlackLayers,Move.top,List.map_append,List.append_assoc] using ih hg

private theorem cast_mem_signed {a b c d : List (DoubleStrand I ℓ)} (ea : a=c) (eb : b=d)
    (f : obj RD Λ μ a ⟶ obj RD Λ μ b) {n : ℕ}
    (h : P.diag f ∈ signedCrossingSpan RD Λ P μ a b n) :
    P.diag (Diagram.cast f (congrArg _ ea) (congrArg _ eb)) ∈ signedCrossingSpan RD Λ P μ c d n := by
  cases ea; cases eb; exact h

include hP

/-- Crossing-bounded raw KL layers inject into an arbitrary signed rectangle
in their own horizontal order. This form uses the reflected KL normalization
of Webster v2, §4.5, Lemma 4.28. -/
theorem physicalBlack_mem_signedCrossingSpanQ {ν : X} {s t : List (Letter I)} (ls : List (LayerData I))
    (hl : SChain s ls t) (hν : endWeight RD Λ μ L = -wt RD ν s) {n : ℕ}
    (hf : NF.dg (CLQ.pres RD k sc) ν s t ls ∈ CLQ.LeL RD k sc ν s t n) :
    let a := L ++ s.map Sum.inl ++ R
    let b := L ++ t.map Sum.inl ++ R
    signedDg RD Λ P μ a b (physicalBlackLayers L R ls) ∈ signedCrossingSpan RD Λ P μ a b n := by
  let η := endWeight RD Λ μ L
  have hs : ∀ z : List (Letter I), blackWord (ℓ := ℓ) z.reverse = z.map Sum.inl := by
    intro z; simp [blackWord]
  have hwt : endWeight RD Λ μ (L ++ blackWord t.reverse) = endWeight RD Λ μ (L ++ blackWord s.reverse) := by
    simp only [endWeight_append,endWeight_blackWord]
    exact SChain.wt_eq RD η (Sig.sChain_sls hl)
  have h := blackRectangleHom_mem_signedCrossingSpanQ RD Λ sc P hP μ L R rfl hwt
    (reflected_dg_mem_LeLQ RD sc ls hl hν hf)
  rw [NF.dg_of (Sig.sChain_sls hl), ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of,
    Presentation.lin_of] at h
  let d := blackDiagram RD Λ μ L R (mkD RD η (Sig.sls ls) (Sig.sChain_sls hl))
  have ht : Diagram.layers d = signedLayers RD Λ μ (physicalBlackLayers L R ls) := by
    rw [show Diagram.layers d = _ from layers_blackDiagram_mkD RD Λ μ L R _ (Sig.sChain_sls hl)]
    simp only [Sig.sls, signedLayers, physicalBlackLayers,List.map_map]
    apply List.map_congr_left
    rintro ⟨a,g,b⟩ _
    simp only [Function.comp_apply, Sig.ld, hs, shape_twice]
  dsimp only
  have hc := physicalBlackLayers_chain L R ls hl
  rw [signedDg_eq_diag_of_layers RD Λ P μ hc
    (Diagram.cast d (by rw [hs]) (by rw [hs])) (by rw [Diagram.layers_cast,ht])]
  exact cast_mem_signed RD Λ P μ (by rw [hs]) (by rw [hs]) d h

end Categorification.Stendhal.DoubleDiagram
