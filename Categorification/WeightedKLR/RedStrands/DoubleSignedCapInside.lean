/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave

/-!
# Sweeping a black cap past a crossing inside its block

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, and Khovanov–Lauda III,
arXiv:0807.3250v1, proof of Proposition 3.11. The part of the crossing
filtration coming from a braid correction decreases under a cap sweep.
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

section Interleaved

private theorem signedDg_eq_reindex (P : Presentation.{w,max u v} S k) (μ : X)
    {s t s' t' : List B} {F G : List (SignedLayer I ℓ)} (hs : s = s') (ht : t = t')
    (h : signedDg RD Λ P μ s t F = signedDg RD Λ P μ s t G) :
    signedDg RD Λ P μ s' t' F = signedDg RD Λ P μ s' t' G := by
  subst hs ht
  exact h

/-- Webster v2, Lemma 4.28: the contextual braid correction passes between
the two untouched sweeps, so it has smaller crossing number than the original composite. -/
theorem signedCapBlock_crossInside (P : Presentation.{w,max u v} S k) (μ : X)
    (L U V R : List B) (l : Letter I) (d : ℕ) {x y : B} (hxy : CanCross x y)
    (hBraid : signedDg (k := k) RD Λ P μ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y,(Sum.inl l : B)] ++ (V ++ R)) ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),y,x] ++ (V ++ R))
          (signedCapBraidLeft (L ++ [(Sum.inl l.dual : B)] ++ U) x y l (V ++ R)) -
        signedDg (k := k) RD Λ P μ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y,(Sum.inl l : B)] ++ (V ++ R)) ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),y,x] ++ (V ++ R))
          (signedCapBraidRight (L ++ [(Sum.inl l.dual : B)] ++ U) x y l (V ++ R)) ∈
      signedCrossingSpan RD Λ P μ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y,(Sum.inl l : B)] ++ (V ++ R)) ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),y,x] ++ (V ++ R)) 2) :
    signedDg (k := k) RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) (L ++ (U ++ [y,x] ++ V) ++ R)
        (signedCrossLayers (L ++ [(Sum.inl l.dual : B)] ++ U) x y (V ++ [(Sum.inl l : B)] ++ R) ++ signedCapBlock L (U ++ [y,x] ++ V) l R d) -
      signedDg (k := k) RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) (L ++ (U ++ [y,x] ++ V) ++ R)
        (signedCapBlock L (U ++ [x,y] ++ V) l R d ++ signedCrossLayers (L ++ U) x y (V ++ R)) ∈
    signedCrossingSpan RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) (L ++ (U ++ [y,x] ++ V) ++ R) (U.length + 2 + V.length) := by
  let pre := sweepBlackLeft ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y]) V l R
  let post := signedCapBlock L U l (y :: x :: (V ++ R)) d
  have hp : signedChain (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) pre ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y,(Sum.inl l : B)] ++ (V ++ R)) := by
    simpa only [pre, List.append_assoc, List.cons_append, List.nil_append] using
      sweepBlackLeft_chain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x,y]) V l R
  have hq : signedChain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),y,x] ++ (V ++ R)) post (L ++ (U ++ [y,x] ++ V) ++ R) := by
    simpa only [post, List.append_assoc, List.cons_append, List.nil_append] using
      signedCapBlock_chain L U l (y :: x :: (V ++ R)) d
  have hlo := signedDg_replace_span RD Λ P μ hp (signedCapBraidLeft_chain (L ++ [(Sum.inl l.dual : B)] ++ U) hxy l (V ++ R))
    (signedCapBraidRight_chain (L ++ [(Sum.inl l.dual : B)] ++ U) hxy l (V ++ R)) hq hBraid
  rw [show signedCrossings pre = V.length from sweepBlackLeft_crossings ..,
    show signedCrossings post = U.length from signedCapBlock_crossings ..,
    show V.length + 2 + U.length = U.length + 2 + V.length by omega] at hlo
  convert hlo using 2
  · let pre' := sweepBlackLeft ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x]) V l R
    let rest := crossBlackLeft ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y]) x l (V ++ R) ++ crossBlackLeft (L ++ [(Sum.inl l.dual : B)] ++ U) y l (x :: (V ++ R)) ++ post
    have he := signedDg_interchange RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ U) R (signedCrossLayers_chain [] hxy [])
      (sweepBlackLeft_chain [] V l [])
    have he' : signedDg RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x,(Sum.inl l : B)] ++ (V ++ R))
          (signedCrossLayers (L ++ [(Sum.inl l.dual : B)] ++ U) x y (V ++ [(Sum.inl l : B)] ++ R) ++ pre') =
        signedDg RD Λ P μ (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x,(Sum.inl l : B)] ++ (V ++ R))
          (pre ++ signedCrossLayers (L ++ [(Sum.inl l.dual : B)] ++ U) x y ((Sum.inl l : B) :: (V ++ R))) := by
      have reindexed := signedDg_eq_reindex RD Λ P μ
        (s' := L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R)
        (t' := (L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x,(Sum.inl l : B)] ++ (V ++ R))
        (by simp [List.append_assoc]) (by simp [List.append_assoc]) he
      simpa only [signedCrossLayers_whisk, sweepBlackLeft_whisk, pre, pre', List.append_assoc,
        List.cons_append, List.append_nil, List.nil_append] using reindexed
    have hrest : signedChain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x,(Sum.inl l : B)] ++ (V ++ R)) rest (L ++ (U ++ [y,x] ++ V) ++ R) := by
      have h₁ := crossBlackLeft_chain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y]) x l (V ++ R)
      have h₂ := crossBlackLeft_chain (L ++ [(Sum.inl l.dual : B)] ++ U) y l (x :: (V ++ R))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h₁ h₂ hq ⊢
      simpa only [rest, List.append_assoc, List.cons_append, List.nil_append] using (h₁.append h₂).append hq
    have h₁ := (signedCrossLayers_chain (L ++ [(Sum.inl l.dual : B)] ++ U) hxy (V ++ [(Sum.inl l : B)] ++ R)).append
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        sweepBlackLeft_chain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [y,x]) V l R)
    have h₂ := hp.append (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      signedCrossLayers_chain (L ++ [(Sum.inl l.dual : B)] ++ U) hxy ((Sum.inl l : B) :: (V ++ R)))
    have he'' := signedDg_replace RD Λ P μ [] _ _ rest (show signedChain (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) [] (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) from rfl)
      hrest (by simpa only [pre', List.append_assoc, List.cons_append, List.nil_append] using h₁)
      (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using h₂) he'
    have hsplit : signedCapBlock L (U ++ [y,x] ++ V) l R d =
        pre' ++ sweepBlackLeft (L ++ [(Sum.inl l.dual : B)] ++ U) [y,x] l (V ++ R) ++ post := by
      rw [List.append_assoc, signedCapBlock_append L U ([y,x] ++ V) l R d,
        sweepBlackLeft_append (L ++ [(Sum.inl l.dual : B)] ++ U) [y,x] V l R]
      rfl
    rw [hsplit]
    simpa only [signedCapBraidLeft, pre', rest, post, sweepBlackLeft, List.nil_append,
      List.append_assoc, List.cons_append, List.nil_append] using he''
  · let pre₀ := pre ++ crossBlackLeft ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x]) y l (V ++ R) ++ crossBlackLeft (L ++ [(Sum.inl l.dual : B)] ++ U) x l (y :: (V ++ R))
    let post₀ := signedCapBlock L U l (x :: y :: (V ++ R)) d
    have he := signedDg_interchange RD Λ P μ L (V ++ R) (signedCapBlock_chain [] U l [] d)
      (signedCrossLayers_chain [] hxy [])
    have he' : signedDg RD Λ P μ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R)) (L ++ (U ++ [y,x] ++ V) ++ R)
          (post₀ ++ signedCrossLayers (L ++ U) x y (V ++ R)) =
        signedDg RD Λ P μ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R)) (L ++ (U ++ [y,x] ++ V) ++ R)
          (signedCrossLayers ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B)]) x y (V ++ R) ++ post) := by
      have reindexed := signedDg_eq_reindex RD Λ P μ
        (s' := (L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R))
        (t' := L ++ (U ++ [y,x] ++ V) ++ R)
        (by simp [List.append_assoc]) (by simp [List.append_assoc]) he
      simpa only [signedCrossLayers_whisk, signedCapBlock_whisk, post, post₀, List.append_assoc,
        List.cons_append, List.append_nil, List.nil_append] using reindexed
    have hpre : signedChain (L ++ [(Sum.inl l.dual : B)] ++ (U ++ [x,y] ++ V) ++ [(Sum.inl l : B)] ++ R) pre₀ ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R)) := by
      have h₁ := crossBlackLeft_chain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [x]) y l (V ++ R)
      have h₂ := crossBlackLeft_chain (L ++ [(Sum.inl l.dual : B)] ++ U) x l (y :: (V ++ R))
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hp h₁ h₂ ⊢
      simpa only [pre₀, List.append_assoc, List.cons_append, List.nil_append] using (hp.append h₁).append h₂
    have h₁ : signedChain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R))
        (post₀ ++ signedCrossLayers (L ++ U) x y (V ++ R)) (L ++ (U ++ [y,x] ++ V) ++ R) := by
      have c₁ := signedCapBlock_chain L U l (x :: y :: (V ++ R)) d
      have c₂ := signedCrossLayers_chain (L ++ U) hxy (V ++ R)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at c₁ c₂ ⊢
      exact c₁.append c₂
    have h₂ : signedChain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B),x,y] ++ (V ++ R)) (signedCrossLayers ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B)]) x y (V ++ R) ++ post) (L ++ (U ++ [y,x] ++ V) ++ R) := by
      have c := signedCrossLayers_chain ((L ++ [(Sum.inl l.dual : B)] ++ U) ++ [(Sum.inl l : B)]) hxy (V ++ R)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at c hq ⊢
      exact c.append hq
    have he'' := signedDg_replace RD Λ P μ pre₀ _ _ [] hpre
      (show signedChain (L ++ (U ++ [y,x] ++ V) ++ R) [] (L ++ (U ++ [y,x] ++ V) ++ R) from rfl) h₁ h₂ he'
    have hsplit : signedCapBlock L (U ++ [x,y] ++ V) l R d =
        pre ++ sweepBlackLeft (L ++ [(Sum.inl l.dual : B)] ++ U) [x,y] l (V ++ R) ++ post₀ := by
      rw [List.append_assoc, signedCapBlock_append L U ([x,y] ++ V) l R d,
        sweepBlackLeft_append (L ++ [(Sum.inl l.dual : B)] ++ U) [x,y] V l R]
      rfl
    rw [hsplit]
    simpa only [signedCapBraidRight, pre₀, post₀, post, sweepBlackLeft, List.nil_append,
      List.append_nil, List.append_assoc, List.cons_append, List.nil_append] using he''

end Interleaved

end Categorification.Stendhal.DoubleDiagram
