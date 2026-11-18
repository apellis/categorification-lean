/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Lemma39
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.QuantumGroup.UDotKL3

/-!
# Black straightening at the fundamental rank-one boundary

Webster, arXiv:1309.3796v3, Lemma 4.29, refers to KL III, Lemma 3.9 for
the reduction to downward dots and bubbles. At the fundamental rank-one
boundary the existing upward spanning result transfers by the sign
symmetry of KL III §3.3.2. The bubbles are on the right in KL order, next
to the red strand after reflection.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram

/-- At weight one for type A₁ every endomorphism of the downward strand
is in the right-bubble span from KL III, Lemma 3.9. -/
theorem fundamental_down_mem_slideSetR (k : Type*) [CommRing k]
    (f : End ((pres sl2RootDatum k).obj (ob sl2RootDatum 1 [dn ()]))) :
    f ∈ slideSetR sl2RootDatum k 1 (dn ()) := by
  let ω := omegaU sl2RootDatum k
  have hm (g : End ((pres sl2RootDatum k).obj (ob sl2RootDatum (-1) [up ()])))
      (hg : g ∈ slideSetR sl2RootDatum k (-1) (up ())) :
      ω.map g ∈ slideSetR sl2RootDatum k 1 (dn ()) := by
    induction hg using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, β, _, rfl⟩ := hz
      have hd := omegaU_dotsU (RD := sl2RootDatum) (k := k) (-1) (up ()) a
      have hb := omegaU_bubRU (RD := sl2RootDatum) (k := k) (-1) (up ()) β
      have h₁ : ω.map (dotsU sl2RootDatum k (-1) (up ()) a) = dotsU sl2RootDatum k 1 (dn ()) a := by
        change _ = TR sl2RootDatum k
          (rfl : ob sl2RootDatum 1 [dn ()] = _) rfl (dotsU sl2RootDatum k 1 (dn ()) a) at hd
        exact hd.trans (TR_rfl _)
      have h₂ : ω.map (bubRU sl2RootDatum k (-1) (up ()) β) =
          bubRU sl2RootDatum k 1 (dn ()) (ω.map β) := by
        change _ = TR sl2RootDatum k (rfl : ob sl2RootDatum 1 [dn ()] = _) rfl
          (bubRU sl2RootDatum k 1 (dn ()) (ω.map β)) at hb
        exact hb.trans (TR_rfl _)
      rw [Functor.map_comp, h₁, h₂]
      apply mem_slideSetR
      exact isBub_of_prop36 (RD := sl2RootDatum) 1 (prop36 1) _
    | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
    | add x y _ _ h₁ h₂ => rw [Functor.map_add]; exact Submodule.add_mem _ h₁ h₂
    | smul r x _ h₁ => rw [Functor.map_smul]; exact Submodule.smul_mem _ r h₁
  have he : ω.map (ω.map f) = f := by
    have h := omegaU_omegaU (RD := sl2RootDatum) (k := k) f
    change ω.map (ω.map f) = TR sl2RootDatum k rfl rfl f at h
    exact h.trans (TR_rfl _)
  let g : End ((pres sl2RootDatum k).obj (ob sl2RootDatum (-1) [up ()])) := ω.map f
  rw [← he]
  exact hm g ((endUpSpan (RD := sl2RootDatum) (k := k) (-1) ()) g)

end Categorification.Stendhal.DoubleDiagram
