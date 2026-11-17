/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedShuffle

/-!
# The adjacent crossing that restores the red order

When shuffling two ordered blocks whose red labels are separated, any
adjacent transposition that restores the red order necessarily removes an
inversion of the two input blocks.
-/
namespace Categorification.Stendhal
open KLR TypeA Equiv

variable {I : Type*} {ℓ : ℕ} {μ : Multiset (I ⊕ Fin ℓ)}

/-- The inversion repaired by one adjacent crossing consists of precisely
the two red strands at that crossing. -/
theorem red_inversion_of_ordered_swap {s : Seq μ} {j : ℕ} (hj : j+1 < μ.card)
    (hs : ¬ IsRedOrdered s) (ht : IsRedOrdered (sadj μ.card j • s)) :
    ∃ r t : Fin ℓ, s.lbl ⟨j,by omega⟩ = .inr r ∧ s.lbl ⟨j+1,hj⟩ = .inr t ∧ ¬ r < t := by
  unfold IsRedOrdered at hs
  push Not at hs
  obtain ⟨a,b,r,t,hab,har,hbt,hn⟩ := hs
  have he : a.val = j ∧ b.val = j+1 := by
    by_contra hne
    have hlt : sadj _ j a < sadj _ j b := by
      change a.val < b.val at hab
      rw [Fin.lt_def, sadj_val_of_lt hj, sadj_val_of_lt hj]
      simp only [swapNat]
      split_ifs <;> omega
    have har' : (sadj μ.card j • s).lbl (sadj _ j a) = .inr r := by
      change s.lbl ((sadj _ j).symm (sadj _ j a)) = _
      rwa [Equiv.symm_apply_apply]
    have hbt' : (sadj μ.card j • s).lbl (sadj _ j b) = .inr t := by
      change s.lbl ((sadj _ j).symm (sadj _ j b)) = _
      rwa [Equiv.symm_apply_apply]
    exact (not_lt_of_ge hn) (ht _ _ _ _ hlt har' hbt')
  refine ⟨r,t,?_,?_,not_lt_of_ge hn⟩
  · exact (congrArg s.lbl (Fin.ext he.1.symm)).trans har
  · exact (congrArg s.lbl (Fin.ext he.2.symm)).trans hbt

variable {α β : Multiset (I ⊕ Fin ℓ)} {a : Seq α} {b : Seq β}

/-- A crossing restoring the red order acts on a second-block strand
followed by a first-block strand. The hypotheses on the inputs apply to
the earlier reds and the new last-red factor in parabolic induction. -/
theorem shuffle_returns_order {s : Seq (α+β)} {j : ℕ} (hj : j+1 < (α+β).card)
    (ha : IsRedOrdered a) (hb : IsRedOrdered b)
    (hab : ∀ x y r t, a.lbl x = .inr r → b.lbl y = .inr t → r < t)
    (u : Shuffle (Seq.card_add' α β)) (hu : u.1 • s = a.append b)
    (hs : ¬ IsRedOrdered s) (ht : IsRedOrdered (sadj (α+β).card j • s)) :
    ∃ (x : Fin α.card) (y : Fin β.card) (r t : Fin ℓ),
      u.1 ⟨j,by omega⟩ = Seq.posR α y ∧ u.1 ⟨j+1,hj⟩ = Seq.posL β x ∧
      s.lbl ⟨j,by omega⟩ = .inr r ∧ s.lbl ⟨j+1,hj⟩ = .inr t := by
  obtain ⟨r,t,hr,ht',hn⟩ := red_inversion_of_ordered_swap hj hs ht
  let c : Fin (α+β).card := ⟨j,by omega⟩
  let d : Fin (α+β).card := ⟨j+1,hj⟩
  have hcd : c < d := by change j < j+1; omega
  have H (z : Fin (α+β).card) : s.lbl z = (a.append b).1 (u.1 z) := by
    rw [← hu]
    change s.lbl z = s.lbl (u.1.symm (u.1 z))
    rw [Equiv.symm_apply_apply]
  obtain ⟨x,hx⟩ := (blockEquiv (Seq.card_add' α β)).surjective (u.1 c)
  obtain ⟨y,hy⟩ := (blockEquiv (Seq.card_add' α β)).surjective (u.1 d)
  cases x with
  | inl x =>
    have hx' : a.lbl x = .inr r := (Seq.append_posL a b x).symm.trans ((congrArg (a.append b).1 hx).trans ((H c).symm.trans hr))
    cases y with
    | inl y =>
      have hy' : a.lbl y = .inr t := (Seq.append_posL a b y).symm.trans ((congrArg (a.append b).1 hy).trans ((H d).symm.trans ht'))
      have hxy : x < y := u.2.1.lt_iff_lt.mp (by
        change u.1.symm (blockEquiv _ (.inl x)) < u.1.symm (blockEquiv _ (.inl y))
        rw [hx, hy, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hcd)
      exact (hn (ha x y r t hxy hx' hy')).elim
    | inr y =>
      have hy' : b.lbl y = .inr t := (Seq.append_posR a b y).symm.trans ((congrArg (a.append b).1 hy).trans ((H d).symm.trans ht'))
      exact (hn (hab _ _ _ _ hx' hy')).elim
  | inr x =>
    cases y with
    | inl y => exact ⟨y,x,r,t,hx.symm,hy.symm,hr,ht'⟩
    | inr y =>
      have hx' : b.lbl x = .inr r := (Seq.append_posR a b x).symm.trans ((congrArg (a.append b).1 hx).trans ((H c).symm.trans hr))
      have hy' : b.lbl y = .inr t := (Seq.append_posR a b y).symm.trans ((congrArg (a.append b).1 hy).trans ((H d).symm.trans ht'))
      have hxy : x < y := u.2.2.lt_iff_lt.mp (by
        change u.1.symm (blockEquiv _ (.inr x)) < u.1.symm (blockEquiv _ (.inr y))
        rw [hx, hy, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hcd)
      exact (hn (hb x y r t hxy hx' hy')).elim

end Categorification.Stendhal
