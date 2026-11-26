/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Dimension
import Categorification.Algebra.ModuleFiltration

/-!
# The dimension comparison for a braided projective

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.11, step `p_n → f_n`.
After constructing the diagram filtration, Webster obtains a surjection from the
corresponding standard module to each piece. Equality of the total dimension and
the sum of standard dimensions then makes every surjection an isomorphism.
This module proves that last implication. The filtration, the surjections and
the total dimension identity are inputs.
-/

namespace Categorification.ModuleFiltration.HasFiltration

open scoped ModuleCat.Algebra
open Module

variable {k A ι : Type*} [Field k] [Ring A] [Algebra k A]
  {P S : ι → ModuleCat A}

private theorem finrank_filtered {m : List ι} {Y : ModuleCat A}
    (h : HasFiltration P m Y) :
    FiniteDimensional k Y → finrank k Y = (m.map fun c => finrank k (P c)).sum := by
  induction h with
  | zero hs =>
    intro _
    have := hs
    simp [finrank_zero_of_subsingleton]
  | @cons X Y Z f g m c hf hfg hg hX hZ ih =>
    intro hY
    have hFinite : FiniteDimensional k X := Module.Finite.of_injective (f.restrictScalars k) hf
    obtain ⟨e⟩ := hZ
    have hexact : Function.Exact (f.restrictScalars k) (g.restrictScalars k) := hfg
    rw [Graded.finrank_eq_add_of_exact hf hg hexact, ih hFinite,
      (e.restrictScalars k).finrank_eq, List.map_cons, List.sum_cons, Nat.add_comm]

private theorem finrank_factors {n : List ι} (d : ∀ c, S c →ₗ[A] P c)
    (hs : ∀ c, FiniteDimensional k (S c)) (hd : ∀ c, Function.Surjective (d c))
    (he : (n.map fun c => finrank k (P c)).sum = (n.map fun c => finrank k (S c)).sum) :
    ∀ c ∈ n, finrank k (S c) = finrank k (P c) := by
  have hle (c : ι) : finrank k (P c) ≤ finrank k (S c) := by
    have := hs c
    exact LinearMap.finrank_le_finrank_of_surjective (f := (d c).restrictScalars k) (hd c)
  have hsum (l : List ι) :
      (l.map fun c => finrank k (P c)).sum ≤ (l.map fun c => finrank k (S c)).sum := by
    induction l with
    | nil => simp
    | cons c l ih => simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (hle c) ih
  induction n with
  | nil => simp
  | cons c n ih =>
    simp only [List.map_cons, List.sum_cons] at he
    have hc := hle c
    have hn := hsum n
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · apply ih (by omega) a ha

/-- **Webster v2, Lemma 6.11, step `p_n → f_n`, dimension comparison.**
If the pieces of a finite-dimensional filtration are surjective images of the
proposed standards and the total dimensions agree, the filtration has those
standard modules as its pieces. The individual quotient maps come from the
diagram construction, and the dimension identity comes from decategorification. -/
theorem of_surjective_factors {m : List ι} {Y : ModuleCat A}
    (h : HasFiltration P m Y) [FiniteDimensional k Y]
    (d : ∀ c, S c →ₗ[A] P c) (hs : ∀ c, FiniteDimensional k (S c))
    (hd : ∀ c, Function.Surjective (d c))
    (hDim : finrank k Y = (m.map fun c => finrank k (S c)).sum) :
    HasFiltration S m Y := by
  have hranks := finrank_factors d hs hd ((h.finrank_filtered (k := k) inferInstance).symm.trans hDim)
  clear hDim ‹FiniteDimensional k Y›
  induction h with
  | zero hY => exact .zero hY
  | @cons X Y Z f g m c hf hfg hg hX hZ ih =>
    have := hs c
    have : FiniteDimensional k (P c) :=
      Module.Finite.of_surjective ((d c).restrictScalars k) (hd c)
    have hbij : Function.Bijective (d c) :=
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (d c).restrictScalars k) (hranks c (by simp))).mpr (hd c), hd c⟩
    obtain ⟨e⟩ := hZ
    exact .cons f g m c hf hfg hg (ih fun a ha => hranks a (List.mem_cons_of_mem _ ha))
      ⟨e.trans (LinearEquiv.ofBijective (d c) hbij).symm⟩

end Categorification.ModuleFiltration.HasFiltration
