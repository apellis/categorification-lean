/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration

/-!
# Filtrations along a decomposition by orthogonal idempotents

If `1 = Σ_{t ∈ s} e_t` is a decomposition of the identity of a module `M` into orthogonal
idempotent endomorphisms and each image `e_t M` has a finite filtration by modules of a family
`L`, then so does `M` (`exists_hasFiltration_of_orthogonal`). This is used for the braiding
bimodules in B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§6.1, proof of Lemma 6.11, which split along the loading idempotents.
-/

namespace Categorification.ModuleFiltration

open Module

variable {A : Type*} [Ring A] {ι : Type*} {L : ι → ModuleCat A} {M : ModuleCat A}
  {β : Type*} [DecidableEq β] (e : β → End A M)

/-- **Filtrations along orthogonal idempotents.** If `e_t` (`t ∈ s`) are orthogonal idempotent
endomorphisms of `M` summing to the identity, and each image `e_t M` has a finite filtration by
`L`, then `M` has one. -/
theorem exists_hasFiltration_of_orthogonal (s : Finset β)
    (hidem : ∀ t ∈ s, e t * e t = e t)
    (horth : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → e t * e u = 0)
    (hsum : ∑ t ∈ s, e t = 1)
    (h : ∀ t ∈ s, ∃ m : List ι, HasFiltration L m (ModuleCat.of A (LinearMap.range (e t)))) :
    ∃ m : List ι, HasFiltration L m M := by
  have key : ∀ s' ⊆ s, ∃ m : List ι,
      HasFiltration L m (ModuleCat.of A (LinearMap.range (∑ t ∈ s', e t))) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨[], .zero ⟨fun x y => ?_⟩⟩
      obtain ⟨_, x, rfl⟩ := x
      obtain ⟨_, y, rfl⟩ := y
      simp
    | @insert a s' ha ih =>
      intro hs
      have has : a ∈ s := hs (Finset.mem_insert_self a s')
      have hs' : s' ⊆ s := fun t ht => hs (Finset.mem_insert_of_mem ht)
      obtain ⟨m, hm⟩ := ih hs'
      obtain ⟨ma, hma⟩ := h a has
      set E := ∑ t ∈ s', e t
      have hEa : E * e a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun t ht =>
          horth t (hs' ht) a has (fun hta => ha (hta ▸ ht))
      have haE : e a * E = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun t ht =>
          horth a has t (hs' ht) (fun hta => ha (hta ▸ ht))
      have hEE : E * E = E := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mul_sum, Finset.sum_eq_single t]
        · exact hidem t (hs' ht)
        · exact fun u hu hut => horth t (hs' ht) u (hs' hu) (Ne.symm hut)
        · exact fun h' => absurd ht h'
      have hins : ∑ t ∈ insert a s', e t = e a + E := Finset.sum_insert ha
      have hiE : ∀ x : LinearMap.range E, (∑ t ∈ insert a s', e t) x.1 = x.1 := by
        rintro ⟨_, y, rfl⟩
        rw [hins, LinearMap.add_apply, ← Module.End.mul_apply, haE, ← Module.End.mul_apply,
          hEE, LinearMap.zero_apply, zero_add]
      have hia : ∀ x : LinearMap.range (e a), (∑ t ∈ insert a s', e t) x.1 = x.1 := by
        rintro ⟨_, y, rfl⟩
        rw [hins, LinearMap.add_apply, ← Module.End.mul_apply, ← Module.End.mul_apply,
          hidem a has, hEa, LinearMap.zero_apply, add_zero]
      let f : LinearMap.range E →ₗ[A] LinearMap.range (∑ t ∈ insert a s', e t) :=
        LinearMap.codRestrict _ (LinearMap.range E).subtype fun x => ⟨x.1, hiE x⟩
      let g : LinearMap.range (∑ t ∈ insert a s', e t) →ₗ[A] LinearMap.range (e a) :=
        LinearMap.codRestrict _ (e a ∘ₗ Submodule.subtype _) fun x => ⟨x.1, rfl⟩
      have hf : Function.Injective f := by
        intro x y hxy
        have := congrArg Subtype.val hxy
        exact Subtype.ext this
      refine ⟨ma ++ m, hma.extension (X := ModuleCat.of A (LinearMap.range E))
        (Y := ModuleCat.of A (LinearMap.range (∑ t ∈ insert a s', e t))) f g hf ?_ ?_ hm⟩
      · intro x
        constructor
        · intro hx
          have hx' : e a x.1 = 0 := congrArg Subtype.val hx
          obtain ⟨_, y, rfl⟩ := x
          refine ⟨⟨E y, y, rfl⟩, Subtype.ext ?_⟩
          change E y = (∑ t ∈ insert a s', e t) y
          rw [hins, LinearMap.add_apply]
          have : e a ((∑ t ∈ insert a s', e t) y) = e a y := by
            rw [hins, LinearMap.add_apply, map_add, ← Module.End.mul_apply,
              ← Module.End.mul_apply, hidem a has, haE, LinearMap.zero_apply, add_zero]
          rw [this] at hx'
          rw [hx', zero_add]
        · rintro ⟨⟨_, y, rfl⟩, rfl⟩
          apply Subtype.ext
          change e a (E y) = 0
          rw [← Module.End.mul_apply, haE, LinearMap.zero_apply]
      · rintro ⟨_, y, rfl⟩
        refine ⟨⟨e a y, e a y, hia ⟨e a y, y, rfl⟩⟩, ?_⟩
        apply Subtype.ext
        change e a (e a y) = e a y
        rw [← Module.End.mul_apply, hidem a has]
  obtain ⟨m, hm⟩ := key s subset_rfl
  rw [hsum] at hm
  refine ⟨m, hm.of_equiv ?_⟩
  exact (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩))

end Categorification.ModuleFiltration
