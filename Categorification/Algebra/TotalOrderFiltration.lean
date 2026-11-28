/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.FinrankCountingFiltration
import Categorification.Algebra.ModuleFiltrationMap

/-!
# Filtrations along a total order

Let `N φ` be submodules of a module, indexed by a finite set with a strict total order `≺`,
and put `P_{≻φ} = Σ_{φ ≺ φ'} N φ'` (`Submodule.above`) and `P_{⪰φ} = N φ + P_{≻φ}`. For every
upward closed set `S`, the sum `⨆_{φ ∈ S} N φ` has a finite filtration whose subquotients are
the layers `P_{⪰φ}/P_{≻φ}`, `φ ∈ S` (`Submodule.hasFiltration_iSup_of_total`). Unlike
`Submodule.hasFiltration_iSup`, no dimension count is needed: removing the least element `φ` of
`S` leaves exactly `P_{≻φ}`, since the order is total.

This is the form of the standard filtration used for B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Corollary 5.23, where the filtration of a projective
is taken along a linear extension of Webster's order.

## Main results

* `Submodule.iSup_erase_eq_above_of_total`, `Submodule.hasFiltration_iSup_of_total`.
-/

namespace Submodule

open Categorification

universe v

variable {R : Type*} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
  {ι : Type*} [DecidableEq ι] {rel : ι → ι → Prop} {N : ι → Submodule R M}

/-- Removing the least element `φ` of an upward closed set `S` for a strict total order leaves
`P_{≻φ}`. -/
theorem iSup_erase_eq_above_of_total (hirr : ∀ φ, ¬ rel φ φ)
    (htot : ∀ a b, a ≠ b → rel a b ∨ rel b a) (S : Finset ι)
    (hup : ∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) {φ : ι} (hφ : φ ∈ S)
    (hmin : ∀ ψ ∈ S, ¬ rel ψ φ) :
    (⨆ ψ ∈ S.erase φ, N ψ) = above rel N φ := by
  apply le_antisymm
  · refine iSup₂_le fun ψ hψ => ?_
    have hne : ψ ≠ φ := Finset.ne_of_mem_erase hψ
    rcases htot φ ψ hne.symm with h | h
    · exact le_iSup₂_of_le (f := fun ψ (_ : rel φ ψ) => N ψ) ψ h le_rfl
    · exact absurd h (hmin ψ (Finset.mem_of_mem_erase hψ))
  · refine iSup₂_le fun ψ hrel => ?_
    exact le_biSup N (Finset.mem_erase.2 ⟨fun h => hirr φ (h ▸ hrel), hup φ hφ ψ hrel⟩)

/-- **The sum over an upward closed set is filtered by the layers** of a strict total order. -/
theorem hasFiltration_iSup_of_total [Fintype ι] (hirr : ∀ φ, ¬ rel φ φ)
    (htr : ∀ a b c, rel a b → rel b c → rel a c) (htot : ∀ a b, a ≠ b → rel a b ∨ rel b a) :
    ∀ S : Finset ι, (∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) →
      ∃ l : List ι, (∀ φ ∈ l, φ ∈ S) ∧
        ModuleFiltration.HasFiltration (fun φ => ModuleCat.of R (layer rel N φ)) l
          (ModuleCat.of R ↥(⨆ φ ∈ S, N φ)) := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hup
    rcases S.eq_empty_or_nonempty with rfl | hne
    · refine ⟨[], by simp, .zero ⟨fun x y => Subtype.ext ?_⟩⟩
      have hx := x.2
      have hy := y.2
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, mem_bot] at hx hy
      rw [hx, hy]
    let h : ι → ℕ := fun φ => (Finset.univ.filter fun φ' => rel φ φ').card
    obtain ⟨φ, hφ, hmax⟩ := S.exists_max_image h hne
    have hmin : ∀ ψ ∈ S, ¬ rel ψ φ := by
      intro ψ hψ hrel
      have hlt : h φ < h ψ := by
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact htr _ _ _ hrel ha
        · have := hsub (show φ ∈ Finset.univ.filter fun φ' => rel ψ φ' by simp [hrel])
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact hirr φ this
      exact absurd (hmax ψ hψ) (not_le.2 hlt)
    have hup' : ∀ ψ ∈ S.erase φ, ∀ ψ', rel ψ ψ' → ψ' ∈ S.erase φ := by
      intro ψ hψ ψ' hrel
      refine Finset.mem_erase.2 ⟨?_, hup ψ (Finset.mem_of_mem_erase hψ) ψ' hrel⟩
      rintro rfl
      exact hmin ψ (Finset.mem_of_mem_erase hψ) hrel
    obtain ⟨l, hl, hX⟩ := ih (S.erase φ) (Finset.erase_ssubset hφ) hup'
    set P := ⨆ ψ ∈ S, N ψ
    set P' := ⨆ ψ ∈ S.erase φ, N ψ
    have hPP' : P' ≤ P := biSup_mono fun ψ hψ => Finset.mem_of_mem_erase hψ
    have hD : P = P' ⊔ N φ := iSup_eq_iSup_erase_sup (N := N) S hφ
    have hP' : P' = above rel N φ := iSup_erase_eq_above_of_total hirr htot S hup hφ hmin
    have hNP : N φ ⊔ above rel N φ ≤ P := by rw [hD, hP', sup_comm]
    let θ : layer rel N φ →ₗ[R] ↥P ⧸ P'.comap P.subtype :=
      ((above rel N φ).comap (N φ ⊔ above rel N φ).subtype).liftQ
        ((P'.comap P.subtype).mkQ ∘ₗ Submodule.inclusion hNP) (by
          intro x hx
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          rw [mem_comap] at hx ⊢
          rw [hP']
          exact hx)
    have hθs : Function.Surjective θ := by
      intro z
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [hD] at hy
      obtain ⟨y', hy', n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      refine ⟨Submodule.Quotient.mk ⟨n, Submodule.mem_sup_left hn⟩, ?_⟩
      change Submodule.Quotient.mk _ = _
      rw [Submodule.Quotient.eq]
      change (⟨n, _⟩ - ⟨y' + n, _⟩ : ↥P) ∈ P'.comap P.subtype
      rw [Submodule.mem_comap]
      convert P'.neg_mem hy' using 1
      change n - (y' + n) = -y'
      abel
    have hθi : Function.Injective θ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [LinearMap.mem_ker] at hz
      change Submodule.Quotient.mk (Submodule.inclusion hNP y) = 0 at hz
      rw [Submodule.Quotient.mk_eq_zero, mem_comap] at hz
      rw [mem_bot, Submodule.Quotient.mk_eq_zero, mem_comap]
      rw [hP'] at hz
      exact hz
    refine ⟨φ :: l, fun ψ hψ => ?_, ?_⟩
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hφ
      · exact Finset.mem_of_mem_erase (hl ψ hψ)
    refine .cons (X := ModuleCat.of R ↥P') (Z := ModuleCat.of R (↥P ⧸ P'.comap P.subtype))
      (Submodule.inclusion hPP') (P'.comap P.subtype).mkQ l φ
      (Submodule.inclusion_injective hPP') ?_ (Submodule.mkQ_surjective _) hX
      ⟨(LinearEquiv.ofBijective θ ⟨hθi, hθs⟩).symm⟩
    exact exact_inclusion_mkQ hPP'

end Submodule
