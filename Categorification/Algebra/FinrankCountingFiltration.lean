/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.FinrankCounting
import Categorification.Algebra.ModuleFiltration

/-!
# Filtrations from a tight dimension count

A complement to `Categorification.Algebra.FinrankCounting`, for the dimension argument of
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21, in the form used for the partial standardizations of §6.1, Lemma 6.8. Let
`N φ` be submodules of a finite-dimensional module, indexed by a finite set with a strict
order, with layers `P_{≥φ}/P_{>φ}` (`Submodule.layer`). When the layer dimensions add up to the
dimension of the sum of all `N φ`, every upward closed set `S` has
`dim ⨆_{φ ∈ S} N φ = ∑_{φ ∈ S} dim P_{≥φ}/P_{>φ}` (`Submodule.finrankK_iSup_eq_sum`), and
`⨆_{φ ∈ S} N φ` has a finite filtration whose subquotients are the layers at `φ ∈ S`
(`Submodule.hasFiltration_iSup`).
-/

namespace Submodule

open Module Categorification

universe v

variable {k R : Type*} {M : Type v} [Field k] [Ring R] [Algebra k R] [AddCommGroup M]
  [Module k M] [Module R M] [IsScalarTower k R M] [FiniteDimensional k M]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)
  (N : ι → Submodule R M)

/-- The layer `P_{≥φ}/P_{>φ}`. -/
abbrev layer (φ : ι) : Type v :=
  ↥(N φ ⊔ above rel N φ) ⧸ (above rel N φ).comap (N φ ⊔ above rel N φ).subtype

omit [FiniteDimensional k M] in
/-- The dimension of `P/Q` for `Q ≤ P`. -/
theorem finrank_quotient_comap_subtype [FiniteDimensional k M] {P P' : Submodule R M}
    (h : P' ≤ P) :
    finrank k (↥P ⧸ P'.comap P.subtype) = finrankK k P - finrankK k P' := by
  have : FiniteDimensional k P :=
    Module.Finite.of_injective (P.subtype.restrictScalars k) Subtype.val_injective
  set p := P'.comap P.subtype
  have hq : finrank k (↥P ⧸ p.restrictScalars k) + finrank k (p.restrictScalars k) =
      finrank k P := Submodule.finrank_quotient_add_finrank _
  have h1 : finrank k (↥P ⧸ p.restrictScalars k) = finrank k (↥P ⧸ p) :=
    (Submodule.Quotient.restrictScalarsEquiv k p).finrank_eq
  have h2 : finrank k p = finrank k P' :=
    ((Submodule.comapSubtypeEquivOfLe h).restrictScalars k).finrank_eq
  change finrank k (↥P ⧸ p.restrictScalars k) + finrank k p = _ at hq
  unfold finrankK
  change _ = finrank k P - finrank k P'
  omega

omit [FiniteDimensional k M] in
theorem exact_inclusion_mkQ {P P' : Submodule R M} (h : P' ≤ P) :
    Function.Exact (Submodule.inclusion h) (P'.comap P.subtype).mkQ :=
  LinearMap.exact_iff.2 (by rw [Submodule.ker_mkQ, Submodule.range_inclusion])

omit [Fintype ι] [DecidableEq ι] in
theorem finrank_layer (φ : ι) : finrank k (layer rel N φ) = layerRank (k := k) rel N φ :=
  finrank_quotient_comap_subtype le_sup_right

variable {rel N}

omit [Fintype ι] [FiniteDimensional k M] in
theorem iSup_eq_iSup_erase_sup (S : Finset ι) {φ : ι} (hφ : φ ∈ S) :
    (⨆ ψ ∈ S, N ψ) = (⨆ ψ ∈ S.erase φ, N ψ) ⊔ N φ := by
  rw [← Finset.insert_erase hφ, Finset.iSup_insert, sup_comm, Finset.erase_insert_eq_erase,
    Finset.erase_eq_of_notMem (Finset.notMem_erase φ S)]

omit [Fintype ι] in
/-- Removing a minimal element from an upward closed set. -/
theorem finrankK_iSup_le_erase (hirr : ∀ φ, ¬ rel φ φ) (S : Finset ι)
    (hup : ∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) {φ : ι} (hφ : φ ∈ S) :
    finrankK k (⨆ ψ ∈ S, N ψ) ≤ finrankK k (⨆ ψ ∈ S.erase φ, N ψ) + layerRank (k := k) rel N φ := by
  have hD := iSup_eq_iSup_erase_sup (N := N) S hφ
  have habove : above rel N φ ≤ ⨆ ψ ∈ S.erase φ, N ψ := by
    refine iSup₂_le fun ψ hrel => ?_
    exact le_biSup N (Finset.mem_erase.2 ⟨fun h => hirr φ (h ▸ hrel), hup φ hφ ψ hrel⟩)
  have hinf : above rel N φ ⊓ N φ ≤ (⨆ ψ ∈ S.erase φ, N ψ) ⊓ N φ := inf_le_inf_right _ habove
  have e₁ := finrankK_sup_add_inf (k := k) (⨆ ψ ∈ S.erase φ, N ψ) (N φ)
  have e₂ := finrankK_sup_add_inf (k := k) (above rel N φ) (N φ)
  have e₃ := finrankK_le_of_le (k := k) hinf
  have hl : layerRank (k := k) rel N φ =
      finrankK k (above rel N φ ⊔ N φ) - finrankK k (above rel N φ) := by
    unfold layerRank
    rw [sup_comm]
  rw [hD, hl]
  omega

/-- Upward closed sets `S ⊆ S'`: the dimension of the sum over `S'` is at most that over `S`
plus the layer dimensions over `S' \ S`. -/
theorem finrankK_iSup_le_add (hirr : ∀ φ, ¬ rel φ φ) (htr : ∀ a b c, rel a b → rel b c → rel a c)
    (S : Finset ι) (hS : ∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) :
    ∀ S' : Finset ι, S ⊆ S' → (∀ φ ∈ S', ∀ φ', rel φ φ' → φ' ∈ S') →
      finrankK k (⨆ φ ∈ S', N φ) ≤
        finrankK k (⨆ φ ∈ S, N φ) + ∑ φ ∈ S' \ S, layerRank (k := k) rel N φ := by
  classical
  intro S'
  induction S' using Finset.strongInduction with
  | H S' ih =>
    intro hsub hup
    rcases (S' \ S).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, add_zero, le_antisymm hsub (Finset.sdiff_eq_empty_iff_subset.1 he)]
    let h : ι → ℕ := fun φ => (Finset.univ.filter fun φ' => rel φ φ').card
    obtain ⟨φ, hφ, hmax⟩ := (S' \ S).exists_max_image h hne
    have hφS' := (Finset.mem_sdiff.1 hφ).1
    have hφS := (Finset.mem_sdiff.1 hφ).2
    have hmin : ∀ ψ ∈ S', ¬ rel ψ φ := by
      intro ψ hψ hrel
      by_cases hψS : ψ ∈ S
      · exact hφS (hS ψ hψS φ hrel)
      have hlt : h φ < h ψ := by
        refine Finset.card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
          exact htr _ _ _ hrel ha
        · have := hsub (show φ ∈ Finset.univ.filter fun φ' => rel ψ φ' by simp [hrel])
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          exact hirr φ this
      exact absurd (hmax ψ (Finset.mem_sdiff.2 ⟨hψ, hψS⟩)) (not_le.2 hlt)
    have hup' : ∀ ψ ∈ S'.erase φ, ∀ ψ', rel ψ ψ' → ψ' ∈ S'.erase φ := by
      intro ψ hψ ψ' hrel
      refine Finset.mem_erase.2 ⟨?_, hup ψ (Finset.mem_of_mem_erase hψ) ψ' hrel⟩
      rintro rfl
      exact hmin ψ (Finset.mem_of_mem_erase hψ) hrel
    have hsub' : S ⊆ S'.erase φ := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => hφS (h ▸ hx), hsub hx⟩
    have hIH := ih (S'.erase φ) (Finset.erase_ssubset hφS') hsub' hup'
    have hstep := finrankK_iSup_le_erase (k := k) (N := N) hirr S' hup hφS'
    have hsd : S' \ S = insert φ ((S'.erase φ) \ S) := by
      rw [Finset.erase_sdiff_comm, Finset.insert_erase hφ]
    rw [hsd, Finset.sum_insert (by simp)]
    omega

/-- **Tightness on upward closed sets**: if the layer dimensions add up to the dimension of
the sum of all `N φ`, the same holds on every upward closed set. -/
theorem finrankK_iSup_eq_sum (hirr : ∀ φ, ¬ rel φ φ) (htr : ∀ a b c, rel a b → rel b c → rel a c)
    (htight : ∑ φ, layerRank (k := k) rel N φ = finrankK k (⨆ φ, N φ)) (S : Finset ι)
    (hS : ∀ φ ∈ S, ∀ φ', rel φ φ' → φ' ∈ S) :
    finrankK k (⨆ φ ∈ S, N φ) = ∑ φ ∈ S, layerRank (k := k) rel N φ := by
  classical
  refine le_antisymm (finrankK_iSup_le rel N hirr htr S hS) ?_
  have h := finrankK_iSup_le_add (k := k) (N := N) hirr htr S hS Finset.univ
    (Finset.subset_univ _) (by simp)
  simp only [Finset.mem_univ, iSup_pos] at h
  rw [← htight, ← Finset.sum_sdiff (Finset.subset_univ S)] at h
  omega

/-- **The sum over an upward closed set is filtered by the layers**, when the layer dimensions
add up to the dimension of the sum of all `N φ`. -/
theorem hasFiltration_iSup (hirr : ∀ φ, ¬ rel φ φ) (htr : ∀ a b c, rel a b → rel b c → rel a c)
    (htight : ∑ φ, layerRank (k := k) rel N φ = finrankK k (⨆ φ, N φ)) :
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
    have habove : above rel N φ ≤ P' := by
      refine iSup₂_le fun ψ hrel => ?_
      exact le_biSup N (Finset.mem_erase.2 ⟨fun h => hirr φ (h ▸ hrel), hup φ hφ ψ hrel⟩)
    have hNP : N φ ⊔ above rel N φ ≤ P := sup_le (hD ▸ le_sup_right) (habove.trans hPP')
    -- the map from the layer to `P / P'`
    let θ : layer rel N φ →ₗ[R] ↥P ⧸ P'.comap P.subtype :=
      ((above rel N φ).comap (N φ ⊔ above rel N φ).subtype).liftQ
        ((P'.comap P.subtype).mkQ ∘ₗ Submodule.inclusion hNP) (by
          intro x hx
          rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero]
          exact habove hx)
    have hθ : Function.Surjective θ := by
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
    have hdim : finrank k (layer rel N φ) = finrank k (↥P ⧸ P'.comap P.subtype) := by
      rw [finrank_layer, finrank_quotient_comap_subtype hPP',
        finrankK_iSup_eq_sum (k := k) hirr htr htight S hup,
        finrankK_iSup_eq_sum (k := k) hirr htr htight _ hup', ← Finset.add_sum_erase S _ hφ]
      omega
    have : FiniteDimensional k ↥(N φ ⊔ above rel N φ) :=
      Module.Finite.of_injective ((N φ ⊔ above rel N φ).subtype.restrictScalars k)
        Subtype.val_injective
    have : FiniteDimensional k (layer rel N φ) := Module.Finite.equiv
      (Submodule.Quotient.restrictScalarsEquiv k
        ((above rel N φ).comap (N φ ⊔ above rel N φ).subtype))
    have : FiniteDimensional k ↥P :=
      Module.Finite.of_injective (P.subtype.restrictScalars k) Subtype.val_injective
    have : FiniteDimensional k (↥P ⧸ P'.comap P.subtype) := Module.Finite.equiv
      (Submodule.Quotient.restrictScalarsEquiv k (P'.comap P.subtype))
    have hθb : Function.Bijective θ :=
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
        (f := θ.restrictScalars k)).2 hθ, hθ⟩
    refine ⟨φ :: l, fun ψ hψ => ?_, ?_⟩
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hφ
      · exact Finset.mem_of_mem_erase (hl ψ hψ)
    refine .cons (X := ModuleCat.of R ↥P') (Z := ModuleCat.of R (↥P ⧸ P'.comap P.subtype))
      (Submodule.inclusion hPP') (P'.comap P.subtype).mkQ l φ
      (Submodule.inclusion_injective hPP') ?_ (Submodule.mkQ_surjective _) hX
      ⟨(LinearEquiv.ofBijective θ hθb).symm⟩
    exact exact_inclusion_mkQ hPP'

end Submodule

namespace Categorification.ModuleFiltration.HasFiltration

universe u v w w'

variable {A : Type u} [Ring A] {ι : Type w} {ι' : Type w'}

/-- A filtration whose labels are relabelled. -/
theorem map {L : ι' → ModuleCat.{v} A} (F : ι → ι') {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration (fun c => L (F c)) m Y) : HasFiltration L (m.map F) Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons f g m c hf hfg hg _ hZ ih => exact .cons f g (m.map F) (F c) hf hfg hg ih hZ

/-- A filtration with layers replaced by isomorphic ones along its labels. -/
theorem mono_of_mem {L L' : ι → ModuleCat.{v} A} {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) (hL : ∀ c ∈ m, Nonempty (L c ≃ₗ[A] L' c)) :
    HasFiltration L' m Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    exact .cons f g m c hf hfg hg (ih fun c' hc' => hL c' (List.mem_cons_of_mem _ hc'))
      ⟨e.trans (hL c List.mem_cons_self).some⟩

end Categorification.ModuleFiltration.HasFiltration
