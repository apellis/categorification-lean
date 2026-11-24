/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.KLR.PolNu

/-!
# Dimension of a vacuum braid column

Webster, arXiv:1309.3796v2, Proposition 6.4 and proof of Lemma 6.11.
With zero black strands, the fixed-top braid column has one basis vector.
The red orders determine both loadings and their unique connecting
permutation, there are no dot monomials, and the violated ideal is zero.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MulOpposite

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "ν₀" => (0 : Multiset I)
local notation "μ" => stendhalWeight ℓ ν₀
local notation "m" => Multiset.card μ
local notation "q" => violMk k Q Λ ν₀
local notation "raw" => ofKLR k Q Λ ν₀

omit [DecidableEq I] in
private theorem vacuum_right (s : Seq μ) (a : Fin m) : (s.lbl a).isRight := by
  have h := s.mem a
  have hs : ∃ r, s.lbl a = .inr r := by
    simpa [stendhalWeight, eq_comm] using h
  obtain ⟨r, hr⟩ := hs
  rw [hr]
  rfl

omit [DecidableEq I] in
private theorem vacuum_redWord_injective : Function.Injective (redWord : Seq μ → List (Fin ℓ)) := by
  intro s t h
  have list_of (u : Seq μ) : (redWord u).map (Sum.inr : Fin ℓ → I ⊕ Fin ℓ) = List.ofFn u.lbl := by
    rw [redWord, List.map_filterMap, List.ofFn_eq_map]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro a _
    have hr := vacuum_right u a
    cases h : u.lbl a <;> simp_all
  apply Subtype.ext
  apply List.ofFn_injective
  rw [← list_of s, ← list_of t, h]

omit [DecidableEq I] in
private theorem vacuum_lbl_injective (s : Seq μ) : Function.Injective s.lbl := by
  intro a b h
  have hr := vacuum_right s a
  cases ha : s.lbl a with
  | inl _ => simp [ha] at hr
  | inr r => exact lbl_inj_of_inr s r ha (h.symm.trans ha)

private theorem vacuum_violIdeal_eq_bot : violIdeal k Q Λ ν₀ = ⊥ := by
  apply le_antisymm _ bot_le
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨s, ⟨h, hs⟩, rfl⟩
  have hr := vacuum_right s ⟨0, h⟩
  cases he : s.lbl ⟨0, h⟩ <;> simp_all

private theorem vacuum_violMk_injective : Function.Injective q := by
  intro x y h
  have hz : q (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hm := (violMk_eq_zero_iff _).1 hz
  rw [vacuum_violIdeal_eq_bot Q Λ, TwoSidedIdeal.mem_bot] at hm
  exact sub_eq_zero.mp hm

private theorem vacuum_redProj_eq (s : Seq μ) : redProj k Q Λ ν₀ (redWord s) = raw (e s) := by
  change raw (redIdem k Q Λ (redWord s)) = raw (e s)
  congr 1
  unfold redIdem
  refine Finset.sum_eq_single s (fun t ht hn => ?_) (fun h => ?_)
  · exact (hn (vacuum_redWord_injective (Finset.mem_filter.mp ht).2)).elim
  · exact (h (by simp)).elim

/-- The fixed-top vacuum column in the violated quotient is the affine
vacuum column, since there are no violated loadings. -/
noncomputable def vacuumColumnEquiv (s t : Seq μ) :
    cornerSpace k Q Λ ν₀ (redWord s) (redWord t) ≃ₗ[k]
      violCorner k Q Λ ν₀ s (redWord t) := by
  let f : cornerSpace k Q Λ ν₀ (redWord s) (redWord t) →ₗ[k]
      violCorner k Q Λ ν₀ s (redWord t) :=
    ((violMk k Q Λ ν₀).toLinearMap.comp (cornerSpace k Q Λ ν₀ (redWord s) (redWord t)).subtype).codRestrict _ (by
      intro x
      obtain ⟨a,ha⟩ := x.prop
      change redProj k Q Λ ν₀ (redWord s) * (a * redProj k Q Λ ν₀ (redWord t)) = x.val at ha
      rw [vacuum_redProj_eq Q Λ s] at ha
      exact ⟨a, congrArg q ha⟩)
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (vacuum_violMk_injective Q Λ (congrArg Subtype.val h))
  · intro y
    obtain ⟨a, ha⟩ := y.prop
    let x : cornerSpace k Q Λ ν₀ (redWord s) (redWord t) :=
      ⟨redProj k Q Λ ν₀ (redWord s) * (a * redProj k Q Λ ν₀ (redWord t)), a, rfl⟩
    refine ⟨x, Subtype.ext ?_⟩
    change q (redProj k Q Λ ν₀ (redWord s) * (a * redProj k Q Λ ν₀ (redWord t))) = y.val
    rw [vacuum_redProj_eq Q Λ s]
    exact ha

/-- Vacuum case of the dimension comparison in Webster v2, §6.1, Lemma 6.11.
For any top and bottom red orders given by loadings, the fixed-top braid
column has dimension one. -/
theorem finrank_vacuum_braidColumn (hQ : KLRSymm Q) (s t : Seq μ) :
    Module.finrank k (violCorner k Q Λ ν₀ s (redWord t)) = 1 := by
  classical
  have sub : Subsingleton {b : BlackIdx (ℓ := ℓ) ν₀ //
      redWord (b.1.2.1 • b.1.1) = redWord s ∧ redWord b.1.1 = redWord t} := by
    constructor
    rintro ⟨⟨⟨t₁, w₁, u₁⟩, hu₁⟩, hs₁, ht₁⟩ ⟨⟨⟨t₂, w₂, u₂⟩, hu₂⟩, hs₂, ht₂⟩
    have ht : t₁ = t₂ := vacuum_redWord_injective (ht₁.trans ht₂.symm)
    subst t₂
    have hsmul : w₁ • t₁ = w₂ • t₁ := vacuum_redWord_injective (hs₁.trans hs₂.symm)
    have hw : w₁ = w₂ := by
      apply Equiv.symm_bijective.injective
      apply Equiv.ext
      intro a
      have hh := congrArg (fun z : Seq μ => z.lbl a) hsmul
      exact vacuum_lbl_injective t₁ hh
    have hu : u₁ = u₂ := by
      apply Finsupp.ext
      intro a
      exact (hu₁ a (vacuum_right t₁ a)).trans (hu₂ a (vacuum_right t₁ a)).symm
    subst w₂
    subst u₂
    rfl
  obtain ⟨w, hw⟩ := Seq.exists_smul_eq t s
  let idx : {b : BlackIdx (ℓ := ℓ) ν₀ //
      redWord (b.1.2.1 • b.1.1) = redWord s ∧ redWord b.1.1 = redWord t} :=
    ⟨⟨(t, w, 0), fun _ _ => rfl⟩, congrArg redWord hw, rfl⟩
  have : Fintype {b : BlackIdx (ℓ := ℓ) ν₀ //
      redWord (b.1.2.1 • b.1.1) = redWord s ∧ redWord b.1.1 = redWord t} :=
    @Fintype.ofSubsingleton _ idx sub
  have : Unique {b : BlackIdx (ℓ := ℓ) ν₀ //
      redWord (b.1.2.1 • b.1.1) = redWord s ∧ redWord b.1.1 = redWord t} :=
    ⟨⟨idx⟩, fun a => sub.elim a idx⟩
  rw [← (vacuumColumnEquiv Q Λ s t).finrank_eq,
    Module.finrank_eq_card_basis
      (cornerBasis (Λ := Λ) hQ (canWord m)
        (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) (redWord s) (redWord t))]
  exact Fintype.card_unique

theorem vacuum_violStandardUpper_eq_bot (t : Seq μ) :
    violStandardUpper (k := k) (Q := Q) (Λ := Λ) t (redWord t) = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨j, _, hred, hlt, _⟩
  have hj := vacuum_redWord_injective hred
  subst j
  exact (hlt.2 (fun _ _ => le_rfl)).elim

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "Right" κ:arg => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν₀) κ)ᵐᵒᵖ

private instance vacuumCornerRightScalarTower (t : Seq μ) (κ : List (Fin ℓ)) :
    IsScalarTower k (Right κ) (violCorner k Q Λ ν₀ t κ) where
  smul_assoc c a x := Subtype.ext <| by
    rw [violCorner_smul_val, Submodule.coe_smul_of_tower, violCorner_smul_val]
    change x.1 * (c • a.unop.val) = c • (x.1 * a.unop.val)
    rw [mul_smul_comm]

private noncomputable instance vacuumStandardModule (t : Seq μ) (κ : List (Fin ℓ)) :
    Module k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t κ) :=
  Submodule.Quotient.module' (violStandardUpper t κ)

/-- The vacuum braid column has the dimension of its single proposed standard
factor, as required by the dimension argument in Webster's Lemma 6.11. -/
theorem finrank_vacuum_braidColumn_eq_standard (hQ : KLRSymm Q) (s t : Seq μ) :
    Module.finrank k (violCorner k Q Λ ν₀ s (redWord t)) =
      Module.finrank k (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t (redWord t)) := by
  have e := (Submodule.quotEquivOfEqBot (violStandardUpper (k := k) (Q := Q) (Λ := Λ)
    t (redWord t)) (vacuum_violStandardUpper_eq_bot Q Λ t)).restrictScalars k
  rw [e.finrank_eq, finrank_vacuum_braidColumn Q Λ hQ s t,
    finrank_vacuum_braidColumn Q Λ hQ t t]

end Categorification.Stendhal.BraidedStendhalAlgebra
