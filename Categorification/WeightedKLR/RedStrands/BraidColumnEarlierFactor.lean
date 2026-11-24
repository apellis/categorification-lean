/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnGeneration

/-!
# Factor through an earlier loading projective

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.11. A word admitting a cut
after a selected diagram with the prescribed red order factors through that
loading projective. Changing to the cut word leaves only shorter subword
corrections.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial

variable {I : Type*} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "q" => violMk k Q Λ ν
local notation "E" => fun s : Seq μ => q (raw (e s))
local notation "C" => fun κ => q (redProj k Q Λ ν κ)

/-- A concatenated crossing word factors through its intermediate loading projective. -/
theorem cutProduct_mem_columnProductsOn (ρ : Equiv.Perm (Fin m) → List ℕ)
    (s : Seq μ) (κ : List (Fin ℓ)) (S : Set (Equiv.Perm (Fin m)))
    {v w : Equiv.Perm (Fin m)} {γ : List ℕ} (hv : v ∈ S)
    (hw : v * wordProd m γ = w) (hk : redWord (v⁻¹ • s) = κ)
    (z : cornerBimodule (E (w⁻¹ • s)) (C κ)) :
    q (raw (ψw (ρ v ++ γ) * e (w⁻¹ • s))) * z.val ∈
      columnProductsOn (Q := Q) (Λ := Λ) ρ s κ S := by
  let t := w⁻¹ • s
  let u := v⁻¹ • s
  have ht : wordProd m γ • t = u := by
    change wordProd m γ • (w⁻¹ • s) = v⁻¹ • s
    rw [← hw, mul_inv_rev, mul_smul, smul_inv_smul]
  have he : (e u * (ψw γ * e t) : KLRAlgebra k (stendhalQ Q Λ) μ) = ψw γ * e t := by
    rw [ψw_mul_e, ht, ← mul_assoc, e_mul_self]
  let a : V := q (raw (ψw γ * e t))
  have ha : E u * a = a := by
    change q (raw (e u)) * q (raw (ψw γ * e t)) = a
    rw [← map_mul q, ← map_mul raw, he]
  refine ⟨v, a * z.val, hv, hk, ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, z.prop.2]⟩, ?_⟩
  change q (raw (ψw (ρ v ++ γ) * e t)) * z.val =
    q (raw (ψw (ρ v) * e u)) * (a * z.val)
  rw [← mul_assoc]
  congr 1
  have hfactor : (ψw (ρ v ++ γ) * e t : KLRAlgebra k (stendhalQ Q Λ) μ) =
      (ψw (ρ v) * e u) * (ψw γ * e t) := by
    rw [ψw_append, mul_assoc (ψw (ρ v)), mul_assoc (ψw (ρ v)), he]
  rw [hfactor, map_mul raw, map_mul q]

/-- Retaining the original bottom idempotent in the word-change estimate
keeps every shorter correction at the very same loading. -/
theorem columnProjection_sub_mem_same_loading_of_braidEquiv
    (ρ : Equiv.Perm (Fin m) → List ℕ) (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (s : Seq μ) (κ : List (Fin ℓ)) {α β : List ℕ} (hB : BraidEquiv α β)
    (hv : ValidWord m α) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    columnProjection (Q := Q) (Λ := Λ) s κ (q (raw (ψw α * pol p * e i))) -
      columnProjection (Q := Q) (Λ := Λ) s κ (q (raw (ψw β * pol p * e i))) ∈
      Submodule.span k (columnProductsOn (Q := Q) (Λ := Λ) ρ s κ
        {w | (w ∈ subProds m α ∧ length m w < α.length - 2) ∧ w⁻¹ • s = i}) := by
  let T : Set (Equiv.Perm (Fin m)) := {w | w ∈ subProds m α ∧ length m w < α.length - 2}
  let f := (columnProjection (Q := Q) (Λ := Λ) s κ).comp
    (((violMk k Q Λ ν).comp raw).toLinearMap.comp (LinearMap.mulRight k (e i)))
  have h := lowSpan_le_stdSpan (Q := Q) (Λ := Λ) ρ hρ _ _
    (braidEquiv_sub_mem_lowSpan (Q := stendhalQ Q Λ) hB hv p i)
  have hm := Submodule.mem_map_of_mem (f := f) h
  rw [stdSpan, Submodule.map_span] at hm
  have hs : f (ψw α * pol p * e i - ψw β * pol p * e i) ∈
      Submodule.span k (columnProductsOn (Q := Q) (Λ := Λ) ρ s κ
        {w | w ∈ T ∧ w⁻¹ • s = i}) := by
    refine (Submodule.span_le.mpr ?_) hm
    rintro _ ⟨_, ⟨⟨j, w, u⟩, hw, rfl⟩, rfl⟩
    change columnProjection s κ (q (raw ((ψw (ρ w) * pol (monomial u 1) * e j) * e i))) ∈ _
    rw [gen_mul_e]
    split_ifs with hj
    · subst j
      by_cases he : w⁻¹ • s = i
      · exact columnProjection_word_mem_span ρ s κ {w | w ∈ T ∧ w⁻¹ • s = i}
          w (hρ w).2 ⟨hw, he⟩ (monomial u 1) i
      · change E s * (q (raw (ψw (ρ w) * pol (monomial u 1) * e i)) * C κ) ∈ _
        rw [← mul_assoc, ← map_mul q, ← map_mul raw, e_mul_gen, (hρ w).2, ite_eq_right he,
          map_zero, map_zero, zero_mul]
        exact zero_mem _
    · rw [map_zero, map_zero, map_zero]
      exact zero_mem _
  simpa only [T, Set.mem_ofPred_eq, f, LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    LinearMap.mulRight_apply, sub_mul, gen_mul_e, ite_eq_left rfl, ↓reduceIte, map_sub] using hs

/-- A cut through an earlier loading projective puts the original diagram in
the earlier span modulo shorter subword terms. The cut has the bottom red
order, and the concatenated word is braid equivalent to the original word.
Webster v2, §6.1, proof of Lemma 6.11. -/
theorem crossing_mul_mem_earlier_sup_short (ρ : Equiv.Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (s : Seq μ) (κ : List (Fin ℓ)) (S : Set (Equiv.Perm (Fin m)))
    {v w : Equiv.Perm (Fin m)} {γ : List ℕ} (hv : v ∈ S)
    (hB : BraidEquiv (ρ w) (ρ v ++ γ))
    (hk : redWord (v⁻¹ • s) = κ) (hwκ : redWord (w⁻¹ • s) = κ)
    (z : cornerBimodule (E (w⁻¹ • s)) (C κ)) :
    q (raw (ψw (ρ w) * e (w⁻¹ • s))) * z.val ∈
      Submodule.span k (columnProductsOn (Q := Q) (Λ := Λ) ρ s κ S) ⊔
      Submodule.span k (columnProductsOn (Q := Q) (Λ := Λ) ρ s κ
        {u | (u ∈ subProds m (ρ w) ∧ length m u < (ρ w).length - 2) ∧ u⁻¹ • s = w⁻¹ • s}) := by
  have hw := ((hB.wordProd_eq (hρ w).1.1).symm.trans (hρ w).2)
  rw [wordProd_append, (hρ v).2] at hw
  have hcut := cutProduct_mem_columnProductsOn ρ s κ S hv hw hk z
  have hβ : wordProd m (ρ v ++ γ) = w := by rw [wordProd_append, (hρ v).2, hw]
  have hshort := columnProjection_sub_mem_same_loading_of_braidEquiv (Q := Q) (Λ := Λ)
    ρ hρ s κ hB (hρ w).1.1 1 (w⁻¹ • s)
  rw [columnProjection_crossing s κ (hρ w).2 hwκ, columnProjection_crossing s κ hβ hwκ] at hshort
  have hshort := mul_mem_span_columnProductsOn ρ s κ _ hshort z.prop.2
  rw [sub_mul] at hshort
  have h := Submodule.add_mem_sup (Submodule.subset_span hcut) hshort
  rwa [add_comm, sub_add_cancel] at h

end Categorification.Stendhal.BraidedStendhalAlgebra
