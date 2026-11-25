/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBlockPermutation

/-!
# Support of projected braid-column corrections

Webster, arXiv:1309.3796v2, Lemma 6.11 and v3, Lemma 6.12. In the
crossing induction, straightening a lower-span term retains its subword
support and yields a reduced word below the given bound. Projection
keeps precisely the terms at the same prescribed loading pair.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra
open MvPolynomial

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)

/-- Projection retains only the terms with the prescribed top and bottom.
Each raw correction word straightens to reduced diagrams of smaller
Coxeter length, with subword support retained. -/
theorem braidColumnLoadingProjection_map_lowSpan_le_same_bottom
    (top bottom : Seq μ) (ρ : Perm (Fin m) → List ℕ)
    (hρ : IsReducedChoice ρ) (S : Set (Perm (Fin m))) (L : ℕ) :
    (lowSpan k (stendhalQ Q Λ) μ S L).map
      (braidColumnLoadingProjection (Q := Q) (Λ := Λ) top bottom) ≤
    Submodule.span k {x | ∃ w : Perm (Fin m), ∃ a : Fin m →₀ ℕ,
      w ∈ S ∧ length m w < L ∧ w⁻¹ • top = bottom ∧
      x = F (ψw (ρ w) * pol (monomial a 1) * e bottom)} := by
  have hraw : lowSpan k (stendhalQ Q Λ) μ S L ≤
      stdSpan (stendhalQ Q Λ) ρ {w | w ∈ S ∧ length m w < L} := by
    rw [lowSpan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨τ,p,b,hv,hS,hL,rfl⟩
    apply stdSpan_mono ρ _ (gen_mem_stdSpan ρ hρ τ hv p b)
    intro w hw
    refine ⟨hS hw, ?_⟩
    obtain ⟨δ, hδ, heq⟩ := mem_subProds.mp hw
    exact (length_le_of_wordProd_eq (hv.sublist hδ) heq).trans_lt
      (hδ.length_le.trans_lt hL)
  refine le_trans (Submodule.map_mono hraw) ?_
  rw [stdSpan, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨⟨b,w,a⟩,hw,rfl⟩,rfl⟩
  change F (e top * ((ψw (ρ w) * pol (monomial a 1) * e b) * e bottom)) ∈ _
  rw [gen_mul_e]
  by_cases hb : b = bottom
  · subst b
    rw [ite_eq_left rfl, e_mul_gen, (hρ w).2]
    by_cases ht : w⁻¹ • top = bottom
    · rw [ite_eq_left ht]
      exact Submodule.subset_span ⟨w,a,hw.1,hw.2,ht,rfl⟩
    · rw [ite_eq_right ht,map_zero]
      exact zero_mem _
  · rw [ite_eq_right hb,mul_zero,map_zero]
    exact zero_mem _

end Categorification.Stendhal
