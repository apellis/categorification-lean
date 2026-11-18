/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NegligibleMaps
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverRedDotAction

/-!
# Morphisms negligible for unique red colours

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. In the extended
cyclotomic action, a set `R` of colours each occurring once acts through the
central coloured dot sums. Morphisms factoring through these central actions
are stable under induction and restriction at colours outside `R`, and at the
final tensor-product block the projection kills them when `R` consists of red
colours. This is the ideal through which the downward relations of the double
calculus are checked on the regular module.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra KLR.CyclotomicAction InductionAlong

universe u v w

section Cyclotomic

variable {C : Type u} {k : Type v} [DecidableEq C] [CommRing k]
  (S : C → C → MvPolynomial (Fin 2) k) (p : C → Polynomial k)
  (hc : ∀ δ c (z : CycKLR k S p δ), Commute z (cyclotomicColourDot S p δ c))
  (R : Set C)

/-- The central coloured-dot actions of the colours in `R` on the block `β`. -/
def colourDotActions (β : Multiset C) :
    Set (𝟭 (ModuleCat.{max (max u v) w} (CycKLR k S p β)) ⟶ 𝟭 _) :=
  {η | ∃ c ∈ R, η = centralModuleAction _ (hc β c)}

variable {S p hc R}

/-- Induction at a colour outside `R` preserves morphisms negligible for `R`,
when every colour of `R` occurs once below. -/
theorem ind_map_mem_negligible {β : Multiset C} (j : C) (hj : j ∉ R)
    (hR : ∀ c ∈ R, β.count c = 1)
    {M N : ModuleCat.{max (max u v) w} (CycKLR k S p β)} {f : M ⟶ N}
    (hf : f ∈ negligible (colourDotActions S p hc R β) M N) :
    (CyclotomicAction.ind S p j rfl).map f ∈
      negligible (colourDotActions S p hc R ({j} + β)) _ _ := by
  refine map_mem_negligible _ ?_ hf
  rintro η ⟨c, hcR, rfl⟩
  refine ⟨_, ⟨c, hcR, rfl⟩, fun N => ?_⟩
  have hβ := hR c hcR
  have hjc : c ≠ j := fun h => hj (h ▸ hcR)
  exact ind_map_centralModuleAction _ _ _ _ _
    (lastEmb_cyclotomicColourDot_of_count S p j c hjc hβ) N

/-- Restriction at a colour outside `R` preserves morphisms negligible for
`R`, when every colour of `R` occurs once in the result. -/
theorem res_map_mem_negligible {γ : Multiset C} (j : C) (hj : j ∉ R)
    (hR : ∀ c ∈ R, γ.count c = 1)
    {M N : ModuleCat.{max (max u v) w} (CycKLR k S p ({j} + γ))} {f : M ⟶ N}
    (hf : f ∈ negligible (colourDotActions S p hc R ({j} + γ)) M N) :
    (CyclotomicAction.res S p j rfl).map f ∈
      negligible (colourDotActions S p hc R γ) _ _ := by
  refine map_mem_negligible _ ?_ hf
  rintro η ⟨c, hcR, rfl⟩
  refine ⟨_, ⟨c, hcR, rfl⟩, fun N => ?_⟩
  have hγ := hR c hcR
  have hjc : c ≠ j := fun h => hj (h ▸ hcR)
  exact res_map_centralModuleAction _ _ _ _ _
    (lastEmb_cyclotomicColourDot_of_count S p j c hjc hγ) N

end Cyclotomic

section Projection

variable {J : Type u} {K : Type v} [DecidableEq J] [Field K] {m : ℕ}
  {Q₀ : J → J → MvPolynomial (Fin 2) K} (Λ₀ : Fin m → J →₀ ℕ)
  (ν₀ : Multiset J) (C₀ : QuantumGroup.CartanDatum J)

local notation "S" => cyclotomicCoverQ C₀ Λ₀ Q₀
local notation "p" => cyclotomicCoverPolynomial (k := K) (I := J) (ℓ := m)
local notation "π" => RingHom.toNonUnitalRingHom
  (AlgHom.toRingHom (cyclotomicCoverToTensor (Q := Q₀) Λ₀ ν₀ C₀))
local notation "μ" => stendhalWeight m ν₀

/-- At the tensor-product block, projection kills every morphism negligible
for a set of red colours. -/
theorem cyclotomicCover_project_eq_zero_of_mem_negligible
    {hc : ∀ δ c (z : CycKLR K S p δ), Commute z (cyclotomicColourDot S p δ c)}
    {R : Set (J ⊕ Fin m)} (hR : R ⊆ Set.range Sum.inr)
    {M N : ModuleCat.{max (max u v) w} (CycKLR K S p μ)} {f : M ⟶ N}
    (hf : f ∈ negligible (colourDotActions S p hc R μ) M N) :
    (functor π).map f = 0 := by
  refine map_eq_zero_of_mem_negligible _ ?_ hf
  rintro η ⟨c, hcR, rfl⟩ N
  obtain ⟨r, rfl⟩ := hR hcR
  exact ind_map_centralModuleAction_eq_zero _ _ _
    (cyclotomicCoverToTensor_colourDot Λ₀ ν₀ C₀ r) N

end Projection

end Categorification.Stendhal
