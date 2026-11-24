/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.FourSlotExitSpan
import Categorification.WeightedKLR.RedStrands.FiniteExitAffineLift
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationSpan

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open TypeA Equiv KLR KLRAlgebra

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun s : KLR.Seq μ => raw (e s)

/-- The four exits with both orders of the two black strands at the middle cut. -/
abbrev FourSlotExit := {w : List ℕ // w ∈ fourSlotExitWords}

instance : Fintype FourSlotExit :=
  Fintype.ofFinset fourSlotExitWords.toFinset (fun _ => List.mem_toFinset)

local notation "leg" => fun (s : KLR.Seq μ) (i : FourSlotExit) => raw (ψw (Subtype.val i) * e s)

/-- The four explicit exits generate the red-dot quotient column. -/
theorem fourSlotExit_generate (hQ : KLRSymm Q) (h : m = 4) (s t : KLR.Seq μ)
    {a b : Fin ℓ} (ha : s.lbl ⟨0, by omega⟩ = Sum.inr a)
    (hb : s.lbl ⟨3, by omega⟩ = Sum.inr b) (ht : [b, a].Sublist (redWord t))
    (z : A) : ∃ c : FourSlotExit → A, p t * z * p s = ∑ i, c i * leg s i := by
  classical
  let L : (FourSlotExit → A) →ₗ[k] A :=
    ∑ i : FourSlotExit, (LinearMap.mulRight k (leg s i)).comp (LinearMap.proj i)
  have hL (c : FourSlotExit → A) : L c = ∑ i, c i * leg s i := by
    simp [L, LinearMap.sum_apply, mul_assoc]
  obtain ⟨y, rfl⟩ := ofKLR_surjective (Q := Q) (Λ := Λ) z
  have hs := mem_span_fourSlotExit_column (stendhalQ_symm Q Λ hQ) h s t
    (fun w hw => (mem_invSet.mp (mem_invSet_of_sublist_redWord
      (by rw [hw]; exact ht) (by change 0 < 3; decide) ha hb)).2) y
  have hspan : Submodule.span k {y : R |
      ∃ (ρ : List ℕ) (_ : ρ ∈ fourSlotExitWords) (x : R),
        e t * x * e ((wordProd m ρ) • s) = x ∧ y = x * (ψw ρ * e s)} ≤
      (LinearMap.range L).comap (raw).toLinearMap := by
    apply Submodule.span_le.2
    rintro _ ⟨ρ, hρ, x, _, rfl⟩
    let i : FourSlotExit := ⟨ρ, hρ⟩
    refine ⟨Pi.single i (raw x), ?_⟩
    rw [hL, Finset.sum_eq_single i]
    · simp [i, map_mul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · exact fun hh => (hh (Finset.mem_univ i)).elim
  obtain ⟨c, hc⟩ := hspan hs
  refine ⟨c, ?_⟩
  simpa only [hL, AlgHom.toLinearMap_apply, map_mul] using hc.symm

/-- A relation on the four explicit exits lifts from the violated quotient,
with all coefficient projections fixed. -/
theorem exists_fourSlotExitRelation_affine_lift (hQ : KLRSymm Q) (h : m = 4) (s t : KLR.Seq μ)
    {a b : Fin ℓ} (ha : s.lbl ⟨0, by omega⟩ = Sum.inr a)
    (hb : s.lbl ⟨3, by omega⟩ = Sum.inr b) (ht : [b, a].Sublist (redWord t))
    (x : FourSlotExit → V)
    (hs : ∀ i, mk (p t) * x i * mk (p (wordProd m i.val • s)) = x i)
    (hz : ∑ i, x i * mk (leg s i) = 0) :
    ∃ c : FourSlotExit → A,
      (∀ i, mk (p t * c i * p (wordProd m i.val • s)) = x i) ∧
      ∑ i, (p t * c i * p (wordProd m i.val • s)) * leg s i = 0 := by
  exact exists_finiteExitRelation_affine_lift Q Λ s t Subtype.val hQ
    (fun v hv z => fourSlotExit_generate Q Λ hQ h s v ha hb (hv.symm ▸ ht) z) x hs hz

end Categorification.Stendhal.BraidedStendhalAlgebra
