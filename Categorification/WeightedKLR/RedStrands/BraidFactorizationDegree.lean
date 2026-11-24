/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NormalizedBraidMultiplication
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient
import Mathlib.Data.List.NodupEquivFin

/-!
# Length and degree in braid factorization

The inversion-set condition of Webster's Lemma 6.5 implies additivity of
the normalized degree offsets. Ordinary diagram multiplication identifies
the factorized balanced tensor with the actual rectangular quotient corner.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open scoped List

private theorem pair_sublist_iff_index {α : Type*} [DecidableEq α]
    {l : List α} (hl : l.Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) :
    [a, b] <+ l ↔ l.idxOf a < l.idxOf b := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  constructor
  · rintro ⟨f, hf⟩
    have h₀ : l.get (f 0) = a := (hf 0).symm
    have h₁ : l.get (f 1) = b := (hf 1).symm
    rw [← h₀, ← h₁, List.get_idxOf hl, List.get_idxOf hl]
    exact f.strictMono (show (0 : Fin 2) < 1 by decide)
  · intro h
    let i : Fin l.length := ⟨l.idxOf a, List.idxOf_lt_length_iff.mpr ha⟩
    let j : Fin l.length := ⟨l.idxOf b, List.idxOf_lt_length_iff.mpr hb⟩
    let f : Fin [a, b].length → Fin l.length := fun k => if k = 0 then i else j
    have hf : StrictMono f := by
      intro c d hcd
      fin_cases c <;> fin_cases d <;> try contradiction
      exact h
    refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
    intro ix
    fin_cases ix
    · exact (List.idxOf_get _).symm
    · exact (List.idxOf_get _).symm

/-- The length-additivity condition used in the ordinary braid factorization
also gives additivity of the normalized degree offsets. -/
theorem redWordOffset_add_of_sublist {ℓ : ℕ} {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin ℓ → Module.Dual ℂ H)
    {lower middle upper : List (Fin ℓ)}
    (hL : lower.Nodup) (hM : middle.Nodup) (hU : upper.Nodup)
    (hmL : ∀ r, r ∈ lower) (hmM : ∀ r, r ∈ middle) (hmU : ∀ r, r ∈ upper)
    (Hlen : ∀ r d, [r, d] <+ lower → [d, r] <+ middle → [d, r] <+ upper) :
    redWordOffset B η lower upper = redWordOffset B η lower middle + redWordOffset B η middle upper := by
  apply redWordOffset_add B η hmL hmM hmU
  intro r d hl hm hu
  have hu' := Hlen r d ((pair_sublist_iff_index hL (hmL r) (hmL d)).mpr hl)
    ((pair_sublist_iff_index hM (hmM d) (hmM r)).mpr hm)
  exact lt_asymm hu ((pair_sublist_iff_index hU (hmU d) (hmU r)).mp hu')

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv
open scoped List

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {lower middle upper : List (Fin ℓ)}

local notation "A" => ViolQuotient k Q Λ ν
local notation "e" κ:arg => violMk k Q Λ ν (redProj k Q Λ ν κ)
local notation "hE" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "T" => CornerTensor k A (e upper) (e middle) (e lower)
local notation "mult" => CornerTensor.mult (k := k) (hE upper) (hE middle) (hE lower)

private theorem mult_mem (t : T) : mult t ∈ braidingBimodule k Q Λ ν upper lower := by
  induction t using CornerTensor.induction_on with
  | tmul x y =>
    rw [CornerTensor.mult_tmul]
    apply mem_cornerBimodule.mpr
    constructor
    · simp only [← mul_assoc, (hE upper).eq]
    · rw [mul_assoc _ (e lower) (e lower), (hE lower).eq]
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- The ordinary balanced multiplication valued in the actual quotient corner. -/
noncomputable def violCornerTensorMul : T →+ braidingBimodule k Q Λ ν upper lower where
  toFun t := ⟨mult t, mult_mem t⟩
  map_zero' := Subtype.ext (map_zero mult)
  map_add' x y := Subtype.ext (map_add mult x y)

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}

/-- The ordinary quotient form of Lemma 6.5 as an equivalence with the actual
corner coefficient. -/
noncomputable def violCornerTensorMulEquiv (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    T ≃+ braidingBimodule k Q Λ ν upper lower :=
  AddEquiv.ofBijective violCornerTensorMul ⟨
    fun _ _ h => violMk_mult_injective hρ hQ h0 hp H (congrArg Subtype.val h),
    fun z => by
      obtain ⟨t, ht⟩ := violMk_mult_surjective hρ hQ h0 hp H z.val
      obtain ⟨hL, hR⟩ := mem_cornerBimodule.mp z.property
      rw [hL, hR] at ht
      exact ⟨t, Subtype.ext ht⟩⟩

/-- On a tensor of corner elements, the ordinary equivalence is diagram multiplication. -/
theorem violCornerTensorMulEquiv_tmul (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper)
    (x : braidingBimodule k Q Λ ν upper middle) (y : braidingBimodule k Q Λ ν middle lower) :
    (violCornerTensorMulEquiv hρ hQ h0 hp H (CornerTensor.tmul x.val y.val)).val =
      x.val * y.val := by
  change mult (CornerTensor.tmul x.val y.val) = _
  have hx := mem_cornerBimodule.mp x.property
  have hy := mem_cornerBimodule.mp y.property
  rw [CornerTensor.mult_tmul, hx.1, hx.2, mul_assoc, hy.2]

end Categorification.Stendhal.BraidedStendhalAlgebra
