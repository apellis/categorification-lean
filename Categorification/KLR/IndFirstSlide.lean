/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandFirstFactor
import Categorification.KLR.Crystal.IndDecomp

/-!
# Sliding the last strand to the front of the second factor

For `ν = ν₀ + i` the element `G = 1_{ν,ν'} ψ_d^* 1_{ν₀ + ν', i}` of `R(ν₀ + ν' + i)`, where `ψ_d^*`
is the horizontal flip of the crossing `ψ_d` of `IndLastStrandFirstFactor` moving the last strand
of `ν₀ + i` across `ν'`, satisfies
`G ι(ι(t) ⊗ 1_i) = ι_{ν,ν'}(t ⊗_{ν₀} 1_i) G` up to a defect, the horizontal flip of a lower Mackey
step. The defect vanishes on every vector `u` killed by the idempotents `e_s ι(T)` for which the
last label of `s` lies in the second block `ν'`.

This is the KLR input of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5: the map from `Ind ₁F_i N` to the module with the new
strand moved to the left of the last block.

## Main results

* `firstG_mul_appendR_concat` : the intertwining identity with its defect;
* `firstG_mul_appendR_concat_smul` : the identity on vectors killed by the idempotents above.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

section Flip

variable {μ μ' ν ν' ν'' ν''' : Multiset I}

theorem hflip_castAlg (h : μ = μ') (a : KLRAlgebra k Q μ) :
    hflip (castAlg Q h a) = castAlg Q h (hflip a) := by
  subst h
  rw [castAlg_eq_castKLR, castAlg_eq_castKLR, castKLR_rfl, castKLR_rfl]

theorem hflip_botConcat (h : ν'' + ν''' = ν + ν') (t : TensorKLR Q ν'' ν''') :
    hflip (botConcat Q h t) = botConcat Q h (tensorHflip ν'' ν''' t) := by
  rw [botConcat_apply, botConcat_apply, hflip_castAlg, hflip_concat]

theorem hflip_botOne (h : ν'' + ν''' = ν + ν') :
    hflip (botOne Q h) = botOne Q h :=
  hflip_eSum _

theorem hflip_appendR (i : I) (a : KLRAlgebra k Q ν) :
    hflip (appendR Q ν i a) = appendR Q ν i (hflip a) := by
  rw [appendR_apply, appendR_apply, hflip_concat_tmul_one]

theorem tensorHflip_tensorAppendL (i : I) (t : TensorKLR Q ν ν') :
    tensorHflip (ν + Si i) ν' (tensorAppendL Q ν ν' i t) =
      tensorAppendL Q ν ν' i (tensorHflip ν ν' t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht]
  | tmul a b =>
    rw [tensorAppendL_tmul, tensorHflip_tmul, tensorHflip_tmul, tensorAppendL_tmul,
      hflip_appendR]

end Flip

section Slide

variable (Q) (ν₀ ν' : Multiset I) (i : I)

/-- `G = 1_{ν₀ + i, ν'} ψ_d^* 1_{ν₀ + ν', i}`. -/
noncomputable def firstG : KLRAlgebra k Q (ν₀ + ν' + Si i) :=
  botOne Q (firstQuad_h ν₀ ν' i) * hflip (firstψ Q ν₀ ν' i) * oneConcat Q (ν₀ + ν') (Si i)

variable {Q ν₀ ν' i}

/-- **The slide identity**: `G ι(ι(t) ⊗ 1) = ι(t ⊗ 1) G` up to the flipped defect. -/
theorem firstG_mul_appendR_concat (t : TensorKLR Q ν₀ ν') :
    firstG Q ν₀ ν' i * appendR Q _ i (concat Q ν₀ ν' t) =
      hflip (oneConcat Q (ν₀ + ν') (Si i) *
          quadDefect (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) (tensorHflip ν₀ ν' t ⊗ₜ 1) *
          botOne Q (firstQuad_h ν₀ ν' i)) +
        botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i t) * firstG Q ν₀ ν' i := by
  have h := congrArg hflip (appendR_mul_concat_mul_firstψ (Q := Q) (i := i) 1
    (tensorHflip ν₀ ν' t))
  rw [one_mul, hflip_mul, hflip_appendR, hflip_concat, tensorHflip_tensorHflip, hflip_add,
    hflip_mul, hflip_mul, hflip_mul, hflip_botConcat, tensorHflip_tensorAppendL,
    tensorHflip_tensorHflip, appendR_one, hflip_oneConcat] at h
  have hc : oneConcat Q (ν₀ + ν') (Si i) * appendR Q _ i (concat Q ν₀ ν' t) =
      appendR Q _ i (concat Q ν₀ ν' t) := by
    rw [appendR_apply, oneConcat_mul_concat]
  rw [firstG, mul_assoc, hc, mul_assoc, h, mul_add, hflip_mul, hflip_mul, hflip_oneConcat,
    hflip_botOne, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, botOne_mul_botConcat,
    ← mul_assoc (botConcat Q _ _), botConcat_mul_botOne]

end Slide

section Vanishing

variable {ν₀ ν' : Multiset I} {i : I}
variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (KLRAlgebra k Q (ν₀ + ν' + ({i} : Multiset I))) M]
  [IsScalarTower k (KLRAlgebra k Q (ν₀ + ν' + ({i} : Multiset I))) M]

/-- A vector killed by the idempotents `e_s ι(T)` with `s` in both `concatSet (ν₀ + ν') i` and
the block set of `(ν₀ + i, ν')` is killed by the flip of every Mackey step with fewer than `|ν'|`
crossings. -/
theorem hflip_smul_eq_zero_of_mem_filt {u : M}
    (hu : ∀ s ∈ concatSet (ν₀ + ν') (Si i), s ∈ botSet (firstQuad_h ν₀ ν' i) →
      ∀ T : TensorKLR Q (ν₀ + ν') (Si i), (e s * concat Q (ν₀ + ν') (Si i) T) • u = 0)
    {c : ℕ} (hc : c + 1 ≤ Multiset.card ν')
    {w : KLRAlgebra k Q (ν₀ + ν' + Si i)}
    (hw : w ∈ mackeyBimodFilt Q (firstQuad_h ν₀ ν' i) c) : hflip w • u = 0 := by
  rw [mackeyBimodFilt_eq_span_crossings (firstQuad_h ν₀ ν' i) (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)] at hw
  induction hw using Submodule.span_induction with
  | zero => rw [hflip_zero, zero_smul]
  | add w w' _ _ hw hw' => rw [hflip_add, add_smul, hw, hw', add_zero]
  | smul c w _ hw => rw [hflip_smul, smul_assoc, hw, smul_zero]
  | mem w hw =>
    obtain ⟨d, t₁, t', hd, hdc, rfl⟩ := hw
    have h1 : d = 1 := IsDoubleShuffle.eq_one_of_crossCount_lt (Seq.card_add' _ _)
      (by simp) (card_add_bot (firstQuad_h ν₀ ν' i)) hd (by omega)
    subst h1
    rw [canWord_one, ψw_nil, mul_one, ← concat_mul_oneConcat, ← botOne_mul_botConcat, mul_assoc,
      ← mul_assoc (oneConcat Q _ _), hflip_mul, hflip_mul, hflip_mul, hflip_botConcat,
      hflip_oneConcat, hflip_botOne, hflip_concat, botOne, oneConcat, eSum_mul_eSum, eSum,
      mul_assoc, mul_smul, Finset.sum_mul, Finset.sum_smul]
    refine (congrArg _ (Finset.sum_eq_zero fun s hs => ?_)).trans (smul_zero _)
    rw [Finset.mem_inter] at hs
    exact hu s hs.2 hs.1 _

/-- **The flipped defect vanishes** on vectors killed by the idempotents above. -/
theorem hflip_defect_smul_eq_zero {u : M}
    (hu : ∀ s ∈ concatSet (ν₀ + ν') (Si i), s ∈ botSet (firstQuad_h ν₀ ν' i) →
      ∀ T : TensorKLR Q (ν₀ + ν') (Si i), (e s * concat Q (ν₀ + ν') (Si i) T) • u = 0)
    {D : KLRAlgebra k Q (ν₀ + ν' + Si i)}
    (hD : D ∈ mackeyLower k Q (ν₀ + ν' + Si i) (Multiset.card (ν₀ + ν'))
      (Multiset.card (ν₀ + Si i)) (Multiset.card ν')) :
    hflip (oneConcat Q (ν₀ + ν') (Si i) * D * botOne Q (firstQuad_h ν₀ ν' i)) • u = 0 := by
  rcases hν : Multiset.card ν' with _ | c
  · rw [hν] at hD
    rw [(Submodule.mem_bot k).1 hD, mul_zero, zero_mul, hflip_zero, zero_smul]
  · rw [hν] at hD
    refine hflip_smul_eq_zero_of_mem_filt hu (c := c) (by omega) ?_
    rw [← mackeyLowerBimod_succ]
    refine ⟨(mem_bimod _).2 ?_, ?_⟩
    · simp only [← mul_assoc, oneConcat_idem.eq]
      rw [mul_assoc _ (botOne Q _), (botOne_idem _).eq]
    · have h1 := mackeyLower_concat_mul 1 hD
      have h2 := mackeyLower_mul_botConcat (firstQuad_h ν₀ ν' i) 1 h1
      rw [concat_one, botConcat_one] at h2
      exact h2

/-- **The slide identity on vectors** killed by the idempotents `e_s ι(T)` whose last label lies
in the second block. -/
theorem firstG_mul_appendR_concat_smul {u : M}
    (hu : ∀ s ∈ concatSet (ν₀ + ν') (Si i), s ∈ botSet (firstQuad_h ν₀ ν' i) →
      ∀ T : TensorKLR Q (ν₀ + ν') (Si i), (e s * concat Q (ν₀ + ν') (Si i) T) • u = 0)
    (t : TensorKLR Q ν₀ ν') :
    (firstG Q ν₀ ν' i * appendR Q _ i (concat Q ν₀ ν' t)) • u =
      (botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i t) * firstG Q ν₀ ν' i) • u := by
  rw [firstG_mul_appendR_concat, add_smul,
    hflip_defect_smul_eq_zero hu (quad_intertwine (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) _),
    zero_add]

end Vanishing

end KLRAlgebra

end Categorification.KLR
