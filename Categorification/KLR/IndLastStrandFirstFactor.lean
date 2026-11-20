/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandOneSided

/-!
# The last strand of an induced module when `i` occurs in the first factor only

Khovanov–Lauda I (arXiv:0803.4121v2), Proposition 2.18, in the case where the restricted colour
`i` does not occur in the second factor: for `ν = ν₀ + i` and `i ∉ ν'`,
`Ψ : Ind_{ν₀,ν'} ₁N → E(Ind_{ν,ν'} N)`, `r ⊗ n ↦ ι(r ⊗ 1_i) ψ_d ⊗ n`, is an isomorphism, where
`d` moves the last strand of `ν` across `ν'`. This is the KLR input of B. Webster, *Knot
invariants and higher representation theory*, arXiv:1309.3796v3, proof of Proposition 5.5, in
the case where `i` occurs in the weight of the first block only.

The intertwining defect of `ψ_d` lies in the lower Mackey step, which vanishes here: its
generators have fewer than `|ν'|` crossings, hence `d = 1`, and the idempotent
`1_{ν₀ + ν', i} 1_{ν, ν'}` is zero since the last strand would be a strand of `ν'` coloured `i`.

## Main results

* `indFirst` : the map `Ψ`, well defined for `i ∉ ν'`;
* `firstIdem_smul_indFirst` : `Ψ` lands in `E(Ind_{ν,ν'} N)`;
* `mem_range_indFirst` : `E(Ind_{ν,ν'} N)` lies in the image of `Ψ`;
* `indFirst_injective` : `Ψ` is injective.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

/-! ### The Mackey datum of the first factor -/

section FirstQuad

variable (ν₀ ν' : Multiset I) (i : I)

omit [DecidableEq I] in
theorem firstQuad_h : ν₀ + Si i + ν' = ν₀ + ν' + Si i := add_right_comm _ _ _

/-- The Mackey datum `(α, β, γ, δ) = (ν₀, ν', i, 0)` for restricting `Ind_{ν,ν'}` to
`R(ν₀ + ν') ⊗ R(i)`, `ν = ν₀ + i`. -/
abbrev firstQuad : MackeyQuad (ν₀ + ν') (Si i) (ν₀ + Si i) ν' where
  α := ν₀
  β := ν'
  γ := Si i
  δ := 0
  h₁ := rfl
  h₂ := add_zero _
  h₃ := rfl
  h₄ := add_zero _

variable {ν₀ ν' i}

theorem quadTop_firstQuad (t : TensorKLR Q ν₀ ν') :
    quadTop (firstQuad ν₀ ν' i) (t ⊗ₜ 1) = concat Q ν₀ ν' t ⊗ₜ 1 := by
  rw [Algebra.TensorProduct.one_def (A := KLRAlgebra k Q (Si i))]
  change TensorProduct.map _ _ _ = _
  rw [TensorProduct.map_tmul]
  change castAlg Q (rfl : ν₀ + ν' = ν₀ + ν') (concat Q ν₀ ν' t) ⊗ₜ castAlg Q (add_zero (Si i))
    (concat Q (Si i) 0 ((1 : KLRAlgebra k Q (Si i)) ⊗ₜ (1 : KLRAlgebra k Q 0))) = _
  rw [castAlg_eq_castKLR, castAlg_eq_castKLR, castKLR_rfl, concat_one_right]

theorem quadBot_firstQuad (t : TensorKLR Q ν₀ ν') :
    quadBot (firstQuad ν₀ ν' i) (t ⊗ₜ 1) = tensorAppendL Q ν₀ ν' i t := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [TensorProduct.add_tmul, map_add, map_add, hs, ht]
  | tmul a b =>
    rw [Algebra.TensorProduct.one_def (A := KLRAlgebra k Q (Si i)), quadBot_tmul,
      tensorAppendL_tmul, appendR_apply]
    change castAlg Q rfl _ ⊗ₜ castAlg Q (add_zero _) (concat Q ν' 0 (b ⊗ₜ 1)) = _
    rw [castAlg_eq_castKLR, castAlg_eq_castKLR, castKLR_rfl, concat_one_right]

variable (Q ν₀ ν' i) in
/-- The crossing `ψ_d` of the first-factor Mackey datum. -/
noncomputable def firstψ : KLRAlgebra k Q (ν₀ + ν' + Si i) :=
  ψw (canWord (Multiset.card (ν₀ + ν' + Si i))
    (quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i)))

/-- The intertwining property of `ψ_d` for the first factor. -/
theorem appendR_mul_concat_mul_firstψ (r : KLRAlgebra k Q (ν₀ + ν')) (t : TensorKLR Q ν₀ ν') :
    appendR Q _ i (r * concat Q ν₀ ν' t) * firstψ Q ν₀ ν' i =
      appendR Q _ i r * quadDefect (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) (t ⊗ₜ 1) +
        appendR Q _ i r * firstψ Q ν₀ ν' i *
          botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i t) := by
  rw [quadDefect_apply, quadTop_firstQuad, quadBot_firstQuad, map_mul, ← appendR_apply]
  unfold firstψ
  rw [mul_sub, ← mul_assoc, ← mul_assoc, sub_add_cancel]

end FirstQuad

/-! ### The lower Mackey step vanishes -/

section Vanishing

variable {ν₀ ν' : Multiset I} {i : I}

/-- `1_{ν₀ + ν', i} 1_{ν, ν'} = 0` when `i ∉ ν' ≠ 0`. -/
theorem oneConcat_mul_botOne_firstQuad (hi : i ∉ ν') (hν : 1 ≤ Multiset.card ν') :
    oneConcat Q (ν₀ + ν') (Si i) * botOne Q (firstQuad_h ν₀ ν' i) = 0 := by
  rw [oneConcat, botOne, eSum_mul_eSum, show concatSet (ν₀ + ν') (Si i) ∩
    botSet (firstQuad_h ν₀ ν' i) = ∅ from Finset.eq_empty_of_forall_notMem fun s hs => ?_,
    eSum_empty]
  rw [Finset.mem_inter] at hs
  obtain ⟨h1, h2⟩ := hs
  rw [mem_concatSet_singleton_iff] at h1
  simp only [botSet, Finset.mem_image, mem_concatSet] at h2
  obtain ⟨_, ⟨s₃, s₄, rfl⟩, rfl⟩ := h2
  rw [seqCast_apply, Seq.append_apply_ge _ _ _ (by simp; omega)] at h1
  exact hi (h1 ▸ Seq.mem _ _)

/-- The Mackey step with fewer than `|ν'|` crossings vanishes when `i ∉ ν'`. -/
theorem eq_zero_of_mem_filt (hi : i ∉ ν') {c : ℕ} (hc : c + 1 ≤ Multiset.card ν')
    {w : KLRAlgebra k Q (ν₀ + ν' + Si i)}
    (hw : w ∈ mackeyBimodFilt Q (firstQuad_h ν₀ ν' i) c) : w = 0 := by
  rw [mackeyBimodFilt_eq_span_crossings (firstQuad_h ν₀ ν' i) (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)] at hw
  induction hw using Submodule.span_induction with
  | zero => rfl
  | add w w' _ _ hw hw' => rw [hw, hw', add_zero]
  | smul c w _ hw => rw [hw, smul_zero]
  | mem w hw =>
    obtain ⟨d, t₁, t', hd, hdc, rfl⟩ := hw
    have h1 : d = 1 := IsDoubleShuffle.eq_one_of_crossCount_lt (Seq.card_add' _ _)
      (by simp) (card_add_bot (firstQuad_h ν₀ ν' i)) hd (by omega)
    subst h1
    rw [canWord_one, ψw_nil, mul_one, ← concat_mul_oneConcat, ← botOne_mul_botConcat, mul_assoc,
      ← mul_assoc (oneConcat Q _ _), oneConcat_mul_botOne_firstQuad hi (by omega), zero_mul,
      mul_zero]

/-- **The lower Mackey step vanishes when `i ∉ ν'`.** -/
theorem eq_zero_of_mem_mackeyLower (hi : i ∉ ν') {D : KLRAlgebra k Q (ν₀ + ν' + Si i)}
    (hD : D ∈ mackeyLower k Q (ν₀ + ν' + Si i) (Multiset.card (ν₀ + ν'))
      (Multiset.card (ν₀ + Si i)) (Multiset.card ν')) :
    oneConcat Q (ν₀ + ν') (Si i) * D * botOne Q (firstQuad_h ν₀ ν' i) = 0 := by
  rcases hν : Multiset.card ν' with _ | c
  · rw [hν] at hD
    rw [(Submodule.mem_bot k).1 hD, mul_zero, zero_mul]
  · rw [hν] at hD
    refine eq_zero_of_mem_filt hi (c := c) (by omega) ?_
    rw [← mackeyLowerBimod_succ]
    refine ⟨(mem_bimod _).2 ?_, ?_⟩
    · simp only [← mul_assoc, oneConcat_idem.eq]
      rw [mul_assoc _ (botOne Q _), (botOne_idem _).eq]
    · have h1 := mackeyLower_concat_mul 1 hD
      have h2 := mackeyLower_mul_botConcat (firstQuad_h ν₀ ν' i) 1 h1
      rw [concat_one, botConcat_one] at h2
      exact h2

end Vanishing

/-! ### The map `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N` -/

section FirstMap

variable (Q) (ν₀ ν' : Multiset I) (i : I)

/-- `tensorAppendL` as a nonunital ring map. -/
noncomputable abbrev tensorAppendLHom' :
    TensorKLR Q ν₀ ν' →ₙ+* TensorKLR Q (ν₀ + Si i) ν' :=
  NonUnitalRingHomClass.toNonUnitalRingHom (tensorAppendL Q ν₀ ν' i)

/-- **`₁N = (1_{ν₀,i} ⊗ 1) N`**, an `R(ν₀) ⊗ R(ν')`-module through `tensorAppendL`. -/
abbrev ResFirst (N : Type*) [AddCommGroup N] [Module (TensorKLR Q (ν₀ + Si i) ν') N] : Type _ :=
  InductionAlong.Res (tensorAppendLHom' Q ν₀ ν' i) N

variable {Q ν₀ ν' i}
variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]

noncomputable instance : Module k (ResFirst Q ν₀ ν' i N) :=
  Module.compHom _ (algebraMap k (TensorKLR Q ν₀ ν'))

instance : IsScalarTower k (TensorKLR Q ν₀ ν') (ResFirst Q ν₀ ν' i N) where
  smul_assoc c t n := by
    change (c • t) • n = (algebraMap k (TensorKLR Q ν₀ ν') c) • (t • n)
    rw [Algebra.smul_def, mul_smul]

theorem ResFirst.val_smul_k (c : k) (n : ResFirst Q ν₀ ν' i N) : (c • n).val = c • n.val := by
  change tensorAppendL Q ν₀ ν' i (algebraMap k _ c) • n.val = c • n.val
  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc]
  exact congrArg (c • ·) n.prop

variable (Q ν₀ ν' i) in
/-- `z ↦ z 1_{ν,ν'}`, `R(ν₀ + ν' + i) → R(ν + ν') 1_{ν,ν'}`, reassociating. -/
noncomputable def firstElt :
    KLRAlgebra k Q (ν₀ + ν' + Si i) →ₗ[k] IndBimod Q (ν₀ + Si i) ν' where
  toFun z := ⟨castKLR Q (firstQuad_h ν₀ ν' i).symm z * oneConcat Q _ _, by
    rw [Graded.mem_leftIdeal, mul_assoc, oneConcat_idem.eq]⟩
  map_add' z z' := Subtype.ext (by simp [add_mul])
  map_smul' c z := Subtype.ext (by simp)

theorem coe_firstElt (z : KLRAlgebra k Q (ν₀ + ν' + Si i)) :
    (firstElt Q ν₀ ν' i z : KLRAlgebra k Q (ν₀ + Si i + ν')) =
      castKLR Q (firstQuad_h ν₀ ν' i).symm z * oneConcat Q _ _ := rfl

theorem castKLR_botConcat_firstQuad_h (t : TensorKLR Q (ν₀ + Si i) ν') :
    castKLR Q (firstQuad_h ν₀ ν' i).symm (botConcat Q (firstQuad_h ν₀ ν' i) t) =
      concat Q (ν₀ + Si i) ν' t := by
  rw [botConcat_apply, castAlg_eq_castKLR]
  exact castKLR_castAlg_symm _ _

theorem castKLR_botOne_firstQuad_h :
    castKLR Q (firstQuad_h ν₀ ν' i).symm (botOne Q (firstQuad_h ν₀ ν' i)) =
      oneConcat Q (ν₀ + Si i) ν' := by
  rw [← botConcat_one, castKLR_botConcat_firstQuad_h, concat_one]

theorem firstElt_mul_botConcat (Y : KLRAlgebra k Q (ν₀ + ν' + Si i))
    (T : TensorKLR Q (ν₀ + Si i) ν') :
    firstElt Q ν₀ ν' i (Y * botConcat Q (firstQuad_h ν₀ ν' i) T) =
      op T • firstElt Q ν₀ ν' i Y := Subtype.ext (by
  rw [coe_op_smul, unop_op, coe_firstElt, coe_firstElt, map_mul, castKLR_botConcat_firstQuad_h,
    mul_assoc, concat_mul_oneConcat, mul_assoc, oneConcat_mul_concat])

/-- `Ψ` kills the lower Mackey step when `i ∉ ν'`. -/
theorem firstElt_appendR_mul_eq_zero (hi : i ∉ ν') (x : KLRAlgebra k Q (ν₀ + ν'))
    {D : KLRAlgebra k Q (ν₀ + ν' + Si i)}
    (hD : D ∈ mackeyLower k Q (ν₀ + ν' + Si i) (Multiset.card (ν₀ + ν'))
      (Multiset.card (ν₀ + Si i)) (Multiset.card ν')) :
    firstElt Q ν₀ ν' i (appendR Q _ i x * D) = 0 := by
  have hy : appendR Q (ν₀ + ν') i x = appendR Q _ i x * oneConcat Q (ν₀ + ν') (Si i) := by
    rw [← appendR_one, ← map_mul, mul_one]
  have h0 : appendR Q _ i x * D * botOne Q (firstQuad_h ν₀ ν' i) = 0 := by
    rw [hy, mul_assoc, mul_assoc, ← mul_assoc (oneConcat Q _ _),
      eq_zero_of_mem_mackeyLower hi hD, mul_zero]
  apply Subtype.ext
  rw [Submodule.coe_zero, coe_firstElt, ← castKLR_botOne_firstQuad_h, ← map_mul, h0, map_zero]

variable (Q ν₀ ν' i) in
/-- The bimodule part of `Ψ`: `r ↦ ι(r ⊗ 1_i) ψ_d 1_{ν,ν'}`. -/
noncomputable def firstBimod : IndBimod Q ν₀ ν' →ₗ[k] IndBimod Q (ν₀ + Si i) ν' where
  toFun r := firstElt Q ν₀ ν' i
    (appendR Q _ i (r : KLRAlgebra k Q (ν₀ + ν')) * firstψ Q ν₀ ν' i)
  map_add' r r' := by rw [Submodule.coe_add, map_add, add_mul, map_add]
  map_smul' c r := by
    change firstElt Q ν₀ ν' i (appendR Q _ i (c • (r : KLRAlgebra k Q (ν₀ + ν'))) *
      firstψ Q ν₀ ν' i) = c • _
    rw [map_smul, smul_mul_assoc, map_smul]

theorem firstBimod_apply (r : IndBimod Q ν₀ ν') :
    firstBimod Q ν₀ ν' i r = firstElt Q ν₀ ν' i
      (appendR Q _ i (r : KLRAlgebra k Q (ν₀ + ν')) * firstψ Q ν₀ ν' i) := rfl

/-- `Ψ` on the bimodule is balanced when `i ∉ ν'`. -/
theorem firstBimod_op_smul (hi : i ∉ ν') (r : IndBimod Q ν₀ ν') (t : TensorKLR Q ν₀ ν') :
    firstBimod Q ν₀ ν' i (op t • r) = op (tensorAppendL Q ν₀ ν' i t) • firstBimod Q ν₀ ν' i r := by
  rw [firstBimod_apply, coe_op_smul, unop_op, appendR_mul_concat_mul_firstψ, map_add,
    firstElt_mul_botConcat, firstElt_appendR_mul_eq_zero hi _
      (quad_intertwine (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) _), zero_add, ← firstBimod_apply]

/-- The bilinear map `(r, n) ↦ ι(r ⊗ 1_i) ψ_d ⊗ n`. -/
noncomputable def firstBil :
    IndBimod Q ν₀ ν' →ₗ[k] ResFirst Q ν₀ ν' i N →ₗ[k] Ind Q (ν₀ + Si i) ν' N :=
  LinearMap.mk₂ k (fun r n => BalancedTensor.tmul (firstBimod Q ν₀ ν' i r) n.val)
    (fun r r' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c r n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun r n n' => by rw [InductionAlong.Res.val_add, BalancedTensor.tmul_add])
    (fun c r n => by rw [ResFirst.val_smul_k, BalancedTensor.tmul_smul])

variable (N) in
/-- **The map `Ψ : Ind_{ν₀,ν'} ₁N → Ind_{ν,ν'} N`**, `r ⊗ n ↦ ι(r ⊗ 1_i) ψ_d ⊗ n`, for
`i ∉ ν'`. -/
noncomputable def indFirst (hi : i ∉ ν') :
    Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N) →ₗ[k] Ind Q (ν₀ + Si i) ν' N :=
  BalancedTensor.lift firstBil (fun r t n => by
    change BalancedTensor.tmul (firstBimod Q ν₀ ν' i (op t • r)) n.val =
      BalancedTensor.tmul (firstBimod Q ν₀ ν' i r) (tensorAppendL Q ν₀ ν' i t • n.val)
    rw [firstBimod_op_smul hi, BalancedTensor.op_smul_tmul])

theorem indFirst_tmul (hi : i ∉ ν') (r : IndBimod Q ν₀ ν') (n : ResFirst Q ν₀ ν' i N) :
    indFirst N hi (BalancedTensor.tmul r n) =
      BalancedTensor.tmul (firstBimod Q ν₀ ν' i r) n.val := rfl

end FirstMap

/-! ### Reduced words adapted to the last strand of the first factor -/

section FirstWords

variable (ν₀ ν' : Multiset I) (i : I)

omit [DecidableEq I] in
theorem firstHm : Multiset.card (ν₀ + ν') + 1 = Multiset.card (ν₀ + Si i + ν') := by
  simp only [Multiset.card_add, Multiset.card_singleton]; omega

omit [DecidableEq I] in
theorem exists_firstPerm :
    ∃ d, IsDoubleShuffle (firstHm ν₀ ν' i) (Seq.card_add' (ν₀ + Si i) ν') d ∧
      crossCount (Multiset.card (ν₀ + ν')) (Multiset.card (ν₀ + Si i)) d =
        Multiset.card ν' := by
  refine (exists_isDoubleShuffle_iff _ _ _).2 ?_
  simp only [Multiset.card_add, Multiset.card_singleton]
  omega

/-- The minimal double coset representative `d` moving the last strand of `ν = ν₀ + i` across
`ν'`. -/
noncomputable def firstPerm : Perm (Fin (Multiset.card (ν₀ + Si i + ν'))) :=
  Classical.choose (exists_firstPerm ν₀ ν' i)

omit [DecidableEq I] in
theorem firstPerm_spec :
    IsDoubleShuffle (firstHm ν₀ ν' i) (Seq.card_add' (ν₀ + Si i) ν') (firstPerm ν₀ ν' i) ∧
      crossCount (Multiset.card (ν₀ + ν')) (Multiset.card (ν₀ + Si i)) (firstPerm ν₀ ν' i) =
        Multiset.card ν' :=
  Classical.choose_spec (exists_firstPerm ν₀ ν' i)

/-- The position of the strand coloured `i` at the end of the first block `ν₀ + i`. -/
abbrev firstPos : Fin (Multiset.card (ν₀ + Si i + ν')) :=
  ⟨Multiset.card ν₀, by simp only [Multiset.card_add, Multiset.card_singleton]; omega⟩

/-- The shuffles `d⁻¹ (v ⊕ 1)` whose last strand comes from the first block. -/
noncomputable def firstTop (v : Shuffle (Seq.card_add' ν₀ ν')) :
    Shuffle (Seq.card_add' (ν₀ + Si i) ν') :=
  topShuffle (Seq.card_add' (ν₀ + Si i) ν') (firstHm ν₀ ν' i) (Seq.card_add' ν₀ ν')
    (firstPerm_spec ν₀ ν' i).1 (firstPerm_spec ν₀ ν' i).2 v

omit [DecidableEq I] in
theorem firstTop_last (v : Shuffle (Seq.card_add' ν₀ ν')) :
    (firstTop ν₀ ν' i v).1 (lastPos (firstHm ν₀ ν' i)) =
      firstPos ν₀ ν' i :=
  topShuffle_last _ _ _ (firstPerm_spec ν₀ ν' i).1 (firstPerm_spec ν₀ ν' i).2 v

omit [DecidableEq I] in
theorem firstTop_injective : Function.Injective (firstTop ν₀ ν' i) :=
  topShuffle_injective _ _ _ (firstPerm_spec ν₀ ν' i).1 (firstPerm_spec ν₀ ν' i).2

omit [DecidableEq I] in
theorem exists_firstTop_eq {u : Shuffle (Seq.card_add' (ν₀ + Si i) ν')}
    (hu : u.1 (lastPos (firstHm ν₀ ν' i)) =
      firstPos ν₀ ν' i) :
    ∃ v, firstTop ν₀ ν' i v = u :=
  exists_topShuffle_eq _ _ _ (firstPerm_spec ν₀ ν' i).1 (firstPerm_spec ν₀ ν' i).2 hu

/-- The reduced words adapted to the last strand of the first factor: `(canWord d)ʳᵉᵛ ++
canWord v` at `d⁻¹ (v ⊕ 1)`, the canonical word elsewhere. -/
noncomputable def firstWord (u : Shuffle (Seq.card_add' (ν₀ + Si i) ν')) : List ℕ :=
  if hu : u.1 (lastPos (firstHm ν₀ ν' i)) =
      firstPos ν₀ ν' i then
    (canWord _ (firstPerm ν₀ ν' i)).reverse ++
      canWord _ (Classical.choose (exists_firstTop_eq ν₀ ν' i hu)).1
  else shufWord u

omit [DecidableEq I] in
theorem firstWord_top (v : Shuffle (Seq.card_add' ν₀ ν')) :
    firstWord ν₀ ν' i (firstTop ν₀ ν' i v) =
      (canWord _ (firstPerm ν₀ ν' i)).reverse ++ canWord _ v.1 := by
  have hu := firstTop_last ν₀ ν' i v
  simp only [firstWord, hu, ↓reduceDIte]
  rw [firstTop_injective ν₀ ν' i (Classical.choose_spec (exists_firstTop_eq ν₀ ν' i hu))]

omit [DecidableEq I] in
theorem firstWord_spec (u : Shuffle (Seq.card_add' (ν₀ + Si i) ν')) :
    IsReduced (Multiset.card (ν₀ + Si i + ν')) (firstWord ν₀ ν' i u) ∧
      wordProd (Multiset.card (ν₀ + Si i + ν')) (firstWord ν₀ ν' i u) = u.1 := by
  by_cases hu : u.1 (lastPos (firstHm ν₀ ν' i)) =
      firstPos ν₀ ν' i
  · obtain ⟨v, rfl⟩ := exists_firstTop_eq ν₀ ν' i hu
    rw [firstWord_top]
    exact ⟨isReduced_topWord (firstHm ν₀ ν' i) (firstPerm_spec ν₀ ν' i).1.1 v.1,
      wordProd_topWord (firstHm ν₀ ν' i) _ _⟩
  · simp only [firstWord, hu, ↓reduceDIte]
    exact shufWord_spec u

omit [DecidableEq I] in
/-- The Mackey crossing `ψ_d` of the first factor is `ψ` of the canonical word of `firstPerm`. -/
theorem canWord_quadPerm_firstQuad :
    canWord _ (quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i)) =
      canWord _ (firstPerm ν₀ ν' i) := by
  refine canWord_congr (by simp only [Multiset.card_add]; omega) _ _ fun p => ?_
  rw [quadPerm_val, dval (Seq.card_add' (ν₀ + Si i) ν') (firstHm ν₀ ν' i)
    (Seq.card_add' ν₀ ν') (firstPerm_spec ν₀ ν' i).1 (firstPerm_spec ν₀ ν' i).2]
  have hp := p.isLt
  simp only [Multiset.card_add, Multiset.card_singleton, Fin.val_cast]
    at hp ⊢
  split_ifs <;> omega

end FirstWords

/-! ### `Ψ` on the shuffle basis -/

section ShuffleBasis

variable {ν₀ ν' : Multiset I} {i : I}

/-- The intertwining property of `ψ_d` on the idempotent `ι(1_{ν₀,ν'} ⊗ 1_i)`. -/
theorem appendR_oneConcat_mul_firstψ :
    appendR Q _ i (oneConcat Q ν₀ ν') * firstψ Q ν₀ ν' i =
      firstψ Q ν₀ ν' i * botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i 1) := by
  have h := concat_quadTop_one_mul_ψD (Q := Q) (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i)
  rw [Algebra.TensorProduct.one_def (A := TensorKLR Q ν₀ ν'), quadTop_firstQuad,
    quadBot_firstQuad, concat_one, ← appendR_apply] at h
  exact h

/-- **`Ψ` on the shuffle basis, bimodule level**: `ι(ŵ_v^* ⊗ 1_i) ψ_d 1_{ν,ν'}` is
`ŵ_{d⁻¹(v ⊕ 1)}^*` times `ι(1_{ν₀,i} ⊗ 1_{ν'})`. -/
theorem firstBimod_hatWRevSub (v₀ : Shuffle (Seq.card_add' ν₀ ν')) :
    firstBimod Q ν₀ ν' i (hatWRevSub v₀) =
      op (tensorAppendL Q ν₀ ν' i 1) •
        hatWRevSubOf (firstWord ν₀ ν' i) (firstTop ν₀ ν' i v₀) := by
  have hα : ValidWord (Multiset.card (ν₀ + ν')) (shufWord v₀).reverse := by
    rw [validWord_reverse]
    exact validWord_canWord _ _
  have hE := appendR_oneConcat_mul_firstψ (Q := Q) (ν₀ := ν₀) (ν' := ν') (i := i)
  have hO : oneConcat Q (ν₀ + ν') (Si i) * (firstψ Q ν₀ ν' i *
      botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i 1)) =
      firstψ Q ν₀ ν' i * botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i 1) := by
    rw [← hE, ← mul_assoc, ← appendR_one, ← map_mul, one_mul]
  have hY : appendR Q _ i (hatWRev v₀ : KLRAlgebra k Q (ν₀ + ν')) * firstψ Q ν₀ ν' i =
      ψw (shufWord v₀).reverse * firstψ Q ν₀ ν' i *
        botConcat Q (firstQuad_h ν₀ ν' i) (tensorAppendL Q ν₀ ν' i 1) := by
    rw [hatWRev_eq, map_mul, mul_assoc, hE, appendR_ψw hα, mul_assoc, hO, mul_assoc]
  rw [firstBimod_apply, coe_hatWRevSub, hY, firstElt_mul_botConcat]
  congr 1
  apply Subtype.ext
  rw [coe_firstElt, coe_hatWRevSubOf, hatWRevOf, firstWord_top, List.reverse_append,
    List.reverse_reverse, ψw_append, map_mul, castKLR_ψw', firstψ, castKLR_ψw',
    canWord_quadPerm_firstQuad]
  rfl

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]

/-- **`Ψ` on the shuffle basis**: `Ψ(ŵ_v^* ⊗ n) = ŵ_{d⁻¹(v ⊕ 1)}^* ⊗ n`. -/
theorem indFirst_tmul_hatWRevSub (hi : i ∉ ν') (v₀ : Shuffle (Seq.card_add' ν₀ ν'))
    (n : ResFirst Q ν₀ ν' i N) :
    indFirst N hi (BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v₀) n) =
      BalancedTensor.tmul (hatWRevSubOf (firstWord ν₀ ν' i) (firstTop ν₀ ν' i v₀)) n.val := by
  rw [indFirst_tmul, firstBimod_hatWRevSub, BalancedTensor.op_smul_tmul]
  exact congrArg (BalancedTensor.tmul _) n.prop

end ShuffleBasis

/-! ### Coordinates of `E(Ind_{ν,ν'} N)` -/

section Coordinates

variable {ν₀ ν' : Multiset I} {i : I}

variable (Q ν₀ ν' i) in
/-- The idempotent `1_{-,i} = ι(1_{ν₀+ν'} ⊗ 1_i)` of `R(ν + ν')`, `ν = ν₀ + i`. -/
noncomputable def firstIdem : KLRAlgebra k Q (ν₀ + Si i + ν') :=
  castKLR Q (firstQuad_h ν₀ ν' i).symm (oneConcat Q (ν₀ + ν') (Si i))

theorem firstIdem_eq :
    firstIdem Q ν₀ ν' i = ∑ s ∈ concatSet (ν₀ + ν') (Si i),
      (e (Seq.cast (firstQuad_h ν₀ ν' i).symm s) : KLRAlgebra k Q (ν₀ + Si i + ν')) := by
  rw [firstIdem, oneConcat, eSum, map_sum]
  exact Finset.sum_congr rfl fun s _ => castKLR_e _ s

theorem firstIdem_mul_firstBimod (r : IndBimod Q ν₀ ν') :
    firstIdem Q ν₀ ν' i * (firstBimod Q ν₀ ν' i r : KLRAlgebra k Q (ν₀ + Si i + ν')) =
      (firstBimod Q ν₀ ν' i r : KLRAlgebra k Q (ν₀ + Si i + ν')) := by
  rw [firstBimod_apply, coe_firstElt, firstIdem, ← mul_assoc, ← map_mul, ← appendR_one,
    ← mul_assoc, ← map_mul, one_mul]

theorem cast_last_of_mem_first {s : Seq (ν₀ + ν' + Si i)} (hs : s ∈ concatSet (ν₀ + ν') (Si i))
    (p : Fin (Multiset.card (ν₀ + Si i + ν'))) (hp : p.val = Multiset.card (ν₀ + ν')) :
    (Seq.cast (firstQuad_h ν₀ ν' i).symm s).1 p = i := by
  rw [Seq.cast_apply]
  exact (Seq.apply_congr _ (by simp [hp])).trans (mem_concatSet_singleton_iff.1 hs)

/-- A shuffle not sending the last strand of `ν` to the end places the strand coloured `i` in
the second block. -/
theorem concatIdem_smul_cast_eq_zero_first (hi : i ∉ ν')
    (u : Shuffle (Seq.card_add' (ν₀ + Si i) ν'))
    (hu : u.1 (lastPos (firstHm ν₀ ν' i)) ≠ firstPos ν₀ ν' i)
    {s : Seq (ν₀ + ν' + Si i)} (hs : s ∈ concatSet (ν₀ + ν') (Si i)) :
    concatIdem (Q := Q) (u.1 • Seq.cast (firstQuad_h ν₀ ν' i).symm s) = 0 := by
  refine concatIdem_of_not_mem fun hm => hi ?_
  obtain ⟨a, b, hab⟩ := mem_concatSet.1 hm
  have hne : (u.1 (lastPos (firstHm ν₀ ν' i))).val ≠ Multiset.card ν₀ := fun h => hu (Fin.ext h)
  have hpν : Multiset.card (ν₀ + Si i) ≤ (u.1 (lastPos (firstHm ν₀ ν' i))).val := by
    rcases IsShuffle.val_last (Seq.card_add' (ν₀ + Si i) ν') (firstHm ν₀ ν' i) u.2 with h | h
    · simp only [Multiset.card_add, Multiset.card_singleton] at h hne; omega
    · simp only [Multiset.card_add, Multiset.card_singleton] at h hne ⊢; omega
  have hlbl : (u.1 • Seq.cast (firstQuad_h ν₀ ν' i).symm s).1
      (u.1 (lastPos (firstHm ν₀ ν' i))) = i := by
    rw [Seq.smul_apply, Equiv.symm_apply_apply]
    exact cast_last_of_mem_first hs _ (by simp)
  rw [← hab, Seq.append_apply_ge _ _ _ hpν] at hlbl
  exact hlbl ▸ b.mem _

variable {N : Type*} [AddCommGroup N] [Module k N]
  [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
  [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]

/-- **`Ψ` lands in `E(Ind_{ν,ν'} N)`.** -/
theorem firstIdem_smul_indFirst (hi : i ∉ ν') (x : Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N)) :
    firstIdem Q ν₀ ν' i • indFirst N hi x = indFirst N hi x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul r n =>
    rw [indFirst_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (firstIdem_mul_firstBimod r)
  | add x x' hx hx' => rw [map_add, smul_add, hx, hx']

variable (hsym : KLRSymm Q)

/-- The shuffle coordinates adapted to the last strand of the first factor. -/
noncomputable abbrev firstDecomp :
    Ind Q (ν₀ + Si i) ν' N ≃ₗ[k] (Shuffle (Seq.card_add' (ν₀ + Si i) ν') → N) :=
  indDecompOf (firstWord ν₀ ν' i) hsym (firstWord_spec ν₀ ν' i) N

theorem firstDecomp_firstIdem_smul (y : Ind Q (ν₀ + Si i) ν' N)
    (u : Shuffle (Seq.card_add' (ν₀ + Si i) ν')) :
    firstDecomp hsym (firstIdem Q ν₀ ν' i • y) u =
      ∑ s ∈ concatSet (ν₀ + ν') (Si i),
        concatIdem (Q := Q) (u.1 • Seq.cast (firstQuad_h ν₀ ν' i).symm s) •
          firstDecomp hsym y u := by
  rw [firstIdem_eq, Finset.sum_smul, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun s _ => indDecompOf_e_smul _ hsym _ N _ y u

/-- At a shuffle `d⁻¹ (v ⊕ 1)`, the coordinates of `E(Ind_{ν,ν'} N)` lie in `₁N`. -/
theorem tensorAppendL_smul_firstDecomp_top {y : Ind Q (ν₀ + Si i) ν' N}
    (hy : firstIdem Q ν₀ ν' i • y = y) (v : Shuffle (Seq.card_add' ν₀ ν')) :
    tensorAppendL Q ν₀ ν' i 1 • firstDecomp hsym y (firstTop ν₀ ν' i v) =
      firstDecomp hsym y (firstTop ν₀ ν' i v) := by
  have h := firstDecomp_firstIdem_smul hsym y (firstTop ν₀ ν' i v)
  rw [hy] at h
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [smul_smul, tensorAppendL_one_mul_concatIdem]
  rw [Seq.smul_apply]
  have hl : (firstTop ν₀ ν' i v).1.symm (firstPos ν₀ ν' i) =
      lastPos (firstHm ν₀ ν' i) := by
    rw [Equiv.symm_apply_eq]
    exact (firstTop_last ν₀ ν' i v).symm
  rw [hl]
  exact cast_last_of_mem_first hs _ (by simp)

include hsym in
/-- **`E(Ind_{ν,ν'} N)` is the image of `Ψ` when `i ∉ ν'`.** -/
theorem mem_range_indFirst (hi : i ∉ ν') {y : Ind Q (ν₀ + Si i) ν' N}
    (hy : firstIdem Q ν₀ ν' i • y = y) :
    y ∈ LinearMap.range (indFirst (Q := Q) (ν₀ := ν₀) (ν' := ν') (i := i) N hi) := by
  have hzero : ∀ u : Shuffle (Seq.card_add' (ν₀ + Si i) ν'),
      u.1 (lastPos (firstHm ν₀ ν' i)) ≠ firstPos ν₀ ν' i →
        firstDecomp hsym y u = 0 := fun u hu => by
    rw [← hy, firstDecomp_firstIdem_smul]
    exact Finset.sum_eq_zero fun s hs => by
      rw [concatIdem_smul_cast_eq_zero_first hi u hu hs, zero_smul]
  refine ⟨∑ v, BalancedTensor.tmul (hatWRevSub (k := k) (Q := Q) v)
    (InductionAlong.Res.mk (firstDecomp hsym y (firstTop ν₀ ν' i v))
      (tensorAppendL_smul_firstDecomp_top hsym hy v)), ?_⟩
  rw [map_sum]
  simp_rw [indFirst_tmul_hatWRevSub]
  conv_rhs => rw [← (firstDecomp hsym).symm_apply_apply y, indDecompOf_symm_apply]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map
    ⟨_, firstTop_injective ν₀ ν' i⟩)) (fun u _ hu => ?_), Finset.sum_map]
  · rfl
  · have hne : u.1 (lastPos (firstHm ν₀ ν' i)) ≠ firstPos ν₀ ν' i := fun he => hu (by
      obtain ⟨v, rfl⟩ := exists_firstTop_eq ν₀ ν' i he
      exact Finset.mem_map_of_mem _ (Finset.mem_univ v))
    rw [hzero u hne, BalancedTensor.tmul_zero]

include hsym in
/-- **`Ψ` is injective.** -/
theorem indFirst_injective (hi : i ∉ ν') :
    Function.Injective (indFirst (Q := Q) (ν₀ := ν₀) (ν' := ν') (i := i) N hi) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set g := indDecomp hsym (ResFirst Q ν₀ ν' i N) x with hg
  have hxg : x = (indDecomp hsym (ResFirst Q ν₀ ν' i N)).symm g :=
    ((indDecomp hsym _).symm_apply_apply x).symm
  rw [indDecomp_symm_apply] at hxg
  rw [hxg, map_sum] at hx
  simp_rw [indFirst_tmul_hatWRevSub] at hx
  suffices g = 0 by rw [hxg, this]; simp
  funext w
  apply InductionAlong.Res.ext
  have h := congrArg (fun y => firstDecomp hsym y (firstTop ν₀ ν' i w)) hx
  simp only [map_sum, Finset.sum_apply, map_zero, Pi.zero_apply] at h
  rw [Finset.sum_eq_single w] at h
  · rw [indDecompOf_tmul_hatWRevSubOf, Pi.single_eq_same] at h
    exact h
  · intro w' _ hw'
    rw [indDecompOf_tmul_hatWRevSubOf]
    exact Pi.single_eq_of_ne (fun he => hw' (firstTop_injective ν₀ ν' i he).symm) _
  · simp

end Coordinates

end KLRAlgebra

end Categorification.KLR
