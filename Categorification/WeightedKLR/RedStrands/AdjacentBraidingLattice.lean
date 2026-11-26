/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingLattice

/-!
# The adjacent braiding on the integral tensor lattice, and its limit at `v = 1`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. For dominant weights `λ_1, …, λ_ℓ` with `ℓ = k + 2 + m`, the braiding `R` of the
factors `k + 1, k + 2` of `V_λ = V_{λ_1} ⊗ ⋯ ⊗ V_{λ_ℓ}` (`adjacentBraiding`) maps the integral
lattice `integralTensor` of `V_λ` into that of the exchanged product, and agrees with the flip of
those two factors (`adjacentFlip`) modulo `(v - 1)` times the lattice:

* `adjacentBraiding_mem_integralTensor`;
* `adjacentBraiding_sub_adjacentFlip_mem`.

Both follow from the two-factor statements of `BraidingLattice.lean`, since the braiding and the
flip act on the two factors only.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR LusztigF
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local instance adjacentBraidingLatticeInst1 : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1

/-! ### Transport of one factor -/

omit [Finite I] in
theorem heq_facCongr {w w' : Dom R} (h : w = w') (y : Fac w) : HEq y (facCongr h y) := by
  subst h; rfl

theorem facCongr_mem_hwIntegral {w w' : Dom R} (h : w = w') {y : Fac w}
    (hy : y ∈ hwIntegral w) : facCongr h y ∈ hwIntegral w' := by
  subst h; exact hy

omit [Finite I] in
theorem facCongr_mem_weightSpace {w w' : Dom R} (h : w = w') {μ : Y →+ ℤ} {y : Fac w}
    (hy : y ∈ weightSpace R 𝕍 (Fac w) μ) : facCongr h y ∈ weightSpace R 𝕍 (Fac w') μ := by
  subst h; exact hy

theorem congr_facCongr_mem_laurentSpan {u₁ u₂ u₁' u₂' : Dom R} (h₁ : u₁ = u₁') (h₂ : u₂ = u₂')
    {t : TensorModule 𝕂 (Fac u₁) (Fac u₂)} (ht : t ∈ laurentSpan (pureIntegralTensor u₁ u₂)) :
    TensorProduct.congr (facCongr h₁) (facCongr h₂) t ∈
      laurentSpan (pureIntegralTensor u₁' u₂') := by
  refine map_mem_laurentSpan (TensorProduct.congr (facCongr h₁) (facCongr h₂)).toLinearMap ?_ ht
  rintro _ ⟨x, y, μ₁, μ₂, hx, hxμ, hy, hyμ, rfl⟩
  exact mem_laurentSpan_of_mem ⟨_, _, μ₁, μ₂, facCongr_mem_hwIntegral h₁ hx,
    facCongr_mem_weightSpace h₁ hxμ, facCongr_mem_hwIntegral h₂ hy,
    facCongr_mem_weightSpace h₂ hyμ, rfl⟩

theorem congr_facCongr_mem_vOneSpan {u₁ u₂ u₁' u₂' : Dom R} (h₁ : u₁ = u₁') (h₂ : u₂ = u₂')
    {t : TensorModule 𝕂 (Fac u₁) (Fac u₂)} (ht : t ∈ vOneSpan (pureIntegralTensor u₁ u₂)) :
    TensorProduct.congr (facCongr h₁) (facCongr h₂) t ∈
      vOneSpan (pureIntegralTensor u₁' u₂') := by
  refine map_mem_laurentSpan (TensorProduct.congr (facCongr h₁) (facCongr h₂)).toLinearMap ?_ ht
  rintro _ ⟨s, hs, rfl⟩
  show TensorProduct.congr (facCongr h₁) (facCongr h₂) ((𝕍 - 1) • s) ∈ _
  erw [map_smul]
  exact sub_one_smul_mem_vOneSpan (congr_facCongr_mem_laurentSpan h₁ h₂ (mem_laurentSpan_of_mem hs))

/-! ### `𝒜`-spans inside the integral tensor lattice -/

omit [Finite I] in
theorem mem_of_mem_laurentSpan {V : Type*} [AddCommGroup V] [Module 𝕂 V] {n : ℕ}
    {wt : Fin n → Dom R} (N : Submodule LP (TensorSpace wt)) (f : V →ₗ[𝕂] TensorSpace wt)
    {S : Set V} (hf : ∀ s ∈ S, f s ∈ N) {t : V} (ht : t ∈ laurentSpan S) : f t ∈ N := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, s, hs, rfl⟩ := hx
    rw [map_smul, ← integralLaurentEval_T, ← tensor_laurent_smul]
    exact N.smul_mem _ (hf s hs)
  | zero => rw [map_zero]; exact N.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
  | smul c x _ hx => rw [map_zsmul]; exact N.toAddSubgroup.zsmul_mem hx c

variable {k m : ℕ}

/-! ### Families split at two adjacent factors -/

section Family

variable (wt : Fin (k + 2 + m) → Dom R)

/-- The family with prefix `a`, the two factors `x, y` at `k, k + 1`, and suffix `c`. -/
def adjacentFamily (a : ∀ i : Fin k, Fac (wt (Fin.castAdd m (Fin.castAdd 2 i))))
    (x : Fac (wt (Fin.castAdd m (Fin.natAdd k 0))))
    (y : Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))
    (c : ∀ i : Fin m, Fac (wt (Fin.natAdd (k + 2) i))) : ∀ j, Fac (wt j) :=
  Fin.addCases (motive := fun j => Fac (wt j))
    (Fin.addCases (motive := fun j => Fac (wt (Fin.castAdd m j))) a
      (Fin.cons (α := fun t : Fin 2 => Fac (wt (Fin.castAdd m (Fin.natAdd k t)))) x
        (Fin.cons (α := fun t : Fin 1 => Fac (wt (Fin.castAdd m (Fin.natAdd k t.succ)))) y
          finZeroElim))) c

omit [Finite I] in
theorem adjacentDecomp_tprod_adjacentFamily
    (a : ∀ i : Fin k, Fac (wt (Fin.castAdd m (Fin.castAdd 2 i))))
    (x : Fac (wt (Fin.castAdd m (Fin.natAdd k 0))))
    (y : Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))
    (c : ∀ i : Fin m, Fac (wt (Fin.natAdd (k + 2) i))) :
    adjacentDecomp wt (PiTensorProduct.tprod 𝕂 (adjacentFamily wt a x y c)) =
      (PiTensorProduct.tprod 𝕂 a ⊗ₜ[𝕂] (x ⊗ₜ[𝕂] y)) ⊗ₜ[𝕂] PiTensorProduct.tprod 𝕂 c := by
  rw [adjacentDecomp_tprod]
  simp only [adjacentFamily, Fin.addCases_left, Fin.addCases_right]
  rfl

theorem tprod_adjacentFamily_mem
    {a : ∀ i : Fin k, Fac (wt (Fin.castAdd m (Fin.castAdd 2 i)))}
    {x : Fac (wt (Fin.castAdd m (Fin.natAdd k 0)))}
    {y : Fac (wt (Fin.castAdd m (Fin.natAdd k 1)))}
    {c : ∀ i : Fin m, Fac (wt (Fin.natAdd (k + 2) i))}
    (ha : ∀ i, a i ∈ hwIntegral _) (hx : x ∈ hwIntegral _) (hy : y ∈ hwIntegral _)
    (hc : ∀ i, c i ∈ hwIntegral _) :
    PiTensorProduct.tprod 𝕂 (adjacentFamily wt a x y c) ∈ integralTensor wt := by
  refine Submodule.subset_span ⟨_, fun j => ?_, rfl⟩
  induction j using Fin.addCases with
  | left j =>
    induction j using Fin.addCases with
    | left i => simpa [adjacentFamily] using ha i
    | right t =>
      fin_cases t
      · simpa [adjacentFamily] using hx
      · simpa [adjacentFamily] using hy
  | right i => simpa [adjacentFamily] using hc i

/-- Insert a vector of the two middle factors between a prefix and a suffix. -/
def adjacentInsert (A : TensorSpace fun i : Fin k ↦ wt (Fin.castAdd m (Fin.castAdd 2 i)))
    (C : TensorSpace fun i : Fin m ↦ wt (Fin.natAdd (k + 2) i)) :
    (Fac (wt (Fin.castAdd m (Fin.natAdd k 0))) ⊗[𝕂] Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))
      →ₗ[𝕂] TensorSpace wt where
  toFun t := (adjacentDecomp wt).symm ((A ⊗ₜ[𝕂] t) ⊗ₜ[𝕂] C)
  map_add' s t := by rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
  map_smul' c t := by
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, RingHom.id_apply]

/-- Inserting a pure tensor of integral vectors between integral pure tensors stays in the
integral lattice. -/
theorem adjacentInsert_mem
    {a : ∀ i : Fin k, Fac (wt (Fin.castAdd m (Fin.castAdd 2 i)))}
    {c : ∀ i : Fin m, Fac (wt (Fin.natAdd (k + 2) i))}
    (ha : ∀ i, a i ∈ hwIntegral _) (hc : ∀ i, c i ∈ hwIntegral _)
    {t : TensorModule 𝕂 (Fac (wt (Fin.castAdd m (Fin.natAdd k 0))))
      (Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))}
    (ht : t ∈ laurentSpan (pureIntegralTensor _ _)) :
    adjacentInsert wt (PiTensorProduct.tprod 𝕂 a) (PiTensorProduct.tprod 𝕂 c) t ∈
      integralTensor wt := by
  refine mem_of_mem_laurentSpan _ _ ?_ ht
  rintro _ ⟨x, y, _, _, hx, _, hy, _, rfl⟩
  have h := tprod_adjacentFamily_mem wt ha hx hy hc
  rw [← LinearEquiv.symm_apply_apply (adjacentDecomp wt) (PiTensorProduct.tprod 𝕂 _),
    adjacentDecomp_tprod_adjacentFamily] at h
  exact h

/-- The `(v - 1)`-multiples of the integral tensor lattice. -/
def vOneTensor {n : ℕ} (wt : Fin n → Dom R) : Submodule LP (TensorSpace wt) :=
  (integralTensor wt).map (DistribSMul.toLinearMap LP _ (LaurentPolynomial.T 1 - 1 : LP))

theorem mem_vOneTensor_iff {n : ℕ} {wt : Fin n → Dom R} {z : TensorSpace wt} :
    z ∈ vOneTensor wt ↔ ∃ y ∈ integralTensor wt, z = (𝕍 - 1) • y := by
  have he (y : TensorSpace wt) : DistribSMul.toLinearMap LP _ (LaurentPolynomial.T 1 - 1 : LP) y =
      (𝕍 - 1) • y := by
    rw [DistribSMul.toLinearMap_apply, tensor_laurent_smul, map_sub, integralLaurentEval_T,
      map_one, zpow_one]
  simp only [vOneTensor, Submodule.mem_map, he]
  exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h.symm⟩⟩

theorem adjacentInsert_mem_vOneTensor
    {a : ∀ i : Fin k, Fac (wt (Fin.castAdd m (Fin.castAdd 2 i)))}
    {c : ∀ i : Fin m, Fac (wt (Fin.natAdd (k + 2) i))}
    (ha : ∀ i, a i ∈ hwIntegral _) (hc : ∀ i, c i ∈ hwIntegral _)
    {t : TensorModule 𝕂 (Fac (wt (Fin.castAdd m (Fin.natAdd k 0))))
      (Fac (wt (Fin.castAdd m (Fin.natAdd k 1))))}
    (ht : t ∈ vOneSpan (pureIntegralTensor _ _)) :
    adjacentInsert wt (PiTensorProduct.tprod 𝕂 a) (PiTensorProduct.tprod 𝕂 c) t ∈
      vOneTensor wt := by
  refine mem_of_mem_laurentSpan _ _ ?_ ht
  rintro _ ⟨s, hs, rfl⟩
  show adjacentInsert wt _ _ ((𝕍 - 1) • s) ∈ _
  erw [map_smul]
  exact mem_vOneTensor_iff.2 ⟨_, adjacentInsert_mem wt ha hc (mem_laurentSpan_of_mem hs), rfl⟩

end Family

/-! ### The braiding and the flip of two adjacent factors -/

variable (hR : R.IsXRegular) (wt wt' : Fin (k + 2 + m) → Dom R)
  (h₁ : ∀ i : Fin k, wt' (Fin.castAdd m (Fin.castAdd 2 i)) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
  (h₂ : wt' (Fin.castAdd m (Fin.natAdd k 0)) = wt (Fin.castAdd m (Fin.natAdd k 1)))
  (h₃ : wt' (Fin.castAdd m (Fin.natAdd k 1)) = wt (Fin.castAdd m (Fin.natAdd k 0)))
  (h₄ : ∀ i : Fin m, wt' (Fin.natAdd (k + 2) i) = wt (Fin.natAdd (k + 2) i))

/-- The flip of the factors `k` and `k + 1` of the ordered tensor product, onto the ordered
tensor product with the two weights exchanged: the limit of `adjacentBraiding` at `v = 1`. -/
def adjacentFlip : TensorSpace wt ≃ₗ[𝕂] TensorSpace wt' :=
  (adjacentDecomp wt).trans
    ((TensorProduct.congr
      (TensorProduct.congr (tensorCongr (funext h₁).symm)
        ((TensorProduct.comm 𝕂 _ _).trans
          (TensorProduct.congr (facCongr h₂.symm) (facCongr h₃.symm))))
      (tensorCongr (funext h₄).symm)).trans
    (adjacentDecomp wt').symm)

omit [Finite I] in
private theorem tensorCongr_tprod_facCongr {n : ℕ} {u u' : Fin n → Dom R} (h : ∀ j, u' j = u j)
    (z : ∀ j, Fac (u j)) :
    tensorCongr (funext h).symm (PiTensorProduct.tprod 𝕂 z) =
      PiTensorProduct.tprod 𝕂 (fun j => facCongr (h j).symm (z j)) :=
  tensorCongr_tprod _ _ _ fun _ => heq_facCongr _ _

theorem adjacentBraiding_tprod (z : ∀ j, Fac (wt j)) :
    adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ (PiTensorProduct.tprod 𝕂 z) =
      adjacentInsert wt'
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₁ i).symm (z (Fin.castAdd m (Fin.castAdd 2 i))))
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₄ i).symm (z (Fin.natAdd (k + 2) i)))
        (TensorProduct.congr (facCongr h₂.symm) (facCongr h₃.symm)
          (IrreducibleModule.braidingEquiv hR _ _ (TensorModule.mk _ _
            (z (Fin.castAdd m (Fin.natAdd k 0)) ⊗ₜ[𝕂] z (Fin.castAdd m (Fin.natAdd k 1)))))) := by
  rw [adjacentBraiding, LinearEquiv.trans_apply, LinearEquiv.trans_apply, adjacentDecomp_tprod,
    TensorProduct.congr_tmul, TensorProduct.congr_tmul, tensorCongr_tprod_facCongr h₁,
    tensorCongr_tprod_facCongr h₄]
  rfl

omit [Finite I] in
theorem adjacentFlip_tprod (z : ∀ j, Fac (wt j)) :
    adjacentFlip wt wt' h₁ h₂ h₃ h₄ (PiTensorProduct.tprod 𝕂 z) =
      adjacentInsert wt'
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₁ i).symm (z (Fin.castAdd m (Fin.castAdd 2 i))))
        (PiTensorProduct.tprod 𝕂 fun i => facCongr (h₄ i).symm (z (Fin.natAdd (k + 2) i)))
        (TensorProduct.congr (facCongr h₂.symm) (facCongr h₃.symm)
          (tensorFlip _ _ (TensorModule.mk _ _
            (z (Fin.castAdd m (Fin.natAdd k 0)) ⊗ₜ[𝕂] z (Fin.castAdd m (Fin.natAdd k 1)))))) := by
  rw [adjacentFlip, LinearEquiv.trans_apply, LinearEquiv.trans_apply, adjacentDecomp_tprod,
    TensorProduct.congr_tmul, TensorProduct.congr_tmul, tensorCongr_tprod_facCongr h₁,
    tensorCongr_tprod_facCongr h₄]
  rfl

private theorem integralTensor_induction {n : ℕ} {u : Fin n → Dom R} {W : Type*}
    [AddCommGroup W] [Module 𝕂 W] [Module LP W]
    (hW : ∀ (a : LP) (w : W), a • w = integralLaurentEval a • w)
    (N : Submodule LP W) (f : TensorSpace u →ₗ[𝕂] W)
    (hf : ∀ z : ∀ j, Fac (u j), (∀ j, z j ∈ hwIntegral (u j)) → f (PiTensorProduct.tprod 𝕂 z) ∈ N)
    {x : TensorSpace u} (hx : x ∈ integralTensor u) : f x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact hf z hz
  | zero => rw [map_zero]; exact N.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
  | smul c x _ hx =>
    rw [tensor_laurent_smul, map_smul, ← hW]
    exact N.smul_mem c hx

/-- **The adjacent braiding preserves the integral tensor lattice** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11). -/
theorem adjacentBraiding_mem_integralTensor {x : TensorSpace wt} (hx : x ∈ integralTensor wt) :
    adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ x ∈ integralTensor wt' := by
  refine integralTensor_induction (fun _ _ => rfl) _
    (adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄).toLinearMap (fun z hz => ?_) hx
  rw [LinearEquiv.coe_coe, adjacentBraiding_tprod]
  exact adjacentInsert_mem wt' (fun i => facCongr_mem_hwIntegral _ (hz _))
    (fun i => facCongr_mem_hwIntegral _ (hz _))
    (congr_facCongr_mem_laurentSpan _ _ (braidingEquiv_mem_laurentSpan hR _ _
      (tmul_mem_laurentSpan_pure hR _ _ (hz _) (hz _))))

/-- **At `v = 1` the adjacent braiding is the flip** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11): on the integral tensor lattice, `R x - flip x` is `v - 1` times a lattice vector. -/
theorem adjacentBraiding_sub_adjacentFlip_mem {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) :
    ∃ y ∈ integralTensor wt',
      adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ x - adjacentFlip wt wt' h₁ h₂ h₃ h₄ x =
        (𝕍 - 1) • y := by
  refine mem_vOneTensor_iff.1 (integralTensor_induction (fun _ _ => rfl) _
    ((adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄).toLinearMap -
      (adjacentFlip wt wt' h₁ h₂ h₃ h₄).toLinearMap) (fun z hz => ?_) hx)
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, adjacentBraiding_tprod,
    adjacentFlip_tprod, ← map_sub]
  erw [← map_sub]
  exact adjacentInsert_mem_vOneTensor wt' (fun i => facCongr_mem_hwIntegral _ (hz _))
    (fun i => facCongr_mem_hwIntegral _ (hz _))
    (congr_facCongr_mem_vOneSpan _ _ (braidingEquiv_sub_tensorFlip_mem hR _ _
      (tmul_mem_laurentSpan_pure hR _ _ (hz _) (hz _))))

end Categorification.Stendhal.FirstWeight
