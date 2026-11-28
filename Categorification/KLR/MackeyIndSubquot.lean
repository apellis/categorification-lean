/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndLayer
import Categorification.KLR.MackeyMap

/-!
# The Mackey layers of an induced module are the bimodule layers tensored with the input

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, for induced modules. Let
`h : ν'' + ν''' = ν + ν'`, let `N` be an `R(ν'') ⊗ R(ν''')`-module and
`Ind N = R(ν'' + ν''') 1_{ν'',ν'''} ⊗ N`, filtered by the Mackey filtration for the top cut at
`|ν|` (`IndMackeyLayer`). Let `F_c / F_{c-1}` be the subquotient of the Mackey filtration of
the bimodule `_{ν,ν'}R_{ν'',ν'''}` (`MackeySubquot`), a left `R(ν) ⊗ R(ν')`-module and a right
`R(ν'') ⊗ R(ν''')`-module (the instances below). Then

  `Φ : (F_c / F_{c-1}) ⊗_{R(ν'') ⊗ R(ν''')} N → F_c(Ind N) / F_{c-1}(Ind N)`,
  `[r] ⊗ x ↦ [r ⊗ x]`

is injective, with image the `1_{ν,ν'}`-part of the layer, and it commutes with the action of
`R(ν) ⊗ R(ν')` (`indSubquotMap`). Together with the decomposition of `F_c / F_{c-1}` into the
balanced tensor products of KL I, Proposition 2.18 (`mackeySubquot_isInternal`), this describes
`1_{ν,ν'}` of each layer of `Ind N` as a module over `R(ν) ⊗ R(ν')`.

Proof. A left inverse `Ψ` is defined in the coordinates of Proposition 2.16 of the layer
(`indMackeyLayerEquiv`): `Ψ(v) = ∑_u [1_{ν,ν'} ŵ_u^*] ⊗ v_u`. That `Ψ ∘ Φ = id` is the
expansion `r = ∑_u ŵ_u^* ι(t_u)`, in which the terms with `crossCount(u⁻¹) < c` lie in `F_{c-1}`
and those with `crossCount(u⁻¹) > c` vanish (`mem_mackeyFilt_iff_rightFreeEquivOf_symm`), and
`Φ ∘ Ψ` is the action of `1_{ν,ν'}`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main definitions

* The module structures on `KLRAlgebra.MackeySubquot`.
* `KLRAlgebra.indSubquotMap` (`Φ`), `KLRAlgebra.indSubquotInv` (`Ψ`),
  `KLRAlgebra.indTopAct` (the action of `R(ν) ⊗ R(ν')` on the layers of `Ind N`).

## Main results

* `KLRAlgebra.indSubquotInv_comp_indSubquotMap`, `KLRAlgebra.indSubquotMap_comp_indSubquotInv`,
  `KLRAlgebra.indSubquotMap_injective`, `KLRAlgebra.range_indSubquotMap`,
  `KLRAlgebra.indSubquotMap_smul`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

section Cast

theorem castAlg_mem_mackeyFilt {μ₁ μ₂ : Multiset I} (e : μ₁ = μ₂) {n n'' c : ℕ}
    {y : KLRAlgebra k Q μ₁} (hy : y ∈ mackeyFilt k Q μ₁ n n'' c) :
    castAlg Q e y ∈ mackeyFilt k Q μ₂ n n'' c := by
  subst e; exact hy

theorem castAlg_symm_castAlg {μ₁ μ₂ : Multiset I} (e : μ₁ = μ₂) (y : KLRAlgebra k Q μ₁) :
    castAlg Q e.symm (castAlg Q e y) = y := by
  subst e; rfl

theorem castAlg_castAlg_symm {μ₁ μ₂ : Multiset I} (e : μ₁ = μ₂) (y : KLRAlgebra k Q μ₂) :
    castAlg Q e (castAlg Q e.symm y) = y := by
  subst e; rfl

end Cast

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

section Instances

/-- The left action of `R(ν) ⊗ R(ν')` on `F_c / F_{c-1}`, as a ring map. -/
def subquotLeftHom (c : ℕ) : TensorKLR Q ν ν' →+* Module.End k (MackeySubquot Q h c) where
  toFun t := subquotLeft h c t
  map_one' := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [subquotLeft_of]
    refine subquotOf_congr h ?_ _ _
    have := (mem_bimod h).1 hr.1
    rw [concat_one, ← this, ← mul_assoc, ← mul_assoc, oneConcat_idem.eq]
  map_mul' a b := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    change subquotLeft h c (a * b) (subquotOf h r hr) =
      subquotLeft h c a (subquotLeft h c b (subquotOf h r hr))
    rw [subquotLeft_of, subquotLeft_of, subquotLeft_of]
    exact subquotOf_congr h (by rw [concat_mul, mul_assoc]) _ _
  map_zero' := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [subquotLeft_of, LinearMap.zero_apply, subquotOf_eq_zero_iff, map_zero, zero_mul]
    exact zero_mem _
  map_add' a b := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [LinearMap.add_apply, subquotLeft_of, subquotLeft_of, subquotLeft_of, ← subquotOf_add]
    exact subquotOf_congr h (by rw [map_add, add_mul]) _ _

/-- The right action of `R(ν'') ⊗ R(ν''')` on `F_c / F_{c-1}`, as a ring map. -/
def subquotRightHom (c : ℕ) :
    (TensorKLR Q ν'' ν''')ᵐᵒᵖ →+* Module.End k (MackeySubquot Q h c) where
  toFun t := subquotRight h c t.unop
  map_one' := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [unop_one, subquotRight_of]
    refine subquotOf_congr h ?_ _ _
    have := (mem_bimod h).1 hr.1
    rw [botConcat_one, ← this, mul_assoc, (botOne_idem h).eq]
  map_mul' a b := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    change subquotRight h c (a * b).unop (subquotOf h r hr) =
      subquotRight h c a.unop (subquotRight h c b.unop (subquotOf h r hr))
    rw [subquotRight_of, subquotRight_of, subquotRight_of]
    exact subquotOf_congr h (by rw [unop_mul, botConcat_mul, mul_assoc]) _ _
  map_zero' := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [unop_zero, subquotRight_of, LinearMap.zero_apply, subquotOf_eq_zero_iff, map_zero,
      mul_zero]
    exact zero_mem _
  map_add' a b := LinearMap.ext fun z => by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [LinearMap.add_apply, unop_add, subquotRight_of, subquotRight_of, subquotRight_of,
      ← subquotOf_add]
    exact subquotOf_congr h (by rw [map_add, mul_add]) _ _

instance (c : ℕ) : Module (TensorKLR Q ν ν') (MackeySubquot Q h c) :=
  Module.compHom _ (subquotLeftHom h c)

instance (c : ℕ) : Module (TensorKLR Q ν'' ν''')ᵐᵒᵖ (MackeySubquot Q h c) :=
  Module.compHom _ (subquotRightHom h c)

theorem subquot_smul_def {c : ℕ} (t : TensorKLR Q ν ν') (z : MackeySubquot Q h c) :
    t • z = subquotLeft h c t z := rfl

theorem subquot_op_smul_def {c : ℕ} (t : (TensorKLR Q ν'' ν''')ᵐᵒᵖ) (z : MackeySubquot Q h c) :
    t • z = subquotRight h c t.unop z := rfl

instance (c : ℕ) : IsScalarTower k (TensorKLR Q ν ν') (MackeySubquot Q h c) where
  smul_assoc a t z := by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [subquot_smul_def, subquot_smul_def, subquotLeft_of, subquotLeft_of, ← subquotOf_smul]
    exact subquotOf_congr h (by rw [map_smul, smul_mul_assoc]) _ _

instance (c : ℕ) :
    SMulCommClass (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''')ᵐᵒᵖ (MackeySubquot Q h c) where
  smul_comm a b z := by
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [subquot_smul_def, subquot_op_smul_def, subquot_op_smul_def, subquot_smul_def,
      subquotLeft_of, subquotRight_of, subquotRight_of, subquotLeft_of]
    exact subquotOf_congr h (mul_assoc _ _ _).symm _ _

end Instances

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

local notation "Sh" => Shuffle (Seq.card_add' ν'' ν''')
local notation "Lay" c => IndMackeyLayer Q ν'' ν''' N (Multiset.card ν) c
local notation "Stp" c => indMackeyStep Q ν'' ν''' N (Multiset.card ν) c

section Map

theorem castAlg_oneConcat_bot :
    castAlg Q h (oneConcat Q ν'' ν''') = (botOne Q h : KLRAlgebra k Q (ν + ν')) := by
  rw [← concat_one, ← botConcat_apply, botConcat_one]

/-- An element of `_{ν,ν'}R_{ν'',ν'''}`, transported to `R(ν'' + ν''') 1_{ν'',ν'''}`. -/
def bimodToInd {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ bimod Q h) : IndBimod Q ν'' ν''' :=
  ⟨castAlg Q h.symm r, by
    rw [Graded.mem_leftIdeal]
    have hr' : r * botOne Q h = r := by
      rw [← (mem_bimod h).1 hr, mul_assoc, (botOne_idem h).eq]
    calc castAlg Q h.symm r * oneConcat Q ν'' ν'''
        = castAlg Q h.symm r * castAlg Q h.symm (castAlg Q h (oneConcat Q ν'' ν''')) := by
          rw [castAlg_symm_castAlg]
      _ = castAlg Q h.symm (r * botOne Q h) := by rw [map_mul, castAlg_oneConcat_bot]
      _ = castAlg Q h.symm r := by rw [hr']⟩

theorem coe_bimodToInd {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ bimod Q h) :
    (bimodToInd h hr : KLRAlgebra k Q (ν'' + ν''')) = castAlg Q h.symm r := rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem tmul_bimodToInd_mem {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) (x : N) :
    BalancedTensor.tmul (bimodToInd h hr.1) x ∈ Stp c :=
  Submodule.subset_span ⟨_, x, castAlg_mem_mackeyFilt h.symm hr.2, rfl⟩

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem tmul_bimodToInd_mem_lower {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyLowerBimod Q h c) (x : N) :
    BalancedTensor.tmul (bimodToInd h hr.1) x ∈
      indMackeyLower Q ν'' ν''' N (Multiset.card ν) c := by
  obtain ⟨hb, hl⟩ := hr
  cases c with
  | zero =>
    have hl0 : r = 0 := (Submodule.mem_bot k).1 hl
    subst hl0
    rw [indMackeyLower, Submodule.mem_bot]
    have : bimodToInd h hb = 0 := Subtype.ext (by rw [coe_bimodToInd, map_zero]; rfl)
    rw [this, BalancedTensor.zero_tmul]
  | succ c => exact Submodule.subset_span ⟨_, x, castAlg_mem_mackeyFilt h.symm hl, rfl⟩

/-- The bilinear map `(r, x) ↦ [r ⊗ x]` on the step `F_c` of the bimodule. -/
def indSubquotPre (c : ℕ) : mackeyBimodFilt Q h c →ₗ[k] N →ₗ[k] Lay c :=
  LinearMap.mk₂ k (fun r x => Submodule.Quotient.mk
      (⟨_, tmul_bimodToInd_mem h N r.2 x⟩ : Stp c))
    (fun r r' x => by
      rw [← Submodule.Quotient.mk_add]; congr 1; apply Subtype.ext
      change BalancedTensor.tmul _ x = BalancedTensor.tmul _ x + BalancedTensor.tmul _ x
      rw [← BalancedTensor.add_tmul]; congr 1; apply Subtype.ext
      simp only [coe_bimodToInd, Submodule.coe_add, map_add])
    (fun a r x => by
      rw [← Submodule.Quotient.mk_smul]; congr 1; apply Subtype.ext
      change BalancedTensor.tmul _ x = a • BalancedTensor.tmul _ x
      rw [← BalancedTensor.smul_tmul]; congr 1; apply Subtype.ext
      change castAlg Q h.symm (a • (r : KLRAlgebra k Q (ν + ν'))) = a • castAlg Q h.symm r
      rw [map_smul])
    (fun r x x' => by
      rw [← Submodule.Quotient.mk_add]; congr 1; apply Subtype.ext
      exact BalancedTensor.tmul_add _ x x')
    (fun a r x => by
      rw [← Submodule.Quotient.mk_smul]; congr 1; apply Subtype.ext
      exact BalancedTensor.tmul_smul a _ x)

/-- The bilinear map `([r], x) ↦ [r ⊗ x]`. -/
def indSubquotBil (c : ℕ) : MackeySubquot Q h c →ₗ[k] N →ₗ[k] Lay c :=
  Submodule.liftQ _ (indSubquotPre h N c) fun r hr => LinearMap.ext fun x => by
    change Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact tmul_bimodToInd_mem_lower h N (r := (r : KLRAlgebra k Q (ν + ν'))) hr x

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indSubquotBil_of {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) (x : N) :
    indSubquotBil h N c (subquotOf h r hr) x =
      Submodule.Quotient.mk (⟨_, tmul_bimodToInd_mem h N hr x⟩ : Stp c) := rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indSubquotBil_balanced {c : ℕ} (z : MackeySubquot Q h c)
    (b : TensorKLR Q ν'' ν''') (x : N) :
    indSubquotBil h N c (op b • z) x = indSubquotBil h N c z (b • x) := by
  obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
  rw [subquot_op_smul_def, unop_op, subquotRight_of, indSubquotBil_of, indSubquotBil_of]
  congr 1; apply Subtype.ext
  change BalancedTensor.tmul _ x = BalancedTensor.tmul _ (b • x)
  rw [← BalancedTensor.op_smul_tmul]; congr 1; apply Subtype.ext
  rw [coe_bimodToInd, coe_op_smul, coe_bimodToInd, unop_op, map_mul, botConcat_apply,
    castAlg_symm_castAlg]

/-- **The map `Φ : (F_c / F_{c-1}) ⊗ N → F_c(Ind N) / F_{c-1}(Ind N)`**, `[r] ⊗ x ↦ [r ⊗ x]`. -/
def indSubquotMap (c : ℕ) :
    BalancedTensor k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N →ₗ[k]
      Lay c :=
  BalancedTensor.lift (indSubquotBil h N c) fun z b x => indSubquotBil_balanced h N z b x

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indSubquotMap_tmul {c : ℕ} (z : MackeySubquot Q h c) (x : N) :
    indSubquotMap h N c (BalancedTensor.tmul z x) = indSubquotBil h N c z x :=
  BalancedTensor.lift_tmul _ _ _ _

end Map

section TopAct

/-- The image of `ι_{ν,ν'}(t)` in `R(ν'' + ν''')` preserves the Mackey filtration. -/
theorem castAlg_concat_mul_mem (t : TensorKLR Q ν ν') (c : ℕ) (y : KLRAlgebra k Q (ν'' + ν'''))
    (hy : y ∈ mackeyFilt k Q (ν'' + ν''') (Multiset.card ν) (Multiset.card ν'') c) :
    castAlg Q h.symm (concat Q ν ν' t) * y ∈
      mackeyFilt k Q (ν'' + ν''') (Multiset.card ν) (Multiset.card ν'') c := by
  rw [← castAlg_symm_castAlg h y, ← map_mul]
  exact castAlg_mem_mackeyFilt h.symm (concat_mul_mem_mackeyFilt t (castAlg_mem_mackeyFilt h hy))

/-- **The action of `R(ν) ⊗ R(ν')` on the layers of `Ind N`.** -/
def indTopAct (c : ℕ) (t : TensorKLR Q ν ν') : (Lay c) →ₗ[k] Lay c :=
  indMackeyLayerAct N (castAlg Q h.symm (concat Q ν ν' t)) (castAlg_concat_mul_mem h t) c

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **`Φ` commutes with the action of `R(ν) ⊗ R(ν')`.** -/
theorem indSubquotMap_smul {c : ℕ} (t : TensorKLR Q ν ν')
    (w : BalancedTensor k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N) :
    indSubquotMap h N c (t • w) = indTopAct h N c t (indSubquotMap h N c w) := by
  induction w using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul z x =>
    obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
    rw [BalancedTensor.smul_tmul', indSubquotMap_tmul, indSubquotMap_tmul, subquot_smul_def,
      subquotLeft_of, indSubquotBil_of, indSubquotBil_of, indTopAct, indMackeyLayerAct_mk]
    congr 1; apply Subtype.ext
    change BalancedTensor.tmul _ x = _ • BalancedTensor.tmul _ x
    rw [BalancedTensor.smul_tmul']; congr 1; apply Subtype.ext
    rw [coe_bimodToInd, Submodule.coe_smul, smul_eq_mul, coe_bimodToInd, map_mul]
  | add w w' hw hw' => rw [smul_add, map_add, hw, hw', map_add, map_add]

end TopAct

section Inv

variable (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν'' ν''') → List ℕ}
  (hσ : ∀ u : Shuffle (Seq.card_add' ν'' ν'''), IsReduced (Multiset.card (ν'' + ν''')) (σ u) ∧
    wordProd (Multiset.card (ν'' + ν''')) (σ u) = u.1)

omit [DecidableEq I] in
include h in
theorem card_le_card_bot : Multiset.card ν ≤ Multiset.card (ν'' + ν''') := by
  rw [h, Multiset.card_add]; exact Nat.le_add_right _ _

theorem oneConcat_mul_castAlg_mem_bimod {y : KLRAlgebra k Q (ν'' + ν''')}
    (hy : y * oneConcat Q ν'' ν''' = y) :
    oneConcat Q ν ν' * castAlg Q h y ∈ bimod Q h := by
  rw [mem_bimod, ← mul_assoc, oneConcat_idem.eq, mul_assoc, ← castAlg_oneConcat_bot h, ← map_mul,
    hy]

theorem oneConcat_mul_castAlg_mem_mackeyFilt {y : KLRAlgebra k Q (ν'' + ν''')} {c : ℕ}
    (hy : y ∈ mackeyFilt k Q (ν'' + ν''') (Multiset.card ν) (Multiset.card ν'') c) :
    oneConcat Q ν ν' * castAlg Q h y ∈
      mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c := by
  rw [oneConcat]
  exact eSum_mul_mem_mackeyFilt _ (castAlg_mem_mackeyFilt h hy)

include hσ in
theorem oneConcat_mul_castAlg_hatWRevOf_mem (c : ℕ)
    (u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c) :
    oneConcat Q ν ν' * castAlg Q h (hatWRevOf σ u.1) ∈ mackeyBimodFilt Q h c := by
  have hm := hatWRevOf_mem_mackeyFilt (Q := Q) hσ (card_le_card_bot h) u.1
  rw [u.2] at hm
  exact ⟨oneConcat_mul_castAlg_mem_bimod h (hatWRevOf_mul_oneConcat σ u.1),
    oneConcat_mul_castAlg_mem_mackeyFilt h hm⟩

/-- The class `[1_{ν,ν'} ŵ_u^*] ∈ F_c / F_{c-1}` of a shuffle of the layer `c`. -/
def indSubquotGen (c : ℕ) (u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c) :
    MackeySubquot Q h c :=
  subquotOf h _ (oneConcat_mul_castAlg_hatWRevOf_mem h hσ c u)

include hsym in
/-- **The left inverse `Ψ`** of `Φ`: `v ↦ ∑_u [1_{ν,ν'} ŵ_u^*] ⊗ v_u`, in the coordinates of
the layer. -/
def indSubquotInv (c : ℕ) :
    (Lay c) →ₗ[k]
      BalancedTensor k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N :=
  (∑ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
    (BalancedTensor.mkBil k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N
      (indSubquotGen h hσ c u)).comp (LinearMap.proj u)).comp
    (indMackeyLayerEquiv N hsym hσ (card_le_card_bot h) c).toLinearMap

theorem indSubquotInv_apply {c : ℕ} (v : Lay c) :
    indSubquotInv h N hsym hσ c v = ∑ u, BalancedTensor.tmul (indSubquotGen h hσ c u)
      (indMackeyLayerEquiv N hsym hσ (card_le_card_bot h) c v u) := by
  rw [indSubquotInv, LinearMap.comp_apply, LinearMap.sum_apply]
  rfl

theorem subquotOf_sum {c : ℕ} {ι : Type*} (s : Finset ι) (f : ι → KLRAlgebra k Q (ν + ν'))
    (hf : ∀ i, f i ∈ mackeyBimodFilt Q h c) :
    ∑ i ∈ s, subquotOf h (f i) (hf i) =
      subquotOf h (∑ i ∈ s, f i) (Submodule.sum_mem _ fun i _ => hf i) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    refine Finset.sum_empty.trans ?_
    exact ((subquotOf_eq_zero_iff h _).2 (by rw [Finset.sum_empty]; exact zero_mem _)).symm
  | cons a s ha ih =>
    rw [Finset.sum_cons, ih, ← subquotOf_add]
    exact subquotOf_congr h (Finset.sum_cons ha).symm _ _

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem subquot_sum_tmul {c : ℕ} {ι : Type*} (s : Finset ι) (f : ι → MackeySubquot Q h c) (x : N) :
    ∑ i ∈ s, (BalancedTensor.tmul (f i) x : BalancedTensor k (TensorKLR Q ν ν')
      (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N) = BalancedTensor.tmul (∑ i ∈ s, f i) x := by
  have := map_sum ((BalancedTensor.mkBil k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''')
    (MackeySubquot Q h c) N).flip x) f s
  simp only [LinearMap.flip_apply, BalancedTensor.mkBil_apply] at this
  exact this.symm

include hsym hσ in
/-- The expansion `[r] = ∑_{u : crossCount(u⁻¹) = c} [1_{ν,ν'} ŵ_u^*] t_u` in `F_c / F_{c-1}`. -/
theorem subquotOf_eq_sum {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) :
    subquotOf h r hr = ∑ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      op ((rightFreeEquivOf ν'' ν''' σ hsym hσ).symm (bimodToInd h hr.1) u.1) •
        indSubquotGen h hσ c u := by
  obtain ⟨g, hg⟩ : ∃ g, g = (rightFreeEquivOf ν'' ν''' σ hsym hσ).symm (bimodToInd h hr.1) :=
    ⟨_, rfl⟩
  rw [← hg]
  obtain ⟨Y, hYdef⟩ : ∃ Y : Shuffle (Seq.card_add' ν'' ν''') → KLRAlgebra k Q (ν + ν'),
      ∀ u, Y u = oneConcat Q ν ν' * castAlg Q h (hatWRevOf σ u * concat Q ν'' ν''' (g u)) :=
    ⟨_, fun _ => rfl⟩
  have hYb : ∀ u, Y u ∈ bimod Q h := fun u => by
    rw [hYdef]
    exact oneConcat_mul_castAlg_mem_bimod h (by rw [mul_assoc, concat_mul_oneConcat])
  have hYm : ∀ u : Shuffle (Seq.card_add' ν'' ν'''),
      Y u ∈ mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'')
      (crossCount (Multiset.card ν) (Multiset.card ν'') u.1⁻¹) := fun u => by
    rw [hYdef]
    exact oneConcat_mul_castAlg_mem_mackeyFilt h
      (hatWRevOf_mul_concat_mem_mackeyFilt hσ (card_le_card_bot h) u _)
  have hY : ∀ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      Y u.1 ∈ mackeyBimodFilt Q h c := fun u => by
    have hm := hYm u.1
    rw [u.2] at hm
    exact ⟨hYb u.1, hm⟩
  have hgen : ∀ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      op (g u.1) • indSubquotGen h hσ c u = subquotOf h (Y u.1) (hY u) := fun u => by
    rw [subquot_op_smul_def, unop_op, indSubquotGen, subquotRight_of]
    refine subquotOf_congr h ?_ _ _
    rw [hYdef, botConcat_apply, mul_assoc, ← map_mul]
  simp only [hgen]
  refine Eq.trans ?_ (subquotOf_sum h Finset.univ
    (fun u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c => Y u.1) hY).symm
  rw [subquotOf_eq_iff]
  -- `r = ∑_u Y u`
  have hrY : r = ∑ u, Y u := by
    have h1 : (bimodToInd h hr.1 : KLRAlgebra k Q (ν'' + ν''')) =
        ∑ u, hatWRevOf σ u * concat Q ν'' ν''' (g u) := by
      rw [← (rightFreeEquivOf ν'' ν''' σ hsym hσ).apply_symm_apply (bimodToInd h hr.1), ← hg,
        coe_rightFreeEquivOf, rightFreeMapOf_apply,
        Finsupp.sum_fintype _ _ (fun _ => by rw [map_zero, mul_zero])]
    have h2 : r = oneConcat Q ν ν' * castAlg Q h (bimodToInd h hr.1) := by
      have := (mem_bimod h).1 hr.1
      have hr1 : oneConcat Q ν ν' * r = r := by
        rw [← this, ← mul_assoc, ← mul_assoc, oneConcat_idem.eq]
      rw [coe_bimodToInd, castAlg_castAlg_symm, hr1]
    rw [h2, h1, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => (hYdef u).symm
  have hsplit : ∑ u, Y u = ∑ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      Y u.1 + ∑ u ∈ Finset.univ.filter (fun u : Shuffle (Seq.card_add' ν'' ν''') =>
        ¬ crossCount (Multiset.card ν) (Multiset.card ν'') u.1⁻¹ = c), Y u := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun u : Shuffle (Seq.card_add' ν'' ν''') =>
        crossCount (Multiset.card ν) (Multiset.card ν'') u.1⁻¹ = c)]
    congr 1
    exact Finset.sum_subtype _ (fun u => by simp) _
  rw [hrY, hsplit, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun u hu => ?_
  rw [Finset.mem_filter] at hu
  rcases lt_or_gt_of_ne hu.2 with hlt | hgt
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact ⟨hYb u, mackeyFilt_mono (Nat.lt_succ_iff.1 hlt) (hYm u)⟩
  · have hgu : g u = 0 := by
      rw [hg]
      exact rightFreeEquivOf_symm_eq_zero_of_mem_mackeyFilt (r := bimodToInd h hr.1) hsym hσ
        (card_le_card_bot h) (castAlg_mem_mackeyFilt h.symm hr.2) u hgt
    have : Y u = 0 := by
      rw [hYdef, hgu, map_zero, mul_zero, map_zero, mul_zero]
    rw [this]; exact zero_mem _

/-- **`Ψ ∘ Φ = id`.** -/
theorem indSubquotInv_comp_indSubquotMap (c : ℕ) :
    (indSubquotInv h N hsym hσ c).comp (indSubquotMap (Q := Q) h N c) = LinearMap.id := by
  refine BalancedTensor.ext fun z x => ?_
  obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h z
  rw [LinearMap.comp_apply, indSubquotMap_tmul, indSubquotBil_of, indSubquotInv_apply,
    LinearMap.id_apply, subquotOf_eq_sum h hsym hσ hr, ← subquot_sum_tmul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [indMackeyLayerEquiv_mk, BalancedTensor.op_smul_tmul]
  rfl

/-- **`Φ ∘ Ψ` is the action of `1_{ν,ν'}`.** -/
theorem indSubquotMap_comp_indSubquotInv (c : ℕ) :
    (indSubquotMap (Q := Q) h N c).comp (indSubquotInv h N hsym hσ c) = indTopAct h N c 1 := by
  refine LinearMap.ext fun v => ?_
  set E := indMackeyLayerEquiv N hsym hσ (card_le_card_bot h) c
  have hmem : ∀ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      (BalancedTensor.tmul (hatWRevSubOf σ u.1) (E v u) : Ind Q ν'' ν''' N) ∈ Stp c := by
    intro u
    have := tmul_hatWRevSubOf_mem_indMackeyStep (Q := Q) N hσ (card_le_card_bot h) u.1 (E v u)
    rwa [u.2] at this
  have hv : v = ∑ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
      Submodule.Quotient.mk (⟨_, hmem u⟩ : Stp c) := by
    apply E.injective
    rw [map_sum]
    have hs : ∀ u : LayerShuffle (ν := ν'') (ν' := ν''') (Multiset.card ν) c,
        E (Submodule.Quotient.mk (⟨_, hmem u⟩ : Stp c)) = Pi.single u (E v u) := fun u =>
      indMackeyLayerEquiv_mk_hatWRevSubOf (Q := Q) N hsym hσ (card_le_card_bot h) u.1 u.2 (E v u)
    rw [Finset.sum_congr rfl fun u _ => hs u]
    exact (Finset.univ_sum_single _).symm
  rw [LinearMap.comp_apply, indSubquotInv_apply, map_sum]
  conv_rhs => rw [hv, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [indSubquotMap_tmul, indSubquotGen, indSubquotBil_of, indTopAct, indMackeyLayerAct_mk]
  congr 1; apply Subtype.ext
  change BalancedTensor.tmul _ _ = _ • BalancedTensor.tmul _ _
  rw [BalancedTensor.smul_tmul']; congr 1; apply Subtype.ext
  rw [coe_bimodToInd, Submodule.coe_smul, smul_eq_mul, coe_hatWRevSubOf, map_mul,
    castAlg_symm_castAlg, concat_one]

include hsym hσ in
/-- **`Φ` is injective.** -/
theorem indSubquotMap_injective (c : ℕ) :
    Function.Injective (indSubquotMap (Q := Q) h N c) := by
  intro w w' hww'
  have := congrArg (indSubquotInv h N hsym hσ c) hww'
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply,
    indSubquotInv_comp_indSubquotMap h N hsym hσ, LinearMap.id_apply, LinearMap.id_apply] at this

include hsym hσ in
/-- **The image of `Φ` is the `1_{ν,ν'}`-part of the layer.** -/
theorem range_indSubquotMap (c : ℕ) :
    LinearMap.range (indSubquotMap (Q := Q) h N c) =
      LinearMap.range (indTopAct (Q := Q) h N c 1) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine ⟨indSubquotMap h N c w, ?_⟩
    rw [← indSubquotMap_comp_indSubquotInv h N hsym hσ, LinearMap.comp_apply,
      ← LinearMap.comp_apply (indSubquotInv h N hsym hσ c),
      indSubquotInv_comp_indSubquotMap h N hsym hσ, LinearMap.id_apply]
  · rintro _ ⟨v, rfl⟩
    exact ⟨indSubquotInv h N hsym hσ c v, by
      rw [← LinearMap.comp_apply, indSubquotMap_comp_indSubquotInv h N hsym hσ]⟩

end Inv

end KLRAlgebra

end Categorification.KLR
