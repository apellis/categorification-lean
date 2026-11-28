/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndSubquot
import Categorification.KLR.MackeyInj
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.BalancedTensorInternal

/-!
# The Mackey layers of an induced module, factor by factor

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, tensored with a module. Let
`h : ν'' + ν''' = ν + ν'`, let `N` be an `R(ν'') ⊗ R(ν''')`-module, and let `Ind N` be filtered
by the Mackey filtration for the top cut at `|ν|`, with layers `F_c(Ind N) / F_{c-1}(Ind N)`
(`IndMackeyLayer`). For each datum `λ` (a `MackeyQuad` with `|λ| = c`) the map

  `Ξ_λ : (_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} ((_{ν-λ,…} R_{ν''} ⊗ _{λ,…} R_{ν'''}) ⊗_{R''} N)
      → F_c(Ind N) / F_{c-1}(Ind N)`,
  `t ⊗ (b ⊗ x) ↦ [ι(t) ψ_d ι(b) ⊗ x]`

(`indMackeyLeftMap`) is injective and `R(ν) ⊗ R(ν')`-linear; the images for the different `λ`
are independent, and together they span the `1_{ν,ν'}`-part of the layer. So

  `1_{ν,ν'} · gr_c(Ind N) ≅ ⊕_{|λ| = c} MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)`

as `R(ν) ⊗ R(ν')`-modules: the layer is induced from `R' = R(ν-λ) ⊗ R(λ) ⊗ R(γ) ⊗ R(δ)`.

Proof: the decomposition `F_c / F_{c-1} = ⊕_λ MackeyX_λ` of KL I, Proposition 2.18
(`mackeySubquot_isInternal`, a decomposition of right `R''`-modules by `mackeyMap_right`) stays
a direct sum after `- ⊗_{R''} N` (`BalancedTensor.isInternal_range_mapLeftOp`), associativity of
the balanced tensor product, and the injective map `Φ` of `MackeyIndSubquot`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, any choice `σ` of reduced words for the
shuffles (used only for the coordinates in the proof).

## Main definitions

* The right `R(ν'') ⊗ R(ν''')`-module structures on `MackeyBot` and `MackeyX`.
* `KLRAlgebra.indMackeyLeftMap` (`Ξ_λ`).

## Main results

* `KLRAlgebra.indMackeyLeftMap_tmul`, `KLRAlgebra.indMackeyLeftMap_smul`,
  `KLRAlgebra.indMackeyLeftMap_injective`, `KLRAlgebra.indMackeyLeftMap_iSupIndep`,
  `KLRAlgebra.iSup_range_indMackeyLeftMap`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I}

/-! ### Finitely many data `λ` -/

omit [DecidableEq I] in
theorem mackeyQuad_finite [DecidableEq I] : Finite (MackeyQuad ν ν' ν'' ν''') :=
  Finite.of_injective (fun q : MackeyQuad ν ν' ν'' ν''' =>
      (⟨q.β, Multiset.mem_toFinset.2
        (Multiset.mem_powerset.2 ((Multiset.le_add_left _ _).trans_eq q.h₁))⟩ :
        (Multiset.powerset ν).toFinset))
    fun _ _ hqq' => MackeyQuad.ext_of_β (congrArg Subtype.val hqq')

instance : DecidableEq (MackeyQuad ν ν' ν'' ν''') := fun q q' =>
  decidable_of_iff (q.β = q'.β) ⟨MackeyQuad.ext_of_β, fun e => e ▸ rfl⟩

instance (c : ℕ) : Fintype {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} :=
  haveI := mackeyQuad_finite (ν := ν) (ν' := ν') (ν'' := ν'') (ν''' := ν''')
  Fintype.ofFinite _

/-! ### Right module structures -/

section Right

variable (q : MackeyQuad ν ν' ν'' ν''')

instance : SMul (TensorKLR Q ν'' ν''')ᵐᵒᵖ (MackeyBot Q q) := ⟨fun c x => botRMul c.unop x⟩

theorem op_smul_bot_def (c : (TensorKLR Q ν'' ν''')ᵐᵒᵖ) (x : MackeyBot Q q) :
    c • x = botRMul c.unop x := rfl

instance : Module (TensorKLR Q ν'' ν''')ᵐᵒᵖ (MackeyBot Q q) where
  one_smul x := Subtype.ext (mul_one (x : TensorKLR Q ν'' ν'''))
  mul_smul c d x := Subtype.ext (by
    change (x : TensorKLR Q ν'' ν''') * (d.unop * c.unop) = (x * d.unop) * c.unop
    rw [mul_assoc])
  smul_zero c := Subtype.ext (zero_mul _)
  smul_add c x y := Subtype.ext (add_mul _ _ _)
  add_smul c d x := Subtype.ext (mul_add _ _ _)
  zero_smul x := Subtype.ext (mul_zero _)

instance : SMulCommClass (QuadAlg Q q) (TensorKLR Q ν'' ν''')ᵐᵒᵖ (MackeyBot Q q) where
  smul_comm r c x := ((botRMul c.unop).map_smul r x).symm

/-- The right action on `MackeyX` (through `MackeyBot`) is `MackeyX.rightAct`. -/
theorem op_smul_mackeyX (c : (TensorKLR Q ν'' ν''')ᵐᵒᵖ) (x : MackeyX Q q) :
    c • x = MackeyX.rightAct c.unop x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero]
  | tmul t b => rw [BalancedTensor.smul_tmul_right, MackeyX.rightAct_tmul]; rfl
  | add x y hx hy => rw [smul_add, hx, hy, map_add]

variable (h : ν'' + ν''' = ν + ν')

/-- `mackeyMap` is right `R(ν'') ⊗ R(ν''')`-linear for the module structures. -/
theorem mackeyMap_op_smul {c : ℕ} (hc : Multiset.card q.β = c) (a : TensorKLR Q ν'' ν''')
    (x : MackeyX Q q) : mackeyMap h q hc (op a • x) = op a • mackeyMap h q hc x := by
  rw [op_smul_mackeyX, mackeyMap_right, subquot_op_smul_def, unop_op]

end Right

/-! ### The maps `Ξ_λ` -/

variable (h : ν'' + ν''' = ν + ν')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

local notation "Lay" c => IndMackeyLayer Q ν'' ν''' N (Multiset.card ν) c

variable (Q) in
/-- `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)`. -/
abbrev MackeyLeftInd (q : MackeyQuad ν ν' ν'' ν''') : Type _ :=
  BalancedTensor k (TensorKLR Q ν ν') (QuadAlg Q q) (MackeyTop Q q)
    (BalancedTensor k (QuadAlg Q q) (TensorKLR Q ν'' ν''') (MackeyBot Q q) N)

/-- `mackeyMap ⊗ 1 : MackeyX_λ ⊗_{R''} N → (F_c / F_{c-1}) ⊗_{R''} N`. -/
def mackeyTensorMap (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hc : Multiset.card q.β = c) :
    BalancedTensor k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeyX Q q) N →ₗ[k]
      BalancedTensor k (TensorKLR Q ν ν') (TensorKLR Q ν'' ν''') (MackeySubquot Q h c) N :=
  BalancedTensor.mapLeftOp (TensorKLR Q ν ν') N (mackeyMap h q hc) (mackeyMap_op_smul q h hc)

/-- **The map `Ξ_λ`**: `t ⊗ (b ⊗ x) ↦ [ι(t) ψ_d ι(b) ⊗ x]` in the `c`-th layer of `Ind N`. -/
def indMackeyLeftMap (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hc : Multiset.card q.β = c) :
    MackeyLeftInd Q N q →ₗ[k] Lay c :=
  indSubquotMap h N c ∘ₗ mackeyTensorMap h N q hc ∘ₗ
    ((BalancedTensor.assoc k (TensorKLR Q ν ν') (QuadAlg Q q) (TensorKLR Q ν'' ν''')
      (MackeyTop Q q) (MackeyBot Q q) N).symm.toLinearMap.restrictScalars k)

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indMackeyLeftMap_apply (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hc : Multiset.card q.β = c) (w : MackeyLeftInd Q N q) :
    indMackeyLeftMap h N q hc w = indSubquotMap h N c (mackeyTensorMap h N q hc
      ((BalancedTensor.assoc k (TensorKLR Q ν ν') (QuadAlg Q q) (TensorKLR Q ν'' ν''')
        (MackeyTop Q q) (MackeyBot Q q) N).symm w)) := rfl

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indMackeyLeftMap_tmul (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hc : Multiset.card q.β = c) (t : MackeyTop Q q) (b : MackeyBot Q q) (x : N) :
    indMackeyLeftMap h N q hc (BalancedTensor.tmul t (BalancedTensor.tmul b x)) =
      indSubquotBil h N c (mackeyMap h q hc (BalancedTensor.tmul t b)) x := by
  simp only [indMackeyLeftMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, BalancedTensor.assoc_symm_tmul, mackeyTensorMap,
    BalancedTensor.mapLeftOp_tmul, indSubquotMap_tmul]

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- `Ξ_λ` is `R(ν) ⊗ R(ν')`-linear. -/
theorem indMackeyLeftMap_smul (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hc : Multiset.card q.β = c) (a : TensorKLR Q ν ν') (w : MackeyLeftInd Q N q) :
    indMackeyLeftMap h N q hc (a • w) = indTopAct h N c a (indMackeyLeftMap h N q hc w) := by
  simp only [indMackeyLeftMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, map_smul]
  rw [mackeyTensorMap, BalancedTensor.mapLeftOp_smul _ _ (mackeyMap_left h q hc),
    indSubquotMap_smul]

variable (hsym : KLRSymm Q) {σ : Shuffle (Seq.card_add' ν'' ν''') → List ℕ}
  (hσ : ∀ u : Shuffle (Seq.card_add' ν'' ν'''), IsReduced (Multiset.card (ν'' + ν''')) (σ u) ∧
    wordProd (Multiset.card (ν'' + ν''')) (σ u) = u.1)

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
include hsym in
/-- The maps `mackeyMap ⊗ 1` are injective, with independent ranges spanning
`(F_c / F_{c-1}) ⊗_{R''} N`. -/
theorem mackeyTensorMap_isInternal (c : ℕ) :
    (∀ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
      Function.Injective (mackeyTensorMap (Q := Q) h N q.1 q.2)) ∧
    DirectSum.IsInternal fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} =>
      LinearMap.range (mackeyTensorMap (Q := Q) h N q.1 q.2) := by
  exact BalancedTensor.isInternal_range_mapLeftOp (B := TensorKLR Q ν ν') (N := N)
    (Mq := fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} => MackeyX Q q.1)
    (fun q => mackeyMap h q.1 q.2) (fun q a m => mackeyMap_op_smul q.1 h q.2 a m)
    (fun q => mackeyMap_injective h hsym q.1 q.2) (by convert mackeySubquot_isInternal h hsym c)

include hsym hσ in
/-- **`Ξ_λ` is injective.** -/
theorem indMackeyLeftMap_injective {c : ℕ}
    (q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c}) :
    Function.Injective (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
  intro w w' hw
  rw [indMackeyLeftMap_apply, indMackeyLeftMap_apply] at hw
  exact (BalancedTensor.assoc k (TensorKLR Q ν ν') (QuadAlg Q q.1) (TensorKLR Q ν'' ν''')
    (MackeyTop Q q.1) (MackeyBot Q q.1) N).symm.injective
    ((mackeyTensorMap_isInternal h N hsym c).1 q (indSubquotMap_injective h N hsym hσ c hw))

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem range_indMackeyLeftMap (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ}
    (hc : Multiset.card q.β = c) :
    LinearMap.range (indMackeyLeftMap (Q := Q) h N q hc) =
      (LinearMap.range (mackeyTensorMap (Q := Q) h N q hc)).map (indSubquotMap h N c) := by
  rw [indMackeyLeftMap, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (by
      exact (BalancedTensor.assoc k (TensorKLR Q ν ν') (QuadAlg Q q) (TensorKLR Q ν'' ν''')
        (MackeyTop Q q) (MackeyBot Q q) N).symm.surjective), Submodule.map_top]

include hsym hσ in
/-- **The images of the `Ξ_λ` are independent.** -/
theorem indMackeyLeftMap_iSupIndep (c : ℕ) :
    iSupIndep fun q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} =>
      LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
  simp only [range_indMackeyLeftMap]
  exact LinearMap.iSupIndep_map _ (indSubquotMap_injective h N hsym hσ c)
    (mackeyTensorMap_isInternal h N hsym c).2.submodule_iSupIndep

include hsym hσ in
/-- **The images of the `Ξ_λ` span the `1_{ν,ν'}`-part of the layer.** -/
theorem iSup_range_indMackeyLeftMap (c : ℕ) :
    (⨆ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
      LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2)) =
      LinearMap.range (indTopAct (Q := Q) h N c 1) := by
  simp only [range_indMackeyLeftMap]
  rw [← Submodule.map_iSup, (mackeyTensorMap_isInternal h N hsym c).2.submodule_iSup_eq_top,
    Submodule.map_top, range_indSubquotMap h N hsym hσ]

end KLRAlgebra

end Categorification.KLR
