/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidFunctor
import Categorification.WeightedKLR.RedStrands.GradedRightStandardModule
import Categorification.WeightedKLR.RedStrands.BlockCrossingGrading
import Categorification.WeightedKLR.RedStrands.BlockPartialStandardRigid
import Categorification.WeightedKLR.RedStrands.RightStandardReflection

/-!
# The braid of a standard module at a rigid cut

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10, using Proposition 6.9.
Let `t` be a loading of the red order `κ₁ = (1, …, ℓ) = L ++ b :: a :: M` whose cut at `a` is
rigid, and let `σ` be a permutation with `σ(κ₁) = κ₀ = L ++ a :: b :: M`. The braid functor
`𝔅_σ = - ⊗_{T^λ} B` takes the standard module `e(t) T / U_t` to the cut
`e(t) V e_{κ₀}` modulo the diagrams through loadings of order `κ₀` with strictly higher retained
root (`braidRigidStandardEquiv`): `[y] ⊗ m ↦ [y m]`. The map preserves the auxiliary gradings
(`braidRigidStandardGradedEquiv`).
-/

noncomputable section


namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv Categorification.Graded MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "ord" => List.finRange ℓ
local notation "V" => ViolQuotient k Q Λ ν
local notation "E" κ:arg => violMk k Q Λ ν (redProj k Q Λ ν κ)
local notation "𝔹" => braidBimod Q Λ ν hρ hQ σ
local notation "bv" => RectBimod.val (identityCornerMap Q Λ ν hρ hQ) (permCornerMap Q Λ ν hρ hQ σ)

variable {t : Seq (stendhalWeight ℓ ν)} {a b : Fin ℓ} {L M : List (Fin ℓ)}

theorem braidBimod_val_mem (m : 𝔹) : E ord * bv m = bv m ∧ bv m * E ((List.finRange ℓ).map σ) =
    bv m := by
  have h := RectBimod.mem m
  rwa [identityCornerMap_one, permCornerMap_one] at h

/-- Right multiplication by an element of the braiding bimodule, from the cut at the order
`(1, …, ℓ)` to the cut at `κ = σ(1, …, ℓ)`. -/
def cutMulBraid {κ : List (Fin ℓ)} (hκ : (List.finRange ℓ).map σ = κ) (m : 𝔹) :
    violCorner k Q Λ ν t ord →ₗ[k] violCorner k Q Λ ν t κ where
  toFun y := ⟨y.1 * bv m, mem_violCorner_iff.2
    ⟨by rw [← mul_assoc, (mem_violCorner_iff.1 y.2).1],
      by rw [mul_assoc, ← hκ, (braidBimod_val_mem hρ hQ σ m).2]⟩⟩
  map_add' y z := Subtype.ext (add_mul _ _ _)
  map_smul' c y := Subtype.ext (smul_mul_assoc c y.1 _)

theorem cutMulBraid_val {κ : List (Fin ℓ)} (hκ : (List.finRange ℓ).map σ = κ) (m : 𝔹)
    (y : violCorner k Q Λ ν t ord) : (cutMulBraid hρ hQ σ hκ m y).1 = y.1 * bv m := rfl

/-- A standard upper diagram at a rigid cut lies in the block upper ideal of `(1, …, ℓ)`. -/
theorem mem_blockUpperIdeal_of_mem_violStandardUpper {κ₁ : List (Fin ℓ)} (ht : redWord t = κ₁)
    (hord : κ₁ = L ++ b :: a :: M) (hrig : IsRigidCut t a) (y : violCorner k Q Λ ν t κ₁)
    (hy : y ∈ violStandardUpper t κ₁) :
    y.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) κ₁ := by
  subst ht
  have h := (mem_violStandardUpper_iff_mem_blockUpperIdeal hord hrig y).1 hy
  rwa [blockUpperIdeal_swap, adjacentBlockRoot_swap] at h

theorem e_mul_of_mem_violCorner {κ₁ : List (Fin ℓ)} (ht : redWord t = κ₁) {κ : List (Fin ℓ)}
    (y : violCorner k Q Λ ν t κ) : E κ₁ * y.1 = y.1 := by
  rw [← (mem_violCorner_iff.1 y.2).1, ← mul_assoc, ← map_mul, redProj_mul_e, ite_eq_left ht]

variable (t a b) in
/-- `[y] ↦ [y m]`, from the standard module at `t` to the cut quotient at the order `κ₀`. -/
def stdCutMul (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) (m : 𝔹) :
    RightStandard Λ hρ hQ t →ₗ[k] BraidCutQuotient Q Λ t a b (L ++ a :: b :: M) where
  toFun := QuotientAddGroup.lift (violStandardUpper t ord).toAddSubgroup
    ((RedBlock.braidCutMkK t a b _).toAddMonoidHom.comp (cutMulBraid hρ hQ σ hκ m).toAddMonoidHom)
    (fun y hy => by
      have h1 := mem_blockUpperIdeal_of_mem_violStandardUpper ht hord hrig y hy
      have h2 : y.1 * bv m ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) ord :=
        TwoSidedIdeal.mul_mem_right _ _ _ h1
      apply (Submodule.Quotient.mk_eq_zero _).2
      change y.1 * bv m ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (L ++ a :: b :: M)
      refine (mem_blockUpperIdeal_iff ?_ ?_).2 (hord ▸ h2)
      · rw [← hord, ← mul_assoc, e_mul_of_mem_violCorner ht]
      · rw [← hκ, mul_assoc, (braidBimod_val_mem hρ hQ σ m).2])
  map_add' := map_add _
  map_smul' c x := by
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change RedBlock.braidCutMkK t a b _ (cutMulBraid hρ hQ σ hκ m (c • y)) =
        c • RedBlock.braidCutMkK t a b _ (cutMulBraid hρ hQ σ hκ m y)
      rw [map_smul, map_smul]

theorem stdCutMul_mk (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) (m : 𝔹)
    (y : violCorner k Q Λ ν t ord) :
    stdCutMul hρ hQ σ t a b ht hord hκ hrig m (Submodule.Quotient.mk y) =
      braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ m y) := rfl

local notation "𝒯" => TensorProductAlgebra k Q Λ ν
local notation "𝒯σ" => TensorProductAlgebra k Q (Λ ∘ σ) ν

variable (t a b) in
/-- `m ⊗ [y] ↦ [y m]` as a bilinear map. -/
def stdCutBil (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) :
    𝔹 →ₗ[k] RightStandard Λ hρ hQ t →ₗ[k] BraidCutQuotient Q Λ t a b (L ++ a :: b :: M) where
  toFun m := stdCutMul hρ hQ σ t a b ht hord hκ hrig m
  map_add' m m' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ (m + m') y) =
        braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ m y) +
          braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ m' y)
      rw [← map_add]
      congr 1
      exact Subtype.ext (mul_add y.1 (bv m) (bv m'))
  map_smul' c m := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ (c • m) y) =
        c • RedBlock.braidCutMkK t a b _ (cutMulBraid hρ hQ σ hκ m y)
      rw [← map_smul]
      change braidCutMk Q Λ t a b _ _ = braidCutMk Q Λ t a b _ _
      congr 1
      exact Subtype.ext (mul_smul_comm c y.1 (bv m))

theorem stdCutBil_balanced (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) (m : 𝔹)
    (u : 𝒯ᵐᵒᵖ) (n : RightStandard Λ hρ hQ t) :
    stdCutBil hρ hQ σ t a b ht hord hκ hrig (op u • m) n =
      stdCutBil hρ hQ σ t a b ht hord hκ hrig m (u • n) := by
  induction n using Submodule.Quotient.induction_on with
  | H y =>
    change braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ (op u • m) y) =
      braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ m (rightCornerHom hρ hQ u • y))
    congr 1
    exact Subtype.ext (mul_assoc _ _ _).symm

variable (t a b) in
/-- **The braid of a standard module at a rigid cut**, forward map:
`m ⊗ [y] ↦ [y m]`. -/
def braidRigidStandardMap (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) :
    BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t) →ₗ[k]
      BraidCutQuotient Q Λ t a b (L ++ a :: b :: M) :=
  BalancedTensor.lift (stdCutBil hρ hQ σ t a b ht hord hκ hrig)
    (stdCutBil_balanced hρ hQ σ ht hord hκ hrig)

theorem braidRigidStandardMap_tmul_mk (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) (m : 𝔹)
    (y : violCorner k Q Λ ν t ord) :
    braidRigidStandardMap hρ hQ σ t a b ht hord hκ hrig
        (BalancedTensor.tmul m (Submodule.Quotient.mk y)) =
      braidCutMk Q Λ t a b _ (cutMulBraid hρ hQ σ hκ m y) := rfl

/-- A diagram at a rigid cut in the block upper ideal of `(1, …, ℓ)` is a standard upper
diagram. -/
theorem mem_violStandardUpper_of_mem_blockUpperIdeal {κ₁ : List (Fin ℓ)} (ht : redWord t = κ₁)
    (hord : κ₁ = L ++ b :: a :: M) (hrig : IsRigidCut t a) (y : violCorner k Q Λ ν t κ₁)
    (hy : y.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) κ₁) :
    y ∈ violStandardUpper t κ₁ := by
  subst ht
  apply (mem_violStandardUpper_iff_mem_blockUpperIdeal hord hrig y).2
  rwa [blockUpperIdeal_swap, adjacentBlockRoot_swap]

/-- The cut `e_λ v e_{σλ}` of an element of `V`, in the braiding bimodule. -/
def braidCutV (v : V) : 𝔹 :=
  RectBimod.mk (E ord * v * E ((List.finRange ℓ).map σ)) (by
    rw [identityCornerMap_one, permCornerMap_one]
    exact ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq],
      by rw [mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq]⟩)

theorem braidCutV_val (v : V) : bv (braidCutV hρ hQ σ v) = E ord * v * E ((List.finRange ℓ).map σ) :=
  rfl

/-- The generator `[e(t)]` of the right standard module. -/
def rightStandardUnit (ht : redWord t = ord) : RightStandard Λ hρ hQ t :=
  loadingUnit (k := k) (Q := Q) ht

variable (t) in
/-- `v ↦ e_λ v e_{σλ} ⊗ [e(t)]`. -/
def braidTmulV (ht : redWord t = ord) :
    V →+ BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t) where
  toFun v := BalancedTensor.tmul (braidCutV hρ hQ σ v) (rightStandardUnit hρ hQ ht)
  map_zero' := by
    rw [show braidCutV hρ hQ σ 0 = 0 from RectBimod.ext (by
      rw [braidCutV_val, mul_zero, zero_mul]; rfl)]
    exact BalancedTensor.zero_tmul _
  map_add' v w := by
    rw [show braidCutV hρ hQ σ (v + w) = braidCutV hρ hQ σ v + braidCutV hρ hQ σ w from
      RectBimod.ext (by rw [braidCutV_val, mul_add, add_mul]; rfl)]
    exact BalancedTensor.add_tmul _ _ _

theorem braidTmulV_apply (ht : redWord t = ord) (v : V) :
    braidTmulV hρ hQ σ t ht v =
      BalancedTensor.tmul (braidCutV hρ hQ σ v) (rightStandardUnit hρ hQ ht) := rfl

theorem tmul_op_op_smul (m : 𝔹) (τ : 𝒯) (n : RightStandard Λ hρ hQ t) :
    (BalancedTensor.tmul ((op (op τ) : 𝒯ᵐᵒᵖᵐᵒᵖ) • m) n :
      BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t)) =
      BalancedTensor.tmul m ((op τ : 𝒯ᵐᵒᵖ) • n) :=
  BalancedTensor.op_smul_tmul m (op τ) n

theorem op_smul_loadingUnit (ht : redWord t = ord) (τ : 𝒯) :
    ((op τ : 𝒯ᵐᵒᵖ) • rightStandardUnit hρ hQ ht) =
      (Submodule.Quotient.mk (rightCornerHom hρ hQ (op τ) •
        loadingUnitCorner (k := k) (Q := Q) (Λ := Λ) ht) : RightStandard Λ hρ hQ t) := rfl

theorem braidTmulV_generator (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hrig : IsRigidCut t a) {s : Seq (stendhalWeight ℓ ν)} (hs : redWord s = ord)
    (hlt : adjacentBlockRoot a b t < adjacentBlockRoot a b s) (c d : V) :
    braidTmulV hρ hQ σ t ht (c * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) = 0 := by
  have hsE : violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * E ord =
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) := by
    rw [← map_mul, e_mul_redProj, ite_eq_left hs]
  let y : IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν ord) :=
    ⟨E ord * c * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)),
      (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν ord)).2
        ⟨by rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_violMk_redProj k Q Λ ν _).eq],
          by rw [mul_assoc, hsE]⟩⟩
  have hy : ((violCornerEquiv hρ hQ).symm (violCornerEquiv hρ hQ y)).1 =
      E ord * c * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) := by
    rw [RingEquiv.symm_apply_apply]
  have hcut : braidCutV hρ hQ σ (c * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) =
      (op (op (violCornerEquiv hρ hQ y)) : 𝒯ᵐᵒᵖᵐᵒᵖ) • braidCutV hρ hQ σ d := by
    apply RectBimod.ext
    rw [RectBimod.val_smul_left, braidCutV_val, braidCutV_val, unop_op, unop_op,
      identityCornerMap_apply, hy]
    calc E ord * (c * violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * d) *
          E ((List.finRange ℓ).map σ)
        = E ord * c * (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e s)) * E ord) * d *
            E ((List.finRange ℓ).map σ) := by rw [hsE]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have hmem : rightCornerHom hρ hQ (op (violCornerEquiv hρ hQ y)) •
      loadingUnitCorner (k := k) (Q := Q) (Λ := Λ) ht ∈ violStandardUpper t ord := by
    apply mem_violStandardUpper_of_mem_blockUpperIdeal ht hord hrig
    rw [RightStandard.smul_mk_val, unop_op, hy]
    exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.mul_mem_left _ _ _
      (TwoSidedIdeal.subset_span ⟨s, hs, hlt, rfl⟩))
  rw [braidTmulV_apply, hcut, tmul_op_op_smul]
  erw [op_smul_loadingUnit,
    (Submodule.Quotient.mk_eq_zero _).2 hmem, BalancedTensor.tmul_zero]

theorem braidTmulV_eq_zero (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hrig : IsRigidCut t a) {v : V}
    (hv : v ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) ord) :
    braidTmulV hρ hQ σ t ht v = 0 := by
  rw [blockUpperIdeal, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hv
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, ⟨c, -, _, ⟨s, hs, hlt, rfl⟩, rfl⟩, d, -, rfl⟩ := hx
    exact braidTmulV_generator hρ hQ σ ht hord hrig hs hlt c d
  | zero => exact map_zero _
  | add _ _ _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | neg _ _ hu => rw [map_neg, hu, neg_zero]

variable (t a b) in
/-- The inverse map `[w] ↦ (e_λ w e_{σλ}) ⊗ [e(t)]`. -/
def braidRigidStandardInv (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hrig : IsRigidCut t a) :
    BraidCutQuotient Q Λ t a b (L ++ a :: b :: M) →+
      BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t) :=
  braidCutLift ((braidTmulV hρ hQ σ t ht).comp
    (violCorner k Q Λ ν t (L ++ a :: b :: M)).subtype.toAddMonoidHom) fun w hw => by
    apply braidTmulV_eq_zero hρ hQ σ ht hord hrig
    have hw' : w.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (L ++ a :: b :: M) := hw
    rw [hord]
    refine (mem_blockUpperIdeal_iff ?_ ?_).1 hw'
    · rw [← hord]
      exact e_mul_of_mem_violCorner ht w
    · exact (mem_violCorner_iff.1 w.2).2

theorem braidRigidStandardInv_mk (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hrig : IsRigidCut t a)
    (w : violCorner k Q Λ ν t (L ++ a :: b :: M)) :
    braidRigidStandardInv hρ hQ σ t a b ht hord hrig (braidCutMk Q Λ t a b _ w) =
      BalancedTensor.tmul (braidCutV hρ hQ σ w.1) (rightStandardUnit hρ hQ ht) := rfl

theorem braidRigidStandardInv_map (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a)
    (x : BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t)) :
    braidRigidStandardInv (Λ := Λ) hρ hQ σ t a b ht hord hrig
      (braidRigidStandardMap (Λ := Λ) hρ hQ σ t a b ht hord hκ hrig x) = x := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m n =>
    induction n using Submodule.Quotient.induction_on with
    | H y =>
      rw [braidRigidStandardMap_tmul_mk, braidRigidStandardInv_mk]
      let τ : 𝒯 := violCornerEquiv hρ hQ ⟨y.1, mem_corner_of_mem_violCorner ht y⟩
      have hτ : ((violCornerEquiv hρ hQ).symm τ).1 = y.1 :=
        congrArg Subtype.val ((violCornerEquiv hρ hQ).symm_apply_apply _)
      have hcut : braidCutV hρ hQ σ (cutMulBraid hρ hQ σ hκ m y).1 =
          (op (op τ) : 𝒯ᵐᵒᵖᵐᵒᵖ) • m := by
        apply RectBimod.ext
        rw [RectBimod.val_smul_left, braidCutV_val, cutMulBraid_val, unop_op, unop_op,
          identityCornerMap_apply, hτ, ← mul_assoc, e_mul_of_mem_violCorner ht, mul_assoc,
          (braidBimod_val_mem hρ hQ σ m).2]
      have hy : rightCornerHom hρ hQ (op τ) • loadingUnitCorner (k := k) (Q := Q) (Λ := Λ) ht =
          y := by
        apply Subtype.ext
        rw [RightStandard.smul_mk_val, unop_op, hτ]
        exact (mem_violCorner_iff.1 y.2).1
      rw [hcut, tmul_op_op_smul]
      erw [op_smul_loadingUnit, hy]

theorem braidRigidStandardMap_inv (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a)
    (z : BraidCutQuotient Q Λ t a b (L ++ a :: b :: M)) :
    braidRigidStandardMap (Λ := Λ) hρ hQ σ t a b ht hord hκ hrig
      (braidRigidStandardInv (Λ := Λ) hρ hQ σ t a b ht hord hrig z) = z := by
  obtain ⟨w, rfl⟩ := braidCutMk_surjective Q Λ t a b _ z
  rw [braidRigidStandardInv_mk, rightStandardUnit, loadingUnit, braidRigidStandardMap_tmul_mk]
  congr 1
  apply Subtype.ext
  rw [cutMulBraid_val, braidCutV_val]
  change violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t)) * _ = w.1
  rw [← mul_assoc, ← mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left ht,
    (mem_violCorner_iff.1 w.2).1, hκ, (mem_violCorner_iff.1 w.2).2]

variable (t a b) in
/-- **The braid of a standard module at a rigid cut** (part of the proof of Webster,
arXiv:1309.3796v2, Corollary 6.10, via Proposition 6.9): for a loading `t` of the order
`(1, …, ℓ) = L ++ b :: a :: M` whose cut at `a` is rigid, and `σ(1, …, ℓ) = L ++ a :: b :: M`,
`B ⊗_{T^λ} (e(t) T / U_t)` is the cut `e(t) V e_{σλ}` modulo higher loadings, by
`m ⊗ [y] ↦ [y m]`. -/
def braidRigidStandardEquiv (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) :
    BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t) ≃ₗ[k]
      BraidCutQuotient Q Λ t a b (L ++ a :: b :: M) :=
  { braidRigidStandardMap (Λ := Λ) hρ hQ σ t a b ht hord hκ hrig with
    invFun := braidRigidStandardInv (Λ := Λ) hρ hQ σ t a b ht hord hrig
    left_inv := braidRigidStandardInv_map hρ hQ σ ht hord hκ hrig
    right_inv := braidRigidStandardMap_inv hρ hQ σ ht hord hκ hrig }


/-! ### Gradings -/

variable (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "𝔹G" => RectBimod.grading (violAuxiliaryGrade (ν := ν) G)
  (identityCornerMap Q Λ ν hρ hQ) (permCornerMap Q Λ ν hρ hQ σ)
variable (t) in
/-- The auxiliary grading of the right standard module `e(t) T / U_t`. -/
abbrev rightStandardGrade : ℤ → Submodule k (RightStandard Λ hρ hQ t) :=
  RedBlock.loadingStandardGrade G t ord

theorem braidRigidStandardMap_mem_grade (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) {d : ℤ}
    {x : BalancedTensor k 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹 (RightStandard Λ hρ hQ t)}
    (hx : x ∈ balancedGrading 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹G (rightStandardGrade (Λ := Λ) hρ hQ t G) d) :
    braidRigidStandardMap (Λ := Λ) hρ hQ σ t a b ht hord hκ hrig x ∈
      RedBlock.braidCutGrade G t a b (L ++ a :: b :: M) d := by
  refine balancedGrading_map_mem _ _ (fun i j m n hm hn => ?_) hx
  have hn' : (n : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord) ∈
      RedBlock.loadingStandardGrade G t ord j := hn
  obtain ⟨y, hy, hyn⟩ := (Submodule.mem_map (f := RedBlock.loadingMkK t ord)).1 hn'
  have hn'' : n = (Submodule.Quotient.mk y : RightStandard Λ hρ hQ t) := hyn.symm
  subst hn''
  have hc : cutMulBraid hρ hQ σ hκ m y ∈ RedBlock.violCornerGrade G t (L ++ a :: b :: M) (i + j) := by
    change (cutMulBraid hρ hQ σ hκ m y).1 ∈ violAuxiliaryGrade G (i + j)
    rw [cutMulBraid_val, add_comm]
    exact SetLike.GradedMul.mul_mem hy ((RectBimod.mem_grading _).1 hm)
  exact RedBlock.braidCutMk_preservesGrading G t a b _ hc

theorem braidRigidStandardInv_mem_grade (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hrig : IsRigidCut t a) {d : ℤ} {z : BraidCutQuotient Q Λ t a b (L ++ a :: b :: M)}
    (hz : z ∈ RedBlock.braidCutGrade G t a b (L ++ a :: b :: M) d) :
    braidRigidStandardInv (Λ := Λ) hρ hQ σ t a b ht hord hrig z ∈
      balancedGrading 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹G (rightStandardGrade (Λ := Λ) hρ hQ t G) d := by
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
  rw [RedBlock.braidCutMkK_apply, braidRigidStandardInv_mk, ← add_zero d]
  refine tmul_mem_balancedGrading ((RectBimod.mem_grading _).2 ?_) ?_
  · change E ord * w.1 * E ((List.finRange ℓ).map σ) ∈ _
    rw [← zero_add d, ← add_zero (0 + d)]
    exact SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem
      (redProj_mem_violAuxiliaryGrade G _) hw) (redProj_mem_violAuxiliaryGrade G _)
  · change (Submodule.Quotient.mk (loadingUnitCorner (k := k) (Q := Q) (Λ := Λ) ht) :
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t ord) ∈
        RedBlock.loadingStandardGrade G t ord 0
    exact Submodule.mem_map_of_mem (f := RedBlock.loadingMkK t ord)
      (RedBlock.violIdem_mem_violAuxiliaryGrade G t)

variable (t a b) in
/-- `braidRigidStandardEquiv` preserves the auxiliary gradings: the balanced tensor grading of
`B ⊗ (e(t) T / U_t)` and the grading of the cut quotient. -/
def braidRigidStandardGradedEquiv (ht : redWord t = ord) (hord : ord = L ++ b :: a :: M)
    (hκ : (List.finRange ℓ).map σ = L ++ a :: b :: M) (hrig : IsRigidCut t a) :
    balancedGrading 𝒯σᵐᵒᵖ 𝒯ᵐᵒᵖ 𝔹G (rightStandardGrade (Λ := Λ) hρ hQ t G) ≃ᵍ[k]
      RedBlock.braidCutGrade G t a b (L ++ a :: b :: M) where
  toLinearEquiv := braidRigidStandardEquiv (Λ := Λ) hρ hQ σ t a b ht hord hκ hrig
  map_mem' _ _ hx := braidRigidStandardMap_mem_grade hρ hQ σ G ht hord hκ hrig hx
  symm_map_mem' _ _ hz := braidRigidStandardInv_mem_grade hρ hQ σ G ht hord hrig hz

end Categorification.Stendhal.BraidedStendhalAlgebra
