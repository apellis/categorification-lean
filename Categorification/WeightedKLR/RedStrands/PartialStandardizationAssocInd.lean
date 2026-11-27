/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ConcatAssoc
import Categorification.WeightedKLR.RedStrands.LastRedShuffleModule

/-!
# Associativity of KLR induction for three blocks

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, induction `Ind_{ν,ν'}`, for modules over the
tensor product of three KLR algebras `R(ν) ⊗ (R(ν') ⊗ R(ν''))`. Such a module `N` can be
induced in one step, along the triple concatenation
`ι₃ = ι_{ν,ν'+ν''} ∘ (id ⊗ ι_{ν',ν''})` (`Ind3`), or in two: first along `ι_{ν',ν''}` from the
last two factors, with `R(ν)` acting by functoriality (`IndMid`), then along `ι_{ν,ν'+ν''}`
(`IndIter`). The two agree (`indIterEquiv`). This is the input for comparing the orders of the
cuts of an iterated partial standardization (Webster, arXiv:1309.3796v3, §5.1).

## Main definitions

* `KLRAlgebra.concat3`: the triple concatenation `ι₃`.
* `KLRAlgebra.IndBimod3`, `KLRAlgebra.Ind3`: one-step induction along `ι₃`.
* `KLRAlgebra.IndMid`: induction from the last two factors, a module over `R(ν) ⊗ R(ν'+ν'')`.
* `KLRAlgebra.IndIter`: the iterated induction.
* `KLRAlgebra.indIterEquiv`: `IndIter N ≅ Ind3 N`, linear over `R(ν + (ν' + ν''))`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open MulOpposite KLRAlgebra Categorification.Stendhal

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (ν ν' ν'' : Multiset I)

/-- The tensor product of three KLR algebras, `R(ν) ⊗ (R(ν') ⊗ R(ν''))`. -/
abbrev TensorKLR3 : Type _ := KLRAlgebra k Q ν ⊗[k] TensorKLR Q ν' ν''

/-- **The triple concatenation** `ι₃ = ι_{ν,ν'+ν''} ∘ (id ⊗ ι_{ν',ν''})`. -/
def concat3 : TensorKLR3 Q ν ν' ν'' →ₗ[k] KLRAlgebra k Q (ν + (ν' + ν'')) :=
  (concat Q ν (ν' + ν'')).comp (TensorProduct.map LinearMap.id (concat Q ν' ν''))

variable {Q ν ν' ν''}

theorem concat3_tmul (a : KLRAlgebra k Q ν) (u : TensorKLR Q ν' ν'') :
    concat3 Q ν ν' ν'' (a ⊗ₜ u) = concat Q ν (ν' + ν'') (a ⊗ₜ concat Q ν' ν'' u) := rfl

theorem concat3_mul (s t : TensorKLR3 Q ν ν' ν'') :
    concat3 Q ν ν' ν'' (s * t) = concat3 Q ν ν' ν'' s * concat3 Q ν ν' ν'' t := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => rw [add_mul, map_add, map_add, hs, hs', add_mul]
  | tmul a u =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [mul_add, map_add, map_add, ht, ht', mul_add]
    | tmul b v =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, concat3_tmul, concat3_tmul, concat3_tmul,
        concat_mul u v, ← concat_mul (a ⊗ₜ concat Q ν' ν'' u) (b ⊗ₜ concat Q ν' ν'' v),
        Algebra.TensorProduct.tmul_mul_tmul]

variable (Q ν ν' ν'') in
/-- The idempotent `1_{ν,ν',ν''} = ι₃(1)`. -/
abbrev oneConcat3 : KLRAlgebra k Q (ν + (ν' + ν'')) := concat3 Q ν ν' ν'' 1

theorem oneConcat3_eq :
    oneConcat3 Q ν ν' ν'' = concat Q ν (ν' + ν'') (1 ⊗ₜ oneConcat Q ν' ν'') := by
  rw [oneConcat3, Algebra.TensorProduct.one_def, concat3_tmul, concat_one]

theorem concat3_mul_oneConcat3 (t : TensorKLR3 Q ν ν' ν'') :
    concat3 Q ν ν' ν'' t * oneConcat3 Q ν ν' ν'' = concat3 Q ν ν' ν'' t := by
  rw [oneConcat3, ← concat3_mul, mul_one]

theorem oneConcat3_mul_concat3 (t : TensorKLR3 Q ν ν' ν'') :
    oneConcat3 Q ν ν' ν'' * concat3 Q ν ν' ν'' t = concat3 Q ν ν' ν'' t := by
  rw [oneConcat3, ← concat3_mul, one_mul]

theorem oneConcat3_mul_oneConcat :
    oneConcat3 Q ν ν' ν'' * oneConcat Q ν (ν' + ν'') = oneConcat3 Q ν ν' ν'' := by
  rw [oneConcat3_eq, concat_mul_oneConcat]

theorem oneConcat3_idem : IsIdempotentElem (oneConcat3 Q ν ν' ν'') :=
  concat3_mul_oneConcat3 1

/-! ### One-step induction along `ι₃` -/

variable (Q ν ν' ν'') in
/-- The `(R(ν + (ν' + ν'')), R(ν) ⊗ R(ν') ⊗ R(ν''))`-bimodule `R(ν + (ν' + ν'')) 1_{ν,ν',ν''}`. -/
abbrev IndBimod3 : Type _ := Graded.leftIdeal (oneConcat3 Q ν ν' ν'')

theorem mul_concat3_mem (m : IndBimod3 Q ν ν' ν'') (t : TensorKLR3 Q ν ν' ν'') :
    (m : KLRAlgebra k Q (ν + (ν' + ν''))) * concat3 Q ν ν' ν'' t ∈
      Graded.leftIdeal (oneConcat3 Q ν ν' ν'') := by
  rw [Graded.mem_leftIdeal, mul_assoc, concat3_mul_oneConcat3]

instance : SMul (TensorKLR3 Q ν ν' ν'')ᵐᵒᵖ (IndBimod3 Q ν ν' ν'') :=
  ⟨fun t m => ⟨m * concat3 Q ν ν' ν'' t.unop, mul_concat3_mem m _⟩⟩

theorem coe_op_smul3 (t : (TensorKLR3 Q ν ν' ν'')ᵐᵒᵖ) (m : IndBimod3 Q ν ν' ν'') :
    ((t • m : IndBimod3 Q ν ν' ν'') : KLRAlgebra k Q (ν + (ν' + ν''))) =
      m * concat3 Q ν ν' ν'' t.unop := rfl

instance : Module (TensorKLR3 Q ν ν' ν'')ᵐᵒᵖ (IndBimod3 Q ν ν' ν'') where
  one_smul m := Subtype.ext (by rw [coe_op_smul3, unop_one]; exact m.2)
  mul_smul s t m := Subtype.ext (by simp only [coe_op_smul3, unop_mul, concat3_mul, mul_assoc])
  smul_zero t := Subtype.ext (by simp [coe_op_smul3])
  smul_add t m m' := Subtype.ext (by simp [coe_op_smul3, add_mul])
  add_smul s t m := Subtype.ext (by simp [coe_op_smul3, mul_add])
  zero_smul m := Subtype.ext (by simp [coe_op_smul3])

instance : IsScalarTower k (TensorKLR3 Q ν ν' ν'')ᵐᵒᵖ (IndBimod3 Q ν ν' ν'') where
  smul_assoc c t m := Subtype.ext (by
    change (m : KLRAlgebra k Q (ν + (ν' + ν''))) * concat3 Q ν ν' ν'' (unop (c • t)) =
      c • ((m : KLRAlgebra k Q (ν + (ν' + ν''))) * concat3 Q ν ν' ν'' t.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (KLRAlgebra k Q (ν + (ν' + ν''))) (TensorKLR3 Q ν ν' ν'')ᵐᵒᵖ
    (IndBimod3 Q ν ν' ν'') where
  smul_comm r t m := Subtype.ext (by
    rw [coe_op_smul3, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul3, smul_eq_mul,
      smul_eq_mul, mul_assoc])

variable (Q ν ν' ν'') in
/-- **One-step induction along `ι₃`**: `R(ν + (ν' + ν'')) 1_{ν,ν',ν''} ⊗ N`. -/
abbrev Ind3 (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR3 Q ν ν' ν'') N] :
    Type _ :=
  BalancedTensor k (KLRAlgebra k Q (ν + (ν' + ν''))) (TensorKLR3 Q ν ν' ν'')
    (IndBimod3 Q ν ν' ν'') N

/-! ### Iterated induction -/

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR3 Q ν ν' ν'') N]
  [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N]

variable (Q ν ν' ν'') in
/-- A module over the three factors, as a module over the last two. -/
@[nolint unusedArguments]
def IndInnerInput (_Q : I → I → MvPolynomial (Fin 2) k) (_ν _ν' _ν'' : Multiset I) (N : Type*)
    [AddCommGroup N] [Module k N] [Module (TensorKLR3 _Q _ν _ν' _ν'') N] : Type _ := N

local notation "N₂" => IndInnerInput Q ν ν' ν'' N
local notation "B₃" => TensorKLR3 Q ν ν' ν''
local notation "B₂" => TensorKLR Q ν' ν''

instance : AddCommGroup N₂ := inferInstanceAs (AddCommGroup N)
instance : Module k N₂ := inferInstanceAs (Module k N)
instance : Module B₃ N₂ := inferInstanceAs (Module B₃ N)
instance : Module B₂ N₂ :=
  Module.compHom N (Algebra.TensorProduct.includeRight : B₂ →ₐ[k] B₃).toRingHom

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indInnerInput_smul (u : B₂) (n : N₂) :
    u • n = ((1 : KLRAlgebra k Q ν) ⊗ₜ u : B₃) • (n : N) := rfl

instance : IsScalarTower k B₂ N₂ where
  smul_assoc c u n := by
    rw [indInnerInput_smul, indInnerInput_smul, TensorProduct.tmul_smul]
    exact smul_assoc c ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] u : B₃) (show N from n)

/-- The action of `a ∈ R(ν)` on `N`, linear over the last two factors. -/
def indHeadEnd (a : KLRAlgebra k Q ν) : N₂ →ₗ[B₂] N₂ where
  toFun n := ((a ⊗ₜ (1 : B₂) : B₃) • (n : N) : N)
  map_add' := smul_add _
  map_smul' u n := by
    change (a ⊗ₜ (1 : B₂) : B₃) • ((1 ⊗ₜ u : B₃) • (n : N)) =
      ((1 : KLRAlgebra k Q ν) ⊗ₜ u : B₃) • ((a ⊗ₜ (1 : B₂) : B₃) • (n : N))
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

local notation "A₂" => KLRAlgebra k Q (ν' + ν'')

variable (Q ν ν' ν'') in
/-- **Induction from the last two factors**, `R(ν'+ν'') 1_{ν',ν''} ⊗ N`. -/
abbrev IndInner : Type _ := Ind Q ν' ν'' (IndInnerInput Q ν ν' ν'' N)

/-- The action of `R(ν)` on the inner induction, by functoriality. -/
def indHeadAction : KLRAlgebra k Q ν →ₐ[k] Module.End k (IndInner Q ν ν' ν'' N) where
  toFun a := (BalancedTensor.mapRight (k := k) (B := A₂) (indHeadEnd N a)).restrictScalars k
  map_one' := by
    refine LinearMap.ext fun y => ?_
    induction y using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n =>
      change BalancedTensor.tmul m (((1 : KLRAlgebra k Q ν) ⊗ₜ (1 : B₂) : B₃) • (n : N)) = _
      rw [← Algebra.TensorProduct.one_def, one_smul]; rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_mul' a b := by
    refine LinearMap.ext fun y => ?_
    induction y using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n =>
      change BalancedTensor.tmul m (((a * b) ⊗ₜ (1 : B₂) : B₃) • (n : N)) =
        BalancedTensor.tmul m ((a ⊗ₜ (1 : B₂) : B₃) • (b ⊗ₜ (1 : B₂) : B₃) • (n : N))
      rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_zero' := by
    refine LinearMap.ext fun y => ?_
    induction y using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n =>
      change BalancedTensor.tmul m (((0 : KLRAlgebra k Q ν) ⊗ₜ (1 : B₂) : B₃) • (n : N)) = _
      rw [TensorProduct.zero_tmul, show ((0 : B₃) • (n : N)) = 0 from zero_smul B₃ (show N from n),
        LinearMap.zero_apply]
      exact BalancedTensor.tmul_zero _
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_add' a b := by
    refine LinearMap.ext fun y => ?_
    induction y using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n =>
      change BalancedTensor.tmul m (((a + b) ⊗ₜ (1 : B₂) : B₃) • (n : N)) =
        BalancedTensor.tmul m ((a ⊗ₜ (1 : B₂) : B₃) • (n : N)) +
          BalancedTensor.tmul m ((b ⊗ₜ (1 : B₂) : B₃) • (n : N))
      rw [TensorProduct.add_tmul, add_smul, BalancedTensor.tmul_add]
    | add x y hx hy => rw [map_add, hx, hy, ← map_add]
  commutes' c := by
    refine LinearMap.ext fun y => ?_
    induction y using BalancedTensor.induction_on with
    | zero => simp
    | tmul m n =>
      rw [Module.algebraMap_end_apply]
      have h : ((((algebraMap k (KLRAlgebra k Q ν) c) ⊗ₜ (1 : B₂) : B₃) • (show N from n) : N) :
          N₂) = c • n := by
        change _ = c • (show N from n)
        rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', smul_assoc,
          ← Algebra.TensorProduct.one_def, one_smul]
      exact (congrArg (BalancedTensor.tmul (k := k) (B := A₂) (A := B₂) (N := N₂) m) h).trans
        (BalancedTensor.tmul_smul c m n)
    | add x y hx hy => rw [map_add, hx, hy, map_add]

theorem indHeadAction_tmul (a : KLRAlgebra k Q ν) (m : IndBimod Q ν' ν'') (n : N₂) :
    indHeadAction N a (BalancedTensor.tmul m n : IndInner Q ν ν' ν'' N) =
      BalancedTensor.tmul m ((a ⊗ₜ (1 : B₂) : B₃) • (n : N) : N) := rfl

/-- The action of `R(ν)` commutes with the action of `R(ν' + ν'')`. -/
theorem commute_indHeadAction (a : KLRAlgebra k Q ν) (z : A₂) :
    Commute (indHeadAction N a) (Algebra.lsmul k k (IndInner Q ν ν' ν'' N) z) :=
  LinearMap.ext fun y => (BalancedTensor.mapRight (k := k) (B := A₂) (indHeadEnd N a)).map_smul
    z y

/-- The action of `R(ν) ⊗ R(ν' + ν'')` on the inner induction. -/
def indMidAction :
    TensorKLR Q ν (ν' + ν'') →ₐ[k] Module.End k (IndInner Q ν ν' ν'' N) :=
  Algebra.TensorProduct.lift (indHeadAction N) (Algebra.lsmul k k (IndInner Q ν ν' ν'' N))
    (fun a z => commute_indHeadAction N a z)

theorem indMidAction_tmul (a : KLRAlgebra k Q ν) (z : A₂) (y : IndInner Q ν ν' ν'' N) :
    indMidAction N (a ⊗ₜ z) y = indHeadAction N a (z • y) := rfl

variable (Q ν ν' ν'') in
/-- **The inner induction**, as a module over `R(ν) ⊗ R(ν' + ν'')`. -/
abbrev IndMid : Type _ := IndInner Q ν ν' ν'' N

instance : Module (TensorKLR Q ν (ν' + ν'')) (IndMid Q ν ν' ν'' N) :=
  Module.compHom (IndInner Q ν ν' ν'' N) (indMidAction N).toRingHom

theorem indMid_smul (s : TensorKLR Q ν (ν' + ν'')) (y : IndMid Q ν ν' ν'' N) :
    s • y = indMidAction N s y := rfl

instance : IsScalarTower k (TensorKLR Q ν (ν' + ν'')) (IndMid Q ν ν' ν'' N) where
  smul_assoc c s y := by
    rw [indMid_smul, indMid_smul, map_smul]; rfl

variable (Q ν ν' ν'') in
/-- **Iterated induction**: induction along `ι_{ν,ν'+ν''}` of the inner induction. -/
abbrev IndIter : Type _ := Ind Q ν (ν' + ν'') (IndMid Q ν ν' ν'' N)

/-! ### The comparison -/

local notation "A₃" => KLRAlgebra k Q (ν + (ν' + ν''))

/-- The element `m · ι_{ν,ν'+ν''}(1 ⊗ m')` of `R(ν + (ν' + ν'')) 1_{ν,ν',ν''}`. -/
def indIterElt (m : IndBimod Q ν (ν' + ν'')) : IndBimod Q ν' ν'' →ₗ[k] IndBimod3 Q ν ν' ν'' where
  toFun m' := ⟨(m : A₃) * concat Q ν (ν' + ν'') (1 ⊗ₜ (m' : A₂)), by
    rw [Graded.mem_leftIdeal, oneConcat3_eq, mul_assoc, ← concat_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, m'.2]⟩
  map_add' m' m'' := Subtype.ext (by
    simp only [Submodule.coe_add, TensorProduct.tmul_add, map_add, mul_add])
  map_smul' c m' := Subtype.ext (by
    simp only [Submodule.coe_smul_of_tower, TensorProduct.tmul_smul, map_smul, mul_smul_comm,
      RingHom.id_apply])

theorem coe_indIterElt (m : IndBimod Q ν (ν' + ν'')) (m' : IndBimod Q ν' ν'') :
    ((indIterElt m m' : IndBimod3 Q ν ν' ν'') : A₃) =
      (m : A₃) * concat Q ν (ν' + ν'') (1 ⊗ₜ (m' : A₂)) := rfl

/-- The inner bilinear map `m' ⊗ n ↦ (m · ι(1 ⊗ m')) ⊗ n`. -/
def indIterInnerBil (m : IndBimod Q ν (ν' + ν'')) :
    IndBimod Q ν' ν'' →ₗ[k] N₂ →ₗ[k] Ind3 Q ν ν' ν'' N :=
  LinearMap.mk₂ k (fun m' n => BalancedTensor.tmul (indIterElt m m') (show N from n))
    (fun m' m'' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c m' n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun m' n n' => BalancedTensor.tmul_add _ _ _)
    (fun c m' n => BalancedTensor.tmul_smul _ _ _)

/-- The map from the inner induction for a fixed outer coefficient `m`. -/
def indIterInner (m : IndBimod Q ν (ν' + ν'')) : IndInner Q ν ν' ν'' N →ₗ[k] Ind3 Q ν ν' ν'' N :=
  BalancedTensor.lift (indIterInnerBil N m) (fun m' u n => by
    change (BalancedTensor.tmul (indIterElt m (op u • m')) (show N from n) : Ind3 Q ν ν' ν'' N) =
      BalancedTensor.tmul (indIterElt m m') (((1 : KLRAlgebra k Q ν) ⊗ₜ u : B₃) • (n : N))
    have h : indIterElt m (op u • m') = op ((1 : KLRAlgebra k Q ν) ⊗ₜ u : B₃) • indIterElt m m' :=
      Subtype.ext (by
        rw [coe_op_smul3, coe_indIterElt, coe_indIterElt, coe_op_smul]
        simp only [unop_op]
        rw [concat3_tmul, mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    rw [h, BalancedTensor.op_smul_tmul]
    rfl)

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indIterInner_tmul (m : IndBimod Q ν (ν' + ν'')) (m' : IndBimod Q ν' ν'') (n : N₂) :
    indIterInner N m (BalancedTensor.tmul m' n) =
      BalancedTensor.tmul (indIterElt m m') (show N from n) := rfl

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indIterInner_add (m m₂ : IndBimod Q ν (ν' + ν'')) :
    indIterInner N (m + m₂) = indIterInner N m + indIterInner N m₂ :=
  BalancedTensor.ext fun m' n => by
    change (BalancedTensor.tmul (indIterElt (m + m₂) m') (show N from n) : Ind3 Q ν ν' ν'' N) =
      BalancedTensor.tmul (indIterElt m m') (show N from n) +
        BalancedTensor.tmul (indIterElt m₂ m') (show N from n)
    rw [← BalancedTensor.add_tmul]
    congr 1
    exact Subtype.ext (by simp only [coe_indIterElt, Submodule.coe_add, add_mul])

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indIterInner_smul (b : A₃) (m : IndBimod Q ν (ν' + ν'')) (y : IndInner Q ν ν' ν'' N) :
    indIterInner N (b • m) y = b • indIterInner N m y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp
  | tmul m' n =>
    rw [indIterInner_tmul, indIterInner_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (by simp only [coe_indIterElt, Submodule.coe_smul, smul_eq_mul, mul_assoc])
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indIterInner_smul_k (c : k) (m : IndBimod Q ν (ν' + ν'')) :
    indIterInner N (c • m) = c • indIterInner N m :=
  BalancedTensor.ext fun m' n => by
    change (BalancedTensor.tmul (indIterElt (c • m) m') (show N from n) : Ind3 Q ν ν' ν'' N) =
      c • (BalancedTensor.tmul (indIterElt m m') (show N from n) : Ind3 Q ν ν' ν'' N)
    rw [← BalancedTensor.smul_tmul]
    congr 1
    exact Subtype.ext (by
      simp only [coe_indIterElt, Submodule.coe_smul_of_tower, smul_mul_assoc])

/-- The outer balancing of the comparison map. -/
theorem indIterInner_balanced (m : IndBimod Q ν (ν' + ν'')) (s : TensorKLR Q ν (ν' + ν''))
    (y : IndInner Q ν ν' ν'' N) :
    indIterInner N (op s • m) y = indIterInner N m (indMidAction N s y) := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' =>
    rw [op_add, add_smul, indIterInner_add, LinearMap.add_apply, hs, hs', map_add,
      LinearMap.add_apply, map_add]
  | tmul a z =>
    induction y using BalancedTensor.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul m' n =>
      rw [indMidAction_tmul, BalancedTensor.smul_tmul', indHeadAction_tmul, indIterInner_tmul,
        indIterInner_tmul]
      have h : indIterElt (op (a ⊗ₜ z) • m) m' =
          op (a ⊗ₜ (1 : B₂) : B₃) • indIterElt m (z • m') := Subtype.ext (by
        rw [coe_op_smul3, coe_indIterElt, coe_indIterElt, coe_op_smul]
        simp only [unop_op]
        rw [concat3_tmul, concat_one, Submodule.coe_smul, smul_eq_mul, mul_assoc, mul_assoc,
          ← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_assoc, m'.2])
      rw [h, BalancedTensor.op_smul_tmul]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- **The comparison map** `IndIter N → Ind3 N`, `m ⊗ (m' ⊗ n) ↦ (m · ι(1 ⊗ m')) ⊗ n`. -/
def indIterHom : IndIter Q ν ν' ν'' N →ₗ[A₃] Ind3 Q ν ν' ν'' N :=
  BalancedTensor.liftB
    { toFun := fun m => indIterInner N m
      map_add' := indIterInner_add N
      map_smul' := indIterInner_smul_k N }
    (fun m s y => indIterInner_balanced N m s y)
    (fun b m y => indIterInner_smul N b m y)

theorem indIterHom_tmul (m : IndBimod Q ν (ν' + ν'')) (y : IndMid Q ν ν' ν'' N) :
    indIterHom N (BalancedTensor.tmul m y) = indIterInner N m y := rfl

/-- An element of `R(ν + (ν' + ν'')) 1_{ν,ν',ν''}` lies in `R(ν + (ν' + ν'')) 1_{ν,ν'+ν''}`. -/
def indBimod3Incl : IndBimod3 Q ν ν' ν'' →ₗ[k] IndBimod Q ν (ν' + ν'') where
  toFun x := ⟨x, by
    have hx : (x : A₃) * oneConcat3 Q ν ν' ν'' = x := x.2
    have h2 : (x : A₃) * oneConcat Q ν (ν' + ν'') =
        (x : A₃) * oneConcat3 Q ν ν' ν'' * oneConcat Q ν (ν' + ν'') := by rw [hx]
    rw [Graded.mem_leftIdeal, h2, mul_assoc, oneConcat3_mul_oneConcat, hx]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (Q ν ν' ν'') in
/-- `n ∈ N` viewed in the module over the last two factors. -/
abbrev asInner (n : N) : N₂ := n

/-- The identity-shuffle copy of `n` in the inner induction. -/
def indMidUnit : N →ₗ[k] IndMid Q ν ν' ν'' N where
  toFun n := BalancedTensor.tmul (oneConcatSubBimod : IndBimod Q ν' ν'') (asInner Q ν ν' ν'' N n)
  map_add' n n' := BalancedTensor.tmul_add _ (asInner Q ν ν' ν'' N n) (asInner Q ν ν' ν'' N n')
  map_smul' c n := BalancedTensor.tmul_smul c _ (asInner Q ν ν' ν'' N n)

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem indMidUnit_apply (n : N) :
    indMidUnit N n =
      BalancedTensor.tmul (oneConcatSubBimod : IndBimod Q ν' ν'') (asInner Q ν ν' ν'' N n) :=
  rfl

theorem indMid_tmul_smul_unit (a : KLRAlgebra k Q ν) (u : B₂) (n : N) :
    ((a ⊗ₜ concat Q ν' ν'' u : TensorKLR Q ν (ν' + ν'')) • indMidUnit N n : IndMid Q ν ν' ν'' N) =
      indMidUnit N (((a ⊗ₜ u : B₃)) • n) := by
  rw [indMid_smul, indMidAction_tmul, indMidUnit_apply]
  have h := concat_smul_indShuffleUnit (Q := Q) (ν := ν') (ν' := ν'') N₂ u (asInner Q ν ν' ν'' N n)
  rw [indShuffleUnit, indShuffleUnit] at h
  rw [h, indHeadAction_tmul, indMidUnit_apply]
  congr 1
  change ((a ⊗ₜ (1 : B₂) : B₃) • ((1 : KLRAlgebra k Q ν) ⊗ₜ u : B₃) • n : N) = (a ⊗ₜ u : B₃) • n
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The inverse bilinear map `x ⊗ n ↦ x ⊗ (1_{ν',ν''} ⊗ n)`. -/
def indIterInvBil : IndBimod3 Q ν ν' ν'' →ₗ[k] N →ₗ[k] IndIter Q ν ν' ν'' N :=
  LinearMap.mk₂ k (fun x n => BalancedTensor.tmul (indBimod3Incl x) (indMidUnit N n))
    (fun x x' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c x n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun x n n' => by rw [map_add, BalancedTensor.tmul_add])
    (fun c x n => by rw [map_smul, BalancedTensor.tmul_smul])

/-- **The inverse comparison map** `Ind3 N → IndIter N`. -/
def indIterInv : Ind3 Q ν ν' ν'' N →ₗ[A₃] IndIter Q ν ν' ν'' N :=
  BalancedTensor.liftB (indIterInvBil N)
    (fun x t n => by
      change BalancedTensor.tmul (indBimod3Incl (op t • x)) (indMidUnit N n) =
        BalancedTensor.tmul (indBimod3Incl x) (indMidUnit N (t • n))
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' =>
        rw [op_add, add_smul, map_add, BalancedTensor.add_tmul, ht, ht', add_smul, map_add,
          BalancedTensor.tmul_add]
      | tmul a u =>
        have h : indBimod3Incl (op (a ⊗ₜ u : B₃) • x) =
            op (a ⊗ₜ concat Q ν' ν'' u : TensorKLR Q ν (ν' + ν'')) • indBimod3Incl x :=
          Subtype.ext (by rw [coe_op_smul, unop_op]; rfl)
        rw [h, BalancedTensor.op_smul_tmul, indMid_tmul_smul_unit])
    (fun b x n => by
      change BalancedTensor.tmul (indBimod3Incl (b • x)) _ = b • BalancedTensor.tmul _ _
      rw [BalancedTensor.smul_tmul']; rfl)

theorem indIterInv_tmul (x : IndBimod3 Q ν ν' ν'') (n : N) :
    indIterInv N (BalancedTensor.tmul x n) =
      BalancedTensor.tmul (indBimod3Incl x) (indMidUnit N n) := rfl

/-- **Associativity of KLR induction for three blocks**: iterated induction is one-step
induction along `ι₃`, as `R(ν + (ν' + ν''))`-modules. -/
def indIterEquiv : IndIter Q ν ν' ν'' N ≃ₗ[A₃] Ind3 Q ν ν' ν'' N :=
  LinearEquiv.ofLinearMap (indIterHom N) (indIterInv N)
    (BalancedTensor.extB fun x n => by
      rw [LinearMap.comp_apply, indIterInv_tmul, indIterHom_tmul, indMidUnit_apply,
        indIterInner_tmul, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (by
        rw [coe_indIterElt]
        change (x : A₃) * concat Q ν (ν' + ν'') (1 ⊗ₜ oneConcat Q ν' ν'') = x
        rw [← oneConcat3_eq]
        exact x.2))
    (BalancedTensor.extB fun m y => by
      rw [LinearMap.comp_apply, indIterHom_tmul, LinearMap.id_apply]
      induction y using BalancedTensor.induction_on with
      | zero =>
        change indIterInv N (indIterInner N m 0) = BalancedTensor.tmul m (0 : IndMid Q ν ν' ν'' N)
        rw [map_zero, map_zero, BalancedTensor.tmul_zero]
      | tmul m' n =>
        rw [indIterInner_tmul, indIterInv_tmul]
        have h : indBimod3Incl (indIterElt m m') =
            op ((1 : KLRAlgebra k Q ν) ⊗ₜ (m' : A₂) : TensorKLR Q ν (ν' + ν'')) • m :=
          Subtype.ext (by rw [coe_op_smul, unop_op]; rfl)
        rw [h, BalancedTensor.op_smul_tmul]
        congr 1
        rw [indMidUnit_apply, indMid_smul, indMidAction_tmul, map_one, Module.End.one_apply,
          BalancedTensor.smul_tmul']
        congr 1
        exact Subtype.ext m'.2
      | add x y hx hy =>
        change indIterInv N (indIterInner N m (x + y)) =
          BalancedTensor.tmul m ((x : IndMid Q ν ν' ν'' N) + y)
        rw [map_add, map_add, hx, hy, BalancedTensor.tmul_add])

end KLRAlgebra

end Categorification.KLR
