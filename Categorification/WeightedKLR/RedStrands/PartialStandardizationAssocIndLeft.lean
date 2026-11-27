/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorTransport
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocInd

/-!
# Associativity of KLR induction for three blocks, first two blocks first

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, induction `Ind_{ν,ν'}`, for modules over the
tensor product of three KLR algebras `(R(ν) ⊗ R(ν')) ⊗ R(ν'')`. Such a module `N` can be induced
in one step along `ι₃ᴸ = ι_{ν+ν',ν''} ∘ (ι_{ν,ν'} ⊗ id)` (`Ind3L`), or in two: first along
`ι_{ν,ν'}` from the first two factors, with `R(ν'')` acting by functoriality (`IndMidL`), then
along `ι_{ν+ν',ν''}` (`IndIterL`). The two agree (`indIterEquivL`), and the one-step induction
agrees with the one-step induction `Ind3` along `ι₃` of `PartialStandardizationAssocInd`
(`ind3LEquiv`), by associativity of concatenation. This is the input for the second order of
the cuts of an iterated partial standardization (Webster, arXiv:1309.3796v3, §5.1).

## Main definitions

* `KLRAlgebra.concat3L`, `KLRAlgebra.Ind3L`: one-step induction along `ι₃ᴸ`.
* `KLRAlgebra.IndMidL`, `KLRAlgebra.IndIterL`: the iterated induction.
* `KLRAlgebra.indIterEquivL`: `IndIterL N ≅ Ind3L N`, linear over `R((ν + ν') + ν'')`.
* `KLRAlgebra.ind3LEquiv`: `Ind3L N ≅ Ind3 N`, semilinear along `castKLR (add_assoc _ _ _)`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open MulOpposite Categorification.Stendhal

namespace KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (ν ν' ν'' : Multiset I)

/-- The tensor product of three KLR algebras, `(R(ν) ⊗ R(ν')) ⊗ R(ν'')`. -/
abbrev TensorKLR3L : Type _ := TensorKLR Q ν ν' ⊗[k] KLRAlgebra k Q ν''

/-- **The triple concatenation** `ι₃ᴸ = ι_{ν+ν',ν''} ∘ (ι_{ν,ν'} ⊗ id)`. -/
def concat3L : TensorKLR3L Q ν ν' ν'' →ₗ[k] KLRAlgebra k Q (ν + ν' + ν'') :=
  (concat Q (ν + ν') ν'').comp (TensorProduct.map (concat Q ν ν') LinearMap.id)

variable {Q ν ν' ν''}

theorem concat3L_tmul (u : TensorKLR Q ν ν') (d : KLRAlgebra k Q ν'') :
    concat3L Q ν ν' ν'' (u ⊗ₜ d) = concat Q (ν + ν') ν'' (concat Q ν ν' u ⊗ₜ d) := rfl

theorem concat3L_mul (s t : TensorKLR3L Q ν ν' ν'') :
    concat3L Q ν ν' ν'' (s * t) = concat3L Q ν ν' ν'' s * concat3L Q ν ν' ν'' t := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => rw [add_mul, map_add, map_add, hs, hs', add_mul]
  | tmul u d =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [mul_add, map_add, map_add, ht, ht', mul_add]
    | tmul v d' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, concat3L_tmul, concat3L_tmul, concat3L_tmul,
        concat_mul u v, ← concat_mul (concat Q ν ν' u ⊗ₜ d) (concat Q ν ν' v ⊗ₜ d'),
        Algebra.TensorProduct.tmul_mul_tmul]

variable (Q ν ν' ν'') in
/-- The idempotent `ι₃ᴸ(1)`. -/
abbrev oneConcat3L : KLRAlgebra k Q (ν + ν' + ν'') := concat3L Q ν ν' ν'' 1

theorem oneConcat3L_eq :
    oneConcat3L Q ν ν' ν'' = concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ 1) := by
  rw [oneConcat3L, Algebra.TensorProduct.one_def, concat3L_tmul, concat_one]

theorem concat3L_mul_oneConcat3L (t : TensorKLR3L Q ν ν' ν'') :
    concat3L Q ν ν' ν'' t * oneConcat3L Q ν ν' ν'' = concat3L Q ν ν' ν'' t := by
  rw [oneConcat3L, ← concat3L_mul, mul_one]

theorem oneConcat3L_mul_oneConcat :
    oneConcat3L Q ν ν' ν'' * oneConcat Q (ν + ν') ν'' = oneConcat3L Q ν ν' ν'' := by
  rw [oneConcat3L_eq, concat_mul_oneConcat]

/-! ### One-step induction along `ι₃ᴸ` -/

variable (Q ν ν' ν'') in
/-- The bimodule `R(ν + ν' + ν'') ι₃ᴸ(1)`. -/
abbrev IndBimod3L : Type _ := Graded.leftIdeal (oneConcat3L Q ν ν' ν'')

theorem mul_concat3L_mem (m : IndBimod3L Q ν ν' ν'') (t : TensorKLR3L Q ν ν' ν'') :
    (m : KLRAlgebra k Q (ν + ν' + ν'')) * concat3L Q ν ν' ν'' t ∈
      Graded.leftIdeal (oneConcat3L Q ν ν' ν'') := by
  rw [Graded.mem_leftIdeal, mul_assoc, concat3L_mul_oneConcat3L]

instance : SMul (TensorKLR3L Q ν ν' ν'')ᵐᵒᵖ (IndBimod3L Q ν ν' ν'') :=
  ⟨fun t m => ⟨m * concat3L Q ν ν' ν'' t.unop, mul_concat3L_mem m _⟩⟩

theorem coe_op_smul3L (t : (TensorKLR3L Q ν ν' ν'')ᵐᵒᵖ) (m : IndBimod3L Q ν ν' ν'') :
    ((t • m : IndBimod3L Q ν ν' ν'') : KLRAlgebra k Q (ν + ν' + ν'')) =
      m * concat3L Q ν ν' ν'' t.unop := rfl

instance : Module (TensorKLR3L Q ν ν' ν'')ᵐᵒᵖ (IndBimod3L Q ν ν' ν'') where
  one_smul m := Subtype.ext (by rw [coe_op_smul3L, unop_one]; exact m.2)
  mul_smul s t m := Subtype.ext (by simp only [coe_op_smul3L, unop_mul, concat3L_mul, mul_assoc])
  smul_zero t := Subtype.ext (by simp [coe_op_smul3L])
  smul_add t m m' := Subtype.ext (by simp [coe_op_smul3L, add_mul])
  add_smul s t m := Subtype.ext (by simp [coe_op_smul3L, mul_add])
  zero_smul m := Subtype.ext (by simp [coe_op_smul3L])

instance : IsScalarTower k (TensorKLR3L Q ν ν' ν'')ᵐᵒᵖ (IndBimod3L Q ν ν' ν'') where
  smul_assoc c t m := Subtype.ext (by
    change (m : KLRAlgebra k Q (ν + ν' + ν'')) * concat3L Q ν ν' ν'' (unop (c • t)) =
      c • ((m : KLRAlgebra k Q (ν + ν' + ν'')) * concat3L Q ν ν' ν'' t.unop)
    rw [unop_smul, map_smul, mul_smul_comm])

instance : SMulCommClass (KLRAlgebra k Q (ν + ν' + ν'')) (TensorKLR3L Q ν ν' ν'')ᵐᵒᵖ
    (IndBimod3L Q ν ν' ν'') where
  smul_comm r t m := Subtype.ext (by
    rw [coe_op_smul3L, Submodule.coe_smul, Submodule.coe_smul, coe_op_smul3L, smul_eq_mul,
      smul_eq_mul, mul_assoc])

variable (Q ν ν' ν'') in
/-- **One-step induction along `ι₃ᴸ`**. -/
abbrev Ind3L (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR3L Q ν ν' ν'') N] :
    Type _ :=
  BalancedTensor k (KLRAlgebra k Q (ν + ν' + ν'')) (TensorKLR3L Q ν ν' ν'')
    (IndBimod3L Q ν ν' ν'') N

/-! ### Induction from the first two factors -/

section Iter

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR3L Q ν ν' ν'') N]
  [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N]

variable (Q ν ν' ν'') in
/-- A module over the three factors, as a module over the first two. -/
@[nolint unusedArguments]
def IndInnerInputL (_Q : I → I → MvPolynomial (Fin 2) k) (_ν _ν' _ν'' : Multiset I) (N : Type*)
    [AddCommGroup N] [Module k N] [Module (TensorKLR3L _Q _ν _ν' _ν'') N] : Type _ := N

local notation "N₂" => IndInnerInputL Q ν ν' ν'' N
local notation "B₃" => TensorKLR3L Q ν ν' ν''
local notation "B₂" => TensorKLR Q ν ν'

instance : AddCommGroup N₂ := inferInstanceAs (AddCommGroup N)
instance : Module k N₂ := inferInstanceAs (Module k N)
instance : Module B₃ N₂ := inferInstanceAs (Module B₃ N)
instance : Module B₂ N₂ :=
  Module.compHom N (Algebra.TensorProduct.includeLeft : B₂ →ₐ[k] B₃).toRingHom

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indInnerInputL_smul (u : B₂) (n : N₂) :
    u • n = (u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • (n : N) := rfl

instance : IsScalarTower k B₂ N₂ where
  smul_assoc c u n := by
    rw [indInnerInputL_smul, indInnerInputL_smul, ← TensorProduct.smul_tmul']
    exact smul_assoc c (u ⊗ₜ[k] (1 : KLRAlgebra k Q ν'') : B₃) (show N from n)

/-- The action of `d ∈ R(ν'')` on `N`, linear over the first two factors. -/
def indTailEnd (d : KLRAlgebra k Q ν'') : N₂ →ₗ[B₂] N₂ where
  toFun n := (((1 : B₂) ⊗ₜ d : B₃) • (n : N) : N)
  map_add' := smul_add _
  map_smul' u n := by
    change ((1 : B₂) ⊗ₜ d : B₃) • ((u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • (n : N)) =
      (u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • (((1 : B₂) ⊗ₜ d : B₃) • (n : N))
    rw [← mul_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul, mul_one]

local notation "A₂" => KLRAlgebra k Q (ν + ν')

variable (Q ν ν' ν'') in
/-- **Induction from the first two factors**, `R(ν+ν') 1_{ν,ν'} ⊗ N`. -/
abbrev IndInnerL : Type _ := Ind Q ν ν' (IndInnerInputL Q ν ν' ν'' N)

/-- The action of `R(ν'')` on the inner induction, by functoriality. -/
def indTailAction : KLRAlgebra k Q ν'' →ₐ[k] Module.End k (IndInnerL Q ν ν' ν'' N) where
  toFun d := (BalancedTensor.mapRight (k := k) (B := A₂) (indTailEnd N d)).restrictScalars k
  map_one' := BalancedTensor.ext fun m n => by
    change BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • (n : N)) : N₂) =
      BalancedTensor.tmul m n
    rw [← Algebra.TensorProduct.one_def, one_smul]
  map_mul' d d' := BalancedTensor.ext fun m n => by
    change BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ (d * d') : B₃) • (n : N)) : N₂) =
      BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ d : B₃) • ((1 : B₂) ⊗ₜ d' : B₃) • (n : N)) : N₂)
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := BalancedTensor.ext fun m n => by
    change BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ (0 : KLRAlgebra k Q ν'') : B₃) • (n : N)) : N₂) =
      0
    have h : (((((1 : B₂) ⊗ₜ (0 : KLRAlgebra k Q ν'')) : B₃) • (n : N) : N) : N₂) =
        0 := by
      rw [TensorProduct.tmul_zero]
      exact zero_smul B₃ (n : N)
    exact (congrArg (BalancedTensor.tmul (k := k) (B := A₂) (A := B₂) (N := N₂) m) h).trans
      (BalancedTensor.tmul_zero _)
  map_add' d d' := BalancedTensor.ext fun m n => by
    change BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ (d + d') : B₃) • (n : N)) : N₂) =
      BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ d : B₃) • (n : N)) : N₂) +
        BalancedTensor.tmul m ((((1 : B₂) ⊗ₜ d' : B₃) • (n : N)) : N₂)
    rw [TensorProduct.tmul_add, add_smul, BalancedTensor.tmul_add]
  commutes' c := BalancedTensor.ext fun m n => by
    rw [Module.algebraMap_end_apply]
    have h : (((((1 : B₂) ⊗ₜ (algebraMap k (KLRAlgebra k Q ν'') c)) : B₃) •
        (show N from n) : N) : N₂) = c • n := by
      change _ = c • (show N from n)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, smul_assoc,
        ← Algebra.TensorProduct.one_def, one_smul]
    exact (congrArg (BalancedTensor.tmul (k := k) (B := A₂) (A := B₂) (N := N₂) m) h).trans
      (BalancedTensor.tmul_smul c m n)

theorem indTailAction_tmul (d : KLRAlgebra k Q ν'') (m : IndBimod Q ν ν') (n : N₂) :
    indTailAction N d (BalancedTensor.tmul m n : IndInnerL Q ν ν' ν'' N) =
      BalancedTensor.tmul m (((1 : B₂) ⊗ₜ d : B₃) • (n : N) : N) := rfl

/-- The action of `R(ν'')` commutes with the action of `R(ν + ν')`. -/
theorem commute_indTailAction (z : A₂) (d : KLRAlgebra k Q ν'') :
    Commute (Algebra.lsmul k k (IndInnerL Q ν ν' ν'' N) z) (indTailAction N d) :=
  LinearMap.ext fun y =>
    ((BalancedTensor.mapRight (k := k) (B := A₂) (indTailEnd N d)).map_smul z y).symm

/-- The action of `R(ν + ν') ⊗ R(ν'')` on the inner induction. -/
def indMidActionL :
    TensorKLR Q (ν + ν') ν'' →ₐ[k] Module.End k (IndInnerL Q ν ν' ν'' N) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k (IndInnerL Q ν ν' ν'' N)) (indTailAction N)
    (fun z d => commute_indTailAction N z d)

theorem indMidActionL_tmul (z : A₂) (d : KLRAlgebra k Q ν'') (y : IndInnerL Q ν ν' ν'' N) :
    indMidActionL N (z ⊗ₜ d) y = z • indTailAction N d y := rfl

variable (Q ν ν' ν'') in
/-- **The inner induction**, as a module over `R(ν + ν') ⊗ R(ν'')`. -/
abbrev IndMidL : Type _ := IndInnerL Q ν ν' ν'' N

instance : Module (TensorKLR Q (ν + ν') ν'') (IndMidL Q ν ν' ν'' N) :=
  Module.compHom (IndInnerL Q ν ν' ν'' N) (indMidActionL N).toRingHom

theorem indMidL_smul (s : TensorKLR Q (ν + ν') ν'') (y : IndMidL Q ν ν' ν'' N) :
    s • y = indMidActionL N s y := rfl

instance : IsScalarTower k (TensorKLR Q (ν + ν') ν'') (IndMidL Q ν ν' ν'' N) where
  smul_assoc c s y := by
    rw [indMidL_smul, indMidL_smul, map_smul]
    rfl

variable (Q ν ν' ν'') in
/-- **Iterated induction**: induction along `ι_{ν+ν',ν''}` of the inner induction. -/
abbrev IndIterL : Type _ := Ind Q (ν + ν') ν'' (IndMidL Q ν ν' ν'' N)

/-! ### The comparison -/

local notation "A₃" => KLRAlgebra k Q (ν + ν' + ν'')

/-- The element `m · ι_{ν+ν',ν''}(m' ⊗ 1)` of `R(ν + ν' + ν'') ι₃ᴸ(1)`. -/
def indIterEltL (m : IndBimod Q (ν + ν') ν'') : IndBimod Q ν ν' →ₗ[k] IndBimod3L Q ν ν' ν'' where
  toFun m' := ⟨(m : A₃) * concat Q (ν + ν') ν'' ((m' : A₂) ⊗ₜ 1), by
    rw [Graded.mem_leftIdeal, oneConcat3L_eq, mul_assoc, ← concat_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, m'.2]⟩
  map_add' m' m'' := Subtype.ext (by
    simp only [Submodule.coe_add, TensorProduct.add_tmul, map_add, mul_add])
  map_smul' c m' := Subtype.ext (by
    simp only [Submodule.coe_smul_of_tower, ← TensorProduct.smul_tmul', map_smul,
      mul_smul_comm, RingHom.id_apply])

theorem coe_indIterEltL (m : IndBimod Q (ν + ν') ν'') (m' : IndBimod Q ν ν') :
    ((indIterEltL m m' : IndBimod3L Q ν ν' ν'') : A₃) =
      (m : A₃) * concat Q (ν + ν') ν'' ((m' : A₂) ⊗ₜ 1) := rfl

/-- The inner bilinear map `m' ⊗ n ↦ (m · ι(m' ⊗ 1)) ⊗ n`. -/
def indIterInnerBilL (m : IndBimod Q (ν + ν') ν'') :
    IndBimod Q ν ν' →ₗ[k] N₂ →ₗ[k] Ind3L Q ν ν' ν'' N :=
  LinearMap.mk₂ k (fun m' n => BalancedTensor.tmul (indIterEltL m m') (show N from n))
    (fun m' m'' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c m' n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun m' n n' => BalancedTensor.tmul_add _ _ _)
    (fun c m' n => BalancedTensor.tmul_smul _ _ _)

/-- The map from the inner induction for a fixed outer coefficient `m`. -/
def indIterInnerL (m : IndBimod Q (ν + ν') ν'') :
    IndInnerL Q ν ν' ν'' N →ₗ[k] Ind3L Q ν ν' ν'' N :=
  BalancedTensor.lift (indIterInnerBilL N m) (fun m' u n => by
    change (BalancedTensor.tmul (indIterEltL m (op u • m')) (show N from n) :
        Ind3L Q ν ν' ν'' N) =
      BalancedTensor.tmul (indIterEltL m m') ((u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • (n : N))
    have h : indIterEltL m (op u • m') =
        op (u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • indIterEltL m m' :=
      Subtype.ext (by
        rw [coe_op_smul3L, coe_indIterEltL, coe_indIterEltL, coe_op_smul]
        simp only [unop_op]
        rw [concat3L_tmul, mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul])
    rw [h, BalancedTensor.op_smul_tmul]
    rfl)

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indIterInnerL_tmul (m : IndBimod Q (ν + ν') ν'') (m' : IndBimod Q ν ν') (n : N₂) :
    indIterInnerL N m (BalancedTensor.tmul m' n) =
      BalancedTensor.tmul (indIterEltL m m') (show N from n) := rfl

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indIterInnerL_add (m m₂ : IndBimod Q (ν + ν') ν'') :
    indIterInnerL N (m + m₂) = indIterInnerL N m + indIterInnerL N m₂ :=
  BalancedTensor.ext fun m' n => by
    change (BalancedTensor.tmul (indIterEltL (m + m₂) m') (show N from n) :
        Ind3L Q ν ν' ν'' N) =
      BalancedTensor.tmul (indIterEltL m m') (show N from n) +
        BalancedTensor.tmul (indIterEltL m₂ m') (show N from n)
    rw [← BalancedTensor.add_tmul]
    congr 1
    exact Subtype.ext (by simp only [coe_indIterEltL, Submodule.coe_add, add_mul])

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indIterInnerL_smul (b : A₃) (m : IndBimod Q (ν + ν') ν'')
    (y : IndInnerL Q ν ν' ν'' N) : indIterInnerL N (b • m) y = b • indIterInnerL N m y := by
  induction y using BalancedTensor.induction_on with
  | zero => simp
  | tmul m' n =>
    rw [indIterInnerL_tmul, indIterInnerL_tmul, BalancedTensor.smul_tmul']
    congr 1
    exact Subtype.ext (by simp only [coe_indIterEltL, Submodule.coe_smul, smul_eq_mul, mul_assoc])
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indIterInnerL_smul_k (c : k) (m : IndBimod Q (ν + ν') ν'') :
    indIterInnerL N (c • m) = c • indIterInnerL N m :=
  BalancedTensor.ext fun m' n => by
    change (BalancedTensor.tmul (indIterEltL (c • m) m') (show N from n) :
        Ind3L Q ν ν' ν'' N) =
      c • (BalancedTensor.tmul (indIterEltL m m') (show N from n) : Ind3L Q ν ν' ν'' N)
    rw [← BalancedTensor.smul_tmul]
    congr 1
    exact Subtype.ext (by
      simp only [coe_indIterEltL, Submodule.coe_smul_of_tower, smul_mul_assoc])

/-- The outer balancing of the comparison map. -/
theorem indIterInnerL_balanced (m : IndBimod Q (ν + ν') ν'') (s : TensorKLR Q (ν + ν') ν'')
    (y : IndInnerL Q ν ν' ν'' N) :
    indIterInnerL N (op s • m) y = indIterInnerL N m (indMidActionL N s y) := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' =>
    rw [op_add, add_smul, indIterInnerL_add, LinearMap.add_apply, hs, hs', map_add,
      LinearMap.add_apply, map_add]
  | tmul z d =>
    induction y using BalancedTensor.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul m' n =>
      rw [indMidActionL_tmul, indTailAction_tmul, BalancedTensor.smul_tmul', indIterInnerL_tmul,
        indIterInnerL_tmul]
      have h : indIterEltL (op (z ⊗ₜ d) • m) m' =
          op ((1 : B₂) ⊗ₜ d : B₃) • indIterEltL m (z • m') := Subtype.ext (by
        rw [coe_op_smul3L, coe_indIterEltL, coe_indIterEltL, coe_op_smul]
        simp only [unop_op]
        rw [concat3L_tmul, concat_one, Submodule.coe_smul, smul_eq_mul, mul_assoc, mul_assoc,
          ← concat_mul, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_assoc, m'.2])
      rw [h, BalancedTensor.op_smul_tmul]
      rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- **The comparison map** `IndIterL N → Ind3L N`. -/
def indIterHomL : IndIterL Q ν ν' ν'' N →ₗ[A₃] Ind3L Q ν ν' ν'' N :=
  BalancedTensor.liftB
    { toFun := fun m => indIterInnerL N m
      map_add' := indIterInnerL_add N
      map_smul' := indIterInnerL_smul_k N }
    (fun m s y => indIterInnerL_balanced N m s y)
    (fun b m y => indIterInnerL_smul N b m y)

theorem indIterHomL_tmul (m : IndBimod Q (ν + ν') ν'') (y : IndMidL Q ν ν' ν'' N) :
    indIterHomL N (BalancedTensor.tmul m y) = indIterInnerL N m y := rfl

/-- An element of `R(ν + ν' + ν'') ι₃ᴸ(1)` lies in `R(ν + ν' + ν'') 1_{ν+ν',ν''}`. -/
def indBimod3InclL : IndBimod3L Q ν ν' ν'' →ₗ[k] IndBimod Q (ν + ν') ν'' where
  toFun x := ⟨x, by
    have hx : (x : A₃) * oneConcat3L Q ν ν' ν'' = x := x.2
    have h2 : (x : A₃) * oneConcat Q (ν + ν') ν'' =
        (x : A₃) * oneConcat3L Q ν ν' ν'' * oneConcat Q (ν + ν') ν'' := by rw [hx]
    rw [Graded.mem_leftIdeal, h2, mul_assoc, oneConcat3L_mul_oneConcat, hx]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (Q ν ν' ν'') in
/-- `n ∈ N` viewed in the module over the first two factors. -/
abbrev asInnerL (n : N) : N₂ := n

/-- The identity-shuffle copy of `n` in the inner induction. -/
def indMidUnitL : N →ₗ[k] IndMidL Q ν ν' ν'' N where
  toFun n := BalancedTensor.tmul (oneConcatSubBimod : IndBimod Q ν ν') (asInnerL Q ν ν' ν'' N n)
  map_add' n n' :=
    BalancedTensor.tmul_add _ (asInnerL Q ν ν' ν'' N n) (asInnerL Q ν ν' ν'' N n')
  map_smul' c n := BalancedTensor.tmul_smul c _ (asInnerL Q ν ν' ν'' N n)

omit [IsScalarTower k (TensorKLR3L Q ν ν' ν'') N] in
theorem indMidUnitL_apply (n : N) :
    indMidUnitL N n =
      BalancedTensor.tmul (oneConcatSubBimod : IndBimod Q ν ν') (asInnerL Q ν ν' ν'' N n) :=
  rfl

theorem indMidL_tmul_smul_unit (u : B₂) (d : KLRAlgebra k Q ν'') (n : N) :
    ((concat Q ν ν' u ⊗ₜ d : TensorKLR Q (ν + ν') ν'') • indMidUnitL N n :
        IndMidL Q ν ν' ν'' N) = indMidUnitL N (((u ⊗ₜ d : B₃)) • n) := by
  rw [indMidL_smul, indMidActionL_tmul, indMidUnitL_apply, indTailAction_tmul]
  have h := concat_smul_indShuffleUnit (Q := Q) (ν := ν) (ν' := ν') N₂ u
    (show N₂ from (((1 : B₂) ⊗ₜ d : B₃) • (asInnerL Q ν ν' ν'' N n : N) : N))
  rw [indShuffleUnit, indShuffleUnit] at h
  rw [h, indMidUnitL_apply]
  congr 1
  change ((u ⊗ₜ (1 : KLRAlgebra k Q ν'') : B₃) • ((1 : B₂) ⊗ₜ d : B₃) • n : N) =
    (u ⊗ₜ d : B₃) • n
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The inverse bilinear map `x ⊗ n ↦ x ⊗ (1_{ν,ν'} ⊗ n)`. -/
def indIterInvBilL : IndBimod3L Q ν ν' ν'' →ₗ[k] N →ₗ[k] IndIterL Q ν ν' ν'' N :=
  LinearMap.mk₂ k (fun x n => BalancedTensor.tmul (indBimod3InclL x) (indMidUnitL N n))
    (fun x x' n => by rw [map_add, BalancedTensor.add_tmul])
    (fun c x n => by rw [map_smul, BalancedTensor.smul_tmul])
    (fun x n n' => by rw [map_add, BalancedTensor.tmul_add])
    (fun c x n => by rw [map_smul, BalancedTensor.tmul_smul])

/-- **The inverse comparison map** `Ind3L N → IndIterL N`. -/
def indIterInvL : Ind3L Q ν ν' ν'' N →ₗ[A₃] IndIterL Q ν ν' ν'' N :=
  BalancedTensor.liftB (indIterInvBilL N)
    (fun x t n => by
      change BalancedTensor.tmul (indBimod3InclL (op t • x)) (indMidUnitL N n) =
        BalancedTensor.tmul (indBimod3InclL x) (indMidUnitL N (t • n))
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' =>
        rw [op_add, add_smul, map_add, BalancedTensor.add_tmul, ht, ht', add_smul, map_add,
          BalancedTensor.tmul_add]
      | tmul u d =>
        have h : indBimod3InclL (op (u ⊗ₜ d : B₃) • x) =
            op (concat Q ν ν' u ⊗ₜ d : TensorKLR Q (ν + ν') ν'') • indBimod3InclL x :=
          Subtype.ext (by rw [coe_op_smul, unop_op]; rfl)
        rw [h, BalancedTensor.op_smul_tmul, indMidL_tmul_smul_unit])
    (fun b x n => by
      change BalancedTensor.tmul (indBimod3InclL (b • x)) _ = b • BalancedTensor.tmul _ _
      rw [BalancedTensor.smul_tmul']; rfl)

theorem indIterInvL_tmul (x : IndBimod3L Q ν ν' ν'') (n : N) :
    indIterInvL N (BalancedTensor.tmul x n) =
      BalancedTensor.tmul (indBimod3InclL x) (indMidUnitL N n) := rfl

/-- **Associativity of KLR induction for three blocks, first two blocks first**: iterated
induction is one-step induction along `ι₃ᴸ`, as `R(ν + ν' + ν'')`-modules. -/
def indIterEquivL : IndIterL Q ν ν' ν'' N ≃ₗ[A₃] Ind3L Q ν ν' ν'' N :=
  LinearEquiv.ofLinearMap (indIterHomL N) (indIterInvL N)
    (BalancedTensor.extB fun x n => by
      rw [LinearMap.comp_apply, indIterInvL_tmul, indIterHomL_tmul, indMidUnitL_apply,
        indIterInnerL_tmul, LinearMap.id_apply]
      congr 1
      exact Subtype.ext (by
        rw [coe_indIterEltL]
        change (x : A₃) * concat Q (ν + ν') ν'' (oneConcat Q ν ν' ⊗ₜ 1) = x
        rw [← oneConcat3L_eq]
        exact x.2))
    (BalancedTensor.extB fun m y => by
      rw [LinearMap.comp_apply, indIterHomL_tmul, LinearMap.id_apply]
      induction y using BalancedTensor.induction_on with
      | zero =>
        change indIterInvL N (indIterInnerL N m 0) =
          BalancedTensor.tmul m (0 : IndMidL Q ν ν' ν'' N)
        rw [map_zero, map_zero, BalancedTensor.tmul_zero]
      | tmul m' n =>
        rw [indIterInnerL_tmul, indIterInvL_tmul]
        have h : indBimod3InclL (indIterEltL m m') =
            op ((m' : A₂) ⊗ₜ (1 : KLRAlgebra k Q ν'') : TensorKLR Q (ν + ν') ν'') • m :=
          Subtype.ext (by rw [coe_op_smul, unop_op]; rfl)
        rw [h, BalancedTensor.op_smul_tmul]
        congr 1
        rw [indMidUnitL_apply, indMidL_smul, indMidActionL_tmul, map_one, Module.End.one_apply,
          BalancedTensor.smul_tmul']
        congr 1
        exact Subtype.ext m'.2
      | add x y hx hy =>
        change indIterInvL N (indIterInnerL N m (x + y)) =
          BalancedTensor.tmul m ((x : IndMidL Q ν ν' ν'' N) + y)
        rw [map_add, map_add, hx, hy, BalancedTensor.tmul_add])

end Iter

/-! ### The two one-step inductions agree -/

section Reassoc

/-- The two triple concatenations agree, by associativity of concatenation. -/
theorem castKLR_concat3L (t : TensorKLR3L Q ν ν' ν'') :
    castKLR Q (add_assoc ν ν' ν'') (concat3L Q ν ν' ν'' t) =
      concat3 Q ν ν' ν'' (Algebra.TensorProduct.assoc k k k _ _ _ t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  | tmul u d =>
    induction u using TensorProduct.inductionOn with
    | add u u' hu hu' =>
      rw [TensorProduct.add_tmul, map_add, map_add, hu, hu', map_add, map_add]
    | tmul a b =>
      rw [concat3L_tmul, concat_tmul, ← concat_tmul, concat_assoc]
      rfl

theorem castKLR_oneConcat3L :
    castKLR Q (add_assoc ν ν' ν'') (oneConcat3L Q ν ν' ν'') = oneConcat3 Q ν ν' ν'' := by
  rw [oneConcat3L, castKLR_concat3L, map_one]

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR3 Q ν ν' ν'') N]
  [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N]

/-- A module over `R(ν) ⊗ (R(ν') ⊗ R(ν''))`, as a module over `(R(ν) ⊗ R(ν')) ⊗ R(ν'')`. -/
@[nolint unusedArguments]
def ReassocInput (_Q : I → I → MvPolynomial (Fin 2) k) (_ν _ν' _ν'' : Multiset I) (N : Type*) :
    Type _ := N

local notation "Nₗ" => ReassocInput Q ν ν' ν'' N

instance : AddCommGroup Nₗ := inferInstanceAs (AddCommGroup N)
instance : Module k Nₗ := inferInstanceAs (Module k N)
instance : Module (TensorKLR3L Q ν ν' ν'') Nₗ :=
  Module.compHom N (Algebra.TensorProduct.assoc k k k (KLRAlgebra k Q ν) (KLRAlgebra k Q ν')
    (KLRAlgebra k Q ν'')).toAlgHom.toRingHom

omit [Module k N] [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem reassocInput_smul (t : TensorKLR3L Q ν ν' ν'') (n : Nₗ) :
    t • n = Algebra.TensorProduct.assoc k k k _ _ _ t • (show N from n) := rfl

instance : IsScalarTower k (TensorKLR3L Q ν ν' ν'') Nₗ where
  smul_assoc c t n := by
    rw [reassocInput_smul, reassocInput_smul, map_smul]
    exact smul_assoc c _ (show N from n)

/-- The bimodule isomorphism `R(ν+ν'+ν'') ι₃ᴸ(1) ≃ R(ν+(ν'+ν'')) ι₃(1)`. -/
def bimod3Reassoc : IndBimod3L Q ν ν' ν'' ≃ₗ[k] IndBimod3 Q ν ν' ν'' where
  toFun m := ⟨castKLR Q (add_assoc ν ν' ν'') (m : KLRAlgebra k Q (ν + ν' + ν'')), by
    change _ * oneConcat3 Q ν ν' ν'' = _
    rw [← castKLR_oneConcat3L, ← map_mul, m.2]⟩
  invFun m := ⟨(castKLR Q (add_assoc ν ν' ν'')).symm (m : KLRAlgebra k Q (ν + (ν' + ν''))), by
    change _ * oneConcat3L Q ν ν' ν'' = _
    rw [← (castKLR Q (add_assoc ν ν' ν'')).symm_apply_apply (oneConcat3L Q ν ν' ν''),
      castKLR_oneConcat3L, ← map_mul, m.2]⟩
  map_add' m m' := Subtype.ext (map_add _ (m : KLRAlgebra k Q (ν + ν' + ν'')) m')
  map_smul' c m := Subtype.ext (map_smul _ c (m : KLRAlgebra k Q (ν + ν' + ν'')))
  left_inv m := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv m := Subtype.ext (AlgEquiv.apply_symm_apply _ _)

theorem bimod3Reassoc_op_smul (t : TensorKLR3L Q ν ν' ν'') (m : IndBimod3L Q ν ν' ν'') :
    bimod3Reassoc (op t • m) =
      op (Algebra.TensorProduct.assoc k k k _ _ _ t) • bimod3Reassoc m :=
  Subtype.ext (by
    change castKLR Q _ ((m : KLRAlgebra k Q (ν + ν' + ν'')) * concat3L Q ν ν' ν'' t) =
      castKLR Q _ (m : KLRAlgebra k Q (ν + ν' + ν'')) * concat3 Q ν ν' ν'' _
    rw [map_mul, castKLR_concat3L]
    rfl)

theorem bimod3Reassoc_smul (a : KLRAlgebra k Q (ν + ν' + ν'')) (m : IndBimod3L Q ν ν' ν'') :
    bimod3Reassoc (a • m) = castKLR Q (add_assoc ν ν' ν'') a • bimod3Reassoc m :=
  Subtype.ext (map_mul _ a (m : KLRAlgebra k Q (ν + ν' + ν'')))

/-- **The two one-step inductions agree**: `Ind3L N ≅ Ind3 N`, semilinear along
`castKLR (add_assoc _ _ _)`. -/
def ind3LEquiv : Ind3L Q ν ν' ν'' Nₗ ≃ₗ[k] Ind3 Q ν ν' ν'' N :=
  BalancedTensor.changeRingEquiv
    (Algebra.TensorProduct.assoc k k k (KLRAlgebra k Q ν) (KLRAlgebra k Q ν')
      (KLRAlgebra k Q ν'')).toRingEquiv
    bimod3Reassoc (LinearEquiv.refl k N) bimod3Reassoc_op_smul (fun _ _ => rfl)

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem ind3LEquiv_tmul (m : IndBimod3L Q ν ν' ν'') (n : Nₗ) :
    ind3LEquiv N (BalancedTensor.tmul m n) =
      BalancedTensor.tmul (bimod3Reassoc m) (show N from n) := rfl

omit [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] in
theorem ind3LEquiv_smul (a : KLRAlgebra k Q (ν + ν' + ν'')) (y : Ind3L Q ν ν' ν'' Nₗ) :
    ind3LEquiv N (a • y) = castKLR Q (add_assoc ν ν' ν'') a • ind3LEquiv N y :=
  BalancedTensor.changeRingEquiv_smul _ _ _ _ _ (castKLR Q (add_assoc ν ν' ν'')).toRingEquiv
    bimod3Reassoc_smul a y

end Reassoc

end KLRAlgebra

end Categorification.KLR
