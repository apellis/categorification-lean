/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicProjective
import Categorification.Algebra.RightActionImage
import Categorification.Algebra.BalancedTensorSplit

/-!
# Kang–Kashiwara's split exact sequence as right modules, and its tensor products

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, **Theorem 4.5** and its proof: with
`ν = {i} + β`, the sequence
`0 → K_1 e(i, β) → K_0 e(β, i) → F^Λ e(β, i) → 0` (maps `P` and `π`) is exact and split as
a sequence of right `R(β)`-modules. Here:

* `rightAct0`, `rightAct1`, `rightActF`: the right actions of `R(β)` on `K_0`, `K_1`, `F^Λ`
  (right multiplication by `cL b`, `cR b`, `cL b`), and `K0E`, `K1E`, `FE'` their images
  (`RightAct.Image`), right `R(β)`-modules with a compatible left `R(ν)`-action.
* `pE`, `piE`, `splitE`: `P`, `π` and the splitting restricted to these images;
  `splitE_pE` (the splitting is a left inverse), `range_pE` (exactness), `piE_surjective`.
* `kkTensor_injective`, `kkTensor_exact`, `kkTensor_surjective`: for every left `R(β)`-module
  `N`, `0 → K_1 e ⊗ N → K_0 e ⊗ N → F^Λ e ⊗ N → 0` is exact, as left `R(ν)`-modules.

Hypotheses as in `projective_FE`: any commutative ring `k`, `KLRSymm Q`, `LeadUnitAt Q i`,
monic `a_i`, `β ≠ 0`.
-/

namespace Categorification.KLR

open MulOpposite Categorification.BalancedTensor

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "K0" => KZero Q (Si + β) a (zero_lt_card_single_add i β)

section Actions

theorem act0_add (u v : Rb) (z : K0) : act0 Q i β a (u + v) z = act0 Q i β a u z +
    act0 Q i β a v z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act0_mk, act0_mk, act0_mk, cL_add, mul_add, Submodule.Quotient.mk_add]

theorem act0_smul (r : k) (u : Rb) (z : K0) :
    act0 Q i β a (r • u) z = r • act0 Q i β a u z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act0_mk, act0_mk, cL_smul, mul_smul_comm]
  rfl

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

theorem act1_act1 (u v : Rb) (z : KOne Q (Si + β) a h1) :
    act1 Q i β a h1 u (act1 Q i β a h1 v z) = act1 Q i β a h1 (v * u) z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act1_mk, act1_mk, act1_mk, mul_assoc, cR_mul]

theorem act1_add (u v : Rb) (z : KOne Q (Si + β) a h1) :
    act1 Q i β a h1 (u + v) z = act1 Q i β a h1 u z + act1 Q i β a h1 v z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act1_mk, act1_mk, act1_mk, cR_add, mul_add, Submodule.Quotient.mk_add]

theorem act1_smul (r : k) (u : Rb) (z : KOne Q (Si + β) a h1) :
    act1 Q i β a h1 (r • u) z = r • act1 Q i β a h1 u z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [act1_mk, act1_mk, cR_smul, mul_smul_comm]
  rfl

variable (Q) in
/-- The right action of `R(β)` on `K_0` through `cL`. -/
noncomputable def rightAct0 : RightAct k R Rb K0 where
  act := act0 Q i β a
  act_act := act0_act0 i β a
  act_add := act0_add i β a
  act_smul := act0_smul i β a

variable (Q) in
/-- The right action of `R(β)` on `K_1` through `cR`. -/
noncomputable def rightAct1 : RightAct k R Rb (KOne Q (Si + β) a h1) where
  act := act1 Q i β a h1
  act_act := act1_act1 i β a h1
  act_add := act1_add i β a h1
  act_smul := act1_smul i β a h1

variable (Q) in
/-- The right action of `R(β)` on `F^Λ` through `cL`. -/
noncomputable def rightActF : RightAct k R Rb (FLam Q (Si + β) a) where
  act := actF Q i β a
  act_act := actF_actF i β a
  act_add := actF_add i β a
  act_smul := actF_smul i β a

variable (Q) in
/-- `K_0 e(β, i)`. -/
abbrev K0E : Type _ := (rightAct0 Q i β a).Image

variable (Q) in
/-- `K_1 e(i, β)`. -/
abbrev K1E : Type _ := (rightAct1 Q i β a h1).Image

variable (Q) in
/-- `F^Λ e(β, i)`, with its right `R(β)`-module structure. -/
abbrev FE' : Type _ := (rightActF Q i β a).Image

end Actions

section Maps

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

variable (Q) in
/-- `P : K_1 e(i, β) → K_0 e(β, i)`. -/
noncomputable def pE : K1E Q i β a h1 →ₗ[k] K0E Q i β a :=
  (rightAct1 Q i β a h1).mapImage
    ((pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
      (card_single_add i β).symm).restrictScalars k)
    (fun b z => pMap_act i β a h1 b z)

variable (Q) in
/-- `π : K_0 e(β, i) → F^Λ e(β, i)`. -/
noncomputable def piE : K0E Q i β a →ₗ[k] FE' Q i β a :=
  (rightAct0 Q i β a).mapImage
    ((piMap a (zero_lt_card_single_add i β)).restrictScalars k)
    (fun b z => piMap_act0 i β a b z)

theorem pE_op_smul (b : Rb) (z : K1E Q i β a h1) :
    pE Q i β a h1 (op b • z) = op b • pE Q i β a h1 z :=
  RightAct.mapImage_op_smul _ _ _ b z

theorem piE_op_smul (b : Rb) (z : K0E Q i β a) :
    piE Q i β a (op b • z) = op b • piE Q i β a z :=
  RightAct.mapImage_op_smul _ _ _ b z

theorem pE_smul (c : R) (z : K1E Q i β a h1) :
    pE Q i β a h1 (c • z) = c • pE Q i β a h1 z :=
  RightAct.mapImage_smul _ _ _
    (fun c x => (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
      (card_single_add i β).symm).map_smul c x) c z

theorem piE_smul (c : R) (z : K0E Q i β a) :
    piE Q i β a (c • z) = c • piE Q i β a z :=
  RightAct.mapImage_smul _ _ _
    (fun c x => (piMap (Q := Q) a (zero_lt_card_single_add i β)).map_smul c x) c z

theorem piE_surjective : Function.Surjective (piE Q i β a) := by
  rintro ⟨f, hf⟩
  obtain ⟨z, hz⟩ := piMap_surjective (Q := Q) a (zero_lt_card_single_add i β) f
  refine ⟨⟨act0 Q i β a 1 z, (rightAct0 Q i β a).act_mem 1 z⟩, ?_⟩
  ext
  show piMap a (zero_lt_card_single_add i β) (act0 Q i β a 1 z) = f
  rw [piMap_act0, hz]
  exact (rightActF Q i β a).act_one_of_mem hf

theorem range_pE {z : K0E Q i β a} (hz : piE Q i β a z = 0) :
    ∃ y, pE Q i β a h1 y = z := by
  have hz' : (z : K0) ∈ LinearMap.ker (piMap a (zero_lt_card_single_add i β)) :=
    congrArg Subtype.val hz
  rw [← range_pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
    (card_single_add i β).symm] at hz'
  obtain ⟨y, hy⟩ := hz'
  refine ⟨⟨act1 Q i β a h1 1 y, (rightAct1 Q i β a h1).act_mem 1 y⟩, ?_⟩
  ext
  show pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
      (card_single_add i β).symm (act1 Q i β a h1 1 y) = (z : K0)
  rw [pMap_act, hy]
  exact (rightAct0 Q i β a).act_one_of_mem z.2

theorem piE_pE (y : K1E Q i β a h1) : piE Q i β a (pE Q i β a h1 y) = 0 := by
  ext
  show piMap a (zero_lt_card_single_add i β)
    (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
      (y : KOne Q (Si + β) a h1)) = 0
  rw [← LinearMap.mem_ker, ← range_pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
    (card_single_add i β).symm]
  exact ⟨_, rfl⟩

variable (hsym : KLRSymm Q) (hQ : LeadUnitAt Q i) (ha : (a i).Monic)
  (hβ : 0 < Multiset.card β)

variable (Q) in
/-- The splitting `K_0 e(β, i) → K_1 e(i, β)` of `P`. -/
noncomputable def splitE : K0E Q i β a →ₗ[k] K1E Q i β a h1 :=
  (rightAct0 Q i β a).mapImage (splitMap Q i β a hsym hQ ha h1 hβ)
    (fun b z => splitMap_act i β a hsym hQ ha h1 hβ b z)

theorem splitE_op_smul (b : Rb) (z : K0E Q i β a) :
    splitE Q i β a h1 hsym hQ ha hβ (op b • z) = op b • splitE Q i β a h1 hsym hQ ha hβ z :=
  RightAct.mapImage_op_smul _ _ _ b z

/-- **KK Lemma 4.19**: the splitting is a left inverse of `P` on `K_1 e(i, β)`. -/
theorem splitE_pE (y : K1E Q i β a h1) :
    splitE Q i β a h1 hsym hQ ha hβ (pE Q i β a h1 y) = y := by
  obtain ⟨y, z, rfl⟩ := y
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  ext
  show splitMap Q i β a hsym hQ ha h1 hβ (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
      (card_single_add i β).symm
      (act1 Q i β a h1 1 _)) =
    act1 Q i β a h1 1 _
  rw [act1_mk, cR_one]
  exact splitMap_pMap i β a hsym hQ ha h1 hβ w

end Maps

section Tensor

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hsym : KLRSymm Q) (hQ : LeadUnitAt Q i)
  (ha : (a i).Monic) (hβ : 0 < Multiset.card β)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (KLRAlgebra k Q β) N]

include hsym hQ ha hβ in
/-- **`K_1 e(i, β) ⊗_{R(β)} N → K_0 e(β, i) ⊗_{R(β)} N` is injective.** -/
theorem kkTensor_injective :
    Function.Injective (mapLeft (A := Rb) R N (pE Q i β a h1) (pE_op_smul i β a h1)) :=
  mapLeft_injective_of_leftInverse _ _ _ (splitE_op_smul i β a h1 hsym hQ ha hβ)
    (splitE_pE i β a h1 hsym hQ ha hβ)

theorem kkTensor_surjective :
    Function.Surjective (mapLeft (A := Rb) R N (piE Q i β a) (piE_op_smul i β a)) :=
  mapLeft_surjective _ _ (piE_surjective i β a)

include hsym hQ ha hβ in
/-- **Exactness in the middle** of the tensored Kang–Kashiwara sequence. -/
theorem kkTensor_exact {x : BalancedTensor k R Rb (K0E Q i β a) N}
    (hx : mapLeft R N (piE Q i β a) (piE_op_smul i β a) x = 0) :
    ∃ y, mapLeft R N (pE Q i β a h1) (pE_op_smul i β a h1) y = x :=
  exists_mapLeft_eq_of_mapLeft_eq_zero _ _ _ (splitE_op_smul i β a h1 hsym hQ ha hβ)
    (splitE_pE i β a h1 hsym hQ ha hβ) _ _ (piE_surjective i β a)
    (fun _ hz => range_pE i β a h1 hz) hx

theorem kkTensor_comp (y : BalancedTensor k R Rb (K1E Q i β a h1) N) :
    mapLeft R N (piE Q i β a) (piE_op_smul i β a)
      (mapLeft R N (pE Q i β a h1) (pE_op_smul i β a h1) y) = 0 := by
  induction y using induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m n => rw [mapLeft_tmul, mapLeft_tmul, piE_pE, zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

end Tensor

end KLRAlgebra

end Categorification.KLR
