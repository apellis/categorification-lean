/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockBlackRes
import Categorification.WeightedKLR.RedStrands.BlockAlgebraCast
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebra
import Categorification.Algebra.PiTensorProductNonUnitalExt

/-!
# The map of block algebras behind `ₖEᵢ` on generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
functors `ₖEᵢ` before Proposition 5.5. The nonunital map of block algebras `B(b') → B(b)` along
which `ₖEᵢ` restricts is computed on the generators `a ⊗ 1` and the single factors
(`blockBlackRes_tmul_one`, `blockBlackRes_single_self`, `blockBlackRes_single_of_ne`); it is the
identity, up to casts, times the idempotent `e = blockBlackRes 1` away from the factor `κ`.
For `ℓ + 1` red strands this compares `ₖEᵢ` with the restriction to the first `ℓ` red strands
and with the last factor (`blockBlackRes_initBlockAlgHom_last`,
`initBlockAlgHom_blockBlackRes_castSucc`, `blockBlackRes_lastBlockAlgHom_last`,
`blockBlackRes_lastBlockAlgHom_castSucc`), as used in the induction on the number of red strands
in the proof of Proposition 5.5.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (κ : Fin ℓ)
  {b b' : Fin (ℓ + 1) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ = rightBlock b κ)

local notation "Fac" => fun r : Fin ℓ => CycKLR k Q (redCyc Λ r) (rightBlock b r)
local notation "Fac'" => fun r : Fin ℓ => CycKLR k Q (redCyc Λ r) (rightBlock b' r)
local notation "sg" => PiTensorProduct.singleAlgHom (R := k) (A := Fac)
local notation "sg'" => PiTensorProduct.singleAlgHom (R := k) (A := Fac')

theorem blockFactorRes_of_ne {r : Fin ℓ} (h : r ≠ κ)
    (c : CycKLR k Q (redCyc Λ r) (rightBlock b' r)) :
    blockFactorRes Q Λ i κ hr hκ r c = CyclotomicAction.castCyc Q (redCyc Λ r) (hr r h) c := by
  rw [blockFactorRes, dite_eq_right_of_eq_false (eq_false h)]
  rfl

theorem blockFactorRes_self (c : CycKLR k Q (redCyc Λ κ) (rightBlock b' κ)) :
    blockFactorRes Q Λ i κ hr hκ κ c = CyclotomicAction.castCyc Q (redCyc Λ κ) hκ
      (AbsentColour.cyclotomicLast Q i (redCyc Λ κ) (rightBlock b' κ) c) := by
  rw [blockFactorRes, dite_eq_left_of_eq_true (eq_true rfl)]
  rfl

theorem blockFactorRes_one_of_ne (r : Fin ℓ) (h : r ≠ κ) :
    blockFactorRes Q Λ i κ hr hκ r 1 = 1 := by
  rw [blockFactorRes_of_ne Q Λ i κ hr hκ h, map_one]

theorem blockBlackRes_tmul (a : KLRAlgebra k Q (leftBlock b'))
    (y : ⨂[k] r : Fin ℓ, CycKLR k Q (redCyc Λ r) (rightBlock b' r)) :
    blockBlackRes Q Λ i κ h0 hr hκ (a ⊗ₜ y) =
      castKLR Q h0 a ⊗ₜ PiTensorProduct.nonUnitalMap (blockFactorRes Q Λ i κ hr hκ) y := rfl

/-- The idempotent `e = blockBlackRes 1`. -/
theorem blockBlackRes_one :
    blockBlackRes Q Λ i κ h0 hr hκ 1 = 1 ⊗ₜ sg κ (blockFactorRes Q Λ i κ hr hκ κ 1) := by
  rw [Algebra.TensorProduct.one_def, blockBlackRes_tmul, map_one,
    PiTensorProduct.nonUnitalMap_one_of_ne _ κ (blockFactorRes_one_of_ne Q Λ i κ hr hκ)]

theorem blockBlackRes_tmul_one (a : KLRAlgebra k Q (leftBlock b')) :
    blockBlackRes Q Λ i κ h0 hr hκ (a ⊗ₜ 1) =
      castKLR Q h0 a ⊗ₜ sg κ (blockFactorRes Q Λ i κ hr hκ κ 1) := by
  rw [blockBlackRes_tmul,
    PiTensorProduct.nonUnitalMap_one_of_ne _ κ (blockFactorRes_one_of_ne Q Λ i κ hr hκ)]

theorem blockBlackRes_single_self (c : CycKLR k Q (redCyc Λ κ) (rightBlock b' κ)) :
    blockBlackRes Q Λ i κ h0 hr hκ (1 ⊗ₜ sg' κ c) =
      1 ⊗ₜ sg κ (blockFactorRes Q Λ i κ hr hκ κ c) := by
  rw [blockBlackRes_tmul, map_one,
    PiTensorProduct.nonUnitalMap_single_self _ κ (blockFactorRes_one_of_ne Q Λ i κ hr hκ)]

theorem blockBlackRes_single_of_ne {r : Fin ℓ} (h : r ≠ κ)
    (c : CycKLR k Q (redCyc Λ r) (rightBlock b' r)) :
    blockBlackRes Q Λ i κ h0 hr hκ (1 ⊗ₜ sg' r c) =
      (1 ⊗ₜ sg r (CyclotomicAction.castCyc Q (redCyc Λ r) (hr r h) c)) *
        blockBlackRes Q Λ i κ h0 hr hκ 1 := by
  rw [blockBlackRes_tmul, map_one,
    PiTensorProduct.nonUnitalMap_single_of_ne _ κ (blockFactorRes_one_of_ne Q Λ i κ hr hκ) h,
    blockBlackRes_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    blockFactorRes_of_ne _ _ _ _ _ _ h]

end Generic

section Cast

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) {c c' : Fin (ℓ + 1) → Multiset I}

theorem blockAlgebraCast_tmul_one (h : c = c') (a : KLRAlgebra k Q (leftBlock c)) :
    blockAlgebraCast Q Λ h (a ⊗ₜ 1) = castKLR Q (congrArg leftBlock h) a ⊗ₜ 1 := by
  subst h
  rfl

theorem blockAlgebraCast_single (h : c = c') (r : Fin ℓ)
    (x : CycKLR k Q (redCyc Λ r) (rightBlock c r)) :
    blockAlgebraCast Q Λ h (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
        (A := fun r : Fin ℓ => CycKLR k Q (redCyc Λ r) (rightBlock c r)) r x) =
      1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
        (A := fun r : Fin ℓ => CycKLR k Q (redCyc Λ r) (rightBlock c' r)) r
        (CyclotomicAction.castCyc Q (redCyc Λ r) (congrArg (fun c => rightBlock c r) h) x) := by
  subst h
  rfl

end Cast

section TwoPiece

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b b' : Fin (ℓ + 2) → Multiset I}

local notation "B" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Fac" => fun r : Fin (ℓ + 1) => CycKLR k Q (redCyc Λ r) (rightBlock b r)
local notation "sg" => PiTensorProduct.singleAlgHom (R := k) (A := Fac)

section Last

variable (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' (Fin.last ℓ) = rightBlock b (Fin.last ℓ))

local notation "E" => blockBlackRes Q Λ i (Fin.last ℓ) h0 hr hκ

omit [DecidableEq I] in
include h0 hr in
theorem initBlocks_eq_of_last : initBlocks b' = initBlocks b := by
  funext j
  induction j using Fin.cases with
  | zero => exact h0
  | succ r => exact hr r.castSucc (Fin.castSucc_lt_last r).ne

theorem blockBlackRes_one_eq_lastBlockAlgHom :
    E 1 = lastBlockAlgHom Q Λ b (blockFactorRes Q Λ i (Fin.last ℓ) hr hκ (Fin.last ℓ) 1) :=
  blockBlackRes_one Q Λ i (Fin.last ℓ) h0 hr hκ

theorem isIdempotentElem_blockBlackRes_one : IsIdempotentElem (E 1) := by
  change E 1 * E 1 = E 1
  rw [← map_mul, one_mul]

/-- `x ↦ ι(x) e` for the inclusion `ι` of the first `ℓ` red strands and `e = blockBlackRes 1`. -/
def initBlockAlgHomMulLast :
    BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b') →ₙₐ[k] B where
  toFun x := initBlockAlgHom Q Λ b (blockAlgebraCast Q (Λ ∘ Fin.castSucc)
    (initBlocks_eq_of_last h0 hr) x) * E 1
  map_smul' c x := by rw [map_smul, map_smul, smul_mul_assoc]; rfl
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_add' x y := by rw [map_add, map_add, add_mul]
  map_mul' x y := by
    have hLL := (isIdempotentElem_blockBlackRes_one Q Λ i h0 hr hκ).eq
    rw [blockBlackRes_one_eq_lastBlockAlgHom] at hLL
    rw [map_mul, map_mul, blockBlackRes_one_eq_lastBlockAlgHom,
      mul_assoc _ (lastBlockAlgHom Q Λ b _),
      ← mul_assoc (lastBlockAlgHom Q Λ b _) (initBlockAlgHom Q Λ b _),
      ← (commute_initBlockAlgHom_lastBlockAlgHom Q Λ b _ _).eq,
      mul_assoc _ (lastBlockAlgHom Q Λ b _),
      hLL, ← mul_assoc]

/-- **`ₗEᵢ` on the first `ℓ` red strands**: for `κ` the last red strand, the map of block algebras
is the cast on the first `ℓ` red strands, times `e`. -/
theorem blockBlackRes_initBlockAlgHom_last
    (x : BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b')) :
    E (initBlockAlgHom Q Λ b' x) = initBlockAlgHom Q Λ b (blockAlgebraCast Q (Λ ∘ Fin.castSucc)
      (initBlocks_eq_of_last h0 hr) x) * E 1 := by
  have := NonUnitalAlgHom.tensorPi_ext
    (f := (E).comp (initBlockAlgHom Q Λ b').toNonUnitalAlgHom)
    (g := initBlockAlgHomMulLast Q Λ i h0 hr hκ) (fun a => ?_) (fun r y => ?_)
  · exact DFunLike.congr_fun this x
  · change E (initBlockAlgHom Q Λ b' (a ⊗ₜ 1)) = initBlockAlgHom Q Λ b
      (blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_eq_of_last h0 hr) (a ⊗ₜ 1)) * E 1
    rw [initBlockAlgHom_tmul_one, blockBlackRes_tmul_one, blockAlgebraCast_tmul_one,
      initBlockAlgHom_tmul_one, blockBlackRes_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one]
  · change E (initBlockAlgHom Q Λ b' (1 ⊗ₜ _)) = initBlockAlgHom Q Λ b
      (blockAlgebraCast Q (Λ ∘ Fin.castSucc) (initBlocks_eq_of_last h0 hr) (1 ⊗ₜ _)) * E 1
    rw [initBlockAlgHom_one_tmul_single, blockBlackRes_single_of_ne Q Λ i (Fin.last ℓ) h0 hr hκ
      (Fin.castSucc_lt_last r).ne, blockAlgebraCast_single, initBlockAlgHom_one_tmul_single]
    rfl

/-- **`ₗEᵢ` on the last factor**: appending a strand of colour `i` to the last block. -/
theorem blockBlackRes_lastBlockAlgHom_last
    (y : CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b' (Fin.last ℓ))) :
    E (lastBlockAlgHom Q Λ b' y) = lastBlockAlgHom Q Λ b
      (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ
        (AbsentColour.cyclotomicLast Q i (redCyc Λ (Fin.last ℓ)) (rightBlock b' (Fin.last ℓ))
          y)) := by
  rw [lastBlockAlgHom_apply, blockBlackRes_single_self, blockFactorRes_self]
  rfl

end Last

section CastSucc

variable (κ : Fin ℓ) (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ.castSucc → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ.castSucc = rightBlock b κ.castSucc)

local notation "E" => blockBlackRes Q Λ i κ.castSucc h0 hr hκ

omit [DecidableEq I] in
include hr in
theorem initBlocks_rightBlock_of_ne (r : Fin ℓ) (h : r ≠ κ) :
    rightBlock (initBlocks b') r = rightBlock (initBlocks b) r :=
  hr r.castSucc fun h' => h (Fin.castSucc_injective _ h')

/-- `ₖEᵢ` for the first `ℓ` red strands. -/
abbrev initBlockBlackRes :
    BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b') →ₙₐ[k]
      BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b) :=
  blockBlackRes Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b) (b' := initBlocks b') h0
    (initBlocks_rightBlock_of_ne κ hr) hκ

theorem blockFactorRes_init_self :
    blockFactorRes Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b) (b' := initBlocks b')
        (initBlocks_rightBlock_of_ne κ hr) hκ κ 1 =
      blockFactorRes Q Λ i κ.castSucc hr hκ κ.castSucc 1 := by
  rw [blockFactorRes_self, blockFactorRes_self]
  rfl

/-- **`ₖEᵢ` commutes with the restriction to the first `ℓ` red strands**, `κ < ℓ`. -/
theorem initBlockAlgHom_blockBlackRes_castSucc
    (x : BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b')) :
    initBlockAlgHom Q Λ b (initBlockBlackRes Q Λ i κ h0 hr hκ x) =
      E (initBlockAlgHom Q Λ b' x) := by
  have := NonUnitalAlgHom.tensorPi_ext
    (f := (initBlockAlgHom Q Λ b).toNonUnitalAlgHom.comp (initBlockBlackRes Q Λ i κ h0 hr hκ))
    (g := (E).comp (initBlockAlgHom Q Λ b').toNonUnitalAlgHom) (fun a => ?_) (fun r y => ?_)
  · exact DFunLike.congr_fun this x
  · change initBlockAlgHom Q Λ b (initBlockBlackRes Q Λ i κ h0 hr hκ (a ⊗ₜ 1)) =
      E (initBlockAlgHom Q Λ b' (a ⊗ₜ 1))
    rw [blockBlackRes_tmul_one, initBlockAlgHom_tmul_one, blockBlackRes_tmul_one,
      ← mul_one (castKLR Q _ a), ← one_mul (PiTensorProduct.singleAlgHom _ _),
      ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, initBlockAlgHom_tmul_one,
      initBlockAlgHom_one_tmul_single, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      blockFactorRes_init_self]
  · change initBlockAlgHom Q Λ b (initBlockBlackRes Q Λ i κ h0 hr hκ (1 ⊗ₜ _)) =
      E (initBlockAlgHom Q Λ b' (1 ⊗ₜ _))
    rw [initBlockAlgHom_one_tmul_single]
    by_cases hrκ : r = κ
    · subst hrκ
      rw [blockBlackRes_single_self, initBlockAlgHom_one_tmul_single, blockBlackRes_single_self,
        blockFactorRes_self, blockFactorRes_self]
      rfl
    · have hcs : r.castSucc ≠ κ.castSucc := fun h' => hrκ (Fin.castSucc_injective _ h')
      rw [blockBlackRes_single_of_ne _ _ _ _ _ _ _ hrκ, blockBlackRes_one, map_mul,
        initBlockAlgHom_one_tmul_single, initBlockAlgHom_one_tmul_single,
        blockBlackRes_single_of_ne _ _ _ _ _ _ _ hcs, blockBlackRes_one,
        blockFactorRes_init_self]
      rfl

/-- **`ₖEᵢ` on the last factor**, `κ < ℓ`: the cast of the last factor, times `e`. -/
theorem blockBlackRes_lastBlockAlgHom_castSucc
    (y : CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b' (Fin.last ℓ))) :
    E (lastBlockAlgHom Q Λ b' y) = lastBlockAlgHom Q Λ b
      (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ))
        (hr (Fin.last ℓ) (Fin.castSucc_lt_last κ).ne') y) * E 1 := by
  rw [lastBlockAlgHom_apply, blockBlackRes_single_of_ne _ _ _ _ _ _ _
    (Fin.castSucc_lt_last κ).ne']
  rfl

theorem commute_blockBlackRes_one_lastBlockAlgHom_castSucc
    (y : CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b (Fin.last ℓ))) :
    Commute (E 1) (lastBlockAlgHom Q Λ b y) := by
  rw [blockBlackRes_one, lastBlockAlgHom_apply]
  refine Algebra.TensorProduct.tmul_mul_tmul _ _ _ _ |>.trans ?_ |>.trans
    (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm
  rw [mul_one, PiTensorProduct.commute_singleAlgHom (R := k) (A := Fac)
    (Fin.castSucc_lt_last κ).ne _ _ |>.eq]

end CastSucc

end TwoPiece

end StendhalAlgebra

end Categorification.Stendhal
