/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalCornerDimension
import Categorification.WeightedKLR.Rigidity.SMoveRightStdTensorLayer
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltration
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers

/-!
# The diagonal S-move module is a standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `Tor_0` term on the diagonal. For the inner projective
`Z = T^{λ_2}(β) e(red₂ 𝐮)` (`SMove.cycProjective`), the S-move module
`𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ Z) ⊠ P_∅)` is the standard module `S_s` of the loading
`s = (red₁ red₂ 𝐮 red₃)`, written as the two-piece loading of the two-piece loading
`(red₁)(red₂ 𝐮)` and `(red₃)`. Both steps are `nonempty_stdLayerModule_twoPiece_equiv`: the
inner one through `cutStandardParabolicIso` at the cut `{1} | {2}`, where `P_∅` is the standard
module of the empty loading of one red strand; the outer one through
`SMove.rightStdTensorLayerIso`. Hence the dimension of the fixed vectors of the loading
idempotent on `S_s` is the corner dimension of `SMove.finrank_diagonalCorner`.

## Main results

* `Stendhal.oneZeroStandardEquiv`: with one red strand and no black strand, the standard
  module of the (unique) loading is the regular module.
* `Stendhal.SMove.midFactorEquiv`: `P_∅ ⊠ Z ≅ S_{(red₁)} ⊠ R^{λ_2}(β) e(𝐮)` over the parabolic
  factor algebra of the cut `{1} | {2}`.
* `Stendhal.SMove.nonempty_emptyLeftStd_cycProjective_equiv`: `𝕊(P_∅ ⊠ Z) ≅ S_{(red₁ red₂ 𝐮)}`.
* `Stendhal.SMove.nonempty_rightStd_equiv_of_equiv`: `𝕊(W ⊠ P_∅) ≅ S_{t red₃}` for `W ≅ S_t`.
* `Stendhal.SMove.nonempty_diagonal_standard_equiv`: the S-move module of `Z` is `S_s`.
* `Stendhal.SMove.finrank_fixSub_diagonalStandard`: the dimension of the fixed vectors.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra
open scoped TensorProduct

/-! ### One red strand, no black strand -/

section OneZero

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ' : Fin 1 → I →₀ ℕ)

omit [DecidableEq I] in
/-- With one red strand and no black strand there is exactly one loading. -/
theorem subsingleton_seq_stendhalWeight_one_zero :
    Subsingleton (Seq (stendhalWeight 1 (0 : Multiset I))) :=
  ⟨fun s t => Subtype.ext (funext fun a => by
    have hs := Seq.mem s a
    have ht := Seq.mem t a
    simp only [stendhalWeight, Multiset.map_zero, zero_add, Multiset.mem_map] at hs ht
    obtain ⟨r, -, hr⟩ := hs
    obtain ⟨r', -, hr'⟩ := ht
    rw [← hr, ← hr', Subsingleton.elim r r'])⟩

theorem seqIdem_eq_one_of_one_zero (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) : seqIdem Q Λ' t ht = 1 := by
  have := subsingleton_seq_stendhalWeight_one_zero (I := I)
  have h := sum_seqIdem_eq_one (Q := Q) (Λ := Λ') 1 (0 : Multiset I)
  rwa [Fintype.sum_subsingleton _ ⟨t, ht⟩] at h

theorem leftUpper_eq_bot_of_one_zero (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) : leftUpper Q Λ' t ht = ⊥ := by
  have := subsingleton_seq_stendhalWeight_one_zero (I := I)
  refine le_antisymm (Submodule.span_le.2 ?_) bot_le
  rintro _ ⟨t', ht', a, hlt, rfl⟩
  obtain rfl : t' = t := Subsingleton.elim _ _
  exact (hlt.2 hlt.1).elim

/-- With one red strand and no black strand, the standard module of the loading is the regular
module `T^{λ}(0)` (Webster, arXiv:1309.3796v3, Definition 5.1). -/
def oneZeroStandardEquiv (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    leftStandard Q Λ' t ht ≃ₗ[TensorProductAlgebra k Q Λ' 0] TensorProductAlgebra k Q Λ' 0 :=
  (Submodule.quotEquivOfEqBot _ (by
    rw [leftUpper_eq_bot_of_one_zero Q Λ' t ht, Submodule.comap_bot, Submodule.ker_subtype])).trans
    ((LinearEquiv.ofEq _ ⊤ (by
      rw [seqIdem_eq_one_of_one_zero Q Λ' t ht]
      exact eq_top_iff.2 fun y _ => mul_one y)).trans Submodule.topEquiv)

end OneZero

/-! ### The inner cut `{1} | {2}` -/

namespace SMove

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

local notation "Λ₂" => (Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ)
local notation "Λ₁" => ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) ∘ Fin.natAdd 1)
local notation "L" => TensorProductAlgebra k Q ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) ∘
  Fin.castAdd 1) 0
local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^
  (Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) (Fin.last 1) j)

/-- The standard module of the empty loading of the first red strand. -/
abbrev firstStd (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ₂ ∘ Fin.castSucc) 0) :=
  ModuleCat.of _ (leftStandard Q (Λ₂ ∘ Fin.castSucc) t ht)

/-- `P_∅ = T^{λ_1}(0) ≅ S_{(red₁)}`, `k`-linearly. -/
def midLeftEquiv (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) :
    L ≃ₗ[k] KMod (k := k) (firstStd Q Λ t ht) where
  toFun l := (oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht).symm l
  invFun x := oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht x
  left_inv l := (oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht).apply_symm_apply l
  right_inv x := (oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht).symm_apply_apply x
  map_add' l l' := map_add _ l l'
  map_smul' c l := by
    rw [Algebra.smul_def]
    exact (oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht).symm.map_smul
      (algebraMap k L c) l

theorem midLeftEquiv_mul (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (a l : L) : midLeftEquiv Q Λ t ht (a * l) = a • midLeftEquiv Q Λ t ht l :=
  (oneZeroStandardEquiv Q (Λ₂ ∘ Fin.castSucc) t ht).symm.map_smul a l

/-- `Z = T^{λ_2}(β) e(red₂ 𝐮) ≅ R^{λ_2}(β) e(𝐮)`, `k`-linearly, through `midCycEquiv`. -/
def midRightEquiv (u : Seq β) :
    cycProjective Q Λ β u ≃ₗ[k] KMod (k := k) (cycProj Q Λ₂ β u) where
  toFun z := ⟨(midCycEquiv Q Λ β).symm (@id (TensorProductAlgebra k Q Λ₁ β) z.1),
    (mem_lIdeal).mpr ((midCycEquiv Q Λ β).injective (by
      rw [map_mul, AlgEquiv.apply_symm_apply]
      exact (mem_lIdeal).mp z.2))⟩
  invFun y := ⟨midCycEquiv Q Λ β y.1, (mem_lIdeal).mpr (by
    rw [← map_mul, (mem_lIdeal).mp y.2])⟩
  left_inv z := Subtype.ext ((midCycEquiv Q Λ β).apply_symm_apply z.1)
  right_inv y := Subtype.ext ((midCycEquiv Q Λ β).symm_apply_apply y.1)
  map_add' z z' := Subtype.ext (map_add (midCycEquiv Q Λ β).symm z.1 z'.1)
  map_smul' c z := Subtype.ext (by
    change (midCycEquiv Q Λ β).symm (algebraMap k _ c * z.1) =
      algebraMap k (CycKLR k Q aΛ β) c * (midCycEquiv Q Λ β).symm z.1
    rw [map_mul, AlgEquiv.commutes])

theorem midRightEquiv_smul (u : Seq β) (c : CycKLR k Q aΛ β) (z : cycProjective Q Λ β u) :
    midRightEquiv Q Λ β u (midCycEquiv Q Λ β c • z) = c • midRightEquiv Q Λ β u z :=
  Subtype.ext (by
    change (midCycEquiv Q Λ β).symm (midCycEquiv Q Λ β c * z.1) =
      c * (midCycEquiv Q Λ β).symm z.1
    rw [map_mul, AlgEquiv.symm_apply_apply])

/-- The `k`-linear map `P_∅ ⊠ Z → S_{(red₁)} ⊠ R^{λ_2}(β) e(𝐮)`. -/
abbrev midInputLinearEquiv (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (u : Seq β) :
    ExtTensor k L (cycProjective Q Λ β u) ≃ₗ[k]
      ExtTensor k (KMod (k := k) (firstStd Q Λ t ht)) (KMod (k := k) (cycProj Q Λ₂ β u)) :=
  TensorProduct.congr (midLeftEquiv Q Λ t ht) (midRightEquiv Q Λ β u)

theorem midInputLinearEquiv_smul (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) (u : Seq β) (a : L) (c : CycKLR k Q aΛ β)
    (x : ExtTensor k L (cycProjective Q Λ β u)) :
    midInputLinearEquiv Q Λ β t ht u ((a ⊗ₜ[k] midCycEquiv Q Λ β c) • x) =
      (a ⊗ₜ[k] c) • midInputLinearEquiv Q Λ β t ht u x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | tmul l z =>
    rw [ExtTensor.smul_tmul]
    change midLeftEquiv Q Λ t ht (a * l) ⊗ₜ[k] midRightEquiv Q Λ β u (midCycEquiv Q Λ β c • z) =
      (a ⊗ₜ[k] c) • ExtTensor.tmul (k := k) (midLeftEquiv Q Λ t ht l)
        (midRightEquiv Q Λ β u z)
    rw [ExtTensor.smul_tmul, midLeftEquiv_mul, midRightEquiv_smul]
    rfl

/-- **`P_∅ ⊠ Z ≅ S_{(red₁)} ⊠ R^{λ_2}(β) e(𝐮)`** as modules over the parabolic factor algebra
`T^{λ_1}(0) ⊗ R^{λ_2}(β)` of the cut `{1} | {2}`. -/
def midFactorEquiv (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (u : Seq β) :
    (parabolicOfCutModule Q Λ₂
        ((SMove.regularLeftTensor (k := k) L).obj (cycProjective Q Λ β u))).carrier ≃ₗ[
      parabolicFactorAlgebra Q Λ₂ 0 β]
      (tensorFactor Q Λ₂ (firstStd Q Λ t ht) (cycProj Q Λ₂ β u)).carrier where
  toFun x := midInputLinearEquiv Q Λ β t ht u x
  invFun x := (midInputLinearEquiv Q Λ β t ht u).symm x
  left_inv x := (midInputLinearEquiv Q Λ β t ht u).left_inv x
  right_inv x := (midInputLinearEquiv Q Λ β t ht u).right_inv x
  map_add' x y := map_add (midInputLinearEquiv Q Λ β t ht u) x y
  map_smul' d x := by
    rw [RingHom.id_apply]
    induction d using TensorProduct.inductionOn with
    | add d d' hd hd' => rw [add_smul, map_add, hd, hd', add_smul]
    | tmul a c =>
      rw [parabolicOfCut_smul]
      exact midInputLinearEquiv_smul Q Λ β t ht u a c x

/-- **`𝕊^{λ_1; λ_2}(P_∅ ⊠ T^{λ_2}(β) e(red₂ 𝐮)) ≅ S_{(red₁ red₂ 𝐮)}`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): the inner S-move module of the
cyclotomic projective is the standard module of the two-piece loading `(red₁)(red₂ 𝐮)`. -/
theorem nonempty_emptyLeftStd_cycProjective_equiv
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) (u : Seq β) :
    Nonempty ((emptyLeftStd Q hQ Λ₂ β).obj (cycProjective Q Λ β u) ≃ₗ[
      TensorProductAlgebra k Q Λ₂ β] ModuleCat.of (TensorProductAlgebra k Q Λ₂ β)
        (leftStandard Q Λ₂ (twoPieceLabel (zero_add β) u ⟨t, ht⟩).1
          (twoPieceLabel (zero_add β) u ⟨t, ht⟩).2)) := by
  obtain ⟨g⟩ := nonempty_stdLayerModule_twoPiece_equiv Q Λ₂ hQ (zero_add β) ht u
  exact ⟨((cutStandardParabolicIso Q hQ Λ₂ (zero_add β)
    ((SMove.regularLeftTensor (k := k) L).obj (cycProjective Q Λ β u))) ≪≫
      stdLayerIso Q Λ₂ hQ (zero_add β) (midFactorEquiv Q Λ β t ht u)).toLinearEquiv.trans g⟩

/-- **`𝕊^{λ_1, λ_2; λ_3}(S_t ⊠ P_∅) ≅ S_{t red₃}`** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22): for `W ≅ S_t` over the first two red strands, the outer S-move module is
the standard module of the two-piece loading `t (red₃)`. -/
theorem nonempty_rightStd_equiv_of_equiv
    (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β))
    {t : Seq (stendhalWeight 2 β)} (ht : IsRedOrdered t) (u₀ : Seq (0 : Multiset I))
    (f : W ≃ₗ[TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) β]
      ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) β)
        (leftStandard Q (Λ ∘ Fin.castSucc) t ht)) :
    Nonempty ((rightStd Q hQ Λ β).obj W ≃ₗ[TensorProductAlgebra k Q Λ β]
      ModuleCat.of (TensorProductAlgebra k Q Λ β)
        (leftStandard Q Λ (twoPieceLabel (add_zero β) u₀ ⟨t, ht⟩).1
          (twoPieceLabel (add_zero β) u₀ ⟨t, ht⟩).2)) := by
  obtain ⟨g⟩ := nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ (add_zero β) ht u₀
  exact ⟨((rightStdTensorLayerIso Q hQ Λ β W u₀) ≪≫
    stdLayerIso Q Λ hQ (add_zero β)
      (tensorFactorCongr Q Λ f (LinearEquiv.refl _ _))).toLinearEquiv.trans g⟩

/-- The loading `(red₁ red₂ 𝐮 red₃)` of the three red strands, as the two-piece loading of the
two-piece loading `(red₁)(red₂ 𝐮)` and `(red₃)`. -/
def diagonalLoading (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (u : Seq β) (u₀ : Seq (0 : Multiset I)) :
    {s : Seq (stendhalWeight (2 + 1) β) // IsRedOrdered s} :=
  twoPieceLabel (ℓ := 2) (add_zero β) u₀ (twoPieceLabel (ℓ := 1) (zero_add β) u ⟨t, ht⟩)

/-- **The diagonal S-move module is a standard module** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22): for `Z = T^{λ_2}(β) e(red₂ 𝐮)`,
`𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ Z) ⊠ P_∅) ≅ S_s` for `s = (red₁ red₂ 𝐮 red₃)`. -/
theorem nonempty_diagonal_standard_equiv (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) (u : Seq β) (u₀ : Seq (0 : Multiset I)) :
    Nonempty ((rightStd Q hQ Λ β).obj ((emptyLeftStd Q hQ Λ₂ β).obj (cycProjective Q Λ β u))
      ≃ₗ[TensorProductAlgebra k Q Λ β] ModuleCat.of (TensorProductAlgebra k Q Λ β)
        (leftStandard Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2)) := by
  obtain ⟨f⟩ := nonempty_emptyLeftStd_cycProjective_equiv Q hQ Λ β t ht u
  exact nonempty_rightStd_equiv_of_equiv Q hQ Λ β _ _ u₀ f

local notation "α₂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
  (stendhalWeight 1 (0 : Multiset I))
local notation "δ₃" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight 1 (0 : Multiset I))

include hQ in
/-- **The dimension of the diagonal corner of the standard module** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor_0` on the diagonal): for a Rouquier
choice of `Q` and `s = (red₁ red₂ 𝐮 red₃)`, the vectors of `S_s` fixed by the loading
idempotent of `(red₁ red₂ 𝐮' red₃)` (in cut coordinates) have the dimension of the cyclotomic
corner `e(𝐮') R^{λ_2}(β) e(𝐮)`, given by the Hu–Shi permutation formula. -/
theorem finrank_fixSub_diagonalStandard {C : QuantumGroup.CartanDatum I} (hP : IsRouquierQ C Q)
    (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t) (u u' : Seq β)
    (u₀ : Seq (0 : Multiset I)) (i : Seq α₂) (j₃ : Seq δ₃) :
    (Module.finrank k (fixSub k
        (leftStandard Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2)
        (cutLoad Q Λ (add_zero β) ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃)))
      : ℤ) =
      ∑ w : Equiv.Perm (Fin β.card) with ∀ j, u'.1 j = u.1 (w j),
        ∏ j, CycKLR.huShiN C (Λ₂ (Fin.last 1)) u'.1 w j := by
  obtain ⟨f⟩ := nonempty_diagonal_standard_equiv Q hQ Λ β t ht u u₀
  rw [← (fixSubModuleCatEquiv (k := k) _
    (leftStandard Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2) f
    _).finrank_eq]
  exact finrank_diagonalCorner Q hQ Λ β hP i u u' j₃

end SMove

end Categorification.Stendhal
