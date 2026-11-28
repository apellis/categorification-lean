/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalCorner
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.KLR.CyclotomicCornerDimension
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutParabolic

/-!
# The dimension of the diagonal corner of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `Tor_0` term on the diagonal. For the inner one-red module
`Z = T^{λ_2}(β) e(red₂ 𝐮)`, the projective cover of a loading of the middle red strand, the
corner of `SMove.diagonalCornerEquiv` is a corner of the cyclotomic KLR algebra
`R^{λ_2}(β)` (through `SingleRed.cyclotomicEquiv`), and its dimension is given by the
permutation formula `CycKLR.finrank_corner_permutationFormula`.

## Main results

* `Stendhal.cutSuffixProjection_e`: the loading idempotents of the second block of a cut.
* `Stendhal.SingleRed.cyclotomicEquiv_mk_e`: `SingleRed.cyclotomicEquiv` sends `e(𝐮)` to the
  loading idempotent of `(red 𝐮)`.
* `fixSubLIdealAlgEquiv`: for an algebra isomorphism `φ : C ≃ₐ A` and idempotents `p, q` of
  `C`, the vectors of `A φ(q)` fixed by `φ(p)` form the corner `p C q`.
* `Stendhal.SMove.cycProjective`: `T^{λ_2}(β) e(red₂ 𝐮)`, through the cyclotomic factor
  `midCycEquiv` of `parabolicCutFactorEquiv`.
* `Stendhal.SMove.diagonalCornerCycEquiv`, `Stendhal.SMove.finrank_diagonalCorner`.
-/

noncomputable section

namespace Categorification

open CategoryTheory KLR KLRAlgebra
open scoped TensorProduct

/-! ### Fixed vectors of a left ideal along an algebra isomorphism -/

section Generic

variable {k C A : Type*} [CommRing k] [Ring C] [Ring A] [Algebra k C] [Algebra k A]

/-- For idempotents `p, q`, the range of `x ↦ p x q` is `{x | p x = x, x q = x}`. -/
theorem mem_range_mulLeft_comp_mulRight_iff {p q : C} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (x : C) :
    x ∈ LinearMap.range ((LinearMap.mulLeft k p).comp (LinearMap.mulRight k q)) ↔
      p * x = x ∧ x * q = x := by
  constructor
  · rintro ⟨z, rfl⟩
    change p * (p * (z * q)) = p * (z * q) ∧ p * (z * q) * q = p * (z * q)
    refine ⟨by rw [← mul_assoc, hp.eq], by rw [mul_assoc, mul_assoc, hq.eq]⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨x, ?_⟩
    change p * (x * q) = x
    rw [h₂, h₁]

/-- **Fixed vectors of a left ideal along an algebra isomorphism.** For `φ : C ≃ₐ[k] A` and
idempotents `p, q` of `C`, the vectors of `A φ(q)` fixed by `φ(p)` are the corner `p C q`,
`y ↦ φ⁻¹(y)`. -/
def fixSubLIdealAlgEquiv (φ : C ≃ₐ[k] A) {p q : C} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) :
    fixSub k (lIdeal (φ q)) (φ p) ≃ₗ[k]
      LinearMap.range ((LinearMap.mulLeft k p).comp (LinearMap.mulRight k q)) where
  toFun y := ⟨φ.symm y.1.1, (mem_range_mulLeft_comp_mulRight_iff hp hq _).mpr
    ⟨φ.injective (by
      rw [map_mul, AlgEquiv.apply_symm_apply]
      exact congrArg Subtype.val ((mem_fixSub (k := k)).mp y.2)),
     φ.injective (by
      rw [map_mul, AlgEquiv.apply_symm_apply]
      exact (mem_lIdeal).mp y.1.2)⟩⟩
  invFun x := ⟨⟨φ x.1, (mem_lIdeal).mpr (by
      rw [← map_mul, ((mem_range_mulLeft_comp_mulRight_iff hp hq _).mp x.2).2])⟩,
    (mem_fixSub (k := k)).mpr (Subtype.ext (by
      change φ p * φ x.1 = φ x.1
      rw [← map_mul, ((mem_range_mulLeft_comp_mulRight_iff hp hq _).mp x.2).1]))⟩
  left_inv y := Subtype.ext (Subtype.ext (φ.apply_symm_apply y.1.1))
  right_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  map_add' y y' := Subtype.ext (map_add φ.symm y.1.1 y'.1.1)
  map_smul' c y := Subtype.ext (map_smul φ.symm c y.1.1)

end Generic

namespace Stendhal

/-! ### Loading idempotents of the second block of a cut -/

section Suffix

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (β : Multiset I)

/-- The loading idempotents of the second block of a cut. -/
theorem cutSuffixProjection_e
    (p : Seq (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β))) :
    cutSuffixProjection Q Λ β (e p) = tensorLoad Q (Λ ∘ Fin.natAdd a) β
      ((redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective r a) β).equiv.symm p) := by
  have h : (relabelEquiv (redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective r a)
      β)).symm (e p) = e ((redSubfamilyRelabel Q Λ (Fin.natAdd a) (Fin.natAdd_injective r a)
        β).equiv.symm p) :=
    (AlgEquiv.symm_apply_eq _).2 ((relabelHom_e (redSubfamilyRelabel Q Λ (Fin.natAdd a)
      (Fin.natAdd_injective r a) β) _).trans (by rw [Equiv.apply_symm_apply])).symm
  simp only [cutSuffixProjection, redSubfamilyProjection, tensorLoad, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, h]

end Suffix

/-! ### The cyclotomic idempotents in the one-red algebra -/

namespace SingleRed

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

/-- `SingleRed.cyclotomicEquiv` sends the idempotent `e(𝐮)` of the cyclotomic quotient to the
loading idempotent of `(red 𝐮)` (Webster, arXiv:1309.3796v3, Theorem 4.20). -/
theorem cyclotomicEquiv_mk_e (u : Seq ν) :
    cyclotomicEquiv Q Λ ν (CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) ν (e u)) =
      tensorLoad Q Λ ν (insertWord ν u) := by
  change cyclotomicProjection Q Λ ν (CycKLR.mk k Q _ ν (e u)) = _
  rw [cyclotomicProjection, CycKLR.lift_mk, insertRed_e]
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  have h : StendhalAlgebraAllOrders.e (insertWord ν u) *
      StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν =
      StendhalAlgebraAllOrders.e (insertWord ν u) := by
    rw [redOrderedIdem_eq_one, mul_one]
  exact h.symm

end SingleRed

/-! ### The diagonal corner at a cyclotomic projective -/

/-- `tensorProductAlgebraCast` sends loading idempotents to loading idempotents. -/
theorem tensorProductAlgebraCast_tensorLoad {I k : Type*} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {n : ℕ} {Λa Λb : Fin n → I →₀ ℕ} (h : Λa = Λb)
    (ν : Multiset I) (c : Seq (stendhalWeight n ν)) :
    tensorProductAlgebraCast Q h ν (tensorLoad Q Λa ν c) = tensorLoad Q Λb ν c := by
  subst h; rfl

namespace SMove

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

local notation "Λ₂" => (Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ)
local notation "Λ₁" => ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) ∘ Fin.natAdd 1)
local notation "α₂" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
  (stendhalWeight 1 (0 : Multiset I))
local notation "δ₂" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd 1)) (stendhalWeight 1 β)
local notation "δ₃" =>
  Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight 1 (0 : Multiset I))
local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^
  (Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) (Fin.last 1) j)

/-- The cyclotomic factor of `parabolicCutFactorEquiv` at the cut `{1} | {2}`:
`R^{λ_2}(β) ≅ T^{λ_2}(β)` (Theorem 4.20). -/
abbrev midCycEquiv : CycKLR k Q aΛ β ≃ₐ[k] TensorProductAlgebra k Q Λ₁ β :=
  (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ₂ (Fin.last 1)) β).trans
    (tensorProductAlgebraCast Q (congrArg (Λ₂ ∘ ·) lastIndex_eq_natAdd) β)

theorem midCycEquiv_mk_e (u : Seq β) :
    midCycEquiv Q Λ β (CycKLR.mk k Q aΛ β (e u)) =
      tensorLoad Q Λ₁ β (SingleRed.insertWord β u) :=
  (congrArg (tensorProductAlgebraCast Q (congrArg (Λ₂ ∘ ·) lastIndex_eq_natAdd) β)
    (SingleRed.cyclotomicEquiv_mk_e Q (fun _ : Fin 1 => Λ₂ (Fin.last 1)) β u)).trans
    (tensorProductAlgebraCast_tensorLoad Q _ β _)

/-- The loading `(red₂ 𝐮)` of the inner block `{2}`, for a black word `𝐮`. -/
def middleLoading (u : Seq β) : Seq δ₂ :=
  (redSubfamilyRelabel Q Λ₂ (Fin.natAdd 1) (Fin.natAdd_injective 1 1) β).equiv
    (SingleRed.insertWord β u)

/-- The idempotent of `middleLoading u` is the image of `e(𝐮)` under `midCycEquiv`. -/
theorem cutSuffixProjection_e_middleLoading (u : Seq β) :
    cutSuffixProjection Q Λ₂ β (e (middleLoading Q Λ β u)) =
      midCycEquiv Q Λ β (CycKLR.mk k Q aΛ β (e u)) := by
  rw [cutSuffixProjection_e, middleLoading, Equiv.symm_apply_apply, midCycEquiv_mk_e]

theorem isIdempotentElem_cycKLR_mk_e (u : Seq β) :
    IsIdempotentElem (CycKLR.mk k Q aΛ β (e u)) := by
  rw [IsIdempotentElem, ← map_mul, e_mul_self]

/-- The projective `T^{λ_2}(β) e(red₂ 𝐮)` of the one-red algebra of the inner block, written as
the image of the cyclotomic projective `R^{λ_2}(β) e(𝐮)`. -/
def cycProjective (u : Seq β) : ModuleCat.{0} (TensorProductAlgebra k Q Λ₁ β) :=
  ModuleCat.of _ (lIdeal (midCycEquiv Q Λ β (CycKLR.mk k Q aΛ β (e u))))

/-- The fixed vectors of a `ModuleCat` object, in its `ModuleCat` scalars, along a linear
equivalence with a module carrying its own scalars. -/
def fixSubModuleCatEquiv {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) (M : Type)
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (f : X ≃ₗ[A] M) (a : A) :
    fixSub k X a ≃ₗ[k] fixSub k M a where
  toFun y := ⟨f y.1, by rw [mem_fixSub, ← f.map_smul, (mem_fixSub (k := k)).mp y.2]⟩
  invFun y := ⟨f.symm y.1, by rw [mem_fixSub, ← f.symm.map_smul, (mem_fixSub (k := k)).mp y.2]⟩
  left_inv y := Subtype.ext (f.symm_apply_apply y.1)
  right_inv y := Subtype.ext (f.apply_symm_apply y.1)
  map_add' y y' := Subtype.ext (map_add f y.1 y'.1)
  map_smul' c y := Subtype.ext ((f.map_smul (algebraMap k A c) y.1).trans
    (algebraMap_smul A c (f y.1)))

/-- The fixed vectors of `cycProjective u` in its `ModuleCat` scalars are those of the left
ideal. -/
def cycProjectiveFixSubEquiv (u : Seq β) (f : TensorProductAlgebra k Q Λ₁ β) :
    fixSub k (cycProjective Q Λ β u) f ≃ₗ[k]
      fixSub k (lIdeal (midCycEquiv Q Λ β (CycKLR.mk k Q aΛ β (e u)))) f :=
  fixSubModuleCatEquiv (k := k) (cycProjective Q Λ β u) _
    (LinearEquiv.refl (TensorProductAlgebra k Q Λ₁ β)
      (lIdeal (midCycEquiv Q Λ β (CycKLR.mk k Q aΛ β (e u))))) f

/-- **The diagonal corner of the S-move at a cyclotomic projective** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor_0` on the diagonal): for
`Z = T^{λ_2}(β) e(red₂ 𝐮)` and the loading `(red₁ red₂ 𝐮' red₃)`, the vectors of
`𝕊^{λ_1, λ_2; λ_3}(𝕊^{λ_1; λ_2}(P_∅ ⊠ Z) ⊠ P_∅)` fixed by its loading idempotent form the
cyclotomic corner `e(𝐮') R^{λ_2}(β) e(𝐮)`. -/
def diagonalCornerCycEquiv (i : Seq α₂) (u u' : Seq β) (j₃ : Seq δ₃) :
    fixSub k ((rightStd Q hQ Λ β).obj ((emptyLeftStd Q hQ Λ₂ β).obj (cycProjective Q Λ β u)))
        (cutLoad Q Λ (add_zero β) ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃))
      ≃ₗ[k] CycKLR.corner k Q aΛ u' u :=
  (diagonalCornerEquiv Q hQ Λ β (cycProjective Q Λ β u) i (middleLoading Q Λ β u') j₃).trans
    ((LinearEquiv.ofEq _ _ (by rw [cutSuffixProjection_e_middleLoading])).trans
      ((cycProjectiveFixSubEquiv Q Λ β u _).trans
        (fixSubLIdealAlgEquiv (midCycEquiv Q Λ β) (isIdempotentElem_cycKLR_mk_e Q Λ β u')
          (isIdempotentElem_cycKLR_mk_e Q Λ β u))))

/-- **The dimension of the diagonal corner** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): for a Rouquier choice of `Q`, the dimension of the corner of
`diagonalCornerCycEquiv` is the Hu–Shi permutation formula for `e(𝐮') R^{λ_2}(β) e(𝐮)`
(`CycKLR.finrank_corner_permutationFormula`). -/
theorem finrank_diagonalCorner {C : QuantumGroup.CartanDatum I} (hP : IsRouquierQ C Q)
    (i : Seq α₂) (u u' : Seq β) (j₃ : Seq δ₃) :
    (Module.finrank k (fixSub k ((rightStd Q hQ Λ β).obj
        ((emptyLeftStd Q hQ Λ₂ β).obj (cycProjective Q Λ β u)))
        (cutLoad Q Λ (add_zero β) ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃)))
      : ℤ) =
      ∑ w : Equiv.Perm (Fin β.card) with ∀ j, u'.1 j = u.1 (w j),
        ∏ j, CycKLR.huShiN C (Λ₂ (Fin.last 1)) u'.1 w j := by
  rw [(diagonalCornerCycEquiv Q hQ Λ β i u u' j₃).finrank_eq]
  exact CycKLR.finrank_corner_permutationFormula hP _ u' u

end SMove

end Stendhal

end Categorification
