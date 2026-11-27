/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSpectatorChange
import Categorification.WeightedKLR.RedStrands.PartialStandardizationLift

/-!
# Partial standardization commutes with tensoring the spectator

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors after Definition 5.4, and §7.3 (proof of Lemma 7.19, where
`S_+(Z ⊠ L)` is computed). The partial standardization at a cut acts on the blocks of the cut
only, so a module `L` over a further algebra `B`, tensored onto the input over `k`, passes
through it: for a module `N` over `D ⊗ C`, with `D` the algebra of the two blocks of the cut,
and a module `P` over `D ⊗ (C ⊗ B)` identified with `N ⊗_k L` (with
`(d ⊗ (c ⊗ b)) (n ⊗ v) = (d ⊗ c) n ⊗ b v`), the partial standardization of `P` is that of `N`
tensored with `L` (`cutSpectTensorEquiv`). The map sends `z ⊗ v` to the partial
standardization of `n ↦ n ⊗ v` applied to `z`; its inverse is induced, by the universal
property of the partial standardization (`cutStandardLift`), by the identity shuffle of `N`
tensored with `L`.

## Main definitions

* `Stendhal.cutSpectTensorToStd`: the map `𝕊(N) ⊗ L → 𝕊(P)`.
* `Stendhal.cutSpectTensorEquiv`: the isomorphism `𝕊(N) ⊗ L ≅ 𝕊(P)`.

## Main results

* `Stendhal.cutSpectTensorEquiv_smul`: it intertwines `(t ⊗ c) z ⊗ b v` and
  `(t ⊗ (c ⊗ b)) (z ⊗ v)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Cut

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  {C B : Type*} [Ring C] [Algebra k C] [Ring B] [Algebra k B]

local notation "D" => cutFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "ι" => cutSpectTmul Q Λ θ β

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (cutSpectAlgebra Q Λ θ β C) N]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β C) N]
  {L : Type*} [AddCommGroup L] [Module k L] [Module B L]
  {P : Type*} [AddCommGroup P] [Module k P] [Module (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P]

variable (C B) in
/-- **The tensor condition** on an isomorphism `N ⊗ L ≅ P`: `(d ⊗ c) n ⊗ b v` goes to
`(d ⊗ (c ⊗ b))` applied to the image of `n ⊗ v`. -/
def IsCutSpectTensor (f : N ⊗[k] L ≃+ P) : Prop :=
  ∀ (d : D) (c : C) (b : B) (n : N) (v : L),
    f ((ι C d c • n) ⊗ₜ[k] (b • v)) = ι (C ⊗[k] B) d (c ⊗ₜ[k] b) • f (n ⊗ₜ[k] v)

variable (f : N ⊗[k] L ≃+ P) (hf : IsCutSpectTensor Q Λ θ β C B f)

local notation "N₀" => CutSpectInput Q Λ θ β C N
local notation "P₀" => CutSpectInput Q Λ θ β (C ⊗[k] B) P

omit [IsScalarTower k (cutSpectAlgebra Q Λ θ β C) N] [Module k P]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P] in
include hf in
theorem cutSpectTensor_factor_tmul (d : D) (n : N) (v : L) :
    f ((ι C d 1 • n) ⊗ₜ[k] v) = ι (C ⊗[k] B) d 1 • f (n ⊗ₜ[k] v) := by
  have h := hf d 1 1 n v
  rw [one_smul] at h
  exact h

omit [Module k P] [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P] in
include hf in
/-- The action of the factor algebra on `P`, through `N ⊗ L`. -/
theorem cutSpectTensor_factor_smul (d : D) (x : N ⊗[k] L) :
    ι (C ⊗[k] B) d 1 • f x = f (LinearMap.rTensor L (Algebra.lsmul k k N
      (ι C d 1)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul n v => exact (cutSpectTensor_factor_tmul Q Λ θ β f hf d n v).symm
  | add x y hx hy => rw [map_add, smul_add, hx, hy, map_add, map_add]

include hf in
theorem cutSpectTensor_map_smul (c : k) (x : N ⊗[k] L) : f (c • x) = c • f x := by
  induction x using TensorProduct.inductionOn with
  | tmul n v =>
    rw [TensorProduct.smul_tmul', ← algebraMap_smul (cutSpectAlgebra Q Λ θ β C) c n,
      ← algebraMap_smul (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) c (f (n ⊗ₜ[k] v))]
    exact cutSpectTensor_factor_tmul Q Λ θ β f hf (algebraMap k D c) n v
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The isomorphism `N ⊗ L ≅ P`, as a linear isomorphism. -/
def cutSpectTensorLinear : N ⊗[k] L ≃ₗ[k] P :=
  { f with map_smul' := cutSpectTensor_map_smul Q Λ θ β f hf }

/-- The slice `n ↦ n ⊗ v`, a map of modules over the factor algebra. -/
def cutSpectTensorSlice (v : L) : N₀ →ₗ[D] P₀ where
  toFun n := f ((show N from n) ⊗ₜ[k] v)
  map_add' n n' := by
    change f (((show N from n) + (show N from n')) ⊗ₜ[k] v) = _
    rw [TensorProduct.add_tmul, map_add]
    rfl
  map_smul' d n := cutSpectTensor_factor_tmul Q Λ θ β f hf d n v

omit [IsScalarTower k (cutSpectAlgebra Q Λ θ β C) N] [Module k P]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P] in
theorem cutSpectTensorSlice_apply (v : L) (n : N₀) :
    cutSpectTensorSlice Q Λ θ β f hf v n = f ((show N from n) ⊗ₜ[k] v) := rfl

omit [IsScalarTower k (cutSpectAlgebra Q Λ θ β C) N] [Module k P]
  [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P] in
theorem cutSpectTensorSlice_add (v v' : L) :
    cutSpectTensorSlice Q Λ θ β f hf (v + v') =
      cutSpectTensorSlice Q Λ θ β f hf v + cutSpectTensorSlice Q Λ θ β f hf v' :=
  LinearMap.ext fun n => by
    rw [LinearMap.add_apply, cutSpectTensorSlice_apply, cutSpectTensorSlice_apply,
      cutSpectTensorSlice_apply, TensorProduct.tmul_add, map_add]
    rfl

omit [Module k P] [IsScalarTower k (cutSpectAlgebra Q Λ θ β (C ⊗[k] B)) P] in
theorem cutSpectTensorSlice_smul (c : k) (v : L) :
    cutSpectTensorSlice Q Λ θ β f hf (c • v) =
      cutSpectTensorSlice Q Λ θ β f hf v ∘ₗ (c • (LinearMap.id : N₀ →ₗ[D] N₀)) :=
  LinearMap.ext fun n => by
    rw [LinearMap.comp_apply, cutSpectTensorSlice_apply, cutSpectTensorSlice_apply,
      ← TensorProduct.smul_tmul]
    rfl

/-- **The map `𝕊(N) ⊗ L → 𝕊(P)`**: `z ⊗ v` goes to the partial standardization of the slice
`n ↦ n ⊗ v`, applied to `z`. -/
def cutSpectTensorToStd : CutStandard Q Λ θ β N₀ ⊗[k] L →ₗ[k] CutStandard Q Λ θ β P₀ :=
  TensorProduct.lift (LinearMap.mk₂ k
    (fun z v => cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v) z)
    (fun z z' v => map_add _ z z')
    (fun c z v => map_smul _ c z)
    (fun z v v' => by
      rw [cutSpectTensorSlice_add]
      exact cutStandardMap_add Q Λ θ β _ _ z)
    (fun c z v => by
      rw [cutSpectTensorSlice_smul, cutStandardMap_comp, cutStandardMap_smul_id, map_smul]))

theorem cutSpectTensorToStd_tmul (z : CutStandard Q Λ θ β N₀) (v : L) :
    cutSpectTensorToStd Q Λ θ β f hf (z ⊗ₜ[k] v) =
      cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v) z := rfl

variable (hQ : KLRSymm Q)

/-- The action of `T^λ(θ + β)` on `𝕊(N) ⊗ L`, on the first factor. -/
def cutSpectTensorRep : T →ₐ[k] Module.End k (CutStandard Q Λ θ β N₀ ⊗[k] L) :=
  (Module.End.rTensorAlgHom k (CutStandard Q Λ θ β N₀) L).comp
    (cutStandardAction Q Λ θ β N₀ hQ)

theorem cutSpectTensorRep_tmul (t : T) (z : CutStandard Q Λ θ β N₀) (v : L) :
    cutSpectTensorRep Q Λ θ β hQ (C := C) (N := N) (L := L) t (z ⊗ₜ[k] v) =
      cutStandardAction Q Λ θ β N₀ hQ t z ⊗ₜ[k] v := rfl

theorem cutSpectTensorToStd_rep (t : T) (w : CutStandard Q Λ θ β N₀ ⊗[k] L) :
    cutSpectTensorToStd Q Λ θ β f hf
        (cutSpectTensorRep Q Λ θ β hQ (C := C) (N := N) (L := L) t w) =
      cutStandardAction Q Λ θ β P₀ hQ t (cutSpectTensorToStd Q Λ θ β f hf w) :=
  LinearMap.congr_fun (TensorProduct.ext' (R := k)
    (g := cutSpectTensorToStd Q Λ θ β f hf ∘ₗ
      cutSpectTensorRep Q Λ θ β hQ (C := C) (N := N) (L := L) t)
    (h := cutStandardAction Q Λ θ β P₀ hQ t ∘ₗ cutSpectTensorToStd Q Λ θ β f hf)
    fun z _ => cutStandardMap_action Q Λ θ β hQ _ t z) w

/-- The identity shuffle of `N`, tensored with `L`, on `P`. -/
def cutSpectTensorUnit : P₀ →ₗ[k] CutStandard Q Λ θ β N₀ ⊗[k] L :=
  LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀) ∘ₗ
    (cutSpectTensorLinear Q Λ θ β f hf).symm.toLinearMap

theorem cutSpectTensorUnit_apply (x : N ⊗[k] L) :
    cutSpectTensorUnit Q Λ θ β f hf (f x) =
      LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀) x :=
  congrArg (LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀))
    ((cutSpectTensorLinear Q Λ θ β f hf).symm_apply_apply x)

theorem isCutInputHom_cutSpectTensorUnit :
    IsCutInputHom Q Λ θ β P₀ (cutSpectTensorRep Q Λ θ β hQ (C := C) (N := N) (L := L))
      (cutSpectTensorUnit Q Λ θ β f hf) := by
  intro t p
  obtain ⟨x, rfl⟩ := EquivLike.surjective f p
  have h1 : (cutInputMap Q Λ θ β t • (show P₀ from f x) : P₀) =
      f (LinearMap.rTensor L (Algebra.lsmul k k N (ι C (cutInputMap Q Λ θ β t) 1)) x) :=
    cutSpectTensor_factor_smul Q Λ θ β f hf _ x
  refine (congrArg (cutSpectTensorUnit Q Λ θ β f hf) h1).trans ?_
  refine ((cutSpectTensorUnit_apply Q Λ θ β f hf _).trans ?_).trans
    (congrArg _ (cutSpectTensorUnit_apply Q Λ θ β f hf x)).symm
  change (LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀) ∘ₗ LinearMap.rTensor L
      (Algebra.lsmul k k N (ι C (cutInputMap Q Λ θ β t) 1))) x =
    (LinearMap.rTensor L (cutStandardAction Q Λ θ β N₀ hQ
      (cutAffineMap Q Λ θ β (concat (stendhalQ Q Λ) _ _ t))) ∘ₗ
      LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀)) x
  refine (LinearMap.congr_fun (LinearMap.rTensor_comp L _ _) x).symm.trans
    (Eq.trans ?_ (LinearMap.congr_fun (LinearMap.rTensor_comp L _ _) x))
  congr 2
  exact LinearMap.ext fun n => (cutStandardAction_concat_unit Q Λ θ β N₀ hQ t n).symm

/-- The map `𝕊(P) → 𝕊(N) ⊗ L` induced by the identity shuffle. -/
def cutSpectTensorFromStd : CutStandard Q Λ θ β P₀ →ₗ[k] CutStandard Q Λ θ β N₀ ⊗[k] L :=
  cutStandardLift Q Λ θ β (cutSpectTensorUnit Q Λ θ β f hf)
    (isCutInputHom_cutSpectTensorUnit Q Λ θ β f hf hQ)

/-- The partial standardization of a map on the identity shuffle. -/
theorem cutStandardMap_unit {X Y : Type*} [AddCommGroup X] [Module k X] [Module D X]
    [IsScalarTower k D X] [AddCommGroup Y] [Module k Y] [Module D Y] [IsScalarTower k D Y]
    (g : X →ₗ[D] Y) (x : X) :
    cutStandardMap Q Λ θ β g (cutStandardUnit Q Λ θ β X x) =
      cutStandardUnit Q Λ θ β Y (g x) := rfl

theorem cutSpectTensorToStd_unit (x : N ⊗[k] L) :
    cutSpectTensorToStd Q Λ θ β f hf (LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀) x) =
      cutStandardUnit Q Λ θ β P₀ (f x) :=
  LinearMap.congr_fun (TensorProduct.ext' (R := k)
    (g := cutSpectTensorToStd Q Λ θ β f hf ∘ₗ LinearMap.rTensor L (cutStandardUnit Q Λ θ β N₀))
    (h := cutStandardUnit Q Λ θ β P₀ ∘ₗ
      ((cutSpectTensorLinear Q Λ θ β f hf).toLinearMap : N ⊗[k] L →ₗ[k] P₀))
    fun _ _ => rfl) x

theorem cutSpectTensorFromStd_unit (v : L) (n : N₀) :
    cutSpectTensorFromStd Q Λ θ β f hf hQ
        (cutStandardUnit Q Λ θ β P₀ (f ((show N from n) ⊗ₜ[k] v))) =
      cutStandardUnit Q Λ θ β N₀ n ⊗ₜ[k] v :=
  (cutStandardLift_unit Q Λ θ β _ _ _).trans
    ((cutSpectTensorUnit_apply Q Λ θ β f hf ((show N from n) ⊗ₜ[k] v)).trans
      (LinearMap.rTensor_tmul L (cutStandardUnit Q Λ θ β N₀) v n))

theorem cutSpectTensorFromStd_toStd :
    cutSpectTensorFromStd Q Λ θ β f hf hQ ∘ₗ cutSpectTensorToStd Q Λ θ β f hf =
      LinearMap.id :=
  TensorProduct.ext' fun z v => LinearMap.congr_fun (cutStandardLift_unique Q Λ θ β hQ
    (N := N₀) (σ := cutSpectTensorRep Q Λ θ β hQ (C := C) (N := N) (L := L))
    (h := cutSpectTensorFromStd Q Λ θ β f hf hQ ∘ₗ
      cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v))
    (h' := (TensorProduct.mk k (CutStandard Q Λ θ β N₀) L).flip v)
    (fun t z => (congrArg (cutSpectTensorFromStd Q Λ θ β f hf hQ)
      (cutStandardMap_action Q Λ θ β hQ _ t z)).trans
        (cutStandardLift_action Q Λ θ β hQ _ _ t _))
    (fun _ _ => rfl)
    (fun n => (congrArg (cutSpectTensorFromStd Q Λ θ β f hf hQ)
      (cutStandardMap_unit Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v) n)).trans
        (cutSpectTensorFromStd_unit Q Λ θ β f hf hQ v n))) z

theorem cutSpectTensorToStd_fromStd :
    cutSpectTensorToStd Q Λ θ β f hf ∘ₗ cutSpectTensorFromStd Q Λ θ β f hf hQ =
      LinearMap.id :=
  cutStandardLift_unique Q Λ θ β hQ (N := P₀) (σ := cutStandardAction Q Λ θ β P₀ hQ)
    (fun t w => (congrArg (cutSpectTensorToStd Q Λ θ β f hf)
      (cutStandardLift_action Q Λ θ β hQ _ _ t w)).trans
        (cutSpectTensorToStd_rep Q Λ θ β f hf hQ t _))
    (fun _ _ => rfl)
    (fun p => by
      obtain ⟨x, rfl⟩ := EquivLike.surjective f p
      exact (congrArg (cutSpectTensorToStd Q Λ θ β f hf)
        ((cutStandardLift_unit Q Λ θ β _ _ _).trans
          (cutSpectTensorUnit_apply Q Λ θ β f hf x))).trans
        (cutSpectTensorToStd_unit Q Λ θ β f hf x))

/-- **The partial standardization commutes with tensoring the spectator**: `𝕊(N) ⊗ L ≅ 𝕊(P)`
for `P ≅ N ⊗ L`. -/
def cutSpectTensorEquiv : CutStandard Q Λ θ β N₀ ⊗[k] L ≃ₗ[k] CutStandard Q Λ θ β P₀ :=
  LinearEquiv.ofLinearMap (cutSpectTensorToStd Q Λ θ β f hf) (cutSpectTensorFromStd Q Λ θ β f hf hQ)
    (cutSpectTensorToStd_fromStd Q Λ θ β f hf hQ) (cutSpectTensorFromStd_toStd Q Λ θ β f hf hQ)

theorem cutSpectTensorEquiv_tmul (z : CutStandard Q Λ θ β N₀) (v : L) :
    cutSpectTensorEquiv Q Λ θ β f hf hQ (z ⊗ₜ[k] v) =
      cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v) z := rfl

/-- **The isomorphism `𝕊(N) ⊗ L ≅ 𝕊(P)` intertwines the actions**: `(t ⊗ c) z ⊗ b v` goes to
`(t ⊗ (c ⊗ b))` applied to the image of `z ⊗ v`. -/
theorem cutSpectTensorEquiv_smul (t : T) (c : C) (b : B) (z : CutStandard Q Λ θ β N₀)
    (v : L) :
    cutSpectTensorEquiv Q Λ θ β f hf hQ
        (cutSpectStandardAction Q Λ θ β C N hQ (t ⊗ₜ[k] c) z ⊗ₜ[k] (b • v)) =
      cutSpectStandardAction Q Λ θ β (C ⊗[k] B) P hQ (t ⊗ₜ[k] (c ⊗ₜ[k] b))
        (cutSpectTensorEquiv Q Λ θ β f hf hQ (z ⊗ₜ[k] v)) := by
  rw [cutSpectTensorEquiv_tmul, cutSpectTensorEquiv_tmul]
  change cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf (b • v))
      (cutStandardAction Q Λ θ β N₀ hQ t
        (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β C N c) z)) =
    cutStandardAction Q Λ θ β P₀ hQ t
      (cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β (C ⊗[k] B) P (c ⊗ₜ[k] b))
        (cutStandardMap Q Λ θ β (cutSpectTensorSlice Q Λ θ β f hf v) z))
  rw [cutStandardMap_action, ← cutStandardMap_comp, ← cutStandardMap_comp]
  exact congrArg (fun g => cutStandardAction Q Λ θ β P₀ hQ t (cutStandardMap Q Λ θ β g z))
    (LinearMap.ext fun n => hf 1 c b n v)

end Cut

end Categorification.Stendhal
