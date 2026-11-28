/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A module of the middle block as a spectator

Webster, arXiv:1309.3796v3, Lemma 7.19 (K): the input `Z ⊠ L` of the partial standardization
`S_+` of `λ⁺`. For `k`-algebras `A`, `B`, `C`, a module `Y` over `A ⊗ C` (the outer blocks) and a
module `L` over `B` (the middle block), `Y ⊗_k L` is a module over `A ⊗ (B ⊗ C)`
(`MidSpect`), with `(a ⊗ (b ⊗ c)) (y ⊗ v) = ((a ⊗ c) y) ⊗ (b v)` (`midSpect_tmul_smul`).

## Main definitions

* `Categorification.midSpectRep`: the representation of `A ⊗ (B ⊗ C)` on `Y ⊗_k L`.
* `Categorification.MidSpect`: `Y ⊗_k L` as a module over `A ⊗ (B ⊗ C)`.
* `Categorification.midSpectMap`: its functoriality in `Y`.
-/

noncomputable section

namespace Categorification

open scoped TensorProduct
open Algebra.TensorProduct

variable {k : Type*} [CommRing k]

section Generic

variable (Y L : Type*) [AddCommGroup Y] [Module k Y] [AddCommGroup L] [Module k L]

theorem commute_rTensor_lTensor (f : Module.End k Y) (g : Module.End k L) :
    Commute (f.rTensor L) (g.lTensor Y) := by
  change f.rTensor L ∘ₗ g.lTensor Y = g.lTensor Y ∘ₗ f.rTensor L
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

/-- **`Y ⊗_k L`, as the spectator module over three blocks** (see `midSpectRep`). -/
def MidSpect : Type _ := Y ⊗[k] L

instance : AddCommGroup (MidSpect (k := k) Y L) := inferInstanceAs (AddCommGroup (Y ⊗[k] L))
instance : Module k (MidSpect (k := k) Y L) := inferInstanceAs (Module k (Y ⊗[k] L))

variable {Y L} in
/-- The element `y ⊗ v` of `MidSpect (k := k) Y L`. -/
def midSpectTmul (y : Y) (v : L) : MidSpect (k := k) Y L := (y ⊗ₜ[k] v : Y ⊗[k] L)

end Generic

variable {A B C : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [Ring C] [Algebra k C]
  (Y : Type*) [AddCommGroup Y] [Module k Y] [Module (A ⊗[k] C) Y] [IsScalarTower k (A ⊗[k] C) Y]
  (L : Type*) [AddCommGroup L] [Module k L]

/-- The outer blocks acting on `Y`. -/
abbrev midSpectOuter : A ⊗[k] C →ₐ[k] Module.End k Y := Algebra.lsmul k k Y

/-- The first block acting on `Y ⊗ L`. -/
abbrev midSpectA : A →ₐ[k] Module.End k (Y ⊗[k] L) :=
  (Module.End.rTensorAlgHom k Y L).comp
    ((midSpectOuter (k := k) (A := A) (C := C) Y).comp (includeLeft : A →ₐ[k] A ⊗[k] C))

/-- The last block acting on `Y ⊗ L`. -/
abbrev midSpectC : C →ₐ[k] Module.End k (Y ⊗[k] L) :=
  (Module.End.rTensorAlgHom k Y L).comp
    ((midSpectOuter (k := k) (A := A) (C := C) Y).comp (includeRight : C →ₐ[k] A ⊗[k] C))

theorem commute_midSpectA_midSpectC (a : A) (c : C) :
    Commute (midSpectA (k := k) (C := C) Y L a) (midSpectC (k := k) (A := A) Y L c) := by
  let O := midSpectOuter (k := k) (A := A) (C := C) Y
  have h : Commute (O (a ⊗ₜ[k] (1 : C))) (O ((1 : A) ⊗ₜ[k] c)) := by
    change O _ * O _ = O _ * O _
    rw [← map_mul, ← map_mul, tmul_mul_tmul, tmul_mul_tmul, mul_one, one_mul, mul_one, one_mul]
  exact h.map (Module.End.rTensorAlgHom k Y L)

variable [Module B L] [IsScalarTower k B L]

/-- The middle block acting on `Y ⊗ L`. -/
abbrev midSpectB : B →ₐ[k] Module.End k (Y ⊗[k] L) :=
  (Module.End.lTensorAlgHom k L Y).comp (Algebra.lsmul k k L)

/-- The last two blocks acting on `Y ⊗ L`. -/
def midSpectBC : B ⊗[k] C →ₐ[k] Module.End k (Y ⊗[k] L) :=
  lift (midSpectB (k := k) Y L) (midSpectC (k := k) (A := A) Y L) fun _ _ =>
    (commute_rTensor_lTensor (k := k) Y L _ _).symm

theorem midSpectBC_tmul (b : B) (c : C) :
    midSpectBC (k := k) (A := A) Y L (b ⊗ₜ c) =
      midSpectB (k := k) Y L b * midSpectC (k := k) (A := A) Y L c :=
  lift_tmul _ _ _ b c

theorem commute_midSpectA_midSpectBC (a : A) (x : B ⊗[k] C) :
    Commute (midSpectA (k := k) (C := C) Y L a) (midSpectBC (k := k) (A := A) Y L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b c =>
    rw [midSpectBC_tmul]
    exact (commute_rTensor_lTensor (k := k) Y L _ _).mul_right
      (commute_midSpectA_midSpectC (A := A) Y L a c)
  | add x y hx hy => rw [map_add]; exact hx.add_right hy

/-- **The representation of the three blocks on `Y ⊗ L`.** -/
def midSpectRep : A ⊗[k] (B ⊗[k] C) →ₐ[k] Module.End k (Y ⊗[k] L) :=
  lift (midSpectA (k := k) (C := C) Y L) (midSpectBC (k := k) (A := A) Y L)
    (commute_midSpectA_midSpectBC (A := A) Y L)

instance : Module (A ⊗[k] (B ⊗[k] C)) (MidSpect (k := k) Y L) :=
  Module.compHom (Y ⊗[k] L) (midSpectRep (k := k) (A := A) (B := B) (C := C) Y L).toRingHom

variable {Y L}

variable (Y L) in
theorem midSpect_smul_def (x : A ⊗[k] (B ⊗[k] C)) (z : MidSpect (k := k) Y L) :
    x • z =
      (midSpectRep (k := k) (A := A) (B := B) (C := C) Y L x (show Y ⊗[k] L from z) :
        Y ⊗[k] L) := rfl

instance : IsScalarTower k (A ⊗[k] (B ⊗[k] C)) (MidSpect (k := k) Y L) where
  smul_assoc c x z := by
    rw [midSpect_smul_def, midSpect_smul_def, map_smul]
    rfl

variable (Y L) in
/-- The representation on pure tensors. -/
theorem midSpectRep_tmul (a : A) (b : B) (c : C) (y : Y) (v : L) :
    midSpectRep (k := k) Y L (a ⊗ₜ[k] (b ⊗ₜ[k] c)) (y ⊗ₜ[k] v) =
      ((a ⊗ₜ[k] c : A ⊗[k] C) • y) ⊗ₜ[k] (b • v) := by
  rw [midSpectRep, lift_tmul, midSpectBC_tmul]
  change (midSpectA (k := k) (C := C) Y L a) ((midSpectB (k := k) Y L b)
    ((midSpectC (k := k) (A := A) Y L c) (y ⊗ₜ[k] v))) = _
  change (((a ⊗ₜ[k] (1 : C)) : A ⊗[k] C) • (((1 : A) ⊗ₜ[k] c : A ⊗[k] C) • y)) ⊗ₜ[k] (b • v) = _
  rw [smul_smul, tmul_mul_tmul, mul_one, one_mul]

/-- **The action on pure tensors**: `(a ⊗ (b ⊗ c)) (y ⊗ v) = ((a ⊗ c) y) ⊗ (b v)`. -/
theorem midSpect_tmul_smul (a : A) (b : B) (c : C) (y : Y) (v : L) :
    (a ⊗ₜ[k] (b ⊗ₜ[k] c) : A ⊗[k] (B ⊗[k] C)) • midSpectTmul (k := k) y v =
      midSpectTmul (k := k) ((a ⊗ₜ[k] c : A ⊗[k] C) • y) (b • v) :=
  midSpectRep_tmul Y L a b c y v

variable {Y' : Type*} [AddCommGroup Y'] [Module k Y'] [Module (A ⊗[k] C) Y']
  [IsScalarTower k (A ⊗[k] C) Y']

/-- A map of modules over the outer blocks commutes with the representation. -/
theorem rTensor_comp_midSpectRep (g : Y →ₗ[A ⊗[k] C] Y') (x : A ⊗[k] (B ⊗[k] C)) :
    (g.restrictScalars k).rTensor L ∘ₗ midSpectRep (k := k) Y L x =
      midSpectRep (k := k) Y' L x ∘ₗ (g.restrictScalars k).rTensor L := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hx']
  | tmul a bc =>
    induction bc using TensorProduct.inductionOn with
    | add u u' hu hu' =>
      rw [TensorProduct.tmul_add, map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hu,
        hu']
    | tmul b c =>
      refine TensorProduct.ext' fun y v => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, midSpectRep_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, midSpectRep_tmul, LinearMap.restrictScalars_apply,
        LinearMap.restrictScalars_apply, g.map_smul]

/-- **Functoriality of the spectator construction in `Y`.** -/
def midSpectMap (g : Y →ₗ[A ⊗[k] C] Y') :
    MidSpect (k := k) Y L →ₗ[A ⊗[k] (B ⊗[k] C)] MidSpect (k := k) Y' L where
  toFun z := ((g.restrictScalars k).rTensor L (show Y ⊗[k] L from z) : Y' ⊗[k] L)
  map_add' _ _ := map_add _ _ _
  map_smul' x z := LinearMap.congr_fun (rTensor_comp_midSpectRep g x) z

theorem midSpectMap_tmul (g : Y →ₗ[A ⊗[k] C] Y') (y : Y) (v : L) :
    midSpectMap (B := B) g (midSpectTmul (k := k) y v) = midSpectTmul (k := k) (g y) v := rfl

end Categorification
