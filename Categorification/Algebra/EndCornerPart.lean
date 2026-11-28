/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CornerCoinduced

/-!
# The corner of a module cut out by a non-unital action

Used for Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (trace half: the dévissage of
`Hom_W(L', e_s S_+(X))` along the head-strand filtration).

Let `ψ : R →ₙ+* End_k(V)` be a non-unital ring map, for instance a diagram placed on the window
of the cap generators at one loading, and `ε` an endomorphism commuting with every `ψ(g)` with
`ψ(1) ε = ε`, for instance the image of the red-ordered idempotent. Then the fixed points
`ε V` of `ε` form an `R`-module (`EndCornerPart`). A `k`-submodule `F` of `V` preserved by
every `ψ(g)` cuts out an `R`-submodule `F ∩ ε V` (`endCornerSub`). For a finite filtration by
such submodules whose layers above the first are right orthogonal to `L`, composing with the
projection to the first layer is a bijection on `Hom_R(L, -)`
(`bijective_mkQ_comp_of_endCornerFilt`, from `bijective_mkQ_comp_of_layers`).

## Main definitions and results

* `EndCornerPart`, `endCornerSub`, `bijective_mkQ_comp_of_endCornerFilt`.
-/

universe u

namespace Categorification

variable {k : Type*} [CommRing k] {R : Type u} [Ring R] {V : Type u} [AddCommGroup V]
  [Module k V] (ψ : R →ₙ+* Module.End k V) (ε : Module.End k V)
  (hcomm : ∀ g, ε * ψ g = ψ g * ε) (hone : ψ 1 * ε = ε)

/-- The fixed points of `ε`. -/
def endCornerFixed : AddSubgroup V where
  carrier := {v | ε v = v}
  add_mem' {x y} hx hy := by
    change ε (x + y) = x + y
    rw [map_add, show ε x = x from hx, show ε y = y from hy]
  zero_mem' := map_zero _
  neg_mem' {x} hx := by
    change ε (-x) = -x
    rw [map_neg, show ε x = x from hx]

/-- **The corner `ε V`**, an `R`-module through `ψ`. -/
@[nolint unusedArguments]
def EndCornerPart (_hcomm : ∀ g, ε * ψ g = ψ g * ε) (_hone : ψ 1 * ε = ε) : Type u :=
  endCornerFixed ε

instance : AddCommGroup (EndCornerPart ψ ε hcomm hone) :=
  inferInstanceAs (AddCommGroup (endCornerFixed ε))

namespace EndCornerPart

variable {ψ ε hcomm hone}

/-- The underlying element of `V`. -/
def val (x : EndCornerPart ψ ε hcomm hone) : V := (show endCornerFixed ε from x).1

theorem prop (x : EndCornerPart ψ ε hcomm hone) : ε x.val = x.val :=
  (show endCornerFixed ε from x).2

/-- An element of `V` fixed by `ε`. -/
def mk (v : V) (h : ε v = v) : EndCornerPart ψ ε hcomm hone := (⟨v, h⟩ : endCornerFixed ε)

@[simp] theorem val_mk (v : V) (h : ε v = v) :
    (mk v h : EndCornerPart ψ ε hcomm hone).val = v := rfl

theorem ext {x y : EndCornerPart ψ ε hcomm hone} (h : x.val = y.val) : x = y :=
  Subtype.ext (p := fun v => v ∈ endCornerFixed ε) h

@[simp] theorem val_add (x y : EndCornerPart ψ ε hcomm hone) : (x + y).val = x.val + y.val := rfl

@[simp] theorem val_zero : (0 : EndCornerPart ψ ε hcomm hone).val = 0 := rfl

theorem smul_mem (g : R) (x : EndCornerPart ψ ε hcomm hone) : ε (ψ g x.val) = ψ g x.val := by
  rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, x.prop]

instance : Module R (EndCornerPart ψ ε hcomm hone) where
  smul g x := mk (ψ g x.val) (smul_mem g x)
  one_smul x := ext (by
    change ψ 1 x.val = x.val
    conv_lhs => rw [← x.prop]
    rw [← Module.End.mul_apply, hone, x.prop])
  mul_smul g h x := ext (by
    change ψ (g * h) x.val = ψ g (ψ h x.val)
    rw [map_mul, Module.End.mul_apply])
  smul_zero g := ext (map_zero (ψ g))
  smul_add g x y := ext (map_add (ψ g) x.val y.val)
  add_smul g h x := ext (by
    change ψ (g + h) x.val = ψ g x.val + ψ h x.val
    rw [map_add, LinearMap.add_apply])
  zero_smul x := ext (by
    change ψ 0 x.val = 0
    rw [map_zero, LinearMap.zero_apply])

@[simp] theorem val_smul (g : R) (x : EndCornerPart ψ ε hcomm hone) : (g • x).val = ψ g x.val := rfl

end EndCornerPart

/-- **A `k`-submodule preserved by `ψ` cuts out an `R`-submodule** of the corner. -/
def endCornerSub (F : Submodule k V) (hF : ∀ g : R, ∀ v ∈ F, ψ g v ∈ F) :
    Submodule R (EndCornerPart ψ ε hcomm hone) where
  carrier := {x | x.val ∈ F}
  add_mem' hx hy := F.add_mem hx hy
  zero_mem' := F.zero_mem
  smul_mem' g _ hx := hF g _ hx

theorem mem_endCornerSub {F : Submodule k V} {hF : ∀ g : R, ∀ v ∈ F, ψ g v ∈ F}
    {x : EndCornerPart ψ ε hcomm hone} : x ∈ endCornerSub ψ ε hcomm hone F hF ↔ x.val ∈ F := Iff.rfl

theorem endCornerSub_mono {F F' : Submodule k V} {hF : ∀ g : R, ∀ v ∈ F, ψ g v ∈ F}
    {hF' : ∀ g : R, ∀ v ∈ F', ψ g v ∈ F'} (h : F ≤ F') :
    endCornerSub ψ ε hcomm hone F hF ≤ endCornerSub ψ ε hcomm hone F' hF' := fun _ hx => h hx

theorem endCornerSub_bot {hF : ∀ g : R, ∀ v ∈ (⊥ : Submodule k V), ψ g v ∈ (⊥ : Submodule k V)} :
    endCornerSub ψ ε hcomm hone ⊥ hF = ⊥ := by
  ext x
  rw [mem_endCornerSub, Submodule.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => EndCornerPart.ext h, fun h => by rw [h]; rfl⟩

/-- **Dévissage on the corner**: let `G` be an antitone family of `k`-submodules of `V`
preserved by `ψ`, with `G n = 0`. If the layers of `G ∩ ε V` from the first on are right
orthogonal to `L`, then composing with the projection to `ε V / (G 1 ∩ ε V)` is a
bijection on `Hom_R(L, -)`. -/
theorem bijective_mkQ_comp_of_endCornerFilt {L : Type u} [AddCommGroup L] [Module R L]
    (G : ℕ → Submodule k V) (hG : ∀ m, ∀ g : R, ∀ v ∈ G m, ψ g v ∈ G m)
    (hanti : ∀ m, G (m + 1) ≤ G m) (n : ℕ) (hn : G n = ⊥)
    (hlay : ∀ m, 1 ≤ m → IsRightOrthogonal R L
      ((endCornerSub ψ ε hcomm hone (G m) (hG m)).map
        (endCornerSub ψ ε hcomm hone (G (m + 1)) (hG (m + 1))).mkQ)) :
    Function.Bijective fun h : L →ₗ[R] EndCornerPart ψ ε hcomm hone =>
      (endCornerSub ψ ε hcomm hone (G 1) (hG 1)).mkQ ∘ₗ h := by
  refine bijective_mkQ_comp_of_layers (fun m => endCornerSub ψ ε hcomm hone (G m) (hG m))
    (fun m => endCornerSub_mono ψ ε hcomm hone (hanti m)) n ?_ hlay
  ext x
  rw [mem_endCornerSub, hn, Submodule.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => EndCornerPart.ext h, fun h => by rw [h]; rfl⟩

end Categorification
