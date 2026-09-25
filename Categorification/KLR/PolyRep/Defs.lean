/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Basic
import Categorification.Algebra.DividedDifference

/-!
# The polynomial representation of `R(ν)`: operators

KL I §2.3 (arXiv:0803.4121v2) defines an action of `R(ν)` on
`Pol_ν = ⊕_{i ∈ Seq(ν)} Pol_i`, `Pol_i = ℤ[x_1(i), …, x_m(i)]`. Here all `Pol_i` are
identified with `MvPolynomial (Fin m) k`, the variable `X a` being `x_{a+1}(i)`,
and `Pol_ν` is the product `Seq ν → MvPolynomial (Fin m) k`.

The action depends on a choice of polynomials `P i j ∈ k[u, v]` (for KL I:
`P i j = u + v` if the edge between `i` and `j` is oriented `i → j`, and `P i j = 1`
otherwise). The crossing `ψ_k` sends `f ∈ Pol_i` to the component `s_k i` as

* `∂_k f = (f - s_k f) / (x_k - x_{k+1})` if `i_k = i_{k+1}`;
* `P_{i_k i_{k+1}}(x_k, x_{k+1}) · s_k f` otherwise.

The defining relations of `R(ν)` hold provided
`Q i j (u, v) = P j i (u, v) * P i j (v, u)` for `i ≠ j`; see `PolyRep.Sound`.

This file only defines the operators; the relations are checked elsewhere.
-/

namespace Categorification.KLR.PolyRep

open MvPolynomial TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-- The underlying module `Pol_ν = ∏_{i ∈ Seq ν} k[x_1, …, x_m]`. -/
abbrev Pol (k : Type*) [CommRing k] (ν : Multiset I) : Type _ :=
  Seq ν → MvPolynomial (Fin (Multiset.card ν)) k

variable {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The idempotent `1_i` acts as the projection onto the `i`-th component. -/
noncomputable def opE (i : Seq ν) : Module.End k (Pol k ν) :=
  (LinearMap.single k (fun _ => MvPolynomial (Fin m) k) i).comp (LinearMap.proj i)

/-- The dot `x_a` acts by multiplication by `X a` in every component. -/
noncomputable def opX (a : Fin m) : Module.End k (Pol k ν) :=
  LinearMap.pi fun j => (LinearMap.mulLeft k (X a)).comp (LinearMap.proj j)

/-- The action of the crossing `ψ_j` (`j + 1 < m`) on the component of the input
sequence `i`, landing in the component `s_j i`. -/
noncomputable def crossComp (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m)
    (i : Seq ν) : MvPolynomial (Fin m) k →ₗ[k] MvPolynomial (Fin m) k :=
  if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then
    ddiff ⟨j, by omega⟩ ⟨j + 1, h⟩
  else
    (LinearMap.mulLeft k (rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩]
        (P (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)))).comp
      (rename (sadj m j)).toLinearMap

/-- The crossing `ψ_j` acts by `crossComp` from component `s_j t` to component `t`
(`s_j` is an involution), and by zero if `j + 1 ≥ m`. -/
noncomputable def opΨ (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) : Module.End k (Pol k ν) :=
  if h : j + 1 < m then
    LinearMap.pi fun t => (crossComp P j h (sadj m j • t)).comp (LinearMap.proj (sadj m j • t))
  else 0

@[simp] theorem opE_apply (i : Seq ν) (f : Pol k ν) (t : Seq ν) :
    opE i f t = if t = i then f i else 0 := by
  simp only [opE, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearMap.coe_single, Pi.single_apply]

omit [DecidableEq I] in
@[simp] theorem opX_apply (a : Fin m) (f : Pol k ν) (t : Seq ν) :
    opX a f t = X a * f t := rfl

theorem opΨ_apply (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m)
    (f : Pol k ν) (t : Seq ν) :
    opΨ P j f t = crossComp P j h (sadj m j • t) (f (sadj m j • t)) := by
  simp [opΨ, h]

end Categorification.KLR.PolyRep
