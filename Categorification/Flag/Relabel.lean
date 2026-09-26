/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Crossing
import Categorification.Flag.Bubbles

/-!
# Relabelling Borel models

The Borel model of `H_k` (`Categorification.Flag.Borel`) depends on a choice of a labelled set of
variables; the rings `H_{k^{±i}}` of the composition model (`ERing`) use the variables `Gen d`
of their own composition `d`, while the computations of `Categorification.Flag.Crossing` and
`Categorification.Flag.AdjacentCrossing` use one set of variables for all strands. This file
provides the canonical identifications between the two.

## Main results

* `borelCongr_refineHom` : relabelling commutes with the forgetful maps `refineHom`;
* `borelCongr_xiS` : relabelling sends the class of `x_v` to the class of `x_{e v}`;
* `relabel S S' v v'` : a label-preserving bijection with `v ↦ v'` (`relabel_lab`,
  `relabel_self`, `relabel_split`), for labellings with the same block sizes;
* `algHom_H_ext` : `K`-algebra maps out of `H_d` agree if they agree on the generators
  `x(d)_{j,α}`;
* `borelEquivH'_symm_x` : the canonical isomorphism `H_d ≅ BorelRing lab` sends `x_{j,α}` to the
  class of `e_α` of block `j`.
* `card_moveLab_general` : the block sizes after moving a variable.
-/

noncomputable section

namespace Categorification.Flag

open MvPolynomial

section Congr

variable (k : Type*) [Field k] {V V' : Type*} [Fintype V] [Fintype V']

/-- **Relabelling commutes with the forgetful maps.** -/
theorem borelCongr_refineHom {J₁ J₂ : Type*} {F : V → J₁} {F' : V' → J₁} {C : V → J₂}
    {C' : V' → J₂} (e : V ≃ V') (hF : ∀ v, F' (e v) = F v) (hC : ∀ v, C' (e v) = C v)
    (h : Refines F C) (h' : Refines F' C') (z : BorelRing k C) :
    borelCongr k e hF (refineHom k h z) = refineHom k h' (borelCongr k e hC z) := by
  obtain ⟨a, rfl⟩ := mkB_surjective C z
  rw [refineHom_mk h a ⟨a, labelInvariants_mono k h a.2⟩ rfl,
    borelCongr_mk k e hF _ ⟨rename e (a : MvPolynomial V k),
      rename_mem_labelInvariants e hF (labelInvariants_mono k h a.2)⟩ rfl,
    borelCongr_mk k e hC a ⟨rename e (a : MvPolynomial V k),
      rename_mem_labelInvariants e hC a.2⟩ rfl,
    refineHom_mk h' _ ⟨rename e (a : MvPolynomial V k),
      labelInvariants_mono k h' (rename_mem_labelInvariants e hC a.2)⟩ rfl]

variable {k}

/-- **Relabelling sends `x_v` to `x_{e v}`.** -/
theorem borelCongr_xiS {J₁ : Type*} {F : V → J₁} {F' : V' → J₁} (e : V ≃ V')
    (hF : ∀ v, F' (e v) = F v) (v : V) (hv : ∀ w, F w = F v → w = v)
    (hv' : ∀ w, F' w = F' (e v) → w = e v) :
    borelCongr k e hF (xiS k F v hv) = xiS k F' (e v) hv' :=
  borelCongr_mk k e hF _ _ (rename_X _ _)

end Congr

/-! ### Label-preserving bijections -/

section Relabel

variable {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] {J : Type*}
  [DecidableEq J]

theorem card_fibre_split_none (S : V → J) (v : V) :
    Fintype.card {x // splitLab S v x = none} = 1 := by
  rw [card_fibre_eq_card_labSet, labSet_split_none, Finset.card_singleton]

theorem card_fibre_split_some (S : V → J) (v : V) (j : J) :
    Fintype.card {x // splitLab S v x = some j} =
      Fintype.card {x // S x = j} - if j = S v then 1 else 0 := by
  rw [card_fibre_eq_card_labSet, card_fibre_eq_card_labSet, card_split_some]

variable (S : V → J) (S' : V' → J) (v : V) (v' : V')
  (hc : ∀ j, Fintype.card {x // S x = j} = Fintype.card {x // S' x = j}) (hv : S v = S' v')

include hc hv in
theorem card_fibre_split_eq (o : Option J) :
    Fintype.card {x // splitLab S v x = o} = Fintype.card {x // splitLab S' v' x = o} := by
  rcases o with _ | j
  · rw [card_fibre_split_none, card_fibre_split_none]
  · rw [card_fibre_split_some, card_fibre_split_some, hc, hv]

/-- **A label-preserving bijection sending `v` to `v'`**, for labellings with the same block sizes
and `S v = S' v'`. -/
def relabel : V ≃ V' :=
  Equiv.ofFiberEquiv (f := splitLab S v) (g := splitLab S' v')
    fun o => Fintype.equivOfCardEq (card_fibre_split_eq S S' v v' hc hv o)

theorem relabel_split (x : V) :
    splitLab S' v' (relabel S S' v v' hc hv x) = splitLab S v x :=
  Equiv.ofFiberEquiv_map _ x

theorem relabel_self : relabel S S' v v' hc hv v = v' := by
  have h := relabel_split S S' v v' hc hv v
  rw [splitLab_self] at h
  exact splitLab_eq_none.1 h

theorem relabel_ne {x : V} (hx : x ≠ v) : relabel S S' v v' hc hv x ≠ v' := by
  intro h
  have h2 := relabel_self S S' v v' hc hv
  exact hx ((relabel S S' v v' hc hv).injective (h.trans h2.symm))

theorem relabel_lab (x : V) : S' (relabel S S' v v' hc hv x) = S x := by
  by_cases hx : x = v
  · subst hx; rw [relabel_self, hv]
  · have h := relabel_split S S' v v' hc hv x
    rw [splitLab_of_ne (relabel_ne S S' v v' hc hv hx), splitLab_of_ne hx] at h
    exact Option.some_injective _ h

theorem relabel_move (j : J) (x : V) :
    moveLab S' v' j (relabel S S' v v' hc hv x) = moveLab S v j x := by
  by_cases hx : x = v
  · subst hx; rw [relabel_self, moveLab_self, moveLab_self]
  · rw [moveLab, Function.update_of_ne (relabel_ne S S' v v' hc hv hx),
      relabel_lab S S' v v' hc hv, moveLab, Function.update_of_ne hx]

end Relabel

/-! ### Maps out of `H_d` -/

section Hmaps

variable {K : Type*} [Field K]

/-- **`K`-algebra maps out of `H_d` are determined by the generators `x(d)_{j,α}`.** -/
theorem algHom_H_ext {n : ℕ} {d : Fin n → ℕ} {X : Type*} [Ring X] [Algebra K X]
    {f g : H K d →ₐ[K] X} (h : ∀ j α, f (x K d j α) = g (x K d j α)) : f = g :=
  AlgHom.ext_of_adjoin_eq_top (adjoin_x d) fun _ ⟨p, hp⟩ => hp ▸ h p.1 p.2

theorem borelEquivH'_symm_x {V : Type*} [Fintype V] {n : ℕ} (lab : V → Fin n) (d : Fin n → ℕ)
    (hd : ∀ j, Fintype.card {v // lab v = j} = d j) (j : Fin n) (α : ℕ) :
    (borelEquivH' K lab d hd).symm (x K d j α) = xB K lab j α := by
  rw [AlgEquiv.symm_apply_eq, borelEquivH'_xB]

theorem borelEquivH'_symm_xbar {V : Type*} [Fintype V] {n : ℕ} (lab : V → Fin n)
    (d : Fin n → ℕ) (hd : ∀ j, Fintype.card {v // lab v = j} = d j) (j : Fin n) (α : ℕ) :
    (borelEquivH' K lab d hd).symm (xbar K d j α) = xbarB K lab j α := by
  rw [AlgEquiv.symm_apply_eq, borelEquivH'_xbarB]

theorem hEquiv_eq_borelEquivH'_symm {n : ℕ} (d : Fin n → ℕ) (z : H K d) :
    hEquiv K d z = (borelEquivH' K (Sigma.fst : Gen d → Fin n) d (card_fibre_sigma (d := d))).symm z := by
  have : (hEquiv K d).toAlgHom =
      (borelEquivH' K (Sigma.fst : Gen d → Fin n) d (card_fibre_sigma (d := d))).symm.toAlgHom :=
    algHom_H_ext fun j α => by
      simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, hEquiv_x, borelEquivH'_symm_x]
  exact congrArg (fun φ : H K d →ₐ[K] _ => φ z) this

end Hmaps

/-! ### Block sizes after moving a variable -/

section Card

variable {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [DecidableEq J]

/-- The block sizes of `moveLab lab v₀ j'` (`j' ≠ lab v₀`). -/
theorem card_moveLab_general (lab : V → J) (v₀ : V) (j' : J) (h : j' ≠ lab v₀) (j : J) :
    Fintype.card {v // moveLab lab v₀ j' v = j} =
      Fintype.card {v // lab v = j} + (if j = j' then 1 else 0) - (if j = lab v₀ then 1 else 0) := by
  rw [card_fibre_eq_card_labSet, card_fibre_eq_card_labSet, labSet_move_eq]
  split_ifs with h1 h2 h2
  · exact absurd (h1.symm.trans h2) h
  · subst h1
    rw [Finset.card_insert_of_not_mem (by simp), labSet_split_some, Finset.erase_eq_of_not_mem
      (by simp [Ne.symm h])]
    rfl
  · subst h2
    rw [labSet_split_some, Finset.card_erase_of_mem (by simp)]
    rfl
  · rw [labSet_split_some, Finset.erase_eq_of_not_mem (by simp [Ne.symm h2])]
    rfl

end Card

end Categorification.Flag

end
