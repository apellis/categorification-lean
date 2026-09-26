/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.RescaleBasic
import Categorification.Diagrams.KL3.Grading

/-!
# Rescaling isomorphisms between the 2-categories `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3: the Remark after `eq_r3_hard-gen` (§2.3, `sec:KLR`: "It is always possible to
rescale the `ii`-crossing by `r_i` so that `r_i = 1`"; for a simply-laced tree "it is always
possible to rescale the coefficients so that `t_{ij} = t_{ji} = 1`, see [KL2]") and §2.6.1
(`sec:sl2convs`: for a single vertex, "by rescaling the `ii`-crossing ... the
2-categories `U_Q(sl_2)` are isomorphic to the 2-category `U(sl_2)` given by taking `r_i = 1`").
This file constructs the general rescaling isomorphism behind these remarks.

## The rescaling datum

A `RescaleDatum RD k` consists of units

* `dot i = a_i`: every dot (upward or downward) on a strand labelled `i` is multiplied by `a_i`;
* `cross i j = c_{ij}`: the upward crossing `E_i E_j ⟶ E_j E_i` is multiplied by `c_{ij}`;
* `cup c = β_c`: the cup `1 ⟶ c c*` of the strand colour `c` (a signed letter with the weight of
  the region on its right) is multiplied by `β_c`, and the cap `c* c ⟶ 1` by `β_c⁻¹`,

subject to one condition, `cup_up`: for an upward strand `c = E_i` with right region `x`,
`β_{E_i, x} = a_i^{-1 - ⟨i, x⟩} β_{F_i, x + i_X}`. The downward crossing `F_j F_i 1_ν ⟶ F_i F_j 1_ν`
is then multiplied by the unit forced by `Q`-cyclicity (`dnCross`): `a_j^{d_{ji}} c_{ij}^{-1}` if
`i ≠ j`, `c_{ii}` if `i = j`, times the gauge factor
`β_{F_i, ν - j_X} β_{F_j, ν} / (β_{F_j, ν - i_X} β_{F_i, ν})` of its boundary strands.

These conditions are forced. The zigzag relations force the cap of `c` to be scaled by the
inverse of the cup of `c`. The degree-zero bubble relations (`eq_positivity_bubbles`) with the
extended `sl₂` relations force the clockwise bubble in the region `λ` to be scaled by
`a_i^{1-⟨i,λ⟩}` (`weight_cwReal`), which is `cup_up`. The remaining freedom `β_{F_i, ρ}` is a
gauge (conjugation by a rescaling of the identity 2-morphisms of the strands `F_i`); it cancels
from every relation, but it rescales downward crossings in a weight-dependent way. KL III's
erratum uses a nontrivial gauge (`Categorification.Diagrams.CL.Sigma`).

## The transformation of the scalars (`RescaleDatum.mapScalars`)

If `S = (t, s, r)` is a choice of scalars, rescaling sends every relation of `U_S(g)` to a unit
multiple of the corresponding relation of `U_{S'}(g)` (`scL_relationCL`) where, for `i ≠ j`,

* `t'_{ij} = t_{ij} a_i^{d_{ij}} (c_{ij} c_{ji})^{-1}` (and `t'_{ii} = 1`);
* `s'^{pq}_{ij} = s^{pq}_{ij} a_i^p a_j^q (c_{ij} c_{ji})^{-1}`;
* `r'_i = r_i (a_i c_{ii})^{-1}`.

Equivalently `Q'_{ij}(u, v) = (c_{ij} c_{ji})^{-1} Q_{ij}(a_i u, a_j v)` (`scaleP_qCL`): the double
crossing `ψ²` on `E_i E_j` is scaled by `c_{ij} c_{ji}`, the dots by `a_i`, `a_j`. The nilHecke dot
slides fix `r'_i`, and the braid relation `eq_r3_hard-gen` is consistent with it because
`Q̄[Q(a_i x₀, a_j x₁)] = a_i Q̄[Q](a_i x₀, a_j x₁, a_i x₂)` (`qbar_scaleP`). The other relations
are consistent: the mixed relations `eq_downup` (`crossl ≫ crossr = t_{ji}`) because
`crossl i j ≫ crossr i j` is scaled by `c_{ij} c_{ji} a_j^{⟨j, i⟩} = c_{ij} c_{ji} a_j^{-d_{ji}}`
(`weight_crossl_crossr`); `Q`-cyclicity by the choice of `dnCross` (`weight_rotCrossR`,
`weight_rotCrossL`); the curl relations and the decompositions of `1_{EF}`, `1_{FE}` because every
bubble, real or fake, with label `m` in the region `λ` is scaled by `a_i^{m + 1 ∓ ⟨i, λ⟩}`, i.e. by
`a_i` to the power (degree)/`(i·i)` (`scL_cwL`, `scL_ccwL`), and `crossl i i ≫ crossr i i` by
`c_{ii}² a_i²`.

## Main results

* `RescaleDatum`, `RescaleDatum.chi`, `RescaleDatum.mapScalars`, `RescaleDatum.inv`,
  `RescaleDatum.mapScalars_inv`.
* `RescaleDatum.scL_relationCL`: every relation of `presCL RD k S` is sent to a unit multiple
  of the corresponding relation of `presCL RD k (D.mapScalars S)`; `RescaleDatum.lin_scL_rel`.
* `RescaleDatum.functor D S : (presCL RD k S).Presented ⥤ (presCL RD k (D.mapScalars S)).Presented`,
  the rescaling 2-functor (identity on objects and 1-morphisms).
* `RescaleDatum.equiv D S hS`: for `presCL RD k (D.mapScalars S) = presCL RD k S'`, the
  isomorphism `(presCL RD k S).Presented ≌ (presCL RD k S').Presented` whose inverse is the
  rescaling by `D.inv`; it is an isomorphism of categories (`equiv_functor_comp_inverse`,
  `equiv_inverse_comp_functor`), commutes with whiskering (`equiv_functor_whisk`), is `k`-linear
  and preserves degrees (`equiv_functor_homDeg`).
* `relationCL_congr`, `presCL_congr`: `U_Q(g)` depends only on `t`, on `s^{pq}_{ij}` for `i ≠ j`
  and on `r`.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial Rescale

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- **A rescaling datum** (see the module docstring): units `a_i` for dots, `c_{ij}` for upward
crossings and `β_c` for cups (caps get `β_c⁻¹`), with `β_{E_i, x} = a_i^{-1-⟨i,x⟩} β_{F_i, x+i_X}`. -/
structure RescaleDatum where
  /-- `a_i`: the scalar of a dot on a strand labelled `i`. -/
  dot : I → kˣ
  /-- `c_{ij}`: the scalar of the upward crossing `E_i E_j ⟶ E_j E_i`. -/
  cross : I → I → kˣ
  /-- `β_c`: the scalar of the cup `1 ⟶ c c*` (the cap `c* c ⟶ 1` gets `β_c⁻¹`). -/
  cup : Col I X → kˣ
  cup_up : ∀ (i : I) (x : X), cup ⟨up i, x⟩ = dot i ^ (-1 - ip RD i x) * cup ⟨dn i, sh RD (up i) + x⟩

/-- Close an identity between products of integer powers of units in a commutative group, by
passing to the additive group and using `module`. -/
macro "unit_tac" : tactic => `(tactic| (
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ofMul_div]
  module))

namespace RescaleDatum

variable {RD k}

section Datum

variable (D : RescaleDatum RD k)

/-- The scalar of the downward crossing `F_j F_i 1_ν ⟶ F_i F_j 1_ν`, forced by `Q`-cyclicity:
`a_j^{d_{ji}} c_{ij}^{-1}` for `i ≠ j`, `c_{ii}` for `i = j`, times the gauge factor
`β(F_i, ν - j_X) β(F_j, ν) / (β(F_j, ν - i_X) β(F_i, ν))` of its top and bottom boundary strands
(`β(F_i, ρ)` is the scalar of the cup of the strand `F_i` with right region `ρ`). -/
def dnCross [DecidableEq I] (j i : I) (ν : X) : kˣ :=
  (if j = i then D.cross i i else D.dot j ^ C.dij j i * (D.cross i j)⁻¹) *
    (D.cup ⟨dn i, sh RD (dn j) + ν⟩ * D.cup ⟨dn j, ν⟩ *
      (D.cup ⟨dn j, sh RD (dn i) + ν⟩ * D.cup ⟨dn i, ν⟩)⁻¹)

/-- The scalar of every generator of `U`. -/
def chi [DecidableEq I] : (psig RD).Gen → kˣ
  | .gen (.dot c) => D.dot c.l.2
  | .gen (.cross true i j _) => D.cross i j
  | .gen (.cross false j i ν) => D.dnCross j i ν
  | .cup c => D.cup c
  | .cap c => (D.cup c)⁻¹

/-- The inverse rescaling datum. -/
def inv : RescaleDatum RD k where
  dot i := (D.dot i)⁻¹
  cross i j := (D.cross i j)⁻¹
  cup c := (D.cup c)⁻¹
  cup_up i x := by rw [D.cup_up, mul_inv, inv_zpow']; simp only [inv_zpow', neg_neg, zpow_neg]

@[simp] theorem inv_dot (i : I) : D.inv.dot i = (D.dot i)⁻¹ := rfl
@[simp] theorem inv_cross (i j : I) : D.inv.cross i j = (D.cross i j)⁻¹ := rfl
@[simp] theorem inv_cup (c : Col I X) : D.inv.cup c = (D.cup c)⁻¹ := rfl

theorem inv_dnCross [DecidableEq I] (j i : I) (ν : X) :
    D.inv.dnCross j i ν = (D.dnCross j i ν)⁻¹ := by
  unfold dnCross
  split_ifs
  · simp only [inv_cross, inv_cup]; unit_tac
  · simp only [inv_dot, inv_cross, inv_cup, inv_pow]; unit_tac

theorem chi_inv [DecidableEq I] (g : (psig RD).Gen) : D.inv.chi g * D.chi g = 1 := by
  rcases g with (⟨c⟩ | ⟨ε, i, j, ν⟩) | c | c
  · exact inv_mul_cancel _
  · cases ε
    · show D.inv.dnCross i j ν * D.dnCross i j ν = 1
      rw [inv_dnCross, inv_mul_cancel]
    · exact inv_mul_cancel _
  · exact inv_mul_cancel _
  · show (D.cup c)⁻¹⁻¹ * (D.cup c)⁻¹ = 1
    rw [inv_inv, mul_inv_cancel]

/-- **The transformed scalars** `S' = D.mapScalars S`: for `i ≠ j`,
`t'_{ij} = t_{ij} a_i^{d_{ij}} (c_{ij} c_{ji})^{-1}`,
`s'^{pq}_{ij} = s^{pq}_{ij} a_i^p a_j^q (c_{ij} c_{ji})^{-1}`, and `r'_i = r_i (a_i c_{ii})^{-1}`. -/
def mapScalars [DecidableEq I] (S : CLScalars C k) : CLScalars C k where
  t i j := if i = j then 1 else S.t i j * D.dot i ^ C.dij i j * (D.cross i j * D.cross j i)⁻¹
  s i j p q := S.s i j p q * (D.dot i : k) ^ p * (D.dot j : k) ^ q *
    (((D.cross i j * D.cross j i)⁻¹ : kˣ) : k)
  r i := S.r i * (D.dot i * D.cross i i)⁻¹
  t_self i := if_pos rfl
  t_symm i j h := by
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), (C.dij_eq_zero_iff hij).2 h,
        (C.dij_eq_zero_iff (Ne.symm hij)).2 (by rw [C.symm]; exact h), pow_zero, pow_zero,
        S.t_symm i j h, mul_comm (D.cross i j)]
  s_symm i j p q := by
    rw [S.s_symm i j p q, mul_comm (D.cross i j)]
    ring

variable [DecidableEq I]

theorem mapScalars_t_of_ne (S : CLScalars C k) {i j : I} (h : i ≠ j) :
    (D.mapScalars S).t i j = S.t i j * D.dot i ^ C.dij i j * (D.cross i j * D.cross j i)⁻¹ :=
  if_neg h

@[simp] theorem mapScalars_s (S : CLScalars C k) (i j : I) (p q : ℕ) :
    (D.mapScalars S).s i j p q = S.s i j p q * (D.dot i : k) ^ p * (D.dot j : k) ^ q *
      (((D.cross i j * D.cross j i)⁻¹ : kˣ) : k) := rfl

@[simp] theorem mapScalars_r (S : CLScalars C k) (i : I) :
    (D.mapScalars S).r i = S.r i * (D.dot i * D.cross i i)⁻¹ := rfl

/-- Rescaling by the inverse datum undoes the transformation of scalars. -/
theorem mapScalars_inv (S : CLScalars C k) : D.inv.mapScalars (D.mapScalars S) = S := by
  refine CLScalars.ext (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun p => funext fun q => ?_) (funext fun i => ?_)
  · by_cases h : i = j
    · subst h; rw [(D.inv.mapScalars _).t_self, S.t_self]
    · rw [mapScalars_t_of_ne _ _ h, mapScalars_t_of_ne _ _ h]
      simp only [inv_dot, inv_cross, inv_pow, mul_inv_rev, inv_inv]
      unit_tac
  · simp only [mapScalars_s, inv_dot, inv_cross, Units.val_inv_eq_inv_val, mul_inv_rev, inv_inv]
    simp only [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_pow_eq_pow_val, mul_assoc]
    rw [← mul_one (S.s i j p q)]
    simp only [mul_assoc]
    congr 1
    simp only [← Units.val_mul, ← Units.val_one (α := k)]
    congr 1
    unit_tac
  · simp only [mapScalars_r, inv_dot, inv_cross]
    unit_tac

end Datum

/-! ## Weights of the diagrams of `U` -/

section Weights

theorem shUp_shDn_add (i : I) (x : X) : sh RD (up i) + (sh RD (dn i) + x) = x := by
  simp only [sh, sgn_true, sgn_false, one_smul, neg_smul]; abel

theorem shDn_shUp_add (i : I) (x : X) : sh RD (dn i) + (sh RD (up i) + x) = x := by
  simp only [sh, sgn_true, sgn_false, one_smul, neg_smul]; abel

variable (D : RescaleDatum RD k) [DecidableEq I]

theorem weight_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') :
    weight D.chi (Diagram.layers (mkD RD μ ls h)) =
      (ls.map fun x => D.chi (x.2.1.gen RD (wt RD μ x.2.2))).prod := by
  simp only [weight, layers_mkD, layList, List.map_map]
  rfl

@[simp] theorem chi_dot (l : Letter I) (ν : X) :
    D.chi ((Shape.dot l).gen RD ν) = D.dot l.2 := rfl

@[simp] theorem chi_crossT (i j : I) (ν : X) :
    D.chi ((Shape.cross true i j).gen RD ν) = D.cross i j := rfl

@[simp] theorem chi_crossF (j i : I) (ν : X) :
    D.chi ((Shape.cross false j i).gen RD ν) = D.dnCross j i ν := rfl

@[simp] theorem chi_cupDn (i : I) (ν : X) :
    D.chi ((Shape.cup (dn i)).gen RD ν) = D.cup ⟨dn i, sh RD (up i) + ν⟩ := rfl

@[simp] theorem chi_capDn (i : I) (ν : X) :
    D.chi ((Shape.cap (dn i)).gen RD ν) = (D.cup ⟨dn i, ν⟩)⁻¹ := rfl

@[simp] theorem chi_cupUp (i : I) (ν : X) :
    D.chi ((Shape.cup (up i)).gen RD ν) = D.dot i ^ (1 - ip RD i ν) * D.cup ⟨dn i, ν⟩ := by
  show D.cup ⟨up i, sh RD (dn i) + ν⟩ = _
  rw [D.cup_up, shUp_shDn_add]
  congr 2
  simp only [ip, pair_sh, sgn_false, A_self]
  ring

@[simp] theorem chi_capUp (i : I) (ν : X) :
    D.chi ((Shape.cap (up i)).gen RD ν) =
      (D.dot i ^ (-1 - ip RD i ν) * D.cup ⟨dn i, sh RD (up i) + ν⟩)⁻¹ := by
  show (D.cup ⟨up i, ν⟩)⁻¹ = _
  rw [D.cup_up]

/-- Unfold the weight of a normal-form diagram. -/
macro "weight_tac" : tactic => `(tactic| (
  simp only [weight_mkD, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, chi_dot,
    chi_crossT, chi_crossF, chi_cupDn, chi_capDn, chi_cupUp, chi_capUp, wt_cons, wt_nil,
    List.map_append, List.prod_append, List.map_replicate, List.prod_replicate, mul_one,
    shUp_shDn_add, shDn_shUp_add]))

/-- **The clockwise bubble with `m` dots in the region `λ` is scaled by
`a_i^{m + 1 - ⟨i, λ⟩}`** (`a_i` to the power its degree divided by `i · i`). -/
theorem weight_cwReal (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (cwReal RD lam i m)) = D.dot i ^ ((m : ℤ) + 1 - ip RD i lam) := by
  unfold cwReal
  weight_tac
  unit_tac

/-- **The counterclockwise bubble with `m` dots in the region `λ` is scaled by
`a_i^{m + 1 + ⟨i, λ⟩}`.** -/
theorem weight_ccwReal (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (ccwReal RD lam i m)) =
      D.dot i ^ ((m : ℤ) + 1 + ip RD i lam) := by
  unfold ccwReal
  weight_tac
  unit_tac

end Weights

/-! ## Rescaling bubbles, real and fake -/

section Bubbles

variable (D : RescaleDatum RD k) [DecidableEq I]

theorem weight_dots (μ : X) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) (m : ℕ) :
    weight D.chi (Diagram.layers (dots RD μ u l v m)) = D.dot l.2 ^ m := by
  unfold dots
  weight_tac

theorem scL_cwR (lam : X) (i : I) (m : ℤ) :
    scL D.chi (cwR RD k lam i m) =
      ((D.dot i ^ (m + 1 - ip RD i lam) : kˣ) : k) •
        (cwR RD k lam i m : LinDiagram k (ob RD lam []) (ob RD lam [])) := by
  unfold cwR
  split_ifs with h
  · rw [scL_of, weight_cwReal, Int.toNat_of_nonneg h]
  · rw [scL_zero, smul_zero]

theorem scL_ccwR (lam : X) (i : I) (m : ℤ) :
    scL D.chi (ccwR RD k lam i m) =
      ((D.dot i ^ (m + 1 + ip RD i lam) : kˣ) : k) •
        (ccwR RD k lam i m : LinDiagram k (ob RD lam []) (ob RD lam [])) := by
  unfold ccwR
  split_ifs with h
  · rw [scL_of, weight_ccwReal, Int.toNat_of_nonneg h]
  · rw [scL_zero, smul_zero]

/-- **Every clockwise bubble with label `m` in the region `λ`, real or fake, is scaled by
`a_i^{m + 1 - ⟨i, λ⟩}`.** For fake bubbles this follows from the infinite Grassmannian
recursion (`grassInv_smul`). -/
theorem scL_cwL (lam : X) (i : I) (m : ℤ) :
    scL D.chi (cwL RD k lam i m) =
      ((D.dot i ^ (m + 1 - ip RD i lam) : kˣ) : k) •
        (cwL RD k lam i m : LinDiagram k (ob RD lam []) (ob RD lam [])) := by
  unfold cwL
  split_ifs with h h'
  · rw [scL_of, weight_cwReal, Int.toNat_of_nonneg h]
  · rw [← scEnd_apply, ← AlgHom.coe_toRingHom, grassInv_map_ringHom]
    show grassInv (A := LEnd RD k (ob RD lam [])) (fun a : ℕ => scL D.chi (ccwR RD k lam i (-ip RD i lam - 1 + a))) _ = _
    have e : ∀ a : ℕ, scL D.chi (ccwR RD k lam i (-ip RD i lam - 1 + a)) =
        (D.dot i : k) ^ a • ccwR RD k lam i (-ip RD i lam - 1 + a) := by
      intro a
      rw [scL_ccwR, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
      congr 3
      ring
    simp only [e]
    rw [grassInv_smul, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg h']
  · rw [scL_zero, smul_zero]

/-- **Every counterclockwise bubble with label `m` in the region `λ`, real or fake, is scaled
by `a_i^{m + 1 + ⟨i, λ⟩}`.** -/
theorem scL_ccwL (lam : X) (i : I) (m : ℤ) :
    scL D.chi (ccwL RD k lam i m) =
      ((D.dot i ^ (m + 1 + ip RD i lam) : kˣ) : k) •
        (ccwL RD k lam i m : LinDiagram k (ob RD lam []) (ob RD lam [])) := by
  unfold ccwL
  split_ifs with h h'
  · rw [scL_of, weight_ccwReal, Int.toNat_of_nonneg h]
  · rw [← scEnd_apply, ← AlgHom.coe_toRingHom, grassInv_map_ringHom]
    show grassInv (A := LEnd RD k (ob RD lam [])) (fun a : ℕ => scL D.chi (cwR RD k lam i (ip RD i lam - 1 + a))) _ = _
    have e : ∀ a : ℕ, scL D.chi (cwR RD k lam i (ip RD i lam - 1 + a)) =
        (D.dot i : k) ^ a • cwR RD k lam i (ip RD i lam - 1 + a) := by
      intro a
      rw [scL_cwR, ← Units.val_pow_eq_pow_val, ← zpow_natCast]
      congr 3
      ring
    simp only [e]
    rw [grassInv_smul, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Int.toNat_of_nonneg h']
  · rw [scL_zero, smul_zero]

theorem scL_bubR (lam : X) (t : List (Letter I)) (b : LEnd RD k (ob RD lam [])) :
    scL D.chi (bubR RD k lam t b) = bubR RD k lam t (scL D.chi b) := by
  unfold bubR
  rw [scL_cast, scL_whisker]

theorem scL_bubL (μ : X) (t : List (Letter I)) (b : LEnd RD k (ob RD (wt RD μ t) [])) :
    scL D.chi (bubL RD k μ t b) = bubL RD k μ t (scL D.chi b) := by
  unfold bubL
  rw [scL_cast, scL_whisker]

end Bubbles

/-! ## Weights of crossings, curls and cups/caps with dots -/

theorem shDn_eq (i : I) : sh RD (dn i) = -sh RD (up i) := by
  simp only [sh, sgn_true, sgn_false, one_smul, neg_smul]

theorem region₁ (i j : I) (x : X) :
    sh RD (up i) + (sh RD (dn j) + (sh RD (dn i) + x)) = sh RD (dn j) + x := by
  rw [shDn_eq, shDn_eq]; abel

theorem region₂ (i j : I) (x : X) :
    sh RD (up j) + (sh RD (up i) + (sh RD (dn j) + (sh RD (dn i) + x))) = x := by
  rw [shDn_eq, shDn_eq]; abel

theorem region₃ (i j : I) (x : X) :
    sh RD (up i) + (sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + x))) = x := by
  rw [shDn_eq, shDn_eq]; abel

theorem region₄ (i j : I) (x : X) :
    sh RD (up j) + (sh RD (dn i) + (sh RD (dn j) + x)) = sh RD (dn i) + x := by
  rw [shDn_eq, shDn_eq]; abel

section MoreWeights

variable (D : RescaleDatum RD k) [DecidableEq I]

/-- `crossl i j ≫ crossr i j` (on `E_i F_j`) is scaled by `c_{ji} c_{ij} a_j^{⟨j, i⟩}`. -/
theorem weight_crossl_crossr (i j : I) (μ : X) :
    weight D.chi (Diagram.layers (crossl RD i j μ ≫ crossr RD i j μ)) =
      D.cross j i * D.cross i j * D.dot j ^ A C j i := by
  rw [Diagram.layers_comp, weight_append]
  unfold crossl crossr
  weight_tac
  simp only [ip, pair_sh, sgn_true, sgn_false, A_self]
  unit_tac

/-- `crossr j i ≫ crossl j i` (on `F_i E_j`) is scaled by `c_{ji} c_{ij} a_i^{⟨i, j⟩}`. -/
theorem weight_crossr_crossl (i j : I) (μ : X) :
    weight D.chi (Diagram.layers (crossr RD j i μ ≫ crossl RD j i μ)) =
      D.cross j i * D.cross i j * D.dot i ^ A C i j := by
  rw [Diagram.layers_comp, weight_append]
  unfold crossl crossr
  weight_tac
  simp only [ip, pair_sh, sgn_true, sgn_false, A_self]
  unit_tac

theorem weight_downCross (j i : I) (μ : X) :
    weight D.chi (Diagram.layers (downCross RD j i μ)) = D.dnCross j i μ := by
  unfold downCross
  weight_tac

/-- The gauge factor of `F_j F_i 1_μ ⟶ F_i F_j 1_μ`. -/
abbrev gaugeFF (j i : I) (μ : X) : kˣ :=
  D.cup ⟨dn i, sh RD (dn j) + μ⟩ * D.cup ⟨dn j, μ⟩ *
    (D.cup ⟨dn j, sh RD (dn i) + μ⟩ * D.cup ⟨dn i, μ⟩)⁻¹

/-- The left rotation of the upward crossing `E_j E_i ⟶ E_i E_j` is scaled by `c_{ji}` times
the gauge factor. -/
theorem weight_rotCrossL (j i : I) (μ : X) :
    weight D.chi (Diagram.layers (rotCrossL RD j i μ)) = D.cross j i * D.gaugeFF j i μ := by
  unfold rotCrossL
  weight_tac
  simp only [region₁, region₂, shUp_shDn_add]
  unit_tac

/-- The right rotation of the upward crossing `E_j E_i ⟶ E_i E_j` is scaled by
`c_{ji} a_j^{-⟨j, i⟩} a_i^{⟨i, j⟩}`. -/
theorem weight_rotCrossR (j i : I) (μ : X) :
    weight D.chi (Diagram.layers (rotCrossR RD j i μ)) =
      D.cross j i * D.dot j ^ (-A C j i) * D.dot i ^ A C i j * D.gaugeFF j i μ := by
  unfold rotCrossR
  weight_tac
  simp only [region₃, region₄, shUp_shDn_add]
  simp only [ip, pair_sh, sgn_true, sgn_false, A_self]
  unit_tac

theorem weight_rotDotR (i : I) (μ : X) :
    weight D.chi (Diagram.layers (rotDotR RD i μ)) = D.dot i := by
  unfold rotDotR
  weight_tac
  simp only [ip, pair_sh, sgn_false, A_self]
  unit_tac

theorem weight_rotDotL (i : I) (μ : X) :
    weight D.chi (Diagram.layers (rotDotL RD i μ)) = D.dot i := by
  unfold rotDotL
  weight_tac
  unit_tac

theorem weight_downDot (i : I) (μ : X) :
    weight D.chi (Diagram.layers (downDot RD i μ)) = D.dot i := by
  unfold downDot
  weight_tac

theorem weight_curlR (i : I) (lam : X) :
    weight D.chi (Diagram.layers (curlR RD i lam)) = D.cross i i * D.dot i ^ (1 - ip RD i lam) := by
  unfold curlR
  weight_tac
  unit_tac

theorem weight_curlL (i : I) (μ : X) :
    weight D.chi (Diagram.layers (curlL RD i μ)) =
      D.cross i i * D.dot i ^ (1 + ip RD i (wt RD μ [up i])) := by
  unfold curlL
  weight_tac
  unit_tac

theorem weight_dotCapEF (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (dotCapEF RD lam i m)) = D.dot i ^ m * (D.cup ⟨dn i, lam⟩)⁻¹ := by
  unfold dotCapEF
  weight_tac

theorem weight_cupDotEF (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (cupDotEF RD lam i m)) =
      D.dot i ^ (1 - ip RD i lam) * D.cup ⟨dn i, lam⟩ * D.dot i ^ m := by
  unfold cupDotEF
  weight_tac

theorem weight_dotCapFE (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (dotCapFE RD lam i m)) =
      D.dot i ^ m * (D.dot i ^ (-1 - ip RD i lam) * D.cup ⟨dn i, sh RD (up i) + lam⟩)⁻¹ := by
  unfold dotCapFE
  weight_tac

theorem weight_cupDotFE (lam : X) (i : I) (m : ℕ) :
    weight D.chi (Diagram.layers (cupDotFE RD lam i m)) =
      D.cup ⟨dn i, sh RD (up i) + lam⟩ * D.dot i ^ m := by
  unfold cupDotFE
  weight_tac

end MoreWeights

theorem bubR_smul (lam : X) (t : List (Letter I)) (r : k) (b : LEnd RD k (ob RD lam [])) :
    bubR RD k lam t (r • (b : LinDiagram k (ob RD lam []) (ob RD lam []))) =
      r • bubR RD k lam t b := by
  unfold bubR
  rw [LinDiagram.whisker_smul, LinDiagram.cast_smul]

theorem bubL_smul (μ : X) (t : List (Letter I)) (r : k) (b : LEnd RD k (ob RD (wt RD μ t) [])) :
    bubL RD k μ t (r • (b : LinDiagram k (ob RD (wt RD μ t) []) (ob RD (wt RD μ t) []))) =
      r • bubL RD k μ t b := by
  unfold bubL
  rw [LinDiagram.whisker_smul, LinDiagram.cast_smul]

theorem unit_smul_eq_self {a b : Obj (psig RD)} {u : kˣ} (x : LinDiagram k a b) (h : u = 1) :
    (u : k) • x = x := by
  rw [h, Units.val_one, one_smul]

/-! ## The rescaled relations -/

section Relations

variable (D : RescaleDatum RD k) [DecidableEq I] (S : CLScalars C k)

theorem scL_curlRHS (i : I) (lam : X) :
    scL D.chi (curlRHS RD k i lam) = ((D.dot i ^ (-ip RD i lam) : kˣ) : k) • curlRHS RD k i lam := by
  unfold curlRHS
  rw [scL_neg, scL_sum, smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' := Int.lt_toNat.mp (Finset.mem_range.mp hf)
  rw [scL_comp, scL_bubR, scL_cwL, bubR_smul, scL_of, weight_dots, Linear.smul_comp,
    Linear.comp_smul, smul_smul, ← Units.val_mul]
  congr 2
  have e : ((-ip RD i lam - f).toNat : ℤ) = -ip RD i lam - f := Int.toNat_of_nonneg (by omega)
  rw [← zpow_natCast, e]
  unit_tac

theorem scL_curlLHS (i : I) (μ : X) :
    scL D.chi (curlLHS RD k i μ) =
      ((D.dot i ^ ip RD i (wt RD μ [up i]) : kˣ) : k) • curlLHS RD k i μ := by
  unfold curlLHS
  rw [scL_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Int.lt_toNat.mp (Finset.mem_range.mp hg)
  rw [scL_comp, scL_bubL, scL_ccwL, bubL_smul, scL_of, weight_dots, Linear.smul_comp,
    Linear.comp_smul, smul_smul, ← Units.val_mul]
  congr 2
  have e : ((ip RD i (wt RD μ [up i]) - g).toNat : ℤ) = ip RD i (wt RD μ [up i]) - g :=
    Int.toNat_of_nonneg (by omega)
  rw [← zpow_natCast, e]
  unit_tac

theorem scL_decompEFSum (i : I) (lam : X) :
    scL D.chi (decompEFSum RD k i lam) = decompEFSum RD k i lam := by
  unfold decompEFSum
  rw [scL_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [scL_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hf' := Int.lt_toNat.mp (Finset.mem_range.mp hf)
  have hg' := Finset.mem_range.mp hg
  rw [scL_comp, scL_comp, scL_of, scL_of, scL_ccwL, weight_dotCapEF, weight_cupDotEF]
  rw [Linear.smul_comp (R := k) (f := ccwL RD k lam i (-ip RD i lam - 1 + ↑g))]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, ← Units.val_mul]
  refine unit_smul_eq_self (k := k) (RD := RD) _ ?_
  have e₁ : ((f - g : ℕ) : ℤ) = f - g := by omega
  have e₂ : (((ip RD i lam).toNat - 1 - f : ℕ) : ℤ) = ip RD i lam - 1 - f := by omega
  simp only [← zpow_natCast, e₁, e₂]
  unit_tac

theorem scL_decompFESum (i : I) (lam : X) :
    scL D.chi (decompFESum RD k i lam) = decompFESum RD k i lam := by
  unfold decompFESum
  rw [scL_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [scL_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hf' := Int.lt_toNat.mp (Finset.mem_range.mp hf)
  have hg' := Finset.mem_range.mp hg
  rw [scL_comp, scL_comp, scL_of, scL_of, scL_cwL, weight_dotCapFE, weight_cupDotFE]
  rw [Linear.smul_comp (R := k) (f := cwL RD k lam i (ip RD i lam - 1 + ↑g))]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, ← Units.val_mul]
  refine unit_smul_eq_self (k := k) (RD := RD) _ ?_
  have e₁ : ((f - g : ℕ) : ℤ) = f - g := by omega
  have e₂ : (((-ip RD i lam).toNat - 1 - f : ℕ) : ℤ) = -ip RD i lam - 1 - f := by omega
  simp only [← zpow_natCast, e₁, e₂]
  unit_tac

omit [DecidableEq I] in
theorem rel_two_sub {a b : Obj (psig RD)} (x y : LinDiagram k a b) (w p q : kˣ) (h : p = w * q) :
    (w : k) • x - (p : k) • y = (w : k) • (x - (q : k) • y) := by
  rw [smul_sub, smul_smul, ← Units.val_mul, h]

omit [DecidableEq I] in
theorem rel_sub_two {a b : Obj (psig RD)} (x y : LinDiagram k a b) (w p q : kˣ) (h : p = w * q) :
    (p : k) • x - (w : k) • y = (w : k) • ((q : k) • x - y) := by
  rw [smul_sub, smul_smul, ← Units.val_mul, h]

omit [DecidableEq I] in
theorem A_eq_neg_dij' {i j : I} (h : i ≠ j) : A C i j = -(C.dij i j : ℤ) := by
  have h₁ := C.dij_mul h
  have hpos := C.dot_self_pos i
  rw [A, show 2 * C.dot i j = -(C.dij i j : ℤ) * C.dot i i by linarith,
    Int.mul_ediv_cancel _ hpos.ne']

theorem scL_rel_cycDotR (i : I) (μ : X) :
    scL D.chi (relationCL RD k S (.cycDotR i μ)) =
      ((D.dot i : kˣ) : k) • relationCL RD k (D.mapScalars S) (.cycDotR i μ) := by
  simp only [relationCL, relation]
  rw [scL_sub, scL_of, scL_of, weight_rotDotR, weight_downDot, smul_sub]

theorem scL_rel_cycDotL (i : I) (μ : X) :
    scL D.chi (relationCL RD k S (.cycDotL i μ)) =
      ((D.dot i : kˣ) : k) • relationCL RD k (D.mapScalars S) (.cycDotL i μ) := by
  simp only [relationCL, relation]
  rw [scL_sub, scL_of, scL_of, weight_rotDotL, weight_downDot, smul_sub]

theorem scL_rel_cwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < ip RD i lam - 1) :
    scL D.chi (relationCL RD k S (.cwNeg i lam α h)) =
      ((D.dot i ^ ((α : ℤ) + 1 - ip RD i lam) : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.cwNeg i lam α h) := by
  simp only [relationCL, relation]
  rw [scL_of, weight_cwReal]

theorem scL_rel_ccwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -ip RD i lam - 1) :
    scL D.chi (relationCL RD k S (.ccwNeg i lam α h)) =
      ((D.dot i ^ ((α : ℤ) + 1 + ip RD i lam) : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.ccwNeg i lam α h) := by
  simp only [relationCL, relation]
  rw [scL_of, weight_ccwReal]

theorem scL_rel_cwOne (i : I) (lam : X) (h : 1 ≤ ip RD i lam) :
    scL D.chi (relationCL RD k S (.cwOne i lam h)) =
      relationCL RD k (D.mapScalars S) (.cwOne i lam h) := by
  simp only [relationCL, relation]
  rw [scL_sub, scL_of, weight_cwReal, Int.toNat_of_nonneg (by omega)]
  erw [scL_of_id]
  simp
  rfl

theorem scL_rel_ccwOne (i : I) (lam : X) (h : ip RD i lam ≤ -1) :
    scL D.chi (relationCL RD k S (.ccwOne i lam h)) =
      relationCL RD k (D.mapScalars S) (.ccwOne i lam h) := by
  simp only [relationCL, relation]
  rw [scL_sub, scL_of, weight_ccwReal, Int.toNat_of_nonneg (by omega)]
  erw [scL_of_id]
  simp
  rfl

theorem scL_rel_curlR (i : I) (lam : X) :
    scL D.chi (relationCL RD k S (.curlR i lam)) =
      ((D.cross i i * D.dot i ^ (1 - ip RD i lam) : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.curlR i lam) := by
  simp only [relationCL]
  rw [scL_sub, scL_of, weight_curlR, scL_smul, scL_curlRHS, smul_smul, ← Units.val_mul]
  refine rel_two_sub _ _ _ _ _ ?_
  simp only [mapScalars_r]
  unit_tac

theorem scL_rel_curlL (i : I) (μ : X) :
    scL D.chi (relationCL RD k S (.curlL i μ)) =
      ((D.cross i i * D.dot i ^ (1 + ip RD i (wt RD μ [up i])) : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.curlL i μ) := by
  simp only [relationCL]
  rw [scL_sub, scL_of, weight_curlL, scL_smul, scL_curlLHS, smul_smul, ← Units.val_mul]
  refine rel_two_sub _ _ _ _ _ ?_
  simp only [mapScalars_r]
  unit_tac

theorem scL_rel_decompEF (i : I) (lam : X) :
    scL D.chi (relationCL RD k S (.decompEF i lam)) =
      relationCL RD k (D.mapScalars S) (.decompEF i lam) := by
  simp only [relationCL]
  rw [scL_sub, scL_add, scL_smul, scL_of (crossl RD i i lam ≫ crossr RD i i lam),
    weight_crossl_crossr, scL_decompEFSum, smul_smul]
  erw [scL_of_id]
  congr 3
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul, mapScalars_r, A_self]
  congr 1
  unit_tac

theorem scL_rel_decompFE (i : I) (lam : X) :
    scL D.chi (relationCL RD k S (.decompFE i lam)) =
      relationCL RD k (D.mapScalars S) (.decompFE i lam) := by
  simp only [relationCL]
  rw [scL_sub, scL_add, scL_smul, scL_of (crossr RD i i lam ≫ crossl RD i i lam),
    weight_crossr_crossl, scL_decompFESum, smul_smul]
  erw [scL_of_id]
  congr 3
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul, mapScalars_r, A_self]
  congr 1
  unit_tac

theorem scL_rel_downupEF (i j : I) (h : i ≠ j) (μ : X) :
    scL D.chi (relationCL RD k S (.downupEF i j h μ)) =
      ((D.cross j i * D.cross i j * D.dot j ^ A C j i : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.downupEF i j h μ) := by
  simp only [relationCL]
  rw [scL_sub, scL_smul, scL_of (crossl RD i j μ ≫ crossr RD i j μ), weight_crossl_crossr]
  erw [scL_of_id]
  refine rel_two_sub _ _ _ _ _ ?_
  rw [mapScalars_t_of_ne _ _ (Ne.symm h), A_eq_neg_dij' (Ne.symm h)]
  unit_tac

theorem scL_rel_downupFE (i j : I) (h : i ≠ j) (μ : X) :
    scL D.chi (relationCL RD k S (.downupFE i j h μ)) =
      ((D.cross j i * D.cross i j * D.dot i ^ A C i j : kˣ) : k) •
        relationCL RD k (D.mapScalars S) (.downupFE i j h μ) := by
  simp only [relationCL]
  rw [scL_sub, scL_smul, scL_of (crossr RD j i μ ≫ crossl RD j i μ), weight_crossr_crossl]
  erw [scL_of_id]
  refine rel_two_sub _ _ _ _ _ ?_
  rw [mapScalars_t_of_ne _ _ h, A_eq_neg_dij' h]
  unit_tac

theorem scL_rel_cycCrossR (j i : I) (μ : X) :
    scL D.chi (relationCL RD k S (.cycCrossR j i μ)) =
      ((D.dnCross j i μ : kˣ) : k) • relationCL RD k (D.mapScalars S) (.cycCrossR j i μ) := by
  simp only [relationCL]
  rw [scL_sub, scL_smul, scL_of, scL_of, weight_rotCrossR, weight_downCross, smul_smul,
    ← Units.val_mul]
  refine rel_sub_two _ _ _ _ _ ?_
  by_cases h : i = j
  · subst h
    rw [(D.mapScalars S).t_self, S.t_self, dnCross, if_pos rfl, A_self]
    unit_tac
  · rw [mapScalars_t_of_ne _ _ h, dnCross, if_neg (Ne.symm h), A_eq_neg_dij' h,
      A_eq_neg_dij' (Ne.symm h)]
    unit_tac

theorem scL_rel_cycCrossL (j i : I) (μ : X) :
    scL D.chi (relationCL RD k S (.cycCrossL j i μ)) =
      ((D.dnCross j i μ : kˣ) : k) • relationCL RD k (D.mapScalars S) (.cycCrossL j i μ) := by
  simp only [relationCL]
  rw [scL_sub, scL_smul, scL_of, scL_of, weight_rotCrossL, weight_downCross, smul_smul,
    ← Units.val_mul]
  refine rel_sub_two _ _ _ _ _ ?_
  by_cases h : j = i
  · subst h
    rw [(D.mapScalars S).t_self, S.t_self, dnCross, if_pos rfl]
    unit_tac
  · rw [mapScalars_t_of_ne _ _ h, dnCross, if_neg h]
    unit_tac

end Relations

/-! ## The KLR relations -/

section KLRRel

open KLR.Diagram in
/-- The scalars of the KLR generators: `a_c` for a dot, `c_{cd}` for a crossing. -/
def chiK (D : RescaleDatum RD k) : KLR.Diagram.Gen I → kˣ
  | .dot c => D.dot c
  | .cross c d => D.cross c d

variable (D : RescaleDatum RD k) [DecidableEq I] (S : CLScalars C k)

theorem chi_upLay (μ : X) (L : Layer (KLR.Diagram.sig I)) :
    D.chi (upLay RD μ L).gen = D.chiK L.gen := by
  show D.chi ((upShape L.gen).gen RD _) = _
  cases L.gen <;> rfl

/-- Rescaling commutes with placing KLR diagrams on upward strands. -/
theorem scL_upLin (μ : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b) :
    scL D.chi (upLin RD k μ f) = upLin RD k μ (scL D.chiK f) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [scL_zero, show upLin RD k μ (0 : LinDiagram k a b) = 0 from Finsupp.mapDomain_zero,
      scL_zero]
  | add f g hf hg =>
    rw [show upLin RD k μ (f + g) = upLin RD k μ f + upLin RD k μ g from Finsupp.mapDomain_add,
      scL_add, hf, hg, scL_add,
      show upLin RD k μ (scL D.chiK f + scL D.chiK g) =
        upLin RD k μ (scL D.chiK f) + upLin RD k μ (scL D.chiK g) from Finsupp.mapDomain_add]
  | single d r =>
    rw [show upLin RD k μ (Finsupp.single d r) = Finsupp.single (upDiag RD μ d) r from
      Finsupp.mapDomain_single, scL_single, scL_single]
    have hw : weight D.chi (Diagram.layers (upDiag RD μ d)) =
        weight D.chiK (Diagram.layers d) := by
      simp only [weight, layers_upDiag, List.map_map, Function.comp_def, chi_upLay]
    rw [hw]
    show _ = Finsupp.mapDomain (upDiag RD μ) _
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem ncEval_C_mul {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) (x : k)
    (p : MvPolynomial (Fin n) k) : KLR.ncEval y (MvPolynomial.C x * p) = x • KLR.ncEval y p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [C_mul_monomial, ncEval_monomial, ncEval_monomial, map_mul, Algebra.smul_def, mul_assoc]
  | add p q hp hq => rw [mul_add, ncEval_add, hp, hq, ncEval_add, smul_add]

theorem qbar_C_mul (x : k) (Q : MvPolynomial (Fin 2) k) :
    KLR.qbar (MvPolynomial.C x * Q) = MvPolynomial.C x * KLR.qbar Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [C_mul_monomial, KLR.qbar_monomial, KLR.qbar_monomial, map_mul]
    ring
  | add p q hp hq => rw [mul_add, KLR.qbar_add, hp, hq, KLR.qbar_add, mul_add]

/-- **The KLR polynomials transform as `Q'_{ij}(u, v) = (c_{ij} c_{ji})^{-1} Q_{ij}(a_i u, a_j v)`**
(for `i ≠ j`). -/
theorem scaleP_qCL {c d : I} (h : c ≠ d) :
    scaleP ![(D.dot c : k), (D.dot d : k)] (qCL S c d) =
      MvPolynomial.C ((D.cross c d * D.cross d c : kˣ) : k) * qCL (D.mapScalars S) c d := by
  have hκ : (MvPolynomial.C ((D.cross c d * D.cross d c : kˣ) : k) : MvPolynomial (Fin 2) k) *
      MvPolynomial.C (((D.cross c d * D.cross d c)⁻¹ : kˣ) : k) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hκ' : (MvPolynomial.C ((D.cross c d * D.cross d c : kˣ) : k) : MvPolynomial (Fin 2) k) *
      MvPolynomial.C (((D.cross d c * D.cross c d)⁻¹ : kˣ) : k) = 1 := by
    rw [mul_comm (D.cross d c), hκ]
  simp only [Units.val_mul, map_mul] at hκ hκ'
  by_cases h0 : C.dot c d = 0
  · rw [qCL_of_dot_eq_zero _ h0, qCL_of_dot_eq_zero _ h0, scaleP_C, mapScalars_t_of_ne _ _ h,
      (C.dij_eq_zero_iff h).2 h0, pow_zero, mul_one]
    simp only [Units.val_mul, map_mul]
    linear_combination (-(MvPolynomial.C (S.t c d : k) : MvPolynomial (Fin 2) k)) * hκ
  · rw [qCL_of_dot_ne_zero _ h0, qCL_of_dot_ne_zero _ h0, mapScalars_t_of_ne _ _ h,
      mapScalars_t_of_ne _ _ (Ne.symm h)]
    simp only [map_add, map_mul, map_pow, map_sum, scaleP_C, scaleP_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, mul_add, Finset.mul_sum, Units.val_mul,
      Units.val_pow_eq_pow_val, apply_ite (scaleP _), map_zero, mul_ite, mul_zero,
      mapScalars_s]
    congr 1
    · congr 1
      · linear_combination (-(MvPolynomial.C (S.t c d : k) * MvPolynomial.C (D.dot c : k) ^ C.dij c d * MvPolynomial.X 0 ^ C.dij c d :
          MvPolynomial (Fin 2) k)) * hκ
      · linear_combination (-(MvPolynomial.C (S.t d c : k) * MvPolynomial.C (D.dot d : k) ^ C.dij d c * MvPolynomial.X 1 ^ C.dij d c :
          MvPolynomial (Fin 2) k)) * hκ'
    · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · linear_combination (-(MvPolynomial.C (S.s c d p q) * MvPolynomial.C (D.dot c : k) ^ p * MvPolynomial.C (D.dot d : k) ^ q *
          MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) k)) * hκ
      · rfl

omit [DecidableEq I] in
theorem scL_lpoly {w : Obj (KLR.Diagram.sig I)} {n : ℕ} (y : Fin n → (w ⟶ w)) (u : Fin n → kˣ)
    (hy : ∀ t, weight D.chiK (Diagram.layers (y t)) = u t) (p : MvPolynomial (Fin n) k) :
    scL D.chiK (KLR.Diagram.lpoly k y p) =
      KLR.Diagram.lpoly k y (scaleP (fun t => (u t : k)) p) := by
  show scEnd D.chiK w (KLR.ncEval _ p) = _
  rw [AlgHom.map_ncEval]
  have e : (fun a => scEnd D.chiK w (LinDiagram.of (y a))) =
      fun a => (u a : k) • (LinDiagram.of (y a) : End (Free.of k w)) := by
    funext a
    rw [scEnd_apply, scL_of, hy]
  rw [e, ncEval_smul]

omit [AddCommGroup X] [AddCommGroup Y] [DecidableEq I] in
theorem lpoly_C_mul {w : Obj (KLR.Diagram.sig I)} {n : ℕ} (y : Fin n → (w ⟶ w)) (x : k)
    (p : MvPolynomial (Fin n) k) :
    KLR.Diagram.lpoly k y (MvPolynomial.C x * p) = x • KLR.Diagram.lpoly k y p :=
  ncEval_C_mul (A := End (Free.of k w)) _ _ _

omit [DecidableEq I] in
theorem scL_ofK {a b : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) :
    scL D.chiK (LinDiagram.of d) = ((weight D.chiK (Diagram.layers d) : kˣ) : k) • LinDiagram.of d :=
  scL_of d

open KLR.Diagram in
/-- **Each KLR relation with the scalars `S` is sent to a unit multiple of the KLR relation with
the scalars `D.mapScalars S`.** -/
theorem scL_relationR (x : KLR.Diagram.Rel I) :
    ∃ u : kˣ, scL D.chiK (relationR k (qCL S) (fun c => (S.r c : k)) x) =
      (u : k) • relationR k (qCL (D.mapScalars S)) (fun c => ((D.mapScalars S).r c : k)) x := by
  cases x with
  | sqEq c =>
    refine ⟨D.cross c c * D.cross c c, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_ofK]
    simp [weight, chiK, smul_smul]
  | sqNe c d h =>
    refine ⟨D.cross c d * D.cross d c, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_ofK, scL_lpoly D _ ![D.dot c, D.dot d] (fun t => by fin_cases t <;> simp [weight, chiK]),
      show (fun t => ((![D.dot c, D.dot d] t : kˣ) : k)) = ![(D.dot c : k), (D.dot d : k)] by
        funext t; fin_cases t <;> rfl,
      scaleP_qCL D S h, lpoly_C_mul, smul_sub]
    simp [weight, chiK]
  | slideLEq c =>
    refine ⟨D.cross c c * D.dot c, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_sub, scL_smul, scL_ofK, scL_ofK]
    erw [scL_of_id]
    rw [smul_sub, smul_sub, smul_smul, ← Units.val_mul,
      show D.cross c c * D.dot c * (D.mapScalars S).r c = S.r c by
        rw [mapScalars_r]; unit_tac]
    simp [weight, chiK, mul_comm]
    rfl
  | slideLNe c d h =>
    refine ⟨D.cross c d * D.dot d, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_ofK, scL_ofK, smul_sub]
    simp [weight, chiK, mul_comm]
  | slideREq c =>
    refine ⟨D.dot c * D.cross c c, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_sub, scL_smul, scL_ofK, scL_ofK]
    erw [scL_of_id]
    rw [smul_sub, smul_sub, smul_smul, ← Units.val_mul,
      show D.dot c * D.cross c c * (D.mapScalars S).r c = S.r c by
        rw [mapScalars_r]; unit_tac]
    simp [weight, chiK, mul_comm]
    rfl
  | slideRNe c d h =>
    refine ⟨D.dot c * D.cross c d, ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_ofK, scL_ofK, smul_sub]
    simp [weight, chiK, mul_comm]
  | braid c d e h =>
    refine ⟨D.cross c d * (D.cross c e * D.cross d e), ?_⟩
    simp only [relationR, KLR.Diagram.relation]
    rw [scL_sub, scL_ofK, scL_ofK, smul_sub]
    simp only [weight, chiK, Diagram.layers_comp, layers_dl, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, lay_gen, mul_one]
    congr 3
    ac_rfl
  | braidQ c d h =>
    refine ⟨D.cross c d * (D.cross c c * D.cross d c), ?_⟩
    simp only [relationR]
    have hq : scaleP ![(D.dot c : k), (D.dot d : k), (D.dot c : k)] (KLR.qbar (qCL S c d)) =
        MvPolynomial.C (((D.dot c)⁻¹ * (D.cross c d * D.cross d c) : kˣ) : k) *
          KLR.qbar (qCL (D.mapScalars S) c d) := by
      have := qbar_scaleP (D.dot c : k) (D.dot d : k) (qCL S c d)
      rw [scaleP_qCL D S h, qbar_C_mul] at this
      rw [Units.val_mul, map_mul, mul_assoc, this, ← mul_assoc, ← map_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, map_one, one_mul]
    rw [scL_sub, scL_sub, scL_smul, scL_ofK, scL_ofK,
      scL_lpoly D _ ![D.dot c, D.dot d, D.dot c] (fun t => by fin_cases t <;> simp [weight, chiK]),
      show (fun t => ((![D.dot c, D.dot d, D.dot c] t : kˣ) : k)) =
        ![(D.dot c : k), (D.dot d : k), (D.dot c : k)] by funext t; fin_cases t <;> rfl,
      hq, lpoly_C_mul, smul_sub, smul_sub, smul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul]
    congr 1
    · simp only [weight, chiK, Diagram.layers_comp, layers_dl, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, lay_gen, mul_one]
      rw [show D.cross d c * (D.cross c c * D.cross c d) =
        D.cross c d * (D.cross c c * D.cross d c) by ac_rfl]
    · congr 2
      rw [mapScalars_r]
      unit_tac

end KLRRel

end RescaleDatum

/-! ## Dependence of `U_Q(g)` on the scalars -/

section Congr

variable {RD k}

omit [AddCommGroup X] [AddCommGroup Y] in
theorem qCL_congr {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → S.s i j p q = S'.s i j p q) {i j : I} (h : i ≠ j) :
    qCL S i j = qCL S' i j := by
  unfold qCL
  rw [ht i j h, ht j i (Ne.symm h)]
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hs i j p q h]

/-- `U_Q(g)` only depends on `t_{ij}`, `s^{pq}_{ij}` for `i ≠ j` and on `r` (the values
`s^{pq}_{ii}` are never used). -/
theorem relationCL_congr {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → S.s i j p q = S'.s i j p q) (hr : S.r = S'.r) :
    relationCL RD k S = relationCL RD k S' := by
  have ht' : S.t = S'.t := by
    funext i j
    by_cases h : i = j
    · subst h; rw [S.t_self, S'.t_self]
    · exact ht i j h
  funext r
  cases r with
  | klr μ x =>
    simp only [relationCL]
    rw [relationR_congr k (fun c d h => qCL_congr ht hs h) (by rw [hr])]
  | _ => simp only [relationCL, ht', hr]

theorem presCL_congr {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → S.s i j p q = S'.s i j p q) (hr : S.r = S'.r) :
    presCL RD k S = presCL RD k S' := by
  rw [presCL, presCL, relationCL_congr ht hs hr]

end Congr

namespace RescaleDatum

variable {RD k}

/-! ## The rescaling 2-functor -/

section Functor

variable (D : RescaleDatum RD k) [DecidableEq I] (S : CLScalars C k)

/-- **Every relation of `U_S(g)` is sent by rescaling to a unit multiple of the corresponding
relation of `U_{S'}(g)`, `S' = D.mapScalars S`.** -/
theorem scL_relationCL (r : Rel RD) :
    ∃ u : kˣ, scL D.chi (relationCL RD k S r) = (u : k) • relationCL RD k (D.mapScalars S) r := by
  cases r with
  | cycDotR i μ => exact ⟨_, D.scL_rel_cycDotR S i μ⟩
  | cycDotL i μ => exact ⟨_, D.scL_rel_cycDotL S i μ⟩
  | cwNeg i lam α h => exact ⟨_, D.scL_rel_cwNeg S i lam α h⟩
  | ccwNeg i lam α h => exact ⟨_, D.scL_rel_ccwNeg S i lam α h⟩
  | cwOne i lam h => exact ⟨1, by rw [Units.val_one, one_smul]; exact D.scL_rel_cwOne S i lam h⟩
  | ccwOne i lam h => exact ⟨1, by rw [Units.val_one, one_smul]; exact D.scL_rel_ccwOne S i lam h⟩
  | curlR i lam => exact ⟨_, D.scL_rel_curlR S i lam⟩
  | curlL i μ => exact ⟨_, D.scL_rel_curlL S i μ⟩
  | decompEF i lam => exact ⟨1, by rw [Units.val_one, one_smul]; exact D.scL_rel_decompEF S i lam⟩
  | decompFE i lam => exact ⟨1, by rw [Units.val_one, one_smul]; exact D.scL_rel_decompFE S i lam⟩
  | cycCrossR j i μ => exact ⟨_, D.scL_rel_cycCrossR S j i μ⟩
  | cycCrossL j i μ => exact ⟨_, D.scL_rel_cycCrossL S j i μ⟩
  | downupEF i j h μ => exact ⟨_, D.scL_rel_downupEF S i j h μ⟩
  | downupFE i j h μ => exact ⟨_, D.scL_rel_downupFE S i j h μ⟩
  | klr μ x =>
    obtain ⟨u, hu⟩ := D.scL_relationR S x
    refine ⟨u, ?_⟩
    show scL D.chi (upLin RD k μ _) = _ • upLin RD k μ _
    rw [scL_upLin, hu]
    exact Finsupp.mapDomain_smul _ _

/-- The rescaled relations of `presCL RD k S` hold in `presCL RD k (D.mapScalars S)` (the zigzag
relations are fixed, since a cup and the matching cap are scaled by inverse units). -/
theorem lin_scL_rel (i : (presCL RD k S).Rel) :
    (presCL RD k (D.mapScalars S)).lin (scL D.chi ((presCL RD k S).rel i)) = 0 := by
  rcases i with ((e | c | c) | r)
  · exact e.elim
  · show (presCL RD k (D.mapScalars S)).lin
      (scL D.chi (LinDiagram.of (Pivotal.zigL _ c) - LinDiagram.of (𝟙 _))) = 0
    have hw : weight D.chi (Diagram.layers (Pivotal.zigL (Diagram.inv RD).toColourDuality c)) =
        D.cup c * ((D.cup c)⁻¹ * 1) := rfl
    rw [scL_sub, scL_of, hw, mul_one, mul_inv_cancel, Units.val_one, one_smul]
    erw [scL_of_id]
    exact (presCL RD k (D.mapScalars S)).lin_rel_self (.inl (.inr (.inl c)))
  · show (presCL RD k (D.mapScalars S)).lin
      (scL D.chi (LinDiagram.of (Pivotal.zigR _ c) - LinDiagram.of (𝟙 _))) = 0
    have hw : weight D.chi (Diagram.layers (Pivotal.zigR (Diagram.inv RD).toColourDuality c)) =
        D.cup c * ((D.cup c)⁻¹ * 1) := rfl
    rw [scL_sub, scL_of, hw, mul_one, mul_inv_cancel, Units.val_one, one_smul]
    erw [scL_of_id]
    exact (presCL RD k (D.mapScalars S)).lin_rel_self (.inl (.inr (.inr c)))
  · obtain ⟨u, hu⟩ := D.scL_relationCL S r
    show (presCL RD k (D.mapScalars S)).lin (scL D.chi (relationCL RD k S r)) = 0
    rw [hu, Presentation.lin_smul]
    convert smul_zero ((u : kˣ) : k)
    exact (presCL RD k (D.mapScalars S)).lin_rel_self (.inr r)

/-- **The rescaling 2-functor** `U_S(g) ⟶ U_{S'}(g)`, `S' = D.mapScalars S`: the identity on
objects and 1-morphisms, a diagram `d` goes to `weight D.chi d • d`. It is `k`-linear
(`Rescale.functor` instances), commutes with whiskering (`Rescale.functor_whisk`) and preserves
degrees (`Rescale.functor_homDeg`). -/
def functor : (presCL RD k S).Presented ⥤ (presCL RD k (D.mapScalars S)).Presented :=
  Rescale.functor D.chi (D.lin_scL_rel S)

theorem functor_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (D.functor S).map ((presCL RD k S).diag d) =
      ((weight D.chi (Diagram.layers d) : kˣ) : k) • (presCL RD k (D.mapScalars S)).diag d :=
  Rescale.functor_diag _ d

theorem chi_inv' (g : (psig RD).Gen) : D.chi g * D.inv.chi g = 1 := by
  rw [mul_comm, chi_inv]

/-- The inverse datum rescales the relations of `U_{S'}(g)` into those of `U_S(g)`. -/
theorem lin_scL_rel_inv {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') (i : (presCL RD k S').Rel) :
    (presCL RD k S).lin (scL D.inv.chi ((presCL RD k S').rel i)) = 0 := by
  revert i
  rw [← hS]
  intro i
  have := D.inv.lin_scL_rel (D.mapScalars S) i
  rwa [mapScalars_inv] at this

theorem lin_scL_rel' {S' : CLScalars C k} (hS : presCL RD k (D.mapScalars S) = presCL RD k S')
    (i : (presCL RD k S).Rel) :
    (presCL RD k S').lin (scL D.chi ((presCL RD k S).rel i)) = 0 := by
  rw [← hS]
  exact D.lin_scL_rel S i

/-- **The rescaling isomorphism** `U_S(g) ≅ U_{S'}(g)` whenever `U_{S'}(g)` has the relations of
`U_{D.mapScalars S}(g)` (e.g. `S' = D.mapScalars S`, or `presCL_congr`): an isomorphism
of categories (`Rescale.functor_comp_functor_inv`) whose functor is the rescaling by `D` and whose
inverse is the rescaling by `D.inv`; both commute with whiskering and are `k`-linear and
degree-preserving. -/
def equiv {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') :
    (presCL RD k S).Presented ≌ (presCL RD k S').Presented :=
  Rescale.equiv D.chi (D.lin_scL_rel' S hS) D.inv.chi (D.lin_scL_rel_inv S hS) D.chi_inv

theorem equiv_functor_diag {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') {a b : Obj (psig RD)}
    (d : a ⟶ b) :
    (D.equiv S hS).functor.map ((presCL RD k S).diag d) =
      ((weight D.chi (Diagram.layers d) : kˣ) : k) • (presCL RD k S').diag d :=
  Rescale.functor_diag (D.lin_scL_rel' S hS) d

theorem equiv_inverse_diag {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') {a b : Obj (psig RD)}
    (d : a ⟶ b) :
    (D.equiv S hS).inverse.map ((presCL RD k S').diag d) =
      ((weight D.inv.chi (Diagram.layers d) : kˣ) : k) • (presCL RD k S).diag d :=
  Rescale.functor_diag (D.lin_scL_rel_inv S hS) d

/-- The functor of `equiv` is an isomorphism of categories (not only an equivalence). -/
theorem equiv_functor_comp_inverse {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') :
    (D.equiv S hS).functor ⋙ (D.equiv S hS).inverse = 𝟭 _ :=
  Rescale.functor_comp_functor_inv (D.lin_scL_rel' S hS) (D.lin_scL_rel_inv S hS) D.chi_inv

theorem equiv_inverse_comp_functor {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') :
    (D.equiv S hS).inverse ⋙ (D.equiv S hS).functor = 𝟭 _ :=
  Rescale.functor_comp_functor_inv (D.lin_scL_rel_inv S hS) (D.lin_scL_rel' S hS) D.chi_inv'

/-- The functor of `equiv` commutes with whiskering (a strict 2-functor). -/
theorem equiv_functor_whisk {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') {a b : Obj (psig RD)}
    (f : (presCL RD k S).obj a ⟶ (presCL RD k S).obj b) (u : Obj (psig RD))
    (v : List (psig RD).Colour) :
    (D.equiv S hS).functor.map ((presCL RD k S).whisk f u v) =
      (presCL RD k S').whisk ((D.equiv S hS).functor.map f) u v :=
  Rescale.functor_whisk (D.lin_scL_rel' S hS) f u v

/-- The functor of `equiv` preserves degrees. -/
theorem equiv_functor_homDeg {S' : CLScalars C k}
    (hS : presCL RD k (D.mapScalars S) = presCL RD k S') {a b : Obj (psig RD)}
    {f : (presCL RD k S).obj a ⟶ (presCL RD k S).obj b} {t : ℤ}
    (hf : f ∈ (presCL RD k S).homDeg (deg RD) a b t) :
    (D.equiv S hS).functor.map f ∈ (presCL RD k S').homDeg (deg RD) a b t :=
  Rescale.functor_homDeg (D.lin_scL_rel' S hS) hf

end Functor

end RescaleDatum

end Categorification.KL3.Diagram.CL
