/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Rescale
import Categorification.Diagrams.CL.Specialize

/-!
# Normalizing the scalars of `U_Q(g)` by rescaling

S. Cautis, A. D. Lauda, arXiv:1111.1431v3.

## `r_i = 1` (CL, Remark after `eq_r3_hard-gen`, item 1, and §2.6.1)

"It is always possible to rescale the `ii`-crossing by `r_i` so that `r_i = 1`." With the
rescaling datum `rDatum S` (upward `ii`-crossings multiplied by `r_i`, every other generator
fixed; the downward `ii`-crossings are then multiplied by `r_i` as well, by `Q`-cyclicity),
`U_S(g) ≅ U_{S₁}(g)` where `S₁ = S.withRone` has the same `t`, `s` and `r = 1`
(`equivWithRone`).

For a single vertex (`Subsingleton I`; CL §2.6.1, `sec:sl2convs`: "for all choices of `Q` the
2-categories `U_Q(sl_2)` are isomorphic to the 2-category `U(sl_2)` given by taking `r_i = 1`",
and the same for a single vertex with `(α_i, α_i) > 2`), `U_{S₁}(g)` has the relations of
`U_{kl}(g)`, which is KL III's `U` (`presCL_kl`), so every `U_Q(g)` is isomorphic to KL III's `U`
(`equivSingleVertex`, `equivSingleVertexPres`).

## Balanced scalars (CL Remark after `eq_r3_hard-gen`, item 3)

If `s^{pq}_{ij} = 0` for `i ≠ j` and there are units `a_i` with
`t_{ij} a_i^{d_{ij}} = t_{ji} a_j^{d_{ji}}` for all `i ≠ j` ("balanced" scalars), then
`U_S(g) ≅ U_{kl}(g)` (`equivOfBalanced`): take dots `a_i`, crossings `c_{ii} = a_i^{-1} r_i`
and, for `i < j` (a linear order on `I`), `c_{ij} = t_{ij} a_i^{d_{ij}}`, `c_{ji} = 1`. CL assert
(citing KL II) that for a simply-laced tree one can always rescale to `t_{ij} = t_{ji} = 1`; in
the simply-laced case the balancing condition reads `a_i / a_j = t_{ji} / t_{ij}` on edges, which
is solvable on a tree by propagating from a root. For the `A_m` path this is made explicit in
`Categorification.Diagrams.CL.Sigma`. The general tree case (existence of the `a_i`) is not
formalized here.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Rescale

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

namespace CLScalars

variable {k}

/-- The scalars `S` with `r` replaced by `1`. -/
def withRone (S : CLScalars C k) : CLScalars C k := { S with r := fun _ => 1 }

@[simp] theorem withRone_t (S : CLScalars C k) : S.withRone.t = S.t := rfl
@[simp] theorem withRone_s (S : CLScalars C k) : S.withRone.s = S.s := rfl
@[simp] theorem withRone_r (S : CLScalars C k) (i : I) : S.withRone.r i = 1 := rfl

end CLScalars

namespace RescaleDatum

variable {RD k} [DecidableEq I]

/-- **Rescaling the `ii`-crossings by `r_i`** (CL, Remark after `eq_r3_hard-gen`, item 1). -/
def rDatum (S : CLScalars C k) : RescaleDatum RD k where
  dot _ := 1
  cross i j := if i = j then S.r i else 1
  cup _ := 1
  cup_up _ _ := by rw [one_zpow, one_mul]

/-- Rescaling by `rDatum S` gives the relations of `S.withRone` (only the diagonal values
`s^{pq}_{ii}`, which are never used, differ). -/
theorem rDatum_mapScalars (S : CLScalars C k) :
    presCL RD k ((rDatum (RD := RD) S).mapScalars S) = presCL RD k S.withRone := by
  refine presCL_congr (fun i j h => ?_) (fun i j p q h => ?_) (funext fun i => ?_)
  · rw [mapScalars_t_of_ne _ _ h]
    simp [rDatum, h, Ne.symm h]
  · simp [rDatum, mapScalars_s, h, Ne.symm h]
  · simp [rDatum, mapScalars_r]

end RescaleDatum

open RescaleDatum

variable [DecidableEq I]

/-- **`U_S(g) ≅ U_{S₁}(g)` with `r = 1`** (CL, Remark after `eq_r3_hard-gen`, item 1): the
isomorphism rescales the `ii`-crossings (upward and downward) by `r_i`. -/
def equivWithRone (S : CLScalars C k) :
    (presCL RD k S).Presented ≌ (presCL RD k S.withRone).Presented :=
  (rDatum S).equiv S (rDatum_mapScalars S)

theorem equivWithRone_functor_diag (S : CLScalars C k) {a b : Obj (psig RD)} (d : a ⟶ b) :
    (equivWithRone RD k S).functor.map ((presCL RD k S).diag d) =
      ((weight (rDatum (RD := RD) S).chi (Diagram.layers d) : kˣ) : k) •
        (presCL RD k S.withRone).diag d :=
  equiv_functor_diag _ _ _ d

omit [DecidableEq I] in
/-- For a single vertex, `U_{S₁}(g)` has the relations of the KL scalars. -/
theorem presCL_withRone_of_subsingleton [Subsingleton I] (S : CLScalars C k) :
    presCL RD k S.withRone = presCL RD k CLScalars.kl :=
  presCL_congr (fun i j h => absurd (Subsingleton.elim i j) h)
    (fun i j _ _ h => absurd (Subsingleton.elim i j) h) rfl

/-- **All `U_Q(g)` with a single vertex are isomorphic to the one with the KL scalars**
(CL §2.6.1, `sec:sl2convs`), by rescaling the `ii`-crossing by `r_i`. -/
def equivSingleVertex [Subsingleton I] (S : CLScalars C k) :
    (presCL RD k S).Presented ≌ (presCL RD k CLScalars.kl).Presented :=
  (rDatum S).equiv S (by rw [rDatum_mapScalars, presCL_withRone_of_subsingleton])

/-- **All `U_Q(g)` with a single vertex are isomorphic to KL III's `U`** (`pres RD k`, via
`presCL_kl`). -/
def equivSingleVertexPres [Subsingleton I] (S : CLScalars C k) :
    (presCL RD k S).Presented ≌ (pres RD k).Presented :=
  (equivSingleVertex RD k S).trans (by rw [presCL_kl RD k])

/-! ## Balanced scalars -/

namespace RescaleDatum

variable {RD k}

/-- The rescaling datum for balanced scalars: dots `a_i`, `c_{ii} = a_i^{-1} r_i`, and for
`i < j`, `c_{ij} = t_{ij} a_i^{d_{ij}}`, `c_{ji} = 1`; cups and caps fixed up to the forced
factors `a_i^{-1-⟨i,x⟩}` on the cups `1 → E_i F_i`. -/
def balDatum [LinearOrder I] (S : CLScalars C k) (a : I → kˣ) : RescaleDatum RD k where
  dot := a
  cross i j := if i = j then (a i)⁻¹ * S.r i else if i < j then S.t i j * a i ^ C.dij i j else 1
  cup c := if c.l.1 then a c.l.2 ^ (-1 - ip RD c.l.2 c.r) else 1
  cup_up i x := by simp

theorem balDatum_mapScalars [LinearOrder I] (S : CLScalars C k) (a : I → kˣ)
    (hs : ∀ i j p q, i ≠ j → S.s i j p q = 0)
    (ha : ∀ i j, i ≠ j → S.t i j * a i ^ C.dij i j = S.t j i * a j ^ C.dij j i) :
    presCL RD k ((balDatum (RD := RD) S a).mapScalars S) = presCL RD k CLScalars.kl := by
  refine presCL_congr (fun i j h => ?_) (fun i j p q h => ?_) (funext fun i => ?_)
  · rw [mapScalars_t_of_ne _ _ h, CLScalars.kl_t]
    simp only [balDatum, if_neg h, if_neg (Ne.symm h)]
    rcases lt_or_gt_of_ne h with hij | hij
    · rw [if_pos hij, if_neg (not_lt.2 hij.le), mul_one, mul_inv_cancel]
    · rw [if_neg (not_lt.2 hij.le), if_pos hij, one_mul, ha i j h, mul_inv_cancel]
  · rw [mapScalars_s, hs i j p q h, CLScalars.kl_s, zero_mul, zero_mul, zero_mul]
  · simp [balDatum, mapScalars_r]

end RescaleDatum

/-- **Balanced scalars can be rescaled to the KL scalars** (CL, Remark after `eq_r3_hard-gen`,
item 3, for the part asserting the rescaling): if `s^{pq}_{ij} = 0` for `i ≠ j` and there are
units `a_i` with `t_{ij} a_i^{d_{ij}} = t_{ji} a_j^{d_{ji}}` for `i ≠ j`, then
`U_S(g) ≅ U_{kl}(g)`, which is KL III's `U` (`presCL_kl`). -/
def equivOfBalanced [LinearOrder I] (S : CLScalars C k) (a : I → kˣ)
    (hs : ∀ i j p q, i ≠ j → S.s i j p q = 0)
    (ha : ∀ i j, i ≠ j → S.t i j * a i ^ C.dij i j = S.t j i * a j ^ C.dij j i) :
    (presCL RD k S).Presented ≌ (presCL RD k CLScalars.kl).Presented :=
  (balDatum S a).equiv S (balDatum_mapScalars S a hs ha)

end Categorification.KL3.Diagram.CL
