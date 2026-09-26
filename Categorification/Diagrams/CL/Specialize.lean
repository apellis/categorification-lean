/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Presentation
import Categorification.Diagrams.KL3.SignedSlnErratum

/-!
# Specializations of `U_Q(g)`: the KL scalars and the signed `sl_n` scalars

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §1.1: "the 2-category `U(g)` from [KL3] corresponds
to the choice of scalars with `t_{ij} = t_{ji} = 1` and `s_{ij}^{pq} = 0`" (and `r_i = 1`, the
convention of KL III, cf. CL's Remark after `eq_r3_hard-gen`).

## The KL scalars

`presCL_kl`: for the KL scalars `CLScalars.kl` (`t = 1`, `s = 0`, `r = 1`), `presCL RD k kl` is
literally the presentation `pres RD k` of KL III Definition 3.1 (relation by relation,
`relationCL_kl`).

## The signed `sl_n` scalars

For the root datum of `sl_n` (`Flag.slRootDatum m`, `n = m + 1`, vertices `Fin m`) take
`t_{ij} = i - j` for adjacent `i, j` (computed in `ℤ`, so `t_{ij} = ±1`), `t_{ij} = 1` otherwise,
`s = 0`, `r = 1` (`Sln.slnScalars`). Then:

* `Sln.qCL_sln_of_ne`: `Q_{ij}` is the signed polynomial `Q^τ_{ij}` of KL III (4.10)–(4.14)
  (`Signed.qSigned`): `1` for `i · j = 0` and `(i - j)(u - v)` for adjacent `i, j`.
* `Sln.relationCL_sln_eq_relationQT'`: on every relation index other than the adjacent-colour
  crossing-cyclicity relations, the relations of `presCL` agree with those of the consistent
  variant `Signed.presSignedQT'` of the revised Definition 4.1 of KL III's erratum
  (`Categorification.Diagrams.KL3.SignedSlnErratum`). In particular the mixed relations give
  `crossl i j ≫ crossr i j = t_{ji} · 1 = (j - i) · 1` on `E_i F_j` and
  `crossr j i ≫ crossl j i = t_{ij} · 1 = (i - j) · 1` on `F_i E_j`
  (`Sln.relationCL_sln_downupEF_adj`, `Sln.relationCL_sln_downupFE_adj`), which are the relations
  of `presSignedQT'` and differ from the literal erratum `presSignedQT` by `2 (j - i) · 1`,
  resp. `2 (i - j) · 1` (`Sln.relationQT_sub_relationCL_sln_downupEF_adj`, …).
* **The adjacent crossing cyclicity.** For `j · i = -1`, `presSignedQT'` (like the erratum)
  imposes the single relation `rotCrossR j i + rotCrossL j i = 0` and nothing on the downward
  crossing. CL's `eq_almost_cyclic` imposes
  `downCross j i = (i - j) · rotCrossR j i = (j - i) · rotCrossL j i`
  (`Sln.relationCL_sln_cycCrossR_adj`, `Sln.relationCL_sln_cycCrossL_adj`; note
  `t_{ij}^{-1} = t_{ij}` as `t_{ij}^2 = 1`). The erratum's relation is the linear combination
  `(i - j) · (CL's cycCrossR) + (j - i) · (CL's cycCrossL)` (`Sln.erratum_cyc_eq`), so CL's
  presentation imposes the erratum's cyclicity relation and additionally identifies the
  downward crossing with `(i - j)` times the right rotation of the upward crossing. (Remark: on
  the path model of KL III §6, as formalized in `Categorification.Flag`, the downward crossing
  generator is sent to the left rotation of the image of the upward crossing
  (`Categorification.Flag.rotCrossLW_eq_crossDn`, see the remarks in
  `Categorification.Diagrams.KL3.SignedSlnErratum`), whereas CL's normalisation is
  `downCross = (j - i) · rotCrossL`; the two agree when `j - i = 1`. Whether CL's own
  2-representation uses a different sign for the downward crossing is not examined here.)
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

/-! ## The KL scalars -/

section KL

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- For the KL scalars every relation of `presCL` is the corresponding relation of KL III
Definition 3.1. -/
theorem relationCL_kl : relationCL RD k CLScalars.kl = relation (RD := RD) k := by
  funext r
  cases r with
  | klr μ r =>
    simp only [relationCL, qCL_kl, CLScalars.kl_r, Units.val_one]
    rw [relationR_one]
    rfl
  | curlR i lam => simp [relationCL, relation]
  | curlL i μ => simp [relationCL, relation]
  | decompEF i lam => simp [relationCL, relation]
  | decompFE i lam => simp [relationCL, relation]
  | cycCrossR j i μ => simp [relationCL, relation]
  | cycCrossL j i μ => simp [relationCL, relation]
  | downupEF i j h μ => simp [relationCL, relation]
  | downupFE i j h μ => simp [relationCL, relation]
  | _ => rfl

/-- **`U_Q(g)` for the KL scalars is the `U` of KL III** (CL §1.1, after Definition 1.1):
`presCL RD k kl = pres RD k`. -/
theorem presCL_kl : presCL RD k CLScalars.kl = pres RD k := by
  rw [presCL, relationCL_kl]
  rfl

end KL

/-! ## The signed `sl_n` scalars -/

namespace Sln

open Flag Signed LinDiagram

variable (k : Type w) [CommRing k] (m : ℕ)

local notation "SRD" => slRootDatum m

/-- `t_{ij} = i - j` (in `ℤ`, cast to `k`) for adjacent `i, j`, a unit with `t_{ij}^2 = 1`; `t_{ij} = 1`
otherwise. -/
def slnT (i j : Fin m) : kˣ :=
  if h : (slCartan m).dot i j = -1 then
    ⟨((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k), ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k),
      by rw [← Int.cast_mul, ← sq, sq_sub_of_adj h, Int.cast_one],
      by rw [← Int.cast_mul, ← sq, sq_sub_of_adj h, Int.cast_one]⟩
  else 1

variable {m}

theorem slnT_of_adj {i j : Fin m} (h : (slCartan m).dot i j = -1) :
    (slnT k m i j : k) = ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) := by
  rw [slnT, dif_pos h]

theorem slnT_of_not_adj {i j : Fin m} (h : ¬ (slCartan m).dot i j = -1) : slnT k m i j = 1 := by
  rw [slnT, dif_neg h]

/-- `t_{ij}` is its own inverse. -/
theorem slnT_inv (i j : Fin m) : (slnT k m i j)⁻¹ = slnT k m i j := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  by_cases h : (slCartan m).dot i j = -1
  · rw [Units.val_mul, slnT_of_adj k h, ← Int.cast_mul, ← sq, sq_sub_of_adj h, Int.cast_one]; rfl
  · rw [slnT_of_not_adj k h, one_mul]

theorem not_adj_self (i : Fin m) : ¬ (slCartan m).dot i i = -1 := by
  rw [dot_self]; decide

theorem not_adj_of_dot_eq_zero {i j : Fin m} (h : (slCartan m).dot i j = 0) :
    ¬ (slCartan m).dot i j = -1 := by
  rw [h]; decide

variable (m)

/-- **The signed `sl_n` scalars**: `t_{ij} = i - j` for adjacent `i, j` and `1` otherwise,
`s = 0`, `r = 1`. -/
def slnScalars : CLScalars (slCartan m) k where
  t := slnT k m
  s _ _ _ _ := 0
  r _ := 1
  t_self i := slnT_of_not_adj k (not_adj_self i)
  t_symm i j h := by
    rw [slnT_of_not_adj k (not_adj_of_dot_eq_zero h),
      slnT_of_not_adj k (not_adj_of_dot_eq_zero (by rwa [(slCartan m).symm]))]
  s_symm _ _ _ _ := rfl

@[simp] theorem slnScalars_t (i j : Fin m) : (slnScalars k m).t i j = slnT k m i j := rfl
@[simp] theorem slnScalars_s (i j : Fin m) (p q : ℕ) : (slnScalars k m).s i j p q = 0 := rfl
@[simp] theorem slnScalars_r (i : Fin m) : (slnScalars k m).r i = 1 := rfl

variable {m}

theorem dij_of_adj {i j : Fin m} (h : (slCartan m).dot i j = -1) : (slCartan m).dij i j = 1 := by
  rw [CartanDatum.dij, h, dot_self]; rfl

/-- **`Q_{ij}` is KL III's signed polynomial `Q^τ_{ij}`** (KL III (4.11), (4.14);
`Signed.qSigned`) for `i ≠ j`. -/
theorem qCL_sln_of_ne {i j : Fin m} (hij : i ≠ j) :
    qCL (slnScalars k m) i j = qSigned k m i j := by
  by_cases h : (slCartan m).dot i j = 0
  · rw [qCL_of_dot_eq_zero _ h, qSigned_of_dot_eq_zero h, slnScalars_t,
      slnT_of_not_adj k (not_adj_of_dot_eq_zero h), Units.val_one, map_one]
  · have hadj := dot_eq_neg_one_of_ne_zero hij h
    have hadj' : (slCartan m).dot j i = -1 := by rwa [(slCartan m).symm]
    rw [qCL_of_dot_ne_zero _ h, qSigned_of_adj hadj, dij_of_adj hadj, dij_of_adj hadj',
      slnScalars_t, slnScalars_t, slnT_of_adj k hadj, slnT_of_adj k hadj']
    simp only [Finset.sum_range_one, slnScalars_s, map_zero, zero_mul, ite_self, add_zero,
      pow_one]
    rw [zsmul_eq_mul, ← map_intCast (MvPolynomial.C : k →+* MvPolynomial (Fin 2) k)]
    push_cast
    simp only [map_sub, map_add, map_neg]
    ring

/-- The adjacent-colour crossing-cyclicity relations `cycCrossR j i`, `cycCrossL j i` with
`j · i = -1`. -/
def IsCycCrossAdj : Rel SRD → Prop
  | .cycCrossR j i _ => (slCartan m).dot j i = -1
  | .cycCrossL j i _ => (slCartan m).dot j i = -1
  | _ => False

/-- **`presCL` for the signed `sl_n` scalars has the relations of `presSignedQT'`** (the
consistent variant of the revised Definition 4.1 of KL III's erratum) on every relation index
except the adjacent-colour crossing-cyclicity relations. -/
theorem relationCL_sln_eq_relationQT' (r : Rel SRD) (h : ¬ IsCycCrossAdj r) :
    relationCL SRD k (slnScalars k m) r = relationQT' k m r := by
  cases r with
  | klr μ r =>
    show upLin _ _ _ _ = upLin _ _ _ _
    rw [relationR_congr k (fun c d hcd => qCL_sln_of_ne k hcd)
      (show (fun c => ((slnScalars k m).r c : k)) = fun _ => 1 by simp), relationR_one]
  | curlR i lam => simp [relationCL, relationQT', relationQT, relationQ, relation]
  | curlL i μ => simp [relationCL, relationQT', relationQT, relationQ, relation]
  | decompEF i lam => simp [relationCL, relationQT', relationQT, relationQ, relation]
  | decompFE i lam => simp [relationCL, relationQT', relationQT, relationQ, relation]
  | cycCrossR j i μ =>
    have h' : ¬ (slCartan m).dot j i = -1 := h
    have h'' : ¬ (slCartan m).dot i j = -1 := by rwa [(slCartan m).symm]
    simp only [relationCL, relationQT', relationQT, if_neg h', relation, slnScalars_t,
      slnT_of_not_adj k h'', inv_one, Units.val_one, one_smul]
  | cycCrossL j i μ =>
    have h' : ¬ (slCartan m).dot j i = -1 := h
    simp only [relationCL, relationQT', relationQT, if_neg h', relation, slnScalars_t,
      slnT_of_not_adj k h', inv_one, Units.val_one, one_smul]
  | downupEF i j hij μ =>
    simp only [relationCL, relationQT', slnScalars_t]
    split_ifs with hadj
    · rw [slnT_of_adj k (by rwa [(slCartan m).symm])]
    · rw [slnT_of_not_adj k (by rwa [(slCartan m).symm]), Units.val_one, one_smul]; rfl
  | downupFE i j hij μ =>
    simp only [relationCL, relationQT', slnScalars_t]
    split_ifs with hadj
    · rw [slnT_of_adj k hadj]
    · rw [slnT_of_not_adj k hadj, Units.val_one, one_smul]; rfl
  | _ => rfl

/-- **CL's mixed relation on `E_i F_j`** for adjacent `i, j`:
`crossl i j ≫ crossr i j = t_{ji} · 1 = (j - i) · 1`. This is the relation of `presSignedQT'`
(`Signed.relationQT'_downupEF_adj`). -/
theorem relationCL_sln_downupEF_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationCL SRD k (slnScalars k m) (.downupEF i j hij μ) =
      of (crossl SRD i j μ ≫ crossr SRD i j μ) -
        (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) := by
  simp only [relationCL, slnScalars_t]
  rw [slnT_of_adj k (by rwa [(slCartan m).symm])]

/-- **CL's mixed relation on `F_i E_j`** for adjacent `i, j`:
`crossr j i ≫ crossl j i = t_{ij} · 1 = (i - j) · 1`. This is the relation of `presSignedQT'`
(`Signed.relationQT'_downupFE_adj`). -/
theorem relationCL_sln_downupFE_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationCL SRD k (slnScalars k m) (.downupFE i j hij μ) =
      of (crossr SRD j i μ ≫ crossl SRD j i μ) -
        (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (𝟙 _)) := by
  simp only [relationCL, slnScalars_t]
  rw [slnT_of_adj k h]

/-- The literal erratum relation `presSignedQT` on `E_i F_j` (`i, j` adjacent) differs from
CL's by `2 (j - i) · 1_{E_i F_j}`: it has the opposite sign. -/
theorem relationQT_sub_relationCL_sln_downupEF_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT k m (.downupEF i j hij μ) - relationCL SRD k (slnScalars k m) (.downupEF i j hij μ) =
      ((2 * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : k) • of (𝟙 _) := by
  rw [relationQT_downupEF_adj hij μ h, relationCL_sln_downupEF_adj k hij μ h,
    sub_sub_sub_cancel_left, ← sub_smul]
  congr 1
  push_cast
  ring

/-- The literal erratum relation `presSignedQT` on `F_i E_j` (`i, j` adjacent) differs from
CL's by `2 (i - j) · 1_{F_i E_j}`. -/
theorem relationQT_sub_relationCL_sln_downupFE_adj {i j : Fin m} (hij : i ≠ j) (μ : Fin m → ℤ)
    (h : (slCartan m).dot i j = -1) :
    relationQT k m (.downupFE i j hij μ) - relationCL SRD k (slnScalars k m) (.downupFE i j hij μ) =
      ((2 * (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) : ℤ) : k) • of (𝟙 _) := by
  rw [relationQT_downupFE_adj hij μ h, relationCL_sln_downupFE_adj k hij μ h,
    sub_sub_sub_cancel_left, ← sub_smul]
  congr 1
  push_cast
  ring

/-- **CL's `Q`-cyclicity, right rotation**, for adjacent `j, i`:
`downCross j i = t_{ij}^{-1} · rotCrossR j i = (i - j) · rotCrossR j i`. -/
theorem relationCL_sln_cycCrossR_adj (i j : Fin m) (μ : Fin m → ℤ)
    (h : (slCartan m).dot j i = -1) :
    relationCL SRD k (slnScalars k m) (.cycCrossR j i μ) =
      (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (rotCrossR SRD j i μ)) -
        of (downCross SRD j i μ) := by
  simp only [relationCL, slnScalars_t, slnT_inv]
  rw [slnT_of_adj k (by rwa [(slCartan m).symm])]

/-- **CL's `Q`-cyclicity, left rotation**, for adjacent `j, i`:
`downCross j i = t_{ji}^{-1} · rotCrossL j i = (j - i) · rotCrossL j i`. -/
theorem relationCL_sln_cycCrossL_adj (i j : Fin m) (μ : Fin m → ℤ)
    (h : (slCartan m).dot j i = -1) :
    relationCL SRD k (slnScalars k m) (.cycCrossL j i μ) =
      (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (rotCrossL SRD j i μ)) -
        of (downCross SRD j i μ) := by
  simp only [relationCL, slnScalars_t, slnT_inv]
  rw [slnT_of_adj k h]

/-- **The erratum's adjacent cyclicity relation `rotCrossR j i + rotCrossL j i = 0`**
(`Signed.relationQT_cycCrossR_adj`) is the linear combination
`(i - j) · (CL's cycCrossR) + (j - i) · (CL's cycCrossL)` of CL's two `Q`-cyclicity relations
(`relationCL_sln_cycCrossR_adj`, `relationCL_sln_cycCrossL_adj`), so it holds in `U_Q(sl_n)`;
CL's relations additionally fix the downward crossing. -/
theorem erratum_cyc_eq (i j : Fin m) (μ : Fin m → ℤ) (h : (slCartan m).dot j i = -1) :
    (of (rotCrossR SRD j i μ) + of (rotCrossL SRD j i μ) :
        LinDiagram k (ob SRD μ [dn j, dn i]) (ob SRD μ [dn i, dn j])) =
      (((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) •
          ((((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) • of (rotCrossR SRD j i μ)) -
            of (downCross SRD j i μ))) +
        (((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) •
          ((((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) • of (rotCrossL SRD j i μ)) -
            of (downCross SRD j i μ))) := by
  have hsq : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) * ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) =
      1 := by
    rw [← Int.cast_mul, ← sq, sq_sub_of_adj (by rwa [(slCartan m).symm]), Int.cast_one]
  have hneg : ((((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) : k) =
      -((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) := by
    push_cast; ring
  rw [hneg, smul_sub, smul_sub, smul_smul, smul_smul, neg_mul_neg, hsq, one_smul, one_smul,
    neg_smul, sub_neg_eq_add]
  abel

end Sln

end Categorification.KL3.Diagram.CL
