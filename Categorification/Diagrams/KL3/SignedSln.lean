/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation
import Categorification.Flag.SlRootDatum

/-!
# The 2-category `U→(sl_n)` of KL III Definition 4.1

Khovanov–Lauda III, arXiv:0807.3250v1, §4.2 (TeX label `def_Ucatq-sln`, Definition 4.1,
eqs. (4.10)–(4.14)).

`U→(sl_n)` has the objects, 1-morphisms and generating 2-morphisms of `U` (Definition 3.1) for the
root datum of `sl_n` (`Flag.slRootDatum`; KL III §4.1), and the same relations except that the
`R(ν)`-relations are replaced by the *signed* `R(ν)`-relations of the oriented graph
`1 → 2 → ⋯ → n-1` (eq. (4.10)):

* (4.11) for `i ≠ j`: the double crossing on `i j` is the identity if `i · j = 0` and
  `(i - j)(x_i - x_j)` (dot on the `i`-strand minus dot on the `j`-strand) if `i · j = -1`;
* (4.12) the dot slides for `i ≠ j` (unchanged);
* (4.13) the braid relation unless `(i, j, k) = (i, i ± 1, i)` (unchanged);
* (4.14) for `j = i ± 1`: the identity of `i j i` is `(i - j)` times the difference of the two
  triple crossings.

The sl₂ relations, the cyclicity relations and (3.13) (`downup*`) are unchanged. The objects are
all weights `λ ∈ ℤ^{n-1}` (Definition 4.1 does not restrict the weights; the restriction to
weights of compositions of `N` happens in the 2-representation `Γ_N : U→* → Flag*_N`, which sends
the other weights to zero).

## Interpretation

The `R(ν)`-relations of `U` are the relations of the diagrammatic KLR presentation
`KLR.Diagram.relation k Q` for the KL II polynomials `Q = KLR.klQ2 k C`, placed on upward strands
(`Categorification.Diagrams.KL3.Relations`). Of these relations only `sqNe` (the double crossing
`ψ² = Q_{cd}(x_c, x_d)`, `c ≠ d`) and `braidQ` (`ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = Q̄_{cd}` on `c d c`) involve
`Q`. Hence `U→(sl_n)` is `U` with `Q` replaced by

  `Q^τ_{ij}(u, v) = 1` if `i · j = 0`,  `Q^τ_{ij}(u, v) = (i - j)(u - v)` if `i · j = -1`

(`qSigned`), which gives exactly (4.11) (`qSigned_of_adj`) and, since `Q̄^τ_{ij} = i - j`
(`qbar_qSigned_of_adj`) and `(i - j)² = 1`, exactly (4.14). The relations (4.12), (4.13) do not
involve `Q` (for `i · j = 0`, `Q̄ = Q̄(1) = 0`: `qbar_qSigned_of_dot_eq_zero`). This agrees with
the choice `τ_{ij} = τ_{ji} = -1` stated before Definition 4.1 in the convention of KL II
(`Q_{ij} = τ_{ij} u - τ_{ji} v` for an edge oriented `i → j`), with the edges oriented `i → i + 1`.

We define `presQ RD k Q` (Definition 3.1 with the polynomials `Q`) for any root datum, check
`presQ RD k (klQ2 k C) = pres RD k` (`presQ_klQ2`), and set `presSigned m k := presQ
(slRootDatum m) k (qSigned k m)` (`n = m + 1`).

The isomorphism `Σ : U → U→` of §4.2.1 and the 2-category with translation / direct sums are
not formalized here.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- The relations of Definition 3.1, with the `R(ν)`-relations those of the KLR presentation for
the polynomials `Q` instead of the KL II polynomials. -/
def relationQ (Q : I → I → MvPolynomial (Fin 2) k) : (r : Rel RD) → LinDiagram k r.dom r.cod
  | .klr μ r => upLin RD k μ (KLR.Diagram.relation k Q r)
  | r => relation k r

/-- Definition 3.1 with the `R(ν)`-relations for the polynomials `Q`. -/
def presQ (Q : I → I → MvPolynomial (Fin 2) k) : Presentation.{w, max u v} (psig RD) k :=
  ((pres0 RD k).pivotal (inv RD).toColourDuality).addRels (Rel RD) Rel.dom Rel.cod
    (relationQ RD k Q)

theorem relationQ_klQ2 : relationQ RD k (KLR.klQ2 k C) = relation (RD := RD) k := by
  funext r
  cases r <;> rfl

/-- For the KL II polynomials, `presQ` is the presentation `pres` of `U`. -/
theorem presQ_klQ2 : presQ RD k (KLR.klQ2 k C) = pres RD k := by
  rw [presQ, relationQ_klQ2]
  rfl

namespace Signed

open Flag

variable (m : ℕ)

/-- **The signed polynomials `Q^τ` of KL III (4.10)–(4.14)**: `Q^τ_{ij} = 1` if `i · j = 0`, and
`Q^τ_{ij}(u, v) = (i - j)(u - v)` otherwise (the value on the diagonal is not used). Vertices
are `Fin m`; `i - j` is computed in `ℤ`, so it agrees with the paper's `1`-based difference. -/
def qSigned : Fin m → Fin m → MvPolynomial (Fin 2) k := fun i j =>
  if (slCartan m).dot i j = 0 then 1 else (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) • (MvPolynomial.X 0 - MvPolynomial.X 1)

/-- **KL III Definition 4.1**: the presentation of `U→(sl_{m+1})`. -/
def presSigned : Presentation.{w, 0} (psig (slRootDatum m)) k :=
  presQ (slRootDatum m) k (qSigned k m)

/-- **The 2-category `U→(sl_{m+1})`** (without grading shifts and direct sums). -/
abbrev USigned := (presSigned k m).Bicat

variable {k m}

theorem qSigned_of_dot_eq_zero {i j : Fin m} (h : (slCartan m).dot i j = 0) :
    qSigned k m i j = 1 := if_pos h

/-- **KL III eq. (4.11)**, `i · j = -1`: `Q^τ_{ij}(u, v) = (i - j)(u - v)`. -/
theorem qSigned_of_adj {i j : Fin m} (h : (slCartan m).dot i j = -1) :
    qSigned k m i j = (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) • (MvPolynomial.X 0 - MvPolynomial.X 1) := by
  rw [qSigned, if_neg (by omega)]

/-- `Q^τ_{ij}(u, v) = Q^τ_{ji}(v, u)`, as required of the polynomials of a KLR algebra. -/
theorem rename_swap_qSigned (i j : Fin m) :
    rename ![(1 : Fin 2), 0] (qSigned k m j i) = qSigned k m i j := by
  unfold qSigned
  rw [(slCartan m).symm j i]
  split_ifs
  · simp
  · rw [map_zsmul, map_sub, rename_X, rename_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← neg_sub (MvPolynomial.X 0 : MvPolynomial (Fin 2) k), smul_neg, ← neg_smul, neg_sub]

/-- `Q̄^τ_{ij} = 0` for `i · j = 0`: the braid relation (4.13) holds on `i j i`. -/
theorem qbar_qSigned_of_dot_eq_zero {i j : Fin m} (h : (slCartan m).dot i j = 0) :
    KLR.qbar (qSigned k m i j) = 0 := by
  rw [qSigned_of_dot_eq_zero h]
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [KLR.qbar_spec]
  simp

/-- **KL III eq. (4.14)**: for `i · j = -1`, `Q̄^τ_{ij} = i - j`, so the relation `braidQ` reads
`ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁ = (i - j)` on `i j i`, i.e. `1 = (i - j)(ψ₀ψ₁ψ₀ - ψ₁ψ₀ψ₁)` since `(i - j)² = 1`. -/
theorem qbar_qSigned_of_adj {i j : Fin m} (h : (slCartan m).dot i j = -1) :
    KLR.qbar (qSigned k m i j) = MvPolynomial.C ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) := by
  rw [qSigned_of_adj h]
  apply X_sub_X_mul_left_cancel (show (0 : Fin 3) ≠ 2 by decide)
  rw [KLR.qbar_spec]
  simp only [map_zsmul, map_sub, rename_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [zsmul_eq_mul, zsmul_eq_mul, ← map_intCast (MvPolynomial.C : k →+* MvPolynomial (Fin 3) k)]
  ring

/-- The difference `i - j` of adjacent vertices is a unit, `(i - j)² = 1`. -/
theorem sq_sub_of_adj {i j : Fin m} (h : (slCartan m).dot i j = -1) :
    ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 = 1) := by
  rw [slCartan_dot] at h
  split_ifs at h with h1 h2
  have : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 1 ∨ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = -1 := by omega
  rcases this with h3 | h3 <;> rw [h3] <;> norm_num

end Signed

end Categorification.KL3.Diagram
