/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Rewriting

/-!
# Reidemeister 3 moves with one downward strand (KL III Proposition 3.5, first part)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.5 (TeX label `prop_other_triangle`), equation (3.22) (TeX label `eq_other_r3_1`).

Throughout, KL III's strand label `k` is written `k'` (`k` is the ground ring). Diagrams are in
the normal form of `Categorification.Diagrams.KL3.Basic` (lists of layers, bottom to top, with
the rightmost region `μ`, KL III's `λ`); `crossl RD i j : E_i F_j ⟶ F_j E_i` and
`crossr RD i j : F_j E_i ⟶ E_i F_j` are KL III's sideways crossings (`eq_crossl-gen`,
`eq_crossr-gen`), with layers `crosslL i j` and `crossrL i j`.

## Reading of (3.22)

Decoding the `xy-pic` source, both sides of (3.22) are 2-morphisms
`E_i F_j E_k 1_λ ⟶ E_k F_j E_i 1_λ` (bottom boundary `i` up, `j` down, `k` up):

* left-hand side `r3mixL i j k'`: `crossl_{ij}` on the two left strands, the upward crossing
  `ψ_{ik}` on the two right strands, `crossr_{kj}` on the two left strands;
* right-hand side `r3mixR i j k'`: `crossr_{kj}` on the two right strands, `ψ_{ik}` on the two
  left strands, `crossl_{ij}` on the two right strands.

The downward `j`-strand is the middle strand of the Reidemeister 3 move, passing on the left of
the crossing `ψ_{ik}` on the left-hand side and on its right on the right-hand side.

## Proof

We follow the proof of KL III. The *outer* mixed R3 moves (the downward strand passes from one
side of the diagram to the other) are rotations of the braid relation on upward strands:

* `dg_r3outR` (`F_j E_i E_k ⟶ E_k E_i F_j`): the rotation of the braid relation
  `ψ₀ψ₁ψ₀ = ψ₁ψ₀ψ₁` on `E_i E_k E_j` (unless `i = j ≠ k`);
* `dg_r3outL` (`E_i E_k F_j ⟶ F_j E_k E_i`): the rotation of the braid relation on
  `E_j E_i E_k` (unless `j = k ≠ i`).

Both are proved by the interchange law, one zigzag relation on each side, and the braid
relation (`dg_braid`); no cyclicity relation is needed, since the sideways crossings are
rotations of upward crossings in a fixed direction. Then (3.22) follows by composing with
the sideways crossings, which are mutually inverse isomorphisms for distinct labels
(`eq_downup_ij-gen`; `crossl_comp_crossr`, `crossr_comp_crossl`, `crossIso`): if `i ≠ j`, post-
and pre-compose with `crossr_{ij}`; if `j ≠ k`, with `crossr_{kj}` and `crossl_{kj}`.

## Main results

* `crossl_comp_crossr`, `crossr_comp_crossl`, `crossIso`: `E_i F_j 1_μ ≅ F_j E_i 1_μ` for
  `i ≠ j` (KL III `eq_downup_ij-gen`).
* `dg_r3outR`, `dg_r3outL`: the outer mixed Reidemeister 3 moves.
* `prop35_a` (and `prop35_a_diag`): **KL III Proposition 3.5, (3.22)**: unless `i = j = k`,
  `r3mixL i j k' = r3mixR i j k'`.

The case `i = j = k` (equation (3.23), with a correction term) is in
`Categorification.Diagrams.KL3.MixedR3Sl2`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## The sideways crossings are inverse isomorphisms for distinct labels -/

/-- **KL III `eq_downup_ij-gen`**, first relation, in `U`: `crossl ≫ crossr = 1` on `E_i F_j 1_μ`
for `i ≠ j`. -/
theorem crossl_comp_crossr (i j : I) (h : i ≠ j) (μ : X) :
    (pres RD k).diag (crossl RD i j μ) ≫ (pres RD k).diag (crossr RD i j μ) = 𝟙 _ := by
  rw [← dg_crossl, ← dg_crossr, dg_comp (by schain) (by schain), dg_downupEF RD k i j h μ,
    dg_nil]

/-- **KL III `eq_downup_ij-gen`**, second relation, in `U`: `crossr ≫ crossl = 1` on
`F_j E_i 1_μ` for `i ≠ j`. -/
theorem crossr_comp_crossl (i j : I) (h : i ≠ j) (μ : X) :
    (pres RD k).diag (crossr RD i j μ) ≫ (pres RD k).diag (crossl RD i j μ) = 𝟙 _ := by
  rw [← dg_crossl, ← dg_crossr, dg_comp (by schain) (by schain), dg_downupFE RD k j i h.symm μ,
    dg_nil]

/-- For `i ≠ j` the sideways crossing `crossl : E_i F_j 1_μ ⟶ F_j E_i 1_μ` is an isomorphism
with inverse `crossr` (KL III `eq_downup_ij-gen`). -/
def crossIso (i j : I) (h : i ≠ j) (μ : X) :
    (pres RD k).obj (ob RD μ [up i, dn j]) ≅ (pres RD k).obj (ob RD μ [dn j, up i]) where
  hom := (pres RD k).diag (crossl RD i j μ)
  inv := (pres RD k).diag (crossr RD i j μ)
  hom_inv_id := crossl_comp_crossr RD k i j h μ
  inv_hom_id := crossr_comp_crossl RD k i j h μ

/-! ## The outer mixed Reidemeister 3 moves -/

/-- **Outer mixed Reidemeister 3 move, downward strand from bottom left to top right**
(`F_j E_i E_k 1_μ ⟶ E_k E_i F_j 1_μ`): `ψ_{ik}`, then the downward strand passes `k` and `i`
(`crossr_{kj}`, `crossr_{ij}`), equals: the downward strand passes `i` and `k`, then `ψ_{ik}`.
This is the rotation of the braid relation on `E_i E_k E_j`, hence holds unless `i = j ≠ k`. -/
theorem dg_r3outR (i k' j : I) (h : ¬ (i = j ∧ i ≠ k')) (μ : X) :
    dg RD k μ [dn j, up i, up k'] [up k', up i, dn j]
      ([([dn j], .cross true i k', [])] ++ (crossrL k' j).map (whL [] [up i]) ++
        (crossrL i j).map (whL [up k'] [])) =
    dg RD k μ [dn j, up i, up k'] [up k', up i, dn j]
      ((crossrL i j).map (whL [] [up k']) ++ (crossrL k' j).map (whL [up i] []) ++
        [([], .cross true i k', [dn j])]) := by
  dnorm
  -- the left-hand side is the rotated `ψ₀ ψ₁ ψ₀`
  dswap 3; dswap 4; dswap 2; dswap 3; dswap 1; dswap 2; dswap 5; dswap 4
  dat 3 [dn j, up k'] [up i, dn j] (dg_zigL' RD k _ (up j))
  dswap 0
  -- the braid relation
  dat 1 [dn j] [dn j] (dg_braid RD k _ i k' j h)
  -- the right-hand side is the rotated `ψ₁ ψ₀ ψ₁`
  symm
  dswap 2; dswap 3; dswap 1; dswap 2; dswap 0; dswap 1; dswap 4; dswap 3
  dat 2 [dn j, up i] [up k', dn j] (dg_zigL' RD k _ (up j))
  dswap 3

/-- **Outer mixed Reidemeister 3 move, downward strand from bottom right to top left**
(`E_i E_k F_j 1_μ ⟶ F_j E_k E_i 1_μ`): the downward strand passes `k` and `i` (`crossl_{kj}`,
`crossl_{ij}`), then `ψ_{ik}`, equals: `ψ_{ik}`, then the downward strand passes `i` and `k`.
This is the rotation of the braid relation on `E_j E_i E_k`, hence holds unless `j = k ≠ i`. -/
theorem dg_r3outL (i k' j : I) (h : ¬ (j = k' ∧ j ≠ i)) (μ : X) :
    dg RD k μ [up i, up k', dn j] [dn j, up k', up i]
      ((crosslL k' j).map (whL [up i] []) ++ (crosslL i j).map (whL [] [up k']) ++
        [([dn j], .cross true i k', [])]) =
    dg RD k μ [up i, up k', dn j] [dn j, up k', up i]
      ([([], .cross true i k', [dn j])] ++ (crosslL i j).map (whL [up k'] []) ++
        (crosslL k' j).map (whL [] [up i])) := by
  dnorm
  -- the left-hand side is the rotated `ψ₀ ψ₁ ψ₀`
  dswap 2; dswap 3; dswap 1; dswap 2; dswap 0; dswap 1; dswap 4; dswap 3
  dat 2 [dn j, up i] [up k', dn j] (dg_zigR' RD k _ (dn j))
  dswap 3
  -- the braid relation
  dat 1 [dn j] [dn j] (dg_braid RD k _ j i k' h)
  -- the right-hand side is the rotated `ψ₁ ψ₀ ψ₁`
  symm
  dswap 3; dswap 4; dswap 2; dswap 3; dswap 1; dswap 2; dswap 0; dswap 5; dswap 4
  dat 3 [dn j, up k'] [up i, dn j] (dg_zigR' RD k _ (dn j))

/-! ## Proposition 3.5, equation (3.22) -/

/-- The layers of the left-hand side of KL III (3.22) (`E_i F_j E_k ⟶ E_k F_j E_i`):
`crossl_{ij}` on the left, `ψ_{ik}` on the right, `crossr_{kj}` on the left. -/
def r3mixL (i j k' : I) : List (LayerData I) :=
  (crosslL i j).map (whL [] [up k']) ++ [([dn j], .cross true i k', [])] ++
    (crossrL k' j).map (whL [] [up i])

/-- The layers of the right-hand side of KL III (3.22): `crossr_{kj}` on the right, `ψ_{ik}` on
the left, `crossl_{ij}` on the right. -/
def r3mixR (i j k' : I) : List (LayerData I) :=
  (crossrL k' j).map (whL [up i] []) ++ [([], .cross true i k', [dn j])] ++
    (crosslL i j).map (whL [up k'] [])

theorem sChain_r3mixL (i j k' : I) :
    SChain [up i, dn j, up k'] (r3mixL i j k') [up k', dn j, up i] := by
  simp only [r3mixL, crosslL, crossrL]; schain

theorem sChain_r3mixR (i j k' : I) :
    SChain [up i, dn j, up k'] (r3mixR i j k') [up k', dn j, up i] := by
  simp only [r3mixR, crosslL, crossrL]; schain

/-- The left-hand side of KL III (3.22), as a diagram `E_i F_j E_k 1_μ ⟶ E_k F_j E_i 1_μ`. -/
def r3mixLD (i j k' : I) (μ : X) : ob RD μ [up i, dn j, up k'] ⟶ ob RD μ [up k', dn j, up i] :=
  mkD RD μ (r3mixL i j k') (sChain_r3mixL i j k')

/-- The right-hand side of KL III (3.22), as a diagram `E_i F_j E_k 1_μ ⟶ E_k F_j E_i 1_μ`. -/
def r3mixRD (i j k' : I) (μ : X) : ob RD μ [up i, dn j, up k'] ⟶ ob RD μ [up k', dn j, up i] :=
  mkD RD μ (r3mixR i j k') (sChain_r3mixR i j k')

/-- (3.22) when `i ≠ j`: compose with the isomorphism `crossr_{ij}` above and below and use the
outer move `dg_r3outR`. -/
theorem prop35_a_of_ne_left (i j k' : I) (hij : i ≠ j) (μ : X) :
    dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  simp only [r3mixL, r3mixR]
  dnorm
  -- insert `1 = crossr_{ij} ≫ crossl_{ij}` on the top right
  dat 7 [up k'] [] (dg_downupFE RD k j i hij.symm _).symm
  -- the outer move
  dat 3 [] [] (dg_r3outR RD k i k' j (fun h => hij h.1) _)
  -- `crossl_{ij} ≫ crossr_{ij} = 1` on the bottom left
  dat 0 [] [up k'] (dg_downupEF RD k i j hij _)

/-- (3.22) when `j ≠ k`: compose with the isomorphisms `crossr_{kj}` below and `crossl_{kj}`
above and use the outer move `dg_r3outL`. -/
theorem prop35_a_of_ne_right (i j k' : I) (hjk : j ≠ k') (μ : X) :
    dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  simp only [r3mixL, r3mixR]
  dnorm
  -- insert `1 = crossr_{kj} ≫ crossl_{kj}` on the bottom right
  dat 0 [up i] [] (dg_downupFE RD k j k' hjk _).symm
  -- the outer move
  dat 3 [] [] (dg_r3outL RD k i k' j (fun h => hjk h.1) _)
  -- `crossl_{kj} ≫ crossr_{kj} = 1` on the top left
  dat 7 [] [up i] (dg_downupEF RD k k' j hjk.symm _)

/-- **KL III Proposition 3.5, equation (3.22)** (label `eq_other_r3_1`), in normal form: unless
`i = j = k`, the mixed Reidemeister 3 move with the downward `j`-strand in the middle holds:
`crossl_{ij} ⊗ 1, 1 ⊗ ψ_{ik}, crossr_{kj} ⊗ 1` equals `1 ⊗ crossr_{kj}, ψ_{ik} ⊗ 1,
1 ⊗ crossl_{ij}` as 2-morphisms `E_i F_j E_k 1_μ ⟶ E_k F_j E_i 1_μ`, for every weight `μ`. -/
theorem prop35_a (i j k' : I) (h : ¬ (i = j ∧ j = k')) (μ : X) :
    dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixL i j k') =
      dg RD k μ [up i, dn j, up k'] [up k', dn j, up i] (r3mixR i j k') := by
  by_cases hij : i = j
  · exact prop35_a_of_ne_right RD k i j k' (fun hjk => h ⟨hij, hjk⟩) μ
  · exact prop35_a_of_ne_left RD k i j k' hij μ

/-- **KL III Proposition 3.5, equation (3.22)** (label `eq_other_r3_1`): unless `i = j = k`,
`r3mixLD i j k' μ = r3mixRD i j k' μ` in `U`. -/
theorem prop35_a_diag (i j k' : I) (h : ¬ (i = j ∧ j = k')) (μ : X) :
    (pres RD k).diag (r3mixLD RD i j k' μ) = (pres RD k).diag (r3mixRD RD i j k' μ) := by
  rw [r3mixLD, r3mixRD, ← dg_of, ← dg_of]
  exact prop35_a RD k i j k' h μ

end Categorification.KL3.Diagram
