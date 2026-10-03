/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointInduction

/-!
# Low-degree endomorphisms of `E 1_n`: the dimension count (CL §3.6)

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3.6 (`Endomorphisms of E1_n`), Lemma 3.14 (`lem:main`), eqs. (3.15)
(`eq:2`) and (3.17) (`eq:new`).

Lemma 3.14 says that for `m < 2|n + 2|` every `f ∈ Hom^m(E 1_n, E 1_n)` is a combination of dots
times degree-`(m - 2i)` endomorphisms of `1_{n+2}` (for `n ≥ -1`). CL's proof has two parts: a
dimension count (eq. `eq:2`),
`Hom^m(E 1_n, E 1_n) ≅ ⊕_{k ≥ 0} Hom(1_{n+2}, 1_{n+2} ⟨m - 2k⟩)`,
and the identification of the isomorphism with "bubble, then `k` dots", which uses Corollary 3.13
(`cor:1`, hence Lemma 3.6). Here we prove the dimension count:

* `lemMain_finrank`: for `n = wt r ≥ -1` and `m < 2(n + 2)`, assuming the adjoint induction
  hypothesis (3.2) for all weights `> n`,
  `dim Hom(E 1_n, E 1_n ⟨m⟩) = ∑_{k=0}^{n+1} dim Hom(1_{n+2}, 1_{n+2} ⟨m - 2k⟩)`
  (the terms with `m - 2k < 0` vanish by condition (2), so this is CL's `⊕_{k ≥ 0}`);
* `lemMain_finrank_two`: the special case `m = 2`, `n = -1` (eq. `eq:new`):
  `dim Hom^2(E 1_{-1}, E 1_{-1}) = dim Hom^2(1_1, 1_1) + dim End(E 1_1)`.

CL's proof passes through `(E 1_n)_L` (Proposition 3.9); the count here instead moves `E` across
its defining right adjoint, as in the proof of Lemma 3.1, and uses the induction hypothesis only
at the weights `> n`. The mirror statement for `n ≤ -1` (eq. `eq:main2`) needs the `n ≤ 0` half
of §3.2 (Remark 3.11) and is not formalized.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)] (S : StrongSl2 k B)

/-- **Lemma 3.14, dimension count** (CL eq. `eq:2`): for `n = wt r ≥ -1` and `m < 2(n + 2)`,
assuming the adjoint induction hypothesis (3.2) for all weights `> n`,
`dim Hom(E 1_n, E 1_n ⟨m⟩) = ∑_{k=0}^{n+1} dim Hom(1_{n+2}, 1_{n+2} ⟨m - 2k⟩)`. -/
theorem lemMain_finrank {r : ℤ} (hr : -1 ≤ S.wt r) (hyp : ∀ r', r < r' → S.AdjHyp r') {m : ℤ}
    (hm : m < 2 * (S.wt r + 2)) :
    finrank k (S.E r ⟶ (S.E r)⟦m⟧) =
      ∑ j ∈ Finset.range (S.wt (r + 1)).toNat,
        finrank k (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦m - 2 * (j : ℤ)⟧) := by
  have hw : S.wt (r + 1) = S.wt r + 2 := S.wt_add_one r
  have hM := S.toNat_wt_succ (r := r) (by omega)
  rw [S.lem1_step (by omega) (hyp _ (by omega)) m,
    S.lem1_neg (r₀ := r + 1) (by omega) (fun r' h => hyp r' (by omega)) (r + 1) le_rfl _
      (by omega), zero_add, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => finrank_hom_shift_congr k _ _ ?_
  rw [Finset.mem_range] at hj
  omega

/-- **Lemma 3.14, the case `m = 2`, `n = -1`** (CL eq. `eq:new`): assuming (3.2) for all weights
`> -1`, `dim Hom^2(E 1_{-1}, E 1_{-1}) = dim Hom^2(1_1, 1_1) + dim End(E 1_1)`. -/
theorem lemMain_finrank_two {r : ℤ} (hr : S.wt r = -1) (hyp : ∀ r', r < r' → S.AdjHyp r') :
    finrank k (S.E r ⟶ (S.E r)⟦(2 : ℤ)⟧) =
      finrank k (𝟙 (S.obj (r + 1)) ⟶ (𝟙 (S.obj (r + 1)))⟦(2 : ℤ)⟧) +
        finrank k (S.E (r + 1) ⟶ S.E (r + 1)) := by
  have hw : S.wt (r + 1) = 1 := by rw [S.wt_add_one, hr]; norm_num
  rw [S.lem1_step (by omega) (hyp _ (by omega)) 2, hw, add_comm]
  simp only [show (1 : ℤ).toNat = 1 from rfl, Finset.sum_range_one]
  rw [finrank_hom_shift_congr k _ _ (show 2 - 2 * S.wt r - 2 + 2 * ((0 : ℕ) : ℤ) = (2 : ℤ) by
      rw [hr]; norm_num),
    finrank_hom_shift_zero k _ _ (show 2 - 2 * S.wt r - 4 = (0 : ℤ) by rw [hr]; norm_num)]

end Categorification.TwoRep.StrongSl2
