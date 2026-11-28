/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndIdempotent
import Categorification.KLR.Crystal.IndDecomp

/-!
# A loading idempotent on the Mackey layers of an induced module

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, used for Webster,
arXiv:1309.3796v3, §7.3, proof of Lemma 7.19 (trace half, step L2: the leading layer of the
head-strand filtration).

Let `h : ν'' + ν''' = ν + ν'` and let `i j` be a loading of `ν + ν'` which is a concatenation
of a loading `i` of `ν` and a loading `j` of `ν'`. On the `c`-th Mackey layer of `Ind N`, for
the top cut at `|ν|`, the idempotent `e(i j)` acts as `e(i) ⊗ e(j) ∈ R(ν) ⊗ R(ν')`
(`indMackeyLayerAct_e_append`). Since the images of the maps `Ξ_λ` span the `1_{ν,ν'}`-part of
the layer (`iSup_range_indMackeyLeftMap`) and `Ξ_λ` is `R(ν) ⊗ R(ν')`-linear, `e(i j)` maps
the layer into the span of the images of those `Ξ_λ` on which `e(i) ⊗ 1` does not vanish
(`indTopAct_e_tmul_mem_iSup`); if it vanishes on every `Ξ_λ`, `e(i j)` kills the layer
(`indTopAct_e_tmul_e_eq_zero`).

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `KLR.KLRAlgebra.indTopAct_mul`, `KLR.KLRAlgebra.indMackeyLayerAct_e_append`,
  `KLR.KLRAlgebra.indTopAct_e_tmul_mem_iSup`, `KLR.KLRAlgebra.indTopAct_e_tmul_e_eq_zero`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')
  (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

local notation "Lay" c => IndMackeyLayer Q ν'' ν''' N (Multiset.card ν) c

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **The action of `R(ν) ⊗ R(ν')` on the layers is multiplicative.** -/
theorem indTopAct_mul (c : ℕ) (t t' : TensorKLR Q ν ν') (w : Lay c) :
    indTopAct h N c t (indTopAct h N c t' w) = indTopAct h N c (t * t') w := by
  rw [indTopAct, indTopAct, indMackeyLayerAct_mul]
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [indMackeyLayerAct_mk, indTopAct, indMackeyLayerAct_mk]
  congr 1
  refine Subtype.ext ?_
  change (castAlg Q h.symm (concat Q ν ν' t) * castAlg Q h.symm (concat Q ν ν' t')) •
      (y : Ind Q ν'' ν''' N) = castAlg Q h.symm (concat Q ν ν' (t * t')) • (y : Ind Q ν'' ν''' N)
  rw [concat_mul, map_mul]

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **A concatenated loading acts on the layers through `R(ν) ⊗ R(ν')`**:
`e(i j) = e(i) ⊗ e(j)`. -/
theorem indMackeyLayerAct_e_append (i : Seq ν) (j : Seq ν') (c : ℕ) (w : Lay c) :
    indMackeyLayerAct N (e (seqCast h.symm (i.append j)) : KLRAlgebra k Q (ν'' + ν'''))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c w =
      indTopAct h N c ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) w := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [indMackeyLayerAct_mk, indTopAct, indMackeyLayerAct_mk]
  congr 1
  refine Subtype.ext ?_
  change (e (seqCast h.symm (i.append j)) : KLRAlgebra k Q (ν'' + ν''')) •
      (y : Ind Q ν'' ν''' N) =
    castAlg Q h.symm (concat Q ν ν' ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν'))) •
      (y : Ind Q ν'' ν''' N)
  rw [concat_e_tmul_e, castAlg_e]

variable (hsym : KLRSymm Q)

include hsym in
/-- **A loading `e(i) ⊗ e(j)` maps the layer into the images of the surviving `Ξ_λ`**: if
`e(i) ⊗ 1` kills `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` for every datum `λ` outside a
set `P`, then `e(i) ⊗ e(j)` maps the `c`-th layer into the span of the images of `Ξ_λ`,
`λ ∈ P`. -/
theorem indTopAct_e_tmul_mem_iSup {c : ℕ} (i : Seq ν) (j : Seq ν')
    (P : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c} → Prop)
    (hk : ∀ q, ¬ P q → ∀ w : MackeyLeftInd Q N q.1,
      ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w = 0)
    (y : Lay c) :
    indTopAct h N c ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) y ∈
      ⨆ (q) (_ : P q), LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
  have hsplit : ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν') : TensorKLR Q ν ν') =
      ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) *
        (1 * ((1 : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν'))) := by
    rw [one_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit, ← indTopAct_mul, ← indTopAct_mul]
  have hmem : indTopAct h N c 1 (indTopAct h N c
      ((1 : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) y) ∈
      ⨆ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
        LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2) := by
    rw [iSup_range_indMackeyLeftMap h N hsym shufWord_spec]
    exact ⟨_, rfl⟩
  refine Submodule.iSup_induction _ (motive := fun x => indTopAct h N c
    ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν')) x ∈
      ⨆ (q) (_ : P q), LinearMap.range (indMackeyLeftMap (Q := Q) h N q.1 q.2)) hmem ?_ ?_ ?_
  · rintro q x ⟨w, rfl⟩
    rw [← indMackeyLeftMap_smul]
    by_cases hq : P q
    · exact Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hq ⟨_, rfl⟩)
    · rw [hk q hq w, map_zero]
      exact zero_mem _
  · rw [map_zero]; exact zero_mem _
  · intro x x' hx hx'
    rw [map_add]; exact add_mem hx hx'

include hsym in
/-- **A loading killing every `Ξ_λ` kills the layer.** -/
theorem indTopAct_e_tmul_e_eq_zero {c : ℕ} (i : Seq ν) (j : Seq ν')
    (hk : ∀ q : {q : MackeyQuad ν ν' ν'' ν''' // Multiset.card q.β = c},
      ∀ w : MackeyLeftInd Q N q.1,
        ((e i : KLRAlgebra k Q ν) ⊗ₜ (1 : KLRAlgebra k Q ν') : TensorKLR Q ν ν') • w = 0)
    (y : Lay c) :
    indTopAct h N c ((e i : KLRAlgebra k Q ν) ⊗ₜ (e j : KLRAlgebra k Q ν')) y = 0 := by
  have hm := indTopAct_e_tmul_mem_iSup h N hsym i j (fun _ => False) (fun q _ => hk q) y
  simpa only [iSup_false, iSup_bot, Submodule.mem_bot] using hm

end KLRAlgebra

end Categorification.KLR
