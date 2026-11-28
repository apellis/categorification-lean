/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndAssoc

/-!
# Loading idempotents on the Mackey layers of an induced module

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, Proposition 2.18, tensored with a module, as in
`MackeyIndAssoc`. Let `h : ν'' + ν''' = ν + ν'` and let `P = Σ_{s ∈ T} e(s)` be a sum of loading
idempotents of `R(ν'' + ν''')`. On the image of `ι_{ν,ν'}`, `P` is the image of the element
`P_{ν,ν'} = Σ e(i) ⊗ e(j)` of `R(ν) ⊗ R(ν')`, the sum over the pairs of loadings whose
concatenation lies in `T` (`concatLoadIdem`, `eSum_mul_castAlg_concat`). Hence on the layers of the
Mackey filtration of `Ind N`, `P` acts on the image of `Ξ_λ` through `P_{ν,ν'}` acting on
`MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` (`indMackeyLayerAct_eSum_indMackeyLeftMap`).

This passes the layers of KL I, Proposition 2.18, to the idempotent truncation by the loadings
with the red strands in order, for the trace half of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Lemma 7.19.

Any commutative ring `k`.
-/

noncomputable section

namespace Categorification.KLR

open Equiv TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

variable (Q) in
/-- The element `Σ e(i) ⊗ e(j)` of `R(ν) ⊗ R(ν')`, over the pairs of loadings whose
concatenation, read in `R(ν'' + ν''')`, lies in `T`. -/
def concatLoadIdem (T : Finset (Seq (ν'' + ν'''))) : TensorKLR Q ν ν' :=
  ∑ p : Seq ν × Seq ν',
    if seqCast h.symm (p.1.append p.2) ∈ T then (e p.1 ⊗ₜ e p.2 : TensorKLR Q ν ν') else 0

/-- **A sum of loading idempotents on the image of `ι_{ν,ν'}`** is the image of `concatLoadIdem`. -/
theorem eSum_mul_castAlg_concat (T : Finset (Seq (ν'' + ν'''))) (t : TensorKLR Q ν ν') :
    eSum Q T * castAlg Q h.symm (concat Q ν ν' t) =
      castAlg Q h.symm (concat Q ν ν' (concatLoadIdem Q h T * t)) := by
  have h1 : eSum Q T * castAlg Q h.symm (concat Q ν ν' 1) =
      castAlg Q h.symm (concat Q ν ν' (concatLoadIdem Q h T)) := by
    rw [concat_one, oneConcat_eq, map_sum, Finset.mul_sum, concatLoadIdem, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [castAlg_e, eSum_mul_e]
    split_ifs
    · rw [concat_e_tmul_e, castAlg_e]
    · rw [map_zero, map_zero]
  conv_rhs => rw [concat_mul, map_mul, ← h1, mul_assoc, ← map_mul, ← concat_mul, one_mul]

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]
  [IsScalarTower k (TensorKLR Q ν'' ν''') N]

local notation "Lay" c => IndMackeyLayer Q ν'' ν''' N (Multiset.card ν) c

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem indMackeyLayerAct_mul {n : ℕ} {z z' : KLRAlgebra k Q (ν'' + ν''')}
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      z * y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c)
    (hz' : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      z' * y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c)
    (c : ℕ) (w : IndMackeyLayer Q ν'' ν''' N n c) :
    indMackeyLayerAct N z hz c (indMackeyLayerAct N z' hz' c w) =
      indMackeyLayerAct N (z * z') (fun c y hy => by rw [mul_assoc]; exact hz c _ (hz' c y hy))
        c w := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [indMackeyLayerAct_mk, indMackeyLayerAct_mk, indMackeyLayerAct_mk]
  congr 1
  exact Subtype.ext (smul_smul z z' (y : Ind Q ν'' ν''' N))

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
theorem eSum_preserves (T : Finset (Seq (ν'' + ν'''))) {n : ℕ} :
    ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      (eSum Q T : KLRAlgebra k Q (ν'' + ν''')) * y ∈
        mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c := by
  classical
  intro c y hy
  rw [eSum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun s _ => e_mul_mem_mackeyFilt s hy

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- On the layers, a sum of loading idempotents acts on the image of `ι_{ν,ν'}` through
`concatLoadIdem`. -/
theorem indMackeyLayerAct_eSum_indTopAct (T : Finset (Seq (ν'' + ν'''))) (c : ℕ)
    (t : TensorKLR Q ν ν') (w : Lay c) :
    indMackeyLayerAct N (eSum Q T) (eSum_preserves T) c (indTopAct h N c t w) =
      indTopAct h N c (concatLoadIdem Q h T * t) w := by
  rw [indTopAct, indTopAct, indMackeyLayerAct_mul]
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [indMackeyLayerAct_mk, indMackeyLayerAct_mk]
  congr 1
  exact Subtype.ext (congrArg (· • (y : Ind Q ν'' ν''' N)) (eSum_mul_castAlg_concat h T t))

omit [IsScalarTower k (TensorKLR Q ν'' ν''') N] in
/-- **Loading idempotents on the image of `Ξ_λ`**: `P Ξ_λ(w) = Ξ_λ(P_{ν,ν'} w)`, with
`P_{ν,ν'} = concatLoadIdem T` acting on `MackeyTop_λ`. -/
theorem indMackeyLayerAct_eSum_indMackeyLeftMap (T : Finset (Seq (ν'' + ν''')))
    (q : MackeyQuad ν ν' ν'' ν''') {c : ℕ} (hc : Multiset.card q.β = c)
    (w : MackeyLeftInd Q N q) :
    indMackeyLayerAct N (eSum Q T) (eSum_preserves T) c (indMackeyLeftMap h N q hc w) =
      indMackeyLeftMap h N q hc (concatLoadIdem Q h T • w) := by
  rw [indMackeyLeftMap_smul, ← mul_one (concatLoadIdem Q h T), ← indMackeyLayerAct_eSum_indTopAct,
    ← indMackeyLeftMap_smul, one_smul]

end KLRAlgebra

end Categorification.KLR
