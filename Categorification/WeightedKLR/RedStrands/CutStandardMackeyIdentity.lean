/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLoading
import Categorification.KLR.MackeyIdentityShuffle

/-!
# The leading Mackey datum of a partial standardization: the identity shuffle

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L3: the leading piece
of the head-strand filtration of `e_s 𝕊(N)`.

Let `q` be a Mackey datum of the top cut `ν | ν'` of the induced model of a cut
(`CutInput`), with `|q.α| = p`, and let `s` be a loading of `ν` whose strands left of `p` with
labels in `λ = q.β` are black. Under a shuffle `u ≠ 1` of `α | β` the first `β`-strand ends
left of `p` (`shuffle_first_tail_lt_of_ne_one`), so its loading is violated and is killed by
the input (`cutInput_tail_smul_eq_zero`). Hence only the identity shuffle survives:
`(1_s ⊗ 1) w` lies in the span of the elements `(1 ⊗ b) · (1_λ ⊗ y)`
(`cutInput_e_tmul_one_smul_mackeyLeftInd_mem_span`), on which the parabolic part acts through
the bottom factor (`castAlg_concat_tmul_one_smul_tmul_mackeyTopOne`). For a loading `σ` with
the top cut after `p + M` and a datum with `M` strands, this is
`prefixSeq_tmul_one_smul_mem_mackeyTopOneSpan`.

Webster's proof does not spell this out.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `Stendhal.cutInput_e_tmul_one_smul_mackeyLeftInd_mem_span`,
  `Stendhal.prefixSeq_tmul_one_smul_mem_mackeyTopOneSpan`,
  `Stendhal.indMackeyLayerAct_e_mem_of_black_mackeyTopOne`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]

variable {ν ν' : Multiset (I ⊕ Fin (a + r))}

/-- **L3 for the cut, on one Mackey datum**: if `|q.α| = p` and the strands of `s` left of `p`
with labels in `λ` are black, then `(1_s ⊗ 1) w` lies in the identity-shuffle part
`mackeyTopOneSpan`. -/
theorem cutInput_e_tmul_one_smul_mackeyLeftInd_mem_span (hsym : KLRSymm S)
    (q : MackeyQuad ν ν' α δ) (s : Seq ν) {p : ℕ} (hp : Multiset.card q.α = p)
    (hs : ∀ a' : Fin (Multiset.card (q.α + q.β)), a'.val < p →
      (seqCast q.h₁.symm s).1 a' ∈ q.β → ((seqCast q.h₁.symm s).1 a').isLeft)
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    ((e s : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν') : TensorKLR S ν ν') • w ∈
      mackeyTopOneSpan q (CutInput Q Λ θ β N) := by
  refine e_tmul_one_smul_mackeyLeftInd_mem_span q hsym s (violatedLoadings q.β) ?_
    (cutInput_tail_smul_eq_zero q) w
  intro u hu i j h
  by_cases hc : 0 < Multiset.card q.β
  · refine mem_violatedLoadings.2 ⟨hc, ?_⟩
    have hmem : j.1 ⟨0, hc⟩ ∈ q.β := by
      have hm := Multiset.mem_map_of_mem j.1 (Finset.mem_univ_val (⟨0, hc⟩ : Fin _))
      rwa [j.2] at hm
    change (j.1 ⟨0, hc⟩).isLeft
    rw [tail_val_of_append_eq h] at hmem ⊢
    exact hs _ (hp ▸ shuffle_first_tail_lt_of_ne_one u hu hc) hmem
  · exfalso
    refine hu (shuffle_eq_one_of_tail_fixed u fun y => ?_)
    exact absurd y.2 (by omega)

/-- **L3 for a loading split at `p + M`**: on a Mackey datum `λ` with `M` strands of the top
cut after `p + M`, if the strands of `σ` before `p` with labels in `δ` are black, then
`(1_{σ^{< p+M}} ⊗ 1) w` lies in the identity-shuffle part. -/
theorem prefixSeq_tmul_one_smul_mem_mackeyTopOneSpan (hsym : KLRSymm S) {p M : ℕ}
    (σ : Seq (α + δ)) (hpM : p + M ≤ Multiset.card (α + δ))
    (hbl : ∀ x : Fin (Multiset.card (α + δ)), x.val < p → σ.1 x ∈ δ → (σ.1 x).isLeft)
    (q : MackeyQuad (Seq.prefixWt σ (p + M) hpM) (Seq.suffixWt σ (p + M) hpM) α δ)
    (hq : Multiset.card q.β = M)
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    ((e (Seq.prefixSeq σ (p + M) hpM) : KLRAlgebra k S (Seq.prefixWt σ (p + M) hpM)) ⊗ₜ
      (1 : KLRAlgebra k S (Seq.suffixWt σ (p + M) hpM)) : TensorKLR S _ _) • w ∈
        mackeyTopOneSpan q (CutInput Q Λ θ β N) := by
  have hcardν := Seq.card_prefixWt σ (p + M) hpM
  have hcq : Multiset.card q.α + Multiset.card q.β = p + M := by
    rw [← Multiset.card_add, q.h₁, hcardν]
  have hlbl : ∀ (a' : Fin (Multiset.card (q.α + q.β))),
      (seqCast q.h₁.symm (Seq.prefixSeq σ (p + M) hpM)).1 a' =
        σ.1 ⟨a'.val, by
          have := a'.2; have h2 := Multiset.card_add q.α q.β; omega⟩ := by
    intro a'
    rw [seqCast_apply, Seq.prefixSeq_apply]
    rfl
  refine cutInput_e_tmul_one_smul_mackeyLeftInd_mem_span hsym q _ (p := p) (by omega) ?_ w
  intro a' ha' hmem
  rw [hlbl] at hmem ⊢
  have key : ∀ z, z ∈ q.β → z ∈ δ := fun z hz => by
    rw [← q.h₄]; exact Multiset.mem_add.2 (Or.inl hz)
  exact hbl _ ha' (key _ hmem)

variable [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **L2 and L3 together, on the top layer**: on the `M`-th layer of `Ind N` for the top cut at
`p + M`, `e(σ)` lands in the span of the images under `Ξ_λ` of the identity-shuffle parts
`mackeyTopOneSpan` of the data `λ` of weight `W`, the weight of the labels of `σ` at
`p, …, p + M - 1`. -/
theorem indMackeyLayerAct_e_mem_of_black_mackeyTopOne (hsym : KLRSymm S) {p M : ℕ}
    (σ : Seq (α + δ)) (hpM : p + M ≤ Multiset.card (α + δ))
    (hbl : ∀ x : Fin (Multiset.card (α + δ)), x.val < p → σ.1 x ∈ δ → (σ.1 x).isLeft)
    (W : Multiset (I ⊕ Fin (a + r))) (hW : windowWt p M σ hpM = W)
    (y : IndMackeyLayer S α δ (CutInput Q Λ θ β N)
      (Multiset.card (Seq.prefixWt σ (p + M) hpM)) M) :
    indMackeyLayerAct (CutInput Q Λ θ β N) (e σ : KLRAlgebra k S (α + δ))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) M y ∈
      ⨆ (q : {q : MackeyQuad (Seq.prefixWt σ (p + M) hpM) (Seq.suffixWt σ (p + M) hpM) α δ //
        Multiset.card q.β = M}) (_ : q.1.β = W),
        (mackeyTopOneSpan q.1 (CutInput Q Λ θ β N)).map
          (indMackeyLeftMap (Q := S) (Seq.prefixWt_add_suffixWt σ (p + M) hpM).symm
            (CutInput Q Λ θ β N) q.1 q.2) := by
  subst hW
  have hm := indTopAct_e_tmul_mem_iSup_map (Q := S)
    (Seq.prefixWt_add_suffixWt σ (p + M) hpM).symm (CutInput Q Λ θ β N) hsym
    (Seq.prefixSeq σ (p + M) hpM) (Seq.suffixSeq σ (p + M) hpM)
    (fun q => q.1.β = windowWt p M σ hpM) (fun q => mackeyTopOneSpan q.1 (CutInput Q Λ θ β N))
    (fun q hq w => prefixSeq_tmul_one_smul_eq_zero hsym σ hpM hbl q (Or.inr ⟨rfl, hq⟩) w)
    (fun q _ w => prefixSeq_tmul_one_smul_mem_mackeyTopOneSpan hsym σ hpM hbl q.1 q.2 w) y
  rw [← indMackeyLayerAct_e_append, Seq.seqCast_append_prefixSeq_suffixSeq] at hm
  exact hm

end Categorification.Stendhal
