/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyTop
import Categorification.KLR.MackeyLayerLoading
import Categorification.KLR.SeqSplit

/-!
# A loading idempotent on the Mackey filtration of a partial standardization

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L2: the filtration of
`e_s 𝕊(N)` by the head strands. Here `𝕊(N)` is the partial standardization of a cut
(`CutStandard`), filtered by the Mackey filtration for a top cut `ν | ν'` of the weight
(`cutMackeyFilt (|ν|)`), and `e = e(i j)` is the idempotent of a concatenation of loadings
`i` of `ν` and `j` of `ν'`.

* If `e(i) ⊗ 1` kills every Mackey datum `λ` with `|λ| = c`, then `e` maps `F_c` into
  `F_{c-1}` (`cutStandardAction_e_append_mem_lower`).
* If this holds for every `c` with `c₀ < c ≤ |ν|`, then `e 𝕊(N) ⊆ F_{c₀}`
  (`cutStandardAction_e_append_mem`).
* On the layer `F_c / F_{c-1}` of the induced module, `e` lands in the span of the images of
  the maps `Ξ_λ` on which `e(i) ⊗ 1` does not vanish (`indMackeyLayerAct_e_append_mem_iSup`).

Webster's proof does not spell this out. Together with the vanishing results of
`CutStandardMackeyTop` it shows that on `e_s`, for the window of the cap generators at `s`, the
filtration of `S_+` starts at the step `N = |window|` and the top layer comes from the datum
`λ₀` of the window strands alone.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `Stendhal.cutStandardAction_e_append_mem_lower`, `Stendhal.cutStandardAction_e_append_mem`,
  `Stendhal.indMackeyLayerAct_e_append_mem_iSup`.
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
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)
  (hsym : KLRSymm (stendhalQ Q Λ))

variable {ν ν' : Multiset (I ⊕ Fin (a + r))}

local notation "eij" h:max i:max j:max =>
  (e (seqCast (Eq.symm h) (Seq.append i j)) : KLRAlgebra k (stendhalQ Q Λ) (α + δ))

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- The action of a concatenated loading on the class of an element of the step `c`. -/
theorem indMackeyLayerAct_e_append_mk (h : α + δ = ν + ν') (i : Seq ν) (j : Seq ν') {c : ℕ}
    {y : CutShuffle Q Λ θ β N} (hy : y ∈ indMackeyFilt Q Λ θ β N (Multiset.card ν) c) :
    indMackeyLayerAct (CutInput Q Λ θ β N) (eij h i j) (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c
        (Submodule.Quotient.mk (⟨y, hy⟩ : indMackeyStep S α δ (CutInput Q Λ θ β N)
          (Multiset.card ν) c)) =
      Submodule.Quotient.mk ⟨eij h i j • y, indMackeyFilt_smul (preservesMackeyFilt_e _) hy⟩ :=
  rfl

include hQ hsym in
/-- **A loading killing every Mackey datum of size `c` lowers the step `c`**: if `e(i) ⊗ 1`
kills `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` for every `λ` with `|λ| = c`, then
`e(i j)` maps `F_c(𝕊)` into `F_{c-1}(𝕊)`. -/
theorem cutStandardAction_e_append_mem_lower (h : α + δ = ν + ν') (i : Seq ν) (j : Seq ν')
    {c : ℕ}
    (hk : ∀ q : {q : MackeyQuad ν ν' α δ // Multiset.card q.β = c},
      ∀ w : MackeyLeftInd S (CutInput Q Λ θ β N) q.1,
        ((e i : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν') : TensorKLR S ν ν') • w = 0)
    {v : CutStandard Q Λ θ β N} (hv : v ∈ cutMackeyFilt Q Λ θ β N (Multiset.card ν) c) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eij h i j)) v ∈
      cutMackeyFiltLower Q Λ θ β N (Multiset.card ν) c := by
  obtain ⟨y, hy, rfl⟩ := hv
  have h0 := indTopAct_e_tmul_e_eq_zero (Q := S) h (CutInput Q Λ θ β N) hsym
    i j hk (Submodule.Quotient.mk (⟨y, hy⟩ : indMackeyStep S α δ (CutInput Q Λ θ β N)
      (Multiset.card ν) c))
  rw [← indMackeyLayerAct_e_append] at h0
  change (Submodule.Quotient.mk (⟨eij h i j • y, indMackeyFilt_smul (preservesMackeyFilt_e _) hy⟩ :
    indMackeyStep S α δ (CutInput Q Λ θ β N) (Multiset.card ν) c) :
      IndMackeyLayer S α δ (CutInput Q Λ θ β N) (Multiset.card ν) c) = 0 at h0
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  change cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eij h i j))
    ((excludedSpace (cutShuffleAction Q Λ θ β N) (cutOrderedLoadings θ β)).mkQ y) ∈ _
  rw [cutStandardAction_affineToTensor]
  refine ⟨eij h i j • y, ?_, rfl⟩
  rw [indMackeyFiltLower_eq_indMackeyLower]
  exact h1

include hQ hsym in
/-- **A loading killing the Mackey data above `c₀` maps `𝕊(N)` into `F_{c₀}`**. -/
theorem cutStandardAction_e_append_mem (h : α + δ = ν + ν') (i : Seq ν) (j : Seq ν')
    (hn : Multiset.card ν ≤ Multiset.card (α + δ)) (c₀ : ℕ)
    (hk : ∀ c, c₀ < c → c ≤ Multiset.card ν →
      ∀ q : {q : MackeyQuad ν ν' α δ // Multiset.card q.β = c},
      ∀ w : MackeyLeftInd S (CutInput Q Λ θ β N) q.1,
        ((e i : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν') : TensorKLR S ν ν') • w = 0)
    (v : CutStandard Q Λ θ β N) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eij h i j)) v ∈
      cutMackeyFilt Q Λ θ β N (Multiset.card ν) c₀ := by
  set E := cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (eij h i j))
  have hE : ∀ v, E (E v) = E v := fun v => by
    change (E * E) v = E v
    rw [← map_mul, ← map_mul, e_mul_self]
  have key : ∀ d, c₀ + d ≤ Multiset.card ν → ∀ v ∈ cutMackeyFilt Q Λ θ β N (Multiset.card ν)
      (c₀ + d), E v ∈ cutMackeyFilt Q Λ θ β N (Multiset.card ν) c₀ := by
    intro d
    induction d with
    | zero => exact fun _ v hv => cutMackeyFilt_action hQ (preservesMackeyFilt_e _) hv
    | succ d ih =>
      intro hd v hv
      have h1 := cutStandardAction_e_append_mem_lower hQ hsym h i j
        (hk (c₀ + (d + 1)) (by omega) hd) hv
      rw [show c₀ + (d + 1) = (c₀ + d) + 1 from rfl, cutMackeyFiltLower_succ] at h1
      rw [← hE]
      exact ih (by omega) _ h1
  by_cases hc : c₀ ≤ Multiset.card ν
  · have hv : v ∈ cutMackeyFilt Q Λ θ β N (Multiset.card ν) (c₀ + (Multiset.card ν - c₀)) := by
      rw [Nat.add_sub_cancel' hc, cutMackeyFilt_eq_top hn]; exact Submodule.mem_top
    exact key _ (by omega) v hv
  · refine cutMackeyFilt_mono (Nat.le_of_not_le hc) ?_
    rw [cutMackeyFilt_eq_top hn]; exact Submodule.mem_top

include hsym in
/-- **On a layer of the induced module, a loading lands in the surviving `Ξ_λ`**: if
`e(i) ⊗ 1` kills every datum `λ` of size `c` outside `P`, then `e(i j)` maps the `c`-th layer
into the span of the images of `Ξ_λ`, `λ ∈ P`. -/
theorem indMackeyLayerAct_e_append_mem_iSup (h : α + δ = ν + ν') (i : Seq ν) (j : Seq ν')
    {c : ℕ} (P : {q : MackeyQuad ν ν' α δ // Multiset.card q.β = c} → Prop)
    (hk : ∀ q, ¬ P q → ∀ w : MackeyLeftInd S (CutInput Q Λ θ β N) q.1,
      ((e i : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν') : TensorKLR S ν ν') • w = 0)
    (y : IndMackeyLayer S α δ (CutInput Q Λ θ β N) (Multiset.card ν) c) :
    indMackeyLayerAct (CutInput Q Λ θ β N) (eij h i j) (fun _ _ hy => e_mul_mem_mackeyFilt _ hy)
        c y ∈
      ⨆ (q) (_ : P q), LinearMap.range
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q.1 q.2) := by
  rw [indMackeyLayerAct_e_append]
  exact indTopAct_e_tmul_mem_iSup (Q := S) h (CutInput Q Λ θ β N) hsym i j P hk y

/-! ### Loadings whose strands of the second block before `p` are black -/

omit [DecidableEq I] in
theorem map_univ_fin_cast {X : Type*} {n n' : ℕ} (hn : n = n') (f : Fin n' → X) :
    (Finset.univ.val.map fun b : Fin n => f (Fin.cast hn b)) = Finset.univ.val.map f := by
  subst hn; rfl

variable (p M : ℕ)

/-- The weight of the labels of a loading `σ` at the positions `p, …, p + M - 1`. -/
def windowWt (σ : Seq (α + δ)) (hpM : p + M ≤ Multiset.card (α + δ)) :
    Multiset (I ⊕ Fin (a + r)) :=
  Finset.univ.val.map fun b : Fin M => σ.1 ⟨p + b.val, by omega⟩

variable {p M}

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
include hsym in
/-- **The Mackey data on a loading whose second-block strands before `p` are black**: with
the top cut after `p + M` (`Seq.prefixWt`), `e(i) ⊗ 1` kills every datum `λ` with more than
`M` strands, and every datum with `M` strands whose weight is not that of the labels at
`p, …, p + M - 1`. -/
theorem prefixSeq_tmul_one_smul_eq_zero (σ : Seq (α + δ)) (hpM : p + M ≤ Multiset.card (α + δ))
    (hbl : ∀ x : Fin (Multiset.card (α + δ)), x.val < p → σ.1 x ∈ δ → (σ.1 x).isLeft)
    {c : ℕ} (q : {q : MackeyQuad (Seq.prefixWt σ (p + M) hpM) (Seq.suffixWt σ (p + M) hpM) α δ //
      Multiset.card q.β = c})
    (hq : M < c ∨ (c = M ∧ q.1.β ≠ windowWt p M σ hpM))
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q.1) :
    ((e (Seq.prefixSeq σ (p + M) hpM) : KLRAlgebra k S (Seq.prefixWt σ (p + M) hpM)) ⊗ₜ
      (1 : KLRAlgebra k S (Seq.suffixWt σ (p + M) hpM)) : TensorKLR S _ _) • w = 0 := by
  have hcardν := Seq.card_prefixWt σ (p + M) hpM
  have hcq : Multiset.card q.1.α + Multiset.card q.1.β = p + M := by
    rw [← Multiset.card_add, q.1.h₁, hcardν]
  have hlbl : ∀ (a' : Fin (Multiset.card (q.1.α + q.1.β))),
      (seqCast q.1.h₁.symm (Seq.prefixSeq σ (p + M) hpM)).1 a' =
        σ.1 ⟨a'.val, by
          have := a'.2; have h2 := Multiset.card_add q.1.α q.1.β; omega⟩ := by
    intro a'
    rw [seqCast_apply, Seq.prefixSeq_apply]
    rfl
  refine cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero hsym q.1 _ (p := p) (by omega) ?_ ?_ w
  · intro a' ha' hmem
    rw [hlbl] at hmem ⊢
    have key : ∀ z, z ∈ q.1.β → z ∈ δ := fun z hz => by
      rw [← q.1.h₄]; exact Multiset.mem_add.2 (Or.inl hz)
    exact hbl _ ha' (key _ hmem)
  · rcases hq with hlt | ⟨rfl, hne⟩
    · left; have := q.2; omega
    · right
      refine ⟨by have := q.2; omega, fun heq => hne (heq.symm.trans ?_)⟩
      rw [windowWt, ← map_univ_fin_cast q.2]
      refine Multiset.map_congr rfl fun b _ => ?_
      rw [hlbl]
      exact congrArg σ.1 (Fin.ext (by simp only [Seq.posR_val, Fin.val_cast]; have := q.2; omega))

include hQ hsym in
/-- **A loading whose second-block strands before `p` are black maps `𝕊(N)` into `F_M`** for
the top cut at `p + M`. -/
theorem cutStandardAction_e_mem_of_black (σ : Seq (α + δ))
    (hpM : p + M ≤ Multiset.card (α + δ))
    (hbl : ∀ x : Fin (Multiset.card (α + δ)), x.val < p → σ.1 x ∈ δ → (σ.1 x).isLeft)
    (v : CutStandard Q Λ θ β N) :
    cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e σ)) v ∈
      cutMackeyFilt Q Λ θ β N (p + M) M := by
  have hm := cutStandardAction_e_append_mem hQ hsym (Seq.prefixWt_add_suffixWt σ (p + M) hpM).symm
    (Seq.prefixSeq σ (p + M) hpM) (Seq.suffixSeq σ (p + M) hpM)
    (by rw [Seq.card_prefixWt]; exact hpM) M
    (fun c hc _ q w => prefixSeq_tmul_one_smul_eq_zero hsym σ hpM hbl q (Or.inl hc) w) v
  rw [Seq.seqCast_append_prefixSeq_suffixSeq, Seq.card_prefixWt] at hm
  exact hm

include hsym in
/-- **The top layer on such a loading**: on the `M`-th layer of `Ind N` for the top cut at
`p + M`, `e(σ)` lands in the span of the images of the `Ξ_λ` whose datum has the weight `W` of
the labels of `σ` at `p, …, p + M - 1`. -/
theorem indMackeyLayerAct_e_mem_of_black (σ : Seq (α + δ))
    (hpM : p + M ≤ Multiset.card (α + δ))
    (hbl : ∀ x : Fin (Multiset.card (α + δ)), x.val < p → σ.1 x ∈ δ → (σ.1 x).isLeft)
    (W : Multiset (I ⊕ Fin (a + r))) (hW : windowWt p M σ hpM = W)
    (y : IndMackeyLayer S α δ (CutInput Q Λ θ β N)
      (Multiset.card (Seq.prefixWt σ (p + M) hpM)) M) :
    indMackeyLayerAct (CutInput Q Λ θ β N) (e σ : KLRAlgebra k S (α + δ))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) M y ∈
      ⨆ (q : {q : MackeyQuad (Seq.prefixWt σ (p + M) hpM) (Seq.suffixWt σ (p + M) hpM) α δ //
        Multiset.card q.β = M}) (_ : q.1.β = W), LinearMap.range
        (indMackeyLeftMap (Q := S) (Seq.prefixWt_add_suffixWt σ (p + M) hpM).symm
          (CutInput Q Λ θ β N) q.1 q.2) := by
  subst hW
  have hm := indMackeyLayerAct_e_append_mem_iSup hsym
    (Seq.prefixWt_add_suffixWt σ (p + M) hpM).symm (Seq.prefixSeq σ (p + M) hpM)
    (Seq.suffixSeq σ (p + M) hpM) (fun q => q.1.β = windowWt p M σ hpM)
    (fun q hq w => prefixSeq_tmul_one_smul_eq_zero hsym σ hpM hbl q (Or.inr ⟨rfl, hq⟩) w) y
  rw [Seq.seqCast_append_prefixSeq_suffixSeq] at hm
  exact hm

end Categorification.Stendhal
