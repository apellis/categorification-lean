/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingWindow

/-!
# The loading idempotents on the identity-shuffle spans of the leading Mackey layers

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the e-form of
(T_w) of the handoff).

For a loading `s` with the head condition, write `l` for the cut loading and `l⁺_w` for the
window loading. The loadings split at the top cuts: the strands of `l⁺_w` right of the window
are those of `l` right of `p = midPos s`, read in `λ⁺` (`seqCast_map_suffixSeq_cutLoading`),
and the strands of `l⁺_w` up to the end of the window are those of `l` left of `p`, read in
`λ⁺`, followed by `w` in the middle block (`seqCast_append_map_prefixSeq_cutLoading`). In the
algebras: `e(pre l) = ι_{q'.α,0}(e ⊗ 1)` (`castAlg_concat_e_prefixSeq_cutLoading`, from
`castAlg_concat_castAlg_tmul_one_of_β_eq_zero`), `e(pre l⁺_w) = ι_{q.α,q.β}(ρ e ⊗ e(w))`
(`castAlg_concat_relabel_e_prefixSeq`) and `e(suf l⁺_w) = ρ e(suf l)`
(`castAlg_relabel_e_suffixSeq`). With (T_w) of `CupCapTraceCutLeadingWindow`,
`leadingTopOneSpanEquiv` carries `e(l)` after the window factor `ε_{e(w)}` to `e(l⁺_w)`
(`leadingTopOneSpanEquiv_e_smul`).

`Ξ_λ` carries `e(pre σ) ⊗ e(suf σ)` to `e(σ)` on the layers (`indMackeyLeftMap_e_smul`). Hence
`leadingLayerSpanEquiv` carries `Ξ_{q₁}(e(l) · ε_{e(w)} y)` to `e(l⁺_w) · Ξ_{q₀}(L y)` on the
layer `N` of the induced model of `S_+(X)` (`leadingLayerSpanEquiv_e_smul`).

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `KLR.KLRAlgebra.castAlg_concat_castAlg_tmul_one_of_β_eq_zero`,
  `KLR.KLRAlgebra.indMackeyLayerAct_congr`, `KLR.KLRAlgebra.indMackeyLeftMap_e_smul`.
* `Stendhal.CupCap.seqCast_map_suffixSeq_cutLoading`,
  `Stendhal.CupCap.seqCast_append_map_prefixSeq_cutLoading`, `Stendhal.CupCap.leadingQuad'_α_eq`,
  `Stendhal.CupCap.castAlg_concat_e_prefixSeq_cutLoading`,
  `Stendhal.CupCap.castAlg_concat_relabel_e_prefixSeq`,
  `Stendhal.CupCap.castAlg_relabel_e_suffixSeq`, `Stendhal.CupCap.leadingTopOneSpanEquiv_e_smul`,
  `Stendhal.CupCap.leadingLayerSpanEquiv_e_smul`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}

/-- For a Mackey datum with `β = 0`, `a ↦ ι_{α,0}(a ⊗ 1)` is the identity of `R(ν)` up to
`ν = α`. -/
theorem castAlg_concat_castAlg_tmul_one_of_β_eq_zero (q : MackeyQuad ν ν' ν'' ν''')
    (hβ : q.β = 0) (hα : ν = q.α) (a : KLRAlgebra k Q ν) :
    castAlg Q q.h₁ (concat Q q.α q.β (castAlg Q hα a ⊗ₜ (1 : KLRAlgebra k Q q.β))) = a := by
  obtain ⟨α, β, γ, δ, h₁, h₂, h₃, h₄⟩ := q
  simp only at hβ hα ⊢
  subst hβ hα
  rw [castAlg_rfl, castAlg_eq_castKLR]
  exact concat_one_right a

section Layers

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (TensorKLR Q ν'' ν''') N]

/-- `indMackeyLayerAct` depends only on the element acting. -/
theorem indMackeyLayerAct_congr {n : ℕ} (c : ℕ) {z z' : KLRAlgebra k Q (ν'' + ν''')}
    (hzz : z = z')
    (hz : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      z * y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c)
    (hz' : ∀ c y, y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c →
      z' * y ∈ mackeyFilt k Q (ν'' + ν''') n (Multiset.card ν'') c) :
    indMackeyLayerAct N z hz c = indMackeyLayerAct N z' hz' c := by
  subst hzz
  rfl

/-- **`Ξ_λ` carries `e(pre σ) ⊗ e(suf σ)` to `e(σ)`**: for the top cut of a loading `σ` after
`n` strands, `Ξ_λ (e(pre σ) ⊗ e(suf σ) · w) = e(σ) · Ξ_λ w` on the layers. -/
theorem indMackeyLeftMap_e_smul (σ : Seq (ν'' + ν''')) (n : ℕ)
    (hn : n ≤ Multiset.card (ν'' + ν'''))
    (q : MackeyQuad (Seq.prefixWt σ n hn) (Seq.suffixWt σ n hn) ν'' ν''') {c : ℕ}
    (hc : Multiset.card q.β = c) (w : MackeyLeftInd Q N q) :
    indMackeyLeftMap (Seq.prefixWt_add_suffixWt σ n hn).symm N q hc
        (((e (Seq.prefixSeq σ n hn) : KLRAlgebra k Q _) ⊗ₜ
          (e (Seq.suffixSeq σ n hn) : KLRAlgebra k Q _) : TensorKLR Q _ _) • w) =
      indMackeyLayerAct N (e σ : KLRAlgebra k Q (ν'' + ν'''))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) c
        (indMackeyLeftMap (Seq.prefixWt_add_suffixWt σ n hn).symm N q hc w) := by
  rw [indMackeyLeftMap_smul, ← indMackeyLayerAct_e_append]
  exact LinearMap.congr_fun (indMackeyLayerAct_congr N c
    (congrArg e (Seq.seqCast_append_prefixSeq_suffixSeq σ n hn)) _ _) _

end Layers

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Seqs

private theorem seq_map_val {J J' : Type*} (g : J → J') {ν : Multiset J} (i : Seq ν)
    (a : Fin (Multiset.card (ν.map g))) :
    (Seq.map g i).1 a = g (i.1 (Fin.cast (Multiset.card_map g ν) a)) := rfl

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {θ γ ν₀ : Multiset I}

/-- **The strands right of the window of the window loading** are those right of `p` of the
cut loading, read in `λ⁺`. -/
theorem seqCast_map_suffixSeq_cutLoading (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) {δ' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {δ : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (h' : Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) = δ')
    (hd : δ'.map (cutToPlusColour (I := I) j hj) = δ)
    (h : δ = Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)) :
    seqCast h (seqCast hd (Seq.map (cutToPlusColour (I := I) j hj) (seqCast h'
        (Seq.suffixSeq (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))))) =
      Seq.suffixSeq (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) := by
  apply Subtype.ext
  funext b
  have hm := midPos_le j s
  have hb := b.2
  have h1 := Seq.card_suffixWt (windowLoading j hj θ γ ν₀ s w)
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)
  have h2 := card_windowLoading_weight (I := I) (hj := hj) (θ := θ) (γ := γ) (ν₀ := ν₀)
  have h3 := card_plus j hj (θ + γ) ν₀
  have h4 := Multiset.card_map (cupColour (I := I) j hj) (stendhalWeight 2 ν₀)
  have hy : midPos j s + Multiset.card (stendhalWeight 2 ν₀) + b.val <
      Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
    rw [card_plus j hj, Multiset.card_map]
    omega
  rw [seqCast_apply, seqCast_apply, seq_map_val, seqCast_apply, Seq.suffixSeq_apply,
    Seq.suffixSeq_apply,
    cutLoading_apply s _ ⟨midPos j s + b.val, by omega⟩ (by simp),
    windowLoading_lbl (hj := hj) s w _ ⟨_, hy⟩ rfl,
    insertSeq_lbl_ge s (midPos_le j s) _ ⟨midPos j s + b.val, by omega⟩ (by simp)
      (by simp only; omega)]
  exact congrFun (cutToPlusColour_comp_cast j hj) _

/-- **The strands left of the end of the window of the window loading** are the strands left
of `p` of the cut loading, read in `λ⁺`, followed by the window `w` in the middle block. -/
theorem seqCast_append_map_prefixSeq_cutLoading (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) {α' : Multiset (I ⊕ Fin (j + (ℓ - j)))}
    {α β : Multiset (I ⊕ Fin (j + (2 + (ℓ - j))))}
    (hα' : Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) = α')
    (hα : α'.map (cutToPlusColour (I := I) j hj) = α)
    (hβ : ((stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))).map
      (Sum.map (id : I → I) (Fin.natAdd j)) = β)
    (h₁ : α + β = Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)) :
    seqCast h₁ ((seqCast hα (Seq.map (cutToPlusColour (I := I) j hj)
        (seqCast hα' (Seq.prefixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))))).append
        (seqCast hβ (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)))) =
      Seq.prefixSeq (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) := by
  have hcα : Multiset.card α = midPos j s := by
    rw [← hα, Multiset.card_map, ← hα', Seq.card_prefixWt, add_zero]
  apply Subtype.ext
  funext b
  have hm := midPos_le j s
  have hb := b.2
  have h1 := Seq.card_prefixWt (windowLoading j hj θ γ ν₀ s w)
    (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)
  have h3 := card_plus j hj (θ + γ) ν₀
  have h4 := Multiset.card_map (cupColour (I := I) j hj) (stendhalWeight 2 ν₀)
  have hy : b.val < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by omega
  rw [Seq.prefixSeq_apply, windowLoading_lbl (hj := hj) s w _ ⟨b.val, hy⟩ rfl]
  by_cases hlt : b.val < Multiset.card α
  · rw [seqCast_append_apply_lt h₁ _ _ b hlt, seqCast_apply, seq_map_val, seqCast_apply,
      Seq.prefixSeq_apply, cutLoading_apply s _ ⟨b.val, by omega⟩ (by simp),
      insertSeq_lbl_lt s (midPos_le j s) _ ⟨b.val, by omega⟩ (by simp only; omega) rfl]
    exact congrFun (cutToPlusColour_comp_cast j hj) _
  · rw [seqCast_append_apply_ge h₁ _ _ b (by omega), seqCast_apply, seq_map_val, seq_map_val,
      insertSeq_lbl_win s (midPos_le j s) _
        (⟨b.val - midPos j s, by rw [h4]; omega⟩ :
          Fin (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (I := I) j hj))))
        (by simp only; omega), Seq.map_lbl]
    refine (congrFun (windowColour_eq_comp (I := I) (j := j) (hj := hj)).symm _).trans ?_
    exact congrArg _ (congrArg w.1 (Fin.ext (by simp only [Fin.val_cast]; omega)))

end Seqs

section Leading

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type*) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)
local notation "Inner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) ν₀ γ
  (BlocksInner Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X))

variable (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
  (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
  (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
  (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
  (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
  (hq' : q'.β = 0)

local notation "preC" => Seq.prefixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "sufC" => Seq.suffixSeq (cutLoading j hj θ γ s) (midPos j s + 0)
  (midPos_le_card_cut s)
local notation "preP" => Seq.prefixSeq (windowLoading j hj θ γ ν₀ s w)
  (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)
local notation "sufP" => Seq.suffixSeq (windowLoading j hj θ γ ν₀ s w)
  (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)
local notation "wP" => Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w

omit [DecidableEq I] in
include hq' in
/-- The prefix weight of the cut loading is `q'.α`, as `q'.β = 0`. -/
theorem leadingQuad'_α_eq :
    Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) = q'.α :=
  (q'.h₁.symm.trans (congrArg (q'.α + ·) hq')).trans (add_zero _)

include hq' in
/-- **The head factor of `e(l)`**: `e(pre l) = ι_{q'.α,0}(e ⊗ 1)` for the cut loading `l`. -/
theorem castAlg_concat_e_prefixSeq_cutLoading :
    castAlg Sc q'.h₁ (concat Sc q'.α q'.β (castAlg Sc (leadingQuad'_α_eq s q' hq')
        (e preC : KLRAlgebra k Sc _) ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) =
      (e preC : KLRAlgebra k Sc _) :=
  castAlg_concat_castAlg_tmul_one_of_β_eq_zero q' hq' _ _

/-- **The first factor of `e(l⁺_w)`**: `e(pre l⁺_w) = ι_{q.α,q.β}(ρ e ⊗ e(w))`, with `ρ` the
relabelling of the head and `e(w)` relabelled from the middle block. -/
theorem castAlg_concat_relabel_e_prefixSeq :
    castAlg Sp q.h₁ (concat Sp q.α q.β
        (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_α_eq_map s w hs q hq q' hq'))
          (castAlg Sc (leadingQuad'_α_eq s q' hq') (e preC : KLRAlgebra k Sc _)) ⊗ₜ
        relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
          (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) (e wP))) =
      (e preP : KLRAlgebra k Sp _) := by
  rw [castAlg_e, relabelHom_e, relabelHom_e, concat_e_tmul_e, castAlg_e, cutPlusRelabel_equiv,
    subfamilyRelabel_equiv]
  exact congrArg e (seqCast_append_map_prefixSeq_cutLoading s w _ _ _ _)

/-- **The second factor of `e(l⁺_w)`**: `e(suf l⁺_w)` is the relabelling of `e(suf l)`. -/
theorem castAlg_relabel_e_suffixSeq :
    castAlg Sp q.h₂ (relabelHom (cutPlusRelabel j hj Q Λ Λc
        (leadingQuad_add_eq_map j hj s w q hq q' hq'))
        (castAlg Sc q'.h₂.symm (e sufC : KLRAlgebra k Sc _))) =
      (e sufP : KLRAlgebra k Sp _) := by
  rw [castAlg_e, relabelHom_e, cutPlusRelabel_equiv, castAlg_e]
  exact congrArg e (seqCast_map_suffixSeq_cutLoading s w _ _ _)

/-- **(T_w), e-form, on the identity-shuffle spans** (Webster v3, Lemma 7.19, trace half,
step L5): `leadingTopOneSpanEquiv` carries the action of `e(l) = e(pre l) ⊗ e(suf l)` after the
window factor `ε_{e(w)}` at `S_cut(Res X)` to the action of `e(l⁺_w)` at `S_+(X)`, for the cut
loading `l` and the window loading `l⁺_w` of `s`. -/
theorem leadingTopOneSpanEquiv_e_smul (y y' : mackeyTopOneSpan (Q := Sc) q' Yc)
    (hy : (y' : MackeyLeftInd Sc Yc q') =
      (((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
        (topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q' (e wP))
            ((topOneCornerEquiv q' Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q'))) :
    (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y' : MackeyLeftInd Sp Nₒ q) =
      (((e preP : KLRAlgebra k Sp _) ⊗ₜ (e sufP : KLRAlgebra k Sp _) : TensorKLR Sp _ _) •
        (leadingTopOneSpanEquiv X hQ s w hs q hq q' hq' y : MackeyLeftInd Sp Nₒ q)) := by
  have hel : ((e preC : KLRAlgebra k Sc _) ⊗ₜ (e sufC : KLRAlgebra k Sc _) : TensorKLR Sc _ _) =
      castAlg Sc q'.h₁ (concat Sc q'.α q'.β (castAlg Sc (leadingQuad'_α_eq s q' hq')
        (e preC : KLRAlgebra k Sc _) ⊗ₜ (1 : KLRAlgebra k Sc q'.β))) ⊗ₜ
      castAlg Sc q'.h₂ (castAlg Sc q'.h₂.symm (e sufC : KLRAlgebra k Sc _)) := by
    rw [castAlg_concat_e_prefixSeq_cutLoading s q' hq', castAlg_castAlg_symm]
  have hep : ((e preP : KLRAlgebra k Sp _) ⊗ₜ (e sufP : KLRAlgebra k Sp _) : TensorKLR Sp _ _) =
      castAlg Sp q.h₁ (concat Sp q.α q.β
        (relabelHom (cutPlusRelabel j hj Q Λ Λc (leadingQuad_α_eq_map s w hs q hq q' hq'))
          (castAlg Sc (leadingQuad'_α_eq s q' hq') (e preC : KLRAlgebra k Sc _)) ⊗ₜ
        relabelHom (subfamilyRelabel Q (plusBlockLabels Λ Λc j hj)
          (Fin.natAdd_injective _ j) (leadingQuad_β_eq_map s w q hq)) (e wP))) ⊗ₜ
      castAlg Sp q.h₂ (relabelHom (cutPlusRelabel j hj Q Λ Λc
        (leadingQuad_add_eq_map j hj s w q hq q' hq'))
        (castAlg Sc q'.h₂.symm (e sufC : KLRAlgebra k Sc _))) := by
    rw [castAlg_concat_relabel_e_prefixSeq s w hs q hq q' hq',
      castAlg_relabel_e_suffixSeq s w q hq q' hq']
  refine (leadingTopOneSpanEquiv_head_window_smul X hQ s w hs q hq q' hq' _ (e wP) _ y y'
    (hy.trans (congrArg (· • _) hel))).trans ?_
  exact congrArg (· • _) hep.symm

end Leading

section Layer

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

attribute [local instance] botCornerModuleRight botCornerModuleRight_isScalarTower

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)

local notation "Yc" => CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X)
local notation "Nₒ" => CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ)
  (BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ)

/-- **(T_w), e-form, on the leading summands of the layers** (Webster v3, Lemma 7.19, trace
half, step L5): `leadingLayerSpanEquiv` carries `Ξ_{q₁}` of `e(l)` after the window factor
`ε_{e(w)}` to the action of `e(l⁺_w)` on the layer `N` of the induced model of `S_+(X)`. -/
theorem leadingLayerSpanEquiv_e_smul (hsc : KLRSymm Sc) (hsp : KLRSymm Sp)
    (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (q₀ : {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)})
    (hq₀ : q₀.1.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q₁ : {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0})
    (hq₁ : q₁.1.β = 0) (y y' : mackeyTopOneSpan (Q := Sc) q₁.1 Yc)
    (hy : (y' : MackeyLeftInd Sc Yc q₁.1) =
      (((e (Seq.prefixSeq (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) :
          KLRAlgebra k Sc _) ⊗ₜ
        (e (Seq.suffixSeq (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)) :
          KLRAlgebra k Sc _) : TensorKLR Sc _ _) •
        (topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)
          (BalancedTensor.mapRight (plusWindowEnd X s q₁.1
              (e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)))
            ((topOneCornerEquiv q₁.1 Yc (stendhalQ_symm Q (cutLabels j hj Λ) hQ)).symm y)) :
          MackeyLeftInd Sc Yc q₁.1))) :
    (leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
        (Submodule.equivMapOfInjective _
          (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ y')).1 =
      indMackeyLayerAct Nₒ (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀))
        (leadingLayerSpanEquiv X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁
          (Submodule.equivMapOfInjective _
            (indMackeyLeftMap_injective_of_klrSymm _ Yc hsc q₁) _ y)).1 := by
  have a1 := congrArg Subtype.val
    (leadingLayerSpanEquiv_apply X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁ y')
  have a2 := congrArg Subtype.val
    (leadingLayerSpanEquiv_apply X hQ hsc hsp s w hs q₀ hq₀ q₁ hq₁ y)
  have hL := leadingTopOneSpanEquiv_e_smul X hQ s w hs q₀.1 hq₀ q₁.1 hq₁ y y' hy
  refine a1.trans ((Submodule.coe_equivMapOfInjective_apply _ _ _ _).trans ?_)
  refine ((congrArg (indMackeyLeftMap (Q := Sp) _ Nₒ q₀.1 q₀.2) hL).trans
    (indMackeyLeftMap_e_smul Nₒ (windowLoading j hj θ γ ν₀ s w)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)
      q₀.1 q₀.2 _)).trans ?_
  refine congrArg _ ?_
  exact ((Submodule.coe_equivMapOfInjective_apply _ _ _ _).symm.trans a2.symm)

end Layer

end Categorification.Stendhal.CupCap
