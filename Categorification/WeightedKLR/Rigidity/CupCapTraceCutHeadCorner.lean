/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutBotCorner
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutStdLoading

/-!
# The head factors of the leading Mackey data at `S_+` and at `S_cut` agree

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the head factor).

The bottom idempotent `quadBot 1` of a Mackey datum `q` of a cut `A | R` has the head factor
`1_{q.α, q.γ}`, read in `T^A(θ)` through the first-block projection (`botHeadIdem` for three
blocks, `cutBotHeadIdem` for two). When `q.α` is the image of a weight `αh` of the head
labels, this factor is the image in `T^A(θ)` of the concatenation idempotent `1_{αh, θ_A - αh}`
of the head alone (`cutPrefixProjection_castAlg_oneConcat`): it depends on `αh` and the labels
of the head, not on the rest of the cut.

For a loading `s` of `λ` whose red strands left of `p = midPos s` are among `λ_1, …, λ_j`:

* the weight of the first `p + N` strands of the window loading is that of the first `p` strands
  of `s` plus the window weight (`prefixWt_windowLoading`), and the weight of the first `p`
  strands of the cut loading is that of `s` (`prefixWt_cutLoading`);
* both are images of one weight `αh` of the head labels (`exists_headWeight_prefixWt`).

Hence the head factor of the leading datum of `S_+` (weight of the window), relabelled along
`plusBlockLabels_head`, is the head factor of the leading datum of `S_cut` (weight `0`)
(`relabel_botHeadIdem_eq_cutBotHeadIdem`).

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.cutPrefixProjection_e_map`, `Stendhal.cutPrefixProjection_castAlg_oneConcat`,
  `Stendhal.relabelTensorProductAlgebra_tensorOfKLR`,
  `Stendhal.CupCap.prefixWt_windowLoading`, `Stendhal.CupCap.prefixWt_cutLoading`,
  `Stendhal.CupCap.exists_headWeight_prefixWt`,
  `Stendhal.CupCap.relabel_botHeadIdem_eq_cutBotHeadIdem`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

section Head

private theorem seqCast_injective_head {J : Type*} {μ μ' : Multiset J} (h : μ = μ') :
    Function.Injective (Seq.cast h) := by
  subst h
  intro x y hxy
  exact hxy

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ : Multiset I)

local notation "cL" => Sum.map (id : I → I) (Fin.castAdd r : Fin a → Fin (a + r))

/-- **The first-block projection of a cut on a relabelled idempotent**: `e(c ∘ t) ↦` the image
of `e(t)` in `T^A(θ)`. -/
theorem cutPrefixProjection_e_map (t : Seq (stendhalWeight a θ)) :
    cutPrefixProjection (a := a) (r := r) Q Λ θ (e (Seq.map cL t)) =
      tensorOfKLR Q (Λ ∘ Fin.castAdd r) θ (e t) := by
  have h : (e (Seq.map cL t) : KLRAlgebra k (stendhalQ Q Λ) _) =
      relabelEquiv (redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r) θ)
        (e t) := by rw [relabelEquiv_apply, relabelHom_e]; rfl
  rw [h, cutPrefixProjection, redSubfamilyProjection]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]

omit [CommRing k] in
/-- The concatenations of `c(αh)` and `q.γ` are the relabelled concatenations of `αh` and
`θ_A - αh`. -/
theorem image_seqCast_concatSet_eq_map_head {αo γo : Multiset (I ⊕ Fin (a + r))}
    {αh γh : Multiset (I ⊕ Fin a)} (hh : αh + γh = stendhalWeight a θ)
    (h : αo + γo = (stendhalWeight a θ).map cL) (hα : αo = αh.map cL) :
    (concatSet αo γo).image (seqCast h) =
      (concatSet αh γh).image (fun s' => Seq.map cL (Seq.cast hh s')) := by
  subst hα
  have hle : Multiset.card (αh.map cL) ≤ Multiset.card ((stendhalWeight a θ).map cL) := by
    rw [← h, Multiset.card_add]; omega
  have key : ∀ t, t ∈ (concatSet _ γo).image (seqCast h) ↔
      Seq.prefixWt t _ hle = αh.map cL := by
    intro t
    constructor
    · intro ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
      rw [seqCast_eq_cast, Seq.prefixWt_cast]
      exact (Seq.mem_concatSet_iff_prefixWt t₀).1 ht₀
    · intro ht
      refine Finset.mem_image.2 ⟨Seq.cast h.symm t, ?_, ?_⟩
      · rw [Seq.mem_concatSet_iff_prefixWt, Seq.prefixWt_cast]
        exact ht
      · rw [seqCast_eq_cast]
        rfl
  have hc : Function.Injective cL :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective a r⟩
  ext t
  rw [key]
  constructor
  · intro ht
    obtain ⟨s, rfl⟩ := (Seq.map_bijective hc _).2 t
    refine Finset.mem_image.2 ⟨Seq.cast hh.symm s, ?_, rfl⟩
    rw [Seq.mem_concatSet_iff_prefixWt, Seq.prefixWt_cast]
    rw [Seq.prefixWt_map] at ht
    exact (Seq.prefixWt_congr s (by simp) _ _).trans (Multiset.map_injective hc ht)
  · intro ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 ht
    rw [Seq.prefixWt_map, Seq.prefixWt_cast]
    congr 1
    exact (Seq.prefixWt_congr _ (by simp) _ _).trans ((Seq.mem_concatSet_iff_prefixWt s').1 hs')

/-- **The head factor of a concatenation idempotent at a cut**: if `q.α = c(αh)`, the
first-block projection sends `1_{q.α, q.γ}` to the image in `T^A(θ)` of the concatenation
idempotent `1_{αh, γh}` of the head labels. -/
theorem cutPrefixProjection_castAlg_oneConcat {αo γo : Multiset (I ⊕ Fin (a + r))}
    {αh γh : Multiset (I ⊕ Fin a)} (hh : αh + γh = stendhalWeight a θ)
    (h : αo + γo = (stendhalWeight a θ).map cL) (hα : αo = αh.map cL) :
    cutPrefixProjection (a := a) (r := r) Q Λ θ
        (castAlg (stendhalQ Q Λ) h (oneConcat (stendhalQ Q Λ) αo γo)) =
      tensorOfKLR Q (Λ ∘ Fin.castAdd r) θ
        (castAlg (stendhalQ Q (Λ ∘ Fin.castAdd r)) hh
          (oneConcat (stendhalQ Q (Λ ∘ Fin.castAdd r)) αh γh)) := by
  have hc : Function.Injective cL :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective a r⟩
  rw [oneConcat, castAlg_eSum, image_seqCast_concatSet_eq_map_head θ hh h hα, oneConcat,
    castAlg_eSum, eSum, eSum, map_sum]
  simp only [tensorOfKLR, map_sum]
  rw [Finset.sum_image, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s' _ => ?_
    rw [cutPrefixProjection_e_map, seqCast_eq_cast]
  · intro x _ y _ hxy
    rw [seqCast_eq_cast, seqCast_eq_cast] at hxy
    exact (seqCast_injective_head hh) hxy
  · intro x _ y _ hxy
    exact (seqCast_injective_head hh) ((Seq.map_bijective hc _).1 hxy)

end Head

/-- Relabelling `T^{Λ₁}(θ)` along `Λ₁ = Λ₂` fixes the images of concatenation idempotents. -/
theorem relabelTensorProductAlgebra_tensorOfKLR {I k : Type*} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (hΛ : Λ₁ = Λ₂)
    (θ : Multiset I) {αh γh : Multiset (I ⊕ Fin n)} (hh : αh + γh = stendhalWeight n θ) :
    relabelTensorProductAlgebra Q hΛ θ (tensorOfKLR Q Λ₁ θ
        (castAlg (stendhalQ Q Λ₁) hh (oneConcat (stendhalQ Q Λ₁) αh γh))) =
      tensorOfKLR Q Λ₂ θ (castAlg (stendhalQ Q Λ₂) hh (oneConcat (stendhalQ Q Λ₂) αh γh)) := by
  subst hΛ
  rfl

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {θ γ ν₀ : Multiset I}

/-- **The weight of the first `p` strands of the cut loading** is that of `s`, `p = midPos s`. -/
theorem prefixWt_cutLoading (s : Seq (stendhalWeight ℓ (θ + γ))) :
    Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) =
      (Seq.prefixWt s (midPos j s) (midPos_le j s)).map
        (Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm)) := by
  rw [Seq.prefixWt, Seq.prefixWt, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  exact cutLoading_apply s _ _ rfl

/-- **The weight of the first `p + N` strands of the window loading** is the weight of the
first `p = midPos s` strands of `s`, read in `λ⁺`, plus the window weight. -/
theorem prefixWt_windowLoading (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) :
    Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) =
      (Seq.prefixWt s (midPos j s) (midPos_le j s)).map
          (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) +
        (stendhalWeight 2 ν₀).map (windowColour j hj) := by
  rw [← windowWt_windowLoading s w, Seq.prefixWt, Seq.prefixWt, windowWt, univ_val_fin_add,
    Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map]
  congr 1
  · refine Multiset.map_congr rfl fun x _ => ?_
    have hm := midPos_le j s
    have hy : x.val < Multiset.card (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀)) := by
      have := x.2; rw [card_plus j hj, Multiset.card_map]; omega
    simp only [Function.comp_apply]
    rw [windowLoading_lbl (hj := hj) s w _ ⟨x.val, hy⟩ (by simp),
      insertSeq_lbl_lt s (midPos_le j s) _ (Fin.castLE (midPos_le j s) x) x.2 rfl]

/-- **The first `p` strands of `s` carry a weight of the head labels**, for `s` whose red
strands left of `p = midPos s` are among `λ_1, …, λ_j`. -/
theorem exists_headWeight_prefixWt (s : Seq (stendhalWeight ℓ (θ + γ)))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j) :
    ∃ αh : Multiset (I ⊕ Fin j), Seq.prefixWt s (midPos j s) (midPos_le j s) =
      αh.map (Sum.map (id : I → I) (Fin.castLE hj)) := by
  have hex : ∀ x : Fin (midPos j s), ∃ y : I ⊕ Fin j,
      Sum.map (id : I → I) (Fin.castLE hj) y = s.1 (Fin.castLE (midPos_le j s) x) := by
    intro x
    rcases hsl : s.1 (Fin.castLE (midPos_le j s) x) with b | u
    · exact ⟨.inl b, rfl⟩
    · exact ⟨.inr ⟨u.val, hs _ x.2 u hsl⟩, congrArg Sum.inr (Fin.ext rfl)⟩
  choose g hg using hex
  refine ⟨Finset.univ.val.map g, ?_⟩
  rw [Seq.prefixWt, Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => (hg x).symm

variable {k : Type*} [CommRing k] [DecidableEq I] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)

/-- **The head factors of the leading Mackey data agree** (Webster v3, Lemma 7.19, trace half,
step L5). Let `s` be a loading of `λ` whose red strands left of `p = midPos s` are among
`λ_1, …, λ_j`. For a Mackey datum `q` of the outer cut of `S_+` at the end of the window whose
weight is the window weight, and a datum `q'` of the cut of `S_cut` at `p` with weight `0`, the
head factor `1_{q.α, q.γ}` of `S_+`, relabelled along `plusBlockLabels_head`, is the head factor
`1_{q'.α, q'.γ}` of `S_cut`. -/
theorem relabel_botHeadIdem_eq_cutBotHeadIdem (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
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
    (hq' : q'.β = 0) :
    relabelTensorProductAlgebra Q (plusBlockLabels_head Λ Λc j hj) θ
        (botHeadIdem Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ q) =
      cutBotHeadIdem Q (cutLabels j hj Λ) θ γ q' := by
  obtain ⟨αh, hαh⟩ := exists_headWeight_prefixWt (hj := hj) s hs
  have hα' : q'.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) := by
    have h1 := q'.h₁
    rw [hq', add_zero] at h1
    refine h1.trans ?_
    rw [prefixWt_cutLoading, hαh, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · exact congrArg Sum.inr (Fin.ext rfl)
  have hα : q.α = αh.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) := by
    have h1 := q.h₁.trans (prefixWt_windowLoading s w)
    rw [hq, hαh, Multiset.map_map, add_left_inj] at h1
    rw [h1]
    refine Multiset.map_congr rfl fun x _ => ?_
    rcases x with b | u
    · rfl
    · refine congrArg Sum.inr (Fin.ext ?_)
      simp [oldRed, u.2]
  have hinj : Function.Injective (Sum.map (id : I → I) (Fin.castAdd (ℓ - j) : Fin j → _)) :=
    Sum.map_injective.2 ⟨Function.injective_id, Fin.castAdd_injective j (ℓ - j)⟩
  have hle : αh ≤ stendhalWeight j θ := by
    have h3 := Multiset.le_add_right q'.α q'.γ
    rw [q'.h₃, hα'] at h3
    exact (Multiset.map_le_map_iff hinj).1 h3
  have hh : αh + (stendhalWeight j θ - αh) = stendhalWeight j θ := add_tsub_cancel_of_le hle
  rw [botHeadIdem, cutBotHeadIdem, cutPrefixProjection_castAlg_oneConcat Q _ θ hh q.h₃ hα,
    cutPrefixProjection_castAlg_oneConcat Q _ θ hh q'.h₃ hα',
    relabelTensorProductAlgebra_tensorOfKLR]
  rfl

end Categorification.Stendhal.CupCap
