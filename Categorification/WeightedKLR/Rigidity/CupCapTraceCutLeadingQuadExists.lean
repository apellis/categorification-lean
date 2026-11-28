/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutWindowResSum

/-!
# Existence of the leading Mackey data of `S_+` and of `S_cut`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5.

A Mackey datum of a cut is determined by its weight `λ = q.β` (`MackeyQuad.ext_of_β`), and one
of weight `λ` exists as soon as `λ` fits in the bottom right block and in the top left block and
the rest of the top left block fits in the bottom left block (`MackeyQuad.ofLe`). For a loading
`s` of `λ`, `p = midPos s`, both leading data of step L5 (weight `0` at the cut `p` of
`S_cut`, weight of the window at the cut `p + N` of `S_+`) exist exactly when the strands of `s`
left of `p` fit in the first block (`PrefixInFirstBlock`): `cutLeadingQuad`, `windowLeadingQuad`,
and conversely `prefixInFirstBlock_of_cutQuad`, `prefixInFirstBlock_of_windowQuad`.

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `KLR.KLRAlgebra.MackeyQuad.ofLe`, `Stendhal.CupCap.PrefixInFirstBlock`,
  `Stendhal.CupCap.cutLeadingQuad`, `Stendhal.CupCap.windowLeadingQuad`.

## Main results

* `Stendhal.CupCap.prefixInFirstBlock_of_cutQuad`,
  `Stendhal.CupCap.prefixInFirstBlock_of_windowQuad`.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra.MackeyQuad

variable {I : Type*} [DecidableEq I] {ν ν' ν'' ν''' : Multiset I}

/-- **A Mackey datum of a given weight** `β`: `α = ν - β`, `γ = ν'' - α`, `δ = ν''' - β`. -/
def ofLe (hsum : ν + ν' = ν'' + ν''') (β : Multiset I) (hβ : β ≤ ν) (hβ' : β ≤ ν''')
    (hα : ν - β ≤ ν'') : MackeyQuad ν ν' ν'' ν''' where
  α := ν - β
  β := β
  γ := ν'' - (ν - β)
  δ := ν''' - β
  h₁ := tsub_add_cancel_of_le hβ
  h₂ := by
    have h3 : ν - β + (ν'' - (ν - β)) = ν'' := add_tsub_cancel_of_le hα
    have h4 : β + (ν''' - β) = ν''' := add_tsub_cancel_of_le hβ'
    have h1 : ν - β + β = ν := tsub_add_cancel_of_le hβ
    have h : (ν - β + β) + ((ν'' - (ν - β)) + (ν''' - β)) =
        (ν - β + (ν'' - (ν - β))) + (β + (ν''' - β)) := add_add_add_comm _ _ _ _
    rw [h3, h4, h1, ← hsum] at h
    exact add_left_cancel h
  h₃ := add_tsub_cancel_of_le hα
  h₄ := add_tsub_cancel_of_le hβ'

@[simp] theorem ofLe_β (hsum : ν + ν' = ν'' + ν''') (β : Multiset I) (hβ : β ≤ ν)
    (hβ' : β ≤ ν''') (hα : ν - β ≤ ν'') : (ofLe hsum β hβ hβ' hα).β = β := rfl

omit [DecidableEq I] in
/-- The left part of a Mackey datum lies in the first top block. -/
theorem α_le (q : MackeyQuad ν ν' ν'' ν''') : q.α ≤ ν'' :=
  le_of_le_of_eq (Multiset.le_add_right _ _) q.h₃

end Categorification.KLR.KLRAlgebra.MackeyQuad

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {θ γ ν₀ : Multiset I}

variable (j hj θ) in
/-- **The strands left of the maximum fit in the first block**: the weight of the first
`midPos s` strands of `s` is at most that of the black strands `θ` and the red strands
`λ_1, …, λ_j` of the first block of the cut. -/
def PrefixInFirstBlock (s : Seq (stendhalWeight ℓ (θ + γ))) : Prop :=
  Seq.prefixWt s (midPos j s) (midPos_le j s) ≤
    (stendhalWeight j θ).map (Sum.map (id : I → I) (Fin.castLE hj))

theorem cutColour_comp_castLE :
    Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm) ∘
        Sum.map (id : I → I) (Fin.castLE hj) =
      Sum.map (id : I → I) (Fin.castAdd (ℓ - j)) := by
  funext x
  rcases x with b | u
  · rfl
  · exact congrArg Sum.inr (Fin.ext rfl)

theorem plusColour_comp_castLE :
    (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) ∘
        Sum.map (id : I → I) (Fin.castLE hj) =
      Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))) := by
  funext x
  rcases x with b | u
  · rfl
  · refine congrArg Sum.inr (Fin.ext ?_)
    simp [oldRed, u.2]

theorem cutColour_injective :
    Function.Injective (Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm)) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.cast_injective _⟩

theorem plusColour_injective :
    Function.Injective
      (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) :=
  (Sum.map_injective.2 ⟨Function.injective_id, Fin.cast_injective _⟩).comp
    (oldColour_injective j hj)

/-- The first block of the cut is the first block of `λ`, read in the cut labels. -/
theorem firstBlock_cut_eq_map :
    Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) =
      ((stendhalWeight j θ).map (Sum.map (id : I → I) (Fin.castLE hj))).map
        (Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm)) := by
  rw [Multiset.map_map, cutColour_comp_castLE]

/-- The first block of `λ⁺` is the first block of `λ`, read in `λ⁺`. -/
theorem firstBlock_plus_eq_map :
    Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) =
      ((stendhalWeight j θ).map (Sum.map (id : I → I) (Fin.castLE hj))).map
        (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) := by
  rw [Multiset.map_map, plusColour_comp_castLE]

/-- `PrefixInFirstBlock` is the condition read at the cut of `S_cut`. -/
theorem prefixInFirstBlock_iff_cut (s : Seq (stendhalWeight ℓ (θ + γ))) :
    PrefixInFirstBlock j hj θ s ↔
      Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s) ≤
        Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ) := by
  rw [prefixWt_cutLoading, firstBlock_cut_eq_map (hj := hj),
    Multiset.map_le_map_iff (cutColour_injective (hj := hj))]
  rfl

variable [DecidableEq I]

/-- The weight of the strands left of the window of the window loading, without the window. -/
theorem prefixWt_windowLoading_sub (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) :
    Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) -
        (stendhalWeight 2 ν₀).map (windowColour j hj) =
      (Seq.prefixWt s (midPos j s) (midPos_le j s)).map
          (Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj) := by
  rw [prefixWt_windowLoading]
  exact add_tsub_cancel_right _ _

variable (j hj θ γ) in
/-- **The leading datum at `S_cut`**: the Mackey datum of weight `0` at the cut `midPos s`. -/
def cutLeadingQuad (s : Seq (stendhalWeight ℓ (θ + γ))) (h : PrefixInFirstBlock j hj θ s) :
    {q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)) //
            Multiset.card q.β = 0} :=
  ⟨MackeyQuad.ofLe (Seq.prefixWt_add_suffixWt _ _ _) 0 (Multiset.zero_le _)
    (Multiset.zero_le _) ((tsub_zero _).trans_le ((prefixInFirstBlock_iff_cut s).1 h)),
    Multiset.card_zero⟩

theorem cutLeadingQuad_β (s : Seq (stendhalWeight ℓ (θ + γ)))
    (h : PrefixInFirstBlock j hj θ s) : (cutLeadingQuad j hj θ γ s h).1.β = 0 := rfl

variable (j hj θ γ ν₀) in
/-- **The leading datum at `S_+`**: the Mackey datum of the weight of the window at the cut
`midPos s + N`. -/
def windowLeadingQuad (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (h : PrefixInFirstBlock j hj θ s) :
    {q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))) //
            Multiset.card q.β = Multiset.card (stendhalWeight 2 ν₀)} :=
  ⟨MackeyQuad.ofLe (Seq.prefixWt_add_suffixWt _ _ _)
    ((stendhalWeight 2 ν₀).map (windowColour j hj))
    (by rw [prefixWt_windowLoading]; exact Multiset.le_add_left _ _)
    (by rw [plusTailWeight_eq j hj ν₀ γ]; exact Multiset.le_add_right _ _)
    (by
      rw [prefixWt_windowLoading_sub, firstBlock_plus_eq_map (hj := hj)]
      exact Multiset.map_le_map h),
    Multiset.card_map _ _⟩

theorem windowLeadingQuad_β (s : Seq (stendhalWeight ℓ (θ + γ))) (w : Seq (stendhalWeight 2 ν₀))
    (h : PrefixInFirstBlock j hj θ s) :
    (windowLeadingQuad j hj θ γ ν₀ s w h).1.β = (stendhalWeight 2 ν₀).map (windowColour j hj) :=
  rfl

omit [DecidableEq I] in
/-- A Mackey datum of weight `0` at the cut of `S_cut` forces `PrefixInFirstBlock`. -/
theorem prefixInFirstBlock_of_cutQuad (s : Seq (stendhalWeight ℓ (θ + γ)))
    (q : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
          (midPos_le_card_cut s))
          (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq : q.β = 0) : PrefixInFirstBlock j hj θ s := by
  refine (prefixInFirstBlock_iff_cut s).2 ?_
  have h1 := q.h₁
  rw [hq, add_zero] at h1
  exact h1 ▸ q.α_le

omit [DecidableEq I] in
/-- A Mackey datum of the weight of the window at the cut of `S_+` forces
`PrefixInFirstBlock`. -/
theorem prefixInFirstBlock_of_windowQuad (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
          (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj)) :
    PrefixInFirstBlock j hj θ s := by
  have h1 := q.h₁.trans (prefixWt_windowLoading s w)
  rw [hq, add_left_inj] at h1
  have h2 := q.α_le
  rw [h1, firstBlock_plus_eq_map (hj := hj)] at h2
  exact (Multiset.map_le_map_iff plusColour_injective).1 h2

end Categorification.Stendhal.CupCap

namespace Categorification.Stendhal

open KLR KLRAlgebra

/-- A supremum over the indices satisfying a predicate with no solution is `0`. -/
theorem eq_zero_of_mem_iSup_iSup_of_forall_not {R M ι : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {S : ι → Submodule R M} {P : ι → Prop} (hP : ∀ i, ¬ P i) {x : M}
    (hx : x ∈ ⨆ (i : ι) (_ : P i), S i) : x = 0 :=
  (Submodule.mem_bot R).1
    ((iSup_le fun i => iSup_le fun hi => absurd hi (hP i) : (⨆ (i : ι) (_ : P i), S i) ≤ ⊥) hx)

/-- The range of a map that vanishes everywhere is a subsingleton. -/
theorem subsingleton_range_of_forall_eq_zero {R M M' : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M'] [Module R M] [Module R M'] {f : M →ₗ[R] M'} (hf : ∀ x, f x = 0) :
    Subsingleton (LinearMap.range f) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  obtain ⟨_, x, rfl⟩ := a
  obtain ⟨_, y, rfl⟩ := b
  exact (hf x).trans (hf y).symm

/-- The image of a zero submodule is zero. -/
theorem subsingleton_map_of_subsingleton {R M M' : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M'] [Module R M] [Module R M'] {p : Submodule R M} (h : Subsingleton p)
    (f : M →ₗ[R] M') : Subsingleton (p.map f) := by
  rw [Submodule.eq_bot_of_subsingleton (p := p), Submodule.map_bot]
  infer_instance

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {θ γ ν₀ : Multiset I}

local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
local notation "Sp" => stendhalQ Q (plusBlockLabels Λ Λc j hj)

variable (X : Type) [AddCommGroup X] [Module k X]
  [Module (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X]
  [IsScalarTower k (PlusFactorAlgebra Q Λ Λc j hj θ ν₀ γ) X] (hQ : KLRSymm Q)
  (s : Seq (stendhalWeight ℓ (θ + γ)))

local notation "Bp" => BlocksMid Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ X) hQ

/-- **Without the leading datum the window corner vanishes** (Webster v3, Lemma 7.19, trace
half, step L5): if the strands of `s` left of the maximum do not fit in the first block, then
`ι_s(e(w))` kills the `N`-th layer of the induced model of `S_+`. -/
theorem indMackeyLayerAct_windowLoading_eq_zero (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hn : ¬ PrefixInFirstBlock j hj θ s)
    (y : IndMackeyLayer Sp
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)))
      (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp)
      (Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
      (Multiset.card (stendhalWeight 2 ν₀))) :
    indMackeyLayerAct (CutInput Q (plusBlockLabels Λ Λc j hj) θ (ν₀ + γ) Bp)
        (e (windowLoading j hj θ γ ν₀ s w))
        (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) (Multiset.card (stendhalWeight 2 ν₀)) y = 0 :=
  have hm := indMackeyLayerAct_windowLoading_mem_mackeyTopOne hQ hsp s w hs y
  eq_zero_of_mem_iSup_iSup_of_forall_not
    (fun q hq => hn (prefixInFirstBlock_of_windowQuad s w q.1 hq)) hm

/-- **Without the leading datum the window corner of a layer of `𝕊(S_+ X)` is zero.** -/
theorem subsingleton_range_windowLayerAct_e (hsp : KLRSymm Sp)
    (w : Seq (stendhalWeight 2 ν₀))
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hsr : IsRedOrdered s) (hwr : IsRedOrdered w) (hn : ¬ PrefixInFirstBlock j hj θ s) :
    Subsingleton (LinearMap.range (windowLayerAct j hj Q Λ Λc θ γ ν₀ X hQ s (e w)
      (Multiset.card (stendhalWeight 2 ν₀)))) := by
  have h1 := subsingleton_range_of_forall_eq_zero
    (indMackeyLayerAct_windowLoading_eq_zero X hQ s hsp w hs hn)
  have e1 := cutLoadingIndLayerEquiv (Λ := plusBlockLabels Λ Λc j hj) (N := Bp) hQ
    (windowLoading j hj θ γ ν₀ s w) (windowLoading_mem_cutOrderedLoadings hsr hwr)
    (Multiset.card (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s)))
    (Multiset.card (stendhalWeight 2 ν₀))
  have e2 := cutLayerCornerCast (Λ := plusBlockLabels Λ Λc j hj) (N := Bp) hQ
    (Seq.card_prefixWt (windowLoading j hj θ γ ν₀ s w)
      (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
    (windowLoading j hj θ γ ν₀ s w) (Multiset.card (stendhalWeight 2 ν₀))
  have e3 := LinearEquiv.ofEq _ _ (congrArg LinearMap.range
    (windowLayerAct_e (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (θ := θ) (γ := γ)
      (ν₀ := ν₀) X hQ s w (Multiset.card (stendhalWeight 2 ν₀))))
  exact (e3.trans (e2.symm.trans e1)).toEquiv.subsingleton

/-- **Without the leading datum the cut loading kills the layer `0`** of the induced model of
`S_cut(Res X)`. -/
theorem indMackeyLayerAct_cutLoading_eq_zero (hsc : KLRSymm Sc)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hn : ¬ PrefixInFirstBlock j hj θ s)
    (y : IndMackeyLayer Sc
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ))
      (CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X))
      (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))) 0) :
    indMackeyLayerAct (CutInput Q (cutLabels j hj Λ) θ γ (PlusRes j hj Q Λ Λc θ γ ν₀ X))
        (e (cutLoading j hj θ γ s)) (fun _ _ hy => e_mul_mem_mackeyFilt _ hy) 0 y = 0 :=
  have hm := indMackeyLayerAct_cutLoading_mem_mackeyTopOne (PlusRes j hj Q Λ Λc θ γ ν₀ X)
    hsc s hs y
  eq_zero_of_mem_iSup_iSup_of_forall_not
    (fun q hq => hn (prefixInFirstBlock_of_cutQuad s q.1 hq)) hm

/-- **Without the leading datum the cut corner `e_w · e(l)` is zero** on the layer `0` of
`S_cut(Res X)`, for every `u` of the middle block. -/
theorem subsingleton_range_cutWindowCorner (hsc : KLRSymm Sc)
    (hs : ∀ a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ))), a.val < midPos j s →
      ∀ u : Fin ℓ, s.lbl a = .inr u → u.val < j)
    (hsr : IsRedOrdered s) (hn : ¬ PrefixInFirstBlock j hj θ s)
    (u : TensorProductAlgebra k Q Λc ν₀) :
    Subsingleton (LinearMap.range (cutWindowCorner Λ Λc (Q := Q) (j := j) (hj := hj) (θ := θ)
      (γ := γ) (ν₀ := ν₀) X hQ s u)) := by
  have h1 := subsingleton_range_of_forall_eq_zero
    (indMackeyLayerAct_cutLoading_eq_zero (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (θ := θ)
      (γ := γ) (ν₀ := ν₀) X s hsc hs hn)
  have e1 := cutLoadingIndLayerEquiv (Λ := cutLabels j hj Λ)
    (N := PlusRes j hj Q Λ Λc θ γ ν₀ X) hQ
    (cutLoading j hj θ γ s) (cutLoading_mem_cutOrderedLoadings hsr)
    (Multiset.card (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
      (midPos_le_card_cut s))) 0
  have e2 := cutLayerCornerCast (Λ := cutLabels j hj Λ) (N := PlusRes j hj Q Λ Λc θ γ ν₀ X) hQ
    (Seq.card_prefixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
    (cutLoading j hj θ γ s) 0
  have h2 : Subsingleton (LinearMap.range (cutLayerAct (Λ := cutLabels j hj Λ) hQ
      (N := PlusRes j hj Q Λ Λc θ γ ν₀ X)
      (preservesMackeyFilt_e (Q := Sc) (n := midPos j s)
        (n'' := Multiset.card
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ)))
        (cutLoading j hj θ γ s)) 0)) :=
    (e2.symm.trans e1).toEquiv.subsingleton
  rw [range_cutWindowCorner]
  exact subsingleton_map_of_subsingleton h2 _

end CupCap

end Categorification.Stendhal
