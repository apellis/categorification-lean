/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyGraded

/-!
# The Mackey subquotients are spanned by the balanced tensor products

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18** (TeX lines 1784–1817). Let
`F_c = mackeyBimodFilt Q h c` be the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` by the number
`c = |λ|` of strands from the second bottom block to the first top block. This file proves that
the images of the bimodule maps
`mackeyMap h q : (_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (_{ν-λ,…} R_{ν''} ⊗ _{λ,…} R_{ν'''}) → F_c/F_{c-1}`,
over the quadruples `q` (the data `λ = β`) with `|λ| = c`, span `F_c / F_{c-1}`
(`KLRAlgebra.mackeyImage_eq_top`, over any commutative ring). Injectivity and independence of
these maps (hence `F_c / F_{c-1} ≅ ⊕_{|λ| = c} (…) ⊗_{R'} (…)`) are proved in
`Categorification.KLR.MackeyInj`.

## Auxiliary results

* `KLRAlgebra.seq_exists_split` : a sequence of weight `μ` splits as a concatenation of
  sequences of weights `μ₁ + μ₂ = μ` at any position.
* `KLRAlgebra.seq_weight_eq` : sequences with the same labels have the same weight.
* `KLRAlgebra.exists_quad_of_smul` : if `d` (the minimal double coset representative with `c`
  crossing strands) carries a bottom sequence `s₁ s₂` (`s₁ ∈ Seq ν''`, `s₂ ∈ Seq ν'''`) to a top
  sequence `ij` (`i ∈ Seq ν`, `j ∈ Seq ν'`), then `s₁ s₂ = (i_α i_γ)(i_β i_δ)` for a quadruple `q`
  with `|λ| = card β = c`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

/-! ### Splitting sequences -/

section Split

omit [DecidableEq I]

/-- Sequences with the same labels have the same weight. -/
theorem seq_weight_eq {μ μ' : Multiset I} (x : Seq μ) (y : Seq μ')
    (hc : Multiset.card μ = Multiset.card μ') (hxy : ∀ t, x.1 t = y.1 (Fin.cast hc t)) :
    μ = μ' := by
  calc μ = Multiset.map x.1 Finset.univ.val := x.2.symm
    _ = Multiset.map (y.1 ∘ Fin.cast hc) Finset.univ.val := by congr 1; funext t; exact hxy t
    _ = (Multiset.map (Fin.cast hc) Finset.univ.val).map y.1 := by rw [Multiset.map_map]
    _ = Multiset.map y.1 Finset.univ.val := by
      rw [show Multiset.map (Fin.cast hc) Finset.univ.val = Finset.univ.val from
        Multiset.map_univ_val_equiv (finCongr hc)]
    _ = μ' := y.2

/-- **Splitting a sequence**: a sequence of weight `μ` is the concatenation of its first `p`
labels and the remaining ones. -/
theorem seq_exists_split {μ : Multiset I} (s : Seq μ) (p : ℕ) (hp : p ≤ Multiset.card μ) :
    ∃ (μ₁ μ₂ : Multiset I) (hμ : μ₁ + μ₂ = μ) (x : Seq μ₁) (y : Seq μ₂),
      Multiset.card μ₁ = p ∧ seqCast hμ (x.append y) = s := by
  have e : p + (Multiset.card μ - p) = Multiset.card μ := by omega
  set f₁ : Fin p → I := fun a => s.1 (blockEquiv e (Sum.inl a))
  set f₂ : Fin (Multiset.card μ - p) → I := fun b => s.1 (blockEquiv e (Sum.inr b))
  set μ₁ := Multiset.map f₁ Finset.univ.val
  set μ₂ := Multiset.map f₂ Finset.univ.val
  have hc₁ : Multiset.card μ₁ = p := by simp [μ₁]
  have hc₂ : Multiset.card μ₂ = Multiset.card μ - p := by simp [μ₂]
  have hμ : μ₁ + μ₂ = μ := by
    calc μ₁ + μ₂ = Multiset.map (s.1 ∘ blockEquiv e) Finset.univ.val := by
          rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
            Multiset.map_add, Multiset.map_map, Multiset.map_map]
          rfl
      _ = (Multiset.map (blockEquiv e) Finset.univ.val).map s.1 := by rw [Multiset.map_map]
      _ = Multiset.map s.1 Finset.univ.val := by rw [Multiset.map_univ_val_equiv]
      _ = μ := s.2
  let x : Seq μ₁ := ⟨fun t => f₁ (Fin.cast hc₁ t), by
    show Multiset.map (f₁ ∘ Fin.cast hc₁) Finset.univ.val = μ₁
    rw [← Multiset.map_map, show Multiset.map (Fin.cast hc₁) Finset.univ.val = Finset.univ.val
      from Multiset.map_univ_val_equiv (finCongr hc₁)]⟩
  let y : Seq μ₂ := ⟨fun t => f₂ (Fin.cast hc₂ t), by
    show Multiset.map (f₂ ∘ Fin.cast hc₂) Finset.univ.val = μ₂
    rw [← Multiset.map_map, show Multiset.map (Fin.cast hc₂) Finset.univ.val = Finset.univ.val
      from Multiset.map_univ_val_equiv (finCongr hc₂)]⟩
  refine ⟨μ₁, μ₂, hμ, x, y, hc₁, ?_⟩
  apply Subtype.ext
  funext t
  by_cases ht : t.val < Multiset.card μ₁
  · rw [seqCast_append_apply_lt _ _ _ _ ht]
    exact s.apply_congr (by simp)
  · rw [seqCast_append_apply_ge _ _ _ _ (not_lt.1 ht)]
    exact s.apply_congr (by simp; omega)

end Split

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')

omit [DecidableEq I] in
/-- **Recovering `λ` from the sequences**: if the minimal double coset representative `d` with `c`
crossing strands carries the bottom sequence `s₁ s₂` to a top sequence `i j`, then
`s₁ = i_α i_γ`, `s₂ = i_β i_δ` for a quadruple `q = (α, β, γ, δ)` with `card β = c`. -/
theorem exists_quad_of_smul {d : Perm (Fin (Multiset.card (ν + ν')))}
    (hd : IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) d) (s₁ : Seq ν'') (s₂ : Seq ν''')
    (i : Seq ν) (j : Seq ν') (hs : d • seqCast h (s₁.append s₂) = i.append j) :
    ∃ (q : MackeyQuad ν ν' ν'' ν''') (i₁ : Seq q.α) (i₂ : Seq q.β) (i₃ : Seq q.γ) (i₄ : Seq q.δ),
      Multiset.card q.β = crossCount (Multiset.card ν) (Multiset.card ν'') d ∧
      seqCast q.h₃ (i₁.append i₃) = s₁ ∧ seqCast q.h₄ (i₂.append i₄) = s₂ := by
  set c := crossCount (Multiset.card ν) (Multiset.card ν'') d with hcdef
  have hm : Multiset.card (ν + ν') = Multiset.card ν + Multiset.card ν' := Multiset.card_add _ _
  have hm' := card_add_bot h
  have hc1 : c ≤ Multiset.card ν := crossCount_le d (by omega)
  have hc2 : Multiset.card ν ≤ c + Multiset.card ν'' := le_crossCount d (by omega) (by omega)
  have hc3 : c + Multiset.card ν'' ≤ Multiset.card (ν + ν') :=
    by have := crossCount_le_right (Multiset.card ν) (show Multiset.card ν'' ≤ _ by omega) d; omega
  set a := Multiset.card ν - c
  obtain ⟨α, γ, h₃, i₁, i₃, ha, rfl⟩ := seq_exists_split s₁ a (by omega)
  obtain ⟨β, δ, h₄, i₂, i₄, hb, rfl⟩ := seq_exists_split s₂ c (by omega)
  obtain ⟨α', β', h₁, i₁', i₂', ha', rfl⟩ := seq_exists_split i a (by omega)
  obtain ⟨γ', δ', h₂, i₃', i₄', hg', rfl⟩ :=
    seq_exists_split j (Multiset.card ν'' - a) (by omega)
  -- cardinalities
  have e3 : Multiset.card α + Multiset.card γ = Multiset.card ν'' := by
    rw [← h₃, Multiset.card_add]
  have e4 : Multiset.card β + Multiset.card δ = Multiset.card ν''' := by
    rw [← h₄, Multiset.card_add]
  have e1 : Multiset.card α' + Multiset.card β' = Multiset.card ν := by
    rw [← h₁, Multiset.card_add]
  have e2 : Multiset.card γ' + Multiset.card δ' = Multiset.card ν' := by
    rw [← h₂, Multiset.card_add]
  -- the labels: `top (d p) = bot p`
  have key : ∀ p, ((seqCast h₁ (i₁'.append i₂')).append (seqCast h₂ (i₃'.append i₄'))).1 (d p) =
      ((seqCast h₃ (i₁.append i₃)).append (seqCast h₄ (i₂.append i₄))).1
        (Fin.cast (congrArg Multiset.card h).symm p) := by
    intro p
    rw [← hs, Seq.smul_apply, Equiv.symm_apply_apply, seqCast_apply]
  have hv := fun p => hd.val_eq_ite _ _ p
  -- `α' = α`
  have hα : α' = α := by
    refine seq_weight_eq i₁' i₁ (by omega) fun x => ?_
    have hx := x.2
    have := key ⟨x.val, by omega⟩
    have hdp : d ⟨x.val, by omega⟩ = ⟨x.val, by omega⟩ := by
      ext; rw [hv, if_pos (by simp; omega)]
    rw [hdp, lbl4_1 _ _ _ _ _ _ _ (by simp), lbl4_1 _ _ _ _ _ _ _ (by simp; omega)] at this
    exact this.trans (i₁.apply_congr (by simp))
  have hβ : β' = β := by
    refine seq_weight_eq i₂' i₂ (by omega) fun x => ?_
    have hx := x.2
    have := key ⟨Multiset.card ν'' + x.val, by omega⟩
    have hdp : d ⟨Multiset.card ν'' + x.val, by omega⟩ = ⟨a + x.val, by omega⟩ := by
      ext; rw [hv, if_neg (by simp; omega), if_neg (by simp), if_pos (by simp; omega)]
      simp; omega
    rw [hdp, lbl4_2 _ _ _ _ _ _ _ (by simp; omega) (by simp; omega),
      lbl4_3 _ _ _ _ _ _ _ (by simp) (by simp; omega)] at this
    refine (i₂'.apply_congr (by simp; omega)).trans (this.trans (i₂.apply_congr ?_))
    simp
  have hγ : γ' = γ := by
    refine seq_weight_eq i₃' i₃ (by omega) fun x => ?_
    have hx := x.2
    have := key ⟨a + x.val, by omega⟩
    have hdp : d ⟨a + x.val, by omega⟩ = ⟨Multiset.card ν + x.val, by omega⟩ := by
      ext; rw [hv, if_neg (by simp; omega), if_pos (by simp; omega)]
      simp; omega
    rw [hdp, lbl4_3 _ _ _ _ _ _ _ (by simp) (by simp),
      lbl4_2 _ _ _ _ _ _ _ (by simp; omega) (by simp; omega)] at this
    refine (i₃'.apply_congr (by simp)).trans (this.trans (i₃.apply_congr ?_))
    simp; omega
  have hδ : δ' = δ := by
    refine seq_weight_eq i₄' i₄ (by omega) fun x => ?_
    have hx := x.2
    have := key ⟨Multiset.card ν'' + c + x.val, by omega⟩
    have hdp : d ⟨Multiset.card ν'' + c + x.val, by omega⟩ =
        ⟨Multiset.card ν'' + c + x.val, by omega⟩ := by
      ext; rw [hv, if_neg (by simp; omega), if_neg (by simp; omega), if_neg (by simp; omega)]
    rw [hdp, lbl4_4 _ _ _ _ _ _ _ (by simp; omega), lbl4_4 _ _ _ _ _ _ _ (by simp; omega)] at this
    refine (i₄'.apply_congr (by simp; omega)).trans (this.trans (i₄.apply_congr ?_))
    simp; omega
  subst hα hβ hγ hδ
  exact ⟨⟨α', β', γ', δ', h₁, h₂, h₃, h₄⟩, i₁, i₂, i₃, i₄, hb, rfl, rfl⟩

/-! ### Surjectivity -/

section Surj

theorem castAlg_oneConcat_mul_e {α γ μ : Multiset I} (h₃ : α + γ = μ) (i₁ : Seq α) (i₃ : Seq γ) :
    castAlg Q h₃ (oneConcat Q α γ) * e (seqCast h₃ (i₁.append i₃)) =
      e (seqCast h₃ (i₁.append i₃)) := by
  rw [oneConcat, castAlg_eSum, eSum_mul_e, if_pos (Finset.mem_image_of_mem _
    (append_mem_concatSet i₁ i₃))]

theorem quadBot_one_mul_e (q : MackeyQuad ν ν' ν'' ν''') (i₁ : Seq q.α) (i₂ : Seq q.β)
    (i₃ : Seq q.γ) (i₄ : Seq q.δ) :
    quadBot q 1 * ((e (seqCast q.h₃ (i₁.append i₃)) : KLRAlgebra k Q ν'') ⊗ₜ
      (e (seqCast q.h₄ (i₂.append i₄)) : KLRAlgebra k Q ν''')) =
      (e (seqCast q.h₃ (i₁.append i₃)) : KLRAlgebra k Q ν'') ⊗ₜ
        (e (seqCast q.h₄ (i₂.append i₄)) : KLRAlgebra k Q ν''') := by
  rw [quadBot_one, Algebra.TensorProduct.tmul_mul_tmul, castAlg_oneConcat_mul_e,
    castAlg_oneConcat_mul_e]

theorem sum_e_tmul_e : (∑ s₁ : Seq ν'', ∑ s₂ : Seq ν''',
    ((e s₁ : KLRAlgebra k Q ν'') ⊗ₜ (e s₂ : KLRAlgebra k Q ν''')) : TensorKLR Q ν'' ν''') = 1 := by
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, sum_e,
    Algebra.TensorProduct.one_def]

variable (Q) in
/-- The span of the images of the maps `mackeyMap h q` with `|λ| = card β = c`. -/
def mackeyImage (c : ℕ) : Submodule k (MackeySubquot Q h c) :=
  ⨆ (q : MackeyQuad ν ν' ν'' ν''') (hq : Multiset.card q.β = c), LinearMap.range (mackeyMap h q hq)

theorem mackeyMap_mem_image {c : ℕ} (q : MackeyQuad ν ν' ν'' ν''') (hq : Multiset.card q.β = c)
    (y : MackeyX Q q) : mackeyMap h q hq y ∈ mackeyImage Q h c :=
  Submodule.mem_iSup_of_mem q (Submodule.mem_iSup_of_mem hq (LinearMap.mem_range_self _ y))

variable (Q) in
/-- The elements `r ∈ F_c` whose class lies in `mackeyImage`. -/
def surjSub (c : ℕ) : Submodule k (KLRAlgebra k Q (ν + ν')) where
  carrier := {r | ∃ hr : r ∈ mackeyBimodFilt Q h c,
    subquotOf h r hr ∈ mackeyImage Q h c}
  add_mem' := by
    rintro r s ⟨hr, hr'⟩ ⟨hs, hs'⟩
    exact ⟨add_mem hr hs, by rw [subquotOf_add]; exact add_mem hr' hs'⟩
  zero_mem' := ⟨zero_mem _, by
    rw [show subquotOf h (0 : KLRAlgebra k Q (ν + ν')) (zero_mem _) = 0 from
      Submodule.Quotient.mk_zero _]
    exact zero_mem _⟩
  smul_mem' := by
    rintro a r ⟨hr, hr'⟩
    exact ⟨Submodule.smul_mem _ a hr, by rw [subquotOf_smul]; exact Submodule.smul_mem _ a hr'⟩

/-- **KL I, Proposition 2.18 (surjectivity)**: `F_c / F_{c-1}` is spanned by the images of the
balanced tensor products `(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (…)` with `|λ| = c`. -/
theorem mackeyImage_eq_top (c : ℕ) : mackeyImage Q h c = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨r, hr, rfl⟩ := subquotOf_surjective h x
  have hσ : ∀ w, IsReduced (Multiset.card (ν + ν')) (canWord _ w) ∧
      wordProd (Multiset.card (ν + ν')) (canWord _ w) = w :=
    fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩
  suffices hle : mackeyBimodFilt Q h c ≤ surjSub Q h c by
    obtain ⟨_, hr'⟩ := hle hr
    exact hr'
  have hgen : ∀ (d : Perm (Fin (Multiset.card (ν + ν')))) (t : TensorKLR Q ν ν')
      (t' : TensorKLR Q ν'' ν'''), IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) d →
      crossCount (Multiset.card ν) (Multiset.card ν'') d ≤ c →
      concat Q ν ν' t * ψw (canWord _ d) * botConcat Q h t' ∈ mackeyBimodFilt Q h c := by
    intro d t t' hd hdc
    rw [mackeyBimodFilt_eq_span_crossings h (canWord _) hσ c]
    exact Submodule.subset_span ⟨d, t, t', hd, hdc, rfl⟩
  rw [mackeyBimodFilt_eq_span_crossings h (canWord _) hσ c]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨d, t, t', hd, hdc, rfl⟩
  rcases lt_or_eq_of_le hdc with hlt | heq
  · -- lower terms vanish in the subquotient
    refine ⟨hgen d t t' hd hdc, ?_⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [(subquotOf_eq_zero_iff h _).2]
    · exact zero_mem _
    rw [mackeyLowerBimod_succ, mackeyBimodFilt_eq_span_crossings h (canWord _) hσ c']
    exact Submodule.subset_span ⟨d, t, t', hd, by omega, rfl⟩
  · -- decompose along the bottom idempotents
    have ht' : t' = ∑ s₁ : Seq ν'', ∑ s₂ : Seq ν''',
        ((e s₁ : KLRAlgebra k Q ν'') ⊗ₜ (e s₂ : KLRAlgebra k Q ν''')) * t' := by
      calc t' = 1 * t' := (one_mul _).symm
        _ = _ := by rw [← sum_e_tmul_e (Q := Q), Finset.sum_mul]; simp only [Finset.sum_mul]
    rw [ht', map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun s₁ _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun s₂ _ => ?_
    have hmem := hgen d t (((e s₁ : KLRAlgebra k Q ν'') ⊗ₜ (e s₂ : KLRAlgebra k Q ν''')) * t')
      hd hdc
    have hsplit : concat Q ν ν' t * ψw (canWord _ d) *
        botConcat Q h (((e s₁ : KLRAlgebra k Q ν'') ⊗ₜ (e s₂ : KLRAlgebra k Q ν''')) * t') =
        concat Q ν ν' t * (oneConcat Q ν ν' * e (d • seqCast h (s₁.append s₂))) *
          ψw (canWord _ d) * botConcat Q h t' := by
      rw [botConcat_mul, botConcat_apply, concat_e_tmul_e, castAlg_e, ← mul_assoc,
        mul_assoc _ (ψw _), ψw_mul_e, wordProd_canWord, ← mul_assoc, ← mul_assoc,
        concat_mul_oneConcat]
    by_cases hin : d • seqCast h (s₁.append s₂) ∈ concatSet ν ν'
    · obtain ⟨i, j, hij⟩ := mem_concatSet.1 hin
      obtain ⟨q, i₁, i₂, i₃, i₄, hq, hs₁, hs₂⟩ := exists_quad_of_smul h hd s₁ s₂ i j hij.symm
      have hqc : Multiset.card q.β = c := hq.trans heq
      have hdq : quadPerm h q = d :=
        (quadPerm_spec h q).1.eq_of_crossCount_eq _ _ hd ((quadPerm_spec h q).2.trans hq)
      subst hs₁ hs₂
      set x := ((e (seqCast q.h₃ (i₁.append i₃)) : KLRAlgebra k Q ν'') ⊗ₜ
        (e (seqCast q.h₄ (i₂.append i₄)) : KLRAlgebra k Q ν''')) * t'
      have hx : x ∈ quadBotSub Q q := by
        rw [mem_quadBotSub, ← mul_assoc, quadBot_one_mul_e]
      have ht : t * quadTop q 1 ∈ Graded.leftIdeal (quadTop (Q := Q) q 1) := by
        rw [Graded.mem_leftIdeal, mul_assoc, quadTop_mul_one]
      refine ⟨hmem, ?_⟩
      have := mackeyMap_mem_image h q hqc (BalancedTensor.tmul ⟨_, ht⟩ ⟨x, hx⟩)
      rw [mackeyMap_tmul] at this
      subst hdq
      have hrep : concat Q ν ν' (t * quadTop q 1) *
          ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) * botConcat Q h x =
          concat Q ν ν' t * ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) *
            botConcat Q h x := by
        rw [concat_mul, mul_assoc (concat Q ν ν' t), concat_quadTop_one_mul_ψD, ← mul_assoc,
          mul_assoc _ (botConcat Q h (quadBot q 1)), ← botConcat_mul, hx]
      rwa [subquotOf_congr h hrep _ hmem] at this
    · refine ⟨hmem, ?_⟩
      have h0 : concat Q ν ν' t * ψw (canWord _ d) *
          botConcat Q h (((e s₁ : KLRAlgebra k Q ν'') ⊗ₜ (e s₂ : KLRAlgebra k Q ν''')) * t') =
          0 := by
        rw [hsplit, oneConcat, eSum_mul_e, if_neg hin, mul_zero, zero_mul, zero_mul]
      rw [subquotOf_congr h h0 hmem (zero_mem _),
        show subquotOf h (0 : KLRAlgebra k Q (ν + ν')) (zero_mem _) = 0 from
          Submodule.Quotient.mk_zero _]
      exact zero_mem _

end Surj

end KLRAlgebra

end Categorification.KLR

end
