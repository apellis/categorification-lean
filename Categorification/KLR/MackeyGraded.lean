/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyMap

/-!
# The grading shift of the Mackey subquotients

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18** (TeX lines 1784–1817): the
subquotient of the Mackey filtration indexed by `λ` is the balanced tensor product
`(…) ⊗_{R'} (…)` **with the grading shift `{-λ·(ν'+λ-ν''')}`**, "the degree of the intersection
diagram of `|λ|` parallel lines colored by any `i ∈ Seq(λ)` and `|ν'+λ-ν'''|` parallel lines
colored by any `j ∈ Seq(ν'+λ-ν''')`".

For a grading datum `G` (`KLR.GradingDatum`, with crossing degrees `degΨ`) and a quadruple
`q = (α, β, γ, δ)` (`β = λ`, `γ = ν' + λ - ν'''`) put

`mackeyShift G q = ∑_{y ∈ γ} ∑_{x ∈ β} degΨ(y, x)`.

For KL I (`klGradingDatum`, `degΨ(y, x) = -y·x`) this is `-λ·(ν'+λ-ν''')`
(`KL1.mackeyShift_eq`).

## Main results

* `KLRAlgebra.ψD_mul_quadBot_one_mem_grade` : `ψ_d ι''(1_{α,γ} ⊗ 1_{β,δ})` is homogeneous of
  degree `mackeyShift G q`: the crossings of `d` are exactly the crossings of the `β`-strands
  with the `γ`-strands (`TypeA.IsDoubleShuffle.mem_invSet_iff`).
* `KLRAlgebra.mackeyRep_mem_grade` : for homogeneous `t ∈ MackeyTop` of degree `i` and
  `b ∈ MackeyBot` of degree `j`, the representative `ι(t) ψ_d ι''(b)` of `mackeyMap (t ⊗ b)` is
  homogeneous of degree `i + j + mackeyShift G q`.
* `KLRAlgebra.mackeyMap_mem_subquotGrading` : **`mackeyMap` is homogeneous of degree
  `mackeyShift G q`**: it maps the degree `d` part of the balanced tensor product
  (`MackeyX.grading`) into the degree `d + mackeyShift G q` part of `F_c / F_{c-1}`
  (`subquotGrading`), i.e. it is a degree-preserving map `MackeyX{mackeyShift} → F_c/F_{c-1}`
  in the convention `M{a}_d = M_{d-a}`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Graded
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν') (G : GradingDatum Q) (q : MackeyQuad ν ν' ν'' ν''')

local notation "ψD" =>
  (ψw (canWord (Multiset.card (ν + ν')) (quadPerm h q)) : KLRAlgebra k Q (ν + ν'))

/-- **The grading shift of KL I, Proposition 2.18**: the degree `∑_{y ∈ γ} ∑_{x ∈ β} degΨ(y, x)`
of the crossings of the `λ = β`-strands with the `γ = ν' + λ - ν'''`-strands. -/
def mackeyShift : ℤ := (q.γ.map fun y => (q.β.map fun x => G.degΨ y x).sum).sum

omit [DecidableEq I] in
theorem sum_seq_eq {μ : Multiset I} (s : Seq μ) (f : I → ℤ) :
    ∑ x, f (s.1 x) = (μ.map f).sum := by
  conv_rhs => rw [← s.2]
  rw [Multiset.map_map]; rfl

omit [DecidableEq I] in
/-- The crossings of `d`: the pairs (`γ`-strand, `β`-strand). -/
theorem invSet_quadPerm :
    invSet (Multiset.card (ν + ν')) (quadPerm h q) =
      Finset.image (fun xy : Fin (Multiset.card q.γ) × Fin (Multiset.card q.β) =>
        ((⟨Multiset.card q.α + xy.1.val, by
            have := xy.1.2; obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
            simp only [Multiset.card_add]; omega⟩ : Fin (Multiset.card (ν + ν'))),
          (⟨Multiset.card ν'' + xy.2.val, by
            have := xy.2.2; obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
            rw [← card_add_bot h, ← e4]; omega⟩ : Fin (Multiset.card (ν + ν'))))) Finset.univ := by
  obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
  obtain ⟨hd, hc⟩ := quadPerm_spec h q
  have hm := card_add_bot h
  ext ⟨p₁, p₂⟩
  rw [hd.mem_invSet_iff, quadPerm_val, quadPerm_val]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, Prod.exists]
  have h1 := p₁.2
  have h2 := p₂.2
  constructor
  · rintro ⟨q1, q2, q3, q4⟩
    refine ⟨⟨p₁.val - Multiset.card q.α, ?_⟩, ⟨p₂.val - Multiset.card ν'', ?_⟩, ?_, ?_⟩
    · split_ifs at q4 <;> omega
    · split_ifs at q3 <;> omega
    · ext; simp only; split_ifs at q4 <;> omega
    · ext; simp only; split_ifs at q3 <;> omega
  · rintro ⟨x, y, rfl, rfl⟩
    have := x.2
    have := y.2
    simp only
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega
    · rw [if_neg (by omega), if_pos (by omega)]; omega

/-- `ψ_d 1_s` for a bottom sequence `s = (i_α i_γ)(i_β i_δ)` has degree `mackeyShift G q`. -/
theorem ψD_mul_e_mem_grade (i₁ : Seq q.α) (i₂ : Seq q.β) (i₃ : Seq q.γ) (i₄ : Seq q.δ) :
    ψD * e (seqCast h ((seqCast q.h₃ (i₁.append i₃)).append (seqCast q.h₄ (i₂.append i₄)))) ∈
      G.grade (ν + ν') (mackeyShift G q) := by
  have hg := G.ψw_mul_pol_mul_e_mem_grade (canWord (Multiset.card (ν + ν')) (quadPerm h q))
    (seqCast h ((seqCast q.h₃ (i₁.append i₃)).append (seqCast q.h₄ (i₂.append i₄))))
    (p := 1) (D := 0) (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, G.degW_eq_sum_invSet (isReduced_canWord _ _),
    wordProd_canWord, invSet_quadPerm, Finset.sum_image] at hg
  · convert hg using 2
    rw [Fintype.sum_prod_type, mackeyShift, ← sum_seq_eq i₃]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← sum_seq_eq i₂]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨e1, e2, e3, e4⟩ := card_eqs q
    have := x.2
    have := y.2
    simp only [Seq.lbl]
    rw [seqCast_apply, seqCast_apply,
      lbl4_2 _ _ _ _ _ _ _ (by simp only [Fin.coe_cast]; omega) (by simp only [Fin.coe_cast]; omega),
      lbl4_3 _ _ _ _ _ _ _ (by simp only [Fin.coe_cast]; omega) (by simp only [Fin.coe_cast]; omega)]
    exact congrArg₂ G.degΨ (i₃.apply_congr (by simp)) (i₂.apply_congr (by simp))
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - hxy
    dsimp only at hxy
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

theorem botConcat_quadBot_e (i₁ : Seq q.α) (i₂ : Seq q.β) (i₃ : Seq q.γ) (i₄ : Seq q.δ) :
    botConcat Q h (quadBot q (((e i₁ : KLRAlgebra k Q q.α) ⊗ₜ (e i₂ : KLRAlgebra k Q q.β)) ⊗ₜ
      ((e i₃ : KLRAlgebra k Q q.γ) ⊗ₜ (e i₄ : KLRAlgebra k Q q.δ)))) =
      e (seqCast h ((seqCast q.h₃ (i₁.append i₃)).append (seqCast q.h₄ (i₂.append i₄)))) := by
  rw [quadBot_tmul, concat_e_tmul_e, concat_e_tmul_e, castAlg_e, castAlg_e, botConcat_apply,
    concat_e_tmul_e, castAlg_e]

/-- **The degree of the intersection diagram**: `ψ_d ι''(1_{α,γ} ⊗ 1_{β,δ})` is homogeneous of
degree `mackeyShift G q`. -/
theorem ψD_mul_quadBot_one_mem_grade :
    ψD * botConcat Q h (quadBot q 1) ∈ G.grade (ν + ν') (mackeyShift G q) := by
  have h1 : (1 : QuadAlg Q q) = (((1 : KLRAlgebra k Q q.α) ⊗ₜ (1 : KLRAlgebra k Q q.β)) ⊗ₜ
      ((1 : KLRAlgebra k Q q.γ) ⊗ₜ (1 : KLRAlgebra k Q q.δ)) : QuadAlg Q q) := by
    simp only [Algebra.TensorProduct.one_def]
  rw [h1, ← sum_e (ν := q.α), ← sum_e (ν := q.β), ← sum_e (ν := q.γ), ← sum_e (ν := q.δ)]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, Finset.mul_sum,
    botConcat_quadBot_e]
  exact Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ =>
    Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ => ψD_mul_e_mem_grade h G q _ _ _ _

theorem castAlg_mem_grade {μ₁ μ₂ : Multiset I} (h' : μ₁ = μ₂) {a : KLRAlgebra k Q μ₁} {d : ℤ}
    (ha : a ∈ G.grade μ₁ d) : castAlg Q h' a ∈ G.grade μ₂ d := by
  subst h'; exact ha

theorem botConcat_mem_grade {t : TensorKLR Q ν'' ν'''} {d : ℤ}
    (ht : t ∈ tensorGrading (G.grade ν'') (G.grade ν''') d) :
    botConcat Q h t ∈ G.grade (ν + ν') d :=
  castAlg_mem_grade G h (G.concat_mem_grade ht)

/-- **The representatives are homogeneous of the shifted degree**: for `t ∈ MackeyTop` of
degree `i` and `b ∈ MackeyBot` of degree `j`, `ι(t) ψ_d ι''(b)` has degree
`i + j + mackeyShift G q`. -/
theorem mackeyRep_mem_grade {t : TensorKLR Q ν ν'} {i j : ℤ}
    (ht : t ∈ tensorGrading (G.grade ν) (G.grade ν') i) (b : MackeyBot Q q)
    (hb : (b : TensorKLR Q ν'' ν''') ∈ tensorGrading (G.grade ν'') (G.grade ν''') j) :
    concat Q ν ν' t * ψD * botConcat Q h b ∈ G.grade (ν + ν') (i + j + mackeyShift G q) := by
  have hb' : botConcat Q h (b : TensorKLR Q ν'' ν''') =
      botConcat Q h (quadBot q 1) * botConcat Q h b := by
    rw [← botConcat_mul, b.2]
  rw [hb', ← mul_assoc, mul_assoc (concat Q ν ν' t),
    show i + j + mackeyShift G q = i + mackeyShift G q + j by ring]
  exact SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem (G.concat_mem_grade ht)
    (ψD_mul_quadBot_one_mem_grade h G q)) (botConcat_mem_grade h G hb)

/-! ### Gradings of the modules -/

variable (Q) in
/-- The grading of `MackeyTop` (the tensor product grading of `R(ν) ⊗ R(ν')`). -/
def MackeyTop.grading : ℤ → Submodule k (MackeyTop Q q) := fun d =>
  (tensorGrading (G.grade ν) (G.grade ν') d).comap
    ((Graded.leftIdeal (quadTop (Q := Q) q 1)).subtype.restrictScalars k)

variable (Q) in
/-- The grading of `MackeyBot` (the tensor product grading of `R(ν'') ⊗ R(ν''')`). -/
def MackeyBot.grading : ℤ → Submodule k (MackeyBot Q q) := fun d =>
  (tensorGrading (G.grade ν'') (G.grade ν''') d).comap (quadBotSub Q q).subtype

variable (Q) in
/-- The grading of the balanced tensor product `MackeyX Q q`. -/
def MackeyX.grading : ℤ → Submodule k (MackeyX Q q) :=
  balancedGrading (TensorKLR Q ν ν') (QuadAlg Q q) (MackeyTop.grading Q G q)
    (MackeyBot.grading Q G q)

variable (Q) in
/-- The grading of `F_c / F_{c-1}` induced by the grading of `R(ν + ν')`: the classes of the
homogeneous elements of `F_c`. -/
def subquotGrading (c : ℕ) : ℤ → Submodule k (MackeySubquot Q h c) := fun d =>
  (Submodule.comap (mackeyBimodFilt Q h c).subtype (G.grade (ν + ν') d)).map
    (Submodule.mkQ ((mackeyLowerBimod Q h c).comap (mackeyBimodFilt Q h c).subtype))

theorem subquotOf_mem_subquotGrading {c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyBimodFilt Q h c) {d : ℤ} (hd : r ∈ G.grade (ν + ν') d) :
    subquotOf h r hr ∈ subquotGrading Q h G c d :=
  ⟨⟨r, hr⟩, hd, rfl⟩

/-- **KL I, Proposition 2.18 (grading)**: `mackeyMap` is homogeneous of degree
`mackeyShift G q = -λ·(ν'+λ-ν''')`: it maps the degree `d` part of
`(_ν R_{ν-λ,λ} ⊗ _{ν'} R_{…}) ⊗_{R'} (…)` into the degree `d + mackeyShift G q` part of
`F_c / F_{c-1}`. -/
theorem mackeyMap_mem_subquotGrading {c : ℕ} (hc : Multiset.card q.β = c) {d : ℤ}
    {x : MackeyX Q q} (hx : x ∈ MackeyX.grading Q G q d) :
    mackeyMap h q hc x ∈ subquotGrading Q h G c (d + mackeyShift G q) :=
  balancedGrading_map_mem (fun d => subquotGrading Q h G c (d + mackeyShift G q))
    (mackeyMap h q hc) (fun _ _ t b ht hb => by
      rw [mackeyMap_tmul]
      exact subquotOf_mem_subquotGrading h G _ (mackeyRep_mem_grade h G q ht b hb)) hx

end KLRAlgebra

/-! ### The case of KL I -/

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj] {ν ν' ν'' ν''' : Multiset I}

/-- For KL I, `mackeyShift = -(ν' + λ - ν''')·λ` (`λ = β`, `ν' + λ - ν''' = γ`), with the
(symmetric) Cartan pairing `i·j = cartan Γ i j` extended bilinearly to `ℕ[I]`: this is the shift
`{-λ·(ν'+λ-ν''')}` of KL I, Proposition 2.18. -/
theorem mackeyShift_eq (q : KLRAlgebra.MackeyQuad ν ν' ν'' ν''') :
    KLRAlgebra.mackeyShift (klGradingDatum k Γ) q =
      -(q.γ.map fun y => (q.β.map fun x => cartan Γ y x).sum).sum := by
  simp only [KLRAlgebra.mackeyShift]
  rw [← Multiset.sum_map_neg]
  congr 1
  refine Multiset.map_congr rfl fun y _ => ?_
  rw [← Multiset.sum_map_neg]
  rfl

end KL1

end Categorification.KLR

end
