/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumQuotient
import Categorification.KLR.CyclotomicAction.VacuumEvalIdeal
import Categorification.KLR.CyclotomicAction.VacuumFactor
import Categorification.Diagrams.CLQ.SortDecomp

/-!
# Evaluation at `P_∅` between words

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Prop. 3.25 (the Morita step used in Cor. 3.27). For words `s`, `s'` at the region of `P_∅`,
evaluation of 2-morphisms on `P_∅`
`Hom(E_s 1_λ, E_{s'} 1_λ) → Hom(E_s P_∅, E_{s'} P_∅)` has kernel the ideal `I`
(`mem_vacIdeal_of_vacEvW_eq_zero`) and is surjective (`exists_vacEvQ_eq`).

The proof sorts each word (`CLQ.decR`): an identity is a combination of composites through
words `E_a F_b`; those with `b` nonempty factor through a downward strand next to the vacuum,
so lie in `I`; for upward words the statement is the identification of the image of `E_a` at
`P_∅` with the cyclotomic quotient (`mem_vacIdeal_of_eval_eq_zero_up`, `exists_eval_eq_up`),
together with the vanishing of morphisms between upward words of different colour content
(`CLQ.hom_eq_zero_of_sCnt_ne`, `vacUp_hom_eq_zero`).
-/

universe u v w u₁

namespace Categorification.KL3.Diagram.CLQ
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
variable {I : Type u} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y} {k : Type v} [CommRing k] {sc : CL.CLScalars C k}

/-- The signed number of strands of colour `i` in a signed sequence. -/
def sCnt (i : I) (w : List (Letter I)) : ℤ := (w.count (true, i) : ℤ) - w.count (false, i)

theorem sCnt_append (i : I) (a b : List (Letter I)) :
    sCnt i (a ++ b) = sCnt i a + sCnt i b := by
  simp only [sCnt, List.count_append]; push_cast; ring

theorem sCnt_dom_eq_cod (i : I) (g : Shape I) : sCnt i g.dom = sCnt i g.cod := by
  cases g with
  | dot l => rfl
  | cross ε a b =>
    simp only [Shape.dom, Shape.cod, sCnt, List.count_cons, List.count_nil]; push_cast; ring
  | cup l =>
    obtain ⟨b, j⟩ := l
    cases b <;> simp [Shape.dom, Shape.cod, sCnt, List.count_cons, Letter.dual]
  | cap l =>
    obtain ⟨b, j⟩ := l
    cases b <;> simp [Shape.dom, Shape.cod, sCnt, List.count_cons, Letter.dual]

theorem sCnt_of_sChain (i : I) : ∀ {s t : List (Letter I)} {A : List (LayerData I)},
    SChain s A t → sCnt i s = sCnt i t
  | s, t, [], h => h ▸ rfl
  | s, t, x :: A, h => by
    obtain ⟨rfl, h'⟩ := h
    rw [← sCnt_of_sChain i h', sCnt_append, sCnt_append, sCnt_append, sCnt_append,
      sCnt_dom_eq_cod]

/-- 2-morphisms preserve the signed number of strands of each colour. -/
theorem hom_eq_zero_of_sCnt_ne (μ : X) {s t : List (Letter I)} (i : I)
    (h : sCnt i s ≠ sCnt i t)
    (f : (pres RD k sc).obj (ob RD μ s) ⟶ (pres RD k sc).obj (ob RD μ t)) : f = 0 := by
  have hf := mem_span_dg RD k sc μ f
  have : {g | ∃ ls, SChain s ls t ∧ g = dg RD k sc μ s t ls} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun g ⟨ls, hls, _⟩ => h (sCnt_of_sChain i hls)
  rwa [this, Submodule.span_empty, Submodule.mem_bot] at hf

theorem sCnt_ups (i : I) (a : List I) : sCnt i (ups a) = a.count i := by
  induction a with
  | nil => rfl
  | cons j a ih =>
    simp only [ups, List.map_cons] at ih ⊢
    simp only [sCnt, List.count_cons] at ih ⊢
    by_cases hj : j = i
    · subst hj; simp at ih ⊢; omega
    · simp [hj] at ih ⊢; omega

end Categorification.KL3.Diagram.CLQ

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory CategoryTheory.Limits TwoRep KLRAlgebra
noncomputable section

section Generic
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  {μ : X} (V : weightSpace.{u, v, w} Q a RD Λ μ) (h0 : blockWeight RD Λ 0 = μ)
  (v₀ : V ⟨0, h0⟩) {ν : Multiset I}

/-- A morphism out of the word module of `t` over a cyclic vacuum is determined by its value on
the generator. -/
theorem wordCell_hom_ext (hv : ∀ x : V ⟨0, h0⟩, ∃ z : CycKLR k Q a 0, x = z • v₀)
    (hV : ∀ β : WeightBlocks RD Λ μ, β.1 ≠ 0 → IsZero (V β)) {t : Seq ν}
    {Z : ((cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).obj (wtop RD μ ν)).carrier}
    {f g : (RouqData.wordCell (cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg).toRouqData
      μ t).obj.obj (familyObj hQ hlead ha hΛ hdeg V) ⟶ Z}
    (h : (f (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t) =
      (g (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t)) : f = g := by
  funext δ
  by_cases hδ : δ.1 = ν
  · obtain rfl : δ = topBlk h0 := Subtype.ext hδ
    ext x
    obtain ⟨z, rfl⟩ := exists_eq_smul_vgen hQ hlead ha hΛ hdeg V h0 v₀ hv _ _
      (wValid_wordL μ t) _ (topBlk_eq h0 t) x
    exact ((f _).hom.map_smul z _).trans ((congrArg (z • ·) h).trans ((g _).hom.map_smul z _).symm)
  · exact (isZero_wcell_of_ne hQ hlead ha hΛ hdeg V hV _ _
      (wValid_wordL μ t) δ (by rw [← topBlk_eq h0 t]; exact hδ)).eq_of_src _ _

end Generic

section Universal
open QuantumGroup StringDiagrams Diagrams.BicatInterp KL3.Diagram KLR.Diagram.MatEnd
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- A vacuum entry is the corner of the comparison map cut out by the two idempotents. -/
theorem vacCoeff_eq_e_mul_vacSum_mul_e (ν : Multiset I) (φ : VacMat hQ RD Λ ν)
    (t s : KLR.Seq ν) :
    vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s =
      CycKLR.mk (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν (e t.rev) *
        vacSum.{u, v, w} hQ RD Λ hΛ ν φ *
          CycKLR.mk (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν (e s.rev) := by
  set E : KLR.Seq ν → CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν :=
    fun t => CycKLR.mk _ _ _ ν (e t.rev) with hE
  have hEE : ∀ t t' : KLR.Seq ν, E t * E t' = if t = t' then E t else 0 := fun t t' => by
    simp only [E, ← map_mul, e_mul_e, Seq.rev_inj]
    split_ifs <;> simp
  have hc : ∀ t' s', vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t' s' =
      E t' * vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t' s' * E s' := fun t' s' => by
    rw [← vacCoeff_eq_e_mul, ← vacCoeff_eq_mul_e]
  have hterm : ∀ t' s', E t * vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t' s' * E s =
      if t' = t then (if s' = s then vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s else 0) else 0 :=
    fun t' s' => by
    rw [hc, show E t * (E t' * vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t' s' * E s') * E s =
      E t * E t' * vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t' s' * (E s' * E s) by
        simp only [mul_assoc], hEE, hEE]
    by_cases h1 : t' = t
    · subst h1
      by_cases h2 : s' = s
      · subst h2
        simp only [ite_true]
        exact (hc _ _).symm
      · simp [h2]
    · simp [h1, Ne.symm h1]
  unfold vacSum
  simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [hE] at hterm
  simp only [hterm]
  simp

/-- **Upward surjectivity**: every morphism between the images of two upward words at `P_∅` is the
evaluation of a 2-morphism. -/
theorem exists_eval_eq_up {ν : Multiset I} (t s : KLR.Seq ν)
    (g : ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (vacUpHom₁ hQ RD Λ t)).obj.obj
        (univVacuum.{u, v, w} hQ RD Λ hΛ) ⟶
      ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map (vacUpHom₁ hQ RD Λ s)).obj.obj
        (univVacuum.{u, v, w} hQ RD Λ hΛ)) :
    ∃ ψ : vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s,
      ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂ ψ).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ) = g := by
  let iT := (univFamily (lam := lam) hQ RD Λ hΛ).upIso (vacWt RD Λ) t
    (RouqFamily.cond_word (vacWt RD Λ) t)
  let iS := (univFamily (lam := lam) hQ RD Λ hΛ).upIso (vacWt RD Λ) s
    (RouqFamily.cond_word (vacWt RD Λ) s)
  let W := familyObj hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
    (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
    (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ)
  let g' := iT.inv.hom.app W ≫ g.hom ≫ iS.hom.hom.app W
  have hv := univVac_cyclic.{u, v, w} (Q := Q) (lam := lam) RD Λ
  have hV : ∀ β : WeightBlocks RD Λ (blockWeight RD Λ 0), β.1 ≠ 0 →
      IsZero (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ β) :=
    fun β hβ => isZero_emptyBlockObj hβ
  let E : KLR.Seq ν → CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν :=
    fun t => CycKLR.mk _ _ _ ν (e t.rev)
  let y := wcoord hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
      (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
      (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ) rfl
      (univVacCoord RD Λ) s ((g' (topBlk rfl)).hom
        (wgen hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
          (univCycPoly_natDegree_pair RD Λ hΛ)
          (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) _ rfl (univVacGen RD Λ) t))
  obtain ⟨φ, hφ⟩ := vacRingHom_surjective.{u, v, w} hQ RD Λ hΛ ν (MulOpposite.op (E t * y))
  have hsum : vacSum.{u, v, w} hQ RD Λ hΛ ν φ = E t * y := by
    rw [vacRingHom_apply] at hφ
    exact MulOpposite.op_injective hφ
  have hEt : E t * E t = E t := by
    simp only [E, ← map_mul, e_mul_self]
  have hy : y = y * E s := wcoord_eq_mul_e _ _ _ _ _ _ rfl (univVacGen RD Λ) hv
    (univVacCoord_univVacGen RD Λ) s _
  have hyE : E t * y = y := by
    change _ = wcoord _ _ _ _ _ _ _ _ s ((g' (topBlk rfl)).hom _)
    conv_rhs => rw [← e_smul_wgen]
    erw [map_smul, map_smul, smul_eq_mul]
  have hcoef : vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s = E t * y := by
    rw [vacCoeff_eq_e_mul_vacSum_mul_e, hsum, ← mul_assoc, hEt, mul_assoc, ← hy]
  have key : (((univFamily hQ RD Λ hΛ).upActP (univScalars hQ RD)
      (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) ν
        φ t s).hom.app W) = g' := by
    refine wordCell_hom_ext _ _ _ _ _ _ rfl (univVacGen RD Λ) hv hV ?_
    have h1 := eq_wcoord_smul_wgen hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
      (univCycPoly_monic k lam) (univCycPoly_natDegree_pair RD Λ hΛ)
      (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) _ rfl (univVacGen RD Λ) hv
      (univVacCoord_univVacGen RD Λ) s
    refine (h1 _).trans (Eq.trans ?_ (h1 _).symm)
    change vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s • _ = y • _
    rw [hcoef, hyE]
  refine ⟨φ t s, ObjectProperty.hom_ext _ ?_⟩
  have eT : iT.hom.hom.app W ≫ iT.inv.hom.app W = 𝟙 _ :=
    congrArg (fun f => f.hom.app W) iT.hom_inv_id
  have eS : iS.hom.hom.app W ≫ iS.inv.hom.app W = 𝟙 _ :=
    congrArg (fun f => f.hom.app W) iS.hom_inv_id
  have key' : iT.inv.hom.app W ≫ (admissibleQuotientMap (RouqFamily.genImg
      (univFamily (lam := lam) hQ RD Λ hΛ) (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD))
      (univPres_rel hQ RD Λ hΛ) Signature.IsEven.odd_eq_false (RouqFamily.cond_word (vacWt RD Λ) t)
      (RouqFamily.cond_word (vacWt RD Λ) s) (φ t s)).hom.app W ≫ iS.hom.hom.app W = g' := key
  change (admissibleQuotientMap (RouqFamily.genImg
      (univFamily (lam := lam) hQ RD Λ hΛ) (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD))
      (univPres_rel hQ RD Λ hΛ) Signature.IsEven.odd_eq_false (RouqFamily.cond_word (vacWt RD Λ) t)
      (RouqFamily.cond_word (vacWt RD Λ) s) (φ t s)).hom.app W = g.hom
  have := congrArg (fun f => iT.hom.hom.app W ≫ f ≫ iS.inv.hom.app W) key'
  simp only [g', ← Category.assoc, eT, Category.id_comp] at this
  simp only [Category.assoc, eS, Category.comp_id] at this
  refine this.trans ?_
  exact (Category.assoc g.hom _ _).trans ((congrArg (g.hom ≫ ·) eS).trans (Category.comp_id _))

theorem vacCoeff_eq_zero_of_eval {ν : Multiset I} (φ : VacMat hQ RD Λ ν) (t s : KLR.Seq ν)
    (h : ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from φ t s)).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ) = 0) :
    vacCoeff.{u, v, w} (lam := lam) hQ RD Λ hΛ ν φ t s = 0 := by
  have h1 : ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from φ t s)).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj = 0 := congrArg (fun f => f.hom) h
  unfold vacCoeff
  erw [comp_app_apply, comp_app_apply]
  have h2 : (admissibleQuotientMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ)
      (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
      Signature.IsEven.odd_eq_false (RouqFamily.cond_word (vacWt RD Λ) t)
      (RouqFamily.cond_word (vacWt RD Λ) s) (φ t s)).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj = 0 := h1
  erw [h2, zero_app_apply, map_zero, map_zero]

/-- **Upward kernel**: an upward 2-morphism at the region of `P_∅` acting by zero on `P_∅` lies
in `I`. -/
theorem mem_vacIdeal_of_eval_eq_zero_up {ν : Multiset I} (t s : KLR.Seq ν)
    (ψ : vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s)
    (h : ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂ ψ).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ) = 0) :
    ψ ∈ vacIdeal hQ RD Λ _ _ := by
  have hc : ∀ t' s', vacCoeff.{u, v, w} (lam := lam) hQ RD Λ hΛ ν (single t s ψ) t' s' = 0 := by
    intro t' s'
    by_cases hts : t' = t ∧ s' = s
    · obtain ⟨rfl, rfl⟩ := hts
      refine vacCoeff_eq_zero_of_eval hQ RD Λ hΛ _ _ _ ?_
      have e : single t' s' ψ t' s' = ψ := single_apply_self _ _ _
      exact (congrArg (fun g : vacUpHom₁ hQ RD Λ t' ⟶ vacUpHom₁ hQ RD Λ s' =>
        ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂ g).hom.app
          (univVacuum.{u, v, w} hQ RD Λ hΛ)) e).trans h
    · refine vacCoeff_eq_zero_of_mem_vacIdeal hQ RD Λ hΛ _ _ _ ?_
      have e : single t s ψ t' s' = 0 := single_apply_of_ne _ hts
      exact e ▸ zero_mem _
  have hr : vacRingHom.{u, v, w} hQ RD Λ hΛ ν (single t s ψ) = 0 := by
    rw [vacRingHom_apply]
    change MulOpposite.op (vacSum.{u, v, w} hQ RD Λ hΛ ν _) = 0
    rw [show vacSum.{u, v, w} hQ RD Λ hΛ ν (single t s ψ) = 0 from
      Finset.sum_eq_zero fun t' _ => Finset.sum_eq_zero fun s' _ => hc t' s']
    rfl
  have hm := ((mem_vacMatIdeal hQ RD Λ _).1 ((vacRingHom_eq_zero_iff hQ RD Λ hΛ _).1 hr)) t s
  have e : single t s ψ t s = ψ := single_apply_self _ _ _
  exact e ▸ hm

end Universal
end
end Categorification.KLR.CyclotomicAction

namespace Categorification.KLR.CyclotomicAction
open CategoryTheory CategoryTheory.Limits TwoRep KLRAlgebra
noncomputable section
open QuantumGroup StringDiagrams Diagrams.BicatInterp KL3.Diagram KLR.Diagram.MatEnd
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)
attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- Evaluation of a 2-morphism at the region of `P_∅` on `P_∅`. -/
abbrev vacEv {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g : vacRegion hQ RD Λ ⟶ c} (φ : f ⟶ g) :=
  ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map₂ φ).hom.app (univVacuum hQ RD Λ hΛ)

theorem vacEv_comp {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    {f g h : vacRegion hQ RD Λ ⟶ c} (φ : f ⟶ g) (ψ : g ⟶ h) :
    vacEv hQ RD Λ hΛ (φ ≫ ψ) = vacEv hQ RD Λ hΛ φ ≫ vacEv hQ RD Λ hΛ ψ := by
  simp only [vacEv, PrelaxFunctor.map₂_comp]; rfl

theorem vacEv_id {c : RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat}
    (f : vacRegion hQ RD Λ ⟶ c) : vacEv hQ RD Λ hΛ (𝟙 f) = 𝟙 _ := by
  simp only [vacEv, PrelaxFunctor.map₂_id]; rfl

omit [DecidableEq I] in
theorem exists_word_eq {ν : Multiset I} (a : List I) (h : (a : Multiset I) = ν) :
    ∃ t : KLR.Seq ν, KLR.Diagram.word t = a := by
  subst h
  refine ⟨⟨fun i => a.get (Fin.cast (by simp) i), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (by simp) a.get, List.ofFn_get]⟩, ?_⟩
  show List.ofFn (fun i => a.get (Fin.cast _ i)) = a
  rw [List.ofFn_congr (by simp : Multiset.card (a : Multiset I) = a.length)]
  simp

/-- Upward words with the same multiset of colours: kernel and surjectivity. -/
theorem up_eval {z z' : List (Letter I)} {a a' : List I} (ha : z = ups a) (ha' : z' = ups a')
    (h : (a : Multiset I) = a') {c : X} (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c)
    (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c) :
    (∀ m : vacHom (k := k) hQ RD Λ z hz ⟶ vacHom hQ RD Λ z' hz',
      vacEv hQ RD Λ hΛ m = 0 → m ∈ vacIdeal hQ RD Λ _ _) ∧
    (∀ g, ∃ m : vacHom (k := k) hQ RD Λ z hz ⟶ vacHom hQ RD Λ z' hz',
      vacEv hQ RD Λ hΛ m = g) := by
  subst ha ha'
  generalize hν : (a : Multiset I) = ν at h
  obtain ⟨t, rfl⟩ : ∃ t : KLR.Seq ν, KLR.Diagram.word t = a := exists_word_eq a hν
  obtain ⟨s, rfl⟩ : ∃ s : KLR.Seq ν, KLR.Diagram.word s = a' := exists_word_eq a' h.symm
  obtain rfl : c = _ := hz.symm.trans (RouqFamily.cond_word (vacWt RD Λ) t).2.2
  exact ⟨fun m hm => mem_vacIdeal_of_eval_eq_zero_up hQ RD Λ hΛ t s m hm,
    fun g => exists_eval_eq_up hQ RD Λ hΛ t s g⟩

/-- The image of an upward word at `P_∅` is supported on the block of its colours. -/
theorem isZero_vacUp_block {z : List (Letter I)} {a : List I} (ha : z = ups a) {c : X}
    (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c) (δ : WeightBlocks RD Λ c)
    (hδ : δ.1 ≠ (a : Multiset I)) :
    IsZero ((((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map
      (vacHom (k := k) hQ RD Λ z hz)).obj.obj (univVacuum.{u, v, w} hQ RD Λ hΛ)).obj δ) := by
  subst ha
  generalize hν : (a : Multiset I) = ν at hδ
  obtain ⟨t, rfl⟩ : ∃ t : KLR.Seq ν, KLR.Diagram.word t = a := exists_word_eq a hν
  obtain rfl : c = _ := hz.symm.trans (RouqFamily.cond_word (vacWt RD Λ) t).2.2
  let iT := (univFamily (lam := lam) hQ RD Λ hΛ).upIso (vacWt RD Λ) t
    (RouqFamily.cond_word (vacWt RD Λ) t)
  let W := familyObj hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
    (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
    (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ)
  have hV : ∀ β : WeightBlocks RD Λ (blockWeight RD Λ 0), β.1 ≠ 0 →
      IsZero (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ β) :=
    fun β hβ => isZero_emptyBlockObj hβ
  have hZ := isZero_wcell_of_ne hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading (univCycPoly_monic k lam)
    (univCycPoly_natDegree_pair RD Λ hΛ) (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)
    (emptyBlockObj.{u, max u v, w} (cycQ k lam Q) (univCycPoly k lam) RD Λ) hV _ _
    (wValid_wordL (vacWt RD Λ) t) δ (by rw [← topBlk_eq rfl t]; exact hδ)
  let e : _ ≅ _ := ⟨iT.hom.hom.app W, iT.inv.hom.app W,
    congrArg (fun f => f.hom.app W) iT.hom_inv_id, congrArg (fun f => f.hom.app W) iT.inv_hom_id⟩
  exact hZ.of_iso (Pi.isoApp e δ)

/-- Between upward words with different colours, the images at `P_∅` have no morphisms. -/
theorem vacUp_hom_eq_zero {z z' : List (Letter I)} {a a' : List I} (ha : z = ups a)
    (ha' : z' = ups a') (h : (a : Multiset I) ≠ a') {c : X}
    (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c) (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c)
    (g : ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map
      (vacHom (k := k) hQ RD Λ z hz)).obj.obj (univVacuum.{u, v, w} hQ RD Λ hΛ) ⟶
      ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map
      (vacHom (k := k) hQ RD Λ z' hz')).obj.obj (univVacuum.{u, v, w} hQ RD Λ hΛ)) :
    g = 0 := by
  apply ObjectProperty.hom_ext
  funext δ
  by_cases hδ : δ.1 = a
  · exact (isZero_vacUp_block hQ RD Λ hΛ ha' hz' δ (hδ ▸ h)).eq_of_tgt _ _
  · exact (isZero_vacUp_block hQ RD Λ hΛ ha hz δ hδ).eq_of_src _ _

/-- **Upward words**: a 2-morphism between upward words at the region of `P_∅` acting by zero
on `P_∅` lies in `I`, and every morphism between their images at `P_∅` is an evaluation. -/
theorem up_eval' {z z' : List (Letter I)} {a a' : List I} (ha : z = ups a) (ha' : z' = ups a')
    {c : X} (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c)
    (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c) :
    (∀ m : vacHom (k := k) hQ RD Λ z hz ⟶ vacHom hQ RD Λ z' hz',
      vacEv hQ RD Λ hΛ m = 0 → m ∈ vacIdeal hQ RD Λ _ _) ∧
    (∀ g, ∃ m : vacHom (k := k) hQ RD Λ z hz ⟶ vacHom hQ RD Λ z' hz',
      vacEv hQ RD Λ hΛ m = g) := by
  by_cases h : (a : Multiset I) = a'
  · exact up_eval hQ RD Λ hΛ ha ha' h hz hz'
  refine ⟨fun m _ => ?_, fun g => ⟨0, ?_⟩⟩
  · obtain ⟨i, hi⟩ : ∃ i, a.count i ≠ a'.count i := by
      by_contra hc
      push Not at hc
      exact h (Multiset.ext.2 fun i => by simpa using hc i)
    have hm : (show (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z) ⟶
        (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z') from m) = 0 :=
      CLQ.hom_eq_zero_of_sCnt_ne (sc := univScalars hQ RD) (vacWt RD Λ) i
        (by rw [ha, ha', CLQ.sCnt_ups, CLQ.sCnt_ups]; exact_mod_cast hi) m
    change m ∈ _
    rw [show m = 0 from hm]
    exact zero_mem _
  · exact (vacUp_hom_eq_zero hQ RD Λ hΛ ha ha' h hz hz' _).trans
      (vacUp_hom_eq_zero hQ RD Λ hΛ ha ha' h hz hz' _).symm

/-- Evaluation at `P_∅` of a 2-morphism between words at the region of `P_∅`. -/
abbrev vacEvW {s s' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
    (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (x : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :=
  vacEv hQ RD Λ hΛ (f := vacHom (k := k) hQ RD Λ s hs) (g := vacHom hQ RD Λ s' hs') x

theorem vacEvW_comp {s s' s'' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (hs'' : KL3.Diagram.wt RD (vacWt RD Λ) s'' = c)
    (x : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'))
    (y : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s') ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'')) :
    vacEvW hQ RD Λ hΛ hs hs'' (x ≫ y) =
      vacEvW hQ RD Λ hΛ hs hs' x ≫ vacEvW hQ RD Λ hΛ hs' hs'' y :=
  vacEv_comp hQ RD Λ hΛ (f := vacHom (k := k) hQ RD Λ s hs) (g := vacHom hQ RD Λ s' hs')
    (h := vacHom hQ RD Λ s'' hs'') x y

theorem vacEvW_add {s s' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
    (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (x y : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    vacEvW hQ RD Λ hΛ hs hs' (x + y) = vacEvW hQ RD Λ hΛ hs hs' x + vacEvW hQ RD Λ hΛ hs hs' y :=
  univPmod_map₂_add hQ RD Λ hΛ (f := vacHom (k := k) hQ RD Λ s hs) (g := vacHom hQ RD Λ s' hs')
    x y _

theorem vacEvW_smul {s s' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
    (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c) (r : k)
    (x : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    vacEvW hQ RD Λ hΛ hs hs' (r • x) = r • vacEvW hQ RD Λ hΛ hs hs' x :=
  univPmod_map₂_smul hQ RD Λ hΛ (f := vacHom (k := k) hQ RD Λ s hs)
    (g := vacHom hQ RD Λ s' hs') r x _

theorem vacEvW_zero {s s' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
    (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c) :
    vacEvW hQ RD Λ hΛ hs hs' 0 = 0 := by
  have := vacEvW_smul hQ RD Λ hΛ hs hs' 0 0
  rwa [zero_smul, zero_smul] at this

/-- A composite through a word whose strand next to the vacuum is downward lies in `I`. -/
theorem comp_mem_vacIdeal_of_dn {s s' z : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    {a b : List I} (hz : z = ups a ++ dns b) (hb : b ≠ [])
    (hw : KL3.Diagram.wt RD (vacWt RD Λ) z = KL3.Diagram.wt RD (vacWt RD Λ) s)
    (α : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z))
    (β : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    α ≫ β ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs') := by
  obtain ⟨b₀, j, rfl⟩ := (List.eq_nil_or_concat b).resolve_left hb
  obtain rfl : z = (ups a ++ dns b₀) ++ [dn j] := by simp [hz]
  exact mem_vacIdeal_of_mem_vacFactor hQ RD Λ hs hs'
    (Submodule.subset_span ⟨_, j, hw, α, β, rfl⟩)

/-- Upward words: the kernel of `vacEvW` lies in `I`. -/
theorem up_kernel_W {z z' : List (Letter I)} {a a' : List I} (ha : z = ups a)
    (ha' : z' = ups a') {c : X} (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c)
    (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c)
    (m : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z'))
    (h : vacEvW.{u, v, u₁, w} hQ RD Λ hΛ hz hz' m = 0) :
    m ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ z hz) (vacHom hQ RD Λ z' hz') :=
  (up_eval'.{u, v, u₁, w, w} hQ RD Λ hΛ ha ha' hz hz').1 m h

/-- A composite with a middle factor in `I` lies in `I`. -/
theorem comp_comp_mem_vacIdeal {s z z' s' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c)
    (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (α : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z))
    (m : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z'))
    (β : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z') ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'))
    (hm : m ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ z hz) (vacHom hQ RD Λ z' hz')) :
    α ≫ m ≫ β ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs') := by
  have := TwoRep.mem_factorIdeal_comp (TwoRep.comp_mem_factorIdeal
    (show vacHom (k := k) hQ RD Λ s hs ⟶ vacHom hQ RD Λ z hz from α) hm)
    (show vacHom (k := k) hQ RD Λ z' hz' ⟶ vacHom hQ RD Λ s' hs' from β)
  rw [← Category.assoc]
  exact this

/-- `comp_mem_vacIdeal_of_dn` with factors in `CLQ.pres`. -/
theorem comp_mem_vacIdeal_of_dn' {s s' z : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    {a b : List I} (hz : z = ups a ++ dns b) (hb : b ≠ [])
    (hw : KL3.Diagram.wt RD (vacWt RD Λ) z = KL3.Diagram.wt RD (vacWt RD Λ) s)
    (α : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z))
    (β : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) z) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    α ≫ β ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs') :=
  comp_mem_vacIdeal_of_dn hQ RD Λ hs hs' hz hb hw α β

/-- **The kernel of evaluation at `P_∅` is `I`** (Webster, arXiv:1309.3796v2, proof of
Prop. 3.25): a 2-morphism between words at the region of `P_∅` acting by zero on `P_∅` lies
in `I`. -/
theorem mem_vacIdeal_of_vacEvW_eq_zero {s s' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (φ : (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'))
    (h : vacEvW hQ RD Λ hΛ hs hs' φ = 0) :
    φ ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs') := by
  let φ' : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s') := φ
  have key : ∀ x ∈ CLQ.decRSet RD k (univScalars hQ RD) (vacWt RD Λ) s,
      ∀ y ∈ CLQ.decRSet RD k (univScalars hQ RD) (vacWt RD Λ) s',
        x ≫ φ' ≫ y ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs') := by
    intro x hx
    induction hx using Submodule.span_induction with
    | zero => intro y _; rw [Limits.zero_comp]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ =>
      intro y hy; rw [Preadditive.add_comp]; exact add_mem (h₁ y hy) (h₂ y hy)
    | smul r x _ hx => intro y hy; rw [Linear.smul_comp]; exact Submodule.smul_mem _ r (hx y hy)
    | mem x hx =>
      obtain ⟨a, b, P, Q, δ, -, hcP, -, hcQ, -, rfl⟩ := hx
      have hz : KL3.Diagram.wt RD (vacWt RD Λ) (ups a ++ dns b) = c :=
        (SChain.wt_eq RD (vacWt RD Λ) hcP).trans hs
      by_cases hb : b ≠ []
      · intro y _
        have := comp_mem_vacIdeal_of_dn' hQ RD Λ hs hs' rfl hb (SChain.wt_eq RD (vacWt RD Λ) hcP)
          (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s _ P)
          (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s Q ≫ φ' ≫ y)
        simpa only [Category.assoc] using this
      push Not at hb
      subst hb
      intro y hy
      induction hy using Submodule.span_induction with
      | zero => rw [Limits.comp_zero, Limits.comp_zero]; exact zero_mem _
      | add y₁ y₂ _ _ h₁ h₂ =>
        rw [Preadditive.comp_add, Preadditive.comp_add]; exact add_mem h₁ h₂
      | smul r y _ hy => rw [Linear.comp_smul, Linear.comp_smul]; exact Submodule.smul_mem _ r hy
      | mem y hy =>
        obtain ⟨a', b', P', Q', δ', -, hcP', -, hcQ', -, rfl⟩ := hy
        have hz' : KL3.Diagram.wt RD (vacWt RD Λ) (ups a' ++ dns b') = c :=
          (SChain.wt_eq RD (vacWt RD Λ) hcP').trans hs'
        by_cases hb' : b' ≠ []
        · have := comp_mem_vacIdeal_of_dn' hQ RD Λ hs hs' rfl hb'
            ((SChain.wt_eq RD (vacWt RD Λ) hcP').trans (hs'.trans hs.symm))
            ((CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ ≫
                CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s (ups a ++ dns []) P ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) (ups a ++ dns []) s Q) ≫ φ' ≫
              CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' _ P')
            (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s' Q')
          simpa only [Category.assoc] using this
        push Not at hb'
        subst hb'
        have e1 := vacEvW_comp hQ RD Λ hΛ hz hs hz' (CLQ.dg RD k (univScalars hQ RD)
            (vacWt RD Λ) _ s Q)
          (φ ≫ CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
            CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' _ P')
        have e2 := vacEvW_comp hQ RD Λ hΛ hs hs' hz' φ
          (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' _ P')
        erw [e2] at e1
        rw [h, Limits.zero_comp, Limits.comp_zero] at e1
        have hm := up_kernel_W hQ RD Λ hΛ (a := a) (a' := a') (by simp) (by simp) hz hz' _ e1
        have := comp_comp_mem_vacIdeal hQ RD Λ hs hz hz' hs'
          (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s _ P)
          (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s Q ≫ φ' ≫
            CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
            CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' _ P')
          (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s' Q') hm
        simpa only [Category.assoc] using this
  have h1 := CLQ.decR (RD := RD) (k := k) (sc := univScalars hQ RD) (vacWt RD Λ) _ s
      (Nat.lt_succ_self _)
  have h2 := CLQ.decR (RD := RD) (k := k) (sc := univScalars hQ RD) (vacWt RD Λ) _ s'
      (Nat.lt_succ_self _)
  have := key _ h1 _ h2
  rw [Category.id_comp, Category.comp_id] at this
  exact this

/-- The image at `P_∅` of a word at the region of `P_∅`. -/
abbrev vacWordObj {s : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) :=
  ((univCyclotomicPresCLPmod.{u, v, w} hQ RD Λ hΛ).map
    (vacHom (k := k) hQ RD Λ s hs)).obj.obj (univVacuum hQ RD Λ hΛ)

/-- `vacEvW` on morphisms of `CLQ.pres`. -/
abbrev vacEvQ {s s' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
    (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (x : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    vacWordObj.{u, v, w} hQ RD Λ hΛ hs ⟶ vacWordObj hQ RD Λ hΛ hs' :=
  vacEvW.{u, v, u₁, w} hQ RD Λ hΛ hs hs' x

section
variable {s s' s'' : List (Letter I)} {c : X} (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c)
  (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c) (hs'' : KL3.Diagram.wt RD (vacWt RD Λ) s'' = c)

theorem vacEvQ_comp
    (x : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'))
    (y : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s') ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s'')) :
    vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs'' (x ≫ y) =
      vacEvQ hQ RD Λ hΛ hs hs' x ≫ vacEvQ hQ RD Λ hΛ hs' hs'' y :=
  vacEvW_comp hQ RD Λ hΛ hs hs' hs'' x y

theorem vacEvQ_add
    (x y : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs' (x + y) =
      vacEvQ hQ RD Λ hΛ hs hs' x + vacEvQ hQ RD Λ hΛ hs hs' y :=
  vacEvW_add hQ RD Λ hΛ hs hs' x y

theorem vacEvQ_smul (r : k)
    (x : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')) :
    vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs' (r • x) = r • vacEvQ hQ RD Λ hΛ hs hs' x :=
  vacEvW_smul hQ RD Λ hΛ hs hs' r x

theorem vacEvQ_zero : vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs' 0 = 0 :=
  vacEvW_zero hQ RD Λ hΛ hs hs'

theorem vacEvQ_id : vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs (𝟙 _) = 𝟙 _ :=
  vacEv_id hQ RD Λ hΛ (vacHom hQ RD Λ s hs)

theorem vacEvQ_eq_zero
    {x : (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s) ⟶
      (CLQ.pres RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) s')}
    (hx : x ∈ vacIdeal hQ RD Λ (vacHom hQ RD Λ s hs) (vacHom hQ RD Λ s' hs')) :
    vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs' x = 0 :=
  univVacuum_map₂_eq_zero_of_mem_vacIdeal hQ RD Λ hΛ hx

end

/-- Upward words: every morphism of images at `P_∅` is an evaluation. -/
theorem up_surj_Q {z z' : List (Letter I)} {a a' : List I} (ha : z = ups a)
    (ha' : z' = ups a') {c : X} (hz : KL3.Diagram.wt RD (vacWt RD Λ) z = c)
    (hz' : KL3.Diagram.wt RD (vacWt RD Λ) z' = c)
    (g : vacWordObj.{u, v, w} hQ RD Λ hΛ hz ⟶ vacWordObj hQ RD Λ hΛ hz') :
    ∃ m, vacEvQ.{u, v, w} hQ RD Λ hΛ hz hz' m = g :=
  (up_eval'.{u, v, u₁, w, w} hQ RD Λ hΛ ha ha' hz hz').2 g

/-- **Evaluation at `P_∅` is surjective** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25):
every morphism between the images at `P_∅` of two words is the evaluation of a 2-morphism. -/
theorem exists_vacEvQ_eq {s s' : List (Letter I)} {c : X}
    (hs : KL3.Diagram.wt RD (vacWt RD Λ) s = c) (hs' : KL3.Diagram.wt RD (vacWt RD Λ) s' = c)
    (g : vacWordObj.{u, v, w} hQ RD Λ hΛ hs ⟶ vacWordObj hQ RD Λ hΛ hs') :
    ∃ φ, vacEvQ.{u, v, w} hQ RD Λ hΛ hs hs' φ = g := by
  have key : ∀ x ∈ CLQ.decRSet RD k (univScalars hQ RD) (vacWt RD Λ) s,
      ∀ y ∈ CLQ.decRSet RD k (univScalars hQ RD) (vacWt RD Λ) s', ∃ φ,
        vacEvQ hQ RD Λ hΛ hs hs' φ =
          vacEvQ hQ RD Λ hΛ hs hs x ≫ g ≫ vacEvQ hQ RD Λ hΛ hs' hs' y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | zero => intro y _; exact ⟨0, by rw [vacEvQ_zero, vacEvQ_zero, Limits.zero_comp]⟩
    | add x₁ x₂ _ _ h₁ h₂ =>
      intro y hy
      obtain ⟨φ₁, e₁⟩ := h₁ y hy
      obtain ⟨φ₂, e₂⟩ := h₂ y hy
      exact ⟨φ₁ + φ₂, by rw [vacEvQ_add, vacEvQ_add, e₁, e₂, Preadditive.add_comp]⟩
    | smul r x _ hx =>
      intro y hy
      obtain ⟨φ, e⟩ := hx y hy
      exact ⟨r • φ, by rw [vacEvQ_smul, vacEvQ_smul, e, Linear.smul_comp]⟩
    | mem x hx =>
      obtain ⟨a, b, P, Q, δ, -, hcP, -, hcQ, -, rfl⟩ := hx
      have hz : KL3.Diagram.wt RD (vacWt RD Λ) (ups a ++ dns b) = c :=
        (SChain.wt_eq RD _ hcP).trans hs
      by_cases hb : b ≠ []
      · intro y _
        refine ⟨0, ?_⟩
        have := comp_mem_vacIdeal_of_dn' hQ RD Λ hs hs rfl hb (SChain.wt_eq RD _ hcP)
          (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ ≫
            CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s _ P)
          (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s Q)
        rw [Category.assoc] at this
        rw [vacEvQ_zero, vacEvQ_eq_zero hQ RD Λ hΛ hs hs this, Limits.zero_comp]
      push Not at hb
      subst hb
      intro y hy
      induction hy using Submodule.span_induction with
      | zero => exact ⟨0, by rw [vacEvQ_zero, vacEvQ_zero, Limits.comp_zero, Limits.comp_zero]⟩
      | add y₁ y₂ _ _ h₁ h₂ =>
        obtain ⟨φ₁, e₁⟩ := h₁
        obtain ⟨φ₂, e₂⟩ := h₂
        exact ⟨φ₁ + φ₂, by
          rw [vacEvQ_add, vacEvQ_add, e₁, e₂, Preadditive.comp_add, Preadditive.comp_add]⟩
      | smul r y _ hy =>
        obtain ⟨φ, e⟩ := hy
        exact ⟨r • φ, by rw [vacEvQ_smul, vacEvQ_smul, e, Linear.comp_smul, Linear.comp_smul]⟩
      | mem y hy =>
        obtain ⟨a', b', P', Q', δ', -, hcP', -, hcQ', -, rfl⟩ := hy
        have hz' : KL3.Diagram.wt RD (vacWt RD Λ) (ups a' ++ dns b') = c :=
          (SChain.wt_eq RD _ hcP').trans hs'
        by_cases hb' : b' ≠ []
        · refine ⟨0, ?_⟩
          have := comp_mem_vacIdeal_of_dn' hQ RD Λ hs' hs' rfl hb' (SChain.wt_eq RD _ hcP')
            (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' _ P')
            (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s' Q')
          rw [Category.assoc] at this
          rw [vacEvQ_zero, vacEvQ_eq_zero hQ RD Λ hΛ hs' hs' this, Limits.comp_zero,
            Limits.comp_zero]
        push Not at hb'
        subst hb'
        obtain ⟨m, hm⟩ := up_surj_Q hQ RD Λ hΛ (a := a) (a' := a') (by simp) (by simp) hz hz'
          (vacEvQ hQ RD Λ hΛ hz hs (CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s Q) ≫ g ≫
            vacEvQ hQ RD Λ hΛ hs' hz' (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ' ≫
              CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s' (ups a' ++ dns []) P'))
        refine ⟨(CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ ≫
          CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) s (ups a ++ dns []) P) ≫ m ≫
          CLQ.dg RD k (univScalars hQ RD) (vacWt RD Λ) _ s' Q', ?_⟩
        rw [vacEvQ_comp hQ RD Λ hΛ hs hz hs', vacEvQ_comp hQ RD Λ hΛ hz hz' hs', hm,
          ← Category.assoc (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s δ),
          vacEvQ_comp hQ RD Λ hΛ hs hz hs,
          ← Category.assoc (CLQ.bubAt RD k (univScalars hQ RD) (vacWt RD Λ) s' δ'),
          vacEvQ_comp hQ RD Λ hΛ hs' hz' hs']
        simp only [Category.assoc]
  have h1 := CLQ.decR (RD := RD) (k := k) (sc := univScalars hQ RD) (vacWt RD Λ) _ s
    (Nat.lt_succ_self _)
  have h2 := CLQ.decR (RD := RD) (k := k) (sc := univScalars hQ RD) (vacWt RD Λ) _ s'
    (Nat.lt_succ_self _)
  obtain ⟨φ, e⟩ := key _ h1 _ h2
  refine ⟨φ, e.trans ?_⟩
  rw [vacEvQ_id, vacEvQ_id, Category.id_comp, Category.comp_id]

end
end Categorification.KLR.CyclotomicAction
