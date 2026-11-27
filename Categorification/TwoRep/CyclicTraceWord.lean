/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclicTrace
import Categorification.TwoRep.WordAdjunction
import Categorification.TwoRep.RouqMixedCyc
import Categorification.TwoRep.RouqFullCL

/-!
# Cyclicity of the KLR action on words

For a Rouquier family `S` with its right adjunctions `E_i ⊣ F_i` and the left adjunctions
`F_i ⊣ E_i` constructed from the local Rouquier inverses (`RouqFamily.adjL`), the dots are
cyclic (Brundan, arXiv:1501.00350v1, Theorem 5.3, (5.6); `RouqFamily.dotDn_eq_rightMate`) and
so are the same-colour crossings (`RouqFamily.cyclic_cross`). A distinct-colour crossing
`ψ : E_j E_i ⟶ E_i E_j` is cyclic up to the scalar `t_ij / t_ji` (Brundan, (5.8);
`RouqFamily.mixed_cross_doubleMate`), so all crossings are cyclic when `t_ij = t_ji` for
`i ≠ j` (`crossCyclic_of_scalars`). This is the condition under which Webster's trace needs no
rescaling (Webster, arXiv:1309.3796v3, discussion after Theorem 3.18, and Remark 3.19).

For the biadjunctions of words (`RouqFamily.wadj`, `RouqFamily.wadjL`), every dot and crossing
on a word is then cyclic, and so is every entry of the matrix by which an element of the KLR
algebra acts on the words (`klrAct_isCyclic`). Consequently the closing trace on these
matrices is symmetric (`wordTrace₂_mul_comm`).

## Main declarations

* `RouqFamily.CrossCyclic`, `RouqFamily.crossCyclic_of_scalars`;
* `RouqFamily.WCyc`: cyclicity for the word biadjunctions;
* `RouqFamily.klrAct_isCyclic`;
* `RouqFamily.wordTrace₂`, `RouqFamily.wordTrace₂_mul_comm`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory QuantumGroup UDot KLR Diagram MatEnd

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily

variable (S : RouqFamily (B := B) RD)

/-- Every dot of a Rouquier family is cyclic. -/
theorem dot_isCyclic (i : I) {x y : X} (h : x + RD.iX i = y) :
    IsCyclic (S.adj i h) (S.adjL i h) (S.adj i h) (S.adjL i h) (S.dot i h) := by
  unfold IsCyclic
  rw [← S.dotDn_eq_rightMate, dotDn, Equiv.apply_symm_apply]

/-- All upward crossings of `S` are cyclic for the composite right and left adjunctions. -/
def CrossCyclic : Prop :=
  ∀ (i j : I) {a b c d : X} (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d),
    IsCyclic ((S.adj j h₁).comp (S.adj i h₂)) ((S.adjL i h₂).comp (S.adjL j h₁))
      ((S.adj i h₃).comp (S.adj j h₄)) ((S.adjL j h₄).comp (S.adjL i h₃))
      (S.cross i j h₁ h₂ h₃ h₄)

/-- Same-colour crossings are always cyclic. -/
theorem cross_self_isCyclic (i : I) {a b c d : X} (h₁ : a + RD.iX i = b)
    (h₂ : b + RD.iX i = d) (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX i = d) :
    IsCyclic ((S.adj i h₁).comp (S.adj i h₂)) ((S.adjL i h₂).comp (S.adjL i h₁))
      ((S.adj i h₃).comp (S.adj i h₄)) ((S.adjL i h₄).comp (S.adjL i h₃))
      (S.cross i i h₁ h₂ h₃ h₄) := by
  obtain rfl : c = b := h₃.symm.trans h₁
  exact S.cyclic_cross i h₁ h₂

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

/-- **Cyclicity of all crossings** when the mixed scalars satisfy `t_ij = t_ji` (Brundan,
arXiv:1501.00350v1, Theorem 5.3, (5.8)), for a Rouquier family with Brundan's mixed upward
relations and mixed inversion. -/
theorem crossCyclic_of_scalars (P : KL3.Diagram.CL.CLScalars C k) (H : BrundanUpKLR S P)
    (M : BrundanMixedInversion S) (ht : ∀ i j, i ≠ j → (P.t i j : k) = P.t j i) :
    S.CrossCyclic := by
  intro i j a b c d h₁ h₂ h₃ h₄
  by_cases hij : i = j
  · subst hij
    exact S.cross_self_isCyclic i h₁ h₂ h₃ h₄
  · have := M j i (Ne.symm hij) h₃ h₄ h₁ h₂
    have := M i j hij h₁ h₂ h₃ h₄
    have hm := S.mixed_cross_doubleMate P H j i (Ne.symm hij) h₁ h₂ h₃ h₄
    unfold IsCyclic
    rw [hm, ht i j hij, Units.mul_inv, one_smul]

/-! ### Words -/

variable (μ : X)

/-- Cyclicity of a 2-morphism between words, for the word biadjunctions. -/
def WCyc {L M : List (I × X)} {μ' : X} (h : wValid RD μ L μ') (hM : wValid RD μ M μ')
    (α : S.wcell μ L μ' h ⟶ S.wcell μ M μ' hM) : Prop :=
  IsCyclic (S.wadj μ L μ' h) (S.wadjL μ L μ' h) (S.wadj μ M μ' hM) (S.wadjL μ M μ' hM) α

variable {S μ}

theorem WCyc.comp {L M N : List (I × X)} {μ' : X} {h : wValid RD μ L μ'}
    {hM : wValid RD μ M μ'} {hN : wValid RD μ N μ'} {α : S.wcell μ L μ' h ⟶ S.wcell μ M μ' hM}
    {β : S.wcell μ M μ' hM ⟶ S.wcell μ N μ' hN} (hα : S.WCyc μ h hM α)
    (hβ : S.WCyc μ hM hN β) : S.WCyc μ h hN (α ≫ β) :=
  IsCyclic.comp hα hβ

theorem WCyc.eqToHom {L M : List (I × X)} {μ' : X} (e : L = M) (h : wValid RD μ L μ')
    (hM : wValid RD μ M μ') :
    S.WCyc μ h hM (eqToHom (S.wcell_congr μ e h hM)) := by
  subst e
  exact IsCyclic.id _ _

theorem WCyc.zero {L M : List (I × X)} {μ' : X} (h : wValid RD μ L μ')
    (hM : wValid RD μ M μ') : S.WCyc μ h hM 0 :=
  IsCyclic.zero

variable (S μ)

/-- Dots on words are cyclic. -/
theorem wdot_wcyc : ∀ (a : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    S.WCyc μ h h (S.wdot μ a L μ' h)
  | 0, (c, ν) :: L, _, h =>
    IsCyclic.whiskerLeft (S.wadj μ L ν h.1) (S.wadjL μ L ν h.1) (S.dot_isCyclic c h.2)
  | a + 1, (c, ν) :: L, _, h =>
    IsCyclic.whiskerRight (S.adj c h.2) (S.adjL c h.2) (wdot_wcyc a L ν h.1)
  | 0, [], _, h => WCyc.zero h h
  | _ + 1, [], _, h => WCyc.zero h h

/-- The crossing of the first two letters of a word is cyclic. -/
theorem wcross_zero_wcyc (hX : S.CrossCyclic) (c d : I) (ν₁ ν₂ : X) (L : List (I × X))
    (μ' : X) (h : wValid RD μ ((c, ν₁) :: (d, ν₂) :: L) μ') :
    S.WCyc μ h (wValid_wswap 0 _ h) (S.wcross μ 0 ((c, ν₁) :: (d, ν₂) :: L) μ' h) := by
  have e : ν₂ + RD.iX c + RD.iX d = μ' := by rw [← h.2, ← h.1.2, add_right_comm]
  have h₁ := IsCyclic.associator_hom (S.wadj μ L ν₂ h.1.1) (S.wadjL μ L ν₂ h.1.1)
    (S.adj d h.1.2) (S.adjL d h.1.2) (S.adj c h.2) (S.adjL c h.2)
  have h₂ := IsCyclic.whiskerLeft (S.wadj μ L ν₂ h.1.1) (S.wadjL μ L ν₂ h.1.1)
    (hX c d h.1.2 h.2 rfl e)
  have h₃ := IsCyclic.associator_inv (S.wadj μ L ν₂ h.1.1) (S.wadjL μ L ν₂ h.1.1)
    (S.adj c (rfl : ν₂ + RD.iX c = ν₂ + RD.iX c))
    (S.adjL c (rfl : ν₂ + RD.iX c = ν₂ + RD.iX c)) (S.adj d e) (S.adjL d e)
  exact h₁.comp (h₂.comp h₃)

/-- Crossings on words are cyclic when all crossings of `S` are. -/
theorem wcross_wcyc (hX : S.CrossCyclic) : ∀ (j : ℕ) (L : List (I × X)) (μ' : X)
    (h : wValid RD μ L μ'), S.WCyc μ h (wValid_wswap j L h) (S.wcross μ j L μ' h)
  | 0, (c, ν₁) :: (d, ν₂) :: L, μ', h => S.wcross_zero_wcyc μ hX c d ν₁ ν₂ L μ' h
  | j + 1, (c, ν) :: L, _, h =>
    IsCyclic.whiskerRight (S.adj c h.2) (S.adjL c h.2) (wcross_wcyc hX j L ν h.1)
  | 0, [], _, h => WCyc.zero h _
  | 0, [_], _, h => WCyc.zero h _
  | _ + 1, [], _, h => WCyc.zero h _

theorem wcrossTo_wcyc (hX : S.CrossCyclic) (j : ℕ) (L M : List (I × X)) (μ' : X)
    (e : wswap RD j L = M) (h : wValid RD μ L μ') (hM : wValid RD μ M μ') :
    S.WCyc μ h hM (S.wcrossTo μ j L M μ' e h hM) :=
  (S.wcross_wcyc μ hX j L μ' h).comp (WCyc.eqToHom e _ hM)

/-! ### The KLR action on words -/

variable [DecidableEq I] {ν : Multiset I}

/-- The matrices of 2-morphisms between the words of weight `ν` all of whose entries are
cyclic. -/
def cycSubalgebra : Subalgebra k (S.WordEnd μ ν) where
  carrier := {M | ∀ t s, S.WCyc μ (wValid_wordL μ t) (wValid_wordL μ s) (M t s)}
  mul_mem' {M N} hM hN t s := by
    rw [mul_apply]
    exact IsCyclic.sum _ fun u _ => (hN t u).comp (hM u s)
  add_mem' {M N} hM hN t s := (hM t s).add (hN t s)
  algebraMap_mem' r t s := by
    rw [Algebra.algebraMap_eq_smul_one, MatEnd.smul_apply]
    refine IsCyclic.smul ?_ r
    by_cases hts : t = s
    · subst hts
      rw [one_apply_self]
      exact IsCyclic.id _ _
    · rw [one_apply_of_ne hts]
      exact IsCyclic.zero

theorem single_mem_cycSubalgebra {t s : Seq ν} {f : S.wordCell μ t ⟶ S.wordCell μ s}
    (hf : S.WCyc μ (wValid_wordL μ t) (wValid_wordL μ s) f) :
    single t s f ∈ S.cycSubalgebra (k := k) μ (ν := ν) := by
  intro t' s'
  by_cases h : t' = t ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := h
    rw [single_apply_self]
    exact hf
  · rw [single_apply_of_ne _ h]
    exact IsCyclic.zero

theorem klrGen_mem_cycSubalgebra (hX : S.CrossCyclic) (g : KLR.Gen ν) :
    S.klrGen μ ν g ∈ S.cycSubalgebra (k := k) μ (ν := ν) := by
  cases g with
  | idem t => exact S.single_mem_cycSubalgebra μ (IsCyclic.id _ _)
  | dot a =>
    exact Subalgebra.sum_mem _ fun t _ =>
      S.single_mem_cycSubalgebra μ (S.wdot_wcyc μ a _ _ _)
  | cross j =>
    refine Subalgebra.sum_mem _ fun t _ => S.single_mem_cycSubalgebra μ ?_
    unfold RouqData.wordCross
    split_ifs with hj
    · exact S.wcrossTo_wcyc μ hX j _ _ _ _ _ _
    · exact IsCyclic.zero

theorem klrActFree_mem_cycSubalgebra (hX : S.CrossCyclic) (a : FreeAlgebra k (KLR.Gen ν)) :
    S.klrActFree k μ ν a ∈ S.cycSubalgebra (k := k) μ (ν := ν) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | grade1 g =>
    rw [RouqData.klrActFree, FreeAlgebra.lift_ι_apply]
    exact S.klrGen_mem_cycSubalgebra μ hX g
  | mul a b ha hb => rw [map_mul]; exact Subalgebra.mul_mem _ ha hb
  | add a b ha hb => rw [map_add]; exact Subalgebra.add_mem _ ha hb

/-- **Every entry of the action of the KLR algebra on words is cyclic**, when all crossings
of `S` are. -/
theorem klrAct_isCyclic {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (hX : S.CrossCyclic) (r : KLRAlgebra k Q ν) (t s : Seq ν) :
    S.WCyc μ (wValid_wordL μ t) (wValid_wordL μ s) (klrAct H μ r t s) := by
  obtain ⟨a, rfl⟩ := RingQuot.mkAlgHom_surjective k _ r
  have := S.klrActFree_mem_cycSubalgebra μ hX a
  change S.WCyc μ _ _ (klrAct H μ (KLRAlgebra.mk k Q ν a) t s)
  rw [klrAct_mk]
  exact this t s

theorem klrAct_mem_cycSubalgebra {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
    (hX : S.CrossCyclic) (r : KLRAlgebra k Q ν) :
    klrAct H μ r ∈ S.cycSubalgebra (k := k) μ (ν := ν) :=
  fun t s => S.klrAct_isCyclic μ H hX r t s

/-! ### The closing trace on words -/

/-- The closing trace on the matrix algebra of the words of weight `ν`, with values in the
endomorphisms of the identity 1-morphism at `μ`. -/
def wordTrace₂ (A : S.WordEnd μ ν) : 𝟙 (S.obj μ) ⟶ 𝟙 (S.obj μ) :=
  ∑ t, closeTrace (S.wadj μ _ _ (wValid_wordL μ t)) (S.wadjL μ _ _ (wValid_wordL μ t)) (A t t)

/-- **The closing trace is symmetric** on products with a matrix of cyclic entries. -/
theorem wordTrace₂_mul_comm {A : S.WordEnd μ ν} (hA : A ∈ S.cycSubalgebra (k := k) μ (ν := ν))
    (N : S.WordEnd μ ν) : S.wordTrace₂ μ (A * N) = S.wordTrace₂ μ (N * A) := by
  unfold wordTrace₂
  simp only [mul_apply]
  have hlin : ∀ (t : Seq ν) (f : Seq ν → (S.wordCell μ t ⟶ S.wordCell μ t)),
      closeTrace (S.wadj μ _ _ (wValid_wordL μ t)) (S.wadjL μ _ _ (wValid_wordL μ t))
        (∑ u, f u) = ∑ u, closeTrace (S.wadj μ _ _ (wValid_wordL μ t))
          (S.wadjL μ _ _ (wValid_wordL μ t)) (f u) := by
    intro t f
    unfold closeTrace
    have := map_sum (AdditiveWhiskering.whiskerRightAddHom _ _
      (S.wcellR μ _ _ (wValid_wordL μ t))) f Finset.univ
    simp only [AdditiveWhiskering.whiskerRightAddHom, AddMonoidHom.mk'_apply] at this
    rw [this, Preadditive.sum_comp, Preadditive.comp_sum]
  simp only [hlin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  exact (closeTrace_comp_comm (hA t u) (N u t)).symm

end RouqFamily

end Categorification.TwoRep
