/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent
import Categorification.WeightedKLR.RedStrands.LastRedLayerTensor
import Categorification.WeightedKLR.RedStrands.LastRedShuffleSupport

/-!
# The last-red layer action on standardization

Webster, arXiv:1309.3796v2, §5, Theorem 5.8. Every shuffle preserves the
order of strands within each group. The final red strand starts its own
group, so no loading strictly beyond the initial cut survives.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "μ" => stendhalWeight (ℓ+1) (θ+β)
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)
local notation "N₀" => ParabolicInput Q Λ θ β N
local notation "ρ" => parabolicShuffleAction Q Λ θ β N
local notation "ρT" => parabolicStandardAction Q Λ θ β N hQ
local notation "V" => ParabolicStandard Q Λ θ β N
local notation "π" => TensorProductAlgebra.mk Q Λ (θ+β)
local notation "q" => StendhalAlgebraAllOrders.ofKLR k Q Λ (θ+β)

include hQ in
private theorem late_affine (s : Seq (α+δ)) (p : Fin (α+δ).card)
    (hp : s.lbl p = .inr (Fin.last ℓ)) (hr : (α).card < p.val) : ρ (e s) = 0 := by
  apply LinearMap.ext; intro z
  apply (indDecomp (ν := α) (ν' := δ) (stendhalQ_swap_symm Q Λ hQ) N₀).injective
  funext u
  change indDecomp _ N₀ ((e s : KLRAlgebra k S (α+δ)) • z) u = _
  rw [indDecomp_e_smul]
  have hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    by_contra hn
    have he := parabolicShuffle_last_red Q Λ θ β N s p hp u hn
    have he' := u.1.eq_symm_apply.mpr he
    have hu := lastRedShuffle_eq_one (Seq.card_add' α δ) u (by simp [stendhalWeight])
      (show (α).card ≤ (u.1.symm (Seq.posR α ⟨0,by simp [stendhalWeight]⟩)).val by
        rw [← he']; exact hr.le)
    rw [hu] at he
    have hv : p.val = (α).card := congrArg Fin.val he
    exact hr.ne hv.symm
  rw [hz]
  change 0 = indDecomp _ N₀ 0 u
  rw [map_zero]; rfl

private theorem proj_ordered (s : Seq μ) (hs : IsRedOrdered s) :
    orderProjection Q Λ (θ+β) (q (e s)) = StendhalAlgebra.e s hs :=
  Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs))

private theorem late_boundary (s : Seq μ) (hs : IsRedOrdered s) (p : Fin (μ).card)
    (hp : s.lbl p = .inr (Fin.last ℓ)) (hr : (α).card < p.val) :
    ρT (π (StendhalAlgebra.e s hs)) = 0 := by
  let s' := Seq.cast (Eq.symm H) s
  let p' := Fin.cast (congrArg Multiset.card H).symm p
  have his : Seq.cast H s' = s := by
    change Seq.cast H (Seq.cast (Eq.symm H) s) = _
    exact (show ∀ {a b : Multiset (I ⊕ Fin (ℓ+1))} (h : a=b) (x : Seq b), Seq.cast h (Seq.cast h.symm x) = x
      from fun h x => by subst h; rfl) H s
  rw [← proj_ordered Q Λ θ β s hs, ← his, ← castKLR_e, parabolicStandardAction_affine]
  apply orderedShuffleAction_eq_zero_of_eq_zero
  exact late_affine Q Λ θ β N hQ s' p' hp hr

/-- The standardization action factors through its specified last-red layer. -/
def parabolicStandardLayerAction (p : Fin (μ).card) (hp : p.val = (α).card) :
    (smallerSuffixIdeal Q Λ p).ringCon.Quotient →ₐ[k] Module.End k V := by
  apply (smallerSuffixIdeal Q Λ p).ringCon.liftₐ ρT
  apply (TwoSidedIdeal.ringCon_le_iff (J := TwoSidedIdeal.ker (ρT).toRingHom)).mp
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨s,hs,a,ha,hred,rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  exact late_boundary Q Λ θ β N hQ s hs a hred (by rw [← hp]; exact ha)

theorem parabolicStandardLayerAction_comp (p : Fin (μ).card) (hp : p.val = (α).card) :
    (parabolicStandardLayerAction Q Λ θ β N hQ p hp).comp
      ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k) = ρT := rfl


private theorem cast_trans_apply {J : Type*} [DecidableEq J] {Q' : J → J → MvPolynomial (Fin 2) k}
    {a b c : Multiset J} (h : a = b) (h' : b = c) (z : KLRAlgebra k Q' a) :
    castKLR Q' h' (castKLR Q' h z) = castKLR Q' (h.trans h') z := by
  subst c; subst b; rfl

omit [DecidableEq I] in
private theorem exists_final_red (s : Seq (α+δ)) :
    ∃ p, s.lbl p = .inr (Fin.last ℓ) := by
  have hmem : Sum.inr (Fin.last ℓ) ∈ α+δ := by
    rw [H]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)))
  rw [← s.2, Multiset.mem_map] at hmem
  obtain ⟨p,_,hp⟩ := hmem
  exact ⟨p,hp⟩

variable (θ' β' : Multiset I)
local notation "α'" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ')
local notation "δ'" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β')
variable (hTot : θ'+β'=θ+β) (hnot : ¬ θ' ≤ θ)
local notation "H'" => Eq.trans (parabolicInputWeights_add (ℓ := ℓ) θ' β') (congrArg (stendhalWeight (ℓ+1)) hTot)
local notation "HC" => Eq.trans H' (Eq.symm H)

include hQ hnot in
private theorem offcut_append_eq_zero (c : Seq α') (d : Seq δ') :
    ρ (e (Seq.cast HC (c.append d))) = 0 := by
  let s := Seq.cast HC (c.append d)
  obtain ⟨p,hp⟩ := exists_final_red θ β s
  apply LinearMap.ext; intro z
  apply (indDecomp (ν := α) (ν' := δ) (stendhalQ_swap_symm Q Λ hQ) N₀).injective
  funext u
  change indDecomp _ N₀ ((e s : KLRAlgebra k S (α+δ)) • z) u = _
  rw [indDecomp_e_smul]
  have hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    by_contra hn
    obtain ⟨a,b,hu,_,_,_,_⟩ := parabolicShuffle_supported_input Q Λ θ β N s u hn
    have hpos := parabolicShuffle_last_red Q Λ θ β N s p hp u hn
    apply hnot
    exact parabolicShuffle_cut_le HC a b c d u hu p hp hpos
  rw [hz]
  change 0 = indDecomp _ N₀ 0 u
  rw [map_zero]; rfl

include hnot in
/-- Every affine concatenation at a cut whose black prefix exceeds the
prefix of the inducing module vanishes on standardization. -/
theorem parabolicStandardAction_other_concat_eq_zero (t : TensorKLR S α' δ') :
    ρT (π (orderProjection Q Λ (θ+β) (q (castKLR S H' (concat S α' δ' t))))) = 0 := by
  let z := castKLR S HC (concat S α' δ' t)
  have htransfer : castKLR S H z = castKLR S H' (concat S α' δ' t) := by
    rw [show castKLR S H z = _ from cast_trans_apply HC H (concat S α' δ' t)]
  rw [← htransfer, parabolicStandardAction_affine]
  apply orderedShuffleAction_eq_zero_of_eq_zero
  have hgate : ρ (castKLR S HC (oneConcat S α' δ')) = 0 := by
    rw [oneConcat_eq (Q := S) (ν := α') (ν' := δ'), map_sum, map_sum]
    exact Finset.sum_eq_zero fun cd _ => by
      rw [castKLR_e]
      exact offcut_append_eq_zero Q Λ θ β N hQ θ' β' hTot hnot cd.1 cd.2
  change ρ (castKLR S HC (concat S α' δ' t)) = 0
  rw [← oneConcat_mul_concat t, map_mul, map_mul, hgate, zero_mul]

end Categorification.Stendhal
