/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedShuffleRepresentation
import Categorification.WeightedKLR.RedStrands.LastRedShuffleOrder
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients

/-!
# Support of the parabolically induced standardization module

Webster, arXiv:1309.3796v2, §5, Theorem 5.8. Induce from the preceding
tensor product algebra and the final cyclotomic factor, using the affine
KLR block inclusions of both red families.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "C" => CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β
/-- Tensor product of the two factor algebras at the cut. -/
abbrev parabolicFactorAlgebra := (L ⊗[k] C)
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "A" => KLRAlgebra k S (α+δ)
local notation "B" => TensorKLR S α δ

/-- The two quotient maps defining the input module for parabolic induction. -/
def parabolicInputMap : B →ₐ[k] D :=
  Algebra.TensorProduct.map (parabolicPrefixProjection Q Λ θ) (parabolicLastCyclotomic Q Λ β)

/-- A module of the factor algebras, restricted along the affine parabolic
quotient. -/
def ParabolicInput (N : Type*) [AddCommGroup N] [Module D N] := N

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
local notation "N₀" => ParabolicInput Q Λ θ β N
instance : AddCommGroup N₀ := inferInstanceAs (AddCommGroup N)
instance : Module k N₀ := inferInstanceAs (Module k N)
instance : Module D N₀ := inferInstanceAs (Module D N)
instance : IsScalarTower k D N₀ := inferInstanceAs (IsScalarTower k D N)
instance : Module B N₀ := Module.compHom N (parabolicInputMap Q Λ θ β).toRingHom
instance : IsScalarTower k B N₀ := ⟨fun c t n => by
  change (parabolicInputMap Q Λ θ β (c • t)) • (n : N) = c • ((parabolicInputMap Q Λ θ β t) • (n : N))
  rw [map_smul, smul_assoc]⟩

/-- The affine induced module before excluding unordered red loadings. -/
abbrev ParabolicShuffle := Ind S α δ N₀
local notation "M" => ParabolicShuffle Q Λ θ β N

/-- The affine action on the shuffle module. -/
abbrev parabolicShuffleAction : A →ₐ[k] Module.End k M := Algebra.lsmul k k M

omit [DecidableEq I] in
theorem stendhalQ_swap_symm (hQ : KLRSymm Q) : KLRSymm S := by
  rintro (i | r) (j | t) h
  · exact hQ i j (fun he => h (congrArg Sum.inl he))
  · simp [stendhalQ]
  · simp [stendhalQ]
  · simp [stendhalQ]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
private theorem concatIdem_annihilates (s : Seq (α+δ))
    (h : ∀ (a : Seq α) (b : Seq δ), s = a.append b →
      parabolicInputMap Q Λ θ β (e a ⊗ₜ[k] e b) = 0) (n : N₀) :
    concatIdem (Q := S) s • n = 0 := by
  classical
  by_cases hc : s ∈ concatSet α δ
  · obtain ⟨⟨a,b⟩,_,he⟩ := Finset.mem_image.mp hc
    change a.append b = s at he
    subst s
    change parabolicInputMap Q Λ θ β (concatIdem (a.append b)) • (n : N) = 0
    rw [concatIdem_append, h a b rfl]
    exact zero_smul D (n : N)
  · rw [concatIdem_of_not_mem hc, zero_smul]

private theorem parabolicInputMap_tmul (t : KLRAlgebra k S α) (r : KLRAlgebra k S δ) :
    parabolicInputMap Q Λ θ β (t ⊗ₜ[k] r) =
      parabolicPrefixProjection Q Λ θ t ⊗ₜ[k] parabolicLastCyclotomic Q Λ β r := by
  simp [parabolicInputMap]

/-- The affine induced module is zero at a violated loading. -/
theorem parabolicShuffle_violated (hQ : KLRSymm Q) (s : Seq (α+δ)) (hv : IsViolated s) :
    parabolicShuffleAction Q Λ θ β N (e s) = 0 := by
  apply LinearMap.ext; intro z
  apply (indDecomp (stendhalQ_swap_symm Q Λ hQ) N₀).injective
  funext u
  change indDecomp _ N₀ ((e s : A) • z) u = _
  rw [indDecomp_e_smul]
  have hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    apply concatIdem_annihilates
    intro a b hh
    rw [parabolicInputMap_tmul]
    by_cases ha : IsViolated a
    · rw [parabolicPrefixProjection_e_violated Q Λ θ a ha, zero_tmul]
    · have hb : IsViolated b := by
        by_contra hb
        exact shuffle_not_violated a b ha hb u hh hv
      change _ ⊗ₜ[k] ((SingleRed.cyclotomicEquiv Q _ β).symm (parabolicLastProjection Q Λ β (e b))) = _
      rw [parabolicLastProjection_e_violated Q Λ β b hb, map_zero, tmul_zero]
  rw [hz]
  change 0 = indDecomp _ N₀ 0 u
  rw [map_zero]; rfl


private theorem finalProjected_violated (s : Seq δ) (hv : IsViolated s) :
    parabolicLastCyclotomic Q Λ β (e s) = 0 := by
  simp only [parabolicLastCyclotomic, AlgHom.comp_apply, parabolicLastProjection_e_violated Q Λ β s hv, map_zero]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- A nonzero input coordinate comes from ordered, nonviolating loadings of both factors. -/
theorem parabolicShuffle_supported_input (s : Seq (α+δ)) (u : Shuffle (Seq.card_add' α δ))
    (hn : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) :
    ∃ a : Seq α, ∃ b : Seq δ, u.1 • s = a.append b ∧ IsRedOrdered a ∧
      IsRedOrdered b ∧ ¬ IsViolated a ∧ ¬ IsViolated b := by
  classical
  by_contra! h
  apply hn
  apply concatIdem_annihilates
  intro a b he
  rw [parabolicInputMap_tmul]
  by_cases ha : IsRedOrdered a
  · have hb := parabolicLast_ordered β b
    by_cases hva : IsViolated a
    · rw [parabolicPrefixProjection_e_violated Q Λ θ a hva, zero_tmul]
    · have hvb : IsViolated b := h a b he ha hb hva
      rw [finalProjected_violated Q Λ β b hvb, tmul_zero]
  · rw [parabolicPrefixProjection_e_unordered Q Λ θ a ha, zero_tmul]

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- At every crossing which returns to the prescribed order, the affine
shuffle action vanishes. -/
theorem parabolicShuffle_returns (hQ : KLRSymm Q) :
    VanishingReturnCrossings (parabolicShuffleAction Q Λ θ β N)
      (open Classical in Finset.univ.filter (fun s : Seq (α+δ) => IsRedOrdered s)) := by
  classical
  intro j s hs ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  by_cases hj : j+1 < (α+δ).card
  · obtain ⟨r,t,hr,ht',_⟩ := red_inversion_of_ordered_swap hj hs ht
    have hquad : (ψ j * ψ j * e (sadj (α+δ).card j • s) : A) = 0 := by
      rw [ψ_sq j hj]
      have h₁ : (sadj (α+δ).card j • s).lbl ⟨j,by omega⟩ = .inr t := by
        change s.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_left] using ht'
      have h₂ : (sadj (α+δ).card j • s).lbl ⟨j+1,hj⟩ = .inr r := by
        change s.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_right] using hr
      rw [h₁,h₂]
      split_ifs
      · rfl
      · change ncEval _ (0 : MvPolynomial (Fin 2) k) * _ = 0
        simp [ncEval]
    apply LinearMap.ext; intro z
    apply indShuffle_crossing_eq_zero (stendhalQ_swap_symm Q Λ hQ) N₀ s j hquad _ z
    intro u
    by_cases hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0
    · exact ⟨shufWord u, (shufWord_spec u).1, (shufWord_spec u).2, Or.inl hz⟩
    obtain ⟨a,b,he,ha,hb,_,_⟩ := parabolicShuffle_supported_input Q Λ θ β N s u hz
    have hbefore : ∀ x y r t, a.lbl x = .inr r → b.lbl y = .inr t → r < t := by
      intro x y r t h1 h2
      rw [parabolicLast_red_eq_last β b y h2]
      exact parabolicPrefix_red_lt_last θ a x h1
    obtain ⟨x,y,_,_,h₁,h₂,_,_⟩ := shuffle_returns_order hj ha hb hbefore u he hs ht
    have hd := (shuffle_right_descent (Seq.card_add' α δ) u hj h₁ h₂).2
    let v := canWord (α+δ).card (u.1 * sadj (α+δ).card j)
    have hw : wordProd (α+δ).card (v ++ [j]) = u.1 := by
      rw [wordProd_append, wordProd_singleton, show wordProd _ v = _ from wordProd_canWord _ _,
        mul_assoc, TypeA.sadj_mul_self, mul_one]
    refine ⟨v ++ [j], ⟨?_, ?_⟩, hw, Or.inr ⟨v,rfl⟩⟩
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact (isReduced_canWord _ _).1 p h
      · exact (List.mem_singleton.mp h).symm ▸ hj
    · simpa only [hw, v, List.length_append, List.length_singleton, length_canWord] using hd
  · rw [ψ_eq_zero j (by omega), zero_mul, map_zero]


private theorem concat_dot_left (a : Seq α) (b : Seq δ) (p : Fin (α).card) :
    concat S α δ ((x p * e a) ⊗ₜ[k] e b) = x (Seq.posL δ p) * e (a.append b) := by
  have h : ((x p * e a) ⊗ₜ[k] e b : B) = (x p ⊗ₜ[k] 1) * (e a ⊗ₜ[k] e b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_x_tmul_one, concat_e_tmul_e, mul_assoc,
    oneConcat_mul_e (append_mem_concatSet a b)]

private theorem concat_dot_right (a : Seq α) (b : Seq δ) (p : Fin (δ).card) :
    concat S α δ (e a ⊗ₜ[k] (x p * e b)) = x (Seq.posR α p) * e (a.append b) := by
  have h : (e a ⊗ₜ[k] (x p * e b) : B) = (1 ⊗ₜ[k] x p) * (e a ⊗ₜ[k] e b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_one_tmul_x, concat_e_tmul_e, mul_assoc,
    oneConcat_mul_e (append_mem_concatSet a b)]

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
private theorem dot_zero_unit (s : Seq (α+δ)) (p : Fin (α+δ).card) (hr : (s.lbl p).isRight) (n : N₀) :
    (x p * e s : A) • indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀ n = 0 := by
  classical
  by_cases hc : s ∈ concatSet α δ
  · obtain ⟨⟨a,b⟩,_,he⟩ := Finset.mem_image.mp hc
    change a.append b = s at he
    subst s
    obtain ⟨i,rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective p
    cases i with
    | inl i =>
      change (x (Seq.posL δ i) * e (a.append b) : A) • _ = _
      rw [← concat_dot_left Q Λ θ β a b i, concat_smul_indShuffleUnit]
      have hi : (a.lbl i).isRight := by
        change ((a.append b).1 (Seq.posL δ i)).isRight = true at hr
        rwa [Seq.append_posL] at hr
      have hzero : ((x i * e a) ⊗ₜ[k] e b : B) • n = 0 := by
        change (parabolicInputMap Q Λ θ β _) • (n : N) = 0
        rw [parabolicInputMap_tmul, parabolicPrefixProjection_red_dot Q Λ θ a i hi, zero_tmul]
        exact zero_smul D (n : N)
      rw [hzero, indShuffleUnit, BalancedTensor.tmul_zero]
    | inr i =>
      change (x (Seq.posR α i) * e (a.append b) : A) • _ = _
      rw [← concat_dot_right Q Λ θ β a b i, concat_smul_indShuffleUnit]
      have hi : (b.lbl i).isRight := by
        change ((a.append b).1 (Seq.posR α i)).isRight = true at hr
        rwa [Seq.append_posR] at hr
      have hzero : (e a ⊗ₜ[k] (x i * e b) : B) • n = 0 := by
        change (parabolicInputMap Q Λ θ β _) • (n : N) = 0
        rw [parabolicInputMap_tmul]
        have hg : parabolicLastCyclotomic Q Λ β (x i * e b) = 0 := by
          rw [parabolicLastCyclotomic, AlgHom.comp_apply, parabolicLastProjection_red_dot Q Λ β b i hi, map_zero]
        rw [hg, tmul_zero]
        exact zero_smul D (n : N)
      rw [hzero, indShuffleUnit, BalancedTensor.tmul_zero]
  · rw [mul_smul, idem_smul_indShuffleUnit, concatIdem_of_not_mem hc, zero_smul,
      indShuffleUnit, BalancedTensor.tmul_zero, smul_zero]

theorem parabolicShuffle_red_label_unique (s : Seq (α+δ)) {r : Fin (ℓ+1)} (a b)
    (ha : s.lbl a = .inr r) (hb : s.lbl b = .inr r) : a = b := by
  classical
  let F := Finset.univ.filter (fun c => Sum.inr r = s.lbl c)
  have hc : F.card = 1 := by
    change (Finset.univ.val.filter (fun c => Sum.inr r = s.lbl c)).card = 1
    rw [← Multiset.count_map, show Finset.univ.val.map s.lbl = α+δ from s.2, parabolicInputWeights_add,
      stendhalWeight, Multiset.count_add, Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective]
    simp
  exact Finset.card_le_one_iff.mp hc.le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.symm⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- All red dots annihilate the affine standardization module, before
taking its ordered quotient. -/
theorem parabolicShuffle_red_dot (hQ : KLRSymm Q) (s : Seq (α+δ)) (a : Fin (α+δ).card)
    (hr : (s.lbl a).isRight) : parabolicShuffleAction Q Λ θ β N (x a * e s) = 0 := by
  cases he : s.lbl a with
  | inl i => simp [he] at hr
  | inr r =>
    apply LinearMap.ext; intro z
    apply indShuffle_dot_eq_zero (stendhalQ_swap_symm Q Λ hQ) N₀ (Sum.inr r)
      (fun t b c => parabolicShuffle_red_label_unique θ β t b c) _ s a he z
    intro t b hb n
    exact dot_zero_unit Q Λ θ β N t b (by simp [hb]) n

end Categorification.Stendhal
