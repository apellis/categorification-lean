/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAction
import Categorification.WeightedKLR.RedStrands.RepresentationLift

/-!
# Partial standardization at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+r}}` (after Definition 5.4), for a module
`N` over `T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)`: the quotient of the affine induced module
by the part supported on loadings whose red strands are out of order. It is a module over the
tensor product algebra `T^λ(θ + β)` (`cutStandardAction`), and contains `N` as the image of
the identity shuffle (`cutStandardUnit_injective`).

## Main definitions

* `Stendhal.CutStandard`: the partial standardization of `N`.
* `Stendhal.cutStandardAction`: the action of `T^λ(θ + β)`.
* `Stendhal.cutStandardUnit`: the inclusion of `N` along the identity shuffle.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "νall" => (θ + β)
local notation "T" => TensorProductAlgebra k Q Λ νall

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
local notation "ρ" => cutShuffleAction Q Λ θ β N

open Classical in
/-- The affine loadings with the red strands in order. -/
def cutOrderedLoadings := Finset.univ.filter (fun s : Seq (α + δ) => IsRedOrdered s)
local notation "F" => cutOrderedLoadings (a := a) (r := r) θ β

/-- **The partial standardization at a cut**: the affine induced module modulo the part
supported on loadings whose red strands are out of order. -/
abbrev CutStandard := CutShuffle Q Λ θ β N ⧸ excludedSpace ρ F
local notation "V" => CutStandard Q Λ θ β N
variable (hQ : KLRSymm Q)
local notation "ord" => orderedShuffleAction ρ F (cutShuffle_returns Q Λ θ β N hQ)

omit [DecidableEq I] in
private theorem swap_unorders_red {i : Seq (α + δ)} (ho : IsRedOrdered i) {j : ℕ}
    (hj : j + 1 < (α + δ).card) (h₁ : (i.lbl ⟨j, by omega⟩).isRight)
    (h₂ : (i.lbl ⟨j + 1, hj⟩).isRight) : ¬ IsRedOrdered (sadj (α + δ).card j • i) := by
  cases he : i.lbl ⟨j, by omega⟩ with
  | inl c => simp [he] at h₁
  | inr u =>
    cases he' : i.lbl ⟨j + 1, hj⟩ with
    | inl c => simp [he'] at h₂
    | inr t =>
      intro h
      have hlt : (⟨j, by omega⟩ : Fin (α + δ).card) < ⟨j + 1, hj⟩ := by simp
      have h₁' : (sadj (α + δ).card j • i).lbl ⟨j, by omega⟩ = .inr t := by
        change i.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_left] using he'
      have h₂' : (sadj (α + δ).card j • i).lbl ⟨j + 1, hj⟩ = .inr u := by
        change i.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_right] using he
      exact (asymm (ho _ _ _ _ hlt he he')) (h _ _ _ _ hlt h₁' h₂')

private theorem relations_of_cast' {μ : Multiset (I ⊕ Fin (a + r))}
    {W : Type*} [Ring W] [Algebra k W] (H : μ = stendhalWeight (a + r) νall)
    (f : KLRAlgebra k S μ →ₐ[k] W)
    (hd : ∀ p (s : Seq μ), (s.lbl p).isRight → f (x p * e s) = 0)
    (hc : ∀ j (hj : j + 1 < μ.card) (s : Seq μ), (s.lbl ⟨j, by omega⟩).isRight →
      (s.lbl ⟨j + 1, hj⟩).isRight → f (ψ j * e s) = 0)
    (hu : ∀ s : Seq μ, ¬ IsRedOrdered s → f (e s) = 0)
    (hv : ∀ s : Seq μ, IsViolated s → f (e s) = 0) :
    TensorRepresentationRelations (f.comp (castKLR S H.symm).toAlgHom) := by
  subst μ
  exact ⟨hd, hc, hu, fun s _ => hv s⟩

private theorem cutOrderedRelations : TensorRepresentationRelations
    ((ord).comp (castKLR S (cutInputWeights_add (a := a) (r := r) θ β).symm).toAlgHom) := by
  classical
  apply relations_of_cast' Q Λ θ β (cutInputWeights_add (a := a) (r := r) θ β) (ord)
  · intro p s h
    exact orderedShuffleAction_eq_zero_of_eq_zero _ _ _ (cutShuffle_red_dot Q Λ θ β N hQ s p h)
  · intro j hj s h₁ h₂
    apply orderedShuffleAction_cross_eq_zero
    by_cases ho : IsRedOrdered s
    · exact Or.inr (by simpa [cutOrderedLoadings] using swap_unorders_red θ β ho hj h₁ h₂)
    · exact Or.inl (by simpa [cutOrderedLoadings] using ho)
  · intro s ho
    apply orderedShuffleAction_e_eq_zero
    simpa [cutOrderedLoadings] using ho
  · intro s hv
    exact orderedShuffleAction_eq_zero_of_eq_zero _ _ _ (cutShuffle_violated Q Λ θ β N hQ s hv)

/-- **The action of `T^λ(θ + β)` on the partial standardization.** -/
def cutStandardAction : T →ₐ[k] Module.End k V :=
  tensorRepresentationLift _ (cutOrderedRelations Q Λ θ β N hQ)

/-- The action of `T^λ(θ + β)` is induced by the affine action on the ordered quotient. -/
theorem cutStandardAction_affine (z : KLRAlgebra k S (α + δ)) :
    cutStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (cutInputWeights_add (a := a) (r := r) θ β) z)))) = ord z := by
  let H := cutInputWeights_add (a := a) (r := r) θ β
  have he := AlgHom.congr_fun (tensorRepresentationLift_comp _
    (cutOrderedRelations Q Λ θ β N hQ)) (castKLR S H z)
  exact he.trans (congrArg (ord) (castKLR_symm_castAlg H z))

omit [DecidableEq I] in
/-- The concatenation of red-ordered loadings of the two blocks is red-ordered. -/
theorem cut_isRedOrdered_append {a' : Seq α} {b' : Seq δ} (ha : IsRedOrdered a')
    (hb : IsRedOrdered b') : IsRedOrdered (a'.append b') := by
  intro p q u t hpq hp hq
  obtain ⟨p | p, rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective p <;>
    obtain ⟨q | q, rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective q
  · exact ha p q u t hpq ((Seq.append_posL a' b' p).symm.trans hp)
      ((Seq.append_posL a' b' q).symm.trans hq)
  · have h1 := cutPrefix_red θ a' p ((Seq.append_posL a' b' p).symm.trans hp)
    have h2 := cutSuffix_red β b' q ((Seq.append_posR a' b' q).symm.trans hq)
    rw [Fin.lt_def]; omega
  · exact False.elim ((not_lt_of_ge (blockEquiv_inl_lt_inr _ _ _).le) hpq)
  · apply hb p q u t _ ((Seq.append_posR a' b' p).symm.trans hp)
      ((Seq.append_posR a' b' q).symm.trans hq)
    change (Seq.posR α p).val < (Seq.posR α q).val at hpq
    exact Nat.add_lt_add_iff_left.mp hpq

local notation "N₀" => CutInput Q Λ θ β N
local notation "unitI" => indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀
local notation "π" => Submodule.mkQ (excludedSpace ρ F)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
private theorem indUnit_ordered (n : N) : ρ (eSum S F) (unitI n) = unitI n := by
  classical
  apply indShuffle_eSum_unit
  intro s hs'
  by_contra h
  have h' : ¬ ∀ m : N₀,
      concatIdem (Q := S) ((shufOne : Shuffle (Seq.card_add' α δ)).1 • s) • m = 0 := by
    simpa only [shufOne, one_smul] using h
  obtain ⟨a', b', he, ha, hb, _, _⟩ := cutShuffle_supported_input Q Λ θ β N s shufOne h'
  simp only [shufOne, one_smul] at he
  exact hs' (by simpa [cutOrderedLoadings, he] using cut_isRedOrdered_append θ β ha hb)

/-- The identity-shuffle inclusion of the factor module into its partial standardization. -/
def cutStandardUnit : N →ₗ[k] V :=
  (π).comp (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀)

include hQ in
/-- The partial standardization contains an isomorphic copy of its input module. -/
theorem cutStandardUnit_injective : Function.Injective (cutStandardUnit Q Λ θ β N) := by
  intro u v he
  exact indShuffleUnit_injective (ν := α) (ν' := δ) (cutStendhalQ_symm Q Λ hQ) N₀
    (orderedShuffle_mkQ_injOn ρ F (indUnit_ordered Q Λ θ β N u) (indUnit_ordered Q Λ θ β N v)
      he)

/-- The image of an affine diagram of the two blocks on the identity shuffle. -/
theorem cutStandardAction_concat_unit (t : TensorKLR S α δ) (n : N) :
    cutStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (cutInputWeights_add (a := a) (r := r) θ β) (concat S α δ t)))))
      (cutStandardUnit Q Λ θ β N n) =
      cutStandardUnit Q Λ θ β N (cutInputMap Q Λ θ β t • n) := by
  rw [cutStandardAction_affine]
  change π (ρ (concat S α δ t) (unitI n)) = π (unitI _)
  exact congrArg (fun m => π m) (concat_smul_indShuffleUnit N₀ t (n : N₀))

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
private theorem own_concat_one (hr : 0 < r) (s : Seq (α + δ)) (hconcat : s ∈ concatSet α δ)
    (u : Shuffle (Seq.card_add' α δ))
    (hne : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) : u = shufOne := by
  have hδ : 0 < (δ).card := by simp [stendhalWeight]; omega
  obtain ⟨a', b', he, _, _, _, hb⟩ := cutShuffle_supported_input Q Λ θ β N s u hne
  let z : Fin (δ).card := ⟨0, hδ⟩
  obtain ⟨t, ht⟩ : ∃ t, b'.lbl z = .inr t := by
    cases h : b'.lbl z with
    | inr t => exact ⟨t, rfl⟩
    | inl i => exact (hb ⟨hδ, by change (b'.lbl z).isLeft = true; simp [h]⟩).elim
  let p := u.1.symm (Seq.posR α z)
  have hp : s.lbl p = .inr t := by
    change (u.1 • s).1 (Seq.posR α z) = _
    rw [he, Seq.append_posR]
    exact ht
  obtain ⟨c, d, hs⟩ := mem_concatSet.mp hconcat
  apply Subtype.ext
  apply lastRedShuffle_eq_one (Seq.card_add' α δ) u hδ
  change (α).card ≤ p.val
  by_contra! h
  have hic : c.lbl ⟨p.val, h⟩ = .inr t := by
    change s.1 p = _ at hp
    rw [← hs, Seq.append_apply_lt c d p h] at hp
    exact hp
  have h1 := cutPrefix_red θ c _ hic
  have h2 := cutSuffix_red β b' z ht
  omega

/-- At the cut, every affine concatenation has image in the identity-shuffle copy of the
factor module (for a nonempty second block). -/
theorem cutStandardAction_concat_mem_range (hr : 0 < r) (t : TensorKLR S α δ) (z : V) :
    cutStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (cutInputWeights_add (a := a) (r := r) θ β) (concat S α δ t))))) z ∈
      LinearMap.range (cutStandardUnit Q Λ θ β N) := by
  classical
  obtain ⟨m, rfl⟩ := (excludedSpace ρ F).mkQ_surjective z
  rw [cutStandardAction_affine]
  change π (ρ (concat S α δ t) m) ∈ _
  have ho (s : Seq (α + δ)) (h : s ∈ concatSet α δ) (u : Shuffle (Seq.card_add' α δ))
      (hu : u ≠ shufOne) : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    by_contra hn
    exact hu (own_concat_one Q Λ θ β N hr s h u hn)
  obtain ⟨n, hn⟩ := indShuffle_eSum_mem_unit (cutStendhalQ_symm Q Λ hQ) N₀ (concatSet α δ) ho
    ((concat S α δ t) • m)
  change (oneConcat S α δ) • ((concat S α δ t) • m) = unitI n at hn
  rw [← mul_smul, oneConcat_mul_concat] at hn
  exact ⟨n, congrArg (fun x => π x) hn.symm⟩

end Categorification.Stendhal
