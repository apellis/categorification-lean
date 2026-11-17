/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleAction
import Categorification.WeightedKLR.RedStrands.RepresentationLift

/-!
# Standardization by the ordered quotient of affine induction

Webster, arXiv:1309.3796v2, §5, Theorem 5.8. The ordered quotient of
parabolic induction carries the action of the tensor product algebra.
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
local notation "νall" => (θ + β)
local notation "T" => TensorProductAlgebra k Q Λ νall
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
local notation "ρ" => parabolicShuffleAction Q Λ θ β N

open Classical in
/-- The affine loadings with the required red order. -/
def parabolicOrderedLoadings := Finset.univ.filter (fun s : Seq (α+δ) => IsRedOrdered s)
local notation "F" => parabolicOrderedLoadings (ℓ := ℓ) θ β

/-- The underlying space of standardization of a factor module. -/
abbrev ParabolicStandard := ParabolicShuffle Q Λ θ β N ⧸ excludedSpace ρ F
local notation "V" => ParabolicStandard Q Λ θ β N
variable (hQ : KLRSymm Q)
local notation "ord" => orderedShuffleAction ρ F (parabolicShuffle_returns Q Λ θ β N hQ)

omit [DecidableEq I] in
private theorem swap_unorders_red {i : Seq (α+δ)} (ho : IsRedOrdered i) {j : ℕ}
    (hj : j+1 < (α+δ).card) (h₁ : (i.lbl ⟨j, by omega⟩).isRight)
    (h₂ : (i.lbl ⟨j+1,hj⟩).isRight) : ¬ IsRedOrdered (sadj (α+δ).card j • i) := by
  cases he : i.lbl ⟨j,by omega⟩ with
  | inl c => simp [he] at h₁
  | inr r =>
    cases he' : i.lbl ⟨j+1,hj⟩ with
    | inl c => simp [he'] at h₂
    | inr t =>
      intro h
      have hlt : (⟨j, by omega⟩ : Fin (α+δ).card) < ⟨j+1,hj⟩ := by simp
      have h₁' : (sadj (α+δ).card j • i).lbl ⟨j,by omega⟩ = .inr t := by
        change i.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_left] using he'
      have h₂' : (sadj (α+δ).card j • i).lbl ⟨j+1,hj⟩ = .inr r := by
        change i.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_right] using he
      exact (asymm (ho _ _ _ _ hlt he he')) (h _ _ _ _ hlt h₁' h₂')

private theorem relations_of_cast {μ : Multiset (I ⊕ Fin (ℓ+1))}
    {W : Type*} [Ring W] [Algebra k W] (H : μ = stendhalWeight (ℓ+1) νall)
    (f : KLRAlgebra k S μ →ₐ[k] W)
    (hd : ∀ a (s : Seq μ), (s.lbl a).isRight → f (x a * e s) = 0)
    (hc : ∀ j (hj : j+1 < μ.card) (s : Seq μ), (s.lbl ⟨j,by omega⟩).isRight →
      (s.lbl ⟨j+1,hj⟩).isRight → f (ψ j * e s) = 0)
    (hu : ∀ s : Seq μ, ¬ IsRedOrdered s → f (e s) = 0)
    (hv : ∀ s : Seq μ, IsViolated s → f (e s) = 0) :
    TensorRepresentationRelations (f.comp (castKLR S H.symm).toAlgHom) := by
  subst μ
  exact ⟨hd,hc,hu,fun s _ => hv s⟩

private theorem parabolicOrderedRelations : TensorRepresentationRelations
    ((ord).comp (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β).symm).toAlgHom) := by
  classical
  apply relations_of_cast Q Λ θ β (parabolicInputWeights_add (ℓ := ℓ) θ β) (ord)
  · intro a s h
    exact orderedShuffleAction_eq_zero_of_eq_zero _ _ _ (parabolicShuffle_red_dot Q Λ θ β N hQ s a h)
  · intro j hj s h₁ h₂
    apply orderedShuffleAction_cross_eq_zero
    by_cases ho : IsRedOrdered s
    · exact Or.inr (by simpa [parabolicOrderedLoadings] using swap_unorders_red θ β ho hj h₁ h₂)
    · exact Or.inl (by simpa [parabolicOrderedLoadings] using ho)
  · intro s ho
    apply orderedShuffleAction_e_eq_zero
    simpa [parabolicOrderedLoadings] using ho
  · intro s hv
    exact orderedShuffleAction_eq_zero_of_eq_zero _ _ _ (parabolicShuffle_violated Q Λ θ β N hQ s hv)

/-- The action of the violated, red-ordered Webster algebra on the
standardization of an arbitrary module of the two factor algebras. -/
def parabolicStandardAction : T →ₐ[k] Module.End k V :=
  tensorRepresentationLift _ (parabolicOrderedRelations Q Λ θ β N hQ)

/-- The tensor product algebra action is induced by the affine action on
the ordered quotient. -/
theorem parabolicStandardAction_affine (a : KLRAlgebra k S (α+δ)) :
    parabolicStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) a)))) = ord a := by
  let H := parabolicInputWeights_add (ℓ := ℓ) θ β
  have he := AlgHom.congr_fun (tensorRepresentationLift_comp _
    (parabolicOrderedRelations Q Λ θ β N hQ)) (castKLR S H a)
  exact he.trans (congrArg (ord) (castKLR_symm_castAlg H a))


omit [DecidableEq I] in
private theorem ordered_inputs {a : Seq α} {b : Seq δ} (ha : IsRedOrdered a)
    (hb : IsRedOrdered b) : IsRedOrdered (a.append b) := by
  intro x y r t hxy hx hy
  obtain ⟨x|x,rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective x <;>
    obtain ⟨y|y,rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective y
  · exact ha x y r t hxy ((Seq.append_posL a b x).symm.trans hx)
      ((Seq.append_posL a b y).symm.trans hy)
  · have hr := parabolicPrefix_red_lt_last θ a x ((Seq.append_posL a b x).symm.trans hx)
    rwa [parabolicLast_red_eq_last β b y ((Seq.append_posR a b y).symm.trans hy)]
  · exact False.elim ((not_lt_of_ge (blockEquiv_inl_lt_inr _ _ _).le) hxy)
  · apply hb x y r t _ ((Seq.append_posR a b x).symm.trans hx) ((Seq.append_posR a b y).symm.trans hy)
    change (Seq.posR α x).val < (Seq.posR α y).val at hxy
    exact Nat.add_lt_add_iff_left.mp hxy

local notation "N₀" => ParabolicInput Q Λ θ β N
local notation "unitI" => indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀
local notation "π" => Submodule.mkQ (excludedSpace ρ F)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
private theorem indUnit_ordered (n : N) : ρ (eSum S F) (unitI n) = unitI n := by
  classical
  apply indShuffle_eSum_unit
  intro s hs'
  by_contra h
  have h' : ¬ ∀ m : N₀, concatIdem (Q := S) ((shufOne : Shuffle (Seq.card_add' α δ)).1 • s) • m = 0 := by
    simpa only [shufOne, one_smul] using h
  obtain ⟨a,b,he,ha,hb,_,_⟩ := parabolicShuffle_supported_input Q Λ θ β N s shufOne h'
  simp only [shufOne, one_smul] at he
  exact hs' (by simpa [parabolicOrderedLoadings, he] using ordered_inputs θ β ha hb)

/-- The identity-shuffle inclusion of the factor module into its
standardization. -/
def parabolicStandardUnit : N →ₗ[k] V :=
  (π).comp (indShuffleUnitLinear (Q := S) (ν := α) (ν' := δ) N₀)

include hQ in
/-- Standardization retains an isomorphic copy of its input module. -/
theorem parabolicStandardUnit_injective :
    Function.Injective (parabolicStandardUnit Q Λ θ β N) := by
  intro a b he
  exact indShuffleUnit_injective (ν := α) (ν' := δ) (stendhalQ_swap_symm Q Λ hQ) N₀
    (orderedShuffle_mkQ_injOn ρ F (indUnit_ordered Q Λ θ β N a) (indUnit_ordered Q Λ θ β N b) he)

/-- Image of an affine diagram on the projected identity shuffle. -/
theorem parabolicStandardAction_concat_unit (t : TensorKLR S α δ) (n : N) :
    parabolicStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) (concat S α δ t)))))
      (parabolicStandardUnit Q Λ θ β N n) =
      parabolicStandardUnit Q Λ θ β N (parabolicInputMap Q Λ θ β t • n) := by
  rw [parabolicStandardAction_affine]
  change π (ρ (concat S α δ t) (unitI n)) = π (unitI _)
  exact congrArg (fun m => π m) (concat_smul_indShuffleUnit N₀ t (n : N₀))


omit [DecidableEq I] in
private theorem lastInput_positive : 0 < (δ).card := by simp [stendhalWeight]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- In every supported shuffle the final red is the first strand
of the right input block. -/
theorem parabolicShuffle_last_red (s : Seq (α+δ)) (p : Fin (α+δ).card)
    (hp : s.lbl p = .inr (Fin.last ℓ)) (u : Shuffle (Seq.card_add' α δ))
    (hne : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) :
    u.1 p = Seq.posR α ⟨0, lastInput_positive (ℓ := ℓ) β⟩ := by
  obtain ⟨a,b,he,_,_,_,hb⟩ := parabolicShuffle_supported_input Q Λ θ β N s u hne
  let z : Fin (δ).card := ⟨0, lastInput_positive (ℓ := ℓ) β⟩
  have hx : b.lbl z = .inr (Fin.last ℓ) := by
    cases h : b.lbl z with
    | inr r => exact congrArg Sum.inr (parabolicLast_red_eq_last β b z h)
    | inl i => exact (hb ⟨_,by change (b.lbl z).isLeft = true; simp [h]⟩).elim
  have he' : s.lbl (u.1.symm (Seq.posR α z)) = .inr (Fin.last ℓ) := by
    change (u.1 • s).1 (Seq.posR α z) = _
    rw [he, Seq.append_posR]
    exact hx
  have eqv := parabolicShuffle_red_label_unique θ β s _ _ hp he'
  exact u.1.eq_symm_apply.mp eqv

omit [DecidableEq I] in
private theorem lastInput_first (b : Seq δ) (hb : ¬ IsViolated b) :
    b.lbl ⟨0, lastInput_positive (ℓ := ℓ) β⟩ = .inr (Fin.last ℓ) := by
  let z : Fin (δ).card := ⟨0, lastInput_positive (ℓ := ℓ) β⟩
  change b.lbl z = _
  cases hx : b.lbl z with
  | inr r => exact congrArg Sum.inr (parabolicLast_red_eq_last β b z hx)
  | inl i => exact (hb ⟨_,by change (b.lbl z).isLeft = true; simp [hx]⟩).elim

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
private theorem own_concat_one (s : Seq (α+δ)) (hconcat : s ∈ concatSet α δ)
    (u : Shuffle (Seq.card_add' α δ))
    (hne : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) : u = shufOne := by
  obtain ⟨a,b,he,_,_,_,hb⟩ := parabolicShuffle_supported_input Q Λ θ β N s u hne
  let z : Fin (δ).card := ⟨0,lastInput_positive (ℓ := ℓ) β⟩
  let p := u.1.symm (Seq.posR α z)
  have hp : s.lbl p = .inr (Fin.last ℓ) := by
    change (u.1 • s).1 (Seq.posR α z) = _
    rw [he, Seq.append_posR]
    exact lastInput_first β b hb
  obtain ⟨c,d,hs⟩ := mem_concatSet.mp hconcat
  apply Subtype.ext
  apply lastRedShuffle_eq_one (Seq.card_add' α δ) u (lastInput_positive (ℓ := ℓ) β)
  change (α).card ≤ p.val
  by_contra! h
  have hic : c.lbl ⟨p.val,h⟩ = .inr (Fin.last ℓ) := by
    change s.1 p = _ at hp
    rw [← hs, Seq.append_apply_lt c d p h] at hp
    exact hp
  exact (lt_irrefl _ (parabolicPrefix_red_lt_last θ c _ hic))

/-- At the parabolic cut, every affine concatenation has image in the
identity-shuffle copy of the factor module. -/
theorem parabolicStandardAction_concat_mem_range (t : TensorKLR S α δ) (z : V) :
    parabolicStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
      (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) (concat S α δ t))))) z ∈
      LinearMap.range (parabolicStandardUnit Q Λ θ β N) := by
  classical
  obtain ⟨m,rfl⟩ := (excludedSpace ρ F).mkQ_surjective z
  rw [parabolicStandardAction_affine]
  change π (ρ (concat S α δ t) m) ∈ _
  have ho (s : Seq (α+δ)) (h : s ∈ concatSet α δ) (u : Shuffle (Seq.card_add' α δ))
      (hu : u ≠ shufOne) : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    by_contra hn
    exact hu (own_concat_one Q Λ θ β N s h u hn)
  obtain ⟨n,hn⟩ := indShuffle_eSum_mem_unit (stendhalQ_swap_symm Q Λ hQ) N₀ (concatSet α δ) ho
    ((concat S α δ t) • m)
  change (oneConcat S α δ) • ((concat S α δ t) • m) = unitI n at hn
  rw [← mul_smul, oneConcat_mul_concat] at hn
  exact ⟨n, congrArg (fun x => π x) hn.symm⟩

end Categorification.Stendhal
