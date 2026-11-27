/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleAction

/-!
# Partial standardization at a cut: the affine induced module

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1;…;λ_m}` defined after Definition 5.4, for two
blocks: the red strands `λ_1, …, λ_a` and `λ_{a+1}, …, λ_{a+r}` of `λ = (λ_1, …, λ_{a+r})`.
Only right crossings of the red strands of the second block with black strands of the first
block are killed. The factor algebra is `T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)`, and a module
over it is induced to the affine KLR algebra of all strands. This generalizes the cut with
one red strand in the second block (`ParabolicShuffle`), where `T^{λ_{a+1}}(β)` is the
cyclotomic quotient; with `r = 2` it gives Webster's `𝕊^{λ⁺}_+` for a pair `(μ, μ*)` added at
the end, used in Lemma 7.19.

## Main definitions

* `Stendhal.cutFactorAlgebra`: the tensor product of the two factor algebras.
* `Stendhal.cutInputMap`: the quotient map from the affine KLR algebras of the two blocks.
* `Stendhal.CutShuffle`: the affine induced module.

## Main results

* `Stendhal.cutInputWeights_add`: the weights of the two blocks add up to the total weight.
* `Stendhal.cutShuffle_violated`, `Stendhal.cutShuffle_red_dot`,
  `Stendhal.cutShuffle_returns`: violated loadings and red dots act by zero, and every
  crossing returning to the red order vanishes, as in the one-red case.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

/-- The elements of `Fin (a + r)`: those of `Fin a`, then those of `Fin r` shifted by `a`. -/
theorem univ_val_fin_add (a r : ℕ) : (Finset.univ : Finset (Fin (a + r))).val =
    (Finset.univ : Finset (Fin a)).val.map (Fin.castAdd r) +
      (Finset.univ : Finset (Fin r)).val.map (Fin.natAdd a) := by
  classical
  ext x
  rw [Multiset.count_add, Multiset.count_univ]
  refine Fin.addCases (fun u => ?_) (fun v => ?_) x
  · rw [Multiset.count_map_eq_count' _ _ (Fin.castAdd_injective a r), Multiset.count_univ,
      Multiset.count_eq_zero.2]
    intro h
    obtain ⟨v, -, hv⟩ := Multiset.mem_map.1 h
    have := congrArg Fin.val hv
    simp at this; omega
  · rw [Multiset.count_map_eq_count' _ _ (Fin.natAdd_injective r a), Multiset.count_univ,
      Multiset.count_eq_zero.2]
    intro h
    obtain ⟨u, -, hu⟩ := Multiset.mem_map.1 h
    have := congrArg Fin.val hu
    simp at this; omega

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "L" => TensorProductAlgebra k Q (Λ ∘ Fin.castAdd r) θ
local notation "C" => TensorProductAlgebra k Q (Λ ∘ Fin.natAdd a) β

omit [DecidableEq I] in
/-- The weights of the two blocks add up to the Stendhal weight of all strands. -/
theorem cutInputWeights_add :
    (stendhalWeight a θ).map (Sum.map (id : I → I) (Fin.castAdd r)) +
      (stendhalWeight r β).map (Sum.map (id : I → I) (Fin.natAdd a)) =
      stendhalWeight (a + r) (θ + β) := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, Function.comp_def,
    Sum.map_inl, Sum.map_inr, id_eq]
  rw [univ_val_fin_add, Multiset.map_add, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def]
  abel

/-- The quotient of the affine KLR algebra of the first block onto `T^{λ_1…λ_a}(θ)`. -/
abbrev cutPrefixProjection :=
  redSubfamilyProjection Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r) θ

/-- The quotient of the affine KLR algebra of the second block onto
`T^{λ_{a+1}…λ_{a+r}}(β)`. -/
abbrev cutSuffixProjection :=
  redSubfamilyProjection Q Λ (Fin.natAdd a) (Fin.natAdd_injective r a) β

/-- The tensor product of the two factor algebras at the cut. -/
abbrev cutFactorAlgebra := L ⊗[k] C

local notation "D" => cutFactorAlgebra Q Λ θ β
local notation "A" => KLRAlgebra k S (α + δ)
local notation "B" => TensorKLR S α δ

/-- The two quotient maps defining the input module of induction. -/
def cutInputMap : B →ₐ[k] D :=
  Algebra.TensorProduct.map (cutPrefixProjection Q Λ θ) (cutSuffixProjection Q Λ β)

/-- A module over the factor algebras, restricted along the affine quotient. -/
def CutInput (N : Type*) [AddCommGroup N] [Module D N] := N

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
local notation "N₀" => CutInput Q Λ θ β N
instance : AddCommGroup N₀ := inferInstanceAs (AddCommGroup N)
instance : Module k N₀ := inferInstanceAs (Module k N)
instance : Module D N₀ := inferInstanceAs (Module D N)
instance : IsScalarTower k D N₀ := inferInstanceAs (IsScalarTower k D N)
instance : Module B N₀ := Module.compHom N (cutInputMap Q Λ θ β).toRingHom
instance : IsScalarTower k B N₀ := ⟨fun c t n => by
  change (cutInputMap Q Λ θ β (c • t)) • (n : N) = c • ((cutInputMap Q Λ θ β t) • (n : N))
  rw [map_smul, smul_assoc]⟩

/-- The affine induced module, before excluding unordered red loadings. -/
abbrev CutShuffle := Ind S α δ N₀
local notation "M" => CutShuffle Q Λ θ β N

/-- The affine action on the induced module. -/
abbrev cutShuffleAction : A →ₐ[k] Module.End k M := Algebra.lsmul k k M

omit [DecidableEq I] in
private theorem red_of_map_eq' {m n : ℕ} {f : Fin m → Fin n} {z : I ⊕ Fin m} {t : Fin n}
    (h : Sum.map (id : I → I) f z = .inr t) : ∃ j, z = .inr j ∧ f j = t := by
  cases z with
  | inl i => contradiction
  | inr j => exact ⟨j, rfl, Sum.inr.inj h⟩

omit [DecidableEq I] in
/-- A red label of the first block is `castAdd` of a label of `Fin a`. -/
theorem cutPrefix_red (t : Seq α) (p : Fin (α).card) {u : Fin (a + r)} (hu : t.lbl p = .inr u) :
    u.val < a := by
  obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp (t.mem p)
  obtain ⟨j, _, rfl⟩ := red_of_map_eq' (hz.trans hu)
  exact j.isLt

omit [DecidableEq I] in
/-- A red label of the second block is `natAdd` of a label of `Fin r`. -/
theorem cutSuffix_red (t : Seq δ) (p : Fin (δ).card) {u : Fin (a + r)} (hu : t.lbl p = .inr u) :
    a ≤ u.val := by
  obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp (t.mem p)
  obtain ⟨j, _, rfl⟩ := red_of_map_eq' (hz.trans hu)
  simp

omit [DecidableEq I] in
theorem strictMono_natAdd' : StrictMono (Fin.natAdd a : Fin r → Fin (a + r)) := fun x y h => by
  simp only [Fin.lt_def, Fin.val_natAdd] at h ⊢; omega

omit [DecidableEq I] in
/-- The Stendhal parameters of symmetric `Q` are symmetric, for any number of red strands (the
form of `stendhalQ_symm` used with the cut factor algebras). -/
theorem cutStendhalQ_symm (hQ : KLRSymm Q) : KLRSymm S := by
  rintro (i | u) (j | t) h
  · exact hQ i j (fun he => h (congrArg Sum.inl he))
  · simp [stendhalQ]
  · simp [stendhalQ]
  · simp [stendhalQ]

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
private theorem concatIdem_annihilates (s : Seq (α + δ))
    (h : ∀ (a' : Seq α) (b' : Seq δ), s = a'.append b' →
      cutInputMap Q Λ θ β (e a' ⊗ₜ[k] e b') = 0) (n : N₀) :
    concatIdem (Q := S) s • n = 0 := by
  classical
  by_cases hc : s ∈ concatSet α δ
  · obtain ⟨⟨a', b'⟩, _, he⟩ := Finset.mem_image.mp hc
    change a'.append b' = s at he
    subst s
    change cutInputMap Q Λ θ β (concatIdem (a'.append b')) • (n : N) = 0
    rw [concatIdem_append, h a' b' rfl]
    exact zero_smul D (n : N)
  · rw [concatIdem_of_not_mem hc, zero_smul]

private theorem cutInputMap_tmul (t : KLRAlgebra k S α) (u : KLRAlgebra k S δ) :
    cutInputMap Q Λ θ β (t ⊗ₜ[k] u) =
      cutPrefixProjection Q Λ θ t ⊗ₜ[k] cutSuffixProjection Q Λ β u := by
  simp [cutInputMap]

/-- The affine induced module is zero at a violated loading. -/
theorem cutShuffle_violated (hQ : KLRSymm Q) (s : Seq (α + δ)) (hv : IsViolated s) :
    cutShuffleAction Q Λ θ β N (e s) = 0 := by
  apply LinearMap.ext; intro z
  apply (indDecomp (cutStendhalQ_symm Q Λ hQ) N₀).injective
  funext u
  change indDecomp _ N₀ ((e s : A) • z) u = _
  rw [indDecomp_e_smul]
  have hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0 := by
    apply concatIdem_annihilates
    intro a' b' hh
    rw [cutInputMap_tmul]
    by_cases ha : IsViolated a'
    · rw [redSubfamilyProjection_e_violated_ambient Q Λ _ _ θ a' ha, zero_tmul]
    · have hb : IsViolated b' := by
        by_contra hb
        exact shuffle_not_violated a' b' ha hb u hh hv
      rw [redSubfamilyProjection_e_violated_ambient Q Λ _ _ β b' hb, tmul_zero]
  rw [hz]
  change 0 = indDecomp _ N₀ 0 u
  rw [map_zero]; rfl

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- A nonzero input coordinate comes from ordered, nonviolating loadings of both blocks. -/
theorem cutShuffle_supported_input (s : Seq (α + δ)) (u : Shuffle (Seq.card_add' α δ))
    (hn : ¬ ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0) :
    ∃ a' : Seq α, ∃ b' : Seq δ, u.1 • s = a'.append b' ∧ IsRedOrdered a' ∧
      IsRedOrdered b' ∧ ¬ IsViolated a' ∧ ¬ IsViolated b' := by
  classical
  by_contra! h
  apply hn
  apply concatIdem_annihilates
  intro a' b' he
  rw [cutInputMap_tmul]
  by_cases ha : IsRedOrdered a'
  · by_cases hb : IsRedOrdered b'
    · by_cases hva : IsViolated a'
      · rw [redSubfamilyProjection_e_violated_ambient Q Λ _ _ θ a' hva, zero_tmul]
      · have hvb : IsViolated b' := h a' b' he ha hb hva
        rw [redSubfamilyProjection_e_violated_ambient Q Λ _ _ β b' hvb, tmul_zero]
    · rw [redSubfamilyProjection_e_unordered_ambient Q Λ _ _ β strictMono_natAdd' b' hb,
        tmul_zero]
  · rw [redSubfamilyProjection_e_unordered_ambient Q Λ (Fin.castAdd r) _ θ
      (fun _ _ h => h) a' ha, zero_tmul]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- At every crossing which returns to the prescribed order, the affine action vanishes. -/
theorem cutShuffle_returns (hQ : KLRSymm Q) :
    VanishingReturnCrossings (cutShuffleAction Q Λ θ β N)
      (open Classical in Finset.univ.filter (fun s : Seq (α + δ) => IsRedOrdered s)) := by
  classical
  intro j s hs ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  by_cases hj : j + 1 < (α + δ).card
  · obtain ⟨r', t, hr, ht', _⟩ := red_inversion_of_ordered_swap hj hs ht
    have hquad : (ψ j * ψ j * e (sadj (α + δ).card j • s) : A) = 0 := by
      rw [ψ_sq j hj]
      have h₁ : (sadj (α + δ).card j • s).lbl ⟨j, by omega⟩ = .inr t := by
        change s.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_left] using ht'
      have h₂ : (sadj (α + δ).card j • s).lbl ⟨j + 1, hj⟩ = .inr r' := by
        change s.lbl ((sadj _ j).symm _) = _
        simpa only [sadj, dite_eq_left hj, Equiv.symm_swap, Equiv.swap_apply_right] using hr
      rw [h₁, h₂]
      split_ifs
      · rfl
      · change ncEval _ (0 : MvPolynomial (Fin 2) k) * _ = 0
        simp [ncEval]
    apply LinearMap.ext; intro z
    apply indShuffle_crossing_eq_zero (cutStendhalQ_symm Q Λ hQ) N₀ s j hquad _ z
    intro u
    by_cases hz : ∀ n : N₀, concatIdem (Q := S) (u.1 • s) • n = 0
    · exact ⟨shufWord u, (shufWord_spec u).1, (shufWord_spec u).2, Or.inl hz⟩
    obtain ⟨a', b', he, ha, hb, _, _⟩ := cutShuffle_supported_input Q Λ θ β N s u hz
    have hbefore : ∀ x y r₁ t₁, a'.lbl x = .inr r₁ → b'.lbl y = .inr t₁ → r₁ < t₁ := by
      intro x y r₁ t₁ h1 h2
      have := cutPrefix_red θ a' x h1
      have := cutSuffix_red β b' y h2
      rw [Fin.lt_def]; omega
    obtain ⟨x, y, _, _, h₁, h₂, _, _⟩ := shuffle_returns_order hj ha hb hbefore u he hs ht
    have hd := (shuffle_right_descent (Seq.card_add' α δ) u hj h₁ h₂).2
    let v := canWord (α + δ).card (u.1 * sadj (α + δ).card j)
    have hw : wordProd (α + δ).card (v ++ [j]) = u.1 := by
      rw [wordProd_append, wordProd_singleton, show wordProd _ v = _ from wordProd_canWord _ _,
        mul_assoc, TypeA.sadj_mul_self, mul_one]
    refine ⟨v ++ [j], ⟨?_, ?_⟩, hw, Or.inr ⟨v, rfl⟩⟩
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact (isReduced_canWord _ _).1 p h
      · exact (List.mem_singleton.mp h).symm ▸ hj
    · simpa only [hw, v, List.length_append, List.length_singleton, length_canWord] using hd
  · rw [ψ_eq_zero j (by omega), zero_mul, map_zero]

private theorem concat_dot_left (a' : Seq α) (b' : Seq δ) (p : Fin (α).card) :
    concat S α δ ((x p * e a') ⊗ₜ[k] e b') = x (Seq.posL δ p) * e (a'.append b') := by
  have h : ((x p * e a') ⊗ₜ[k] e b' : B) = (x p ⊗ₜ[k] 1) * (e a' ⊗ₜ[k] e b') := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_x_tmul_one, concat_e_tmul_e, mul_assoc,
    oneConcat_mul_e (append_mem_concatSet a' b')]

private theorem concat_dot_right (a' : Seq α) (b' : Seq δ) (p : Fin (δ).card) :
    concat S α δ (e a' ⊗ₜ[k] (x p * e b')) = x (Seq.posR α p) * e (a'.append b') := by
  have h : (e a' ⊗ₜ[k] (x p * e b') : B) = (1 ⊗ₜ[k] x p) * (e a' ⊗ₜ[k] e b') := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h, concat_mul, concat_one_tmul_x, concat_e_tmul_e, mul_assoc,
    oneConcat_mul_e (append_mem_concatSet a' b')]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
private theorem dot_zero_unit (s : Seq (α + δ)) (p : Fin (α + δ).card)
    (hr : (s.lbl p).isRight) (n : N₀) :
    (x p * e s : A) • indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀ n = 0 := by
  classical
  by_cases hc : s ∈ concatSet α δ
  · obtain ⟨⟨a', b'⟩, _, he⟩ := Finset.mem_image.mp hc
    change a'.append b' = s at he
    subst s
    obtain ⟨i, rfl⟩ := (blockEquiv (Seq.card_add' α δ)).surjective p
    cases i with
    | inl i =>
      change (x (Seq.posL δ i) * e (a'.append b') : A) • _ = _
      rw [← concat_dot_left Q Λ θ β a' b' i, concat_smul_indShuffleUnit]
      have hi : (a'.lbl i).isRight := by
        change ((a'.append b').1 (Seq.posL δ i)).isRight = true at hr
        rwa [Seq.append_posL] at hr
      have hzero : ((x i * e a') ⊗ₜ[k] e b' : B) • n = 0 := by
        change (cutInputMap Q Λ θ β _) • (n : N) = 0
        rw [cutInputMap_tmul, redSubfamilyProjection_red_dot_ambient Q Λ _ _ θ a' i hi,
          zero_tmul]
        exact zero_smul D (n : N)
      rw [hzero, indShuffleUnit, BalancedTensor.tmul_zero]
    | inr i =>
      change (x (Seq.posR α i) * e (a'.append b') : A) • _ = _
      rw [← concat_dot_right Q Λ θ β a' b' i, concat_smul_indShuffleUnit]
      have hi : (b'.lbl i).isRight := by
        change ((a'.append b').1 (Seq.posR α i)).isRight = true at hr
        rwa [Seq.append_posR] at hr
      have hzero : (e a' ⊗ₜ[k] (x i * e b') : B) • n = 0 := by
        change (cutInputMap Q Λ θ β _) • (n : N) = 0
        rw [cutInputMap_tmul, redSubfamilyProjection_red_dot_ambient Q Λ _ _ β b' i hi,
          tmul_zero]
        exact zero_smul D (n : N)
      rw [hzero, indShuffleUnit, BalancedTensor.tmul_zero]
  · rw [mul_smul, idem_smul_indShuffleUnit, concatIdem_of_not_mem hc, zero_smul,
      indShuffleUnit, BalancedTensor.tmul_zero, smul_zero]

omit [DecidableEq I] in
/-- Each red label occurs once in a loading of all strands. -/
theorem cutShuffle_red_label_unique (s : Seq (α + δ)) {u : Fin (a + r)} (p q : Fin (α + δ).card)
    (hp : s.lbl p = .inr u) (hq : s.lbl q = .inr u) : p = q := by
  classical
  let F := Finset.univ.filter (fun c => Sum.inr u = s.lbl c)
  have hc : F.card = 1 := by
    change (Finset.univ.val.filter (fun c => Sum.inr u = s.lbl c)).card = 1
    rw [← Multiset.count_map, show Finset.univ.val.map s.lbl = α + δ from s.2,
      cutInputWeights_add, stendhalWeight, Multiset.count_add,
      Multiset.count_map_eq_count' Sum.inr _ Sum.inr_injective]
    simp
  exact Finset.card_le_one_iff.mp hc.le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.symm⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq.symm⟩)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- All red dots annihilate the affine induced module. -/
theorem cutShuffle_red_dot (hQ : KLRSymm Q) (s : Seq (α + δ)) (p : Fin (α + δ).card)
    (hr : (s.lbl p).isRight) : cutShuffleAction Q Λ θ β N (x p * e s) = 0 := by
  cases he : s.lbl p with
  | inl i => simp [he] at hr
  | inr u =>
    apply LinearMap.ext; intro z
    apply indShuffle_dot_eq_zero (cutStendhalQ_symm Q Λ hQ) N₀ (Sum.inr u)
      (fun t b c => cutShuffle_red_label_unique θ β t b c) _ s p he z
    intro t b hb n
    exact dot_zero_unit Q Λ θ β N t b (by simp [hb]) n

end Categorification.Stendhal
