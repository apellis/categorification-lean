/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedHom
import Categorification.WeightedKLR.RedStrands.SplitRedWords
import Categorification.WeightedKLR.RedStrands.StendhalParameters

/-!
# Splitting a red strand before quotienting

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. Splitting the red strand `λ_c = λ'_c + λ'_{c+1}` sends a Stendhal term
`ψ_ρ x^u e(s)` of `T̃^λ` to the Stendhal term of `T̃^{λ'}` with loading the split loading of
`s`, word the expanded word of `ρ`, and the same dots on the old strands. Distinct terms go to
distinct terms, so the independence of the Stendhal terms of `T̃^{λ'}` (Proposition 4.16)
gives injectivity of the splitting map on red-ordered diagrams.

## Main results

* `splitHom_word` : the value of the splitting map on `ψ_ρ x^u e(s)`.
* `splitStendhalValue` : the splitting map on red-ordered diagrams, `T̃^λ → T̃^{λ'}`.
* `splitStendhalValue_injective` : it is injective, for the crossing parameters of §2.2.
* `e_mul_mul_e_mem_range_splitStendhalValue` : its image contains `e(t') T̃^{λ'} e(s')` for all
  split loadings `s'`, `t'`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

/-- A family of vectors is independent if projections cut it into independent pieces. -/
theorem linearIndependent_of_projections {R M ι κ : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [DecidableEq κ] (v : ι → M) (key : ι → κ) (P : κ → M →ₗ[R] M)
    (hP : ∀ s i, P s (v i) = if key i = s then v i else 0)
    (h : ∀ s, LinearIndependent R (fun i : {i // key i = s} => v i)) :
    LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro t g hg i hi
  have h1 := congrArg (P (key i)) hg
  rw [map_sum, map_zero] at h1
  simp only [map_smul, hP, smul_ite, smul_zero] at h1
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter] at h1
  exact linearIndependent_iff'.1 (h (key i)) (t.subtype _) (fun x => g x) h1 ⟨i, rfl⟩
    (Finset.mem_subtype.2 hi)

namespace SplitRed

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (c : Fin ℓ)
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "m'" => Multiset.card (stendhalWeight (ℓ + 1) ν)
local notation "C" => SplitCorner c Q Λ' ν
local notation "π" => StendhalAlgebraAllOrders.ofKLR k Q (mergeWeights c Λ') ν
local notation "π'" => StendhalAlgebraAllOrders.ofKLR k Q Λ' ν

noncomputable local instance : Algebra k C := KLR.cornerAlgebra _

/-! ### The value on standard elements -/

theorem splitHom_polA (p : MvPolynomial (Fin m) k) :
    splitHom c Q Λ' ν (polA k Q (mergeWeights c Λ') ν p) = polSplit c Λ' p := by
  have : (splitHom c Q Λ' ν).comp (polA k Q (mergeWeights c Λ') ν) = polSplit c Λ' := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, polA_X, splitHom_x]
  exact DFunLike.congr_fun this p

theorem W_eq_ofKLR (j q : ℕ) : W Q Λ' ν j q = π' (KLRAlgebra.ψw (wLetters j q)) := by
  unfold W wLetters
  split_ifs <;> simp [KLRAlgebra.ψw_cons, map_mul, StendhalAlgebraAllOrders.ψ]

/-- The splitting map on `ψ_ρ x^p e(s)`: the word is expanded, the dots move to the old strands
of the split loading. -/
theorem splitHom_word (s : Seq μ) (p : MvPolynomial (Fin m) k) {ρ : List ℕ}
    (hρ : ValidWord m ρ) :
    gE c Λ' (wordProd m ρ • s) *
        splitHom c Q Λ' ν (π (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e s)) =
      splitHom c Q Λ' ν (π (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e s)) ∧
    (splitHom c Q Λ' ν (π (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e s))).val =
      π' (KLRAlgebra.ψw (expandWord c s ρ) * KLRAlgebra.pol (rename (splitPos c s) p) *
        KLRAlgebra.e (splitLoading c s)) := by
  induction ρ with
  | nil =>
    have h0 : splitHom c Q Λ' ν (π (KLRAlgebra.ψw [] * KLRAlgebra.pol p * KLRAlgebra.e s)) =
        polSplit c Λ' p * gE c Λ' s := by
      rw [KLRAlgebra.ψw_nil, one_mul, map_mul, map_mul, ← splitHom_polA,
        show π (KLRAlgebra.e s) = StendhalAlgebraAllOrders.e s from rfl, splitHom_e]
      rfl
    rw [h0]
    refine ⟨?_, ?_⟩
    · rw [wordProd_nil, one_smul, polSplit_mul_gE, ← mul_assoc, gE_mul_gE, ite_eq_left_of_eq_true _ _ (eq_self _)]
    · rw [val_polSplit_mul_gE, expandWord_nil, KLRAlgebra.ψw_nil, one_mul, map_mul]
      rfl
  | cons j ρ ih =>
    obtain ⟨hj, hρ'⟩ := validWord_cons.1 hρ
    obtain ⟨ih1, ih2⟩ := ih hρ'
    have hsplit : splitHom c Q Λ' ν
        (π (KLRAlgebra.ψw (j :: ρ) * KLRAlgebra.pol p * KLRAlgebra.e s)) =
        gΨ c Λ' j * splitHom c Q Λ' ν
          (π (KLRAlgebra.ψw ρ * KLRAlgebra.pol p * KLRAlgebra.e s)) := by
      rw [KLRAlgebra.ψw_cons, mul_assoc, mul_assoc, map_mul, map_mul, ← mul_assoc,
        show π (KLRAlgebra.ψ j) = StendhalAlgebraAllOrders.ψ j from rfl, splitHom_ψ]
    rw [hsplit]
    refine ⟨?_, ?_⟩
    · rw [wordProd_cons, mul_smul]
      exact gE_mul_gΨ_mul c Λ' j _ ih1
    · rw [val_gΨ_mul c Λ' j hj _ ih1, ih2, W_eq_ofKLR, ← map_mul, expandWord_cons,
        KLRAlgebra.ψw_append, mul_assoc, mul_assoc, mul_assoc]

/-! ### The splitting map on red-ordered diagrams -/

local notation "P" => StendhalAlgebraAllOrders.redOrderedIdem k Q (mergeWeights c Λ') ν
local notation "P'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν

open Classical in
private theorem val_splitHom_redOrderedIdem :
    (splitHom c Q Λ' ν P).val =
      ∑ s ∈ Finset.univ.filter (fun s : Seq μ => IsRedOrdered s),
        StendhalAlgebraAllOrders.e (Q := Q) (Λ := Λ') (splitLoading c s) := by
  rw [StendhalAlgebraAllOrders.redOrderedIdem, map_sum, Corner.val_sum]
  simp only [splitHom_e, val_gE]

private theorem redOrderedIdem_mul_splitHom :
    P' * (splitHom c Q Λ' ν P).val = (splitHom c Q Λ' ν P).val ∧
      (splitHom c Q Λ' ν P).val * P' = (splitHom c Q Λ' ν P).val := by
  classical
  rw [val_splitHom_redOrderedIdem, Finset.mul_sum, Finset.sum_mul]
  constructor <;> refine Finset.sum_congr rfl fun s hs => ?_
  · rw [StendhalAlgebraAllOrders.redOrderedIdem_mul_e]
    simp only [(isRedOrdered_splitLoading_iff c s).2 (Finset.mem_filter.1 hs).2, ↓reduceIte]
  · rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
    simp only [(isRedOrdered_splitLoading_iff c s).2 (Finset.mem_filter.1 hs).2, ↓reduceIte]

private theorem val_splitHom_mem_corner (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    (splitHom c Q Λ' ν z.val).val ∈ Subsemigroup.corner P' := by
  obtain ⟨hl, hr⟩ := redOrderedIdem_mul_splitHom c (Q := Q) Λ' (ν := ν)
  apply (Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).2
  have h1 : (splitHom c Q Λ' ν z.val).val =
      (splitHom c Q Λ' ν P).val * (splitHom c Q Λ' ν z.val).val := by
    rw [← Corner.val_mul, ← map_mul, Corner.E_mul_val]
  have h2 : (splitHom c Q Λ' ν z.val).val =
      (splitHom c Q Λ' ν z.val).val * (splitHom c Q Λ' ν P).val := by
    rw [← Corner.val_mul, ← map_mul, Corner.val_mul_E]
  constructor
  · rw [h1, ← mul_assoc, hl]
  · rw [h2, mul_assoc, hr]

variable (Q ν) in
/-- Webster, arXiv:1309.3796v3, Proposition 4.21: splitting the red strand `λ_c` on red-ordered
diagrams, `T̃^λ → T̃^{λ'}`, before quotienting by the violating ideals. -/
def splitStendhalValue :
    StendhalAlgebra k Q (mergeWeights c Λ') ν →ₙ+* StendhalAlgebra k Q Λ' ν where
  toFun z := ⟨(splitHom c Q Λ' ν z.val).val, val_splitHom_mem_corner c Λ' z⟩
  map_zero' := Subtype.ext (by
    change (splitHom c Q Λ' ν 0).val = 0
    rw [map_zero]; rfl)
  map_add' x y := Subtype.ext (by
    change (splitHom c Q Λ' ν (x.val + y.val)).val =
      (splitHom c Q Λ' ν x.val).val + (splitHom c Q Λ' ν y.val).val
    rw [map_add]; rfl)
  map_mul' x y := Subtype.ext (by
    change (splitHom c Q Λ' ν (x.val * y.val)).val =
      (splitHom c Q Λ' ν x.val).val * (splitHom c Q Λ' ν y.val).val
    rw [map_mul, Corner.val_mul])

theorem splitStendhalValue_val (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    (splitStendhalValue c Q Λ' ν z).val = (splitHom c Q Λ' ν z.val).val := rfl

theorem val_splitHom_smul (a : k) (u : StendhalAlgebraAllOrders k Q (mergeWeights c Λ') ν) :
    (splitHom c Q Λ' ν (a • u)).val = a • (splitHom c Q Λ' ν u).val := by
  rw [AlgHom.map_smul_of_tower, Corner.val_smul]

section Smul

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

theorem splitStendhalValue_smul (a : k) (z : StendhalAlgebra k Q (mergeWeights c Λ') ν) :
    splitStendhalValue c Q Λ' ν (a • z) = a • splitStendhalValue c Q Λ' ν z := by
  apply Subtype.ext
  change (splitHom c Q Λ' ν (a • z.val)).val = a • (splitHom c Q Λ' ν z.val).val
  exact val_splitHom_smul c Λ' a z.val

end Smul

theorem splitStendhalValue_e (s : Seq μ) (hs : IsRedOrdered s) :
    splitStendhalValue c Q Λ' ν (StendhalAlgebra.e s hs) =
      StendhalAlgebra.e (splitLoading c s) ((isRedOrdered_splitLoading_iff c s).2 hs) := by
  apply Subtype.ext
  change (splitHom c Q Λ' ν (StendhalAlgebraAllOrders.e s)).val = _
  rw [splitHom_e]
  rfl

/-! ### Expanded words exchanging no two red strands -/

/-- The letters of one crossing exchange no two red strands only if the crossing exchanges no
two red strands. -/
theorem isLeft_of_noRedCross_wLetters (t : Seq μ) {j : ℕ} (hj : j + 1 < m)
    (h : NoRedCross (wLetters j (redPos c t)) (splitLoading c t)) :
    (t.1 ⟨j, by omega⟩).isLeft ∨ (t.1 ⟨j + 1, hj⟩).isLeft := by
  have hm' := m'_eq (ν := ν) (ℓ := ℓ)
  unfold wLetters at h
  split_ifs at h with h1 h2 h3
  · have h' := h.2 (by omega)
    simp only [wordProd_nil, one_smul] at h'
    rwa [splitPos_eq_of_le c t (a := j) (by omega), splitPos_eq_of_le c t (a := j + 1) (by omega),
      isLeft_splitLoading_splitPos, isLeft_splitLoading_splitPos] at h'
  · have h' := h.1.2 (by omega)
    simp only [wordProd_nil, one_smul] at h'
    rw [splitPos_eq_of_le c t (a := j) (by omega), splitPos_eq_of_le c t (a := j + 1) (by omega),
      isLeft_splitLoading_splitPos, isLeft_splitLoading_splitPos] at h'
    exact h'
  · have h' := h.1.2 (by omega)
    simp only [wordProd_nil, one_smul] at h'
    rcases h' with h' | h'
    · rw [show (splitLoading c t).1 ⟨j + 1, by omega⟩ = (splitLoading c t).1 (newPos c t) from
        congrArg _ (Fin.ext (by rw [newPos_val]; show j + 1 = _; omega)), isLeft_splitLoading_newPos] at h'
      exact absurd h' (by simp)
    · right
      rwa [splitPos_eq_of_lt c t (a := j + 1) (by omega) hj, isLeft_splitLoading_splitPos] at h'
  · have h' := h.2 (by omega)
    simp only [wordProd_nil, one_smul] at h'
    rwa [splitPos_eq_of_lt c t (a := j) (by omega) (by omega),
      splitPos_eq_of_lt c t (a := j + 1) (by omega) hj,
      isLeft_splitLoading_splitPos, isLeft_splitLoading_splitPos] at h'

/-- **An expanded word exchanges no two red strands only if the word does.** -/
theorem noRedCross_of_expandWord (s : Seq μ) {ρ : List ℕ} (hv : ValidWord m ρ)
    (h : NoRedCross (expandWord c s ρ) (splitLoading c s)) : NoRedCross ρ s := by
  induction ρ with
  | nil => trivial
  | cons j ρ ih =>
    rw [validWord_cons] at hv
    rw [expandWord_cons, noRedCross_append, ← splitLoading_wordProd c s hv.2] at h
    exact ⟨ih hv.2 h.2, fun hj => isLeft_of_noRedCross_wLetters c _ hj h.1⟩

/-! ### Loading-dependent reduced words -/

/-- The permutation of the split loading induced by `w`, through the expanded word. -/
private def gw (s : Seq μ) (w : Perm (Fin m)) : Perm (Fin m') :=
  wordProd m' (expandWord c s (canWord m w))

private theorem gw_apply_splitPos (s : Seq μ) (w : Perm (Fin m)) (a : Fin m) :
    gw c s w (splitPos c s a) = splitPos c (w • s) (w a) := by
  rw [gw, wordProd_expandWord_splitPos c s (validWord_canWord m w), wordProd_canWord]

private theorem gw_apply_newPos (s : Seq μ) (w : Perm (Fin m)) :
    gw c s w (newPos c s) = newPos c (w • s) := by
  rw [gw, wordProd_expandWord_newPos c s (validWord_canWord m w), wordProd_canWord]

private theorem gw_injective (s : Seq μ) : Function.Injective (gw c s) := by
  intro w₁ w₂ h
  have hr : (redPos c (w₁ • s) : ℕ) = redPos c (w₂ • s) := by
    have := congrArg (fun g : Perm (Fin m') => (g (newPos c s) : ℕ)) h
    simp only [gw_apply_newPos, newPos_val] at this
    omega
  refine Equiv.ext fun a => Fin.ext ?_
  have := congrArg (fun g : Perm (Fin m') => (g (splitPos c s a) : ℕ)) h
  simp only [gw_apply_splitPos, splitPos_val, hr] at this
  split_ifs at this <;> omega

/-- A permutation carrying one split loading to another comes from a permutation of the
unsplit loadings. -/
private theorem exists_gw (s t : Seq μ) (w : Perm (Fin m'))
    (h : w • splitLoading c s = splitLoading c t) : ∃ v : Perm (Fin m), v • s = t ∧ gw c s v = w := by
  have hlbl : ∀ b, (splitLoading c t).lbl (w b) = (splitLoading c s).lbl b := by
    intro b
    rw [← h]
    simp [Seq.lbl]
  have hnew : w (newPos c s) = newPos c t := by
    rcases eq_newPos_or_splitPos c t (w (newPos c s)) with h' | ⟨a, ha⟩
    · exact h'
    · exfalso
      have := hlbl (newPos c s)
      rw [ha, splitLoading_lbl_splitPos, splitLoading_lbl_newPos] at this
      exact splitColor_ne_new c _ this
  have hsp : ∀ a, ∃ a', w (splitPos c s a) = splitPos c t a' := by
    intro a
    rcases eq_newPos_or_splitPos c t (w (splitPos c s a)) with h' | h'
    · exact absurd (w.injective (h'.trans hnew.symm)) (splitPos_ne_newPos c s a)
    · exact h'
  choose f hf using hsp
  have hfinj : Function.Injective f := fun a b hab =>
    splitPos_injective c s (w.injective ((hf a).trans ((congrArg _ hab).trans (hf b).symm)))
  let v : Perm (Fin m) := Equiv.ofBijective f hfinj.bijective_of_finite
  have hvs : v • s = t := by
    apply Subtype.ext
    funext a'
    obtain ⟨a, rfl⟩ := v.surjective a'
    rw [Seq.smul_apply, v.symm_apply_apply]
    apply splitColor_injective c
    have := hlbl (splitPos c s a)
    rw [hf a, splitLoading_lbl_splitPos, splitLoading_lbl_splitPos] at this
    exact this.symm
  refine ⟨v, hvs, Equiv.ext fun b => ?_⟩
  rcases eq_newPos_or_splitPos c s b with rfl | ⟨a, rfl⟩
  · rw [gw_apply_newPos, hvs, hnew]
  · rw [gw_apply_splitPos, hvs, hf]
    rfl

/-- Reduced words for the permutations of the split loadings of `s`: expanded words on the image
of `gw`, canonical words elsewhere. -/
private def ρs (s : Seq μ) : Perm (Fin m') → List ℕ :=
  Function.extend (gw c s) (fun w => expandWord c s (canWord m w)) (canWord m')

private theorem ρs_gw (s : Seq μ) (w : Perm (Fin m)) :
    ρs c s (gw c s w) = expandWord c s (canWord m w) :=
  (gw_injective c s).extend_apply _ _ w

private theorem ρs_spec (s : Seq μ) (w : Perm (Fin m')) :
    IsReduced m' (ρs c s w) ∧ wordProd m' (ρs c s w) = w := by
  classical
  by_cases h : ∃ v, gw c s v = w
  · obtain ⟨v, rfl⟩ := h
    rw [ρs_gw]
    exact ⟨isReduced_expandWord c s (isReduced_canWord m v), rfl⟩
  · rw [ρs, Function.extend_apply' _ _ _ h]
    exact ⟨isReduced_canWord m' w, wordProd_canWord m' w⟩

/-! ### Stendhal terms -/

local notation "OldTerm" => {b // IsStendhalTerm (ν := ν) (ℓ := ℓ) (canWord m) b}

private def splitPosEmb (s : Seq μ) : Fin m ↪ Fin m' := ⟨splitPos c s, splitPos_injective c s⟩

/-- The data of the split Stendhal term. -/
private def splitData (b : Seq μ × Perm (Fin m) × (Fin m →₀ ℕ)) :
    Seq (stendhalWeight (ℓ + 1) ν) × Perm (Fin m') × (Fin m' →₀ ℕ) :=
  (splitLoading c b.1, gw c b.1 b.2.1, Finsupp.embDomain (splitPosEmb c b.1) b.2.2)

private theorem isStendhalTerm_splitData (b : OldTerm) :
    IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) (ρs c b.1.1) (splitData c b.1) := by
  obtain ⟨⟨s, w, d⟩, h1, h2, h3, h4⟩ := b
  refine ⟨(isRedOrdered_splitLoading_iff c s).2 h1, ?_, ?_, ?_⟩
  · change IsRedOrdered (gw c s w • splitLoading c s)
    rw [gw, ← splitLoading_wordProd c s (validWord_canWord m w), wordProd_canWord]
    exact (isRedOrdered_splitLoading_iff c _).2 h2
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 ha
    change ((splitLoading c s).1 (splitPos c s x)).isLeft
    rw [isLeft_splitLoading_splitPos]
    exact h3 x hx
  · change NoRedCross (ρs c s (gw c s w)) (splitLoading c s)
    rw [ρs_gw]
    exact noRedCross_expandWord c s (validWord_canWord m w) h4

/-- The split Stendhal term of a Stendhal term with bottom loading `s`. -/
private def splitTerm (s : Seq μ) (b : {b : OldTerm // b.1.1 = s}) :
    {x // IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) (ρs c s) x} :=
  ⟨splitData c b.1.1, (congrArg (fun t => IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) (ρs c t)
    (splitData c b.1.1)) b.2).mp (isStendhalTerm_splitData c b.1)⟩

private theorem splitTerm_injective (s : Seq μ) :
    Function.Injective (splitTerm c (ν := ν) s) := by
  intro x y h
  obtain ⟨⟨⟨s₁, w₁, d₁⟩, h₁⟩, e₁⟩ := x
  obtain ⟨⟨⟨s₂, w₂, d₂⟩, h₂⟩, e₂⟩ := y
  dsimp only at e₁ e₂
  subst e₁ e₂
  have h' := congrArg (fun z => z.1) h
  simp only [splitTerm, splitData, Prod.mk.injEq] at h'
  obtain ⟨-, hw, hd⟩ := h'
  obtain rfl := gw_injective c _ hw
  obtain rfl := Finsupp.embDomain_injective _ hd
  rfl

section Independence

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

set_option quotPrecheck false in
local notation "oldB" => stendhalTerm Q (mergeWeights c Λ') (ν := ν) (wordProd_canWord m)
set_option quotPrecheck false in
local notation "newB" s => stendhalTerm Q Λ' (ν := ν) (fun w => (ρs_spec c s w).2)

private theorem splitTerm_value (b : OldTerm) :
    splitStendhalValue c Q Λ' ν (oldB b) = (newB b.1.1) (splitTerm c b.1.1 ⟨b, rfl⟩) := by
  apply Subtype.ext
  rw [splitStendhalValue_val, stendhalTerm_val, stendhalTerm_val, KLRAlgebra.stdElt,
    (splitHom_word c Λ' b.1.1 (monomial b.1.2.2 1) (validWord_canWord m b.1.2.1)).2]
  change _ = π' (KLRAlgebra.ψw (ρs c b.1.1 (gw c b.1.1 b.1.2.1)) *
    KLRAlgebra.pol (monomial (Finsupp.embDomain (splitPosEmb c b.1.1) b.1.2.2) 1) *
      KLRAlgebra.e (splitLoading c b.1.1))
  rw [ρs_gw, rename_monomial, Finsupp.embDomain_eq_mapDomain]
  rfl

private theorem splitStendhalValue_injective_of_independent
    (hB : ∀ s : Seq μ, LinearIndependent k (newB s)) :
    Function.Injective (splitStendhalValue c Q Λ' ν) := by
  classical
  let f : StendhalAlgebra k Q (mergeWeights c Λ') ν →ₗ[k] StendhalAlgebra k Q Λ' ν :=
    { toFun := splitStendhalValue c Q Λ' ν, map_add' := map_add _,
      map_smul' := splitStendhalValue_smul c Λ' }
  have hall := span_stendhalTerm (Q := Q) (Λ := mergeWeights c Λ') (ν := ν)
    (fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩)
  apply LinearMap.injective_of_linearIndependent (f := f) (v := oldB) (top_unique hall)
  have he : f ∘ oldB = fun b => (newB b.1.1) (splitTerm c b.1.1 ⟨b, rfl⟩) :=
    funext (splitTerm_value c Λ')
  rw [he]
  let Pr : Seq μ → StendhalAlgebra k Q Λ' ν →ₗ[k] StendhalAlgebra k Q Λ' ν := fun s =>
    if hs : IsRedOrdered s then
      LinearMap.mulRight k
        (StendhalAlgebra.e (splitLoading c s) ((isRedOrdered_splitLoading_iff c s).2 hs))
    else 0
  refine linearIndependent_of_projections _ (fun b : OldTerm => b.1.1) Pr
    (fun s b => ?_) (fun s => ?_)
  · by_cases hs : IsRedOrdered s
    · simp only [Pr, hs, ↓reduceDIte, LinearMap.mulRight_apply]
      rw [stendhalTerm_mul_e]
      exact if_congr (splitLoading_injective c).eq_iff rfl rfl
    · have hb : b.1.1 ≠ s := fun h => hs (h ▸ b.2.1)
      simp only [Pr, hs, ↓reduceDIte, LinearMap.zero_apply, hb, ↓reduceIte]
  · convert (hB s).comp _ (splitTerm_injective c s) using 1
    funext ⟨i, hi⟩
    subst hi
    rfl

/-- Target PBW independence, for any family of reduced expressions, detects the kernel of
splitting a red strand on red-ordered diagrams (Webster, arXiv:1309.3796v3, Propositions 4.16
and 4.21). -/
theorem splitStendhalValue_injective_of_stendhalTerm
    (hB : ∀ (ρ : Perm (Fin m') → List ℕ) (hρ : ∀ w, IsReduced m' (ρ w) ∧ wordProd m' (ρ w) = w),
      LinearIndependent k (stendhalTerm Q Λ' (ν := ν) (fun w => (hρ w).2))) :
    Function.Injective (splitStendhalValue c Q Λ' ν) :=
  splitStendhalValue_injective_of_independent c Λ' (fun s => hB _ (ρs_spec c s))

/-- **Splitting a red strand is injective on red-ordered diagrams** for the crossing parameters
of Webster, arXiv:1309.3796v3, §2.2 (Propositions 4.16 and 4.21). -/
theorem splitStendhalValue_injective {D : QuantumGroup.CartanDatum I} (hQ : IsRouquierQ D Q) :
    Function.Injective (splitStendhalValue c Q Λ' ν) :=
  splitStendhalValue_injective_of_stendhalTerm c Λ'
    (fun _ hρ => linearIndependent_stendhalTerm_of_rouquier Q ν Λ' hQ hρ)

/-- Every Stendhal term of `T̃^{λ'}` from one split loading to another is the split of a Stendhal
term of `T̃^λ`. -/
private theorem exists_stendhalTerm_eq (s t : Seq μ)
    (b : {x // IsStendhalTerm (ν := ν) (ℓ := ℓ + 1) (ρs c s) x})
    (hb1 : b.1.1 = splitLoading c s) (hb2 : b.1.2.1 • b.1.1 = splitLoading c t) :
    ∃ b₀ : OldTerm, (newB s) b = splitStendhalValue c Q Λ' ν (oldB b₀) := by
  classical
  obtain ⟨⟨s', w, d⟩, hb⟩ := b
  dsimp only at hb1 hb2
  subst hb1
  obtain ⟨hr1, hr2, hdot, hcross⟩ := hb
  obtain ⟨v, hvs, rfl⟩ := exists_gw c s t w hb2
  have hsupp : ↑d.support ⊆ Set.range (splitPosEmb c s) := by
    intro x hx
    rcases eq_newPos_or_splitPos c s x with rfl | ⟨a, rfl⟩
    · have := hdot _ hx
      rw [isLeft_splitLoading_newPos] at this
      exact absurd this (by simp)
    · exact ⟨a, rfl⟩
  let d₀ : Fin m →₀ ℕ := d.comapDomain (splitPos c s) (splitPos_injective c s).injOn
  have hd : Finsupp.embDomain (splitPosEmb c s) d₀ = d := Finsupp.embDomain_comapDomain hsupp
  have h0 : IsStendhalTerm (ν := ν) (ℓ := ℓ) (canWord m) (s, v, d₀) := by
    refine ⟨(isRedOrdered_splitLoading_iff c s).1 hr1, ?_, ?_, ?_⟩
    · change IsRedOrdered (v • s)
      rw [hvs, ← isRedOrdered_splitLoading_iff c t, ← hb2]
      exact hr2
    · intro a ha
      have := hdot (splitPos c s a) (by simpa [d₀] using ha)
      rwa [isLeft_splitLoading_splitPos] at this
    · change NoRedCross (ρs c s (gw c s v)) (splitLoading c s) at hcross
      rw [ρs_gw] at hcross
      exact noRedCross_of_expandWord c s (validWord_canWord m v) hcross
  refine ⟨⟨(s, v, d₀), h0⟩, ?_⟩
  rw [splitTerm_value]
  congr 1
  apply Subtype.ext
  change _ = (splitLoading c s, gw c s v, Finsupp.embDomain (splitPosEmb c s) d₀)
  rw [hd]

/-- **Splitting a red strand is onto the corner of the split idempotents** (Webster,
arXiv:1309.3796v3, Proposition 4.21): `e(t') y e(s')` lies in the image of the splitting map
for all split loadings `s'`, `t'` of red-ordered loadings. -/
theorem e_mul_mul_e_mem_range_splitStendhalValue (s t : Seq μ) (hs : IsRedOrdered s)
    (ht : IsRedOrdered t) (y : StendhalAlgebra k Q Λ' ν) :
    StendhalAlgebra.e (splitLoading c t) ((isRedOrdered_splitLoading_iff c t).2 ht) * y *
        StendhalAlgebra.e (splitLoading c s) ((isRedOrdered_splitLoading_iff c s).2 hs) ∈
      Set.range (splitStendhalValue c Q Λ' ν) := by
  classical
  let f : StendhalAlgebra k Q (mergeWeights c Λ') ν →ₗ[k] StendhalAlgebra k Q Λ' ν :=
    { toFun := splitStendhalValue c Q Λ' ν, map_add' := map_add _,
      map_smul' := splitStendhalValue_smul c Λ' }
  suffices hf : _ ∈ LinearMap.range f by
    obtain ⟨z, hz⟩ := hf
    exact ⟨z, hz⟩
  have hy := span_stendhalTerm (Q := Q) (Λ := Λ') (ν := ν) (ρs_spec c s) (Submodule.mem_top (x := y))
  refine Submodule.span_induction (p := fun y _ => StendhalAlgebra.e (splitLoading c t)
      ((isRedOrdered_splitLoading_iff c t).2 ht) * y * StendhalAlgebra.e (splitLoading c s)
      ((isRedOrdered_splitLoading_iff c s).2 hs) ∈ LinearMap.range f) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, rfl⟩
    rw [mul_assoc, stendhalTerm_mul_e]
    split_ifs with h1
    · rw [e_mul_stendhalTerm]
      split_ifs with h2
      · obtain ⟨b₀, hb₀⟩ := exists_stendhalTerm_eq c (k := k) (Q := Q) Λ' s t b h1 (h1 ▸ h2)
        exact ⟨oldB b₀, hb₀.symm⟩
      · exact Submodule.zero_mem _
    · rw [mul_zero]
      exact Submodule.zero_mem _
  · rw [mul_zero, zero_mul]
    exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [mul_add, add_mul]
    exact Submodule.add_mem _ hx hz
  · intro a x _ hx
    rw [mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ a hx

end Independence

end SplitRed

end Categorification.Stendhal
