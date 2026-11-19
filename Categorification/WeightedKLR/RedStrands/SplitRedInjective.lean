/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedHom
import Categorification.WeightedKLR.RedStrands.SplitRedWords
import Categorification.WeightedKLR.RedStrands.StendhalParameters

/-!
# Splitting a red strand: injectivity before quotienting

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

end SplitRed

end Categorification.Stendhal
