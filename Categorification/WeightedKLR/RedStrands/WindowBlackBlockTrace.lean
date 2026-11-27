/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.WindowBlackBlockFree
import Categorification.KLR.MackeyTopDots

/-!
# The trace `c` on the end corner, and the lower step of the Mackey filtration

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, the induction–coinduction identity (IC),
step 2: the coefficient `c(z) ∈ D` of the longest block crossing. By (B3-L)
(`blockSumEquiv`), an element `z` of the end corner `e_L T̃^{λ⁺}` is `∑_c ι(d_c) γ_c` with unique
`d_c ∈ D 1_c`, `D = T̃^λ ⊗ T̃^{(μ,μ*)}`. The **trace** `blockTrace z` is the sum of the `d_c` over
the base generators `c = (e(i), j, u)` whose shuffle `u` takes all `m` strands of `λ` across the
strands at the maximum (`crossCount m N u = m`, the double coset of the longest block crossing
`w_L` in Khovanov–Lauda's Mackey filtration). On all of `T̃^{λ⁺}` it is `z ↦ c(e_L z)`.

* It is left `D`-linear: `c(ι(d) z) = d c(z)` (`blockTrace_blockTensor_mul`).
* It vanishes on every element whose coordinates in the basis with dots on top vanish at the
  permutations with `m` crossing strands (`blockTrace_eq_zero_of_repr`). In particular it
  vanishes on the image of the lower step `F_{m-1}` of the Mackey filtration of the KLR algebra
  of `λ⁺` (`blockTrace_botMap_eq_zero`), for the blocks `(m, N)` at the top and `(N, m)` at the
  bottom: the span of the diagrams all of whose subword products take fewer than `m` strands
  from the second bottom block to the first top block.

The second point is the double-coset refinement of the Bruhat bound (B2) that (IC) needs: by
`KLRAlgebra.lbasis_repr_eq_zero_of_mem_mackeyFilt` the KLR coordinates of an element of `F_{m-1}`
vanish at the permutations with `m` crossing strands, and the quotient map to `T̃^{λ⁺}` sends
the basis with dots on top to the basis with dots on top (`topBasis_repr_topMap`).

Symmetric `Q`, any commutative ring.

## Main definitions

* `CupCap.blockTrace`: the trace `T̃^{λ⁺} → D`.

## Main results

* `Stendhal.topBasis_repr_topMap`: the coordinates of the image of a KLR element.
* `CupCap.blockTrace_blockSum`, `CupCap.blockTrace_blockTensor_mul`,
  `CupCap.blockTrace_eq_zero_of_repr`, `CupCap.blockTrace_botMap_eq_zero`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv MvPolynomial StendhalAlgebraAllOrders
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-! ### The quotient map in the bases with dots on top -/

section TopMap

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

theorem topMap_topElt_of_not {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
    (hρ : ∀ w, wordProd m (ρ w) = w)
    {b : KLR.Seq (stendhalWeight ℓ ν) × Perm (Fin m) × (Fin m →₀ ℕ)}
    (hb : ¬ IsTopTerm ρ b) : CupCap.topMap k Q Λ ν (topElt ρ b) = 0 := by
  apply Subtype.ext
  change ofKLR k Q Λ ν _ * redOrderedIdem k Q Λ ν = 0
  have h := ro_mul_ofKLR_topElt_mul_ro (Q := Q) (Λ := Λ) hρ b
  rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at h
  have hE := isIdempotentElem_redOrderedIdem (k := k) (Q := Q) (Λ := Λ) (ν := ν)
  rw [(redOrderedIdem_commute Q Λ ν _).eq, mul_assoc, hE.eq] at h
  exact h

/-- **Coordinates of the image of a KLR element.** The coordinate of the image of `y` at a basis
term `x^u ψ_{ρ w} e(i)` of `T̃^λ` with dots on top is the coordinate of `y` at the same term of
the basis of the KLR algebra with dots on top. -/
theorem topBasis_repr_topMap (hQ : KLRSymm Q)
    (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (y : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) (b : {b // IsTopTerm (ν := ν) ρ b}) :
    (topBasis Q Λ hQ ρ hρ).repr (CupCap.topMap k Q Λ ν y) b =
      (lbasis (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ).repr y b.1 := by
  classical
  set B := lbasis (stendhalQ_symm (Q := Q) (Λ := Λ) hQ) ρ hρ
  have h : (Finsupp.lapply b ∘ₗ (topBasis Q Λ hQ ρ hρ).repr.toLinearMap ∘ₗ
      (CupCap.topMap k Q Λ ν).toLinearMap) = Finsupp.lapply b.1 ∘ₗ B.repr.toLinearMap := by
    refine B.ext fun b' => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AlgHom.toLinearMap_apply, Finsupp.lapply_apply, Module.Basis.repr_self]
    rw [lbasis_apply]
    change (topBasis Q Λ hQ ρ hρ).repr (CupCap.topMap k Q Λ ν (topElt ρ b')) b = _
    by_cases hb' : IsTopTerm ρ b'
    · rw [CupCap.topMap_topElt (fun w => (hρ w).2) ⟨b', hb'⟩, ← topBasis_apply hQ ρ hρ,
        Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      by_cases he : b' = b.1
      · subst he
        simp
      · have he' : ¬ (⟨b', hb'⟩ : {b // IsTopTerm ρ b}) = b :=
          fun h => he (congrArg Subtype.val h)
        simp [he, he']
    · rw [topMap_topElt_of_not (fun w => (hρ w).2) hb', map_zero, Finsupp.zero_apply,
        Finsupp.single_apply]
      have he : ¬ b' = b.1 := by rintro rfl; exact hb' b.2
      simp [he]
  exact LinearMap.congr_fun h y

end TopMap

namespace CupCap

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀)
local notation "hM" => m_add_N_end (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

variable {ρ₁ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν₀))) → List ℕ}
  {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) → List ℕ}

/-! ### The trace -/

theorem endStendhal_one_mul_self :
    endStendhal Q Λ Λc ν ν₀ 1 * endStendhal Q Λ Λc ν ν₀ 1 = endStendhal Q Λ Λc ν ν₀ 1 := by
  rw [← map_mul, one_mul]

variable (Q Λ Λc ν ν₀) in
/-- The projection `z ↦ e_L z` onto the end corner. -/
def endProj : Tp →ₗ[k] endCorner Q Λ Λc ν ν₀ :=
  (LinearMap.mulLeft k (endStendhal Q Λ Λc ν ν₀ 1)).codRestrict (endCorner Q Λ Λc ν ν₀)
    fun z => by
      change _ * (_ * z) = _ * z
      rw [← mul_assoc, endStendhal_one_mul_self]

theorem endProj_apply (z : Tp) :
    (endProj Q Λ Λc ν ν₀ z : Tp) = endStendhal Q Λ Λc ν ν₀ 1 * z := rfl

variable [DecidableEq (EndGen ν₀ ρ₁)]

variable (Q Λ Λc ρ₁) in
/-- The sum of the components `d_c` over the base generators `c = (e(i), j, u)` whose shuffle `u`
takes all `m` strands of `λ` across the strands at the maximum. -/
def traceSum : (Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) →ₗ[k] T ⊗[k] Tc :=
  DFinsupp.lsum ℕ fun c =>
    if crossCount m N c.1.1.2.2.1 = m then (blockLeft Q Λ Λc c).subtype.restrictScalars k
    else 0

theorem traceSum_single (c : BaseGen ν₀ ρ₁) (a : blockLeft Q Λ Λc c) :
    traceSum Q Λ Λc ρ₁ (DFinsupp.single c a) =
      if crossCount m N c.1.1.2.2.1 = m then (a : T ⊗[k] Tc) else 0 := by
  rw [traceSum, DFinsupp.lsum_single]
  split_ifs <;> rfl

theorem traceSum_blockLeftMul (d : T ⊗[k] Tc) (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    traceSum Q Λ Λc ρ₁ (blockLeftMul Q Λ Λc d a) = d * traceSum Q Λ Λc ρ₁ a := by
  have h : (traceSum Q Λ Λc ρ₁).comp (blockLeftMul Q Λ Λc d) =
      (LinearMap.mulLeft k d).comp (traceSum Q Λ Λc ρ₁) := by
    refine DFinsupp.lhom_ext' fun c => LinearMap.ext fun b => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, DFinsupp.lsingle_apply, blockLeftMul,
      DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mulLeft_apply]
    rw [traceSum_single, traceSum_single]
    split_ifs
    · rfl
    · rw [mul_zero]
  exact LinearMap.congr_fun h a

variable (Q Λ Λc ρ₁ ρ₃) in
/-- **The trace** `c : T̃^{λ⁺} → D`, `z ↦ ∑_{c full} d_c` where `e_L z = ∑_c ι(d_c) γ_c`
(`blockSumEquiv`) and `c = (e(i), j, u)` runs over the base generators whose shuffle moves all
strands of `λ` across the strands at the maximum. -/
def blockTrace (hQ : KLRSymm Q)
    (hρ₁ : ∀ a, IsReduced m (ρ₁ a) ∧ wordProd m (ρ₁ a) = a)
    (hρ₂ : ∀ b, IsReduced N (ρ₂ b) ∧ wordProd N (ρ₂ b) = b)
    (hρ₃ : ∀ w, IsReduced M (ρ₃ w) ∧ wordProd M (ρ₃ w) = w) : Tp →ₗ[k] T ⊗[k] Tc :=
  traceSum Q Λ Λc ρ₁ ∘ₗ (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm.toLinearMap ∘ₗ
    endProj Q Λ Λc ν ν₀

section Trace

variable (hQ : KLRSymm Q)
  (hρ₁ : ∀ a, IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ₁ a) ∧
    wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) ∧
    wordProd (Multiset.card (stendhalWeight 2 ν₀)) (ρ₂ b) = b)
  (hρ₃ : ∀ w, IsReduced (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))) (ρ₃ w) ∧
    wordProd (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))) (ρ₃ w) = w)

include hQ hρ₁ hρ₂ hρ₃

/-- The components of `e_L z`. -/
private theorem symm_endProj_eq {z : Tp} {a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c}
    (h : endStendhal Q Λ Λc ν ν₀ 1 * z = blockSum Q Λ Λc ρ₁ ρ₃ a) :
    (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm (endProj Q Λ Λc ν ν₀ z) = a := by
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext h

/-- **The trace of `∑_c ι(d_c) γ_c`** is the sum of the `d_c` over the generators with full
crossing. -/
theorem blockTrace_blockSum (a : Π₀ c : BaseGen ν₀ ρ₁, blockLeft Q Λ Λc c) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (blockSum Q Λ Λc ρ₁ ρ₃ a) = traceSum Q Λ Λc ρ₁ a := by
  simp only [blockTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [symm_endProj_eq hQ hρ₁ hρ₂ hρ₃ (endStendhal_one_mul_blockSum a)]

/-- **The trace is left `D`-linear**: `c(ι(d) z) = d c(z)`. -/
theorem blockTrace_blockTensor_mul (d : T ⊗[k] Tc) (z : Tp) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (blockTensor Q Λ Λc ν ν₀ d * z) =
      d * blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z := by
  set a := (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm (endProj Q Λ Λc ν ν₀ z)
  have ha : endStendhal Q Λ Λc ν ν₀ 1 * z = blockSum Q Λ Λc ρ₁ ρ₃ a := by
    rw [← blockSumEquiv_apply hQ hρ₁ hρ₂ hρ₃, LinearEquiv.apply_symm_apply, endProj_apply]
  have hd : endStendhal Q Λ Λc ν ν₀ 1 * (blockTensor Q Λ Λc ν ν₀ d * z) =
      blockSum Q Λ Λc ρ₁ ρ₃ (blockLeftMul Q Λ Λc d a) := by
    rw [← mul_assoc, endStendhal_one_mul_blockTensor, blockSum_blockLeftMul, ← ha, ← mul_assoc,
      blockTensor_mul_endStendhal_one]
  simp only [blockTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [symm_endProj_eq hQ hρ₁ hρ₂ hρ₃ hd, traceSum_blockLeftMul]

/-- **The trace vanishes off the full crossing**: if the coordinates of `e_L z` in the basis of
`T̃^{λ⁺}` with dots on top vanish at every permutation taking all strands of the first top block
to the second bottom block, then `c(z) = 0`. -/
theorem blockTrace_eq_zero_of_repr (z : Tp)
    (hz : ∀ b : {b // IsTopTerm (endWord ρ₁ ρ₂ ρ₃) b}, crossCount m N b.1.2.1 = m →
      (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
        (endWord_spec hρ₁ hρ₂ hρ₃)).repr (endStendhal Q Λ Λc ν ν₀ 1 * z) b = 0) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ z = 0 := by
  set BD := (topBasis Q Λ hQ ρ₁ hρ₁).tensorProduct (topBasis Q Λc hQ ρ₂ hρ₂)
  set a := (blockSumEquiv Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃).symm (endProj Q Λ Λc ν ν₀ z)
  have ha : endStendhal Q Λ Λc ν ν₀ 1 * z = blockSum Q Λ Λc ρ₁ ρ₃ a := by
    rw [← blockSumEquiv_apply hQ hρ₁ hρ₂ hρ₃, LinearEquiv.apply_symm_apply, endProj_apply]
  have hc : ∀ c : BaseGen ν₀ ρ₁, crossCount m N c.1.1.2.2.1 = m → a c = 0 := by
    intro c hfull
    refine Subtype.ext (BD.ext_elem fun xy => ?_)
    obtain ⟨x, y⟩ := xy
    rw [ZeroMemClass.coe_zero, map_zero, Finsupp.zero_apply]
    by_cases h : x.1.1 = c.1.1.1.1.1 ∧ y.1.1 = c.1.1.2.1
    · have hp := topBasis_repr_blockSum hQ hρ₁ hρ₂ hρ₃ a ⟨(liftGen c x h.1, y), h.2⟩
      rw [baseOf_liftGen hρ₁ c x h.1, ← ha] at hp
      refine hp.symm.trans (hz _ ?_)
      change crossCount m N (blockPerm hM x.1.2.1 y.1.2.1 * c.1.1.2.2.1) = m
      rw [crossCount_blockPerm_mul, hfull]
    · rw [← (mem_blockLeft.1 (a c).2), topBasis_repr_mul_blockIdem hQ hρ₁ hρ₂,
        ite_eq_right_of_eq_false _ _ (eq_false h)]
  simp only [blockTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  change traceSum Q Λ Λc ρ₁ a = 0
  classical
  rw [traceSum, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with hfull
  · simp [hc c hfull]
  · rfl

/-- **The trace vanishes on the lower step of the Mackey filtration**: for the blocks `(m, N)`
at the top and `(N, m)` at the bottom, `c` kills the image in `T̃^{λ⁺}` of `F_{m-1}`, the span of
the KLR diagrams all of whose subword products take fewer than `m` strands from the second
bottom block to the first top block. -/
theorem blockTrace_botMap_eq_zero
    (y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl)) (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (hy : y ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
      (stendhalWeight (ℓ + 2) (ν + ν₀)) m N m) :
    blockTrace Q Λ Λc ρ₁ ρ₃ hQ hρ₁ hρ₂ hρ₃ (botMap k Q Λ Λc ℓ le_rfl ν ν₀ y) = 0 := by
  classical
  set x := endMapKLR Q Λ Λc ν ν₀ (redOrderedKLR k Q Λc ν₀) * y
  have hx : x ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
      (stendhalWeight (ℓ + 2) (ν + ν₀)) m N m := by
    simp only [x, redOrderedKLR, endMapKLR_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [endMapKLR_e_eq_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun s _ => ?_
    have h := mackeyLower_eSum_mul {endSeq s t} hy
    rwa [eSum, Finset.sum_singleton] at h
  refine blockTrace_eq_zero_of_repr hQ hρ₁ hρ₂ hρ₃ _ fun b hb => ?_
  rw [endStendhal_one_eq_endBot, endBot_apply, ← map_mul]
  change (topBasis Q (plusLabels Λ Λc ℓ le_rfl) hQ (endWord ρ₁ ρ₂ ρ₃)
    (endWord_spec hρ₁ hρ₂ hρ₃)).repr (topMap k Q (plusLabels Λ Λc ℓ le_rfl) (ν + ν₀) x) b = 0
  rw [topBasis_repr_topMap]
  have key : ∀ c, x ∈ mackeyLower k (stendhalQ Q (plusLabels Λ Λc ℓ le_rfl))
      (stendhalWeight (ℓ + 2) (ν + ν₀)) m N c → c ≤ crossCount m N b.1.2.1 →
      (lbasis (stendhalQ_symm (Q := Q) (Λ := plusLabels Λ Λc ℓ le_rfl) hQ) (endWord ρ₁ ρ₂ ρ₃)
        (endWord_spec hρ₁ hρ₂ hρ₃)).repr x b.1 = 0 := by
    intro c
    cases c with
    | zero =>
      intro h _
      rw [mackeyLower_zero, Submodule.mem_bot] at h
      rw [h, map_zero, Finsupp.zero_apply]
    | succ c =>
      intro h hc
      rw [mackeyLower_succ] at h
      exact lbasis_repr_eq_zero_of_mem_mackeyFilt _ _ _ h _ hc
  exact key _ hx hb.ge

end Trace

end CupCap

end Categorification.Stendhal
