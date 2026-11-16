/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.CrawleyBoeveyIn

/-!
# The reduced quotient acts faithfully on polynomials with no dot on `s₀`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §3.1: the reduced
quotient `W̄^ϑ_ν̃` of the weighted KLR algebra by the dots on a strand `s₀` alone in its colour
(`GalleryAlgebra.ReducedQuotient`).

The polynomial representation `V = (FullChamber Γ ν → k[y_s])` of the gallery algebra
(`galleryRep`, Webster's Proposition `prop:action`) commutes with multiplication by `y_{s₀}`,
since the dot on `s₀` is central (`GalleryAlgebra.commute_poly_X`). Hence it descends to
`V / y_{s₀} V` (`GalleryAlgebra.DotQuotient`), and on this quotient the ideal of dots on `s₀`
acts by zero: the reduced quotient acts on `V / y_{s₀} V` (`GalleryAlgebra.reducedRep`), and
`V / y_{s₀} V` is one copy, for each full chamber, of the polynomials in the variables other
than `y_{s₀}` (`GalleryAlgebra.mem_dotRange_iff`).

This action is **faithful**: the images of the basis `GalleryAlgebra.reducedBasis` of the reduced
quotient (the Theorem 2.8 basis elements with no dot on `s₀`) act by linearly independent
operators (`GalleryAlgebra.linearIndependent_reducedRep`), so `reducedRep` is injective. This is
the faithfulness used by the diagrammatic calculator, which decides equality in the reduced
quotient by computing in the polynomial representation with `y_{s₀}` set to `0`.

The proof is the leading-term argument of the independence half of Webster's Theorem 2.8
(`GalleryAlgebra.linearIndependent_basisElt`), after setting `y_{s₀} = 0` (`dotZero`). The
relabellings fix `s₀` and the crossings of strands of one colour do not involve `s₀`, so the
leading coefficients specialize to non-zero-divisors as soon as the wall polynomials do; the
hypothesis is that `Q_e(y_a, y_b)` with `y_{s₀} = 0` is a non-zero-divisor for every wall
(`hW₀`). For the Crawley-Boevey graph with new edges into the new vertex it holds under the
standing hypothesis (`WeightedGraph.crawleyBoeveyIn_isRegular_dotZero_factor`), giving
`GalleryAlgebra.linearIndependent_redReducedRepIn`. No hypothesis on `k` beyond commutativity is
needed.

## Main definitions

* `dotZero s₀`: the substitution `y_{s₀} ↦ 0`.
* `GalleryAlgebra.DotQuotient`: `V / y_{s₀} V`.
* `GalleryAlgebra.quotRep`: the action of the gallery algebra on `V / y_{s₀} V`.
* `GalleryAlgebra.reducedRep`: the action of the reduced quotient on `V / y_{s₀} V`.

## Main results

* `GalleryAlgebra.reducedRep_reducedMk`: the action of the image of `x` is that of `x`.
* `GalleryAlgebra.linearIndependent_reducedRep`, `GalleryAlgebra.reducedRep_injective`:
  faithfulness.
* `GalleryAlgebra.linearIndependent_redReducedRepIn`: faithfulness for the Crawley-Boevey graph
  with new edges into the new vertex.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment

/-! ### Setting one variable to zero -/

section DotZero

variable {σ : Type*} [DecidableEq σ] {k : Type*} [CommRing k] (s₀ : σ)

/-- The substitution `y_{s₀} ↦ 0`. -/
noncomputable def dotZero : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun s => if s = s₀ then 0 else X s

variable {s₀}

theorem dotZero_X_of_ne {s : σ} (h : s ≠ s₀) : dotZero s₀ (X s : MvPolynomial σ k) = X s := by
  simp [dotZero, h]

variable (s₀) in
theorem dotZero_X_self : dotZero s₀ (X s₀ : MvPolynomial σ k) = 0 := by
  simp [dotZero]

variable (s₀) in
theorem sub_dotZero_mem (f : MvPolynomial σ k) : f - dotZero s₀ f ∈ Ideal.span {X s₀} := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dotZero]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p s hp =>
    rw [map_mul]
    have e : p * X s - dotZero s₀ p * dotZero s₀ (X s) =
        (p - dotZero s₀ p) * X s + dotZero s₀ p * (X s - dotZero s₀ (X s)) := by ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases h : s = s₀
    · subst h
      rw [dotZero_X_self, sub_zero]
      exact Ideal.subset_span rfl
    · rw [dotZero_X_of_ne h, sub_self]
      exact zero_mem _

/-- The kernel of `y_{s₀} ↦ 0` consists of the multiples of `y_{s₀}`. -/
theorem dotZero_eq_zero_iff {f : MvPolynomial σ k} : dotZero s₀ f = 0 ↔ ∃ g, f = X s₀ * g := by
  constructor
  · intro h
    have := sub_dotZero_mem s₀ f
    rw [h, sub_zero, Ideal.mem_span_singleton'] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, by rw [← ha, mul_comm]⟩
  · rintro ⟨g, rfl⟩
    rw [map_mul, dotZero_X_self, zero_mul]

theorem dotZero_monomial {m : σ →₀ ℕ} (hm : m s₀ = 0) (c : k) :
    dotZero s₀ (monomial m c) = monomial m c := by
  rw [dotZero, aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  dsimp only
  rw [ite_eq_right]
  rintro rfl
  exact Finsupp.mem_support_iff.1 hs hm

theorem dotZero_rename {g : σ → σ} (hg : ∀ s, g s = s₀ ↔ s = s₀) (f : MvPolynomial σ k) :
    dotZero s₀ (rename g f) = rename g (dotZero s₀ f) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun s => ?_
  simp only [AlgHom.comp_apply, rename_X, dotZero, aeval_X]
  by_cases h : s = s₀
  · rw [ite_eq_left ((hg s).2 h), ite_eq_left h, map_zero]
  · rw [ite_eq_right (fun h' => h ((hg s).1 h')), ite_eq_right h, rename_X]

end DotZero

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

/-! ### Specialized leading terms -/

section Leading

variable {s₀ : Strand ν} (h₀ : ν s₀.1 = 1)

include h₀

omit [DecidableEq I] in
theorem colPerm_apply_eq_iff (g : ColPerm ν) (s : Strand ν) : g.1 s = s₀ ↔ s = s₀ := by
  constructor
  · intro h
    exact g.1.injective (h.trans (colPerm_apply_eq h₀ g).symm)
  · rintro rfl
    exact colPerm_apply_eq h₀ g

theorem dotZero_rename_colPerm (g : ColPerm ν) (f : PolyRing ν k) :
    dotZero s₀ (rename ⇑g.1 f) = rename ⇑g.1 (dotZero s₀ f) :=
  dotZero_rename (colPerm_apply_eq_iff h₀ g) f

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.left_ne_and_right_ne (C : FullChamber Γ ν) (d : Diag ν) :
    d.left C ≠ s₀ ∧ d.right C ≠ s₀ := by
  have hd := diag_ne h₀ d
  constructor
  · unfold Diag.left; split_ifs
    exacts [hd.1, hd.2]
  · unfold Diag.right; split_ifs
    exacts [hd.2, hd.1]

omit h₀ in
theorem dotZero_loopFactor (P : MvPolynomial (Fin 2) k) {a b : Strand ν} (ha : a ≠ s₀)
    (hb : b ≠ s₀) : dotZero s₀ (loopFactor P a b) = loopFactor P a b := by
  rw [loopFactor, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext j
  fin_cases j
  · exact dotZero_X_of_ne ha
  · exact dotZero_X_of_ne hb

/-- Webster's leading-term form of a gallery operator (`exists_isTwisted_opList`), with the
leading coefficients non-zero-divisors after setting `y_{s₀} = 0`. -/
theorem exists_isTwisted_opList_dotZero
    (hW₀ : ∀ w : Wall Γ ν, IsRegular (dotZero s₀ (w.factor (k := k))))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b))
    {C : FullChamber Γ ν} {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular (dotZero s₀ M) ∧
      IsTwisted (opList k Γ C w) M a ∧ IsRegular (dotZero s₀ (a 1)) ∧
      ∀ x, a x ≠ 0 → x ≠ 1 → sepCard C.1 (x⁻¹ • C.flips w).1 < sepCard C.1 (C.flips w).1 := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, fun x => if x = 1 then 1 else 0, by rw [map_one]; exact isRegular_one,
      IsTwisted.id, ?_, fun x hx hx1 => absurd (ite_eq_right_iff.2 fun h => absurd h hx1) hx⟩
    simp only [ite_true, map_one]
    exact isRegular_one
  | append_singleton w h ih =>
    obtain ⟨M, a, hM, hT, ha1, hlt⟩ := ih hw.of_append
    set B := C.flips w with hBdef
    obtain ⟨-, hadj, -⟩ := (hw.append : GoodWord B.1 [h]).cons
    set B' := B.flipH h with hB'def
    have hflips : C.flips (w ++ [h]) = B' := by rw [flips_append]; rfl
    have hop : opList k Γ C (w ++ [h]) = stepOp Γ B B' ∘ₗ opList k Γ C w := by
      rw [opList_append]; rfl
    have hhw : h ∉ w := by
      have := List.nodup_append_comm.1 hw.1
      exact (List.nodup_cons.1 this).1
    have hCB : C.1 h = B.1 h := by
      rw [hBdef, flips_val hw.of_append]
      simp [flipSigns, hhw]
    have hcard : sepCard C.1 B'.1 = sepCard C.1 B.1 + 1 := by
      rw [adjacent_iff_eq_flipSign.1 hadj]
      exact sepCard_flipSign_of_eq hCB
    have hle : ∀ x : ColPerm ν, sepCard C.1 (x⁻¹ • B').1 ≤ sepCard C.1 (x⁻¹ • B).1 + 1 := by
      intro x
      rw [adjacent_iff_eq_flipSign.1 (hadj.smul x⁻¹)]
      exact sepCard_flipSign_le _ _ _
    rw [hflips, hop]
    rcases h with wl | d
    · -- a wall: multiplication by `Q_e(y_a, y_b)` or by `1`
      rw [stepOp_inl hadj, wallOp_eq_mulLeft]
      set c : PolyRing ν k := if B.1 (.inl wl) = false ∧ (!B.1 (.inl wl)) = true then wl.factor
        else 1
      have hc : IsRegular (dotZero s₀ c) := by
        simp only [c]
        split_ifs
        · exact hW₀ wl
        · rw [map_one]; exact isRegular_one
      refine ⟨M, fun x => c * a x, hM, hT.mulLeft c, by rw [map_mul]; exact hc.mul ha1,
        fun x hx hx1 => ?_⟩
      have hax : a x ≠ 0 := fun h0 => hx (by simp only [h0, mul_zero])
      have := hlt x hax hx1
      have := hle x
      omega
    · -- a diagonal: a divided difference or a loop crossing
      set l := d.left B
      set r := d.right B
      have hlr : l ≠ r := Diag.left_ne_right B d
      have hl₀ := (Diag.left_ne_and_right_ne h₀ B d).1
      have hr₀ := (Diag.left_ne_and_right_ne h₀ B d).2
      have hlab : l.1 = r.1 := by rw [Diag.left_label B d, Diag.right_label B d]
      have hs : (rename ⇑d.refl.1 : PolyRing ν k →ₐ[k] PolyRing ν k) = rename (swap l r) := by
        rw [Diag.swap_left_right B d]
        rfl
      have hB' : B' = d.refl • B := (hadj.refl_smul).symm
      obtain ⟨c, α, β, hc, hα, hstep⟩ : ∃ c α β : PolyRing ν k, IsRegular (dotZero s₀ c) ∧
          IsRegular (dotZero s₀ α) ∧
          ∀ u, c * stepOp Γ B B' u = α * u + β * rename ⇑d.refl.1 u := by
        rw [stepOp_inr hadj, hs]
        rcases hloop : Γ.loop l.1 with _ | P
        · refine ⟨X l - X r, 1, -1, ?_, by rw [map_one]; exact isRegular_one, fun u => ?_⟩
          · rw [map_sub, dotZero_X_of_ne hl₀, dotZero_X_of_ne hr₀]
            exact isRegular_X_sub_X hlr
          · rw [psiOp_of_none hloop, ddiff_spec hlr]
            ring
        · refine ⟨1, loopFactor P l r, -loopFactor P l r, by rw [map_one]; exact isRegular_one,
            by rw [dotZero_loopFactor P hl₀ hr₀]; exact hL P l r hloop hlr hlab, fun u => ?_⟩
          rw [psiOp_of_some hloop]
          ring
      have hrefl : d.refl ≠ 1 := by
        intro e
        have := congrArg (fun g : ColPerm ν => g.1 d.fst) e
        simp only [Diag.refl, swap_apply_left] at this
        exact d.fst_ne_snd this.symm
      have hzero : a d.refl⁻¹ = 0 := by
        by_contra hne
        have h1 := hlt _ hne (inv_ne_one.2 hrefl)
        rw [inv_inv, ← hB', hcard] at h1
        omega
      refine ⟨c * M * rename ⇑d.refl.1 M, _, ?_, hT.step d.refl hstep, ?_, fun y hy hy1 => ?_⟩
      · rw [map_mul, map_mul, dotZero_rename_colPerm h₀]
        exact (hc.mul hM).mul (isRegular_rename_colPerm hM _)
      · simp only [mul_one, hzero, map_zero, mul_zero, add_zero]
        rw [map_mul, map_mul, dotZero_rename_colPerm h₀]
        exact (hα.mul (isRegular_rename_colPerm hM _)).mul ha1
      · by_cases hay : a y = 0
        · have hay' : a (d.refl⁻¹ * y) ≠ 0 := fun h0 => hy (by simp only [hay, h0, map_zero,
            mul_zero, add_zero])
          have hsm : y⁻¹ • B' = (d.refl⁻¹ * y)⁻¹ • B := by
            rw [hB', ← mul_smul, mul_inv_rev, inv_inv]
          rw [hsm]
          by_cases hx1 : d.refl⁻¹ * y = 1
          · rw [hx1, inv_one, one_smul]
            omega
          · have := hlt _ hay' hx1
            omega
        · have := hlt y hay hy1
          have := hle y
          omega

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E))

include hP in
/-- The relabelled gallery operator (`exists_isTwisted_ren_opList`), with the leading
coefficient a non-zero-divisor after setting `y_{s₀} = 0`. -/
theorem exists_isTwisted_ren_opList_dotZero
    (hW₀ : ∀ w : Wall Γ ν, IsRegular (dotZero s₀ (w.factor (k := k))))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b))
    (C D : FullChamber Γ ν) (g : ColPerm ν) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular (dotZero s₀ M) ∧
      IsTwisted (ren g ∘ₗ
        opList k Γ C (word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2)) M a ∧
      IsRegular (dotZero s₀ (a g)) ∧
      ∀ x, a x ≠ 0 → x ≠ g → sepCard C.1 (x⁻¹ • D).1 < sepCard C.1 (g⁻¹ • D).1 := by
  obtain ⟨M, a, hM, hT, ha1, hlt⟩ :=
    exists_isTwisted_opList_dotZero h₀ hW₀ hL (goodWord_segWord hP C (g⁻¹ • D))
  rw [flips_segWord_eq hP] at hlt
  refine ⟨rename ⇑g.1 M, fun y => rename ⇑g.1 (a (g⁻¹ * y)), ?_, hT.rename g, ?_,
    fun x hx hxg => ?_⟩
  · rw [dotZero_rename_colPerm h₀]
    exact isRegular_rename_colPerm hM g
  · simp only [inv_mul_cancel]
    rw [dotZero_rename_colPerm h₀]
    exact isRegular_rename_colPerm ha1 g
  · have hax : a (g⁻¹ * x) ≠ 0 := fun h0 => hx (by simp only [h0, map_zero])
    have hne : g⁻¹ * x ≠ 1 := fun h1 => hxg (inv_mul_eq_one.1 h1).symm
    have := hlt _ hax hne
    rwa [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul] at this

end Leading

/-! ### Dedekind's lemma and triangularity with `y_{s₀} = 0` -/

section Triangular

variable {s₀ : Strand ν} (h₀ : ν s₀.1 = 1)

include h₀

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Dedekind's lemma** for relabellings (`eq_zero_of_forall_sum_mul_rename`), tested only on
polynomials with `y_{s₀} = 0`. -/
theorem eq_zero_of_forall_sum_mul_rename_dotZero {a : ColPerm ν → PolyRing ν k}
    (h : ∀ f, ∑ x, a x * rename ⇑x.1 (dotZero s₀ f) = 0) : a = 0 := by
  classical
  suffices H : ∀ S : Finset (ColPerm ν), ∀ a : ColPerm ν → PolyRing ν k, (∀ x ∉ S, a x = 0) →
      (∀ f, ∑ x, a x * rename ⇑x.1 (dotZero s₀ f) = 0) → a = 0 from
    H Finset.univ a (fun x hx => absurd (Finset.mem_univ x) hx) h
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun a ha _ => funext fun x => ha x (Finset.notMem_empty x)
  | insert x₀ S hx₀ ih =>
    intro a ha h
    have hS : ∀ y ∈ S, a y = 0 := by
      intro y hy
      have hne : y ≠ x₀ := fun e => hx₀ (e ▸ hy)
      obtain ⟨t, ht⟩ : ∃ t, y.1 t ≠ x₀.1 t := by
        by_contra hc
        push Not at hc
        exact hne (Subtype.ext (Equiv.ext hc))
      have ht₀ : t ≠ s₀ := by
        rintro rfl
        exact ht ((colPerm_apply_eq h₀ y).trans (colPerm_apply_eq h₀ x₀).symm)
      have hb := ih (fun x => a x * (X (x.1 t) - X (x₀.1 t))) (fun x hx => ?_) (fun f => ?_)
      · have := congrFun hb y
        simpa only [Pi.zero_apply, (isRegular_X_sub_X (k := k) ht).right.mul_right_eq_zero_iff]
          using this
      · by_cases e : x = x₀
        · simp only [e, sub_self, mul_zero]
        · rw [ha x (by simp [e, hx]), zero_mul]
      · have h1 := h (X t * f)
        have h2 := h f
        rw [map_mul, dotZero_X_of_ne ht₀] at h1
        have e : ∑ x, a x * (X (x.1 t) - X (x₀.1 t)) * rename ⇑x.1 (dotZero s₀ f) =
            ∑ x, a x * rename ⇑x.1 (X t * dotZero s₀ f) -
              X (x₀.1 t) * ∑ x, a x * rename ⇑x.1 (dotZero s₀ f) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_mul, rename_X]
          ring
        rw [e, h1, h2, mul_zero, sub_zero]
    have h0 := h 1
    simp only [map_one, mul_one] at h0
    rw [Finset.sum_eq_single x₀ (fun y _ hy => by
      by_cases hyS : y ∈ S
      · exact hS y hyS
      · exact ha y (by simp [hy, hyS])) (fun hx => absurd (Finset.mem_univ x₀) hx)] at h0
    funext x
    by_cases e : x = x₀
    · rw [e]; exact h0
    · by_cases hxS : x ∈ S
      · exact hS x hxS
      · exact ha x (by simp [e, hxS])

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **Triangularity** (`eq_zero_of_forall_sum_twisted_eq_zero`) with `y_{s₀} = 0`: if the
denominators and the leading coefficients are non-zero-divisors after setting `y_{s₀} = 0`, the
coefficients `F g` do not involve `y_{s₀}`, and `∑_g Y g (F g * f)` vanishes at `y_{s₀} = 0` for
every `f`, then `F = 0`. -/
theorem eq_zero_of_forall_sum_twisted_dotZero
    {Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k}
    {M : ColPerm ν → PolyRing ν k} {a : ColPerm ν → ColPerm ν → PolyRing ν k}
    (Λ : ColPerm ν → ℕ) (hM : ∀ g, IsRegular (dotZero s₀ (M g)))
    (hY : ∀ g, IsTwisted (Y g) (M g) (a g)) (ha : ∀ g, IsRegular (dotZero s₀ (a g g)))
    (hlt : ∀ g x, a g x ≠ 0 → x ≠ g → Λ x < Λ g) {F : ColPerm ν → PolyRing ν k}
    (hF₀ : ∀ g, dotZero s₀ (F g) = F g) (hF : ∀ f, dotZero s₀ (∑ g, Y g (F g * f)) = 0) :
    F = 0 := by
  classical
  by_contra hne
  set S := Finset.univ.filter fun g => F g ≠ 0
  have hSne : S.Nonempty := by
    by_contra hc
    refine hne (funext fun g => ?_)
    by_contra hg
    exact hc ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩⟩
  obtain ⟨g₀, hg₀, hmax⟩ := S.exists_max_image Λ hSne
  set N : ColPerm ν → PolyRing ν k := fun g => ∏ h ∈ Finset.univ.erase g, M h
  have hN : ∀ g, IsRegular (dotZero s₀ (N g)) := fun g => by
    rw [map_prod]
    exact IsRegular.prod fun h _ => hM h
  have hE : ∀ f, (∏ h, M h) * ∑ g, Y g (F g * f) =
      ∑ x, (∑ g, N g * a g x * rename ⇑x.1 (F g)) * rename ⇑x.1 f := by
    intro f
    rw [Finset.mul_sum]
    symm
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), mul_assoc, hY g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul]
    ring
  have key : ∀ f, ∑ x, (∑ g, dotZero s₀ (N g) * dotZero s₀ (a g x) * rename ⇑x.1 (F g)) *
      rename ⇑x.1 (dotZero s₀ f) = 0 := by
    intro f
    have := congrArg (dotZero s₀) (hE f)
    rw [map_mul, hF f, mul_zero] at this
    rw [this]
    simp only [map_sum, map_mul, dotZero_rename_colPerm h₀, hF₀]
  have hcoef := congrFun (eq_zero_of_forall_sum_mul_rename_dotZero h₀ key) g₀
  simp only [Pi.zero_apply] at hcoef
  rw [Finset.sum_eq_single g₀ (fun g _ hg => ?_) (fun hx => absurd (Finset.mem_univ g₀) hx)]
    at hcoef
  · have hF₀' : rename ⇑g₀.1 (F g₀) = 0 :=
      ((hN g₀).mul (ha g₀)).left.mul_left_eq_zero_iff.1 hcoef
    rw [← map_zero (rename (R := k) ⇑g₀.1)] at hF₀'
    exact (Finset.mem_filter.1 hg₀).2 (rename_colPerm_injective g₀ hF₀')
  · by_cases hFg : F g = 0
    · rw [hFg, map_zero, mul_zero]
    · have hle := hmax g (by simp [S, hFg])
      have hag : a g g₀ = 0 := by
        by_contra hag
        exact absurd (hlt g g₀ hag (Ne.symm hg)) (not_lt.2 hle)
      rw [hag, map_zero, mul_zero, zero_mul]

end Triangular

/-! ### The action on `V / y_{s₀} V` -/

section Action

variable (k Γ ν) in
/-- The submodule `y_{s₀} V` of `V = (FullChamber Γ ν → k[y_s])`. -/
noncomputable def dotRange (s₀ : Strand ν) : Submodule k (FullChamber Γ ν → PolyRing ν k) :=
  LinearMap.range (diagOp (ι := FullChamber Γ ν) (LinearMap.mulLeft k (X s₀ : PolyRing ν k)))

variable (k Γ ν) in
/-- `V / y_{s₀} V`: one copy, for each full chamber, of the polynomials modulo `y_{s₀}`. -/
abbrev DotQuotient (s₀ : Strand ν) : Type _ :=
  (FullChamber Γ ν → PolyRing ν k) ⧸ dotRange k Γ ν s₀

omit [IsStrictOrderedRing 𝕜] in
/-- `y_{s₀} V` consists of the vectors whose components vanish at `y_{s₀} = 0`. -/
theorem mem_dotRange_iff {s₀ : Strand ν} {v : FullChamber Γ ν → PolyRing ν k} :
    v ∈ dotRange k Γ ν s₀ ↔ ∀ C, dotZero s₀ (v C) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ C
    rw [diagOp_apply, LinearMap.mulLeft_apply, map_mul, dotZero_X_self, zero_mul]
  · intro h
    choose u hu using fun C => dotZero_eq_zero_iff.1 (h C)
    exact ⟨u, funext fun C => (hu C).symm⟩

variable {s₀ : Strand ν} (hΓ : Γ.PSymm) (h₀ : ν s₀.1 = 1)

include h₀ in
theorem dotRange_le_comap (x : GalleryAlgebra k Γ ν) :
    dotRange k Γ ν s₀ ≤ (dotRange k Γ ν s₀).comap (galleryRep k hΓ x) := by
  rintro _ ⟨u, rfl⟩
  refine ⟨galleryRep k hΓ x u, ?_⟩
  have := congrArg (galleryRep k hΓ) (commute_poly_X h₀ x).eq
  rw [map_mul, map_mul, galleryRep_poly] at this
  exact LinearMap.congr_fun this u

/-- The action of the gallery algebra on `V / y_{s₀} V`. -/
noncomputable def quotRep (x : GalleryAlgebra k Γ ν) : Module.End k (DotQuotient k Γ ν s₀) :=
  (dotRange k Γ ν s₀).mapQ (dotRange k Γ ν s₀) (galleryRep k hΓ x) (dotRange_le_comap hΓ h₀ x)

theorem quotRep_mk (x : GalleryAlgebra k Γ ν) (v : FullChamber Γ ν → PolyRing ν k) :
    quotRep hΓ h₀ x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (galleryRep k hΓ x v) :=
  rfl

theorem quotRep_mul (x y : GalleryAlgebra k Γ ν) :
    quotRep hΓ h₀ (x * y) = quotRep hΓ h₀ x * quotRep hΓ h₀ y := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [Module.End.mul_apply, quotRep_mk, quotRep_mk, quotRep_mk, map_mul,
      Module.End.mul_apply]

variable (k Γ ν) in
/-- The action of the gallery algebra on `V / y_{s₀} V`, as a linear map. -/
noncomputable def quotRepLinear :
    GalleryAlgebra k Γ ν →ₗ[k] Module.End k (DotQuotient k Γ ν s₀) where
  toFun := quotRep hΓ h₀
  map_add' x y := by
    refine LinearMap.ext fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      rw [LinearMap.add_apply, quotRep_mk, quotRep_mk, quotRep_mk, map_add,
        LinearMap.add_apply, Submodule.Quotient.mk_add]
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      rw [LinearMap.smul_apply, quotRep_mk, quotRep_mk, map_smul, LinearMap.smul_apply,
        RingHom.id_apply, Submodule.Quotient.mk_smul]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem quotient_mk_sum {ι : Type*} (s : Finset ι) (v : ι → FullChamber Γ ν → PolyRing ν k) :
    ∑ i ∈ s, (Submodule.Quotient.mk (v i) : DotQuotient k Γ ν s₀) =
      Submodule.Quotient.mk (∑ i ∈ s, v i) :=
  (map_sum (dotRange k Γ ν s₀).mkQ v s).symm

/-- The dot on `s₀` acts by zero on `V / y_{s₀} V`. -/
theorem quotRep_poly_X : quotRep hΓ h₀ (poly (X s₀) : GalleryAlgebra k Γ ν) = 0 := by
  refine LinearMap.ext fun v => ?_
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [quotRep_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, galleryRep_poly]
    exact ⟨v, rfl⟩

theorem ker_reducedMk_le :
    LinearMap.ker (reducedMk k Γ ν s₀).toLinearMap ≤ LinearMap.ker
      (quotRepLinear k Γ ν hΓ h₀ ∘ₗ (weightedKLR k Γ ν).subtype ∘ₗ
        (cornerLinearEquiv k Γ ν).toLinearMap) := by
  intro x hx
  rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, reducedMk_eq_zero_iff, mem_dotIdeal_iff h₀]
    at hx
  obtain ⟨y, rfl⟩ := hx
  rw [LinearMap.mem_ker]
  change quotRep hΓ h₀ (reducedDot k Γ ν s₀ * y).1 = 0
  rw [reducedDot_mul_val h₀, quotRep_mul, quotRep_poly_X, zero_mul]

/-- The linear map underlying `reducedRep`. -/
noncomputable def reducedRepLinear :
    ReducedQuotient k Γ ν s₀ →ₗ[k] Module.End k (DotQuotient k Γ ν s₀) :=
  ((LinearMap.ker (reducedMk k Γ ν s₀).toLinearMap).liftQ _ (ker_reducedMk_le hΓ h₀)) ∘ₗ
    ((reducedMk k Γ ν s₀).toLinearMap.quotKerEquivOfSurjective
      (reducedMk_surjective s₀)).symm.toLinearMap

theorem reducedRepLinear_reducedMk (y : WeightedKLRAlgebra k Γ ν) :
    reducedRepLinear hΓ h₀ (reducedMk k Γ ν s₀ y) = quotRep hΓ h₀ y.1 := by
  have he : ((reducedMk k Γ ν s₀).toLinearMap.quotKerEquivOfSurjective
      (reducedMk_surjective s₀)).symm ((reducedMk k Γ ν s₀).toLinearMap y) =
      Submodule.Quotient.mk y :=
    LinearEquiv.symm_apply_eq _ |>.2 rfl
  change (LinearMap.ker (reducedMk k Γ ν s₀).toLinearMap).liftQ _ (ker_reducedMk_le hΓ h₀)
    (((reducedMk k Γ ν s₀).toLinearMap.quotKerEquivOfSurjective (reducedMk_surjective s₀)).symm
      ((reducedMk k Γ ν s₀).toLinearMap y)) = _
  rw [he]
  rfl

/-- **The action of the reduced quotient on `V / y_{s₀} V`** (Webster, arXiv:1209.2463v4,
§3.1): the polynomial representation of Webster's algebra descends to the reduced quotient
acting on the polynomials with `y_{s₀} = 0`, for a strand `s₀` alone in its colour. -/
noncomputable def reducedRep :
    ReducedQuotient k Γ ν s₀ →ₙₐ[k] Module.End k (DotQuotient k Γ ν s₀) :=
  { reducedRepLinear hΓ h₀ with
    map_zero' := (reducedRepLinear hΓ h₀).map_zero
    map_mul' := fun a b => by
      obtain ⟨y, rfl⟩ := reducedMk_surjective s₀ a
      obtain ⟨z, rfl⟩ := reducedMk_surjective s₀ b
      simp only [LinearMap.toFun_eq_coe]
      rw [← map_mul, reducedRepLinear_reducedMk, reducedRepLinear_reducedMk,
        reducedRepLinear_reducedMk]
      exact quotRep_mul hΓ h₀ y.1 z.1 }

theorem reducedRep_reducedMk (y : WeightedKLRAlgebra k Γ ν) :
    reducedRep hΓ h₀ (reducedMk k Γ ν s₀ y) = quotRep hΓ h₀ y.1 :=
  reducedRepLinear_reducedMk hΓ h₀ y

end Action

/-! ### Faithfulness -/

section Faithful

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  {s₀ : Strand ν} (h₀ : ν s₀.1 = 1)

theorem reducedRep_reducedBasis (i) :
    reducedRep hΓ h₀ (reducedBasis hP hD hZ hΓ hW hL h₀ i) =
      quotRep hΓ h₀ (algebraBasis hP hD hZ hΓ hW hL i.1).1 := by
  rw [reducedBasis_apply, reducedRep_reducedMk]

/-- **Faithfulness of the reduced quotient on `V / y_{s₀} V`** (Webster, arXiv:1209.2463v4,
§3.1): for a strand `s₀` alone in its colour, if the wall polynomials `Q_e(y_a, y_b)` remain
non-zero-divisors after setting `y_{s₀} = 0` (`hW₀`), the images of the basis elements
`reducedBasis` of the reduced quotient (the Theorem 2.8 basis elements with no dot on `s₀`) act
on `V / y_{s₀} V` by linearly independent operators. This is the faithfulness used by the
diagrammatic calculator. -/
theorem linearIndependent_reducedRep
    (hW₀ : ∀ w : Wall Γ ν, IsRegular (dotZero s₀ (w.factor (k := k)))) :
    LinearIndependent k (fun i => reducedRep hΓ h₀ (reducedBasis hP hD hZ hΓ hW hL h₀ i)) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  refine Finsupp.ext fun i₀ => ?_
  obtain ⟨⟨C₀, D₀, g₀, m₀⟩, hm₀⟩ := i₀
  rw [Finsupp.coe_zero, Pi.zero_apply]
  -- the operators from the copy of `C₀` to the copy of `D₀`
  set Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k := fun g => ren g ∘ₗ
    opList k Γ C₀.1 (word (hypAff (Γ := Γ)) (P C₀.1 (g⁻¹ • D₀.1)).1
      (P C₀.1 (g⁻¹ • D₀.1)).2) with hY
  -- the coefficient polynomial of the relabelling `g`
  set F : ColPerm ν → PolyRing ν k := fun g =>
    ∑ i ∈ l.support.filter (fun i => i.1.1 = C₀ ∧ i.1.2.1 = D₀ ∧ i.1.2.2.1 = g),
      monomial i.1.2.2.2 (l i) with hFdef
  -- the action of each basis element on `f` in the copy of `C₀`, at the copy of `D₀`
  set T : {i : RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) //
      i.2.2.2 s₀ = 0} → PolyRing ν k → PolyRing ν k := fun i f =>
    if i.1.1 = C₀ ∧ i.1.2.1 = D₀ then Y i.1.2.2.1 (monomial i.1.2.2.2 1 * f) else 0 with hTdef
  have hv : ∀ i f, galleryRep k hΓ (algebraBasis hP hD hZ hΓ hW hL i.1).1
      (Pi.single C₀.1 f) D₀.1 = T i f := by
    rintro ⟨⟨C, D, g, m⟩, hm⟩ f
    rw [algebraBasis_val]
    change galleryRep k hΓ (basisElt k P C.1 (g⁻¹ • D.1) g m) _ _ = _
    rw [galleryRep_basisElt hP, smul_inv_smul, blk_apply]
    simp only [hTdef, hY]
    by_cases hC : C = C₀
    · subst hC
      by_cases hD : D = D₀
      · subst hD
        rw [Pi.single_eq_same, Pi.single_eq_same, ite_eq_left ⟨rfl, rfl⟩]
        rfl
      · rw [Pi.single_eq_of_ne (fun h => hD (Subtype.ext h).symm), ite_eq_right (fun h => hD h.2)]
    · rw [Pi.single_eq_of_ne (fun h => hC (Subtype.ext h)), ite_eq_right (fun h => hC h.1)]
      simp
  have hsum : ∀ f, dotZero s₀ (∑ i ∈ l.support, l i • T i f) = 0 := by
    intro f
    have h1 := congrArg (fun A : Module.End k (DotQuotient k Γ ν s₀) =>
      A (Submodule.Quotient.mk (Pi.single C₀.1 f))) hl
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.zero_apply, reducedRep_reducedBasis, quotRep_mk] at h1
    simp only [← Submodule.Quotient.mk_smul] at h1
    rw [quotient_mk_sum, Submodule.Quotient.mk_eq_zero, mem_dotRange_iff] at h1
    have h2 := h1 D₀.1
    rw [Finset.sum_apply] at h2
    simpa only [Pi.smul_apply, hv] using h2
  have hF : ∀ f, dotZero s₀ (∑ g, Y g (F g * f)) = 0 := by
    intro f
    rw [← hsum f]
    congr 1
    simp only [hFdef, Finset.sum_mul, map_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1.1 = C₀ ∧ i.1.2.1 = D₀
    · rw [Finset.sum_eq_single i.1.2.2.1]
      · rw [ite_eq_left ⟨h1.1, h1.2, rfl⟩]
        simp only [hTdef, ite_eq_left h1]
        rw [← map_smul, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
      · intro g _ hg
        rw [ite_eq_right (fun h => hg h.2.2.symm), zero_mul, map_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero fun g _ => by
        rw [ite_eq_right (fun h => h1 ⟨h.1, h.2.1⟩), zero_mul, map_zero]]
      simp only [hTdef, ite_eq_right h1, smul_zero]
  have hF₀ : ∀ g, dotZero s₀ (F g) = F g := by
    intro g
    simp only [hFdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => dotZero_monomial i.2 _
  choose M a hM hT ha hlt using fun g =>
    exists_isTwisted_ren_opList_dotZero (k := k) h₀ hP hW₀ hL C₀.1 D₀.1 g
  have hF0 := eq_zero_of_forall_sum_twisted_dotZero (Y := Y) h₀
    (fun x => sepCard C₀.1.1 (x⁻¹ • D₀.1).1) hM hT ha hlt hF₀ hF
  by_cases hmem : (⟨(C₀, D₀, g₀, m₀), hm₀⟩ : {i : RankChamber Γ ν × RankChamber Γ ν × ColPerm ν ×
      (Strand ν →₀ ℕ) // i.2.2.2 s₀ = 0}) ∈ l.support
  · have h0 : (F g₀).coeff m₀ = 0 := by simp [congrFun hF0 g₀]
    simp only [hFdef, coeff_sum, coeff_monomial] at h0
    rw [Finset.sum_eq_single_of_mem _ (Finset.mem_filter.2 ⟨hmem, rfl, rfl, rfl⟩)] at h0
    · simpa only [ite_true] using h0
    · rintro ⟨⟨C, D, g, m⟩, hm⟩ hb hne
      obtain ⟨-, hC, hD, hg⟩ := Finset.mem_filter.1 hb
      simp only at hC hD hg
      subst hC hD hg
      exact ite_eq_right fun (h : m = m₀) => hne (by subst h; rfl)
  · exact Finsupp.notMem_support_iff.1 hmem

include hP hD hZ hW hL in
/-- **The reduced quotient acts faithfully on `V / y_{s₀} V`** (Webster, arXiv:1209.2463v4,
§3.1), under the hypotheses of `linearIndependent_reducedRep`. -/
theorem reducedRep_injective
    (hW₀ : ∀ w : Wall Γ ν, IsRegular (dotZero s₀ (w.factor (k := k)))) :
    Function.Injective (reducedRep (k := k) hΓ h₀) := by
  set b := reducedBasis hP hD hZ hΓ hW hL h₀
  have hli := linearIndependent_reducedRep hP hD hZ hΓ hW hL h₀ hW₀
  let f : ReducedQuotient k Γ ν s₀ →ₗ[k] Module.End k (DotQuotient k Γ ν s₀) :=
    reducedRepLinear hΓ h₀
  change Function.Injective f
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← b.linearCombination_repr x, Finsupp.apply_linearCombination] at hx
  have := linearIndependent_iff.1 hli _ hx
  rw [← b.linearCombination_repr x, this, map_zero]

end Faithful

end GalleryAlgebra

/-! ### The Crawley-Boevey graph with new edges into the new vertex -/

namespace WeightedGraph

open GalleryAlgebra

variable {J : Type} [DecidableEq J] {Γ' : WeightedGraph J 𝕜 k} {ℓ : ℕ} {Λ : Fin ℓ → J →₀ ℕ}
  {ϖ : Fin ℓ → 𝕜}

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The wall factors of `crawleyBoeveyIn` remain non-zero-divisors after setting the dot on the
`0`-labelled strand to zero, when `Γ` satisfies Webster's standing hypothesis. -/
theorem crawleyBoeveyIn_isRegular_dotZero_factor (hS : Γ'.Standing) (ν : J →₀ ℕ)
    (w : Wall (Γ'.crawleyBoeveyIn Λ ϖ) (redWeight ν)) :
    IsRegular (dotZero (zeroStrand ν) (w.factor (k := k))) := by
  have h₀ := redWeight_zeroStrand ν
  have hsrc : w.src.1.1 = (Γ'.crawleyBoeveyIn Λ ϖ).head w.edge := w.2.1
  have htgt : w.tgt.1.1 = (Γ'.crawleyBoeveyIn Λ ϖ).tail w.edge := w.2.2.1
  have hne : w.src ≠ w.tgt := w.2.2.2
  rcases he : w.edge with e | e
  · -- an edge of `Γ`: the factor does not involve the `0`-labelled strand
    have hs : w.src ≠ zeroStrand ν := fun h => by
      rw [he, h] at hsrc
      exact absurd hsrc (by simp [zeroStrand, crawleyBoeveyIn])
    have ht : w.tgt ≠ zeroStrand ν := fun h => by
      rw [he, h] at htgt
      exact absurd htgt (by simp [zeroStrand, crawleyBoeveyIn])
    rw [Wall.factor_eq, dotZero_loopFactor _ hs ht, ← Wall.factor_eq]
    exact crawleyBoeveyIn_isRegular_factor hS w
  · -- a new edge `i → 0`: the factor is `(y_{s₀} - y_t) ^ n`
    have hs : w.src = zeroStrand ν := by
      refine eq_of_fst_eq h₀ (Subtype.ext ?_)
      rw [hsrc, he]
      rfl
    have ht : w.tgt ≠ zeroStrand ν := fun h => hne (hs.trans h.symm)
    rw [Wall.factor, he]
    change IsRegular (dotZero (zeroStrand ν) (aeval _ ((X 0 - X 1) ^ _)))
    simp only [map_pow, map_sub, aeval_X, Fin.cons_zero, Fin.cons_one, hs, dotZero_X_self,
      dotZero_X_of_ne ht, zero_sub]
    rw [neg_pow]
    exact ((isUnit_neg_one (α := PolyRing (redWeight ν) k)).pow _).isRegular.mul
      (isRegular_X.pow _)

end WeightedGraph

namespace GalleryAlgebra

open WeightedGraph

variable {J : Type} [DecidableEq J] {Γ' : WeightedGraph J 𝕜 k} {ℓ : ℕ} {Λ' : Fin ℓ → J →₀ ℕ}
  {ϖ : Fin ℓ → 𝕜}

/-- **Faithfulness of the reduced quotient** for the Crawley-Boevey graph with new edges `i → 0`
(Webster, arXiv:1209.2463v4, §3.1): the images of the basis `redReducedBasisIn` of the reduced
quotient act on the polynomial representation with the dot on the `0`-labelled strand set to
zero by linearly independent operators, when `Γ` satisfies the standing hypothesis and (†) and
the weights `ϖ_j` are distinct. -/
theorem linearIndependent_redReducedRepIn (ν : J →₀ ℕ)
    {P : FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      (Strand (redWeight ν) → 𝕜) × (Strand (redWeight ν) → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ'.Dagger) (hZ : Γ'.NoZeroLoops)
    (hS : Γ'.Standing) (hϖ : Function.Injective ϖ) :
    LinearIndependent k (fun i => reducedRep (crawleyBoeveyIn_psymm hS.psymm)
      (redWeight_zeroStrand ν) (redReducedBasisIn ν hP hD hZ hS hϖ i)) :=
  linearIndependent_reducedRep hP _ _ _ _ _ _ (crawleyBoeveyIn_isRegular_dotZero_factor hS ν)

/-- **The reduced quotient acts faithfully** for the Crawley-Boevey graph with new edges `i → 0`
(Webster, arXiv:1209.2463v4, §3.1), under the hypotheses of
`linearIndependent_redReducedRepIn`. -/
theorem redReducedRepIn_injective (ν : J →₀ ℕ)
    {P : FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      FullChamber (Γ'.crawleyBoeveyIn Λ' ϖ) (redWeight ν) →
      (Strand (redWeight ν) → 𝕜) × (Strand (redWeight ν) → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ'.Dagger) (hZ : Γ'.NoZeroLoops)
    (hS : Γ'.Standing) (hϖ : Function.Injective ϖ) :
    Function.Injective (reducedRep (k := k) (crawleyBoeveyIn_psymm (Λ := Λ') (ϖ := ϖ) hS.psymm)
      (redWeight_zeroStrand ν)) :=
  reducedRep_injective hP (crawleyBoeveyIn_dagger hD hϖ) (crawleyBoeveyIn_noZeroLoops hZ) _
    (crawleyBoeveyIn_isRegular_factor hS) (crawleyBoeveyIn_isRegular_loopFactor hS) _
    (crawleyBoeveyIn_isRegular_dotZero_factor hS ν)

end GalleryAlgebra

end Categorification.WeightedKLR
