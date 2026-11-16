/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalCrossing
import Categorification.KLR.PolyRep.Independence

/-!
# The polynomial representation of Stendhal diagrams on the black strands

Towards the injectivity in Webster, arXiv:1209.2463v4, Theorem 3.5: the homomorphism from the
Stendhal algebra `T̃^λ` (arXiv:1309.3796v2, Definition 4.5) to the reduced weighted KLR algebra
is studied through the KLR polynomial representation (KL I, §2.3) for the polynomials
`P₂ = stP`. Killing the variables of the red strands (`blackEval`) turns the crossings for
`stP` into the crossings for `stBlackP`, the polynomials `P₂` with the red-strand variables set
to zero (and `1` between red strands), as long as no two red strands are exchanged.

## Main definitions

* `blackEval i` : sets the variables of the red strands of `i` to zero.
* `stBlackP` : `P₂` on the black strands.
* `NoRedCross ρ i` : the word `ρ`, applied to `i`, never exchanges two red strands.

## Main results

* `blackEval_crossComp`, `blackEval_wordComp` : killing the red variables intertwines the
  crossings for `stP` and `stBlackP`.
* `wordComp_stP_eq_zero` : a word exchanging two red strands acts by zero for `stP`.
* `wordComp_X_mul` : the variable of a red strand is transported along a word.
-/

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv MvPolynomial TypeA KLR.PolyRep

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-! ### Red labels -/

/-- Each red label occurs at one position only. -/
theorem eq_of_lbl_eq_inr {i : KLR.Seq (stendhalWeight ℓ ν)} {a b : Fin m} {r : Fin ℓ}
    (ha : i.1 a = .inr r) (hb : i.1 b = .inr r) : a = b := by
  have e1 := eq_redStrand (ν := ν) (s := i.strandAt a) ha
  have e2 := eq_redStrand (ν := ν) (s := i.strandAt b) hb
  exact i.strandAt_injective (e1.trans e2.symm)

/-- Equal labels at distinct positions are black. -/
theorem isLeft_of_lbl_eq {i : KLR.Seq (stendhalWeight ℓ ν)} {a b : Fin m} (hab : a ≠ b)
    (h : i.1 a = i.1 b) : (i.1 a).isLeft := by
  rcases hr : i.1 a with c | r
  · rfl
  · exact absurd (eq_of_lbl_eq_inr hr (h ▸ hr)) hab

/-! ### Killing the red variables -/

/-- Set the variables of the red strands of `i` to zero. -/
noncomputable def blackEval (i : KLR.Seq (stendhalWeight ℓ ν)) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  aeval fun a => if (i.1 a).isLeft then X a else 0

omit [DecidableEq I] in
theorem blackEval_X (i : KLR.Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    blackEval (k := k) i (X a) = if (i.1 a).isLeft then X a else 0 := by
  simp [blackEval]

omit [DecidableEq I] in
/-- `blackEval` does not change polynomials in the variables of black strands. -/
theorem blackEval_rename {n : ℕ} (i : KLR.Seq (stendhalWeight ℓ ν)) (v : Fin n → Fin m)
    (hv : ∀ c, (i.1 (v c)).isLeft) (g : MvPolynomial (Fin n) k) :
    blackEval i (rename v g) = rename v g := by
  have : (blackEval (k := k) i).comp (rename v) = rename v :=
    algHom_ext fun c => by simp [blackEval_X, hv c]
  exact DFunLike.congr_fun this g

omit [DecidableEq I] in
/-- `blackEval` intertwines the permutations of variables and of sequences. -/
theorem blackEval_rename_perm (i : KLR.Seq (stendhalWeight ℓ ν)) (w : Perm (Fin m))
    (f : MvPolynomial (Fin m) k) :
    blackEval (w • i) (rename w f) = rename w (blackEval i f) := by
  have : (blackEval (k := k) (w • i)).comp (rename w) = (rename w).comp (blackEval i) :=
    algHom_ext fun c => by
      simp only [AlgHom.comp_apply, rename_X, blackEval_X, KLR.Seq.smul_apply,
        Equiv.symm_apply_apply]
      split_ifs <;> simp
  exact DFunLike.congr_fun this f

/-- `blackEval` commutes with the divided difference at two positions with equal labels. -/
theorem blackEval_ddiff (i : KLR.Seq (stendhalWeight ℓ ν)) {a b : Fin m} (hab : a ≠ b)
    (h : i.1 a = i.1 b) (f : MvPolynomial (Fin m) k) :
    blackEval i (ddiff a b f) = ddiff a b (blackEval i f) := by
  have hs : ∀ g : MvPolynomial (Fin m) k,
      blackEval i (rename (swap a b) g) = rename (swap a b) (blackEval i g) := by
    have e : swap a b • i = i := swap_smul_eq_self h
    intro g
    have := blackEval_rename_perm (k := k) i (swap a b) g
    rwa [e] at this
  have ha : (i.1 a).isLeft := isLeft_of_lbl_eq hab h
  have hb : (i.1 b).isLeft := h ▸ ha
  symm
  apply ddiff_eq_of_mul hab
  have := congrArg (blackEval i) (ddiff_spec hab f)
  rw [map_mul, map_sub, map_sub, blackEval_X, blackEval_X, hs] at this
  simpa [ha, hb] using this

variable (Γ Λ) in
/-- The polynomials `P₂ = stP` with the variables of the red strands set to zero, and `1`
between red strands: `∏_{e : a → b} Q_e` between black strands, `u₂ ^ α_a^∨(λ_r)` for a black
`a`-strand left of `λ_r`, and `1` otherwise. -/
noncomputable def stBlackP : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k
  | .inl a, .inl b => Γ.edgeProd a b
  | .inl a, .inr r => X 1 ^ Λ r a
  | .inr _, .inl _ => 1
  | .inr _, .inr _ => 1

/-- **Killing the red variables intertwines the crossings** for `stP` and `stBlackP`, unless
two red strands are exchanged. -/
theorem blackEval_crossComp (t : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (h : j + 1 < m)
    (hr : (t.1 ⟨j, by omega⟩).isLeft ∨ (t.1 ⟨j + 1, h⟩).isLeft) (f : MvPolynomial (Fin m) k) :
    blackEval (sadj m j • t) (crossComp (stP Γ Λ) j h t f) =
      crossComp (stBlackP Γ Λ) j h t (blackEval t f) := by
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  by_cases hc : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩
  · have e : sadj m j • t = t := by rw [sadj_eq h]; exact swap_smul_eq_self hc
    simp only [crossComp, hc, e, ↓reduceIte]
    exact blackEval_ddiff t hne hc f
  · simp only [crossComp, hc, ↓reduceIte, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul]
    rw [blackEval_rename_perm]
    congr 1
    have h0 : (sadj m j • t).1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ := by
      rw [KLR.Seq.smul_apply, sadj_eq h, symm_swap, swap_apply_left]
    have h1 : (sadj m j • t).1 ⟨j + 1, h⟩ = t.1 ⟨j, by omega⟩ := by
      rw [KLR.Seq.smul_apply, sadj_eq h, symm_swap, swap_apply_right]
    simp only [KLR.Seq.lbl] at hc ⊢
    rcases hx : t.1 ⟨j, by omega⟩ with a | r <;> rcases hy : t.1 ⟨j + 1, h⟩ with b | r'
    · simp only [hx, hy] at h0 h1
      exact blackEval_rename _ _ (fun c => by fin_cases c <;> simp [h0, h1]) _
    · simp only [hx, hy] at h0 h1
      simp [stP, stBlackP, blackEval_X, h0, h1]
    · simp [stP, stBlackP]
    · rw [hx, hy] at hr
      simp at hr

/-- The word `ρ`, applied to `i` from the right, never exchanges two red strands. -/
def NoRedCross : List ℕ → KLR.Seq (stendhalWeight ℓ ν) → Prop
  | [], _ => True
  | j :: ρ, i => NoRedCross ρ i ∧ ∀ h : j + 1 < m,
      ((wordProd m ρ • i).1 ⟨j, by omega⟩).isLeft ∨ ((wordProd m ρ • i).1 ⟨j + 1, h⟩).isLeft

/-- **Killing the red variables intertwines the words** for `stP` and `stBlackP`, for words
that never exchange two red strands. -/
theorem blackEval_wordComp (ρ : List ℕ) (i : KLR.Seq (stendhalWeight ℓ ν)) (hρ : NoRedCross ρ i)
    (f : MvPolynomial (Fin m) k) :
    blackEval (wordProd m ρ • i) (wordComp (stP Γ Λ) ρ i f) =
      wordComp (stBlackP Γ Λ) ρ i (blackEval i f) := by
  induction ρ generalizing f with
  | nil => simp [wordComp]
  | cons j ρ ih =>
    obtain ⟨hρ', hj⟩ := hρ
    rw [TypeA.wordProd_cons, mul_smul]
    by_cases h : j + 1 < m
    · simp only [wordComp, h, ↓reduceDIte, LinearMap.coe_comp, Function.comp_apply]
      rw [blackEval_crossComp _ j h (hj h), ih hρ']
    · simp [wordComp, h]

/-- A word exchanging two red strands acts by zero in the polynomial representation for
`stP`, which vanishes between red strands. -/
theorem wordComp_stP_eq_zero (ρ : List ℕ) (i : KLR.Seq (stendhalWeight ℓ ν))
    (hρ : ¬ NoRedCross ρ i) : wordComp (k := k) (stP Γ Λ) ρ i = 0 := by
  induction ρ with
  | nil => exact absurd trivial hρ
  | cons j ρ ih =>
    by_cases h : j + 1 < m
    · simp only [wordComp, h, ↓reduceDIte]
      by_cases hρ' : NoRedCross ρ i
      · have hj : ¬ (((wordProd m ρ • i).1 ⟨j, by omega⟩).isLeft ∨
            ((wordProd m ρ • i).1 ⟨j + 1, h⟩).isLeft) := fun hj =>
          hρ ⟨hρ', fun _ => hj⟩
        push Not at hj
        have hc : (wordProd m ρ • i).lbl ⟨j, by omega⟩ ≠ (wordProd m ρ • i).lbl ⟨j + 1, h⟩ :=
          fun e => by
            exact hj.1 (isLeft_of_lbl_eq (by simp [Fin.ext_iff]) e)
        obtain ⟨r, hr⟩ : ∃ r, (wordProd m ρ • i).1 ⟨j, by omega⟩ = .inr r := by
          rcases hx : (wordProd m ρ • i).1 ⟨j, by omega⟩ with a | r
          · rw [hx] at hj; simp at hj
          · exact ⟨r, rfl⟩
        obtain ⟨r', hr'⟩ : ∃ r', (wordProd m ρ • i).1 ⟨j + 1, h⟩ = .inr r' := by
          rcases hx : (wordProd m ρ • i).1 ⟨j + 1, h⟩ with a | r'
          · rw [hx] at hj; simp at hj
          · exact ⟨r', rfl⟩
        have hrr : (Sum.inr r : I ⊕ Fin ℓ) ≠ .inr r' := by rw [← hr, ← hr']; exact hc
        refine LinearMap.ext fun f => ?_
        simp only [crossComp, hrr, ↓reduceIte, KLR.Seq.lbl, hr, hr', stP, map_zero,
          LinearMap.coe_comp,
          Function.comp_apply, LinearMap.mulLeft_apply, zero_mul, LinearMap.zero_apply]
      · rw [ih hρ', LinearMap.comp_zero]
    · simp [wordComp, h]

/-- A crossing transports the variable of a red strand to its new position. -/
theorem crossComp_X_mul (P : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (j : ℕ) (h : j + 1 < m) {c : Fin m}
    (hc : ¬ (t.1 c).isLeft) (f : MvPolynomial (Fin m) k) :
    crossComp P j h t (X c * f) = X (sadj m j c) * crossComp P j h t f := by
  by_cases he : t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩
  · have hl : (t.1 ⟨j, by omega⟩).isLeft := isLeft_of_lbl_eq (by simp [Fin.ext_iff]) he
    have hl' : (t.1 ⟨j + 1, h⟩).isLeft := by
      rw [← show t.1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ from he]; exact hl
    have h0 : c ≠ ⟨j, by omega⟩ := fun e => hc (e ▸ hl)
    have h1 : c ≠ ⟨j + 1, h⟩ := fun e => hc (e ▸ hl')
    have hs : sadj m j c = c := by rw [sadj_eq h, swap_apply_of_ne_of_ne h0 h1]
    simp only [crossComp, he, ↓reduceIte, hs]
    exact ddiff_mul_of_rename_eq (by simp [Fin.ext_iff])
      (by rw [rename_X, swap_apply_of_ne_of_ne h0 h1]) f
  · simp only [crossComp, he, ↓reduceIte, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, rename_X]
    ring

/-- **The variable of a red strand is transported along a word.** -/
theorem wordComp_X_mul (P : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k) (ρ : List ℕ)
    (i : KLR.Seq (stendhalWeight ℓ ν)) {c : Fin m} (hc : ¬ (i.1 c).isLeft)
    (f : MvPolynomial (Fin m) k) :
    wordComp P ρ i (X c * f) = X (wordProd m ρ c) * wordComp P ρ i f := by
  induction ρ generalizing f with
  | nil => simp [wordComp]
  | cons j ρ ih =>
    by_cases h : j + 1 < m
    · have hc' : ¬ ((wordProd m ρ • i).1 (wordProd m ρ c)).isLeft := by
        rwa [KLR.Seq.smul_apply, Equiv.symm_apply_apply]
      simp only [wordComp, h, ↓reduceDIte, LinearMap.coe_comp, Function.comp_apply]
      rw [ih, crossComp_X_mul P _ j h hc', TypeA.wordProd_cons, Perm.mul_apply]
    · simp [wordComp, h]

/-! ### Faithfulness on the black strands -/

section Faithful

variable (P : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
  (ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
  (s : Finset (KLR.Seq (stendhalWeight ℓ ν) × Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) ×
    (Fin (Multiset.card (stendhalWeight ℓ ν)) →₀ ℕ)))
  (c : KLR.Seq (stendhalWeight ℓ ν) × Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) ×
    (Fin (Multiset.card (stendhalWeight ℓ ν)) →₀ ℕ) → k)

/-- The component from `Pol_i` to `Pol_t` of `∑_{b ∈ s} c_b ψ_{ρ w} x^u 1_i` (`b = (i, w, u)`),
when `ρ w` is a word for `w`. -/
noncomputable def blockSum (i t : KLR.Seq (stendhalWeight ℓ ν)) :
    MvPolynomial (Fin m) k →ₗ[k] MvPolynomial (Fin m) k :=
  ∑ b ∈ s with b.1 = i ∧ b.2.1 • i = t,
    c b • (wordComp P (ρ b.2.1) i ∘ₗ LinearMap.mulLeft k (monomial b.2.2 1))

variable {ρ} in
/-- Within one block, the variable of a red strand is transported to a single position. -/
theorem exists_blockSum_X_mul (hρ : ∀ w, wordProd m (ρ w) = w)
    (i t : KLR.Seq (stendhalWeight ℓ ν)) {a : Fin m} (ha : ¬ (i.1 a).isLeft) :
    ∃ q : Fin m, ∀ h, blockSum P ρ s c i t (X a * h) = X q * blockSum P ρ s c i t h := by
  obtain ⟨r, hr⟩ : ∃ r, i.1 a = .inr r := by
    rcases hx : i.1 a with x | r
    · rw [hx] at ha; simp at ha
    · exact ⟨r, rfl⟩
  by_cases hex : ∃ b ∈ s, b.1 = i ∧ b.2.1 • i = t
  · obtain ⟨b₀, -, -, hb₀⟩ := hex
    refine ⟨b₀.2.1 a, fun h => ?_⟩
    simp only [blockSum, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨-, rfl, hbt⟩ := Finset.mem_filter.1 hb
    have hq : b.2.1 a = b₀.2.1 a := by
      refine eq_of_lbl_eq_inr (i := t) (r := r) ?_ ?_
      · rw [← hbt, KLR.Seq.smul_apply, Equiv.symm_apply_apply, hr]
      · rw [← hb₀, KLR.Seq.smul_apply, Equiv.symm_apply_apply, hr]
    rw [mul_left_comm, wordComp_X_mul P _ _ ha, hρ, hq, mul_smul_comm]
  · refine ⟨a, fun h => ?_⟩
    have he : s.filter (fun b => b.1 = i ∧ b.2.1 • i = t) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun b hb hb' => hex ⟨b, hb, hb'⟩
    simp [blockSum, he]

omit [DecidableEq I] in
theorem blackEval_C (i : KLR.Seq (stendhalWeight ℓ ν)) (x : k) :
    blackEval i (C x : MvPolynomial (Fin m) k) = C x :=
  (blackEval i).commutes x

variable {ρ} in
/-- A block vanishing on the polynomials in the black variables vanishes. -/
theorem blockSum_eq_zero (hρ : ∀ w, wordProd m (ρ w) = w) (i t : KLR.Seq (stendhalWeight ℓ ν))
    (h0 : ∀ h, blackEval i h = h → blockSum P ρ s c i t h = 0) (h : MvPolynomial (Fin m) k) :
    blockSum P ρ s c i t h = 0 := by
  suffices H : ∀ p g : MvPolynomial (Fin m) k, blackEval i g = g →
      blockSum P ρ s c i t (p * g) = 0 by
    simpa using H h 1 (map_one _)
  intro p
  induction p using MvPolynomial.induction_on with
  | C x =>
    intro g hg
    exact h0 _ (by rw [map_mul, blackEval_C, hg])
  | add p p' hp hp' =>
    intro g hg
    rw [add_mul, map_add, hp g hg, hp' g hg, add_zero]
  | mul_X p a hp =>
    intro g hg
    by_cases ha : (i.1 a).isLeft
    · rw [mul_assoc]
      exact hp _ (by simp only [map_mul, hg, blackEval_X, ha, ↓reduceIte])
    · obtain ⟨q, hq⟩ := exists_blockSum_X_mul P s c hρ i t ha
      rw [mul_comm p, mul_assoc, hq, hp g hg, mul_zero]

variable {ρ} in
/-- **Faithfulness on the black strands**: if `P` has non-zero-divisor values and a combination
of the operators `ψ_{ρ w} x^u 1_i` vanishes, in every block, on the polynomials in the
variables of the black strands, then its coefficients vanish. -/
theorem eq_zero_of_blockSum_eq_zero
    (hP : ∀ a b, a ≠ b → ∀ f : Fin 2 → Fin m, Function.Injective f →
      IsRegular (rename f (P a b)))
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (h0 : ∀ i t h, blackEval i h = h → blockSum P ρ s c i t h = 0) :
    ∀ b ∈ s, c b = 0 := by
  have hρ' : ∀ w, wordProd m (ρ w) = w := fun w => (hρ w).2
  refine linearIndependent_iff'.1 (linearIndependent_opΨw_of_isRegular hP ρ hρ) s c ?_
  refine LinearMap.ext fun g => funext fun t => ?_
  have hb : ∀ i, blockSum P ρ s c i t (g i) = 0 := fun i =>
    blockSum_eq_zero P s c hρ' i t (h0 i t) (g i)
  trans ∑ i, blockSum P ρ s c i t (g i)
  swap
  · simp [hb]
  simp only [blockSum, LinearMap.sum_apply, Finset.sum_filter]
  rw [Finset.sum_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e1 : opE b.1 g = Pi.single b.1 (g b.1) := by
    funext t'; rw [opE_apply]; by_cases ht : t' = b.1 <;> simp [ht]
  have e2 : mulMono b.2.2 (Pi.single b.1 (g b.1) : KLR.PolyRep.Pol k _) =
      Pi.single b.1 (monomial b.2.2 1 * g b.1) := by
    funext t'; rw [mulMono_apply]; by_cases ht : t' = b.1 <;> simp [ht]
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, opΨw_single,
    hρ', Pi.smul_apply, Finset.sum_eq_single b.1]
  · by_cases ht : b.2.1 • b.1 = t
    · subst ht; simp
    · simp [ht]
  · intro i _ hi; simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

end Faithful

end Categorification.Stendhal
