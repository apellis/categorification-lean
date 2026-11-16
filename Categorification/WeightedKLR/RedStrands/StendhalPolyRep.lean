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

end Categorification.Stendhal
