/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.K0Relations
import Categorification.KLR.Gamma

/-!
# The homomorphism `γ : _𝒜 f → K₀(R)` for an arbitrary Cartan datum (KL II)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, paragraph "Grothendieck group as the quantum group" (before
Theorem 8): "As in [KL I, Section 3.1] we define a homomorphism … `γ : _𝒜 f → K₀(R)` which takes
the product of divided powers `θ_{i_1}^{(n_1)} ⋯ θ_{i_r}^{(n_r)}` to `[P_i]`, where
`i = i_1^{(n_1)} ⋯ i_r^{(n_r)}`."

This is the KL II version of `Categorification.KLR.Gamma` (namespace `KLR.KLGamma`), for a
Cartan datum `C` (`QuantumGroup.CartanDatum`: symmetric, `i · i ∈ 2ℤ_{>0}`,
`2 (i·j)/(i·i) ∈ ℤ_{≤ 0}`), the rings `R(ν) = R2 k C ν` and the KL II grading
`klGradingDatum2 k C` (`deg x_{a,i} = i_a · i_a`, `deg ψ_{k,i} = -i_k · i_{k+1}`), over any
commutative ring `k`. As in KL I, `'f`, `f`, `_𝒜 f` are Lusztig's algebras over `ℚ(v)` for `C`
(`C.F`, `C.Af`, with `(θ_i, θ_i) = (1 - v_i^{-2})⁻¹`, `v_i = v^{(i·i)/2}`), and `K₀(R)` is base
changed along `q ↦ v⁻¹` (`KLGamma.qToV`).

## Main definitions and results

* `clsSeq2 k C l = [P_l]`, `clsDiv2 k C d = [P_d]` in `K₀(R) = ⊕_ν K₀(R(ν))`, with
  `clsSeq2_append` (`[P_l][P_{l'}] = [P_{ll'}]`), `clsSeq2_nil`, and
  `clsSeq2_expandDiv` : `[P_î] = i! [P_i]`, `i! = ∏_a [n_a]_{q_{i_a}}^!`, `q_c = q^{(c·c)/2}`.
* `clsDiv2_serre` : **the quantum Serre relation in `K₀(R)`** (from KL II, Proposition 6 /
  Corollary 7): for `i ≠ j` and `N = 1 - 2(i·j)/(i·i) = d_ij + 1`, for all divided-power
  contexts `d'`, `d''`,
  `∑_{n=0}^{N} (-1)^n [P_{d' i^{(n)} j i^{(N-n)} d''}] = 0`; equivalently
  (`clsDiv2_serre_even_odd`) `∑_{n even} [P_{…i^{(n)} j i^{(N-n)}…}] = ∑_{n odd} [P_{…}]`. There
  are no extra grading shifts.
* `K0Q2 k C = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` (`q ↦ v⁻¹`), `toK0Q2`, `toK0Q2_smul`.
* `gammaQ2 k C : 'f →ₐ[ℚ(v)] K0Q2 k C`, `θ_i ↦ [P_i]`; `gammaQ2_word`, `gammaQ2_dpow`
  (`θ_i^{(a)} ↦ [P_{i^{(a)}}]`, divided powers in `v_i`), `gammaQ2_dpowMono`
  (`θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)} ↦ [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`).
* `gammaQ2_serreDiv` (Lusztig's divided-power Serre elements, `PreF.serreDiv`) and
  `gammaQ2_serreSeq` (the Serre elements `x_N` of `CartanDatum.serreSet`) lie in the kernel;
  `gammaQ2_eq_zero_of_mem_span` : the two-sided ideal they generate lies in `ker γ`.
* `gammaF2 k C hGK : f →ₐ[ℚ(v)] K0Q2 k C` (KL's `γ_{ℚ(q)}`) **under the explicit hypothesis**
  `hGK : C.GabberKac vQ C.c` (the quantum Gabber–Kac theorem for `C`, Lusztig 33.1.3, not proved
  in this repository), with `gammaF2_dpowMono`.
* `gammaF2_mem_range`, `gammaA2 k C hGK : _𝒜 f →+* (toK0Q2 k C).range`, and, **if `toK0Q2 k C`
  is injective**, `gammaInt2 k C hGK hinj : _𝒜 f →+* K₀(R)` with `gammaInt2_dpowMono` and
  `gammaInt2_smul` (`ℤ[q, q⁻¹]`-linearity).

Injectivity (KL II: "Due to the quantum Gabber–Kac theorem, this homomorphism is injective") is
`Categorification.KLR.KL2.Prop34KL2`. Surjectivity (Theorem 8) is not formalized here.
-/

noncomputable section

namespace Categorification.KLR.KL2Gamma

open Graded KLRAlgebra LaurentPolynomial QuantumGroup KL2 KLGamma Finset

/-! ### List lemmas -/

section Lists

theorem getElem_append_mid {α : Type*} (L1 mid L2 : List α) {r : ℕ} (h1 : L1.length ≤ r)
    (h2 : r < L1.length + mid.length) (hr : r < (L1 ++ mid ++ L2).length) :
    (L1 ++ mid ++ L2)[r] = mid[r - L1.length]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right h1]

theorem getElem_append_mid_congr {α : Type*} (L1 mid mid' L2 : List α)
    (hl : mid.length = mid'.length) {r : ℕ}
    (h : r < L1.length ∨ L1.length + mid.length ≤ r) (hr : r < (L1 ++ mid ++ L2).length)
    (hr' : r < (L1 ++ mid' ++ L2).length) :
    (L1 ++ mid ++ L2)[r] = (L1 ++ mid' ++ L2)[r] := by
  rcases h with h | h
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h,
      List.getElem_append_left (by simp; omega), List.getElem_append_left h]
  · rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega)]
    congr 1
    simp [hl]

theorem getElem_midL {α : Type*} (i j : α) (n M r : ℕ)
    (hr : r < (List.replicate n i ++ j :: List.replicate M i).length) :
    (List.replicate n i ++ j :: List.replicate M i)[r] = if r = n then j else i := by
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp only [List.length_replicate] at h1; omega
  · simp
  · simp only [List.length_replicate] at h1 ⊢
    rw [List.getElem_cons, dif_pos (by omega)]
  · simp only [List.length_replicate] at h1 ⊢
    rw [List.getElem_cons, dif_neg (by omega)]
    simp

end Lists

variable {I : Type*} [DecidableEq I] (k : Type*) [CommRing k] (C : CartanDatum I)

local notation "G2" => klGradingDatum2 k C

/-! ### Classes of the projectives `P_l` and `P_d` -/

section Classes

/-- The class `[P_l] ∈ K₀(R(ν)) ⊆ K₀(R)`, `ν = |l|`, of `P_l = R(ν) 1_l` (KL II grading). -/
def clsSeq2 (l : List I) : (G2).K0R :=
  DirectSum.of (G2).K0fam (l : Multiset I) (K0.of (projSeq2 k C (Seq.ofList l rfl)))

theorem clsSeq2_eq {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    clsSeq2 k C l = DirectSum.of (G2).K0fam ν (K0.of (projSeq2 k C (Seq.ofList l h))) := by
  subst h; rfl

/-- The class `[P_d] ∈ K₀(R(ν)) ⊆ K₀(R)` of `P_d = R(ν) ψ(1_d) {-⟨d⟩}` for a divided-power
expression `d` (KL II grading). -/
def clsDiv2 (d : List (I × ℕ)) : (G2).K0R :=
  DirectSum.of (G2).K0fam (expandDiv d : Multiset I) (K0.of (projDiv2 k C d rfl))

theorem clsDiv2_eq {ν : Multiset I} (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    clsDiv2 k C d = DirectSum.of (G2).K0fam ν (K0.of (projDiv2 k C d h)) := by
  subst h; rfl

/-- **`[P_l] [P_{l'}] = [P_{ll'}]`** in `K₀(R)`. -/
theorem clsSeq2_append (l l' : List I) :
    clsSeq2 k C (l ++ l') = clsSeq2 k C l * clsSeq2 k C l' := by
  unfold clsSeq2
  rw [(G2).K0R_of_mul_of, ← clsSeq2, clsSeq2_eq k C (l ++ l') (Multiset.coe_add l l').symm,
    seq_ofList_append]
  congr 1
  simp only [projSeq2]
  rw [(G2).indK0_ofIdempotent]
  exact K0.of_ofIdempotent_congr (concat_e_tmul_e _ _).symm _ _ _ _

/-- `[P_∅] = [R(0)] = 1` in `K₀(R)`. -/
theorem clsSeq2_nil : clsSeq2 k C [] = 1 := by
  rw [(G2).K0R_one, clsSeq2]
  congr 1
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso]
  refine K0.of_ofIdempotent_congr ?_ _ _ _ _
  have := sum_e (k := k) (Q := klQ2 k C) (ν := 0)
  rwa [Fintype.sum_unique,
    ← Subsingleton.elim (α := Seq (0 : Multiset I)) (Seq.ofList [] rfl) default] at this

theorem K0R_of_smul2 (p : LaurentPolynomial ℤ) {ν : Multiset I} (y : K0 ((G2).grade ν)) :
    DirectSum.of (G2).K0fam ν (p • y) = p • (DirectSum.of (G2).K0fam ν y : (G2).K0R) := by
  rw [← DirectSum.lof_eq_of (LaurentPolynomial ℤ), ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
    map_smul]

/-- **`[P_î] = i! [P_i]`** in `K₀(R)`, `i! = ∏_a [n_a]_{q_{i_a}}^!` (KL II grading). -/
theorem clsSeq2_expandDiv (d : List (I × ℕ)) :
    clsSeq2 k C (expandDiv d) = divQFact2 C d • clsDiv2 k C d := by
  rw [clsSeq2, clsDiv2, K0_projSeq2_expandDiv d rfl, K0R_of_smul2]

end Classes

/-! ### The quantum Serre relation in `K₀(R)` -/

section Serre

variable {C}

omit [DecidableEq I] in
/-- For `i ≠ j`, `N = 1 - 2(i·j)/(i·i)` equals `d_ij + 1`. -/
theorem serreN_eq_dij {i j : I} (hij : i ≠ j) : C.serreN i j = C.dij i j + 1 := by
  have h1 := C.two_mul_dot_eq hij
  have h2 := C.dij_mul hij
  have hpos := C.dot_self_pos i
  have : C.dot i i * ((C.serreN i j : ℤ) - C.dij i j - 1) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.1 this with h | h
  · omega
  · omega

omit [DecidableEq I] in
theorem expandDiv_serre (d' d'' : List (I × ℕ)) (i j : I) (n M : ℕ) :
    expandDiv (d' ++ [(i, n), (j, 1), (i, M)] ++ d'') =
      expandDiv d' ++ (List.replicate n i ++ j :: List.replicate M i) ++ expandDiv d'' := by
  simp [expandDiv_append, expandDiv]

variable (C) in
omit [DecidableEq I] in
/-- The grading shift `⟨d' i^{(n)} j i^{(M)} d''⟩`. -/
theorem divAngle2_serre (d' d'' : List (I × ℕ)) (i j : I) (n M : ℕ) :
    divAngle2 C (d' ++ [(i, n), (j, 1), (i, M)] ++ d'') = divAngle2 C d' + divAngle2 C d'' +
      C.dot i i / 2 * ((n.choose 2 : ℕ) + (M.choose 2 : ℕ) : ℤ) := by
  simp only [divAngle2_append]
  simp [divAngle2]
  ring

variable (C) in
/-- **The quantum Serre relation in `K₀(R)`** (KL II, Proposition 6 / Corollary 7): for
`i ≠ j`, `N = 1 - 2(i·j)/(i·i)` (`= d_ij + 1`) and divided-power contexts `d'`, `d''`,
`∑_{n=0}^{N} (-1)^n [P_{d' i^{(n)} j i^{(N-n)} d''}] = 0`, where
`P_d = R(ν) ψ(1_d) {-⟨d⟩}` (KL II grading). -/
theorem clsDiv2_serre (d' d'' : List (I × ℕ)) {i j : I} (hij : i ≠ j) :
    ∑ n ∈ range (C.serreN i j + 1), ((-1 : LaurentPolynomial ℤ) ^ n) •
      clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') = 0 := by
  set N := C.serreN i j with hNdef
  have hN : N = C.dij i j + 1 := serreN_eq_dij hij
  set L1 := expandDiv d' with hL1
  set L2 := expandDiv d'' with hL2
  set mid : ℕ → List I := fun n => List.replicate n i ++ j :: List.replicate (N - n) i with hmid
  have hexp : ∀ n, expandDiv (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'') = L1 ++ mid n ++ L2 :=
    fun n => expandDiv_serre d' d'' i j n (N - n)
  have hmidlen : ∀ n, n ≤ N → (mid n).length = N + 1 := fun n hn => by
    simp only [hmid, List.length_append, List.length_replicate, List.length_cons]; omega
  set ν : Multiset I := (expandDiv (d' ++ [(i, 0), (j, 1), (i, N - 0)] ++ d'') : Multiset I)
    with hν
  have hνn : ∀ n, n ≤ N →
      (expandDiv (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'') : Multiset I) = ν := fun n hn => by
    rw [hν, hexp, hexp]
    refine Multiset.coe_eq_coe.2 ((List.Perm.append_left L1 ?_).append_right L2)
    simp only [hmid]
    refine List.perm_middle.trans ?_
    rw [← List.replicate_add, show n + (N - n) = N by omega]
    simp
  set t : Seq ν := Seq.ofList (expandDiv (d' ++ [(i, 0), (j, 1), (i, N - 0)] ++ d'')) rfl
    with ht_def
  set p := L1.length with hp
  set bs := ctxBlocks d' d'' (N + 1) with hbs_def
  have hm : Multiset.card ν = L1.length + (N + 1) + L2.length := by
    rw [hν, Multiset.coe_card, hexp, List.length_append, List.length_append, hmidlen 0 (by omega)]
  have hpN : p + N < Multiset.card ν := by rw [hm]; omega
  have hlbl : ∀ n (hn : n ≤ N) (s : Seq ν)
      (_ : s = Seq.ofList (expandDiv (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'')) (hνn n hn))
      (r : Fin (Multiset.card ν)), s.lbl r = (L1 ++ mid n ++ L2)[(r : ℕ)]'(by
        have := r.2; have := hm
        rw [List.length_append, List.length_append, hmidlen n hn]; omega) := by
    intro n hn s hs r
    subst hs
    rw [Seq.ofList_lbl]
    exact List.getElem_of_eq (hexp n) _
  have hlbl0 := hlbl 0 (Nat.zero_le _) t rfl
  have ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j := fun r hr => by
    rw [hlbl0, getElem_append_mid _ _ _ (by omega) (by rw [hmidlen 0 (by omega)]; omega),
      getElem_midL, if_pos (by omega)]
  have ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i :=
    fun r h1 h2 => by
      rw [hlbl0, getElem_append_mid _ _ _ (by omega) (by rw [hmidlen 0 (by omega)]; omega),
        getElem_midL, if_neg (by omega)]
  have hb : IsBlocks t bs := by
    have h := isBlocks_ctxBlocks d' [(i, 0), (j, 1), (i, N - 0)] d'' (ν := ν) rfl
    have hl : (expandDiv [(i, 0), (j, 1), (i, N - 0)]).length = N + 1 := by
      simp [expandDiv]
    rw [hl] at h
    exact h.sublist (List.sublist_append_right _ _)
  have hbs : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1 := fun b hb' => by
    have := ctxBlocks_avoid d' d'' (N + 1) b hb'
    rw [← hL1] at this
    omega
  have hSeq : ∀ n (hn : n ≤ N), serreSeq t p n =
      Seq.ofList (expandDiv (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'')) (hνn n hn) := by
    intro n hn
    apply Subtype.ext; funext r
    change (serreSeq t p n).lbl r = (Seq.ofList _ (hνn n hn)).lbl r
    rw [lbl_serreSeq hpN ht₀ ht hn r, hlbl n hn _ rfl r]
    split_ifs with h1 h2
    · rw [getElem_append_mid _ _ _ (by omega) (by rw [hmidlen n hn]; omega), getElem_midL,
        if_pos (by omega)]
    · rw [getElem_append_mid _ _ _ (by omega) (by rw [hmidlen n hn]; omega), getElem_midL,
        if_neg (by omega)]
    · rw [hlbl0]
      exact getElem_append_mid_congr _ _ _ _ (by rw [hmidlen 0 (by omega), hmidlen n hn])
        (by rw [hmidlen 0 (by omega)]; omega) _ _
  have hIdem : ∀ n (hn : n ≤ N),
      (divIdemOf (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'') (hνn n hn) : R2 k C ν) =
        serreIdem t p N bs n := by
    intro n hn
    rw [divIdemOf_append_mid d' [(i, n), (j, 1), (i, N - n)] d'' (hνn n hn)]
    have hl : (expandDiv [(i, n), (j, 1), (i, N - n)]).length = N + 1 := by
      simp [expandDiv]; omega
    rw [hl, serreIdem_eq_divIdem (k := k) (C := C) hbs hn, hSeq n hn,
      ← divIdem_bigBlocks _ ((p, n) :: _ :: _), ← divIdem_bigBlocks _ (bigBlocks _ ++ _)]
    congr 1
    simp [bigBlocks, blocksDiv, hbs_def, ctxBlocks, List.filter_append, List.filter_filter, hp,
      hL1, List.filter_cons]
    by_cases h1 : 2 ≤ n <;> by_cases h2 : 2 ≤ N - n <;> simp [h1, h2, List.filter_cons]
  -- the shifts
  set sh : ℕ → ℤ := fun n => divAngle2 C (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'') with hsh_def
  have hsh : ∀ n, n < N → sh (n + 1) = sh n + (-((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
    intro n hn
    simp only [hsh_def, divAngle2_serre]
    have e1 : ((n + 1).choose 2 : ℤ) = (n.choose 2 : ℕ) + n := by
      rw [NilHecke.choose_two_succ]; push_cast; ring
    have e2 : ((N - n).choose 2 : ℤ) = ((N - (n + 1)).choose 2 : ℕ) + ((N - n - 1 : ℕ) : ℤ) := by
      rw [show N - n = (N - (n + 1)) + 1 by omega, NilHecke.choose_two_succ]; push_cast
      rw [show N - (n + 1) = N - n - 1 by omega]
    have e3 : ((N - n - 1 : ℕ) : ℤ) = N - n - 1 := by omega
    obtain ⟨r, hr⟩ := C.dot_self_even i
    have e4 : C.dot i i / 2 = r := by omega
    have e5 := C.two_mul_dot_eq hij
    rw [← hNdef] at e5
    rw [e1, e2, e3, e4]
    rw [hr] at e5 ⊢
    have e6 : C.dot i j = r * (1 - N) := by linarith
    linear_combination e6
  let P : ℕ → K0 ((G2).grade ν) := fun n => if hn : n ≤ N then
    K0.of (GProj.ofIdempotent (hflip (serreIdem t p N bs n : R2 k C ν))
      (isIdempotentElem_hflip_serreIdem hpN ht₀ ht hb hbs hij hn)
      (hflip_serreIdem_mem_grade hpN ht₀ ht hb hbs hn)) else 0
  have hP : ∀ n (hn : n ≤ N), P n = K0.of (GProj.ofIdempotent (hflip (serreIdem t p N bs n :
      R2 k C ν)) (isIdempotentElem_hflip_serreIdem hpN ht₀ ht hb hbs hij hn)
      (hflip_serreIdem_mem_grade hpN ht₀ ht hb hbs hn)) := fun n hn => dif_pos hn
  have key : ∀ n ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ n) •
      clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, N - n)] ++ d'') =
        DirectSum.of (G2).K0fam ν (((-1 : LaurentPolynomial ℤ) ^ n * T (-sh n)) • P n) := by
    intro n hn'
    have hn : n ≤ N := by rw [mem_range] at hn'; omega
    rw [clsDiv2_eq k C _ (hνn n hn), hP n hn, K0R_of_smul2, mul_smul, ← K0R_of_smul2 k C (T _),
      projDiv2, ← K0.T_smul_of]
    congr 3
    exact K0.of_ofIdempotent_congr (congrArg hflip (hIdem n hn)) _ _ _ _
  rw [sum_congr rfl key, ← map_sum, K0_serre_window hpN ht₀ ht hb hbs hij hN sh hsh P hP,
    map_zero]

variable (C) in
/-- **The quantum Serre relation in `K₀(R)`, even/odd form** (KL II, Corollary 7 in `K₀`):
`∑_{n even} [P_{d' i^{(n)} j i^{(N-n)} d''}] = ∑_{n odd} [P_{d' i^{(n)} j i^{(N-n)} d''}]`,
`N = 1 - 2(i·j)/(i·i)`. -/
theorem clsDiv2_serre_even_odd (d' d'' : List (I × ℕ)) {i j : I} (hij : i ≠ j) :
    ∑ n ∈ serreEvens (C.serreN i j),
        clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') =
      ∑ n ∈ serreOdds (C.serreN i j),
        clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') := by
  have h := clsDiv2_serre k C d' d'' hij
  rw [← sum_filter_add_sum_filter_not _ Even] at h
  have hE : ∑ n ∈ (range (C.serreN i j + 1)).filter Even, ((-1 : LaurentPolynomial ℤ) ^ n) •
      clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') =
      ∑ n ∈ serreEvens (C.serreN i j),
        clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') := by
    refine sum_congr rfl fun n hn => ?_
    rw [(mem_filter.1 hn).2.neg_one_pow, one_smul]
  have hO : ∑ n ∈ (range (C.serreN i j + 1)).filter (fun n => ¬ Even n),
      ((-1 : LaurentPolynomial ℤ) ^ n) •
        clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') =
      -∑ n ∈ serreOdds (C.serreN i j),
        clsDiv2 k C (d' ++ [(i, n), (j, 1), (i, C.serreN i j - n)] ++ d'') := by
    rw [← sum_neg_distrib, serreOdds]
    refine sum_congr (by ext n; simp [Nat.not_even_iff_odd]) fun n hn => ?_
    rw [(mem_filter.1 hn).2.neg_one_pow, neg_one_smul]
  rw [hE, hO, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

end Serre

/-! ### `K₀(R)_{ℚ(v)} = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` with `q ↦ v⁻¹` -/

section K0Q

attribute [local instance] qToVAlgebra

/-- `K₀(R)_{ℚ(v)} = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` along `q ↦ v⁻¹` (KL II grading). -/
def K0Q2 : Type _ := TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (G2).K0R

instance : Ring (K0Q2 k C) :=
  inferInstanceAs (Ring (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (G2).K0R))

instance : Algebra (RatFunc ℚ) (K0Q2 k C) :=
  inferInstanceAs
    (Algebra (RatFunc ℚ) (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (G2).K0R))

/-- The ring map `K₀(R) → K₀(R)_{ℚ(v)}`, `x ↦ 1 ⊗ x`. -/
def toK0Q2 : (G2).K0R →+* K0Q2 k C :=
  (Algebra.TensorProduct.includeRight : (G2).K0R →ₐ[LaurentPolynomial ℤ]
    TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (G2).K0R).toRingHom

/-- `toK0Q2` is semilinear along `q ↦ v⁻¹`. -/
theorem toK0Q2_smul (p : LaurentPolynomial ℤ) (x : (G2).K0R) :
    toK0Q2 k C (p • x) = qToV p • toK0Q2 k C x := by
  change (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] (p • x) =
    (qToV p • (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x :
      TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (G2).K0R)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]
  rfl

end K0Q

/-! ### Quantum integers under `q ↦ v⁻¹` -/

section QInt

/-- `[n]_{q^h}` in `ℤ[q, q⁻¹]` specialises to `[n]_{v^h}` (bar invariance). -/
theorem qToV_qint_tUnit (h : ℤ) (n : ℕ) : qToV (qint (tUnit h) n) = qint (vQ ^ h) n := by
  rw [qint_tUnit, map_sum, qint_eq_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [qToV_T, ← zpow_mul]
  congr 2
  have : ((n - 1 - j : ℕ) : ℤ) = n - 1 - j := by omega
  rw [this]
  ring

theorem qToV_qfact_tUnit (h : ℤ) (n : ℕ) : qToV (qfact (tUnit h) n) = qfact (vQ ^ h) n := by
  simp only [qfact, map_prod, qToV_qint_tUnit]

omit [DecidableEq I] in
theorem qToV_divQFact2 (d : List (I × ℕ)) :
    qToV (divQFact2 C d) = (d.map fun q => qfact (PreF.vi C.dot vQ q.1) q.2).prod := by
  simp only [divQFact2, map_list_prod, List.map_map, Function.comp_def, qToV_qfact_tUnit]
  rfl

omit [DecidableEq I] in
theorem qToV_divQFact2_ne_zero (d : List (I × ℕ)) : qToV (divQFact2 C d) ≠ 0 := by
  rw [qToV_divQFact2]
  induction d with
  | nil => simp
  | cons q d ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_ne_zero (C.qfact_ne_zero _ _) ih

end QInt

/-! ### Products of `[P_d]` in `K₀(R)_{ℚ(v)}` -/

/-- **`[P_d] [P_{d'}] = [P_{dd'}]`** in `K₀(R)_{ℚ(v)}`. -/
theorem toK0Q2_clsDiv2_append (d d' : List (I × ℕ)) :
    toK0Q2 k C (clsDiv2 k C (d ++ d')) =
      toK0Q2 k C (clsDiv2 k C d) * toK0Q2 k C (clsDiv2 k C d') := by
  have e := clsSeq2_expandDiv k C (d ++ d')
  rw [expandDiv_append, clsSeq2_append, clsSeq2_expandDiv, clsSeq2_expandDiv,
    divQFact2_append] at e
  have e' := congrArg (toK0Q2 k C) e
  rw [map_mul, toK0Q2_smul, toK0Q2_smul, toK0Q2_smul, map_mul, smul_mul_smul_comm] at e'
  have hc := mul_ne_zero (qToV_divQFact2_ne_zero C d) (qToV_divQFact2_ne_zero C d')
  have e'' := congrArg (fun z => (qToV (divQFact2 C d) * qToV (divQFact2 C d'))⁻¹ • z) e'
  simp only [inv_smul_smul₀ hc] at e''
  exact e''.symm

theorem toK0Q2_clsDiv2_nil : toK0Q2 k C (clsDiv2 k C []) = 1 := by
  have e := clsSeq2_expandDiv k C []
  simp only [divQFact2, List.map_nil, List.prod_nil, one_smul] at e
  rw [← e]
  exact (congrArg _ (clsSeq2_nil k C)).trans (map_one _)

/-! ### `γ_{ℚ(q)}` on `'f` and on `f` -/

section GammaQ

/-- `w ↦ [P_w]`, a monoid homomorphism `FreeMonoid I → K₀(R)`. -/
def clsSeqHom2 : FreeMonoid I →* (G2).K0R where
  toFun w := clsSeq2 k C (FreeMonoid.toList w)
  map_one' := clsSeq2_nil k C
  map_mul' u w := by rw [FreeMonoid.toList_mul, clsSeq2_append]

/-- **`'f → K₀(R)_{ℚ(q)}`, `θ_i ↦ [P_i]`** (KL II §3, as in KL I §3.1). -/
def gammaQ2 : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] K0Q2 k C :=
  MonoidAlgebra.lift (RatFunc ℚ) (FreeMonoid I) (K0Q2 k C)
    ((toK0Q2 k C).toMonoidHom.comp (clsSeqHom2 k C))

/-- `γ(θ_{i_1} ⋯ θ_{i_k}) = [P_{i_1 ⋯ i_k}]`. -/
theorem gammaQ2_word (w : FreeMonoid I) :
    gammaQ2 k C (PreF.word w) = toK0Q2 k C (clsSeq2 k C (FreeMonoid.toList w)) := by
  rw [gammaQ2, PreF.word, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem gammaQ2_θ (i : I) : gammaQ2 k C (PreF.θ i) = toK0Q2 k C (clsSeq2 k C [i]) :=
  gammaQ2_word k C _

theorem gammaQ2_θ_pow (i : I) (a : ℕ) :
    gammaQ2 k C (PreF.θ i ^ a) = toK0Q2 k C (clsSeq2 k C (List.replicate a i)) := by
  induction a with
  | zero => rw [pow_zero, map_one, List.replicate_zero, clsSeq2_nil, map_one]
  | succ a ih =>
    rw [pow_succ, map_mul, ih, gammaQ2_θ, ← map_mul, ← clsSeq2_append, List.replicate_succ']

/-- `γ(θ_i^{(a)}) = [P_{i^{(a)}}]`, with `θ_i^{(a)} = θ_i^a / [a]_{v_i}^!`, `v_i = v^{(i·i)/2}`. -/
theorem gammaQ2_dpow (i : I) (a : ℕ) :
    gammaQ2 k C (PreF.dpow C.dot vQ i a) = toK0Q2 k C (clsDiv2 k C [(i, a)]) := by
  have e := clsSeq2_expandDiv k C [(i, a)]
  have hx : expandDiv [(i, a)] = List.replicate a i := by simp [expandDiv]
  rw [hx] at e
  rw [PreF.dpow, map_smul, gammaQ2_θ_pow, e, toK0Q2_smul, qToV_divQFact2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact inv_smul_smul₀ (C.qfact_ne_zero i a) _

/-- The divided-power monomial `θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)} ∈ 'f` for the Cartan datum `C`. -/
def dpowMono2 (d : List (I × ℕ)) : PreF (RatFunc ℚ) I :=
  (d.map fun q => PreF.dpow C.dot vQ q.1 q.2).prod

/-- **`γ(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`** (KL II §3). -/
theorem gammaQ2_dpowMono (d : List (I × ℕ)) :
    gammaQ2 k C (dpowMono2 C d) = toK0Q2 k C (clsDiv2 k C d) := by
  induction d with
  | nil => rw [dpowMono2, List.map_nil, List.prod_nil, map_one, toK0Q2_clsDiv2_nil]
  | cons q d ih =>
    rw [dpowMono2, List.map_cons, List.prod_cons, map_mul, ← dpowMono2, ih, gammaQ2_dpow,
      show q :: d = [q] ++ d from rfl, toK0Q2_clsDiv2_append]

/-- **`γ` kills Lusztig's divided-power Serre elements** (KL II, Corollary 7 in `K₀`):
`γ(∑_{a + b = N} (-1)^b θ_i^{(a)} θ_j θ_i^{(b)}) = 0` for `i ≠ j`, `N = 1 - 2(i·j)/(i·i)`. -/
theorem gammaQ2_serreDiv {i j : I} (hij : i ≠ j) :
    gammaQ2 k C (PreF.serreDiv C.dot vQ i j (C.serreN i j)) = 0 := by
  set N := C.serreN i j
  have hS := congrArg (toK0Q2 k C) (clsDiv2_serre k C [] [] hij)
  simp only [List.nil_append, List.append_nil, map_sum, map_zero, toK0Q2_smul, map_pow, map_neg,
    map_one] at hS
  have hterm : ∀ a b : ℕ, gammaQ2 k C (PreF.dpow C.dot vQ i a * PreF.θ j * PreF.dpow C.dot vQ i b)
      = toK0Q2 k C (clsDiv2 k C [(i, a), (j, 1), (i, b)]) := by
    intro a b
    rw [← gammaQ2_dpowMono]
    simp [dpowMono2, mul_assoc]
  rw [PreF.serreDiv, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_smul, hterm]
  have hsign : ∀ n ∈ range (N + 1), ((-1 : RatFunc ℚ) ^ (N - n)) =
      (-1) ^ N * (-1) ^ n := by
    intro n hn
    rw [mem_range] at hn
    have h1 : ((-1 : RatFunc ℚ) ^ (N - n)) * (-1) ^ n = (-1) ^ N := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [← h1, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
  rw [sum_congr rfl fun n hn => by rw [hsign n hn, mul_smul], ← smul_sum]
  simp only [Nat.succ_eq_add_one] at hS ⊢
  rw [hS, smul_zero]

/-- `γ` kills the Serre elements `x_N` of the Cartan datum (`CartanDatum.serreSet`), since
`x_N = [N]_{v_i}^! · ∑_{a+b=N} (-1)^b θ_i^{(a)} θ_j θ_i^{(b)}`. -/
theorem gammaQ2_serreSeq {i j : I} (hij : i ≠ j) :
    gammaQ2 k C (PreF.serreSeq C.dot vQ i j (C.serreN i j)) = 0 := by
  rw [C.serreSeq_eq_qfact_smul_serreDiv hij, map_smul, gammaQ2_serreDiv k C hij, smul_zero]

theorem gammaQ2_eq_zero_of_mem_serreSet {x : PreF (RatFunc ℚ) I} (hx : x ∈ C.serreSet vQ) :
    gammaQ2 k C x = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := hx
  exact gammaQ2_serreSeq k C hij

/-- **`γ_{ℚ(q)}` kills the Serre relations**: the two-sided ideal of `'f` generated by the Serre
elements of `C` lies in `ker γ_{ℚ(q)}`. -/
theorem gammaQ2_eq_zero_of_mem_span {x : PreF (RatFunc ℚ) I}
    (hx : x ∈ TwoSidedIdeal.span (C.serreSet vQ)) : gammaQ2 k C x = 0 := by
  have h : TwoSidedIdeal.span (C.serreSet (K := RatFunc ℚ) vQ) ≤
      (RingHom.ker (gammaQ2 k C)).toTwoSided := by
    rw [TwoSidedIdeal.span_le]
    intro y hy
    exact Ideal.mem_toTwoSided.2 (gammaQ2_eq_zero_of_mem_serreSet k C hy)
  exact Ideal.mem_toTwoSided.1 (h hx)

/-- The two-sided ideal of `'f` generated by the Serre elements of `C`. -/
abbrev serreIdealQ2 : Ideal (PreF (RatFunc ℚ) I) :=
  TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (C.serreSet vQ))

/-- `γ_{ℚ(q)}` on `'f/⟨Serre⟩` (unconditionally). -/
def gammaSerre2 : (PreF (RatFunc ℚ) I ⧸ serreIdealQ2 C) →ₐ[RatFunc ℚ] K0Q2 k C :=
  Ideal.Quotient.liftₐ (serreIdealQ2 C) (gammaQ2 k C)
    (fun _ ha => gammaQ2_eq_zero_of_mem_span k C (TwoSidedIdeal.mem_asIdeal.1 ha))

/-- **`γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}`** (KL II §3), under the explicit hypothesis `hGK` that the
quantum Gabber–Kac theorem holds for `C` (the radical of Lusztig's form is generated by the Serre
elements; Lusztig 33.1.3, not proved here). -/
def gammaF2 (hGK : C.GabberKac vQ C.c) : C.F →ₐ[RatFunc ℚ] K0Q2 k C :=
  Ideal.Quotient.liftₐ (PreF.radical C.dot vQ C.c) (gammaQ2 k C)
    (fun _ ha => gammaQ2_eq_zero_of_mem_span k C
      (TwoSidedIdeal.mem_asIdeal.1 (by rw [CartanDatum.GabberKac] at hGK; rw [hGK] at ha; exact ha)))

theorem gammaF2_π (hGK : C.GabberKac vQ C.c) (x : PreF (RatFunc ℚ) I) :
    gammaF2 k C hGK (PreF.π C.dot vQ C.c x) = gammaQ2 k C x := rfl

omit [DecidableEq I] in
theorem π_dpowMono2 (d : List (I × ℕ)) :
    PreF.π C.dot vQ C.c (dpowMono2 C d) =
      (d.map fun q => PreF.dpowF C.dot vQ C.c q.1 q.2).prod := by
  rw [dpowMono2, map_list_prod, List.map_map]
  rfl

/-- **KL II §3**: `γ(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]` in
`f` (under the Gabber–Kac hypothesis). -/
theorem gammaF2_dpowMono (hGK : C.GabberKac vQ C.c) (d : List (I × ℕ)) :
    gammaF2 k C hGK (PreF.π C.dot vQ C.c (dpowMono2 C d)) = toK0Q2 k C (clsDiv2 k C d) :=
  gammaQ2_dpowMono k C d

theorem gammaF2_dpowF (hGK : C.GabberKac vQ C.c) (i : I) (a : ℕ) :
    gammaF2 k C hGK (PreF.dpowF C.dot vQ C.c i a) = toK0Q2 k C (clsDiv2 k C [(i, a)]) :=
  gammaQ2_dpow k C i a

end GammaQ

/-! ### The integral form: `γ : _𝒜 f → K₀(R)` -/

section GammaA

omit [DecidableEq I] in
theorem algebraMap_qToV_mem_Af2 (p : LaurentPolynomial ℤ) :
    algebraMap (RatFunc ℚ) C.F (qToV p) ∈ C.Af := by
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Subring.zero_mem _
  | add p q hp hq => rw [map_add, map_add]; exact Subring.add_mem _ hp hq
  | single n m =>
    have : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, qToV_T]
    exact Subring.zsmul_mem _ (PreF.algebraMap_zpow_mem_Af (-n)) m

omit [DecidableEq I] in
/-- The divided-power monomials lie in `_𝒜 f`. -/
theorem π_dpowMono2_mem_Af (d : List (I × ℕ)) : PreF.π C.dot vQ C.c (dpowMono2 C d) ∈ C.Af := by
  rw [π_dpowMono2]
  refine Subring.list_prod_mem _ fun y hy => ?_
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hy
  exact PreF.dpowF_mem_Af q.1 q.2

variable {k C} in
/-- **`γ_{ℚ(q)}(_𝒜 f) ⊆ K₀(R)`**: more precisely, in the image of `K₀(R) → K₀(R)_{ℚ(q)}`. -/
theorem gammaF2_mem_range (hGK : C.GabberKac vQ C.c) {x : C.F} (hx : x ∈ C.Af) :
    gammaF2 k C hGK x ∈ (toK0Q2 k C).range := by
  have hle : C.Af ≤ (toK0Q2 k C).range.comap (gammaF2 k C hGK).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨i, a⟩, rfl⟩ | hy)
    · exact ⟨clsDiv2 k C [(i, a)], (gammaF2_dpowF k C hGK i a).symm⟩
    · have key : ∀ n : ℤ, (gammaF2 k C hGK).toRingHom
          (algebraMap (RatFunc ℚ) C.F ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ)) ∈
            (toK0Q2 k C).range := fun n => by
        refine ⟨(T (-n) : LaurentPolynomial ℤ) • (1 : (G2).K0R), ?_⟩
        rw [toK0Q2_smul, map_one, qToV_T, neg_neg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      rcases hy with rfl | rfl
      · simpa using key 1
      · simpa using key (-1)
  exact hle hx

/-- **The integral `γ`** (KL II §3), with values in the image of `K₀(R)` in `K₀(R)_{ℚ(q)}`,
under the Gabber–Kac hypothesis. -/
def gammaA2 (hGK : C.GabberKac vQ C.c) : C.Af →+* (toK0Q2 k C).range :=
  ((gammaF2 k C hGK).toRingHom.comp C.Af.subtype).codRestrict _
    fun x => gammaF2_mem_range hGK x.2

theorem coe_gammaA2 (hGK : C.GabberKac vQ C.c) (x : C.Af) :
    (gammaA2 k C hGK x : K0Q2 k C) = gammaF2 k C hGK x := rfl

theorem gammaA2_dpowMono (hGK : C.GabberKac vQ C.c) (d : List (I × ℕ)) :
    gammaA2 k C hGK ⟨PreF.π C.dot vQ C.c (dpowMono2 C d), π_dpowMono2_mem_Af C d⟩ =
      (toK0Q2 k C).rangeRestrict (clsDiv2 k C d) :=
  Subtype.ext (gammaF2_dpowMono k C hGK d)

/-- `K₀(R) ≅ toK0Q2(K₀(R))` when `toK0Q2` is injective. -/
def K0RrangeEquiv2 (hinj : Function.Injective (toK0Q2 k C)) :
    (G2).K0R ≃+* (toK0Q2 k C).range :=
  RingEquiv.ofBijective (toK0Q2 k C).rangeRestrict
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), (toK0Q2 k C).rangeRestrict_surjective⟩

/-- **`γ : _𝒜 f → K₀(R)`** (KL II §3, the map of Theorem 8), under the Gabber–Kac hypothesis
`hGK` and the hypothesis `hinj` that `K₀(R) → K₀(R)_{ℚ(q)}` is injective (e.g. `K₀(R)`
torsion-free over `ℤ[q, q⁻¹]`; not proved here). -/
def gammaInt2 (hGK : C.GabberKac vQ C.c) (hinj : Function.Injective (toK0Q2 k C)) :
    C.Af →+* (G2).K0R :=
  (K0RrangeEquiv2 k C hinj).symm.toRingHom.comp (gammaA2 k C hGK)

theorem toK0Q2_gammaInt2 (hGK : C.GabberKac vQ C.c) (hinj : Function.Injective (toK0Q2 k C))
    (x : C.Af) : toK0Q2 k C (gammaInt2 k C hGK hinj x) = gammaF2 k C hGK x := by
  have := (K0RrangeEquiv2 k C hinj).apply_symm_apply (gammaA2 k C hGK x)
  exact congrArg Subtype.val this

/-- **`γ(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`** in `K₀(R)`. -/
theorem gammaInt2_dpowMono (hGK : C.GabberKac vQ C.c) (hinj : Function.Injective (toK0Q2 k C))
    (d : List (I × ℕ)) :
    gammaInt2 k C hGK hinj ⟨PreF.π C.dot vQ C.c (dpowMono2 C d), π_dpowMono2_mem_Af C d⟩ =
      clsDiv2 k C d :=
  hinj (by rw [toK0Q2_gammaInt2]; exact gammaF2_dpowMono k C hGK d)

/-- `γ` is `ℤ[q, q⁻¹]`-linear (`q` acting on `_𝒜 f` as `v⁻¹`). -/
theorem gammaInt2_smul (hGK : C.GabberKac vQ C.c) (hinj : Function.Injective (toK0Q2 k C))
    (p : LaurentPolynomial ℤ) (x : C.Af) :
    gammaInt2 k C hGK hinj
        ⟨algebraMap (RatFunc ℚ) C.F (qToV p) * x,
          Subring.mul_mem _ (algebraMap_qToV_mem_Af2 C p) x.2⟩ =
      p • gammaInt2 k C hGK hinj x :=
  hinj (by
    rw [toK0Q2_gammaInt2, toK0Q2_smul, toK0Q2_gammaInt2, map_mul, AlgHom.commutes,
      Algebra.smul_def])

end GammaA

end Categorification.KLR.KL2Gamma
