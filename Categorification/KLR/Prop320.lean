/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop318
import Categorification.KLR.Cor319

/-!
# KL I, Proposition 3.20: unitriangularity and the integral surjectivity of `γ`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.2 (TeX lines 2275–2303): for finite `Γ` with vertices ordered
`i(0) < i(1) < …`, each simple `S_b` gets a sequence `Y_b = y_0 y_1 …` (`y_r = ε_{i(r)}(M_r)`,
`M_{r+1} = ẽ_{i(r)}^{y_r} M_r`), ordered lexicographically, and a divided-power projective
`P(Y_b)`, and

> **Proposition 3.20.** `HOM(P(Y_b), S_c) = 0` if `b < c` and `HOM(P(Y_b), S_b) = 𝕜`.

> This […] implies that the image `[P]` of any (graded) projective `R(ν)`-module in `K₀(R(ν))`
> can be written as a linear combination, with coefficients in `ℤ[q, q⁻¹]`, of images of divided
> powers projectives […]. Therefore, `γ : _𝒜 f → K₀(R(ν))` is surjective.

## The argument formalized here

Instead of the crystal operators `ẽ_i` and a cyclic order of the vertices, we order the letters by
any injection `rk : I → α` into a linear order and attach to a sequence `s` its **key**: the list
of its maximal runs `(letter, length)` read from the right (`runs`, `runKey`, `seqKey`), compared
lexicographically. For a simple module `M` (finite-dimensional, nilpotent dots) let `s_M` be the
key-maximal sequence of its support `{s | 1_s M ≠ 0}` (`IsKeyMax`). Then (`isKeyMax_aux`, by
induction on `|ν|` using Lemmas 3.5 and 3.8 as in the proof of Theorem 3.17):

* the last run of `s_M` is `(i, ε_i(M))` (`epsI_eq_tailLen_of_isKeyMax`), and `s_M = s_N i^ε` with
  `s_N` key-maximal for `N = HW(Δ_{i^ε} M)` (`isKeyMax_hw`) — this is the recursion defining `Y_b`,
  as `HW(Δ_{i^ε} M) ≅ ẽ_i^ε M`;
* `dim 1_{s_M} M = ∏ (run lengths of s_M)!` (from `Δ_{i^ε} M ≅ N ⊠ L(i^ε)`, `dim L(i^ε) = ε!`);
* `M` is determined up to isomorphism by `s_M` (Lemma 3.7, `nonempty_equiv_of_hwSpace_equiv`).

With `θ_b` the run decomposition of `s_b = s_{S_b}` and `[P_{s_b}] = θ_b! [P_{θ_b}]`
(`K0_projP_expandDiv`), `HOM(P_{θ_b}, S_c) ≠ 0` forces `s_b` into the support of `S_c`, hence
`key(s_b) ≤ key(s_c)`; and `gdim HOM(P_{θ_b}, S_b)` has nonnegative coefficients summing to
`dim 1_{s_b} S_b / θ_b! = 1` at `q = 1`, so it is a power of `q` (`exists_eq_T_of_evalOne_eq_one`).
With the duality of `[P_b]` and `[S_b]` (Corollary 3.19) the coordinates of the `[P_{θ_b}]` in
the basis `[P_c]` form a unitriangular matrix, so the `[P_θ]` span `K₀(R(ν))`
(`basis_mem_span_of_triangular`).

## Main results

* `runs`, `expandDiv_runs`, `runs_append_replicate`, `runKey`, `seqKey`, `seqKey_injective`.
* `KLRAlgebra.isKeyMax_aux` : the ungraded induction described above.
* `KLGamma.prop_3_20` : **KL I, Proposition 3.20** (with the order described above).
* `KLGamma.k0B_mem_span_projDiv` : **the divided-power classes `[P_θ]` span `K₀(R(ν))` over
  `ℤ[q, q⁻¹]`**, for any graph `Γ` (finite or not) and any field `𝕜`.
-/

noncomputable section

namespace Categorification.KLR

open KLRAlgebra

variable {I : Type*}

/-! ### Runs of a sequence -/

section Runs

variable [DecidableEq I]

/-- Prepend a letter to a run decomposition. -/
def runsCons (a : I) : List (I × ℕ) → List (I × ℕ)
  | [] => [(a, 1)]
  | (b, n) :: r => if a = b then (b, n + 1) :: r else (a, 1) :: (b, n) :: r

@[simp] theorem runsCons_nil (a : I) : runsCons a [] = [(a, 1)] := rfl

theorem runsCons_cons (a b : I) (n : ℕ) (r : List (I × ℕ)) :
    runsCons a ((b, n) :: r) = if a = b then (b, n + 1) :: r else (a, 1) :: (b, n) :: r := rfl

/-- **The maximal runs of a sequence**, from the left: `runs (a a b a) = [(a,2),(b,1),(a,1)]`.
It is the divided-power expression `a^{(2)} b a` of the sequence. -/
def runs : List I → List (I × ℕ)
  | [] => []
  | a :: l => runsCons a (runs l)

@[simp] theorem runs_nil : runs ([] : List I) = [] := rfl

@[simp] theorem runs_cons (a : I) (l : List I) : runs (a :: l) = runsCons a (runs l) := rfl

theorem expandDiv_runsCons (a : I) (r : List (I × ℕ)) :
    expandDiv (runsCons a r) = a :: expandDiv r := by
  rcases r with _ | ⟨⟨b, n⟩, r⟩
  · simp [expandDiv]
  · rw [runsCons_cons]
    split_ifs with h
    · subst h
      simp [expandDiv, List.replicate_succ]
    · simp [expandDiv]

/-- The runs of `l` expand back to `l`. -/
theorem expandDiv_runs (l : List I) : expandDiv (runs l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [runs_cons, expandDiv_runsCons, ih]

theorem runs_injective : Function.Injective (runs : List I → List (I × ℕ)) := fun l l' h => by
  rw [← expandDiv_runs l, ← expandDiv_runs l', h]

theorem runs_eq_nil_iff {l : List I} : runs l = [] ↔ l = [] := by
  constructor
  · intro h; rw [← expandDiv_runs l, h]; rfl
  · rintro rfl; rfl

theorem runsCons_append {a : I} {X : List (I × ℕ)} (hX : X ≠ []) (Y : List (I × ℕ)) :
    runsCons a (X ++ Y) = runsCons a X ++ Y := by
  rcases X with _ | ⟨⟨b, n⟩, r⟩
  · exact absurd rfl hX
  · simp only [List.cons_append, runsCons_cons]
    split_ifs <;> rfl

theorem runs_replicate (i : I) {n : ℕ} (hn : 1 ≤ n) : runs (List.replicate n i) = [(i, n)] := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · rfl
    · rw [List.replicate_succ, runs_cons, ih hn']
      simp [runsCons_cons]

/-- **Appending a run**: if `l` does not end with `i` and `n ≥ 1`, the runs of `l i^n` are those of
`l` followed by `(i, n)`. -/
theorem runs_append_replicate {i : I} {n : ℕ} (hn : 1 ≤ n) :
    ∀ {l : List I}, l.getLast? ≠ some i →
      runs (l ++ List.replicate n i) = runs l ++ [(i, n)]
  | [], _ => by rw [List.nil_append, runs_replicate i hn]; rfl
  | a :: l, hl => by
    have hl' : l.getLast? ≠ some i := by
      rcases l with _ | ⟨b, l⟩
      · simp
      · rwa [List.getLast?_cons_cons] at hl
    rw [List.cons_append, runs_cons, runs_append_replicate hn hl', runs_cons]
    by_cases hnil : runs l = []
    · rw [runs_eq_nil_iff.1 hnil] at hl ⊢
      have hai : a ≠ i := fun h => hl (by simp [h])
      simp [runsCons_cons, hai]
    · exact runsCons_append hnil _

end Runs

/-! ### The key of a sequence -/

section Keys

variable [DecidableEq I] {α : Type*} (rk : I → α)

/-- The runs of `l` read from the right, with letters encoded by `rk`, as a list ordered
lexicographically: first the last letter, then the length of the last run, then the letter of the
previous run, … -/
def runKey (l : List I) : List (α ×ₗ ℕ) := (runs l).reverse.map fun q => toLex (rk q.1, q.2)

theorem runKey_append_replicate {i : I} {n : ℕ} (hn : 1 ≤ n) {l : List I}
    (hl : l.getLast? ≠ some i) :
    runKey rk (l ++ List.replicate n i) = toLex (rk i, n) :: runKey rk l := by
  rw [runKey, runs_append_replicate hn hl, List.reverse_append]
  rfl

theorem runKey_injective (hrk : Function.Injective rk) : Function.Injective (runKey (I := I) rk) := by
  intro l l' h
  have hf : Function.Injective fun q : I × ℕ => toLex (rk q.1, q.2) := fun q q' hq => by
    have := congrArg ofLex hq
    simp only [ofLex_toLex, Prod.mk.injEq] at this
    exact Prod.ext (hrk this.1) this.2
  exact runs_injective (List.reverse_injective ((List.map_injective_iff.2 hf) h))

/-- A list ending with exactly `y ≥ 1` letters `i` has key `(i, y) :: _`. -/
theorem runKey_eq_cons_of_tail (l : List I) (i : I) (y : ℕ) (hy : 1 ≤ y) (hyl : y ≤ l.length)
    (htail : ∀ (a : ℕ) (h : a < l.length), l.length ≤ a + y → l[a] = i)
    (hmax : ∀ h : y < l.length, l[l.length - y - 1]'(by omega) ≠ i) :
    ∃ rest, runKey rk l = toLex (rk i, y) :: rest := by
  have hdrop : l.drop (l.length - y) = List.replicate y i := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp; omega, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.1 hb
    rw [List.getElem_drop]
    exact htail _ _ (by simp at ha; omega)
  have htake : (l.take (l.length - y)).getLast? ≠ some i := by
    rcases Nat.lt_or_ge y l.length with h | h
    · rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left (by omega),
        List.getElem?_take, if_pos (by omega)]
      rw [show l.length - y - 1 = l.length - y - 1 from rfl, List.getElem?_eq_getElem (by omega)]
      exact fun h' => hmax h (Option.some_injective _ h')
    · rw [show l.length - y = 0 by omega, List.take_zero]
      simp
  refine ⟨runKey rk (l.take (l.length - y)), ?_⟩
  conv_lhs => rw [← List.take_append_drop (l.length - y) l, hdrop]
  exact runKey_append_replicate rk hy htake

/-- The key of a sequence `s ∈ Seq(ν)`. -/
def seqKey {ν : Multiset I} (s : Seq ν) : List (α ×ₗ ℕ) := runKey rk (List.ofFn s.1)

theorem seqKey_injective (hrk : Function.Injective rk) {ν : Multiset I} :
    Function.Injective (seqKey (ν := ν) rk) := fun _ _ h =>
  Subtype.ext (List.ofFn_injective (runKey_injective rk hrk h))

/-- If `s` ends with exactly `y = tail_i(s) ≥ 1` letters `i`, its key is `(i, y) :: _`. -/
theorem seqKey_eq_cons {ν : Multiset I} (s : Seq ν) (i : I) (hy : 1 ≤ Seq.tailLen i s) :
    ∃ rest, seqKey rk s = toLex (rk i, Seq.tailLen i s) :: rest := by
  refine runKey_eq_cons_of_tail rk _ i _ hy (by simpa using Seq.tailLen_le_card s) ?_ ?_
  · intro a ha hle
    rw [List.getElem_ofFn]
    exact Seq.apply_eq_of_le_tailLen (by simp at ha hle ⊢; omega)
  · intro h
    rw [List.getElem_ofFn]
    intro heq
    have h1 : Seq.HasTail i s (Seq.tailLen i s + 1) := by
      refine ⟨by simp at h; omega, fun a ha => ?_⟩
      by_cases hlt : Multiset.card ν ≤ a.val + Seq.tailLen i s
      · exact Seq.apply_eq_of_le_tailLen hlt
      · have : a = ⟨(List.ofFn s.1).length - Seq.tailLen i s - 1, by simp at h ⊢; omega⟩ :=
          Fin.ext (by simp; omega)
        rw [this]
        exact heq
    have := Seq.le_tailLen h1
    omega

omit [DecidableEq I] in
theorem ofFn_append {μ ν' : Multiset I} (j : Seq μ) (c : Seq ν') :
    List.ofFn (j.append c).1 = List.ofFn j.1 ++ List.ofFn c.1 := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_ofFn]
    by_cases hn : n < Multiset.card μ
    · rw [Seq.append_apply_lt _ _ _ hn, List.getElem_append_left (by simpa using hn),
        List.getElem_ofFn]
    · rw [Seq.append_apply_ge _ _ _ (by simp; omega), List.getElem_append_right (by simp; omega),
        List.getElem_ofFn]
      simp

omit [DecidableEq I] in
theorem ofFn_constSeq {ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) :
    List.ofFn (Seq.constSeq hν').1 = List.replicate (Multiset.card ν') i := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hb
  rfl

theorem getLast?_ofFn_ne {μ : Multiset I} {i : I} (j : Seq μ) (h : Seq.tailLen i j = 0) :
    (List.ofFn j.1).getLast? ≠ some i := by
  rcases Nat.eq_zero_or_pos (Multiset.card μ) with h0 | hpos
  · have : List.ofFn j.1 = [] := List.eq_nil_of_length_eq_zero (by simpa using h0)
    rw [this]; simp
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega), List.getElem_ofFn]
    intro heq
    have h1 : Seq.HasTail i j 1 := ⟨by omega, fun a ha => by
      rw [show a = ⟨(List.ofFn j.1).length - 1, by simp; omega⟩ from Fin.ext (by simp; omega)]
      exact Option.some_injective _ heq⟩
    have := Seq.le_tailLen h1
    omega

/-- **The key of `j i^n`** for `j` not ending with `i`: `(i, n) :: key(j)`. -/
theorem seqKey_append_const {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
    (hn : 1 ≤ Multiset.card ν') (j : Seq μ) (hj : Seq.tailLen i j = 0) :
    seqKey rk (j.append (Seq.constSeq hν')) = toLex (rk i, Multiset.card ν') :: seqKey rk j := by
  rw [seqKey, ofFn_append, ofFn_constSeq, runKey_append_replicate rk hn (getLast?_ofFn_ne j hj)]
  rfl

end Keys

/-! ### Laurent polynomials with nonnegative coefficients at `q = 1` -/

section EvalOne

open LaurentPolynomial

theorem evalOne_invert (p : LaurentPolynomial ℤ) : evalOne (invert p) = evalOne p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add]
  | C_mul_T n a => rw [map_mul, invert_C, invert_T, map_mul, map_mul, evalOne_T, evalOne_T]

theorem evalOne_qint (n : ℕ) : evalOne (QuantumGroup.qint qUnitLP n) = n := by
  rw [qint_qUnitLP, map_sum]
  simp [evalOne_T]

theorem evalOne_qfact (n : ℕ) : evalOne (QuantumGroup.qfact qUnitLP n) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [QuantumGroup.qfact_succ, map_mul, ih, evalOne_qint, Nat.factorial_succ]
    push_cast; ring

theorem evalOne_divQFactLP (d : List (I × ℕ)) :
    evalOne (divQFactLP d) = ((d.map fun q => q.2.factorial).prod : ℕ) := by
  rw [divQFactLP, map_list_prod, List.map_map]
  push_cast [List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp [evalOne_qfact]

/-- A Laurent polynomial with nonnegative coefficients vanishing at `q = 1` is zero. -/
theorem eq_zero_of_evalOne_eq_zero {p : LaurentPolynomial ℤ} (hp : ∀ n, 0 ≤ p n)
    (h : evalOne p = 0) : p = 0 := by
  rw [evalOne_eq_sum, Finsupp.sum] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg fun n _ => hp n).1 h
  ext n
  by_cases hn : n ∈ p.support
  · exact this n hn
  · exact Finsupp.not_mem_support_iff.1 hn

/-- A Laurent polynomial with nonnegative coefficients taking the value `1` at `q = 1` is a
monomial `q^n`. -/
theorem exists_eq_T_of_evalOne_eq_one {p : LaurentPolynomial ℤ} (hp : ∀ n, 0 ≤ p n)
    (h : evalOne p = 1) : ∃ n, p = T n := by
  classical
  rw [evalOne_eq_sum, Finsupp.sum] at h
  obtain ⟨n, hn⟩ : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  rw [← Finset.add_sum_erase _ _ hn] at h
  have hrest := Finset.sum_nonneg (s := p.support.erase n) fun m _ => hp m
  have hpn : 1 ≤ p n := by
    have := Finsupp.mem_support_iff.1 hn
    have := hp n
    omega
  have hpn1 : p n = 1 := by omega
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (s := p.support.erase n)
    fun m _ => hp m).1 (by omega)
  refine ⟨n, ?_⟩
  ext m
  rw [T, Finsupp.single_apply]
  by_cases hm : n = m
  · subst hm; rw [if_pos rfl, hpn1]
  · rw [if_neg hm]
    by_cases hms : m ∈ p.support
    · exact hzero m (Finset.mem_erase.2 ⟨Ne.symm hm, hms⟩)
    · exact Finsupp.not_mem_support_iff.1 hms

end EvalOne

/-! ### Unitriangular families span -/

/-- **Unitriangularity**: if the coordinates `m_{bc}` of vectors `x_b` in a basis `e` satisfy
`m_{bc} ≠ 0 ⇒ key(b) ≤ key(c)` for an injective `key` into a linear order and the diagonal
entries are units, then every basis vector lies in the span of the `x_b`. -/
theorem basis_mem_span_of_triangular {R M B β : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype B] [DecidableEq B] [LinearOrder β] (e : Basis B R M) (x : B → M)
    (key : B → β) (hkey : Function.Injective key)
    (htri : ∀ b c, e.repr (x b) c ≠ 0 → key b ≤ key c) (hdiag : ∀ b, IsUnit (e.repr (x b) b))
    (b : B) : e b ∈ Submodule.span R (Set.range x) := by
  classical
  set S : B → Finset B := fun b => Finset.univ.filter fun c => key b < key c
  suffices h : ∀ n, ∀ b, (S b).card = n → e b ∈ Submodule.span R (Set.range x) from
    h _ b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b hb
  have hx : x b = e.repr (x b) b • e b + ∑ c ∈ Finset.univ.erase b, e.repr (x b) c • e c := by
    conv_lhs => rw [← e.sum_repr (x b)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  have hrest : ∑ c ∈ Finset.univ.erase b, e.repr (x b) c • e c ∈
      Submodule.span R (Set.range x) := by
    refine Submodule.sum_mem _ fun c hc => ?_
    by_cases hm : e.repr (x b) c = 0
    · rw [hm, zero_smul]; exact Submodule.zero_mem _
    have hlt : key b < key c :=
      lt_of_le_of_ne (htri b c hm) fun h => (Finset.mem_erase.1 hc).1 (hkey h).symm
    refine Submodule.smul_mem _ _ (ih _ ?_ c rfl)
    rw [← hb]
    have hsub : S c ⊆ S b := fun c' hc' => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
      exact hlt.trans hc'
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨c, ?_, ?_⟩)
    · simp [S, hlt]
    · simp [S]
  have hmem : e.repr (x b) b • e b ∈ Submodule.span R (Set.range x) := by
    rw [eq_sub_of_add_eq hx.symm]
    exact Submodule.sub_mem _
      (Submodule.subset_span (Set.mem_range_self b) : x b ∈ Submodule.span R (Set.range x)) hrest
  obtain ⟨u, hu⟩ := hdiag b
  have := Submodule.smul_mem _ (↑u⁻¹ : R) hmem
  rwa [smul_smul, ← hu, Units.inv_mul, one_smul] at this

/-! ### The key-maximal sequence of a simple module -/

namespace KLRAlgebra

section KeyMax

variable [DecidableEq I] {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {α : Type*} [LinearOrder α] (rk : I → α)

variable (Q) in
/-- `s` is the key-maximal sequence of the support `{s | 1_s M ≠ 0}` of `M`. -/
def IsKeyMax (ν : Multiset I) (M : Type*) [AddCommGroup M] [Module K M]
    [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M] (s : Seq ν) : Prop :=
  s ∈ seqSupp Q ν M ∧ ∀ t ∈ seqSupp Q ν M, seqKey rk t ≤ seqKey rk s

/-- `∏ (run lengths)!` of a sequence. -/
def runsFact {ν : Multiset I} (s : Seq ν) : ℕ :=
  ((runs (List.ofFn s.1)).map fun q => q.2.factorial).prod

section Basic

variable {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M]

include rk in
theorem exists_isKeyMax [Nontrivial M] : ∃ s, IsKeyMax Q rk ν M s := by
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (seqSupp Q ν M) (seqKey rk)
    (seqSupp_nonempty (Q := Q) (ν := ν) (M := M))
  exact ⟨s, hs, hmax⟩

theorem mem_seqSupp_iff_dimCh [FiniteDimensional K M] {s : Seq ν} :
    s ∈ seqSupp Q ν M ↔ dimCh Q ν M s ≠ 0 := by
  rw [mem_seqSupp, dimCh, ne_eq, ne_eq, Submodule.finrank_eq_zero]

/-- **The last run of the key-maximal sequence is `(i, ε_i(M))`**: if `s` is key-maximal and ends
with `y = tail_i(s) ≥ 1` letters `i`, then `ε_i(M) = y`. -/
theorem epsI_eq_tailLen_of_isKeyMax [Nontrivial M] {s : Seq ν} (hs : IsKeyMax Q rk ν M s)
    {i : I} (hy : 1 ≤ Seq.tailLen i s) : epsI Q ν i M = Seq.tailLen i s := by
  have hle := tailLen_le_epsI (Q := Q) (ν := ν) (M := M) (i := i) (mem_seqSupp.1 hs.1)
  refine le_antisymm ?_ hle
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, ht, hte⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := ν) (i := i) (M := M)
  obtain ⟨r, hr⟩ := seqKey_eq_cons rk s i hy
  obtain ⟨r', hr'⟩ := seqKey_eq_cons rk t i (by omega)
  have h1 := hs.2 t (mem_seqSupp.2 ht)
  rw [hr, hr', hte] at h1
  have h2 : (toLex (rk i, Seq.tailLen i s) :: r : List (α ×ₗ ℕ)) <
      toLex (rk i, epsI Q ν i M) :: r' :=
    List.Lex.rel (Prod.Lex.toLex_strictMono (Prod.mk_lt_mk_of_le_of_lt le_rfl hlt))
  exact absurd h1 (not_le.2 h2)

end Basic

universe u

section Step

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {L : Type u} [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q (μ + ν')) L]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L] [FiniteDimensional K L]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) L]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) L)
  (hε : epsI Q (μ + ν') i L = Multiset.card ν')

include hPQ hP hnil hε in
/-- The support of `HW(Δ_{i^ε} L)`: `j` lies in it iff `j i^ε` lies in the support of `L`. -/
theorem mem_seqSupp_hw_iff (j : Seq μ) :
    j ∈ seqSupp Q μ (HWSpace Q μ ν' (ResSub Q μ ν' L)) ↔
      j.append (Seq.constSeq hν') ∈ seqSupp Q (μ + ν') L := by
  haveI : FiniteDimensional K (HWSpace Q μ ν' (ResSub Q μ ν' L)) :=
    FiniteDimensional.finiteDimensional_submodule _
  rw [mem_seqSupp_iff_dimCh, mem_seqSupp_iff_dimCh, dimCh_append_const hν' hPQ hP hnil hε j]
  have hd : Module.finrank K (KLRRep hν' Q) ≠ 0 := by
    show Module.finrank K (Coinv K (Multiset.card ν')) ≠ 0
    rw [finrank_coinv]
    exact Nat.factorial_ne_zero _
  constructor
  · intro h; exact mul_ne_zero h hd
  · intro h h0; rw [h0, zero_mul] at h; exact h rfl

include hPQ hP hnil hε in
/-- **The key-maximal sequence of `L` is `s' i^ε` with `s'` key-maximal for
`HW(Δ_{i^ε} L)`.** -/
theorem isKeyMax_hw (hn : 1 ≤ Multiset.card ν') {s' : Seq μ}
    (hs : IsKeyMax Q rk (μ + ν') L (s'.append (Seq.constSeq hν'))) :
    IsKeyMax Q rk μ (HWSpace Q μ ν' (ResSub Q μ ν' L)) s' := by
  have h3 := (lemma_3_8 hν' hPQ hP hnil hε).2.2
  have htail : ∀ t ∈ seqSupp Q μ (HWSpace Q μ ν' (ResSub Q μ ν' L)), Seq.tailLen i t = 0 :=
    fun t ht => Nat.eq_zero_of_le_zero (h3 ▸ tailLen_le_epsI (mem_seqSupp.1 ht))
  have hs' := (mem_seqSupp_hw_iff hPQ hP hν' hnil hε s').2 hs.1
  refine ⟨hs', fun t ht => ?_⟩
  have h := hs.2 _ ((mem_seqSupp_hw_iff hPQ hP hν' hnil hε t).1 ht)
  rw [seqKey_append_const rk hν' hn t (htail t ht),
    seqKey_append_const rk hν' hn s' (htail s' hs')] at h
  rcases le_iff_lt_or_eq.1 h with h | h
  · exact le_of_lt ((List.lex_cons_iff (r := (· < ·))).1 h)
  · exact le_of_eq (List.cons.inj h).2

end Step

include hPQ hP in
/-- **The induction behind Proposition 3.20** (ungraded): for a simple finite-dimensional
`R(ν)`-module `L` with nilpotent dots and key-maximal sequence `s` of its support,
(1) `dim 1_s L = ∏ (run lengths of s)!`, and (2) `L` is determined up to isomorphism by `s`. -/
theorem isKeyMax_aux (n : ℕ) : ∀ (ν : Multiset I), Multiset.card ν = n →
    ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ν) L]
      [IsScalarTower K (KLRAlgebra K Q ν) L] [FiniteDimensional K L]
      [IsSimpleModule (KLRAlgebra K Q ν) L],
      (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L) → ∀ s : Seq ν, IsKeyMax Q rk ν L s →
      dimCh Q ν L s = runsFact s ∧
      ∀ (L' : Type u) [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
        [IsScalarTower K (KLRAlgebra K Q ν) L'] [FiniteDimensional K L']
        [IsSimpleModule (KLRAlgebra K Q ν) L'],
        (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L') → IsKeyMax Q rk ν L' s →
        Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν L _ _ _ _ _ _ hnil s hs
  haveI : Nontrivial L := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨?_, fun L' _ _ _ _ _ _ _ _ => nonempty_equiv_of_card_eq_zero hν⟩
    haveI := subsingleton_seq_of_card_eq_zero (ν := ν) hν
    have he : (e s : KLRAlgebra K Q ν) = 1 := by rw [← sum_e, Fintype.sum_subsingleton _ s]
    have hnil' : List.ofFn s.1 = [] := List.eq_nil_of_length_eq_zero (by simp [hν])
    rw [dimCh, he, fixSub_one, finrank_top, finrank_eq_one_of_card_eq_zero (Q := Q) hν, runsFact,
      hnil', runs_nil]
    rfl
  -- the last letter `i` of `s` and its tail
  set i : I := s.1 ⟨Multiset.card ν - 1, by omega⟩
  have hy : 1 ≤ Seq.tailLen i s := by
    have : Seq.HasTail i s 1 := ⟨by omega, fun a ha => by
      rw [show a = ⟨Multiset.card ν - 1, by omega⟩ from
        Fin.ext (show a.val = Multiset.card ν - 1 by have := a.2; omega)]⟩
    exact Seq.le_tailLen this
  have hεs := epsI_eq_tailLen_of_isKeyMax rk hs hy
  set ε := Seq.tailLen i s with hεdef
  have hrep : Multiset.replicate ε i ≤ ν :=
    replicate_le_of_hasTail (Seq.hasTail_tailLen (i := i) s)
  obtain ⟨μ, hμ⟩ := Multiset.le_iff_exists_add.1 hrep
  rw [add_comm] at hμ
  have htail := Seq.hasTail_tailLen (i := i) s
  rw [← hεdef] at htail
  clear_value ε i
  obtain ⟨ν', hν'def⟩ : ∃ ν', Multiset.replicate ε i = ν' := ⟨_, rfl⟩
  rw [hν'def] at hμ
  subst hμ
  have hν' : ∀ a ∈ ν', a = i := fun a ha => Multiset.eq_of_mem_replicate (hν'def ▸ ha)
  have hcard : Multiset.card ν' = ε := by rw [← hν'def, Multiset.card_replicate]
  have hε : epsI Q (μ + ν') i L = Multiset.card ν' := by rw [hcard, hεs]
  rw [← hcard] at htail
  obtain ⟨s', rfl⟩ := Seq.exists_eq_append_const_of_hasTail hν' htail
  have hn1 : 1 ≤ Multiset.card ν' := by omega
  -- `N = HW(Δ_{i^ε} L)`
  set N := HWSpace Q μ ν' (ResSub Q μ ν' L)
  haveI : IsSimpleModule (KLRAlgebra K Q μ) N := (lemma_3_8 hν' hPQ hP hnil hε).2.1
  haveI : FiniteDimensional K N := FiniteDimensional.finiteDimensional_submodule _
  have hNnil : ∀ a : Fin (Multiset.card μ), SmulNilpotent (x a : KLRAlgebra K Q μ) N :=
    fun a => smulNilpotent_hwSpace a (hnil _)
  have hμcard : Multiset.card μ < n := by
    rw [← hν, Multiset.card_add]; omega
  have hsN := isKeyMax_hw hPQ hP rk hν' hnil hε hn1 hs
  obtain ⟨hdimN, hisoN⟩ := ih (Multiset.card μ) hμcard μ rfl N hNnil s' hsN
  have htail0 : Seq.tailLen i s' = 0 := by
    have h3 := (lemma_3_8 hν' hPQ hP hnil hε).2.2
    exact Nat.eq_zero_of_le_zero (h3 ▸ tailLen_le_epsI (mem_seqSupp.1 hsN.1))
  refine ⟨?_, fun L' _ _ _ _ _ _ hnil' hs' => ?_⟩
  · -- the dimension
    rw [dimCh_append_const hν' hPQ hP hnil hε s', hdimN]
    show _ * Module.finrank K (Coinv K (Multiset.card ν')) = _
    rw [finrank_coinv, runsFact, runsFact, ofFn_append, ofFn_constSeq,
      runs_append_replicate hn1 (getLast?_ofFn_ne s' htail0), List.map_append, List.prod_append]
    simp
  · -- the isomorphism
    haveI : Nontrivial L' := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) L'
    have hy' : Seq.tailLen i (s'.append (Seq.constSeq hν')) = Multiset.card ν' := by
      rw [hcard, hεdef]
    have hε' : epsI Q (μ + ν') i L' = Multiset.card ν' := by
      rw [epsI_eq_tailLen_of_isKeyMax rk hs' (by omega), hy']
    set N' := HWSpace Q μ ν' (ResSub Q μ ν' L')
    haveI : IsSimpleModule (KLRAlgebra K Q μ) N' := (lemma_3_8 hν' hPQ hP hnil' hε').2.1
    haveI : FiniteDimensional K N' := FiniteDimensional.finiteDimensional_submodule _
    have hNnil' : ∀ a : Fin (Multiset.card μ), SmulNilpotent (x a : KLRAlgebra K Q μ) N' :=
      fun a => smulNilpotent_hwSpace a (hnil' _)
    have hsN' := isKeyMax_hw hPQ hP rk hν' hnil' hε' hn1 hs'
    obtain ⟨φ⟩ := hisoN N' hNnil' hsN'
    exact nonempty_equiv_of_hwSpace_equiv hν' hPQ hP hnil hnil' hε hε' φ.symm

end KeyMax

end KLRAlgebra

/-! ### Proposition 3.20 for the rings of KL I -/

namespace KLGamma

open Graded LaurentPolynomial QuantumGroup

variable [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-- **KL I, Corollary 3.19** for the tops of KL I: `dim END(S_b)_0 = 1`. -/
theorem endDim_eq_one {ν : Multiset I} (b : GProj.IndecClass ((Gkl).grade ν)) :
    endDim k Γ b = 1 :=
  (Gkl).finrank_endZero_top (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν b

/-- `(z, [S_c]) = \overline{z_c}` where `z = ∑_c z_c [P_c]` (dual bases, Corollary 3.19). -/
theorem pairing_g0B {ν : Multiset I} (z : K0 ((Gkl).grade ν))
    (c : GProj.IndecClass ((Gkl).grade ν)) :
    pairing z (g0B k Γ ν c) = toLaurentSeries (invert ((k0B k Γ ν).repr z c)) := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  conv_lhs => rw [← (k0B k Γ ν).sum_repr z]
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  have hterm : ∀ b', pairing ((k0B k Γ ν).repr z b' • k0B k Γ ν b') (g0B k Γ ν c) =
      toLaurentSeries (invert ((k0B k Γ ν).repr z b') *
        LaurentPolynomial.C (if b' = c then 1 else 0)) := fun b' => by
    refine pairing_smul_left_of_eq ?_ _
    rw [GradingDatum.pairing_k0Basis_g0Basis_eq, toLaurentSeries_C]
    split_ifs <;> simp [HahnSeries.single_zero_one]
  simp only [hterm]
  rw [Finset.sum_eq_single c (fun b' _ hb' => by rw [if_neg hb', map_zero, mul_zero, map_zero])
    (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, map_one, mul_one]

/-- `ch(S_c)_j = \overline{a_{j c}}` where `[P_j] = ∑_c a_{j c} [P_c]`. -/
theorem chG0_g0B_eq {ν : Multiset I} (j : Seq ν) (c : GProj.IndecClass ((Gkl).grade ν)) :
    chG0 (Gkl) j (g0B k Γ ν c) = invert ((k0B k Γ ν).repr (K0.of ((Gkl).projP j)) c) := by
  rw [chG0_g0B, endDim_eq_one, Nat.cast_one, map_one, mul_one]

theorem chG0_g0B_eq_gdimPoly {ν : Multiset I} (j : Seq ν)
    (c : GProj.IndecClass ((Gkl).grade ν)) :
    chG0 (Gkl) j (g0B k Γ ν c) = gdimPoly (idem c.top.grading (e j : KLRAlgebra k (klQ Γ) ν)) := by
  rw [g0B, GradingDatum.g0Basis, G0.topBasis_apply, chG0_of]
  rfl

omit [DecidableEq I] in
theorem seq_ofList_eq {ν : Multiset I} (s : Seq ν) {l : List I} (hl : l = List.ofFn s.1)
    (h : (l : Multiset I) = ν) : Seq.ofList l h = s := by
  subst hl
  exact seq_ofList_ofFn s

omit [DecidableEq I] in
theorem divQFactLP_ne_zero (d : List (I × ℕ)) : divQFactLP d ≠ 0 := fun h =>
  qToV_divQFactLP_ne_zero d (by rw [h, map_zero])

theorem toLaurentSeries_T (n : ℤ) :
    toLaurentSeries (T n : LaurentPolynomial ℤ) = HahnSeries.single n 1 := by
  rw [← mul_one (T n : LaurentPolynomial ℤ), toLaurentSeries_T_mul, ← map_one LaurentPolynomial.C,
    toLaurentSeries_C, HahnSeries.single_zero_one, mul_one]

/-- **KL I, Proposition 3.20**: for every weight `ν` there are divided-power expressions `θ_b`
(`b` running over the simple `R(ν)`-modules `S_b` up to shift) and an injective `key` into a linear
order such that

* `HOM(P_{θ_b}, S_c) = 0` unless `key(b) ≤ key(c)`, and
* `HOM(P_{θ_b}, S_b)` is one-dimensional (`gdim = q^n`),

where `([P], [M]) = gdim HOM(P, M)` is the pairing `K₀ × G₀ → ℤ((q))` (`pairing_of_of`).

The paper's order is the lexicographic order of the sequences `Y_b = y_0 y_1 …` built from a fixed
order `i(0) < i(1) < …` of the vertices of a finite `Γ` and the crystal operators `ẽ_i`, and it
states the vanishing for `b < c` in its order. Here `θ_b` is the run decomposition of the sequence
`s_b` of the support `{s | 1_s S_b ≠ 0}` whose runs, read from the right, are lexicographically
largest (`IsKeyMax`; letters ordered by an arbitrary injection into `Cardinal`), and `key(b)` is
this run list. The last run of `s_b` is `(i, ε_i(S_b))` and the remaining runs are those of the
key-maximal sequence of `HW(Δ_{i^ε} S_b) = ẽ_i^ε S_b` (Lemma 3.8), which is the recursion
defining `Y_b`. No finiteness of `Γ` is needed. -/
theorem prop_3_20 (ν : Multiset I) :
    ∃ (θ : GProj.IndecClass ((Gkl).grade ν) → List (I × ℕ))
      (hθ : ∀ b, (expandDiv (θ b) : Multiset I) = ν)
      (key : GProj.IndecClass ((Gkl).grade ν) → List (Cardinal.{u_1} ×ₗ ℕ)),
      Function.Injective key ∧
      (∀ b c, pairing (K0.of (projDiv k Γ (θ b) (hθ b))) (g0B k Γ ν c) ≠ 0 → key b ≤ key c) ∧
      ∀ b, ∃ n : ℤ, pairing (K0.of (projDiv k Γ (θ b) (hθ b))) (g0B k Γ ν b) =
        HahnSeries.single n 1 := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  let rk : I → Cardinal := embeddingToCardinal
  have hrk : Function.Injective rk := embeddingToCardinal.injective
  have hyp := fun c : GProj.IndecClass ((Gkl).grade ν) =>
    crystal_hypotheses_of_isGradedSimple (Gkl) KL1.klGradingDatum_degX_pos c.top.grading
      (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec) (fun a b _ => KL1.klP_ne_zero _ a b)
      (GProj.IndecClass.isGradedSimple_top c)
  have hex : ∀ c : GProj.IndecClass ((Gkl).grade ν), ∃ s, IsKeyMax (K := k) (klQ Γ) rk ν c.top s :=
    fun c => by
      haveI := (hyp c).2.1
      haveI := IsSimpleModule.nontrivial (KLRAlgebra k (klQ Γ) ν) c.top
      exact exists_isKeyMax rk
  choose s hs using hex
  have hθ : ∀ c, (expandDiv (runs (List.ofFn (s c).1)) : Multiset I) = ν := fun c => by
    rw [expandDiv_runs]
    exact (Fin.univ_val_map _).symm.trans (s c).2
  set x : GProj.IndecClass ((Gkl).grade ν) → K0 ((Gkl).grade ν) :=
    fun c => K0.of (projDiv k Γ (runs (List.ofFn (s c).1)) (hθ c)) with hxdef
  have hPx : ∀ c, K0.of ((Gkl).projP (s c)) = divQFactLP (runs (List.ofFn (s c).1)) • x c := by
    intro c
    rw [← K0_projP_expandDiv (k := k) (Γ := Γ) (runs (List.ofFn (s c).1)) (hθ c),
      seq_ofList_eq (s c) (expandDiv_runs _)]
    rfl
  have hch : ∀ b c, chG0 (Gkl) (s b) (g0B k Γ ν c) =
      invert (divQFactLP (runs (List.ofFn (s b).1)) * (k0B k Γ ν).repr (x b) c) := by
    intro b c
    rw [chG0_g0B_eq, hPx, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hnonneg : ∀ (j : Seq ν) (c : GProj.IndecClass ((Gkl).grade ν)) (n : ℤ),
      0 ≤ chG0 (Gkl) j (g0B k Γ ν c) n := by
    intro j c n
    haveI := (hyp c).1
    letI := idemDecomposition c.top.grading ((Gkl).e_mem_grade j)
    rw [chG0_g0B_eq_gdimPoly, gdimPoly_apply]
    exact Nat.cast_nonneg _
  have hevch : ∀ (j : Seq ν) (c : GProj.IndecClass ((Gkl).grade ν)),
      evalOne (chG0 (Gkl) j (g0B k Γ ν c)) = dimCh (K := k) (klQ Γ) ν c.top j := by
    intro j c
    haveI := (hyp c).1
    rw [chG0_g0B_eq_gdimPoly]
    exact evalOne_gdimPoly_idem (Gkl) c.top.grading j
  -- the key of `b`
  let key : GProj.IndecClass ((Gkl).grade ν) → List (Cardinal ×ₗ ℕ) := fun c => seqKey rk (s c)
  have htri : ∀ b c, (k0B k Γ ν).repr (x b) c ≠ 0 → key b ≤ key c := by
    intro b c hm
    haveI := (hyp c).1
    refine (hs c).2 (s b) (mem_seqSupp_iff_dimCh.2 fun h0 => hm ?_)
    have hzero : chG0 (Gkl) (s b) (g0B k Γ ν c) = 0 :=
      eq_zero_of_evalOne_eq_zero (hnonneg _ c) (by rw [hevch, h0]; rfl)
    rw [hch] at hzero
    have := invert.injective (hzero.trans (map_zero _).symm)
    exact (mul_eq_zero.1 this).resolve_left (divQFactLP_ne_zero _)
  have hdiag : ∀ b, ∃ n, (k0B k Γ ν).repr (x b) b = T n := by
    intro b
    haveI := (hyp b).1
    haveI := (hyp b).2.1
    set m := (k0B k Γ ν).repr (x b) b
    -- `m` has nonnegative coefficients: `(x_b, [S_b]) = \bar m = gdim HOM(P_{θ_b}, S_b)`
    have hm0 : ∀ n, 0 ≤ m n := by
      intro n
      have h1 := pairing_g0B k Γ (x b) b
      rw [g0B, GradingDatum.g0Basis, G0.topBasis_apply, hxdef, pairing_of_of] at h1
      have h2 := congrArg (fun f : LaurentSeries ℤ => f.coeff (-n)) h1
      simp only [coeff_toLaurentSeries, invert_apply, neg_neg] at h2
      rw [← h2, coeff_gdim]
      exact Nat.cast_nonneg _
    -- `m(1) = 1`: `dim 1_{s_b} S_b = θ_b!`
    have hev := hevch (s b) b
    rw [(isKeyMax_aux (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
      (fun a b _ => KL1.klP_ne_zero _ a b) rk _ ν rfl b.top (hyp b).2.2 (s b) (hs b)).1, hch,
      evalOne_invert, map_mul, evalOne_divQFactLP] at hev
    have hpos : (0 : ℤ) < (runsFact (s b) : ℕ) := by
      rw [Nat.cast_pos, runsFact]
      exact List.prod_pos fun a ha => by
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 ha
        exact Nat.factorial_pos _
    have hev1 : evalOne m = 1 := by
      have : ((runsFact (s b) : ℕ) : ℤ) * evalOne m = ((runsFact (s b) : ℕ) : ℤ) * 1 := by
        rw [mul_one]; exact hev
      exact mul_left_cancel₀ hpos.ne' this
    exact exists_eq_T_of_evalOne_eq_one hm0 hev1
  have hkey : Function.Injective key := by
    intro b c h
    have hsc : s b = s c := seqKey_injective rk hrk h
    haveI := (hyp b).1
    haveI := (hyp b).2.1
    haveI := (hyp c).1
    haveI := (hyp c).2.1
    have hsc' : IsKeyMax (K := k) (klQ Γ) rk ν c.top (s b) := hsc ▸ hs c
    obtain ⟨φ⟩ := (isKeyMax_aux (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
      (fun a b _ => KL1.klP_ne_zero _ a b) rk _ ν rfl b.top (hyp b).2.2 (s b) (hs b)).2
      c.top (hyp c).2.2 hsc'
    haveI := IsSimpleModule.nontrivial (KLRAlgebra k (klQ Γ) ν) b.top
    have hφ : φ.toLinearMap ≠ 0 := by
      intro h0
      obtain ⟨v, hv⟩ := exists_ne (0 : b.top)
      exact hv (φ.injective (by simpa using LinearMap.congr_fun h0 v))
    obtain ⟨a, ⟨f⟩⟩ := (GProj.IndecClass.isGradedSimple_top b).exists_gradedEquiv_shift_of_ne_zero
      (GProj.IndecClass.isGradedSimple_top c) hφ
    have f' : Graded.shift b.top.grading 0 ≃ᵍ[KLRAlgebra k (klQ Γ) ν]
        Graded.shift c.top.grading a :=
      (GradedEquiv.ofEq (A := KLRAlgebra k (klQ Γ) ν) (shift_zero b.top.grading)).trans f
    exact (GProj.IndecClass.eq_of_gradedEquiv_top_shift f').1
  refine ⟨_, hθ, key, hkey, fun b c h => htri b c fun hm => h ?_, fun b => ?_⟩
  · show pairing (x b) (g0B k Γ ν c) = 0
    rw [pairing_g0B, hm, map_zero, map_zero]
  · obtain ⟨n, hn⟩ := hdiag b
    refine ⟨-n, ?_⟩
    show pairing (x b) (g0B k Γ ν b) = _
    rw [pairing_g0B, hn, invert_T, toLaurentSeries_T]

/-- **KL I, consequence of Proposition 3.20** (end of §3.2): the classes `[P_θ]` of the
divided-power projectives span `K₀(R(ν))` over `ℤ[q, q⁻¹]` (the unitriangularity of
`prop_3_20`, with the duality of `[P_b]` and `[S_b]` from Corollary 3.19). -/
theorem k0B_mem_span_projDiv (ν : Multiset I) (b : GProj.IndecClass ((Gkl).grade ν)) :
    k0B k Γ ν b ∈ Submodule.span (LaurentPolynomial ℤ)
      {z | ∃ (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν),
        z = K0.of (projDiv k Γ d h)} := by
  classical
  haveI := ((Gkl).finite_and_card_indecClass_le (klQ_eq_klP (Γ := Γ) KL1.stdOrient_spec)
    (fun a b _ => KL1.klP_ne_zero _ a b) KL1.klGradingDatum_degX_pos ν).1
  haveI := Fintype.ofFinite (GProj.IndecClass ((Gkl).grade ν))
  obtain ⟨θ, hθ, key, hkey, htri, hdiag⟩ := prop_3_20 k Γ ν
  set x := fun c => K0.of (projDiv k Γ (θ c) (hθ c)) with hx
  have htri' : ∀ b c, (k0B k Γ ν).repr (x b) c ≠ 0 → key b ≤ key c := fun b c hm =>
    htri b c fun h => hm (by
      rw [pairing_g0B] at h
      exact invert.injective (toLaurentSeries_injective (h.trans (map_zero _).symm) |>.trans
        (map_zero _).symm))
  have hdiag' : ∀ b, IsUnit ((k0B k Γ ν).repr (x b) b) := fun b => by
    obtain ⟨n, hn⟩ := hdiag b
    rw [pairing_g0B, ← toLaurentSeries_T] at hn
    have h := congrArg invert (toLaurentSeries_injective hn)
    have hi : ∀ q : LaurentPolynomial ℤ, invert (invert q) = q := fun q => by ext m; simp
    rw [hi, invert_T] at h
    rw [h]
    exact isUnit_T _
  refine Submodule.span_mono ?_ (basis_mem_span_of_triangular (k0B k Γ ν) x key hkey htri' hdiag' b)
  rintro _ ⟨c, rfl⟩
  exact ⟨_, hθ c, rfl⟩

end KLGamma

end Categorification.KLR
