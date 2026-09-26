/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerK0
import Categorification.KLR.K0Algebra
import Categorification.QuantumGroup.KLSpecialization
import Categorification.QuantumGroup.SerreDivided
import Categorification.QuantumGroup.Grading

/-!
# The homomorphism `γ : _𝒜 f → K₀(R)` (KL I, Theorem 1.1 and §3.1)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §1 (Theorem 1.1, TeX lines ~290–305) and §3.1, **Proposition 3.4** and its
proof (TeX lines ~2020–2070). For a graph `Γ` (no loops, no multiple edges) and the KL I
grading, over any commutative ring `k`:

"Start with the homomorphism of `ℚ(q)`-algebras `'f → K₀(R)_{ℚ(q)}` … defined by the condition
that it takes `θ_i` to `[P_i]`. There are equalities in `K₀(R)_{ℚ(q)}`:
`[P_{ij}] = [P_{ji}]` (`i · j = 0`), `[P_{iji}] = [P_{i^{(2)}j}] + [P_{ji^{(2)}}]` (`i · j = -1`) …
Therefore, the above homomorphism descends to `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}` …
`γ_{ℚ(q)}(θ_{i_1}^{(a_1)} ⋯ θ_{i_k}^{(a_k)}) = [P_{i_1^{(a_1)} ⋯ i_k^{(a_k)}}]`."

## `q` versus `v`

KL I §3.1: "our `q` is Lusztig's `v⁻¹`". In this repository `'f`, `f`, `_𝒜 f` are Lusztig's
algebras over `ℚ(v) = RatFunc ℚ`, `v = vQ` (`Categorification.QuantumGroup.KLSpecialization`),
while `K₀(R)` is a `ℤ[q, q⁻¹]`-module with `q = T 1` acting by the grading shift
(`q^a [P] = [P{a}]`, `K0.T_smul_of`). We therefore base change along
`qToV : ℤ[q, q⁻¹] → ℚ(v)`, `q ↦ v⁻¹` (`qToV_T`). This is forced by the forms, not by the
relations used here: KL I Prop. 3.3(2) `([P_i], [P_i]) = gdim 𝕜[x] = (1 - q²)⁻¹` (`deg x = 2`)
must match Lusztig's `(θ_i, θ_i) = (1 - v^{-2})⁻¹` (`KL.form_θ_θ`), and KL's twist
`q^{-|x₂|·|x₁'|}` must match Lusztig's `v^{|x₂|·|x₁'|}`. The Serre relations and the quantum
factorials are bar-invariant (`qToV_qint`: `[n]_{v⁻¹} = [n]_v`), so nothing below would change
with `q ↦ v`.

## Main definitions and results

`K₀(R)` below is `GradingDatum.K0R` for `klGradingDatum k Γ`.

* `clsSeq k Γ l = [P_l] ∈ K₀(R(|l|))` for a sequence `l`, and `clsDiv k Γ d = [P_d]` for a
  divided-power expression `d = i_1^{(a_1)} ⋯ i_r^{(a_r)}` (the list of pairs `(i_s, a_s)`).
* Integral relations in `K₀(R)` (over `ℤ[q, q⁻¹]`, no torsion issue):
  `clsSeq_append` (`[P_l][P_{l'}] = [P_{ll'}]`), `clsSeq_nil` (`[P_∅] = 1`),
  `clsSeq_expandDiv` (`[P_î] = i! [P_i]`), `clsSeq_comm` (`[P_{ij}] = [P_{ji}]`, `i · j = 0`),
  `clsSeq_cubic` (`[2] [P_{iji}] = [P_{iij}] + [P_{jii}]`, `i · j = -1`).
* `gammaZ k Γ : 'f_{ℤ[q,q⁻¹]} →ₐ K₀(R)`, `θ_i ↦ [P_i]` (`gammaZ_θ`, `gammaZ_word`), killing the
  two-sided ideal of the Serre elements with `v = q` (`gammaZ_eq_zero_of_mem_span`); it factors
  through `gammaSerreZ k Γ : 'f_{ℤ[q,q⁻¹]}/⟨Serre⟩ →ₐ K₀(R)`.
* `K0Q k Γ = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` (`q ↦ v⁻¹`), a `ℚ(v)`-algebra, with the ring map
  `toK0Q k Γ : K₀(R) → K0Q k Γ`, `toK0Q_smul : toK0Q (p • x) = qToV p • toK0Q x`, and
  `toK0Q_span_eq_top`.
* `gammaQ k Γ : 'f →ₐ[ℚ(v)] K0Q k Γ`, `θ_i ↦ [P_i]`; `gammaQ_word`
  (`θ_{i_1} ⋯ θ_{i_k} ↦ [P_{i_1 ⋯ i_k}]`), `gammaQ_dpowMono`
  (`θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)} ↦ [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`),
  `gammaQ_eq_zero_of_mem_span` (Serre elements, `v = vQ`), `gammaSerre k Γ` on
  `'f/⟨Serre⟩`.
* `gammaF k Γ hGK : f →ₐ[ℚ(v)] K0Q k Γ` (= KL's `γ_{ℚ(q)}`) **under the explicit hypothesis**
  `hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c` (quantum Gabber–Kac, not proved; the
  Cartan-datum formulation is equivalent, `gabberKac_iff`), with `gammaF_π`,
  `gammaF_dpowMono`, `gammaF_dpowF`.
* Integral version: `gammaF_mem_range` (`γ_{ℚ(q)}(_𝒜 f) ⊆ image of K₀(R)`), hence
  `gammaA k Γ hGK : _𝒜 f →+* (toK0Q k Γ).range`, and, **if `toK0Q k Γ` is injective** (e.g. if
  `K₀(R)` is `ℤ[q, q⁻¹]`-torsion-free, which is not proved here), the ring map
  `gammaInt k Γ hGK hinj : _𝒜 f →+* K₀(R)` with `gammaInt_dpowMono`
  (`θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)} ↦ [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`) and `gammaInt_smul`
  (`ℤ[q, q⁻¹]`-linearity).
* Weights: `gammaZ_mem_grade` (`'f_ν ↦ K₀(R(ν))`), `gammaQ_mem_grade`, `gammaF_π_mem_grade`
  (into the `ℚ(v)`-span `K0Qgrade k Γ ν` of `K₀(R(ν))`), `gammaInt_mem_grade`
  (`_𝒜 f ∩ f_ν ↦ K₀(R(ν))`).
* Towards injectivity (Prop. 3.4): `ker_gammaQ_le_radical_of_isometry` and
  `gammaF_injective_of_isometry`, `gammaA_injective_of_isometry`: if some `ℚ(v)`-bilinear form
  `B` on `K0Q k Γ` satisfies `B (γ x) (γ y) = (x, y)` for all `x, y ∈ 'f`, then `γ_{ℚ(q)}` and the
  integral `γ` are injective.

## Implementation

`K0Q` is a `def` built with the *local* instance `qToVAlgebra : Algebra ℤ[q,q⁻¹] ℚ(v)`
(`q ↦ v⁻¹`); it is deliberately not global. To work with the tensor product structure of
`K0Q` directly, use `attribute [local instance] KLGamma.qToVAlgebra` and unfold `K0Q`.
-/

noncomputable section

namespace Categorification.KLR.KLGamma

open Graded KLRAlgebra LaurentPolynomial QuantumGroup

variable {I : Type*} [DecidableEq I] (k : Type*) [CommRing k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-! ### Classes of the projectives `P_l` and `P_d` in `K₀(R)` -/

section Classes

omit [DecidableEq I] in
/-- The sequence `l l'` is the concatenation of the sequences `l` and `l'`. -/
theorem seq_ofList_append (l l' : List I)
    (h : ((l ++ l' : List I) : Multiset I) = (l : Multiset I) + (l' : Multiset I)) :
    Seq.ofList (l ++ l') h = (Seq.ofList l rfl).append (Seq.ofList l' rfl) := by
  apply Subtype.ext
  funext a
  obtain ⟨b, rfl⟩ :=
    (TypeA.blockEquiv (Seq.card_add' (l : Multiset I) (l' : Multiset I))).surjective a
  rcases b with x | y
  · change (Seq.ofList (l ++ l') h).lbl _ =
      ((Seq.ofList l rfl).append (Seq.ofList l' rfl)).1 (Seq.posL _ x)
    rw [Seq.append_posL, Seq.ofList_lbl]
    change _ = (Seq.ofList l rfl).lbl x
    rw [Seq.ofList_lbl]
    have hx : (x : ℕ) < l.length := by simp
    simp only [TypeA.blockEquiv_inl_val]
    rw [List.getElem_append_left hx]
  · change (Seq.ofList (l ++ l') h).lbl _ =
      ((Seq.ofList l rfl).append (Seq.ofList l' rfl)).1 (Seq.posR _ y)
    rw [Seq.append_posR, Seq.ofList_lbl]
    change _ = (Seq.ofList l' rfl).lbl y
    rw [Seq.ofList_lbl]
    simp only [TypeA.blockEquiv_inr_val]
    rw [List.getElem_append_right (by simp)]
    congr 1
    simp

/-- The class `[P_l] ∈ K₀(R(ν)) ⊆ K₀(R)`, `ν = |l|`, of `P_l = R(ν) 1_l` for a sequence `l`
(KL I §2.5). -/
def clsSeq (l : List I) : (Gkl).K0R :=
  DirectSum.of (Gkl).K0fam (l : Multiset I) (K0.of (projSeq k Γ (Seq.ofList l rfl)))

theorem clsSeq_eq {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    clsSeq k Γ l = DirectSum.of (Gkl).K0fam ν (K0.of (projSeq k Γ (Seq.ofList l h))) := by
  subst h; rfl

/-- The class `[P_d] ∈ K₀(R(ν)) ⊆ K₀(R)` of `P_d = R(ν) ψ(1_d) {-⟨d⟩}` for a divided-power
expression `d = i_1^{(a_1)} ⋯ i_r^{(a_r)}` (the list of pairs `(i_s, a_s)`), `ν = ∑ a_s i_s`
(KL I §2.5). -/
def clsDiv (d : List (I × ℕ)) : (Gkl).K0R :=
  DirectSum.of (Gkl).K0fam (expandDiv d : Multiset I) (K0.of (projDiv k Γ d rfl))

theorem clsDiv_eq {ν : Multiset I} (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    clsDiv k Γ d = DirectSum.of (Gkl).K0fam ν (K0.of (projDiv k Γ d h)) := by
  subst h; rfl

/-- **`[P_l] [P_{l'}] = [P_{ll'}]`** in `K₀(R)` (KL I §2.6, `Ind (P_i ⊠ P_j) ≅ P_{ij}`). -/
theorem clsSeq_append (l l' : List I) :
    clsSeq k Γ (l ++ l') = clsSeq k Γ l * clsSeq k Γ l' := by
  unfold clsSeq
  rw [(Gkl).K0R_of_mul_of, ← clsSeq, clsSeq_eq k Γ (l ++ l') (Multiset.coe_add l l').symm,
    seq_ofList_append]
  congr 1
  simp only [projSeq]
  rw [(Gkl).indK0_ofIdempotent]
  exact K0.of_ofIdempotent_congr (concat_e_tmul_e _ _).symm _ _ _ _

/-- `[P_∅] = [R(0)] = 1` in `K₀(R)`. -/
theorem clsSeq_nil : clsSeq k Γ [] = 1 := by
  rw [(Gkl).K0R_one, clsSeq]
  congr 1
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso]
  refine K0.of_ofIdempotent_congr ?_ _ _ _ _
  have := sum_e (k := k) (Q := klQ Γ) (ν := 0)
  rwa [Fintype.sum_unique,
    ← Subsingleton.elim (α := Seq (0 : Multiset I)) (Seq.ofList [] rfl) default] at this

theorem K0R_of_smul (p : LaurentPolynomial ℤ) {ν : Multiset I} (y : K0 ((Gkl).grade ν)) :
    DirectSum.of (Gkl).K0fam ν (p • y) = p • (DirectSum.of (Gkl).K0fam ν y : (Gkl).K0R) := by
  rw [← DirectSum.lof_eq_of (LaurentPolynomial ℤ), ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
    map_smul]

/-- **`[P_î] = i! [P_i]`** in `K₀(R)` (KL I §2.5, `P_î ≅ P_i^{i!}`). -/
theorem clsSeq_expandDiv (d : List (I × ℕ)) :
    clsSeq k Γ (expandDiv d) = divQFactLP d • clsDiv k Γ d := by
  rw [clsSeq, clsDiv, K0_projP_expandDiv d rfl, K0R_of_smul]

omit [DecidableEq I] in
theorem divQFactLP_cons (q : I × ℕ) (d : List (I × ℕ)) :
    divQFactLP (q :: d) = qfact qUnitLP q.2 * divQFactLP d := by
  simp [divQFactLP]

omit [DecidableEq I] in
theorem divQFactLP_append (d d' : List (I × ℕ)) :
    divQFactLP (d ++ d') = divQFactLP d * divQFactLP d' := by
  simp [divQFactLP]

theorem clsSeq_pair (i j : I) : clsSeq k Γ [i, j] = clsDiv k Γ [(i, 1), (j, 1)] := by
  have := clsSeq_expandDiv k Γ [(i, 1), (j, 1)]
  simpa [divQFactLP] using this

theorem clsSeq_triple (i j l : I) :
    clsSeq k Γ [i, j, l] = clsDiv k Γ [(i, 1), (j, 1), (l, 1)] := by
  have := clsSeq_expandDiv k Γ [(i, 1), (j, 1), (l, 1)]
  simpa [divQFactLP] using this

theorem clsSeq_iij (i j : I) :
    clsSeq k Γ [i, i, j] = qint qUnitLP 2 • clsDiv k Γ [(i, 2), (j, 1)] := by
  have := clsSeq_expandDiv k Γ [(i, 2), (j, 1)]
  simpa [divQFactLP, qfact_succ] using this

theorem clsSeq_jii (i j : I) :
    clsSeq k Γ [j, i, i] = qint qUnitLP 2 • clsDiv k Γ [(j, 1), (i, 2)] := by
  have := clsSeq_expandDiv k Γ [(j, 1), (i, 2)]
  simpa [divQFactLP, qfact_succ] using this

/-- **KL I §3.1, first relation**: `[P_{ij}] = [P_{ji}]` in `K₀(R)` if `i ≠ j` are not joined
by an edge (`i · j = 0`). -/
theorem clsSeq_comm {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j) :
    clsSeq k Γ [i, j] = clsSeq k Γ [j, i] := by
  have hp : (([j, i] : List I) : Multiset I) = ([i, j] : List I) :=
    Multiset.coe_eq_coe.2 (List.Perm.swap i j [])
  rw [clsSeq_pair, clsSeq_pair, clsDiv_eq k Γ [(i, 1), (j, 1)] (ν := ([i, j] : List I)) rfl,
    clsDiv_eq k Γ [(j, 1), (i, 1)] (ν := ([i, j] : List I)) hp]
  exact congrArg _ (K0_projDiv_zero (k := k) (Γ := Γ) [] [] hne hadj rfl hp)

/-- **KL I §3.1, second relation, integrally**: `[2] [P_{iji}] = [P_{iij}] + [P_{jii}]` in
`K₀(R)` (with `[2] = q + q⁻¹`) if `i` and `j` are joined by an edge (`i · j = -1`); this is
`[P_{iji}] = [P_{i^{(2)}j}] + [P_{ji^{(2)}}]` combined with `[P_{iij}] = [2] [P_{i^{(2)}j}]`. -/
theorem clsSeq_cubic {i j : I} (hadj : Γ.Adj i j) :
    qint qUnitLP 2 • clsSeq k Γ [i, j, i] = clsSeq k Γ [i, i, j] + clsSeq k Γ [j, i, i] := by
  have h₂ : (([i, i, j] : List I) : Multiset I) = ([i, j, i] : List I) :=
    Multiset.coe_eq_coe.2 (List.Perm.cons i (List.Perm.swap j i []))
  have h₃ : (([j, i, i] : List I) : Multiset I) = ([i, j, i] : List I) :=
    Multiset.coe_eq_coe.2 (List.Perm.swap i j [i])
  have key := K0_projDiv_neg_one (k := k) (Γ := Γ) [] [] hadj rfl h₂ h₃
  rw [clsSeq_triple, clsSeq_iij, clsSeq_jii, ← smul_add,
    clsDiv_eq k Γ [(i, 1), (j, 1), (i, 1)] (ν := ([i, j, i] : List I)) rfl,
    clsDiv_eq k Γ [(i, 2), (j, 1)] (ν := ([i, j, i] : List I)) h₂,
    clsDiv_eq k Γ [(j, 1), (i, 2)] (ν := ([i, j, i] : List I)) h₃, ← map_add]
  exact congrArg _ (congrArg _ key)

end Classes

/-! ### `γ` over `ℤ[q, q⁻¹]` on `'f` -/

section Integral

/-- `w ↦ [P_w]`, a monoid homomorphism `FreeMonoid I → K₀(R)`. -/
def clsSeqHom : FreeMonoid I →* (Gkl).K0R where
  toFun w := clsSeq k Γ (FreeMonoid.toList w)
  map_one' := clsSeq_nil k Γ
  map_mul' u w := by rw [FreeMonoid.toList_mul, clsSeq_append]

/-- **`γ` on `'f` over `ℤ[q, q⁻¹]`**: the `ℤ[q, q⁻¹]`-algebra map from the free algebra
`'f_{ℤ[q,q⁻¹]}` on the `θ_i` to `K₀(R)` with `θ_i ↦ [P_i]`. -/
def gammaZ : PreF (LaurentPolynomial ℤ) I →ₐ[LaurentPolynomial ℤ] (Gkl).K0R :=
  MonoidAlgebra.lift (LaurentPolynomial ℤ) (FreeMonoid I) (Gkl).K0R (clsSeqHom k Γ)

/-- `γ(θ_{i_1} ⋯ θ_{i_k}) = [P_{i_1 ⋯ i_k}]`. -/
theorem gammaZ_word (w : FreeMonoid I) :
    gammaZ k Γ (PreF.word w) = clsSeq k Γ (FreeMonoid.toList w) := by
  rw [gammaZ, PreF.word, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- `γ(θ_i) = [P_i]`. -/
theorem gammaZ_θ (i : I) : gammaZ k Γ (PreF.θ i) = clsSeq k Γ [i] :=
  gammaZ_word k Γ _

theorem gammaZ_θ_mul_θ (i j : I) :
    gammaZ k Γ (PreF.θ i * PreF.θ j) = clsSeq k Γ [i, j] := by
  rw [map_mul, gammaZ_θ, gammaZ_θ, ← clsSeq_append]; rfl

theorem gammaZ_θ_mul_θ_mul_θ (i j l : I) :
    gammaZ k Γ (PreF.θ i * (PreF.θ j * PreF.θ l)) = clsSeq k Γ [i, j, l] := by
  rw [map_mul, gammaZ_θ_mul_θ, gammaZ_θ, ← clsSeq_append]; rfl

theorem gammaZ_serreComm {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j) :
    gammaZ k Γ (PreF.serreComm i j) = 0 := by
  rw [PreF.serreComm, map_sub, gammaZ_θ_mul_θ, gammaZ_θ_mul_θ, clsSeq_comm k Γ hne hadj,
    sub_self]

/-- `γ(θ_i²θ_j - (q + q⁻¹)θ_iθ_jθ_i + θ_jθ_i²) = 0` for an edge `i — j`. -/
theorem gammaZ_serreCubic {i j : I} (hadj : Γ.Adj i j) :
    gammaZ k Γ (PreF.serreCubic qUnitLP i j) = 0 := by
  rw [PreF.serreCubic, map_add, map_sub, map_smul, gammaZ_θ_mul_θ_mul_θ, gammaZ_θ_mul_θ_mul_θ,
    gammaZ_θ_mul_θ_mul_θ, ← qint_two, clsSeq_cubic k Γ hadj]
  abel

theorem ofGraph_adj_of_dot_eq_neg_one {i j : I}
    (h : (KL.C Γ).dot i j = -1) : Γ.Adj i j := by
  by_contra hadj
  by_cases hij : i = j
  · subst hij; simp at h
  · rw [CartanDatum.ofGraph_dot_of_not_adj Γ hij hadj] at h; omega

theorem ofGraph_not_adj_of_dot_eq_zero {i j : I}
    (h : (KL.C Γ).dot i j = 0) : ¬ Γ.Adj i j :=
  fun hadj => by rw [CartanDatum.ofGraph_dot_of_adj Γ hadj] at h; omega

theorem gammaZ_eq_zero_of_mem_serreSet {x : PreF (LaurentPolynomial ℤ) I}
    (hx : x ∈ PreF.serreSet (KL.C Γ).dot qUnitLP) : gammaZ k Γ x = 0 := by
  rcases hx with ⟨i, j, hij, h0, rfl⟩ | ⟨i, j, hij, h1, rfl⟩
  · exact gammaZ_serreComm k Γ hij (ofGraph_not_adj_of_dot_eq_zero Γ h0)
  · exact gammaZ_serreCubic k Γ (ofGraph_adj_of_dot_eq_neg_one Γ h1)

/-- **`γ` kills the Serre relations integrally**: the two-sided ideal of `'f_{ℤ[q,q⁻¹]}`
generated by the simply-laced Serre elements (KL I §1, with `v = q`) lies in `ker γ`. -/
theorem gammaZ_eq_zero_of_mem_span {x : PreF (LaurentPolynomial ℤ) I}
    (hx : x ∈ TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot qUnitLP)) : gammaZ k Γ x = 0 := by
  have h : TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot qUnitLP) ≤
      (RingHom.ker (gammaZ k Γ)).toTwoSided := by
    rw [TwoSidedIdeal.span_le]
    intro y hy
    exact Ideal.mem_toTwoSided.2 (gammaZ_eq_zero_of_mem_serreSet k Γ hy)
  exact Ideal.mem_toTwoSided.1 (h hx)

/-- The two-sided ideal of `'f_{ℤ[q,q⁻¹]}` generated by the simply-laced Serre elements. -/
abbrev serreIdealZ : Ideal (PreF (LaurentPolynomial ℤ) I) :=
  TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot qUnitLP))

set_option synthInstance.maxHeartbeats 200000 in
/-- `γ` on `'f_{ℤ[q,q⁻¹]}/⟨Serre⟩` (the algebra of KL I §1 given by generators and relations,
over `ℤ[q, q⁻¹]`). -/
def gammaSerreZ :
    (PreF (LaurentPolynomial ℤ) I ⧸ serreIdealZ Γ) →ₐ[LaurentPolynomial ℤ] (Gkl).K0R :=
  Ideal.Quotient.liftₐ (serreIdealZ Γ) (gammaZ k Γ)
    (fun _ ha => gammaZ_eq_zero_of_mem_span k Γ (TwoSidedIdeal.mem_asIdeal.1 ha))

set_option synthInstance.maxHeartbeats 200000 in
theorem gammaSerreZ_mk (x : PreF (LaurentPolynomial ℤ) I) :
    gammaSerreZ k Γ (Ideal.Quotient.mk (serreIdealZ Γ) x) = gammaZ k Γ x := rfl

end Integral

/-! ### `K₀(R)_{ℚ(v)} = ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` with `q ↦ v⁻¹` -/

section K0Q

/-- The specialisation `ℤ[q, q⁻¹] → ℚ(v)`, `q ↦ v⁻¹` (KL I §3.1: "our `q` is Lusztig's
`v⁻¹`"). -/
def qToV : LaurentPolynomial ℤ →+* RatFunc ℚ := laurentEval vQ⁻¹

theorem qToV_T (n : ℤ) : qToV (T n) = ((vQ ^ (-n) : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [qToV, laurentEval_T, inv_zpow']

/-- The `ℤ[q, q⁻¹]`-algebra structure on `ℚ(v)` given by `q ↦ v⁻¹`. Not a global instance. -/
@[reducible] def qToVAlgebra : Algebra (LaurentPolynomial ℤ) (RatFunc ℚ) := qToV.toAlgebra

attribute [local instance] qToVAlgebra

/-- **`K₀(R)_{ℚ(q)} = K₀(R) ⊗_{ℤ[q,q⁻¹]} ℚ(q)`** of KL I §3.1, realised as
`ℚ(v) ⊗_{ℤ[q,q⁻¹]} K₀(R)` along `q ↦ v⁻¹`. -/
def K0Q : Type _ := TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R

instance : Ring (K0Q k Γ) :=
  inferInstanceAs (Ring (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R))

instance : Algebra (RatFunc ℚ) (K0Q k Γ) :=
  inferInstanceAs
    (Algebra (RatFunc ℚ) (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R))

/-- The ring map `K₀(R) → K₀(R)_{ℚ(v)}`, `x ↦ 1 ⊗ x`. -/
def toK0Q : (Gkl).K0R →+* K0Q k Γ :=
  (Algebra.TensorProduct.includeRight : (Gkl).K0R →ₐ[LaurentPolynomial ℤ]
    TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R).toRingHom

/-- `toK0Q` is semilinear along `q ↦ v⁻¹`. -/
theorem toK0Q_smul (p : LaurentPolynomial ℤ) (x : (Gkl).K0R) :
    toK0Q k Γ (p • x) = qToV p • toK0Q k Γ x := by
  change (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] (p • x) =
    (qToV p • (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x :
      TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (Gkl).K0R)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]
  rfl

/-- `K₀(R)_{ℚ(v)}` is spanned over `ℚ(v)` by the image of `K₀(R)`. -/
theorem toK0Q_span_eq_top :
    Submodule.span (RatFunc ℚ) (Set.range (toK0Q k Γ)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  refine TensorProduct.induction_on (motive := fun z : TensorProduct (LaurentPolynomial ℤ)
    (RatFunc ℚ) (Gkl).K0R => (z : K0Q k Γ) ∈ Submodule.span (RatFunc ℚ) (Set.range (toK0Q k Γ)))
    z ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro a x
    have : (a ⊗ₜ[LaurentPolynomial ℤ] x : TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ)
        (Gkl).K0R) = (a • toK0Q k Γ x : K0Q k Γ) := by
      change _ = a • (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change (a ⊗ₜ[LaurentPolynomial ℤ] x : K0Q k Γ) ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

end K0Q

/-! ### Quantum integers under `q ↦ v⁻¹` -/

section QInt

omit [DecidableEq I] in
/-- `[n]` in `ℤ[q, q⁻¹]` specialises to `[n]_v` (bar invariance: `[n]_{v⁻¹} = [n]_v`). -/
theorem qToV_qint (n : ℕ) : qToV (qint qUnitLP n) = qint vQ n := by
  rw [qint_qUnitLP, map_sum, qint_eq_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [qToV_T]
  congr 2
  omega

theorem qToV_qfact (n : ℕ) : qToV (qfact qUnitLP n) = qfact vQ n := by
  simp only [qfact, map_prod, qToV_qint]

omit [DecidableEq I] in
theorem qToV_divQFactLP (d : List (I × ℕ)) :
    qToV (divQFactLP d) = (d.map fun q => qfact vQ q.2).prod := by
  simp only [divQFactLP, map_list_prod, List.map_map, Function.comp_def, qToV_qfact]

theorem qfact_vQ_ne_zero (n : ℕ) : qfact vQ n ≠ 0 :=
  qfact_ne_zero (fun _ hm => vQ_pow_ne_one hm) n

omit [DecidableEq I] in
theorem qToV_divQFactLP_ne_zero (d : List (I × ℕ)) : qToV (divQFactLP d) ≠ 0 := by
  rw [qToV_divQFactLP]
  induction d with
  | nil => simp
  | cons q d ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_ne_zero (qfact_vQ_ne_zero _) ih

theorem qToV_qint_two :
    qToV (qint qUnitLP 2) = (vQ : RatFunc ℚ) + ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [qToV_qint, qint_two]

/-- For the KL I Cartan datum, `v_i = v`. -/
theorem vi_ofGraph_vQ (i : I) : PreF.vi (KL.C Γ).dot vQ i = vQ := by
  rw [PreF.vi, CartanDatum.ofGraph_dot_self]
  norm_num

end QInt

/-! ### Products of `[P_d]` in `K₀(R)_{ℚ(v)}` -/

/-- **`[P_d] [P_{d'}] = [P_{dd'}]`** in `K₀(R)_{ℚ(v)}` for divided-power expressions (from
`[P_î] = i! [P_i]` and the invertibility of `i!` in `ℚ(v)`). -/
theorem toK0Q_clsDiv_append (d d' : List (I × ℕ)) :
    toK0Q k Γ (clsDiv k Γ (d ++ d')) =
      toK0Q k Γ (clsDiv k Γ d) * toK0Q k Γ (clsDiv k Γ d') := by
  have e := clsSeq_expandDiv k Γ (d ++ d')
  rw [expandDiv_append, clsSeq_append, clsSeq_expandDiv, clsSeq_expandDiv,
    divQFactLP_append] at e
  have e' := congrArg (toK0Q k Γ) e
  rw [map_mul, toK0Q_smul, toK0Q_smul, toK0Q_smul, map_mul, smul_mul_smul_comm] at e'
  have hc := mul_ne_zero (qToV_divQFactLP_ne_zero d) (qToV_divQFactLP_ne_zero d')
  have e'' := congrArg (fun z => (qToV (divQFactLP d) * qToV (divQFactLP d'))⁻¹ • z) e'
  simp only [inv_smul_smul₀ hc] at e''
  exact e''.symm

theorem toK0Q_clsDiv_nil : toK0Q k Γ (clsDiv k Γ []) = 1 := by
  have e := clsSeq_expandDiv k Γ []
  simp only [divQFactLP, List.map_nil, List.prod_nil, one_smul] at e
  rw [← e]
  exact (congrArg _ (clsSeq_nil k Γ)).trans (map_one _)

/-! ### `γ_{ℚ(q)}` on `'f`, on `'f/⟨Serre⟩` and on `f` -/

section GammaQ

/-- **`'f → K₀(R)_{ℚ(q)}`, `θ_i ↦ [P_i]`** (KL I §3.1, proof of Prop. 3.4): the
`ℚ(v)`-algebra map out of the free algebra `'f` on the `θ_i`. -/
def gammaQ : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] K0Q k Γ :=
  MonoidAlgebra.lift (RatFunc ℚ) (FreeMonoid I) (K0Q k Γ)
    ((toK0Q k Γ).toMonoidHom.comp (clsSeqHom k Γ))

/-- `γ_{ℚ(q)}(θ_{i_1} ⋯ θ_{i_k}) = [P_{i_1 ⋯ i_k}]`. -/
theorem gammaQ_word (w : FreeMonoid I) :
    gammaQ k Γ (PreF.word w) = toK0Q k Γ (clsSeq k Γ (FreeMonoid.toList w)) := by
  rw [gammaQ, PreF.word, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- `γ_{ℚ(q)}` is the base change of the integral `γ` on `'f_{ℤ[q,q⁻¹]}`. -/
theorem gammaQ_word_eq (w : FreeMonoid I) :
    gammaQ k Γ (PreF.word w) = toK0Q k Γ (gammaZ k Γ (PreF.word w)) := by
  rw [gammaQ_word, gammaZ_word]

/-- `γ_{ℚ(q)}(θ_i) = [P_i]`. -/
theorem gammaQ_θ (i : I) : gammaQ k Γ (PreF.θ i) = toK0Q k Γ (clsSeq k Γ [i]) :=
  gammaQ_word k Γ _

theorem gammaQ_θ_mul_θ (i j : I) :
    gammaQ k Γ (PreF.θ i * PreF.θ j) = toK0Q k Γ (clsSeq k Γ [i, j]) := by
  rw [map_mul, gammaQ_θ, gammaQ_θ, ← map_mul, ← clsSeq_append]; rfl

theorem gammaQ_θ_mul_θ_mul_θ (i j l : I) :
    gammaQ k Γ (PreF.θ i * (PreF.θ j * PreF.θ l)) = toK0Q k Γ (clsSeq k Γ [i, j, l]) := by
  rw [map_mul, gammaQ_θ_mul_θ, gammaQ_θ, ← map_mul, ← clsSeq_append]; rfl

theorem gammaQ_serreComm {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j) :
    gammaQ k Γ (PreF.serreComm i j) = 0 := by
  rw [PreF.serreComm, map_sub, gammaQ_θ_mul_θ, gammaQ_θ_mul_θ, clsSeq_comm k Γ hne hadj,
    sub_self]

/-- `γ_{ℚ(q)}(θ_i²θ_j - (v + v⁻¹)θ_iθ_jθ_i + θ_jθ_i²) = 0` for an edge `i — j`. -/
theorem gammaQ_serreCubic {i j : I} (hadj : Γ.Adj i j) :
    gammaQ k Γ (PreF.serreCubic vQ i j) = 0 := by
  rw [PreF.serreCubic, map_add, map_sub, map_smul, gammaQ_θ_mul_θ_mul_θ, gammaQ_θ_mul_θ_mul_θ,
    gammaQ_θ_mul_θ_mul_θ, ← qToV_qint_two, ← toK0Q_smul, clsSeq_cubic k Γ hadj, map_add]
  abel

theorem gammaQ_eq_zero_of_mem_serreSet {x : PreF (RatFunc ℚ) I}
    (hx : x ∈ PreF.serreSet (KL.C Γ).dot vQ) : gammaQ k Γ x = 0 := by
  rcases hx with ⟨i, j, hij, h0, rfl⟩ | ⟨i, j, hij, h1, rfl⟩
  · exact gammaQ_serreComm k Γ hij (ofGraph_not_adj_of_dot_eq_zero Γ h0)
  · exact gammaQ_serreCubic k Γ (ofGraph_adj_of_dot_eq_neg_one Γ h1)

/-- **`γ_{ℚ(q)}` kills the Serre relations** (KL I §3.1: "These equalities match the generators
of the ideal `ℐ`"): the two-sided ideal of `'f` generated by the simply-laced Serre elements
lies in `ker γ_{ℚ(q)}`. -/
theorem gammaQ_eq_zero_of_mem_span {x : PreF (RatFunc ℚ) I}
    (hx : x ∈ TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot vQ)) : gammaQ k Γ x = 0 := by
  have h : TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot vQ) ≤
      (RingHom.ker (gammaQ k Γ)).toTwoSided := by
    rw [TwoSidedIdeal.span_le]
    intro y hy
    exact Ideal.mem_toTwoSided.2 (gammaQ_eq_zero_of_mem_serreSet k Γ hy)
  exact Ideal.mem_toTwoSided.1 (h hx)

/-- The two-sided ideal of `'f` generated by the simply-laced Serre elements. -/
abbrev serreIdealQ : Ideal (PreF (RatFunc ℚ) I) :=
  TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (PreF.serreSet (KL.C Γ).dot vQ))

/-- `γ_{ℚ(q)}` on `'f/⟨Serre⟩` (unconditionally). -/
def gammaSerre : (PreF (RatFunc ℚ) I ⧸ serreIdealQ Γ) →ₐ[RatFunc ℚ] K0Q k Γ :=
  Ideal.Quotient.liftₐ (serreIdealQ Γ) (gammaQ k Γ)
    (fun _ ha => gammaQ_eq_zero_of_mem_span k Γ (TwoSidedIdeal.mem_asIdeal.1 ha))

theorem gammaSerre_mk (x : PreF (RatFunc ℚ) I) :
    gammaSerre k Γ (Ideal.Quotient.mk (serreIdealQ Γ) x) = gammaQ k Γ x := rfl

/-- **`γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}`** (KL I §3.1), under the explicit hypothesis `hGK` that the
quantum Gabber–Kac theorem holds (the radical `ℐ` is generated by the Serre elements). -/
def gammaF (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    KL.F Γ →ₐ[RatFunc ℚ] K0Q k Γ :=
  Ideal.Quotient.liftₐ (PreF.radical (KL.C Γ).dot vQ (KL.C Γ).c) (gammaQ k Γ)
    (fun _ ha => gammaQ_eq_zero_of_mem_span k Γ
      (TwoSidedIdeal.mem_asIdeal.1 (by rw [hGK] at ha; exact ha)))

theorem gammaF_π (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) (x : PreF (RatFunc ℚ) I) :
    gammaF k Γ hGK (KL.π Γ x) = gammaQ k Γ x := rfl

/-- The Cartan-datum form of the Serre elements (`CartanDatum.serreSet`) agrees with the
simply-laced one (`PreF.serreSet`) for the KL I datum of `Γ`. -/
theorem cartan_serreSet_ofGraph {K : Type*} [CommRing K] (v : Kˣ) :
    (KL.C Γ).serreSet v = PreF.serreSet (K := K) (KL.C Γ).dot v := by
  ext x
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    by_cases hadj : Γ.Adj i j
    · right
      refine ⟨i, j, hij, CartanDatum.ofGraph_dot_of_adj Γ hadj, ?_⟩
      rw [KL.serreN_of_adj Γ hadj]
      exact PreF.serreSeq_two i j (CartanDatum.ofGraph_dot_self Γ i)
        (CartanDatum.ofGraph_dot_of_adj Γ hadj.symm)
    · left
      refine ⟨i, j, hij, CartanDatum.ofGraph_dot_of_not_adj Γ hij hadj, ?_⟩
      have hN : (KL.C Γ).serreN i j = 1 := by
        simp [CartanDatum.serreN, CartanDatum.ofGraph_dot_of_not_adj Γ hij hadj]
      rw [hN]
      exact PreF.serreSeq_one i j (CartanDatum.ofGraph_dot_of_not_adj Γ (Ne.symm hij)
        (fun h => hadj h.symm))
  · rintro (⟨i, j, hij, h0, rfl⟩ | ⟨i, j, hij, h1, rfl⟩)
    · refine ⟨i, j, hij, ?_⟩
      have hadj := ofGraph_not_adj_of_dot_eq_zero Γ h0
      have hN : (KL.C Γ).serreN i j = 1 := by simp [CartanDatum.serreN, h0]
      rw [hN, PreF.serreSeq_one i j (CartanDatum.ofGraph_dot_of_not_adj Γ (Ne.symm hij)
        (fun h => hadj h.symm))]
    · refine ⟨i, j, hij, ?_⟩
      have hadj := ofGraph_adj_of_dot_eq_neg_one Γ h1
      rw [KL.serreN_of_adj Γ hadj, PreF.serreSeq_two i j (CartanDatum.ofGraph_dot_self Γ i)
        (CartanDatum.ofGraph_dot_of_adj Γ hadj.symm)]

/-- The two formulations of the Gabber–Kac hypothesis agree for the KL I datum. -/
theorem gabberKac_iff :
    (KL.C Γ).GabberKac vQ (KL.C Γ).c ↔ PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c := by
  rw [CartanDatum.GabberKac, PreF.GabberKac, cartan_serreSet_ofGraph]

/-! #### Divided powers -/

theorem gammaQ_θ_pow (i : I) (a : ℕ) :
    gammaQ k Γ (PreF.θ i ^ a) = toK0Q k Γ (clsSeq k Γ (List.replicate a i)) := by
  induction a with
  | zero => rw [pow_zero, map_one, List.replicate_zero, clsSeq_nil, map_one]
  | succ a ih =>
    rw [pow_succ, map_mul, ih, gammaQ_θ, ← map_mul, ← clsSeq_append, List.replicate_succ']

/-- `γ_{ℚ(q)}(θ_i^{(a)}) = [P_{i^{(a)}}]`. -/
theorem gammaQ_dpow (i : I) (a : ℕ) :
    gammaQ k Γ (PreF.dpow (KL.C Γ).dot vQ i a) = toK0Q k Γ (clsDiv k Γ [(i, a)]) := by
  have e := clsSeq_expandDiv k Γ [(i, a)]
  have hx : expandDiv [(i, a)] = List.replicate a i := by simp [expandDiv]
  rw [hx] at e
  rw [PreF.dpow, map_smul, gammaQ_θ_pow, e, toK0Q_smul, qToV_divQFactLP, vi_ofGraph_vQ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact inv_smul_smul₀ (qfact_vQ_ne_zero a) _

/-- The divided-power monomial `θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)} ∈ 'f` of
`d = i_1^{(a_1)} ⋯ i_r^{(a_r)}`. -/
def dpowMono (d : List (I × ℕ)) : PreF (RatFunc ℚ) I :=
  (d.map fun q => PreF.dpow (KL.C Γ).dot vQ q.1 q.2).prod

theorem π_dpowMono (d : List (I × ℕ)) :
    KL.π Γ (dpowMono Γ d) = (d.map fun q => PreF.dpowF (KL.C Γ).dot vQ (KL.C Γ).c q.1 q.2).prod := by
  rw [dpowMono, map_list_prod, List.map_map]
  rfl

/-- **`γ_{ℚ(q)}(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`** (KL I
§3.1). -/
theorem gammaQ_dpowMono (d : List (I × ℕ)) :
    gammaQ k Γ (dpowMono Γ d) = toK0Q k Γ (clsDiv k Γ d) := by
  induction d with
  | nil => rw [dpowMono, List.map_nil, List.prod_nil, map_one, toK0Q_clsDiv_nil]
  | cons q d ih =>
    rw [dpowMono, List.map_cons, List.prod_cons, map_mul, ← dpowMono, ih, gammaQ_dpow,
      show q :: d = [q] ++ d from rfl, toK0Q_clsDiv_append]

/-- **KL I §3.1**: `γ_{ℚ(q)}(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`
in `f` (under the Gabber–Kac hypothesis). -/
theorem gammaF_dpowMono (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (d : List (I × ℕ)) :
    gammaF k Γ hGK (KL.π Γ (dpowMono Γ d)) = toK0Q k Γ (clsDiv k Γ d) :=
  gammaQ_dpowMono k Γ d

theorem gammaF_dpowF (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) (i : I) (a : ℕ) :
    gammaF k Γ hGK (PreF.dpowF (KL.C Γ).dot vQ (KL.C Γ).c i a) =
      toK0Q k Γ (clsDiv k Γ [(i, a)]) :=
  gammaQ_dpow k Γ i a

end GammaQ

/-! ### The integral form: `γ : _𝒜 f → K₀(R)` -/

section GammaA

theorem algebraMap_qToV_mem_Af (p : LaurentPolynomial ℤ) :
    algebraMap (RatFunc ℚ) (KL.F Γ) (qToV p) ∈ KL.Af Γ := by
  induction p using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Subring.zero_mem _
  | add p q hp hq => rw [map_add, map_add]; exact Subring.add_mem _ hp hq
  | single n m =>
    have : (Finsupp.single n m : LaurentPolynomial ℤ) = m • T n := by
      rw [T, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, qToV_T]
    exact Subring.zsmul_mem _ (PreF.algebraMap_zpow_mem_Af (-n)) m

/-- The divided-power monomials lie in `_𝒜 f`. -/
theorem π_dpowMono_mem_Af (d : List (I × ℕ)) : KL.π Γ (dpowMono Γ d) ∈ KL.Af Γ := by
  rw [π_dpowMono]
  refine Subring.list_prod_mem _ fun y hy => ?_
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hy
  exact PreF.dpowF_mem_Af q.1 q.2

variable {k Γ} in
/-- **`γ_{ℚ(q)}(_𝒜 f) ⊆ K₀(R)`** (KL I §3.1: "The image of the restriction of `γ_{ℚ(q)}` to `Af`
lies in `K₀(R)`"): more precisely, in the image of `K₀(R) → K₀(R)_{ℚ(q)}`. -/
theorem gammaF_mem_range (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) {x : KL.F Γ}
    (hx : x ∈ KL.Af Γ) : gammaF k Γ hGK x ∈ (toK0Q k Γ).range := by
  have hle : KL.Af Γ ≤ (toK0Q k Γ).range.comap (gammaF k Γ hGK).toRingHom := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨⟨i, a⟩, rfl⟩ | hy)
    · exact ⟨clsDiv k Γ [(i, a)], (gammaF_dpowF k Γ hGK i a).symm⟩
    · have key : ∀ n : ℤ, (gammaF k Γ hGK).toRingHom
          (algebraMap (RatFunc ℚ) (KL.F Γ) ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ)) ∈
            (toK0Q k Γ).range := fun n => by
        refine ⟨(T (-n) : LaurentPolynomial ℤ) • (1 : (Gkl).K0R), ?_⟩
        rw [toK0Q_smul, map_one, qToV_T, neg_neg, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      rcases hy with rfl | rfl
      · simpa using key 1
      · simpa using key (-1)
  exact hle hx

/-- **The integral `γ`**, with values in the image of `K₀(R)` in `K₀(R)_{ℚ(q)}` (a subring,
stable under `ℤ[q, q⁻¹]` by `toK0Q_smul`), under the Gabber–Kac hypothesis. -/
def gammaA (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) :
    KL.Af Γ →+* (toK0Q k Γ).range :=
  ((gammaF k Γ hGK).toRingHom.comp (KL.Af Γ).subtype).codRestrict _
    fun x => gammaF_mem_range hGK x.2

theorem coe_gammaA (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c) (x : KL.Af Γ) :
    (gammaA k Γ hGK x : K0Q k Γ) = gammaF k Γ hGK x := rfl

theorem gammaA_dpowMono (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (d : List (I × ℕ)) :
    gammaA k Γ hGK ⟨KL.π Γ (dpowMono Γ d), π_dpowMono_mem_Af Γ d⟩ =
      (toK0Q k Γ).rangeRestrict (clsDiv k Γ d) :=
  Subtype.ext (gammaF_dpowMono k Γ hGK d)

/-- `K₀(R) ≅ toK0Q(K₀(R))` when `toK0Q` is injective. -/
def K0RrangeEquiv (hinj : Function.Injective (toK0Q k Γ)) :
    (Gkl).K0R ≃+* (toK0Q k Γ).range :=
  RingEquiv.ofBijective (toK0Q k Γ).rangeRestrict
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), (toK0Q k Γ).rangeRestrict_surjective⟩

/-- **`γ : _𝒜 f → K₀(R)`** (KL I, Theorem 1.1 / Proposition 3.4, the map), under the
Gabber–Kac hypothesis `hGK` and the hypothesis `hinj` that `K₀(R) → K₀(R)_{ℚ(q)}` is injective
(e.g. `K₀(R)` torsion-free over `ℤ[q, q⁻¹]`; not proved here). -/
def gammaInt (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) : KL.Af Γ →+* (Gkl).K0R :=
  (K0RrangeEquiv k Γ hinj).symm.toRingHom.comp (gammaA k Γ hGK)

theorem toK0Q_gammaInt (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) (x : KL.Af Γ) :
    toK0Q k Γ (gammaInt k Γ hGK hinj x) = gammaF k Γ hGK x := by
  have := (K0RrangeEquiv k Γ hinj).apply_symm_apply (gammaA k Γ hGK x)
  exact congrArg Subtype.val this

/-- **`γ(θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}) = [P_{i_1^{(a_1)} ⋯ i_r^{(a_r)}}]`** in `K₀(R)`. -/
theorem gammaInt_dpowMono (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) (d : List (I × ℕ)) :
    gammaInt k Γ hGK hinj ⟨KL.π Γ (dpowMono Γ d), π_dpowMono_mem_Af Γ d⟩ = clsDiv k Γ d :=
  hinj (by rw [toK0Q_gammaInt]; exact gammaF_dpowMono k Γ hGK d)

/-- `γ` is `ℤ[q, q⁻¹]`-linear (`q` acting on `_𝒜 f` as `v⁻¹`). -/
theorem gammaInt_smul (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) (p : LaurentPolynomial ℤ) (x : KL.Af Γ) :
    gammaInt k Γ hGK hinj
        ⟨algebraMap (RatFunc ℚ) (KL.F Γ) (qToV p) * x,
          Subring.mul_mem _ (algebraMap_qToV_mem_Af Γ p) x.2⟩ =
      p • gammaInt k Γ hGK hinj x :=
  hinj (by
    rw [toK0Q_gammaInt, toK0Q_smul, toK0Q_gammaInt, map_mul, AlgHom.commutes,
      Algebra.smul_def])

end GammaA

/-! ### Compatibility with the weight decompositions -/

section Grading

theorem clsSeq_mem_range_lof {ν : Multiset I} (l : List I) (h : (l : Multiset I) = ν) :
    clsSeq k Γ l ∈
      LinearMap.range (DirectSum.lof (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν) :=
  ⟨_, (DirectSum.lof_eq_of _ _ _ _ _).trans (clsSeq_eq k Γ l h).symm⟩

/-- **`γ('f_ν) ⊆ K₀(R(ν))`** over `ℤ[q, q⁻¹]`. -/
theorem gammaZ_mem_grade {ν : Multiset I} {x : PreF (LaurentPolynomial ℤ) I}
    (hx : x ∈ PreF.grade (LaurentPolynomial ℤ) ν) :
    gammaZ k Γ x ∈
      LinearMap.range (DirectSum.lof (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν) := by
  rw [PreF.grade, PreF.supp_eq_span] at hx
  have hle : Submodule.span (LaurentPolynomial ℤ) (PreF.word '' {w : FreeMonoid I | wt w = ν}) ≤
      (LinearMap.range (DirectSum.lof (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν)).comap
        (gammaZ k Γ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, gammaZ_word]
    exact clsSeq_mem_range_lof k Γ _ hw
  exact hle hx

/-- The weight-`ν` part of `K₀(R)_{ℚ(v)}`: the `ℚ(v)`-span of the image of `K₀(R(ν))`. -/
def K0Qgrade (ν : Multiset I) : Submodule (RatFunc ℚ) (K0Q k Γ) :=
  Submodule.span (RatFunc ℚ) (toK0Q k Γ '' Set.range (DirectSum.of (Gkl).K0fam ν))

/-- **`γ_{ℚ(q)}('f_ν) ⊆ K₀(R(ν))_{ℚ(q)}`**. -/
theorem gammaQ_mem_grade {ν : Multiset I} {x : PreF (RatFunc ℚ) I}
    (hx : x ∈ PreF.grade (RatFunc ℚ) ν) : gammaQ k Γ x ∈ K0Qgrade k Γ ν := by
  rw [PreF.grade, PreF.supp_eq_span] at hx
  have hle : Submodule.span (RatFunc ℚ) (PreF.word '' {w : FreeMonoid I | wt w = ν}) ≤
      (K0Qgrade k Γ ν).comap (gammaQ k Γ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply, gammaQ_word,
      clsSeq_eq k Γ _ hw]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle hx

/-- **`γ_{ℚ(q)}(f_ν) ⊆ K₀(R(ν))_{ℚ(q)}`**, `f_ν = π('f_ν)`. -/
theorem gammaF_π_mem_grade (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {ν : Multiset I} {x : PreF (RatFunc ℚ) I} (hx : x ∈ PreF.grade (RatFunc ℚ) ν) :
    gammaF k Γ hGK (KL.π Γ x) ∈ K0Qgrade k Γ ν :=
  gammaQ_mem_grade k Γ hx

/-- The projection `K₀(R) → K₀(R(ν)) ⊆ K₀(R)`. -/
def projK0R (ν : Multiset I) : (Gkl).K0R →ₗ[LaurentPolynomial ℤ] (Gkl).K0R :=
  (DirectSum.lof (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν).comp
    (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν)

attribute [local instance] qToVAlgebra in
/-- Its base change to `K₀(R)_{ℚ(v)}`. -/
def projK0Q (ν : Multiset I) : K0Q k Γ →ₗ[RatFunc ℚ] K0Q k Γ :=
  LinearMap.baseChange (RatFunc ℚ) (projK0R k Γ ν)

attribute [local instance] qToVAlgebra in
theorem projK0Q_toK0Q (ν : Multiset I) (x : (Gkl).K0R) :
    projK0Q k Γ ν (toK0Q k Γ x) = toK0Q k Γ (projK0R k Γ ν x) :=
  LinearMap.baseChange_tmul _ _ _

theorem projK0Q_of_mem {ν : Multiset I} {y : K0Q k Γ} (hy : y ∈ K0Qgrade k Γ ν) :
    projK0Q k Γ ν y = y := by
  have hle : K0Qgrade k Γ ν ≤ LinearMap.eqLocus (projK0Q k Γ ν) LinearMap.id := by
    rw [K0Qgrade, Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    show projK0Q k Γ ν (toK0Q k Γ _) = toK0Q k Γ _
    rw [projK0Q_toK0Q, projK0R, LinearMap.comp_apply,
      ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.lof_self]
  exact hle hy

/-- **`γ(_𝒜 f ∩ f_ν) ⊆ K₀(R(ν))`** for the integral `γ`. -/
theorem gammaInt_mem_grade (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ)) {ν : Multiset I} (x : KL.Af Γ)
    {y : PreF (RatFunc ℚ) I} (hy : y ∈ PreF.grade (RatFunc ℚ) ν)
    (hxy : (x : KL.F Γ) = KL.π Γ y) :
    gammaInt k Γ hGK hinj x ∈
      LinearMap.range (DirectSum.lof (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν) := by
  refine ⟨DirectSum.component (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam ν
    (gammaInt k Γ hGK hinj x), hinj ?_⟩
  have h1 := projK0Q_toK0Q k Γ ν (gammaInt k Γ hGK hinj x)
  rw [toK0Q_gammaInt, hxy, projK0Q_of_mem k Γ (gammaF_π_mem_grade k Γ hGK hy), ← hxy,
    ← toK0Q_gammaInt k Γ hGK hinj] at h1
  exact h1.symm

end Grading

/-! ### Towards injectivity (KL I, Proposition 3.4) -/

section Injectivity

/-- If `γ_{ℚ(q)}` is an isometry for some bilinear form `B` on `K₀(R)_{ℚ(q)}` (KL I §3.1:
`(γ x, γ y) = (x, y)`), its kernel lies in the radical `ℐ` of Lusztig's form. -/
theorem ker_gammaQ_le_radical_of_isometry
    (B : K0Q k Γ →ₗ[RatFunc ℚ] K0Q k Γ →ₗ[RatFunc ℚ] RatFunc ℚ)
    (hB : ∀ x y : PreF (RatFunc ℚ) I, B (gammaQ k Γ x) (gammaQ k Γ y) = (KL.C Γ).form x y)
    {x : PreF (RatFunc ℚ) I} (hx : gammaQ k Γ x = 0) :
    x ∈ PreF.radical (KL.C Γ).dot vQ (KL.C Γ).c :=
  PreF.mem_radical.2 fun y => by
    rw [← CartanDatum.form, ← hB, hx, map_zero, LinearMap.zero_apply]

/-- **Injectivity of `γ_{ℚ(q)} : f → K₀(R)_{ℚ(q)}`** (KL I Prop. 3.4, first step), given the
Gabber–Kac hypothesis and a bilinear form `B` for which `γ_{ℚ(q)}` is an isometry. -/
theorem gammaF_injective_of_isometry (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (B : K0Q k Γ →ₗ[RatFunc ℚ] K0Q k Γ →ₗ[RatFunc ℚ] RatFunc ℚ)
    (hB : ∀ x y : PreF (RatFunc ℚ) I, B (gammaQ k Γ x) (gammaQ k Γ y) = (KL.C Γ).form x y) :
    Function.Injective (gammaF k Γ hGK) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := PreF.π_surjective (dot := (KL.C Γ).dot) (v := vQ) (c := (KL.C Γ).c) z
  exact PreF.π_eq_zero_iff.2 (ker_gammaQ_le_radical_of_isometry k Γ B hB hz)

/-- **Injectivity of the integral `γ`** under the same hypotheses. -/
theorem gammaA_injective_of_isometry (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (B : K0Q k Γ →ₗ[RatFunc ℚ] K0Q k Γ →ₗ[RatFunc ℚ] RatFunc ℚ)
    (hB : ∀ x y : PreF (RatFunc ℚ) I, B (gammaQ k Γ x) (gammaQ k Γ y) = (KL.C Γ).form x y) :
    Function.Injective (gammaA k Γ hGK) := fun _ _ h =>
  Subtype.ext (gammaF_injective_of_isometry k Γ hGK B hB (congrArg Subtype.val h))

theorem gammaInt_injective_of_isometry (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (hinj : Function.Injective (toK0Q k Γ))
    (B : K0Q k Γ →ₗ[RatFunc ℚ] K0Q k Γ →ₗ[RatFunc ℚ] RatFunc ℚ)
    (hB : ∀ x y : PreF (RatFunc ℚ) I, B (gammaQ k Γ x) (gammaQ k Γ y) = (KL.C Γ).form x y) :
    Function.Injective (gammaInt k Γ hGK hinj) := fun _ _ h =>
  gammaA_injective_of_isometry k Γ hGK B hB
    ((K0RrangeEquiv k Γ hinj).symm.injective h)

end Injectivity

end Categorification.KLR.KLGamma

end
