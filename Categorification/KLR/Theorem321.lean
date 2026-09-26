/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Theorem11
import Categorification.Algebra.Graded.KrullSchmidtUnique

/-!
# KL I, Theorem 3.21: relations in `_𝒜 f` lift to isomorphisms

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, end of §3.2 (TeX lines ~2313–2346).

> For each divided power `i^{(a)}` we have the corresponding projective `P_{i^{(a)}}`. Induction
> with this projective is an exact functor, denoted `𝓕_i^{(a)}`, from `R(ν)-mod` to
> `R(ν + ai)-mod`. … This functor restricts to the subcategory `R-pmod` … To any divided power
> sequence `θ = i_1^{(a_1)} ⋯ i_r^{(a_r)}` associate the functor
> `𝓕_θ = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}` …
>
> **Theorem 3.21.** For any relation `∑_k u_k θ(k) = ∑_ℓ v_ℓ θ'(ℓ)` in `_𝒜 f` with positive
> coefficients `u_k, v_ℓ ∈ ℕ[q, q⁻¹]` there is an isomorphism of projectives
> `⊕_k P_{θ(k)}^{⊕ u_k} ≅ ⊕_ℓ P_{θ'(ℓ)}^{⊕ v_ℓ}` inducing an isomorphism of functors
> `⊕_k 𝓕_{θ(k)}^{⊕ u_k} ≅ ⊕_ℓ 𝓕_{θ'(ℓ)}^{⊕ v_ℓ}`.
>
> This result follows immediately from the earlier ones.

## Conventions

* **Side of induction.** The paper does not say on which side `P_{i^{(a)}}` is placed. We use
  `𝓕_i^{(a)} M = Ind (P_{i^{(a)}} ⊠ M)` (`funF`), so that `𝓕_θ = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘
  𝓕_{i_r}^{(a_r)}` acts on `K₀(R)` by *left* multiplication by `γ(θ)` (`of_funTheta`) and the
  theorem applies to the relation as printed. (With `Ind (M ⊠ P_{i^{(a)}})` the composite acts by
  right multiplication by `γ` of the *reversed* monomial, and one would additionally need the
  anti-involution of `_𝒜 f` fixing the `θ_i^{(a)}`.)
* **Coefficients in `ℕ[q, q⁻¹]`.** A sum `∑_k u_k θ(k)` with `u_k ∈ ℕ[q, q⁻¹]` is the same as a
  finite list of pairs `(n, θ)` (one entry `(n, θ(k))` for each monomial `q^n` of `u_k`, with
  multiplicity), standing for `∑ q^n θ`. We encode relations this way:
  `relSum Γ L = ∑_{(n, d) ∈ L} q^n θ_d ∈ _𝒜 f` (`q` acting as Lusztig's `v⁻¹`, as in
  `KLGamma.gammaIntEquiv_smul`), and `⊕_k P_{θ(k)}^{⊕ u_k}` is `⊕_{(n, d) ∈ L} P_d{n}`.
* **Weights.** The categories `R-pmod = ⊕_ν R(ν)-pmod` and `R-mod` split by weight, and so does
  any relation. We state everything one weight at a time: for every weight `μ`, the summands of
  weight `μ` on both sides are isomorphic (`sumP`, `sumF` keep exactly the monomials of weight
  `μ`). For a relation all of whose monomials have weight `μ` (the usual situation) no summand
  is dropped.
* **Functors on `R-pmod`.** `𝓕_θ` is formalized on finitely generated graded projective modules
  (`GProj`), where `Ind` is `GradingDatum.indProj`; the isomorphism is an isomorphism of objects
  for each `P` (`theorem_3_21`), obtained from Krull–Schmidt (`K0.of_eq_of_iff`). The version
  for arbitrary graded modules, with the natural isomorphism `Ind (X ⊠ −) ≅ Ind (X' ⊠ −)`
  induced by the isomorphism of projectives `X ≅ X'`, is in
  `Categorification.KLR.Theorem321Functor`.

## Hypotheses

As for Theorem 1.1, the quantum Gabber–Kac theorem `hGK : PreF.GabberKac (KL.C Γ).dot vQ
(KL.C Γ).c` is an explicit hypothesis: it is used to define `f`, `_𝒜 f` and `γ`.

## Main definitions and results

* `funF k Γ i a P = Ind (P_{i^{(a)}} ⊠ P)` and `funTheta k Γ d P = 𝓕_{i_1}^{(a_1)} (⋯
  (𝓕_{i_r}^{(a_r)} P))` for `d = i_1^{(a_1)} ⋯ i_r^{(a_r)}`;
  `of_funTheta : [𝓕_θ P] = γ(θ) [P]` in `K₀(R)`.
* `relSum Γ L = ∑_{(n, d) ∈ L} q^n θ_d ∈ _𝒜 f`; `gammaIntEquiv_relSum`.
* `sumP k Γ μ L = ⊕_{(n, d) ∈ L, |d| = μ} P_d{n}` and
  `sumF k Γ μ P L = ⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(P){n}`.
* **`theorem_3_21_proj`** : if `relSum Γ L = relSum Γ L'` then `sumP k Γ μ L ≅ sumP k Γ μ L'`
  for every weight `μ` (the isomorphism of projectives).
* **`theorem_3_21`** : if `relSum Γ L = relSum Γ L'` then
  `sumF k Γ μ P L ≅ sumF k Γ μ P L'` for every weight `μ` and every `P ∈ R(ν)-pmod` (the
  functors agree on `R-pmod`, up to isomorphism).
* `theorem_3_21_iff`, `theorem_3_21_proj_iff` : conversely, if the isomorphisms exist for every
  `μ` (for `P = R(0)` it suffices), then the relation holds in `_𝒜 f` (injectivity of `γ`).
-/

noncomputable section

namespace Categorification.KLR.KLGamma

open Graded LaurentPolynomial QuantumGroup KLRAlgebra

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-! ### Weights and casts -/

omit [DecidableEq I] in
/-- The weight `|d| = ∑ a_s i_s ∈ ℕ[I]` of a divided-power expression `d`. -/
abbrev wtDiv (d : List (I × ℕ)) : Multiset I := (expandDiv d : Multiset I)

omit [DecidableEq I] in
theorem wtDiv_cons (q : I × ℕ) (d : List (I × ℕ)) : wtDiv (q :: d) = wtDiv [q] + wtDiv d := by
  rw [show q :: d = [q] ++ d from rfl, wtDiv, expandDiv_append, ← Multiset.coe_add]

omit [DecidableEq I] in
theorem wtDiv_nil : wtDiv ([] : List (I × ℕ)) = 0 := rfl

variable {k Γ} in
/-- Transport of an object of `R(μ)-pmod` along an equality of weights `μ = μ'`. -/
def castProj {μ μ' : Multiset I} (h : μ = μ') (P : GProj ((Gkl).grade μ)) :
    GProj ((Gkl).grade μ') :=
  h ▸ P

theorem of_castProj {μ μ' : Multiset I} (h : μ = μ') (P : GProj ((Gkl).grade μ)) :
    DirectSum.of (Gkl).K0fam μ' (K0.of (castProj h P)) = DirectSum.of (Gkl).K0fam μ (K0.of P) := by
  subst h; rfl

/-! ### `[P_d]` in `K₀(R)`: unit and products -/

/-- `[P_∅] = 1` in `K₀(R)`. -/
theorem clsDiv_nil : clsDiv k Γ [] = 1 :=
  toK0Q_injective k Γ (by rw [toK0Q_clsDiv_nil, map_one])

/-- **`[P_{dd'}] = [P_d] [P_{d'}]`** in `K₀(R)` (from the `ℚ(v)`-statement and the
torsion-freeness of `K₀(R)`). -/
theorem clsDiv_append (d d' : List (I × ℕ)) :
    clsDiv k Γ (d ++ d') = clsDiv k Γ d * clsDiv k Γ d' :=
  toK0Q_injective k Γ (by rw [toK0Q_clsDiv_append, map_mul])

theorem clsDiv_cons (q : I × ℕ) (d : List (I × ℕ)) :
    clsDiv k Γ (q :: d) = clsDiv k Γ [q] * clsDiv k Γ d :=
  clsDiv_append k Γ [q] d

/-! ### The functors `𝓕_i^{(a)}` and `𝓕_θ` on `R-pmod` -/

/-- **`𝓕_i^{(a)} P = Ind (P_{i^{(a)}} ⊠ P)`**, from `R(ν)-pmod` to `R(ai + ν)-pmod`
(KL I §3.2, TeX line ~2316). -/
def funF (i : I) (a : ℕ) {ν : Multiset I} (P : GProj ((Gkl).grade ν)) :
    GProj ((Gkl).grade (wtDiv [(i, a)] + ν)) :=
  (Gkl).indProj (projDiv k Γ [(i, a)] rfl) P

/-- **`𝓕_θ = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}`** on `R-pmod`, for
`θ = d = i_1^{(a_1)} ⋯ i_r^{(a_r)}` (KL I §3.2, TeX lines ~2321–2324), from `R(ν)-pmod` to
`R(|d| + ν)-pmod`. -/
def funTheta : (d : List (I × ℕ)) → {ν : Multiset I} → GProj ((Gkl).grade ν) →
    GProj ((Gkl).grade (wtDiv d + ν))
  | [], _, P => castProj (by rw [wtDiv_nil, zero_add]) P
  | q :: d, _, P => castProj (by rw [wtDiv_cons q d, add_assoc]) (funF k Γ q.1 q.2 (funTheta d P))

/-- `[𝓕_i^{(a)} P] = [P_{i^{(a)}}] [P]` in `K₀(R)`. -/
theorem of_funF (i : I) (a : ℕ) {ν : Multiset I} (P : GProj ((Gkl).grade ν)) :
    DirectSum.of (Gkl).K0fam (wtDiv [(i, a)] + ν) (K0.of (funF k Γ i a P)) =
      clsDiv k Γ [(i, a)] * DirectSum.of (Gkl).K0fam ν (K0.of P) := by
  rw [funF, ← (Gkl).K0R_of_of_mul_of_of]
  rfl

/-- **`[𝓕_θ P] = γ(θ) [P]`** in `K₀(R)`: `𝓕_θ` acts on `K₀(R)` by left multiplication by
`[P_θ] = γ(θ)`. -/
theorem of_funTheta (d : List (I × ℕ)) {ν : Multiset I} (P : GProj ((Gkl).grade ν)) :
    DirectSum.of (Gkl).K0fam (wtDiv d + ν) (K0.of (funTheta k Γ d P)) =
      clsDiv k Γ d * DirectSum.of (Gkl).K0fam ν (K0.of P) := by
  induction d generalizing ν with
  | nil => rw [funTheta, of_castProj, clsDiv_nil, one_mul]
  | cons q d ih =>
    rw [funTheta, of_castProj, of_funF, ih, clsDiv_cons k Γ q d, mul_assoc]

/-! ### Relations in `_𝒜 f` -/

/-- The divided-power monomial `θ_d = θ_{i_1}^{(a_1)} ⋯ θ_{i_r}^{(a_r)}` as an element of
`_𝒜 f`. -/
def monoAf (d : List (I × ℕ)) : KL.Af Γ :=
  ⟨KL.π Γ (dpowMono Γ d), π_dpowMono_mem_Af Γ d⟩

/-- The action of `p ∈ ℤ[q, q⁻¹]` on `_𝒜 f` (`q` acting as `v⁻¹`, KL I §3.1). -/
def qsmulAf (p : LaurentPolynomial ℤ) (x : KL.Af Γ) : KL.Af Γ :=
  ⟨algebraMap (RatFunc ℚ) (KL.F Γ) (qToV p) * x,
    Subring.mul_mem _ (algebraMap_qToV_mem_Af Γ p) x.2⟩

/-- **`∑_{(n, d) ∈ L} q^n θ_d ∈ _𝒜 f`**: a `ℕ[q, q⁻¹]`-linear combination of divided-power
monomials (one entry per monomial `q^n` of a coefficient, with multiplicity). -/
def relSum (L : List (ℤ × List (I × ℕ))) : KL.Af Γ :=
  (L.map fun x => qsmulAf Γ (T x.1) (monoAf Γ x.2)).sum

/-- `∑_{(n, d) ∈ L} q^n [P_d] ∈ K₀(R)`. -/
def clsSum (L : List (ℤ × List (I × ℕ))) : (Gkl).K0R :=
  (L.map fun x => (T x.1 : LaurentPolynomial ℤ) • clsDiv k Γ x.2).sum

theorem relSum_cons (x : ℤ × List (I × ℕ)) (L : List (ℤ × List (I × ℕ))) :
    relSum Γ (x :: L) = qsmulAf Γ (T x.1) (monoAf Γ x.2) + relSum Γ L := by
  rw [relSum, List.map_cons, List.sum_cons, ← relSum]

theorem clsSum_nil : clsSum k Γ [] = 0 := rfl

theorem clsSum_cons (x : ℤ × List (I × ℕ)) (L : List (ℤ × List (I × ℕ))) :
    clsSum k Γ (x :: L) = (T x.1 : LaurentPolynomial ℤ) • clsDiv k Γ x.2 + clsSum k Γ L := by
  rw [clsSum, List.map_cons, List.sum_cons, ← clsSum]

/-- `γ(∑ q^n θ_d) = ∑ q^n [P_d]`. -/
theorem gammaIntEquiv_relSum (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (L : List (ℤ × List (I × ℕ))) :
    gammaIntEquiv k Γ hGK (relSum Γ L) = clsSum k Γ L := by
  induction L with
  | nil => rw [clsSum_nil, relSum, List.map_nil, List.sum_nil, map_zero]
  | cons x L ih =>
    rw [relSum_cons, clsSum_cons, map_add, ih, qsmulAf, gammaIntEquiv_smul, monoAf,
      gammaIntEquiv_dpowMono]

/-- The relation `∑ q^n θ_d = ∑ q^{n'} θ_{d'}` in `_𝒜 f` is equivalent to the equality of the
corresponding classes in `K₀(R)` (KL I, Theorem 1.1). -/
theorem relSum_eq_iff (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (L L' : List (ℤ × List (I × ℕ))) :
    relSum Γ L = relSum Γ L' ↔ clsSum k Γ L = clsSum k Γ L' := by
  rw [← gammaIntEquiv_relSum k Γ hGK, ← gammaIntEquiv_relSum k Γ hGK]
  exact (gammaIntEquiv k Γ hGK).injective.eq_iff.symm

/-! ### The weight-`μ` parts -/

theorem projK0R_clsDiv_of_eq {μ : Multiset I} (d : List (I × ℕ)) (h : wtDiv d = μ) :
    projK0R k Γ μ (clsDiv k Γ d) = DirectSum.of (Gkl).K0fam μ (K0.of (projDiv k Γ d h)) := by
  rw [clsDiv_eq k Γ d h, projK0R, LinearMap.comp_apply,
    ← DirectSum.lof_eq_of (LaurentPolynomial ℤ), DirectSum.component.lof_self]

theorem projK0R_clsDiv_of_ne {μ : Multiset I} (d : List (I × ℕ)) (h : ¬ wtDiv d = μ) :
    projK0R k Γ μ (clsDiv k Γ d) = 0 := by
  rw [clsDiv, projK0R, LinearMap.comp_apply, ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
    DirectSum.component.of, dif_neg h, map_zero]

/-- **`⊕_{(n, d) ∈ L, |d| = μ} P_d{n}`**, the weight-`μ` part of `⊕_k P_{θ(k)}^{⊕ u_k}`, an
object of `R(μ)-pmod`. -/
def sumP (μ : Multiset I) : List (ℤ × List (I × ℕ)) → GProj ((Gkl).grade μ)
  | [] => GProj.zeroObj _
  | x :: L =>
    if h : wtDiv x.2 = μ then ((projDiv k Γ x.2 h).shift x.1).prod (sumP μ L) else sumP μ L

/-- **`⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(P){n}`**, the weight-`(μ + ν)` part of
`⊕_k 𝓕_{θ(k)}^{⊕ u_k}` applied to `P ∈ R(ν)-pmod`. -/
def sumF (μ : Multiset I) {ν : Multiset I} (P : GProj ((Gkl).grade ν)) :
    List (ℤ × List (I × ℕ)) → GProj ((Gkl).grade (μ + ν))
  | [] => GProj.zeroObj _
  | x :: L =>
    if h : wtDiv x.2 = μ then
      ((castProj (by rw [h]) (funTheta k Γ x.2 P)).shift x.1).prod (sumF μ P L)
    else sumF μ P L

theorem of_zeroObj (μ : Multiset I) :
    DirectSum.of (Gkl).K0fam μ (K0.of (GProj.zeroObj ((Gkl).grade μ))) = 0 := by
  rw [K0.of_eq_zero_of_subsingleton, map_zero]

/-- `[sumP μ L]` is the weight-`μ` component of `∑ q^n [P_d]`. -/
theorem of_sumP (μ : Multiset I) (L : List (ℤ × List (I × ℕ))) :
    DirectSum.of (Gkl).K0fam μ (K0.of (sumP k Γ μ L)) = projK0R k Γ μ (clsSum k Γ L) := by
  induction L with
  | nil => rw [sumP, of_zeroObj, clsSum_nil, map_zero]
  | cons x L ih =>
    rw [clsSum_cons, map_add, map_smul, sumP]
    by_cases h : wtDiv x.2 = μ
    · rw [dif_pos h, K0.of_prod, map_add, ih, ← K0.T_smul_of, K0R_of_smul,
        projK0R_clsDiv_of_eq k Γ x.2 h]
    · rw [dif_neg h, ih, projK0R_clsDiv_of_ne k Γ x.2 h, smul_zero, zero_add]

/-- `[sumF μ P L]` is (the weight-`μ` component of `∑ q^n [P_d]`) times `[P]`. -/
theorem of_sumF (μ : Multiset I) {ν : Multiset I} (P : GProj ((Gkl).grade ν))
    (L : List (ℤ × List (I × ℕ))) :
    DirectSum.of (Gkl).K0fam (μ + ν) (K0.of (sumF k Γ μ P L)) =
      projK0R k Γ μ (clsSum k Γ L) * DirectSum.of (Gkl).K0fam ν (K0.of P) := by
  induction L with
  | nil => rw [sumF, of_zeroObj, clsSum_nil, map_zero, zero_mul]
  | cons x L ih =>
    rw [clsSum_cons, map_add, map_smul, add_mul, sumF]
    by_cases h : wtDiv x.2 = μ
    · rw [dif_pos h, K0.of_prod, map_add, ih, ← K0.T_smul_of, K0R_of_smul, of_castProj,
        of_funTheta, projK0R_clsDiv_of_eq k Γ x.2 h, ← clsDiv_eq k Γ x.2 h, smul_mul_assoc]
    · rw [dif_neg h, ih, projK0R_clsDiv_of_ne k Γ x.2 h, smul_zero, zero_mul, zero_add]

/-! ### Theorem 3.21 -/

/-- **KL I, Theorem 3.21 (isomorphism of projectives)**: for any relation
`∑_{(n, d) ∈ L} q^n θ_d = ∑_{(n', d') ∈ L'} q^{n'} θ_{d'}` in `_𝒜 f` (coefficients in
`ℕ[q, q⁻¹]`), and every weight `μ`,
`⊕_{(n, d) ∈ L, |d| = μ} P_d{n} ≅ ⊕_{(n', d') ∈ L', |d'| = μ} P_{d'}{n'}` in `R(μ)-pmod`. -/
theorem theorem_3_21_proj (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I) :
    Nonempty ((sumP k Γ μ L).Iso (sumP k Γ μ L')) := by
  refine K0.of_eq_of_iff.1 (DirectSum.of_injective (β := (Gkl).K0fam) μ ?_)
  rw [of_sumP, of_sumP, (relSum_eq_iff k Γ hGK L L').1 hrel]

/-- **KL I, Theorem 3.21 (isomorphism of functors, on `R-pmod`)**: for any relation
`∑_{(n, d) ∈ L} q^n θ_d = ∑_{(n', d') ∈ L'} q^{n'} θ_{d'}` in `_𝒜 f` (coefficients in
`ℕ[q, q⁻¹]`), every weight `μ` and every finitely generated graded projective `R(ν)`-module `P`,
`⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(P){n} ≅ ⊕_{(n', d') ∈ L', |d'| = μ} 𝓕_{d'}(P){n'}`
in `R(μ + ν)-pmod`, where `𝓕_d = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}`. -/
theorem theorem_3_21 (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I)
    {ν : Multiset I} (P : GProj ((Gkl).grade ν)) :
    Nonempty ((sumF k Γ μ P L).Iso (sumF k Γ μ P L')) := by
  refine K0.of_eq_of_iff.1 (DirectSum.of_injective (β := (Gkl).K0fam) (μ + ν) ?_)
  rw [of_sumF, of_sumF, (relSum_eq_iff k Γ hGK L L').1 hrel]

/-- An element of `K₀(R)` is determined by its weight components. -/
theorem eq_of_forall_projK0R_eq {x y : (Gkl).K0R} (h : ∀ μ, projK0R k Γ μ x = projK0R k Γ μ y) :
    x = y := by
  refine DFunLike.ext x y fun μ => ?_
  have := congrArg (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) (Gkl).K0fam μ) (h μ)
  simp only [projK0R, LinearMap.comp_apply, DirectSum.component.lof_self] at this
  exact this

/-- **Converse of Theorem 3.21 for projectives**: `∑ q^n θ_d = ∑ q^{n'} θ_{d'}` in `_𝒜 f` iff
the weight-`μ` parts `⊕ P_d{n}` and `⊕ P_{d'}{n'}` are isomorphic for every `μ`. -/
theorem theorem_3_21_proj_iff (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (L L' : List (ℤ × List (I × ℕ))) :
    relSum Γ L = relSum Γ L' ↔ ∀ μ, Nonempty ((sumP k Γ μ L).Iso (sumP k Γ μ L')) := by
  refine ⟨fun h μ => theorem_3_21_proj k Γ hGK h μ, fun h => ?_⟩
  rw [relSum_eq_iff k Γ hGK]
  refine eq_of_forall_projK0R_eq k Γ fun μ => ?_
  rw [← of_sumP, ← of_sumP, K0.of_eq_of_iso (h μ).some]

/-- **Converse of Theorem 3.21 for the functors**: if `⊕ 𝓕_d(R(0)){n} ≅ ⊕ 𝓕_{d'}(R(0)){n'}`
weight by weight, then `∑ q^n θ_d = ∑ q^{n'} θ_{d'}` in `_𝒜 f`; so the relation holds iff the
functors agree on every `P ∈ R-pmod` (up to isomorphism). -/
theorem theorem_3_21_iff (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    (L L' : List (ℤ × List (I × ℕ))) :
    relSum Γ L = relSum Γ L' ↔
      ∀ (μ ν : Multiset I) (P : GProj ((Gkl).grade ν)),
        Nonempty ((sumF k Γ μ P L).Iso (sumF k Γ μ P L')) := by
  refine ⟨fun h μ ν P => theorem_3_21 k Γ hGK h μ P, fun h => ?_⟩
  rw [relSum_eq_iff k Γ hGK]
  refine eq_of_forall_projK0R_eq k Γ fun μ => ?_
  have e := (of_sumF k Γ μ (GProj.regular ((Gkl).grade 0)) L).symm.trans
    ((congrArg (DirectSum.of (Gkl).K0fam (μ + 0))
      (K0.of_eq_of_iso (h μ 0 (GProj.regular _)).some)).trans
      (of_sumF k Γ μ (GProj.regular ((Gkl).grade 0)) L'))
  rwa [← (Gkl).K0R_one, mul_one, mul_one] at e

end Categorification.KLR.KLGamma
