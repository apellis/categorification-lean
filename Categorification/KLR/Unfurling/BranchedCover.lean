/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Cover
import Categorification.KLR.KL2.Datum
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The unfurled graph as a branched cover

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §2 (definition
with label `def:tilde-I`) and §3.3 (equation with label `eq:factorize` and the factorization of
`P_{ij}(ϖ_{u,i}(x), ϖ_{u',j}(y))` after it). The number of arrows between two labels of the
unfurled graph is an order of vanishing; Webster remarks before `def:tilde-I` that, by
homogeneity, it equals the order of vanishing in either variable alone. For the factorization
field of `UnfurlingDatum` this holds over any field and for any datum
(`arrows_eq_rootMultiplicity_fst`, `arrows_eq_rootMultiplicity_snd`): set one variable of
`P(ϖ_j(x), ϖ_{j'}(y)) = (x - y)^n P°(x, y)` to `0` and use that `ϖ_j` has nonzero linear
coefficient.

The arrows of `UnfurlingDatum` count the factors `x - y` of `P_{ij}` after substitution, as in
§3.3. The printed definition `def:tilde-I` uses the order of vanishing of `Q_{ij}` instead; since
`Q_{ij}(x, y) = P_{ij}(x, y) P_{ji}(y, x)`, that count would make `n_{ab} + n_{ba}` twice the
value below, and the identity would read `-2 a_{ij}`. We follow §3.3.

Two consequences, both used but not stated separately by Webster (proofs reconstructed):

* **Branched-cover identity.** For a label `b` over `j` with spectral value `w ≠ 0` and the
  labels `a` over `i ≠ j`, `n_{ab} + n_{ba}` is the multiplicity of `ϖ_a(0)` as a root of
  `Q_{ij}(·, w)`. Over an algebraically closed field, and when the spectra over `i` are
  complete at `b` (Webster's completeness condition in `def:tilde-I`), these numbers sum to the
  degree of `Q_{ij}(·, w)`, which is `-a_{ij}` for KLR polynomials with nonzero extremal
  coefficients. This is the count behind the homomorphism with label
  `eq:furling-homomorphism` (`E_i ↦ ∑_u E_{i,u}`): the colour-`i` weight of `g` restricted
  from `g̃` shifts by `-a_{ij}` along an `E_j`.
* **Splitting.** If the `P_{ij}` are defined over a subfield `K` that is algebraically closed in
  `L`, no arrow joins a label with spectral value in `K` to one with spectral value outside `K`.

## Main results

* `UnfurlingDatum.arrows_eq_rootMultiplicity_fst`, `UnfurlingDatum.arrows_eq_rootMultiplicity_snd`
  : arrows as root multiplicities of `P_{π j', π j}` in one variable.
* `UnfurlingDatum.arrows_add_arrows_eq_rootMultiplicity` : `n_{ab} + n_{ba}` as a root
  multiplicity of `Q_{π a, π b}(·, ϖ_b(0))`.
* `UnfurlingDatum.finsum_arrows_eq_of_complete` : the branched-cover identity for complete
  spectra.
* `UnfurlingDatum.ofClosure_finsum_arrows`, `UnfurlingDatum.ofClosure_finsum_arrows_eq_dij` :
  the identity on the full closure `Σ i, L ∖ {0}`, with sum `d_{ij} = -a_{ij}`.
* `UnfurlingDatum.arrows_eq_zero_of_isIntegrallyClosedIn` : the splitting.
-/

open MvPolynomial

namespace Categorification.KLR.Unfurling

variable {L : Type*} [Field L]

/-- If `q(0) ≠ 0`, then `0` is a root of `X^n q` of multiplicity exactly `n`. -/
theorem rootMultiplicity_zero_X_pow_mul {n : ℕ} {q : Polynomial L} (hq : q.eval 0 ≠ 0) :
    (Polynomial.X ^ n * q).rootMultiplicity 0 = n := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (a := (0 : L)) (n := n) hq0
  rwa [map_zero, sub_zero, Polynomial.rootMultiplicity_eq_zero hq, zero_add, mul_comm] at this

/-- Composing with a polynomial `φ` with `φ'(0) ≠ 0` moves a root `φ(0)` of `g` to the root `0`
of `g ∘ φ`, with the same multiplicity. -/
theorem rootMultiplicity_zero_comp (g φ : Polynomial L) (hφ : φ.coeff 1 ≠ 0) :
    (g.comp φ).rootMultiplicity 0 = g.rootMultiplicity (φ.coeff 0) := by
  by_cases hg : g = 0
  · subst hg; simp
  set c := φ.coeff 0 with hc
  set m := g.rootMultiplicity c
  have hgh : (Polynomial.X - Polynomial.C c) ^ m * (g /ₘ (Polynomial.X - Polynomial.C c) ^ m) =
      g := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq g c
  have hh : (g /ₘ (Polynomial.X - Polynomial.C c) ^ m).eval c ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hg
  have hφ' : φ - Polynomial.C c = Polynomial.X * φ.divX := by
    nth_rewrite 1 [← Polynomial.divX_mul_X_add φ]
    rw [← hc]; ring
  rw [← hgh, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.C_comp, hφ', mul_pow, mul_assoc]
  apply rootMultiplicity_zero_X_pow_mul
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_comp,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX,
    ← Polynomial.coeff_zero_eq_eval_zero, ← hc]
  exact mul_ne_zero (pow_ne_zero _ hφ) hh

/-- Over an algebraically closed field, the root multiplicities of a nonzero polynomial `q`,
read through an injective map `c : ι → L` whose image contains every root of `q`, have finite
support and sum to the degree of `q`. -/
theorem finsum_rootMultiplicity_eq_natDegree [IsAlgClosed L] {ι : Type*} {c : ι → L}
    (hc : Function.Injective c) {q : Polynomial L} (hq : q ≠ 0)
    (hroots : ∀ u, q.IsRoot u → u ∈ Set.range c) :
    (Function.support fun a => q.rootMultiplicity (c a)).Finite ∧
      ∑ᶠ a, q.rootMultiplicity (c a) = q.natDegree := by
  classical
  have hsupp : ∀ x, q.rootMultiplicity x ≠ 0 → x ∈ q.roots.toFinset := fun x hx => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact (Polynomial.rootMultiplicity_pos hq).1 (Nat.pos_of_ne_zero hx)
  refine ⟨(q.roots.toFinset.finite_toSet.preimage hc.injOn).subset fun a ha => hsupp _ ha, ?_⟩
  rw [← finsum_mem_range hc (f := fun x => q.rootMultiplicity x),
    finsum_mem_eq_sum_of_subset _ (t := q.roots.toFinset) (fun x hx => hsupp x hx.2)
      (fun x hx => hroots x ((Polynomial.mem_roots hq).1 (Multiset.mem_toFinset.1 hx)))]
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree]

/-- The coefficients of `Q(t, w)` as a polynomial in `t`. -/
theorem coeff_aeval_X_C (Q : MvPolynomial (Fin 2) L) (w : L) (p : ℕ) :
    (aeval ![Polynomial.X, Polynomial.C w] Q).coeff p =
      ∑ d ∈ Q.support, if d 0 = p then Q.coeff d * w ^ d 1 else 0 := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← Polynomial.C_pow, mul_comm (Polynomial.X ^ _),
    ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

private theorem weight_fin_two' (w : Fin 2 → ℕ) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight w d = d 0 * w 0 + d 1 * w 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simp [smul_eq_mul]

/-- **Degree and constant term of `Q(t, w)`.** If `Q` is weighted homogeneous for positive
weights `(e₁, e₂)` with nonzero coefficients at `u^m` and at `v^{m'}`, and `w ≠ 0`, then
`t ↦ Q(t, w)` has degree `m` and does not vanish at `t = 0`. -/
theorem natDegree_aeval_X_C_and_eval_zero {Q : MvPolynomial (Fin 2) L} {e₁ e₂ N : ℕ}
    (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hhom : Q.IsWeightedHomogeneous ![e₁, e₂] N) {m m' : ℕ}
    (hm : Q.coeff (Finsupp.single 0 m) ≠ 0) (hm' : Q.coeff (Finsupp.single 1 m') ≠ 0)
    {w : L} (hw : w ≠ 0) :
    (aeval ![Polynomial.X, Polynomial.C w] Q).natDegree = m ∧
      (aeval ![Polynomial.X, Polynomial.C w] Q).eval 0 ≠ 0 := by
  have hD : ∀ d ∈ Q.support, d 0 * e₁ + d 1 * e₂ = N := fun d hd => by
    have := hhom (mem_support_iff.mp hd)
    rwa [weight_fin_two'] at this
  have hmN : m * e₁ = N := by
    have := hD _ (mem_support_iff.mpr hm); simpa using this
  have hm'N : m' * e₂ = N := by
    have := hD _ (mem_support_iff.mpr hm'); simpa using this
  set q := aeval ![Polynomial.X, Polynomial.C w] Q
  have hlead : q.coeff m = Q.coeff (Finsupp.single 0 m) := by
    rw [coeff_aeval_X_C, Finset.sum_eq_single (Finsupp.single 0 m)]
    · simp
    · intro d hd hne
      rw [ite_eq_right_iff]
      intro h0
      exfalso
      apply hne
      have h1 : d 1 = 0 := by
        have := hD d hd
        rw [h0, hmN.symm] at this
        exact (Nat.mul_eq_zero.mp (by omega)).resolve_right he₂.ne'
      ext x; fin_cases x <;> simp [h0, h1]
    · intro h; exact absurd (mem_support_iff.mpr hm) h
  have hconst : q.coeff 0 = Q.coeff (Finsupp.single 1 m') * w ^ m' := by
    rw [coeff_aeval_X_C, Finset.sum_eq_single (Finsupp.single 1 m')]
    · simp
    · intro d hd hne
      rw [ite_eq_right_iff]
      intro h0
      exfalso
      apply hne
      have h1 : d 1 = m' := by
        have := hD d hd
        rw [h0, ← hm'N] at this
        exact Nat.eq_of_mul_eq_mul_right he₂ (by omega)
      ext x; fin_cases x <;> simp [h0, h1]
    · intro h; exact absurd (mem_support_iff.mpr hm') h
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun p hp => ?_
    rw [coeff_aeval_X_C]
    refine Finset.sum_eq_zero fun d hd => ite_eq_right_iff.mpr fun h0 => absurd ?_ hp.not_ge
    have := hD d hd
    rw [h0, ← hmN] at this
    exact Nat.le_of_mul_le_mul_right (by omega) he₁
  · exact Polynomial.le_natDegree_of_ne_zero (by rw [hlead]; exact hm)
  · rw [← Polynomial.coeff_zero_eq_eval_zero, hconst]
    exact mul_ne_zero hm' (pow_ne_zero _ hw)

private theorem mapDomain_swap_apply (d : Fin 2 →₀ ℕ) :
    (Finsupp.mapDomain ![(1 : Fin 2), 0] d) 0 = d 1 ∧
      (Finsupp.mapDomain ![(1 : Fin 2), 0] d) 1 = d 0 := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  exact ⟨by simpa using Finsupp.mapDomain_apply_of_injective hinj d 1,
    by simpa using Finsupp.mapDomain_apply_of_injective hinj d 0⟩

private theorem mapDomain_swap_swap (d : Fin 2 →₀ ℕ) :
    Finsupp.mapDomain ![(1 : Fin 2), 0] (Finsupp.mapDomain ![(1 : Fin 2), 0] d) = d := by
  rw [← Finsupp.mapDomain_comp]
  have : (![(1 : Fin 2), 0] ∘ ![(1 : Fin 2), 0]) = id := by funext x; fin_cases x <;> rfl
  rw [this, Finsupp.mapDomain_id]

/-- Exchanging the variables exchanges the weights. -/
theorem isWeightedHomogeneous_rename_swap {F : MvPolynomial (Fin 2) L} {e₁ e₂ N : ℕ}
    (h : F.IsWeightedHomogeneous ![e₂, e₁] N) :
    (rename (![1, 0] : Fin 2 → Fin 2) F).IsWeightedHomogeneous ![e₁, e₂] N := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  intro d hd
  rw [← mapDomain_swap_swap d, coeff_rename_mapDomain _ hinj] at hd
  have := h hd
  rw [weight_fin_two'] at this ⊢
  obtain ⟨h0, h1⟩ := mapDomain_swap_apply d
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
  rw [h0, h1] at this
  omega

/-- The coefficient of `u^n` after exchanging the variables is the coefficient of `v^n`. -/
theorem coeff_rename_swap_single_zero (F : MvPolynomial (Fin 2) L) (n : ℕ) :
    (rename (![1, 0] : Fin 2 → Fin 2) F).coeff (Finsupp.single 0 n) =
      F.coeff (Finsupp.single 1 n) := by
  have hinj : Function.Injective (![1, 0] : Fin 2 → Fin 2) := by decide
  have := coeff_rename_mapDomain (![1, 0] : Fin 2 → Fin 2) hinj F (Finsupp.single 1 n)
  rw [Finsupp.mapDomain_single] at this
  exact this

namespace UnfurlingDatum

variable {I J : Type*} {P : I → I → MvPolynomial (Fin 2) L} (D : UnfurlingDatum L P J)

omit [Field L] in
private theorem algHom_aeval {A B : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring L]
    [Algebra L A] [Algebra L B] (Φ : A →ₐ[L] B) (v : Fin 2 → A) (F : MvPolynomial (Fin 2) L) :
    Φ (aeval v F) = aeval (fun i => Φ (v i)) F := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- The constant term of `F(x, 0)` is the constant term of `F`. -/
private theorem eval_zero_aeval_X_zero (G : MvPolynomial (Fin 2) L) (v : Fin 2 → Polynomial L)
    (hv : ∀ i, (v i).eval 0 = 0) : (aeval v G).eval 0 = constantCoeff G := by
  have := algHom_aeval (Polynomial.aeval (0 : L)) v G
  rw [Polynomial.coe_aeval_eq_eval] at this
  rw [this]
  simp only [hv]
  rw [show (fun _ : Fin 2 => (0 : L)) = 0 from rfl, MvPolynomial.aeval_zero]
  rfl

/-- **Arrows as root multiplicities, first variable.** For `π j ≠ π j'`, the number of arrows
`j → j'` is the multiplicity of `ϖ_j(0)` as a root of `t ↦ P_{π j', π j}(t, ϖ_{j'}(0))`
(Webster, arXiv:1603.06311v3, §2, remark before the definition with label `def:tilde-I`: the
order of vanishing at `(u, u')` equals that of `x ↦ P(x, u')` at `x = u`; proof reconstructed:
set `y = 0` in the factorization of §3.3). -/
theorem arrows_eq_rootMultiplicity_fst {j j' : J} (h : D.π j ≠ D.π j') :
    D.arrows j j' = (aeval ![Polynomial.X, Polynomial.C ((D.pw j').coeff 0)]
      (P (D.π j') (D.π j))).rootMultiplicity ((D.pw j).coeff 0) := by
  let Φ : MvPolynomial (Fin 2) L →ₐ[L] Polynomial L := aeval ![Polynomial.X, 0]
  have hf := congrArg Φ (D.factor j j' h)
  have hL : Φ (aeval ![Polynomial.aeval (X 0) (D.pw j), Polynomial.aeval (X 1) (D.pw j')]
      (P (D.π j') (D.π j))) = (aeval ![Polynomial.X, Polynomial.C ((D.pw j').coeff 0)]
        (P (D.π j') (D.π j))).comp (D.pw j) := by
    rw [Polynomial.comp_eq_aeval, algHom_aeval, algHom_aeval]
    refine congrArg (fun v => aeval v _) (funext fun i => ?_)
    fin_cases i
    · simp [Φ, ← Polynomial.aeval_algHom_apply]
    · simp [Φ, ← Polynomial.aeval_algHom_apply, ← Polynomial.coeff_zero_eq_aeval_zero']
  rw [hL, map_mul, map_pow, map_sub] at hf
  simp only [Φ, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero] at hf
  rw [← rootMultiplicity_zero_comp _ _ (D.pw_coeff_one j), hf,
    rootMultiplicity_zero_X_pow_mul]
  rw [eval_zero_aeval_X_zero]
  · exact D.unit_constantCoeff j j' h
  · intro i; fin_cases i <;> simp

/-- **Arrows as root multiplicities, second variable.** For `π j ≠ π j'`, the number of arrows
`j → j'` is the multiplicity of `ϖ_{j'}(0)` as a root of `t ↦ P_{π j', π j}(ϖ_j(0), t)`
(Webster, arXiv:1603.06311v3, §2, remark before the definition with label `def:tilde-I`: the
order of vanishing at `(u, u')` equals that of `y ↦ P(u, y)` at `y = u'`; proof reconstructed:
set `x = 0` in the factorization of §3.3). -/
theorem arrows_eq_rootMultiplicity_snd {j j' : J} (h : D.π j ≠ D.π j') :
    D.arrows j j' = (aeval ![Polynomial.C ((D.pw j).coeff 0), Polynomial.X]
      (P (D.π j') (D.π j))).rootMultiplicity ((D.pw j').coeff 0) := by
  let Φ : MvPolynomial (Fin 2) L →ₐ[L] Polynomial L := aeval ![0, Polynomial.X]
  have hf := congrArg Φ (D.factor j j' h)
  have hL : Φ (aeval ![Polynomial.aeval (X 0) (D.pw j), Polynomial.aeval (X 1) (D.pw j')]
      (P (D.π j') (D.π j))) = (aeval ![Polynomial.C ((D.pw j).coeff 0), Polynomial.X]
        (P (D.π j') (D.π j))).comp (D.pw j') := by
    rw [Polynomial.comp_eq_aeval, algHom_aeval, algHom_aeval]
    refine congrArg (fun v => aeval v _) (funext fun i => ?_)
    fin_cases i
    · simp [Φ, ← Polynomial.aeval_algHom_apply, ← Polynomial.coeff_zero_eq_aeval_zero']
    · simp [Φ, ← Polynomial.aeval_algHom_apply]
  rw [hL, map_mul, map_pow, map_sub] at hf
  simp only [Φ, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub] at hf
  rw [neg_pow, mul_comm _ (Polynomial.X ^ _), mul_assoc] at hf
  rw [← rootMultiplicity_zero_comp _ _ (D.pw_coeff_one j'), hf,
    rootMultiplicity_zero_X_pow_mul]
  rw [Polynomial.eval_mul, eval_zero_aeval_X_zero]
  · exact mul_ne_zero (by simp) (D.unit_constantCoeff j j' h)
  · intro i; fin_cases i <;> simp

/-! ### Splitting along an algebraically closed subfield -/

omit [Field L] in
/-- A root of the base change of a nonzero polynomial over `K` is integral over `K`; if `K` is
integrally closed in `L`, it lies in `K`. -/
private theorem mem_range_of_rootMultiplicity_pos {K : Type*} [Field K] [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {p : Polynomial K} {w : L}
    (h : 0 < (p.map (algebraMap K L)).rootMultiplicity w) : w ∈ Set.range (algebraMap K L) := by
  have hp : p.map (algebraMap K L) ≠ 0 := by
    rintro h0; rw [h0, Polynomial.rootMultiplicity_zero] at h; exact lt_irrefl _ h
  have hroot := (Polynomial.rootMultiplicity_pos hp).1 h
  have halg : IsAlgebraic K w := ⟨p, fun h0 => hp (by rw [h0, Polynomial.map_zero]), by
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]⟩
  exact IsIntegrallyClosedIn.isIntegral_iff.mp halg.isIntegral

omit [Field L] in
/-- Base change commutes with substituting polynomials for the variables. -/
private theorem aeval_map_eq_map_aeval {K : Type*} [Field K] [Field L] [Algebra K L]
    (F₀ : MvPolynomial (Fin 2) K) (v : Fin 2 → Polynomial K) :
    aeval (fun i => (v i).map (algebraMap K L)) (MvPolynomial.map (algebraMap K L) F₀) =
      (aeval v F₀).map (algebraMap K L) := by
  rw [MvPolynomial.aeval_map_algebraMap]
  simpa [Polynomial.mapAlg_eq_map] using (algHom_aeval (Polynomial.mapAlg K L) v F₀).symm

/-- **Splitting of the unfurled graph** (Webster, arXiv:1603.06311v3, §2, definition with label
`def:tilde-I`, and §3.3; not stated there, proof reconstructed). Let the `P_{ij}` be defined over a subfield `K` of `L` that is
integrally (equivalently, algebraically) closed in `L`, for instance the algebraic closure in `L`
of a field of rational functions. Then there are no arrows, in either direction, between a label
whose spectral value `ϖ_a(0)` lies in `K` and a label whose spectral value does not. -/
theorem arrows_eq_zero_of_isIntegrallyClosedIn {K : Type*} [Field K] [Algebra K L]
    [IsIntegrallyClosedIn K L] {P₀ : I → I → MvPolynomial (Fin 2) K}
    (D : UnfurlingDatum L (fun i i' => MvPolynomial.map (algebraMap K L) (P₀ i i')) J)
    {a b : J} (ha : (D.pw a).coeff 0 ∈ Set.range (algebraMap K L))
    (hb : (D.pw b).coeff 0 ∉ Set.range (algebraMap K L)) :
    D.arrows a b = 0 ∧ D.arrows b a = 0 := by
  by_cases hπ : D.π a = D.π b
  · exact ⟨D.arrows_of_eq a b hπ, D.arrows_of_eq b a hπ.symm⟩
  obtain ⟨u, hu⟩ := ha
  constructor
  · rw [D.arrows_eq_rootMultiplicity_snd hπ, ← hu]
    by_contra h0
    apply hb
    refine mem_range_of_rootMultiplicity_pos (p := aeval ![Polynomial.C u, Polynomial.X]
      (P₀ (D.π b) (D.π a))) ?_
    rw [← aeval_map_eq_map_aeval]
    convert Nat.pos_of_ne_zero h0 using 4
    funext i; fin_cases i <;> simp
  · rw [D.arrows_eq_rootMultiplicity_fst (Ne.symm hπ), ← hu]
    by_contra h0
    apply hb
    refine mem_range_of_rootMultiplicity_pos (p := aeval ![Polynomial.X, Polynomial.C u]
      (P₀ (D.π a) (D.π b))) ?_
    rw [← aeval_map_eq_map_aeval]
    convert Nat.pos_of_ne_zero h0 using 4
    funext i; fin_cases i <;> simp

/-! ### The branched-cover identity -/

/-- `Q(t, w)` evaluated at `t = u` is `Q(u, w)`. -/
private theorem eval_aeval_X_C (Q : MvPolynomial (Fin 2) L) (u w : L) :
    (aeval ![Polynomial.X, Polynomial.C w] Q).eval u = aeval ![u, w] Q := by
  have := algHom_aeval (Polynomial.aeval u) ![Polynomial.X, Polynomial.C w] Q
  rw [Polynomial.coe_aeval_eq_eval] at this
  rw [this]
  refine congrArg (fun v => aeval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

/-- **Arrows in both directions as one root multiplicity.** For labels `a`, `b` over different
vertices, with spectral values `u = ϖ_a(0)`, `w = ϖ_b(0)`: if `Q(t, w)` is not identically zero,
where `Q(x, y) = P_{π b, π a}(x, y) P_{π a, π b}(y, x)` (the KLR polynomial `Q_{π a, π b}`, first
variable on the `π a`-strand), then `n_{ab} + n_{ba}` is the multiplicity of `u` as a root of
`t ↦ Q(t, w)` (Webster, arXiv:1603.06311v3, §2, definition with label `def:tilde-I`, and §3.3,
the factorization of `Q_{ij}` after equation `eq:factorize`; proof reconstructed). -/
theorem arrows_add_arrows_eq_rootMultiplicity {a b : J} (hab : D.π a ≠ D.π b)
    {Q : MvPolynomial (Fin 2) L} (hQ : Q = P (D.π b) (D.π a) * rename ![1, 0] (P (D.π a) (D.π b)))
    (hQ0 : aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] Q ≠ 0) :
    D.arrows a b + D.arrows b a =
      (aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] Q).rootMultiplicity
        ((D.pw a).coeff 0) := by
  rw [D.arrows_eq_rootMultiplicity_fst hab, D.arrows_eq_rootMultiplicity_snd (Ne.symm hab)]
  have hmul : aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] Q =
      aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] (P (D.π b) (D.π a)) *
        aeval ![Polynomial.C ((D.pw b).coeff 0), Polynomial.X] (P (D.π a) (D.π b)) := by
    rw [hQ, map_mul, aeval_rename]
    refine congrArg (_ * ·) (congrArg (fun v => aeval v _) (funext fun i => ?_))
    fin_cases i <;> rfl
  rw [hmul] at hQ0 ⊢
  rw [Polynomial.rootMultiplicity_mul hQ0]

/-- **The branched-cover identity for complete spectra** (Webster, arXiv:1603.06311v3, §2:
the definition with label `def:tilde-I` of complete spectra, and the homomorphism with label
`eq:furling-homomorphism`, which sends `E_i` to `∑_{u ∈ U_i} E_{i,u}` and so needs
`∑_u (n_{(i,u),b} + n_{b,(i,u)}) = -a_{ij}` for `b` over `j ≠ i`; the statement is implicit there
and the proof is reconstructed).

Let `L` be algebraically closed, `b` a label over `j ≠ i` with spectral value `w = ϖ_b(0) ≠ 0`,
and `Q = Q_{ij}`, `Q(x, y) = P_{ji}(x, y) P_{ij}(y, x)`, weighted homogeneous for positive weights
with nonzero coefficients at `x^m` and at `y^{m'}`. Suppose the labels over `i` are complete
at `b`: every root `u` of `Q(·, w)` is the spectral value of a label over `i`. Then
`a ↦ n_{ab} + n_{ba}` on the labels over `i` has finite support and sums to `m`. -/
theorem finsum_arrows_eq_of_complete [IsAlgClosed L] {i : I} {b : J} (hib : i ≠ D.π b)
    {Q : MvPolynomial (Fin 2) L} (hQ : Q = P (D.π b) i * rename ![1, 0] (P i (D.π b)))
    {e₁ e₂ N : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂) (hhom : Q.IsWeightedHomogeneous ![e₁, e₂] N)
    {m m' : ℕ} (hm : Q.coeff (Finsupp.single 0 m) ≠ 0) (hm' : Q.coeff (Finsupp.single 1 m') ≠ 0)
    (hw : (D.pw b).coeff 0 ≠ 0)
    (hcomplete : ∀ u, aeval ![u, (D.pw b).coeff 0] Q = 0 →
      ∃ a, D.π a = i ∧ (D.pw a).coeff 0 = u) :
    (Function.support fun a : {a : J // D.π a = i} => D.arrows a b + D.arrows b a).Finite ∧
      ∑ᶠ a : {a : J // D.π a = i}, (D.arrows a b + D.arrows b a) = m := by
  obtain ⟨hdeg, h0⟩ := natDegree_aeval_X_C_and_eval_zero he₁ he₂ hhom hm hm' hw
  have hq : aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] Q ≠ 0 := fun h => h0 (by
    rw [h, Polynomial.eval_zero])
  have key : (fun a : {a : J // D.π a = i} => D.arrows a b + D.arrows b a) = fun a =>
      (aeval ![Polynomial.X, Polynomial.C ((D.pw b).coeff 0)] Q).rootMultiplicity
        ((D.pw a.1).coeff 0) := by
    funext a
    obtain ⟨a, rfl⟩ := a
    exact D.arrows_add_arrows_eq_rootMultiplicity hib hQ hq
  rw [key, ← hdeg]
  refine finsum_rootMultiplicity_eq_natDegree (fun a a' h => Subtype.ext
    (D.pw_coeff_zero_inj _ _ (a.2.trans a'.2.symm) h)) hq fun u hu => ?_
  rw [Polynomial.IsRoot, eval_aeval_X_C] at hu
  obtain ⟨a, ha, rfl⟩ := hcomplete u hu
  exact ⟨⟨a, ha⟩, rfl⟩

/-- **The branched-cover identity on the full closure** (Webster, arXiv:1603.06311v3, §2, the
definition with label `def:tilde-I` with `U_i = L ∖ {0}`, and the homomorphism with label
`eq:furling-homomorphism`; the statement is implicit there and the proof is reconstructed).

Over an algebraically closed field `L`, with `d_i > 0` invertible in `L` and each `P_{ij} ≠ 0`
weighted homogeneous for the weights `(d_j, d_i)`, take the unfurling datum `ofClosure` on
`Σ i, L ∖ {0}`. Let `i ≠ j`, `w ≠ 0`, and `Q = Q_{ij}`, `Q(x, y) = P_{ji}(x, y) P_{ij}(y, x)`, with
nonzero coefficients at `x^m` and at `y^{m'}`. Then `u ↦ n_{(i,u),(j,w)} + n_{(j,w),(i,u)}` has
finite support and sums to `m`. -/
theorem ofClosure_finsum_arrows [IsAlgClosed L] (d : I → ℕ) (hdpos : ∀ i, 0 < d i)
    (hd : ∀ i, ((d i : ℕ) : L) ≠ 0) (hP : ∀ i j, i ≠ j → P i j ≠ 0)
    (hhom : ∀ i j, i ≠ j → ∃ D, (P i j).IsWeightedHomogeneous ![d j, d i] D)
    {i j : I} (hij : i ≠ j) (w : {w : L // w ≠ 0}) {Q : MvPolynomial (Fin 2) L}
    (hQ : Q = P j i * rename ![1, 0] (P i j)) {m m' : ℕ}
    (hm : Q.coeff (Finsupp.single 0 m) ≠ 0) (hm' : Q.coeff (Finsupp.single 1 m') ≠ 0) :
    (Function.support fun u : {u : L // u ≠ 0} =>
      (ofClosure d hdpos hd hP hhom).arrows ⟨i, u⟩ ⟨j, w⟩ +
        (ofClosure d hdpos hd hP hhom).arrows ⟨j, w⟩ ⟨i, u⟩).Finite ∧
      ∑ᶠ u : {u : L // u ≠ 0}, ((ofClosure d hdpos hd hP hhom).arrows ⟨i, u⟩ ⟨j, w⟩ +
        (ofClosure d hdpos hd hP hhom).arrows ⟨j, w⟩ ⟨i, u⟩) = m := by
  obtain ⟨D₁, h₁⟩ := hhom j i (Ne.symm hij)
  obtain ⟨D₂, h₂⟩ := hhom i j hij
  have hhomQ : Q.IsWeightedHomogeneous ![d i, d j] (D₁ + D₂) :=
    hQ ▸ h₁.mul (isWeightedHomogeneous_rename_swap h₂)
  obtain ⟨hdeg, h0⟩ := natDegree_aeval_X_C_and_eval_zero (hdpos i) (hdpos j) hhomQ hm hm' w.2
  have hq : aeval ![Polynomial.X, Polynomial.C (w : L)] Q ≠ 0 := fun h => h0 (by
    rw [h, Polynomial.eval_zero])
  set D := ofClosure (P := P) d hdpos hd hP hhom
  have key : (fun u : {u : L // u ≠ 0} => D.arrows ⟨i, u⟩ ⟨j, w⟩ + D.arrows ⟨j, w⟩ ⟨i, u⟩) =
      fun u : {u : L // u ≠ 0} =>
        (aeval ![Polynomial.X, Polynomial.C (w : L)] Q).rootMultiplicity (u : L) := by
    funext u
    have := D.arrows_add_arrows_eq_rootMultiplicity (a := ⟨i, u⟩) (b := ⟨j, w⟩) hij hQ
      (by rw [ofClosure_pw_coeff_zero]; exact hq)
    rwa [ofClosure_pw_coeff_zero, ofClosure_pw_coeff_zero] at this
  rw [key, ← hdeg]
  refine finsum_rootMultiplicity_eq_natDegree Subtype.val_injective hq fun u hu => ?_
  have hu0 : u ≠ 0 := by rintro rfl; exact h0 hu
  exact ⟨⟨u, hu0⟩, rfl⟩

/-- **The branched-cover identity, Cartan form** (Webster, arXiv:1603.06311v3, §2, as in
`ofClosure_finsum_arrows`; Khovanov–Lauda, arXiv:0804.2080v1, §3.1, for `d_{ij}`). For a Cartan
datum and KLR polynomials `Q_{ab}(x, y) = P_{ba}(x, y) P_{ab}(y, x)` whose extremal coefficients
(of `x^{d_{ab}}` in `Q_{ab}`) are nonzero, on the full closure `Σ i, L ∖ {0}`: for `i ≠ j` and
`w ≠ 0`, `∑_{u ≠ 0} (n_{(i,u),(j,w)} + n_{(j,w),(i,u)}) = d_{ij} = -a_{ij}`. -/
theorem ofClosure_finsum_arrows_eq_dij [IsAlgClosed L] (C : QuantumGroup.CartanDatum I)
    (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, ((d i : ℕ) : L) ≠ 0)
    (hP : ∀ i j, i ≠ j → P i j ≠ 0)
    (hhom : ∀ i j, i ≠ j → ∃ D, (P i j).IsWeightedHomogeneous ![d j, d i] D)
    (Q : I → I → MvPolynomial (Fin 2) L)
    (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
    (hext : ∀ a b, a ≠ b → (Q a b).coeff (Finsupp.single 0 (C.dij a b)) ≠ 0)
    {i j : I} (hij : i ≠ j) (w : {w : L // w ≠ 0}) :
    (Function.support fun u : {u : L // u ≠ 0} =>
      (ofClosure d hdpos hd hP hhom).arrows ⟨i, u⟩ ⟨j, w⟩ +
        (ofClosure d hdpos hd hP hhom).arrows ⟨j, w⟩ ⟨i, u⟩).Finite ∧
      ∑ᶠ u : {u : L // u ≠ 0}, ((ofClosure d hdpos hd hP hhom).arrows ⟨i, u⟩ ⟨j, w⟩ +
        (ofClosure d hdpos hd hP hhom).arrows ⟨j, w⟩ ⟨i, u⟩) = C.dij i j := by
  have hswap : Q j i = rename (![1, 0] : Fin 2 → Fin 2) (Q i j) := by
    rw [hPQ j i (Ne.symm hij), hPQ i j hij, map_mul, rename_rename,
      show (![(1 : Fin 2), 0] ∘ ![(1 : Fin 2), 0]) = id by funext x; fin_cases x <;> rfl,
      rename_id_apply, mul_comm]
  have hm' : (Q i j).coeff (Finsupp.single 1 (C.dij j i)) ≠ 0 := by
    rw [← coeff_rename_swap_single_zero, ← hswap]
    exact hext j i (Ne.symm hij)
  exact ofClosure_finsum_arrows d hdpos hd hP hhom hij w (hPQ i j hij) (hext i j hij) hm'

end UnfurlingDatum

end Categorification.KLR.Unfurling
