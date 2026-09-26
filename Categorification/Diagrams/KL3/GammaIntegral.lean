/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KaroubiAssoc
import Categorification.Diagrams.KL3.DownwardDecomp
import Categorification.QuantumGroup.UDotIntegral
import Categorification.KLR.Prop318
import Mathlib.RingTheory.Localization.BaseChange

/-!
# `γ` on the integral form `_𝒜 U̇` (KL III Proposition 3.27, integral version)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6
(TeX label `subsec_KzeroU`), Proposition 3.27: "The assignment `E_i 1_λ ↦ [E_i 1_λ]` extends
to a `ℤ[q, q⁻¹]`-algebra homomorphism `γ : _𝒜 U̇ → K₀(U̇)`", where `i` runs over the divided
powers signed sequences (KL III (2.13)–(2.17)) and `E_i 1_λ` is the corresponding 1-morphism of
`U̇` built from the divided powers `E_{+i^{(a)}} 1_λ`, `E_{-i^{(a)}} 1_λ` of (3.54). KL III's
proof: "`K₀(U̇)` is a free `ℤ[q, q⁻¹]`-module, so it is enough to check that the assignment above
extends to a homomorphism of `ℚ(q)`-algebras `γ_{ℚ(q)}` […]. Restricting `γ_{ℚ(q)}` to `_𝒜 U̇`
gives a homomorphism of `ℤ[q, q⁻¹]`-algebras with the image […] lying in `K₀(U̇)`."

The freeness of `K₀(U̇)` (KL III: from the Krull–Schmidt property of `U̇(λ, μ)`) is **not
formalized**. We prove everything that does not need it, and state precisely where it enters.

## Classes of divided powers (exact, in `K₀(U̇)`)

A divided powers signed sequence (dpss) is a list `d = ((ε₁, i₁, a₁), …)` (`UDot.dpW`);
`dpWord d = ε₁i₁^{a₁} ε₂i₂^{a₂} ⋯` is the underlying signed sequence.

* `dpObj1 ε i a μ ρ h`: the object `E_{εi^{(a)}} 1_μ` of `U̇(μ, ρ)` (`objEdiv` for `ε = +`,
  `objFdiv` for `ε = -`), placed at the left weight `ρ` (`h : ρ = μ + ε a i_X`).
* `dpC d μ ρ h = [E_{ε₁i₁^{(a₁)}}] ⋯ [E_{εₘiₘ^{(aₘ)}} 1_μ] ∈ K₀(U̇(μ, ρ))`, the class of the
  1-morphism `E_d 1_μ` (a product in the ring `K₀(U̇)`, `KaroubiAssoc`).
* `eC_dp1`: `[E_{(εi)^a} 1_μ] = [a]_i! [E_{εi^{(a)}} 1_μ]` (KL III display after (3.55), both
  lines);
* `eC_dpWord`: `[E_{dpWord d} 1_μ] = (∏_r [a_r]_{i_r}!) [E_d 1_μ]`;
* `dpC_append`: `[E_{d d'} 1_μ] = [E_d 1_ν] [E_{d'} 1_μ]` (multiplicativity of `γ` on the
  generators; `E1dp_mul_E1dp` on the algebraic side);
* `dpC_divided`: `[a]_i! [b]_i! [E_{εi^{(a)}}][E_{εi^{(b)}} 1_μ] = [a + b]_i! [E_{εi^{(a+b)}} 1_μ]`
  exactly in `K₀(U̇)` (the divided-power relation `E^{(a)} E^{(b)} = [a+b choose a] E^{(a+b)}`
  multiplied by `[a]_i! [b]_i!`).

## Compatibility with `γ_{ℚ(q)}`

* `gammaQ'_dpW`: for every `ℚ(q)`-vector space `V` receiving `K₀(U̇ 1_λ)` compatibly with `q`
  (`QTarget`), `γ_{ℚ(q)}(E_d 1_λ) = φ([E_d 1_λ])`, where `γ_{ℚ(q)} = gammaQ'` is KL III
  Proposition 3.27 over `ℚ(q)`. So the integral classes `dpC d` are the values of `γ` on the
  `ℤ[q, q⁻¹]`-algebra generators of `_𝒜 U̇` (`UDot.AUD`).

## The relations of `_𝒜 U̇` in `K₀(U̇)`, and `γ` on `_𝒜 U̇`

* `univTarget`: the `QTarget` `ℚ(q) ⊗_{ℤ[q,q⁻¹]} ⊕_ρ K₀(U̇(λ, ρ))`; its kernel on `K₀` is the
  `ℤ[q, q⁻¹]`-torsion (`univTarget_eq_zero_iff`).
* `dpC_relation`: **every `ℤ[q, q⁻¹]`-linear relation among the generators `E_{d_j} 1_λ` of
  `1_ρ (_𝒜 U̇) 1_λ` holds in `K₀(U̇(λ, ρ))` up to torsion**: if `∑_j c_j E_{d_j} 1_λ = 0` in `U̇`
  (`c_j ∈ ℤ[q, q⁻¹]`), then `p · ∑_j c_j [E_{d_j} 1_λ] = 0` for some non-zero-divisor
  `p ∈ ℤ[q, q⁻¹]`.
* `dpC_relation_of_torsionFree`: if `K₀(U̇(λ, ρ))` has no `ℤ[q, q⁻¹]`-torsion (true by KL III's
  Krull–Schmidt argument, **not formalized**), these relations hold exactly.
* `gammaUA`: consequently, **under this torsion-freeness hypothesis**, `γ` is a well-defined
  `ℤ[q, q⁻¹]`-linear map to `K₀(U̇(λ, ρ))` on the `ℤ[q, q⁻¹]`-span of the `E_d 1_λ` with left
  weight `ρ` inside `U̇ 1_λ` (the range of `dpComb`), with `γ(E_d 1_λ) = [E_d 1_λ]`
  (`gammaUA_dpW`, `gammaUA_apply`), and it is **multiplicative** (`gammaUA_mul`: for formal
  combinations `f`, `g` of dpss, `E(f) E(g) = E(dpMul f g)` in `U̇` (`dpComb_dpMul`) and
  `γ(E(f) E(g)) = γ(E(f)) γ(E(g))`; unconditionally on formal combinations, `dpCComb_dpMul`).
  Since products of the
  generators `E_d 1_λ` of `UDot.AUD` are again generators or zero (`UDot.E1dp_mul_E1dp`), this
  span is the block `1_ρ (_𝒜 U̇) 1_λ`; the identification of the two submodules is not
  formalized here.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.KL2 LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Divided powers signed sequences -/

section Words

/-- The signed sequence `(εi)^a` of an entry `(ε, i, a)` of a dpss. -/
def dpLetters (e : Bool × I × ℕ) : List (Letter I) := List.replicate e.2.2 (e.1, e.2.1)

/-- The signed sequence `ε₁i₁^{a₁} ⋯ εₘiₘ^{aₘ}` underlying a dpss. -/
def dpWord : List (Bool × I × ℕ) → List (Letter I)
  | [] => []
  | e :: d => dpLetters e ++ dpWord d

@[simp] theorem dpWord_nil : dpWord ([] : List (Bool × I × ℕ)) = [] := rfl

@[simp] theorem dpWord_cons (e : Bool × I × ℕ) (d : List (Bool × I × ℕ)) :
    dpWord (e :: d) = dpLetters e ++ dpWord d := rfl

theorem dpWord_append (d d' : List (Bool × I × ℕ)) : dpWord (d ++ d') = dpWord d ++ dpWord d' := by
  induction d with
  | nil => rfl
  | cons e d ih => rw [List.cons_append, dpWord_cons, dpWord_cons, ih, List.append_assoc]

/-- The product `∏_r [a_r]_{i_r}!` of symmetric quantum factorials of a dpss. -/
def dpFac (d : List (Bool × I × ℕ)) : LaurentPolynomial ℤ :=
  (d.map fun e => qfac (di C e.2.1) e.2.2).prod

@[simp] theorem dpFac_nil : dpFac (C := C) [] = 1 := rfl

@[simp] theorem dpFac_cons (e : Bool × I × ℕ) (d : List (Bool × I × ℕ)) :
    dpFac (C := C) (e :: d) = qfac (di C e.2.1) e.2.2 * dpFac (C := C) d := by
  simp [dpFac]

end Words

variable [DecidableEq I]

/-! ## The objects `E_{εi^{(a)}} 1_μ` at a given left weight -/

section One

variable {RD k}

omit [DecidableEq I] in
theorem wt_rep_up (i : I) (a : ℕ) (μ : X) :
    wν RD (Multiset.replicate a i) + μ = wt RD μ (List.replicate a (true, i)) := by
  rw [← wt_ups_word (RD := RD) (μ := μ) (seqPow i a), word_seqPow]
  simp [ups, List.map_replicate]

variable (RD k) in
/-- **The object `E_{εi^{(a)}} 1_μ` of `U̇(μ, ρ)`** (KL III (3.54)): `objEdiv` for `ε = +`,
`objFdiv` for `ε = -`, with shift `0`, transported to the left weight `ρ = μ + ε a i_X`. -/
def dpObj1 : (ε : Bool) → (i : I) → (a : ℕ) → (μ ρ : X) →
    wt RD μ (List.replicate a (ε, i)) = ρ → UKar RD k ρ μ
  | true, i, a, μ, _, h => ((wt_rep_up i a μ).trans h) ▸ objEdiv RD k i a μ 0
  | false, i, a, μ, _, h => h ▸ objFdiv RD k i a μ 0

variable (RD k) in
/-- The class `[E_{εi^{(a)}} 1_μ] ∈ K₀(U̇(μ, ρ))`. -/
abbrev dp1 (ε : Bool) (i : I) (a : ℕ) (μ ρ : X) (h : wt RD μ (List.replicate a (ε, i)) = ρ) :
    K0Kar RD k ρ μ :=
  K0U.cl (dpObj1 RD k ε i a μ ρ h)

theorem cl_objEdiv_shift (i : I) (a : ℕ) (μ : X) (s : ℤ) :
    K0U.cl (objEdiv RD k i a μ s) = (T s : LaurentPolynomial ℤ) • K0U.cl (objEdiv RD k i a μ 0) := by
  rw [kobj_shift, kobj_shift (t := _ + 0), add_zero, smul_smul, ← T_add]
  congr 2
  ring

theorem cl_objFdiv_shift (i : I) (a : ℕ) (μ : X) (s : ℤ) :
    K0U.cl (objFdiv RD k i a μ s) = (T s : LaurentPolynomial ℤ) • K0U.cl (objFdiv RD k i a μ 0) := by
  rw [← omegaK0_cl, ← omegaK0_cl, cl_objEdiv_shift, map_smul]

/-- `[E_{(+i)^a} 1_μ] = [a]_i! [E_{+i^{(a)}} 1_μ]` at the native left weight. -/
theorem eC_objEdiv (i : I) (a : ℕ) (μ : X) (h : wt RD μ (ups (List.replicate a i)) =
    wν RD (Multiset.replicate a i) + μ) :
    eC RD k _ μ (ups (List.replicate a i)) h =
      qfac (di C i) a • K0U.cl (objEdiv RD k i a μ 0) := by
  obtain ⟨ι, _, _, sh, _, hgen, ⟨e⟩⟩ := Epow_decomp RD k i a μ
  change SplitK0.of _ = _
  rw [SplitK0.of_iso e, SplitK0.of_biproduct]
  have hs : ∀ j, SplitK0.of (objEdiv RD k i a μ (sh j)) =
      (T (sh j) : LaurentPolynomial ℤ) • K0U.cl (objEdiv RD k i a μ 0) := fun j =>
    cl_objEdiv_shift i a μ (sh j)
  rw [Finset.sum_congr rfl fun j _ => hs j, ← Finset.sum_smul, hgen]
  rfl

/-- `[E_{(-i)^a} 1_μ] = [a]_i! [E_{-i^{(a)}} 1_μ]` (KL III, display after (3.55), second line). -/
theorem eC_objFdiv (i : I) (a : ℕ) (μ : X) :
    eC RD k _ μ (List.replicate a (dn i)) rfl =
      qfac (di C i) a • K0U.cl (objFdiv RD k i a μ 0) := by
  obtain ⟨ι, _, _, sh, _, hgen, ⟨e⟩⟩ := Fpow_decomp RD k i a μ
  change SplitK0.of _ = _
  rw [SplitK0.of_iso e, SplitK0.of_biproduct]
  have hs : ∀ j, SplitK0.of (objFdiv RD k i a μ (sh j)) =
      (T (sh j) : LaurentPolynomial ℤ) • K0U.cl (objFdiv RD k i a μ 0) := fun j =>
    cl_objFdiv_shift i a μ (sh j)
  rw [Finset.sum_congr rfl fun j _ => hs j, ← Finset.sum_smul, hgen]
  rfl

omit [DecidableEq I] in
theorem cl_cast {ρ ρ' μ : X} (h : ρ = ρ') (A : UKar RD k ρ μ) :
    K0U.cl (h ▸ A) = h ▸ K0U.cl A := by
  subst h; rfl

omit [DecidableEq I] in
theorem eC_cast {ρ ρ' μ : X} (h : ρ = ρ') (w : List (Letter I)) (hw : wt RD μ w = ρ) :
    eC RD k ρ' μ w (hw.trans h) = h ▸ eC RD k ρ μ w hw := by
  subst h; rfl

omit [DecidableEq I] in
theorem smul_cast {ρ ρ' μ : X} (h : ρ = ρ') (p : LaurentPolynomial ℤ) (x : K0Kar RD k ρ μ) :
    (h ▸ (p • x) : K0Kar RD k ρ' μ) = p • (h ▸ x : K0Kar RD k ρ' μ) := by
  subst h; rfl

/-- **Divided powers in `K₀(U̇)`** (KL III, display after (3.55), both lines):
`[E_{(εi)^a} 1_μ] = [a]_i! [E_{εi^{(a)}} 1_μ]`. -/
theorem eC_dp1 (ε : Bool) (i : I) (a : ℕ) (μ ρ : X) (h : wt RD μ (List.replicate a (ε, i)) = ρ) :
    eC RD k ρ μ (List.replicate a (ε, i)) h = qfac (di C i) a • dp1 RD k ε i a μ ρ h := by
  cases ε with
  | true =>
    have hE := (wt_rep_up i a μ).trans h
    have hw : wt RD μ (ups (List.replicate a i)) = wν RD (Multiset.replicate a i) + μ := by
      rw [wt_rep_up]; simp [ups, List.map_replicate]
    have e1 : eC RD k ρ μ (List.replicate a (true, i)) h =
        hE ▸ eC RD k _ μ (ups (List.replicate a i)) hw := by
      rw [← eC_cast]
      exact eC_congr (by simp [ups, List.map_replicate]) _ _
    rw [e1, eC_objEdiv, smul_cast, dp1, dpObj1, cl_cast]
  | false =>
    subst h
    exact eC_objFdiv i a μ

end One

/-! ## The classes `[E_d 1_μ]` of dpss -/

section Dpss

/-- **The class `[E_d 1_μ] ∈ K₀(U̇(μ, ρ))` of a dpss `d`**: the product
`[E_{ε₁i₁^{(a₁)}}] ⋯ [E_{εₘiₘ^{(aₘ)}} 1_μ]` in the ring `K₀(U̇)`, i.e. the class of the
1-morphism `E_d 1_μ` of KL III (2.17), (3.54). -/
def dpC : (d : List (Bool × I × ℕ)) → (μ ρ : X) → wt RD μ (dpWord d) = ρ → K0Kar RD k ρ μ
  | [], μ, _, h => (show μ = _ from h) ▸ K0U.one (deg := deg RD) (wtObj RD k μ)
  | e :: d, μ, ρ, h =>
    K0U.mul (dp1 RD k e.1 e.2.1 e.2.2 (wt RD μ (dpWord d)) ρ
      (by rw [← h, dpWord_cons, wt_append]; rfl)) (dpC d μ _ rfl)

variable {RD k}

omit [DecidableEq I] in
theorem one_eq_eC (μ : X) :
    K0U.one (deg := deg RD) (wtObj RD k μ) = eC RD k μ μ [] rfl := rfl

theorem dpC_nil (μ : X) : dpC RD k [] μ μ rfl = eC RD k μ μ [] rfl := rfl

/-- The recursion for `dpC` at an arbitrary intermediate weight. -/
theorem dpC_cons (e : Bool × I × ℕ) (d : List (Bool × I × ℕ)) (μ ν ρ : X)
    (hν : wt RD μ (dpWord d) = ν) (h1 : wt RD ν (dpLetters e) = ρ)
    (h : wt RD μ (dpWord (e :: d)) = ρ) :
    dpC RD k (e :: d) μ ρ h = K0U.mul (dp1 RD k e.1 e.2.1 e.2.2 ν ρ h1) (dpC RD k d μ ν hν) := by
  subst hν; rfl

theorem dpC_congr {d : List (Bool × I × ℕ)} {μ ρ : X} (h h' : wt RD μ (dpWord d) = ρ) :
    dpC RD k d μ ρ h = dpC RD k d μ ρ h' := rfl

/-- **`[E_{dpWord d} 1_μ] = (∏_r [a_r]_{i_r}!) [E_d 1_μ]`** in `K₀(U̇)`. -/
theorem eC_dpWord (d : List (Bool × I × ℕ)) (μ ρ : X) (h : wt RD μ (dpWord d) = ρ) :
    eC RD k ρ μ (dpWord d) h = dpFac (C := C) d • dpC RD k d μ ρ h := by
  induction d generalizing ρ with
  | nil =>
    subst h
    rw [dpFac_nil, one_smul]
    rfl
  | cons e d ih =>
    have h1 : wt RD (wt RD μ (dpWord d)) (dpLetters e) = ρ := by
      rw [← h, dpWord_cons, wt_append]
    have hm : eC RD k ρ μ (dpWord (e :: d)) h = K0U.mul (eC RD k ρ _ (dpLetters e) h1)
        (eC RD k _ μ (dpWord d) rfl) := (eC_mul (dpLetters e) (dpWord d) h1 rfl h).symm
    have h2 : eC RD k ρ _ (dpLetters e) h1 = _ := eC_dp1 e.1 e.2.1 e.2.2 _ ρ h1
    rw [dpC_cons e d μ _ ρ rfl h1 h, dpFac_cons, hm, h2, ih _ rfl, K0U.mul_smul_left, K0U.mul_smul_right, smul_smul]

/-- **Multiplicativity**: `[E_{d d'} 1_μ] = [E_d 1_ν] · [E_{d'} 1_μ]` (`ν = μ + |d'|_X`). -/
theorem dpC_append (d d' : List (Bool × I × ℕ)) (μ ν ρ : X) (h' : wt RD μ (dpWord d') = ν)
    (h : wt RD ν (dpWord d) = ρ) (h'' : wt RD μ (dpWord (d ++ d')) = ρ) :
    dpC RD k (d ++ d') μ ρ h'' = K0U.mul (dpC RD k d ν ρ h) (dpC RD k d' μ ν h') := by
  induction d generalizing ρ with
  | nil =>
    subst h
    exact (K0U.one_mul _).symm
  | cons e d ih =>
    have hν1 : wt RD ν (dpWord d) = wt RD μ (dpWord (d ++ d')) := by
      rw [← h', dpWord_append, wt_append]
    have h1 : wt RD (wt RD μ (dpWord (d ++ d'))) (dpLetters e) = ρ := by
      rw [← h'', List.cons_append, dpWord_cons, wt_append]
    change dpC RD k (e :: (d ++ d')) μ ρ h'' = _
    rw [dpC_cons e (d ++ d') μ _ ρ rfl h1,
      ih _ hν1 rfl, ← K0U.mul_assoc, dpC_cons e d ν _ ρ hν1 h1]

/-- **The divided-power relation in `K₀(U̇)`**:
`[a]_i! [b]_i! [E_{εi^{(a)}}] [E_{εi^{(b)}} 1_μ] = [a + b]_i! [E_{εi^{(a+b)}} 1_μ]`
(the relation `E^{(a)} E^{(b)} 1_μ = [a+b choose a]_i E^{(a+b)} 1_μ` of `_𝒜 U̇` multiplied by
`[a]_i! [b]_i!`), exactly, in `K₀(U̇)`. -/
theorem dp1_mul_dp1 (ε : Bool) (i : I) (a b : ℕ) (μ ν ρ : X)
    (hb : wt RD μ (List.replicate b (ε, i)) = ν) (ha : wt RD ν (List.replicate a (ε, i)) = ρ)
    (hab : wt RD μ (List.replicate (a + b) (ε, i)) = ρ) :
    (qfac (di C i) a * qfac (di C i) b) •
        K0U.mul (dp1 RD k ε i a ν ρ ha) (dp1 RD k ε i b μ ν hb) =
      qfac (di C i) (a + b) • dp1 RD k ε i (a + b) μ ρ hab := by
  rw [mul_smul, ← K0U.mul_smul_right, ← K0U.mul_smul_left, ← eC_dp1, ← eC_dp1, ← eC_dp1,
    eC_mul _ _ ha hb (by rw [wt_append, hb, ha])]
  exact eC_congr (List.replicate_add a b _).symm _ _

end Dpss

/-! ## Compatibility with `γ_{ℚ(q)}` -/

section Compat

variable {RD k}

omit [DecidableEq I] in
theorem lpToQ_qfac_di (i : I) (a : ℕ) :
    lpToQ (qfac (di C i) a) = qfact (qi C vQ i) a := by
  rw [lpToQ_qfac]; rfl

omit [DecidableEq I] in
/-- `E_{εi}^{(a)} ⋯ = (∏ [a_r]_{i_r}!)⁻¹ E_{dpWord d}` in the free algebra `'U 1_λ`. -/
theorem dpW_eq_smul (d : List (Bool × I × ℕ)) :
    dpW C vQ d = (lpToQ (dpFac (C := C) d))⁻¹ • (ew (dpWord d) : UDot.Free (RatFunc ℚ) I) := by
  induction d with
  | nil => simp [dpW, dpFac, ew_nil]
  | cons e d ih =>
    have hd : dpW C vQ (e :: d) = dpE C vQ e * dpW C vQ d := by
      simp [dpW, List.map_cons, List.prod_cons]
    rw [hd, ih, dpE, dpFac_cons, map_mul, dpWord_cons, ew_append, smul_mul_smul_comm,
      lpToQ_qfac_di, mul_inv]
    rfl

omit [DecidableEq I] in
theorem lpToQ_dpFac_ne_zero (d : List (Bool × I × ℕ)) : lpToQ (dpFac (C := C) d) ≠ 0 := by
  induction d with
  | nil => simp [dpFac]
  | cons e d ih =>
    rw [dpFac_cons, map_mul, lpToQ_qfac_di]
    exact mul_ne_zero (C.qfact_ne_zero e.2.1 e.2.2) ih

variable {lam : X} {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]
  (Φ : QTarget RD k lam V)

/-- **`γ_{ℚ(q)}(E_d 1_λ) = φ([E_d 1_λ])`**: on the `ℤ[q, q⁻¹]`-algebra generators
`E_d 1_λ = E_{ε₁i₁}^{(a₁)} ⋯ E_{εₘiₘ}^{(aₘ)} 1_λ` of `_𝒜 U̇`, KL III's `γ_{ℚ(q)}` (`gammaQ'`)
takes the values `[E_d 1_λ] ∈ K₀(U̇)` (after base change to `ℚ(q)`). -/
theorem gammaQ'_dpW (d : List (Bool × I × ℕ)) (ρ : X) (h : wt RD lam (dpWord d) = ρ) :
    gammaQ' Φ (UDot.mk RD vQ lam (dpW C vQ d)) = Φ.φ ρ (dpC RD k d lam ρ h) := by
  subst h
  rw [dpW_eq_smul, map_smul, map_smul, gammaQ'_mk_ew, eC_dpWord, Φ.map_smul, smul_smul,
    inv_mul_cancel₀ (lpToQ_dpFac_ne_zero d), one_smul]

end Compat

/-! ## Torsion: the universal `ℚ(q)`-target -/

section Universal

attribute [local instance] KLR.KLGamma.vAlgebra

open scoped Classical

omit [DecidableEq I] in
theorem lpToQ_eq_laurentEval : lpToQ = laurentEval (vQ : (RatFunc ℚ)ˣ) := by
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, map_add, hp, hp']
  | C_mul_T n a =>
    rw [map_mul, map_mul, lpToQ_T, laurentEval_T, lpToQ, eval₂_C, KLR.KLGamma.laurentEval_C]
    rfl

variable (lam : X)

/-- `⊕_ρ K₀(U̇(λ, ρ))`. -/
abbrev K0Blk : Type _ := DirectSum X fun ρ => K0Kar RD k ρ lam

/-- `ℚ(q) ⊗_{ℤ[q,q⁻¹]} ⊕_ρ K₀(U̇(λ, ρ))` (`q ↦ q`). -/
abbrev K0BlkQ : Type _ := TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) (K0Blk RD k lam)

/-- The map `K₀(U̇(λ, ρ)) → ℚ(q) ⊗ ⊕_ρ K₀(U̇(λ, ρ))`, `x ↦ 1 ⊗ x`. -/
def toBlkQ (ρ : X) : K0Kar RD k ρ lam →ₗ[LaurentPolynomial ℤ] K0BlkQ RD k lam :=
  (TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0Blk RD k lam) 1).comp
    (DirectSum.lof (LaurentPolynomial ℤ) X (fun ρ => K0Kar RD k ρ lam) ρ)

omit [DecidableEq I] in
theorem toBlkQ_smul (ρ : X) (p : LaurentPolynomial ℤ) (x : K0Kar RD k ρ lam) :
    toBlkQ RD k lam ρ (p • x) = lpToQ p • toBlkQ RD k lam ρ x := by
  rw [map_smul, lpToQ_eq_laurentEval, ← algebraMap_smul (RatFunc ℚ) p]
  rfl

/-- **The universal `QTarget`** `ℚ(q) ⊗_{ℤ[q,q⁻¹]} ⊕_ρ K₀(U̇(λ, ρ))`. -/
def univTarget : QTarget RD k lam (K0BlkQ RD k lam) where
  φ ρ := (toBlkQ RD k lam ρ).toAddMonoidHom
  map_T ρ n x := by
    change toBlkQ RD k lam ρ _ = _
    rw [toBlkQ_smul, lpToQ_T]
    rfl

omit [DecidableEq I] in
/-- **The kernel of `K₀(U̇(λ, ρ)) → ℚ(q) ⊗ K₀` is the `ℤ[q, q⁻¹]`-torsion.** -/
theorem univTarget_eq_zero_iff (ρ : X) (x : K0Kar RD k ρ lam) :
    (univTarget RD k lam).φ ρ x = 0 ↔
      ∃ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), p • x = 0 := by
  haveI := KLR.KLGamma.isFractionRing_vAlgebra
  have hL : IsLocalizedModule (nonZeroDivisors (LaurentPolynomial ℤ))
      (TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0Blk RD k lam) 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (LaurentPolynomial ℤ)) (RatFunc ℚ)
      _).2 (TensorProduct.isBaseChange _ _ _)
  change TensorProduct.mk (LaurentPolynomial ℤ) (RatFunc ℚ) (K0Blk RD k lam) 1
    (DirectSum.lof (LaurentPolynomial ℤ) X (fun ρ => K0Kar RD k ρ lam) ρ x) = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors (LaurentPolynomial ℤ))]
  constructor
  · rintro ⟨⟨p, hp⟩, hpx⟩
    refine ⟨p, hp, ?_⟩
    rw [Submonoid.mk_smul, ← map_smul] at hpx
    exact DirectSum.of_injective (β := fun ρ => K0Kar RD k ρ lam) ρ
      (by rw [map_zero]; exact hpx)
  · rintro ⟨p, hp, hpx⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    rw [Submonoid.mk_smul, ← map_smul, hpx, map_zero]

end Universal

/-! ## The relations of `_𝒜 U̇` in `K₀(U̇)` -/

section Relations

variable {RD k}

/-- **The `ℤ[q, q⁻¹]`-linear relations among the generators of `1_ρ (_𝒜 U̇) 1_λ` hold in
`K₀(U̇(λ, ρ))` up to torsion**: if `∑_j c_j E_{d_j} 1_λ = 0` in `U̇ 1_λ` for dpss `d_j` with
left weight `ρ` and `c_j ∈ ℤ[q, q⁻¹]`, then `p · ∑_j c_j [E_{d_j} 1_λ] = 0` for a
non-zero-divisor `p ∈ ℤ[q, q⁻¹]`. -/
theorem dpC_relation {ι : Type*} (s : Finset ι) (c : ι → LaurentPolynomial ℤ)
    (d : ι → List (Bool × I × ℕ)) (lam ρ : X) (hd : ∀ j, wt RD lam (dpWord (d j)) = ρ)
    (hrel : ∑ j ∈ s, lpToQ (c j) • UDot.mk RD vQ lam (dpW C vQ (d j)) = 0) :
    ∃ p ∈ nonZeroDivisors (LaurentPolynomial ℤ),
      p • ∑ j ∈ s, c j • dpC RD k (d j) lam ρ (hd j) = 0 := by
  rw [← univTarget_eq_zero_iff, map_sum]
  have := congrArg (gammaQ' (univTarget RD k lam)) hrel
  rw [map_zero, map_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QTarget.map_smul, LinearMap.map_smul, gammaQ'_dpW _ _ ρ (hd j)]

/-- **The relations of `1_ρ (_𝒜 U̇) 1_λ` hold exactly in `K₀(U̇(λ, ρ))` if it is torsion free**
(KL III: `K₀(U̇)` is a free `ℤ[q, q⁻¹]`-module, by the Krull–Schmidt property; not formalized
here). -/
theorem dpC_relation_of_torsionFree {lam ρ : X}
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0)
    {ι : Type*} (s : Finset ι) (c : ι → LaurentPolynomial ℤ) (d : ι → List (Bool × I × ℕ))
    (hd : ∀ j, wt RD lam (dpWord (d j)) = ρ)
    (hrel : ∑ j ∈ s, lpToQ (c j) • UDot.mk RD vQ lam (dpW C vQ (d j)) = 0) :
    ∑ j ∈ s, c j • dpC RD k (d j) lam ρ (hd j) = 0 := by
  obtain ⟨p, hp, hpx⟩ := dpC_relation (k := k) s c d lam ρ hd hrel
  exact htf p hp _ hpx

end Relations

/-! ## `γ` on `1_ρ (_𝒜 U̇) 1_λ`, given torsion-freeness -/

section GammaA

attribute [local instance] KLR.KLGamma.vAlgebra

variable {RD k} (lam ρ : X)

/-- The dpss with right weight `λ` and left weight `ρ`. -/
def DpIdx : Type u := {d : List (Bool × I × ℕ) // wt RD lam (dpWord d) = ρ}

/-- `U̇ 1_λ` as a `ℤ[q, q⁻¹]`-module (by restriction of scalars along `q ↦ q`). -/
abbrev U1Z : Type _ := RestrictScalars (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)

/-- The `ℤ[q, q⁻¹]`-linear map `∑_d c_d d ↦ ∑_d c_d E_d 1_λ` from formal combinations of dpss to
`U̇ 1_λ`; its range is `1_ρ (_𝒜 U̇) 1_λ`. -/
def dpComb : (DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) →ₗ[LaurentPolynomial ℤ]
    U1Z (RD := RD) lam :=
  Finsupp.linearCombination (LaurentPolynomial ℤ) fun d =>
    (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)).symm
      (UDot.mk RD vQ lam (dpW C vQ d.1))

/-- The `ℤ[q, q⁻¹]`-linear map `∑_d c_d d ↦ ∑_d c_d [E_d 1_λ]` to `K₀(U̇(λ, ρ))`. -/
def dpCComb : (DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) →ₗ[LaurentPolynomial ℤ]
    K0Kar RD k ρ lam :=
  Finsupp.linearCombination (LaurentPolynomial ℤ) fun d => dpC RD k d.1 lam ρ d.2

omit [DecidableEq I] in
theorem dpComb_apply (f : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) :
    RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam) (dpComb lam ρ f) =
      ∑ j ∈ f.support, lpToQ (f j) • UDot.mk RD vQ lam (dpW C vQ j.1) := by
  rw [dpComb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RestrictScalars.addEquiv_map_smul, lpToQ_eq_laurentEval, AddEquiv.apply_symm_apply]
  rfl

theorem ker_dpComb_le (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ),
      ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0) :
    LinearMap.ker (dpComb (RD := RD) lam ρ) ≤ LinearMap.ker (dpCComb (RD := RD) (k := k) lam ρ) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  have h0 := congrArg (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ)
    (U1 RD vQ lam)) hf
  rw [dpComb_apply, map_zero] at h0
  have := dpC_relation_of_torsionFree (k := k) htf f.support (fun j => f j) (fun j => j.1)
    (fun j => j.2) h0
  rw [dpCComb, Finsupp.linearCombination_apply, Finsupp.sum]
  exact this

/-- **KL III Proposition 3.27, integral form, on the block `1_ρ (_𝒜 U̇) 1_λ`, assuming that
`K₀(U̇(λ, ρ))` is `ℤ[q, q⁻¹]`-torsion free**: the `ℤ[q, q⁻¹]`-linear map
`γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` with `γ(E_d 1_λ) = [E_d 1_λ]` (`gammaUA_dpW`), defined on the
`ℤ[q, q⁻¹]`-span of the `E_d 1_λ` (the range of `dpComb`). -/
def gammaUA (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ),
      ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0) :
    LinearMap.range (dpComb (RD := RD) lam ρ) →ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  ((LinearMap.ker (dpComb (RD := RD) lam ρ)).liftQ (dpCComb lam ρ) (ker_dpComb_le lam ρ htf)).comp
    (dpComb (RD := RD) lam ρ).quotKerEquivRange.symm.toLinearMap

/-- `γ(∑_d c_d E_d 1_λ) = ∑_d c_d [E_d 1_λ]`. -/
theorem gammaUA_apply (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ),
      ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0) (f : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ) :
    gammaUA lam ρ htf ⟨dpComb lam ρ f, LinearMap.mem_range_self _ _⟩ = dpCComb lam ρ f := by
  rw [gammaUA, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- `γ(E_d 1_λ) = [E_d 1_λ]`. -/
theorem gammaUA_dpW (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ),
      ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0) (d : DpIdx (RD := RD) lam ρ) :
    gammaUA lam ρ htf ⟨dpComb lam ρ (Finsupp.single d 1), LinearMap.mem_range_self _ _⟩ =
      dpC RD k d.1 lam ρ d.2 := by
  rw [gammaUA_apply, dpCComb, Finsupp.linearCombination_single, one_smul]

/-! ### Multiplicativity -/

omit [DecidableEq I] in
theorem dpFac_append (d d' : List (Bool × I × ℕ)) :
    dpFac (C := C) (d ++ d') = dpFac (C := C) d * dpFac (C := C) d' := by
  simp [dpFac, List.map_append, List.prod_append]

omit [DecidableEq I] in
/-- `(E_d 1_μ)(E_{d'} 1_λ) = E_{d d'} 1_λ` in `U̇` for `μ = λ + |d'|_X`. -/
theorem mulU_dpW (d d' : List (Bool × I × ℕ)) (μ : X) (h : wt RD lam (dpWord d') = μ) :
    mulU RD vQ μ lam (UDot.mk RD vQ μ (dpW C vQ d)) (UDot.mk RD vQ lam (dpW C vQ d')) =
      UDot.mk RD vQ lam (dpW C vQ (d ++ d')) := by
  have hw : lam + RD.wX (dpWord d') = μ := by rw [add_comm, ← wt_eq_add_wX, h]
  rw [dpW_eq_smul d, dpW_eq_smul d', dpW_eq_smul (d ++ d'), map_smul (UDot.mk RD vQ μ),
    map_smul (UDot.mk RD vQ lam), map_smul (UDot.mk RD vQ lam), map_smul (mulU RD vQ μ lam),
    LinearMap.smul_apply, map_smul, mulU_mk_ew, if_pos hw, dpWord_append, dpFac_append,
    map_mul, mul_inv, smul_smul]

variable {lam ρ} {μ : X}

/-- Concatenation of dpss, `E_d 1_μ · E_{d'} 1_λ = E_{d d'} 1_λ`. -/
def dpCat (d : DpIdx (RD := RD) μ ρ) (d' : DpIdx (RD := RD) lam μ) : DpIdx (RD := RD) lam ρ :=
  ⟨d.1 ++ d'.1, by rw [dpWord_append, wt_append, d'.2, d.2]⟩

/-- The product of formal combinations of dpss (convolution along concatenation). -/
def dpMul (f : DpIdx (RD := RD) μ ρ →₀ LaurentPolynomial ℤ)
    (g : DpIdx (RD := RD) lam μ →₀ LaurentPolynomial ℤ) : DpIdx (RD := RD) lam ρ →₀ LaurentPolynomial ℤ :=
  f.sum fun d a => g.sum fun d' b => Finsupp.single (dpCat d d') (a * b)

/-- **Multiplicativity of `[E_d 1_λ]` on formal combinations**:
`∑ (c c')_{dd'} [E_{dd'} 1_λ] = (∑ c_d [E_d]) · (∑ c'_{d'} [E_{d'} 1_λ])` in `K₀(U̇)`. -/
theorem dpCComb_dpMul (f : DpIdx (RD := RD) μ ρ →₀ LaurentPolynomial ℤ)
    (g : DpIdx (RD := RD) lam μ →₀ LaurentPolynomial ℤ) :
    dpCComb (k := k) lam ρ (dpMul f g) =
      K0U.mul (dpCComb (k := k) μ ρ f) (dpCComb (k := k) lam μ g) := by
  have hR : K0U.mul (dpCComb (k := k) μ ρ f) (dpCComb (k := k) lam μ g) =
      ∑ d ∈ f.support, ∑ d' ∈ g.support,
        K0U.mul (f d • dpC RD k d.1 μ ρ d.2) (g d' • dpC RD k d'.1 lam μ d'.2) := by
    rw [dpCComb, dpCComb, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum, Finsupp.sum]
    simp only [map_sum, AddMonoidHom.finset_sum_apply]
    first | rfl | exact Finset.sum_comm
  rw [hR, dpMul, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [dpCComb, Finsupp.linearCombination_single, K0U.mul_smul_left, K0U.mul_smul_right, smul_smul]
  congr 1
  exact dpC_append d.1 d'.1 lam μ ρ d'.2 d.2 (dpCat d d').2

omit [DecidableEq I] in
/-- The corresponding identity in `U̇`: `E(dpMul f g) = E(f) · E(g)`. -/
theorem dpComb_dpMul (f : DpIdx (RD := RD) μ ρ →₀ LaurentPolynomial ℤ)
    (g : DpIdx (RD := RD) lam μ →₀ LaurentPolynomial ℤ) :
    RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)
        (dpComb lam ρ (dpMul f g)) =
      mulU RD vQ μ lam
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ μ) (dpComb μ ρ f))
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)
          (dpComb lam μ g)) := by
  have hs : ∀ (ν ν' : X) (x : DpIdx (RD := RD) ν ν') (c : LaurentPolynomial ℤ),
      RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ ν)
        (dpComb ν ν' (Finsupp.single x c)) = lpToQ c • UDot.mk RD vQ ν (dpW C vQ x.1) := by
    intro ν ν' x c
    rw [dpComb_apply]
    by_cases hc : c = 0
    · subst hc; simp
    · rw [Finsupp.support_single_ne_zero _ hc, Finset.sum_singleton, Finsupp.single_eq_same]
  have hf : ∀ (ν ν' : X) (f : DpIdx (RD := RD) ν ν' →₀ LaurentPolynomial ℤ),
      RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ ν) (dpComb ν ν' f) =
        ∑ x ∈ f.support, lpToQ (f x) • UDot.mk RD vQ ν (dpW C vQ x.1) := fun ν ν' f =>
    dpComb_apply ν ν' f
  have hR : mulU RD vQ μ lam
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ μ) (dpComb μ ρ f))
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)
          (dpComb lam μ g)) =
      ∑ d ∈ f.support, ∑ d' ∈ g.support, mulU RD vQ μ lam
        (lpToQ (f d) • UDot.mk RD vQ μ (dpW C vQ d.1))
        (lpToQ (g d') • UDot.mk RD vQ lam (dpW C vQ d'.1)) := by
    rw [hf μ ρ f, hf lam μ g]
    simp only [map_sum, LinearMap.coeFn_sum, Finset.sum_apply]
    first | rfl | exact Finset.sum_comm
  rw [hR, dpMul, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [hs lam ρ (dpCat d d') (f d * g d'), LinearMap.map_smul₂, LinearMap.map_smul,
    mulU_dpW lam d.1 d'.1 μ d'.2, map_mul, mul_smul]
  rfl

/-- **`γ` is multiplicative** (KL III Proposition 3.27: `γ` is a `ℤ[q, q⁻¹]`-*algebra*
homomorphism), on the blocks `1_ρ (_𝒜 U̇) 1_μ × 1_μ (_𝒜 U̇) 1_λ → 1_ρ (_𝒜 U̇) 1_λ`, under the
torsion-freeness hypotheses needed to define `γ`: for `x = E(f)`, `y = E(g)`, the product
`x y = E(dpMul f g)` in `U̇` and `γ(x y) = γ(x) γ(y)` in `K₀(U̇)`. -/
theorem gammaUA_mul
    (htf₁ : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ μ, p • x = 0 → x = 0)
    (htf₂ : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k μ lam, p • x = 0 → x = 0)
    (htf : ∀ p ∈ nonZeroDivisors (LaurentPolynomial ℤ), ∀ x : K0Kar RD k ρ lam, p • x = 0 → x = 0)
    (f : DpIdx (RD := RD) μ ρ →₀ LaurentPolynomial ℤ)
    (g : DpIdx (RD := RD) lam μ →₀ LaurentPolynomial ℤ) :
    RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)
        (dpComb lam ρ (dpMul f g)) =
      mulU RD vQ μ lam
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ μ) (dpComb μ ρ f))
        (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)
          (dpComb lam μ g)) ∧
    gammaUA lam ρ htf ⟨dpComb lam ρ (dpMul f g), LinearMap.mem_range_self _ _⟩ =
      K0U.mul (gammaUA μ ρ htf₁ ⟨dpComb μ ρ f, LinearMap.mem_range_self _ _⟩)
        (gammaUA lam μ htf₂ ⟨dpComb lam μ g, LinearMap.mem_range_self _ _⟩) := by
  refine ⟨dpComb_dpMul f g, ?_⟩
  rw [gammaUA_apply, gammaUA_apply, gammaUA_apply, dpCComb_dpMul]

end GammaA

end Categorification.KL3.Diagram
