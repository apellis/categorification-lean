/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SortedSpanProof
import Categorification.Diagrams.KL3.EndOneGraded
import Categorification.QuantumGroup.UDotFormNondeg
import Categorification.QuantumGroup.UDotFormFormula

/-!
# KL III Theorem 1.2: `γ` is injective if the graphical calculus is nondegenerate

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1:

* §1, **Theorem 1.2** (TeX label `thm-injective`): "The map `γ` is injective if the graphical
  calculus for the root datum and field `𝕜` is nondegenerate";
* §1, **Proposition 1.4** (`prop-iso`): with Theorems 1.1 and 1.3, `γ` is an isomorphism;
* §3.9 (`subsec_injectivity`, "Injectivity of `γ` in the nondegenerate case"), the proof: under
  nondegeneracy `gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` (eq. (3.69),
  `eq_gdim_U_semi`), so `γ` intertwines `π ⟨ , ⟩` with the form
  `⟨[P], [Q]⟩_π = Σ_t q^t dim U̇(P{t}, Q)` on `K₀(U̇)`; by Proposition 2.5 (`prop_nondeg`)
  `⟨ , ⟩` is nondegenerate, hence `γ` is injective.

## Hypotheses

* **Nondegeneracy of the calculus** (KL III §3.2.3, Definition before Remark 3.14: "`B_{𝐢,𝐣,λ}`
  is a basis of `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)` for all `𝐢, 𝐣, λ`"; equivalently — KL III: "Thus, a
  calculus is nondegenerate if the equality holds in Corollary 3.13 for all `𝐢, 𝐣, λ`" — the
  equality `gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`, eq. (3.69)). We use the latter
  form, `CalculusNondeg RD k`, stated coefficientwise: for every `t`, `dim_𝕜 HOM_U(E_𝐢 1_λ,
  E_𝐣 1_λ)_t` is the coefficient of `q^t` in the Laurent expansion of `π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`.
  Here `π = ∏_{i ∈ I} ∏_{a ≥ 1} (1 - q_i^{2a})⁻¹` is the graded dimension of the bubble algebra
  `Π_λ` (KL III (3.26)): `piLS C` has as coefficient of `q^d` the number of monomials of degree
  `d` in the generators `(i, α)` of degree `α (i·i)` (`monDeg`; `piTrunc_coeff` identifies this
  with the product formula).
* **KL III Proposition 2.5** for `( , )`: `QuantumGroup.UDot.KL3.FormNondeg RD`
  (`Categorification.QuantumGroup.UDotFormNondeg`; KL III cite Lusztig 26.3.1 for it).

As for Theorem 1.1 (`gammaUA'_surjective`), the Cartan datum is simply-laced, `I` finite and `𝕜`
a field (these are the hypotheses under which `γ = gammaUA'` is defined in the library).

## Main results

* `homDim`: the additive functional `[B] ↦ dim_𝕜 U̇(A, B)` on `K₀(U̇(λ, ρ))`;
* `finrank_hom_nfObj`: `dim U̇(E_𝐢 1_λ {a}, E_𝐣 1_λ {b}) = dim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)_{a - b}`;
* **`gammaUA'_injective`** — KL III Theorem 1.2;
* **`gammaUA'_bijective`**, `gammaUA'Equiv` — the Proposition 1.4-type consequence: under the two
  hypotheses `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is an isomorphism of `ℤ[q, q⁻¹]`-modules.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents StringDiagrams QuantumGroup
  UDot Presentation GradedBicat KrullSchmidtCat LaurentPolynomial Module

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

/-! ## The series `π` -/

variable (C) in
/-- `π ∈ ℚ[[q]]`: the coefficient of `q^n` is the number of monomials of degree `n` in the
generators of `Π_λ` (KL III (3.26): `π = ∏_{i ∈ I} ∏_{a ≥ 1} 1/(1 - q_i^{2a})`, "the graded
dimension of `Π_λ` is `π`"). -/
def piPS : PowerSeries ℚ := PowerSeries.mk fun n => ((monDeg C (n : ℤ)).ncard : ℚ)

variable (C) in
/-- `π` as a Laurent series. -/
def piLS : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ (piPS C)

theorem monDeg_zero : monDeg C 0 = {0} := by
  ext s
  simp only [monDeg, Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨weight_wPi_eq_zero, fun h => by rw [h]; simp⟩

theorem piLS_ne_zero : piLS C ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries ℚ => x.coeff ((0 : ℕ) : ℤ)) h
  simp only [piLS, HahnSeries.ofPowerSeries_apply_coeff, piPS, PowerSeries.coeff_mk,
    HahnSeries.coeff_zero] at this
  rw [Nat.cast_zero, monDeg_zero, Set.ncard_singleton] at this
  norm_num at this

/-! ## Laurent expansions -/

/-- The expansion `ℚ(q) → ℚ((q))`. -/
abbrev toLS : RatFunc ℚ →+* LaurentSeries ℚ := (RatFunc.coeAlgHom ℚ).toRingHom

theorem toLS_injective : Function.Injective toLS := (toLS).injective

theorem single_one_zpow (n : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : ℚ)) ^ n = HahnSeries.single n (1 : ℚ) := by
  rcases n with m | m
  · rw [Int.ofNat_eq_coe, zpow_natCast, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  · rw [zpow_negSucc, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [HahnSeries.single_mul_single, one_mul, Int.negSucc_eq]
    push_cast
    rw [show ((m : ℤ) + 1 + -((m : ℤ) + 1)) = 0 by ring]
    rfl

theorem toLS_vQ_zpow (n : ℤ) :
    toLS ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) = HahnSeries.single n (1 : ℚ) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, vQ_val]
  change ((RatFunc.X : RatFunc ℚ) : LaurentSeries ℚ) ^ n = _
  rw [RatFunc.coe_X, single_one_zpow]

theorem toLS_lpToQ_C_mul_T (a n : ℤ) :
    toLS (lpToQ (LaurentPolynomial.C a * T n)) = HahnSeries.single n (a : ℚ) := by
  rw [map_mul, map_mul, lpToQ_T, toLS_vQ_zpow]
  have : lpToQ (LaurentPolynomial.C a) = (a : RatFunc ℚ) := by
    rw [lpToQ, eval₂_C]; rfl
  rw [this, map_intCast]
  have h2 : ((a : ℤ) : LaurentSeries ℚ) = HahnSeries.single (0 : ℤ) (a : ℚ) := by
    rw [← map_intCast (HahnSeries.C (Γ := ℤ) (R := ℚ)), HahnSeries.C_apply]
  rw [h2, HahnSeries.single_mul_single, zero_add, mul_one]

/-! ## Hom-spaces between the objects `E_s 1_λ {a}` -/

section HomObj

variable {S : Signature} {P : Presentation S k} {deg : S.Gen → ℤ} {l m : P.Bicat}

/-- The entry of a morphism `x{a} ⟶ y{b}` of `U̇` between shifted 1-morphisms. -/
def objOfEntry (x y : Bicat.Hom l m) (a b : ℤ) :
    (objOf (P := P) (deg := deg) x a ⟶ objOf y b) →ₗ[k] (P.homDeg deg x.obj y.obj (a - b)) where
  toFun f := f.f PUnit.unit PUnit.unit
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem objOfEntry_bijective (x y : Bicat.Hom l m) (a b : ℤ) :
    Function.Bijective (objOfEntry (P := P) (deg := deg) x y a b) := by
  constructor
  · intro f g h
    apply Karoubi.hom_ext
    apply Mat_.hom_ext
    rintro ⟨⟩ ⟨⟩
    exact h
  · intro g
    exact ⟨(incl P deg l m).map (X := ⟨x, a⟩) (Y := ⟨y, b⟩) g, rfl⟩

/-- `dim U̇(x{a}, y{b}) = dim HOM(x, y)_{a - b}`. -/
theorem finrank_hom_objOf (x y : Bicat.Hom l m) (a b : ℤ) :
    finrank k (objOf (P := P) (deg := deg) x a ⟶ objOf y b) =
      finrank k (P.homDeg deg x.obj y.obj (a - b)) :=
  (LinearEquiv.ofBijective _ (objOfEntry_bijective x y a b)).finrank_eq

end HomObj

variable (RD k)

/-- **`dim U̇(E_𝐢 1_λ {a}, E_𝐣 1_λ {b}) = dim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)_{a - b}`**. -/
theorem finrank_hom_nfObj {ρ lam : X} (s w : List (Letter I)) (hs : wt RD lam s = ρ)
    (hw : wt RD lam w = ρ) (a b : ℤ) :
    finrank k (nfObj RD k ρ lam s hs a ⟶ nfObj RD k ρ lam w hw b) =
      finrank k (HomD RD k lam s w (a - b)) :=
  finrank_hom_objOf _ _ a b

variable {RD k}

/-! ## The functional `[B] ↦ dim U̇(A, B)` on `K₀` -/

section HomDim

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

include hSL in
/-- **The additive functional `[B] ↦ dim_𝕜 U̇(A, B)` on `K₀(U̇(λ, ρ))`** (for a fixed object `A`;
the coefficients of KL III's form `⟨[A], [B]⟩_π = Σ_t q^t dim U̇(A{t}, B)`). -/
def homDim {ρ lam : X} (A : UKar RD k ρ lam) : K0Kar RD k ρ lam →+ ℤ :=
  haveI := homFinite_UDot (RD := RD) (k := k) hSL ρ lam
  SplitK0.lift (fun B => (finrank k (A ⟶ B) : ℤ))
    (fun B B' e => by
      show (finrank k (A ⟶ B) : ℤ) = finrank k (A ⟶ B')
      rw [(postIso k A e).finrank_eq])
    (fun B B' => by
      show (finrank k (A ⟶ B ⊞ B') : ℤ) = finrank k (A ⟶ B) + finrank k (A ⟶ B')
      rw [(biprodEquiv k A B B').finrank_eq, Module.finrank_prod]; push_cast; rfl)


theorem homDim_cl {ρ lam : X} (A B : UKar RD k ρ lam) :
    homDim hSL A (K0U.cl B) = (finrank k (A ⟶ B) : ℤ) := by
  rw [homDim, K0U.cl, SplitK0.lift_of]

/-- `homDim (E_𝐣 {t}) (q^n [E_𝐢]) = dim HOM(E_𝐣 1_λ, E_𝐢 1_λ)_{t - n}`. -/
theorem homDim_T_eC {ρ lam : X} (w s : List (Letter I)) (hw : wt RD lam w = ρ)
    (hs : wt RD lam s = ρ) (t n : ℤ) :
    homDim hSL (nfObj RD k ρ lam w hw t) ((T n : LaurentPolynomial ℤ) • eC RD k ρ lam s hs) =
      (finrank k (HomD RD k lam w s (t - n)) : ℤ) := by
  have e : (T n : LaurentPolynomial ℤ) • eC RD k ρ lam s hs = K0U.cl (nfObj RD k ρ lam s hs n) := by
    exact (K0U.objOf_shift _ n).symm
  rw [e, homDim_cl, finrank_hom_nfObj]

/-- `homDim (E_𝐣 {t}) (h [E_𝐢]) = Σ_n h_n dim HOM(E_𝐣 1_λ, E_𝐢 1_λ)_{t - n}`, i.e. the
coefficient of `q^t` in `h · gdim HOM(E_𝐣 1_λ, E_𝐢 1_λ)`. -/
theorem homDim_smul_eC {ρ lam : X} (w s : List (Letter I)) (hw : wt RD lam w = ρ)
    (hs : wt RD lam s = ρ) (t : ℤ) (h : LaurentPolynomial ℤ) :
    homDim hSL (nfObj RD k ρ lam w hw t) (h • eC RD k ρ lam s hs) =
      h.sum (fun n a => a * (finrank k (HomD RD k lam w s (t - n)) : ℤ)) := by
  induction h using LaurentPolynomial.induction_on' with
  | add p p' hp hp' =>
    rw [add_smul, map_add, hp, hp', Finsupp.sum_add_index']
    · intro n; ring
    · intro n a b; ring
  | C_mul_T n a =>
    rw [SplitK0.C_mul_T_smul, map_zsmul, ← SplitK0.T_smul, homDim_T_eC,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum_single_index (by ring), smul_eq_mul]

end HomDim

/-- The coefficients of `h(q) · S` for a Laurent polynomial `h`. -/
theorem coeff_toLS_lpToQ_mul (h : LaurentPolynomial ℤ) (S : LaurentSeries ℚ) (t : ℤ) :
    (toLS (lpToQ h) * S).coeff t = h.sum fun n a => (a : ℚ) * S.coeff (t - n) := by
  induction h using LaurentPolynomial.induction_on' with
  | add p p' hp hp' =>
    rw [map_add, map_add, add_mul, HahnSeries.coeff_add, hp, hp', Finsupp.sum_add_index']
    · intro n; simp
    · intro n a b; push_cast; ring
  | C_mul_T n a =>
    rw [toLS_lpToQ_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      Finsupp.sum_single_index (by simp)]
    have := HahnSeries.coeff_single_mul_add (r := (a : ℚ)) (x := S) (a := t - n) (b := n)
    rw [sub_add_cancel] at this
    exact this

/-! ## Nondegeneracy of the calculus -/

variable (RD k) in
/-- **The graphical calculus is nondegenerate** (KL III §3.2.3; in the equivalent form "the
equality holds in Corollary 3.13 for all `𝐢, 𝐣, λ`", eq. (3.69)):
`gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) = π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`, i.e. for every degree `t`, the dimension of
the degree-`t` part of `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)` is the coefficient of `q^t` in the Laurent
expansion of `π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩` (`π = piLS C`, `⟨ , ⟩ = UDot.KL3.sform RD`). -/
def CalculusNondeg : Prop :=
  ∀ (lam : X) (s w : List (Letter I)) (t : ℤ),
    ((finrank k (HomD RD k lam s w t) : ℤ) : ℚ) =
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ w lam))).coeff t

/-- The Hom-spaces between `E_s 1_λ` and `E_w 1_λ` vanish unless the left weights agree. -/
theorem homD_eq_bot_of_wt_ne {lam : X} {s w : List (Letter I)} (h : wt RD lam s ≠ wt RD lam w)
    (d : ℤ) : HomD RD k lam s w d = ⊥ := by
  rw [homD_eq_span, Submodule.span_eq_bot]
  rintro f ⟨ls, hls, -, rfl⟩
  exact absurd (hls.wt_eq RD lam).symm h

/-- **Sanity check of `CalculusNondeg`**: for sequences with different left weights both sides of
the defining equality vanish, so the condition is only about `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)` with
`λ + 𝐢_X = λ + 𝐣_X`. -/
theorem calculusNondeg_cond_of_wt_ne {lam : X} {s w : List (Letter I)}
    (h : wt RD lam s ≠ wt RD lam w) (t : ℤ) :
    ((finrank k (HomD RD k lam s w t) : ℤ) : ℚ) =
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ w lam))).coeff t := by
  rw [homD_eq_bot_of_wt_ne h, finrank_bot, ← (UDot.KL3.thm_2_7 C RD s w lam lam).1]
  have e1 : E1 RD vQ s lam = idem RD vQ (lam + RD.wX s) lam (E1 RD vQ s lam) := by
    rw [idem_E1, if_pos ⟨rfl, rfl⟩]
  have e2 : E1 RD vQ w lam = idem RD vQ (lam + RD.wX w) lam (E1 RD vQ w lam) := by
    rw [idem_E1, if_pos ⟨rfl, rfl⟩]
  have hne : ¬ (lam + RD.wX s = lam + RD.wX w ∧ lam = lam) := fun e => h (by
    rw [wt_eq_add_wX, wt_eq_add_wX, add_comm, e.1, add_comm])
  rw [e1, e2, UDot.KL3.form, formUD_weight _ _ _ _ _ _ _ _ _ _ hne]
  simp

section Main

attribute [local instance] KLR.KLGamma.vAlgebra

variable [DecidableEq I] [Finite I] (hSL : SimplyLaced C)

include hSL in
/-- **The key step of KL III §3.9**: a `ℤ[q, q⁻¹]`-linear relation `Σ_j h_j [E_{s_j} 1_λ] = 0`
in `K₀(U̇(λ, ρ))` gives `(E_w 1_λ, Σ_j h_j E_{s_j} 1_λ) = 0` for every `w`, if the calculus is
nondegenerate (`γ` intertwines `π ⟨ , ⟩` and `⟨ , ⟩_π`). -/
theorem form_eq_zero_of_relation (hnd : CalculusNondeg RD k) {ρ lam : X} {J : Type*}
    (S : Finset J) (h : J → LaurentPolynomial ℤ) (s : J → List (Letter I))
    (hs : ∀ j, wt RD lam (s j) = ρ) (hrel : ∑ j ∈ S, h j • eC RD k ρ lam (s j) (hs j) = 0)
    (w : List (Letter I)) (hw : wt RD lam w = ρ) :
    ∑ j ∈ S, lpToQ (h j) * UDot.KL3.form RD (E1 RD vQ w lam) (E1 RD vQ (s j) lam) = 0 := by
  apply toLS_injective
  rw [map_sum, map_zero]
  apply mul_left_cancel₀ (piLS_ne_zero (C := C))
  rw [mul_zero, Finset.mul_sum]
  ext t
  rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
  have hterm : ∀ j, (piLS C * toLS (lpToQ (h j) *
      UDot.KL3.form RD (E1 RD vQ w lam) (E1 RD vQ (s j) lam))).coeff t =
      ((homDim hSL (nfObj RD k ρ lam w hw t) (h j • eC RD k ρ lam (s j) (hs j)) : ℤ) : ℚ) := by
    intro j
    rw [map_mul, mul_left_comm, coeff_toLS_lpToQ_mul, homDim_smul_eC, Finsupp.sum, Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [(UDot.KL3.thm_2_7 C RD w (s j) lam lam).1, ← hnd lam w (s j) (t - n)]
    push_cast; rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Int.cast_sum, ← map_sum, hrel, map_zero,
    Int.cast_zero]

include hSL in
/-- The relation of the previous lemma kills `Σ_j h_j E_{s_j} 1_λ` in `U̇`, given KL III
Proposition 2.5. -/
theorem sum_eq_zero_of_relation (hnd : CalculusNondeg RD k) (h25 : UDot.KL3.FormNondeg RD)
    {ρ lam : X} {J : Type*} (S : Finset J) (h : J → LaurentPolynomial ℤ) (s : J → List (Letter I))
    (hs : ∀ j, wt RD lam (s j) = ρ) (hrel : ∑ j ∈ S, h j • eC RD k ρ lam (s j) (hs j) = 0) :
    ∑ j ∈ S, lpToQ (h j) • E1 RD vQ (s j) lam = 0 := by
  set z := ∑ j ∈ S, lpToQ (h j) • E1 RD vQ (s j) lam
  have hform : ∀ (w : List (Letter I)) (μ : X), UDot.KL3.form RD (E1 RD vQ w μ) z = 0 := by
    intro w μ
    rw [map_sum]
    have hsm : ∀ j, UDot.KL3.form RD (E1 RD vQ w μ) (lpToQ (h j) • E1 RD vQ (s j) lam) =
        lpToQ (h j) * UDot.KL3.form RD (E1 RD vQ w μ) (E1 RD vQ (s j) lam) := fun j => by
      rw [LinearMap.map_smul, smul_eq_mul]
    simp only [hsm]
    by_cases hμ : μ = lam
    · subst hμ
      by_cases hw : wt RD μ w = ρ
      · exact form_eq_zero_of_relation hSL hnd S h s hs hrel w hw
      · refine Finset.sum_eq_zero fun j _ => ?_
        have e1 : E1 RD vQ w μ = idem RD vQ (μ + RD.wX w) μ (E1 RD vQ w μ) := by
          rw [idem_E1, if_pos ⟨rfl, rfl⟩]
        have e2 : E1 RD vQ (s j) μ = idem RD vQ (μ + RD.wX (s j)) μ (E1 RD vQ (s j) μ) := by
          rw [idem_E1, if_pos ⟨rfl, rfl⟩]
        have hne : ¬ (μ + RD.wX w = μ + RD.wX (s j) ∧ μ = μ) := fun e => by
          apply hw
          rw [wt_eq_add_wX, add_comm, e.1, ← hs j, wt_eq_add_wX, add_comm]
        rw [e1, e2, UDot.KL3.form, formUD_weight _ _ _ _ _ _ _ _ _ _ hne, mul_zero]
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [UDot.KL3.form, formUD_E1_E1, if_neg hμ, mul_zero]
  have hall : ∀ u, UDot.KL3.form RD u z = 0 := by
    intro u
    induction u using E1_induction with
    | zero => simp
    | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul_E1 r t μ => rw [map_smul, LinearMap.smul_apply, hform, smul_zero]
  exact h25 z fun u => by rw [UDot.KL3.form, formUD_symm]; exact hall u

/-- **Khovanov–Lauda III, Theorem 1.2** (`thm-injective`, proof in §3.9): if the graphical
calculus is nondegenerate (`CalculusNondeg RD k`), then `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is
injective — given KL III Proposition 2.5 (`UDot.KL3.FormNondeg RD`, taken as a hypothesis;
simply-laced Cartan datum, `I` finite, `𝕜` a field). -/
theorem gammaUA'_injective (hnd : CalculusNondeg RD k) (h25 : UDot.KL3.FormNondeg RD)
    (lam ρ : X) : Function.Injective (gammaUA' (RD := RD) (k := k) hSL lam ρ) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨y, f, rfl⟩ hy
  rw [gammaUA'_apply] at hy
  apply Subtype.ext
  apply (RestrictScalars.addEquiv (LaurentPolynomial ℤ) (RatFunc ℚ) (U1 RD vQ lam)).injective
  simp only [ZeroMemClass.coe_zero, map_zero]
  rw [dpComb_apply]
  -- clear the divided powers
  set S := f.support
  set N : DpIdx (RD := RD) lam ρ → LaurentPolynomial ℤ := fun j =>
    ∏ j' ∈ S.erase j, dpFac (C := C) j'.1
  have hN : ∀ j ∈ S, N j * dpFac (C := C) j.1 = ∏ j' ∈ S, dpFac (C := C) j'.1 :=
    fun j hj => Finset.prod_erase_mul _ _ hj
  have hrel : ∑ j ∈ S, (f j * N j) • eC RD k ρ lam (dpWord j.1) j.2 = 0 := by
    have hy' : ∑ j ∈ S, f j • dpC RD k j.1 lam ρ j.2 = 0 := by
      rw [dpCComb, Finsupp.linearCombination_apply, Finsupp.sum] at hy; exact hy
    calc ∑ j ∈ S, (f j * N j) • eC RD k ρ lam (dpWord j.1) j.2
        = ∑ j ∈ S, (∏ j' ∈ S, dpFac (C := C) j'.1) • (f j • dpC RD k j.1 lam ρ j.2) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [eC_dpWord, smul_smul, smul_smul, ← hN j hj]; ring_nf
      _ = 0 := by rw [← Finset.smul_sum, hy', smul_zero]
  have hz := sum_eq_zero_of_relation hSL hnd h25 S (fun j => f j * N j) (fun j => dpWord j.1)
    (fun j => j.2) hrel
  have hz' : ∑ j ∈ S, lpToQ (f j * N j) • UDot.mk RD vQ lam (ew (dpWord j.1)) = 0 := by
    have := congrArg (compB RD vQ lam) hz
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, E1, compB_ofB_self]
  have hP : lpToQ (∏ j' ∈ S, dpFac (C := C) j'.1) ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => lpToQ_dpFac_ne_zero _
  refine (smul_right_injective _ hP) ?_
  dsimp only
  rw [smul_zero, Finset.smul_sum, ← hz']
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dpW_eq_smul, map_smul, smul_smul, smul_smul, ← hN j hj, map_mul, map_mul]
  have hd := lpToQ_dpFac_ne_zero (C := C) j.1
  congr 1
  field_simp
  ring

include hSL in
/-- **KL III Proposition 1.4-type consequence**: if the calculus is nondegenerate and
Proposition 2.5 holds, `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective (surjectivity is KL III
Theorem 1.1, `gammaUA'_surjective`). -/
theorem gammaUA'_bijective (hnd : CalculusNondeg RD k) (h25 : UDot.KL3.FormNondeg RD)
    (lam ρ : X) : Function.Bijective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  ⟨gammaUA'_injective hSL hnd h25 lam ρ, gammaUA'_surjective hSL lam ρ⟩

/-- **`γ` as an isomorphism of `ℤ[q, q⁻¹]`-modules `1_ρ (_𝒜 U̇) 1_λ ≅ K₀(U̇(λ, ρ))`** under the
hypotheses of `gammaUA'_bijective`. -/
def gammaUA'Equiv (hnd : CalculusNondeg RD k) (h25 : UDot.KL3.FormNondeg RD) (lam ρ : X) :
    LinearMap.range (dpComb (RD := RD) lam ρ) ≃ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
  LinearEquiv.ofBijective _ (gammaUA'_bijective hSL hnd h25 lam ρ)

end Main

end Categorification.KL3.Diagram
