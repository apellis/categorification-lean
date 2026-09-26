/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0UDot
import Categorification.Diagrams.KL3.SerreKaroubi

/-!
# Relations in `K₀(U̇)` from Propositions 3.24–3.26

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6, proof of
Proposition 3.27 (TeX label `prop_gamma`): "Propositions 3.24, 3.25, and 3.26 show that defining
relations of `U̇` lift to 2-isomorphisms of 1-morphisms in `U̇` and, therefore, descend to
relations in the Grothendieck group `K₀(U̇)`."

We write `eC ρ λ w h = [E_w 1_λ] ∈ K₀(U̇(λ, ρ))` for a signed sequence `w` with right weight
`λ` and left weight `ρ = λ + w_X` (`h : wt λ w = ρ`), and `qn d n = ∑_{s<n} q^{d(n-1-2s)}`, the
quantum integer `[n]` in the variable `q^d` (so `qn (d_i) n = [n]_i`). In arbitrary contexts
`a`, `b` (signed sequences on either side), with `μ = λ + b_X` the weight between the pair and
`b`:

* `eC_EF` (Proposition 3.25, `⟨i, μ⟩ ≥ 0`):
  `[E_{a +i -i b}] = [E_{a -i +i b}] + [⟨i, μ⟩]_i [E_{a b}]`;
* `eC_FE` (Proposition 3.25, `⟨i, μ⟩ ≤ 0`):
  `[E_{a -i +i b}] = [E_{a +i -i b}] + [-⟨i, μ⟩]_i [E_{a b}]`;
* `eC_ij` (Proposition 3.26, `i ≠ j`): `[E_{a +i -j b}] = [E_{a -j +i b}]`.

These are exactly the images of the relations (2.4) of `U̇` (`E_iF_j 1_μ - F_jE_i 1_μ =
δ_{ij} [⟨i, μ⟩]_i 1_μ`). The divided-power and Serre relations are in
`Categorification.Diagrams.KL3.K0Serre`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-! ## Contexts -/

section Context

variable {RD k}

/-- Concatenation of normal-form 1-morphisms: `E_a E_w E_b = E_{a w b}`. -/
theorem nfHom_comp_comp {ρ ν μ lam : X} {a w b : List (Letter I)} (ha : wt RD ν a = ρ)
    (hw : wt RD μ w = ν) (hb : wt RD lam b = μ) (h : wt RD lam (a ++ w ++ b) = ρ) :
    ((nfHom RD k ρ ν a ha).comp (nfHom RD k ν μ w hw)).comp (nfHom RD k μ lam b hb) =
      nfHom RD k ρ lam (a ++ w ++ b) h := by
  subst hb hw ha
  apply Bicat.Hom.ext
  simp only [Bicat.Hom.comp_obj]
  apply Obj.ext
  · simp [wt_append]
  · simp [ob, wd_append, wt_append]

/-- **Whiskering normal-form objects**: `E_a · (E_w 1_μ {s}) · E_b = E_{a w b} 1_λ {s}`. -/
theorem ctx_nfObj {ρ ν μ lam : X} {a w b : List (Letter I)} (ha : wt RD ν a = ρ)
    (hw : wt RD μ w = ν) (hb : wt RD lam b = μ) (h : wt RD lam (a ++ w ++ b) = ρ) (s : ℤ) :
    (wRDot (deg RD) (nfHom RD k μ lam b hb)).obj
        ((wLDot (deg RD) (nfHom RD k ρ ν a ha)).obj (nfObj RD k ν μ w hw s)) =
      nfObj RD k ρ lam (a ++ w ++ b) h s := by
  rw [wLDot_objOf, wRDot_objOf, nfHom_comp_comp ha hw hb h]

end Context

/-! ## Classes of normal-form 1-morphisms -/

/-- `K₀(U̇(λ, ρ))` (library order: 1-morphisms from the left region `ρ` to the right region `λ`). -/
abbrev K0Kar (ρ lam : X) : Type _ :=
  K0U (pres RD k) (deg RD) (wtObj RD k ρ) (wtObj RD k lam)

/-- **The class `[E_w 1_λ] ∈ K₀(U̇(λ, ρ))`** of a signed sequence `w` with `λ + w_X = ρ`. -/
abbrev eC (ρ lam : X) (w : List (Letter I)) (h : wt RD lam w = ρ) : K0Kar RD k ρ lam :=
  K0U.cl (nfObj RD k ρ lam w h 0)

/-- The quantum integer `[n]` in the variable `q^d`: `∑_{s < n} q^{d (n - 1 - 2s)}`. -/
def qn (d : ℤ) (n : ℕ) : LaurentPolynomial ℤ :=
  ∑ s ∈ Finset.range n, T (d * ((n : ℤ) - 1 - 2 * s))

variable {RD k}

/-- `[E_w 1_λ {s}] = q^s [E_w 1_λ]`. -/
theorem cl_nfObj_shift {ρ lam : X} (w : List (Letter I)) (h : wt RD lam w = ρ) (s : ℤ) :
    K0U.cl (nfObj RD k ρ lam w h s) = (T s : LaurentPolynomial ℤ) • eC RD k ρ lam w h :=
  K0U.objOf_shift _ s

section Commutation

variable {ρ μ lam : X} (a b : List (Letter I))

theorem sum_cl_objOne (ha : wt RD μ a = ρ) (hb : wt RD lam b = μ) (i : I) {n : ℕ} (d : Fin n → ℤ) (hd : ∀ s : Fin n, d s = di C i * (n - 1 - 2 * s))
    (h3 : wt RD lam (a ++ [] ++ b) = ρ) :
    ∑ s : Fin n, K0U.cl ((wRDot (deg RD) (nfHom RD k μ lam b hb)).obj
        ((wLDot (deg RD) (nfHom RD k ρ μ a ha)).obj (objOne RD k μ (d s)))) =
      qn (di C i) n • eC RD k ρ lam (a ++ [] ++ b) h3 := by
  have e : ∀ s : Fin n, K0U.cl ((wRDot (deg RD) (nfHom RD k μ lam b hb)).obj
      ((wLDot (deg RD) (nfHom RD k ρ μ a ha)).obj (objOne RD k μ (d s)))) =
      (T (di C i * ((n : ℤ) - 1 - 2 * (s : ℕ))) : LaurentPolynomial ℤ) •
        eC RD k ρ lam (a ++ [] ++ b) h3 := fun s => by
    rw [ctx_nfObj ha rfl hb h3, cl_nfObj_shift, hd]
  rw [Finset.sum_congr rfl fun s _ => e s, qn, Finset.sum_smul]
  exact Fin.sum_univ_eq_sum_range (fun s => (T (di C i * ((n : ℤ) - 1 - 2 * s)) :
    LaurentPolynomial ℤ) • eC RD k ρ lam (a ++ [] ++ b) h3) n

/-- **KL III Proposition 3.25 in `K₀`, `⟨i, μ⟩ ≥ 0`**: `[E_{a +i -i b} 1_λ] =
[E_{a -i +i b} 1_λ] + [⟨i, μ⟩]_i [E_{a b} 1_λ]`, where `μ = λ + b_X`. -/
theorem eC_EF (ha : wt RD μ a = ρ) (hb : wt RD lam b = μ) (i : I) (hn : 0 ≤ ip RD i μ) (h1 : wt RD lam (a ++ [up i, dn i] ++ b) = ρ)
    (h2 : wt RD lam (a ++ [dn i, up i] ++ b) = ρ) (h3 : wt RD lam (a ++ [] ++ b) = ρ) :
    eC RD k ρ lam (a ++ [up i, dn i] ++ b) h1 =
      eC RD k ρ lam (a ++ [dn i, up i] ++ b) h2 +
        qn (di C i) (ip RD i μ).toNat • eC RD k ρ lam (a ++ [] ++ b) h3 := by
  have e := prop325EF_whisker i μ (nfHom RD k ρ μ a ha) (nfHom RD k μ lam b hb) hn
  have h := SplitK0.of_iso e
  rw [SplitK0.of_biprod, SplitK0.of_biproduct] at h
  erw [ctx_nfObj ha _ hb h1, ctx_nfObj ha _ hb h2] at h
  refine h.trans (congrArg _ ?_)
  exact sum_cl_objOne a b ha hb i _ (fun s => by rw [Int.toNat_of_nonneg hn]) h3

/-- **KL III Proposition 3.25 in `K₀`, `⟨i, μ⟩ ≤ 0`**: `[E_{a -i +i b} 1_λ] =
[E_{a +i -i b} 1_λ] + [-⟨i, μ⟩]_i [E_{a b} 1_λ]`, where `μ = λ + b_X`. -/
theorem eC_FE (ha : wt RD μ a = ρ) (hb : wt RD lam b = μ) (i : I) (hn : ip RD i μ ≤ 0) (h1 : wt RD lam (a ++ [up i, dn i] ++ b) = ρ)
    (h2 : wt RD lam (a ++ [dn i, up i] ++ b) = ρ) (h3 : wt RD lam (a ++ [] ++ b) = ρ) :
    eC RD k ρ lam (a ++ [dn i, up i] ++ b) h2 =
      eC RD k ρ lam (a ++ [up i, dn i] ++ b) h1 +
        qn (di C i) (-ip RD i μ).toNat • eC RD k ρ lam (a ++ [] ++ b) h3 := by
  have e := prop325FE_whisker i μ (nfHom RD k ρ μ a ha) (nfHom RD k μ lam b hb) hn
  have h := SplitK0.of_iso e
  rw [SplitK0.of_biprod, SplitK0.of_biproduct] at h
  erw [ctx_nfObj ha _ hb h1, ctx_nfObj ha _ hb h2] at h
  refine h.trans (congrArg _ ?_)
  exact sum_cl_objOne a b ha hb i _ (fun s => by rw [Int.toNat_of_nonneg (by omega)]) h3

end Commutation

/-- **KL III Proposition 3.26 in `K₀`**: for `i ≠ j`, `[E_{a +i -j b} 1_λ] = [E_{a -j +i b} 1_λ]`. -/
theorem eC_ij {ρ ν μ lam : X} (a b : List (Letter I)) (i j : I) (hij : i ≠ j)
    (ha : wt RD ν a = ρ) (hν : wt RD μ [up i, dn j] = ν) (hb : wt RD lam b = μ)
    (h1 : wt RD lam (a ++ [up i, dn j] ++ b) = ρ) (h2 : wt RD lam (a ++ [dn j, up i] ++ b) = ρ) :
    eC RD k ρ lam (a ++ [up i, dn j] ++ b) h1 = eC RD k ρ lam (a ++ [dn j, up i] ++ b) h2 := by
  subst hν
  have e := prop326_whisker RD k i j hij μ 0 (nfHom RD k ρ _ a ha) (nfHom RD k μ lam b hb)
  have h := SplitK0.of_iso e
  erw [ctx_nfObj ha _ hb h1, ctx_nfObj ha _ hb h2] at h
  exact h

end Categorification.KL3.Diagram
