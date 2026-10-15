/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Defs
import Categorification.KLR.Unfurling.Density

/-!
# Unfurling: the substitution map on polynomial representations

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras* (arXiv:1603.06311v3), §3.3, unfurls an
index set `I` along a map `π : J → I` (for Webster, `J = Ĩ` is the set of pairs `(i, u)` with
`u` in a spectrum `U_i`, Def. label `def:tilde-I`), attaching to every `j ∈ J` a power series
`ϖ_j(z)` (for Webster `ϖ_{(i,u)}(z) = u (z + 1)^{d_i}`). The proof of Lemma label
`lem:gamma-homo` compares the polynomial representations of the two KLR algebras through the map
`γ_P` of (label `com0new`): on the summand of a sequence `j ∈ Seq ν̃` lying over `i ∈ Seq ν`,
the variable `x_a` is replaced by `ϖ_{j_a}(y_a)`.

Here `ϖ_j` is a polynomial `pw j` (which covers Webster's choice). This file defines

* `Unfurling.down`: the sequence `π ∘ j ∈ Seq ν` under a sequence `j ∈ Seq ν̃`, where
  `ν̃.map π = ν`;
* `Unfurling.substAt`: the substitution `x_a ↦ ϖ_{j_a}(y_a)` on one summand;
* `Unfurling.polySubst`: the map `γ_P : Pol_ν → Pol_ν̃`;

and proves how `γ_P` intertwines the operators of the polynomial representation (`opE`, `opX`,
and the crossing operators `crossComp` for the three cases of Webster's formulas
(labels `com0new`, `com0newer`, `com0newerer`)), as polynomial identities.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial TypeA PolyRep

variable {I J : Type*} {k : Type*} [CommRing k]
  (π : J → I) (pw : J → Polynomial k)

/-- `ϖ_j` evaluated at the variable `X a`. -/
noncomputable def pwAt {σ : Type*} (j : J) (a : σ) : MvPolynomial σ k :=
  Polynomial.aeval (X a) (pw j)

variable {ν : Multiset I} {ν' : Multiset J} (hν : ν'.map π = ν)

include hν in
theorem card_eq : Multiset.card ν = Multiset.card ν' := by
  rw [← hν, Multiset.card_map]

/-- The sequence `π ∘ j` under a sequence `j` of weight `ν̃`. -/
def down (t : Seq ν') : Seq ν :=
  ⟨fun a => π (t.lbl (Fin.cast (card_eq π hν) a)), by
    have h1 : (Finset.univ.val.map fun a => t.lbl (Fin.cast (card_eq π hν) a)) = ν' := by
      rw [show (fun a => t.lbl (Fin.cast (card_eq π hν) a)) = t.1 ∘ finCongr (card_eq π hν) from
        rfl, ← Multiset.map_map, Multiset.map_univ_val_equiv]
      exact t.2
    have := congrArg (Multiset.map π) h1
    rw [Multiset.map_map] at this
    exact this.trans hν⟩

@[simp] theorem down_lbl (t : Seq ν') (a : Fin (Multiset.card ν)) :
    (down π hν t).lbl a = π (t.lbl (Fin.cast (card_eq π hν) a)) := rfl

theorem sadj_cast {m m' : ℕ} (h : m = m') (j : ℕ) (a : Fin m) :
    sadj m' j (Fin.cast h a) = Fin.cast h (sadj m j a) := by
  subst h; rfl

theorem sadj_symm_cast {m m' : ℕ} (h : m = m') (j : ℕ) (a : Fin m) :
    (sadj m' j).symm (Fin.cast h a) = Fin.cast h ((sadj m j).symm a) := by
  subst h; rfl

theorem down_sadj_smul (j : ℕ) (t : Seq ν') :
    down π hν (sadj (Multiset.card ν') j • t) = sadj (Multiset.card ν) j • down π hν t := by
  apply Subtype.ext
  funext a
  simp only [Seq.smul_apply, down_lbl, Seq.lbl]
  congr 2
  rw [sadj_symm_cast]

theorem sadj_smul_down_eq (t : Seq ν') {j : ℕ} (h : j + 1 < Multiset.card ν)
    (heq : (down π hν t).lbl ⟨j, by omega⟩ = (down π hν t).lbl ⟨j + 1, h⟩) :
    sadj (Multiset.card ν) j • down π hν t = down π hν t := by
  apply Subtype.ext
  funext a
  simp only [Seq.smul_apply]
  show (down π hν t).lbl ((sadj (Multiset.card ν) j).symm a) = (down π hν t).lbl a
  rw [← Equiv.Perm.inv_def, sadj_inv]
  by_cases h1 : (a : ℕ) = j
  · rw [show a = ⟨j, by omega⟩ from Fin.ext h1, sadj_apply_left h]; exact heq.symm
  · by_cases h2 : (a : ℕ) = j + 1
    · rw [show a = ⟨j + 1, h⟩ from Fin.ext h2, sadj_apply_right h]; exact heq
    · rw [sadj_apply_of_ne a h1 h2]

/-- The substitution `x_a ↦ ϖ_{t_a}(y_a)` on the summand of a sequence `t ∈ Seq ν̃`. -/
noncomputable def substAt (t : Seq ν') :
    MvPolynomial (Fin (Multiset.card ν)) k →ₐ[k] MvPolynomial (Fin (Multiset.card ν')) k :=
  aeval fun a => pwAt pw (t.lbl (Fin.cast (card_eq π hν) a)) (Fin.cast (card_eq π hν) a)

@[simp] theorem substAt_X (t : Seq ν') (a : Fin (Multiset.card ν)) :
    substAt π pw hν t (X a) =
      pwAt pw (t.lbl (Fin.cast (card_eq π hν) a)) (Fin.cast (card_eq π hν) a) :=
  aeval_X _ _

/-- Webster's `γ_P : Pol_ν → Pol_ν̃` (label `com0new`, on the polynomial representations):
the summand of `t ∈ Seq ν̃` is the substitution applied to the summand of `π ∘ t`. -/
noncomputable def polySubst : Pol k ν →ₗ[k] Pol k ν' :=
  LinearMap.pi fun t => (substAt π pw hν t).toLinearMap ∘ₗ LinearMap.proj (down π hν t)

theorem polySubst_apply (p : Pol k ν) (t : Seq ν') :
    polySubst π pw hν p t = substAt π pw hν t (p (down π hν t)) := rfl

/-- Substitution commutes with the swap of adjacent variables. -/
theorem substAt_rename_sadj (t : Seq ν') (j : ℕ) (f : MvPolynomial (Fin (Multiset.card ν)) k) :
    substAt π pw hν t (rename (sadj (Multiset.card ν) j) f) =
      rename (sadj (Multiset.card ν') j) (substAt π pw hν (sadj (Multiset.card ν') j • t) f) := by
  rw [substAt, substAt, aeval_rename, ← AlgHom.comp_apply, comp_aeval]
  congr 1
  ext1 a
  simp only [aeval_X, Function.comp_apply, pwAt, Seq.smul_apply]
  rw [← Polynomial.aeval_algHom_apply, rename_X, sadj_cast, sadj_symm_cast, ← Equiv.Perm.inv_def,
    sadj_inv]

@[simp] theorem polySubst_opX (a : Fin (Multiset.card ν)) (p : Pol k ν) (t : Seq ν') :
    polySubst π pw hν (opX a p) t =
      pwAt pw (t.lbl (Fin.cast (card_eq π hν) a)) (Fin.cast (card_eq π hν) a) *
        polySubst π pw hν p t := by
  rw [polySubst_apply, opX_apply, map_mul, substAt_X, polySubst_apply]

variable [DecidableEq I]

@[simp] theorem polySubst_opE (i : Seq ν) (p : Pol k ν) (t : Seq ν') :
    polySubst π pw hν (opE i p) t = if down π hν t = i then polySubst π pw hν p t else 0 := by
  rw [polySubst_apply, opE_apply]
  split_ifs <;> simp [polySubst_apply, *]

theorem polySubst_opΨ (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ} (h : j + 1 < Multiset.card ν)
    (p : Pol k ν) (t : Seq ν') :
    polySubst π pw hν (opΨ P j p) t =
      substAt π pw hν t (crossComp P j h (down π hν (sadj (Multiset.card ν') j • t))
        (p (down π hν (sadj (Multiset.card ν') j • t)))) := by
  rw [polySubst_apply, opΨ_apply P j h, down_sadj_smul]

omit [DecidableEq I] in
theorem down_sadj_lbl_left (t : Seq ν') {j : ℕ} (h : j + 1 < Multiset.card ν) :
    (down π hν (sadj (Multiset.card ν') j • t)).lbl ⟨j, by omega⟩ = (down π hν t).lbl ⟨j + 1, h⟩ := by
  rw [down_sadj_smul]
  show (down π hν t).lbl ((sadj (Multiset.card ν) j).symm _) = _
  rw [← Equiv.Perm.inv_def, sadj_inv, sadj_apply_left h]

omit [DecidableEq I] in
theorem down_sadj_lbl_right (t : Seq ν') {j : ℕ} (h : j + 1 < Multiset.card ν) :
    (down π hν (sadj (Multiset.card ν') j • t)).lbl ⟨j + 1, h⟩ = (down π hν t).lbl ⟨j, by omega⟩ := by
  rw [down_sadj_smul]
  show (down π hν t).lbl ((sadj (Multiset.card ν) j).symm _) = _
  rw [← Equiv.Perm.inv_def, sadj_inv, sadj_apply_right h]

/-- `γ_P` and a crossing of strands with distinct labels: the factor `P` is substituted and
the variables are swapped. -/
theorem polySubst_opΨ_of_ne (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ}
    (h : j + 1 < Multiset.card ν) (p : Pol k ν) (t : Seq ν')
    (hne : (down π hν t).lbl ⟨j, by omega⟩ ≠ (down π hν t).lbl ⟨j + 1, h⟩) :
    polySubst π pw hν (opΨ P j p) t =
      substAt π pw hν t (rename ![(⟨j, by omega⟩ : Fin (Multiset.card ν)), ⟨j + 1, h⟩]
          (P ((down π hν t).lbl ⟨j + 1, h⟩) ((down π hν t).lbl ⟨j, by omega⟩))) *
        rename (sadj (Multiset.card ν') j) (polySubst π pw hν p (sadj (Multiset.card ν') j • t)) := by
  rw [polySubst_opΨ π pw hν P h, crossComp, ite_eq_right_of_eq_false _ _ (eq_false (by
      rw [down_sadj_lbl_left π hν t h, down_sadj_lbl_right π hν t h]; exact fun e => hne e.symm)),
    LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul,
    substAt_rename_sadj, down_sadj_lbl_left π hν t h, down_sadj_lbl_right π hν t h, polySubst_apply]

/-- `γ_P` and a crossing of strands with equal labels (the divided difference), multiplied
by the substituted difference of the two variables. -/
theorem polySubst_opΨ_of_eq (P : I → I → MvPolynomial (Fin 2) k) {j : ℕ}
    (h : j + 1 < Multiset.card ν) (p : Pol k ν) (t : Seq ν')
    (heq : (down π hν t).lbl ⟨j, by omega⟩ = (down π hν t).lbl ⟨j + 1, h⟩) :
    (substAt π pw hν t (X ⟨j, by omega⟩) - substAt π pw hν t (X ⟨j + 1, h⟩)) *
        polySubst π pw hν (opΨ P j p) t =
      polySubst π pw hν p t -
        rename (sadj (Multiset.card ν') j) (polySubst π pw hν p (sadj (Multiset.card ν') j • t)) := by
  have hs : down π hν (sadj (Multiset.card ν') j • t) = down π hν t := by
    rw [down_sadj_smul, sadj_smul_down_eq π hν t h heq]
  rw [polySubst_opΨ π pw hν P h, hs, crossComp, ite_eq_left_of_eq_true _ _ (eq_true heq), ← map_sub, ← map_mul,
    ddiff_spec (by simp [Fin.ext_iff]), map_sub, polySubst_apply, polySubst_apply, hs,
    show Equiv.swap (⟨j, by omega⟩ : Fin (Multiset.card ν)) ⟨j + 1, h⟩ = sadj _ j by
      simp [sadj, h], substAt_rename_sadj]

/-! ### Density and injectivity over a field -/

section Field

variable {K : Type*} [Field K] (pw : J → Polynomial K)

omit [DecidableEq I] in
/-- On the summand of `t`, `γ_P` is the coordinatewise substitution `subst` (with variables
renamed along `card ν = card ν̃`). -/
theorem substAt_eq_subst (t : Seq ν') (f : MvPolynomial (Fin (Multiset.card ν)) K) :
    substAt π pw hν t f = subst (fun b => pw (t.lbl b)) (rename (Fin.cast (card_eq π hν)) f) := by
  rw [substAt, subst, aeval_rename]
  rfl

omit [DecidableEq I] in
theorem substAt_injective (hpw1 : ∀ j, (pw j).coeff 1 ≠ 0) (t : Seq ν') :
    Function.Injective (substAt π pw hν t) := by
  intro f g hfg
  rw [substAt_eq_subst, substAt_eq_subst] at hfg
  exact rename_injective _ (Fin.cast_injective _) (subst_injective _ (fun b => hpw1 _) hfg)

omit [DecidableEq I] in
/-- `γ_P` is injective as soon as every sequence of weight `ν` lifts to weight `ν̃`. -/
theorem polySubst_injective (hpw1 : ∀ j, (pw j).coeff 1 ≠ 0)
    (hlift : ∀ i : Seq ν, ∃ t : Seq ν', down π hν t = i) :
    Function.Injective (polySubst π pw hν) := by
  intro p q hpq
  funext i
  obtain ⟨t, rfl⟩ := hlift i
  exact substAt_injective π hν pw hpw1 t (congrFun hpq t)

omit [DecidableEq I] in
/-- Density of the image of `γ_P` (Webster, proof of Lemma label `lem:gamma-homo`): modulo
monomials of total degree `≥ D`, every element of `Pol_ν̃` is in the image of `γ_P`, provided
the base points `ϖ_j(0)` of labels with the same image in `I` are distinct. -/
theorem exists_polySubst_coeff_sub_eq_zero (hpw1 : ∀ j, (pw j).coeff 1 ≠ 0)
    (hpw0 : ∀ j j', π j = π j' → (pw j).coeff 0 = (pw j').coeff 0 → j = j')
    (D : ℕ) (q : Pol K ν') :
    ∃ p : Pol K ν, ∀ t c, c.degree < D → (polySubst π pw hν p t - q t).coeff c = 0 := by
  have key : ∀ i : Seq ν, ∃ f : MvPolynomial (Fin (Multiset.card ν')) K,
      ∀ t : {t : Seq ν' // down π hν t = i}, ∀ c : Fin (Multiset.card ν') →₀ ℕ, c.degree < D →
        (subst (fun b => pw (t.1.lbl b)) f - q t.1).coeff c = 0 := by
    intro i
    have hinj : Function.Injective fun (t : {t : Seq ν' // down π hν t = i})
        (b : Fin (Multiset.card ν')) => (pw (t.1.lbl b)).coeff 0 := by
      rintro ⟨t, ht⟩ ⟨t', ht'⟩ htt'
      have hlbl : t.lbl = t'.lbl := by
        funext b
        have h1 : (down π hν t).lbl (Fin.cast (card_eq π hν).symm b) =
            (down π hν t').lbl (Fin.cast (card_eq π hν).symm b) := by rw [ht, ht']
        rw [down_lbl, down_lbl, Fin.cast_cast, Fin.cast_eq_self] at h1
        exact hpw0 _ _ h1 (congrFun htt' b)
      exact Subtype.ext (Subtype.ext hlbl)
    exact exists_subst_coeff_sub_eq_zero (σ := Fin (Multiset.card ν'))
      (fun (t : {t : Seq ν' // down π hν t = i}) b => pw (t.1.lbl b)) (fun _ _ => hpw1 _) hinj D
      (fun t => q t.1)
  choose f hf using key
  refine ⟨fun i => rename (Fin.cast (card_eq π hν).symm) (f i), fun t c hc => ?_⟩
  rw [polySubst_apply, substAt_eq_subst, rename_rename]
  have : (Fin.cast (card_eq π hν)) ∘ (Fin.cast (card_eq π hν).symm) = id := by
    funext b; simp
  rw [this, rename_id_apply]
  exact hf _ ⟨t, rfl⟩ c hc

end Field

end Categorification.KLR.Unfurling
