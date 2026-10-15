/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Cyclotomic

/-!
# Reindexing KLR algebras along an injection of labels

For an injective map of labels `f : J → I`, KLR data `Q` on `I` and a weight `ν' : Multiset J`,
the KLR algebra of the pulled back data `Q ∘ (f × f)` in weight `ν'` is isomorphic to the KLR
algebra of `Q` in weight `ν'.map f`: a sequence `𝐣` of weight `ν'` goes to `f ∘ 𝐣`, and since
`f` is injective every sequence of weight `ν'.map f` arises in this way exactly once. The
isomorphism sends `e(𝐣) ↦ e(f ∘ 𝐣)`, `x_a ↦ x_a` and `ψ_k ↦ ψ_k`. The same holds for the
cyclotomic quotients (Kang–Kashiwara, arXiv:1102.4677v4, §4.1, Definition 4.1) with
cyclotomic polynomials `a ∘ f`.

This is a step toward the nondegeneracy hypothesis of Khovanov–Lauda, *A categorification of
quantum `sl(n)`*, arXiv:0807.3250v1 (KL III), Theorem 1.2, along Webster, *Unfurling
Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the theorem with label
`nondegenerate`: there a cyclotomic KLR algebra whose strands carry finitely many generic labels
of the unfurled index set is compared with the cyclotomic quotient of the unfurled KLR algebra
on those labels, on which the parameters are `1` (`Unfurling.GenericLabels`); the restriction
of the labels to finitely many generic ones is a reindexing in the sense of this file.

Both directions are instances of one construction, `KLRAlgebra.relabelHom`, attached to a
`SeqRelabel`: a bijection of sequences of the same length compatible with the adjacent
transpositions, with equality of labels and with the parameters `Q`.

## Main definitions and results

* `Seq.mapEquiv hf ν' : Seq ν' ≃ Seq (ν'.map f)`, `𝐣 ↦ f ∘ 𝐣`.
* `KLRAlgebra.reindexEquiv hf Q ν' :
    KLRAlgebra k (fun a b => Q (f a) (f b)) ν' ≃ₐ[k] KLRAlgebra k Q (ν'.map f)`, with simp
  lemmas `reindexEquiv_e`, `reindexEquiv_x`, `reindexEquiv_ψ` and their `symm` versions.
* `CycKLR.reindexEquiv hf Q ν' a :
    CycKLR k (fun a b => Q (f a) (f b)) (a ∘ f) ν' ≃ₐ[k] CycKLR k Q a (ν'.map f)`, with the
  same simp lemmas.
-/

namespace Categorification.KLR

open Equiv TypeA

variable {k : Type*} [CommRing k]

/-- Adjacent transpositions commute with reindexing positions along `m = n`. -/
theorem cast_sadj_symm {m n : ℕ} (h : m = n) (j : ℕ) (a : Fin m) :
    Fin.cast h ((sadj m j).symm a) = (sadj n j).symm (Fin.cast h a) := by
  subst h; rfl

/-! ### Relabelling sequences -/

variable {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]

variable (k) in
/-- A relabelling of the sequences of weight `ν₁` (for data `Q₁`) by those of weight `ν₂` (for
data `Q₂`): a bijection `σ : Seq ν₁ ≃ Seq ν₂` between sequences of the same length which
commutes with the adjacent transpositions, preserves equality of labels at any two positions,
and carries the parameters `Q₁` at two distinct labels of `𝐢` to the parameters `Q₂` at the
corresponding labels of `σ 𝐢`. -/
structure SeqRelabel (Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k)
    (Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k) (ν₁ : Multiset I₁) (ν₂ : Multiset I₂) where
  /-- The two weights have the same number of strands. -/
  card_eq : Multiset.card ν₁ = Multiset.card ν₂
  /-- The bijection of sequences. -/
  equiv : Seq ν₁ ≃ Seq ν₂
  /-- `σ` commutes with the adjacent transpositions. -/
  equiv_smul (j : ℕ) (i : Seq ν₁) :
    equiv (sadj (Multiset.card ν₁) j • i) = sadj (Multiset.card ν₂) j • equiv i
  /-- `σ` preserves equality of labels. -/
  lbl_eq_iff (i : Seq ν₁) (a b : Fin (Multiset.card ν₁)) :
    (equiv i).lbl (Fin.cast card_eq a) = (equiv i).lbl (Fin.cast card_eq b) ↔ i.lbl a = i.lbl b
  /-- `σ` carries the parameters `Q₁` to `Q₂`. -/
  Q_eq (i : Seq ν₁) (a b : Fin (Multiset.card ν₁)) (h : i.lbl a ≠ i.lbl b) :
    Q₂ ((equiv i).lbl (Fin.cast card_eq a)) ((equiv i).lbl (Fin.cast card_eq b)) =
      Q₁ (i.lbl a) (i.lbl b)

namespace SeqRelabel

omit [DecidableEq I₁] [DecidableEq I₂]

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)

/-- The inverse relabelling. -/
def symm : SeqRelabel k Q₂ Q₁ ν₂ ν₁ where
  card_eq := R.card_eq.symm
  equiv := R.equiv.symm
  equiv_smul j i := by
    obtain ⟨i, rfl⟩ := R.equiv.surjective i
    rw [R.equiv.symm_apply_eq, ← R.equiv_smul, Equiv.symm_apply_apply]
  lbl_eq_iff i a b := by
    obtain ⟨i, rfl⟩ := R.equiv.surjective i
    rw [Equiv.symm_apply_apply, ← R.lbl_eq_iff]
    simp
  Q_eq i a b h := by
    obtain ⟨i, rfl⟩ := R.equiv.surjective i
    rw [Equiv.symm_apply_apply]
    have h' : i.lbl (Fin.cast R.card_eq.symm a) ≠ i.lbl (Fin.cast R.card_eq.symm b) := by
      rwa [Ne, ← R.lbl_eq_iff, Fin.cast_cast, Fin.cast_cast, Fin.cast_eq_self, Fin.cast_eq_self]
    have := R.Q_eq _ _ _ h'
    simp only [Fin.cast_cast, Fin.cast_eq_self] at this
    exact this.symm

@[simp] theorem symm_equiv : R.symm.equiv = R.equiv.symm := rfl

@[simp] theorem symm_symm : R.symm.symm = R := rfl

/-- The labels at positions `j`, `j'` of `σ 𝐢` agree iff those of `𝐢` do. -/
theorem lbl_mk_eq_iff (i : Seq ν₁) (j j' : ℕ) (hj : j < Multiset.card ν₁)
    (hj' : j' < Multiset.card ν₁) :
    (R.equiv i).lbl ⟨j, R.card_eq ▸ hj⟩ = (R.equiv i).lbl ⟨j', R.card_eq ▸ hj'⟩ ↔
      i.lbl ⟨j, hj⟩ = i.lbl ⟨j', hj'⟩ :=
  R.lbl_eq_iff i ⟨j, hj⟩ ⟨j', hj'⟩

theorem Q_mk_eq (i : Seq ν₁) (j j' : ℕ) (hj : j < Multiset.card ν₁)
    (hj' : j' < Multiset.card ν₁) (h : i.lbl ⟨j, hj⟩ ≠ i.lbl ⟨j', hj'⟩) :
    Q₂ ((R.equiv i).lbl ⟨j, R.card_eq ▸ hj⟩) ((R.equiv i).lbl ⟨j', R.card_eq ▸ hj'⟩) =
      Q₁ (i.lbl ⟨j, hj⟩) (i.lbl ⟨j', hj'⟩) :=
  R.Q_eq i ⟨j, hj⟩ ⟨j', hj'⟩ h

end SeqRelabel

namespace KLRAlgebra

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)

/-- The images of the generators of `R(ν₁)` under a relabelling. -/
noncomputable def relabelGen : Gen ν₁ → KLRAlgebra k Q₂ ν₂
  | .idem i => e (R.equiv i)
  | .dot a => x (Fin.cast R.card_eq a)
  | .cross j => ψ j

/-- The free algebra on the generators of `R(ν₁)` maps to `R(ν₂)` through `relabelGen`. -/
noncomputable def relabelFree : FreeAlgebra k (Gen ν₁) →ₐ[k] KLRAlgebra k Q₂ ν₂ :=
  FreeAlgebra.lift k (relabelGen R)

theorem relabelFree_rel ⦃u v : FreeAlgebra k (Gen ν₁)⦄ (h : Rel k Q₁ ν₁ u v) :
    relabelFree R u = relabelFree R v := by
  have hfe : ∀ i, relabelFree R (fe k ν₁ i) = e (R.equiv i) := fun i =>
    FreeAlgebra.lift_ι_apply _ _
  have hfx : ∀ a, relabelFree R (fx k ν₁ a) = x (Fin.cast R.card_eq a) := fun a =>
    FreeAlgebra.lift_ι_apply _ _
  have hfψ : ∀ j, relabelFree R (fψ k ν₁ j) = (ψ j : KLRAlgebra k Q₂ ν₂) := fun j =>
    FreeAlgebra.lift_ι_apply _ _
  have hev {n : ℕ} (y : Fin n → FreeAlgebra k (Gen ν₁)) (p : MvPolynomial (Fin n) k) :
      relabelFree R (ncEval y p) = ncEval (fun a => relabelFree R (y a)) p := by
    simp only [ncEval, Finsupp.sum, map_sum, map_mul, AlgHom.commutes, map_list_prod,
      List.map_ofFn, Function.comp_def, map_pow]
  have hc := R.card_eq
  cases h with
  | idem_mul i j =>
    rw [map_mul, hfe, hfe, e_mul_e]
    simp only [R.equiv.injective.eq_iff]
    split_ifs <;> simp [hfe]
  | idem_sum =>
    rw [map_sum, map_one]
    simp only [hfe]
    rw [R.equiv.sum_comp (fun i => (e i : KLRAlgebra k Q₂ ν₂)), sum_e]
  | dot_idem a i => rw [map_mul, map_mul, hfe, hfx, x_mul_e]
  | cross_idem j i =>
    rw [map_mul, map_mul, hfe, hfe, hfψ, ψ_mul_e, R.equiv_smul]
  | cross_zero j h => rw [map_zero, hfψ, ψ_eq_zero j (by omega)]
  | dot_dot a b => rw [map_mul, map_mul, hfx, hfx, x_mul_x]
  | cross_cross j l h => rw [map_mul, map_mul, hfψ, hfψ, ψ_mul_ψ j l h]
  | dot_cross a j h₁ h₂ =>
    rw [map_mul, map_mul, hfx, hfψ, x_mul_ψ _ j (by simpa using h₁) (by simpa using h₂)]
  | dot_cross_left j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe]
    have := dot_cross_left (Q := Q₂) j (by omega) (R.equiv i)
    simp only [Fin.cast_mk] at this ⊢
    rw [this]
    simp only [R.lbl_mk_eq_iff i j (j + 1) (by omega) h]
    split_ifs <;> simp [hfe]
  | dot_cross_right j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe]
    have := dot_cross_right (Q := Q₂) j (by omega) (R.equiv i)
    simp only [Fin.cast_mk] at this ⊢
    rw [this]
    simp only [R.lbl_mk_eq_iff i j (j + 1) (by omega) h]
    split_ifs <;> simp [hfe]
  | cross_sq j h i =>
    rw [map_mul, map_mul, hfψ, hfe, ψ_sq j (by omega) (R.equiv i)]
    simp only [R.lbl_mk_eq_iff i j (j + 1) (by omega) h]
    split_ifs with hl
    · simp
    · rw [map_mul, hfe, hev, R.Q_mk_eq i _ _ _ _ hl]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
  | braid j h i =>
    rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul, hfψ, hfψ, hfe,
      braid j (by omega) (R.equiv i)]
    simp only [ne_eq, R.lbl_mk_eq_iff i j (j + 2) (by omega) h,
      R.lbl_mk_eq_iff i j (j + 1) (by omega) (by omega)]
    split_ifs with hl
    · rw [map_mul, hfe, hev, R.Q_mk_eq i _ _ _ _ hl.2]
      congr 2
      funext a; fin_cases a <;> simp [hfx]
    · simp

/-- **The isomorphism attached to a relabelling** `σ : Seq ν₁ ≃ Seq ν₂`, as an algebra map
`R(ν₁) → R(ν₂)`: `e(𝐢) ↦ e(σ 𝐢)`, `x_a ↦ x_a`, `ψ_k ↦ ψ_k`. -/
noncomputable def relabelHom : KLRAlgebra k Q₁ ν₁ →ₐ[k] KLRAlgebra k Q₂ ν₂ :=
  RingQuot.liftAlgHom k ⟨relabelFree R, relabelFree_rel R⟩

theorem relabelHom_mk (u : FreeAlgebra k (Gen ν₁)) :
    relabelHom R (mk k Q₁ ν₁ u) = relabelFree R u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem relabelHom_e (i : Seq ν₁) : relabelHom R (e i) = e (R.equiv i) := by
  rw [e, relabelHom_mk]; exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem relabelHom_x (a : Fin (Multiset.card ν₁)) :
    relabelHom R (x a) = x (Fin.cast R.card_eq a) := by
  rw [x, relabelHom_mk]; exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem relabelHom_ψ (j : ℕ) : relabelHom R (ψ j) = (ψ j : KLRAlgebra k Q₂ ν₂) := by
  rw [ψ, relabelHom_mk]; exact FreeAlgebra.lift_ι_apply _ _

theorem relabelHom_symm_comp :
    (relabelHom R.symm).comp (relabelHom R) = AlgHom.id k (KLRAlgebra k Q₁ ν₁) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | idem i =>
    change relabelHom R.symm (relabelHom R (e i)) = e i
    simp
  | dot a =>
    change relabelHom R.symm (relabelHom R (x a)) = x a
    simp [SeqRelabel.symm]
  | cross j =>
    change relabelHom R.symm (relabelHom R (ψ j)) = ψ j
    simp

/-- **Relabelling** `R(ν₁) ≃ R(ν₂)` along `σ : Seq ν₁ ≃ Seq ν₂`. -/
noncomputable def relabelEquiv : KLRAlgebra k Q₁ ν₁ ≃ₐ[k] KLRAlgebra k Q₂ ν₂ :=
  AlgEquiv.ofAlgHom (relabelHom R) (relabelHom R.symm)
    (by simpa only [SeqRelabel.symm_symm] using relabelHom_symm_comp R.symm)
    (relabelHom_symm_comp R)

@[simp] theorem relabelEquiv_apply (u : KLRAlgebra k Q₁ ν₁) :
    relabelEquiv R u = relabelHom R u := rfl

@[simp] theorem relabelEquiv_symm_apply (u : KLRAlgebra k Q₂ ν₂) :
    (relabelEquiv R).symm u = relabelHom R.symm u := rfl

end KLRAlgebra

/-! ### Relabelling cyclotomic quotients -/

namespace CycKLR

open KLRAlgebra Polynomial

variable {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)
  {a₁ : I₁ → k[X]} {a₂ : I₂ → k[X]}
  (ha : ∀ (i : Seq ν₁) (h : 0 < Multiset.card ν₁),
    a₂ ((R.equiv i).lbl (Fin.cast R.card_eq ⟨0, h⟩)) = a₁ (i.lbl ⟨0, h⟩))

include ha in
theorem relabelHom_cycElt (i : Seq ν₁) :
    relabelHom R (cycElt Q₁ a₁ i) = cycElt Q₂ a₂ (R.equiv i) := by
  by_cases h : 0 < Multiset.card ν₁
  · have h₂ : 0 < Multiset.card ν₂ := R.card_eq ▸ h
    rw [cycElt_of_pos _ _ _ h, cycElt_of_pos _ _ _ h₂, map_mul, relabelHom_e,
      ← Polynomial.aeval_algHom_apply, relabelHom_x, ← ha i h]
    rfl
  · have h₂ : ¬ 0 < Multiset.card ν₂ := R.card_eq ▸ h
    simp only [cycElt, h, h₂, ↓reduceDIte, map_zero]

omit [DecidableEq I₁] [DecidableEq I₂] in
include ha in
/-- The cyclotomic compatibility of a relabelling passes to the inverse relabelling. -/
theorem relabel_symm_cyc (t : Seq ν₂) (h : 0 < Multiset.card ν₂) :
    a₁ ((R.symm.equiv t).lbl (Fin.cast R.symm.card_eq ⟨0, h⟩)) = a₂ (t.lbl ⟨0, h⟩) := by
  obtain ⟨i, rfl⟩ := R.equiv.surjective t
  have := ha i (R.card_eq ▸ h)
  simp only [SeqRelabel.symm_equiv, Equiv.symm_apply_apply]
  exact this.symm

/-- The relabelling `R(ν₁) → R(ν₂)` descends to the cyclotomic quotients when it matches the
cyclotomic polynomials of the first labels. -/
noncomputable def relabelHom : CycKLR k Q₁ a₁ ν₁ →ₐ[k] CycKLR k Q₂ a₂ ν₂ :=
  lift ((mk k Q₂ a₂ ν₂).comp (KLRAlgebra.relabelHom R)) fun i => by
    rw [AlgHom.comp_apply, relabelHom_cycElt R ha, mk_cycElt]

@[simp] theorem relabelHom_mk (u : KLRAlgebra k Q₁ ν₁) :
    relabelHom R ha (mk k Q₁ a₁ ν₁ u) = mk k Q₂ a₂ ν₂ (KLRAlgebra.relabelHom R u) :=
  lift_mk _ _ u

theorem relabelHom_symm_comp :
    (relabelHom R.symm (relabel_symm_cyc R ha)).comp (relabelHom R ha) =
      AlgHom.id k (CycKLR k Q₁ a₁ ν₁) := by
  apply algHom_ext
  ext u
  simp only [AlgHom.comp_apply, relabelHom_mk, AlgHom.id_apply]
  rw [← AlgHom.comp_apply (KLRAlgebra.relabelHom R.symm), KLRAlgebra.relabelHom_symm_comp]
  rfl

/-- **Relabelling** of cyclotomic quotients `R^{a₁}(ν₁) ≃ R^{a₂}(ν₂)`. -/
noncomputable def relabelEquiv : CycKLR k Q₁ a₁ ν₁ ≃ₐ[k] CycKLR k Q₂ a₂ ν₂ :=
  AlgEquiv.ofAlgHom (relabelHom R ha) (relabelHom R.symm (relabel_symm_cyc R ha))
    (by simpa only [SeqRelabel.symm_symm] using
      relabelHom_symm_comp R.symm (relabel_symm_cyc R ha))
    (relabelHom_symm_comp R ha)

@[simp] theorem relabelEquiv_mk (u : KLRAlgebra k Q₁ ν₁) :
    relabelEquiv R ha (mk k Q₁ a₁ ν₁ u) = mk k Q₂ a₂ ν₂ (KLRAlgebra.relabelHom R u) :=
  lift_mk _ _ u

@[simp] theorem relabelEquiv_symm_mk (u : KLRAlgebra k Q₂ ν₂) :
    (relabelEquiv R ha).symm (mk k Q₂ a₂ ν₂ u) =
      mk k Q₁ a₁ ν₁ (KLRAlgebra.relabelHom R.symm u) :=
  lift_mk _ _ u

end CycKLR

/-! ### Reindexing along an injection of labels -/

section Reindex

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {f : J → I}

namespace Seq

omit [DecidableEq I] [DecidableEq J]

variable (f) in
/-- The sequence `f ∘ 𝐣` of weight `ν'.map f` attached to a sequence `𝐣` of weight `ν'`. -/
def map {ν' : Multiset J} (i : Seq ν') : Seq (ν'.map f) :=
  ⟨f ∘ i.1 ∘ Fin.cast (Multiset.card_map f ν'), by
    have hu : (Finset.univ.val.map (Fin.cast (Multiset.card_map f ν'))) = Finset.univ.val :=
      Multiset.map_univ_val_equiv (finCongr (Multiset.card_map f ν'))
    rw [← Multiset.map_map, ← Multiset.map_map, hu, i.2]⟩

@[simp] theorem map_lbl {ν' : Multiset J} (i : Seq ν') (b : Fin (Multiset.card (ν'.map f))) :
    (map f i).lbl b = f (i.lbl (Fin.cast (Multiset.card_map f ν') b)) := rfl

theorem map_bijective (hf : Function.Injective f) (ν' : Multiset J) :
    Function.Bijective (map f (ν' := ν')) := by
  have hc := Multiset.card_map f ν'
  refine ⟨fun i i' h => Subtype.ext (funext fun a => hf ?_), fun t => ?_⟩
  · have := congrArg (fun s : Seq (ν'.map f) => s.lbl (Fin.cast hc.symm a)) h
    simpa using this
  · have hm : ∀ a, ∃ b ∈ ν', f b = t.lbl (Fin.cast hc.symm a) := fun a =>
      Multiset.mem_map.1 (t.mem _)
    choose g _ hg using hm
    refine ⟨⟨g, Multiset.map_injective hf ?_⟩, Subtype.ext (funext fun b => ?_)⟩
    · have hu : (Finset.univ.val.map (Fin.cast hc.symm)) = Finset.univ.val :=
        Multiset.map_univ_val_equiv (finCongr hc.symm)
      rw [Multiset.map_map, show f ∘ g = t.1 ∘ Fin.cast hc.symm from funext hg,
        ← Multiset.map_map, hu, t.2]
    · change f (g (Fin.cast hc b)) = t.1 b
      rw [hg]
      simp

/-- **Sequences along an injection**: `Seq ν' ≃ Seq (ν'.map f)`, `𝐣 ↦ f ∘ 𝐣`. -/
noncomputable def mapEquiv (hf : Function.Injective f) (ν' : Multiset J) :
    Seq ν' ≃ Seq (ν'.map f) :=
  Equiv.ofBijective _ (map_bijective hf ν')

@[simp] theorem mapEquiv_apply (hf : Function.Injective f) {ν' : Multiset J} (i : Seq ν') :
    mapEquiv hf ν' i = map f i := rfl

theorem map_mapEquiv_symm (hf : Function.Injective f) {ν' : Multiset J}
    (t : Seq (ν'.map f)) : map f ((mapEquiv hf ν').symm t) = t :=
  (mapEquiv hf ν').apply_symm_apply t

end Seq

variable (hf : Function.Injective f) (Q : I → I → MvPolynomial (Fin 2) k) (ν' : Multiset J)

/-- The relabelling `𝐣 ↦ f ∘ 𝐣` from the data `Q ∘ (f × f)` in weight `ν'` to the data `Q` in
weight `ν'.map f`. -/
noncomputable def SeqRelabel.ofInjective :
    SeqRelabel k (fun a b => Q (f a) (f b)) Q ν' (ν'.map f) where
  card_eq := (Multiset.card_map f ν').symm
  equiv := Seq.mapEquiv hf ν'
  equiv_smul j i := by
    apply Subtype.ext
    funext b
    change f (i.1 ((sadj _ j).symm (Fin.cast _ b))) = f (i.1 (Fin.cast _ ((sadj _ j).symm b)))
    rw [cast_sadj_symm]
  lbl_eq_iff i a b := by
    simp only [Seq.mapEquiv_apply, Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self, hf.eq_iff]
  Q_eq i a b _ := by
    simp only [Seq.mapEquiv_apply, Seq.map_lbl, Fin.cast_cast, Fin.cast_eq_self]

namespace KLRAlgebra

/-- **Reindexing along an injection of labels** `f : J → I`: the KLR algebra of the pulled
back data `Q ∘ (f × f)` in weight `ν'` is the KLR algebra of `Q` in weight `ν'.map f`, via
`e(𝐣) ↦ e(f ∘ 𝐣)`, `x_a ↦ x_a`, `ψ_k ↦ ψ_k`. -/
noncomputable def reindexEquiv :
    KLRAlgebra k (fun a b => Q (f a) (f b)) ν' ≃ₐ[k] KLRAlgebra k Q (ν'.map f) :=
  relabelEquiv (SeqRelabel.ofInjective hf Q ν')

variable {Q ν'}

@[simp] theorem reindexEquiv_e (i : Seq ν') :
    reindexEquiv hf Q ν' (e i) = e (Seq.map f i) := by
  simp [reindexEquiv, SeqRelabel.ofInjective]

@[simp] theorem reindexEquiv_x (a : Fin (Multiset.card ν')) :
    reindexEquiv hf Q ν' (x a) = x (Fin.cast (Multiset.card_map f ν').symm a) := by
  simp [reindexEquiv, SeqRelabel.ofInjective]

@[simp] theorem reindexEquiv_ψ (j : ℕ) :
    reindexEquiv hf Q ν' (ψ j) = ψ j := by
  simp [reindexEquiv]

@[simp] theorem reindexEquiv_symm_e (t : Seq (ν'.map f)) :
    (reindexEquiv hf Q ν').symm (e t) = e ((Seq.mapEquiv hf ν').symm t) := by
  simp [reindexEquiv, SeqRelabel.ofInjective]

@[simp] theorem reindexEquiv_symm_x (a : Fin (Multiset.card (ν'.map f))) :
    (reindexEquiv hf Q ν').symm (x a) = x (Fin.cast (Multiset.card_map f ν') a) := by
  simp [reindexEquiv, SeqRelabel.ofInjective, SeqRelabel.symm]

@[simp] theorem reindexEquiv_symm_ψ (j : ℕ) :
    (reindexEquiv hf Q ν').symm (ψ j) = ψ j := by
  simp [reindexEquiv]

end KLRAlgebra

namespace CycKLR

open KLRAlgebra Polynomial

variable (a : I → k[X])

/-- **Reindexing cyclotomic quotients along an injection of labels** `f : J → I`:
`R^{a ∘ f}(ν')` for the data `Q ∘ (f × f)` is `R^a(ν'.map f)` for the data `Q`. -/
noncomputable def reindexEquiv :
    CycKLR k (fun a b => Q (f a) (f b)) (a ∘ f) ν' ≃ₐ[k] CycKLR k Q a (ν'.map f) :=
  relabelEquiv (SeqRelabel.ofInjective hf Q ν') (a₁ := a ∘ f) (a₂ := a) fun i h => by
    simp [SeqRelabel.ofInjective]

variable {Q ν' a}

@[simp] theorem reindexEquiv_mk (u : KLRAlgebra k (fun a b => Q (f a) (f b)) ν') :
    reindexEquiv hf Q ν' a (mk k _ (a ∘ f) ν' u) =
      mk k Q a (ν'.map f) (KLRAlgebra.reindexEquiv hf Q ν' u) :=
  relabelEquiv_mk _ _ u

@[simp] theorem reindexEquiv_symm_mk (u : KLRAlgebra k Q (ν'.map f)) :
    (reindexEquiv hf Q ν' a).symm (mk k Q a (ν'.map f) u) =
      mk k _ (a ∘ f) ν' ((KLRAlgebra.reindexEquiv hf Q ν').symm u) :=
  relabelEquiv_symm_mk _ _ u

theorem reindexEquiv_e (i : Seq ν') :
    reindexEquiv hf Q ν' a (mk k _ (a ∘ f) ν' (e i)) = mk k Q a (ν'.map f) (e (Seq.map f i)) := by
  simp

theorem reindexEquiv_x (b : Fin (Multiset.card ν')) :
    reindexEquiv hf Q ν' a (mk k _ (a ∘ f) ν' (x b)) =
      mk k Q a (ν'.map f) (x (Fin.cast (Multiset.card_map f ν').symm b)) := by
  simp

theorem reindexEquiv_ψ (j : ℕ) :
    reindexEquiv hf Q ν' a (mk k _ (a ∘ f) ν' (ψ j)) = mk k Q a (ν'.map f) (ψ j) := by
  simp

theorem reindexEquiv_symm_e (t : Seq (ν'.map f)) :
    (reindexEquiv hf Q ν' a).symm (mk k Q a (ν'.map f) (e t)) =
      mk k _ (a ∘ f) ν' (e ((Seq.mapEquiv hf ν').symm t)) := by
  simp

theorem reindexEquiv_symm_x (b : Fin (Multiset.card (ν'.map f))) :
    (reindexEquiv hf Q ν' a).symm (mk k Q a (ν'.map f) (x b)) =
      mk k _ (a ∘ f) ν' (x (Fin.cast (Multiset.card_map f ν') b)) := by
  simp

theorem reindexEquiv_symm_ψ (j : ℕ) :
    (reindexEquiv hf Q ν' a).symm (mk k Q a (ν'.map f) (ψ j)) = mk k _ (a ∘ f) ν' (ψ j) := by
  simp

end CycKLR

end Reindex

end Categorification.KLR
