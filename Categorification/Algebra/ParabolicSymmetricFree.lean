/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.SymmetricFree

/-!
# Polynomials are free over invariants of Young subgroups (parabolic Artin theorem)

Let `V` be a finite set of variables with a labelling `lab : V → J`, and let
`G_lab = {g : Perm V // lab ∘ g = lab}` be the group of label-preserving permutations (a Young
subgroup: the product of the symmetric groups of the fibres of `lab`). Over any commutative ring
`k`, the polynomial ring `k[V]` is a free module over the invariants

  `labelInvariants k lab = {f | ∀ g, lab ∘ g = lab → rename g f = f}`

of rank `|G_lab| = ∏_c |lab⁻¹(c)|!`.

This is used in KL I (arXiv:0803.4121v2), §2.4, for Corollary 2.10: for `i ∈ Seq ν`,
`Sym(ν) ≅ k[x_1, …, x_m]^{G_i}` with `G_i` the stabiliser of `i`.

## Main results

* `Categorification.labelInvariants k lab` : the subalgebra of `G_lab`-invariants.
* `Categorification.exists_labelBasis` : a basis of `k[V]` over `labelInvariants k lab`
  indexed by a finite type of cardinality `|G_lab|`.
* `Categorification.labelInvariants_free`, `Categorification.labelInvariants_finite`,
  `Categorification.finrank_labelInvariants` : freeness, finiteness, and rank `|G_lab|`.
* `Categorification.exists_isInvBasis_label` : the elementary form (every polynomial is uniquely
  an invariant combination of the basis).

## Proof

* *One fibre* (`isInvBasis_fibre`). For a predicate `p` on `V`, the permutations fixing every `v`
  with `¬ p v` act on `k[V] ≅ K[x_a : a ∈ p]`, `K = k[v : ¬ p v]`, as the full symmetric group on
  the variables of `p`; Artin's theorem over the coefficient ring `K`
  (`staircase_indep_and_span`) gives the staircase monomials of the fibre as a basis.
* *Several fibres* (`IsInvBasis.mul`). If `k[V]` has invariant bases `b₁` over `H₁` and `b₂`
  over `H₂`, where `H₁` and `H₂` commute elementwise and `b₂` is `H₁`-invariant, then the
  products `b₁ i * b₂ j` form a basis over the `H₁ ∪ H₂`-invariants.
  Induction over the fibres gives a basis over the polynomials invariant under every fibre
  group.
* *Decomposition*: a label-preserving permutation is a product of permutations supported on
  single fibres (`labelPiece`), so invariance under all fibre groups is invariance under `G_lab`.
-/

namespace Categorification

open MvPolynomial Equiv Finset

universe u v

variable {k : Type u} [CommRing k] {V : Type v}

/-! ### Invariant bases -/

/-- `f` is invariant under every permutation in `H`. -/
def IsInvariant (H : Set (Perm V)) (f : MvPolynomial V k) : Prop :=
  ∀ g ∈ H, rename g f = f

namespace IsInvariant

variable {H : Set (Perm V)} {f g : MvPolynomial V k}

theorem zero : IsInvariant H (0 : MvPolynomial V k) := fun _ _ => map_zero _

theorem one : IsInvariant H (1 : MvPolynomial V k) := fun _ _ => map_one _

theorem sub (hf : IsInvariant H f) (hg : IsInvariant H g) : IsInvariant H (f - g) :=
  fun h hh => by rw [map_sub, hf h hh, hg h hh]

theorem mul (hf : IsInvariant H f) (hg : IsInvariant H g) : IsInvariant H (f * g) :=
  fun h hh => by rw [map_mul, hf h hh, hg h hh]

theorem union_iff {H₁ H₂ : Set (Perm V)} :
    IsInvariant (H₁ ∪ H₂) f ↔ IsInvariant H₁ f ∧ IsInvariant H₂ f :=
  ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun h g hg => hg.elim (h.1 g) (h.2 g)⟩

end IsInvariant

/-- `b` is a basis of `k[V]` over the `H`-invariant polynomials, in elementary form: every
polynomial is uniquely a combination `∑ i, g i * b i` with `H`-invariant coefficients. -/
structure IsInvBasis (H : Set (Perm V)) {ι : Type*} [Fintype ι] (b : ι → MvPolynomial V k) :
    Prop where
  indep : ∀ g : ι → MvPolynomial V k, (∀ i, IsInvariant H (g i)) → ∑ i, g i * b i = 0 →
    ∀ i, g i = 0
  span : ∀ p : MvPolynomial V k,
    ∃ g : ι → MvPolynomial V k, (∀ i, IsInvariant H (g i)) ∧ ∑ i, g i * b i = p

namespace IsInvBasis

variable {H : Set (Perm V)}

theorem reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] {b : ι → MvPolynomial V k}
    (hb : IsInvBasis H b) (e : ι' ≃ ι) : IsInvBasis H (b ∘ e) where
  indep g hg h i := by
    have := hb.indep (g ∘ e.symm) (fun i => hg _)
      (by rw [← h]; exact Fintype.sum_equiv e.symm _ _ fun i => by simp)
    simpa using this (e i)
  span p := by
    obtain ⟨g, hg, hgp⟩ := hb.span p
    exact ⟨g ∘ e, fun i => hg _, by rw [← hgp]; exact Fintype.sum_equiv e _ _ fun i => rfl⟩

theorem congr {ι : Type*} [Fintype ι] {b b' : ι → MvPolynomial V k} (hb : IsInvBasis H b)
    (h : ∀ i, b i = b' i) : IsInvBasis H b' := by
  rwa [← funext h]

theorem mono_eq {H' : Set (Perm V)} {ι : Type*} [Fintype ι] {b : ι → MvPolynomial V k}
    (hb : IsInvBasis H b) (hH : ∀ f : MvPolynomial V k, IsInvariant H f ↔ IsInvariant H' f) :
    IsInvBasis H' b where
  indep g hg := hb.indep g fun i => (hH _).2 (hg i)
  span p := by
    obtain ⟨g, hg, hgp⟩ := hb.span p
    exact ⟨g, fun i => (hH _).1 (hg i), hgp⟩

/-- The trivial basis over all of `k[V]` (no symmetry). -/
theorem empty : IsInvBasis (∅ : Set (Perm V)) (fun _ : Unit => (1 : MvPolynomial V k)) where
  indep g _ h i := by simpa using h
  span p := ⟨fun _ => p, fun _ _ hg => hg.elim, by simp⟩

/-- **Product of invariant bases.** If `b₁` is a basis over the `H₁`-invariants, `b₂` a basis
over the `H₂`-invariants consisting of `H₁`-invariant polynomials, and `H₁`, `H₂` commute
elementwise, then the products `b₁ i * b₂ j` form a basis over the `H₁ ∪ H₂`-invariants. -/
theorem mul {H₁ H₂ : Set (Perm V)} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b₁ : ι → MvPolynomial V k} {b₂ : κ → MvPolynomial V k}
    (h₁ : IsInvBasis H₁ b₁) (h₂ : IsInvBasis H₂ b₂) (hb₂ : ∀ j, IsInvariant H₁ (b₂ j))
    (hc : ∀ g₁ ∈ H₁, ∀ g₂ ∈ H₂, g₁ * g₂ = g₂ * g₁) :
    IsInvBasis (H₁ ∪ H₂) (fun p : ι × κ => b₁ p.1 * b₂ p.2) where
  indep g hg h := by
    simp only [IsInvariant.union_iff] at hg
    have h' : ∑ i, (∑ j, g (i, j) * b₂ j) * b₁ i = 0 := by
      rw [← h, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hinv : ∀ i, IsInvariant H₁ (∑ j, g (i, j) * b₂ j) := fun i σ hσ => by
      simp only [map_sum, map_mul, (hg _).1 σ hσ, hb₂ _ σ hσ]
    have h0 := h₁.indep _ hinv h'
    rintro ⟨i, j⟩
    exact h₂.indep (fun j => g (i, j)) (fun j => (hg _).2) (h0 i) j
  span p := by
    obtain ⟨g, hg, hgp⟩ := h₁.span p
    choose c hc₂ hcg using fun i => h₂.span (g i)
    have hc₁ : ∀ i j, IsInvariant H₁ (c i j) := by
      intro i j₀ σ hσ
      have hσ' : ∀ j, IsInvariant H₂ (rename σ (c i j)) := fun j τ hτ => by
        rw [rename_rename, ← Perm.coe_mul, ← hc σ hσ τ hτ, Perm.coe_mul, ← rename_rename,
          hc₂ i j τ hτ]
      have hsum : ∑ j, (rename σ (c i j) - c i j) * b₂ j = 0 := by
        simp only [sub_mul, Finset.sum_sub_distrib]
        have : ∑ j, rename σ (c i j) * b₂ j = rename σ (g i) := by
          rw [← hcg i, map_sum]
          simp only [map_mul, hb₂ _ σ hσ]
        rw [this, hg i σ hσ, hcg i, sub_self]
      exact sub_eq_zero.1 (h₂.indep _ (fun j => (hσ' j).sub (hc₂ i j)) hsum j₀)
    refine ⟨fun q => c q.1 q.2, fun q => IsInvariant.union_iff.2 ⟨hc₁ _ _, hc₂ _ _⟩, ?_⟩
    rw [← hgp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hcg i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

end IsInvBasis

/-! ### One fibre -/

section Fibre

variable (p : V → Prop) [DecidablePred p]

/-- The permutations fixing every variable outside `p`. -/
def fibreGroup : Set (Perm V) := {g | ∀ v, ¬ p v → g v = v}

variable {p}

theorem fibreGroup_iff {g : Perm V} (hg : g ∈ fibreGroup p) (v : V) : p (g v) ↔ p v := by
  by_cases hv : p v
  · simp only [hv, iff_true]
    by_contra h
    have := hg _ h
    rw [g.injective this] at h
    exact h hv
  · rw [hg v hv]

variable [Fintype V]

variable (p) in
/-- `V ≃ Fin n ⊕ {v // ¬ p v}`, enumerating the fibre `p` by `Fintype.equivFin`. -/
noncomputable def fibreSplit : V ≃ Fin (Fintype.card {v // p v}) ⊕ {v // ¬ p v} :=
  (sumCompl p).symm.trans (sumCongr (Fintype.equivFin _) (Equiv.refl _))

theorem fibreSplit_of_pos {v : V} (h : p v) :
    fibreSplit p v = Sum.inl (Fintype.equivFin _ ⟨v, h⟩) := by
  simp [fibreSplit, sumCompl_apply_symm_of_pos p v h]

theorem fibreSplit_of_neg {v : V} (h : ¬ p v) : fibreSplit p v = Sum.inr ⟨v, h⟩ := by
  simp [fibreSplit, sumCompl_apply_symm_of_neg p v h]

theorem fibreSplit_symm_inl (a : Fin (Fintype.card {v // p v})) :
    (fibreSplit p).symm (Sum.inl a) = ((Fintype.equivFin {v // p v}).symm a : V) := by
  simp [fibreSplit]

theorem fibreSplit_symm_inr (w : {v // ¬ p v}) : (fibreSplit p).symm (Sum.inr w) = (w : V) := by
  simp [fibreSplit]

variable (k p) in
/-- `k[V] ≃ K[x_a : a ∈ p]` with `K = k[v : ¬ p v]`. -/
noncomputable def fibreEquiv : MvPolynomial V k ≃ₐ[k]
    MvPolynomial (Fin (Fintype.card {v // p v})) (MvPolynomial {v // ¬ p v} k) :=
  (renameEquiv k (fibreSplit p)).trans (sumAlgEquiv k _ _)

variable (p) in
/-- A permutation of the fibre `p`, extended by the identity. -/
noncomputable def fibreExt (σ : Perm (Fin (Fintype.card {v // p v}))) : Perm V :=
  (fibreSplit p).trans ((sumCongr σ (Equiv.refl _)).trans (fibreSplit p).symm)

theorem fibreExt_mem (σ : Perm (Fin (Fintype.card {v // p v}))) :
    fibreExt p σ ∈ fibreGroup p := fun v hv => by
  simp [fibreExt, fibreSplit_of_neg hv, fibreSplit_symm_inr]

theorem exists_fibreExt_eq {g : Perm V} (hg : g ∈ fibreGroup p) :
    ∃ σ, fibreExt p σ = g := by
  refine ⟨(Fintype.equivFin {v // p v}).permCongr (g.subtypePerm fun v => (fibreGroup_iff hg v).symm), ?_⟩
  ext v
  by_cases hv : p v
  · simp [fibreExt, fibreSplit_of_pos hv, fibreSplit_symm_inl, Equiv.permCongr_apply]
  · simp [fibreExt, fibreSplit_of_neg hv, fibreSplit_symm_inr, hg v hv]

theorem sumAlgEquiv_X_inl {S W : Type*} (a : S) :
    sumAlgEquiv k S W (X (Sum.inl a)) = X a :=
  sumToIter_Xl _ _ _ _

theorem sumAlgEquiv_X_inr {S W : Type*} (b : W) :
    sumAlgEquiv k S W (X (Sum.inr b)) = C (X b) :=
  sumToIter_Xr _ _ _ _

theorem sumAlgEquiv_rename_sumCongr {S W : Type*} (σ : Perm S) (q : MvPolynomial (S ⊕ W) k) :
    sumAlgEquiv k S W (rename (sumCongr σ (Equiv.refl W)) q) = rename σ (sumAlgEquiv k S W q) := by
  have : ((sumAlgEquiv k S W).toAlgHom.comp (rename (sumCongr σ (Equiv.refl W)))) =
      ((rename σ).restrictScalars k).comp (sumAlgEquiv k S W).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro (a | b)
    · simp [sumAlgEquiv_X_inl]
    · simp [sumAlgEquiv_X_inr]
  exact congrArg (fun φ : MvPolynomial (S ⊕ W) k →ₐ[k] _ => φ q) this

theorem fibreEquiv_rename_fibreExt (σ : Perm (Fin (Fintype.card {v // p v})))
    (f : MvPolynomial V k) :
    fibreEquiv k p (rename (fibreExt p σ) f) = rename σ (fibreEquiv k p f) := by
  simp only [fibreEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename]
  rw [← sumAlgEquiv_rename_sumCongr, rename_rename]
  have hcomp : (⇑(fibreSplit p) ∘ ⇑(fibreExt p σ)) =
      ⇑(sumCongr σ (Equiv.refl {v // ¬ p v})) ∘ ⇑(fibreSplit p) := by
    funext v; simp [fibreExt]
  rw [hcomp]

theorem fibreEquiv_stair (u : Fin (Fintype.card {v // p v}) → ℕ) :
    fibreEquiv k p (∏ a, X ((Fintype.equivFin {v // p v}).symm a : V) ^ u a) =
      stairMonomial (MvPolynomial {v // ¬ p v} k) u := by
  simp only [fibreEquiv, AlgEquiv.trans_apply, renameEquiv_apply, map_prod, map_pow, rename_X,
    stairMonomial]
  refine Finset.prod_congr rfl fun a _ => ?_
  have h := ((Fintype.equivFin {v // p v}).symm a).2
  rw [fibreSplit_of_pos h]
  simp [sumAlgEquiv_X_inl]

theorem isInvariant_fibreGroup_iff {f : MvPolynomial V k} :
    IsInvariant (fibreGroup p) f ↔ (fibreEquiv k p f).IsSymmetric := by
  constructor
  · intro h σ
    rw [← fibreEquiv_rename_fibreExt, h _ (fibreExt_mem σ)]
  · intro h g hg
    obtain ⟨σ, rfl⟩ := exists_fibreExt_eq hg
    apply (fibreEquiv k p).injective
    rw [fibreEquiv_rename_fibreExt, h σ]

variable (k p) in
/-- **Artin's theorem for one fibre**: the staircase monomials in the variables of `p` form a
basis of `k[V]` over the polynomials invariant under all permutations of `p`. -/
theorem isInvBasis_fibre :
    IsInvBasis (fibreGroup p)
      (fun u : {u : Fin (Fintype.card {v // p v}) → ℕ // ∀ a, u a ≤ a} =>
        (∏ a, X ((Fintype.equivFin {v // p v}).symm a : V) ^ u.1 a : MvPolynomial V k)) where
  indep g hg h u := by
    have h' := congrArg (fibreEquiv k p) h
    simp only [map_sum, map_mul, fibreEquiv_stair, map_zero] at h'
    have := (staircase_indep_and_span _ (MvPolynomial {v // ¬ p v} k)).1 _
      (fun u => isInvariant_fibreGroup_iff.1 (hg u)) h' u
    exact (fibreEquiv k p).injective (by rw [this, map_zero])
  span q := by
    obtain ⟨G, hG, hGq⟩ :=
      (staircase_indep_and_span _ (MvPolynomial {v // ¬ p v} k)).2 (fibreEquiv k p q)
    refine ⟨fun u => (fibreEquiv k p).symm (G u), fun u => ?_, ?_⟩
    · rw [isInvariant_fibreGroup_iff, AlgEquiv.apply_symm_apply]; exact hG u
    · apply (fibreEquiv k p).injective
      simp only [map_sum, map_mul, fibreEquiv_stair, AlgEquiv.apply_symm_apply, hGq]

end Fibre

/-! ### Several fibres -/

section Label

variable {J : Type*} [DecidableEq J] (lab : V → J)

theorem fibreGroup_commute {c c' : J} (hcc : c ≠ c') {g g' : Perm V}
    (hg : g ∈ fibreGroup (lab · = c)) (hg' : g' ∈ fibreGroup (lab · = c')) :
    g * g' = g' * g := by
  ext v
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases hv : lab v = c
  · have hv' : lab v ≠ c' := hv ▸ hcc
    have h1 : lab (g v) = c := (fibreGroup_iff hg v).2 hv
    rw [hg' v hv', hg' (g v) (by show ¬ lab (g v) = c'; rw [h1]; exact hcc)]
  · rw [hg v hv]
    have : lab (g' v) ≠ c := by
      by_cases hv' : lab v = c'
      · rw [(fibreGroup_iff hg' v).2 hv']; exact hcc.symm
      · rwa [hg' v hv']
    rw [hg _ this]

/-- The union of the fibre groups over the labels in `T`. -/
def fibresGroup (T : Finset J) : Set (Perm V) := {g | ∃ c ∈ T, g ∈ fibreGroup (lab · = c)}

theorem fibresGroup_insert (c : J) (T : Finset J) :
    fibresGroup lab (insert c T) = fibresGroup lab T ∪ fibreGroup (lab · = c) := by
  ext g
  simp only [fibresGroup, Finset.mem_insert, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨c', hc' | hc', hg⟩
    · subst hc'; exact Or.inr hg
    · exact Or.inl ⟨c', hc', hg⟩
  · rintro (⟨c', hc', hg⟩ | hg)
    · exact ⟨c', Or.inr hc', hg⟩
    · exact ⟨c, Or.inl rfl, hg⟩

omit [DecidableEq J] in
theorem fibresGroup_empty : fibresGroup lab (∅ : Finset J) = ∅ := by
  ext g; simp [fibresGroup]

omit [DecidableEq J] in
/-- A polynomial in the variables of the fibre `c` is invariant under the fibre groups of
other labels. -/
theorem isInvariant_prod_fibre {c : J} {T : Finset J} (hc : c ∉ T) {n : ℕ} (e : Fin n → V)
    (he : ∀ a, lab (e a) = c) (u : Fin n → ℕ) :
    IsInvariant (fibresGroup lab T) (∏ a, X (e a) ^ u a : MvPolynomial V k) := by
  rintro g ⟨c', hc', hg⟩
  simp only [map_prod, map_pow, rename_X]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [hg (e a) fun h => hc (by rw [← he a, h]; exact hc')]

variable [Fintype V]

/-- Induction over the fibres: an invariant basis for the fibres with labels in `T`, whose
elements are invariant under the other fibre groups. -/
theorem exists_isInvBasis_fibres (T : Finset J) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → MvPolynomial V k),
      Fintype.card ι = ∏ c ∈ T, (Fintype.card {v // lab v = c}).factorial ∧
      IsInvBasis (fibresGroup lab T) b := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => 1, by simp, ?_⟩
    rw [fibresGroup_empty]
    exact IsInvBasis.empty
  | @insert c T hcT ih =>
    obtain ⟨ι, _, b, hcard, hb⟩ := ih
    refine ⟨ι × {u : Fin (Fintype.card {v // lab v = c}) → ℕ // ∀ a, u a ≤ a}, inferInstance,
      fun q => b q.1 * ∏ a, X ((Fintype.equivFin {v // lab v = c}).symm a : V) ^ q.2.1 a,
      ?_, ?_⟩
    · rw [Fintype.card_prod, hcard, card_staircase, Finset.prod_insert hcT, mul_comm]
    · rw [fibresGroup_insert]
      refine IsInvBasis.mul hb (isInvBasis_fibre k (lab · = c)) (fun u => ?_) ?_
      · exact isInvariant_prod_fibre lab hcT _ (fun a => ((Fintype.equivFin _).symm a).2) _
      · rintro g ⟨c', hc', hg⟩ g' hg'
        exact fibreGroup_commute lab (fun h : c' = c => hcT (h ▸ hc')) hg hg'

/-! ### Decomposing label-preserving permutations -/

variable {lab}

/-- The part of a label-preserving permutation `g` on the fibres with labels in `T`. -/
def labelPiece {g : Perm V} (hg : lab ∘ g = lab) (T : Finset J) : Perm V where
  toFun v := if lab v ∈ T then g v else v
  invFun v := if lab v ∈ T then g⁻¹ v else v
  left_inv v := by
    have h1 : ∀ w, lab (g w) = lab w := fun w => congrFun hg w
    by_cases hv : lab v ∈ T
    · simp [hv, h1]
    · simp [hv]
  right_inv v := by
    have h1 : ∀ w, lab (g⁻¹ w) = lab w := fun w => by
      conv_rhs => rw [← g.apply_symm_apply w]
      exact (congrFun hg _).symm
    by_cases hv : lab v ∈ T
    · simp [hv, h1]
    · simp [hv]

omit [Fintype V] in
theorem labelPiece_apply {g : Perm V} (hg : lab ∘ g = lab) (T : Finset J) (v : V) :
    labelPiece hg T v = if lab v ∈ T then g v else v := rfl

omit [Fintype V] in
theorem labelPiece_insert {g : Perm V} (hg : lab ∘ g = lab) {c : J} {T : Finset J}
    (hcT : c ∉ T) : labelPiece hg (insert c T) = labelPiece hg {c} * labelPiece hg T := by
  have h1 : ∀ w, lab (g w) = lab w := fun w => congrFun hg w
  ext v
  simp only [Perm.coe_mul, Function.comp_apply, labelPiece_apply, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases hv : lab v ∈ T
  · have : lab v ≠ c := fun h => hcT (h ▸ hv)
    simp [hv, h1, this]
  · by_cases hvc : lab v = c
    · subst hvc; simp [hv, h1]
    · simp [hv, hvc]

omit [Fintype V] in
theorem labelPiece_singleton_mem {g : Perm V} (hg : lab ∘ g = lab) (c : J) :
    labelPiece hg {c} ∈ fibreGroup (lab · = c) := fun v hv => by
  simp [labelPiece_apply, hv]

omit [Fintype V] in
theorem isInvariant_labelPiece {g : Perm V} (hg : lab ∘ g = lab) {f : MvPolynomial V k}
    (T : Finset J) (hf : ∀ c, IsInvariant (fibreGroup (lab · = c)) f) :
    rename (labelPiece hg T) f = f := by
  induction T using Finset.induction_on with
  | empty =>
    have : labelPiece hg (∅ : Finset J) = 1 := by ext v; simp [labelPiece_apply]
    rw [this, Perm.coe_one, rename_id_apply]
  | @insert c T hcT ih =>
    rw [labelPiece_insert hg hcT, Perm.coe_mul, ← rename_rename, ih,
      hf c _ (labelPiece_singleton_mem hg c)]

variable (lab) in
theorem isInvariant_fibresGroup_iff {f : MvPolynomial V k} :
    IsInvariant (fibresGroup lab (Finset.univ.image lab)) f ↔
      ∀ g : Perm V, lab ∘ g = lab → rename g f = f := by
  constructor
  · intro h g hg
    have hf : ∀ c, IsInvariant (fibreGroup (lab · = c)) f := by
      intro c σ hσ
      by_cases hc : c ∈ Finset.univ.image lab
      · exact h σ ⟨c, hc, hσ⟩
      · have : σ = 1 := by
          ext v
          exact hσ v fun h => hc (Finset.mem_image.2 ⟨v, Finset.mem_univ _, h⟩)
        rw [this, Perm.coe_one, rename_id_apply]
    have hpiece : labelPiece hg (Finset.univ.image lab) = g := by
      ext v; simp [labelPiece_apply]
    rw [← hpiece]
    exact isInvariant_labelPiece hg _ hf
  · rintro h σ ⟨c, -, hσ⟩
    refine h σ (funext fun v => ?_)
    by_cases hv : lab v = c
    · exact ((fibreGroup_iff hσ v).2 hv).trans hv.symm
    · simp [hσ v hv]

end Label

/-! ### The main theorem -/

section Main

variable (k) {J : Type*} (lab : V → J)

/-- The polynomials invariant under all label-preserving permutations of the variables
(invariants of a Young subgroup). -/
def labelInvariants : Subalgebra k (MvPolynomial V k) where
  carrier := {f | ∀ g : Perm V, lab ∘ g = lab → rename g f = f}
  mul_mem' hf hg σ hσ := by rw [map_mul, hf σ hσ, hg σ hσ]
  add_mem' hf hg σ hσ := by rw [map_add, hf σ hσ, hg σ hσ]
  algebraMap_mem' c σ _ := by rw [algebraMap_eq, rename_C]

variable {k lab} in
theorem mem_labelInvariants {f : MvPolynomial V k} :
    f ∈ labelInvariants k lab ↔ ∀ g : Perm V, lab ∘ g = lab → rename g f = f := Iff.rfl

variable [Fintype V] [DecidableEq V] [DecidableEq J]

/-- **Parabolic Artin theorem**, elementary form: there is a finite family `b`, indexed by a
type of cardinality `|G_lab|`, such that every polynomial is uniquely a combination of the
`b i` with `G_lab`-invariant coefficients. -/
theorem exists_isInvBasis_label :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → MvPolynomial V k),
      Fintype.card ι = Fintype.card {g : Perm V // lab ∘ g = lab} ∧
      (∀ g : ι → MvPolynomial V k, (∀ i, g i ∈ labelInvariants k lab) →
        ∑ i, g i * b i = 0 → ∀ i, g i = 0) ∧
      (∀ p : MvPolynomial V k, ∃ g : ι → MvPolynomial V k,
        (∀ i, g i ∈ labelInvariants k lab) ∧ ∑ i, g i * b i = p) := by
  obtain ⟨ι, _, b, hcard, hb⟩ := exists_isInvBasis_fibres (k := k) lab (Finset.univ.image lab)
  refine ⟨ι, inferInstance, b, ?_, fun g hg => hb.indep g fun i =>
    (isInvariant_fibresGroup_iff lab).2 (hg i), fun p => ?_⟩
  · rw [hcard, DomMulAct.stabilizer_card']
  · obtain ⟨g, hg, hgp⟩ := hb.span p
    exact ⟨g, fun i => (isInvariant_fibresGroup_iff lab).1 (hg i), hgp⟩

/-- **Parabolic Artin theorem**: `k[V]` has a basis over the invariants of the Young subgroup
`G_lab = {g // lab ∘ g = lab}`, indexed by a finite type of cardinality `|G_lab|`. -/
theorem exists_labelBasis :
    ∃ (ι : Type) (_ : Fintype ι),
      Fintype.card ι = Fintype.card {g : Perm V // lab ∘ g = lab} ∧
      Nonempty (Basis ι (labelInvariants k lab) (MvPolynomial V k)) := by
  obtain ⟨ι, _, b, hcard, hind, hspan⟩ := exists_isInvBasis_label k lab
  refine ⟨ι, inferInstance, hcard, ⟨Basis.mk (v := b) ?_ ?_⟩⟩
  · exact Fintype.linearIndependent_iff.2 fun c hc i => Subtype.ext <|
      hind (fun i => c i) (fun i => (c i).2) (by simpa [Subalgebra.smul_def] using hc) i
  · intro p _
    obtain ⟨g, hg, hgp⟩ := hspan p
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨fun i => ⟨g i, hg i⟩, by simpa [Subalgebra.smul_def] using hgp⟩

/-- `k[V]` is a free module over the invariants of a Young subgroup. -/
instance labelInvariants_free : Module.Free (labelInvariants k lab) (MvPolynomial V k) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_labelBasis k lab
  exact Module.Free.of_basis b

/-- `k[V]` is a finite module over the invariants of a Young subgroup. -/
instance labelInvariants_finite : Module.Finite (labelInvariants k lab) (MvPolynomial V k) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_labelBasis k lab
  exact Module.Finite.of_basis b

/-- The rank of `k[V]` over the invariants of the Young subgroup `G_lab` is `|G_lab|`. -/
theorem finrank_labelInvariants [Nontrivial k] :
    Module.finrank (labelInvariants k lab) (MvPolynomial V k) =
      Fintype.card {g : Perm V // lab ∘ g = lab} := by
  obtain ⟨ι, _, hcard, ⟨b⟩⟩ := exists_labelBasis k lab
  rw [Module.finrank_eq_card_basis b, hcard]

end Main

end Categorification
