/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CoarseAssignment
import Categorification.WeightedKLR.RedStrands.LeftPartialStandard
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers
import Categorification.Algebra.FinrankCountingFiltration
import Categorification.Algebra.ModuleFiltrationMap

/-!
# Coarse layers of a loading projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §6.1, proof
of Lemma 6.8: the kernel of `T^λ e(s)` onto its partial standard module is filtered by partial
standard modules at loadings of strictly higher root. The partial standardization drops the red
cut at `λ_a`, and the root `adjacentBlockRoot a b` (for `b < a`) reads the black counts at every
other red strand.

The argument is the dimension count of Proposition 5.21, applied to the coarse block
assignments of `s` (`IsCoarse`), which move black strands only across the retained cuts.

* Reduced words adapted to the coarse part (`adaptedWords`) give `x_φ ∈ T^λ x_{φᶜ}` for the
  coarse part `φᶜ` of `φ`, so the `x_g`, `g` coarse, generate `T^λ e(s)`
  (`iSup_coarseSub_eq_top`).
* For coarse `g`, the partial standard module at `φ_g • s` maps onto the layer of `x_g`
  (`coarseLayerMap_surjective`).
* The partial standard module at `u` has dimension at most the sum of the dimensions of the
  standard modules at the bottoms of the local assignments of `u`
  (`finrank_leftPartialStandard_le`).
* Coarse and local assignments together are the block assignments
  (`sum_assignments_eq_sum_coarse_local`), so the count of Lemma 5.19 forces all these
  inequalities to be equalities.

Route hypothesis, as for Proposition 5.21: `AllFiniteDeltaInjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "E" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ) (ν := ν)

section Words

omit [DecidableEq I] in
private theorem reduced_frame' {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (v : Perm (Fin m) → Perm (Fin m)) (hv : ∀ τ, invSet m (v τ) ⊆ invSet m τ) (τ : Perm (Fin m)) :
    IsReduced m (ρ (τ * (v τ)⁻¹) ++ ρ (v τ)) ∧ wordProd m (ρ (τ * (v τ)⁻¹) ++ ρ (v τ)) = τ := by
  have hl := length_add_of_invSet_subset (hv τ)
  refine ⟨⟨validWord_append.2 ⟨(hρ _).1.1, (hρ _).1.1⟩, ?_⟩, ?_⟩
  · rw [List.length_append, wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right,
      (hρ _).1.2, (hρ _).1.2, (hρ _).2, (hρ _).2, hl]
  · rw [wordProd_append, (hρ _).2, (hρ _).2, inv_mul_cancel_right]

/-- The coarse part of a permutation: `φ_{fᶜ}` when the permutation is `φ_f`. -/
def coarseFrame (j : ℕ) (s : Seq μ) (τ : Perm (Fin m)) : Perm (Fin m) :=
  if τ = phiPerm s (diagAssign s τ) then phiPerm s (coarsen j s (diagAssign s τ)) else 1

omit [DecidableEq I] in
theorem invSet_coarseFrame_subset (j : ℕ) (s : Seq μ) (τ : Perm (Fin m)) :
    invSet m (coarseFrame j s τ) ⊆ invSet m τ := by
  unfold coarseFrame
  split_ifs with h
  · have := invSet_phiPerm_coarsen_subset (j := j) (diagAssign_mem s τ)
    rwa [← h] at this
  · intro x hx
    simp only [mem_invSet, Perm.one_apply] at hx
    exact absurd hx.2 (lt_asymm hx.1)

omit [DecidableEq I] in
theorem coarseFrame_phiPerm {j : ℕ} {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) : coarseFrame j s (phiPerm s f) = phiPerm s (coarsen j s f) := by
  unfold coarseFrame
  simp only [diagAssign_phiPerm hs hf, ↓reduceIte]

/-- Reduced words through the coarse part. -/
def adaptedWords (ρ : Perm (Fin m) → List ℕ) (j : ℕ) (s : Seq μ) (τ : Perm (Fin m)) :
    List ℕ :=
  ρ (τ * (coarseFrame j s τ)⁻¹) ++ ρ (coarseFrame j s τ)

omit [DecidableEq I] in
theorem adaptedWords_reduced {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (j : ℕ) (s : Seq μ) :
    ∀ w, IsReduced m (adaptedWords ρ j s w) ∧ wordProd m (adaptedWords ρ j s w) = w :=
  reduced_frame' hρ _ (invSet_coarseFrame_subset j s)

omit [DecidableEq I] in
theorem eq_nil_of_reduced_one {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) : ρ 1 = [] := by
  have h := (hρ 1).1.2
  rw [(hρ 1).2, length_one] at h
  exact List.length_eq_zero_iff.1 h

omit [DecidableEq I] in
theorem adaptedWords_phiPerm_of_isCoarse {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {j : ℕ} {s : Seq μ}
    (hs : IsRedOrdered s) {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) (hc : IsCoarse j s g) :
    adaptedWords ρ j s (phiPerm s g) = ρ (phiPerm s g) := by
  rw [adaptedWords, coarseFrame_phiPerm hs hg, coarsen_eq_of_isCoarse hc, mul_inv_cancel,
    eq_nil_of_reduced_one hρ, List.nil_append]

end Words

section Factor

private theorem e_mul_e_self' (t : Seq μ) : E t * E t = E t := by
  simp [StendhalAlgebraAllOrders.e_mul_e]

/-- **`x_φ` factors through its coarse part**, for the adapted reduced words. -/
theorem phiElt_adaptedWords_eq_mul {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) (j : ℕ) {s : Seq μ} (hs : IsRedOrdered s) {f : Fin m → ℕ}
    (hf : f ∈ assignments s.lbl) :
    phiElt Q Λ (adaptedWords ρ j s) hs hf =
      TensorProductAlgebra.mk Q Λ ν (phiCut Q Λ (phiBottom s f) (phiBottom s (coarsen j s f))
        (isRedOrdered_phiBottom hs hf) (isRedOrdered_phiBottom hs (coarsen_mem hf))
        (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
          (KLRAlgebra.ψw (ρ (phiPerm s f * (phiPerm s (coarsen j s f))⁻¹))))) *
      phiElt Q Λ ρ hs (coarsen_mem (j := j) hf) := by
  set g := coarsen j s f
  have hb' : E (phiBottom s g) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ (phiPerm s g))) =
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν
        (KLRAlgebra.ψw (ρ (phiPerm s g)) * KLRAlgebra.e s) := by
    change StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      (KLRAlgebra.e (phiPerm s g • s)) * _ = _
    rw [← map_mul, KLRAlgebra.e_mul_ψw, (hρ _).2, inv_smul_smul]
  have hw : (KLRAlgebra.ψw (adaptedWords ρ j s (phiPerm s f)) :
      KLRAlgebra k (stendhalQ Q Λ) μ) =
      KLRAlgebra.ψw (ρ (phiPerm s f * (phiPerm s g)⁻¹)) * KLRAlgebra.ψw (ρ (phiPerm s g)) := by
    rw [adaptedWords, coarseFrame_phiPerm hs hf, KLRAlgebra.ψw_append]
  rw [phiElt, phiElt, ← map_mul, phiCut_mul_phiCut]
  congr 1
  apply Subtype.ext
  rw [phiCut_val, phiCut_val, hw, mul_assoc (StendhalAlgebraAllOrders.ofKLR k Q Λ ν _) (E _), hb',
    ← map_mul]
  simp only [map_mul]
  change _ = E _ * (_ * (_ * E s)) * E s
  simp only [mul_assoc, e_mul_e_self']
  rfl

end Factor

section Roots

variable {a b : Fin ℓ}

/-- The root is monotone in Webster's order on red-ordered loadings. -/
theorem adjacentBlockRoot_le_of_stendhalLE (hba : b < a) {t t' : Seq μ} (ht : IsRedOrdered t)
    (ht' : IsRedOrdered t') (hle : StendhalLE t t') :
    adjacentBlockRoot a b t ≤ adjacentBlockRoot a b t' := fun r i => by
  rw [adjacentBlockRoot_eq_of_isRedOrdered hba ht, adjacentBlockRoot_eq_of_isRedOrdered hba ht']
  exact hle _ i

/-- Coarsening keeps the root. -/
theorem adjacentBlockRoot_phiBottom_coarsen (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s)
    {f : Fin m → ℕ} (hf : f ∈ assignments s.lbl) :
    adjacentBlockRoot a b (phiBottom s (coarsen a s f)) = adjacentBlockRoot a b (phiBottom s f) :=
  adjacentBlockRoot_eq_of_blackCount hba rfl (isRedOrdered_phiBottom hs (coarsen_mem hf))
    (isRedOrdered_phiBottom hs hf) fun _ hr => funext fun i => blackCount_phiBottom_coarsen hs hf hr i

/-- Local assignments keep the root. -/
theorem adjacentBlockRoot_phiBottom_of_isLocal (hba : b < a) {u : Seq μ} (hu : IsRedOrdered u)
    {f' : Fin m → ℕ} (hf' : f' ∈ assignments u.lbl) (hl : IsLocal a u f') :
    adjacentBlockRoot a b (phiBottom u f') = adjacentBlockRoot a b u :=
  adjacentBlockRoot_eq_of_blackCount hba rfl (isRedOrdered_phiBottom hu hf') hu
    fun _ hr => blackCount_phiBottom_of_isLocal hu hf' hl hr

/-- Assignments that are not local raise the root. -/
theorem adjacentBlockRoot_lt_phiBottom_of_not_isLocal (hba : b < a) {u : Seq μ}
    (hu : IsRedOrdered u) {f' : Fin m → ℕ} (hf' : f' ∈ assignments u.lbl) (hl : ¬ IsLocal a u f') :
    adjacentBlockRoot a b u < adjacentBlockRoot a b (phiBottom u f') :=
  adjacentBlockRoot_lt_of_blackCount hba rfl hu (isRedOrdered_phiBottom hu hf')
    (stendhalLE_phiBottom hu hf') (exists_blackCount_ne_of_not_isLocal hu hf' hl)

end Roots

/-- The coarse block assignments of `s`, for the cut at `λ_a`. -/
abbrev CoarseIndex (a : Fin ℓ) (s : Seq μ) : Type :=
  {g : PhiIndex s // IsCoarse a s g.1}

noncomputable instance (a : Fin ℓ) (s : Seq μ) : Fintype (CoarseIndex a s) := Fintype.ofFinite _

/-- The order of coarse assignments: the order of the roots of their bottoms. -/
def coarseRel (a b : Fin ℓ) {s : Seq μ} (g g' : CoarseIndex a s) : Prop :=
  adjacentBlockRoot a b (phiBottom s g.1.1) < adjacentBlockRoot a b (phiBottom s g'.1.1)

theorem coarseRel_irrefl (a b : Fin ℓ) {s : Seq μ} (g : CoarseIndex a s) :
    ¬ coarseRel a b g g := lt_irrefl _

theorem coarseRel_trans (a b : Fin ℓ) {s : Seq μ} (g g' g'' : CoarseIndex a s)
    (h : coarseRel a b g g') (h' : coarseRel a b g' g'') : coarseRel a b g g'' := h.trans h'

variable (Q Λ) in
/-- The submodule `T^λ x_g` of `T^λ e(s)` for a coarse assignment `g`. -/
abbrev coarseSub (ρ : Perm (Fin m) → List ℕ) (a : Fin ℓ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : CoarseIndex a s) : Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  phiSub Q Λ ρ hs g.1

section Span

variable {a b : Fin ℓ}

/-- The coarse part of a block assignment, as a coarse index. -/
def PhiIndex.coarse (a : Fin ℓ) {s : Seq μ} (f : PhiIndex s) : CoarseIndex a s :=
  ⟨⟨coarsen a s f.1, List.mem_toFinset.2 (coarsen_mem f.mem)⟩, isCoarse_coarsen s f.1 f.mem⟩

theorem phiSub_adaptedWords_le {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) (f : PhiIndex s) :
    phiSub Q Λ (adaptedWords ρ a s) hs f ≤ coarseSub Q Λ ρ a hs (f.coarse a) := by
  refine Submodule.span_le.2 ?_
  rintro _ rfl
  refine Submodule.mem_span_singleton.2 ⟨TensorProductAlgebra.mk Q Λ ν (phiCut Q Λ
    (phiBottom s f.1) (phiBottom s (coarsen a s f.1)) (isRedOrdered_phiBottom hs f.mem)
    (isRedOrdered_phiBottom hs (coarsen_mem f.mem)) (StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      (KLRAlgebra.ψw (ρ (phiPerm s f.1 * (phiPerm s (coarsen a s f.1))⁻¹))))), Subtype.ext ?_⟩
  exact (phiElt_adaptedWords_eq_mul hρ a hs f.mem).symm

/-- **The `x_g`, `g` coarse, generate `T^λ e(s)`.** -/
theorem iSup_coarseSub_eq_top {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) :
    (⨆ g : CoarseIndex a s, coarseSub Q Λ ρ a hs g) = ⊤ := by
  rw [eq_top_iff, ← iSup_phiSub_eq_top (adaptedWords ρ a s) hs (adaptedWords_reduced hρ a s)]
  exact iSup_le fun f => (phiSub_adaptedWords_le hρ hs f).trans
    (le_iSup (fun g : CoarseIndex a s => coarseSub Q Λ ρ a hs g) (f.coarse a))

/-- An element of `T^λ e(s)` in `e(t) T^λ e(s)` lies in the sum of the `T^λ x_g` with `g` coarse
and root at least that of `t`. -/
theorem mem_iSup_coarseSub_of_seqIdem {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s)
    {t : Seq μ} (ht : IsRedOrdered t) (y : lIdeal (seqIdem Q Λ s hs))
    (hy : seqIdem Q Λ t ht * (y : A) = (y : A)) :
    y ∈ ⨆ (g : CoarseIndex a s)
      (_ : adjacentBlockRoot a b t ≤ adjacentBlockRoot a b (phiBottom s g.1.1)),
        coarseSub Q Λ ρ a hs g := by
  have h := mem_iSup_phiSub_of_seqIdem (adaptedWords ρ a s) hs (adaptedWords_reduced hρ a s) ht y hy
  suffices H : (⨆ (f : PhiIndex s) (_ : StendhalLE t (phiBottom s f.1)),
      phiSub Q Λ (adaptedWords ρ a s) hs f) ≤ ⨆ (g : CoarseIndex a s)
        (_ : adjacentBlockRoot a b t ≤ adjacentBlockRoot a b (phiBottom s g.1.1)),
          coarseSub Q Λ ρ a hs g from H h
  refine iSup₂_le fun f hle => ?_
  refine (phiSub_adaptedWords_le hρ hs f).trans ?_
  refine le_iSup₂_of_le (f := fun (g : CoarseIndex a s)
    (_ : adjacentBlockRoot a b t ≤ adjacentBlockRoot a b (phiBottom s g.1.1)) =>
      coarseSub Q Λ ρ a hs g) (f.coarse a) ?_ le_rfl
  change adjacentBlockRoot a b t ≤ adjacentBlockRoot a b (phiBottom s (coarsen a s f.1))
  rw [adjacentBlockRoot_phiBottom_coarsen hba hs f.mem]
  exact adjacentBlockRoot_le_of_stendhalLE hba ht (f.isRedOrdered hs) hle

end Span

section Layer

variable {a b : Fin ℓ}

variable (Q Λ a b) in
/-- The layer of `x_g` among the coarse assignments. -/
abbrev coarseLayer (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) : Type :=
  Submodule.layer (coarseRel a b) (coarseSub Q Λ ρ a hs) g

variable (Q Λ a b) in
/-- The sum of the coarse layer and the layers above it. -/
abbrev coarseAtLeast (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : CoarseIndex a s) : Submodule A (lIdeal (seqIdem Q Λ s hs)) :=
  coarseSub Q Λ ρ a hs g ⊔ Submodule.above (coarseRel a b) (coarseSub Q Λ ρ a hs) g

instance (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    AddCommGroup (coarseAtLeast Q Λ a b ρ hs g) :=
  Submodule.addCommGroup _

instance (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    AddCommGroup (coarseLayer Q Λ a b ρ hs g) :=
  Submodule.Quotient.addCommGroup _

instance (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    Module A (coarseLayer Q Λ a b ρ hs g) :=
  Submodule.Quotient.module _

variable (Q Λ a b) in
/-- The class `[x_g]` in its layer. -/
def coarseLayerGen (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    coarseLayer Q Λ a b ρ hs g :=
  Submodule.Quotient.mk ⟨phiVec Q Λ ρ hs g.1, Submodule.mem_sup_left (Submodule.subset_span rfl)⟩

theorem coarseLayerGen_annihilated {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s)
    (g : CoarseIndex a s) (t : Seq μ) (ht : IsRedOrdered t) (c : A)
    (hlt : adjacentBlockRoot a b (phiBottom s g.1.1) < adjacentBlockRoot a b t) :
    (seqIdem Q Λ t ht * c) • coarseLayerGen Q Λ a b ρ hs g = 0 := by
  rw [coarseLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change (seqIdem Q Λ t ht * c) • phiVec Q Λ ρ hs g.1 ∈
    Submodule.above (coarseRel a b) (coarseSub Q Λ ρ a hs) g
  have h := mem_iSup_coarseSub_of_seqIdem hρ hba hs ht ((seqIdem Q Λ t ht * c) • phiVec Q Λ ρ hs g.1)
    (by
      change seqIdem Q Λ t ht * (seqIdem Q Λ t ht * c * phiElt Q Λ ρ hs g.1.mem) =
        seqIdem Q Λ t ht * c * phiElt Q Λ ρ hs g.1.mem
      rw [← mul_assoc, ← mul_assoc, seqIdem_mul_self])
  refine (iSup₂_le (fun g' hle => ?_) : _ ≤ Submodule.above (coarseRel a b) _ g) h
  exact le_iSup₂_of_le (f := fun g' (_ : coarseRel a b g g') => coarseSub Q Λ ρ a hs g') g'
    (lt_of_lt_of_le hlt hle) le_rfl

variable (Q Λ a b) in
/-- **The map from the partial standard module at `φ_g • s` onto the layer of `x_g`**,
`[e(φ_g • s)] ↦ [x_g]`. -/
def coarseLayerMap {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    leftPartialStandard Q Λ a b (phiBottom s g.1.1) (g.1.isRedOrdered hs) →ₗ[A]
      coarseLayer Q Λ a b ρ hs g :=
  leftPartialStandardLift _ _ (coarseLayerGen Q Λ a b ρ hs g) fun t ht c hlt =>
    coarseLayerGen_annihilated hρ hba hs g t ht c hlt

theorem coarseLayerMap_unit {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s)
    (g : CoarseIndex a s) :
    coarseLayerMap Q Λ a b hρ hba hs g (leftPartialStandardUnit Q Λ a b _ (g.1.isRedOrdered hs)) =
      coarseLayerGen Q Λ a b ρ hs g := by
  refine leftPartialStandardLift_unit (k := k) (Q := Q) (Λ := Λ) (ν := ν) _ _ _ ?_ _
  rw [coarseLayerGen, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact seqIdem_mul_phiElt (Q := Q) (Λ := Λ) ρ hs g.1.mem

/-- **The partial standard module at `φ_g • s` maps onto the layer of `x_g`.** -/
theorem coarseLayerMap_surjective {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (hba : b < a) {s : Seq μ} (hs : IsRedOrdered s)
    (g : CoarseIndex a s) : Function.Surjective (coarseLayerMap Q Λ a b hρ hba hs g) := by
  intro v
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨n, hn, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hn
  refine ⟨d • leftPartialStandardUnit Q Λ a b _ (g.1.isRedOrdered hs), ?_⟩
  rw [map_smul, coarseLayerMap_unit, coarseLayerGen, ← Submodule.Quotient.mk_smul, eq_comm,
    Submodule.Quotient.eq]
  rw [Submodule.mem_comap]
  convert hc using 1
  simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub, Submodule.coe_smul]
  abel

end Layer

end Categorification.Stendhal
