/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CoarsePhiLayers
import Categorification.WeightedKLR.RedStrands.LabelledStandardFiltration

/-!
# The kernel onto a left partial standard module is filtered by partial standards

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §6.1, proof
of Lemma 6.8, left form over `T^λ`: for a red-ordered loading `s` and a merged pair `b < a`, the
kernel of `T^λ e(s)` onto its partial standard module has a finite filtration whose subquotients
are partial standard modules at loadings with strictly higher root
(`exists_hasFiltration_leftPartialKernel`).

The proof is the dimension count of Proposition 5.21 for the coarse layers
(`Stendhal.coarseLayerMap`):

* the partial standard module at `u` has dimension at most the sum of the dimensions of the
  standard modules at the bottoms of the local assignments of `u`
  (`finrank_leftPartialStandard_le`), since the `x_φ` of the other assignments lie in the kernel;
* the dimension identity of Lemma 5.19 (`finrank_lIdeal_eq_sum_phiBottom`) and the
  factorization into coarse and local assignments (`sum_assignments_eq_sum_coarse_local`) then
  force every coarse layer map to be an isomorphism (`coarseLayerMap_bijective`), and the layer
  dimensions add up (`coarse_count`);
* the kernel is the sum of the `T^λ x_g` over the coarse `g` with a strictly higher root
  (`leftPartialKernel_eq_iSup_coarseSub`), an upward closed set, so the filtration of
  `Submodule.hasFiltration_iSup` applies.

Route hypothesis, inherited from Lemma 5.19: `AllFiniteDeltaInjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {C : QuantumGroup.CartanDatum I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => TensorProductAlgebra k Q Λ ν

private theorem finite_tensor (hR : IsRouquierQ C Q) : Module.Finite k A := by
  convert tensorProductAlgebra_finite (Q := Q) Λ ν hR using 4
  exact cornerAlgebra_eq_instAlgebraCorner _

private theorem finrank_quotient_add_finrank_tower {X : Type*} [AddCommGroup X] [Module k X]
    [Module A X] [IsScalarTower k A X] [FiniteDimensional k X] (p : Submodule A X) :
    Module.finrank k (X ⧸ p) + Module.finrank k p = Module.finrank k X := by
  have h := Submodule.finrank_quotient_add_finrank (p.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k p).finrank_eq] at h
  exact h

private instance finiteDimensional_lIdeal [FiniteDimensional k A] (x : A) :
    FiniteDimensional k (lIdeal x) :=
  Module.Finite.of_injective ((lIdeal x).subtype.restrictScalars k) Subtype.val_injective

private instance finiteDimensional_leftPartialStandard [FiniteDimensional k A] (a b : Fin ℓ)
    (u : Seq μ) (hu : IsRedOrdered u) : FiniteDimensional k (leftPartialStandard Q Λ a b u hu) :=
  Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k (leftPartialKernel Q Λ a b u hu))

private theorem phiVec_mem_leftPartialKernel {a b : Fin ℓ} (ρ : Perm (Fin m) → List ℕ)
    {u : Seq μ} (hu : IsRedOrdered u) (f : PhiIndex u)
    (hlt : adjacentBlockRoot a b u < adjacentBlockRoot a b (phiBottom u f.1)) :
    phiVec Q Λ ρ hu f ∈ leftPartialKernel Q Λ a b u hu := by
  change phiElt Q Λ ρ hu f.mem ∈ leftPartialUpper Q Λ a b u hu
  have e : phiElt Q Λ ρ hu f.mem = seqIdem Q Λ _ (f.isRedOrdered hu) * phiElt Q Λ ρ hu f.mem *
      seqIdem Q Λ u hu := by
    rw [mul_assoc, phiElt_mul_seqIdem, seqIdem_mul_phiElt]
  rw [e]
  exact seqIdem_mul_mul_seqIdem_mem_leftPartialUpper hu _ hlt _

section Bound

variable (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
  (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)

include hR hall in
open scoped Classical in
/-- **The dimension of a partial standard module is at most the sum over the local
assignments** of the dimensions of the standard modules at their bottoms. -/
theorem finrank_leftPartialStandard_le {a b : Fin ℓ} (hba : b < a) {u : Seq μ}
    (hu : IsRedOrdered u) :
    Module.finrank k (leftPartialStandard Q Λ a b u hu) ≤
      ∑ f' ∈ (assignments u.lbl).toFinset.filter (IsLocal a u), stdDim Q Λ (phiBottom u f') := by
  classical
  have := finite_tensor (Λ := Λ) (ν := ν) hR
  let ρ : Perm (Fin m) → List ℕ := fun w => (exists_reduced m w).choose
  have hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := fun w =>
    (exists_reduced m w).choose_spec
  have hlay : ∀ f : PhiIndex u, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hu) f =
      stdDim Q Λ (phiBottom u f.1) := fun f => by
    rw [← finrank_phiLayer, ← ((phiLayerEquiv Q hQ hR hall Λ ρ hρ hu f).restrictScalars k).finrank_eq]
    simp only [stdDim, f.isRedOrdered hu, ↓reduceDIte]
  have hD := finrank_lIdeal_eq_sum_phiBottom Q hQ hR hall Λ hu
  have hD' : ∑ f : PhiIndex u, stdDim Q Λ (phiBottom u f.1) =
      Module.finrank k (lIdeal (seqIdem Q Λ u hu)) := by
    rw [← hD]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [stdDim, f.isRedOrdered hu, ↓reduceDIte]
  have htight : ∑ f, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hu) f =
      Submodule.finrankK k (⨆ f, phiSub Q Λ ρ hu f) := by
    rw [iSup_phiSub_eq_top ρ hu hρ]
    unfold Submodule.finrankK
    rw [Submodule.restrictScalars_top, finrank_top, ← hD']
    exact Finset.sum_congr rfl fun f _ => hlay f
  let U : Finset (PhiIndex u) := Finset.univ.filter fun f => ¬ IsLocal a u f.1
  have hU : ∀ f ∈ U, ∀ f', PhiLT f f' → f' ∈ U := by
    intro f hf f' hff'
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    intro hl
    have h1 := adjacentBlockRoot_lt_phiBottom_of_not_isLocal (b := b) hba hu f.mem hf
    have h2 := adjacentBlockRoot_le_of_stendhalLE hba (f.isRedOrdered hu) (f'.isRedOrdered hu)
      hff'.1
    rw [adjacentBlockRoot_phiBottom_of_isLocal hba hu f'.mem hl] at h2
    exact lt_irrefl _ (h1.trans_le h2)
  have hUeq := Submodule.finrankK_iSup_eq_sum (k := k) phiLT_irrefl phiLT_trans htight U hU
  have hle : (⨆ f ∈ U, phiSub Q Λ ρ hu f) ≤ leftPartialKernel Q Λ a b u hu := by
    refine iSup₂_le fun f hf => Submodule.span_le.2 ?_
    rintro _ rfl
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact phiVec_mem_leftPartialKernel ρ hu f
      (adjacentBlockRoot_lt_phiBottom_of_not_isLocal hba hu f.mem hf)
  have hK := Submodule.finrankK_le_of_le (k := k) hle
  have hq := finrank_quotient_add_finrank_tower (k := k) (leftPartialKernel Q Λ a b u hu)
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun f : PhiIndex u => IsLocal a u f.1) fun f => stdDim Q Λ (phiBottom u f.1)
  have hloc : ∑ f ∈ Finset.univ.filter (fun f : PhiIndex u => IsLocal a u f.1),
      stdDim Q Λ (phiBottom u f.1) =
      ∑ f' ∈ (assignments u.lbl).toFinset.filter (IsLocal a u), stdDim Q Λ (phiBottom u f') := by
    rw [Finset.sum_filter, Finset.sum_filter,
      Finset.sum_coe_sort (assignments u.lbl).toFinset
        (fun f => if IsLocal a u f then stdDim Q Λ (phiBottom u f) else 0)]
  have hUs : ∑ f ∈ U, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hu) f =
      ∑ f ∈ U, stdDim Q Λ (phiBottom u f.1) := Finset.sum_congr rfl fun f _ => hlay f
  unfold Submodule.finrankK at hK hUeq
  have hK' : Module.finrank k ((⨆ f ∈ U, phiSub Q Λ ρ hu f).restrictScalars k) ≤
      Module.finrank k (leftPartialKernel Q Λ a b u hu) := hK
  rw [← hloc]
  have hUn : ∑ f ∈ U, stdDim Q Λ (phiBottom u f.1) =
      ∑ f ∈ Finset.univ.filter (fun f : PhiIndex u => ¬ IsLocal a u f.1),
        stdDim Q Λ (phiBottom u f.1) := rfl
  have hPS : Module.finrank k (leftPartialStandard Q Λ a b u hu) =
      Module.finrank k (lIdeal (seqIdem Q Λ u hu) ⧸ leftPartialKernel Q Λ a b u hu) := rfl
  omega

include hR hall in
/-- **The count of Proposition 5.21 for the coarse layers**: the layer of `x_g` among the coarse
assignments has the dimension of the partial standard module at `φ_g • s`, which is the sum over
the local assignments of the bottom. -/
theorem coarse_count {a b : Fin ℓ} (hba : b < a) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {s : Seq μ}
    (hs : IsRedOrdered s) :
    (∀ g : CoarseIndex a s, Submodule.layerRank (k := k) (coarseRel a b)
        (coarseSub Q Λ ρ a hs) g =
      Module.finrank k (leftPartialStandard Q Λ a b (phiBottom s g.1.1) (g.1.isRedOrdered hs))) ∧
    ∑ g, Submodule.layerRank (k := k) (coarseRel a b) (coarseSub Q Λ ρ a hs) g =
      Submodule.finrankK k (⨆ g, coarseSub Q Λ ρ a hs g) := by
  classical
  have := finite_tensor (Λ := Λ) (ν := ν) hR
  let d : CoarseIndex a s → ℕ := fun g =>
    ∑ f' ∈ (assignments (phiBottom s g.1.1).lbl).toFinset.filter
      (IsLocal a (phiBottom s g.1.1)), stdDim Q Λ (phiBottom (phiBottom s g.1.1) f')
  have hPS : ∀ g : CoarseIndex a s, Module.finrank k
      (leftPartialStandard Q Λ a b (phiBottom s g.1.1) (g.1.isRedOrdered hs)) ≤ d g := by
    intro g
    convert finrank_leftPartialStandard_le (Λ := Λ) hQ hR hall hba (g.1.isRedOrdered hs) using 2
  have hlay : ∀ g : CoarseIndex a s, Submodule.layerRank (k := k) (coarseRel a b)
      (coarseSub Q Λ ρ a hs) g ≤
      Module.finrank k (leftPartialStandard Q Λ a b (phiBottom s g.1.1) (g.1.isRedOrdered hs)) := by
    intro g
    rw [← Submodule.finrank_layer (k := k) (coarseRel a b) (coarseSub Q Λ ρ a hs) g]
    have := LinearMap.finrank_range_le ((coarseLayerMap Q Λ a b hρ hba hs g).restrictScalars k)
    rwa [(LinearMap.range_eq_top (f := (coarseLayerMap Q Λ a b hρ hba hs g).restrictScalars k)
      ).2 (coarseLayerMap_surjective (Q := Q) (Λ := Λ) hρ hba hs g), finrank_top] at this
  have hD := finrank_lIdeal_eq_sum_phiBottom Q hQ hR hall Λ hs
  have hsum : ∑ g, d g = Submodule.finrankK k (⊤ : Submodule A (lIdeal (seqIdem Q Λ s hs))) := by
    unfold Submodule.finrankK
    rw [Submodule.restrictScalars_top, finrank_top, ← hD]
    have h1 : ∑ g : PhiIndex s, Module.finrank k
        (leftStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs)) =
        ∑ f ∈ (assignments s.lbl).toFinset, stdDim Q Λ (phiBottom s f) := by
      rw [← Finset.sum_coe_sort (assignments s.lbl).toFinset]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [stdDim, f.isRedOrdered hs, ↓reduceDIte]
    rw [h1, sum_assignments_eq_sum_coarse_local (j := a) hs (stdDim Q Λ)]
    rw [← Finset.sum_subtype (Finset.univ.filter fun g : PhiIndex s => IsCoarse a s g.1)
      (fun g => by simp) (fun g : PhiIndex s => ∑ f' ∈ (assignments (phiBottom s g.1).lbl).toFinset.filter
        (IsLocal a (phiBottom s g.1)), stdDim Q Λ (phiBottom (phiBottom s g.1) f'))]
    rw [Finset.sum_filter, Finset.sum_filter,
      Finset.sum_coe_sort (assignments s.lbl).toFinset (fun g => if IsCoarse a s g then
        ∑ f' ∈ (assignments (phiBottom s g).lbl).toFinset.filter
          (IsLocal a (phiBottom s g)), stdDim Q Λ (phiBottom (phiBottom s g) f') else 0)]
  have hEq := Submodule.layerRank_eq_of_sum_eq (k := k) (coarseRel a b) (coarseSub Q Λ ρ a hs)
    (coarseRel_irrefl a b) (coarseRel_trans a b) (iSup_coarseSub_eq_top hρ hs) d
    (fun g => (hlay g).trans (hPS g)) hsum
  refine ⟨fun g => le_antisymm (hlay g) (hEq g ▸ hPS g), ?_⟩
  rw [iSup_coarseSub_eq_top hρ hs, ← hsum]
  exact Finset.sum_congr rfl fun g _ => hEq g

include hR hall in
/-- **The coarse layer maps are isomorphisms.** -/
theorem coarseLayerMap_bijective {a b : Fin ℓ} (hba : b < a) {ρ : Perm (Fin m) → List ℕ}
    (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) {s : Seq μ}
    (hs : IsRedOrdered s) (g : CoarseIndex a s) :
    Function.Bijective (coarseLayerMap Q Λ a b hρ hba hs g) := by
  have := finite_tensor (Λ := Λ) (ν := ν) hR
  have hs' : Function.Surjective (coarseLayerMap Q Λ a b hρ hba hs g) :=
    coarseLayerMap_surjective hρ hba hs g
  refine ⟨?_, hs'⟩
  have h := ((coarse_count (Λ := Λ) hQ hR hall hba hρ hs).1 g).symm
  rw [← Submodule.finrank_layer (k := k) (coarseRel a b) (coarseSub Q Λ ρ a hs) g] at h
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (coarseLayerMap Q Λ a b hρ hba hs g).restrictScalars k)).2 hs'

/-- The kernel onto the partial standard module is the sum of the `T^λ x_g` over the coarse
`g` whose bottom has a strictly higher root. -/
theorem leftPartialKernel_eq_iSup_coarseSub {a b : Fin ℓ} (hba : b < a)
    {ρ : Perm (Fin m) → List ℕ} (hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) :
    leftPartialKernel Q Λ a b s hs = ⨆ (g : CoarseIndex a s)
      (_ : adjacentBlockRoot a b s < adjacentBlockRoot a b (phiBottom s g.1.1)),
        coarseSub Q Λ ρ a hs g := by
  set K := ⨆ (g : CoarseIndex a s)
    (_ : adjacentBlockRoot a b s < adjacentBlockRoot a b (phiBottom s g.1.1)),
      coarseSub Q Λ ρ a hs g
  refine le_antisymm ?_ (iSup₂_le fun g hg => Submodule.span_le.2 ?_)
  · have key : ∀ w ∈ leftPartialUpper Q Λ a b s hs,
        w * seqIdem Q Λ s hs ∈ K.map (lIdeal (seqIdem Q Λ s hs)).subtype := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨t, ht, c, hst, rfl⟩ := hw
        have hz : seqIdem Q Λ t ht * c * seqIdem Q Λ s hs * seqIdem Q Λ s hs =
            seqIdem Q Λ t ht * c * seqIdem Q Λ s hs := by
          rw [mul_assoc _ (seqIdem Q Λ s hs), seqIdem_mul_self]
        let y : lIdeal (seqIdem Q Λ s hs) := ⟨seqIdem Q Λ t ht * c * seqIdem Q Λ s hs, hz⟩
        have hy : seqIdem Q Λ t ht * (y : A) = (y : A) := by
          change seqIdem Q Λ t ht * (seqIdem Q Λ t ht * c * seqIdem Q Λ s hs) = _
          rw [← mul_assoc, ← mul_assoc, seqIdem_mul_self]
        refine ⟨y, ?_, hz.symm⟩
        refine (iSup₂_le fun g hle => ?_ : _ ≤ K) (mem_iSup_coarseSub_of_seqIdem hρ hba hs ht y hy)
        exact le_iSup₂_of_le (f := fun (g : CoarseIndex a s)
          (_ : adjacentBlockRoot a b s < adjacentBlockRoot a b (phiBottom s g.1.1)) =>
            coarseSub Q Λ ρ a hs g) g (hst.trans_le hle) le_rfl
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [smul_eq_mul, mul_assoc]; exact Submodule.smul_mem _ c hx
    intro x hx
    obtain ⟨y, hy, hyx⟩ := key _ hx
    have : y = x := Subtype.ext (hyx.trans x.2)
    exact this ▸ hy
  · rintro _ rfl
    exact phiVec_mem_leftPartialKernel ρ hs g.1 hg

include hR hall in
/-- **The kernel onto a left partial standard module is filtered by partial standard modules**
(B. Webster, arXiv:1309.3796v3, §6.1, proof of Lemma 6.8, over `T^λ`): for a merged pair
`b < a` and a red-ordered `s`, the kernel of `T^λ e(s)` onto its partial standard module has a
finite filtration whose subquotients are partial standard modules at red-ordered loadings with a
strictly higher root. -/
theorem exists_hasFiltration_leftPartialKernel {a b : Fin ℓ} (hba : b < a) {s : Seq μ}
    (hs : IsRedOrdered s) :
    ∃ l : List {t : Seq μ // IsRedOrdered t},
      (∀ v ∈ l, adjacentBlockRoot a b s < adjacentBlockRoot a b v.1) ∧
        ModuleFiltration.HasFiltration
          (fun v => ModuleCat.of A (leftPartialStandard Q Λ a b v.1 v.2)) l
          (ModuleCat.of A (leftPartialKernel Q Λ a b s hs)) := by
  classical
  have := finite_tensor (Λ := Λ) (ν := ν) hR
  let ρ : Perm (Fin m) → List ℕ := fun w => (exists_reduced m w).choose
  have hρ : ∀ w, TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w := fun w =>
    (exists_reduced m w).choose_spec
  let S : Finset (CoarseIndex a s) := Finset.univ.filter fun g =>
    adjacentBlockRoot a b s < adjacentBlockRoot a b (phiBottom s g.1.1)
  have hS : ∀ g ∈ S, ∀ g', coarseRel a b g g' → g' ∈ S := by
    intro g hg g' hgg'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hg.trans hgg'
  obtain ⟨l, hl, hfil⟩ := Submodule.hasFiltration_iSup (k := k) (coarseRel_irrefl a b)
    (coarseRel_trans a b) (coarse_count (Λ := Λ) hQ hR hall hba hρ hs).2 S hS
  let F : CoarseIndex a s → {t : Seq μ // IsRedOrdered t} := fun g =>
    ⟨phiBottom s g.1.1, g.1.isRedOrdered hs⟩
  refine ⟨l.map F, ?_, ?_⟩
  · intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hv
    have := hl g hg
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using this
  · refine ModuleFiltration.HasFiltration.relabel F ?_
    refine ModuleFiltration.HasFiltration.of_equiv
      (Y := ModuleCat.of A ↥(⨆ g ∈ S, coarseSub Q Λ ρ a hs g)) ?_
      (LinearEquiv.ofEq _ (leftPartialKernel Q Λ a b s hs) ?_)
    · refine hfil.mono_of_mem fun g _ => ⟨(LinearEquiv.ofBijective
        (coarseLayerMap Q Λ a b hρ hba hs g)
        (coarseLayerMap_bijective (Λ := Λ) hQ hR hall hba hρ hs g)).symm⟩
    · rw [leftPartialKernel_eq_iSup_coarseSub hba hρ hs]
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]

end Bound

end Categorification.Stendhal
