/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelledStandardFiltration
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.Algebra.Graded.HomogeneousLayerCount
import Categorification.KLR.GradedFree

/-!
# The graded dimension identity for `T^λ e(s)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 5.19
and Proposition 5.21, graded form. The subspaces `T^λ e(t)`, `U_t` and `T^λ x_φ` of `T^λ` are
homogeneous for the diagram grading, and `x_φ = ψ_{ρφ} e(s)` is homogeneous of degree
`deg(ψ_{ρφ} e(s))`. The ungraded layer isomorphisms `S_{φ • s} ≅ P_{≥φ}/P_{>φ}`
(`phiLayerEquiv`) therefore give, in every degree `n`,

`dim (T^λ e(s))_n = ∑_φ dim (S_{φ • s})_{n - deg x_φ}`,

where `dim (S_t)_m = dim (T^λ e(t))_m - dim (U_t)_m` (`finrank_lIdeal_grade_eq_sum`). This is
the form of the count that passes to `T̃^λ` by adding a red strand of large label.

## Main definitions

* `stdGradedRank`: the dimension of the degree-`m` part of the left standard module.

## Main results

* `isHomogeneousSubspace_lIdeal`, `isHomogeneousSubspace_leftUpper`, `phiElt_mem_grade`.
* `finrank_lIdeal_grade_eq_sum`: the graded dimension identity. Route hypothesis:
  `AllFiniteDeltaInjective`, as for `phiLayerEquiv`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR DirectSum TypeA Equiv _root_.Categorification.Graded _root_.Module

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => TensorProductAlgebra k Q Λ ν

section Homogeneous

private theorem decompose_mul_left_of_zero {e : A} (he : e ∈ tensorProductGrade G ν 0) (x : A)
    (n : ℤ) : (decompose (tensorProductGrade G ν) (e * x) n : A) =
      e * decompose (tensorProductGrade G ν) x n := by
  have hμ : ∀ m', ∀ y ∈ tensorProductGrade G ν m', LinearMap.mulLeft k e y ∈
      tensorProductGrade G ν (m' + 0) := fun m' y hy => by
    rw [add_zero, LinearMap.mulLeft_apply]
    simpa using SetLike.GradedMul.mul_mem he hy
  have h := decompose_map_of_shift hμ x n
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, sub_zero] at h
  exact h

private theorem decompose_mul_right_of_zero {e : A} (he : e ∈ tensorProductGrade G ν 0) (x : A)
    (n : ℤ) : (decompose (tensorProductGrade G ν) (x * e) n : A) =
      decompose (tensorProductGrade G ν) x n * e := by
  have hμ : ∀ m', ∀ y ∈ tensorProductGrade G ν m', LinearMap.mulRight k e y ∈
      tensorProductGrade G ν (m' + 0) := fun m' y hy => by
    rw [LinearMap.mulRight_apply]
    exact SetLike.GradedMul.mul_mem hy he
  have h := decompose_map_of_shift hμ x n
  rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply, sub_zero] at h
  exact h

/-- `T^λ e(t)` is homogeneous. -/
theorem isHomogeneousSubspace_lIdeal (t : Seq μ) (ht : IsRedOrdered t) :
    IsHomogeneousSubspace (tensorProductGrade G ν)
      ((lIdeal (seqIdem Q Λ t ht)).restrictScalars k) := by
  intro n x hx
  change _ * _ = _
  have hx' : x * seqIdem Q Λ t ht = x := hx
  rw [← decompose_mul_right_of_zero G (mk_e_mem_tensorProductGrade G ν t ht), hx']

/-- `U_t` is homogeneous. -/
theorem isHomogeneousSubspace_leftUpper (t : Seq μ) (ht : IsRedOrdered t) :
    IsHomogeneousSubspace (tensorProductGrade G ν)
      ((leftUpper Q Λ t ht).restrictScalars k) := by
  refine isHomogeneousSubspace_span (tensorProductGrade G ν) ?_
  rintro _ ⟨t', ht', a, hlt, rfl⟩ n
  rw [decompose_mul_right_of_zero G (mk_e_mem_tensorProductGrade G ν t ht),
    decompose_mul_left_of_zero G (mk_e_mem_tensorProductGrade G ν t' ht')]
  exact Submodule.subset_span ⟨t', ht', _, hlt, rfl⟩

/-- `x_φ = ψ_{ρφ} e(s)` is homogeneous of degree `deg(ψ_{ρφ} e(s))`. -/
theorem phiElt_mem_grade (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    {g : Fin m → ℕ} (hg : g ∈ assignments s.lbl) :
    phiElt Q Λ ρ hs hg ∈ tensorProductGrade G ν (G.degW (ρ (phiPerm s g)) s) := by
  apply Graded.mem_map_of_mem (stendhalGrade G ν) (TensorProductAlgebra.mk Q Λ ν).toLinearMap
  change StendhalAlgebraAllOrders.e (phiBottom s g) *
      StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.ψw (ρ (phiPerm s g))) *
      StendhalAlgebraAllOrders.e s ∈ allOrdersGrade G ν _
  have h3 := SetLike.GradedMul.mul_mem (G.e_mem_grade (phiBottom s g))
    (G.ψw_mul_e_mem_grade (ρ (phiPerm s g)) s)
  rw [zero_add] at h3
  have h4 := Graded.mem_map_of_mem _ (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).toLinearMap h3
  simpa [allOrdersGrade, map_mul, mul_assoc, StendhalAlgebraAllOrders.e] using h4

end Homogeneous

section Transport

variable {R M : Type*} [Ring R] [Algebra k R] [AddCommGroup M] [Module k M] [Module R M]
  [IsScalarTower k R M] {ι : Type*} [Fintype ι] [DecidableEq ι] (rel : ι → ι → Prop)

omit [Fintype ι] [DecidableEq ι] in
private theorem finrank_map_subtype (L : Submodule R M) (Y : Submodule R L) :
    finrank k ((Y.map L.subtype).restrictScalars k) = finrank k (Y.restrictScalars k) :=
  ((Submodule.equivMapOfInjective L.subtype Subtype.val_injective Y).restrictScalars k
    ).finrank_eq.symm

omit [Fintype ι] [DecidableEq ι] in
/-- The layers of a family of submodules of `L` and of their images in `M` agree. -/
theorem layerRank_map_subtype (L : Submodule R M) (N : ι → Submodule R L) (g : ι) :
    Submodule.layerRank (k := k) rel (fun g => ((N g).map L.subtype).restrictScalars k) g =
      Submodule.layerRank (k := k) rel N g := by
  have habove : Submodule.above rel (fun g => ((N g).map L.subtype).restrictScalars k) g =
      ((Submodule.above rel N g).map L.subtype).restrictScalars k := by
    simp only [Submodule.above, Submodule.map_iSup, Submodule.restrictScalars_iSup]
  have hsup : ((N g).map L.subtype).restrictScalars k ⊔
      ((Submodule.above rel N g).map L.subtype).restrictScalars k =
      ((N g ⊔ Submodule.above rel N g).map L.subtype).restrictScalars k := by
    rw [Submodule.map_sup, Submodule.restrictScalars_sup']
  rw [Submodule.layerRank, Submodule.layerRank, habove, hsup, Submodule.finrankK,
    Submodule.finrankK, Submodule.restrictScalars_self, Submodule.restrictScalars_self,
    finrank_map_subtype, finrank_map_subtype]

end Transport

/-- The dimension of the degree-`n` part of the left standard module `S_t = T^λ e(t) / U_t`:
`dim (T^λ e(t))_n - dim (U_t)_n` (both subspaces are homogeneous). -/
def stdGradedRank (t : Seq μ) (ht : IsRedOrdered t) (n : ℤ) : ℕ :=
  finrank k ((lIdeal (seqIdem Q Λ t ht)).restrictScalars k ⊓ tensorProductGrade G ν n :) -
    finrank k ((leftUpper Q Λ t ht).restrictScalars k ⊓ tensorProductGrade G ν n :)

section CornerCount

attribute [local instance 2000] KLR.cornerAlgebra

variable {C : QuantumGroup.CartanDatum I}

private theorem finiteDimensional_tensor_corner (hR : IsRouquierQ C Q) :
    FiniteDimensional k A := by
  convert tensorProductAlgebra_finite (Q := Q) Λ ν hR using 4
  exact cornerAlgebra_eq_instAlgebraCorner _

private theorem sum_layerRank_phiSub_corner (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ TypeA.wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) :
    ∑ g : PhiIndex s, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hs) g =
      finrank k ((lIdeal (seqIdem Q Λ s hs)).restrictScalars k) := by
  have := finiteDimensional_tensor_corner (Q := Q) (Λ := Λ) (ν := ν) hR
  have h := finrank_lIdeal_eq_sum_phiBottom Q hQ hR hall Λ hs
  have h2 : ∑ g : PhiIndex s, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hs) g =
      ∑ g : PhiIndex s, finrank k (leftStandard Q Λ _ (g.isRedOrdered hs)) :=
    Finset.sum_congr rfl fun g _ => by
      rw [← finrank_phiLayer]
      exact ((phiLayerEquiv Q hQ hR hall Λ ρ hρ hs g).restrictScalars k).finrank_eq.symm
  rw [h2, h]
  rfl

end CornerCount

section Count

variable {C : QuantumGroup.CartanDatum I}

private theorem phiSub_map (ρ : Perm (Fin m) → List ℕ) {s : Seq μ} (hs : IsRedOrdered s)
    (g : PhiIndex s) :
    (phiSub Q Λ ρ hs g).map (lIdeal (seqIdem Q Λ s hs)).subtype =
      Submodule.span A {phiElt Q Λ ρ hs g.mem} := by
  rw [phiSub, Submodule.map_span, Set.image_singleton]
  rfl

private theorem finiteDimensional_tensor (hR : IsRouquierQ C Q) : FiniteDimensional k A :=
  tensorProductAlgebra_finite (Q := Q) Λ ν hR

private theorem sum_layerRank_phiSub (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ TypeA.wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) :
    ∑ g : PhiIndex s, Submodule.layerRank (k := k) PhiLT (phiSub Q Λ ρ hs) g =
      finrank k ((lIdeal (seqIdem Q Λ s hs)).restrictScalars k) := by
  convert sum_layerRank_phiSub_corner (Λ := Λ) hQ hR hall ρ hρ hs
  all_goals try exact (cornerAlgebra_eq_instAlgebraCorner _).symm
  rw [cornerAlgebra_eq_instAlgebraCorner]

/-- **Graded dimension identity for `T^λ e(s)`** (Webster, arXiv:1309.3796v3, Lemma 5.19 and
Proposition 5.21, graded form). In every degree `n`, the dimension of `(T^λ e(s))_n` is the
sum over block assignments `φ` of the dimensions of the standard modules `S_{φ • s}` in degree
`n - deg x_φ`, where `deg x_φ = deg(ψ_{ρφ} e(s))`. Route hypothesis: `AllFiniteDeltaInjective`,
as for `phiLayerEquiv`. -/
theorem finrank_lIdeal_grade_eq_sum (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ TypeA.wordProd m (ρ w) = w)
    {s : Seq μ} (hs : IsRedOrdered s) (n : ℤ) :
    finrank k ((lIdeal (seqIdem Q Λ s hs)).restrictScalars k ⊓ tensorProductGrade G ν n :) =
      ∑ g : PhiIndex s, stdGradedRank G (phiBottom s g.1) (g.isRedOrdered hs)
        (n - G.degW (ρ (phiPerm s g.1)) s) := by
  classical
  have := finiteDimensional_tensor (Q := Q) (Λ := Λ) (ν := ν) hR
  let L := lIdeal (seqIdem Q Λ s hs)
  let N : PhiIndex s → Submodule k A :=
    fun g => ((phiSub Q Λ ρ hs g).map L.subtype).restrictScalars k
  have hNspan : ∀ g, N g = (Submodule.span A {phiElt Q Λ ρ hs g.mem}).restrictScalars k :=
    fun g => by
      change ((phiSub Q Λ ρ hs g).map (lIdeal (seqIdem Q Λ s hs)).subtype).restrictScalars k = _
      rw [phiSub_map]
  have hN : ∀ g, IsHomogeneousSubspace (tensorProductGrade G ν) (N g) := by
    intro g
    rw [hNspan g]
    refine isHomogeneousSubspace_span (tensorProductGrade G ν) ?_
    rintro _ rfl j
    by_cases hj : G.degW (ρ (phiPerm s g.1)) s = j
    · rw [← hj, decompose_of_mem_same _ (phiElt_mem_grade G ρ hs g.mem)]
      exact Submodule.subset_span rfl
    · rw [decompose_of_mem_ne _ (phiElt_mem_grade G ρ hs g.mem) hj]
      exact zero_mem _
  have hspan : (⨆ g, N g) = L.restrictScalars k := by
    change (⨆ g, ((phiSub Q Λ ρ hs g).map L.subtype).restrictScalars k) = _
    rw [← Submodule.restrictScalars_iSup, ← Submodule.map_iSup,
      iSup_phiSub_eq_top ρ hs hρ, Submodule.map_subtype_top]
  have hsum : ∑ g, Submodule.layerRank (k := k) PhiLT N g = finrank k (L.restrictScalars k) := by
    rw [← sum_layerRank_phiSub hQ hR hall ρ hρ hs]
    exact Finset.sum_congr rfl fun g _ => layerRank_map_subtype PhiLT L _ g
  rw [finrank_grade_eq_sum PhiLT phiLT_irrefl phiLT_trans hN hspan hsum n]
  refine Finset.sum_congr rfl fun g _ => ?_
  have ht := g.isRedOrdered hs
  have hμ : ∀ m', ∀ x ∈ tensorProductGrade G ν m', LinearMap.mulRight k (phiElt Q Λ ρ hs g.mem) x ∈
      tensorProductGrade G ν (m' + G.degW (ρ (phiPerm s g.1)) s) := fun m' x hx =>
    SetLike.GradedMul.mul_mem hx (phiElt_mem_grade G ρ hs g.mem)
  have habove : Submodule.above PhiLT N g =
      ((phiAbove Q Λ ρ hs g).map L.subtype).restrictScalars k := by
    simp only [N, Submodule.above, Submodule.map_iSup, Submodule.restrictScalars_iSup]
  have hNg : N g = ((lIdeal (seqIdem Q Λ (phiBottom s g.1) ht)).restrictScalars k).map
      (LinearMap.mulRight k (phiElt Q Λ ρ hs g.mem)) := by
    rw [hNspan g]
    ext y
    simp only [Submodule.restrictScalars_mem, Submodule.mem_span_singleton, Submodule.mem_map,
      LinearMap.mulRight_apply, smul_eq_mul]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a * seqIdem Q Λ (phiBottom s g.1) ht, ?_, ?_⟩
      · change _ * _ = _
        rw [mul_assoc, seqIdem_mul_self]
      · rw [mul_assoc, seqIdem_mul_phiElt]
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
  have hker : ∀ x ∈ (lIdeal (seqIdem Q Λ (phiBottom s g.1) ht)).restrictScalars k,
      LinearMap.mulRight k (phiElt Q Λ ρ hs g.mem) x ∈ Submodule.above PhiLT N g ↔
        x ∈ (leftUpper Q Λ (phiBottom s g.1) ht).restrictScalars k := by
    intro x hx
    rw [habove, LinearMap.mulRight_apply, Submodule.restrictScalars_mem,
      Submodule.restrictScalars_mem]
    have e1 : x * phiElt Q Λ ρ hs g.mem ∈ (phiAbove Q Λ ρ hs g).map L.subtype ↔
        (x • phiVec Q Λ ρ hs g) ∈ phiAbove Q Λ ρ hs g := by
      constructor
      · rintro ⟨z, hz, hzv⟩
        have hz' : z = x • phiVec Q Λ ρ hs g := Subtype.ext hzv
        rwa [← hz']
      · intro h
        exact ⟨_, h, rfl⟩
    rw [e1]
    let y : lIdeal (seqIdem Q Λ (phiBottom s g.1) ht) := ⟨x, hx⟩
    have e2 : x ∈ leftUpper Q Λ (phiBottom s g.1) ht ↔
        (Submodule.Quotient.mk y : leftStandard Q Λ (phiBottom s g.1) ht) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      rfl
    rw [e2, ← (phiLayerEquiv Q hQ hR hall Λ ρ hρ hs g).map_eq_zero_iff]
    have e3 : phiLayerEquiv Q hQ hR hall Λ ρ hρ hs g (Submodule.Quotient.mk y) =
        x • phiLayerGen Q Λ ρ hs g := by
      rw [leftStandard_mk_eq_smul_unit, map_smul]
      congr 1
      exact phiLayerMap_unit ρ hs hρ g
    rw [e3, phiLayerGen, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    rfl
  rw [layerRank_grade_of_generator PhiLT hN g hμ (isHomogeneousSubspace_lIdeal G _ ht)
    (Submodule.restrictScalars_mono k (leftUpper_le_lIdeal Q Λ _ ht)) (by rw [hNg]) hker n]
  rfl

end Count

end Categorification.Stendhal
