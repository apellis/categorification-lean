/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtTorShift
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationTop

/-!
# Corollary 7.10: Tor between `M_λ` and `L_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Corollary 7.10: `Torⁱ(M_λ, L̇_λ) = 0` for `i ≠ 2ρ^∨(λ)` and `Tor^{2ρ^∨(λ)}(M_λ, L̇_λ)` is
one-dimensional.

Here `L_λ` is the simple head `coevaluationHead` of Lemma 7.3 (a right module) and
`M_λ = S(T^λ ⊠ R^{λ*} 1_{d̄})` the standard module of Corollary 7.7 (a left module, as in the
formalization of Corollary 7.7). The horizontal reflection exchanges the two sides of Tor, so
Webster's `Torⁱ(M_λ, L̇_λ)` is `Torⁱ(L_λ, M_λ)`, the cohomology in degree `-i` of the derived
tensor product `L_λ ⊗ᴸ M_λ` (`derivedTensorHomology`).

## Proof

As for Corollary 7.7, the resolution of Proposition 7.6 computes Tor: its terms below the top
degree `|u|` are sums of cut projectives, which `L_λ` kills, so dimension shifting along the
resolution (`nonempty_linearEquiv_derivedTensorHomology_top`) gives
`Torⁱ(L, S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))) = 0` for `i ≠ |u|`
(`isZero_derivedTensorHomology_standard_of_cut`) and `Tor^{|u|} ≅ L e(s)` for the top loading
`s` (`exists_derivedTensorHomology_standard_linearEquiv`). Since `L e(s) ≅ Hom(T e(s), L̇)` is the
top Ext of Corollary 7.7, the expanded standard has `dim Tor^{|ν|} = dim Ext^{|ν|} = ∏ nₐ!`, and
it is a sum of `∏ nₐ!` copies of `M_λ`; comparing dimensions gives
`dim Tor^{|ν|}(L_λ, M_λ) = 1` (`finrank_derivedTensorHomology_coevaluationHead`).

The grading shift `(-2⟨λ, ρ⟩)` of the printed statement is not recorded (ungraded).
-/

universe w

open CategoryTheory Abelian Limits MulOpposite DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

/-! ### Additive functors on bilimit bicones -/

section BiconeMap

variable {k R : Type} [Field k] [Ring R] {J : Type} [Fintype J] [DecidableEq J]
  (G : ModuleCat.{0} R ⥤ ModuleCat.{0} k) [G.Additive]
  {F : J → ModuleCat.{0} R} {c : Bicone F}

/-- An additive functor to `k`-modules sends a bilimit bicone to a product. -/
def biconeMapLinearEquiv (hc : c.IsBilimit) :
    G.obj c.pt ≃ₗ[k] (∀ j, G.obj (F j)) where
  toFun x j := (G.map (c.π j)).hom x
  map_add' x y := by ext j; simp
  map_smul' r x := by ext j; simp
  invFun y := ∑ j, (G.map (c.ι j)).hom (y j)
  left_inv x := by
    have h := congrArg (fun f => (G.map f).hom x) (IsBilimit.total hc)
    simp only [G.map_sum, G.map_comp, G.map_id, ModuleCat.hom_sum, ModuleCat.hom_comp,
      ModuleCat.hom_id, LinearMap.id_apply, LinearMap.sum_apply, LinearMap.comp_apply] at h
    exact h
  right_inv y := by
    funext j
    simp only [map_sum]
    rw [Finset.sum_eq_single j]
    · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, bicone_ι_π_self,
        G.map_id]
      rfl
    · intro i _ hij
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← G.map_comp, bicone_ι_π_ne _ hij,
        G.map_zero]
      rfl
    · simp

end BiconeMap

namespace Stendhal

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

/-! ### Sums of cut projectives -/

/-- A sum of loading projectives whose loadings kill `L` is spanned by elements fixed by
idempotents killing `L`. -/
theorem LoadingSum.mem_span_of_killed {Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {W : Multiset (List (I ⊕ Fin (ℓ + 1)))} (hY : LoadingSum Y W)
    (L : Type) [AddCommGroup L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
    (hW : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), s.word ∈ W →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0)
    (y : Y) :
    y ∈ Submodule.span (TensorProductAlgebra k Q Λ ν)
      {y : Y | ∃ e : TensorProductAlgebra k Q Λ ν, e • y = y ∧ ∀ m : L, op e • m = 0} := by
  classical
  obtain ⟨ι, _, s, hs, hL, ⟨f⟩⟩ := hY
  have hmem : ∀ a, (s a).word ∈ W := fun a =>
    hL ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
  let ε : ∀ a, loadingProj Q Λ (s a) (hs a) := fun a =>
    (⟨loadingIdem Q Λ (s a) (hs a), (isIdempotentElem_mk_e (s a) (hs a)).eq⟩ :
      lIdeal (loadingIdem Q Λ (s a) (hs a)))
  have hy : y = ∑ a, (Subtype.val (f y a) : TensorProductAlgebra k Q Λ ν) •
      f.symm (Pi.single a (ε a)) := by
    apply f.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    funext b
    rw [Finset.sum_apply, Finset.sum_eq_single b (fun a _ hab => by
      rw [Pi.smul_apply, Pi.single_eq_of_ne' hab, smul_zero]) (by simp)]
    rw [Pi.smul_apply, Pi.single_eq_same]
    exact Subtype.ext (f y b).2.symm
  rw [hy]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨loadingIdem Q Λ (s a) (hs a), ?_, hW (s a) (hs a) (hmem a)⟩
  rw [← map_smul, ← Pi.single_smul]
  congr 2
  exact Subtype.ext (isIdempotentElem_mk_e (s a) (hs a)).eq

/-! ### Tor out of a standard module into a module killed by the cuts -/

section Tor

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  (L : Type) [AddCommGroup L] [Module k L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} k]

include hR hall in
/-- **Tor from a module killed by the cuts to a standard module vanishes off the top degree**
(Webster, arXiv:1309.3796v3, §7.1, Corollary 7.10, vanishing part): if `L e(s) = 0` for every
red-ordered loading `s` whose last strand is not the last red strand, then
`Torᵢ(L, S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))) = 0` for `i ≠ |u|`; that is, the cohomology of the
derived tensor product vanishes in degrees `n ≠ -|u|`. Under the route hypothesis `hall` of
Proposition 7.6. -/
theorem isZero_derivedTensorHomology_standard_of_cut
    (hL : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0)
    (n : ℤ) (hn : n ≠ -(u.length : ℤ)) :
    IsZero (derivedTensorHomology.{w} k L n
      (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u))) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  have hlow : ∀ m < u.length, ∀ j : ℤ,
      IsZero (derivedTensorHomology.{w} k L j (P.complex.X m)) := fun m hm j =>
    isZero_derivedTensorHomology_of_projective_span L _ (fun y => (hP m).mem_span_of_killed L
      (fun s hs hmem => hL s hs (not_hasLastRed_of_mem_websterWords _ _
        (by simpa using hm) hmem)) y) j
  obtain ⟨e⟩ := nonempty_linearEquiv_derivedTensorHomology_top L P u.length hz hlow n
  have htop : IsZero (derivedTensorHomology.{w} k L (n + u.length) (P.complex.X u.length)) :=
    isZero_homology_of_isZero_intHomology k _ _
      (isZero_derivedTensor_homology_of_projective (A := k)
        (B := TensorProductAlgebra k Q Λ ν) L (P.complex.X u.length) _ (by omega))
  have := ModuleCat.isZero_iff_subsingleton.mp htop
  exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton

variable [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]

include hR hall in
/-- **Tor in the top degree** (Webster, arXiv:1309.3796v3, §7.1, proof of Corollary 7.10): if
`L` is killed by the cuts, then `Tor_{|u|}(L, S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u.reverse))) ≅ L e(s)`
for the loading `s` with word `t, u, λ_ℓ`. Under the route hypothesis `hall` of
Proposition 7.6. -/
theorem exists_derivedTensorHomology_standard_linearEquiv
    (hL : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0) :
    ∃ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word = t.word.map (addRedColor ℓ) ++ u.map Sum.inl ++ [Sum.inr (Fin.last ℓ)] ∧
        Nonempty (derivedTensorHomology.{w} k L (-(u.length : ℤ))
          (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) ≃ₗ[k]
          BalancedTensor.idemPart k L (op (loadingIdem Q Λ s hs))) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have htop := hP u.reverse.length
  rw [websterWords_length, websterWord_range, List.reverse_reverse, List.length_reverse] at htop
  obtain ⟨s, hs, hw, ⟨i⟩⟩ := htop.exists_equiv_of_singleton
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  have hlow : ∀ m < u.length, ∀ j : ℤ,
      IsZero (derivedTensorHomology.{w} k L j (P.complex.X m)) := fun m hm j =>
    isZero_derivedTensorHomology_of_projective_span L _ (fun y => (hP m).mem_span_of_killed L
      (fun s hs hmem => hL s hs (not_hasLastRed_of_mem_websterWords _ _
        (by simpa using hm) hmem)) y) j
  obtain ⟨e₁⟩ := nonempty_linearEquiv_derivedTensorHomology_top L P u.length hz hlow
    (-(u.length : ℤ))
  rw [neg_add_cancel] at e₁
  have hM : ∀ (c : k) (m : L), op (algebraMap k (TensorProductAlgebra k Q Λ ν) c) • m = c • m :=
    fun c m => algebraMap_smul (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c m
  exact ⟨s, hs, hw, ⟨e₁.trans ((derivedTensorHomologyLinearEquiv (k := k) L i 0).trans
    (ambientDerivedTensorH0LeftIdealEquiv hM (isIdempotentElem_mk_e s hs)))⟩⟩

end Tor

/-! ### Fixed vectors on the two sides of the reflection -/

section Fixed

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable (L : Type) [AddCommGroup L] [Module k L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]

theorem tensorFlip_algebraMap' (c : k) :
    tensorFlip (Q := Q) (Λ := Λ) (ν := ν) (algebraMap k (TensorProductAlgebra k Q Λ ν) c) =
      algebraMap k _ c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tensorFlip_one]

/-- For an idempotent fixed by the reflection, the vectors of `flipLeft L` fixed by `e` are the
vectors of `L` fixed by `e` acting on the right. -/
def fixedSubspaceFlipLeftEquiv (e : TensorProductAlgebra k Q Λ ν) (he : tensorFlip e = e) :
    fixedSubspace (k := k) (flipLeft Q Λ ν L) e ≃ₗ[k] BalancedTensor.idemPart k L (op e) where
  toFun y := ⟨(@id L y.1), by
    have := y.2
    change op (tensorFlip e) • (@id L y.1) = y.1 at this
    rwa [he] at this⟩
  invFun y := ⟨(show flipLeft Q Λ ν L from (y : L)), by
    change op (tensorFlip e) • (y : L) = y
    rw [he]
    exact y.2⟩
  left_inv y := rfl
  right_inv y := rfl
  map_add' x y := rfl
  map_smul' c y := by
    apply Subtype.ext
    change op (tensorFlip (algebraMap k (TensorProductAlgebra k Q Λ ν) c)) • (@id L y.1) =
      c • (@id L y.1)
    rw [tensorFlip_algebraMap']
    exact algebraMap_smul (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ c (@id L y.1)

end Fixed


/-! ### The divided standard module -/

section Divided

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (d : List (I × ℕ)) (h : θ + wordWt (expandDiv d) 0 = ν)
  (L : Type) [AddCommGroup L] [Module k L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [SMulCommClass k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [HasDerivedCategory.{w, 0} (TensorProductAlgebra k Q Λ ν)] [HasDerivedCategory.{w, 0} k]

/-- The derived tensor cohomology of a sum of `card J` copies. -/
private def derivedTensorHomologyBiconeEquiv (n : ℤ) {J : Type} [Fintype J] [DecidableEq J]
    {F : J → ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)} {c : Bicone F} (hc : c.IsBilimit) :
    derivedTensorHomology.{w} k L n c.pt ≃ₗ[k] (∀ j, derivedTensorHomology.{w} k L n (F j)) :=
  biconeMapLinearEquiv (degreeZeroModuleFunctor _ ⋙ DG.DerivedCategory.Q ⋙ derivedTensor.{w} k _ L ⋙
    homologyFunctor (A := k) k n) hc

include hR hall in
/-- **Tor into the divided standard module vanishes off the top degree** (Webster,
arXiv:1309.3796v3, §7.1, Corollary 7.10, vanishing part, for `M_λ`): if `L` is killed by the
cuts, then `Torᵢ(L, S(T^{λ'} e(t) ⊠ R^{λ_ℓ} 1_{d̄})) = 0` for `i ≠ |d̂|`, since this standard
module is a summand of `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(d̂))`. Under the route hypothesis `hall` of
Proposition 7.6. -/
theorem isZero_derivedTensorHomology_standard_cycDivProj_of_cut
    (hL : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0)
    (n : ℤ) (hn : n ≠ -((expandDiv d).length : ℤ)) :
    IsZero (derivedTensorHomology.{w} k L n
      (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycDivProj Q Λ d))) := by
  classical
  obtain ⟨J, _, _, ι, π, hιπ, htot, hc⟩ := exists_bicone_cycWord_cycDivProj Q Λ d
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h (oldProj Q Λ θ t ht) ι π hιπ htot
  have h0 := isZero_derivedTensorHomology_standard_of_cut Q Λ hQ hR hall t ht (expandDiv d) h L
    hL n hn
  have := ModuleCat.isZero_iff_subsingleton.mp h0
  have hsub := @Equiv.subsingleton _ _ (derivedTensorHomologyBiconeEquiv Q Λ L n hB).symm.toEquiv
    this
  obtain ⟨j⟩ : Nonempty J := Fintype.card_pos_iff.1 (hc ▸ prod_factorial_pos d)
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun x y => congrFun (Subsingleton.elim (fun _ : J => x) (fun _ => y)) j⟩

variable [IsScalarTower k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]

include hR hall in
/-- **Tor and Ext of the divided standard module have the same top dimension** (Webster,
arXiv:1309.3796v3, §7.1, proof of Corollary 7.10): if `L` is killed by the cuts, then
`dim Tor_{|d̂|}(L, M) = dim Ext^{|d̂|}(M, L̇)` for `M = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} 1_{d̄})`, when the
latter is finite. Both are computed by the top term `T^λ e(s)` of the resolution of the expanded
standard module: `Tor` gives `L e(s)` and `Ext` gives `Hom(T^λ e(s), L̇)`. Under the route
hypothesis `hall` of Proposition 7.6. -/
theorem finrank_derivedTensorHomology_standard_cycDivProj_eq_finrank_ext
    [HasExt.{0} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]
    (hL : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0)
    [FiniteDimensional k (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycDivProj Q Λ d))
      (flipLeft Q Λ ν L) (expandDiv d).length)] :
    Module.finrank k (derivedTensorHomology.{w} k L (-((expandDiv d).length : ℤ))
        (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycDivProj Q Λ d))) =
      Module.finrank k (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycDivProj Q Λ d))
        (flipLeft Q Λ ν L) (expandDiv d).length) := by
  classical
  obtain ⟨J, _, _, ι, π, hιπ, htot, hc⟩ := exists_bicone_cycWord_cycDivProj Q Λ d
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h (oldProj Q Λ θ t ht) ι π hιπ htot
  have E₁ := Abelian.Ext.biproductLinearEquiv (R := k) hB (flipLeft Q Λ ν L) (expandDiv d).length
  obtain ⟨s, hs, hw, ⟨E₂⟩⟩ := exists_extLinearEquiv_standard Q Λ hQ hR hall t ht (expandDiv d)
    h (flipLeft Q Λ ν L) fun p hp s hs hmem => subsingleton_hom_loadingProj_flipLeft s hs
      (hL s hs (not_hasLastRed_of_mem_websterWords _ _
        (by rw [List.length_reverse]; omega) hmem))
  obtain ⟨s', hs', hw', ⟨E₃⟩⟩ := exists_derivedTensorHomology_standard_linearEquiv Q Λ hQ hR
    hall t ht (expandDiv d) h L hL
  obtain rfl : s = s' := Seq.word_injective (hw.trans hw'.symm)
  have E₄ := lIdealHomEquiv (k := k) (isIdempotentElem_mk_e s hs) (flipLeft Q Λ ν L)
  have E₅ := fixedSubspaceFlipLeftEquiv L (loadingIdem Q Λ s hs)
    (by rw [loadingIdem, tensorFlip_mk_e])
  have E₆ := derivedTensorHomologyBiconeEquiv Q Λ L (-((expandDiv d).length : ℤ)) hB
  have : Nonempty J := Fintype.card_pos_iff.1 (hc ▸ prod_factorial_pos d)
  exact finrank_eq_of_linearEquiv_pi rfl
    (E₆.symm.trans (E₃.trans (E₅.symm.trans (E₄.symm.trans (E₂.symm.trans E₁)))))

end Divided

end Stendhal

/-! ### Corollary 7.10 for the coevaluation word -/

namespace KLR.CycKLR

open KLRAlgebra QuantumGroup QuantumGroup.UDot

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "TL" d:arg => Stendhal.TensorProductAlgebra k Q
  (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d)

omit [Fintype I] in
/-- The right action on `L_λ` is `k`-linear. -/
instance isScalarTower_coevaluationHead (d : List (I × ℕ)) :
    IsScalarTower k (TL d)ᵐᵒᵖ (Stendhal.coevaluationHead Q Λ RD highest d) :=
  Submodule.Quotient.isScalarTower _ _

include hP in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.10 (vanishing part)**, ungraded:
`Torᵢ(M_λ, L̇_λ) = 0` for `i ≠ |d̂|`, for the simple head `L_λ = coevaluationHead d` of
Lemma 7.3 and `M_λ = S(T^{λ} ⊠ R^{λ*} 1_{d̄})`. Here `Torᵢ(M_λ, L̇_λ)` is `Torᵢ(L_λ, M_λ)`
(the two sides are exchanged by the horizontal reflection), the cohomology of `L_λ ⊗ᴸ M_λ` in
degree `-i`. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem _root_.Categorification.Stendhal.isZero_derivedTensorHomology_cycDivProj_coevaluationHead
    (d : List (I × ℕ)) (hQ : KLRSymm Q)
    (hall : Stendhal.AllFiniteDeltaInjective Q (coevaluationLabels Λ RD highest (expandDiv d)) hQ)
    {θ : Multiset I} (t : Seq (Stendhal.stendhalWeight 1 θ)) (ht : Stendhal.IsRedOrdered t)
    (h : θ + Stendhal.wordWt (expandDiv d) 0 = expandDiv d)
    [HasDerivedCategory.{w, 0} (TL d)] [HasDerivedCategory.{w, 0} k]
    (n : ℤ) (hn : n ≠ -((expandDiv d).length : ℤ)) :
    IsZero (derivedTensorHomology.{w} k (Stendhal.coevaluationHead Q Λ RD highest d) n
      (Stendhal.tensorStd Q (coevaluationLabels Λ RD highest (expandDiv d)) hQ h
        (Stendhal.oldProj Q _ θ t ht) (Stendhal.cycDivProj Q _ d))) :=
  Stendhal.isZero_derivedTensorHomology_standard_cycDivProj_of_cut Q _ hQ hP hall t ht d h _
    (fun s hs hcut y => Stendhal.coevaluationHead_cut Q Λ RD highest d s hs hcut y) n hn

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.10 (top degree)**, ungraded: for a reduced
expression `w` of the longest element and `d` the divided coevaluation word of Definition 7.1,
`Tor_{|ν|}(M_λ, L̇_λ)` is one-dimensional, `|ν| = 2ρ^∨(λ)`, for the simple head `L_λ` of Lemma 7.3
and `M_λ = S(T^{λ} ⊠ R^{λ*} 1_{d̄})` as in Corollary 7.7. Here `Torᵢ(M_λ, L̇_λ)` is
`Torᵢ(L_λ, M_λ)`, the cohomology of `L_λ ⊗ᴸ M_λ` in degree `-i`. Under the route hypothesis
`hall` of Proposition 7.6. -/
theorem _root_.Categorification.Stendhal.finrank_derivedTensorHomology_coevaluationHead
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)
    (hQ : KLRSymm Q)
    (hall : Stendhal.AllFiniteDeltaInjective Q (coevaluationLabels Λ RD highest
      (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) hQ)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)) 0 = expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))
    [HasDerivedCategory.{w, 0} (TL (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))] [HasDerivedCategory.{w, 0} k] :
    Module.finrank k (derivedTensorHomology.{w} k
      (Stendhal.coevaluationHead Q Λ RD highest (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))
      (-((expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)).length : ℤ))
      (Stendhal.tensorStd Q (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) hQ h
        (Stendhal.oldProj Q _ 0 t ht) (Stendhal.cycDivProj Q _ (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)))) = 1 := by
  let : HasExt.{0} (ModuleCat.{0} (TL (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) := CategoryTheory.hasExt_of_enoughProjectives _
  have hE := Stendhal.finrank_ext_standard_coevaluationHead hP Λ RD highest hΛ hR P weight
    hweight match_weight w hw hlong hQ hall t ht h
  have : FiniteDimensional k _ := Module.finite_of_finrank_eq_succ hE
  have := isScalarTower_coevaluationHead (Q := Q) Λ RD highest
    (Stendhal.coevaluationDividedWord (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix)
      weight w)
  rw [Stendhal.finrank_derivedTensorHomology_standard_cycDivProj_eq_finrank_ext Q _ hQ hP hall t
    ht _ h _ (fun s hs hcut y => Stendhal.coevaluationHead_cut Q Λ RD highest _ s hs hcut y)]
  exact hE

local notation "QK" => Q

include hP in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.10 (vanishing part)**, ungraded, for
Rouquier parameters with symmetric parameters, with no route hypothesis. -/
theorem _root_.Categorification.Stendhal.isZero_derivedTensorHomology_cycDivProj_coevaluationHead_of_rouquier
    (hQs : KLRSymm QK) (d : List (I × ℕ))
    {θ : Multiset I} (t : Seq (Stendhal.stendhalWeight 1 θ)) (ht : Stendhal.IsRedOrdered t)
    (h : θ + Stendhal.wordWt (expandDiv d) 0 = expandDiv d)
    [HasDerivedCategory.{w, 0} (Stendhal.TensorProductAlgebra k QK
      (coevaluationLabels Λ RD highest (expandDiv d)) (expandDiv d))]
    [HasDerivedCategory.{w, 0} k]
    (n : ℤ) (hn : n ≠ -((expandDiv d).length : ℤ)) :
    IsZero (derivedTensorHomology.{w} k (Stendhal.coevaluationHead QK Λ RD highest d) n
      (Stendhal.tensorStd QK (coevaluationLabels Λ RD highest (expandDiv d)) hQs h
        (Stendhal.oldProj QK _ θ t ht) (Stendhal.cycDivProj QK _ d))) := by
  refine Stendhal.isZero_derivedTensorHomology_cycDivProj_coevaluationHead hP Λ RD highest d hQs
    ?_ t ht h n hn
  convert Stendhal.allFiniteDeltaInjective_of_rouquier
    (Λ := coevaluationLabels Λ RD highest (expandDiv d)) hP hQs

include hP hΛ hR in
/-- **Webster, arXiv:1309.3796v3, §7.1, Corollary 7.10 (top degree)**, ungraded, for
Rouquier parameters with symmetric parameters, with no route hypothesis. -/
theorem _root_.Categorification.Stendhal.finrank_derivedTensorHomology_coevaluationHead_of_rouquier
    (hQs : KLRSymm QK)
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Module.Dual K H))
    (match_weight : ∀ i, (weight : Module.Dual K H) (P.coroot i) =
      (RD.pair.flip highest ((projectiveRootDatum RD).coroot i) : K))
    (w : List I)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)
    (t : Seq (Stendhal.stendhalWeight 1 (0 : Multiset I))) (ht : Stendhal.IsRedOrdered t)
    (h : 0 + Stendhal.wordWt (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)) 0 = expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))
    [HasDerivedCategory.{w, 0} (Stendhal.TensorProductAlgebra k QK
      (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)))]
    [HasDerivedCategory.{w, 0} k] :
    Module.finrank k (derivedTensorHomology.{w} k
      (Stendhal.coevaluationHead QK Λ RD highest (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))
      (-((expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)).length : ℤ))
      (Stendhal.tensorStd QK (coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) hQs h
        (Stendhal.oldProj QK _ 0 t ht) (Stendhal.cycDivProj QK _ (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w)))) = 1 := by
  refine Stendhal.finrank_derivedTensorHomology_coevaluationHead hP Λ RD highest hΛ hR P weight
    hweight match_weight w hw hlong hQs ?_ t ht h
  convert Stendhal.allFiniteDeltaInjective_of_rouquier
    (Λ := coevaluationLabels Λ RD highest (expandDiv (Stendhal.coevaluationDividedWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w))) hP hQs

end KLR.CycKLR

end Categorification
