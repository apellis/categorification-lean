/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtVacuumFactor
import Categorification.WeightedKLR.Rigidity.RigidityExtDualStandardTop
import Categorification.WeightedKLR.Rigidity.RigidityExtBicone

/-!
# The last term of the resolution by standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof of
Proposition 7.8, second clause. In the resolution `0 → M_N → ⋯ → M_0 → X → 0` of
`exists_stdResolution`, `N = |ν|`, the last term `M_N` is a sum of standardizations over the
split `0 + ν`. When the cyclotomic block `R^{λ_ℓ}(ν)` is semisimple with simple `Y₀`, the module
`M_N` is a sum of copies of `S(T^{λ'} e(t) ⊠ Y₀)`, and counting
`Hom(M_N, S(T^{λ'} e(t) ⊠ Y₀)^⋆)` through `Ext^N(X, S^⋆)` for the expanded standard `S` shows
that there is exactly one copy when `Ext^N(S(T^{λ'} e(t) ⊠ Y₀), X)` is one-dimensional.

## Main results

* `Ext.nonempty_linearEquiv_hom_of_chain`: along a resolution ending in degree `N`,
  `Ext^N(K_0, Y) ≅ Hom(M_N, Y)` when `Ext^*(M_n, Y) = 0` for `n < N`.
* `exists_iso_biproduct_stdLayerModule_vacuum`: a standardization over the split `0 + ν` is a sum
  of copies of `S(T^{λ'} e(t) ⊠ Y₀)`.
* `exists_stdResolution_last`: the resolution with `M_N ≅ S(T^{λ'} e(t) ⊠ Y₀)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] (R : Type*) [CommRing R]
  [Linear R C]

/-- **The top degree along a resolution.** Let `S n` be short exact sequences
`0 → K_{n+1} → M_n → K_n → 0` with `M_{N+1} = 0` and `Ext^*(M_n, Y) = 0` for `n < N`. Then
`Ext^N(K_0, Y) ≅ Hom(M_N, Y)`. -/
theorem nonempty_linearEquiv_hom_of_chain (S : ℕ → ShortComplex C)
    (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) (he : ∀ n, (S n).ShortExact) (Y : C)
    (N : ℕ) (hY : ∀ n < N, ∀ i, Subsingleton (Ext.{w} (S n).X₂ Y i))
    (hz : IsZero (S (N + 1)).X₂) :
    Nonempty (Ext.{w} (S 0).X₃ Y N ≃ₗ[R] ((S N).X₂ ⟶ Y)) := by
  obtain ⟨f⟩ := (exists_linearEquiv_of_chain R S hs he Y N hY).1 N le_rfl 0
  have := (he (N + 1)).epi_g
  have h3 : IsZero (S (N + 1)).X₃ := IsZero.of_epi (S (N + 1)).g hz
  obtain ⟨e⟩ := hs N
  have h1 : IsZero (S N).X₁ := h3.of_iso e.symm
  have : IsIso (S N).g := ((he N).isIso_g_iff).2 h1
  exact ⟨f.symm.trans (linearEquiv₀.trans
    (Linear.homCongr R (asIso (S N).g).symm (Iso.refl Y)))⟩

end CategoryTheory.Abelian.Ext

/-- `dim (J → V) = |J| dim V`, also when `V` is infinite-dimensional. -/
theorem finrank_fun_eq_card_mul {k : Type*} [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    (J : Type*) [Fintype J] :
    Module.finrank k (J → V) = Fintype.card J * Module.finrank k V := by
  by_cases hV : Module.Finite k V
  · rw [Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  · rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
    · rw [Fintype.card_eq_zero, zero_mul]
      exact Module.finrank_zero_of_subsingleton
    · rw [Module.finrank_of_not_finite hV, mul_zero]
      refine Module.finrank_of_not_finite fun h => hV ?_
      exact Module.Finite.of_surjective (LinearMap.proj j : (J → V) →ₗ[k] V)
        fun v => ⟨fun _ => v, rfl⟩

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Told" => TensorProductAlgebra k Q (old)
local notation "Cyc" => CycKLR k Q (aΛ)

section Layer

variable (hQ : KLRSymm Q)

/-- `T^{λ'} e(t) ≅ T^{λ'}_0` when `e(t) = 1` in `T^{λ'}_0`. -/
def oldProjVacuumEquiv (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = 1) :
    vacuumRegular Q Λ ≃ₗ[Told 0] oldProj Q Λ 0 t ht where
  toFun a := ⟨a, by
    change (a : Told 0) * TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = a
    rw [het, mul_one]⟩
  invFun x := (x.1 : Told 0)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The standardization `S(X ⊠ Y₀ⁿ)` is a sum of `n` copies of `S(X ⊠ Y₀)`. -/
def tensorStdPiBicone {θ β : Multiset I} (h : θ + β = ν) (X : ModuleCat.{0} (Told θ))
    (Y₀ : ModuleCat.{0} (Cyc β)) (n : ℕ) :
    Bicone (fun _ : Fin n => tensorStd Q Λ hQ h X Y₀) :=
  tensorStdBicone Q Λ hQ h X (Y' := ModuleCat.of (Cyc β) (Fin n → Y₀))
    (fun j => LinearMap.single (Cyc β) (fun _ : Fin n => Y₀) j)
    (fun j => LinearMap.proj j) (fun i j => by
      split_ifs with hij
      · subst hij; exact LinearMap.proj_comp_single_same _ _ _
      · exact LinearMap.proj_comp_single_ne _ _ _ _ (Ne.symm hij))

/-- `tensorStdPiBicone` is a bilimit. -/
def tensorStdPiBiconeIsBilimit {θ β : Multiset I} (h : θ + β = ν) (X : ModuleCat.{0} (Told θ))
    (Y₀ : ModuleCat.{0} (Cyc β)) (n : ℕ) :
    (tensorStdPiBicone Q Λ hQ h X Y₀ n).IsBilimit :=
  tensorStdBiconeIsBilimit Q Λ hQ h X _ _ _ (by
    refine LinearMap.ext fun y => funext fun i => ?_
    rw [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_eq_single i
      (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp)

/-- **A standardization over the split `0 + β` is a sum of copies of `S(T^{λ'} e(t) ⊠ Y₀)`**,
when every finitely generated module over `R^{λ_ℓ}_β` is a sum of copies of `Y₀` and
`T^{λ'}_0 = T^{λ'} e(t)`. -/
theorem exists_iso_biproduct_stdLayerModule_vacuum {β : Multiset I} (h₀ : 0 + β = ν)
    (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (Cyc β))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (Cyc β) M] [Module.Finite (Cyc β) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[Cyc β] (Fin n → Y₀)))
    (c : StdLayer Q Λ ν) (hc : Multiset.card c.θ = 0) [FiniteDimensional k c.M.carrier] :
    ∃ n : ℕ, Nonempty (stdLayerModule Q Λ hQ c ≅
      ⨁ fun _ : Fin n => tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) := by
  obtain ⟨θ, β', h, M⟩ := c
  simp only [Multiset.card_eq_zero] at hc
  subst hc
  obtain rfl : β' = β := add_left_cancel (h.trans h₀.symm)
  let := vacuumRestrictInst Q Λ M
  have : IsScalarTower k (Cyc β') M.carrier := ⟨fun r b m => by
    change ((1 : Told 0) ⊗ₜ[k] (r • b) : parabolicFactorAlgebra Q Λ 0 β') • m =
      r • (((1 : Told 0) ⊗ₜ[k] b : parabolicFactorAlgebra Q Λ 0 β') • m)
    rw [TensorProduct.tmul_smul, smul_assoc]⟩
  have : Module.Finite (Cyc β') M.carrier := Module.Finite.of_restrictScalars_finite k _ _
  obtain ⟨n, ⟨g⟩⟩ := hss M.carrier
  let e : M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ 0 β']
      (tensorFactor Q Λ (oldProj Q Λ 0 t ht) (ModuleCat.of (Cyc β') (Fin n → Y₀))).carrier :=
    (vacuumTensorEquiv Q Λ M).symm.trans
      (tensorFactorCongr Q Λ (oldProjVacuumEquiv Q Λ t ht het) g)
  exact ⟨n, ⟨(stdLayerEquiv Q Λ hQ h e).toModuleIso ≪≫
    biproduct.uniqueUpToIso _ (tensorStdPiBiconeIsBilimit Q Λ hQ h _ Y₀ n)⟩⟩

end Layer

section Last

variable (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

include hR hall in
/-- **Proposition 7.8, second clause** (Webster, arXiv:1309.3796v3, §7.1), ungraded, in the
repaired reading of `exists_stdResolution`. Let `X` be finite-dimensional and killed by every
loading idempotent with a black strand right of the last red strand, `T^{λ'}_0 = T^{λ'} e(t)`,
and let every finitely generated module over `R^{λ_ℓ}(ν)` be a sum of copies of `Y₀`, with
`R^{λ_ℓ} e(u)` a nonempty sum of copies of `Y₀`. If `Ext^{|ν|}(S(T^{λ'} e(t) ⊠ Y₀), X)` is
one-dimensional, the resolution of `exists_stdResolution` can be taken with last term
`M_{|ν|} ≅ S(T^{λ'} e(t) ⊠ Y₀)`; moreover `Hom(S(T^{λ'} e(t) ⊠ Y₀), S(T^{λ'} e(t) ⊠ Y₀)^⋆)` is
one-dimensional. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem exists_stdResolution_last (X : ModuleCat.{0} T) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (Cyc (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (Cyc (wordWt u 0)) M]
      [Module.Finite (Cyc (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[Cyc (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[Cyc (wordWt u 0)] cycWord Q Λ u))
    (π : J → (cycWord Q Λ u →ₗ[Cyc (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{w} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    ∃ S : ℕ → ShortComplex (ModuleCat.{0} T), Nonempty ((S 0).X₃ ≅ X) ∧
      (∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) ∧ (∀ n, (S n).ShortExact) ∧
      (∀ n ≤ Multiset.card ν, StdSum Q Λ hQ (Multiset.card ν + ℓ - n) (S n).X₂) ∧
      (∀ n, Multiset.card ν < n → IsZero (S n).X₂) ∧
      Nonempty ((S (Multiset.card ν)).X₂ ≅ tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) ∧
      Module.finrank k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀ ⟶
        starDualObj k σT (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) = 1 := by
  classical
  obtain ⟨S, h0, hs, he, hstd, hz⟩ := exists_stdResolution Q Λ hQ hR hall X hX
  refine ⟨S, h0, hs, he, hstd, hz, ?_⟩
  have hlen : u.length = Multiset.card ν := by
    have hc := congrArg Multiset.card h₀
    rwa [← coe_reverse_eq_wordWt, zero_add, Multiset.coe_card, List.length_reverse] at hc
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h₀ (oldProj Q Λ 0 t ht) ι π hιπ htot
  have hσ : ∀ z : T, StarDual.bar σT (StarDual.bar σT z) = z := fun z => tensorFlip_tensorFlip z
  have hc : ∀ c : k, StarDual.bar σT (algebraMap k T c) = algebraMap k T c :=
    fun c => tensorFlip_algebraMap' c
  -- `Ext^*(M_n, ∇) = 0` for `n < |ν|`, `∇` the dual of the expanded standard.
  have hY : ∀ n < Multiset.card ν, ∀ i, Subsingleton (Ext.{w} (S n).X₂ (starDualObj k σT
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (cycWord Q Λ u))) i) := by
    intro n hn i
    obtain ⟨J', _, c, hcq, hfin, ⟨e⟩⟩ := hstd n hn.le
    refine Ext.subsingleton_of_iso e _ i (subsingleton_ext_pi _ _ i fun j => ?_)
    have := hfin j
    refine subsingleton_ext_stdLayer_starDual_standard_of_ne Q Λ hQ hR hall (c j) t ht u h₀ i ?_
    rintro ⟨h1, -⟩
    have := hcq j
    rw [Multiset.card_zero] at h1
    omega
  obtain ⟨E₁⟩ := Ext.nonempty_linearEquiv_hom_of_chain k S hs he _ _ hY (hz _ (by omega))
  obtain ⟨e0⟩ := h0
  have hT := finrank_ext_starDual_standard_top Q Λ hQ hR hall t ht u h₀ X hX
  rw [hlen] at hT
  -- `dim Hom(M_N, ∇) = |J|`.
  have hHom : Module.finrank k ((S (Multiset.card ν)).X₂ ⟶ starDualObj k σT
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (cycWord Q Λ u))) = Fintype.card J := by
    rw [← E₁.finrank_eq, ← (Ext.linearEquivOfIso k e0 _ _).finrank_eq, hT]
    refine (Ext.biproductLinearEquiv (R := k) hB X _).finrank_eq.trans ?_
    rw [finrank_fun_eq_card_mul, htop, mul_one]
  -- `dim Hom(M_N, M_λ^⋆) = 1`.
  have hHom' : Module.finrank k ((S (Multiset.card ν)).X₂ ⟶ starDualObj k σT
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) = 1 := by
    have E := ((StarDual.homSwapEquiv hσ hc
        (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (cycWord Q Λ u)) (S (Multiset.card ν)).X₂).trans
      (Limits.Bicone.homLinearEquiv (R := k) hB _)).trans
      (LinearEquiv.piCongrRight fun _ => StarDual.homSwapEquiv hσ hc (S (Multiset.card ν)).X₂
        (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))
    have h2 := E.finrank_eq
    rw [hHom, finrank_fun_eq_card_mul] at h2
    have hJ := Fintype.card_pos (α := J)
    nlinarith
  -- `M_N` is a sum of copies of `M_λ`.
  obtain ⟨J', _, c, hcq, hfin, ⟨e⟩⟩ := hstd (Multiset.card ν) le_rfl
  have hc0 : ∀ i, Multiset.card (c i).θ = 0 := fun i => by have := hcq i; omega
  choose n hn using fun i => by
    have := hfin i
    exact exists_iso_biproduct_stdLayerModule_vacuum Q Λ hQ h₀ t ht het Y₀ hss (c i) (hc0 i)
  let eA : (S (Multiset.card ν)).X₂ ≅
      ⨁ fun _ : (Σ i, Fin (n i)) => tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀ :=
    e ≪≫ (ModuleCat.biproductIsoPi _).symm ≪≫ biproduct.mapIso (fun i => (hn i).some) ≪≫
      biproductBiproductIso _ _
  have hA : Fintype.card (Σ i, Fin (n i)) = 1 := by
    have E := (Linear.homCongr k eA (Iso.refl (starDualObj k σT
        (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)))).trans
      (Limits.Bicone.homLinearEquiv (R := k) (biproduct.isBilimit _) _)
    have h2 := E.finrank_eq
    rw [hHom', finrank_fun_eq_card_mul] at h2
    exact Nat.eq_one_of_mul_eq_one_right h2.symm
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hA
  refine ⟨⟨eA ≪≫ biproductUniqueIso _⟩, ?_⟩
  exact (Linear.homCongr k (eA ≪≫ biproductUniqueIso _) (Iso.refl _)).finrank_eq.symm.trans hHom'

end Last

end Categorification.Stendhal

end
