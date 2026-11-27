/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtLastTerm

/-!
# Ext into the last term of the resolution

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Corollary 7.9: `Extⁱ(L_λ, M_λ)` is one-dimensional for `i = 2ρ^∨(λ)` and zero otherwise. Along
the resolution of `exists_stdResolution_last`, `Extⁱ(X, M)` for `M = S(T^{λ'} e(t) ⊠ Y₀)` is
`Ext^{i-N}(M_N, M) = Ext^{i-N}(M, M)`, since standardizations at higher levels have no `Ext` into
`M`. The standard `M` is a summand of the standard `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`, whose
resolution (Proposition 7.6) has no maps to `M` or `M^⋆` beyond degree `0`; this gives
`Ext^{>0}(M, M) = 0` and `dim End(M) = dim Hom(M, M^⋆) = 1`.

## Main results

* `ProjectiveResolution.homLinearEquivZero`: `Hom(X, Y) ≅ Hom(P₀, Y)` when `Hom(P₁, Y) = 0`.
* `subsingleton_ext_tensorStd_self`, `finrank_end_tensorStd`: `Ext^{>0}(M, M) = 0`,
  `dim End(M) = 1`.
* `ext_stdResolution_last`: `Extⁱ(X, M)` is one-dimensional for `i = N` and zero otherwise.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] {X Y : C} (P : ProjectiveResolution X)
  (R : Type*) [Ring R] [Linear R C]

/-- `Hom(X, Y) ≅ Hom(P₀, Y)` when there are no nonzero maps `P₁ → Y`. -/
noncomputable def homLinearEquivZero [Subsingleton (P.complex.X 1 ⟶ Y)] :
    (X ⟶ Y) ≃ₗ[R] (P.complex.X 0 ⟶ Y) :=
  LinearEquiv.ofBijective (Linear.leftComp R Y (P.π.f 0))
    ⟨fun _ _ h => (cancel_epi (P.π.f 0)).1 h, fun g =>
      let l := CokernelCofork.IsColimit.desc' P.isColimitCokernelCofork g
        (Subsingleton.elim _ _)
      ⟨l.1, l.2⟩⟩

end CategoryTheory.ProjectiveResolution

namespace Categorification.Stendhal

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

/-- A quotient of a finite-dimensional module is finite-dimensional. -/
theorem finiteDimensional_of_surjective {M N : ModuleCat.{0} T} [FiniteDimensional k M]
    (f : M ⟶ N) (hf : Function.Surjective f) : FiniteDimensional k N :=
  Module.Finite.of_surjective (f.hom.restrictScalars k) hf

/-- Loading projectives are finite-dimensional when `T` is. -/
theorem finiteDimensional_loadingProj [Module.Finite k T] (s : Seq (stendhalWeight (ℓ + 1) ν))
    (hs : IsRedOrdered s) : FiniteDimensional k (loadingProj Q Λ s hs) := by
  let f : loadingProj Q Λ s hs →ₗ[k] T :=
    { toFun := fun x => (x : lIdeal (loadingIdem Q Λ s hs)).1
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        change algebraMap k T c * _ = c • _
        rw [Algebra.smul_def] }
  exact Module.Finite.of_injective f fun x y h => Subtype.ext h

omit [DecidableEq I] in
/-- The last red strand of a word of the resolution of Proposition 7.6 in degree `j` is at a
position `|t| + j` of the loading. -/
theorem exists_pos_of_mem_websterWords {tw : List (I ⊕ Fin (ℓ + 1))} {u : List I} {j : ℕ}
    {s : Seq (stendhalWeight (ℓ + 1) ν)} (hs : s.word ∈ websterWords tw u j) :
    ∃ a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν)), a.val = tw.length + j := by
  obtain ⟨Tm, hTm, hw⟩ := Multiset.mem_map.1 hs
  obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 hTm
  have hlen := length_pickIn u hle
  have hl : (websterWord tw u Tm).length = tw.length + (pickIn u Tm).length + 1 +
      (pickOut u Tm).length := by
    simp [websterWord]
    omega
  refine ⟨⟨tw.length + j, ?_⟩, rfl⟩
  rw [← Seq.length_word s, ← hw, hl, hlen, hcard]
  omega

/-- A module killed after position `ℓ` has no maps from the projectives of the resolution of a
standard module `S(T^{λ'} e(t) ⊠ ·)` at `θ = 0` in positive degree. -/
theorem subsingleton_hom_loadingProj_of_killedAfter {Y : ModuleCat.{0} T}
    (hY : KilledAfter Q Λ ℓ Y) (t : Seq (stendhalWeight ℓ (0 : Multiset I))) (u : List I) {j : ℕ}
    (hj : 0 < j) (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (hmem : s.word ∈ websterWords (t.word.map (addRedColor ℓ)) u j) :
    Subsingleton (loadingProj Q Λ s hs ⟶ Y) := by
  have hlen : (t.word.map (addRedColor ℓ)).length = ℓ := by
    rw [List.length_map, Seq.length_word]; simp [stendhalWeight]
  obtain ⟨a, ha⟩ := exists_pos_of_mem_websterWords hmem
  exact subsingleton_hom_loadingProj s hs fun y =>
    hY s hs a (by omega) (lbl_of_word_eq_websterWord hmem a ha) y

/-- A standard module with no black strands left of the last red strand is killed after `ℓ`. -/
theorem killedAfter_tensorStd_zero (hQ : KLRSymm Q) {β : Multiset I} (h : 0 + β = ν)
    (X : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) 0))
    (Y : ModuleCat.{0} (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β)) :
    KilledAfter Q Λ ℓ (tensorStd Q Λ hQ h X Y) := by
  have := killedAfter_stdLayerModule Q Λ hQ (tensorLayer Q Λ h X Y)
  simp only [tensorLayer, Multiset.card_zero, zero_add] at this
  exact this

section Self

variable (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]
  (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
  {Y₀ : ModuleCat.{0} (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
    (wordWt u 0))}
  {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
  (ι : J → (Y₀ →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
    (wordWt u 0)] cycWord Q Λ u))
  (π : J → (cycWord Q Λ u →ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
    (wordWt u 0)] Y₀))
  (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
  (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)

include hR hall ι π hιπ htot in
/-- **`Ext^{>0}(M, M) = 0`** for `M = S(T^{λ'} e(t) ⊠ Y₀)` a summand of the standard
`S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem subsingleton_ext_tensorStd_self (j : ℕ) (hj : 0 < j) :
    Subsingleton (Ext.{w} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) j) := by
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h₀ (oldProj Q Λ 0 t ht) ι π hιπ htot
  have h' := subsingleton_ext_standard Q Λ hQ hR hall t ht u h₀
    (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) j fun s hs hmem =>
      subsingleton_hom_loadingProj_of_killedAfter Q Λ
        (killedAfter_tensorStd_zero Q Λ hQ h₀ _ _) t u.reverse hj s hs hmem
  have := @Equiv.subsingleton _ _ (Ext.biproductAddEquiv hB
    (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) j).symm.toEquiv h'
  obtain ⟨j₀⟩ := ‹Nonempty J›
  exact ⟨fun a b => congrFun (Subsingleton.elim (fun _ : J => a) (fun _ => b)) j₀⟩

omit [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))] in
include hR hall ι π hιπ htot in
/-- **`dim End(M) = 1`** for `M = S(T^{λ'} e(t) ⊠ Y₀)` a summand of the standard
`S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`, given `dim Hom(M, M^⋆) = 1`. Both `Hom(S, M)` and
`Hom(S, M^⋆)` are `e(s₀) M` and `e(s₀) M^⋆` for the degree-`0` term `T^λ e(s₀)` of the resolution
of Proposition 7.6, since neither `M` nor `M^⋆` receives maps from the degree-`1` term; these have
the same dimension, and `Hom(S, ·) = Hom(M, ·)^J`. Under the route hypothesis `hall` of
Proposition 7.6. -/
theorem finrank_end_tensorStd [Module.Finite k T]
    (hHom : Module.finrank k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀ ⟶
      starDualObj k σT (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) = 1) :
    Module.finrank k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀ ⟶
      tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) = 1 := by
  classical
  have hB := tensorStdBiconeIsBilimit Q Λ hQ h₀ (oldProj Q Λ 0 t ht) ι π hιπ htot
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h₀
  have h0 := hP 0
  rw [websterWords, Multiset.powersetCard_zero_left, Multiset.map_singleton] at h0
  obtain ⟨s, hs, -, ⟨i⟩⟩ := h0.exists_equiv_of_singleton
  have he : IsIdempotentElem (loadingIdem Q Λ s hs) := isIdempotentElem_mk_e s hs
  have hc : ∀ c : k, StarDual.bar σT (algebraMap k T c) = algebraMap k T c :=
    fun c => tensorFlip_algebraMap' c
  -- `M` is finite-dimensional, as a quotient of `T^λ e(s₀)`.
  have := finiteDimensional_loadingProj Q Λ s hs
  have : FiniteDimensional k (P.complex.X 0) :=
    finiteDimensional_of_surjective Q Λ i.inv fun y => ⟨i.hom y, Iso.hom_inv_id_apply i y⟩
  have : FiniteDimensional k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (cycWord Q Λ u)) :=
    finiteDimensional_of_surjective Q Λ (P.π.f 0)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have : FiniteDimensional k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) :=
    Module.Finite.of_surjective
      ((tensorStdMapRight Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (π j₀)).restrictScalars k) fun y =>
        ⟨tensorStdMapRight Q Λ hQ h₀ (oldProj Q Λ 0 t ht) (ι j₀) y, by
          have := congrArg (fun f => f y)
            (tensorStdMapRight_comp_ite Q Λ hQ h₀ (oldProj Q Λ 0 t ht) ι π hιπ j₀ j₀)
          simpa using this⟩
  -- `dim Hom(S, Y) = |J| dim Hom(M, Y) = dim e(s₀) Y` for `Y` killed after `ℓ`.
  have hdim : ∀ Y : ModuleCat.{0} T, KilledAfter Q Λ ℓ Y →
      Fintype.card J * Module.finrank k (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀ ⟶ Y) =
        Module.finrank k (fixedSubspace (k := k) Y (loadingIdem Q Λ s hs)) := by
    intro Y hY
    have : Subsingleton (P.complex.X 1 ⟶ Y) := (hP 1).subsingleton_hom fun s hs hmem =>
      subsingleton_hom_loadingProj_of_killedAfter Q Λ hY t u.reverse one_pos s hs hmem
    rw [← finrank_fun_eq_card_mul, ← (Limits.Bicone.homLinearEquiv (R := k) hB Y).finrank_eq]
    exact ((P.homLinearEquivZero k (Y := Y)).trans ((Linear.homCongr k i (Iso.refl Y)).trans
      (lIdealHomEquiv he Y))).finrank_eq
  have hK := killedAfter_tensorStd_zero Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀
  have h1 := hdim _ hK
  have h2 := hdim _ hK.starDual
  rw [StarDual.finrank_fixedSubspace_starDual hc _ he (tensorFlip_loadingIdem s hs), ← h1,
    hHom] at h2
  exact (Nat.eq_of_mul_eq_mul_left Fintype.card_pos h2).symm

include hR hall ι π hιπ htot in
/-- **Corollary 7.9** (Webster, arXiv:1309.3796v3, §7.1), general form, ungraded, in the repaired
reading of Proposition 7.8. Under the hypotheses of `exists_stdResolution_last`, with `T`
finite-dimensional, `Extⁱ(X, M)` for `M = S(T^{λ'} e(t) ⊠ Y₀)` is one-dimensional for `i = |ν|`
and zero otherwise. Along the resolution `0 → M_{|ν|} → ⋯ → M_0 → X → 0`, the terms `M_n` with
`n < |ν|` have no `Ext` into `M`, so `Ext^{|ν|+j}(X, M) = Ext^j(M_{|ν|}, M) = Ext^j(M, M)`. Under
the route hypothesis `hall` of Proposition 7.6. -/
theorem ext_stdResolution_last [Module.Finite k T] (X : ModuleCat.{0} T) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (het : TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) 0 (StendhalAlgebra.e t ht) = 1)
    (hss : ∀ (M : Type) [AddCommGroup M]
      [Module (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
        (wordWt u 0)) M]
      [Module.Finite (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j)
        (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ
        (Fin.last ℓ) j) (wordWt u 0)] (Fin n → Y₀)))
    (htop : Module.finrank k (Ext.{w} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    Module.finrank k (Ext.{w} X (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)
      (Multiset.card ν)) = 1 ∧
      ∀ i ≠ Multiset.card ν,
        Subsingleton (Ext.{w} X (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) i) := by
  obtain ⟨S, ⟨e0⟩, hs, he, hstd, hz, ⟨eN⟩, hHom⟩ := exists_stdResolution_last Q Λ hQ hR hall X
    hX u h₀ t ht het Y₀ hss ι π hιπ htot htop
  have hK := killedAfter_tensorStd_zero Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀
  -- `Ext^*(M_n, M) = 0` for `n < |ν|`.
  have hY : ∀ n < Multiset.card ν, ∀ i, Subsingleton (Ext.{w} (S n).X₂
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) i) := by
    intro n hn i
    obtain ⟨J', _, c, hcq, hfin, ⟨e⟩⟩ := hstd n hn.le
    refine Ext.subsingleton_of_iso e _ i (subsingleton_ext_pi _ _ i fun j => ?_)
    have hq := hcq j
    have hf := hfin j
    generalize c j = cj at hq hf ⊢
    obtain ⟨θ, β, h, N⟩ := cj
    exact subsingleton_ext_stdLayer_of_killedFrom Q Λ hQ hR hall h
      (KilledFrom.mono Q Λ (by dsimp only at hq; omega) hK.killedFrom) i N
  have hC := Ext.exists_linearEquiv_of_chain k S hs he _ _ hY
  -- `K_{|ν|} ≅ M_{|ν|} ≅ M`.
  have := (he (Multiset.card ν + 1)).epi_g
  have h3 : IsZero (S (Multiset.card ν + 1)).X₃ :=
    IsZero.of_epi (S (Multiset.card ν + 1)).g (hz _ (by omega))
  obtain ⟨e1⟩ := hs (Multiset.card ν)
  have : IsIso (S (Multiset.card ν)).g := ((he _).isIso_g_iff).2 (h3.of_iso e1.symm)
  let eK := (asIso (S (Multiset.card ν)).g).symm ≪≫ eN
  refine ⟨?_, fun i hi => ?_⟩
  · obtain ⟨E⟩ := hC.1 _ le_rfl 0
    rw [← (Ext.linearEquivOfIso k e0.symm _ _).finrank_eq]
    refine E.finrank_eq.symm.trans ?_
    rw [(Ext.linearEquivOfIso k eK.symm _ _).finrank_eq, (Ext.linearEquiv₀ (R := k)).finrank_eq]
    exact finrank_end_tensorStd Q Λ hQ hR hall u h₀ t ht ι π hιπ htot hHom
  · refine Ext.subsingleton_of_iso e0.symm _ i ?_
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact hC.2 i hi
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hi
      obtain ⟨E⟩ := hC.1 _ le_rfl (j + 1)
      have := Ext.subsingleton_of_iso eK _ (j + 1)
        (subsingleton_ext_tensorStd_self Q Λ hQ hR hall u h₀ t ht ι π hιπ htot (j + 1) j.succ_pos)
      rw [show Multiset.card ν + j + 1 = Multiset.card ν + (j + 1) by omega]
      exact E.symm.toEquiv.subsingleton

end Self

end Categorification.Stendhal

end
