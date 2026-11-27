/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.StarDual
import Categorification.Algebra.ExtVanishingShift
import Categorification.WeightedKLR.Rigidity.RigidityExtTorShift
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationTor

/-!
# Ext into dual standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof of
Proposition 7.8: "dualizing the projective resolution of Proposition 7.6" computes Ext into the
dual `(S^κ)^⋆` of a standard module. Here `M^⋆` is the `k`-dual of a left `T^λ`-module with the
action twisted by the horizontal reflection (`StarDual`, `starDualObj`).

## Generic part

For a projective resolution `P` of `S` of length `N` whose duals `P_m^⋆` are injective, and a
module `X` with no maps to `P_m^⋆` for `m < N`, dualizing the syzygy sequences of `P` gives an
injective coresolution of `S^⋆` along which `Extʲ(X, S^⋆) = 0` for `j ≠ N`
(`subsingleton_ext_starDual_of_resolution`).

## Standard modules

The resolution of Proposition 7.6 of `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))` has terms sums of projectives
`T^λ e(s)` whose duals are injective (`injective_starDualObj_of_loadingSum`), and below the top
degree `|u|` every loading has a black strand to the right of the last red strand. So for a
module `X` killed by all such cut loadings (as `L_λ` is), `Extʲ(X, S^⋆) = 0` for `j ≠ |u|`
(`subsingleton_ext_starDual_standard`).
-/

universe w

open CategoryTheory Abelian Limits MulOpposite

noncomputable section

namespace Categorification

/-! ### Duals of modules as an exact contravariant functor -/

section Generic

variable {k A : Type} [Field k] [Ring A] [Algebra k A] (σ : A ≃+* Aᵐᵒᵖ)

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable (k) in
/-- The dual `Y^⋆` of a module, as an object of `ModuleCat`. -/
def starDualObj (Y : ModuleCat.{0} A) : ModuleCat.{0} A :=
  ModuleCat.of A (StarDual k σ Y)

variable (k) in
/-- The dual of a morphism. -/
def starDualHom {Y Z : ModuleCat.{0} A} (f : Y ⟶ Z) : starDualObj k σ Z ⟶ starDualObj k σ Y :=
  ModuleCat.ofHom (StarDual.starDualMap (σ := σ) (k := k) f.hom)

variable (k) in
/-- The dual `0 → X₃^⋆ → X₂^⋆ → X₁^⋆ → 0` of a short complex. -/
def starDualShortComplex (S : ShortComplex (ModuleCat.{0} A)) : ShortComplex (ModuleCat.{0} A) :=
  ShortComplex.mk (starDualHom k σ S.g) (starDualHom k σ S.f) (by
    ext φ
    refine LinearMap.ext fun x => ?_
    change StarDual.toDual φ (S.g.hom (S.f.hom x)) = 0
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, S.zero]
    exact map_zero _)

theorem starDualShortComplex_shortExact {S : ShortComplex (ModuleCat.{0} A)} (hS : S.ShortExact) :
    (starDualShortComplex k σ S).ShortExact := by
  have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).mp hS.mono_f
  have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).mp hS.epi_g
  have hex : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact StarDual.exact_starDualMap (σ := σ) (k := k) S.f.hom S.g.hom hex
  · exact ConcreteCategory.mono_of_injective _ (StarDual.starDualMap_injective _ hg)
  · exact (ModuleCat.epi_iff_surjective _).mpr (StarDual.starDualMap_surjective _ hf)

/-- The dual of an isomorphism. -/
def starDualIso {Y Z : ModuleCat.{0} A} (e : Y ≅ Z) : starDualObj k σ Z ≅ starDualObj k σ Y :=
  (StarDual.starDualCongr (σ := σ) (k := k) e.toLinearEquiv).toModuleIso

variable [HasExt.{w} (ModuleCat.{0} A)]

/-- **Ext into the dual of a resolved module.** Let `P` be a projective resolution of `S` with
`P_{N+1} = 0`, all of whose duals `P_m^⋆` (`m ≤ N`) are injective, and let `X` have no nonzero
maps to `P_m^⋆` for `m < N`. Then `Extʲ(X, S^⋆) = 0` for `j ≠ N`. -/
theorem subsingleton_ext_starDual_of_resolution {S : ModuleCat.{0} A}
    (P : ProjectiveResolution S) (N : ℕ) (hz : IsZero (P.complex.X (N + 1)))
    (hinj : ∀ m ≤ N, Injective (starDualObj k σ (P.complex.X m)))
    (X : ModuleCat.{0} A) (hX : ∀ m < N, Subsingleton (X ⟶ starDualObj k σ (P.complex.X m)))
    (j : ℕ) (hj : j ≠ N) : Subsingleton (Ext.{w} X (starDualObj k σ S) j) := by
  -- Ext into the dual of a term of degree `m < N` vanishes in every degree.
  have hP : ∀ m < N, ∀ i, Subsingleton (Ext.{w} X (starDualObj k σ (P.complex.X m)) i) := by
    intro m hm i
    have := hinj m hm.le
    have := hX m hm
    cases i with
    | zero => exact (Ext.homEquiv₀ (X := X) (Y := starDualObj k σ (P.complex.X m))).subsingleton
    | succ i => exact ⟨fun a b => (Ext.eq_zero_of_injective a).trans
        (Ext.eq_zero_of_injective b).symm⟩
  -- The dual of the last syzygy is injective.
  have hlast : ∀ N', N = N' + 1 → ∀ i, i ≠ 0 →
      Subsingleton (Ext.{w} X (starDualObj k σ (syzygy P N')) i) := by
    rintro N' rfl i hi
    have hb := toSyzygy_bijective P N' hz
    have e : P.complex.X (N' + 1) ≅ syzygy P N' :=
      (LinearEquiv.ofBijective (toSyzygy P N').hom hb).toModuleIso
    have := hinj (N' + 1) le_rfl
    have : Injective (starDualObj k σ (syzygy P N')) :=
      Injective.of_iso (starDualIso (k := k) σ e.symm) inferInstance
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    exact ⟨fun a b => (Ext.eq_zero_of_injective a).trans (Ext.eq_zero_of_injective b).symm⟩
  -- Downward induction along the syzygies.
  have hsyz : ∀ d m, m + 1 + d = N → ∀ i, i + m + 1 ≠ N →
      Subsingleton (Ext.{w} X (starDualObj k σ (syzygy P m)) i) := by
    intro d
    induction d with
    | zero =>
      intro m hm i hi
      exact hlast m (by omega) i (by omega)
    | succ d ih =>
      intro m hm i hi
      have hS := starDualShortComplex_shortExact (k := k) σ (syzygySequence_shortExact P m)
      have : ∀ i, Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygySequence P m)).X₂ i) :=
        hP (m + 1) (by omega)
      cases i with
      | zero => exact Ext.subsingleton_X₁_zero hS X
      | succ i =>
        have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygySequence P m)).X₃ i) :=
          ih (m + 1) (by omega) i (by omega)
        exact Ext.subsingleton_X₁_succ hS X i
  -- The first step `0 → S^⋆ → P₀^⋆ → Ω₀^⋆ → 0`.
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `N = 0`: `S ≅ P₀` and `S^⋆` is injective.
    have hb := π_zero_bijective P hz
    have e : P.complex.X 0 ≅ S := (LinearEquiv.ofBijective (P.π.f 0).hom hb).toModuleIso
    have := hinj 0 le_rfl
    have : Injective (starDualObj k σ S) := Injective.of_iso (starDualIso (k := k) σ e.symm) inferInstance
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    exact ⟨fun a b => (Ext.eq_zero_of_injective a).trans (Ext.eq_zero_of_injective b).symm⟩
  · have hS := starDualShortComplex_shortExact (k := k) σ (syzygyZeroSequence_shortExact P)
    have : ∀ i, Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygyZeroSequence P)).X₂ i) :=
      hP 0 hN
    cases j with
    | zero => exact Ext.subsingleton_X₁_zero hS X
    | succ j =>
      have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygyZeroSequence P)).X₃ j) :=
        hsyz (N - 1) 0 (by omega) j (by omega)
      exact Ext.subsingleton_X₁_succ hS X j

end Generic

/-! ### Duals of sums of loading projectives -/

namespace Stendhal

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

theorem tensorFlip_loadingIdem (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s) :
    StarDual.bar σT (loadingIdem Q Λ s hs) = loadingIdem Q Λ s hs := by
  change tensorFlip (loadingIdem Q Λ s hs) = loadingIdem Q Λ s hs
  rw [loadingIdem, tensorFlip_mk_e]

/-- A sum of loading projectives is spanned by vectors fixed by its loading idempotents. -/
theorem LoadingSum.mem_span_loadingIdem {Y : ModuleCat.{0} T}
    {W : Multiset (List (I ⊕ Fin (ℓ + 1)))} (hY : LoadingSum Y W) (y : Y) :
    y ∈ Submodule.span T {y : Y | ∃ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word ∈ W ∧ loadingIdem Q Λ s hs • y = y} := by
  classical
  obtain ⟨ι, _, s, hs, hL, ⟨f⟩⟩ := hY
  have hmem : ∀ a, (s a).word ∈ W := fun a =>
    hL ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
  let ε : ∀ a, loadingProj Q Λ (s a) (hs a) := fun a =>
    (⟨loadingIdem Q Λ (s a) (hs a), (isIdempotentElem_mk_e (s a) (hs a)).eq⟩ :
      lIdeal (loadingIdem Q Λ (s a) (hs a)))
  have hy : y = ∑ a, (Subtype.val (f y a) : T) • f.symm (Pi.single a (ε a)) := by
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
  refine ⟨s a, hs a, hmem a, ?_⟩
  rw [← map_smul, ← Pi.single_smul]
  congr 2
  exact Subtype.ext (isIdempotentElem_mk_e (s a) (hs a)).eq

/-- **The dual of a sum of loading projectives is injective.** -/
theorem injective_starDualObj_of_loadingSum {Y : ModuleCat.{0} T}
    {W : Multiset (List (I ⊕ Fin (ℓ + 1)))} (hY : LoadingSum Y W) :
    Injective (starDualObj k σT Y) := by
  classical
  obtain ⟨ι, _, s, hs, -, ⟨f⟩⟩ := hY
  have := StarDual.injective_of_equiv_pi (k := k) (σ := σT) (fun z => tensorFlip_tensorFlip z)
    (fun c => tensorFlip_algebraMap' c) (fun a => loadingIdem Q Λ (s a) (hs a))
    (fun a => isIdempotentElem_mk_e (s a) (hs a)) (fun a => tensorFlip_loadingIdem (s a) (hs a))
    f
  exact Module.injective_object_of_injective_module (R := T) (M := StarDual k σT Y)

/-- **No maps into the dual of a sum of loading projectives** from a module killed by its
loading idempotents. -/
theorem subsingleton_hom_starDualObj_of_loadingSum {Y : ModuleCat.{0} T}
    {W : Multiset (List (I ⊕ Fin (ℓ + 1)))} (hY : LoadingSum Y W) (X : ModuleCat.{0} T)
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), s.word ∈ W →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0) :
    Subsingleton (X ⟶ starDualObj k σT Y) := by
  refine ⟨fun f g => ?_⟩
  have h0 : ∀ φ : X ⟶ starDualObj k σT Y, φ = 0 := fun φ => by
    ext1
    refine StarDual.hom_eq_zero (σ := σT) (k := k) (fun y => ?_) φ.hom
    refine Submodule.span_mono ?_ (hY.mem_span_loadingIdem y)
    rintro y ⟨s, hs, hw, hy⟩
    exact ⟨loadingIdem Q Λ s hs, hy, tensorFlip_loadingIdem s hs, hX s hs hw⟩
  rw [h0 f, h0 g]

/-! ### Ext into a dual standard module -/

section Ext

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext into a dual standard module vanishes off degree `|u|`** (Webster, arXiv:1309.3796v3,
§7.1, proof of Proposition 7.8: "dualizing the projective resolution of Proposition 7.6"): if
`X` is killed by every loading idempotent `e(s)` with a black strand to the right of the last red
strand, then `Extʲ(X, S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))^⋆) = 0` for `j ≠ |u|`. Under the route
hypothesis `hall` of Proposition 7.6. -/
theorem subsingleton_ext_starDual_standard (X : ModuleCat.{0} T)
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (j : ℕ) (hj : j ≠ u.length) :
    Subsingleton (Ext.{w} X (starDualObj k σT
      (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u))) j) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  exact subsingleton_ext_starDual_of_resolution σT P u.length hz
    (fun m _ => injective_starDualObj_of_loadingSum (hP m)) X
    (fun m hm => subsingleton_hom_starDualObj_of_loadingSum (hP m) X fun s hs hmem =>
      hX s hs (not_hasLastRed_of_mem_websterWords _ _ (by simpa using hm) hmem)) j hj

end Ext

end Stendhal

end Categorification
