/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardVanishing
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.WeightedKLR.RedStrands.StringyClassification

/-!
# Ext out of a standardization into modules killed at its position

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Proposition 7.8. Let `S_c(N)` be the standardization of a finite-dimensional module `N` over the
factor algebra of a split `c = (θ, β)`; its loadings have their last red strand at position
`p = |θ| + ℓ`. If `Y` is killed by every loading idempotent whose last red strand is at a position
`≥ p`, then `Ext^*(S_c(N), Y) = 0`.

For `N = T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)` this follows from the projective resolution of
Proposition 7.6, all of whose terms have their last red strand at positions `≥ p`. The general case
follows by induction on the degree and on the dimension of `N`, since standardization is exact and
every nonzero `N` receives a nonzero map from some `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)`.

## Main results

* `KilledFrom`: `Y` is killed by the loadings whose last red strand is at position `≥ p`.
* `subsingleton_ext_wordFactor`: the case `N = T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)`.
* `subsingleton_ext_stdLayer_of_killedFrom`: the general finite-dimensional case.
-/

noncomputable section
namespace Categorification

namespace Stendhal

open KLR KLRAlgebra CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν

variable (Q Λ) in
/-- `Y` is killed by every loading idempotent `e(s)` whose last red strand is at a position
`≥ p`. -/
def KilledFrom (p : ℕ) (Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)) : Prop :=
  ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s)
    (a : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))), p ≤ a.val →
    s.lbl a = Sum.inr (Fin.last ℓ) → ∀ y : Y, loadingIdem Q Λ s hs • y = 0

theorem KilledAfter.killedFrom {p : ℕ} {Y : ModuleCat.{0} T} (h : KilledAfter Q Λ p Y) :
    KilledFrom Q Λ (p + 1) Y :=
  fun s hs a ha hr y => h s hs a (by omega) hr y

omit [DecidableEq I] in
theorem coe_word_seq {β : Multiset I} (u : Seq β) : ((u.word : List I) : Multiset I) = β := by
  rw [Seq.word, ← Fin.univ_val_map]
  exact u.2

section Word

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext out of a word standard into a module killed at its position**: if `Y` is killed by the
loadings whose last red strand is at a position `≥ |θ| + ℓ`, then
`Ext^n(S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)), Y) = 0` for every `n`, by the resolution of
Proposition 7.6. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem subsingleton_ext_wordFactor {θ β : Multiset I} (h : θ + β = ν)
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (u : Seq β) {Y : ModuleCat.{0} T}
    (hY : KilledFrom Q Λ (Multiset.card θ + ℓ) Y) (n : ℕ) :
    Subsingleton (Ext.{w} (stdLayerModule Q Λ hQ
      (tensorLayer Q Λ h (oldProj Q Λ θ t ht) (cycProj Q Λ β u))) Y n) := by
  obtain ⟨w, hw⟩ : ∃ w : List I, w = u.word.reverse := ⟨_, rfl⟩
  have hβ : wordWt w 0 = β := by
    rw [← coe_reverse_eq_wordWt, hw, List.reverse_reverse, coe_word_seq]
  have hu : u = Seq.ofList w.reverse (by rw [coe_reverse_eq_wordWt, hβ]) :=
    Seq.word_injective (by rw [Seq.word_ofList, hw, List.reverse_reverse])
  clear hw
  subst hβ hu
  obtain ⟨g⟩ := nonempty_cycWord_equiv_cycProj Q Λ w
  let e := stdLayerEquiv Q Λ hQ h (tensorFactorCongr Q Λ (LinearEquiv.refl _ (oldProj Q Λ θ t ht)) g.symm)
  have hs := subsingleton_ext_standard Q Λ hQ hR hall t ht w h Y n fun s hs hmem => by
    have hlen : (t.word.map (addRedColor ℓ)).length = Multiset.card θ + ℓ := by
      rw [List.length_map, Seq.length_word]; simp [stendhalWeight]
    have hlt : Multiset.card θ + ℓ + n < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
      obtain ⟨Tm, hT, hw⟩ := Multiset.mem_map.1 hmem
      have hlen' := congrArg List.length hw
      rw [Seq.length_word] at hlen'
      rw [← hlen', websterWord]
      have := length_pickIn w.reverse (Multiset.mem_powersetCard.1 hT).1
      simp only [List.length_append, List.length_map, List.length_reverse,
        List.length_singleton, hlen, this, (Multiset.mem_powersetCard.1 hT).2]
      omega
    exact subsingleton_hom_loadingProj s hs (hY s hs ⟨_, hlt⟩ (by simp only; omega)
      (lbl_of_word_eq_websterWord hmem _ (by simp only [hlen])))
  exact Ext.subsingleton_of_iso e.toModuleIso Y n hs

end Word


section General

variable (Q Λ) {θ β : Multiset I}

local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "Lθ" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ
local notation "Cβ" => CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β

/-- A submodule of a factor module, as a factor module. -/
abbrev FactorModule.sub {N : FactorModule Q Λ θ β} (N' : Submodule D N.carrier) :
    FactorModule Q Λ θ β :=
  ⟨N'⟩

/-- A quotient of a factor module, as a factor module. -/
abbrev FactorModule.quot {N : FactorModule Q Λ θ β} (N' : Submodule D N.carrier) :
    FactorModule Q Λ θ β :=
  ⟨N.carrier ⧸ N'⟩

/-- Multiplication `A ⊠ B → A ⊗ B`, a map of `A ⊗ B`-modules. -/
def extTensorMul (A B : Type) [Ring A] [Algebra k A] [Ring B] [Algebra k B] :
    ExtTensor k A B →ₗ[A ⊗[k] B] A ⊗[k] B where
  toFun := ExtTensor.equivTensor
  map_add' := map_add _
  map_smul' t x := ExtTensor.smul_eq_induction (F := ExtTensor.equivTensor) (map_add _)
    (map_zero _) (fun a b p q => by
      rw [ExtTensor.smul_tmul]
      change (a * p) ⊗ₜ[k] (b * q) = (a ⊗ₜ[k] b) * (p ⊗ₜ[k] q)
      rw [Algebra.TensorProduct.tmul_mul_tmul]) t x

/-- The map `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u) → N`, `a ⊠ b ↦ (a ⊗ b) y`. -/
def wordFactorMap (N : FactorModule Q Λ θ β) (t : Seq (stendhalWeight ℓ θ))
    (ht : IsRedOrdered t) (u : Seq β) (y : N.carrier) :
    (tensorFactor Q Λ (oldProj Q Λ θ t ht) (cycProj Q Λ β u)).carrier →ₗ[D] N.carrier :=
  (LinearMap.toSpanSingleton D N.carrier y).comp ((extTensorMul (k := k) Lθ Cβ).comp
    (ExtTensor.map (k := k) (P := KMod (k := k) (oldProj Q Λ θ t ht))
      (Q := KMod (k := k) (cycProj Q Λ β u)) (P' := Lθ) (Q' := Cβ)
      (lIdeal (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e t ht))).subtype
      (lIdeal (CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β
        (e u))).subtype))

theorem wordFactorMap_unit (N : FactorModule Q Λ θ β) (t : Seq (stendhalWeight ℓ θ))
    (ht : IsRedOrdered t) (u : Seq β) (y : N.carrier) :
    wordFactorMap Q Λ N t ht u y (ExtTensor.tmul
      (⟨_, isIdempotentElem_mk_e t ht⟩ : lIdeal
        (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e t ht)))
      (⟨_, isIdempotentElem_cyc_e Q Λ β u⟩ : lIdeal
        (CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β (e u)))) =
      (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e t ht) ⊗ₜ[k]
        CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β (e u) : D) •
        y :=
  rfl

/-- Every nonzero vector of a factor module has a nonzero component `(e(t) ⊗ e(u)) y`. -/
theorem exists_idem_smul_ne_zero {N : FactorModule Q Λ θ β} {y : N.carrier} (hy : y ≠ 0) :
    ∃ (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (u : Seq β),
      (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e t ht) ⊗ₜ[k]
        CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β (e u) : D) •
        y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hy
  have hC : ∑ u : Seq β,
      CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β (e u) = 1 := by
    rw [← map_sum, sum_e, map_one]
  rw [← one_smul D y, Algebra.TensorProduct.one_def, ← sum_seqIdem Q (Λ ∘ Fin.castSucc) θ, ← hC,
    TensorProduct.sum_tmul, Finset.sum_smul]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [TensorProduct.tmul_sum, Finset.sum_smul]
  exact Finset.sum_eq_zero fun u _ => hcon t.1 t.2 u

variable (hQ : KLRSymm Q) (h : θ + β = ν)

/-- Standardization of `0 → N' → N → N/N' → 0`. -/
theorem stdShortComplex_sub_shortExact {N : FactorModule Q Λ θ β} (N' : Submodule D N.carrier) :
    (stdShortComplex Q Λ hQ h (N₁ := FactorModule.sub Q Λ N') (N₃ := FactorModule.quot Q Λ N')
      N'.subtype N'.mkQ (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero N').2 x.2)).ShortExact :=
  stdShortComplex_shortExact Q Λ hQ h _ _ _ Subtype.val_injective N'.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N')

/-- Standardization of `0 → ker φ → P → N → 0`. -/
theorem stdShortComplex_ker_shortExact {P N : FactorModule Q Λ θ β}
    (φ : P.carrier →ₗ[D] N.carrier) (hφ : Function.Surjective φ) :
    (stdShortComplex Q Λ hQ h (N₁ := FactorModule.sub Q Λ (LinearMap.ker φ))
      (LinearMap.ker φ).subtype φ (LinearMap.ext fun x => x.2)).ShortExact :=
  stdShortComplex_shortExact Q Λ hQ h _ _ _ Subtype.val_injective hφ
    (LinearMap.exact_subtype_ker_map φ)

/-- Finite dimensionality of submodules and quotients of factor modules. -/
theorem finiteDimensional_sub {N : FactorModule Q Λ θ β} [FiniteDimensional k N.carrier]
    (N' : Submodule D N.carrier) : FiniteDimensional k (FactorModule.sub Q Λ N').carrier :=
  Module.Finite.of_injective (N'.subtype.restrictScalars k) Subtype.val_injective

theorem finiteDimensional_quot {N : FactorModule Q Λ θ β} [FiniteDimensional k N.carrier]
    (N' : Submodule D N.carrier) : FiniteDimensional k (FactorModule.quot Q Λ N').carrier :=
  Module.Finite.of_surjective (N'.mkQ.restrictScalars k) N'.mkQ_surjective

theorem finrank_sub_lt {N : FactorModule Q Λ θ β} [FiniteDimensional k N.carrier]
    {N' : Submodule D N.carrier} (hN' : N' ≠ ⊤) :
    Module.finrank k N' < Module.finrank k N.carrier :=
  Submodule.finrank_lt (s := N'.restrictScalars k)
    (fun h => hN' ((Submodule.restrictScalars_eq_top_iff _ _ _).1 h))

theorem finrank_quot_lt {N : FactorModule Q Λ θ β} [FiniteDimensional k N.carrier]
    {N' : Submodule D N.carrier} (hN' : N' ≠ ⊥) :
    Module.finrank k (N.carrier ⧸ N') < Module.finrank k N.carrier := by
  have h1 := Submodule.finrank_quotient_add_finrank (N'.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k N').finrank_eq] at h1
  have h2 : Module.finrank k (N'.restrictScalars k) ≠ 0 := fun h0 =>
    hN' ((Submodule.restrictScalars_eq_bot_iff _ _ _).1 (Submodule.finrank_eq_zero.1 h0))
  omega

/-- The standardization of the zero module is zero. -/
theorem isZero_stdLayerModule {N : FactorModule Q Λ θ β} [Subsingleton N.carrier] :
    Limits.IsZero (stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩) := by
  have h0 : (LinearMap.id : N.carrier →ₗ[D] N.carrier) = 0 := Subsingleton.elim _ _
  have h2 := congrArg (parabolicStandardMap Q Λ θ β) h0
  rw [parabolicStandardMap_id, parabolicStandardMap_zero] at h2
  have : Subsingleton (stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩) := ⟨fun a b => by
    have ha := LinearMap.congr_fun h2 (a : ParabolicStandard Q Λ θ β N.carrier)
    have hb := LinearMap.congr_fun h2 (b : ParabolicStandard Q Λ θ β N.carrier)
    exact ha.trans hb.symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end General

section Main

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))] {θ β : Multiset I} (h : θ + β = ν)

local notation "D" => parabolicFactorAlgebra Q Λ θ β

omit [DecidableEq I] in
/-- `A e` is finite-dimensional for a finite-dimensional algebra `A`. -/
theorem finite_kMod_lIdeal {A : Type} [Ring A] [Algebra k A] [Module.Finite k A] {e : A}
    (he : IsIdempotentElem e) : Module.Finite k (KMod (k := k) (ModuleCat.of A (lIdeal e))) := by
  have : Module.Finite A (KMod (k := k) (ModuleCat.of A (lIdeal e))) :=
    Module.Finite.of_surjective (LinearMap.toSpanSingleton A _
      ((⟨e, he⟩ : lIdeal e) : KMod (k := k) (ModuleCat.of A (lIdeal e))))
      (fun x => ⟨(x : lIdeal e).1, Subtype.ext (x : lIdeal e).2⟩)
  exact Module.Finite.trans A _

include hR in
/-- `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)` is finite-dimensional. -/
theorem finiteDimensional_wordFactor (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t)
    (u : Seq β) : FiniteDimensional k (tensorFactor Q Λ (oldProj Q Λ θ t ht) (cycProj Q Λ β u)).carrier := by
  have : Module.Finite k (TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) θ) := by
    convert tensorProductAlgebra_finite (Q := Q) (Λ ∘ Fin.castSucc) θ hR using 4
  have : Module.Finite k
      (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β) :=
    CycKLR.module_finite (fun i j hij => by
      obtain ⟨c, hc, he⟩ := hR.polyInY_leading i j hij
      rw [he]
      exact hc.map Polynomial.C) (fun _ => Polynomial.monic_X_pow _)
  have := finite_kMod_lIdeal (k := k)
    (isIdempotentElem_mk_e (k := k) (Q := Q) (Λ := Λ ∘ Fin.castSucc) t ht)
  have := finite_kMod_lIdeal (k := k) (isIdempotentElem_cyc_e Q Λ β u)
  exact inferInstanceAs (Module.Finite k
    (KMod (k := k) (oldProj Q Λ θ t ht) ⊗[k] KMod (k := k) (cycProj Q Λ β u)))

/-- **Reduction to quotients of word factors**: if `Extⁿ(S(N), Y) = 0` for every quotient `N` of
some `T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)`, then for every finite-dimensional `N`, by induction on the
dimension and exactness of standardization. -/
theorem subsingleton_ext_stdLayer_of_wordQuotients {Y : ModuleCat.{0} T} (n : ℕ)
    (hcyc : ∀ (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (u : Seq β)
      (N : FactorModule Q Λ θ β), (∃ φ : (tensorFactor Q Λ (oldProj Q Λ θ t ht) (cycProj Q Λ β u)).carrier →ₗ[D] N.carrier,
        Function.Surjective φ) → Subsingleton (Ext.{w} (stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩) Y n))
    (N : FactorModule Q Λ θ β) [FiniteDimensional k N.carrier] :
    Subsingleton (Ext.{w} (stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩) Y n) := by
  induction hd : Module.finrank k N.carrier using Nat.strong_induction_on generalizing N with
  | _ d ih =>
  by_cases hs : Subsingleton N.carrier
  · exact Ext.subsingleton_of_isZero (isZero_stdLayerModule Q Λ hQ h) Y n
  rw [not_subsingleton_iff_nontrivial] at hs
  obtain ⟨y, hy⟩ := exists_ne (0 : N.carrier)
  obtain ⟨t, ht, u, hne⟩ := exists_idem_smul_ne_zero Q Λ hy
  by_cases htop : LinearMap.range (wordFactorMap Q Λ N t ht u y) = ⊤
  · exact hcyc t ht u N ⟨_, LinearMap.range_eq_top.1 htop⟩
  set N' := LinearMap.range (wordFactorMap Q Λ N t ht u y)
  have hbot : N' ≠ ⊥ := fun hb => by
    have hm := LinearMap.mem_range_self (wordFactorMap Q Λ N t ht u y) (ExtTensor.tmul
      (⟨_, isIdempotentElem_mk_e t ht⟩ : lIdeal
        (TensorProductAlgebra.mk Q (Λ ∘ Fin.castSucc) θ (StendhalAlgebra.e t ht)))
      (⟨_, isIdempotentElem_cyc_e Q Λ β u⟩ : lIdeal
        (CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j) β (e u))))
    rw [wordFactorMap_unit] at hm
    change _ ∈ N' at hm
    rw [hb, Submodule.mem_bot] at hm
    exact hne hm
  let S := stdShortComplex Q Λ hQ h (N₁ := FactorModule.sub Q Λ N') (N₂ := N)
    (N₃ := FactorModule.quot Q Λ N') N'.subtype N'.mkQ
    (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero N').2 x.2)
  have hS : S.ShortExact := stdShortComplex_sub_shortExact Q Λ hQ h N'
  have := finiteDimensional_sub Q Λ N'
  have := finiteDimensional_quot Q Λ N'
  have h1 : Subsingleton (Ext.{w} S.X₁ Y n) :=
    ih _ (hd ▸ finrank_sub_lt Q Λ htop) (FactorModule.sub Q Λ N') rfl
  have h3 : Subsingleton (Ext.{w} S.X₃ Y n) :=
    ih _ (hd ▸ finrank_quot_lt Q Λ hbot) (FactorModule.quot Q Λ N') rfl
  exact Ext.subsingleton_X₂ hS Y n

include hR hall in
/-- **Ext out of a standardization into a module killed at its position** (Webster,
arXiv:1309.3796v3, §7.1, proof of Proposition 7.8): if `N` is a finite-dimensional module over the
factor algebra of the split `θ + β` and `Y` is killed by the loadings whose last red strand is at
a position `≥ |θ| + ℓ`, then `Extⁿ(S(N), Y) = 0` for every `n`. Under the route hypothesis `hall`
of Proposition 7.6. -/
theorem subsingleton_ext_stdLayer_of_killedFrom {Y : ModuleCat.{0} T}
    (hY : KilledFrom Q Λ (Multiset.card θ + ℓ) Y) (n : ℕ) (N : FactorModule Q Λ θ β)
    [FiniteDimensional k N.carrier] :
    Subsingleton (Ext.{w} (stdLayerModule Q Λ hQ ⟨θ, β, h, N⟩) Y n) := by
  induction n generalizing N with
  | zero =>
    refine subsingleton_ext_stdLayer_of_wordQuotients Q Λ hQ h 0
      (fun t ht u N ⟨φ, hφ⟩ => ?_) N
    let S := stdShortComplex Q Λ hQ h (N₁ := FactorModule.sub Q Λ (LinearMap.ker φ))
      (N₂ := tensorFactor Q Λ (oldProj Q Λ θ t ht) (cycProj Q Λ β u)) (N₃ := N) (LinearMap.ker φ).subtype φ (LinearMap.ext fun x => x.2)
    have hS : S.ShortExact := stdShortComplex_ker_shortExact Q Λ hQ h φ hφ
    have : Subsingleton (Ext.{w} S.X₂ Y 0) :=
      subsingleton_ext_wordFactor Q Λ hQ hR hall h t ht u hY 0
    exact Ext.subsingleton_X₃_zero hS Y
  | succ n ih =>
    refine subsingleton_ext_stdLayer_of_wordQuotients Q Λ hQ h (n + 1)
      (fun t ht u N ⟨φ, hφ⟩ => ?_) N
    let S := stdShortComplex Q Λ hQ h (N₁ := FactorModule.sub Q Λ (LinearMap.ker φ))
      (N₂ := tensorFactor Q Λ (oldProj Q Λ θ t ht) (cycProj Q Λ β u)) (N₃ := N) (LinearMap.ker φ).subtype φ (LinearMap.ext fun x => x.2)
    have hS : S.ShortExact := stdShortComplex_ker_shortExact Q Λ hQ h φ hφ
    have := finiteDimensional_wordFactor Q Λ hR t ht u
    have := finiteDimensional_sub Q Λ (LinearMap.ker φ)
    have : Subsingleton (Ext.{w} S.X₁ Y n) := ih (FactorModule.sub Q Λ (LinearMap.ker φ))
    have : Subsingleton (Ext.{w} S.X₂ Y (1 + n)) :=
      subsingleton_ext_wordFactor Q Λ hQ hR hall h t ht u hY (1 + n)
    have := Ext.subsingleton_X₃_succ hS Y n
    rwa [Nat.add_comm 1 n] at this

end Main

end Stendhal

end Categorification
