/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtDualStandard
import Categorification.WeightedKLR.Rigidity.RigidityExtDetection
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationTop
import Categorification.Algebra.ExtLinearShift

/-!
# Ext into a dual standard module in the top degree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof of
Proposition 7.8: by "our projective resolution", `Ext^{2ρ^∨(λ)}(L_λ, (S^{κ₀})^⋆)` is computed by
the top term of the resolution of Proposition 7.6.

## Main results

* `nonempty_ext_starDual_top`: for a projective resolution `P` of `S` of length `N` with injective
  duals, and `X` with no maps to `P_m^⋆` for `m < N`, `Ext^N(X, S^⋆) ≅ Hom(X, P_N^⋆)`.
* `StarDual.homSwapEquiv`: `Hom(Y, X^⋆) ≅ Hom(X, Y^⋆)`, `k`-linearly.
* `finrank_fixedSubspace_starDual`: `dim e X^⋆ = dim e X` for `ē = e` and `X` finite-dimensional.
* `Stendhal.finrank_ext_starDual_standard_top`: for a finite-dimensional module `X` killed by
  the cuts, `Ext^{|u|}(X, S^⋆)` and `Ext^{|u|}(S, X)` have the same dimension, for the standard
  module `S = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`. Under the route hypothesis `hall` of
  Proposition 7.6.
-/

universe w

open CategoryTheory Abelian Limits MulOpposite

noncomputable section

namespace Categorification

section Generic

variable {k A : Type} [Field k] [Ring A] [Algebra k A] (σ : A ≃+* Aᵐᵒᵖ)

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable [HasExt.{w} (ModuleCat.{0} A)]

/-- **Ext into the dual of a resolved module, top degree.** Let `P` be a projective resolution
of `S` with `P_{N+1} = 0`, all of whose duals `P_m^⋆` (`m ≤ N`) are injective, and let `X` have no
nonzero maps to `P_m^⋆` for `m < N`. Then `Ext^N(X, S^⋆) ≅ Hom(X, P_N^⋆)`. -/
theorem nonempty_ext_starDual_top {S : ModuleCat.{0} A} (P : ProjectiveResolution S) (N : ℕ)
    (hz : IsZero (P.complex.X (N + 1)))
    (hinj : ∀ m ≤ N, Injective (starDualObj k σ (P.complex.X m)))
    (X : ModuleCat.{0} A) (hX : ∀ m < N, Subsingleton (X ⟶ starDualObj k σ (P.complex.X m))) :
    Nonempty (Ext.{w} X (starDualObj k σ S) N ≃ₗ[k]
      (X ⟶ starDualObj k σ (P.complex.X N))) := by
  have hP : ∀ m ≤ N, ∀ i, (i = 0 → m < N) →
      Subsingleton (Ext.{w} X (starDualObj k σ (P.complex.X m)) i) := by
    intro m hm i hi
    have := hinj m hm
    cases i with
    | zero =>
      have := hX m (hi rfl)
      exact (Ext.homEquiv₀ (X := X) (Y := starDualObj k σ (P.complex.X m))).subsingleton
    | succ i => exact ⟨fun a b => (Ext.eq_zero_of_injective a).trans
        (Ext.eq_zero_of_injective b).symm⟩
  -- Along the syzygies: `Extʲ(X, Ω_m^⋆) ≅ Hom(X, P_N^⋆)` for `m + 1 + j = N`.
  have hsyz : ∀ j m, m + 1 + j = N → Nonempty (Ext.{w} X (starDualObj k σ (syzygy P m)) j ≃ₗ[k]
      (X ⟶ starDualObj k σ (P.complex.X N))) := by
    intro j
    induction j with
    | zero =>
      intro m hm
      obtain rfl : N = m + 1 := by omega
      have hb := toSyzygy_bijective P m hz
      have e : P.complex.X (m + 1) ≅ syzygy P m :=
        (LinearEquiv.ofBijective (toSyzygy P m).hom hb).toModuleIso
      exact ⟨(Ext.linearEquiv₀ (R := k)).trans
        (Linear.homCongr k (Iso.refl X) (starDualIso (k := k) σ e))⟩
    | succ j ih =>
      intro m hm
      have hS := starDualShortComplex_shortExact (k := k) σ (syzygySequence_shortExact P m)
      have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygySequence P m)).X₂ j) :=
        hP (m + 1) (by omega) j (fun _ => by omega)
      have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygySequence P m)).X₂
          (j + 1)) := hP (m + 1) (by omega) (j + 1) (by omega)
      obtain ⟨f⟩ := ih (m + 1) (by omega)
      exact ⟨(Ext.linearEquivOfShortExactRight k hS X j).symm.trans f⟩
  rcases N with _ | N
  · have hb := π_zero_bijective P hz
    have e : P.complex.X 0 ≅ S := (LinearEquiv.ofBijective (P.π.f 0).hom hb).toModuleIso
    exact ⟨(Ext.linearEquiv₀ (R := k)).trans
      (Linear.homCongr k (Iso.refl X) (starDualIso (k := k) σ e))⟩
  · have hS := starDualShortComplex_shortExact (k := k) σ (syzygyZeroSequence_shortExact P)
    have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygyZeroSequence P)).X₂ N) :=
      hP 0 (by omega) N (fun _ => by omega)
    have : Subsingleton (Ext.{w} X (starDualShortComplex k σ (syzygyZeroSequence P)).X₂
        (N + 1)) := hP 0 (by omega) (N + 1) (by omega)
    obtain ⟨f⟩ := hsyz N 0 (by omega)
    exact ⟨(Ext.linearEquivOfShortExactRight k hS X N).symm.trans f⟩

namespace StarDual

variable {σ} (hσ : ∀ a, bar σ (bar σ a) = a)
  (hc : ∀ c : k, bar σ (algebraMap k A c) = algebraMap k A c)

/-- **Swapping maps into duals**, `k`-linearly: `Hom(Y, X^⋆) ≅ Hom(X, Y^⋆)`. -/
def homSwapEquiv (X Y : ModuleCat.{0} A) :
    (Y ⟶ starDualObj k σ X) ≃ₗ[k] (X ⟶ starDualObj k σ Y) where
  toFun g := ModuleCat.ofHom (homSwap hσ hc g.hom)
  invFun g := ModuleCat.ofHom (homSwap hσ hc g.hom)
  left_inv g := rfl
  right_inv g := rfl
  map_add' f g := rfl
  map_smul' c g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    change toDual (k := k) (σ := σ) ((c • g).hom y) x = toDual (k := k) (σ := σ) (g.hom (bar σ (algebraMap k A c) • y)) x
    rw [hc, LinearMap.map_smul]
    rfl

omit [HasExt.{w} (ModuleCat.{0} A)] in
include hc in
/-- **The fixed vectors of a self-dual idempotent on a dual**: `dim e X^⋆ = dim e X` when
`ē = e` and `X` is finite-dimensional. -/
theorem finrank_fixedSubspace_starDual (X : ModuleCat.{0} A) [FiniteDimensional k X] {e : A}
    (he : IsIdempotentElem e) (hbe : bar σ e = e) :
    Module.finrank k (fixedSubspace (k := k) (starDualObj k σ X) e) =
      Module.finrank k (fixedSubspace (k := k) X e) := by
  let p : X →ₗ[k] X :=
    { toFun := fun x => e • x, map_add' := smul_add e, map_smul' := fun c x => smul_comm e c x }
  have hp : ∀ x, p (p x) = p x := fun x => by
    change e • e • x = e • x
    rw [← mul_smul, he.eq]
  have h1 : fixedSubspace (k := k) X e = LinearMap.range p := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx⟩
    · rintro ⟨y, rfl⟩
      exact hp y
  have hfix : ∀ φ : StarDual k σ X, e • φ = φ ↔ (toDual (k := k) (σ := σ) φ).comp p = toDual (k := k) (σ := σ) φ := fun φ => by
    constructor
    · intro h
      refine LinearMap.ext fun x => ?_
      conv_rhs => rw [← h]
      change toDual (k := k) (σ := σ) φ (e • x) = toDual (k := k) (σ := σ) φ (bar σ e • x)
      rw [hbe]
    · intro h
      refine LinearMap.ext fun x => ?_
      change toDual (k := k) (σ := σ) φ (bar σ e • x) = toDual (k := k) (σ := σ) φ x
      rw [hbe]
      exact LinearMap.congr_fun h x
  let E : fixedSubspace (k := k) (starDualObj k σ X) e ≃ₗ[k] LinearMap.range p.dualMap :=
    { toFun := fun φ => ⟨toDual (k := k) (σ := σ) φ.1, ⟨toDual (k := k) (σ := σ) φ.1, ((hfix φ.1).1 φ.2)⟩⟩
      invFun := fun ψ => ⟨ofDual (k := k) (σ := σ) ψ.1, by
        obtain ⟨χ, hχ⟩ := ψ.2
        refine (hfix (ofDual (k := k) (σ := σ) ψ.1)).2 ?_
        rw [← hχ]
        exact LinearMap.ext fun x => congrArg χ (hp x)⟩
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl
      map_add' := fun φ ψ => rfl
      map_smul' := fun c φ => by
        apply Subtype.ext
        refine LinearMap.ext fun x => ?_
        change toDual (k := k) (σ := σ) φ.1 (bar σ (algebraMap k A c) • x) = c • toDual (k := k) (σ := σ) φ.1 x
        rw [hc, algebraMap_smul, LinearMap.map_smul] }
  rw [E.finrank_eq, LinearMap.finrank_range_dualMap_eq_finrank_range, h1]

end StarDual

end Generic

end Categorification

/-! ### Standard modules -/

namespace Categorification.Stendhal

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext into a dual standard module in the top degree** (Webster, arXiv:1309.3796v3, §7.1,
proof of Proposition 7.8): for a finite-dimensional module `X` killed by every loading
idempotent with a black strand to the right of the last red strand,
`dim Ext^{|u|}(X, S^⋆) = dim Ext^{|u|}(S, X)` for `S = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`. Both
are computed by the top term `T^λ e(s)` of the resolution of Proposition 7.6: the first is
`Hom(X, (T^λ e(s))^⋆) ≅ e(s) X^⋆` and the second `Hom(T^λ e(s), X) ≅ e(s) X`. Under the route
hypothesis `hall` of Proposition 7.6. -/
theorem finrank_ext_starDual_standard_top (X : ModuleCat.{0} T) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0) :
    Module.finrank k (Ext.{w} X (starDualObj k σT
        (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u))) u.length) =
      Module.finrank k (Ext.{w} (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) X
        u.length) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  obtain ⟨E₁⟩ := nonempty_ext_starDual_top σT P u.length hz
    (fun m _ => injective_starDualObj_of_loadingSum (hP m)) X
    (fun m hm => subsingleton_hom_starDualObj_of_loadingSum (hP m) X fun s hs hmem =>
      hX s hs (not_hasLastRed_of_mem_websterWords _ _ (by simpa using hm) hmem))
  have htop := hP u.reverse.length
  rw [websterWords_length, websterWord_range, List.reverse_reverse, List.length_reverse] at htop
  obtain ⟨s, hs, hw, ⟨i⟩⟩ := htop.exists_equiv_of_singleton
  obtain ⟨s', hs', hw', ⟨E₂⟩⟩ := exists_extLinearEquiv_standard Q Λ hQ hR hall t ht u h X
    fun p hp s hs hmem => subsingleton_hom_loadingProj s hs
      (hX s hs (not_hasLastRed_of_mem_websterWords _ _
        (by rw [List.length_reverse]; omega) hmem))
  obtain rfl : s = s' := Seq.word_injective (hw.trans hw'.symm)
  have hσ : ∀ z : T, StarDual.bar σT (StarDual.bar σT z) = z := fun z => tensorFlip_tensorFlip z
  have hc : ∀ c : k, StarDual.bar σT (algebraMap k T c) = algebraMap k T c :=
    fun c => tensorFlip_algebraMap' c
  have he : IsIdempotentElem (loadingIdem Q Λ s hs) := isIdempotentElem_mk_e s hs
  have E₃ := E₁.trans ((Linear.homCongr k (Iso.refl X) (starDualIso (k := k) σT i.symm)).trans
    ((StarDual.homSwapEquiv hσ hc (loadingProj Q Λ s hs) X).trans
      (lIdealHomEquiv he (starDualObj k σT X))))
  rw [E₃.finrank_eq, StarDual.finrank_fixedSubspace_starDual hc X he (tensorFlip_loadingIdem s hs),
    ← (lIdealHomEquiv (k := k) he X).finrank_eq, E₂.finrank_eq]
  rfl

end Categorification.Stendhal
