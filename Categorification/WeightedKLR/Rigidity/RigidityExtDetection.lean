/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardKilled
import Categorification.WeightedKLR.RedStrands.LastRedSupport
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition
import Categorification.WeightedKLR.RedStrands.AppendStrandReflection

/-!
# Nonzero modules are detected by maps into dual standard modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Proposition 7.8. Every nonzero module `Y` over `T^λ` receives a nonzero map from a standard
module `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`: take a loading `e(s)` acting nontrivially on `Y` whose
last red strand sits as far right as possible. Then `Y` is killed by the loadings of the degree one
term of the resolution of Proposition 7.6, so the map `T^λ e(s) → Y` of a vector `e(s) y ≠ 0`
descends to the standard module. Dually, every nonzero module has a nonzero map into a dual
standard module `∇(t, u)`.

## Main results

* `StarDual.homSwap`: maps `N → M^⋆` give maps `M → N^⋆`.
* `exists_hom_standard_ne_zero`: a nonzero map from a standard module into a nonzero `Y`.
* `subsingleton_of_forall_subsingleton_hom_starDual_standard`: a module without nonzero maps into
  any dual standard module is zero.
-/

noncomputable section
namespace Categorification

open CategoryTheory Limits MulOpposite

/-! ### Swapping maps into duals -/

namespace StarDual

variable {k A : Type} [Field k] [Ring A] [Algebra k A] {σ : A ≃+* Aᵐᵒᵖ}
  {M N : Type} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- A map `N → M^⋆` gives a map `M → N^⋆`, `(swap g)(m)(n) = g(n)(m)`. -/
def homSwap (hσ : ∀ a, bar σ (bar σ a) = a)
    (hc : ∀ c : k, bar σ (algebraMap k A c) = algebraMap k A c)
    (g : N →ₗ[A] StarDual k σ M) : M →ₗ[A] StarDual k σ N where
  toFun m := ofDual
    { toFun := fun n => toDual (g n) m
      map_add' := fun n n' => by rw [map_add]; rfl
      map_smul' := fun c n => by
        rw [← algebraMap_smul A c n, map_smul, smul_apply, hc, algebraMap_smul,
          LinearMap.map_smul]
        rfl }
  map_add' m m' := LinearMap.ext fun n => map_add (toDual (g n)) m m'
  map_smul' a m := LinearMap.ext fun n => by
    change toDual (g n) (a • m) = toDual (g (bar σ a • n)) m
    rw [LinearMap.map_smul g, smul_apply, hσ]

variable (hσ : ∀ a, bar σ (bar σ a) = a)
  (hc : ∀ c : k, bar σ (algebraMap k A c) = algebraMap k A c)

theorem homSwap_apply (g : N →ₗ[A] StarDual k σ M) (m : M) (n : N) :
    toDual (homSwap hσ hc g m) n = toDual (g n) m := rfl

theorem homSwap_ne_zero {g : N →ₗ[A] StarDual k σ M} (hg : g ≠ 0) : homSwap hσ hc g ≠ 0 := by
  intro h
  apply hg
  refine LinearMap.ext fun n => LinearMap.ext fun m => ?_
  change toDual (homSwap hσ hc g m) n = 0
  rw [h]
  rfl

omit [Algebra k A] [Module A M] [IsScalarTower k A M] in
/-- The dual of a nonzero vector space is nonzero. -/
theorem nontrivial (h : Nontrivial M) : Nontrivial (StarDual k σ M) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k M, φ m ≠ 0 := by
    by_contra! H
    exact hm ((Module.forall_dual_apply_eq_zero_iff k m).1 H)
  exact ⟨⟨ofDual φ, 0, fun h0 => hφ (by rw [show φ = 0 from h0]; rfl)⟩⟩

end StarDual

namespace Stendhal

open KLR KLRAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

omit [DecidableEq I] in
/-- The letters of `u` outside the empty set of positions: all of `u`. -/
theorem pickOut_zero (u : List I) : pickOut u 0 = u := by
  rw [pickOut, List.filter_eq_self.2 (fun p _ => by simp)]
  exact List.map_fst_zip (by simp)

omit [DecidableEq I] in
theorem pickIn_zero (u : List I) : pickIn u 0 = [] := by
  rw [pickIn, List.filter_eq_nil_iff.2 (fun p _ => by simp)]
  rfl

/-- A loading has one last red strand. -/
theorem lastRed_unique (s : Seq (stendhalWeight (ℓ + 1) ν))
    {a b : Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))}
    (ha : s.lbl a = Sum.inr (Fin.last ℓ)) (hb : s.lbl b = Sum.inr (Fin.last ℓ)) : a = b := by
  classical
  have hc := card_filter_lbl_eq s (Sum.inr (Fin.last ℓ))
  have h1 : Multiset.count (Sum.inr (Fin.last ℓ)) (stendhalWeight (ℓ + 1) ν) = 1 := by
    rw [stendhalWeight, Multiset.count_add, Multiset.count_map_eq_count' _ _ Sum.inr_injective,
      Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ _),
      Multiset.count_eq_zero.2 (by simp)]
  rw [h1, Finset.card_eq_one] at hc
  obtain ⟨c, hc⟩ := hc
  have ha' : a ∈ Finset.univ.filter (s.lbl · = Sum.inr (Fin.last ℓ)) := by simp [ha]
  have hb' : b ∈ Finset.univ.filter (s.lbl · = Sum.inr (Fin.last ℓ)) := by simp [hb]
  rw [hc, Finset.mem_singleton] at ha' hb'
  rw [ha', hb']

section Detection

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ)

include hR hall in
/-- **Detection by standard modules**: every nonzero module `Y` over `T^λ` receives a nonzero
map from a standard module `S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`. -/
theorem exists_hom_standard_ne_zero (Y : ModuleCat.{0} T) [Nontrivial Y] :
    ∃ (θ' : Multiset I) (t : Seq (stendhalWeight ℓ θ')) (ht : IsRedOrdered t) (u : List I)
      (h : θ' + wordWt u 0 = ν)
      (f : tensorStd Q Λ hQ h (oldProj Q Λ θ' t ht) (cycWord Q Λ u) ⟶ Y), f ≠ 0 := by
  classical
  let ρ : T →+* AddMonoid.End Y := Module.toAddMonoidEnd T Y
  have : Nontrivial (AddMonoid.End Y) := by
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    exact nontrivial_of_ne 1 0 fun h => hy (DFunLike.congr_fun h y)
  obtain ⟨p, s, hs, hp, hne, hker⟩ := exists_supported_lastRedLayer ρ
  -- `Y` is killed by the loadings whose last red strand is after `p`.
  have hkill : KilledAfter Q Λ p.val Y := by
    intro s' hs' a ha hr y
    have hmem : loadingIdem Q Λ s' hs' ∈ smallerSuffixIdeal Q Λ p :=
      TwoSidedIdeal.subset_span ⟨s', hs', a, ha, hr, rfl⟩
    exact DFunLike.congr_fun ((TwoSidedIdeal.mem_ker ρ).1 (hker hmem)) y
  obtain ⟨y, hy⟩ : ∃ y : Y, loadingIdem Q Λ s hs • y ≠ 0 := by
    by_contra! H
    exact hne (AddMonoidHom.ext H)
  -- Write `s` as a two-piece loading `t λ_{ℓ+1} w`.
  obtain ⟨θ, β, hθβ, t, w, ht, hst⟩ := exists_twoPieceLoading_eq hs
  set u : List I := w.word.reverse with hu
  have hβ : wordWt u 0 = β := by
    rw [← coe_reverse_eq_wordWt, hu, List.reverse_reverse, coe_word_seq]
  have h : θ + wordWt u 0 = ν := by rw [hβ, hθβ]
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have hword : s.word = websterWord (t.word.map (addRedColor ℓ)) u.reverse 0 := by
    rw [← hst, Seq.word_cast, websterWord, pickIn_zero, pickOut_zero, hu, List.reverse_reverse]
    simp only [Seq.word, List.reverse_nil, List.map_nil, List.append_nil]
    rw [ofFn_twoPieceLoading]
    simp
  have h0 : websterWords (t.word.map (addRedColor ℓ)) u.reverse 0 = {s.word} := by
    rw [websterWords, Multiset.powersetCard_zero_left, Multiset.map_singleton, hword]
  obtain ⟨s₀, hs₀, hw₀, ⟨e₀⟩⟩ := LoadingSum.exists_equiv_of_singleton (h0 ▸ hP 0)
  obtain rfl : s = s₀ := (Seq.word_injective hw₀).symm
  -- The position of the last red strand of `s` is `|t|`.
  have hlen : (t.word.map (addRedColor ℓ)).length = Multiset.card θ + ℓ := by
    rw [List.length_map, Seq.length_word]; simp [stendhalWeight]
  have hpos : p.val = (t.word.map (addRedColor ℓ)).length := by
    have hlt : (t.word.map (addRedColor ℓ)).length + 0 <
        Multiset.card (stendhalWeight (ℓ + 1) ν) := by
      rw [← Seq.length_word s, hword, websterWord]; simp
    have := lbl_of_word_eq_websterWord (j := 0) (s := s) (by rw [h0]; simp)
      ⟨_, hlt⟩ rfl
    exact congrArg Fin.val (lastRed_unique s hp this)
  -- The degree one term has no maps to `Y`.
  have h1 : Subsingleton (P.complex.X 1 ⟶ Y) := by
    refine (hP 1).subsingleton_hom fun s' hs' hmem => subsingleton_hom_loadingProj s' hs' ?_
    have hlt : (t.word.map (addRedColor ℓ)).length + 1 <
        Multiset.card (stendhalWeight (ℓ + 1) ν) := by
      obtain ⟨Tm, hT, hw⟩ := Multiset.mem_map.1 hmem
      have hlen' := congrArg List.length hw
      rw [Seq.length_word] at hlen'
      rw [← hlen', websterWord]
      have := length_pickIn u.reverse (Multiset.mem_powersetCard.1 hT).1
      simp only [List.length_append, List.length_map, List.length_reverse, List.length_singleton,
        this, (Multiset.mem_powersetCard.1 hT).2]
      omega
    exact hkill s' hs' ⟨_, hlt⟩ (by simp only [hpos]; omega)
      (lbl_of_word_eq_websterWord hmem _ rfl)
  -- The map `T^λ e(s) → Y` of the vector `e(s) y`.
  have he : loadingIdem Q Λ s hs * loadingIdem Q Λ s hs = loadingIdem Q Λ s hs :=
    isIdempotentElem_mk_e s hs
  let φ : loadingProj Q Λ s hs ⟶ Y := ModuleCat.ofHom
    { toFun := fun x => (show lIdeal (loadingIdem Q Λ s hs) from x).1 • y
      map_add' := fun x x' => add_smul _ _ _
      map_smul' := fun a x => mul_smul _ _ _ }
  have hφ : φ ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun f : loadingProj Q Λ s hs ⟶ Y =>
      f.hom (⟨loadingIdem Q Λ s hs, he⟩ : lIdeal (loadingIdem Q Λ s hs))) h0
    exact this
  let f₀ : P.complex.X 0 ⟶ Y := e₀.hom ≫ φ
  have hf₀ : f₀ ≠ 0 := by
    intro h0
    apply hφ
    rw [← Category.id_comp φ, ← e₀.inv_hom_id, Category.assoc]
    change e₀.inv ≫ f₀ = 0
    rw [h0, comp_zero]
  have hd : P.complex.d 1 0 ≫ f₀ = 0 := Subsingleton.elim _ _
  let g : tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u) ⟶ Y :=
    (P.isColimitCokernelCofork).desc (CokernelCofork.ofπ f₀ hd)
  have hg : P.π.f 0 ≫ g = f₀ :=
    (P.isColimitCokernelCofork).fac (CokernelCofork.ofπ f₀ hd) WalkingParallelPair.one
  refine ⟨θ, t, ht, u, h, g, fun h0 => hf₀ ?_⟩
  rw [← hg, h0]
  exact Limits.comp_zero

include hR hall in
/-- **Detection by dual standard modules**: a module with no nonzero maps into any dual standard
module `∇(t, u) = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))^⋆` is zero. -/
theorem subsingleton_of_forall_subsingleton_hom_starDual_standard (Z : ModuleCat.{0} T)
    (hZ : ∀ (θ' : Multiset I) (t : Seq (stendhalWeight ℓ θ')) (ht : IsRedOrdered t) (u : List I)
      (h : θ' + wordWt u 0 = ν), Subsingleton (Z ⟶ starDualObj k σT
        (tensorStd Q Λ hQ h (oldProj Q Λ θ' t ht) (cycWord Q Λ u)))) :
    Subsingleton Z := by
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  have : Nontrivial (starDualObj k σT Z) :=
    StarDual.nontrivial (k := k) (A := T) (σ := σT) (M := Z) hns
  obtain ⟨θ', t, ht, u, h, f, hf⟩ :=
    exists_hom_standard_ne_zero Q Λ hQ hR hall (starDualObj k σT Z)
  have hσ : ∀ a : T, StarDual.bar σT (StarDual.bar σT a) = a := tensorFlip_tensorFlip
  have hc : ∀ c : k, StarDual.bar σT (algebraMap k T c) = algebraMap k T c := fun c => by
    change tensorFlip _ = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, tensorFlip_one]
  have hf' : f.hom ≠ 0 := fun h0 => hf (ModuleCat.hom_ext h0)
  exact StarDual.homSwap_ne_zero hσ hc hf' (congrArg ModuleCat.Hom.hom
    ((hZ θ' t ht u h).elim (ModuleCat.ofHom (StarDual.homSwap hσ hc f.hom) :
      Z ⟶ starDualObj k σT (tensorStd Q Λ hQ h (oldProj Q Λ θ' t ht) (cycWord Q Λ u))) 0))

end Detection

end Stendhal

end Categorification
