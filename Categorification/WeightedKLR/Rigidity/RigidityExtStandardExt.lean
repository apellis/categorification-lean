/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtResolutionWords
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Ext out of a standard module through the resolution of Proposition 7.6

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1, proof
of Corollary 7.7. Let `S = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))` and let `Y` be a module with no maps
from the projectives `T^λ e(i_T)` of the resolution of Proposition 7.6 for `|T| < |u|`. Then
`Extⁱ(S, Y) = 0` for `i ≠ |u|`, and `Ext^{|u|}(S, Y) ≅ Hom(T^λ e(i_{[1,|u|]}), Y)`, where
`i_{[1,|u|]}` has word `t, u reversed, λ_ℓ`.

## Main results

* `ProjectiveResolution.subsingleton_ext_of_subsingleton_hom`,
  `ProjectiveResolution.extAddEquivHom`: Ext through a projective resolution, in a degree where
  the neighbouring terms have no maps to `Y`.
* `Stendhal.subsingleton_ext_standard`, `Stendhal.exists_extAddEquiv_standard`.
-/

universe w

open CategoryTheory Abelian Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : ProjectiveResolution X)

/-- If the term of degree `n` of a projective resolution of `X` has no nonzero maps to `Y`, then
`Ext X Y n = 0`. -/
theorem subsingleton_ext_of_subsingleton_hom (n : ℕ) [Subsingleton (R.complex.X n ⟶ Y)] :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b => by
    obtain ⟨f, hf, rfl⟩ := R.extMk_surjective a (n + 1) rfl
    obtain ⟨g, hg, rfl⟩ := R.extMk_surjective b (n + 1) rfl
    obtain rfl : f = g := Subsingleton.elim _ _
    rfl⟩

/-- If the terms of degree `n + 1` and `p = n - 1` of a projective resolution of `X` have no
nonzero maps to `Y`, then `Ext X Y n ≅ Hom(R_n, Y)`. -/
noncomputable def extAddEquivHom (p n : ℕ) (hp : p + 1 = n) (hz : IsZero (R.complex.X (n + 1)))
    [Subsingleton (R.complex.X p ⟶ Y)] : Ext X Y n ≃+ (R.complex.X n ⟶ Y) :=
  let φ : (R.complex.X n ⟶ Y) →+ Ext X Y n :=
    { toFun := fun f => R.extMk f (n + 1) rfl (hz.eq_of_src _ _)
      map_zero' := R.extMk_zero (n + 1) rfl
      map_add' := fun f g => (R.add_extMk f g (n + 1) rfl _ _).symm }
  (AddEquiv.ofBijective φ
    ⟨(injective_iff_map_eq_zero _).2 fun f hf => by
        obtain ⟨g, rfl⟩ := (R.extMk_eq_zero_iff f (n + 1) rfl (hz.eq_of_src _ _) p hp).1 hf
        rw [Subsingleton.elim g 0, Limits.comp_zero],
      fun a => by
        obtain ⟨f, hf, rfl⟩ := R.extMk_surjective a (n + 1) rfl
        exact ⟨f, rfl⟩⟩).symm

end CategoryTheory.ProjectiveResolution

namespace Categorification.Stendhal

open CategoryTheory Limits KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

/-- A sum of projectives `T^λ e(s)` has no nonzero maps to `Y` when none of its summands has. -/
theorem LoadingSum.subsingleton_hom {M Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {L : Multiset (List (I ⊕ Fin (ℓ + 1)))} (hM : LoadingSum M L)
    (hY : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), s.word ∈ L →
      Subsingleton (loadingProj Q Λ s hs ⟶ Y)) :
    Subsingleton (M ⟶ Y) := by
  classical
  obtain ⟨ι, _, s, hs, hL, ⟨e⟩⟩ := hM
  refine ⟨fun f g => ModuleCat.hom_ext ?_⟩
  have hmem : ∀ a, (s a).word ∈ L := fun a => hL ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ a)
  have key : f.hom.comp e.symm.toLinearMap = g.hom.comp e.symm.toLinearMap := by
    refine LinearMap.pi_ext fun a x => ?_
    have := hY (s a) (hs a) (hmem a)
    have h := congrArg (fun φ : loadingProj Q Λ (s a) (hs a) ⟶ Y => φ.hom x)
      (Subsingleton.elim
        (ModuleCat.ofHom ((f.hom.comp e.symm.toLinearMap).comp (LinearMap.single (TensorProductAlgebra k Q Λ ν)
          (fun b => loadingProj Q Λ (s b) (hs b)) a)))
        (ModuleCat.ofHom ((g.hom.comp e.symm.toLinearMap).comp (LinearMap.single (TensorProductAlgebra k Q Λ ν)
          (fun b => loadingProj Q Λ (s b) (hs b)) a))))
    simpa using h
  ext x
  simpa using congrArg (fun φ => φ (e x)) key

/-- A sum of projectives indexed by the empty multiset is zero. -/
theorem LoadingSum.isZero {M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    (hM : LoadingSum M 0) : IsZero M := by
  obtain ⟨ι, _, s, hs, hL, ⟨e⟩⟩ := hM
  have : IsEmpty ι := by
    rw [Multiset.map_eq_zero, Finset.val_eq_zero, Finset.univ_eq_empty_iff] at hL
    exact hL
  have : Subsingleton M := e.toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton M

/-- A sum of projectives indexed by one word is a projective `T^λ e(s)` of that word. -/
theorem LoadingSum.exists_equiv_of_singleton {M : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν)}
    {l : List (I ⊕ Fin (ℓ + 1))} (hM : LoadingSum M {l}) :
    ∃ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), s.word = l ∧
      Nonempty (M ≅ loadingProj Q Λ s hs) := by
  obtain ⟨ι, _, s, hs, hL, ⟨e⟩⟩ := hM
  have hcard : Fintype.card ι = 1 := by
    simpa using congrArg Multiset.card hL
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hcard
  have : Unique ι := { default := a, uniq := ha }
  refine ⟨s default, hs default, ?_, ⟨(e.trans (LinearEquiv.piUnique _ _)).toModuleIso⟩⟩
  have : Finset.univ.val.map (fun b => (s b).word) = {(s default).word} := by
    rw [Finset.univ_unique]
    rfl
  exact Multiset.singleton_inj.1 (this.symm.trans hL)

omit [DecidableEq I] in
/-- The subsets of `{0, …, m - 1}` with `m` elements: only the whole set. -/
theorem websterWords_length (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) :
    websterWords t u u.length = {websterWord t u (Multiset.range u.length)} := by
  have h : Multiset.powersetCard u.length (Multiset.range u.length) =
      {Multiset.range u.length} := by
    simpa using Multiset.powersetCard_self (Multiset.range u.length)
  rw [websterWords, h, Multiset.map_singleton]

omit [DecidableEq I] in
/-- There are no subsets of `{0, …, m - 1}` with more than `m` elements. -/
theorem websterWords_eq_zero (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) {n : ℕ}
    (hn : u.length < n) : websterWords t u n = 0 := by
  rw [websterWords, Multiset.powersetCard_eq_empty _ (by simpa using hn), Multiset.map_zero]

omit [DecidableEq I] in
/-- The word `t, u reversed, λ_ℓ` of the last term of the resolution of Proposition 7.6. -/
theorem websterWord_range (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) :
    websterWord t u (Multiset.range u.length) =
      t ++ u.reverse.map Sum.inl ++ [Sum.inr (Fin.last ℓ)] := by
  have hin : pickIn u (Multiset.range u.length) = u := by
    rw [pickIn, List.filter_eq_self.2 fun p hp => by
      simpa using lt_of_mem_zip_range hp]
    exact List.map_fst_zip (by simp)
  have hout : pickOut u (Multiset.range u.length) = [] := by
    rw [pickOut, List.filter_eq_nil_iff.2 fun p hp => by
      simpa using lt_of_mem_zip_range hp]
    rfl
  simp [websterWord, hin, hout]

/-! ### Ext out of a standard module -/

section Ext

universe v

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  (Y : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall

/-- **Vanishing of Ext out of a standard module** (Webster, arXiv:1309.3796v3, §7.1, proof of
Corollary 7.7): if no projective `T^λ e(i_T)` with `|T| = n` of the resolution of Proposition 7.6
maps nontrivially to `Y`, then `Extⁿ(S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)), Y) = 0`. Here
`cycWord Q Λ u = R^{λ_ℓ} e(u.reverse)`. Under the route hypothesis `hall` of Proposition 7.6. -/
theorem subsingleton_ext_standard (n : ℕ)
    (hY : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word ∈ websterWords (t.word.map (addRedColor ℓ)) u.reverse n →
        Subsingleton (loadingProj Q Λ s hs ⟶ Y)) :
    Subsingleton (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) Y n) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have := (hP n).subsingleton_hom hY
  exact P.subsingleton_ext_of_subsingleton_hom n

/-- **Ext out of a standard module in the top degree** (Webster, arXiv:1309.3796v3, §7.1, proof
of Corollary 7.7): for `u` of length `p + 1`, if no projective `T^λ e(i_T)` with `|T| = p` maps
nontrivially to `Y`, then `Ext^{|u|}(S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u.reverse)), Y) ≅ Hom(T^λ e(s), Y)`
for the loading `s` with word `t, u, λ_ℓ`, the last term of the resolution. Under the route
hypothesis `hall` of Proposition 7.6. -/
theorem exists_extAddEquiv_standard (p : ℕ) (hp : p + 1 = u.length)
    (hY : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word ∈ websterWords (t.word.map (addRedColor ℓ)) u.reverse p →
        Subsingleton (loadingProj Q Λ s hs ⟶ Y)) :
    ∃ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s),
      s.word = t.word.map (addRedColor ℓ) ++ u.map Sum.inl ++ [Sum.inr (Fin.last ℓ)] ∧
        Nonempty (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) Y u.length ≃+
          (loadingProj Q Λ s hs ⟶ Y)) := by
  obtain ⟨P, hP⟩ := exists_projectiveResolution_websterWords Q Λ hQ hR hall t ht u h
  have htop := hP u.reverse.length
  rw [websterWords_length, websterWord_range, List.reverse_reverse, List.length_reverse] at htop
  obtain ⟨s, hs, hw, ⟨e⟩⟩ := htop.exists_equiv_of_singleton
  have hz : IsZero (P.complex.X (u.length + 1)) := by
    have := hP (u.length + 1)
    rw [websterWords_eq_zero _ _ (by simp)] at this
    exact this.isZero
  have := (hP p).subsingleton_hom hY
  refine ⟨s, hs, hw, ⟨(P.extAddEquivHom p u.length hp hz).trans ?_⟩⟩
  exact
    { toFun := fun f => e.inv ≫ f
      invFun := fun g => e.hom ≫ g
      left_inv := fun f => by simp
      right_inv := fun g => by simp
      map_add' := fun f g => Preadditive.comp_add _ _ _ _ _ _ }

end Ext

end Categorification.Stendhal
