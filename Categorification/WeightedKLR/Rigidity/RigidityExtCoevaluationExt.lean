/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardExt
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# Vanishing of Ext from a standard module to a module killed by the cuts

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Corollary 7.7, vanishing part. Let `L` be a right `T^λ`-module killed by the idempotents of the
*cuts*, the red-ordered loadings whose last strand is not the last red strand (for the simple
head `L_λ` of Lemma 7.3 these are the loadings `κ` with `κ(2) < |ν|`). Through the horizontal
reflection `T^λ ≅ (T^λ)ᵒᵖ`, `L` is a left module `flipLeft L`. In the resolution of
Proposition 7.6 of `S = S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))`, every term of degree `n < |u|` is a sum of
projectives of cuts, so `Extⁿ(S, L) = 0` for `n ≠ |u|` (`subsingleton_ext_standard_of_cut`).
For `L = L_λ` this is the vanishing part of Corollary 7.7
(`subsingleton_ext_standard_coevaluationHead`).
-/

universe v

open CategoryTheory Abelian Limits MulOpposite

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I}

/-! ### Right modules as left modules -/

variable (Q Λ ν) in
/-- A right `T^λ_ν`-module as a left module, through the horizontal reflection
`T^λ_ν ≅ (T^λ_ν)ᵒᵖ`. -/
noncomputable def flipLeft (L : Type) [AddCommGroup L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L] :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν) :=
  @ModuleCat.of _ _ L _
    (Module.compHom L ((tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν :
      TensorProductAlgebra k Q Λ ν ≃+* (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) :
        TensorProductAlgebra k Q Λ ν →+* (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ))

/-- The action on `flipLeft L`: `a • y = y · ā`, with `ā` the reflection of `a`. -/
theorem flipLeft_smul {L : Type} [AddCommGroup L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
    (a : TensorProductAlgebra k Q Λ ν) (y : flipLeft Q Λ ν L) :
    a • y = (show flipLeft Q Λ ν L from op (tensorFlip a) • (show L from y)) :=
  rfl

/-- If `L e(s) = 0`, there are no nonzero maps `T^λ e(s) → flipLeft L`. -/
theorem subsingleton_hom_loadingProj_flipLeft {L : Type} [AddCommGroup L]
    [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L] (s : Seq (stendhalWeight (ℓ + 1) ν))
    (hs : IsRedOrdered s) (hL : ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0) :
    Subsingleton (loadingProj Q Λ s hs ⟶ flipLeft Q Λ ν L) := by
  have hzero : ∀ f : loadingProj Q Λ s hs ⟶ flipLeft Q Λ ν L, f = 0 := by
    intro f
    have he : loadingIdem Q Λ s hs * loadingIdem Q Λ s hs = loadingIdem Q Λ s hs :=
      isIdempotentElem_mk_e s hs
    let e₀ : loadingProj Q Λ s hs :=
      (⟨loadingIdem Q Λ s hs, he⟩ : lIdeal (loadingIdem Q Λ s hs))
    have hfe : f.hom e₀ = 0 := by
      have h1 : f.hom e₀ = f.hom (loadingIdem Q Λ s hs • e₀) := by
        congr 1
        exact Subtype.ext he.symm
      rw [h1, LinearMap.map_smul]
      rw [flipLeft_smul, loadingIdem, tensorFlip_mk_e]
      exact hL _
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hx : x = (x.1 : TensorProductAlgebra k Q Λ ν) • e₀ :=
      Subtype.ext x.2.symm
    rw [hx, LinearMap.map_smul, hfe, smul_zero]
    rfl
  exact ⟨fun f g => (hzero f).trans (hzero g).symm⟩

/-! ### The cuts among the loadings of the resolution -/

omit [DecidableEq I] in
/-- The last letter of the word of a loading whose last strand is the last red strand. -/
theorem getLast?_word_of_hasLastRed {s : Seq (stendhalWeight (ℓ + 1) ν)} (h : HasLastRed s) :
    s.word.getLast? = some (Sum.inr (Fin.last ℓ)) := by
  rw [List.getLast?_eq_getElem?, Seq.length_word]
  have hc : Multiset.card (stendhalWeight (ℓ + 1) ν) = Multiset.card ν + ℓ + 1 := by
    simp [stendhalWeight]; omega
  rw [hc, show Multiset.card ν + ℓ + 1 - 1 = Multiset.card ν + ℓ by omega,
    List.getElem?_eq_getElem (by simp [hc])]
  simp only [Seq.word, List.getElem_ofFn]
  exact congrArg some h

omit [DecidableEq I] in
/-- A subset `T ⊊ {0, …, |u| - 1}` leaves a letter of `u` outside. -/
theorem pickOut_ne_nil (u : List I) {T : Multiset ℕ}
    (hcard : Multiset.card T < u.length) : pickOut u T ≠ [] := by
  obtain ⟨a, ha, haT⟩ : ∃ a ∈ Multiset.range u.length, a ∉ T := by
    by_contra hcon
    push Not at hcon
    have hle : Multiset.range u.length ≤ T :=
      (Multiset.le_iff_subset (Multiset.nodup_range _)).2 fun a ha => hcon a ha
    have := Multiset.card_le_card hle
    simp at this
    omega
  have hlt : a < u.length := Multiset.mem_range.1 ha
  intro hnil
  have hmem : (u[a], a) ∈ (u.zip (List.range u.length)).filter (fun p => decide (p.2 ∉ T)) := by
    refine List.mem_filter.2 ⟨?_, by simpa using haT⟩
    rw [List.mem_iff_getElem]
    exact ⟨a, by simpa using hlt, by simp⟩
  have : ((u.zip (List.range u.length)).filter (fun p => decide (p.2 ∉ T))) = [] :=
    List.map_eq_nil_iff.1 hnil
  rw [this] at hmem
  simp at hmem

omit [DecidableEq I] in
/-- The loadings of the resolution of Proposition 7.6 in degree `n < |u|` are cuts. -/
theorem not_hasLastRed_of_mem_websterWords (tw : List (I ⊕ Fin (ℓ + 1))) (u : List I) {n : ℕ}
    (hn : n < u.length) {s : Seq (stendhalWeight (ℓ + 1) ν)} (hs : s.word ∈ websterWords tw u n) :
    ¬HasLastRed s := by
  intro h
  obtain ⟨T, hT, hw⟩ := Multiset.mem_map.1 hs
  have hne := pickOut_ne_nil u ((Multiset.mem_powersetCard.1 hT).2 ▸ hn)
  have hlast := getLast?_word_of_hasLastRed h
  rw [← hw, websterWord, List.getLast?_append_of_ne_nil _ (by simpa using hne),
    List.getLast?_map] at hlast
  cases hp : (pickOut u T).getLast? with
  | none => simp [List.getLast?_eq_none_iff, hne] at hp
  | some a => simp [hp] at hlast

/-! ### Corollary 7.7, vanishing part -/

section Ext

variable (Q Λ) (hQ : KLRSymm Q) {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I} (t : Seq (stendhalWeight ℓ θ))
  (ht : IsRedOrdered t) (u : List I) (h : θ + wordWt u 0 = ν)
  (L : Type) [AddCommGroup L] [Module (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ L]
  [HasExt.{v} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR hall in
/-- **Ext from a standard module to a module killed by the cuts** (Webster, arXiv:1309.3796v3,
§7.1, proof of Corollary 7.7): if `L e(s) = 0` for every red-ordered loading `s` whose last
strand is not the last red strand, then `Extⁿ(S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u)), L) = 0` for
`n ≠ |u|`. Ext of left modules, with `L` a left module through the horizontal reflection. Under
the route hypothesis `hall` of Proposition 7.6. -/
theorem subsingleton_ext_standard_of_cut
    (hL : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ y : L, op (loadingIdem Q Λ s hs) • y = 0)
    (n : ℕ) (hn : n ≠ u.length) :
    Subsingleton
      (Ext (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ u)) (flipLeft Q Λ ν L) n) := by
  refine subsingleton_ext_standard Q Λ hQ hR hall t ht u h _ n fun s hs hmem => ?_
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact subsingleton_hom_loadingProj_flipLeft s hs
      (hL s hs (not_hasLastRed_of_mem_websterWords _ _ (by simpa using hlt) hmem))
  · rw [websterWords_eq_zero _ _ (by simpa using hgt)] at hmem
    exact absurd hmem (Multiset.notMem_zero _)

end Ext

end Categorification.Stendhal
