/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardBlackInduction
import Categorification.WeightedKLR.RedStrands.PhiWordsLabels
import Categorification.WeightedKLR.RedStrands.PhiStandardLayers
import Categorification.WeightedKLR.RedStrands.TensorFinite

/-!
# The standard filtration of `T^λ e(s)` with its labels

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 5.19 and of Proposition 5.21. Every projective `T^λ e(s)` has a filtration by standard
modules `S_t` whose labels `t`, read as words, are the bottom words `phiWords s` of Lemma 5.19
(up to order). The filtration is built strand by strand from the right: appending a red strand
`λ_{ℓ+1}` turns a filtration of `T^{λ'} e(s₀)` by the `S_t` into one of `T^λ e(s₀ λ_{ℓ+1})` by
the `S_{t λ_{ℓ+1}}` (Proposition 4.18 and `twoPieceStandardEquiv`), and appending a black strand
`i` is `Fᵢ`, which filters each `S_t` by the `S_{t^{(k)}}`
(`blackIndStandardFiltration`, Proposition 5.5, `Fᵢ`-part).

Counting dimensions along this filtration gives the identity
`dim T^λ e(s) = Σ_φ dim S_{φ • s}` of Lemma 5.19 (`finrank_lIdeal_eq_sum_phiBottom`).

The red step uses the route hypothesis `AllFiniteDeltaInjective` through
`blackIndStandardFiltration`; it is proved at the standard Khovanov–Lauda parameters
(`allFiniteDeltaInjective_std`).

## Main results

* `HasLabelledStandardFiltrations`, `hasLabelledStandardFiltrations`.
* `finrank_lIdeal_eq_sum_phiBottom`: the dimension identity.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleFiltration.HasFiltration

variable {k : Type} [Field k] {A : Type} [Ring A] [Algebra k A] {ι : Type*}
  {L : ι → ModuleCat.{0} A}

open Categorification.Stendhal in
/-- **Dimensions add along a filtration**. -/
theorem finrank_kMod_eq_sum {m : List ι} {Y : ModuleCat.{0} A} (h : HasFiltration L m Y) :
    FiniteDimensional k (KMod (k := k) Y) →
      Module.finrank k (KMod (k := k) Y) =
        (m.map fun c => Module.finrank k (KMod (k := k) (L c))).sum := by
  induction h with
  | zero hY =>
    intro _
    have : Subsingleton (KMod (k := k) _) := hY
    simp [Module.finrank_zero_of_subsingleton]
  | @cons X Y Z f g m c hf hfg hg _ hZ ih =>
    intro hfin
    obtain ⟨e⟩ := hZ
    let kf : KMod (k := k) X →ₗ[k] KMod (k := k) Y := (KMod.map (k := k) f).restrictScalars k
    let kg : KMod (k := k) Y →ₗ[k] KMod (k := k) Z := (KMod.map (k := k) g).restrictScalars k
    have hX : FiniteDimensional k (KMod (k := k) X) := Module.Finite.of_injective kf hf
    have hrn := LinearMap.finrank_range_add_finrank_ker kg
    have hrange : LinearMap.range kg = ⊤ := LinearMap.range_eq_top.2 hg
    have hker : LinearMap.ker kg = LinearMap.range kf :=
      LinearMap.exact_iff.1 (show Function.Exact kf kg from hfg)
    rw [hrange, finrank_top, hker, LinearMap.finrank_range_of_inj (f := kf) hf] at hrn
    have he : Module.finrank k (KMod (k := k) Z) = Module.finrank k (KMod (k := k) (L c)) :=
      (LinearEquiv.restrictScalars k
        (show KMod (k := k) Z ≃ₗ[A] KMod (k := k) (L c) from e)).finrank_eq
    rw [List.map_cons, List.sum_cons, ← he, ← ih hX]
    omega

end Categorification.ModuleFiltration.HasFiltration

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra InductionAlong ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

local notation "Si" j => (Singleton.singleton j : Multiset I)

/-- The word of a loading. -/
abbrev loadingWord {n : ℕ} {ν : Multiset I}
    (c : {t : KLR.Seq (stendhalWeight n ν) // IsRedOrdered t}) : List (I ⊕ Fin n) :=
  List.ofFn c.1.lbl

/-- **Labelled standard filtrations** (Webster, arXiv:1309.3796v3, proofs of Lemma 5.19 and
Proposition 5.21): every `T^λ e(s)` has a filtration by standard modules whose labels, read as
words, are the bottom words of the block assignments of `s`, up to order. -/
def HasLabelledStandardFiltrations {n : ℕ} (Λ : Fin n → I →₀ ℕ) : Prop :=
  ∀ (ν : Multiset I) (s : KLR.Seq (stendhalWeight n ν)) (hs : IsRedOrdered s),
    ∃ m : List {t : KLR.Seq (stendhalWeight n ν) // IsRedOrdered t},
      HasFiltration (stdModule Q Λ ν) m
        (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ s hs))) ∧
      (m.map loadingWord).Perm (phiWords (List.ofFn s.lbl))

/-- **Base**: with no red strands, `T^λ e(s) = S_s`, and `s` is its only bottom word. -/
theorem hasLabelledStandardFiltrations_zero (Λ : Fin 0 → I →₀ ℕ) :
    HasLabelledStandardFiltrations Q Λ := by
  intro ν s hs
  refine ⟨[⟨s, hs⟩], HasFiltration.single ?_, ?_⟩
  · refine (Submodule.quotEquivOfEqBot _ ?_).symm
    rw [leftUpper_eq_bot_of_zero, Submodule.comap_bot, Submodule.ker_subtype]
  · rw [phiWords_of_forall_isLeft]
    · rfl
    · intro x _
      rcases x with i | r
      · rfl
      · exact r.elim0

section Step

variable {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "old" => Λ ∘ Fin.castSucc

omit [DecidableEq I] [Field k] in
theorem ofFn_seqMap' {J K : Type*} (f : J → K) {a : Multiset J} (s : Seq a) :
    List.ofFn (KLR.Seq.map f s).lbl = (List.ofFn s.lbl).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f a).symm (f ∘ s.lbl)).symm

omit [DecidableEq I] [Field k] in
theorem ofFn_appendRedLoading {ν : Multiset I} (s : KLR.Seq (stendhalWeight ℓ ν)) :
    List.ofFn (appendRedLoading s).lbl =
      (List.ofFn s.lbl).map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
  rw [appendRedLoading, ofFn_seqCast', KLR.ofFn_append, ofFn_seqMap', ofFn_seqSingleton']

omit [DecidableEq I] [Field k] in
theorem phiWords_appendRedLoading {ν : Multiset I} (s : KLR.Seq (stendhalWeight ℓ ν)) :
    phiWords (List.ofFn (appendRedLoading s).lbl) =
      (phiWords (List.ofFn s.lbl)).map fun W => W.map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
  rw [ofFn_appendRedLoading, phiWords_append_inr,
    phiWords_map (Fin.castSucc : Fin ℓ → Fin (ℓ + 1)) (fun _ => rfl), List.map_map]
  rfl

omit [DecidableEq I] [Field k] in
theorem ofFn_twoPieceLoading_zero {θ : Multiset I} (t : KLR.Seq (stendhalWeight ℓ θ))
    (u : KLR.Seq (0 : Multiset I)) :
    List.ofFn (twoPieceLoading θ 0 t u).lbl =
      (List.ofFn t.lbl).map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
  rw [ofFn_twoPieceLoading]
  have : List.ofFn u.lbl = [] := List.ofFn_eq_nil_iff.2 (by simp)
  rw [this]
  rfl

variable {C : QuantumGroup.CartanDatum I}

/-- **The red step**: from a labelled filtration of `T^{λ'} e(s₀)`, one of
`T^λ e(s₀ λ_{ℓ+1})`. -/
theorem labelled_appendRed (hQ : KLRSymm Q) (hold : HasLabelledStandardFiltrations Q (old)) {θ : Multiset I}
    (s₀ : KLR.Seq (stendhalWeight ℓ (θ + 0))) (hs₀ : IsRedOrdered s₀) :
    ∃ m : List {t : KLR.Seq (stendhalWeight (ℓ + 1) (θ + 0)) // IsRedOrdered t},
      HasFiltration (stdModule Q Λ (θ + 0)) m
        (loadingProj Q Λ (appendRedLoading s₀) ((appendRedLoading_ordered_iff s₀).2 hs₀)) ∧
      (m.map loadingWord).Perm (phiWords (List.ofFn (appendRedLoading s₀).lbl)) := by
  obtain ⟨t, ht, hts, ⟨f⟩⟩ := nonempty_zeroRestrict_redFactorModule_equiv Q Λ θ s₀ hs₀
  let u₀ : KLR.Seq (0 : Multiset I) := KLRAlgebra.Seq.ofList [] (by simp)
  obtain ⟨m₀, hm₀, hw₀⟩ := hold θ t ht
  have E₁ := loadingProjRedEquiv Q Λ θ hQ s₀ hs₀
  have E₂ : stdLayerModule Q Λ hQ (redLayer Q Λ θ s₀ hs₀) ≃ₗ[TensorProductAlgebra k Q Λ (θ + 0)]
      stdLayerModule Q Λ hQ (tensorLayer Q Λ rfl (oldProj Q Λ θ t ht) (cycProj Q Λ 0 u₀)) :=
    stdLayerEquiv Q Λ hQ rfl ((zeroTensorEquiv Q Λ (redFactorModule Q Λ θ s₀ hs₀)).symm.trans
      (tensorFactorCongr Q Λ f (cycProjZeroEquiv Q Λ u₀)))
  have h₁ := hasFiltration_tensorLayer Q Λ hQ (rfl : θ + 0 = θ + 0) (cycProj Q Λ 0 u₀) hm₀
  have h₂ : HasFiltration (fun d => stdModule Q Λ _ (twoPieceLabel rfl u₀ d)) m₀
      (stdLayerModule Q Λ hQ (tensorLayer Q Λ rfl (oldProj Q Λ θ t ht) (cycProj Q Λ 0 u₀))) :=
    h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ rfl d.2 u₀
  refine ⟨m₀.map (twoPieceLabel rfl u₀),
    (HasFiltration.relabel (L := stdModule Q Λ _) (twoPieceLabel rfl u₀) h₂).of_equiv
      (E₁.trans E₂).symm, ?_⟩
  rw [phiWords_appendRedLoading, List.map_map]
  have hw : ∀ d : {t : KLR.Seq (stendhalWeight ℓ θ) // IsRedOrdered t},
      loadingWord (twoPieceLabel rfl u₀ d) =
        (loadingWord d).map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := fun d => by
    rw [loadingWord, twoPieceLabel, ofFn_seqCast', ofFn_twoPieceLoading_zero]
  have hmap : m₀.map (loadingWord ∘ twoPieceLabel rfl u₀) =
      (m₀.map loadingWord).map fun W => W.map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
    rw [List.map_map]
    exact List.map_congr_left fun d _ => hw d
  have hst : List.ofFn t.lbl = List.ofFn s₀.lbl := by rw [hts, ofFn_seqCast']
  rw [hmap, ← hst]
  exact hw₀.map _

/-- **The black step**: `T^λ e(t, i) ≅ Fᵢ T^λ e(t)`, and `Fᵢ` filters each `S_c` by the
`S_{c^{(k)}}`. -/
theorem labelled_appendBlack (hR : IsRouquierQ C Q) (hblack : BlackIndStandardFiltration Q Λ)
    (i : I) {ν : Multiset I} (t : KLR.Seq (stendhalWeight (ℓ + 1) ν)) (ht : IsRedOrdered t)
    (m : List {t : KLR.Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered t})
    (hm : HasFiltration (stdModule Q Λ ν) m (loadingProj Q Λ t ht))
    (hw : (m.map loadingWord).Perm (phiWords (List.ofFn t.lbl))) :
    HasFiltration (stdModule Q Λ ((Si i) + ν)) (m.flatMap fun c => blockInsertLabels i c.1 c.2)
        (loadingProj Q Λ (appendBlackLoading i ν t) (appendBlackLoading_ordered i ν t ht)) ∧
      ((m.flatMap fun c => blockInsertLabels i c.1 c.2).map loadingWord).Perm
        (phiWords (List.ofFn (appendBlackLoading i ν t).lbl)) := by
  refine ⟨?_, ?_⟩
  · have hF : HasFiltration (fun c => blackIndModule Q Λ i (stdModule Q Λ ν c)) m
        (blackIndModule Q Λ i (loadingProj Q Λ t ht)) :=
      HasFiltration.map (blackIndModule Q Λ i)
        (fun f => Ind.map (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν) f)
        (fun _ hf => appendBlack_ind_map_injective (Q := Q) (Λ := Λ) (i := i) (ν := ν) C hR hf)
        (fun _ hf => Ind.map_surjective (φ := appendBlackNU (Q := Q) (Λ := Λ) i ν) hf)
        (fun _ _ _ hfg _ => appendBlack_ind_map_exact (Q := Q) (Λ := Λ) (i := i) (ν := ν) C hR hfg) hm
    exact (hF.bind_of_mem fun c _ => hblack i ν c.1 c.2).of_equiv
      (loadingProjBlackEquiv Q Λ i t ht).symm
  · rw [ofFn_appendBlackLoading', phiWords_append_inl, redCount_ofFn_lbl, List.map_flatMap]
    have hc : ∀ c : {t : KLR.Seq (stendhalWeight (ℓ + 1) ν) // IsRedOrdered t},
        ((blockInsertLabels i c.1 c.2).map loadingWord).Perm
          ((List.range (ℓ + 1 + 1)).map fun k => blockInsertList i k (loadingWord c)) :=
      fun c => by
        rw [blockInsertLabels, List.map_map, List.map_reverse]
        refine (List.reverse_perm _).trans ?_
        refine List.Perm.of_eq (List.map_congr_left fun k _ => ?_)
        simp [loadingWord]
    refine (List.Perm.flatMap_left _ fun c _ => hc c).trans ?_
    rw [← List.flatMap_map (f := loadingWord)
      (g := fun W => (List.range (ℓ + 1 + 1)).map fun k => blockInsertList i k W)]
    exact hw.flatMap_right _

/-- The black words: `T^λ e(s₀ λ_{ℓ+1} w)` by induction on `w`. -/
theorem labelled_blackWord (hQ : KLRSymm Q) (hR : IsRouquierQ C Q) (hblack : BlackIndStandardFiltration Q Λ)
    (hold : HasLabelledStandardFiltrations Q (old)) {θ : Multiset I}
    (s₀ : KLR.Seq (stendhalWeight ℓ (θ + 0))) (hs₀ : IsRedOrdered s₀) :
    ∀ w : List I, ∃ m : List {t : KLR.Seq (stendhalWeight (ℓ + 1) (wordWt w (θ + 0))) //
        IsRedOrdered t},
      HasFiltration (stdModule Q Λ _) m
        (loadingProj Q Λ (blackWordLoading w (appendRedLoading s₀))
          (blackWordLoading_ordered w _ ((appendRedLoading_ordered_iff s₀).2 hs₀))) ∧
      (m.map loadingWord).Perm
        (phiWords (List.ofFn (blackWordLoading w (appendRedLoading s₀)).lbl))
  | [] => labelled_appendRed Q Λ hQ hold s₀ hs₀
  | j :: w => by
    obtain ⟨m, hm, hw⟩ := labelled_blackWord hQ hR hblack hold s₀ hs₀ w
    exact ⟨_, labelled_appendBlack Q Λ hR hblack j _ _ m hm hw⟩

/-- **Induction step** on the number of red strands. -/
theorem hasLabelledStandardFiltrations_succ (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hblack : BlackIndStandardFiltration Q Λ) (hold : HasLabelledStandardFiltrations Q (old)) :
    HasLabelledStandardFiltrations Q Λ := by
  intro ν s hs
  obtain ⟨θ, w, s₀, hs₀, h, hc⟩ := exists_blackWordLoading_appendRed ν.card ν rfl s hs
  subst h
  rw [KLR.Seq.cast_rfl] at hc
  subst hc
  exact labelled_blackWord Q Λ hQ hR hblack hold s₀ hs₀ w

end Step

variable {C : QuantumGroup.CartanDatum I}

/-- **Labelled standard filtrations** of all projectives `T^λ e(s)` (Webster,
arXiv:1309.3796v3, proofs of Lemma 5.19 and Proposition 5.21). Route hypothesis:
`AllFiniteDeltaInjective` for every sequence of highest weights. -/
theorem hasLabelledStandardFiltrations (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ) :
    ∀ {n : ℕ} (Λ' : Fin n → I →₀ ℕ), HasLabelledStandardFiltrations Q Λ'
  | 0, Λ' => hasLabelledStandardFiltrations_zero Q Λ'
  | _ + 1, Λ' => hasLabelledStandardFiltrations_succ Q Λ' hQ hR
      (blackIndStandardFiltration Q hQ hR hall Λ')
      (hasLabelledStandardFiltrations hQ hR hall (Λ' ∘ Fin.castSucc))

end Categorification.Stendhal

/-! The dimension count, with the standard `k`-algebra structure on the corner (that of
`PhiStandardLayers`). -/

namespace Categorification.Stendhal

open KLR ModuleFiltration

attribute [local instance 2000] KLR.cornerAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

/-- The two `k`-algebra structures on a corner, `KLR.cornerAlgebra` and
`IsIdempotentElem.instAlgebraCorner_categorification`, are equal (not definitionally). -/
theorem cornerAlgebra_eq_instAlgebraCorner {B : Type*} [Ring B] [Algebra k B] {e : B}
    (he : IsIdempotentElem e) :
    KLR.cornerAlgebra (k := k) he = IsIdempotentElem.instAlgebraCorner_categorification he :=
  Algebra.algebra_ext _ _ fun c => Subtype.ext (by
    show algebraMap k B c * e = c • e
    rw [Algebra.smul_def])

section Dimension

variable {C : QuantumGroup.CartanDatum I} {ℓ : ℕ} {ν : Multiset I}

omit [DecidableEq I] in
/-- The identity map from `KMod X` to `X`, for a module `X` with a compatible `k`-structure. -/
def kModEquiv {A : Type} [Ring A] [Algebra k A] (X : ModuleCat.{0} A) [Module k X]
    [IsScalarTower k A X] : KMod (k := k) X ≃ₗ[k] X where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := (algebraMap_smul A c (show X from x))
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- The dimension of `S_t`, as a function of the loading (zero unless `t` is red-ordered). -/
def stdDim (Λ : Fin ℓ → I →₀ ℕ) (t : KLR.Seq (stendhalWeight ℓ ν)) : ℕ :=
  if h : IsRedOrdered t then Module.finrank k (leftStandard Q Λ t h) else 0

/-- **The dimension identity of Lemma 5.19** (Webster, arXiv:1309.3796v3): the dimension of
`T^λ e(s)` is the sum of the dimensions of the standard modules `S_{φ • s}` over the block
assignments `φ` of `s`. Route hypothesis: `AllFiniteDeltaInjective`. -/
theorem finrank_lIdeal_eq_sum_phiBottom (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (Λ : Fin ℓ → I →₀ ℕ) {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    ∑ g : PhiIndex s, Module.finrank k (leftStandard Q Λ _ (g.isRedOrdered hs)) =
      Module.finrank k (lIdeal (seqIdem Q Λ s hs)) := by
  classical
  obtain ⟨m, hm, hw⟩ := hasLabelledStandardFiltrations Q hQ hR hall Λ ν s hs
  have : Module.Finite k (TensorProductAlgebra k Q Λ ν) := by
    convert tensorProductAlgebra_finite (Q := Q) Λ ν hR using 4
    exact cornerAlgebra_eq_instAlgebraCorner _
  have hfin : FiniteDimensional k (lIdeal (seqIdem Q Λ s hs)) :=
    Module.Finite.of_injective ((lIdeal (seqIdem Q Λ s hs)).subtype.restrictScalars k)
      Subtype.val_injective
  have hY := (kModEquiv (k := k) (ModuleCat.of (TensorProductAlgebra k Q Λ ν)
    (lIdeal (seqIdem Q Λ s hs)))).symm
  have hsum := hm.finrank_kMod_eq_sum (k := k) (Module.Finite.equiv hY)
  rw [← hY.finrank_eq] at hsum
  -- the layers
  have hlay : ∀ c : {t : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered t},
      Module.finrank k (KMod (k := k) (stdModule Q Λ ν c)) = stdDim Q Λ c.1 := fun c => by
    simp only [stdDim, c.2, ↓reduceDIte]
    exact (kModEquiv (k := k) (stdModule Q Λ ν c)).finrank_eq
  have hmc : m.map (fun c => Module.finrank k (KMod (k := k) (stdModule Q Λ ν c))) =
      (m.map Subtype.val).map (stdDim Q Λ) := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => hlay c
  rw [hmc] at hsum
  -- the labels are the bottoms
  set L := assignments s.lbl
  have hwords : (L.map fun g => phiBottom s g).map (fun t => List.ofFn t.lbl) =
      phiWords (List.ofFn s.lbl) := by
    rw [List.map_map, ← map_assignWord_assignList s.lbl (redIndexed_of_isRedOrdered hs)]
    exact List.map_congr_left fun g hg => ofFn_phiBottom hg
  have hperm : (m.map Subtype.val).Perm (L.map fun g => phiBottom s g) := by
    rw [← List.map_perm_map_iff (f := fun t : KLR.Seq (stendhalWeight ℓ ν) => List.ofFn t.lbl)
      (fun a b h => seq_ext_ofFn' h), hwords, List.map_map]
    exact hw
  rw [hsum, hperm.map _ |>.sum_eq, List.map_map]
  have hL := List.sum_toFinset (fun g => stdDim Q Λ (phiBottom s g)) (nodup_assignments s.lbl)
  rw [show (stdDim Q Λ ∘ fun g => phiBottom s g) = fun g => stdDim Q Λ (phiBottom s g) from rfl,
    ← hL, ← Finset.sum_coe_sort L.toFinset (fun g => stdDim Q Λ (phiBottom s g))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [stdDim, g.isRedOrdered hs, ↓reduceDIte]

end Dimension

/-- **Webster, arXiv:1309.3796v3, Proposition 5.21 (printed form)**: for any choice `ρ` of
reduced words and every block assignment `φ` of a red-ordered loading `s`,
`P_{≥φ}/P_{>φ} ≅ S_{φ • s}`, where `P = T^λ e(s)`, `P_{>φ}` is the sum of the `T^λ x_{φ'}` with
`φ • s < φ' • s` and `P_{≥φ} = T^λ x_φ + P_{>φ}`; the isomorphism sends `[e(φ • s)]` to
`[x_φ]`. Route hypothesis: `AllFiniteDeltaInjective` (the `F`-part of Proposition 5.5 for
finite-dimensional inputs), proved at the standard Khovanov–Lauda parameters. -/
def phiLayerEquiv {C : QuantumGroup.CartanDatum I} (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    leftStandard Q Λ (phiBottom s g.1) (g.isRedOrdered hs) ≃ₗ[TensorProductAlgebra k Q Λ ν]
      phiLayer Q Λ ρ hs g :=
  LinearEquiv.ofBijective (phiLayerMap Q Λ ρ hs hρ g) (by
    have : Module.Finite k (TensorProductAlgebra k Q Λ ν) :=
      by
        convert tensorProductAlgebra_finite (Q := Q) Λ ν hR using 4
        exact cornerAlgebra_eq_instAlgebraCorner _
    exact phiLayerMap_bijective_of_finrank_sum (Q := Q) (Λ := Λ) ρ hs hρ
      (finrank_lIdeal_eq_sum_phiBottom Q hQ hR hall Λ hs) g)

theorem phiLayerEquiv_unit {C : QuantumGroup.CartanDatum I} (hQ : KLRSymm Q)
    (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    {ℓ : ℕ} {ν : Multiset I} (Λ : Fin ℓ → I →₀ ℕ)
    (ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced (Multiset.card (stendhalWeight ℓ ν)) (ρ w) ∧
      TypeA.wordProd (Multiset.card (stendhalWeight ℓ ν)) (ρ w) = w)
    {s : KLR.Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) (g : PhiIndex s) :
    phiLayerEquiv Q hQ hR hall Λ ρ hρ hs g (leftStandardUnit Q Λ _ (g.isRedOrdered hs)) =
      phiLayerGen Q Λ ρ hs g :=
  phiLayerMap_unit (Q := Q) (Λ := Λ) ρ hs hρ g

end Categorification.Stendhal
