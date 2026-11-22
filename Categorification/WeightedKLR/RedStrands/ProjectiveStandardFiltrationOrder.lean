/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ProjectiveStandardFiltration
import Categorification.WeightedKLR.RedStrands.ConcatLoadingOrder

/-!
# The order of the standard filtration of a projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Corollary 5.21. The standard filtration of `T^λ e(s)` built in the proof of Proposition 5.20
(`hasStandardFiltrations`) has a standard module `S_{s'}` with `s'` equivalent to `s` (equal
black counts) as its top quotient, and all its other subquotients are standard modules `S_t`
with `t` strictly above `s` in Webster's order (`StendhalLT s t`).

The proof follows the induction of Proposition 5.20. For `s = (s₀, λ_{ℓ+1}, w)`, the top layer
of the filtration of `T^λ e(s)` by `F_w` is `S(T^{λ'} e(t) ⊠ R e(u))` with the same first factor
weight `θ` as `s₀` and `t` equivalent to `s₀`; every other layer has strictly larger first factor
weight, and its first factor is `T^{λ'} e(t)` with `t` equivalent to `s₀`
(`StdLayer.wordLayers_head`, `exists_stdLayerModule_equiv_tensorLayer_count`).

## Main definitions and results

* `HasOrderedStandardFiltrations Q Λ`: every `T^λ e(s)` has a standard filtration with top
  quotient `S_{s'}`, `s'` equivalent to `s`, and the other subquotients `S_t` with `t > s`.
* `hasOrderedStandardFiltrations`: this holds, given the route hypothesis
  `AllFiniteDeltaInjective` of Proposition 5.20.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.ModuleFiltration.HasFiltration

universe u v w w'

variable {A : Type u} [Ring A] {ι : Type w} {ι' : Type w'} {L : ι → ModuleCat.{v} A}
  {L' : ι' → ModuleCat.{v} A} (P : ι' → Prop)

/-- Refining a filtration, keeping track of a property of the new labels. -/
theorem exists_refine_forall {m : List ι} {Y : ModuleCat.{v} A} (h : HasFiltration L m Y)
    (hL : ∀ c ∈ m, ∃ l, HasFiltration L' l (L c) ∧ ∀ y ∈ l, P y) :
    ∃ l, HasFiltration L' l Y ∧ ∀ y ∈ l, P y := by
  induction h with
  | zero hY => exact ⟨[], .zero hY, by simp⟩
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    obtain ⟨l₁, h₁, hP₁⟩ := hL c List.mem_cons_self
    obtain ⟨l₂, h₂, hP₂⟩ := ih fun d hd => hL d (List.mem_cons_of_mem _ hd)
    refine ⟨l₁ ++ l₂, (h₁.of_equiv e.symm).extension f g hf hfg hg h₂, fun y hy => ?_⟩
    rcases List.mem_append.1 hy with hy | hy
    exacts [hP₁ y hy, hP₂ y hy]

/-- Refining a filtration whose top subquotient has a filtration with top label `x`: the
refinement has top label `x`. -/
theorem exists_refine_head {c₀ : ι} {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L (c₀ :: m) Y) {x : ι'} {l₀ : List ι'}
    (h₀ : HasFiltration L' (x :: l₀) (L c₀))
    (hL : ∀ c ∈ m, ∃ l, HasFiltration L' l (L c) ∧ ∀ y ∈ l, P y) :
    ∃ l, HasFiltration L' (x :: (l₀ ++ l)) Y ∧ ∀ y ∈ l, P y := by
  cases h with
  | cons f g m c hf hfg hg hX hZ =>
    obtain ⟨e⟩ := hZ
    obtain ⟨l₂, h₂, hP₂⟩ := exists_refine_forall P hX hL
    exact ⟨l₂, (h₀.of_equiv e.symm).extension f g hf hfg hg h₂, hP₂⟩

end Categorification.ModuleFiltration.HasFiltration

namespace Categorification.Stendhal

open KLR ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Counts

variable {I : Type} [DecidableEq I] {ℓ : ℕ}

/-- Appending a black strand at the right does not change the black counts. -/
theorem blackCount_appendBlackLoading (i : I) (ν : Multiset I) (s : Seq (stendhalWeight ℓ ν))
    (r : Fin ℓ) (j : I) : blackCount (appendBlackLoading i ν s) r j = blackCount s r j := by
  rw [appendBlackLoading, blackCount_cast, blackCount_append_left _ _ (exists_lbl_eq_inr s r)]
  intro y hy
  have h : (default : Seq ({Sum.inl i} : Multiset (I ⊕ Fin ℓ))).lbl y ∈
      ({Sum.inl i} : Multiset (I ⊕ Fin ℓ)) := Seq.mem _ y
  rw [hy, Multiset.mem_singleton] at h
  cases h

theorem blackCount_blackWordLoading {ν : Multiset I} (r : Fin (ℓ + 1)) (j : I) :
    (w : List I) → (s : Seq (stendhalWeight (ℓ + 1) ν)) →
      blackCount (blackWordLoading w s) r j = blackCount s r j
  | [], _ => rfl
  | j' :: w, s => (blackCount_appendBlackLoading j' _ _ r j).trans
      (blackCount_blackWordLoading r j w s)

theorem blackCount_appendRedLoading_castSucc {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (r : Fin ℓ) (i : I) : blackCount (appendRedLoading s) r.castSucc i = blackCount s r i := by
  rw [appendRedLoading, blackCount_cast, blackCount_append_left]
  · exact blackCount_map (Fin.castSucc_injective ℓ) s r i
  · obtain ⟨a, ha⟩ := exists_lbl_eq_inr s r
    refine ⟨Fin.cast (Multiset.card_map _ _).symm a, ?_⟩
    rw [Seq.map_lbl]
    simp [ha]
  · intro y hy
    rw [singletonRedSeq_lbl] at hy
    exact (Fin.castSucc_lt_last r).ne (Sum.inr_injective hy).symm

theorem blackCount_appendRedLoading_last {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν))
    (i : I) : blackCount (appendRedLoading s) (Fin.last ℓ) i = ν.count i := by
  have h0 : 0 < Multiset.card ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1))) := by simp
  rw [appendRedLoading, blackCount_cast,
    blackCount_append_right _ _ _ ⟨⟨0, h0⟩, singletonRedSeq_lbl _⟩,
    blackCount_eq_zero_of_first _ h0 (singletonRedSeq_lbl _), add_zero, card_filter_lbl_eq,
    show (Sum.inl i : I ⊕ Fin (ℓ + 1)) = addRedColor ℓ (Sum.inl i) from rfl,
    Multiset.count_map_eq_count' _ _ (addRedColor_injective ℓ) (Sum.inl i)]
  · simp [stendhalWeight, Multiset.count_map_eq_count' _ _ Sum.inl_injective]
  · intro x hx
    rw [Seq.map_lbl] at hx
    rcases h : s.lbl (Fin.cast (Multiset.card_map _ _) x) with j | r
    · rw [h] at hx
      cases hx
    · rw [h] at hx
      exact (Fin.castSucc_lt_last r).ne (Sum.inr_injective hx)

/-- Webster's order on loadings of `ℓ + 1` red strands, at the first `ℓ` and the last red
strand. -/
theorem stendhalLE_iff_castSucc_last {μ : Multiset (I ⊕ Fin (ℓ + 1))} (a b : Seq μ) :
    StendhalLE a b ↔ (∀ (r : Fin ℓ) i, blackCount a r.castSucc i ≤ blackCount b r.castSucc i) ∧
      ∀ i, blackCount a (Fin.last ℓ) i ≤ blackCount b (Fin.last ℓ) i := by
  refine ⟨fun h => ⟨fun r i => h _ i, fun i => h _ i⟩, fun h R i => ?_⟩
  rcases Fin.eq_castSucc_or_eq_last R with ⟨r, rfl⟩ | rfl
  exacts [h.1 r i, h.2 i]

end Counts

variable {I : Type} [DecidableEq I] {k : Type} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k)

/-- **Ordered standard filtrations** (Webster, arXiv:1309.3796v2, proof of Corollary 5.21):
every projective `T^λ e(s)` has a standard filtration whose top quotient is `S_{s'}` with `s'`
equivalent to `s` (equal black counts), and whose other subquotients are standard modules `S_t`
with `t` strictly above `s`. -/
def HasOrderedStandardFiltrations {n : ℕ} (Λ : Fin n → I →₀ ℕ) : Prop :=
  ∀ (ν : Multiset I) (s : Seq (stendhalWeight n ν)) (hs : IsRedOrdered s),
    ∃ (s' : {t : Seq (stendhalWeight n ν) // IsRedOrdered t})
      (m : List {t : Seq (stendhalWeight n ν) // IsRedOrdered t}),
      StendhalLE s s'.1 ∧ StendhalLE s'.1 s ∧ (∀ c ∈ m, StendhalLT s c.1) ∧
      HasFiltration (stdModule Q Λ ν) (s' :: m)
        (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (lIdeal (seqIdem Q Λ s hs)))

/-- **Base of the induction**: with no red strands, `T^λ e(s) = S_s`. -/
theorem hasOrderedStandardFiltrations_zero (Λ : Fin 0 → I →₀ ℕ) :
    HasOrderedStandardFiltrations Q Λ := by
  intro ν s hs
  refine ⟨⟨s, hs⟩, [], fun _ _ => le_rfl, fun _ _ => le_rfl, by simp,
    HasFiltration.single ?_⟩
  refine (Submodule.quotEquivOfEqBot _ ?_).symm
  rw [leftUpper_eq_bot_of_zero, Submodule.comap_bot, Submodule.ker_subtype]

variable {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "old" => Λ ∘ Fin.castSucc
local notation "Told" => TensorProductAlgebra k Q (old)

/-- The top layer of the filtration of `F_w S(N)` has the first factor weight of `N`, and all
other layers have strictly larger first factor weight. -/
theorem StdLayer.wordLayers_head (w : List I) {ν : Multiset I} (c : StdLayer Q Λ ν) :
    ∃ d rest, c.wordLayers Q Λ w = d :: rest ∧ d.θ = c.θ ∧
      ∀ e ∈ rest, c.θ ≤ e.θ ∧ e.θ ≠ c.θ := by
  induction w with
  | nil => exact ⟨c, [], rfl, rfl, by simp⟩
  | cons j w ih =>
    obtain ⟨d, rest, h, hd, hr⟩ := ih
    refine ⟨d.last Q Λ j, d.first Q Λ j :: rest.flatMap (StdLayer.blackIndLayers Q Λ j),
      by simp [StdLayer.wordLayers, h, StdLayer.blackIndLayers], hd, ?_⟩
    have hfirst : ∀ e : StdLayer Q Λ (wordWt w ν), c.θ ≤ e.θ →
        c.θ ≤ (e.first Q Λ j).θ ∧ (e.first Q Λ j).θ ≠ c.θ := fun e he => by
      refine ⟨he.trans (Multiset.le_add_left _ _), fun heq => ?_⟩
      have h₁ := Multiset.card_le_card he
      have h₂ := congrArg Multiset.card heq
      change Multiset.card ((Si j) + e.θ) = _ at h₂
      simp at h₂
      omega
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hfirst d (hd ▸ le_rfl)
    obtain ⟨e', he', he⟩ := List.mem_flatMap.1 he
    simp only [StdLayer.blackIndLayers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hr e' he'
    · exact hfirst e' (hr e' he').1

/-- The modules over `T^{λ'}` of the recursion of Proposition 5.20 that start from
`T^{λ'} e(s₀)`: the projectives `T^{λ'} e(t)` with `t` equivalent to `s₀`. -/
def OldGenCount {θ₀ : Multiset I} (s₀ : Seq (stendhalWeight ℓ θ₀)) :
    ∀ θ : Multiset I, ModuleCat.{0} (Told θ) → Prop :=
  fun θ X => ∃ (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t),
    Nonempty (X ≃ₗ[Told θ] oldProj Q Λ θ t ht) ∧ ∀ r i, blackCount t r i = blackCount s₀ r i

theorem OldGenCount.ind {θ₀ : Multiset I} (s₀ : Seq (stendhalWeight ℓ θ₀)) (j : I)
    (θ : Multiset I) (X : ModuleCat.{0} (Told θ)) (hX : OldGenCount Q Λ s₀ θ X) :
    OldGenCount Q Λ s₀ ((Si j) + θ) (oldIndModule Q Λ j X) := by
  obtain ⟨t, ht, ⟨g⟩, hc⟩ := hX
  exact ⟨_, _, ⟨(InductionAlong.Ind.congr g).trans (oldProjIndEquiv Q Λ j _ t ht)⟩,
    fun r i => (blackCount_appendBlackLoading j θ t r i).trans (hc r i)⟩

variable (hQ : KLRSymm Q)

/-- **The layers of Proposition 5.20, with black counts** (Webster, arXiv:1309.3796v2, proof
of Corollary 5.21): every layer of the filtration of `T^λ e(s₀, λ_{ℓ+1}, w)` by `F_w` is
`S(T^{λ'} e(t) ⊠ R^{λ_{ℓ+1}} e(u))` with `t` equivalent to `s₀`. -/
theorem exists_stdLayerModule_equiv_tensorLayer_count (w : List I) {θ : Multiset I}
    (s₀ : Seq (stendhalWeight ℓ (θ + 0))) (hs₀ : IsRedOrdered s₀) :
    ∀ c ∈ (redLayer Q Λ θ s₀ hs₀).wordLayers Q Λ w,
      ∃ (t : Seq (stendhalWeight ℓ c.θ)) (ht : IsRedOrdered t) (u : Seq c.β),
        (∀ r i, blackCount t r i = blackCount s₀ r i) ∧
        Nonempty (stdLayerModule Q Λ hQ c ≃ₗ[TensorProductAlgebra k Q Λ (wordWt w (θ + 0))]
          stdLayerModule Q Λ hQ
            (tensorLayer Q Λ c.h (oldProj Q Λ c.θ t ht) (cycProj Q Λ c.β u))) := by
  intro c hc
  have hbase : OldGenCount Q Λ s₀ θ (zeroRestrict Q Λ (redFactorModule Q Λ θ s₀ hs₀)) := by
    obtain ⟨t, ht, rfl, he⟩ := nonempty_zeroRestrict_redFactorModule_equiv Q Λ θ s₀ hs₀
    exact ⟨_, ht, he, fun r i => blackCount_cast _ _ r i⟩
  obtain ⟨X, Y, ⟨t, ht, ⟨f⟩, hcount⟩, hY, ⟨e⟩⟩ :=
    StdLayer.TensorForm.wordLayers (𝒳 := OldGenCount Q Λ s₀) (𝒴 := CycGen Q Λ)
      (fun j θ' X hX => OldGenCount.ind Q Λ s₀ j θ' X hX) (fun j _ Y hY => CycGen.ind j Y hY) w
      (c := redLayer Q Λ θ s₀ hs₀) (FactorModule.TensorForm.zero _ hbase CycGen.base) c hc
  obtain ⟨u, ⟨g⟩⟩ := hY.exists_equiv
  obtain ⟨θ', β', h, M⟩ := c
  exact ⟨t, ht, u, hcount, ⟨stdLayerEquiv Q Λ hQ h (e.trans (tensorFactorCongr Q Λ f g))⟩⟩

omit [Field k] in
theorem blackCount_twoPieceLabel_castSucc {θ β ν : Multiset I} (h : θ + β = ν) (u : Seq β)
    (d : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}) (r : Fin ℓ) (i : I) :
    blackCount (twoPieceLabel h u d).1 r.castSucc i = blackCount d.1 r i := by
  rw [twoPieceLabel, blackCount_cast, blackCount_twoPieceLoading_castSucc]

omit [Field k] in
theorem blackCount_twoPieceLabel_last {θ β ν : Multiset I} (h : θ + β = ν) (u : Seq β)
    (d : {t : Seq (stendhalWeight ℓ θ) // IsRedOrdered t}) (i : I) :
    blackCount (twoPieceLabel h u d).1 (Fin.last ℓ) i = θ.count i := by
  rw [twoPieceLabel, blackCount_cast, blackCount_twoPieceLoading_last]

variable {C : QuantumGroup.CartanDatum I}

/-- **Induction step** (Webster, arXiv:1309.3796v2, proof of Corollary 5.21). Route hypothesis:
`AllFiniteDeltaInjective` (Proposition 5.5, `F`-part). -/
theorem hasOrderedStandardFiltrations_succ (hR : IsRouquierQ C Q)
    (hall : AllFiniteDeltaInjective Q Λ hQ) (hold : HasOrderedStandardFiltrations Q (old)) :
    HasOrderedStandardFiltrations Q Λ := by
  intro ν s hs
  obtain ⟨θ, w, s₀, hs₀, h, hc⟩ := exists_blackWordLoading_appendRed ν.card ν rfl s hs
  subst h
  rw [Seq.cast_rfl] at hc
  subst hc
  have hF : HasFiltration (stdLayerModule Q Λ hQ) ((redLayer Q Λ θ s₀ hs₀).wordLayers Q Λ w)
      (ModuleCat.of _ (lIdeal (seqIdem Q Λ _ hs))) :=
    hasFiltration_loadingProj_of_finite hR hall w s₀ hs₀
  -- the black counts of `s = (s₀, λ_{ℓ+1}, w)`
  have hsc : ∀ r i, blackCount (blackWordLoading w (appendRedLoading s₀)) r.castSucc i =
      blackCount s₀ r i := fun r i => by
    rw [blackCount_blackWordLoading, blackCount_appendRedLoading_castSucc]
  have hsl : ∀ i, blackCount (blackWordLoading w (appendRedLoading s₀)) (Fin.last ℓ) i =
      θ.count i := fun i => by
    rw [blackCount_blackWordLoading, blackCount_appendRedLoading_last, add_zero]
  -- the refinement of each layer
  have key : ∀ c ∈ (redLayer Q Λ θ s₀ hs₀).wordLayers Q Λ w,
      ∃ (t : Seq (stendhalWeight ℓ c.θ)) (x : {t' : Seq (stendhalWeight ℓ c.θ) // IsRedOrdered t'})
        (m' : List {t' : Seq (stendhalWeight ℓ c.θ) // IsRedOrdered t'}) (u : Seq c.β),
        (∀ r i, blackCount t r i = blackCount s₀ r i) ∧ StendhalLE t x.1 ∧ StendhalLE x.1 t ∧
        (∀ y ∈ m', StendhalLT t y.1) ∧
        HasFiltration (stdModule Q Λ _) ((x :: m').map (twoPieceLabel c.h u))
          (stdLayerModule Q Λ hQ c) := by
    intro c hc
    obtain ⟨t, ht, u, hcount, ⟨e⟩⟩ :=
      exists_stdLayerModule_equiv_tensorLayer_count Q Λ hQ w s₀ hs₀ c hc
    obtain ⟨x, m', hle₁, hle₂, hlt, hm'⟩ := hold c.θ t ht
    have h₁ := hasFiltration_tensorLayer Q Λ hQ c.h (cycProj Q Λ c.β u)
      (X := oldProj Q Λ c.θ t ht) hm'
    have h₂ : HasFiltration (fun d => stdModule Q Λ _ (twoPieceLabel c.h u d)) (x :: m')
        (stdLayerModule Q Λ hQ (tensorLayer Q Λ c.h (oldProj Q Λ c.θ t ht)
          (cycProj Q Λ c.β u))) :=
      h₁.mono fun d => nonempty_stdLayerModule_twoPiece_equiv Q Λ hQ c.h d.2 u
    exact ⟨t, x, m', u, hcount, hle₁, hle₂, hlt,
      (HasFiltration.relabel (L := stdModule Q Λ _) (twoPieceLabel c.h u) h₂).of_equiv e.symm⟩
  -- comparison of a label with `s`
  have hcmp : ∀ (c : StdLayer Q Λ (wordWt w (θ + 0))) (u : Seq c.β)
      (y : {t' : Seq (stendhalWeight ℓ c.θ) // IsRedOrdered t'}),
      (StendhalLE (blackWordLoading w (appendRedLoading s₀)) (twoPieceLabel c.h u y).1 ↔
        (∀ r i, blackCount s₀ r i ≤ blackCount y.1 r i) ∧ θ ≤ c.θ) ∧
      (StendhalLE (twoPieceLabel c.h u y).1 (blackWordLoading w (appendRedLoading s₀)) ↔
        (∀ r i, blackCount y.1 r i ≤ blackCount s₀ r i) ∧ c.θ ≤ θ) := fun c u y => by
    simp only [stendhalLE_iff_castSucc_last, hsc, hsl, blackCount_twoPieceLabel_castSucc,
      blackCount_twoPieceLabel_last, ← Multiset.le_iff_count]
    exact ⟨trivial, trivial⟩
  have hlab : ∀ (c : StdLayer Q Λ (wordWt w (θ + 0))) (u : Seq c.β)
      (t : Seq (stendhalWeight ℓ c.θ)) (y : {t' : Seq (stendhalWeight ℓ c.θ) // IsRedOrdered t'}),
      (∀ r i, blackCount t r i = blackCount s₀ r i) → StendhalLE t y.1 → θ ≤ c.θ →
        StendhalLE (blackWordLoading w (appendRedLoading s₀)) (twoPieceLabel c.h u y).1 :=
    fun c u t y hc hy hθ => (hcmp c u y).1.2 ⟨fun r i => (hc r i).symm.le.trans (hy r i), hθ⟩
  have hrθ : (redLayer Q Λ θ s₀ hs₀).θ = θ := rfl
  obtain ⟨d, rest, hdr, hdθ, hrest⟩ := (redLayer Q Λ θ s₀ hs₀).wordLayers_head Q Λ w
  rw [hrθ] at hdθ hrest
  rw [hdr] at hF
  obtain ⟨t, x, m', u, hcount, hle₁, hle₂, hlt, hd⟩ :=
    key d (hdr ▸ List.mem_cons_self)
  rw [List.map_cons] at hd
  obtain ⟨l, hl, hP⟩ := hF.exists_refine_head
    (fun y => StendhalLT (blackWordLoading w (appendRedLoading s₀)) y.1) hd (fun c hc => by
      obtain ⟨t', x', m'', u', hcount', hle₁', -, hlt', hc'⟩ :=
        key c (hdr ▸ List.mem_cons_of_mem _ hc)
      refine ⟨_, hc', fun y hy => ?_⟩
      obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
      have hty : StendhalLE t' y'.1 := by
        rcases List.mem_cons.1 hy' with rfl | hy'
        exacts [hle₁', (hlt' y' hy').1]
      refine ⟨hlab c u' t' y' hcount' hty (hrest c hc).1, fun hge => ?_⟩
      exact (hrest c hc).2 (le_antisymm ((hcmp c u' y').2.1 hge).2 (hrest c hc).1))
  refine ⟨twoPieceLabel d.h u x, m'.map (twoPieceLabel d.h u) ++ l,
    hlab d u t x hcount hle₁ hdθ.ge,
    (hcmp d u x).2.2 ⟨fun r i => (hle₂ r i).trans (hcount r i).le, hdθ.le⟩,
    fun y hy => ?_, hl⟩
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    refine ⟨hlab d u t y' hcount (hlt y' hy').1 hdθ.ge, fun hge => (hlt y' hy').2 ?_⟩
    exact fun r i => (((hcmp d u y').2.1 hge).1 r i).trans (hcount r i).symm.le
  · exact hP y hy

/-- **Ordered standard filtrations of projectives** (Webster, arXiv:1309.3796v2, proof of
Corollary 5.21): every `T^λ e(s)` has a standard filtration with top quotient `S_{s'}`, `s'`
equivalent to `s`, and all other subquotients `S_t` with `t > s`. Route hypothesis:
`AllFiniteDeltaInjective` (Proposition 5.5, `F`-part) at every number of red strands. -/
theorem hasOrderedStandardFiltrations (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ) :
    ∀ {n : ℕ} (Λ' : Fin n → I →₀ ℕ), HasOrderedStandardFiltrations Q Λ'
  | 0, Λ' => hasOrderedStandardFiltrations_zero Q Λ'
  | n + 1, Λ' => hasOrderedStandardFiltrations_succ Q Λ' hQ hR (hall n Λ')
      (hasOrderedStandardFiltrations hR hall (Λ' ∘ Fin.castSucc))

end Categorification.Stendhal
