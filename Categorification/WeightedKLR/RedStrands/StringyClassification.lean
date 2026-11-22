/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StringyLoading
import Categorification.WeightedKLR.RedStrands.LastRedStandardCut
import Categorification.WeightedKLR.RedStrands.EmptyTensor

/-!
# Stringy loadings classify the indecomposable projectives

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.3,
Proposition 5.17.

An indecomposable graded projective of `T^λ_ν` is recorded by the shift class `c` of its simple
top; its cover is a summand of `P_p = T^λ e(p)` exactly when `e(p)` acts nonzero on the top,
that is when `p ∈ loadSupp Λ c`. We prove, by induction on the number of red strands:

* every maximal loading of a class (for the refined order `LoadLT σ`) is stringy;
* each class has a unique maximal loading, and the maximal loading determines the class;
* every stringy loading is the maximal loading of some class.

The inductive step splits off the last red strand (`lastRedHeadEquiv`): a class is a pair of a
class for the first `ℓ` red strands and a class for the cyclotomic quotient `R^{λ_{ℓ+1}}`, and
its maximal loading is the two-piece loading of the maximal loading of the first factor and the
string-maximal sequence of the second (`HeadAtCut.isMaxLoad_factors`,
`HeadAtCut.isMaxLoad_of_factors`). The cyclotomic factor is classified by Khovanov–Lauda's
string parametrization (`CycKLR.nonempty_equiv_of_isStrMax`).

## Main results

* `maxLoadClassification`: the four statements above, for every `ℓ`, `λ` and `ν`.
* `existsUnique_isMaxLoad_of_isStringy`, `exists_loadLT_of_not_isStringy`: Proposition 5.17.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded GProj
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {D : QuantumGroup.CartanDatum I}
    {Λ : Fin (ℓ+1) → I →₀ ℕ} {G : GradingDatum (stendhalQ Q Λ)}

/-- A maximal loading of the head at the cut `u` is a two-piece loading at the cut `u`. -/
theorem HeadAtCut.exists_twoPiece_of_isMaxLoad (hQ : IsRouquierQ D Q) {σ : ℕ → I}
    {ν : Multiset I} {u : LastRedWeightSplit ν}
    {b : IndecClass (lastRedFactorGrading Λ ν G u)} {c : IndecClass (tensorProductGrade G ν)}
    (hc : HeadAtCut Λ ν G u b c) {p : Seq (stendhalWeight (ℓ + 1) ν)}
    (hp : IsMaxLoad σ Λ c p) :
    ∃ (t : Seq (stendhalWeight ℓ u.1.1)) (w : Seq u.1.2), IsRedOrdered t ∧
      Seq.cast (congrArg (stendhalWeight (ℓ + 1)) u.2) (twoPieceLoading _ _ t w) = p := by
  obtain ⟨⟨hpo, x, hx⟩, hmax⟩ := hp
  obtain ⟨θ, β, h, t, w, ht, rfl⟩ := exists_twoPieceLoading_eq hpo
  subst h
  have hu := hc.prefix_eq_of_maximal hQ ht w (x := x) hx fun q hq hlt y => by
    by_contra hy
    exact hmax q ⟨hq, y, hy⟩ (.inl hlt)
  rcases u with ⟨⟨θ', β'⟩, hu'⟩
  dsimp only at hu hu' ⊢
  subst hu
  obtain rfl := add_left_cancel hu'
  exact ⟨t, w, ht, rfl⟩

section Generic

variable {k' A : Type*} [Field k'] [Ring A] [Algebra k' A]
  {𝒜 : ℤ → Submodule k' A} [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- Shift classes with isomorphic ungraded tops are equal. -/
theorem IndecClass.eq_of_nonempty_linearEquiv [Module.Finite k' A] {b c : IndecClass 𝒜}
    (e : Nonempty (b.top ≃ₗ[A] c.top)) : b = c := by
  obtain ⟨e⟩ := e
  let := (IndecClass.isGradedSimple_top b).nontrivial
  have hz : e.toLinearMap ≠ 0 := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : b.top)
    exact hx (e.injective ((LinearMap.congr_fun he _).trans e.map_zero.symm))
  obtain ⟨n, ⟨g⟩⟩ := IsGradedSimple.exists_gradedEquiv_shift_of_ne_zero
    (IndecClass.isGradedSimple_top b) (IndecClass.isGradedSimple_top c) hz
  exact (IndecClass.eq_of_gradedEquiv_top_shift (a := 0) (a' := n)
    (by simpa only [shift_zero] using g)).1

end Generic

variable (Q) in
/-- The idempotents of the red-ordered loadings sum to one in `T^λ_ν`. -/
theorem sum_seqIdem {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν : Multiset I) :
    ∑ s : {s : Seq (stendhalWeight ℓ' ν) // IsRedOrdered s}, seqIdem Q Λ' s.1 s.2 = 1 := by
  classical
  have h : (∑ s : {s : Seq (stendhalWeight ℓ' ν) // IsRedOrdered s}, StendhalAlgebra.e s.1 s.2 :
      StendhalAlgebra k Q Λ' ν) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : {s : Seq (stendhalWeight ℓ' ν) // IsRedOrdered s},
      StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' ν
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  simpa only [map_sum, map_one] using congrArg (TensorProductAlgebra.mk Q Λ' ν) h

/-- Every shift class has a maximal loading. -/
theorem exists_isMaxLoad (σ : ℕ → I) {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) {ν : Multiset I}
    {G' : GradingDatum (stendhalQ Q Λ')} (c : IndecClass (tensorProductGrade G' ν)) :
    ∃ p, IsMaxLoad σ Λ' c p := by
  classical
  have hne : (loadSupp Λ' c).Nonempty := by
    let := (IndecClass.isGradedSimple_top c).nontrivial
    obtain ⟨x, hx⟩ := exists_ne (0 : c.top)
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hx
    rw [← one_smul (TensorProductAlgebra k Q Λ' ν) x, ← sum_seqIdem Q Λ' ν, Finset.sum_smul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_contra hs
    exact (Set.eq_empty_iff_forall_notMem.1 h) s.1 ⟨s.2, x, hs⟩
  let r : Seq (stendhalWeight ℓ' ν) → Seq (stendhalWeight ℓ' ν) → Prop :=
    fun p q => LoadLT σ q p
  have : IsTrans _ r := ⟨fun _ _ _ h₁ h₂ => loadLT_trans h₂ h₁⟩
  have : Std.Irrefl r := ⟨fun p => loadLT_irrefl σ p⟩
  obtain ⟨p, hp, hmax⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min _ hne
  exact ⟨p, hp, hmax⟩

theorem LoadLT.le {μ : Multiset (I ⊕ Fin ℓ)} {σ : ℕ → I} {p q : Seq μ} (h : LoadLT σ p q) :
    StendhalLE p q := by
  rcases h with h | h
  exacts [h.1, h.1]

local notation "Xp" => fun (μ : I →₀ ℕ) (i : I) => (Polynomial.X : Polynomial k) ^ μ i

/-- At its own cut, a maximal two-piece loading of a head restricts to a maximal loading of the
first factor class and to the string-maximal sequence of the second factor class. -/
theorem HeadAtCut.isMaxLoad_factors (hQ : IsRouquierQ D Q) {σ : ℕ → I} {θ β : Multiset I}
    {b : IndecClass (lastRedFactorGrading Λ (θ + β) G (twoPieceCut θ β))}
    {c : IndecClass (tensorProductGrade G (θ + β))}
    (hc : HeadAtCut Λ (θ + β) G (twoPieceCut θ β) b c) {t : Seq (stendhalWeight ℓ θ)}
    (ht : IsRedOrdered t) {w : Seq β} (hp : IsMaxLoad σ Λ c (twoPieceLoading θ β t w)) :
    IsMaxLoad σ (Λ ∘ Fin.castSucc) (lastRedFactorEquiv Λ (θ + β) G hQ (twoPieceCut θ β) b).1 t ∧
      CycKLR.IsStrMax Q (Xp (Λ (Fin.last ℓ))) β
        (lastRedFactorEquiv Λ (θ + β) G hQ (twoPieceCut θ β) b).2.top σ w := by
  have key := fun (t' : Seq (stendhalWeight ℓ θ)) (ht' : IsRedOrdered t') (w' : Seq β) =>
    hc.twoPiece_smul_ne_zero_iff_factors hQ ht' w'
  obtain ⟨⟨_, x, hx⟩, hmax⟩ := hp
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := (key t ht w).1 ⟨x, hx⟩
  refine ⟨⟨⟨ht, m, hm⟩, ?_⟩, ⟨n, hn⟩, ?_⟩
  · rintro q ⟨hq, m', hm'⟩ hlt
    exact hmax _ ⟨isRedOrdered_twoPieceLoading hq w, (key q hq w).2 ⟨⟨m', hm'⟩, ⟨n, hn⟩⟩⟩
      (loadLT_twoPiece_left hlt w)
  · rintro w' ⟨n', hn'⟩
    refine not_lt.1 fun hlt => hmax _ ⟨isRedOrdered_twoPieceLoading ht w',
      (key t ht w').2 ⟨⟨m, hm⟩, ⟨n', hn'⟩⟩⟩ (loadLT_twoPiece_right t hlt)

/-- Conversely, a maximal loading of the first factor class followed by the string-maximal
sequence of the second factor class is a maximal loading of the head. -/
theorem HeadAtCut.isMaxLoad_of_factors (hQ : IsRouquierQ D Q) {σ : ℕ → I} {ν : Multiset I}
    {u : LastRedWeightSplit ν} {b : IndecClass (lastRedFactorGrading Λ ν G u)}
    {c : IndecClass (tensorProductGrade G ν)} (hc : HeadAtCut Λ ν G u b c)
    {t : Seq (stendhalWeight ℓ u.1.1)} {w : Seq u.1.2}
    (ht : IsMaxLoad σ (Λ ∘ Fin.castSucc) (lastRedFactorEquiv Λ ν G hQ u b).1 t)
    (hw : CycKLR.IsStrMax Q (Xp (Λ (Fin.last ℓ))) u.1.2
      (lastRedFactorEquiv Λ ν G hQ u b).2.top σ w) :
    IsMaxLoad σ Λ c (Seq.cast (congrArg (stendhalWeight (ℓ + 1)) u.2)
      (twoPieceLoading _ _ t w)) := by
  obtain ⟨⟨hto, m, hm⟩, htmax⟩ := ht
  refine ⟨?_, ?_⟩
  · rcases u with ⟨⟨θ, β⟩, rfl⟩
    exact ⟨isRedOrdered_twoPieceLoading hto w,
      (hc.twoPiece_smul_ne_zero_iff_factors hQ hto w).2 ⟨⟨m, hm⟩, hw.1⟩⟩
  rintro q ⟨hq, y, hy⟩ hlt
  obtain ⟨θ', β', h, t', w', ht', rfl⟩ := exists_twoPieceLoading_eq hq
  subst h
  have hle : θ' ≤ u.1.1 := hc.prefix_le_of_twoPiece Λ G ht' w' hy
  have hge : u.1.1 ≤ θ' := by
    rw [Multiset.le_iff_count]
    intro i
    have := hlt.le (Fin.last ℓ) i
    rw [blackCount_cast, blackCount_twoPieceLoading_last, blackCount_cast,
      blackCount_twoPieceLoading_last] at this
    exact this
  have hu := eq_twoPieceCut (le_antisymm hle hge).symm
  subst hu
  change LoadLT σ (twoPieceLoading θ' β' t w) (twoPieceLoading θ' β' t' w') at hlt
  change seqIdem Q Λ (twoPieceLoading θ' β' t' w') (isRedOrdered_twoPieceLoading ht' w') • y
    ≠ 0 at hy
  have key := fun (t'' : Seq (stendhalWeight ℓ θ')) (ht'' : IsRedOrdered t'') (w'' : Seq β') =>
    hc.twoPiece_smul_ne_zero_iff_factors hQ ht'' w''
  obtain ⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩ := (key t' ht' w').1 ⟨y, hy⟩
  rcases loadLT_twoPiece_cases hlt with h | ⟨-, -, -, h⟩
  · exact htmax t' ⟨ht', m', hm'⟩ h
  · exact not_lt.2 (hw.2 w' ⟨n', hn'⟩) h

theorem CycKLR.supp_eq_of_equiv {a : I → Polynomial k} {β : Multiset I}
    {M M' : Type*} [AddCommGroup M] [Module (CycKLR k Q a β) M]
    [AddCommGroup M'] [Module (CycKLR k Q a β) M'] (f : M ≃ₗ[CycKLR k Q a β] M') :
    CycKLR.supp Q a β M = CycKLR.supp Q a β M' := by
  ext s
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨f m, by rw [← map_smul]; exact (map_ne_zero_iff _ f.injective).2 hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨f.symm m, by rw [← map_smul]; exact (map_ne_zero_iff _ f.symm.injective).2 hm⟩

omit [DecidableEq I] in
/-- Rouquier parameters are nonzero off the diagonal. -/
theorem _root_.Categorification.KLR.IsRouquierQ.ne_zero (hQ : IsRouquierQ D Q) (i j : I)
    (hij : i ≠ j) : Q i j ≠ 0 := by
  intro hz
  have := hQ.unit_coeff i j hij
  simp [hz] at this

variable (k Q) in
/-- The conclusion of Proposition 5.17 for one weight: maximal loadings of shift classes are
stringy, unique, determine the class, and every stringy loading is maximal for a class. -/
structure MaxLoadClassification (σ : ℕ → I) {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ) (ν : Multiset I)
    (G' : GradingDatum (stendhalQ Q Λ')) : Prop where
  stringy : ∀ (c : IndecClass (tensorProductGrade G' ν)) p, IsMaxLoad σ Λ' c p →
    IsStringy k Q σ ℓ' Λ' ν p
  unique : ∀ (c : IndecClass (tensorProductGrade G' ν)) p p', IsMaxLoad σ Λ' c p →
    IsMaxLoad σ Λ' c p' → p = p'
  injective : ∀ (c c' : IndecClass (tensorProductGrade G' ν)) p, IsMaxLoad σ Λ' c p →
    IsMaxLoad σ Λ' c' p → c = c'
  surjective : ∀ p, IsStringy k Q σ ℓ' Λ' ν p →
    ∃ c : IndecClass (tensorProductGrade G' ν), IsMaxLoad σ Λ' c p

/-- The inductive step of Proposition 5.17: the classification for `ℓ` red strands gives the
classification for `ℓ + 1`. -/
theorem maxLoadClassification_succ (hQ : IsRouquierQ D Q) {σ : ℕ → I}
    (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ))
    (ih : ∀ θ, MaxLoadClassification k Q σ (Λ ∘ Fin.castSucc) θ (restrictRedGrading Q Λ G))
    (ν : Multiset I) : MaxLoadClassification k Q σ Λ ν G := by
  have induce := fun ν' => nonempty_lastRedInducedCut Λ ν' G hQ.klrSymm
  have hd : ∀ {ν'} (c : IndecClass (tensorProductGrade G ν')),
      ∃ u b, HeadAtCut Λ ν' G u b c := fun {ν'} c => by
    obtain ⟨⟨u, x⟩, rfl⟩ := (lastRedHeadEquiv Λ ν' G hQ (induce ν')).surjective c
    exact ⟨u, _, lastRedHeadEquiv_headAtCut Λ ν' G hQ (induce ν') u x⟩
  have hfin := fun β => lastRedFinal_finite hQ (Λ (Fin.last ℓ)) β
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c p hp
    obtain ⟨u, b, hc⟩ := hd c
    obtain ⟨t, w, ht, rfl⟩ := hc.exists_twoPiece_of_isMaxLoad hQ hp
    rcases u with ⟨⟨θ, β⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hc.isMaxLoad_factors hQ ht (w := w) hp
    let := hfin β
    let b₂ := (lastRedFactorEquiv Λ (θ + β) G hQ (twoPieceCut θ β) b).2
    let := (IndecClass.isGradedSimple_top b₂).finiteDimensional (⊥ : Submodule k _)
      (fun a ha m => by rw [(Submodule.mem_bot k).mp ha, zero_smul])
    let := (IndecClass.isGradedSimple_top b₂).isSimpleModule
    exact ⟨θ, β, rfl, t, w, ht, rfl, (ih θ).stringy _ _ h1, b₂.top.carrier, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h2⟩
  · intro c p p' hp hp'
    obtain ⟨u, b, hc⟩ := hd c
    obtain ⟨t, w, ht, rfl⟩ := hc.exists_twoPiece_of_isMaxLoad hQ hp
    obtain ⟨t', w', ht', rfl⟩ := hc.exists_twoPiece_of_isMaxLoad hQ hp'
    rcases u with ⟨⟨θ, β⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hc.isMaxLoad_factors hQ ht (w := w) hp
    obtain ⟨h1', h2'⟩ := hc.isMaxLoad_factors hQ ht' (w := w') hp'
    obtain rfl := (ih θ).unique _ _ _ h1 h1'
    have hk := le_antisymm (h2'.2 w h2.1) (h2.2 w' h2'.1)
    obtain rfl : w = w' := Subtype.ext (List.ofFn_injective (strKey_injective hσ hk))
    rfl
  · intro c c' p hp hp'
    obtain ⟨⟨u, x⟩, rfl⟩ := (lastRedHeadEquiv Λ ν G hQ (induce ν)).surjective c
    obtain ⟨⟨u', x'⟩, rfl⟩ := (lastRedHeadEquiv Λ ν G hQ (induce ν)).surjective c'
    have hc := lastRedHeadEquiv_headAtCut Λ ν G hQ (induce ν) u x
    have hc' := lastRedHeadEquiv_headAtCut Λ ν G hQ (induce ν) u' x'
    obtain ⟨t, w, ht, rfl⟩ := hc.exists_twoPiece_of_isMaxLoad hQ hp
    obtain ⟨t', w', ht', he⟩ := hc'.exists_twoPiece_of_isMaxLoad hQ hp'
    have h11 : u.1.1 = u'.1.1 := Multiset.ext.2 fun i => by
      have := congrArg (fun q => blackCount q (Fin.last ℓ) i) he
      simp only [blackCount_cast, blackCount_twoPieceLoading_last] at this
      exact this.symm
    have huu : u = u' := by
      apply Subtype.ext
      apply Prod.ext h11
      exact add_left_cancel (show u.1.1 + u.1.2 = u.1.1 + u'.1.2 from u.2.trans (h11 ▸ u'.2).symm)
    subst huu
    rcases u with ⟨⟨θ, β⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hc.isMaxLoad_factors hQ ht (w := w) hp
    obtain ⟨h1', h2'⟩ := hc'.isMaxLoad_factors hQ ht (w := w) hp'
    rw [Equiv.apply_symm_apply] at h1 h2 h1' h2'
    have e1 := (ih θ).injective _ _ _ h1 h1'
    let := hfin β
    let := HasGdim.of_finiteDimensional
      (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
    let fd := fun b : IndecClass (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β) =>
      (IndecClass.isGradedSimple_top b).finiteDimensional (⊥ : Submodule k _)
        (fun a ha m => by rw [(Submodule.mem_bot k).mp ha, zero_smul])
    let := fd x.2
    let := fd x'.2
    let := (IndecClass.isGradedSimple_top x.2).isSimpleModule
    let := (IndecClass.isGradedSimple_top x'.2).isSimpleModule
    have e2 := IndecClass.eq_of_nonempty_linearEquiv
      (CycKLR.nonempty_equiv_of_isStrMax Q _ β hQ.klrSymm
      hQ.ne_zero (cycKLR_x_isNilpotent hQ _ β) hσ _ _ h2 h2')
    have : x = x' := Prod.ext e1 e2
    subst this
    rfl
  · rintro p ⟨θ, β, h, t, w, ht, hp, hst, M, _, _, _, _, _, _, hw⟩
    subst h hp
    obtain ⟨c₁, hc₁⟩ := (ih θ).surjective t hst
    let := hfin β
    let := HasGdim.of_finiteDimensional
      (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
    obtain ⟨c₂, ⟨f⟩⟩ := exists_indecClass_of_simple
      (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β) M
    have hw' : CycKLR.IsStrMax Q (Xp (Λ (Fin.last ℓ))) β c₂.top σ w := by
      rw [CycKLR.IsStrMax, ← CycKLR.supp_eq_of_equiv f]
      exact hw
    refine ⟨_, (lastRedHeadEquiv_headAtCut Λ (θ + β) G hQ (induce _) (twoPieceCut θ β)
      (c₁, c₂)).isMaxLoad_of_factors hQ ?_ ?_⟩
    · rw [Equiv.apply_symm_apply]
      exact hc₁
    · rw [Equiv.apply_symm_apply]
      exact hw'


omit [DecidableEq I] in
theorem Seq.subsingleton_of_card_eq_zero {μ : Multiset I} (h : Multiset.card μ = 0) :
    Subsingleton (Seq μ) :=
  ⟨fun _ _ => Subtype.ext (funext fun i => ((h ▸ i : Fin 0)).elim0)⟩

/-- With no red strands, a nonzero black weight gives the zero algebra, so no shift class has a
loading; with no black strands there is one class and one loading. -/
theorem maxLoadClassification_zero (hQ : IsRouquierQ D Q) (σ : ℕ → I)
    (Λ : Fin 0 → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I) :
    MaxLoadClassification k Q σ Λ ν G := by
  obtain rfl : Λ = Fin.elim0 := Subsingleton.elim _ _
  have hν : ∀ (c : IndecClass (tensorProductGrade G ν)) p, IsMaxLoad σ Fin.elim0 c p → ν = 0 := by
    intro c p hp
    by_contra hν
    let := subsingleton_emptyTensorAlgebra (k := k) Q hν
    obtain ⟨_, x, hx⟩ := hp.1
    exact hx (Module.eq_zero_of_zero_eq_one (x := _)
      (Subsingleton.elim (0 : TensorProductAlgebra k Q Fin.elim0 ν) 1))
  have hseq : ν = 0 → Subsingleton (Seq (stendhalWeight 0 ν)) := by
    rintro rfl
    exact Seq.subsingleton_of_card_eq_zero (by simp [stendhalWeight])
  have hcls : ν = 0 → Subsingleton (IndecClass (tensorProductGrade G ν)) ∧
      Nonempty (IndecClass (tensorProductGrade G ν)) := by
    rintro rfl
    let := tensorProductAlgebra_finite (Fin.elim0 : Fin 0 → I →₀ ℕ) (0 : Multiset I) hQ
    let := HasGdim.of_finiteDimensional (tensorProductGrade G (0 : Multiset I))
    let b := (K0.indecBasis (tensorProductGrade G (0 : Multiset I))).map
      (tensorProductVacuumK0Equiv G)
    have h1 := b.mk_eq_rank
    rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at h1
    exact ⟨Cardinal.le_one_iff_subsingleton.1 h1.le, b.index_nonempty⟩
  refine ⟨fun c p hp => hν c p hp, ?_, ?_, ?_⟩
  · intro c p p' hp _
    exact (hseq (hν c p hp)).elim _ _
  · intro c c' p hp _
    exact (hcls (hν c p hp)).1.elim _ _
  · intro p hp
    obtain ⟨c⟩ := (hcls hp).2
    obtain ⟨p', hp'⟩ := exists_isMaxLoad σ Fin.elim0 c
    obtain rfl := (hseq hp).elim p p'
    exact ⟨c, hp'⟩

/-- **Webster, arXiv:1309.3796v2, Proposition 5.17**, by induction on the number of red
strands. -/
theorem maxLoadClassification (hQ : IsRouquierQ D Q) {σ : ℕ → I}
    (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) :
    ∀ {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (G : GradingDatum (stendhalQ Q Λ)) (ν : Multiset I),
      MaxLoadClassification k Q σ Λ ν G
  | 0, Λ, G, ν => maxLoadClassification_zero hQ σ Λ G ν
  | _ + 1, Λ, G, ν => maxLoadClassification_succ hQ hσ Λ G
      (fun θ => maxLoadClassification hQ hσ (Λ ∘ Fin.castSucc) _ θ) ν


/-- **Webster, arXiv:1309.3796v2, Proposition 5.17.** Index the indecomposable graded
projectives of `T^λ_ν` by the shift classes `c` of their simple tops `L_c`; the projective
cover of `L_c` is a summand of `P_p = T^λ e(p)` exactly when `e(p) L_c ≠ 0`, that is when
`p ∈ loadSupp Λ c`. Then:

* for each stringy loading `p` there is exactly one class whose cover appears in `P_p` and in
  no `P_q` with `q` above `p` (the refined loading order `LoadLT σ`);
* for a loading `p` that is not stringy, every class whose cover appears in `P_p` also appears
  in some `P_q` with `q` above `p`.

The colour sequence `σ` must take every value infinitely often; it fixes the string
parametrization of the black blocks (Khovanov–Lauda's Kashiwara operators). -/
theorem existsUnique_isMaxLoad_of_isStringy (hQ : IsRouquierQ D Q) {σ : ℕ → I}
    (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ)
    (G' : GradingDatum (stendhalQ Q Λ')) {ν : Multiset I} {p : Seq (stendhalWeight ℓ' ν)}
    (hp : IsStringy k Q σ ℓ' Λ' ν p) :
    ∃! c : IndecClass (tensorProductGrade G' ν), IsMaxLoad σ Λ' c p := by
  have h := maxLoadClassification hQ hσ Λ' G' ν
  obtain ⟨c, hc⟩ := h.surjective p hp
  exact ⟨c, hc, fun c' hc' => h.injective _ _ _ hc' hc⟩

/-- **Webster, arXiv:1309.3796v2, Proposition 5.17**, non-stringy case: if `p` is not stringy,
every class whose cover is a summand of `P_p` has a cover summand of some `P_q` with `q` above
`p`. -/
theorem exists_loadLT_of_not_isStringy (hQ : IsRouquierQ D Q) {σ : ℕ → I}
    (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) {ℓ' : ℕ} (Λ' : Fin ℓ' → I →₀ ℕ)
    (G' : GradingDatum (stendhalQ Q Λ')) {ν : Multiset I} {p : Seq (stendhalWeight ℓ' ν)}
    (hp : ¬ IsStringy k Q σ ℓ' Λ' ν p) (c : IndecClass (tensorProductGrade G' ν))
    (hc : p ∈ loadSupp Λ' c) : ∃ q ∈ loadSupp Λ' c, LoadLT σ p q := by
  by_contra! h
  exact hp ((maxLoadClassification hQ hσ Λ' G' ν).stringy c p ⟨hc, fun q hq => h q hq⟩)

end Categorification.Stendhal
