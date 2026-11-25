/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.KLR.DividedPowerIdempotents
import Categorification.TypeA.WeakOrder
import Categorification.TypeA.SwapConnected

/-!
# The one-black interior column in Webster's (6.21)

For an adjacent red exchange, the balanced kernel inclusion with one black strand
reduces to the unique bottom loading in which the black lies between the exchanged
reds. Every other bottom loading has consecutive exchanged strands and uses the
existing consecutive-red injection.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

omit [DecidableEq I] in
private theorem redWord_sadj_swap_consecutive
    {s : Seq μ} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (ho : redWord s = L ++ a :: b :: M)
    (j : ℕ) (hj : j + 1 < n)
    (ha : s.lbl ⟨j, by omega⟩ = .inr a)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inr b) :
    redWord (sadj n j • s) = L ++ b :: a :: M := by
  let p : Fin n := ⟨j, by omega⟩
  let q : Fin n := ⟨j + 1, hj⟩
  have hone : invSet n (1 : Perm (Fin n)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    rintro ⟨x, y⟩ hxy
    have h := mem_invSet_pair.mp hxy
    exact lt_asymm h.1 h.2
  have hset : invSet n (sadj n j) = {(p, q)} := by
    have hlt : (1 : Perm (Fin n))⁻¹ p < (1 : Perm (Fin n))⁻¹ q := by
      simpa only [inv_one, Perm.one_apply] using (show p < q from Nat.lt_succ_self j)
    simpa [hone, p, q] using invSet_sadj_mul_of_lt hj (w := 1) hlt
  apply (redWord_smul_eq_swap_iff ho ha hb (sadj n j)).2
  intro x y _ _ hxy
  calc
    sadj n j y < sadj n j x ↔ (x, y) ∈ invSet n (sadj n j) :=
      (mem_invSet_pair.trans (and_iff_right hxy)).symm
    _ ↔ x = p ∧ y = q := by rw [hset, Finset.mem_singleton, Prod.mk.injEq]

/-- A one-black loading has its black strand strictly between the specified red cuts. -/
def OneBlackBetween (s : Seq μ) (b a : Fin ℓ) : Prop :=
  ∃ p x q : Fin n, s.lbl p = .inr b ∧ s.lbl x = .inl i ∧ s.lbl q = .inr a ∧ p < x ∧ x < q

omit [DecidableEq I] in
private theorem consecutive_reds_or_oneBlack_between
    {s : Seq μ} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ b :: a :: M) :
    (∃ j : ℕ, ∃ hj : j + 1 < n, ∃ u : Seq μ, redWord u = L ++ a :: b :: M ∧
      u.lbl ⟨j, by omega⟩ = .inr a ∧ u.lbl ⟨j + 1, hj⟩ = .inr b ∧ sadj n j • u = s) ∨
      OneBlackBetween (i := i) s b a := by
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr s b
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr s a
  have hpq : p < q := lt_of_redWord_eq_append hs hp hq
  let j := p.val
  by_cases hgap : j + 1 = q.val
  · have hj : j + 1 < n := hgap.symm ▸ q.isLt
    have hp' : s.lbl ⟨j, by omega⟩ = .inr b := hp
    have hq' : s.lbl ⟨j + 1, hj⟩ = .inr a := by
      rw [show (⟨j + 1, hj⟩ : Fin n) = q from Fin.ext hgap]
      exact hq
    let u := sadj n j • s
    have hu : redWord u = L ++ a :: b :: M :=
      redWord_sadj_swap_consecutive hs j hj hp' hq'
    have ua : u.lbl ⟨j, by omega⟩ = .inr a := by
      change (sadj n j • s).1 _ = _
      rw [sadj_smul_apply, sadj_apply_left hj]
      exact hq'
    have ub : u.lbl ⟨j + 1, hj⟩ = .inr b := by
      change (sadj n j • s).1 _ = _
      rw [sadj_smul_apply, sadj_apply_right hj]
      exact hp'
    have hus : sadj n j • u = s := sadj_smul_smul j s
    exact Or.inl ⟨j, hj, u, hu, ua, ub, hus⟩
  · have hlt : j + 1 < q.val := by change j < q.val at hpq; omega
    let x : Fin n := ⟨j + 1, hlt.trans q.isLt⟩
    have hpx : p < x := Nat.lt_succ_self j
    have hxq : x < q := hlt
    have hx : s.lbl x = .inl i := by
      cases hw : s.lbl x with
      | inr r => exact (not_lt_of_redWord_eq_append hs hp hq (by simp [hw]) hpx hxq).elim
      | inl c =>
        have hm := Seq.mem s x
        change s.lbl x ∈ μ at hm
        rw [hw] at hm
        have hc : c = i := by simpa [stendhalWeight] using hm
        rw [hc]
    exact Or.inr ⟨p, x, q, hp, hx, hq, hpx, hxq⟩


variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- Tests in bottom columns whose black lies between the exchanged reds. -/
def OneBlackInteriorColumnTests (t : Seq μ) (a b : Fin ℓ) (L M : List (Fin ℓ)) : Prop :=
  ∀ s : Seq μ, redWord s = L ++ b :: a :: M → OneBlackBetween (i := i) s b a →
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s)

/-- For one black, the consecutive-red criterion supplies every (6.21)
column except those with the black between the exchanged reds. -/
theorem blockKernelTensorInclusion_injective_of_oneBlack_between
    (hQ : KLRSymm Q) (t : Seq μ) (a b : Fin ℓ) (L M : List (Fin ℓ))
    (ht : redWord t = L ++ a :: b :: M)
    (hinterior : OneBlackInteriorColumnTests Q Λ t a b L M) :
    Function.Injective (blockKernelTensorInclusion Q Λ t a b (L ++ b :: a :: M)) := by
  have hcol (s : Seq μ) (hs : redWord s = L ++ b :: a :: M) :
      Function.Injective (blockKernelColumnInclusion Q Λ t a b s) := by
    have hcases := consecutive_reds_or_oneBlack_between (s := s) (a := a) (b := b) (L := L) (M := M) hs
    rcases hcases with ⟨j, hj, u, hu, ua, ub, hus⟩ | hinterior'
    · exact blockKernelColumnInclusion_injective (ν := (Singleton.singleton i : Multiset I))
        Q Λ t a b s hQ L M ht u (hu.trans ht.symm) j hj ua ub hus
    · exact hinterior s hs hinterior'
  exact blockKernelTensorInclusion_injective_of_columns (ν := (Singleton.singleton i : Multiset I))
    Q Λ t a b (L ++ b :: a :: M) hcol

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra Equiv

variable {I : Type} {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

private theorem interior_black_eq (s : Seq μ) {x y : Fin n} (hx : s.lbl x = .inl i)
    {c : I} (hy : s.lbl y = .inl c) : y = x := by
  have hm := Seq.mem s y
  change s.lbl y ∈ μ at hm
  rw [hy] at hm
  have hc : c = i := by simpa [stendhalWeight] using hm
  subst c
  have hn : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]
    simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
  exact Multiset.inj_on_of_nodup_map hn y (by simp) x (by simp) (hy.trans hx.symm)

private theorem red_before_interior_iff (s : Seq μ) {L M : List (Fin ℓ)} {a b : Fin ℓ}
    (hs : redWord s = L ++ b :: a :: M) {p x q y : Fin n}
    (hp : s.lbl p = .inr b) (hq : s.lbl q = .inr a)
    (hpx : p < x) (hxq : x < q) (hred : (s.lbl y).isRight) :
    y < x ↔ y ≤ p := by
  constructor
  · intro hy
    exact le_of_not_gt fun hpy =>
      not_lt_of_redWord_eq_append hs hp hq hred hpy (hy.trans hxq)
  · exact fun hy => hy.trans_lt hpx

/-- In a fixed red word, there is at most one loading whose unique black
lies between a specified adjacent pair. -/
theorem oneBlackBetween_eq {s t : Seq μ} {L M : List (Fin ℓ)} {a b : Fin ℓ}
    (hs : redWord s = L ++ b :: a :: M) (ht : redWord t = L ++ b :: a :: M)
    (hb₁ : OneBlackBetween (i := i) s b a) (hb₂ : OneBlackBetween (i := i) t b a) :
    s = t := by
  classical
  obtain ⟨p, x, q, hp, hx, hq, hpx, hxq⟩ := hb₁
  obtain ⟨p', x', q', hp', hx', hq', hpx', hxq'⟩ := hb₂
  obtain ⟨v, hv⟩ := Seq.exists_smul_eq s t
  have hlabel (j : Fin n) : t.lbl (v j) = s.lbl j := by
    have h := congrArg (fun z : Seq μ => z.lbl (v j)) hv
    exact (by simpa [lbl_smul] using h.symm)
  have hvp : v p = p' := lbl_inj_of_inr t b ((hlabel p).trans hp) hp'
  have hvx : v x = x' := interior_black_eq t hx' ((hlabel x).trans hx)
  have hord : redWord (v • s) = redWord ((1 : Perm (Fin n)) • s) := by rw [hv, one_smul, hs, ht]
  have hredOrd (y z : Fin n) {r r' : Fin ℓ}
      (hy : s.lbl y = .inr r) (hz : s.lbl z = .inr r') : v y < v z ↔ y < z :=
    (redWord_smul_eq_iff s v 1).1 hord _ _ _ _ hy hz
  have hredBlack (y : Fin n) {r : Fin ℓ} (hy : s.lbl y = .inr r) : y < x ↔ v y < v x := by
    have ho := hredOrd p y hp hy
    rw [hvp] at ho
    rw [hvx, red_before_interior_iff s hs hp hq hpx hxq (by simp [hy]),
      red_before_interior_iff t ht hp' hq' hpx' hxq' (by rw [hlabel, hy]; simp)]
    simpa only [not_lt] using (not_congr ho).symm
  have hm : StrictMono v := by
    intro y z hyz
    cases hy : s.lbl y with
    | inl c =>
      have ex := interior_black_eq s hx hy
      subst y
      cases hz : s.lbl z with
      | inl d =>
        have exz := interior_black_eq s hx hz
        subst z
        exact (lt_irrefl _ hyz).elim
      | inr r =>
        have hn : ¬ v z < v x := fun h => (lt_asymm hyz) ((hredBlack z hz).2 h)
        exact lt_of_le_of_ne (le_of_not_gt hn) fun h => (ne_of_lt hyz) (v.injective h)
    | inr r =>
      cases hz : s.lbl z with
      | inl c =>
        have exz := interior_black_eq s hx hz
        subst z
        exact (hredBlack y hy).1 hyz
      | inr r' => exact (hredOrd y z hy hz).2 hyz
  have he : v = 1 := by
    have e := Subsingleton.elim (hm.orderIsoOfSurjective v v.surjective) (OrderIso.refl _)
    ext j
    exact congrArg Fin.val (congrArg (fun φ : Fin n ≃o Fin n => φ j) e)
  rw [he, one_smul] at hv
  exact hv

private theorem redWord_ofList_eq {β : Multiset I}
    (w : List (I ⊕ Fin ℓ)) (h : (w : Multiset (I ⊕ Fin ℓ)) = stendhalWeight ℓ β) :
    redWord (Seq.ofList w h) = w.filterMap Sum.getRight? := by
  have hlen : Multiset.card (stendhalWeight ℓ β) = w.length := by rw [← h, Multiset.coe_card]
  have hw : List.ofFn (Seq.ofList w h).lbl = w := by
    rw [List.ofFn_congr hlen]
    conv_rhs => rw [← List.ofFn_getElem (xs := w)]
    rfl
  change List.filterMap (Sum.getRight? ∘ (Seq.ofList w h).lbl) (List.finRange (Multiset.card (stendhalWeight ℓ β))) = _
  rw [← List.filterMap_map, ← List.ofFn_eq_map, hw]

/-- The exchanged order has a loading with its unique black between the red pair. -/
theorem exists_oneBlackBetween_swapped_pair {t : Seq μ} {a b : Fin ℓ}
    {L M : List (Fin ℓ)} (ht : redWord t = L ++ a :: b :: M) :
    ∃ s : Seq μ, redWord s = L ++ b :: a :: M ∧ OneBlackBetween (i := i) s b a := by
  have hp : (L ++ a :: b :: M).Perm (List.finRange ℓ) := by
    rw [← ht]
    exact (List.perm_ext_iff_of_nodup (redWord_nodup _) (List.nodup_finRange _)).2
      fun r => by simp [mem_redWord]
  have hred : ((L ++ b :: a :: M : List (Fin ℓ)) : Multiset (Fin ℓ)) = Finset.univ.val := by
    change _ = ((List.ofFn (id : Fin ℓ → Fin ℓ) : List (Fin ℓ)) : Multiset (Fin ℓ))
    rw [List.ofFn_id]
    exact Quot.sound (((List.Perm.swap a b M).append_left L).trans hp)
  let w : List (I ⊕ Fin ℓ) := (L.map Sum.inr) ++ .inr b :: .inl i :: .inr a :: M.map Sum.inr
  have hweight : (w : Multiset (I ⊕ Fin ℓ)) = μ := by
    let pre : List (I ⊕ Fin ℓ) := L.map Sum.inr ++ [.inr b]
    let post : List (I ⊕ Fin ℓ) := .inr a :: M.map Sum.inr
    have hperm : w.Perm (Sum.inl i :: (L ++ b :: a :: M).map Sum.inr) := by
      simpa [pre, post, w, List.map_append, List.append_assoc] using
        (List.perm_middle (l₁ := pre) (l₂ := post) (a := Sum.inl i))
    have heq : (w : Multiset (I ⊕ Fin ℓ)) =
        ((Sum.inl i :: (L ++ b :: a :: M).map Sum.inr : List (I ⊕ Fin ℓ)) : Multiset (I ⊕ Fin ℓ)) :=
      Quot.sound hperm
    rw [heq]
    have e := congrArg (Multiset.map (Sum.inr : Fin ℓ → I ⊕ Fin ℓ)) hred
    change (Sum.inl i ::ₘ ↑((L ++ b :: a :: M).map (Sum.inr : Fin ℓ → I ⊕ Fin ℓ))) = μ
    simpa only [stendhalWeight, Multiset.map_singleton, Multiset.singleton_add, Multiset.map_coe] using
      congrArg (fun z : Multiset (I ⊕ Fin ℓ) => Sum.inl i ::ₘ z) e
  let s := Seq.ofList w hweight
  have hlen : Multiset.card μ = w.length := by rw [← hweight, Multiset.coe_card]
  have hq : L.length + 2 < Multiset.card μ := by simp [w] at hlen; omega
  have hpL : L.length < Multiset.card μ := by omega
  have hxL : L.length + 1 < Multiset.card μ := by omega
  refine ⟨s, ?_, ⟨⟨L.length, hpL⟩, ⟨L.length + 1, hxL⟩, ⟨L.length + 2, hq⟩, ?_, ?_, ?_,
    Nat.lt_succ_self _, Nat.lt_succ_self _⟩⟩
  · change redWord (Seq.ofList w hweight) = _
    rw [redWord_ofList_eq]
    simp [w, List.filterMap_cons, List.filterMap_map, Function.comp_def]
  · change (Seq.ofList w hweight).lbl _ = _
    rw [Seq.ofList_lbl]
    simp [w, List.getElem_append_right]
  · change (Seq.ofList w hweight).lbl _ = _
    rw [Seq.ofList_lbl]
    simp [w, List.getElem_append_right, show L.length + 1 - L.length = 1 by omega]
  · change (Seq.ofList w hweight).lbl _ = _
    rw [Seq.ofList_lbl]
    simp [w, List.getElem_append_right, show L.length + 2 - L.length = 2 by omega]

/-- The exchanged order has exactly one loading with a black between the reds. -/
theorem existsUnique_oneBlackBetween_swapped_pair {t : Seq μ} {a b : Fin ℓ}
    {L M : List (Fin ℓ)} (ht : redWord t = L ++ a :: b :: M) :
    ∃! s : Seq μ, redWord s = L ++ b :: a :: M ∧ OneBlackBetween (i := i) s b a := by
  obtain ⟨s, hs, hb⟩ := exists_oneBlackBetween_swapped_pair ht
  exact ⟨s, ⟨hs, hb⟩, fun _ h => oneBlackBetween_eq h.1 hs h.2 hb⟩

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- One bottom column suffices to check the whole one-black balanced inclusion. -/
theorem blockKernelTensorInclusion_injective_of_oneBlack_singleInterior
    (hQ : KLRSymm Q) (t : Seq μ) (a b : Fin ℓ) (L M : List (Fin ℓ))
    (ht : redWord t = L ++ a :: b :: M)
    (center : Seq μ) (hc : redWord center = L ++ b :: a :: M)
    (hb : OneBlackBetween (i := i) center b a)
    (hcol : Function.Injective (blockKernelColumnInclusion Q Λ t a b center)) :
    Function.Injective (blockKernelTensorInclusion Q Λ t a b (L ++ b :: a :: M)) := by
  have tests : OneBlackInteriorColumnTests Q Λ t a b L M := by
    intro s hs hi
    obtain rfl := oneBlackBetween_eq hs hc hi hb
    exact hcol
  exact blockKernelTensorInclusion_injective_of_oneBlack_between Q Λ hQ t a b L M ht tests

end Categorification.Stendhal.BraidedStendhalAlgebra
