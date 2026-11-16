/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Leading
import Categorification.WeightedKLR.Mackey.Support

/-!
# Dominance of the relabellings of a gallery

Triangularity input for the Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19, which follows Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18).

In the polynomial representation the gallery of a good word `w` from a rank-ordered full chamber
`C` to `B = C.flips w` is supported (`IsSupported`) in relabellings `x` that are *dominated* by
`B` (`IsDominated`): for every set `L` of strands closed to the left in `B` and every set `U`
of strands closed upwards in rank,

  `#(L ∩ x(U)) ≤ #(L ∩ U)`.

Along the gallery a step across a diagonal `x_l = x_r` with `l` left of `r` produces the
relabellings `x` and `s_{l r} x`; both stay dominated because the strands `l, r` are crossed
from rank order (`IsDominated.of_adjacent`). This is the Lean form of the statement that the
permutations occurring in the polynomial action of a KLR diagram lie below the permutation of
the diagram; the shuffle-type bound of the Mackey filtration is the case where `L` is the set of
strands ending in the left block and `U` the set of strands starting in the right block.

## Main definitions

* `FullChamber.StrandLt B s t`: the strands `s`, `t` have the same colour and `s` is left of
  `t` in `B`.
* `FullChamber.IsLeftClosed B L`: `L` contains every strand left of one of its strands.
* `IsRankUpper U`: `U` contains every strand of higher rank than one of its strands, of the
  same colour.
* `IsDominated B x`: `#(L ∩ x(U)) ≤ #(L ∩ U)` for all such `L`, `U`.

## Main results

* `isSupported_opList_isDominated`: the gallery of a good word from a rank-ordered full chamber
  is supported in the relabellings dominated by its end.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-! ### The order of the strands of one colour in a full chamber -/

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two distinct strands of the same colour are joined by a diagonal. -/
theorem Diag.exists_joins {s t : Strand ν} (hc : s.1 = t.1) (hne : s ≠ t) :
    ∃ d : Diag ν, d.Joins s t := by
  rcases lt_trichotomy s.2.val t.2.val with h | h | h
  · exact ⟨⟨(s, t), hc, h⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact absurd (Strand.ext_of hc h) hne
  · exact ⟨⟨(t, s), hc.symm, h⟩, Or.inr ⟨rfl, rfl⟩⟩

omit [DecidableEq I] in
/-- The order of two strands joined by a diagonal is read off the sign of the diagonal. -/
theorem lt_of_fullSigns_eq {p q : Strand ν → 𝕜} (hq : IsGeneric Γ q) {d : Diag ν}
    {s t : Strand ν} (hd : d.Joins s t)
    (he : fullSigns p (Sum.inr d : Hyp Γ ν) = fullSigns q (Sum.inr d : Hyp Γ ν))
    (hst : p s < p t) : q s < q t := by
  have hq0 : d.val q ≠ 0 := hq (.inr d)
  have he' : 0 < d.val p ↔ 0 < d.val q := by
    by_cases h1 : 0 < d.val p <;> by_cases h2 : 0 < d.val q <;>
      simp [fullSigns, h1, h2] at he ⊢
  clear he
  have he := he'
  simp only [Diag.val] at he hq0
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at he
    linarith [he.1 (by linarith)]
  · rw [h1, h2] at he hq0
    rcases lt_or_gt_of_ne hq0 with h | h
    · linarith
    · linarith [he.2 h]

namespace FullChamber

/-- The strands `s` and `t` have the same colour and `s` is to the left of `t` in `B`. -/
def StrandLt (B : FullChamber Γ ν) (s t : Strand ν) : Prop :=
  s.1 = t.1 ∧ ∀ p, IsGeneric Γ p → fullSigns p = B.1 → p s < p t

omit [DecidableEq I] in
theorem strandLt_iff {B : FullChamber Γ ν} {p : Strand ν → 𝕜} (hp : IsGeneric Γ p)
    (hs : fullSigns p = B.1) {s t : Strand ν} (hc : s.1 = t.1) :
    B.StrandLt s t ↔ p s < p t := by
  refine ⟨fun h => h.2 p hp hs, fun h => ⟨hc, fun q hq hqs => ?_⟩⟩
  have hne : s ≠ t := fun e => by rw [e] at h; exact lt_irrefl _ h
  obtain ⟨d, hd⟩ := Diag.exists_joins hc hne
  exact lt_of_fullSigns_eq hq hd (by rw [hs, hqs]) h

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem StrandLt.trans {B : FullChamber Γ ν} {s t u : Strand ν} (h₁ : B.StrandLt s t)
    (h₂ : B.StrandLt t u) : B.StrandLt s u :=
  ⟨h₁.1.trans h₂.1, fun p hp hs => (h₁.2 p hp hs).trans (h₂.2 p hp hs)⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem StrandLt.asymm {B : FullChamber Γ ν} {s t : Strand ν} (h : B.StrandLt s t) :
    ¬ B.StrandLt t s := fun h' => by
  obtain ⟨p, hp, hs⟩ := B.2
  exact lt_asymm (h.2 p hp hs) (h'.2 p hp hs)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem StrandLt.irrefl (B : FullChamber Γ ν) (s : Strand ν) : ¬ B.StrandLt s s := fun h =>
  h.asymm h

omit [DecidableEq I] in
/-- The order of two strands depends only on the signs of the diagonals joining them. -/
theorem strandLt_iff_of_eq {B B' : FullChamber Γ ν} {s t : Strand ν}
    (h : ∀ d : Diag ν, d.Joins s t → B.1 (.inr d) = B'.1 (.inr d)) :
    B.StrandLt s t ↔ B'.StrandLt s t := by
  suffices H : ∀ B B' : FullChamber Γ ν,
      (∀ d : Diag ν, d.Joins s t → B.1 (.inr d) = B'.1 (.inr d)) →
      B.StrandLt s t → B'.StrandLt s t from
    ⟨H B B' h, H B' B fun d hd => (h d hd).symm⟩
  intro B B' h hst
  obtain ⟨p, hp, hps⟩ := B.2
  obtain ⟨q, hq, hqs⟩ := B'.2
  have hlt := hst.2 p hp hps
  have hne : s ≠ t := fun e => by rw [e] at hlt; exact lt_irrefl _ hlt
  obtain ⟨d, hd⟩ := Diag.exists_joins hst.1 hne
  exact (strandLt_iff hq hqs hst.1).2
    (lt_of_fullSigns_eq hq hd (by rw [hps, hqs]; exact h d hd) hlt)

omit [DecidableEq I] in
theorem strandLt_fst_snd (B : FullChamber Γ ν) (d : Diag ν) :
    B.StrandLt d.fst d.snd ↔ B.1 (.inr d) = true := by
  obtain ⟨p, hp, hs⟩ := B.2
  rw [strandLt_iff hp hs d.fst_label_eq_snd, ← hs]
  simp [fullSigns, Diag.val, sub_pos]

omit [DecidableEq I] in
theorem strandLt_snd_fst (B : FullChamber Γ ν) {d : Diag ν} (h : B.1 (.inr d) = false) :
    B.StrandLt d.snd d.fst := by
  obtain ⟨p, hp, hs⟩ := B.2
  have h0 : d.val p ≠ 0 := hp (.inr d)
  rw [strandLt_iff hp hs d.fst_label_eq_snd.symm]
  rw [← hs] at h
  have h' : ¬ 0 < d.val p := fun hc => by simp [fullSigns, hc] at h
  simp only [Diag.val] at h' h0
  exact lt_of_le_of_ne (by linarith) fun e => h0 (by rw [e, sub_self])

/-- `L` contains every strand to the left of one of its strands in `B`. -/
def IsLeftClosed (B : FullChamber Γ ν) (L : Finset (Strand ν)) : Prop :=
  ∀ s t, B.StrandLt s t → t ∈ L → s ∈ L

end FullChamber

/-- `U` contains, with each strand, every strand of the same colour and higher rank. -/
def IsRankUpper (U : Finset (Strand ν)) : Prop :=
  ∀ s t : Strand ν, s.1 = t.1 → s.2.val < t.2.val → s ∈ U → t ∈ U

/-- The relabelling `x` is dominated by `B`: `#(L ∩ x(U)) ≤ #(L ∩ U)` for every `L` closed to the
left in `B` and every `U` closed upwards in rank. -/
def IsDominated (B : FullChamber Γ ν) (x : ColPerm ν) : Prop :=
  ∀ L U : Finset (Strand ν), B.IsLeftClosed L → IsRankUpper U →
    (L ∩ U.image x.1).card ≤ (L ∩ U).card

omit [IsStrictOrderedRing 𝕜] in
theorem isDominated_one (B : FullChamber Γ ν) : IsDominated B 1 := by
  intro L U _ _
  have : U.image ⇑(1 : ColPerm ν).1 = U := by
    ext t
    simp
  rw [this]

theorem isDominated_iff_of_eq {B B' : FullChamber Γ ν}
    (h : ∀ d : Diag ν, B.1 (.inr d) = B'.1 (.inr d)) (x : ColPerm ν) :
    IsDominated B x ↔ IsDominated B' x := by
  have hc : ∀ L, B.IsLeftClosed L ↔ B'.IsLeftClosed L := fun L =>
    forall₂_congr fun s t => by rw [strandLt_iff_of_eq fun d _ => h d]
  exact forall₂_congr fun L U => by rw [hc L]

/-! ### Finite-set bookkeeping -/

section Finset

variable {α : Type*} [DecidableEq α]

theorem card_insert_inter_of_notMem {a : α} {L : Finset α} (ha : a ∉ L) (W : Finset α) :
    (insert a L ∩ W).card = (L ∩ W).card + if a ∈ W then 1 else 0 := by
  split_ifs with h
  · rw [Finset.insert_inter_of_mem h, Finset.card_insert_of_notMem fun h' =>
      ha (Finset.mem_inter.1 h').1]
  · rw [Finset.insert_inter_of_notMem h, add_zero]

theorem mem_image_swap {a b y : α} {L : Finset α} : y ∈ L.image (swap a b) ↔ swap a b y ∈ L :=
  ⟨fun h => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 h
    rwa [swap_apply_self], fun h => Finset.mem_image.2 ⟨_, h, swap_apply_self _ _ _⟩⟩

theorem card_inter_image_swap (a b : α) (L V : Finset α) :
    (L ∩ V.image (swap a b)).card = (L.image (swap a b) ∩ V).card := by
  rw [← Finset.card_image_of_injective _ (swap a b).injective,
    Finset.image_inter _ _ (swap a b).injective, Finset.image_image]
  congr 2
  ext y
  simp [swap_apply_self]

theorem image_swap_of_iff {a b : α} {L : Finset α} (h : a ∈ L ↔ b ∈ L) :
    L.image (swap a b) = L := by
  ext y
  rw [mem_image_swap]
  rcases eq_or_ne y a with rfl | hya
  · rw [swap_apply_left]; exact h.symm
  rcases eq_or_ne y b with rfl | hyb
  · rw [swap_apply_right]; exact h
  · rw [swap_apply_of_ne_of_ne hya hyb]

theorem image_swap_of_notMem_of_mem {a b : α} {L : Finset α} (ha : a ∉ L) (hb : b ∈ L) :
    L.image (swap a b) = insert a (L.erase b) := by
  ext y
  rw [mem_image_swap, Finset.mem_insert, Finset.mem_erase]
  rcases eq_or_ne y a with rfl | hya
  · simp [hb]
  rcases eq_or_ne y b with rfl | hyb
  · simp [ha, hya]
  · simp [swap_apply_of_ne_of_ne hya hyb, hya, hyb]

end Finset

/-! ### Crossing a diagonal from rank order -/

/-- **Crossing a diagonal from rank order keeps dominance.** If `B'` is obtained from `B` by
crossing the diagonal `d` from the side where its strands are in rank order, every relabelling
`x` dominated by `B` gives relabellings `x` and `s_d x` dominated by `B'`. -/
theorem IsDominated.of_adjacent {B B' : FullChamber Γ ν} {d : Diag ν}
    (hadj : B.Adjacent B' (.inr d)) (hd : B.1 (.inr d) = true) {x : ColPerm ν}
    (hx : IsDominated B x) : IsDominated B' x ∧ IsDominated B' (d.refl * x) := by
  have hlr : B.StrandLt d.fst d.snd := (strandLt_fst_snd B d).2 hd
  have hd' : B'.1 (.inr d) = false := by
    have := hadj.1
    rw [hd] at this
    simpa using Ne.symm this
  have hrl : B'.StrandLt d.snd d.fst := strandLt_snd_fst B' hd'
  have hsame : ∀ s t, ¬ d.Joins s t → (B.StrandLt s t ↔ B'.StrandLt s t) := fun s t hj =>
    strandLt_iff_of_eq fun d' hd' => hadj.2 _ fun e => hj (by cases e; exact hd')
  have hfs : d.fst ≠ d.snd := d.fst_ne_snd
  -- closedness in `B` of sets closed in `B'`
  have closed : ∀ L, B'.IsLeftClosed L → (d.snd ∈ L → d.fst ∈ L) → B.IsLeftClosed L := by
    intro L hL himp s t hst ht
    by_cases hj : d.Joins s t
    · rcases hj with ⟨hs, ht'⟩ | ⟨hs, ht'⟩
      · rw [← hs]; rw [← ht'] at ht; exact himp ht
      · rw [← hs, ← ht'] at hst; exact absurd hst hlr.asymm
    · exact hL s t ((hsame s t hj).1 hst) ht
  have closedErase : ∀ L, B'.IsLeftClosed L → d.fst ∉ L → B.IsLeftClosed (L.erase d.snd) := by
    intro L hL hl s t hst ht
    rw [Finset.mem_erase] at ht ⊢
    have hj : ¬ d.Joins s t := by
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ht.1 h.symm
      · exact hl (h ▸ ht.2)
    refine ⟨fun hsr => ?_, hL s t ((hsame s t hj).1 hst) ht.2⟩
    have htl : t ≠ d.fst := fun e => hl (e ▸ ht.2)
    have hlt : B.StrandLt d.fst t := hlr.trans (hsr ▸ hst)
    have hj' : ¬ d.Joins d.fst t := by
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ht.1 h.symm
      · exact htl h.symm
    exact hl (hL _ _ ((hsame _ _ hj').1 hlt) ht.2)
  have closedInsertLeft : ∀ L, B'.IsLeftClosed L → d.snd ∈ L →
      ∀ s, B.StrandLt s d.fst → s ∈ L ∧ s ≠ d.snd := by
    intro L hL hr s hs
    have hsr : B.StrandLt s d.snd := hs.trans hlr
    have hj : ¬ d.Joins s d.snd := by
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · rw [← h] at hs; exact StrandLt.irrefl B _ hs
      · exact hfs h
    exact ⟨hL _ _ ((hsame _ _ hj).1 hsr) hr, fun e => StrandLt.irrefl B _ (e ▸ hsr)⟩
  have closedInsert : ∀ L, B'.IsLeftClosed L → d.snd ∈ L → B.IsLeftClosed (insert d.fst L) := by
    intro L hL hr s t hst ht
    rw [Finset.mem_insert] at ht ⊢
    rcases ht with rfl | ht
    · exact Or.inr (closedInsertLeft L hL hr s hst).1
    · by_cases hj : d.Joins s t
      · rcases hj with ⟨hs, -⟩ | ⟨hs, ht'⟩
        · exact Or.inl hs.symm
        · rw [← hs, ← ht'] at hst; exact absurd hst hlr.asymm
      · exact Or.inr (hL s t ((hsame s t hj).1 hst) ht)
  have closedSwap : ∀ L, B'.IsLeftClosed L → d.snd ∈ L → d.fst ∉ L →
      B.IsLeftClosed (insert d.fst (L.erase d.snd)) := by
    intro L hL hr hl s t hst ht
    rw [Finset.mem_insert] at ht ⊢
    rcases ht with rfl | ht
    · obtain ⟨h1, h2⟩ := closedInsertLeft L hL hr s hst
      exact Or.inr (Finset.mem_erase.2 ⟨h2, h1⟩)
    · exact Or.inr (closedErase L hL hl s t hst ht)
  have hU : ∀ U, IsRankUpper U → d.fst ∈ U → d.snd ∈ U := fun U hU => hU _ _ d.2.1 d.2.2
  refine ⟨fun L U hL hUp => ?_, fun L U hL hUp => ?_⟩
  · by_cases hc : B.IsLeftClosed L
    · exact hx L U hc hUp
    have hr : d.snd ∈ L := by
      by_contra hr
      exact hc (closed L hL fun h => absurd h hr)
    have hl : d.fst ∉ L := fun hl => hc (closed L hL fun _ => hl)
    have h1 := hx _ U (closedErase L hL hl) hUp
    have h2 := hx _ U (closedInsert L hL hr) hUp
    have hlU := hU U hUp
    have e1 := card_insert_inter_of_notMem (Finset.notMem_erase d.snd L) (U.image x.1)
    have e1' := card_insert_inter_of_notMem (Finset.notMem_erase d.snd L) U
    have e2 := card_insert_inter_of_notMem hl (U.image x.1)
    have e2' := card_insert_inter_of_notMem hl U
    rw [Finset.insert_erase hr] at e1 e1'
    split_ifs at e1 e1' e2 e2' <;> first | omega | (exfalso; tauto)
  · have himg : U.image (d.refl * x).1 = (U.image x.1).image (swap d.fst d.snd) := by
      rw [Finset.image_image]
      rfl
    rw [himg, card_inter_image_swap]
    by_cases hr : d.snd ∈ L
    · by_cases hl : d.fst ∈ L
      · rw [image_swap_of_iff (iff_of_true hl hr)]
        exact hx L U (closed L hL fun _ => hl) hUp
      · rw [image_swap_of_notMem_of_mem hl hr]
        refine (hx _ U (closedSwap L hL hr hl) hUp).trans ?_
        have hlU := hU U hUp
        have e1 := card_insert_inter_of_notMem (Finset.notMem_erase d.snd L) U
        have e2 := card_insert_inter_of_notMem (L := L.erase d.snd)
          (fun h => hl (Finset.mem_of_mem_erase h)) U
        rw [Finset.insert_erase hr] at e1
        rw [e2]
        split_ifs at e1 ⊢ <;> first | omega | (exfalso; tauto)
    · have hl : d.fst ∉ L := fun hl => hr (hL _ _ hrl hl)
      rw [image_swap_of_iff (iff_of_false hl hr)]
      exact hx L U (closed L hL fun h => absurd h hr) hUp

/-! ### Galleries from a rank-ordered chamber -/

/-- **Dominance along a gallery.** The gallery of a good word `w` from a rank-ordered full
chamber `C` acts in the polynomial representation by an operator supported in the relabellings
dominated by `C.flips w`. -/
theorem isSupported_opList_isDominated {C : FullChamber Γ ν} (hC : C.IsRankOrdered)
    {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    IsSupported (opList k Γ C w) {x | IsDominated (C.flips w) x} := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    refine IsSupported.id.mono fun x hx => ?_
    rw [Set.mem_singleton_iff.1 hx]
    exact isDominated_one _
  | append_singleton w h ih =>
    have hT := ih hw.of_append
    set B := C.flips w with hBdef
    obtain ⟨-, hadj, -⟩ := (hw.append : GoodWord B.1 [h]).cons
    set B' := B.flipH h with hB'def
    have hflips : C.flips (w ++ [h]) = B' := by rw [flips_append]; rfl
    have hop : opList k Γ C (w ++ [h]) = stepOp Γ B B' ∘ₗ opList k Γ C w := by
      rw [opList_append]; rfl
    have hhw : h ∉ w := by
      have := List.nodup_append_comm.1 hw.1
      exact (List.nodup_cons.1 this).1
    have hCB : C.1 h = B.1 h := by
      rw [hBdef, flips_val hw.of_append]
      simp [flipSigns, hhw]
    rw [hflips, hop]
    rcases h with wl | d
    · rw [stepOp_inl hadj, wallOp_eq_mulLeft]
      refine (hT.mulLeft _).mono fun x hx => ?_
      exact (isDominated_iff_of_eq (fun d => hadj.2 _ (by simp)) x).1 hx
    · have hd : B.1 (.inr d) = true := hCB ▸ hC d
      set l := d.left B
      set r := d.right B
      have hlr : l ≠ r := Diag.left_ne_right B d
      have hs : (rename ⇑d.refl.1 : PolyRing ν k →ₐ[k] PolyRing ν k) = rename (swap l r) := by
        rw [Diag.swap_left_right B d]
        rfl
      obtain ⟨c, α, β, hc, hstep⟩ : ∃ c α β : PolyRing ν k, IsRegular c ∧
          ∀ u, c * stepOp Γ B B' u = α * u + β * rename ⇑d.refl.1 u := by
        rw [stepOp_inr hadj, hs]
        rcases hloop : Γ.loop l.1 with _ | P
        · refine ⟨X l - X r, 1, -1, isRegular_X_sub_X hlr, fun u => ?_⟩
          rw [psiOp_of_none hloop, ddiff_spec hlr]
          ring
        · refine ⟨1, loopFactor P l r, -loopFactor P l r, isRegular_one, fun u => ?_⟩
          rw [psiOp_of_some hloop]
          ring
      refine (hT.step d.refl hc hstep).mono ?_
      rintro x (hx | ⟨y, hy, rfl⟩)
      · exact (IsDominated.of_adjacent hadj hd hx).1
      · exact (IsDominated.of_adjacent hadj hd hy).2

end Categorification.WeightedKLR
