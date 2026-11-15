/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.KLR.SpacedComparison
import Categorification.WeightedKLR.GallerySpan.Spanning
import Categorification.TypeA.Inversions

/-!
# The KLR algebra maps onto the weighted KLR algebra of the evenly spaced loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.14,
surjectivity.

By the spanning half of Theorem 2.8 (`GalleryAlgebra.span_segGallery`) the gallery algebra is
spanned by the elements `poly f * r g E * galList C w`, `w` the word of a simple segment from `C`
to `E`. The `(j, i)` entry of such an element in the weighted KLR algebra of the evenly spaced
loadings is nonzero only for `C = B_s(i)` and `g • E = B_s(j)`. Such an entry is shown to lie in
the image of `R(ν)` by induction on the number of inversions of the permutation of positions
`a ↦ pos_j(g(strand_i(a)))`, modulo elements with fewer steps (induction on the number of steps):

* if this permutation is the identity, then `j = i`, `g = 1`, `E = B_s(i)`, and the element is the
  idempotent `e(i)`;
* otherwise it has a descent at some `n`, so `E` lies on the far side of every hyperplane through
  the strands at positions `n` and `n + 1` of `B_s(i)`. Then the gallery from `B_s(i)` to `E` may
  be chosen to start with the straight crossing of these two strands (`crossElt`, the image of
  `ψ_n`), followed by a gallery with one inversion less. Two galleries with the same end points
  whose prefixes are all chambers differ by an element with fewer steps
  (`galList_sub_of_flips_eq`).

## Main results

* `galList_sub_of_flips_eq`: galleries of good words with the same end points agree
  modulo elements with fewer steps.
* `spacedHom_surjective`: `spacedHom` is surjective (Proposition 2.14, surjectivity). No
  hypothesis on `k` is needed.
* `spacedEquiv`: over a domain, `spacedHom` is an isomorphism (Proposition 2.14).
-/

namespace Categorification.WeightedKLR

open Equiv Segment MvPolynomial FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

section Generic

variable {ν : I →₀ ℕ}

omit [IsStrictOrderedRing 𝕜] in
theorem goodWord_nil (C : FullChamber Γ ν) : GoodWord C.1 [] :=
  ⟨List.nodup_nil, fun j => by rw [List.take_nil, flipSigns_nil]; exact C.2⟩

omit [IsStrictOrderedRing 𝕜] in
theorem GoodWord.of_cons {C C' : FullChamber Γ ν} {h : Hyp Γ ν} {w : List (Hyp Γ ν)}
    (hC : C.Adjacent C' h) (hh : h ∉ w) (hw : GoodWord C'.1 w) : GoodWord C.1 (h :: w) := by
  refine ⟨List.nodup_cons.2 ⟨hh, hw.1⟩, fun j => ?_⟩
  cases j with
  | zero => rw [List.take_zero, flipSigns_nil]; exact C.2
  | succ j =>
    rw [List.take_succ_cons, ← flipSigns_flipSign (fun hm => hh (List.mem_of_mem_take hm)),
      ← adjacent_iff_eq_flipSign.1 hC]
    exact hw.2 j

omit [IsStrictOrderedRing 𝕜] in
theorem GoodWord.append_of {C : FullChamber Γ ν} {a b : List (Hyp Γ ν)} (ha : GoodWord C.1 a)
    (hb : GoodWord (C.flips a).1 b) (hd : ∀ x ∈ a, x ∉ b) : GoodWord C.1 (a ++ b) := by
  induction a generalizing C with
  | nil => exact hb
  | cons h a ih =>
    obtain ⟨-, hadj, ha'⟩ := ha.cons
    refine GoodWord.of_cons hadj ?_ (ih ha' hb fun x hx => hd x (List.mem_cons_of_mem h hx))
    exact fun hm => (List.mem_append.1 (show h ∈ a ++ b from hm)).elim
      (List.nodup_cons.1 ha.1).1 (hd h List.mem_cons_self)

omit [IsStrictOrderedRing 𝕜] in
/-- The hyperplanes of a good word are those on which its end differs from its start. -/
theorem GoodWord.mem_iff {C : FullChamber Γ ν} {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w)
    (x : Hyp Γ ν) : x ∈ w ↔ (C.flips w).1 x ≠ C.1 x := by
  rw [flips_val hw]
  simp only [flipSigns]
  by_cases hx : x ∈ w <;> cases C.1 x <;> simp [hx]

omit [IsStrictOrderedRing 𝕜] in
theorem flip_append_right {σ : Hyp Γ ν → Bool} {w w' : List (Hyp Γ ν)}
    (hf : Flip (hypAff (Γ := Γ)) σ w w') (s : List (Hyp Γ ν)) :
    Flip (hypAff (Γ := Γ)) σ (w ++ s) (w' ++ s) := by
  obtain ⟨a, B, c, rfl, rfl, hB, hx, hr⟩ := hf
  exact ⟨a, B, c ++ s, by simp, by simp, hB, hx, hr⟩

omit [IsStrictOrderedRing 𝕜] in
theorem reflTransGen_flip_append_right {σ : Hyp Γ ν → Bool} {w w' : List (Hyp Γ ν)}
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) σ) w w') (s : List (Hyp Γ ν)) :
    Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) σ) (w ++ s) (w' ++ s) := by
  induction hr with
  | refl => rfl
  | tail _ hf ih => exact ih.tail (flip_append_right hf s)

/-- A good word is related by flips to the word of a simple segment between its end points. -/
theorem exists_simple_of_goodWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    ∃ p q, Simple (hypAff (Γ := Γ)) p q ∧ fullSigns p = C.1 ∧ fullSigns q = (C.flips w).1 ∧
      Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) w (word (hypAff (Γ := Γ)) p q) := by
  induction w using List.reverseRecOn with
  | nil =>
    obtain ⟨⟨p, q⟩, hs, hp, hq⟩ := exists_isChamberSegment hD hZ C C
    refine ⟨p, q, hs, hp, hq, ?_⟩
    have hnil : word (hypAff (Γ := Γ)) p q = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun h hm => ?_
      have hsep := (mem_word (f := hypAff (Γ := Γ))).1 hm
      have he : Segment.signs (hypAff (Γ := Γ)) q = Segment.signs (hypAff (Γ := Γ)) p :=
        hq.trans hp.symm
      exact ((separates_congr_right (f := hypAff (Γ := Γ)) he h).1 hsep) rfl
    rw [hnil]
  | append_singleton w h ih =>
    obtain ⟨p, q, hs, hp, hq, hr⟩ := ih hw.of_append
    have hhw : h ∉ w := fun hm =>
      (List.nodup_append.1 hw.1).2.2 h hm h (List.mem_singleton_self h) rfl
    set E := C.flips w
    obtain ⟨-, hadj, -⟩ := (hw.append : GoodWord E.1 [h]).cons
    set E' := E.flipH h
    have hCE : C.1 h = E.1 h := by
      by_contra hne
      exact hhw ((hw.of_append.mem_iff h).2 (Ne.symm hne))
    obtain ⟨e', he'g, he'E⟩ := E'.2
    obtain ⟨p₀, q₁, q₂, s₀, s₁, s₂, hs₁, hs₂, hword⟩ := exists_word_append
      (f := hypAff (Γ := Γ)) (hdist hD hZ) hs.1 hs.2.1 he'g
      (show fullSigns q h ≠ fullSigns e' h by rw [hq, he'E]; exact hadj.1)
      (fun g hg => show fullSigns q g = fullSigns e' g by rw [hq, he'E]; exact hadj.2 g hg)
      (show fullSigns p h = fullSigns q h by rw [hp, hq]; exact hCE)
    have hr₁ : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) (word (hypAff (Γ := Γ)) p q)
        (word (hypAff (Γ := Γ)) p₀ q₁) := by
      rw [← hp]
      exact reflTransGen_flip_of_simple (f := hypAff (Γ := Γ)) (hdist hD hZ) hs hs₁ s₀ s₁
    refine ⟨p₀, q₂, hs₂, s₀.trans hp, ?_, ?_⟩
    · rw [flips_append, flips_cons, flips_nil]
      exact s₂.trans he'E
    · rw [hword]
      exact (reflTransGen_flip_append_right hr [h]).trans
        (reflTransGen_flip_append_right hr₁ [h])

/-- Two good words from `C` with the same end have the same length, are equal if they have fewer
than two letters, and their galleries differ by an element with fewer steps. -/
theorem galList_sub_of_flips_eq (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {C : FullChamber Γ ν}
    {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w) (hw' : GoodWord C.1 w')
    (he : C.flips w = C.flips w') :
    w.length = w'.length ∧ (w.length < 2 → w = w') ∧
      galList k C w - galList k C w' ∈ stepFilt k Γ ν (w.length - 2) := by
  obtain ⟨p, q, hs, hp, hq, hr⟩ := exists_simple_of_goodWord hD hZ hw
  obtain ⟨p', q', hs', hp', hq', hr'⟩ := exists_simple_of_goodWord hD hZ hw'
  have hr₂ : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) (word (hypAff (Γ := Γ)) p q)
      (word (hypAff (Γ := Γ)) p' q') := by
    rw [← hp]
    exact reflTransGen_flip_of_simple (f := hypAff (Γ := Γ)) (hdist hD hZ) hs hs'
      (show fullSigns p' = fullSigns p by rw [hp, hp'])
      (show fullSigns q' = fullSigns q by rw [hq, hq', he])
  have l₁ := (reflTransGen_flip_perm hr).length_eq
  have l₂ := (reflTransGen_flip_perm hr₂).length_eq
  have l₃ := (reflTransGen_flip_perm hr').length_eq
  refine ⟨by omega, fun hl => ?_, ?_⟩
  · rw [eq_of_reflTransGen_of_length_lt hr hl,
      eq_of_reflTransGen_of_length_lt hr₂ (by omega),
      eq_of_reflTransGen_of_length_lt hr' (by omega)]
  · have d₁ := galList_reflTransGen (k := k) hD hZ hw hr
    have d₂ := galList_reflTransGen (k := k) hD hZ (hw.reflTransGen hr) hr₂
    have d₃ := galList_reflTransGen (k := k) hD hZ hw' hr'
    have hdec : galList k C w - galList k C w' =
        (galList k C w - galList k C (word (hypAff (Γ := Γ)) p q)) +
          (galList k C (word (hypAff (Γ := Γ)) p q) - galList k C (word (hypAff (Γ := Γ)) p' q')) -
          (galList k C w' - galList k C (word (hypAff (Γ := Γ)) p' q')) := by abel
    rw [hdec]
    refine Submodule.sub_mem _ (Submodule.add_mem _ d₁ ?_) ?_
    · rwa [← l₁] at d₂
    · rwa [show w.length = w'.length by omega]

/-- Some good word leads from `C` to `E`. -/
theorem exists_goodWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (C E : FullChamber Γ ν) :
    ∃ w, GoodWord C.1 w ∧ C.flips w = E := by
  obtain ⟨⟨p, q⟩, hs, hp, hq⟩ := exists_isChamberSegment hD hZ C E
  obtain ⟨hw, hf⟩ := goodWord_flips_word hs hp
  exact ⟨_, hw, Subtype.ext (hf.trans hq)⟩

/-- Relabelling a good word. -/
theorem goodWord_smul (g : ColPerm ν) {C : FullChamber Γ ν} {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) :
    GoodWord (g • C).1 (w.map (Hyp.comap g⁻¹)) ∧
      (g • C).flips (w.map (Hyp.comap g⁻¹)) = g • C.flips w ∧
      galList k (g • C) (w.map (Hyp.comap g⁻¹)) * r g C = r g (C.flips w) * galList k C w := by
  induction w generalizing C with
  | nil =>
    refine ⟨goodWord_nil _, rfl, ?_⟩
    rw [List.map_nil, galList_nil, galList_nil, flips_nil, e_mul_r]
    simp [r_mul_e]
  | cons h w ih =>
    obtain ⟨-, hadj, hw'⟩ := hw.cons
    obtain ⟨g₁, g₂, g₃⟩ := ih hw'
    have hadj' := hadj.smul g
    have hfl := flipH_eq_of_adjacent hadj'
    refine ⟨?_, ?_, ?_⟩
    · refine GoodWord.of_cons hadj' (fun hm => ?_) g₁
      obtain ⟨a, ha, hae⟩ := List.mem_map.1 hm
      rw [Hyp.comap_injective _ hae] at ha
      exact (List.nodup_cons.1 hw.1).1 ha
    · rw [List.map_cons, flips_cons, hfl, g₂, flips_cons]
    · rw [List.map_cons, galList_cons, hfl, mul_assoc, ← r_mul_t, ← mul_assoc, g₃, flips_cons,
        galList_cons, mul_assoc]

end Generic

section Spaced

variable {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "ν'" => Multiset.toFinsupp ν

/-! ### Entries of the weighted KLR algebra of the evenly spaced loadings -/

theorem e_mul_e_self {ν₀ : I →₀ ℕ} (C : FullChamber Γ ν₀) :
    (e C * e C : GalleryAlgebra k Γ ν₀) = e C := by
  rw [e_mul_e, ite_eq_left rfl]

theorem spacedIdem_mul_mul_apply (M : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν'))
    (l i : KLR.Seq ν) :
    (spacedIdem k Γ ν * M * spacedIdem k Γ ν) l i =
      e (spacedFull Γ l) * M l i * e (spacedFull Γ i) := by
  simp [spacedIdem, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem spacedIdem_mul_single_mul (j i : KLR.Seq ν) (y : GalleryAlgebra k Γ ν') :
    spacedIdem k Γ ν * Matrix.single j i y * spacedIdem k Γ ν =
      Matrix.single j i (e (spacedFull Γ j) * y * e (spacedFull Γ i)) := by
  ext l i'
  rw [spacedIdem_mul_mul_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · rw [mul_zero, zero_mul]

variable (k Γ) in
/-- The element of the weighted KLR algebra of the evenly spaced loadings with `y` in the entry
`(j, i)` (cut down by the idempotents of `B_s(j)` and `B_s(i)`) and zeros elsewhere. -/
noncomputable def cornerLin (j i : KLR.Seq ν) :
    GalleryAlgebra k Γ ν' →ₗ[k] SpacedAlgebra k Γ ν where
  toFun y := ⟨spacedIdem k Γ ν * Matrix.single j i y * spacedIdem k Γ ν, Matrix.single j i y, rfl⟩
  map_add' y z := Subtype.ext (by
    change _ = spacedIdem k Γ ν * Matrix.single j i y * spacedIdem k Γ ν +
      spacedIdem k Γ ν * Matrix.single j i z * spacedIdem k Γ ν
    simp only [Matrix.single_add, mul_add, add_mul])
  map_smul' c y := Subtype.ext (by
    change spacedIdem k Γ ν * Matrix.single j i (c • y) * spacedIdem k Γ ν =
      c • (spacedIdem k Γ ν * Matrix.single j i y * spacedIdem k Γ ν)
    rw [← Matrix.smul_single, Matrix.mul_smul, Matrix.smul_mul])

theorem cornerLin_val (j i : KLR.Seq ν) (y : GalleryAlgebra k Γ ν') :
    (cornerLin k Γ j i y).1 =
      Matrix.single j i (e (spacedFull Γ j) * y * e (spacedFull Γ i)) :=
  spacedIdem_mul_single_mul j i y

theorem cornerLin_eq_iff {j i : KLR.Seq ν} {y z : GalleryAlgebra k Γ ν'}
    (h : e (spacedFull Γ j) * y * e (spacedFull Γ i) =
      e (spacedFull Γ j) * z * e (spacedFull Γ i)) :
    cornerLin k Γ j i y = cornerLin k Γ j i z :=
  Subtype.ext (by rw [cornerLin_val, cornerLin_val, h])

theorem cornerLin_e_mul (j i : KLR.Seq ν) (y : GalleryAlgebra k Γ ν') :
    cornerLin k Γ j i (e (spacedFull Γ j) * y) = cornerLin k Γ j i y :=
  cornerLin_eq_iff (by rw [← mul_assoc, e_mul_e_self])

theorem cornerLin_mul_e (j i : KLR.Seq ν) (y : GalleryAlgebra k Γ ν') :
    cornerLin k Γ j i (y * e (spacedFull Γ i)) = cornerLin k Γ j i y :=
  cornerLin_eq_iff (by rw [mul_assoc, mul_assoc, e_mul_e_self, mul_assoc])

theorem cornerLin_mul_cornerLin (l j i : KLR.Seq ν) (y z : GalleryAlgebra k Γ ν') :
    cornerLin k Γ l j y * cornerLin k Γ j i z =
      cornerLin k Γ l i (y * e (spacedFull Γ j) * z) := by
  refine Subtype.ext ?_
  rw [IsIdempotentElem.corner_val_mul, cornerLin_val, cornerLin_val, cornerLin_val,
    Matrix.single_mul_single_same]
  congr 1
  have he : (e (spacedFull Γ j) : GalleryAlgebra k Γ ν') * e (spacedFull Γ j) =
      e (spacedFull Γ j) := e_mul_e_self _
  calc e (spacedFull Γ l) * y * e (spacedFull Γ j) * (e (spacedFull Γ j) * z * e (spacedFull Γ i))
      = e (spacedFull Γ l) * y * (e (spacedFull Γ j) * e (spacedFull Γ j)) * z *
          e (spacedFull Γ i) := by noncomm_ring
    _ = _ := by rw [he]; noncomm_ring

theorem cornerLin_mul_of {l j i : KLR.Seq ν} {y : GalleryAlgebra k Γ ν'}
    (hy : y * e (spacedFull Γ j) = y) (z : GalleryAlgebra k Γ ν') :
    cornerLin k Γ l i (y * z) = cornerLin k Γ l j y * cornerLin k Γ j i z := by
  rw [cornerLin_mul_cornerLin, hy]

theorem genImg_idem (i : KLR.Seq ν) :
    genImg k Γ (.idem i) = cornerLin k Γ i i (e (spacedFull Γ i)) := rfl

theorem genImg_idem_mul_mul (l i : KLR.Seq ν) (x : SpacedAlgebra k Γ ν) :
    genImg k Γ (.idem l) * x * genImg k Γ (.idem i) = cornerLin k Γ l i (x.1 l i) := by
  refine Subtype.ext ?_
  rw [IsIdempotentElem.corner_val_mul, IsIdempotentElem.corner_val_mul, genImg_idem, genImg_idem,
    cornerLin_val, cornerLin_val, cornerLin_val, Matrix.single_mul_mul_single]
  simp only [e_mul_e_self, SpacedAlgebra.mul_e, SpacedAlgebra.e_mul]

/-- Every element is the sum of its entries. -/
theorem eq_sum_cornerLin (x : SpacedAlgebra k Γ ν) :
    x = ∑ j, ∑ i, cornerLin k Γ j i (x.1 j i) := by
  let v : SpacedAlgebra k Γ ν →+ Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν') :=
    ⟨⟨fun x => x.1, rfl⟩, fun _ _ => rfl⟩
  refine Subtype.ext ?_
  change v x = v (∑ j, ∑ i, cornerLin k Γ j i (x.1 j i))
  simp only [map_sum]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (v x)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change Matrix.single j i (x.1 j i) = (cornerLin k Γ j i (x.1 j i)).1
  rw [cornerLin_val, SpacedAlgebra.e_mul, SpacedAlgebra.mul_e]

/-! ### The permutation of positions of a relabelling -/

/-- The permutation of positions `a ↦ pos_j(g(strand_i(a)))` of a relabelling `g` from the
strands of `i` to those of `j`. -/
noncomputable def posPerm (i j : KLR.Seq ν) (g : ColPerm ν') : Perm (Fin m) :=
  i.strandEquiv.trans (g.1.trans j.strandEquiv.symm)

theorem posPerm_apply (i j : KLR.Seq ν) (g : ColPerm ν') (a : Fin m) :
    posPerm i j g a = j.posOf (g.1 (i.strandAt a)) := rfl

theorem eq_of_posPerm_eq_one {i j : KLR.Seq ν} {g : ColPerm ν'} (h : posPerm i j g = 1) :
    j = i ∧ g = 1 := by
  have ha : ∀ a, j.posOf (g.1 (i.strandAt a)) = a := fun a => by
    rw [← posPerm_apply, h, Perm.one_apply]
  have hji : j = i := by
    refine Subtype.ext (funext fun a => ?_)
    conv_lhs => rw [← ha a]
    rw [KLR.Seq.label_posOf, Strand.label, ColPerm.apply_fst]
    rfl
  subst hji
  refine ⟨rfl, Subtype.ext (Equiv.ext fun t => ?_)⟩
  have := congrArg j.strandAt (ha (j.posOf t))
  rwa [KLR.Seq.strandAt_posOf, KLR.Seq.strandAt_posOf] at this

theorem posPerm_smul_of_ne {i j : KLR.Seq ν} {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ ≠ i.1 ⟨n + 1, h⟩) (g : ColPerm ν') :
    posPerm (TypeA.sadj m n • i) j g = posPerm i j g * TypeA.sadj m n := by
  refine Equiv.ext fun b => ?_
  rw [Perm.mul_apply, posPerm_apply, posPerm_apply]
  congr 2
  have := KLR.Seq.strandAt_smul i (TypeA.sadj m n) (KLR.Seq.lt_sadj_iff i h hc)
    (TypeA.sadj m n b)
  rwa [← Perm.mul_apply, TypeA.sadj_mul_self, Perm.one_apply] at this

theorem posPerm_smul_of_eq {i j : KLR.Seq ν} {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) (g : ColPerm ν') :
    posPerm (TypeA.sadj m n • i) j (g * (crossDiag i n h hc).refl) =
      posPerm i j g * TypeA.sadj m n := by
  rw [KLR.Seq.sadj_smul_of_eq i h hc]
  refine Equiv.ext fun b => ?_
  rw [Perm.mul_apply, posPerm_apply, posPerm_apply]
  show j.posOf (g.1 (swap (leftStrand i n h) (rightStrand i n h) (i.strandAt b))) = _
  congr 2
  have := congrArg i.strandAt (KLR.Seq.posOf_swap i h (i.strandAt b))
  rwa [KLR.Seq.strandAt_posOf, KLR.Seq.posOf_strandAt] at this

/-! ### Signs of the evenly spaced chambers -/

theorem fullSigns_ne_of_joinsPair {π π' : Strand ν' → ℕ} (hπ : Function.Injective π)
    (hπ' : Function.Injective π') {x : Hyp Γ ν'} {u v : Strand ν'} (hx : x.JoinsPair u v)
    (h1 : π u < π v) (h2 : π' v < π' u) :
    fullSigns (Γ := Γ) (spacedConfig Γ.spacing π) x ≠
      fullSigns (Γ := Γ) (spacedConfig Γ.spacing π') x := by
  rw [fullSigns_spacedConfig WeightedGraph.spacing_pos WeightedGraph.abs_weight_lt_spacing hπ,
    fullSigns_spacedConfig WeightedGraph.spacing_pos WeightedGraph.abs_weight_lt_spacing hπ']
  rcases x with w | d
  · rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    · simp only [ha, hb, ne_eq, decide_eq_decide]
      omega
  · rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    · simp only [ha, hb, ne_eq, decide_eq_decide]
      omega

/-- If `g • E = B_s(j)` and the strands `u, v`, in this order in `i`, are in the other order in
`j` after relabelling, then `E` and `B_s(i)` lie on different sides of every hyperplane through
`u` and `v`. -/
theorem signs_ne_of_descent {i j : KLR.Seq ν} {g : ColPerm ν'} {E : FullChamber Γ ν'}
    (hg : g • E = spacedFull Γ j) {u v : Strand ν'} (huv : i.posOf u < i.posOf v)
    (hd : j.posOf (g.1 v) < j.posOf (g.1 u)) {x : Hyp Γ ν'} (hx : x.JoinsPair u v) :
    E.1 x ≠ (spacedFull Γ i).1 x := by
  have hE : E = g⁻¹ • spacedFull Γ j := by rw [← hg, inv_smul_smul]
  have hinj : Function.Injective (fun t => (j.posOf (g.1 t) : ℕ)) :=
    (injective_posOf_val j).comp g.1.injective
  have hEv : E.1 =
      fullSigns (Γ := Γ) (spacedConfig Γ.spacing (fun t => (j.posOf (g.1 t) : ℕ))) := by
    rw [hE]
    show signMap g⁻¹ (spacedFull Γ j).1 = _
    rw [← fullSigns_spacedPos j, spacedPos_eq_spacedConfig,
      ← fullSigns_act (isGeneric_spacedConfig WeightedGraph.spacing_pos
        WeightedGraph.abs_weight_lt_spacing (injective_posOf_val j))]
    rfl
  rw [hEv, ← fullSigns_spacedPos i, spacedPos_eq_spacedConfig]
  exact (fullSigns_ne_of_joinsPair (injective_posOf_val i) hinj hx
    (Fin.lt_def.1 huv) (Fin.lt_def.1 hd)).symm

/-! ### The crossing word -/

/-- Without loops, the only hyperplane through two neighbouring strands of the same colour is
their diagonal. -/
theorem crossWord_eq_singleton (hE : ∀ e, Γ.head e ≠ Γ.tail e) (i : KLR.Seq ν) (n : ℕ)
    (h : n + 1 < m) (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) :
    crossWord Γ i n h = [.inr (crossDiag i n h hc)] := by
  refine List.eq_singleton_of_nodup (nodup_crossWord i n h) ?_ fun x hx => ?_
  · exact (mem_crossWord i n h).2 (Or.inl ⟨rfl, rfl⟩)
  · have hj := (mem_crossWord i n h).1 hx
    rcases x with w | d'
    · exfalso
      rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · apply hE w.edge
        have e1 : w.src.label = Γ.head w.edge := w.2.1
        have e2 : w.tgt.label = Γ.tail w.edge := w.2.2.1
        rw [← e1, ← e2, hs, ht]
        exact hc
      · apply hE w.edge
        have e1 : w.src.label = Γ.head w.edge := w.2.1
        have e2 : w.tgt.label = Γ.tail w.edge := w.2.2.1
        rw [← e1, ← e2, hs, ht]
        exact hc.symm
    · rcases hj with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · exact congrArg Sum.inr (Subtype.ext (Prod.ext hs ht))
      · exfalso
        have h1 := d'.2.2
        have h2 : (leftStrand i n h).2.val < (rightStrand i n h).2.val :=
          (crossDiag i n h hc).2.2
        change d'.fst.2.val < d'.snd.2.val at h1
        rw [hs, ht] at h1
        omega

/-- For two neighbouring strands of different colours, the straight crossing leads from
`B_s(i)` to `B_s(s_n i)`. -/
theorem flips_crossWord_of_ne (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (i : KLR.Seq ν) (n : ℕ)
    (h : n + 1 < m) (hc : i.1 ⟨n, by omega⟩ ≠ i.1 ⟨n + 1, h⟩) :
    (spacedFull Γ i).flips (crossWord Γ i n h) = spacedFull Γ (TypeA.sadj m n • i) := by
  apply Subtype.ext
  rw [(goodWord_crossWord i n h hD hZ).2, ← fullSigns_spacedPos]
  congr 1
  funext t
  simp only [Function.comp_apply, KLR.Seq.spacedPos]
  rw [KLR.Seq.posOf_swap i h, KLR.Seq.posOf_smul i _ (KLR.Seq.lt_sadj_iff i h hc)]

theorem e_mul_e_of_ne {ν₀ : I →₀ ℕ} {C D : FullChamber Γ ν₀} (h : C ≠ D) :
    (e C * e D : GalleryAlgebra k Γ ν₀) = 0 := by
  rw [e_mul_e]
  split_ifs with h'
  exacts [absurd h' h, rfl]

theorem e_mul_r_of_ne {ν₀ : I →₀ ℕ} {D : FullChamber Γ ν₀} {g : ColPerm ν₀}
    {C : FullChamber Γ ν₀} (h : D ≠ g • C) : (e D * r g C : GalleryAlgebra k Γ ν₀) = 0 := by
  rw [e_mul_r]
  split_ifs with h'
  exacts [absurd h' h, rfl]

/-! ### Generators in a subalgebra -/

variable {S : Subalgebra k (SpacedAlgebra k Γ ν)} (hgen : ∀ g, genImg k Γ g ∈ S)
include hgen

theorem cornerLin_mem_of_mem {l i : KLR.Seq ν} {x : SpacedAlgebra k Γ ν} (hx : x ∈ S) :
    cornerLin k Γ l i (x.1 l i) ∈ S := by
  rw [← genImg_idem_mul_mul]
  exact S.mul_mem (S.mul_mem (hgen _) hx) (hgen _)

theorem cornerLin_poly_mem (j : KLR.Seq ν) (f : PolyRing ν' k) :
    cornerLin k Γ j j (poly f) ∈ S := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : (poly (MvPolynomial.C a) : GalleryAlgebra k Γ ν') = a • 1 := by
      rw [← polyHom_apply, MvPolynomial.C_eq_smul_one, map_smul, map_one]
    rw [this, map_smul]
    refine S.smul_mem ?_ a
    rw [← cornerLin_mul_e, one_mul, ← genImg_idem]
    exact hgen _
  | add p q hp hq =>
    rw [← polyHom_apply, map_add, polyHom_apply, polyHom_apply, map_add]
    exact S.add_mem hp hq
  | mul_X p s hp =>
    have hX : cornerLin k Γ j j (poly (X s)) ∈ S := by
      have h := cornerLin_mem_of_mem hgen (l := j) (i := j) (hgen (.dot (j.posOf s)))
      have hv : (genImg k Γ (.dot (j.posOf s))).1 j j =
          e (spacedFull Γ j) * poly (X s) * e (spacedFull Γ j) := by
        show (spacedIdem k Γ ν * genMat k Γ (.dot (j.posOf s)) * spacedIdem k Γ ν :
          Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) j j = _
        rw [spacedIdem_mul_mul_apply]
        simp [genMat]
      rwa [hv, cornerLin_mul_e, cornerLin_e_mul] at h
    have : cornerLin k Γ j j (poly (p * X s)) =
        cornerLin k Γ j j (poly p) * cornerLin k Γ j j (poly (X s)) := by
      rw [cornerLin_mul_cornerLin, mul_assoc, e_mul_poly, ← mul_assoc, cornerLin_mul_e,
        ← polyHom_apply, ← polyHom_apply, ← polyHom_apply, map_mul]
    rw [this]
    exact S.mul_mem hp hX

theorem cornerLin_crossElt_mem (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) :
    cornerLin k Γ (TypeA.sadj m n • i) i (crossElt k Γ i n h) ∈ S := by
  have hm := cornerLin_mem_of_mem hgen (l := TypeA.sadj m n • i) (i := i) (hgen (.cross n))
  have hv : (genImg k Γ (.cross n)).1 (TypeA.sadj m n • i) i =
      e (spacedFull Γ (TypeA.sadj m n • i)) * crossElt k Γ i n h * e (spacedFull Γ i) := by
    show (spacedIdem k Γ ν * genMat k Γ (.cross n) * spacedIdem k Γ ν :
      Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) (TypeA.sadj m n • i) i = _
    rw [spacedIdem_mul_mul_apply]
    simp [genMat, h]
  rwa [hv, cornerLin_mul_e, cornerLin_e_mul] at hm

omit hgen in
/-- Galleries of good words with the same end points give the same entry modulo elements with
fewer steps. -/
theorem cornerLin_mem_of_flips_eq (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {N : ℕ}
    (hlow : ∀ M < N, ∀ y ∈ stepFilt k Γ ν' M, ∀ j i, cornerLin k Γ j i y ∈ S)
    {C : FullChamber Γ ν'} {w w₂ : List (Hyp Γ ν')} (hw : GoodWord C.1 w)
    (hw₂ : GoodWord C.1 w₂) (he : C.flips w = C.flips w₂) (hN : w.length ≤ N)
    {y : GalleryAlgebra k Γ ν'} (hy : y ∈ stepFilt k Γ ν' 0) {j i : KLR.Seq ν}
    (h₂ : cornerLin k Γ j i (y * galList k C w₂) ∈ S) :
    cornerLin k Γ j i (y * galList k C w) ∈ S := by
  obtain ⟨-, h01, hd⟩ := galList_sub_of_flips_eq (k := k) hD hZ hw hw₂ he
  have : y * galList k C w = y * (galList k C w - galList k C w₂) + y * galList k C w₂ := by
    rw [mul_sub, sub_add_cancel]
  rw [this, map_add]
  refine S.add_mem ?_ h₂
  by_cases hl2 : w.length < 2
  · rw [h01 hl2, sub_self, mul_zero, map_zero]
    exact S.zero_mem
  · have hm := mul_mem_stepFilt hy hd
    rw [zero_add] at hm
    exact hlow _ (by omega) _ hm j i

/-- The induction on the inversions of the permutation of positions: if the entries of elements
with fewer than `N` steps lie in `S`, then so does the entry `(j, i)` of
`r g E * galList B_s(i) w` for a good word `w` of length at most `N` from `B_s(i)` to `E`, when
`g • E = B_s(j)`. -/
theorem cornerLin_r_galList_mem (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e) {N : ℕ}
    (hlow : ∀ M < N, ∀ y ∈ stepFilt k Γ ν' M, ∀ j i, cornerLin k Γ j i y ∈ S) :
    ∀ K (i j : KLR.Seq ν) (g : ColPerm ν') (w : List (Hyp Γ ν')),
      TypeA.invCount m (posPerm i j g) = K → GoodWord (spacedFull Γ i).1 w → w.length ≤ N →
      g • (spacedFull Γ i).flips w = spacedFull Γ j →
      cornerLin k Γ j i (r g ((spacedFull Γ i).flips w) * galList k (spacedFull Γ i) w) ∈ S := by
  have hZ : Γ.NoZeroLoops := fun e he => absurd he (hE e)
  intro K
  induction K using Nat.strong_induction_on with
  | _ K IH =>
  intro i j g w hK hw hN hg
  by_cases h1 : posPerm i j g = 1
  · obtain ⟨rfl, rfl⟩ := eq_of_posPerm_eq_one h1
    rw [one_smul] at hg
    have hnil : w = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx =>
      (hw.mem_iff x).1 hx (by rw [hg])
    subst hnil
    rw [flips_nil, r_one, galList_nil, e_mul_e_self, ← genImg_idem]
    exact hgen _
  obtain ⟨n, h, hdes⟩ := TypeA.exists_descent h1
  have hlt : TypeA.invCount m (posPerm i j g * TypeA.sadj m n) < K := by
    have := TypeA.invCount_mul_sadj_of_gt h hdes
    omega
  obtain ⟨hcw, hcwf⟩ := goodWord_crossWord i n h hD hZ
  set E := (spacedFull Γ i).flips w with hEdef
  set F := (spacedFull Γ i).flips (crossWord Γ i n h) with hFdef
  -- every hyperplane through the two strands separates `B_s(i)` from `E`
  have hEne : ∀ x ∈ crossWord Γ i n h, E.1 x ≠ (spacedFull Γ i).1 x := fun x hx =>
    signs_ne_of_descent hg (u := leftStrand i n h) (v := rightStrand i n h)
      (by simp [Fin.lt_def]) hdes ((mem_crossWord i n h).1 hx)
  obtain ⟨w', hw', hw'f⟩ := exists_goodWord hD hZ F E
  have hdisj : ∀ x ∈ crossWord Γ i n h, x ∉ w' := fun x hx hx' => by
    have a1 := (hcw.mem_iff x).1 hx
    have a2 := (hw'.mem_iff x).1 hx'
    have a3 := hEne x hx
    rw [hw'f] at a2
    revert a1 a2 a3
    cases E.1 x <;> cases F.1 x <;> cases (spacedFull Γ i).1 x <;> decide
  have hw₂ := hcw.append_of hw' hdisj
  have he : (spacedFull Γ i).flips w = (spacedFull Γ i).flips (crossWord Γ i n h ++ w') := by
    rw [flips_append, hw'f]
  obtain ⟨hlen, -, -⟩ := galList_sub_of_flips_eq (k := k) hD hZ hw hw₂ he
  have hlen' : w'.length ≤ N := by
    rw [List.length_append] at hlen
    omega
  refine cornerLin_mem_of_flips_eq hD hZ hlow hw hw₂ he hN (r_mem_stepFilt g E 0) ?_
  rw [galList_append]
  by_cases hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩
  · -- same colour: the crossing ends with the relabelling exchanging the two strands
    have hw1 := crossWord_eq_singleton hE i n h hc
    obtain ⟨-, ha, -⟩ := (hw1 ▸ hcw).cons
    have hC : (crossDiag i n h hc).refl • F = spacedFull Γ (TypeA.sadj m n • i) := by
      show (crossDiag i n h hc).refl • (spacedFull Γ i).flips (crossWord Γ i n h) = _
      rw [hw1, flips_cons, flips_nil, ← ha.refl_smul, smul_smul, Diag.refl_mul_refl, one_smul,
        KLR.Seq.sadj_smul_of_eq i h hc]
    have hcr : crossElt k Γ i n h =
        r (crossDiag i n h hc).refl ((spacedFull Γ i).flips (crossWord Γ i n h)) *
          galList k (spacedFull Γ i) (crossWord Γ i n h) := by
      simp only [crossElt, hc, ↓reduceDIte]
    obtain ⟨g1, g2, g3⟩ := goodWord_smul (k := k) (crossDiag i n h hc).refl hw'
    rw [hw'f] at g2 g3
    have hrg : (r g E : GalleryAlgebra k Γ ν') =
        r (g * (crossDiag i n h hc).refl) ((crossDiag i n h hc).refl • E) *
          r (crossDiag i n h hc).refl E := by
      rw [r_mul_r, mul_assoc, Diag.refl_mul_refl, mul_one]
    have key : r g E * (galList k ((spacedFull Γ i).flips (crossWord Γ i n h)) w' *
        galList k (spacedFull Γ i) (crossWord Γ i n h)) =
        r (g * (crossDiag i n h hc).refl) ((crossDiag i n h hc).refl • E) *
          galList k ((crossDiag i n h hc).refl • F)
            (w'.map (Hyp.comap (crossDiag i n h hc).refl⁻¹)) * crossElt k Γ i n h := by
      rw [hcr, hrg, mul_assoc, ← mul_assoc (r (crossDiag i n h hc).refl E), ← g3]
      simp only [mul_assoc]
      rfl
    rw [key, hC]
    rw [hC] at g1 g2
    rw [cornerLin_mul_of (j := TypeA.sadj m n • i) (by rw [mul_assoc, galList_mul_e])]
    refine S.mul_mem ?_ (cornerLin_crossElt_mem hgen i n h)
    have := IH (TypeA.invCount m (posPerm (TypeA.sadj m n • i) j
      (g * (crossDiag i n h hc).refl))) (by rw [posPerm_smul_of_eq h hc g]; exact hlt)
      (TypeA.sadj m n • i) j _ _ rfl g1 (by rw [List.length_map]; exact hlen')
      (by rw [g2, smul_smul, mul_assoc, Diag.refl_mul_refl, mul_one]; exact hg)
    rwa [g2] at this
  · -- different colours: the crossing is the straight gallery
    have hflip : F = spacedFull Γ (TypeA.sadj m n • i) := flips_crossWord_of_ne hD hZ i n h hc
    have hcr : crossElt k Γ i n h = galList k (spacedFull Γ i) (crossWord Γ i n h) := by
      simp only [crossElt, hc, ↓reduceDIte]
    rw [hflip] at hw' hw'f
    rw [← mul_assoc, ← hcr, flips_crossWord_of_ne hD hZ i n h hc,
      cornerLin_mul_of (j := TypeA.sadj m n • i) (by rw [mul_assoc, galList_mul_e])]
    refine S.mul_mem ?_ (cornerLin_crossElt_mem hgen i n h)
    have := IH (TypeA.invCount m (posPerm (TypeA.sadj m n • i) j g))
      (by rw [posPerm_smul_of_ne h hc g]; exact hlt) (TypeA.sadj m n • i) j g w' rfl hw' hlen'
      (by rw [hw'f]; exact hg)
    rwa [hw'f] at this

/-- Every entry of every element of the gallery algebra lies in `S`. -/
theorem cornerLin_mem (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e) (N : ℕ) :
    ∀ y ∈ stepFilt k Γ ν' N, ∀ j i, cornerLin k Γ j i y ∈ S := by
  have hZ : Γ.NoZeroLoops := fun e he => absurd he (hE e)
  choose P hP using exists_isChamberSegment (Γ := Γ) (ν := ν') hD hZ
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro y hy j i
  have hy' := stepFilt_le_segSpan (one_mem_segSpan hP)
    (fun M hM C E E₁ hl => t_mul_segGallery_mem hP hD hZ M hM C E E₁ hl) N hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, C, E, hl, rfl⟩ := hx
    by_cases hC : C = spacedFull Γ i
    swap
    · have h0 : segGallery (k := k) P C E * e (spacedFull Γ i) = 0 := by
        rw [segGallery, ← galList_mul_e, mul_assoc, e_mul_e_of_ne hC, mul_zero]
      rw [← cornerLin_mul_e, mul_assoc, h0, mul_zero, map_zero]
      exact S.zero_mem
    subst hC
    by_cases hg : g • E = spacedFull Γ j
    swap
    · have h0 : e (spacedFull Γ j) * (poly f * r g E * segGallery (k := k) P (spacedFull Γ i) E) =
          0 := by
        rw [← mul_assoc, ← mul_assoc, e_mul_poly, mul_assoc (poly f),
          e_mul_r_of_ne (Ne.symm hg), mul_zero, zero_mul]
      rw [← cornerLin_e_mul, h0, map_zero]
      exact S.zero_mem
    have hsplit : cornerLin k Γ j i (poly f * r g E * segGallery P (spacedFull Γ i) E) =
        cornerLin k Γ j j (poly f) *
          cornerLin k Γ j i (r g E * segGallery P (spacedFull Γ i) E) := by
      rw [cornerLin_mul_cornerLin, ← e_mul_poly, mul_assoc (e _), cornerLin_e_mul, mul_assoc]
    rw [hsplit]
    refine S.mul_mem (cornerLin_poly_mem hgen j f) ?_
    have hw := (goodWord_flips_word (hP (spacedFull Γ i) E).1 (hP (spacedFull Γ i) E).2.1).1
    have := cornerLin_r_galList_mem hgen hD hE IH _ i j g _ rfl hw hl
      (by rw [flips_segWord hP]; exact hg)
    rwa [flips_segWord hP] at this
  | zero =>
    rw [map_zero]
    exact S.zero_mem
  | add x z _ _ hx hz =>
    rw [map_add]
    exact S.add_mem hx hz
  | smul c x _ hx =>
    rw [map_smul]
    exact S.smul_mem hx c

end Spaced

section Surjective

variable {ν : Multiset I}

/-- B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.14,
surjectivity: the KLR algebra `R(ν)` maps onto the weighted KLR algebra of the evenly spaced
loadings. No hypothesis on `k` is needed. -/
theorem spacedHom_surjective (hS : Γ.Standing) (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) : Function.Surjective (spacedHom k hS hD hE hl (ν := ν)) := by
  have hgen : ∀ g, genImg k Γ g ∈ (spacedHom k hS hD hE hl (ν := ν)).range := fun g =>
    (AlgHom.mem_range _).2 ⟨KLR.KLRAlgebra.mk k Γ.klrQ ν (FreeAlgebra.ι k g), by
      rw [spacedHom_mk, spacedFreeHom, FreeAlgebra.lift_ι_apply]⟩
  intro x
  have hx : x ∈ (spacedHom k hS hD hE hl (ν := ν)).range := by
    rw [eq_sum_cornerLin x]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.sum_mem _ fun i _ => ?_
    obtain ⟨N, hN⟩ := exists_mem_stepFilt (x.1 j i)
    exact cornerLin_mem hgen hD hE N _ hN j i
  exact (AlgHom.mem_range _).1 hx

/-- B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.14:
the KLR algebra `R(ν)` is isomorphic to the weighted KLR algebra of the evenly spaced loadings.

The hypothesis `[IsDomain k]` is not in the source; it is used by the current proof of
injectivity (`spacedHom_injective`, through the faithful polynomial representation). -/
noncomputable def spacedEquiv [IsDomain k] (hS : Γ.Standing) (hD : Γ.Dagger)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ c, Γ.loop c = none) :
    KLR.KLRAlgebra k Γ.klrQ ν ≃ₐ[k] SpacedAlgebra k Γ ν :=
  AlgEquiv.ofBijective (spacedHom k hS hD hE hl)
    ⟨spacedHom_injective hS hD hE hl, spacedHom_surjective hS hD hE hl⟩

theorem spacedEquiv_apply [IsDomain k] (hS : Γ.Standing) (hD : Γ.Dagger)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ c, Γ.loop c = none) (x : KLR.KLRAlgebra k Γ.klrQ ν) :
    spacedEquiv hS hD hE hl x = spacedHom k hS hD hE hl x := rfl

end Surjective

end Categorification.WeightedKLR
