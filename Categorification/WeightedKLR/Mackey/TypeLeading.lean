/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShuffleRigidity
import Categorification.WeightedKLR.Mackey.TypeFiltration

/-!
# The leading term of a four-block shuffle has the top shuffle type

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `μ` be a shuffle type, `Z = blockLeft ν' ν₁ μ`, `B` a
four-block chamber for the strands of `ν'` and `Z`, and `ρ` the relabelling that rank-orders the
top chamber `shuffleTop Z B`. Then `ρ` sends exactly the strands of `Z` into the first block of
`ν₁` and has shuffle type `μ` (`GalleryAlgebra.isLeft_iff_blockLeft_of_isRankOrdered`).

In the polynomial representation the four-block shuffle `r ρ (shuffleTop Z B) * galList B w`
acts through `ren ρ ∘ opList B w`. Combining this with the rigidity of the four-block shuffle
(`GalleryAlgebra.exists_isTwisted_opList_shuffleTop`), its coefficient at `ρ` is
`ρ(galNum / galDen)`, and every other relabelling occurring in it has shuffle type strictly
below `μ` (`GalleryAlgebra.exists_isTwisted_ren_opList_shuffleType_lt`).

## Main results

* `GalleryAlgebra.isLeft_iff_blockLeft_of_isRankOrdered`: the rank-ordering relabelling of the
  top chamber has shuffle type `μ` and sends `Z` into the first block.
* `GalleryAlgebra.exists_isTwisted_ren_opList_shuffleType_lt`: the operator of a four-block
  shuffle has a single term of shuffle type `μ`, at `ρ`, with coefficient `ρ(galNum / galDen)`.
* `GalleryAlgebra.rename_galNum_galDen_of_isFourBlock`: `galNum` and `galDen` are fixed by every
  relabelling preserving the four blocks. Along a good word they are products over the crossed
  hyperplanes (`GalleryAlgebra.galNum_eq_prod`), and the crossed hyperplanes are those joining
  strands in different blocks of `X` and of `Z` in the two different orders
  (`GalleryAlgebra.IsFourBlock.ne_shuffleTop_iff`), a set permuted by such relabellings.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace GalleryAlgebra

/-- **The rank-ordering of the top chamber of a four-block shuffle.** Let `μ` be a shuffle
type, `Z = blockLeft ν' ν₁ μ` and `B` a four-block chamber for the strands of `ν'` and `Z`. A
relabelling `ρ` rank-ordering `shuffleTop Z B` sends exactly the strands of `Z` into the first
block of `ν₁`, and has shuffle type `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem isLeft_iff_blockLeft_of_isRankOrdered (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B) {ρ : ColPerm ν}
    (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered) :
    (∀ t, (ρ.1 t).IsLeft ν₁ ↔ blockLeft ν' ν₁ μ t = true) ∧ shuffleType ν' ν₁ ρ = μ := by
  obtain ⟨g, rfl⟩ := hμ
  obtain ⟨y, hyZ, hyT⟩ := exists_colPerm_isLeft_eq_blockLeft (Γ := Γ) hν' hν₁ g hB.isSeparated
  have hR := isRankOrdered_rankShuffleTop (k := k) hν₁ y B
  rw [rankShuffleTop, hyZ] at hR
  set T := shuffleTop (blockLeft ν' ν₁ (shuffleType ν' ν₁ g)) B
  set u := blockSort hν₁ (y • T)
  have hρ' : ρ = u * y := by
    have h1 : ((u * y) * ρ⁻¹) • (ρ • T) = u • y • T := by
      rw [smul_smul, inv_mul_cancel_right, mul_smul]
    rw [← h1] at hR
    have := eq_one_of_isRankOrdered_smul hρ hR
    rw [mul_inv_eq_one] at this
    exact this.symm
  have hu := blockSort_mem_leftBlockStab (Γ := Γ) hν₁ (y • T)
  refine ⟨fun t => ?_, ?_⟩
  · rw [hρ']
    show (u.1 (y.1 t)).IsLeft ν₁ ↔ _
    rw [(mem_leftBlockStab.1 hu) (y.1 t), ← hyZ]
    simp
  · rw [hρ', shuffleType_mul_of_image_left ν' ν₁ (image_leftStrands_of_mem hu), hyT]

/-- **The four-block gallery has a single term of top shuffle type.** Let `μ` be a shuffle type,
`Z = blockLeft ν' ν₁ μ`, `B` a four-block chamber for the strands of `ν'` and `Z`, `w` a good word
from `B` to `shuffleTop Z B`, and `ρ` the relabelling rank-ordering `shuffleTop Z B`. In the
polynomial representation `opList B w` is twisted with a non-zero-divisor denominator `M`, its
identity coefficient is `M * galNum / galDen`, and every other relabelling `x` occurring in it
has `ρ * x` of shuffle type strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem exists_isTwisted_opList_shuffleType_lt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B)
    {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w) (hT : B.flips w = shuffleTop (blockLeft ν' ν₁ μ) B)
    {ρ : ColPerm ν} (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (opList k Γ B w) M a ∧ a 1 * galDen k B w = M * galNum k B w ∧
      ∀ x, a x ≠ 0 → x ≠ 1 → shuffleType ν' ν₁ (ρ * x) < μ := by
  classical
  obtain ⟨hZ, hρμ⟩ := isLeft_iff_blockLeft_of_isRankOrdered (k := k) hν' hν₁ hμ hB hρ
  obtain ⟨M, a, hM, hTw, h1, hlt⟩ := exists_isTwisted_opList_shuffleTop (k := k) hB hw hT
  refine ⟨M, a, hM, hTw, h1, fun x hax hx1 => ?_⟩
  have hdom : IsDominated (shuffleTop (blockLeft ν' ν₁ μ) B) x := by
    by_contra hnd
    rw [← hT] at hnd
    exact hax ((isSupported_opList_isDominated (k := k) hB.1 hw).coeff_eq_zero hTw hnd)
  have hle := shuffleType_mul_le ν' ν₁ hρ (g := ρ) (x := x) (by rwa [inv_smul_smul])
  obtain ⟨c, hc⟩ := hlt x hax hx1
  refine Pi.lt_def.2 ⟨fun i => hρμ ▸ hle i, c.1, ?_⟩
  have e1 : shuffleType ν' ν₁ (ρ * x) c.1 = (Finset.univ.filter fun t : Strand ν => t.1 = c ∧
      decide (t.IsLeft ν') = false ∧ blockLeft ν' ν₁ μ (x.1 t) = true).card := by
    unfold shuffleType
    congr 1
    refine Finset.filter_congr fun t _ => ?_
    show _ ∧ _ ∧ (ρ.1 (x.1 t)).IsLeft ν₁ ↔ _
    rw [hZ, Subtype.ext_iff]
    simp
  have e2 : μ c.1 = (Finset.univ.filter fun t : Strand ν => t.1 = c ∧
      decide (t.IsLeft ν') = false ∧ blockLeft ν' ν₁ μ t = true).card := by
    conv_lhs => rw [← hρμ]
    unfold shuffleType
    congr 1
    refine Finset.filter_congr fun t _ => ?_
    rw [hZ, Subtype.ext_iff]
    simp
  rw [e1, e2]
  exact hc

/-- **The four-block shuffle has a single term of top shuffle type.** Let `μ` be a shuffle type,
`Z = blockLeft ν' ν₁ μ`, `B` a four-block chamber for the strands of `ν'` and `Z`, `w` a good word
from `B` to `shuffleTop Z B`, and `ρ` the relabelling rank-ordering `shuffleTop Z B`. In the
polynomial representation `ren ρ ∘ opList B w` is twisted with a non-zero-divisor denominator
`M`, its coefficient of `ρ` is `M * ρ(galNum) / ρ(galDen)`, and every other relabelling occurring
in it has shuffle type strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem exists_isTwisted_ren_opList_shuffleType_lt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B)
    {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w) (hT : B.flips w = shuffleTop (blockLeft ν' ν₁ μ) B)
    {ρ : ColPerm ν} (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (ren ρ ∘ₗ opList k Γ B w) M a ∧
      a ρ * rename ⇑ρ.1 (galDen k B w) = M * rename ⇑ρ.1 (galNum k B w) ∧
      ∀ x, a x ≠ 0 → x ≠ ρ → shuffleType ν' ν₁ x < μ := by
  obtain ⟨M, a, hM, hTw, h1, hlt⟩ :=
    exists_isTwisted_opList_shuffleType_lt (k := k) hν' hν₁ hμ hB hw hT hρ
  refine ⟨rename ⇑ρ.1 M, fun y => rename ⇑ρ.1 (a (ρ⁻¹ * y)), isRegular_rename_colPerm hM ρ,
    hTw.rename ρ, ?_, fun x hx hxρ => ?_⟩
  · simp only [inv_mul_cancel]
    rw [← map_mul, h1, map_mul]
  have hax : a (ρ⁻¹ * x) ≠ 0 := fun h => hx (by simp only [h, map_zero])
  have hx1 : ρ⁻¹ * x ≠ 1 := fun h => hxρ (by rw [inv_mul_eq_one] at h; exact h.symm)
  have := hlt _ hax hx1
  rwa [mul_inv_cancel_left] at this

/-! ### Invariance of the leading coefficient under relabellings inside the blocks -/

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- The numerator of the identity coefficient of a step depends only on the sign of the chamber
on the crossed hyperplane. -/
theorem stepNum_congr {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : C.1 h = C'.1 h) :
    stepNum k C h = stepNum k C' h := by
  rcases h with wl | d
  · simp only [stepNum, hC]
  · simp only [stepNum, Diag.left, Diag.right, hC]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- The denominator of the identity coefficient of a step depends only on the sign of the
chamber on the crossed hyperplane. -/
theorem stepDen_congr {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hC : C.1 h = C'.1 h) :
    stepDen k C h = stepDen k C' h := by
  rcases h with wl | d
  · rfl
  · simp only [stepDen, Diag.left, Diag.right, hC]

omit [IsStrictOrderedRing 𝕜] in
/-- Along a good word, the numerator of the identity coefficient is the product of the step
numerators computed at the start chamber, over the hyperplanes of the word. -/
theorem galNum_eq_prod {C : FullChamber Γ ν} {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    galNum k C w = ∏ h ∈ w.toFinset, stepNum k C h := by
  classical
  induction w generalizing C with
  | nil => simp [galNum]
  | cons h w ih =>
    obtain ⟨e, -, hw'⟩ := hw.cons
    have hh : h ∉ w := (List.nodup_cons.1 hw.1).1
    rw [galNum, ih hw', List.toFinset_cons, Finset.prod_insert (by simpa using hh)]
    congr 1
    refine Finset.prod_congr rfl fun x hx => stepNum_congr ?_
    have hxh : x ≠ h := fun hx' => hh (hx' ▸ List.mem_toFinset.1 hx)
    rw [e]
    simp [flipSign, hxh]

omit [IsStrictOrderedRing 𝕜] in
/-- Along a good word, the denominator of the identity coefficient is the product of the step
denominators computed at the start chamber, over the hyperplanes of the word. -/
theorem galDen_eq_prod {C : FullChamber Γ ν} {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    galDen k C w = ∏ h ∈ w.toFinset, stepDen k C h := by
  classical
  induction w generalizing C with
  | nil => simp [galDen]
  | cons h w ih =>
    obtain ⟨e, -, hw'⟩ := hw.cons
    have hh : h ∉ w := (List.nodup_cons.1 hw.1).1
    rw [galDen, ih hw', List.toFinset_cons, Finset.prod_insert (by simpa using hh)]
    congr 1
    refine Finset.prod_congr rfl fun x hx => stepDen_congr ?_
    have hxh : x ≠ h := fun hx' => hh (hx' ▸ List.mem_toFinset.1 hx)
    rw [e]
    simp [flipSign, hxh]

omit [DecidableEq I] in
/-- In a four-block chamber, the sign on a hyperplane joining a strand of `X` with a strand
outside `X` is given by `X`. -/
theorem IsFourBlock.apply_of_ne {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) {x : Hyp Γ ν} (hx : X x.lo ≠ X x.hi) : B.1 x = X x.lo := by
  have := shuffleBot_apply X Z B x
  rw [hB.2] at this
  simpa [hx] using this

omit [DecidableEq I] in
/-- The hyperplanes crossed by the shuffle of a four-block chamber: those joining a strand of
`X` with a strand outside `X`, and a strand of `Z` with a strand outside `Z`, in the two
different orders. -/
theorem IsFourBlock.ne_shuffleTop_iff {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) (x : Hyp Γ ν) :
    B.1 x ≠ (shuffleTop Z B).1 x ↔ X x.lo ≠ X x.hi ∧ Z x.lo ≠ Z x.hi ∧ X x.lo ≠ Z x.lo := by
  have h1 := shuffleBot_apply X Z B x
  rw [hB.2, shuffleTop_apply] at h1
  rw [shuffleTop_apply]
  revert h1
  cases X x.lo <;> cases X x.hi <;> cases Z x.lo <;> cases Z x.hi <;> cases B.1 x <;> simp

omit [DecidableEq I] in
/-- **Relabelling a crossed hyperplane inside the blocks.** Let `B` be a four-block chamber for
`X` and `Z`, and `g` a relabelling preserving `X`. For a hyperplane `x` joining a strand of `X`
with a strand outside `X`, relabelling the step numerator and denominator at `x` by `g` gives
those at the hyperplane `x.comap g⁻¹` on the relabelled strands. -/
theorem rename_stepNum_stepDen_of_isFourBlock {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) {g : ColPerm ν} (hX : ∀ t, X (g.1 t) = X t) {x : Hyp Γ ν}
    (hx : X x.lo ≠ X x.hi) :
    rename ⇑g.1 (stepNum k B x) = stepNum k B (x.comap g⁻¹) ∧
      rename ⇑g.1 (stepDen k B x) = stepDen k B (x.comap g⁻¹) := by
  have hinv : ∀ t, (g⁻¹).1⁻¹ t = g.1 t := fun t => by simp
  rcases x with wl | d
  · have hsrc : (wl.comap g⁻¹).src = g.1 wl.src := hinv _
    have htgt : (wl.comap g⁻¹).tgt = g.1 wl.tgt := hinv _
    have hs : B.1 (.inl (wl.comap g⁻¹)) = B.1 (.inl wl) := by
      rw [IsFourBlock.apply_of_ne hB (x := .inl wl) hx, IsFourBlock.apply_of_ne hB (x := .inl (wl.comap g⁻¹))]
      · show X (wl.comap g⁻¹).src = X wl.src
        rw [hsrc]; exact hX _
      · show X (wl.comap g⁻¹).src ≠ X (wl.comap g⁻¹).tgt
        rw [hsrc, htgt, hX, hX]; exact hx
    have hf : rename ⇑g.1 (wl.factor (k := k)) = (wl.comap g⁻¹).factor := by
      have e := Wall.rename_factor_comap (k := k) g (wl.comap g⁻¹)
      have e' : (wl.comap g⁻¹).comap g = wl :=
        Sum.inl.inj (Hyp.comap_inv_comap (Γ := Γ) g (.inl wl))
      rw [e'] at e
      exact e
    refine ⟨?_, by simp [stepDen, Hyp.comap]⟩
    show rename ⇑g.1 (stepNum k B (.inl wl)) = stepNum k B (.inl (wl.comap g⁻¹))
    simp only [stepNum, hs]
    split_ifs
    · exact hf
    · exact map_one _
  · have hB1 : B.1 (.inr d) = true := hB.1 d
    have hXd : X d.fst = true := by
      have := IsFourBlock.apply_of_ne hB (x := .inr d) hx
      rw [hB1] at this
      exact this.symm
    have hspec : (d.comap g⁻¹).1.fst = g.1 d.fst ∧ (d.comap g⁻¹).1.snd = g.1 d.snd := by
      rcases Diag.comap_spec g⁻¹ d with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩
      · rw [h₁, h₂, hinv, hinv]; exact ⟨rfl, rfl⟩
      · exfalso
        have hx' : X (d.comap g⁻¹).1.fst ≠ X (d.comap g⁻¹).1.snd := by
          rw [h₁, h₂, hinv, hinv, hX, hX]; exact fun e => hx e.symm
        have := IsFourBlock.apply_of_ne hB (x := .inr (d.comap g⁻¹).1) hx'
        rw [hB.1] at this
        have h3 : X (d.comap g⁻¹).1.fst = true := this.symm
        rw [h₁, hinv, hX] at h3
        exact hx (by
          show X d.fst = X d.snd
          rw [hXd, h3])
    have hB2 : B.1 (.inr (d.comap g⁻¹).1) = true := hB.1 _
    have hl : Diag.left B (d.comap g⁻¹).1 = g.1 (Diag.left B d) := by
      simp only [Diag.left, hB1, hB2, ↓reduceIte, hspec.1]
    have hr : Diag.right B (d.comap g⁻¹).1 = g.1 (Diag.right B d) := by
      simp only [Diag.right, hB1, hB2, ↓reduceIte, hspec.2]
    have hc : (Diag.left B (d.comap g⁻¹).1).1 = (Diag.left B d).1 := by
      rw [hl, colPerm_apply_fst]
    show rename ⇑g.1 (stepNum k B (.inr d)) = stepNum k B (.inr (d.comap g⁻¹).1) ∧
      rename ⇑g.1 (stepDen k B (.inr d)) = stepDen k B (.inr (d.comap g⁻¹).1)
    simp only [stepNum, stepDen, hc]
    constructor
    · split
      · exact map_one _
      · rw [loopFactor_rename, hl, hr]
    · split
      · rw [map_sub, rename_X, rename_X, hl, hr]
      · exact map_one _

/-- **The identity coefficient of a four-block shuffle is invariant inside the blocks.** Let
`B` be a four-block chamber for `X` and `Z`, `w` a good word from `B` to `shuffleTop Z B`, and
`g` a relabelling preserving `X` and `Z`. Then `g` fixes `galNum B w` and `galDen B w`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem rename_galNum_galDen_of_isFourBlock {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w)
    (hT : B.flips w = shuffleTop Z B) {g : ColPerm ν} (hX : ∀ t, X (g.1 t) = X t)
    (hZ : ∀ t, Z (g.1 t) = Z t) :
    rename ⇑g.1 (galNum k B w) = galNum k B w ∧ rename ⇑g.1 (galDen k B w) = galDen k B w := by
  classical
  have hinv : ∀ t, (g⁻¹).1⁻¹ t = g.1 t := fun t => by simp
  have hX' : ∀ t, X (g.1⁻¹ t) = X t := fun t => by
    conv_rhs => rw [← g.1.apply_symm_apply t]
    exact (hX _).symm
  have hZ' : ∀ t, Z (g.1⁻¹ t) = Z t := fun t => by
    conv_rhs => rw [← g.1.apply_symm_apply t]
    exact (hZ _).symm
  have hmem : ∀ x, x ∈ w.toFinset ↔ X x.lo ≠ X x.hi ∧ Z x.lo ≠ Z x.hi ∧ X x.lo ≠ Z x.lo := by
    intro x
    rw [List.mem_toFinset, hw.mem_iff, hT, ne_comm]
    exact IsFourBlock.ne_shuffleTop_iff hB x
  have hcomap : ∀ x, x ∈ w.toFinset → x.comap g⁻¹ ∈ w.toFinset := by
    intro x hx
    rw [hmem] at hx ⊢
    rw [Hyp.lo_comap, Hyp.hi_comap]
    split_ifs <;> simp only [hinv, hX, hZ] <;> revert hx <;>
      cases X x.lo <;> cases X x.hi <;> cases Z x.lo <;> cases Z x.hi <;> simp
  have hcomap' : ∀ x, x ∈ w.toFinset → x.comap g ∈ w.toFinset := by
    intro x hx
    rw [hmem] at hx ⊢
    rw [Hyp.lo_comap, Hyp.hi_comap]
    split_ifs <;> simp only [hX', hZ'] <;> revert hx <;>
      cases X x.lo <;> cases X x.hi <;> cases Z x.lo <;> cases Z x.hi <;> simp
  have key : ∀ (f : Hyp Γ ν → PolyRing ν k),
      (∀ x ∈ w.toFinset, rename ⇑g.1 (f x) = f (x.comap g⁻¹)) →
      rename ⇑g.1 (∏ x ∈ w.toFinset, f x) = ∏ x ∈ w.toFinset, f x := by
    intro f hf
    rw [map_prod]
    refine Finset.prod_nbij' (fun x => x.comap g⁻¹) (fun x => x.comap g) hcomap hcomap'
      (fun x _ => Hyp.comap_inv_comap g x) (fun x _ => Hyp.comap_comap_inv g x) hf
  refine ⟨?_, ?_⟩
  · rw [galNum_eq_prod hw]
    exact key _ fun x hx =>
      (rename_stepNum_stepDen_of_isFourBlock hB hX ((hmem x).1 hx).1).1
  · rw [galDen_eq_prod hw]
    exact key _ fun x hx =>
      (rename_stepNum_stepDen_of_isFourBlock hB hX ((hmem x).1 hx).1).2

/-! ### Comparing two four-block chambers for the same blocks -/

/-- Along a good word from a four-block chamber to its shuffle, the crossed hyperplanes are
determined by the blocks. -/
theorem mem_toFinset_iff_of_isFourBlock {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w)
    (hT : B.flips w = shuffleTop Z B) (x : Hyp Γ ν) :
    x ∈ w ↔ X x.lo ≠ X x.hi ∧ Z x.lo ≠ Z x.hi ∧ X x.lo ≠ Z x.lo := by
  rw [hw.mem_iff, hT, ne_comm]
  exact IsFourBlock.ne_shuffleTop_iff hB x

/-- **Two four-block shuffles for the same blocks have the same identity coefficient.** Let `B`
and `B'` be four-block chambers for `X` and `Z`, and `w`, `w'` good words from them to their
shuffles. Then `galNum` and `galDen` agree.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem galNum_galDen_eq_of_isFourBlock {X Z : Strand ν → Bool} {B B' : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) (hB' : IsFourBlock X Z B') {w w' : List (Hyp Γ ν)}
    (hw : GoodWord B.1 w) (hw' : GoodWord B'.1 w') (hT : B.flips w = shuffleTop Z B)
    (hT' : B'.flips w' = shuffleTop Z B') :
    galNum k B w = galNum k B' w' ∧ galDen k B w = galDen k B' w' := by
  classical
  have hs : w.toFinset = w'.toFinset := by
    ext x
    rw [List.mem_toFinset, List.mem_toFinset, mem_toFinset_iff_of_isFourBlock hB hw hT,
      mem_toFinset_iff_of_isFourBlock hB' hw' hT']
  have hsign : ∀ x ∈ w.toFinset, B.1 x = B'.1 x := fun x hx => by
    have h := ((mem_toFinset_iff_of_isFourBlock hB hw hT x).1 (List.mem_toFinset.1 hx)).1
    rw [IsFourBlock.apply_of_ne hB h, IsFourBlock.apply_of_ne hB' h]
  rw [galNum_eq_prod hw, galNum_eq_prod hw', galDen_eq_prod hw, galDen_eq_prod hw', ← hs]
  exact ⟨Finset.prod_congr rfl fun x hx => stepNum_congr (hsign x hx),
    Finset.prod_congr rfl fun x hx => stepDen_congr (hsign x hx)⟩

omit [DecidableEq I] in
/-- The relabelling rank-ordering the shuffle of one rank-ordered chamber rank-orders the shuffle
of every other rank-ordered chamber, for the same block. -/
theorem isRankOrdered_smul_shuffleTop_of_isRankOrdered {Z : Strand ν → Bool}
    {B B' : FullChamber Γ ν} (hB : B.IsRankOrdered) (hB' : B'.IsRankOrdered) {ρ : ColPerm ν}
    (hρ : (ρ • shuffleTop Z B).IsRankOrdered) : (ρ • shuffleTop Z B').IsRankOrdered := by
  intro d
  have key : ∀ e, (shuffleTop Z B').1 (Sum.inr e) = (shuffleTop Z B).1 (Sum.inr e) := fun e => by
    rw [shuffleTop_apply, shuffleTop_apply, hB e, hB' e]
  have h := hρ d
  rw [FullChamber.smul_apply] at h ⊢
  rw [show Hyp.comap ρ (Sum.inr d : Hyp Γ ν) = Sum.inr (d.comap ρ).1 from rfl, key] at *
  exact h

end GalleryAlgebra

end Categorification.WeightedKLR
