/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StendhalInjective
import Categorification.WeightedKLR.KLR.SpacedSurjective

/-!
# Surjectivity of the homomorphism of Webster's Theorem 3.5

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5, surjectivity.
-/

namespace Categorification.WeightedKLR

open Equiv Segment MvPolynomial FullChamber GalleryAlgebra

/-! ### Entries of a chamber algebra -/

section ChamberLin

variable {J : Type*} [DecidableEq J] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Δ : WeightedGraph J 𝕜 k} {ν : J →₀ ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → FullChamber Δ ν)

theorem chamberIdem_mul_mul_apply (M : Matrix ι ι (GalleryAlgebra k Δ ν)) (l i : ι) :
    (chamberIdem k F * M * chamberIdem k F) l i = e (F l) * M l i * e (F i) := by
  simp [chamberIdem, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem chamberElt_val_apply (M : Matrix ι ι (GalleryAlgebra k Δ ν)) (l i : ι) :
    (chamberElt k F M).1 l i = e (F l) * M l i * e (F i) :=
  chamberIdem_mul_mul_apply F M l i

/-- The element of the chamber algebra with `y` in the entry `(j, i)` (cut down by the
idempotents of `F j` and `F i`) and zeros elsewhere. -/
noncomputable def chamberLin (j i : ι) : GalleryAlgebra k Δ ν →ₗ[k] ChamberAlgebra k F where
  toFun y := chamberElt k F (Matrix.single j i y)
  map_add' y z := by rw [Matrix.single_add, chamberElt_add]
  map_smul' c y := by rw [← Matrix.smul_single, chamberElt_smul]; rfl

variable {F}

theorem chamberLin_val (j i : ι) (y : GalleryAlgebra k Δ ν) :
    (chamberLin F j i y).1 = Matrix.single j i (e (F j) * y * e (F i)) := by
  ext l i'
  change (chamberElt k F (Matrix.single j i y)).1 l i' = _
  rw [chamberElt_val_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; rfl
  · rw [mul_zero, zero_mul]

theorem chamberLin_eq_iff {j i : ι} {y z : GalleryAlgebra k Δ ν}
    (h : e (F j) * y * e (F i) = e (F j) * z * e (F i)) :
    chamberLin F j i y = chamberLin F j i z :=
  Subtype.ext (by rw [chamberLin_val, chamberLin_val, h])

theorem e_mul_e_self' (C : FullChamber Δ ν) : (e C * e C : GalleryAlgebra k Δ ν) = e C := by
  rw [e_mul_e, ite_eq_left rfl]

theorem chamberLin_e_mul (j i : ι) (y : GalleryAlgebra k Δ ν) :
    chamberLin F j i (e (F j) * y) = chamberLin F j i y :=
  chamberLin_eq_iff (by rw [← mul_assoc, e_mul_e_self'])

theorem chamberLin_mul_e (j i : ι) (y : GalleryAlgebra k Δ ν) :
    chamberLin F j i (y * e (F i)) = chamberLin F j i y :=
  chamberLin_eq_iff (by rw [mul_assoc, mul_assoc, e_mul_e_self', mul_assoc])

theorem chamberLin_mul_chamberLin (l j i : ι) (y z : GalleryAlgebra k Δ ν) :
    chamberLin F l j y * chamberLin F j i z = chamberLin F l i (y * e (F j) * z) := by
  refine Subtype.ext ?_
  rw [IsIdempotentElem.corner_val_mul, chamberLin_val, chamberLin_val, chamberLin_val,
    Matrix.single_mul_single_same]
  congr 1
  have he : (e (F j) : GalleryAlgebra k Δ ν) * e (F j) = e (F j) := e_mul_e_self' _
  calc e (F l) * y * e (F j) * (e (F j) * z * e (F i))
      = e (F l) * y * (e (F j) * e (F j)) * z * e (F i) := by noncomm_ring
    _ = _ := by rw [he]; noncomm_ring

theorem chamberLin_mul_of {l j i : ι} {y : GalleryAlgebra k Δ ν} (hy : y * e (F j) = y)
    (z : GalleryAlgebra k Δ ν) :
    chamberLin F l i (y * z) = chamberLin F l j y * chamberLin F j i z := by
  rw [chamberLin_mul_chamberLin, hy]

theorem chamberLin_e_mul_mul (l i : ι) (x : ChamberAlgebra k F) :
    chamberLin F l l (e (F l)) * x * chamberLin F i i (e (F i)) = chamberLin F l i (x.1 l i) := by
  refine Subtype.ext ?_
  rw [IsIdempotentElem.corner_val_mul, IsIdempotentElem.corner_val_mul, chamberLin_val,
    chamberLin_val, chamberLin_val, Matrix.single_mul_mul_single]
  simp only [e_mul_e_self', ChamberAlgebra.mul_e, ChamberAlgebra.e_mul]

/-- Every element is the sum of its entries. -/
theorem eq_sum_chamberLin (x : ChamberAlgebra k F) :
    x = ∑ j, ∑ i, chamberLin F j i (x.1 j i) := by
  let v : ChamberAlgebra k F →+ Matrix ι ι (GalleryAlgebra k Δ ν) :=
    ⟨⟨fun x => x.1, rfl⟩, fun _ _ => rfl⟩
  refine Subtype.ext ?_
  change v x = v (∑ j, ∑ i, chamberLin F j i (x.1 j i))
  simp only [map_sum]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (v x)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  change Matrix.single j i (x.1 j i) = (chamberLin F j i (x.1 j i)).1
  rw [chamberLin_val, ChamberAlgebra.e_mul, ChamberAlgebra.mul_e]

/-- The entries of an element of a subalgebra containing the idempotents lie in it. -/
theorem chamberLin_mem_of_mem {S : Subalgebra k (ChamberAlgebra k F)}
    (hidem : ∀ j, chamberLin F j j (e (F j)) ∈ S) {M : Matrix ι ι (GalleryAlgebra k Δ ν)}
    (hM : chamberElt k F M ∈ S) (l i : ι) : chamberLin F l i (M l i) ∈ S := by
  have h := S.mul_mem (S.mul_mem (hidem l) hM) (hidem i)
  rw [chamberLin_e_mul_mul, chamberElt_val_apply, chamberLin_mul_e, chamberLin_e_mul] at h
  exact h

/-- Galleries of good words with the same end points give the same entry modulo elements with
fewer steps. -/
theorem chamberLin_mem_of_flips_eq {S : Subalgebra k (ChamberAlgebra k F)} (hD : Δ.Dagger)
    (hZ : Δ.NoZeroLoops) {N : ℕ}
    (hlow : ∀ M < N, ∀ y ∈ stepFilt k Δ ν M, ∀ j i, chamberLin F j i y ∈ S)
    {C : FullChamber Δ ν} {w w₂ : List (Hyp Δ ν)} (hw : GoodWord C.1 w)
    (hw₂ : GoodWord C.1 w₂) (he : C.flips w = C.flips w₂) (hN : w.length ≤ N)
    {y : GalleryAlgebra k Δ ν} (hy : y ∈ stepFilt k Δ ν 0) {j i : ι}
    (h₂ : chamberLin F j i (y * galList k C w₂) ∈ S) :
    chamberLin F j i (y * galList k C w) ∈ S := by
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

/-- **Generation of a chamber algebra.** By the spanning half of Theorem 2.8, a subalgebra
containing the polynomials on the diagonal, and, given the elements with fewer steps, the entries
`(j, i)` of `r g E * galList (F i) w` for good words `w` from `F i` to `E` with `g • E = F j`,
contains every entry of every element of the gallery algebra. -/
theorem chamberLin_mem_of_r_galList {S : Subalgebra k (ChamberAlgebra k F)} (hD : Δ.Dagger)
    (hZ : Δ.NoZeroLoops) (hpoly : ∀ j (f : PolyRing ν k), chamberLin F j j (poly f) ∈ S)
    (hrg : ∀ N, (∀ M < N, ∀ y ∈ stepFilt k Δ ν M, ∀ j i, chamberLin F j i y ∈ S) →
      ∀ (i j : ι) (g : ColPerm ν) (w : List (Hyp Δ ν)), GoodWord (F i).1 w → w.length ≤ N →
        g • (F i).flips w = F j →
        chamberLin F j i (r g ((F i).flips w) * galList k (F i) w) ∈ S) (N : ℕ) :
    ∀ y ∈ stepFilt k Δ ν N, ∀ j i, chamberLin F j i y ∈ S := by
  choose P hP using exists_isChamberSegment (Γ := Δ) (ν := ν) hD hZ
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro y hy j i
  have hy' := stepFilt_le_segSpan (one_mem_segSpan hP)
    (fun M hM C E E₁ hl => t_mul_segGallery_mem hP hD hZ M hM C E E₁ hl) N hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, C, E, hl, rfl⟩ := hx
    by_cases hC : C = F i
    swap
    · have h0 : segGallery (k := k) P C E * e (F i) = 0 := by
        rw [segGallery, ← galList_mul_e, mul_assoc, e_mul_e_of_ne hC, mul_zero]
      rw [← chamberLin_mul_e, mul_assoc, h0, mul_zero, map_zero]
      exact S.zero_mem
    subst hC
    by_cases hg : g • E = F j
    swap
    · have h0 : e (F j) * (poly f * r g E * segGallery (k := k) P (F i) E) = 0 := by
        rw [← mul_assoc, ← mul_assoc, e_mul_poly, mul_assoc (poly f),
          e_mul_r_of_ne (Ne.symm hg), mul_zero, zero_mul]
      rw [← chamberLin_e_mul, h0, map_zero]
      exact S.zero_mem
    have hsplit : chamberLin F j i (poly f * r g E * segGallery P (F i) E) =
        chamberLin F j j (poly f) * chamberLin F j i (r g E * segGallery P (F i) E) := by
      rw [chamberLin_mul_chamberLin, ← e_mul_poly, mul_assoc (e _), chamberLin_e_mul, mul_assoc]
    rw [hsplit]
    refine S.mul_mem (hpoly j f) ?_
    have hw := (goodWord_flips_word (hP (F i) E).1 (hP (F i) E).2.1).1
    have := hrg N IH i j g _ hw hl (by rw [flips_segWord hP]; exact hg)
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

end ChamberLin

end Categorification.WeightedKLR

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv Segment MvPolynomial FullChamber GalleryAlgebra

/-! ### Relabellings of the strands of `ν̃` as relabellings of the strands of a sequence -/

section Lift

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "s₀" => GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)

/-- A relabelling fixes the `0`-strand, which is alone in its colour. -/
theorem colPerm_zeroStrand (g : ColPerm ν̃) : g.1 s₀ = s₀ :=
  GalleryAlgebra.eq_of_fst_eq (GalleryAlgebra.redWeight_zeroStrand _) (ColPerm.apply_fst g _)

/-- The relabelling of a black strand by `g`; red strands are fixed. -/
def liftFun (g : ColPerm ν̃) (s : Strand μ) : Strand μ := (ofTilde (g.1 (toTilde s))).getD s

theorem liftFun_of_not_isLeft (g : ColPerm ν̃) {s : Strand μ} (hs : ¬ s.1.1.isLeft) :
    liftFun g s = s := by
  rw [liftFun, toTilde_of_not_isLeft hs, colPerm_zeroStrand, ofTilde_zeroStrand]
  rfl

theorem exists_ofTilde_colPerm (g : ColPerm ν̃) {s : Strand μ} (hs : s.1.1.isLeft) :
    ∃ t : Strand μ, ofTilde (g.1 (toTilde s)) = some t := by
  refine exists_ofTilde_of_ne fun h => toTilde_ne_zeroStrand hs ?_
  rw [← colPerm_zeroStrand g] at h
  exact g.1.injective h

theorem isLeft_liftFun (g : ColPerm ν̃) {s : Strand μ} (hs : s.1.1.isLeft) :
    (liftFun g s).1.1.isLeft := by
  obtain ⟨t, ht⟩ := exists_ofTilde_colPerm g hs
  rw [liftFun, ht, Option.getD_some]
  exact isLeft_of_ofTilde ht

theorem toTilde_liftFun (g : ColPerm ν̃) (s : Strand μ) :
    toTilde (liftFun g s) = g.1 (toTilde s) := by
  by_cases hs : s.1.1.isLeft
  · obtain ⟨t, ht⟩ := exists_ofTilde_colPerm g hs
    rw [liftFun, ht, Option.getD_some]
    exact toTilde_of_ofTilde ht
  · rw [liftFun_of_not_isLeft g hs, toTilde_of_not_isLeft hs, colPerm_zeroStrand]

theorem isLeft_liftFun_iff (g : ColPerm ν̃) (s : Strand μ) :
    (liftFun g s).1.1.isLeft ↔ s.1.1.isLeft := by
  refine ⟨fun h => ?_, isLeft_liftFun g⟩
  by_contra hs
  rw [liftFun_of_not_isLeft g hs] at h
  exact hs h

/-- `liftFun g` is determined by its values on the black strands. -/
theorem liftFun_eq_of {g : ColPerm ν̃} {s t : Strand μ}
    (h₁ : s.1.1.isLeft → t.1.1.isLeft ∧ toTilde t = g.1 (toTilde s))
    (h₂ : ¬ s.1.1.isLeft → t = s) : liftFun g s = t := by
  by_cases hs : s.1.1.isLeft
  · obtain ⟨ht, he⟩ := h₁ hs
    exact eq_of_toTilde_eq ht ((toTilde_liftFun g s).trans he.symm)
  · rw [liftFun_of_not_isLeft g hs, h₂ hs]

theorem liftFun_injective (g : ColPerm ν̃) : Function.Injective (liftFun (ℓ := ℓ) g) := by
  intro s t h
  by_cases hs : s.1.1.isLeft
  · have ht : t.1.1.isLeft := by
      rw [← isLeft_liftFun_iff g, ← h]
      exact isLeft_liftFun g hs
    have := congrArg toTilde h
    rw [toTilde_liftFun, toTilde_liftFun] at this
    exact (toTilde_inj hs ht).1 (g.1.injective this)
  · have ht : ¬ t.1.1.isLeft := by
      rw [← isLeft_liftFun_iff g, ← h, isLeft_liftFun_iff]
      exact hs
    rwa [liftFun_of_not_isLeft g hs, liftFun_of_not_isLeft g ht] at h

/-- **The relabelling `g` of the strands of `ν̃` as a permutation of the strands of a Stendhal
sequence**, fixing the red strands. -/
noncomputable def liftPerm (g : ColPerm ν̃) : Perm (Strand μ) :=
  Equiv.ofBijective (liftFun g) (Finite.injective_iff_bijective.1 (liftFun_injective g))

theorem liftPerm_apply (g : ColPerm ν̃) (s : Strand μ) : liftPerm g s = liftFun g s := rfl

theorem liftPerm_redStrand (g : ColPerm ν̃) (r : Fin ℓ) :
    liftPerm g (redStrand ν r) = redStrand ν r :=
  liftFun_of_not_isLeft g (not_isLeft_redStrand r)

theorem liftPerm_fst (g : ColPerm ν̃) (s : Strand μ) : (liftPerm g s).1 = s.1 := by
  by_cases hs : s.1.1.isLeft
  · refine fst_eq_of_toTilde (isLeft_liftFun g hs) hs ?_
    rw [liftPerm_apply, toTilde_liftFun, ColPerm.apply_fst]
  · rw [liftPerm_apply, liftFun_of_not_isLeft g hs]

theorem liftPerm_one (s : Strand μ) : liftPerm (1 : ColPerm ν̃) s = s :=
  liftFun_eq_of (fun hs => ⟨hs, rfl⟩) fun _ => rfl

/-- A relabelling fixing all strands of a sequence is the identity. -/
theorem eq_one_of_liftPerm {g : ColPerm ν̃} (h : ∀ s : Strand μ, liftPerm g s = s) : g = 1 := by
  refine Subtype.ext (Equiv.ext fun t => ?_)
  by_cases ht : t = s₀
  · subst ht
    exact colPerm_zeroStrand g
  · obtain ⟨s, hs⟩ := exists_ofTilde_of_ne (ℓ := ℓ) ht
    have e := toTilde_liftFun g s
    rw [← liftPerm_apply, h, toTilde_of_ofTilde hs] at e
    exact e.symm

end Lift

/-! ### The permutation of positions of a relabelling -/

section Positions

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- The permutation of positions `a ↦ pos_j(g(strand_i(a)))` of a relabelling `g` from the
strands of `i` to those of `j`, the red strands being fixed. -/
noncomputable def posPerm (i j : KLR.Seq (stendhalWeight ℓ ν)) (g : ColPerm ν̃) : Perm (Fin m) :=
  i.strandEquiv.trans ((liftPerm g).trans j.strandEquiv.symm)

theorem posPerm_apply (i j : KLR.Seq (stendhalWeight ℓ ν)) (g : ColPerm ν̃) (a : Fin m) :
    posPerm i j g a = j.posOf (liftPerm g (i.strandAt a)) := rfl

theorem eq_of_posPerm_eq_one {i j : KLR.Seq (stendhalWeight ℓ ν)} {g : ColPerm ν̃}
    (h : posPerm i j g = 1) : j = i ∧ g = 1 := by
  have ha : ∀ a, j.posOf (liftPerm g (i.strandAt a)) = a := fun a => by
    rw [← posPerm_apply, h, Perm.one_apply]
  have hji : j = i := by
    refine Subtype.ext (funext fun a => ?_)
    conv_lhs => rw [← ha a]
    rw [KLR.Seq.label_posOf, Strand.label, liftPerm_fst]
    rfl
  subst hji
  refine ⟨rfl, eq_one_of_liftPerm (ℓ := ℓ) fun t => ?_⟩
  have := congrArg j.strandAt (ha (j.posOf t))
  rwa [KLR.Seq.strandAt_posOf, KLR.Seq.strandAt_posOf] at this

theorem posPerm_smul_of_ne {i j : KLR.Seq (stendhalWeight ℓ ν)} {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ ≠ i.1 ⟨n + 1, h⟩) (g : ColPerm ν̃) :
    posPerm (TypeA.sadj m n • i) j g = posPerm i j g * TypeA.sadj m n := by
  refine Equiv.ext fun b => ?_
  rw [Perm.mul_apply, posPerm_apply, posPerm_apply]
  congr 2
  have := KLR.Seq.strandAt_smul i (TypeA.sadj m n) (KLR.Seq.lt_sadj_iff i h hc)
    (TypeA.sadj m n b)
  rwa [← Perm.mul_apply, TypeA.sadj_mul_self, Perm.one_apply] at this

theorem liftPerm_mul_refl (i : KLR.Seq (stendhalWeight ℓ ν)) {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) (g : ColPerm ν̃) (s : Strand μ) :
    liftPerm (g * (stDiag i n h hc).refl) s =
      liftPerm g (swap (i.strandAt ⟨n, by omega⟩) (i.strandAt ⟨n + 1, h⟩) s) := by
  set u := i.strandAt ⟨n, by omega⟩
  set v := i.strandAt ⟨n + 1, h⟩
  have hu : u.1.1.isLeft := isLeft_of_eq h hc
  have hv : v.1.1.isLeft := by
    show (i.1 ⟨n + 1, h⟩).isLeft
    rw [← hc]
    exact isLeft_of_eq h hc
  refine liftFun_eq_of (fun hs => ⟨?_, ?_⟩) fun hs => ?_
  · refine isLeft_liftFun g ?_
    rcases eq_or_ne s u with rfl | h1
    · rw [swap_apply_left]; exact hv
    rcases eq_or_ne s v with rfl | h2
    · rw [swap_apply_right]; exact hu
    · rw [swap_apply_of_ne_of_ne h1 h2]; exact hs
  · rw [liftPerm_apply, toTilde_liftFun]
    show g.1 (toTilde (swap u v s)) = g.1 (swap (toTilde u) (toTilde v) (toTilde s))
    congr 1
    rcases eq_or_ne s u with rfl | h1
    · rw [swap_apply_left, swap_apply_left]
    rcases eq_or_ne s v with rfl | h2
    · rw [swap_apply_right, swap_apply_right]
    · rw [swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne
        (fun e => h1 (eq_of_toTilde_eq hu e)) (fun e => h2 (eq_of_toTilde_eq hv e))]
  · have h1 : s ≠ u := fun e => hs (e ▸ hu)
    have h2 : s ≠ v := fun e => hs (e ▸ hv)
    rw [swap_apply_of_ne_of_ne h1 h2, liftPerm_apply, liftFun_of_not_isLeft g hs]

theorem posPerm_smul_of_eq {i j : KLR.Seq (stendhalWeight ℓ ν)} {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) (g : ColPerm ν̃) :
    posPerm (TypeA.sadj m n • i) j (g * (stDiag i n h hc).refl) =
      posPerm i j g * TypeA.sadj m n := by
  refine Equiv.ext fun b => ?_
  rw [Perm.mul_apply, posPerm_apply, posPerm_apply, KLR.Seq.sadj_smul_of_eq i h hc,
    liftPerm_mul_refl i h hc]
  congr 2
  have := congrArg i.strandAt (KLR.Seq.posOf_swap i h (i.strandAt b))
  rwa [KLR.Seq.strandAt_posOf, KLR.Seq.posOf_strandAt] at this

end Positions

/-! ### Signs of the relabelled Stendhal chambers -/

section Signs

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "Γλ" => WeightedGraph.crawleyBoeveyIn Γ Λ ϖ
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [IsStrictOrderedRing 𝕜] in
theorem redPosOf_comp_liftPerm (π : Strand μ → ℕ) (g : ColPerm ν̃) :
    redPosOf ν (π ∘ liftPerm g) = redPosOf ν π :=
  funext fun r => by simp [redPosOf, liftPerm_redStrand]

omit [IsStrictOrderedRing 𝕜] in
/-- Relabelling the loading of `π` by `g⁻¹` gives the loading of `π ∘ g`. -/
theorem act_inv_stCfg (g : ColPerm ν̃) (M : ℕ) (π : Strand μ → ℕ) :
    act g⁻¹ (stCfg ϖ M π) = stCfg ϖ M (π ∘ liftPerm g) := by
  funext t
  show stCfg ϖ M π ((g⁻¹).1⁻¹ t) = _
  rw [Subgroup.coe_inv, inv_inv]
  by_cases ht : t = GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)
  · subst ht
    rw [colPerm_zeroStrand, stCfg, stCfg, ofTilde_zeroStrand]
    rfl
  · obtain ⟨s, hs⟩ := exists_ofTilde_of_ne (ℓ := ℓ) ht
    have hsb := isLeft_of_ofTilde hs
    have ht' : t = toTilde s := (toTilde_of_ofTilde hs).symm
    rw [stCfg_some hs, ht', ← toTilde_liftFun,
      stCfg_some (ofTilde_toTilde_inl (isLeft_liftFun g hsb)), redPosOf_comp_liftPerm]
    rfl

theorem IsAdm.comp_liftPerm {M : ℕ} {π : Strand μ → ℕ} (hπ : IsAdm ν M π) (g : ColPerm ν̃) :
    IsAdm ν M (π ∘ liftPerm g) where
  inj := hπ.inj.comp (liftPerm g).injective
  lt _ := hπ.lt _
  red := by rw [redPosOf_comp_liftPerm]; exact hπ.red

/-- The signs of the relabelling `g⁻¹ • stFull j`: the positions in `j` of the relabelled
strands. -/
theorem inv_smul_stFull_eq_true_iff (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (j : OrdSeq ℓ ν) (g : ColPerm ν̃) {x : Hyp Γλ ν̃} {a b : Strand μ} (hl : Lifts ν x a b) :
    (g⁻¹ • stFull Λ hϖ hw0 j).1 x = true ↔
      posVal j.1 (liftPerm g a) < posVal j.1 (liftPerm g b) := by
  rw [stFull, smul_ofPoint]
  show decide (0 < x.val (act g⁻¹ (stCfg ϖ m (posVal j.1)))) = true ↔ _
  rw [act_inv_stCfg, decide_eq_true_iff,
    pos_iff_of_lifts hϖ hw0 ((isAdm_posVal j.2).comp_liftPerm g) hl]
  rfl

/-- If `g • E = stFull j` and the strands `u, v`, in this order in `i`, are in the other order in
`j` after relabelling, then `E` and `stFull i` lie on different sides of every hyperplane
comparing `u` and `v`. -/
theorem stFull_ne_of_descent (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    {i j : OrdSeq ℓ ν} {g : ColPerm ν̃} {E : FullChamber Γλ ν̃}
    (hg : g • E = stFull Λ hϖ hw0 j) {u v : Strand μ} (huv : posVal i.1 u < posVal i.1 v)
    (hd : posVal j.1 (liftPerm g v) < posVal j.1 (liftPerm g u)) {x : Hyp Γλ ν̃}
    (hx : Crosses ν u v x) : E.1 x ≠ (stFull Λ hϖ hw0 i).1 x := by
  have hE : E = g⁻¹ • stFull Λ hϖ hw0 j := by rw [← hg, inv_smul_smul]
  obtain ⟨a, b, hl, hor⟩ := hx
  have h1 := inv_smul_stFull_eq_true_iff hϖ hw0 j g hl
  have h2 := stFull_eq_true_iff hϖ hw0 i hl
  rw [hE]
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro he
    have := h2.2 huv
    rw [← he] at this
    have := h1.1 this
    omega
  · intro he
    have := h1.2 hd
    rw [he] at this
    have := h2.1 this
    omega

end Signs

/-! ### Generation of the chamber algebra -/

section Generation

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}
  (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "Γλ" => WeightedGraph.crawleyBoeveyIn Γ Λ ϖ
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [DecidableEq I] in
theorem crossSign_mul_self (a b : I ⊕ Fin ℓ) :
    crossSign k Λ a b * crossSign k Λ a b = 1 := by
  rcases a with a | r <;> rcases b with b | r' <;> simp [crossSign, ← mul_pow]

theorem chamberElt_stGenMat_idem (j : OrdSeq ℓ ν) :
    chamberElt k _ (stGenMat k Λ hϖ hw0 (.idem j.1)) =
      chamberLin (stFull Λ hϖ hw0) j j (e (stFull Λ hϖ hw0 j)) := by
  refine Subtype.ext ?_
  ext l i
  rw [chamberElt_val_apply, chamberLin_val, Matrix.single_apply]
  simp only [stGenMat, Matrix.diagonal_apply]
  rcases eq_or_ne l j with rfl | hl
  · rcases eq_or_ne l i with rfl | hi
    · simp
    · simp [hi]
  · have hl' : l.1 ≠ j.1 := fun h => hl (Subtype.ext h)
    simp [hl', Ne.symm hl]

variable {hϖ hw0}
variable {S : Subalgebra k (ChamberAlgebra k (stFull (ν := ν) Λ hϖ hw0))}
  (hgen : ∀ g, chamberElt k _ (stGenMat k Λ hϖ hw0 g) ∈ S)
include hgen

theorem chamberLin_e_mem (j : OrdSeq ℓ ν) :
    chamberLin (stFull Λ hϖ hw0) j j (e (stFull Λ hϖ hw0 j)) ∈ S := by
  rw [← chamberElt_stGenMat_idem]
  exact hgen _

theorem chamberLin_poly_mem (hz : stZeroDot ν k Λ hϖ hw0 ∈ S) (j : OrdSeq ℓ ν)
    (f : PolyRing ν̃ k) : chamberLin (stFull Λ hϖ hw0) j j (poly f) ∈ S := by
  have hidem := chamberLin_e_mem hgen
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : (poly (MvPolynomial.C a) : GalleryAlgebra k Γλ ν̃) = a • 1 := by
      rw [← polyHom_apply, MvPolynomial.C_eq_smul_one, map_smul, map_one]
    rw [this, map_smul]
    refine S.smul_mem ?_ a
    rw [← chamberLin_mul_e, one_mul]
    exact hidem j
  | add p q hp hq =>
    rw [← polyHom_apply, map_add, polyHom_apply, polyHom_apply, map_add]
    exact S.add_mem hp hq
  | mul_X p t hp =>
    have hX : chamberLin (stFull Λ hϖ hw0) j j (poly (X t)) ∈ S := by
      by_cases ht : t = GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν)
      · subst ht
        have h := chamberLin_mem_of_mem hidem
          (M := Matrix.diagonal fun _ => poly (X (GalleryAlgebra.zeroStrand _))) hz j j
        rwa [Matrix.diagonal_apply_eq] at h
      · obtain ⟨s, hs⟩ := exists_ofTilde_of_ne (ℓ := ℓ) ht
        have h := chamberLin_mem_of_mem hidem (hgen (.dot (j.1.posOf s))) j j
        simp only [stGenMat, Matrix.diagonal_apply_eq, KLR.Seq.strandAt_posOf] at h
        rwa [toTilde_of_ofTilde hs] at h
    have : chamberLin (stFull Λ hϖ hw0) j j (poly (p * X t)) =
        chamberLin (stFull Λ hϖ hw0) j j (poly p) *
          chamberLin (stFull Λ hϖ hw0) j j (poly (X t)) := by
      rw [chamberLin_mul_chamberLin, mul_assoc, e_mul_poly, ← mul_assoc, chamberLin_mul_e,
        ← polyHom_apply, ← polyHom_apply, ← polyHom_apply, map_mul]
    rw [this]
    exact S.mul_mem hp hX

theorem chamberLin_stCross_mem {i i' : OrdSeq ℓ ν} {n : ℕ} (h : n + 1 < m)
    (hi' : i'.1 = TypeA.sadj m n • i.1) :
    chamberLin (stFull Λ hϖ hw0) i' i (stCross k Λ hϖ hw0 i n h) ∈ S := by
  have hm := chamberLin_mem_of_mem (chamberLin_e_mem hgen) (hgen (.cross n)) i' i
  simpa only [stGenMat, h, ↓reduceDIte, Matrix.of_apply, hi', ↓reduceIte] using hm

end Generation

end Categorification.Stendhal
