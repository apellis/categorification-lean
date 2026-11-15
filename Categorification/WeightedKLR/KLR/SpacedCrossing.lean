/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.KLR.Crossing
import Categorification.WeightedKLR.KLR.Faithful
import Categorification.WeightedKLR.KLR.Loadings
import Categorification.KLR.PolyRep.Defs
import Categorification.WeightedKLR.Standing

/-!
# Crossings of the evenly spaced loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Proposition 2.14.
-/

namespace Categorification.KLR.Seq

open Categorification.WeightedKLR Equiv

variable {I : Type*} [DecidableEq I] {ν : Multiset I}

local notation "m" => Multiset.card ν

theorem strand_ext {s t : Strand (Multiset.toFinsupp ν)} (h₁ : s.1 = t.1)
    (h₂ : s.2.val = t.2.val) : s = t :=
  Sigma.ext h₁ ((Fin.heq_ext_iff (by rw [h₁])).2 h₂)

/-- A permutation of positions preserving the order of the positions of each colour moves the
strands with the positions. -/
theorem strandAt_smul (i : Seq ν) (σ : Perm (Fin m))
    (hσ : ∀ a b, i.1 a = i.1 b → (σ a < σ b ↔ a < b)) (a : Fin m) :
    (σ • i).strandAt (σ a) = i.strandAt a := by
  refine strand_ext (Subtype.ext (by simp [strandAt])) ?_
  show (σ • i).rank (σ a) = i.rank a
  unfold rank
  refine Finset.card_bij' (fun b _ => σ.symm b) (fun b _ => σ b) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, smul_apply,
      symm_apply_apply] at hb ⊢
    refine ⟨?_, hb.2⟩
    have := (hσ (σ.symm b) a hb.2).1
    rw [apply_symm_apply] at this
    exact this hb.1
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, smul_apply,
      symm_apply_apply] at hb ⊢
    exact ⟨(hσ b a hb.2).2 hb.1, hb.2⟩
  · intro b _; exact apply_symm_apply σ b
  · intro b _; exact symm_apply_apply σ b

theorem posOf_smul (i : Seq ν) (σ : Perm (Fin m))
    (hσ : ∀ a b, i.1 a = i.1 b → (σ a < σ b ↔ a < b)) (t : Strand (Multiset.toFinsupp ν)) :
    (σ • i).posOf t = σ (i.posOf t) := by
  conv_lhs => rw [← i.strandAt_posOf t, ← strandAt_smul i σ hσ]
  exact posOf_strandAt _ _

omit [DecidableEq I] in
theorem lt_sadj_iff (i : Seq ν) {n : ℕ} (h : n + 1 < m)
    (hne : i.1 ⟨n, by omega⟩ ≠ i.1 ⟨n + 1, h⟩) (c d : Fin m) (hcd : i.1 c = i.1 d) :
    TypeA.sadj m n c < TypeA.sadj m n d ↔ c < d := by
  have hs : TypeA.sadj m n = swap ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
    simp only [TypeA.sadj, h, ↓reduceDIte]
  rw [hs, Fin.lt_def, Fin.lt_def]
  refine lt_comp_swap_iff (π := fun x : Fin m => x.val) Fin.val_injective rfl ?_
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hne hcd
  · exact hne hcd.symm

omit [DecidableEq I] in
theorem sadj_smul_of_eq (i : Seq ν) {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) : TypeA.sadj m n • i = i := by
  have hs : TypeA.sadj m n = swap ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
    simp only [TypeA.sadj, h, ↓reduceDIte]
  apply Subtype.ext
  funext c
  show i.1 ((TypeA.sadj m n).symm c) = i.1 c
  rw [hs, symm_swap, swap_apply_def]
  split_ifs with h1 h2
  · rw [h1]; exact hc.symm
  · rw [h2]; exact hc
  · rfl

theorem posOf_swap (i : Seq ν) {n : ℕ} (h : n + 1 < m) (t : Strand (Multiset.toFinsupp ν)) :
    i.posOf (swap (i.strandAt ⟨n, by omega⟩) (i.strandAt ⟨n + 1, h⟩) t) =
      TypeA.sadj m n (i.posOf t) := by
  have hs : TypeA.sadj m n = swap ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
    simp only [TypeA.sadj, h, ↓reduceDIte]
  conv_lhs => rw [← i.strandAt_posOf t, i.strandAt_injective.swap_apply]
  rw [posOf_strandAt, hs]

end Categorification.KLR.Seq

namespace Categorification.WeightedKLR

open Equiv Segment MvPolynomial FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : Multiset I}

local notation "m" => Multiset.card ν

namespace WeightedGraph

variable (Γ) in
/-- A spacing larger than every `|ϑ_e|`. -/
def spacing : 𝕜 := 1 + ∑ e, |Γ.weight e|

omit [DecidableEq I] in
theorem spacing_pos : 0 < Γ.spacing := by
  have := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => abs_nonneg (Γ.weight e)
  unfold spacing
  linarith

omit [DecidableEq I] in
theorem abs_weight_lt_spacing (e : Γ.E) : |Γ.weight e| < Γ.spacing := by
  have := Finset.single_le_sum (fun e (_ : e ∈ Finset.univ) => abs_nonneg (Γ.weight e))
    (Finset.mem_univ e)
  unfold spacing
  linarith

variable (Γ) in
/-- The product of the polynomials `Q_e` over the edges `e : a → b`. -/
noncomputable def edgeProd (a b : I) : MvPolynomial (Fin 2) k :=
  ∏ e ∈ Finset.univ.filter (fun e => Γ.tail e = a ∧ Γ.head e = b), Γ.Q e

end WeightedGraph

variable (Γ) in
/-- The full chamber of the evenly spaced loadings `B_s(i)`. -/
noncomputable abbrev spacedFull (i : KLR.Seq ν) : FullChamber Γ (Multiset.toFinsupp ν) :=
  (KLR.Seq.spacedChamber Γ i).toFull

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem spacedPos_eq_spacedConfig (s : 𝕜) (i : KLR.Seq ν) :
    i.spacedPos s = spacedConfig s (fun t => (i.posOf t : ℕ)) := rfl

theorem injective_posOf_val (i : KLR.Seq ν) :
    Function.Injective (fun t : Strand (Multiset.toFinsupp ν) => (i.posOf t : ℕ)) :=
  Fin.val_injective.comp i.posOf_injective

/-- The full chamber of `B_s(i)` is `spacedFull Γ i`. -/
theorem fullSigns_spacedPos (i : KLR.Seq ν) :
    fullSigns (Γ := Γ) (i.spacedPos Γ.spacing) = (spacedFull Γ i).1 := by
  rw [spacedPos_eq_spacedConfig, fullSigns_spacedConfig WeightedGraph.spacing_pos
    WeightedGraph.abs_weight_lt_spacing (injective_posOf_val i)]
  funext x
  rcases x with w | d
  · show decide _ = decide _
    simp only [Fin.lt_def]
  · show decide _ = true
    simp only [decide_eq_true_eq]
    exact Fin.lt_def.1 (i.posOf_lt_posOf d.2.1 d.2.2)

section Crossing


/-- The strand at position `n` of `i`. -/
abbrev leftStrand (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) : Strand (Multiset.toFinsupp ν) := i.strandAt ⟨n, by omega⟩

/-- The strand at position `n + 1` of `i`. -/
abbrev rightStrand (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) : Strand (Multiset.toFinsupp ν) := i.strandAt ⟨n + 1, h⟩

theorem leftStrand_ne_rightStrand (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) : leftStrand i n h ≠ rightStrand i n h := fun e => by
  have := i.strandAt_injective e
  simp [Fin.ext_iff] at this

variable (Γ) in
/-- The hyperplanes crossed when the strands at positions `n` and `n + 1` of `B_s(i)` are
exchanged along a straight segment. -/
noncomputable def crossWord (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) : List (Hyp Γ (Multiset.toFinsupp ν)) :=
  word (hypAff (Γ := Γ)) (i.spacedPos Γ.spacing)
    (i.spacedPos Γ.spacing ∘ swap (leftStrand i n h) (rightStrand i n h))

theorem posOf_rightStrand (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) :
    (i.posOf (rightStrand i n h) : ℕ) = (i.posOf (leftStrand i n h) : ℕ) + 1 := by
  simp

theorem mem_crossWord (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) {x : Hyp Γ (Multiset.toFinsupp ν)} :
    x ∈ crossWord Γ i n h ↔ x.JoinsPair (leftStrand i n h) (rightStrand i n h) := by
  rw [crossWord, word, List.mem_insertionSort, Finset.mem_toList, Finset.mem_filter,
    spacedPos_eq_spacedConfig, separates_spacedConfig_swap_iff WeightedGraph.spacing_pos
      WeightedGraph.abs_weight_lt_spacing (injective_posOf_val i) (posOf_rightStrand i n h)]
  simp

omit [IsStrictOrderedRing 𝕜] in
theorem nodup_crossWord (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) : (crossWord Γ i n h).Nodup := by
  rw [crossWord, word]
  exact (List.perm_insertionSort _ _).nodup_iff.2 (Finset.nodup_toList _)

theorem simple_crossWord (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Simple (hypAff (Γ := Γ)) (i.spacedPos Γ.spacing)
      (i.spacedPos Γ.spacing ∘ swap (leftStrand i n h) (rightStrand i n h)) := by
  rw [spacedPos_eq_spacedConfig]
  exact simple_spacedConfig_swap Γ hD hZ WeightedGraph.spacing_pos
    WeightedGraph.abs_weight_lt_spacing (injective_posOf_val i) (posOf_rightStrand i n h)

theorem goodWord_crossWord (i : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    GoodWord (spacedFull Γ i).1 (crossWord Γ i n h) ∧
      ((spacedFull Γ i).flips (crossWord Γ i n h)).1 =
        fullSigns (i.spacedPos Γ.spacing ∘ swap (leftStrand i n h) (rightStrand i n h)) :=
  goodWord_flips_word (simple_crossWord i n h hD hZ) (fullSigns_spacedPos i)

end Crossing

section Walls

variable {ν' : I →₀ ℕ}

/-- The polynomial by which crossing the hyperplane `x` from the side `σ` multiplies: the wall
polynomial when a wall is crossed from its negative side, and `1` otherwise. -/
noncomputable def wallCoeff : Hyp Γ ν' → Bool → PolyRing ν' k
  | .inl w, σ => if σ = false then w.factor else 1
  | .inr _, _ => 1

omit [IsStrictOrderedRing 𝕜] in
/-- A good word of walls acts by multiplication by the product of the polynomials of the walls
crossed from their negative side. -/
theorem opList_of_walls {C : FullChamber Γ ν'} {w : List (Hyp Γ ν')} (hw : GoodWord C.1 w)
    (hd : ∀ d, Sum.inr d ∉ w) :
    opList k Γ C w = LinearMap.mulLeft k (w.map fun x => wallCoeff x (C.1 x)).prod := by
  induction w generalizing C with
  | nil => refine LinearMap.ext fun f => ?_; simp [opList]
  | cons h w ih =>
    obtain ⟨hf, ha, hw'⟩ := hw.cons
    have hd' : ∀ d, Sum.inr d ∉ w := fun d hm => hd d (List.mem_cons_of_mem _ hm)
    rcases h with y | d
    · rw [opList, ih hw' hd', stepOp_inl ha, wallOp_eq_mulLeft]
      have hn := (List.nodup_cons.1 hw.1).1
      have hmap : (w.map fun x => wallCoeff (k := k) x ((C.flipH (.inl y)).1 x)) =
          w.map fun x => wallCoeff x (C.1 x) := by
        refine List.map_congr_left fun x hx => ?_
        rw [hf, FullChamber.flipSign]
        have : x ≠ .inl y := fun e => hn (e ▸ hx)
        simp [this]
      rw [hmap]
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, List.map_cons, List.prod_cons,
        wallCoeff]
      cases C.1 (.inl y)
      · simp
        ring
      · simp
    · exact absurd List.mem_cons_self (hd d)

omit [IsStrictOrderedRing 𝕜] in
open Classical in
/-- The walls joining two neighbouring strands `u` (left) and `v` (right), crossed from their
negative side when `u` and `v` are exchanged, contribute `∏ Q_e(y_v, y_u)` over the edges
`e : u → v`. -/
theorem prod_wallCoeff_joinsPair (C : FullChamber Γ ν') {u v : Strand ν'} (huv : u ≠ v)
    (h1 : ∀ w : Wall Γ ν', w.src = u → w.tgt = v → C.1 (.inl w) = true)
    (h2 : ∀ w : Wall Γ ν', w.src = v → w.tgt = u → C.1 (.inl w) = false) :
    ∏ x ∈ Finset.univ.filter (fun x : Hyp Γ ν' => x.JoinsPair u v), wallCoeff (k := k) x (C.1 x) =
      rename ![v, u] (Γ.edgeProd u.label v.label) := by
  classical
  rw [Finset.prod_filter, Fintype.prod_sum_type]
  have hD : ∏ d : Diag ν', (if Hyp.JoinsPair (Sum.inr d : Hyp Γ ν') u v then
      wallCoeff (k := k) (Sum.inr d : Hyp Γ ν') (C.1 (.inr d)) else 1) = 1 :=
    Finset.prod_eq_one fun d _ => by split_ifs <;> rfl
  rw [hD, mul_one]
  have hW : ∀ w : Wall Γ ν', (if Hyp.JoinsPair (Sum.inl w : Hyp Γ ν') u v then
      wallCoeff (k := k) (Sum.inl w : Hyp Γ ν') (C.1 (.inl w)) else 1) =
      if w.src = v ∧ w.tgt = u then w.factor else 1 := by
    intro w
    by_cases ha : w.src = u ∧ w.tgt = v
    · have hb : ¬ (w.src = v ∧ w.tgt = u) := fun hb => huv (ha.1.symm.trans hb.1)
      have hj : Hyp.JoinsPair (Sum.inl w : Hyp Γ ν') u v := Or.inl ha
      simp [hj, hb, h1 w ha.1 ha.2, wallCoeff]
    · by_cases hb : w.src = v ∧ w.tgt = u
      · have hj : Hyp.JoinsPair (Sum.inl w : Hyp Γ ν') u v := Or.inr hb
        simp [hj, hb, h2 w hb.1 hb.2, wallCoeff]
      · have hj : ¬ Hyp.JoinsPair (Sum.inl w : Hyp Γ ν') u v := by
          rintro (h | h)
          exacts [ha h, hb h]
        simp [hj, hb]
  simp only [hW]
  rw [← Finset.prod_filter, WeightedGraph.edgeProd, map_prod]
  refine Finset.prod_bij' (fun w _ => w.edge)
    (fun e he => (⟨(e, v, u), ⟨?_, ?_, huv.symm⟩⟩ : Wall Γ ν')) ?_ ?_ ?_ ?_ ?_
  · simpa using (Finset.mem_filter.1 he).2.2.symm
  · simpa using (Finset.mem_filter.1 he).2.1.symm
  · intro w hw
    obtain ⟨hs, ht⟩ := (Finset.mem_filter.1 hw).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by rw [← ht]; exact w.2.2.1.symm, by rw [← hs]; exact w.2.1.symm⟩
  · intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, rfl⟩
  · intro w hw
    obtain ⟨hs, ht⟩ := (Finset.mem_filter.1 hw).2
    apply Subtype.ext
    simp only
    rw [← hs, ← ht]
    rfl
  · intro e he
    rfl
  · intro w hw
    obtain ⟨hs, ht⟩ := (Finset.mem_filter.1 hw).2
    rw [Wall.factor_eq_rename, hs, ht]

end Walls

end Categorification.WeightedKLR
