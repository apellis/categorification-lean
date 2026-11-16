/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.KLR.SpacedSurjective
import Categorification.WeightedKLR.Loadings.Shift
import Categorification.WeightedKLR.Loadings.Family
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Weighted KLR algebras of trees

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Dependence on choice of loadings", Corollary 2.16: if `Γ` is a tree, the weighted KLR algebra
`W^ϑ_ν` is Morita equivalent to the KLR algebra `R(ν)`.

## The argument

Webster's proof is the combination of three facts, each formalized separately.

1. On a forest every weighting is a coboundary (`IsForest.exists_coboundary`): there is a
   `0`-chain `η` with `ϑ_e = η_{h(e)} - η_{t(e)}`. So by Proposition 2.15 (with the corrected sign,
   `weightedKLRShiftEquiv`) the weighted KLR algebra for `ϑ` is isomorphic to the one for the
   weighting `0`.
2. For the weighting `0` the ghost of a strand sits on the strand itself, so a wall is crossed
   exactly when two strands of adjacent colours are exchanged. Sorting the strands of an
   admissible loading by position gives a sequence `i` whose evenly spaced loading `B_s(i)` lies
   in the same chamber (`exists_spacedChamber_eq`). So every chamber, that is every idempotent of
   `W^0_ν`, is the chamber of some `B_s(i)`.
3. Proposition 2.14 (`spacedEquiv`): the weighted KLR algebra on the family of all evenly spaced
   loadings `(B_s(i))_{i ∈ Seq ν}` is the KLR algebra `R(ν)`.

Several sequences may give the same chamber (strands of colours without an edge between them can
be exchanged without crossing a wall), which is why the conclusion is Morita equivalence and not
isomorphism (the remark after the corollary in the source). Choosing one sequence per chamber
(`chamberSeq`) gives an idempotent `f = ∑_C e(i_C)` of `R(ν)` with `f R(ν) f ≅ W^ϑ_ν`
and `f` is full: `1 = ∑_i u_i f v_i` (`IsForest.exists_klrCorner`), the matrix units `u_i`, `v_i` moving `B_s(i)` to the chosen representative
of its chamber.

## The Morita statement

As in `Loadings.Family` (Proposition 2.11), Mathlib does not yet contain the criterion that a
corner at a full idempotent is Morita equivalent to the ring (it is a TODO in
`Mathlib.RingTheory.Morita.Basic`), so the Morita equivalence is recorded through its two
ring-theoretic ingredients: an isomorphism of `W^ϑ_ν` with the corner `f R(ν) f`, and the
identity `1 = ∑ u_i f v_i` (so `R(ν) f R(ν) = R(ν)`).

## Hypotheses

* `WeightedGraph.IsForest`: no edge is a loop, there is no loop polynomial (`loop = none`), no two
  edges join the same pair of vertices, and the underlying simple graph is acyclic.
  `WeightedGraph.IsTree` adds connectedness. Webster states the corollary for trees; the proof
  uses only acyclicity, so the results are stated for forests, with the tree case as a corollary.
* Assumption (†) is not an extra hypothesis: on a forest it holds for every weighting
  (`IsForest.dagger`), in particular for the shifted weighting `0`.
* Webster's standing hypothesis on the `Q_e` (`WeightedGraph.Standing`), which does not involve
  the weighting.
* The ground ring `k` is an arbitrary commutative ring, as in the source: the weighted KLR
  algebra is a full corner of the weighted KLR algebra on the evenly spaced loadings
  (`IsForest.exists_spacedCorner`), which is isomorphic to `R(ν)` (`spacedEquiv`).

## Main results

* `cornerCornerEquiv`, `matrixCornerSumEquiv`: generic facts on corners.
* `WeightedGraph.IsForest`, `WeightedGraph.IsTree`, `IsForest.exists_coboundary`,
  `IsForest.dagger`.
* `exists_spacedChamber_eq`: for the weighting `0`, every chamber is that of an evenly spaced
  loading.
* `weightedKLRChamberEquiv`, `spacedChamberIdem_full`: for the weighting `0`, `W^0_ν` is a full corner of
  the weighted KLR algebra on the evenly spaced loadings.
* `IsForest.exists_spacedCorner`: for a forest, over any commutative ring, `W^ϑ_ν` is a full
  corner of the weighted KLR algebra on the evenly spaced loadings of the shifted weighting.
* `IsForest.exists_klrCorner`: Corollary 2.16, for forests; `IsTree.exists_klrCorner`: the
  statement for trees.
-/

namespace Categorification.WeightedKLR

open GalleryAlgebra

/-! ### Corners -/

section Corner

variable {R : Type*} [Ring R]

/-- The underlying elements of a corner, as an additive homomorphism. -/
def cornerVal {e : R} (he : IsIdempotentElem e) : he.Corner →+ R where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem cornerVal_apply {e : R} (he : IsIdempotentElem e) (x : he.Corner) :
    cornerVal he x = x.1 := rfl

/-- A corner `f (e R e) f` of a corner `e R e` is the corner `f R f` of the ring. -/
def cornerCornerEquiv {e : R} {he : IsIdempotentElem e} {f : he.Corner}
    (hf : IsIdempotentElem f) (hf' : IsIdempotentElem f.1) : hf.Corner ≃+* hf'.Corner where
  toFun x := ⟨x.1.1, by
    have hx := (Subsemigroup.mem_corner_iff hf).1 x.2
    exact (Subsemigroup.mem_corner_iff hf').2
      ⟨congrArg Subtype.val hx.1, congrArg Subtype.val hx.2⟩⟩
  invFun y := by
    have hy := (Subsemigroup.mem_corner_iff hf').1 y.2
    have hfe := (Subsemigroup.mem_corner_iff he).1 f.2
    refine ⟨⟨y.1, (Subsemigroup.mem_corner_iff he).2 ⟨?_, ?_⟩⟩,
      (Subsemigroup.mem_corner_iff hf).2 ⟨Subtype.ext hy.1, Subtype.ext hy.2⟩⟩
    · rw [← hy.1, ← mul_assoc, hfe.1]
    · rw [← hy.2, mul_assoc, hfe.2]
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

section MatrixSum

variable {β : Type*} [Fintype β] [DecidableEq β] {d : β → R}

theorem isIdempotentElem_sum_of_mul_eq (hd : ∀ i j, d i * d j = if i = j then d i else 0) :
    IsIdempotentElem (∑ i, d i) := by
  rw [IsIdempotentElem, Finset.sum_mul_sum]
  simp [hd]

variable (hd : ∀ i j, d i * d j = if i = j then d i else 0)
include hd

theorem mul_eq_ite_of_mem_corner {M N : Matrix β β R}
    (hM : M ∈ Subsemigroup.corner (Matrix.diagonal d))
    (hN : N ∈ Subsemigroup.corner (Matrix.diagonal d)) (i j k l : β) (hjk : j ≠ k) :
    M i j * N k l = 0 := by
  have hD := isIdempotentElem_diagonal (d := d) fun i => by simpa using hd i i
  have hM' := ((mem_corner_diagonal_iff hD).1 hM i j).2
  have hN' := ((mem_corner_diagonal_iff hD).1 hN k l).1
  rw [← hM', ← hN', mul_assoc, ← mul_assoc (d j), hd, ite_eq_right hjk, zero_mul, mul_zero]

theorem left_mul_of_mem_corner {M : Matrix β β R}
    (hM : M ∈ Subsemigroup.corner (Matrix.diagonal d)) (a i j : β) :
    d a * M i j = if a = i then M i j else 0 := by
  have hD := isIdempotentElem_diagonal (d := d) fun i => by simpa using hd i i
  have hM' := ((mem_corner_diagonal_iff hD).1 hM i j).1
  split_ifs with h
  · subst h; exact hM'
  · rw [← hM', ← mul_assoc, hd, ite_eq_right h, zero_mul]

theorem right_mul_of_mem_corner {M : Matrix β β R}
    (hM : M ∈ Subsemigroup.corner (Matrix.diagonal d)) (i j a : β) :
    M i j * d a = if j = a then M i j else 0 := by
  have hD := isIdempotentElem_diagonal (d := d) fun i => by simpa using hd i i
  have hM' := ((mem_corner_diagonal_iff hD).1 hM i j).2
  split_ifs with h
  · subst h; exact hM'
  · rw [← hM', mul_assoc, hd, ite_eq_right h, mul_zero]

theorem diag_mul_sum_mul_diag {M : Matrix β β R}
    (hM : M ∈ Subsemigroup.corner (Matrix.diagonal d)) (i j : β) :
    d i * (∑ a, ∑ b, M a b) * d j = M i j := by
  simp only [Finset.mul_sum, Finset.sum_mul, left_mul_of_mem_corner hd hM]
  simp [ite_mul, right_mul_of_mem_corner hd hM]

theorem sum_entries_mul {M N : Matrix β β R}
    (hM : M ∈ Subsemigroup.corner (Matrix.diagonal d))
    (hN : N ∈ Subsemigroup.corner (Matrix.diagonal d)) :
    ∑ i, ∑ j, (M * N) i j = (∑ i, ∑ j, M i j) * ∑ i, ∑ j, N i j := by
  have h : ∀ i j, (∑ k, ∑ l, M i j * N k l) = ∑ l, M i j * N j l := fun i j =>
    Finset.sum_eq_single j (fun k _ hk => Finset.sum_eq_zero fun l _ =>
      mul_eq_ite_of_mem_corner hd hM hN i j k l (Ne.symm hk))
      fun h => absurd (Finset.mem_univ j) h
  calc ∑ i, ∑ j, (M * N) i j = ∑ i, ∑ j, ∑ k, M i k * N k j := rfl
    _ = ∑ i, ∑ k, ∑ j, M i k * N k j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ a, ∑ b, M i k * N a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => (h i k).symm
    _ = (∑ i, ∑ j, M i j) * ∑ i, ∑ j, N i j := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- For orthogonal idempotents `d i`, the corner of the matrix ring at `diag(d)` is the corner
of the ring at `∑ d i`: a matrix goes to the sum of its entries, and `a` goes to the matrix
`(d i a d j)_{i j}`. -/
noncomputable def matrixCornerSumEquiv (hD : IsIdempotentElem (Matrix.diagonal d))
    (hs : IsIdempotentElem (∑ i, d i)) : hD.Corner ≃+* hs.Corner where
  toFun M := ⟨∑ i, ∑ j, M.1 i j, (Subsemigroup.mem_corner_iff hs).2
    ⟨by simp [Finset.mul_sum, Finset.sum_mul, left_mul_of_mem_corner hd M.2],
      by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Finset.mul_sum, right_mul_of_mem_corner hd M.2]⟩⟩
  invFun a := ⟨Matrix.of fun i j => d i * a.1 * d j, (mem_corner_diagonal_iff hD).2 fun i j => by
    have hii : d i * d i = d i := by simpa using hd i i
    have hjj : d j * d j = d j := by simpa using hd j j
    simp only [Matrix.of_apply]
    exact ⟨by rw [← mul_assoc, ← mul_assoc, hii],
      by rw [mul_assoc, hjj]⟩⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    exact diag_mul_sum_mul_diag hd M.2 i j
  right_inv a := by
    apply Subtype.ext
    have ha := (Subsemigroup.mem_corner_iff hs).1 a.2
    show ∑ i, ∑ j, d i * a.1 * d j = a.1
    conv_rhs => rw [← ha.2, ← ha.1]
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  map_mul' M N := by
    apply Subtype.ext
    show ∑ i, ∑ j, (M.1 * N.1) i j = (∑ i, ∑ j, M.1 i j) * ∑ i, ∑ j, N.1 i j
    exact sum_entries_mul hd M.2 N.2
  map_add' M N := by
    apply Subtype.ext
    show ∑ i, ∑ j, (M.1 + N.1) i j = ∑ i, ∑ j, M.1 i j + ∑ i, ∑ j, N.1 i j
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib).trans Finset.sum_add_distrib

end MatrixSum

end Corner

/-! ### Forests and trees -/

namespace WeightedGraph

variable {I 𝕜 k : Type*} [CommRing k] (Γ : WeightedGraph I 𝕜 k)

/-- The simple graph on the vertices with an edge `{h(e), t(e)}` for each `e ∈ S`. -/
def edgeGraph (S : Set Γ.E) : SimpleGraph I :=
  SimpleGraph.fromRel fun i j => ∃ e ∈ S, Γ.head e = i ∧ Γ.tail e = j

/-- The underlying simple graph of `Γ`. -/
abbrev simpleGraph : SimpleGraph I := Γ.edgeGraph Set.univ

/-- `Γ` is a forest: no edge is a loop, there is no loop polynomial, no two edges join the same
pair of vertices (in either orientation), and the underlying simple graph is acyclic. -/
structure IsForest : Prop where
  head_ne_tail : ∀ e, Γ.head e ≠ Γ.tail e
  loop_eq_none : ∀ i, Γ.loop i = none
  edge_inj : ∀ e e', s(Γ.head e, Γ.tail e) = s(Γ.head e', Γ.tail e') → e = e'
  isAcyclic : Γ.simpleGraph.IsAcyclic

/-- `Γ` is a tree: a connected forest. -/
def IsTree : Prop := Γ.IsForest ∧ Γ.simpleGraph.Connected

variable {Γ}

theorem edgeGraph_adj {S : Set Γ.E} {i j : I} :
    (Γ.edgeGraph S).Adj i j ↔
      i ≠ j ∧ ((∃ e ∈ S, Γ.head e = i ∧ Γ.tail e = j) ∨ ∃ e ∈ S, Γ.head e = j ∧ Γ.tail e = i) :=
  SimpleGraph.fromRel_adj _ _ _

theorem edgeGraph_mono {S T : Set Γ.E} (h : S ⊆ T) : Γ.edgeGraph S ≤ Γ.edgeGraph T := by
  intro i j hij
  rw [edgeGraph_adj] at hij ⊢
  exact ⟨hij.1, hij.2.imp (fun ⟨e, he, h'⟩ => ⟨e, h he, h'⟩) fun ⟨e, he, h'⟩ => ⟨e, h he, h'⟩⟩

/-- On a forest every `1`-chain is a coboundary: for every `w : E → A` there is a `0`-chain
`η` with `η_{h(e)} - η_{t(e)} = w_e`. The proof adds the edges one at a time; the endpoints of a
new edge are not yet connected, so `η` can be shifted by a constant on the component of the
head. -/
theorem IsForest.exists_coboundary (hΓ : Γ.IsForest) {A : Type*} [AddCommGroup A]
    (w : Γ.E → A) : ∃ η : I → A, ∀ e, η (Γ.head e) - η (Γ.tail e) = w e := by
  classical
  suffices h : ∀ S : Finset Γ.E, ∃ η : I → A, ∀ e ∈ S, η (Γ.head e) - η (Γ.tail e) = w e by
    obtain ⟨η, hη⟩ := h Finset.univ
    exact ⟨η, fun e => hη e (Finset.mem_univ e)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert e₀ S he₀ ih =>
    obtain ⟨η, hη⟩ := ih
    set G := Γ.edgeGraph (S : Set Γ.E) with hG
    have hG' : (Γ.edgeGraph ((insert e₀ S : Finset Γ.E) : Set Γ.E)).IsAcyclic :=
      hΓ.isAcyclic.anti (edgeGraph_mono (Set.subset_univ _))
    have hadj : (Γ.edgeGraph ((insert e₀ S : Finset Γ.E) : Set Γ.E)).Adj (Γ.head e₀)
        (Γ.tail e₀) :=
      edgeGraph_adj.2 ⟨hΓ.head_ne_tail e₀, Or.inl ⟨e₀, by simp, rfl, rfl⟩⟩
    have hbr := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hG' hadj
    rw [SimpleGraph.isBridge_iff] at hbr
    have hnr : ¬ G.Reachable (Γ.head e₀) (Γ.tail e₀) := by
      refine fun hr => hbr (hr.mono ?_)
      intro i j h
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨edgeGraph_mono (by simp) h, ?_⟩
      rw [Set.mem_singleton_iff]
      intro hs
      obtain ⟨-, hor⟩ := edgeGraph_adj.1 h
      rcases hor with ⟨e, he, rfl, rfl⟩ | ⟨e, he, rfl, rfl⟩
      · exact he₀ (by rw [← hΓ.edge_inj e e₀ hs]; exact he)
      · exact he₀ (by rw [← hΓ.edge_inj e e₀ (Sym2.eq_swap.trans hs)]; exact he)
    let c := w e₀ - (η (Γ.head e₀) - η (Γ.tail e₀))
    refine ⟨fun i => η i + if G.Reachable (Γ.head e₀) i then c else 0, ?_⟩
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · simp only [SimpleGraph.Reachable.refl, ite_true, hnr, ite_false, c]
      abel
    · have hadjS : G.Adj (Γ.head e) (Γ.tail e) :=
        edgeGraph_adj.2 ⟨hΓ.head_ne_tail e, Or.inl ⟨e, he, rfl, rfl⟩⟩
      have hiff : G.Reachable (Γ.head e₀) (Γ.head e) ↔ G.Reachable (Γ.head e₀) (Γ.tail e) :=
        ⟨fun h => h.trans hadjS.reachable, fun h => h.trans hadjS.reachable.symm⟩
      by_cases hr : G.Reachable (Γ.head e₀) (Γ.head e)
      · simp only [hr, hiff.1 hr, ite_true]
        rw [← hη e he]
        abel
      · simp only [hr, mt hiff.2 hr, ite_false, add_zero]
        exact hη e he

/-- On a forest assumption (†) holds for every weighting: two edges with the same endpoints are
equal, and there is no bigon. -/
theorem IsForest.dagger [Neg 𝕜] (hΓ : Γ.IsForest) : Γ.Dagger := by
  refine ⟨fun e e' ht hh _ => hΓ.edge_inj e e' (by rw [ht, hh]), fun e e' ht hh => ?_⟩
  have := hΓ.edge_inj e e' (by rw [hh, ht, Sym2.eq_swap])
  subst this
  exact (hΓ.head_ne_tail e hh).elim

end WeightedGraph

/-! ### Weighting zero: every chamber contains an evenly spaced loading -/

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : Multiset I}

local notation "ν'" => Multiset.toFinsupp ν

/-- For the weighting `0`, every chamber is the chamber of the evenly spaced loading of a
sequence: list the strands of an admissible loading from left to right. -/
theorem exists_spacedChamber_eq (h0 : ∀ e, Γ.weight e = 0) (c : Chamber Γ ν') :
    ∃ i : KLR.Seq ν, KLR.Seq.spacedChamber Γ i = c := by
  obtain ⟨p, hp, hs⟩ := c.2
  let i₀ : KLR.Seq ν := ⟨fun a => ν.toList.get (Fin.cast (Multiset.length_toList ν).symm a), by
    rw [Fin.univ_val_map]
    conv_rhs => rw [← Multiset.coe_toList ν]
    congr 1
    apply List.ext_get
    · simp
    · intro n h1 h2; simp⟩
  let q : Fin (Multiset.card ν) → 𝕜 := fun a => p (i₀.strandAt a)
  have hq : Function.Injective q := hp.1.comp i₀.strandAt_injective
  let σ : Equiv.Perm (Fin (Multiset.card ν)) := (Tuple.sort q).symm
  have hσq : ∀ a b, σ a < σ b ↔ q a < q b := by
    have hmono : StrictMono (q ∘ Tuple.sort q) :=
      (Tuple.monotone_sort q).strictMono_of_injective (hq.comp (Tuple.sort q).injective)
    intro a b
    have := hmono.lt_iff_lt (a := σ a) (b := σ b)
    simpa [σ, Function.comp] using this.symm
  have key : ∀ a b, i₀.1 a = i₀.1 b → a < b → q a < q b := fun a b hc hab =>
    hp.2.1 _ _ (Subtype.ext hc) (i₀.rank_lt_rank hab hc)
  have hσ : ∀ a b, i₀.1 a = i₀.1 b → (σ a < σ b ↔ a < b) := by
    intro a b hc
    rw [hσq]
    refine ⟨fun h => ?_, key a b hc⟩
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact hab
    · exact absurd h (lt_irrefl _)
    · exact absurd (key b a hc.symm hab) (not_lt.2 h.le)
  refine ⟨σ • i₀, Subtype.ext ?_⟩
  rw [← hs]
  funext w
  have hq' : ∀ t, q (i₀.posOf t) = p t := fun t => by simp [q]
  simp only [KLR.Seq.spacedChamber, signs, Wall.val, h0, sub_zero,
    KLR.Seq.posOf_smul i₀ σ hσ, hσq, hq', sub_pos]

/-- For the weighting `0`, every rank-ordered full chamber is the full chamber of an evenly
spaced loading. -/
theorem exists_spacedFull_eq (h0 : ∀ e, Γ.weight e = 0) (C : RankChamber Γ ν') :
    ∃ i : KLR.Seq ν, spacedFull Γ i = C.1 := by
  obtain ⟨c, hc⟩ := Chamber.exists_toFull_eq C.1 C.2
  obtain ⟨i, hi⟩ := exists_spacedChamber_eq h0 c
  exact ⟨i, by rw [spacedFull, hi, hc]⟩

/-! ### Weighting zero: the Morita data -/

section Zero

variable (h0 : ∀ e, Γ.weight e = 0)

variable (ν) in
/-- A chosen sequence whose evenly spaced loading lies in a given rank-ordered full chamber. -/
noncomputable def chamberSeq (C : RankChamber Γ ν') : KLR.Seq ν :=
  (exists_spacedFull_eq h0 C).choose

theorem spacedFull_chamberSeq (C : RankChamber Γ ν') :
    spacedFull Γ (chamberSeq ν h0 C) = C.1 :=
  (exists_spacedFull_eq h0 C).choose_spec

theorem chamberSeq_injective : Function.Injective (chamberSeq (Γ := Γ) ν h0) := fun C D h =>
  Subtype.ext (by rw [← spacedFull_chamberSeq h0 C, h, spacedFull_chamberSeq])

variable (k ν) in
/-- The diagonal entries of the idempotent: `e(B_s(i))` for the chosen sequences `i`, and `0` for
the others. -/
noncomputable def chamberDiag (i : KLR.Seq ν) : GalleryAlgebra k Γ ν' :=
  if i ∈ Finset.univ.image (chamberSeq ν h0) then e (spacedFull Γ i) else 0

theorem chamberDiag_chamberSeq (C : RankChamber Γ ν') :
    chamberDiag k ν h0 (chamberSeq ν h0 C) = e C.1 := by
  rw [chamberDiag, ite_eq_left (Finset.mem_image_of_mem _ (Finset.mem_univ C)),
    spacedFull_chamberSeq]

theorem chamberDiag_mul (i j : KLR.Seq ν) :
    chamberDiag k ν h0 i * chamberDiag k ν h0 j = if i = j then chamberDiag k ν h0 i else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, chamberDiag]
    split_ifs
    · rw [e_mul_e, ite_eq_left rfl]
    · rw [zero_mul]
  · rw [ite_eq_right hij, chamberDiag, chamberDiag]
    split_ifs with hi hj
    · rw [e_mul_e, ite_eq_right]
      obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨D, -, rfl⟩ := Finset.mem_image.1 hj
      rw [spacedFull_chamberSeq, spacedFull_chamberSeq]
      exact fun h => hij (congrArg _ (Subtype.ext h))
    all_goals simp

theorem e_mul_chamberDiag (i : KLR.Seq ν) :
    e (spacedFull Γ i) * chamberDiag k ν h0 i = chamberDiag k ν h0 i := by
  rw [chamberDiag]
  split_ifs
  · rw [e_mul_e, ite_eq_left rfl]
  · rw [mul_zero]

theorem chamberDiag_mul_e (i : KLR.Seq ν) :
    chamberDiag k ν h0 i * e (spacedFull Γ i) = chamberDiag k ν h0 i := by
  rw [chamberDiag]
  split_ifs
  · rw [e_mul_e, ite_eq_left rfl]
  · rw [zero_mul]

theorem sum_chamberDiag : ∑ i, chamberDiag k ν h0 i = rankIdem k Γ ν' := by
  classical
  calc ∑ i, chamberDiag k ν h0 i
      = ∑ i ∈ Finset.univ.image (chamberSeq ν h0), e (spacedFull Γ i) := by
        simp only [chamberDiag]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ C, e (spacedFull Γ (chamberSeq ν h0 C)) :=
        Finset.sum_image fun C _ D _ h => chamberSeq_injective h0 h
    _ = ∑ C : RankChamber Γ ν', e C.1 := by simp only [spacedFull_chamberSeq]
    _ = rankIdem k Γ ν' :=
        (Finset.sum_subtype _ (fun C => by simp) (fun C => (e C : GalleryAlgebra k Γ ν'))).symm

theorem isIdempotentElem_diagonal_chamberDiag :
    IsIdempotentElem (Matrix.diagonal (chamberDiag k ν h0)) :=
  isIdempotentElem_diagonal fun i => by simpa using chamberDiag_mul h0 i i

variable (k ν) in
/-- The idempotent `∑_C e(B_s(i_C))` of the weighted KLR algebra on the evenly spaced loadings,
one chosen sequence `i_C` for each rank-ordered full chamber `C`. -/
noncomputable def spacedChamberIdem : SpacedAlgebra k Γ ν :=
  ⟨Matrix.diagonal (chamberDiag k ν h0),
    (mem_corner_diagonal_iff (d := fun i => e (spacedFull Γ i)) isIdempotentElem_spacedIdem).2
      fun i j => by
        by_cases hij : i = j
        · subst hij
          simp [e_mul_chamberDiag, chamberDiag_mul_e]
        · simp [hij]⟩

theorem isIdempotentElem_chamberIdem : IsIdempotentElem (spacedChamberIdem k ν h0) :=
  Subtype.ext (isIdempotentElem_diagonal_chamberDiag h0).eq

variable (k ν) in
/-- For the weighting `0`, the weighted KLR algebra is the corner of the weighted KLR algebra on
the evenly spaced loadings at `spacedChamberIdem`. -/
noncomputable def weightedKLRChamberEquiv :
    WeightedKLRAlgebra k Γ ν' ≃+* (isIdempotentElem_chamberIdem (k := k) (ν := ν) h0).Corner :=
  have hd := chamberDiag_mul (k := k) (ν := ν) h0
  have hs : IsIdempotentElem (∑ i, chamberDiag k ν h0 i) := isIdempotentElem_sum_of_mul_eq hd
  have hD := isIdempotentElem_diagonal_chamberDiag (k := k) (ν := ν) h0
  let φ₁ : WeightedKLRAlgebra k Γ ν' ≃+* hs.Corner :=
    cornerEquivOfEq (RingEquiv.refl (GalleryAlgebra k Γ ν')) isIdempotentElem_rankIdem hs
      (sum_chamberDiag (k := k) (ν := ν) h0).symm
  let φ₂ : hD.Corner ≃+* hs.Corner :=
    matrixCornerSumEquiv (R := GalleryAlgebra k Γ ν') hd hD hs
  let φ₃ : (isIdempotentElem_chamberIdem (k := k) (ν := ν) h0).Corner ≃+* hD.Corner :=
    cornerCornerEquiv (he := isIdempotentElem_spacedIdem (k := k) (Γ := Γ) (ν := ν))
      (isIdempotentElem_chamberIdem (k := k) (ν := ν) h0) hD
  (φ₁.trans φ₂.symm).trans φ₃.symm

theorem single_mem_corner_spacedIdem {i j : KLR.Seq ν} {x : GalleryAlgebra k Γ ν'}
    (h₁ : e (spacedFull Γ i) * x = x) (h₂ : x * e (spacedFull Γ j) = x) :
    Matrix.single i j x ∈ Subsemigroup.corner (spacedIdem k Γ ν) :=
  (mem_corner_diagonal_iff (d := fun i => e (spacedFull Γ i)) isIdempotentElem_spacedIdem).2
    fun a b => by
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h
        simp [h₁, h₂]
      · simp [h]

/-- The chosen representative of the full chamber of `B_s(i)`. -/
noncomputable def chamberRep (i : KLR.Seq ν) : KLR.Seq ν :=
  chamberSeq ν h0 ⟨spacedFull Γ i, (KLR.Seq.spacedChamber Γ i).toFull_isRankOrdered⟩

theorem spacedFull_chamberRep (i : KLR.Seq ν) : spacedFull Γ (chamberRep h0 i) = spacedFull Γ i :=
  spacedFull_chamberSeq h0 _

variable (k) in
/-- The matrix unit moving `B_s(i)` to the chosen representative of its chamber. -/
noncomputable def toChamberRep (i : KLR.Seq ν) : SpacedAlgebra k Γ ν :=
  ⟨Matrix.single i (chamberRep h0 i) (e (spacedFull Γ i)), single_mem_corner_spacedIdem
    (by rw [e_mul_e, ite_eq_left rfl]) (by rw [spacedFull_chamberRep, e_mul_e, ite_eq_left rfl])⟩

variable (k) in
/-- The matrix unit moving the chosen representative of the chamber of `B_s(i)` to `B_s(i)`. -/
noncomputable def fromChamberRep (i : KLR.Seq ν) : SpacedAlgebra k Γ ν :=
  ⟨Matrix.single (chamberRep h0 i) i (e (spacedFull Γ i)), single_mem_corner_spacedIdem
    (by rw [spacedFull_chamberRep, e_mul_e, ite_eq_left rfl]) (by rw [e_mul_e, ite_eq_left rfl])⟩

/-- `spacedChamberIdem` is a full idempotent: `1 = ∑_i u_i f v_i`. -/
theorem spacedChamberIdem_full :
    ∑ i, toChamberRep k h0 i * spacedChamberIdem k ν h0 * fromChamberRep k h0 i = 1 := by
  apply Subtype.ext
  rw [← cornerVal_apply, map_sum]
  show ∑ i, Matrix.single i (chamberRep h0 i) (e (spacedFull Γ i)) *
      Matrix.diagonal (chamberDiag k ν h0) *
      Matrix.single (chamberRep h0 i) i (e (spacedFull Γ i)) = spacedIdem k Γ ν
  have hd : ∀ i, chamberDiag k ν h0 (chamberRep h0 i) = e (spacedFull Γ i) := fun i => by
    rw [chamberRep, chamberDiag_chamberSeq]
  simp only [Matrix.single_mul_mul_single, Matrix.diagonal_apply_eq, hd, e_mul_e, ite_true]
  rw [Matrix.sum_single_eq_diagonal]
  rfl

end Zero

/-! ### Corollary 2.16 -/

section Forest

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If `η` is a primitive of the weighting, `η_{h(e)} - η_{t(e)} = ϑ_e`, then the shifted
weighting of Proposition 2.15 vanishes. -/
theorem shift_weight_eq_zero (η : I → 𝕜)
    (hη : ∀ e, η (Γ.head e) - η (Γ.tail e) = Γ.weight e) (e : Γ.E) :
    (Γ.shift η).weight e = 0 := by
  show Γ.weight e + η (Γ.tail e) - η (Γ.head e) = 0
  rw [← hη e]
  ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Changing the weighting does not change the underlying graph, so a forest stays a forest. -/
theorem WeightedGraph.IsForest.shift (hΓ : Γ.IsForest) (η : I → 𝕜) : (Γ.shift η).IsForest :=
  ⟨hΓ.head_ne_tail, hΓ.loop_eq_none, hΓ.edge_inj, hΓ.isAcyclic⟩

/-- Webster, arXiv:1209.2463v4, Corollary 2.16, first step, for a forest `Γ` (any weighting
and any commutative ring `k`): after the shift of Proposition 2.15 by a primitive `η` of the
weighting, the weighted KLR algebra is the corner `f A f` of the weighted KLR algebra `A` on
the evenly spaced loadings at an idempotent `f`, and `f` is full: `1 = ∑_i u_i f v_i`. -/
theorem WeightedGraph.IsForest.exists_spacedCorner (hΓ : Γ.IsForest) :
    ∃ η : I → 𝕜, ∃ f : SpacedAlgebra k (Γ.shift η) ν, ∃ hf : IsIdempotentElem f,
      Nonempty (WeightedKLRAlgebra k Γ ν' ≃+* hf.Corner) ∧
      ∃ u v : KLR.Seq ν → SpacedAlgebra k (Γ.shift η) ν, ∑ i, u i * f * v i = 1 := by
  obtain ⟨η, hη⟩ := hΓ.exists_coboundary Γ.weight
  have h0 : ∀ e, (Γ.shift η).weight e = 0 := shift_weight_eq_zero η hη
  exact ⟨η, spacedChamberIdem k ν h0, isIdempotentElem_chamberIdem h0,
    ⟨(weightedKLRShiftEquiv k ν' η).trans (weightedKLRChamberEquiv k ν h0)⟩,
    toChamberRep k h0, fromChamberRep k h0, spacedChamberIdem_full h0⟩

/-- Webster, arXiv:1209.2463v4, Corollary 2.16: if `Γ` is a forest, the weighted KLR algebra is
Morita equivalent to the KLR algebra. Stated as a full corner: there is an idempotent `f` of the
KLR algebra `R` with `W ≅ f R f` and `1 = ∑_i u_i f v_i` in `R`.

The hypotheses are Webster's standing hypothesis on the polynomials `Q_e` and his condition that
no edge is a loop and there are no loop polynomials (part of `IsForest`); his condition (†)
holds automatically on a forest (`IsForest.dagger`). The ground ring `k` is any commutative
ring. -/
theorem WeightedGraph.IsForest.exists_klrCorner (hΓ : Γ.IsForest)
    (hS : Γ.Standing) :
    ∃ f : KLR.KLRAlgebra k Γ.klrQ ν, ∃ hf : IsIdempotentElem f,
      Nonempty (WeightedKLRAlgebra k Γ ν' ≃+* hf.Corner) ∧
      ∃ u v : KLR.Seq ν → KLR.KLRAlgebra k Γ.klrQ ν, ∑ i, u i * f * v i = 1 := by
  obtain ⟨η, hη⟩ := hΓ.exists_coboundary Γ.weight
  have h0 : ∀ e, (Γ.shift η).weight e = 0 := shift_weight_eq_zero η hη
  have hΓ' := hΓ.shift η
  let φ : KLR.KLRAlgebra k Γ.klrQ ν ≃ₐ[k] SpacedAlgebra k (Γ.shift η) ν :=
    spacedEquiv (Γ := Γ.shift η) hS hΓ'.dagger hΓ'.head_ne_tail hΓ'.loop_eq_none
  have hf := isIdempotentElem_chamberIdem (k := k) (ν := ν) h0
  have hf' : IsIdempotentElem (φ.symm (spacedChamberIdem k ν h0)) := hf.map φ.symm
  refine ⟨φ.symm (spacedChamberIdem k ν h0), hf',
    ⟨((weightedKLRShiftEquiv k ν' η).trans (weightedKLRChamberEquiv k ν h0)).trans
      (cornerEquivOfEq φ.symm.toRingEquiv hf hf' rfl)⟩,
    fun i => φ.symm (toChamberRep k h0 i), fun i => φ.symm (fromChamberRep k h0 i), ?_⟩
  rw [← map_one φ.symm, ← spacedChamberIdem_full h0, map_sum]
  simp only [map_mul]

/-- Webster, arXiv:1209.2463v4, Corollary 2.16, for a tree (the printed case). -/
theorem WeightedGraph.IsTree.exists_klrCorner (hΓ : Γ.IsTree) (hS : Γ.Standing) :
    ∃ f : KLR.KLRAlgebra k Γ.klrQ ν, ∃ hf : IsIdempotentElem f,
      Nonempty (WeightedKLRAlgebra k Γ ν' ≃+* hf.Corner) ∧
      ∃ u v : KLR.Seq ν → KLR.KLRAlgebra k Γ.klrQ ν, ∑ i, u i * f * v i = 1 :=
  hΓ.1.exists_klrCorner hS

end Forest

end Categorification.WeightedKLR
