/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StendhalLoadings

/-!
# Crossings of Stendhal loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5: the image of a crossing of a Stendhal diagram in the weighted KLR algebra of the
Crawley-Boevey graph `Γ_λ` (`WeightedGraph.crawleyBoeveyIn`, old edges of weight `0`, new
weights `ϖ_1 < ⋯ < ϖ_ℓ`), and its action in the polynomial representation.

For a sequence `i` of black and red termini with the red strands in the order `λ_1, …, λ_ℓ`,
`stFull i` is the chamber of the loading `stCfg` of `i`. The crossing of the strands at
positions `n` and `n + 1` is the straight gallery exchanging them, followed by the relabelling
of the two strands when they are black of the same colour (`stCross`). Its image in the
polynomial representation goes from the copy of `stFull i` to the copy of `stFull (s_n i)` and
acts by `stCrossOp`: a divided difference for two black strands of the same colour, and
multiplication by `P₂(i_n, i_{n+1})(y_{n+1}, y_n)` otherwise, where `P₂` is `stP`:
`∏_{e : a → b} Q_e` between black strands, `(u₂ - u₁) ^ α_a^∨(λ_r)` for a black `a`-strand left
of the red strand `λ_r`, and `1` for a red strand left of a black one.

**Sign.** The ghost bigon of a black `a`-strand and the red strand `λ_r` gives
`(y_0 - y_a) ^ α_a^∨(λ_r)` in the polynomial representation, while Stendhal's relation needs
`(y_a - y_0) ^ α_a^∨(λ_r)` up to the variable of the red strand. We therefore multiply the
crossing of a black strand left of a red strand `λ_r` by `(-1) ^ α_a^∨(λ_r)` (`crossSign`).

## Main definitions

* `Stendhal.OrdSeq`: the Stendhal sequences with the red strands in the order `λ_1, …, λ_ℓ`.
* `Stendhal.stFull`: the chamber of the loading of such a sequence.
* `Stendhal.stP`, `Stendhal.crossSign`, `Stendhal.stCross`, `Stendhal.stCrossOp`.

## Main results

* `Stendhal.galleryRep_stCross`: the action of `stCross` in the polynomial representation.
-/

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv Segment MvPolynomial FullChamber GalleryAlgebra

section Strands

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)

/-- A strand labelled `λ_r` is the red strand `λ_r`. -/
theorem eq_redStrand {s : Strand μ} {r : Fin ℓ} (h : s.1.1 = .inr r) : s = redStrand ν r := by
  refine KLR.Seq.strand_ext (Subtype.ext h) ?_
  have h1 : s.2.val < μ s.1 := s.2.2
  have h2 : μ s.1 = 1 := by
    rw [show (s.1 : I ⊕ Fin ℓ) = .inr r from h]
    exact stendhalWeight_inr r
  show s.2.val = 0
  omega

theorem toTilde_fst {s : Strand μ} {a : I} (h : s.1.1 = .inl a) : (toTilde s).1.1 = some a := by
  obtain ⟨⟨_ | _, _⟩, _⟩ := s
  · simp only [Sum.inl.injEq] at h
    subst h
    rfl
  · simp at h

theorem toTilde_snd {s : Strand μ} (h : s.1.1.isLeft) : (toTilde s).2.val = s.2.val := by
  obtain ⟨⟨_ | _, _⟩, _⟩ := s
  · rfl
  · simp at h

theorem toTilde_of_not_isLeft {s : Strand μ} (h : ¬ s.1.1.isLeft) :
    toTilde s = GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν) := by
  obtain ⟨⟨_ | _, _⟩, _⟩ := s
  · simp at h
  · rfl

/-- Strands of the same colour stay of the same colour in `ν̃`. -/
theorem toTilde_fst_eq {s t : Strand μ} (h : s.1 = t.1) : (toTilde s).1 = (toTilde t).1 := by
  obtain ⟨⟨_ | _, _⟩, _⟩ := s <;> obtain ⟨⟨_ | _, _⟩, _⟩ := t <;>
    simp only [Subtype.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · subst h; rfl
  · rfl

theorem fst_eq_of_toTilde {s t : Strand μ} (hs : s.1.1.isLeft) (ht : t.1.1.isLeft)
    (h : (toTilde s).1 = (toTilde t).1) : s.1 = t.1 := by
  obtain ⟨⟨_ | _, _⟩, _⟩ := s
  · obtain ⟨⟨_ | _, _⟩, _⟩ := t
    · simp only [toTilde, Subtype.mk.injEq, Option.some.injEq] at h
      subst h
      rfl
    · simp at ht
  · simp at hs

theorem eq_of_toTilde_eq {s t : Strand μ} (ht : t.1.1.isLeft) (h : toTilde s = toTilde t) :
    s = t := by
  by_cases hs : s.1.1.isLeft
  · exact (toTilde_inj hs ht).1 h
  · rw [toTilde_of_not_isLeft hs] at h
    exact absurd h.symm (toTilde_ne_zeroStrand ht)

end Strands

section Sequences

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable (ℓ ν) in
/-- The Stendhal sequences with the red strands in the order `λ_1, …, λ_ℓ`. -/
abbrev OrdSeq : Type := {i : KLR.Seq (stendhalWeight ℓ ν) // IsRedOrdered i}

/-- The positions of the strands of a sequence. -/
noncomputable def posVal (i : KLR.Seq (stendhalWeight ℓ ν)) (t : Strand μ) : ℕ := (i.posOf t : ℕ)

theorem posVal_strandAt (i : KLR.Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    posVal i (i.strandAt a) = a := by
  simp [posVal]

theorem isAdm_posVal {i : KLR.Seq (stendhalWeight ℓ ν)} (hi : IsRedOrdered i) :
    IsAdm ν m (posVal i) where
  inj := Fin.val_injective.comp i.posOf_injective
  lt s := (i.posOf s).2
  red r r' hrr' := by
    show (i.posOf (redStrand ν r) : ℕ) < i.posOf (redStrand ν r')
    rcases lt_trichotomy (i.posOf (redStrand ν r)) (i.posOf (redStrand ν r')) with h | h | h
    · exact h
    · exact absurd (redStrand_injective (i.posOf_injective h)) hrr'.ne
    · exact absurd (hi _ _ r' r h (i.label_posOf _) (i.label_posOf _)) (not_lt.2 hrr'.le)

/-- Two neighbouring strands of the same colour are black. -/
theorem isLeft_of_eq {i : KLR.Seq (stendhalWeight ℓ ν)} {n : ℕ} (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) : (i.1 ⟨n, by omega⟩).isLeft := by
  rcases hr : i.1 ⟨n, by omega⟩ with a | r
  · rfl
  · exfalso
    have e1 := eq_redStrand (ν := ν) (s := i.strandAt ⟨n, by omega⟩) hr
    have e2 := eq_redStrand (ν := ν) (s := i.strandAt ⟨n + 1, h⟩) (hc ▸ hr)
    have := i.strandAt_injective (e1.trans e2.symm)
    simp [Fin.ext_iff] at this

/-- Exchanging two neighbouring strands of distinct colours exchanges their positions. -/
theorem posVal_sadj (i : KLR.Seq (stendhalWeight ℓ ν)) {n : ℕ} (h : n + 1 < m)
    (hne : i.1 ⟨n, by omega⟩ ≠ i.1 ⟨n + 1, h⟩) :
    posVal (TypeA.sadj m n • i) =
      posVal i ∘ swap (i.strandAt ⟨n, by omega⟩) (i.strandAt ⟨n + 1, h⟩) := by
  funext t
  simp only [posVal, Function.comp_apply]
  rw [KLR.Seq.posOf_swap i h, KLR.Seq.posOf_smul i _ (KLR.Seq.lt_sadj_iff i h hne)]

omit [DecidableEq I] in
/-- Two neighbouring red strands cannot be exchanged in a red-ordered sequence. -/
theorem not_red_red {i : KLR.Seq (stendhalWeight ℓ ν)} (hi : IsRedOrdered i) {n : ℕ}
    (h : n + 1 < m) (hi' : IsRedOrdered (TypeA.sadj m n • i)) {r r' : Fin ℓ}
    (hr : i.1 ⟨n, by omega⟩ = .inr r) (hr' : i.1 ⟨n + 1, h⟩ = .inr r') : False := by
  have h1 := hi ⟨n, by omega⟩ ⟨n + 1, h⟩ r r' (Fin.mk_lt_mk.2 (Nat.lt_succ_self n)) hr hr'
  have hs : (TypeA.sadj m n).symm = TypeA.sadj m n := by
    rw [← Perm.inv_def]
    exact inv_eq_of_mul_eq_one_left (TypeA.sadj_mul_self m n)
  have e1 : (TypeA.sadj m n • i).1 ⟨n, by omega⟩ = .inr r' := by
    show i.1 ((TypeA.sadj m n).symm _) = _
    rw [hs, TypeA.sadj_apply_left h, hr']
  have e2 : (TypeA.sadj m n • i).1 ⟨n + 1, h⟩ = .inr r := by
    show i.1 ((TypeA.sadj m n).symm _) = _
    rw [hs, TypeA.sadj_apply_right h, hr]
  exact absurd (hi' _ _ r' r (Fin.mk_lt_mk.2 (Nat.lt_succ_self n)) e1 e2) (not_lt.2 h1.le)

end Sequences

section Crossing

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {Λ : Fin ℓ → I →₀ ℕ} {ϖ : Fin ℓ → 𝕜}

local notation "μ" => Multiset.toFinsupp (stendhalWeight ℓ ν)
local notation "ν̃" => WeightedGraph.redWeight (Multiset.toFinsupp ν)
local notation "Γλ" => WeightedGraph.crawleyBoeveyIn Γ Λ ϖ
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem loop_crawleyBoeveyIn (hl : ∀ c, Γ.loop c = none) (o : Option I) : Γλ.loop o = none := by
  rcases o with _ | c
  · rfl
  · exact hl c

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem psymm_of_loop (hl : ∀ c, Γ.loop c = none) : Γ.PSymm := fun c P hP => by
  simp [hl c] at hP

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The old edges of `Γ_λ` between two old vertices. -/
theorem edgeProd_crawleyBoeveyIn_some (a b : I) :
    Γλ.edgeProd (some a) (some b) = Γ.edgeProd a b := by
  classical
  unfold WeightedGraph.edgeProd
  rw [Finset.prod_filter, Finset.prod_filter]
  refine (Fintype.prod_sum_type _).trans ?_
  simp [WeightedGraph.crawleyBoeveyIn]

theorem IsAdm.comp_swap {M : ℕ} {π : Strand μ → ℕ} (hπ : IsAdm ν M π) {u v : Strand μ}
    (hu : u.1.1.isLeft) (hv : v.1.1.isLeft) : IsAdm ν M (π ∘ swap u v) where
  inj := hπ.inj.comp (swap u v).injective
  lt _ := hπ.lt _
  red r r' h := by
    have e : ∀ r, swap u v (redStrand ν r) = redStrand ν r := fun r =>
      swap_apply_of_ne_of_ne (fun e => not_isLeft_redStrand r (by rw [e]; exact hu))
        (fun e => not_isLeft_redStrand r (by rw [e]; exact hv))
    show π (swap u v (redStrand ν r)) < π (swap u v (redStrand ν r'))
    rw [e, e]
    exact hπ.red h

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Between two black strands, the hyperplanes comparing them are those joining them. -/
theorem crosses_iff_joinsPair {u v : Strand μ} (hu : u.1.1.isLeft) (hv : v.1.1.isLeft)
    (x : Hyp Γλ ν̃) : Crosses ν u v x ↔ x.JoinsPair (toTilde u) (toTilde v) := by
  refine ⟨joinsPair_of_crosses, fun hx => ?_⟩
  rcases x with w | d
  · rcases hx with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨u, v, ⟨Or.inl (by rw [hs]; exact ofTilde_toTilde_inl hu),
        by rw [ht]; exact ofTilde_toTilde_inl hv⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, u, ⟨Or.inl (by rw [hs]; exact ofTilde_toTilde_inl hv),
        by rw [ht]; exact ofTilde_toTilde_inl hu⟩, Or.inr ⟨rfl, rfl⟩⟩
  · rcases hx with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨u, v, ⟨by rw [hs]; exact ofTilde_toTilde_inl hu,
        by rw [ht]; exact ofTilde_toTilde_inl hv⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, u, ⟨by rw [hs]; exact ofTilde_toTilde_inl hv,
        by rw [ht]; exact ofTilde_toTilde_inl hu⟩, Or.inr ⟨rfl, rfl⟩⟩

variable (Λ) in
/-- The chamber of the loading of a red-ordered Stendhal sequence. -/
noncomputable def stFull (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) (i : OrdSeq ℓ ν) :
    FullChamber Γλ ν̃ :=
  FullChamber.ofPoint (stCfg ϖ m (posVal i.1)) (isGeneric_stCfg hϖ hw0 (isAdm_posVal i.2))

theorem stFull_apply (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) (i : OrdSeq ℓ ν)
    (x : Hyp Γλ ν̃) :
    (stFull Λ hϖ hw0 i).1 x = decide (0 < x.val (stCfg ϖ m (posVal i.1))) := rfl

theorem stFull_eq_true_iff (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) (i : OrdSeq ℓ ν)
    {x : Hyp Γλ ν̃} {a b : Strand μ} (hl : Lifts ν x a b) :
    (stFull Λ hϖ hw0 i).1 x = true ↔ posVal i.1 a < posVal i.1 b := by
  rw [stFull_apply, decide_eq_true_iff, pos_iff_of_lifts hϖ hw0 (isAdm_posVal i.2) hl]

variable (Γ Λ ϖ) in
/-- The word of the segment exchanging the strands at positions `n` and `n + 1`. -/
noncomputable def stWord (i : KLR.Seq (stendhalWeight ℓ ν)) (n : ℕ) (h : n + 1 < m) :
    List (Hyp Γλ ν̃) :=
  Segment.word (hypAff (Γ := Γλ)) (stCfg ϖ m (posVal i))
    (stCfg ϖ m (posVal i ∘ swap (i.strandAt ⟨n, by omega⟩) (i.strandAt ⟨n + 1, h⟩)))

variable (Γ Λ) in
/-- The polynomials `P₂` of the Stendhal crossings: `∏_{e : a → b} Q_e` between black strands,
`(u₂ - u₁) ^ α_a^∨(λ_r)` for a black `a`-strand left of `λ_r`, `1` for `λ_r` left of a black
strand, and `0` between red strands. -/
noncomputable def stP : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k
  | .inl a, .inl b => Γ.edgeProd a b
  | .inl a, .inr r => (X 1 - X 0) ^ Λ r a
  | .inr _, .inl _ => 1
  | .inr _, .inr _ => 0

variable (k Λ) in
/-- The rescaling of the crossings: `(-1) ^ α_a^∨(λ_r)` for a black `a`-strand left of the red
strand `λ_r`, and `1` otherwise. -/
def crossSign : I ⊕ Fin ℓ → I ⊕ Fin ℓ → k
  | .inl _, .inl _ => 1
  | .inl a, .inr r => (-1) ^ Λ r a
  | .inr _, .inl _ => 1
  | .inr _, .inr _ => 1

/-- Two neighbouring black strands of the same colour, as a diagonal of `ν̃`. -/
def stDiag (i : KLR.Seq (stendhalWeight ℓ ν)) (n : ℕ) (h : n + 1 < m)
    (hc : i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩) : Diag ν̃ :=
  ⟨(toTilde (i.strandAt ⟨n, by omega⟩), toTilde (i.strandAt ⟨n + 1, h⟩)),
    toTilde_fst_eq (Subtype.ext hc), by
      have hv : (i.strandAt ⟨n + 1, h⟩).1.1.isLeft := by
        show (i.1 ⟨n + 1, h⟩).isLeft
        rw [← hc]
        exact isLeft_of_eq h hc
      rw [toTilde_snd (isLeft_of_eq h hc), toTilde_snd hv]
      exact i.rank_lt_rank (Fin.mk_lt_mk.2 (Nat.lt_succ_self n)) hc⟩

variable (k Λ) in
/-- **The crossing of a Stendhal diagram** at positions `n` and `n + 1` in the weighted KLR
algebra of `Γ_λ`: the straight gallery between the loadings, followed by the relabelling when
the two strands are black of the same colour, and rescaled by `crossSign`. -/
noncomputable def stCross (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0) (i : OrdSeq ℓ ν)
    (n : ℕ) (h : n + 1 < m) : GalleryAlgebra k Γλ ν̃ :=
  if hc : i.1.1 ⟨n, by omega⟩ = i.1.1 ⟨n + 1, h⟩ then
    r (stDiag i.1 n h hc).refl ((stFull Λ hϖ hw0 i).flips (stWord Γ Λ ϖ i.1 n h)) *
      galList k (stFull Λ hϖ hw0 i) (stWord Γ Λ ϖ i.1 n h)
  else crossSign k Λ (i.1.1 ⟨n, by omega⟩) (i.1.1 ⟨n + 1, h⟩) •
    galList k (stFull Λ hϖ hw0 i) (stWord Γ Λ ϖ i.1 n h)

variable (k Γ Λ) in
/-- The operator of the crossing: the divided difference `∂_{u v}` between black strands of the
same colour, and multiplication by `P₂(i_n, i_{n+1})(y_v, y_u)` otherwise. -/
noncomputable def stCrossOp (i : KLR.Seq (stendhalWeight ℓ ν)) (n : ℕ) (h : n + 1 < m) :
    PolyRing ν̃ k →ₗ[k] PolyRing ν̃ k :=
  if i.1 ⟨n, by omega⟩ = i.1 ⟨n + 1, h⟩ then
    ddiff (toTilde (i.strandAt ⟨n, by omega⟩)) (toTilde (i.strandAt ⟨n + 1, h⟩))
  else LinearMap.mulLeft k (rename ![toTilde (i.strandAt ⟨n + 1, h⟩),
    toTilde (i.strandAt ⟨n, by omega⟩)] (stP Γ Λ (i.1 ⟨n, by omega⟩) (i.1 ⟨n + 1, h⟩)))

omit [DecidableEq I] in
theorem blk_smul {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module k M] (A B : ι) (c : k)
    (a : M →ₗ[k] M) : c • blk k A B a = blk k A B (c • a) := by
  ext x : 1
  simp [blk_apply, Pi.single_smul]

/-- **The crossings of Stendhal diagrams in the polynomial representation**
(Webster, arXiv:1209.2463v4, proof of Theorem 3.5): `stCross` acts from the copy of the chamber
of `i` to the copy of the chamber of `s_n i` by `stCrossOp`. -/
theorem galleryRep_stCross (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hϖ : StrictMono ϖ) (hw0 : ∀ e, Γ.weight e = 0)
    (i : OrdSeq ℓ ν) (n : ℕ) (h : n + 1 < m) (hi : IsRedOrdered (TypeA.sadj m n • i.1)) :
    galleryRep k (WeightedGraph.crawleyBoeveyIn_psymm (psymm_of_loop hl))
        (stCross k Λ hϖ hw0 i n h) =
      blk k (stFull Λ hϖ hw0 i) (stFull Λ hϖ hw0 ⟨TypeA.sadj m n • i.1, hi⟩)
        (stCrossOp k Γ Λ i.1 n h) := by
  have hZ : Γ.NoZeroLoops := fun e he => absurd he (hE e)
  set u := i.1.strandAt ⟨n, by omega⟩ with hu_def
  set v := i.1.strandAt ⟨n + 1, h⟩ with hv_def
  have hπ := isAdm_posVal i.2
  have huv : posVal i.1 v = posVal i.1 u + 1 := by
    rw [hu_def, hv_def, posVal_strandAt, posVal_strandAt]
  have hlt : posVal i.1 u < posVal i.1 v := by omega
  have hne : u ≠ v := fun e => by
    have := i.1.strandAt_injective e
    simp [Fin.ext_iff] at this
  by_cases hc : i.1.1 ⟨n, by omega⟩ = i.1.1 ⟨n + 1, h⟩
  · have hu : u.1.1.isLeft := isLeft_of_eq h hc
    have hv : v.1.1.isLeft := by
      show (i.1.1 ⟨n + 1, h⟩).isLeft
      rw [← hc]
      exact isLeft_of_eq h hc
    have hπ' := hπ.comp_swap hu hv
    set d := stDiag i.1 n h hc
    have hlf : Lifts ν (.inr d : Hyp Γλ ν̃) u v := ⟨ofTilde_toTilde_inl hu, ofTilde_toTilde_inl hv⟩
    have hw : stWord Γ Λ ϖ i.1 n h = [.inr d] :=
      word_stCfg_swap_eq hD hZ hϖ hw0 hπ hπ' huv ⟨u, v, hlf, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨hgood, -⟩ := goodWord_flips_word (C := stFull Λ hϖ hw0 i)
      (simple_stCfg_swap hD hZ hϖ hw0 hπ hπ' huv) rfl
    have hgood' : GoodWord (stFull Λ hϖ hw0 i).1 [.inr d] := by
      rw [← hw]
      exact hgood
    obtain ⟨-, ha, -⟩ := hgood'.cons
    have hC : d.refl • (stFull Λ hϖ hw0 i).flips [.inr d] =
        stFull Λ hϖ hw0 ⟨TypeA.sadj m n • i.1, hi⟩ := by
      rw [flips_cons, flips_nil, ← ha.refl_smul, smul_smul, Diag.refl_mul_refl, one_smul]
      congr 1
      exact Subtype.ext (KLR.Seq.sadj_smul_of_eq i.1 h hc).symm
    have h1 : (stFull Λ hϖ hw0 i).1 (.inr d) = true := (stFull_eq_true_iff hϖ hw0 i hlf).2 hlt
    simp only [stCross, hc, ↓reduceDIte, stCrossOp, ↓reduceIte]
    rw [hw, map_mul, galleryRep_r, galleryRep_galList, Module.End.mul_eq_comp, blk_comp_blk, hC]
    congr 1
    rw [opList, opList, LinearMap.id_comp, stepOp_inr ha,
      psiOp_of_none (loop_crawleyBoeveyIn hl _)]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, Diag.left, Diag.right, h1, ↓reduceIte]
    exact rename_swap_ddiff (fun e => hne (eq_of_toTilde_eq hv e)) _
  · have hπ' : IsAdm ν m (posVal i.1 ∘ swap u v) := by
      have := isAdm_posVal hi
      rwa [posVal_sadj i.1 h hc] at this
    have hmem := fun x => mem_word_stCfg_swap (Γ := Γ) (Λ := Λ) hϖ hw0 hπ hπ' huv (x := x)
    obtain ⟨hgood₀, hflips⟩ := goodWord_flips_word (C := stFull Λ hϖ hw0 i)
      (simple_stCfg_swap hD hZ hϖ hw0 hπ hπ' huv) rfl
    have hgood : GoodWord (stFull Λ hϖ hw0 i).1 (stWord Γ Λ ϖ i.1 n h) := hgood₀
    have hflip : (stFull Λ hϖ hw0 i).flips (stWord Γ Λ ϖ i.1 n h) =
        stFull Λ hϖ hw0 ⟨TypeA.sadj m n • i.1, hi⟩ := by
      refine Subtype.ext (hflips.trans ?_)
      show _ = fullSigns (stCfg ϖ m (posVal (TypeA.sadj m n • i.1)))
      rw [posVal_sadj i.1 h hc]
    have hdiag : ∀ d, (Sum.inr d : Hyp Γλ ν̃) ∉ stWord Γ Λ ϖ i.1 n h := by
      intro d hd
      obtain ⟨a, b, hab, hor⟩ := (hmem _).1 hd
      have e : a.1 = b.1 := fst_eq_of_toTilde (isLeft_of_ofTilde hab.1)
        (isLeft_of_ofTilde hab.2)
        (by rw [toTilde_of_ofTilde hab.1, toTilde_of_ofTilde hab.2]; exact d.2.1)
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc (congrArg Subtype.val e)
      · exact hc (congrArg Subtype.val e).symm
    simp only [stCross, hc, ↓reduceDIte, stCrossOp, ↓reduceIte]
    rw [map_smul, galleryRep_galList, hflip, opList_of_walls hgood hdiag, blk_smul]
    congr 1
    suffices key : crossSign k Λ (i.1.1 ⟨n, by omega⟩) (i.1.1 ⟨n + 1, h⟩) •
        ((stWord Γ Λ ϖ i.1 n h).map
          fun x => wallCoeff (k := k) x ((stFull Λ hϖ hw0 i).1 x)).prod =
        rename ![toTilde v, toTilde u] (stP Γ Λ (i.1.1 ⟨n, by omega⟩) (i.1.1 ⟨n + 1, h⟩)) by
      rw [← key]
      refine LinearMap.ext fun f => ?_
      simp
    rcases hlu : i.1.1 ⟨n, by omega⟩ with a | r <;> rcases hlv : i.1.1 ⟨n + 1, h⟩ with b | r'
    · -- two black strands of distinct colours
      classical
      have hu : u.1.1.isLeft := by rw [show u.1.1 = _ from hlu]; rfl
      have hv : v.1.1.isLeft := by rw [show v.1.1 = _ from hlv]; rfl
      simp only [crossSign, stP, one_smul]
      rw [← edgeProd_crawleyBoeveyIn_some (Λ := Λ) (ϖ := ϖ), ← List.prod_toFinset _ hgood.1]
      have hset : (stWord Γ Λ ϖ i.1 n h).toFinset = Finset.univ.filter
          (fun x : Hyp Γλ ν̃ => x.JoinsPair (toTilde u) (toTilde v)) := by
        ext x
        simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← crosses_iff_joinsPair hu hv]
        exact hmem x
      have e1 : (toTilde u).label = some a := toTilde_fst hlu
      have e2 : (toTilde v).label = some b := toTilde_fst hlv
      rw [hset, ← e1, ← e2]
      refine prod_wallCoeff_joinsPair (k := k) _ (fun e => hne (eq_of_toTilde_eq hv e)) ?_ ?_
      · intro w hs ht
        exact (stFull_eq_true_iff hϖ hw0 i (x := .inl w) (a := u) (b := v)
          ⟨Or.inl (by rw [hs]; exact ofTilde_toTilde_inl hu),
            by rw [ht]; exact ofTilde_toTilde_inl hv⟩).2 hlt
      · intro w hs ht
        rw [Bool.eq_false_iff]
        intro hh
        have := (stFull_eq_true_iff hϖ hw0 i (x := .inl w) (a := v) (b := u)
          ⟨Or.inl (by rw [hs]; exact ofTilde_toTilde_inl hv),
            by rw [ht]; exact ofTilde_toTilde_inl hu⟩).1 hh
        omega
    · -- a black strand left of a red strand
      have hu : u.1.1.isLeft := by rw [show u.1.1 = _ from hlu]; rfl
      have hv : ¬ v.1.1.isLeft := by rw [show v.1.1 = _ from hlv]; simp
      have hvr : v = redStrand ν r' := eq_redStrand hlv
      have htv : toTilde v = GalleryAlgebra.zeroStrand (Multiset.toFinsupp ν) :=
        toTilde_of_not_isLeft hv
      have hcr : ∀ x, Crosses ν u v x → ∃ (w : Wall Γλ ν̃) (c : WeightedGraph.RedEdge Λ),
          x = .inl w ∧ w.edge = .inr c ∧ c.1 = r' ∧ c.2.1 = a ∧ w.tgt = toTilde u ∧
            (stFull Λ hϖ hw0 i).1 x = false := by
        rintro x ⟨a', b', hl', ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact absurd (isLeft_of_lifts hl') hv
        · rcases x with w | d
          · obtain ⟨hsrc | ⟨c, hc', hvc⟩, htg⟩ := hl'
            · exact absurd (isLeft_of_ofTilde hsrc) hv
            · have htg' : w.tgt = toTilde u := (toTilde_of_ofTilde htg).symm
              refine ⟨w, c, rfl, hc', redStrand_injective (hvc.symm.trans hvr), ?_, htg', ?_⟩
              · have := tgt_label_of_edge_inr w hc'
                rw [htg', toTilde_fst hlu] at this
                exact (Option.some_injective _ this).symm
              · rw [Bool.eq_false_iff]
                intro hh
                have := (stFull_eq_true_iff hϖ hw0 i
                  (x := .inl w) (a := v) (b := u) ⟨Or.inr ⟨c, hc', hvc⟩, htg⟩).1 hh
                omega
          · exact absurd (isLeft_of_ofTilde hl'.1) hv
      by_cases hex : ∃ x : Hyp Γλ ν̃, Crosses ν u v x
      · obtain ⟨x, hx⟩ := hex
        have hword := word_stCfg_swap_eq hD hZ hϖ hw0 hπ hπ' huv hx
        obtain ⟨w, c, rfl, hc', hcr', hca, htg, hsg⟩ := hcr x hx
        rw [show stWord Γ Λ ϖ i.1 n h = [.inl w] from hword]
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hsg,
          wallCoeff, ↓reduceIte, crossSign, stP]
        rw [Wall.factor_eq_rename, src_eq_zeroStrand w hc', htg, htv, hc']
        rw [show Γλ.Q (.inr c) = (X 0 - X 1) ^ Λ c.1 c.2.1 from rfl, hca, hcr']
        simp only [map_pow, map_sub, rename_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        rw [Algebra.smul_def, map_pow, map_neg, map_one, ← neg_sub (X _) (X (toTilde u)),
          neg_pow (X _ - X _)]
      · push Not at hex
        have hΛ : Λ r' a = 0 := by
          by_contra hΛ
          let c : WeightedGraph.RedEdge Λ := ⟨r', ⟨a, Finsupp.mem_support_iff.2 hΛ⟩⟩
          let w0 : Wall Γλ ν̃ := ⟨(.inr c, GalleryAlgebra.zeroStrand _, toTilde u),
            rfl, toTilde_fst hlu, (toTilde_ne_zeroStrand hu).symm⟩
          exact hex (.inl w0)
            ⟨v, u, ⟨Or.inr ⟨c, rfl, hvr⟩, ofTilde_toTilde_inl hu⟩, Or.inr ⟨rfl, rfl⟩⟩
        rw [show stWord Γ Λ ϖ i.1 n h = [] from word_stCfg_swap_eq_nil hϖ hw0 hπ hπ' huv hex]
        simp [crossSign, stP, hΛ]
    · -- a red strand left of a black strand
      have hu : ¬ u.1.1.isLeft := by rw [show u.1.1 = _ from hlu]; simp
      rw [List.prod_eq_one]
      · simp [crossSign, stP]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a', b', hl', hor⟩ := (hmem x).1 hx
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(stFull_eq_true_iff hϖ hw0 i hl').2 hlt]
        rcases x with w | d <;> simp [wallCoeff]
      · exact absurd (isLeft_of_lifts hl') hu
    · exact (not_red_red i.2 h hi hlu hlv).elim

end Crossing

end Categorification.Stendhal
