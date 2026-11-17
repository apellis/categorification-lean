/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Standing
import Categorification.WeightedKLR.Relabel

/-!
# The graph seen near a configuration

Supporting constructions for the absolute-irreducibility input of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19 (roadmap A). The local comparison refines a colour by the coordinate of its strand in a fixed configuration.
The walls through that configuration become the zero-weight walls of the
refined graph. This file supplies the graph, dimension vector, and strand
identification; it does not assert absolute irreducibility.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

open Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The original colour together with the coordinate at the fixed configuration. -/
def label (p : Strand ν → 𝕜) (s : Strand ν) : I × 𝕜 := (s.label, p s)

/-- The finitely many coordinates occupied by a configuration. -/
abbrev Coord (p : Strand ν → 𝕜) := {x : 𝕜 // x ∈ Finset.univ.image p}

instance (p : Strand ν → 𝕜) : Fintype (Coord p) := by
  unfold Coord
  infer_instance

instance (p : Strand ν → 𝕜) : DecidableEq (Coord p) := inferInstanceAs (DecidableEq (Subtype _))

/-- The dimension vector obtained by separating strands at different coordinates. -/
def weight (p : Strand ν → 𝕜) : (I × 𝕜) →₀ ℕ := by
  classical
  exact Finsupp.onFinset (Finset.univ.image (label p))
    (fun a => Fintype.card {s : Strand ν // label p s = a}) fun a ha => by
      have : Nonempty {s : Strand ν // label p s = a} :=
        Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero ha)
      obtain ⟨s, hs⟩ := this
      exact Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem weight_apply (p : Strand ν → 𝕜) (a : I × 𝕜) :
    weight p a = Fintype.card {s : Strand ν // label p s = a} := rfl

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem label_mem_support (p : Strand ν → 𝕜) (s : Strand ν) :
    label p s ∈ (weight p).support := by
  classical
  rw [Finsupp.mem_support_iff, weight_apply]
  exact Nat.ne_of_gt (Fintype.card_pos_iff.2 ⟨⟨s, rfl⟩⟩)

private def fibreEquiv (p : Strand ν → 𝕜) :
    (Σ a : (weight p).support, {s : Strand ν // label p s = a.1}) ≃ Strand ν where
  toFun s := s.2.1
  invFun s := ⟨⟨label p s, label_mem_support p s⟩, ⟨s, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨a, ha⟩, s, hs⟩
    cases hs
    rfl
  right_inv _ := rfl

private def fibreRank (p : Strand ν → 𝕜) (a : I × 𝕜)
    (s : {s : Strand ν // label p s = a}) : ℕ := s.1.2.val

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem fibreRank_injective (p : Strand ν → 𝕜) (a : I × 𝕜) :
    Function.Injective (fibreRank p a) := by
  rintro ⟨⟨⟨i, hi⟩, r⟩, hs⟩ ⟨⟨⟨j, hj⟩, t⟩, ht⟩ h
  have hij : i = j := congrArg Prod.fst (hs.trans ht.symm)
  subst j
  have hrt : r = t := Fin.ext h
  subst t
  rfl

private def fibreRanks (p : Strand ν → 𝕜) (a : I × 𝕜) : Finset ℕ :=
  Finset.univ.image (fibreRank p a)

private def fibreRankEquiv (p : Strand ν → 𝕜) (a : I × 𝕜) :
    {s : Strand ν // label p s = a} ≃ (fibreRanks p a) :=
  Equiv.ofBijective
    (fun s => ⟨fibreRank p a s, Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun s t h => fibreRank_injective p a (congrArg Subtype.val h), by
      rintro ⟨r, hr⟩
      obtain ⟨s, _, hs⟩ := Finset.mem_image.1 hr
      exact ⟨s, Subtype.ext hs⟩⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem fibreRanks_card (p : Strand ν → 𝕜) (a : I × 𝕜) :
    (fibreRanks p a).card = weight p a := by
  rw [fibreRanks, Finset.card_image_of_injective _ (fibreRank_injective p a),
    Finset.card_univ, weight_apply]

/-- The refined fibre is enumerated in increasing original rank. -/
def fibreOrderEquiv (p : Strand ν → 𝕜) (a : I × 𝕜) :
    Fin (weight p a) ≃ {s : Strand ν // label p s = a} :=
  ((fibreRanks p a).orderIsoOfFin (fibreRanks_card p a)).toEquiv.trans
    (fibreRankEquiv p a).symm

/-- The refined and original dimension vectors have the same individual strands.
The identification preserves rank order inside each refined colour. -/
def strandEquiv (p : Strand ν → 𝕜) : Strand (weight p) ≃ Strand ν :=
  (Equiv.sigmaCongrRight fun a : (weight p).support =>
    fibreOrderEquiv p a.1).trans (fibreEquiv p)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem label_strandEquiv (p : Strand ν → 𝕜) (s : Strand (weight p)) :
    label p (strandEquiv p s) = s.label := by
  exact (fibreOrderEquiv p s.1.1 s.2).2

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem strandEquiv_colour (p : Strand ν → 𝕜) (s : Strand (weight p)) :
    (strandEquiv p s).label = s.label.1 :=
  congrArg Prod.fst (label_strandEquiv p s)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem strandEquiv_coord (p : Strand ν → 𝕜) (s : Strand (weight p)) :
    p (strandEquiv p s) = s.label.2 :=
  congrArg Prod.snd (label_strandEquiv p s)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem strandEquiv_rank_lt_iff (p : Strand ν → 𝕜) (a : (weight p).support)
    (r t : Fin (weight p a.1)) :
    (strandEquiv p ⟨a, r⟩).2.val < (strandEquiv p ⟨a, t⟩).2.val ↔ r.val < t.val := by
  let E := (fibreRanks p a.1).orderIsoOfFin (fibreRanks_card p a.1)
  have h (r : Fin (weight p a.1)) :
      (strandEquiv p ⟨a, r⟩).2.val = (E r).1 := by
    change ((fibreRankEquiv p a.1) ((fibreRankEquiv p a.1).symm (E r))).1 = (E r).1
    rw [Equiv.apply_symm_apply]
  rw [h r, h t]
  exact E.lt_iff_lt

/-- A small finite indexing type for the occupied coordinates. -/
def coord (p : Strand ν → 𝕜) : Fin (Fintype.card (Coord p)) ≃ Coord p :=
  (Fintype.equivFin (Coord p)).symm

/-- The coordinate index of an original strand. -/
def coordIndex (p : Strand ν → 𝕜) (s : Strand ν) : Fin (Fintype.card (Coord p)) :=
  (coord p).symm ⟨p s, Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩⟩

omit [DecidableEq I] [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem coord_coordIndex (p : Strand ν → 𝕜) (s : Strand ν) :
    (coord p (coordIndex p s)).1 = p s := by
  unfold coordIndex
  rw [Equiv.apply_symm_apply]

/-- The graph of walls incident to the fixed configuration, with all weights zero.
Edges ending at an unoccupied refined vertex do not give walls at the refined weight. -/
def graph (Γ : WeightedGraph I 𝕜 k) (p : Strand ν → 𝕜) :
    WeightedGraph (I × 𝕜) 𝕜 k where
  E := Γ.E × Fin (Fintype.card (Coord p))
  tail e := (Γ.tail e.1, (coord p e.2).1 + Γ.weight e.1)
  head e := (Γ.head e.1, (coord p e.2).1)
  weight _ := 0
  Q e := Γ.Q e.1
  loop a := Γ.loop a.1

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem graph_weight (p : Strand ν → 𝕜) (e : (graph Γ p).E) :
    (graph Γ p).weight e = 0 := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Webster's standing hypothesis is preserved by the local refinement. -/
theorem standing (p : Strand ν → 𝕜) (hS : Γ.Standing) : (graph Γ p).Standing := by
  obtain ⟨d, hd, hQ, hl⟩ := hS
  exact ⟨fun a => d a.1, fun a => hd a.1, fun e => hQ e.1, fun a => hl a.1⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- If the original graph has no edges which are loops, neither does the refinement. -/
theorem head_ne_tail (p : Strand ν → 𝕜) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (e : (graph Γ p).E) : (graph Γ p).head e ≠ (graph Γ p).tail e := by
  intro h
  exact hE e.1 (congrArg Prod.fst h)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem graph_loop (p : Strand ν → 𝕜) (a : I × 𝕜) :
    (graph Γ p).loop a = Γ.loop a.1 := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- Absence of recorded zero-weight loops is preserved by refinement. -/
theorem loop_eq_none (p : Strand ν → 𝕜) (hl : ∀ i, Γ.loop i = none) (a : I × 𝕜) :
    (graph Γ p).loop a = none := hl a.1

omit [DecidableEq I] in
/-- The local graph has no zero-weight edge loops whenever the original encoding has none. -/
theorem noZeroLoops (p : Strand ν → 𝕜) (hZ : Γ.NoZeroLoops) : (graph Γ p).NoZeroLoops := by
  intro e he
  have hc := congrArg Prod.fst he
  have hp := congrArg Prod.snd he
  change (coord p e.2).1 = (coord p e.2).1 + Γ.weight e.1 at hp
  have hw : Γ.weight e.1 = 0 := by linear_combination -hp
  exact (hZ e.1 hc hw).elim

omit [DecidableEq I] in
/-- Webster's condition (†) is preserved by taking the walls through a configuration. -/
theorem dagger (p : Strand ν → 𝕜) (hD : Γ.Dagger) : (graph Γ p).Dagger := by
  constructor
  · rintro ⟨e, i⟩ ⟨f, j⟩ ht hh _
    have hc : i = j := (coord p).injective (Subtype.ext (congrArg Prod.snd hh))
    have hw := congrArg Prod.snd ht
    change (coord p i).1 + Γ.weight e = (coord p j).1 + Γ.weight f at hw
    rw [hc] at hw
    have he := hD.1 e f (congrArg Prod.fst ht) (congrArg Prod.fst hh) (add_left_cancel hw)
    exact Prod.ext he hc
  · intro e f ht hh _
    have h₁ := congrArg Prod.snd ht
    have h₂ := congrArg Prod.snd hh
    change (coord p e.2).1 + Γ.weight e.1 = (coord p f.2).1 at h₁
    change (coord p e.2).1 = (coord p f.2).1 + Γ.weight f.1 at h₂
    exact hD.2 e.1 f.1 (congrArg Prod.fst ht) (congrArg Prod.fst hh) (by
      linear_combination h₁ - h₂)

/-- The permutations of the original strands fixing the chosen configuration. -/
def positionStabilizer (p : Strand ν → 𝕜) : Subgroup (ColPerm ν) where
  carrier := {g | ∀ s, p (g.1 s) = p s}
  one_mem' _ := rfl
  mul_mem' hg hh s := (hg _).trans (hh s)
  inv_mem' {g} hg s := by
    change p (g.1.symm s) = p s
    have h := hg (g.1.symm s)
    simpa only [Equiv.apply_symm_apply] using h.symm

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem strandEquiv_symm_label (p : Strand ν → 𝕜) (s : Strand ν) :
    ((strandEquiv p).symm s).label = label p s := by
  simpa only [Equiv.apply_symm_apply] using
    (label_strandEquiv p ((strandEquiv p).symm s)).symm

/-- A refined colour permutation, regarded as a permutation of the original strands. -/
def toColPerm (p : Strand ν → 𝕜) (g : ColPerm (weight p)) : ColPerm ν :=
  ⟨(strandEquiv p).permCongr g.1, fun s => by
    apply Subtype.ext
    change ((strandEquiv p) (g.1 ((strandEquiv p).symm s))).label = s.label
    rw [strandEquiv_colour]
    have hg := congrArg (fun a : (weight p).support => a.1.1) (g.2 ((strandEquiv p).symm s))
    exact hg.trans (by
      simpa only [Equiv.apply_symm_apply, Strand.label] using
        (strandEquiv_colour p ((strandEquiv p).symm s)).symm)⟩

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem toColPerm_apply (p : Strand ν → 𝕜) (g : ColPerm (weight p))
    (s : Strand (weight p)) :
    (toColPerm p g).1 (strandEquiv p s) = strandEquiv p (g.1 s) := by
  exact congrArg (fun t => strandEquiv p (g.1 t)) ((strandEquiv p).symm_apply_apply s)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem toColPerm_preserves (p : Strand ν → 𝕜) (g : ColPerm (weight p)) (s : Strand ν) :
    p ((toColPerm p g).1 s) = p s := by
  obtain ⟨t, rfl⟩ := (strandEquiv p).surjective s
  rw [toColPerm_apply, strandEquiv_coord p (g.1 t), strandEquiv_coord p t]
  exact congrArg (fun a : (weight p).support => a.1.2) (g.2 t)

/-- A colour permutation fixing the configuration, regarded as a refined colour permutation. -/
def ofColPerm (p : Strand ν → 𝕜) (g : ColPerm ν) (hg : ∀ s, p (g.1 s) = p s) :
    ColPerm (weight p) :=
  ⟨(strandEquiv p).symm.permCongr g.1, fun s => by
    apply Subtype.ext
    change ((strandEquiv p).symm (g.1 (strandEquiv p s))).label = s.label
    rw [strandEquiv_symm_label]
    apply Prod.ext
    · exact (congrArg Subtype.val (g.2 (strandEquiv p s))).trans (strandEquiv_colour p s)
    · exact (hg (strandEquiv p s)).trans (strandEquiv_coord p s)⟩

/-- Refined colour permutations are exactly the original colour permutations fixing the point. -/
def colPermEquiv (p : Strand ν → 𝕜) : ColPerm (weight p) ≃* positionStabilizer p where
  toFun g := ⟨toColPerm p g, toColPerm_preserves p g⟩
  invFun g := ofColPerm p g.1 g.2
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro s
    change (strandEquiv p).symm
      (strandEquiv p (g.1 ((strandEquiv p).symm (strandEquiv p s)))) = g.1 s
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro s
    change strandEquiv p ((strandEquiv p).symm
      (g.1.1 (strandEquiv p ((strandEquiv p).symm s)))) = g.1.1 s
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro s
    change strandEquiv p ((g * h).1 ((strandEquiv p).symm s)) =
      strandEquiv p (g.1 ((strandEquiv p).symm (strandEquiv p (h.1 ((strandEquiv p).symm s)))))
    rw [Equiv.symm_apply_apply]
    rfl

/-- The homomorphism forgetting the coordinate part of a refined colour. -/
def perm (p : Strand ν → 𝕜) : ColPerm (weight p) →* ColPerm ν :=
  (positionStabilizer p).subtype.comp (colPermEquiv p).toMonoidHom

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem perm_apply (p : Strand ν → 𝕜) (g : ColPerm (weight p))
    (s : Strand (weight p)) :
    (perm p g).1 (strandEquiv p s) = strandEquiv p (g.1 s) :=
  toColPerm_apply p g s

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem perm_fix_config (p : Strand ν → 𝕜) (g : ColPerm (weight p)) :
    act (perm p g) p = p := by
  funext s
  change p (((perm p g)⁻¹).1 s) = p s
  exact (positionStabilizer p).inv_mem (colPermEquiv p g).2 s

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem strandEquiv_rank_lt {p : Strand ν → 𝕜} {s t : Strand (weight p)}
    (hc : s.1 = t.1) (hr : s.2.val < t.2.val) :
    (strandEquiv p s).2.val < (strandEquiv p t).2.val := by
  rcases s with ⟨a, r⟩
  rcases t with ⟨b, u⟩
  dsimp only at hc
  subst b
  exact (strandEquiv_rank_lt_iff p a r u).2 hr

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The stabilizer condition is equivalent to fixing the configuration under relabelling. -/
theorem mem_positionStabilizer_iff (p : Strand ν → 𝕜) (g : ColPerm ν) :
    g ∈ positionStabilizer p ↔ act g p = p := by
  constructor
  · intro hg
    funext s
    change p (g.1.symm s) = p s
    have h := hg (g.1.symm s)
    simpa only [Equiv.apply_symm_apply] using h.symm
  · intro hg s
    have h := congrFun hg (g.1 s)
    change p (g.1.symm (g.1 s)) = p (g.1 s) at h
    rw [Equiv.symm_apply_apply] at h
    exact h.symm

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem perm_injective (p : Strand ν → 𝕜) : Function.Injective (perm p) := by
  intro g h he
  apply (colPermEquiv p).injective
  exact Subtype.ext he

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Every original colour permutation fixing the point comes from the refined graph. -/
theorem exists_perm_eq (p : Strand ν → 𝕜) (g : ColPerm ν) (hg : act g p = p) :
    ∃ h : ColPerm (weight p), perm p h = g := by
  obtain ⟨h, hh⟩ := (colPermEquiv p).surjective
    ⟨g, (mem_positionStabilizer_iff p g).2 hg⟩
  exact ⟨h, congrArg Subtype.val hh⟩

end Categorification.WeightedKLR.Local
