/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.SpacedEntries
import Categorification.WeightedKLR.Cartan
import Categorification.KLR.KL2.K0Relations

/-!
# Divided-power projectives for evenly spaced loadings

Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19, uses the positive quantum group of
the loop-free weighted graph. Its divided-power projectives come from the evenly
spaced loading algebra of Proposition 2.14. The shift and factorial relation
are those of Khovanov–Lauda I, arXiv:0803.4121v2, §2.5 (`P_î ≅ P_i^{i!}`), with
the arbitrary Cartan grading of Khovanov–Lauda II, arXiv:0804.2080v1, §3.

The splitting maps lie in one ordinary sequence corner. Applying the diagonal
entry of the spaced comparison gives the splitting of weighted projectives at
that loading, over every commutative coefficient ring.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR Categorification.KLR.KL2
  LaurentPolynomial QuantumGroup KLRAlgebra
open GalleryAlgebra (WeightedKLRAlgebra)

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I}

local notation "A" => KLRAlgebra k Γ.klrQ ν
local notation "W" => WeightedKLRAlgebra k Γ ν.toFinsupp
local notation "idem" => KLRAlgebra.e

/-- The projective of an ordinary word, at its spaced loading (Webster Proposition 2.14). -/
def spacedProjSeq (G : GradingDatum Γ) (t : Seq ν) : GProj (G.klrGrade ν.toFinsupp) :=
  GProj.ofIdempotent (spacedW k Γ t) (isIdempotentElem_spacedW t)
    (G.e_mem_grade (spacedFull Γ t))

variable (G : GradingDatum Γ) (hS : Γ.Standing) (hD : Γ.Dagger)
  (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)

local notation "H" => G.toKLRGrading hne hl
local notation "entry[" t "]" => spacedEntryMap hS hD hne hl t t

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem hflip_mem_ordinaryGrade {a : A} {d : ℤ} (ha : a ∈ (H).grade ν d) :
    KLRAlgebra.hflip a ∈ (H).grade ν d :=
  (H).hflip_mem_grade G.pairDeg_comm ha

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem e_mul_divIdem {t : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks t bs) :
    (idem t * divIdem t bs : A) = divIdem t bs := by
  rw [divIdem, ← mul_assoc, ← blocksElt_mul_e h.const, mul_assoc, e_mul_self]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem hflip_divIdem_mul_e {t : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks t bs) :
    (hflip (divIdem t bs) * idem t : A) = hflip (divIdem t bs) := by
  rw [← hflip_e (k := k) (Q := Γ.klrQ) t, ← hflip_mul, e_mul_divIdem h]

private theorem isIdempotentElem_spacedFlip {t : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks t bs) :
    IsIdempotentElem (entry[t] (hflip (divIdem t bs))) :=
  isIdempotentElem_spacedEntryMap hS hD hne hl (isIdempotentElem_hflip_divIdem h)
    (hflip_divIdem_mul_e h)

private theorem spacedFlip_mem_klrGrade {t : Seq ν} {bs : List (ℕ × ℕ)} (h : IsBlocks t bs) :
    entry[t] (hflip (divIdem t bs)) ∈ G.klrGrade ν.toFinsupp 0 :=
  G.spacedEntryMap_mem_klrGrade hS hD hne hl
    (hflip_mem_ordinaryGrade G hne hl (divIdem_mem_grade H h)) t t

/-- The principal projective of the flipped nilHecke block idempotents, before the shift. -/
def spacedProjFlip (t : Seq ν) (bs : List (ℕ × ℕ)) (h : IsBlocks t bs) :
    GProj (G.klrGrade ν.toFinsupp) :=
  GProj.ofIdempotent (entry[t] (hflip (divIdem t bs)))
    (isIdempotentElem_spacedFlip hS hD hne hl h) (spacedFlip_mem_klrGrade G hS hD hne hl h)

/-- The graded projective of a divided-power word in Webster's standing grading. The convention
is `P_i = W ψ(1_i) {-⟨i⟩}` from KL I §2.5, with the half dot degrees of KL II §3. -/
def spacedProjDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    GProj (hS.gradingDatum.klrGrade ν.toFinsupp) :=
  (hS.gradingDatum.spacedProjFlip hS hD hne hl _ _ (isBlocks_ofList d h)).shift
    (-divAngle2 hS.cartanDatum d)

private theorem K0_spacedProjFlip_congr {t : Seq ν} {bs bs' : List (ℕ × ℕ)}
    (h : IsBlocks t bs) (h' : IsBlocks t bs') (he : (divIdem t bs : A) = divIdem t bs') :
    K0.of (G.spacedProjFlip hS hD hne hl t bs h) =
      K0.of (G.spacedProjFlip hS hD hne hl t bs' h') :=
  K0.of_ofIdempotent_congr (congrArg (entry[t] ∘ hflip) he) _ _ _ _

private theorem K0_spacedProjFlip_succ {t : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks t ((p, n + 1) :: bs)) {d : ℤ}
    (hdeg : ∀ a : Fin ν.card, p ≤ a → (a : ℕ) < p + (n + 1) → G.dot (t.lbl a) = 2 * d) :
    K0.of (G.spacedProjFlip hS hD hne hl t ((p, n) :: bs) (h.cons_mono (Nat.le_succ n))) =
      (T (-(d * n)) * qint (tUnit d) (n + 1)) •
        K0.of (G.spacedProjFlip hS hD hne hl t ((p, n + 1) :: bs) h) := by
  let hpn := h.le _ List.mem_cons_self
  let hc := h.const _ List.mem_cons_self
  let a : Fin (n + 1) → A := fun j => divIdem t bs * blockA k Γ.klrQ t hpn j
  let b : Fin (n + 1) → A := fun j => blockB k Γ.klrQ t hpn j
  -- Left multiplication by the sequence idempotent gives right support after the flip.
  let F : A →+ W := (entry[t]).toAddMonoidHom.comp
    (KLR.GradingDatum.hflipAddHom.comp (AddMonoidHom.mulLeft (idem t)))
  have hF (x : A) : F x = entry[t] (hflip (idem t * x)) := rfl
  have hFmul {x : A} (hx : x * idem t = x) (y : A) : F (x * y) = F y * F x := by
    simp only [hF]
    have hy : hflip (idem t * y) * idem t = hflip (idem t * y) := by
      calc
        _ = hflip (idem t * y) * hflip (idem t) := by rw [hflip_e]
        _ = hflip (idem t * (idem t * y)) := (hflip_mul _ _).symm
        _ = _ := by rw [← mul_assoc, e_mul_self]
    rw [← spacedEntryMap_mul_of_right_support hS hD hne hl _ hy t t,
      ← hflip_mul, mul_assoc (idem t) x (idem t * y), ← mul_assoc x, hx]
  have hFA (j : Fin (n + 1)) : a j * idem t = a j := by
    simp only [a, blockA, mul_assoc, e_mul_self]
  have hFB (j : Fin (n + 1)) : b j * idem t = b j := by
    simp only [b, blockB, mul_assoc, e_mul_self]
  have S := isSplitting_divIdem_succ (k := k) (Q := Γ.klrQ) h
  have S' : IsSplitting (F (divIdem t ((p, n) :: bs)))
      (fun _ => F (divIdem t ((p, n + 1) :: bs))) (F ∘ b) (F ∘ a) := by
    constructor
    · intro i j
      change F (a i) * F (b j) = if i = j then _ else _
      rw [← hFmul (hFB j)]
      change F (blockB k Γ.klrQ t hpn j * a i) = _
      rw [S.mul_eq j i]
      by_cases hij : i = j
      · subst j; simp
      · simp only [hij, Ne.symm hij, ite_false, map_zero]
    · change ∑ j, F (b j) * F (a j) = _
      calc
        _ = ∑ j, F (a j * b j) := Finset.sum_congr rfl fun j _ => (hFmul (hFA j) (b j)).symm
        _ = _ := by rw [← map_sum]; exact congrArg F S.sum_eq
  have hfix {bs' : List (ℕ × ℕ)} (ht : IsBlocks t bs') :
      F (divIdem t bs') = entry[t] (hflip (divIdem t bs')) := by
    rw [hF, e_mul_divIdem ht]
  rw [hfix h, hfix (h.cons_mono (Nat.le_succ n))] at S'
  have hp : p < ν.card := by
    have hp' : p + (n + 1) ≤ ν.card := hpn
    omega
  have hpc : p < p + (n + 1) := by omega
  have hcl : ∀ a : Fin ν.card, p ≤ a → (a : ℕ) < p + (n + 1) →
      t.lbl a = t.lbl ⟨p, hp⟩ := fun a h1 h2 => hc a _ h1 h2 le_rfl hpc
  have hd : (H).degX (t.lbl ⟨p, hp⟩) = 2 * d := hdeg ⟨p, hp⟩ le_rfl hpc
  have hmem {x : A} {r : ℤ} (hx : x ∈ (H).grade ν r) : F x ∈ G.klrGrade ν.toFinsupp r := by
    have hproduct : idem t * x ∈ (H).grade ν r := by
      simpa only [zero_add] using SetLike.mul_mem_graded ((H).e_mem_grade t) hx
    exact G.spacedEntryMap_mem_klrGrade hS hD hne hl (hflip_mem_ordinaryGrade G hne hl hproduct) t t
  have hb (j : Fin (n + 1)) : F (b j) ∈ G.klrGrade ν.toFinsupp
      ((H).degX (t.lbl ⟨p, hp⟩) * ((n : ℤ) - j)) :=
    hmem (blockB_mem_grade H hpn hcl hc (show (j : ℕ) ≤ n by omega))
  have ha (j : Fin (n + 1)) : F (a j) ∈ G.klrGrade ν.toFinsupp
      (-((H).degX (t.lbl ⟨p, hp⟩) * ((n : ℤ) - j))) := by
    apply hmem
    have h' := SetLike.mul_mem_graded (divIdem_mem_grade H h.tail)
      (blockA_mem_grade H hpn hcl hc j)
    convert h' using 2
    ring
  have hIdem {bs'} (ht : IsBlocks t bs') := isIdempotentElem_spacedFlip hS hD hne hl ht
  have hZero {bs'} (ht : IsBlocks t bs') := spacedFlip_mem_klrGrade G hS hD hne hl ht
  let hsmall := h.cons_mono (Nat.le_succ n)
  rw [spacedProjFlip, spacedProjFlip,
    K0.of_ofIdempotent_eq_sum_of_isSplitting S' hb ha
      (hIdem hsmall) (fun _ => hIdem h) (hZero hsmall) (fun _ => hZero h),
    hd, ← sum_T_mul_sub, Finset.sum_smul]

private theorem K0_spacedProjFlip_block {t : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)}
    (hbs : IsBlocks t bs) {d : ℤ} :
    ∀ {n : ℕ} (h : IsBlocks t ((p, n) :: bs))
      (_hdeg : ∀ a : Fin ν.card, p ≤ a → (a : ℕ) < p + n → G.dot (t.lbl a) = 2 * d),
      K0.of (G.spacedProjFlip hS hD hne hl t bs hbs) = blockFactor2 d n •
        K0.of (G.spacedProjFlip hS hD hne hl t ((p, n) :: bs) h)
  | 0, h, _ => by
    rw [blockFactor2_zero, one_smul]
    refine K0_spacedProjFlip_congr G hS hD hne hl hbs h ?_
    rw [divIdem, divIdem, blocksElt_cons]
    simp only [blockElt_zero, one_mul]
  | n + 1, h, hdeg => by
    rw [K0_spacedProjFlip_block hbs (h.cons_mono (Nat.le_succ n))
      (fun a h1 h2 => hdeg a h1 (by omega)), K0_spacedProjFlip_succ G hS hD hne hl h hdeg,
      ← mul_smul, blockFactor2_succ]

private theorem K0_spacedProjSeq_eq_prod_smul {t : Seq ν} (d : ℕ → ℤ) :
    ∀ {bs : List (ℕ × ℕ)} (h : IsBlocks t bs)
      (_hdeg : ∀ b ∈ bs, ∀ a : Fin ν.card, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
        G.dot (t.lbl a) = 2 * d b.1),
      K0.of (G.spacedProjSeq t) = (bs.map fun b => blockFactor2 (d b.1) b.2).prod •
        K0.of (G.spacedProjFlip hS hD hne hl t bs h)
  | [], h, _ => by
    rw [List.map_nil, List.prod_nil, one_smul]
    exact K0.of_ofIdempotent_congr
      (by rw [divIdem_nil, hflip_e, spacedEntryMap_idem_self]) _ _ _ _
  | b :: bs, h, hdeg => by
    rw [K0_spacedProjSeq_eq_prod_smul d h.tail (fun b' hb' => hdeg b' (List.mem_cons_of_mem _ hb')),
      K0_spacedProjFlip_block G hS hD hne hl (p := b.1) (n := b.2) h.tail h
        (hdeg b List.mem_cons_self), List.map_cons, List.prod_cons, ← mul_smul, mul_comm]

/-- The factorial relation `[P_î] = i! [P_i]` in the weighted Grothendieck group. This is the
transport of KL I, arXiv:0803.4121v2, §2.5, through Webster, arXiv:1209.2463v4,
Proposition 2.14, with the Cartan grading of KL II, arXiv:0804.2080v1, §3. -/
theorem K0_spacedProjSeq_expandDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.of (hS.gradingDatum.spacedProjSeq (KLRAlgebra.Seq.ofList (expandDiv d) h)) =
      divQFact2 hS.cartanDatum d • K0.of (spacedProjDiv hS hD hne hl d h) := by
  have hdeg : ∀ b ∈ blocksDiv d 0, ∀ a : Fin ν.card, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
      hS.gradingDatum.dot ((KLRAlgebra.Seq.ofList (expandDiv d) h).lbl a) =
        2 * labHalf hS.cartanDatum (expandDiv d) b.1 := by
    intro b hb a h1 h2
    have hm : (expandDiv d).length = ν.card := by rw [← Multiset.coe_card, h]
    have hb1 : b.1 < ν.card := lt_of_le_of_lt h1 a.2
    have hc := (isBlocks_ofList d h).const b hb a ⟨b.1, hb1⟩ h1 h2 le_rfl (by simp only; omega)
    rw [hc, KLRAlgebra.Seq.ofList_lbl, labHalf_of_lt _ (by rwa [hm]), hS.gradingDatum_dot,
      hS.cartanDatum_dot_self]
    simp only []
    omega
  rw [K0_spacedProjSeq_eq_prod_smul _ hS hD hne hl _ (isBlocks_ofList d h) hdeg]
  have hprod := prod_blockFactor2_blocksDiv (C := hS.cartanDatum) d []
  simp only [List.length_nil, List.nil_append] at hprod
  rw [hprod, spacedProjDiv, ← K0.T_smul_of, ← mul_smul, mul_comm]

end Categorification.WeightedKLR.GradingDatum
