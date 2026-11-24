/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleJointLoading

/-!
# The crossing position in the paired block

For the internal alternative in Webster (arXiv:1309.3796v2), §6.1, Lemma 6.8,
the position of the second paired red identifies the block containing the
crossing. The local swap of that block leaves the exterior loadings fixed.
-/

namespace Categorification.Stendhal.RedBlock

open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ}

private theorem red_label_in_block {B : RedBlock I ℓ} (s : Seq B.localWeight) {r : Fin ℓ}
    {a : Fin B.weight.card} (ha : (Seq.map B.colour s).lbl a = .inr r) :
    ∃ c : Fin B.size, B.label c = r := by
  rw [Seq.map_lbl] at ha
  cases he : s.lbl (Fin.cast (Multiset.card_map B.colour B.localWeight) a) with
  | inl i => simp [he, RedBlock.colour] at ha
  | inr c =>
    exact ⟨c, by simpa [he, RedBlock.colour] using ha⟩

private theorem red_label_in_row {r : Fin ℓ} :
    ∀ (Bs : List (RedBlock I ℓ)) (s : Loadings Bs) (a : Fin (weightSum Bs).card),
      (place Bs s).lbl a = .inr r → ∃ B ∈ Bs, ∃ c : Fin B.size, B.label c = r
  | [], _, a, _ => Fin.elim0 a
  | B :: Bs, s, a, ha => by
    obtain ⟨a | a, rfl⟩ := (blockEquiv (Seq.card_add' B.weight (weightSum Bs))).surjective a
    · have h : (Seq.map B.colour s.1).lbl a = .inr r := by
        change (place (B::Bs) s).lbl (Seq.posL _ a) = _ at ha
        simpa only [place, Seq.append_posL] using ha
      obtain ⟨c,hc⟩ := red_label_in_block s.1 h
      exact ⟨B, List.mem_cons_self, c, hc⟩
    · have h : (place Bs s.2).lbl a = .inr r := by
        change (place (B::Bs) s).lbl (Seq.posR _ a) = _ at ha
        simpa only [place, Seq.append_posR] using ha
      obtain ⟨D,hD,c,hc⟩ := red_label_in_row Bs s.2 a h
      exact ⟨D,List.mem_cons_of_mem _ hD,c,hc⟩

/-- Position of the distinguished block in the juxtaposed row. -/
def pairOffset : List (Fin ℓ × Multiset I) → ℕ
  | [] => 0
  | x :: xs => (spectator x).weight.card + pairOffset xs

/-- An internal crossing with the second distinguished red on its right must lie
inside the distinguished two-red block. -/
theorem insideBlock_at_pair (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β))
      (a : ℕ) (ha : a+1 < (weightSum (adjacentRow L M f β)).card),
      f 1 ∉ L.map Prod.fst → f 1 ∉ M.map Prod.fst →
      InsideBlock (adjacentRow L M f β) a →
      (place (adjacentRow L M f β) s).lbl ⟨a+1,ha⟩ = .inr (f 1) →
      ∃ b, a = pairOffset L + b ∧ b+1 < (⟨2,f,β⟩ : RedBlock I ℓ).weight.card
  | [], s, a, ha, _, hm, hin, hred => by
    let B : RedBlock I ℓ := ⟨2,f,β⟩
    let Bs := M.map spectator
    change (a+1 < B.weight.card ∨ ∃ b, a = B.weight.card+b ∧ InsideBlock Bs b) at hin
    rcases hin with ho | ⟨b,hb,_⟩
    · exact ⟨a,by simp [pairOffset],ho⟩
    · have hpos : b+1 < (weightSum Bs).card := by
        change a+1 < (B.weight + weightSum Bs).card at ha
        rw [Multiset.card_add,hb] at ha
        omega
      have hidx : (⟨a+1,ha⟩ : Fin (weightSum (adjacentRow [] M f β)).card) =
          Seq.posR B.weight ⟨b+1,hpos⟩ := by
        apply Fin.ext
        simp only [Seq.posR_val]
        omega
      rw [hidx] at hred
      have ht : (place Bs s.2).lbl ⟨b+1,hpos⟩ = .inr (f 1) := by
        change ((Seq.map B.colour s.1).append (place Bs s.2)).lbl
          (Seq.posR B.weight ⟨b+1,hpos⟩) = _ at hred
        exact (Seq.append_posR (Seq.map B.colour s.1) (place Bs s.2) ⟨b+1,hpos⟩).symm.trans hred
      obtain ⟨D,hD,c,hc⟩ := red_label_in_row Bs s.2 _ ht
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hD
      change x.1 = f 1 at hc
      exact (hm (hc ▸ List.mem_map_of_mem (f := Prod.fst) hx)).elim
  | x :: xs, s, a, ha, hl, hm, hin, hred => by
    let B := spectator x
    let Bs := adjacentRow xs M f β
    change (a+1 < B.weight.card ∨ ∃ b, a = B.weight.card+b ∧ InsideBlock Bs b) at hin
    rcases hin with ho | ⟨b,hb,hbi⟩
    · have hidx : (⟨a+1,ha⟩ : Fin (weightSum (adjacentRow (x::xs) M f β)).card) =
          Seq.posL (weightSum Bs) ⟨a+1,ho⟩ := by
        apply Fin.ext
        rfl
      rw [hidx] at hred
      have ht : (Seq.map B.colour s.1).lbl ⟨a+1,ho⟩ = .inr (f 1) := by
        change ((Seq.map B.colour s.1).append (place Bs s.2)).lbl
          (Seq.posL (weightSum Bs) ⟨a+1,ho⟩) = _ at hred
        simpa only [Seq.append_posL] using hred
      obtain ⟨c,hc⟩ := red_label_in_block s.1 ht
      change x.1 = f 1 at hc
      exact (hl (hc ▸ List.mem_cons_self)).elim
    · have hpos : b+1 < (weightSum Bs).card := by
        change a+1 < (B.weight + weightSum Bs).card at ha
        rw [Multiset.card_add,hb] at ha
        omega
      have hidx : (⟨a+1,ha⟩ : Fin (weightSum (adjacentRow (x::xs) M f β)).card) =
          Seq.posR B.weight ⟨b+1,hpos⟩ := by
        apply Fin.ext
        simp only [Seq.posR_val]
        omega
      rw [hidx] at hred
      have ht : (place Bs s.2).lbl ⟨b+1,hpos⟩ = .inr (f 1) := by
        change ((Seq.map B.colour s.1).append (place Bs s.2)).lbl
          (Seq.posR B.weight ⟨b+1,hpos⟩) = _ at hred
        exact (Seq.append_posR (Seq.map B.colour s.1) (place Bs s.2) ⟨b+1,hpos⟩).symm.trans hred
      obtain ⟨c,hc,hvalid⟩ := insideBlock_at_pair M f β xs s.2 b hpos
        (fun hz => hl (List.mem_cons_of_mem _ hz)) hm hbi ht
      exact ⟨c,by rw [pairOffset,hb,hc,add_assoc],hvalid⟩

/-- The loading in the distinguished block of a juxtaposed row. -/
def pairLoading (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      Seq (⟨2,f,β⟩ : RedBlock I ℓ).localWeight
  | [], s => s.1
  | _ :: L, s => pairLoading M f β L s.2

/-- The local loading in the paired block keeps identity red order for an
uncrossed row. -/
theorem redWord_pairLoading (M : List (Fin ℓ × Multiset I))
    (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    ∀ L (s : Loadings (adjacentRow L M f β)), UncrossedLoading _ s →
      redWord (pairLoading M f β L s) = List.finRange 2
  | [], _, h => h.1
  | _ :: L, s, h => redWord_pairLoading M f β L s.2 h.2

/-- Read an ambient label at a position of the paired block. -/
theorem place_lbl_pairOffset (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) :
    ∀ L (s : Loadings (adjacentRow L M f β)) (b : Fin (⟨2,f,β⟩ : RedBlock I ℓ).weight.card)
      (hb : pairOffset L + b.val < (weightSum (adjacentRow L M f β)).card),
      (place (adjacentRow L M f β) s).lbl ⟨pairOffset L + b.val,hb⟩ =
        (Seq.map (⟨2,f,β⟩ : RedBlock I ℓ).colour (pairLoading M f β L s)).lbl b
  | [], s, b, hb => by
    let B : RedBlock I ℓ := ⟨2,f,β⟩
    let Bs := M.map spectator
    have hi : (⟨pairOffset [] + b.val,hb⟩ : Fin (weightSum (adjacentRow [] M f β)).card) =
        Seq.posL (weightSum Bs) b := by
      apply Fin.ext
      simp only [pairOffset, Nat.zero_add, Seq.posL_val]
    rw [hi]
    exact Seq.append_posL (Seq.map B.colour s.1) (place Bs s.2) b
  | x :: xs, s, b, hb => by
    let B := spectator x
    let Bs := adjacentRow xs M f β
    have hpos : pairOffset xs + b.val < (weightSum Bs).card := by
      change pairOffset (x :: xs) + b.val < (B.weight + weightSum Bs).card at hb
      rw [pairOffset, Multiset.card_add] at hb
      change B.weight.card + pairOffset xs + b.val < B.weight.card + (weightSum Bs).card at hb
      omega
    let a : Fin (weightSum Bs).card := ⟨pairOffset xs + b.val, hpos⟩
    have hi : (⟨pairOffset (x :: xs) + b.val,hb⟩ :
        Fin (weightSum (adjacentRow (x :: xs) M f β)).card) = Seq.posR B.weight a := by
      apply Fin.ext
      change (B.weight.card + pairOffset xs) + b.val = B.weight.card + (pairOffset xs + b.val)
      exact Nat.add_assoc _ _ _
    rw [hi]
    exact (Seq.append_posR (Seq.map B.colour s.1) (place Bs s.2) a).trans
      (place_lbl_pairOffset M f β xs s.2 b hpos)

/-- Swap the two adjacent positions of the paired loading, keeping the spectators. -/
def swapPairLoading (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) (b : ℕ) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      Loadings (adjacentRow L M f β)
  | [], s => (sadj (⟨2,f,β⟩ : RedBlock I ℓ).localWeight.card b • s.1, s.2)
  | _ :: L, s => (s.1, swapPairLoading M f β b L s.2)

private theorem pairOffset_lt (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) (b : ℕ) (hb : b+1 < (⟨2,f,β⟩ : RedBlock I ℓ).weight.card) :
    ∀ L, pairOffset L + b + 1 < (weightSum (adjacentRow L M f β)).card
  | [] => by
    change 0 + b + 1 < ((⟨2,f,β⟩ : RedBlock I ℓ).weight + weightSum (M.map spectator)).card
    rw [Multiset.card_add, Nat.zero_add]
    omega
  | x :: L => by
    have hi := pairOffset_lt M f β b hb L
    change (spectator x).weight.card + pairOffset L + b + 1 <
      ((spectator x).weight + weightSum (adjacentRow L M f β)).card
    rw [Multiset.card_add]
    omega

/-- The local swap in the pair is the ambient adjacent swap at its row offset. -/
theorem place_swapPairLoading (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) (b : ℕ) (hb : b+1 < (⟨2,f,β⟩ : RedBlock I ℓ).weight.card) :
    ∀ L (s : Loadings (adjacentRow L M f β)),
      place (adjacentRow L M f β) (swapPairLoading M f β b L s) =
        sadj (weightSum (adjacentRow L M f β)).card (pairOffset L + b) • place (adjacentRow L M f β) s
  | [], s => by
    let B : RedBlock I ℓ := ⟨2,f,β⟩
    let t := place (M.map spectator) s.2
    change (Seq.map B.colour (sadj B.localWeight.card b • s.1)).append t =
      sadj (B.weight + weightSum (M.map spectator)).card (0+b) • ((Seq.map B.colour s.1).append t)
    rw [Nat.zero_add, Seq.sadj_smul_append_left hb]
    congr 1
    apply Subtype.ext
    funext m
    change B.colour (s.1.lbl ((sadj B.localWeight.card b).symm (Fin.cast _ m))) =
      B.colour (s.1.lbl (Fin.cast _ ((sadj B.weight.card b).symm m)))
    rw [cast_sadj_symm]
  | x :: L, s => by
    let B := spectator x
    let Bs := adjacentRow L M f β
    let p := Seq.map B.colour s.1
    change p.append (place Bs (swapPairLoading M f β b L s.2)) =
      sadj (B.weight + weightSum Bs).card ((B.weight.card + pairOffset L) + b) • (p.append (place Bs s.2))
    rw [Nat.add_assoc, Seq.sadj_smul_append_right (pairOffset_lt M f β b hb L),
      place_swapPairLoading M f β b hb L s.2]

end Categorification.Stendhal.RedBlock
