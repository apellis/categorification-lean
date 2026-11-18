/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownLift

/-!
# All-down boundaries in cap elimination

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, citing Khovanov–Lauda,
arXiv:0807.3250, Lemma 3.9. A cut in a diagram with an all-down source
has two extra strands for every upward strand at that cut. In particular
no summand can factor nontrivially through a shorter sequence. The outputs
without caps in a cap-push procedure have only ordinary downward layers.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)

private def up : DoubleStrand I ℓ → Bool
  | .inl (ε, _) => ε
  | .inr _ => false

/-- Number of upward black strands at a signed boundary or horizontal cut. -/
def upCount (s : List (DoubleStrand I ℓ)) : ℕ := s.countP up

private theorem up_down (z : I ⊕ Fin ℓ) : up (DoubleStrand.down z) = false := by
  cases z <;> rfl

private theorem upCount_down (z : List (I ⊕ Fin ℓ)) : upCount (z.map DoubleStrand.down) = 0 := by
  induction z with
  | nil => rfl
  | cons h t ih => simp [upCount, up_down] at *

private def charge (s : List (DoubleStrand I ℓ)) : ℤ := (s.length : ℤ) - 2 * (upCount s : ℤ)

private theorem charge_append (s t : List (DoubleStrand I ℓ)) :
    charge (s ++ t) = charge s + charge t := by
  simp [charge, upCount, List.countP_append]; ring

private theorem charge_move (g : Move I ℓ) : charge g.top = charge g.bottom := by
  cases g with
  | black g =>
    cases g with
    | dot => rfl
    | cross ε i j => cases ε <;> rfl
    | cup l | cap l => obtain ⟨ε, i⟩ := l; cases ε <;> rfl
  | blackRed l r | redBlack r l => obtain ⟨ε, i⟩ := l; cases ε <;> rfl

/-- The exact length of any cut reached from an all-down word, including its red strands. -/
theorem cut_length_from_allDown (μ : X) (z : List (I ⊕ Fin ℓ)) {a : Obj (signature RD Λ)}
    (d : obj RD Λ μ (z.map DoubleStrand.down) ⟶ a) :
    a.word.length = z.length + 2 * upCount (a.word.map Prod.snd) := by
  have h := chain_wordInvariant RD Λ charge
    (fun u g v => by simp only [charge_append, charge_move]) (Diagram.chain d)
  change charge (a.word.map Prod.snd) = charge ((colours RD Λ μ (z.map DoubleStrand.down)).map Prod.snd) at h
  simp only [forget_colours, charge, List.length_map, upCount_down, Nat.cast_zero, mul_zero, sub_zero] at h
  omega

/-- The Hom from an all-down boundary to any shorter boundary is zero in every
signed presentation. This discharges the shorter-sequence remainder of a cap push. -/
theorem hom_eq_zero_of_shorter_than_allDown (μ : X) (z : List (I ⊕ Fin ℓ)) {a : Obj (signature RD Λ)}
    (ha : a.word.length < z.length) (f : P.obj (obj RD Λ μ (z.map DoubleStrand.down)) ⟶ P.obj a) :
    f = 0 := by
  induction f using P.hom_induction with
  | diag d => have h := cut_length_from_allDown RD Λ μ z d; omega
  | zero => rfl
  | add f g hf hg => simp [hf, hg]
  | smul c f hf => simp [hf]

/-- A downward-facing local maximum of a black strand. -/
def Move.IsCap : Move I ℓ → Prop
  | .black (.cap _) => True
  | _ => False

private theorem length_colours (μ : X) (z : List (DoubleStrand I ℓ)) :
    (colours RD Λ μ z).length = z.length := by
  simpa only [List.length_map] using congrArg List.length (forget_colours RD Λ μ z)

private theorem layer_lengths (L : Layer (signature RD Λ)) :
    L.dom.word.length = L.left.length + L.gen.2.bottom.length + L.right.length ∧
    L.cod.word.length = L.left.length + L.gen.2.top.length + L.right.length := by
  simp [Layer.dom, Layer.cod, signature, length_colours, Nat.add_assoc]

private theorem move_length_le_of_not_cap {g : Move I ℓ} (h : ¬g.IsCap) :
    g.bottom.length ≤ g.top.length := by
  cases g with
  | black g => cases g <;> simp_all [Move.IsCap, Move.bottom, Move.top]
  | blackRed | redBlack => rfl

private theorem chain_length_le_of_no_caps {a b : Obj (signature RD Λ)} {ls}
    (h : Chain a ls b) (hn : ∀ L ∈ ls, ¬L.gen.2.IsCap) : a.word.length ≤ b.word.length := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    rw [← h.2.1]
    apply le_trans _ (ih h.2.2 (fun M hm => hn M (List.mem_cons_of_mem _ hm)))
    have hg := move_length_le_of_not_cap (hn L (by simp))
    rw [(layer_lengths RD Λ L).1, (layer_lengths RD Λ L).2]
    omega

private theorem downMove_of_level {g : Move I ℓ} (hu : upCount g.bottom = 0)
    (h : g.bottom.length = g.top.length) : ∃ k, downMove k = some g := by
  cases g with
  | black g =>
    cases g with
    | dot l =>
      obtain ⟨ε,i⟩ := l
      cases ε with
      | false => exact ⟨.dot (.inl i), rfl⟩
      | true => contradiction
    | cross ε i j =>
      cases ε with
      | false => exact ⟨.cross (.inl i) (.inl j), rfl⟩
      | true => contradiction
    | cup | cap => contradiction
  | blackRed l r =>
    obtain ⟨ε,i⟩ := l
    cases ε with
    | false => exact ⟨.cross (.inl i) (.inr r), rfl⟩
    | true => contradiction
  | redBlack r l =>
    obtain ⟨ε,i⟩ := l
    cases ε with
    | false => exact ⟨.cross (.inr r) (.inl i), rfl⟩
    | true => contradiction

private theorem layers_down_of_no_caps {a b : Obj (signature RD Λ)} {ls}
    (h : Chain a ls b) (hn : ∀ L ∈ ls, ¬L.gen.2.IsCap)
    (hu : upCount (a.word.map Prod.snd) = 0) (hl : a.word.length = b.word.length) :
    ∀ L ∈ ls, ∃ g, downMove g = some L.gen.2 := by
  induction ls generalizing a with
  | nil => simp
  | cons L ls ih =>
    have hn' : ∀ M ∈ ls, ¬M.gen.2.IsCap := fun M hm => hn M (List.mem_cons_of_mem _ hm)
    have hshort := chain_length_le_of_no_caps RD Λ h.2.2 hn'
    have hg := move_length_le_of_not_cap (hn L (by simp))
    obtain ⟨hd,hc⟩ := layer_lengths RD Λ L
    rw [← h.2.1] at hu hl
    have hlen : L.gen.2.bottom.length = L.gen.2.top.length := by omega
    have he : upCount (L.left.map Prod.snd) + upCount L.gen.2.bottom +
        upCount (L.right.map Prod.snd) = 0 := by
      simpa only [Layer.dom_word, signature, List.map_append, forget_colours, upCount,
        List.countP_append] using hu
    have hbottom : upCount L.gen.2.bottom = 0 := by omega
    have htop : upCount L.gen.2.top = 0 := by
      have hp := charge_move L.gen.2
      simp only [charge, hlen, hbottom, Nat.cast_zero, mul_zero, sub_zero] at hp
      omega
    have hcod : upCount (L.cod.word.map Prod.snd) = 0 := by
      have he' : upCount (L.left.map Prod.snd) + upCount L.gen.2.top +
          upCount (L.right.map Prod.snd) = 0 := by omega
      simpa only [Layer.cod_word, signature, List.map_append, forget_colours, upCount,
        List.countP_append] using he'
    intro M hM
    rcases List.mem_cons.mp hM with rfl | hm
    · exact downMove_of_level hbottom hlen
    · exact ih h.2.2 hn' hcod (by omega) M hm

/-- A cap-free signed diagram between all-down boundaries has only downward layers. -/
theorem all_layers_down_of_no_caps (μ : X) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (d : downContextObj RD Λ μ [] [] a ⟶ downContextObj RD Λ μ [] [] b)
    (hn : ∀ L ∈ Diagram.layers d, ¬L.gen.2.IsCap) :
    ∀ L ∈ Diagram.layers d, ∃ g, downMove g = some L.gen.2 := by
  apply layers_down_of_no_caps RD Λ (Diagram.chain d) hn
  · simp [downContextObj, obj, forget_colours, upCount_down]
  · have hs : downContextObj RD Λ μ [] [] a = obj RD Λ μ (a.word.map DoubleStrand.down) := by
      simp [downContextObj]
    have h := cut_length_from_allDown RD Λ μ a.word (Diagram.cast d hs rfl)
    have hl : a.word.length = b.word.length := by
      simpa [downContextObj, obj, forget_colours, upCount_down, length_colours RD Λ] using h.symm
    simpa [downContextObj, obj, length_colours RD Λ] using hl

/-- Every cap-free term on all-down boundaries in the cap-elimination argument for
Webster, arXiv:1309.3796v2, Lemma 4.28 lifts to an ordinary diagram. In particular,
the presence of cups need not be excluded separately. -/
theorem exists_downDiagramLift_of_no_caps (μ : X) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (d : downContextObj RD Λ μ [] [] a ⟶ downContextObj RD Λ μ [] [] b)
    (hn : ∀ L ∈ Diagram.layers d, ¬L.gen.2.IsCap) :
    ∃ f : a ⟶ b, downLinear RD Λ k μ [] [] (LinDiagram.of f) = LinDiagram.of d :=
  exists_downDiagramLift RD Λ k μ d (all_layers_down_of_no_caps RD Λ μ d hn)

end Categorification.Stendhal.DoubleDiagram
