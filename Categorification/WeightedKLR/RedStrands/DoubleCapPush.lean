/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCapElimination
import Categorification.WeightedKLR.RedStrands.DoubleDownSpan

/-!
# Induction on excursions above an all-down boundary

In the geometric spanning step of Webster, arXiv:1309.3796v2, §4.5,
Lemma 4.28, cuts reached from an all-down word acquire two strands for each
upward strand. At maximum width a diagram therefore has a cup, a (possibly
empty) string of dots and crossings, and a cap. It suffices to lower one such
excursion locally, in its exterior diagram. The two induction parameters are
the maximum upward count and the number of layers reaching it. No bound on
the length of the replacement is needed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram TypeA
open scoped Classical

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {Λ : Fin ℓ → X}

local notation "S" => signature RD Λ

/-- The number of upward black strands at the cut. -/
def cutHeight (a : Obj S) : ℕ := upCount (a.word.map Prod.snd)

/-- The cut heights at the top of the individual layers. -/
def cutHeights (ls : List (Layer S)) : List ℕ := ls.map fun L => cutHeight L.cod

private theorem upCount_cons (l : DoubleStrand I ℓ) (s : List (DoubleStrand I ℓ)) :
    upCount (l :: s) = upCount s + (match l with | .inl (true, _) => 1 | _ => 0) := by
  simp only [upCount, List.countP_cons]
  cases l with
  | inl l => obtain ⟨ε,i⟩ := l; cases ε <;> rfl
  | inr => rfl

/-- The height of an all-down loading is zero. -/
theorem cutHeight_down (μ : X) (s : List (I ⊕ Fin ℓ)) :
    cutHeight (obj RD Λ μ (s.map DoubleStrand.down)) = 0 := by
  simp only [cutHeight, obj, forget_colours]
  induction s with
  | nil => rfl
  | cons l s ih => cases l <;> simpa only [List.map_cons, DoubleStrand.down, upCount_cons, Nat.add_zero] using ih

private theorem layer_height (L : Layer S) :
    cutHeight L.dom = upCount (L.left.map Prod.snd) + upCount L.gen.2.bottom +
      upCount (L.right.map Prod.snd) ∧
    cutHeight L.cod = upCount (L.left.map Prod.snd) + upCount L.gen.2.top +
      upCount (L.right.map Prod.snd) := by
  constructor <;> simp only [cutHeight, Layer.dom, Layer.cod, signature, List.map_append,
    forget_colours, upCount, List.countP_append]

/-- The generator types are detected by the two adjacent cut heights. -/
theorem layer_height_change (L : Layer S) :
    (cutHeight L.dom < cutHeight L.cod ↔ ∃ l, L.gen.2 = .black (.cup l)) ∧
    (cutHeight L.cod < cutHeight L.dom ↔ L.gen.2.IsCap) := by
  obtain ⟨hd,hc⟩ := layer_height L
  rw [hd,hc]
  have hn : upCount ([] : List (DoubleStrand I ℓ)) = 0 := rfl
  cases hg : L.gen.2 with
  | black g =>
    cases g with
    | dot l => obtain ⟨ε,i⟩ := l; cases ε <;> simp [Move.IsCap, Move.top, Move.bottom,
        KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod]
    | cross ε i j => cases ε <;> simp [Move.IsCap, Move.top, Move.bottom,
        KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod, upCount_cons, hn]
    | cup l | cap l =>
      obtain ⟨ε,i⟩ := l; cases ε <;> simp [Move.IsCap, Move.top, Move.bottom,
        KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod, KL3.Diagram.Letter.dual, upCount_cons, hn]
  | blackRed l r | redBlack r l =>
    obtain ⟨ε,i⟩ := l; cases ε <;> simp [Move.IsCap, Move.top, Move.bottom, upCount_cons, hn]

private theorem plateau_exit {a b : Obj S} {ls : List (Layer S)} {n : ℕ} (h : Chain a ls b)
    (ha : cutHeight a = n) (hb : cutHeight b < n) (hle : ∀ L ∈ ls, cutHeight L.cod ≤ n) :
    ∃ mid cap post, ls = mid ++ cap :: post ∧
      (∀ L ∈ mid, cutHeight L.dom = n ∧ cutHeight L.cod = n) ∧
      cutHeight cap.dom = n ∧ cutHeight cap.cod < n := by
  induction ls generalizing a with
  | nil => rw [show a = b from h] at ha; omega
  | cons L ls ih =>
    have hd : cutHeight L.dom = n := h.2.1 ▸ ha
    have hc := hle L (by simp)
    by_cases e : cutHeight L.cod = n
    · obtain ⟨mid,cap,post,hm,hmid,hcap⟩ := ih h.2.2 e (fun M m => hle M (by simp [m]))
      exact ⟨L :: mid, cap, post, congrArg (L :: ·) hm, by simpa [hd, e] using hmid, hcap⟩
    · exact ⟨[], L, ls, rfl, by simp, by rw [h.2.1, ha], by omega⟩

/-- A maximum strictly above both endpoints occurs on a single excursion.
The interior consists of level generators, including crossings through red. -/
theorem exists_maximal_excursion {a b : Obj S} {ls : List (Layer S)} {n : ℕ} (h : Chain a ls b)
    (ha : cutHeight a < n) (hb : cutHeight b < n) (hle : ∀ L ∈ ls, cutHeight L.cod ≤ n)
    (hit : n ∈ cutHeights ls) :
    ∃ pre cup mid cap post, ls = pre ++ cup :: mid ++ cap :: post ∧
      (∃ l, cup.gen.2 = .black (.cup l)) ∧ cutHeight cup.cod = n ∧
      (∀ L ∈ mid, cutHeight L.dom = n ∧ cutHeight L.cod = n) ∧
      cap.gen.2.IsCap ∧ cutHeight cap.cod < n := by
  induction ls generalizing a with
  | nil => simp [cutHeights] at hit
  | cons L ls ih =>
    have hc := hle L (by simp)
    have htail : ∀ M ∈ ls, cutHeight M.cod ≤ n := fun M m => hle M (by simp [m])
    by_cases e : cutHeight L.cod = n
    · obtain ⟨mid,cap,post,hm,hmid,hcap,hbelow⟩ := plateau_exit h.2.2 e hb htail
      exact ⟨[], L, mid, cap, post, congrArg (L :: ·) hm, (layer_height_change L).1.mp
        (by rw [h.2.1,e]; exact ha), e, hmid, (layer_height_change cap).2.mp (by omega), hbelow⟩
    · obtain ⟨pre,cup,mid,cap,post,he,rest⟩ := ih h.2.2 (by omega) htail
        (by simpa [cutHeights, Ne.symm e] using hit)
      exact ⟨L :: pre,cup,mid,cap,post,congrArg (L :: ·) he,rest⟩

private theorem no_caps_at_zero {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    (ha : cutHeight a = 0) (hle : ∀ L ∈ ls, cutHeight L.cod ≤ 0) :
    ∀ L ∈ ls, ¬ L.gen.2.IsCap := by
  induction ls generalizing a with
  | nil => simp
  | cons L ls ih =>
    have hL := hle L (by simp)
    intro M hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [← (layer_height_change M).2, h.2.1, ha]
      exact Nat.not_lt_zero _
    · exact ih h.2.2 (by omega) (fun M m => hle M (by simp [m])) M hm

variable {weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w,max u v} (signature RD (Subtype.val ∘ weights)) k) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "labels" => (Subtype.val ∘ weights)
local notation "W" => fun s : Ord => obj RD labels 0 (List.map DoubleStrand.down (word (Subtype.val s)))
local notation "E" => fun (s t : Ord) (d : W s ⟶ W t) => signedDownEntry P s t (Presentation.diag P d)

/-- A cap-free diagram projects to the ordinary downward span. -/
theorem downward_of_no_caps (s t : Ord) (d : W s ⟶ W t)
    (hd : ∀ L ∈ Diagram.layers d, ¬L.gen.2.IsCap) : E s t d ∈ downwardDiagramSpan P s t := by
  let ds := downContextObj_word (RD := RD) (Λ := weights) s.val
  let dt := downContextObj_word (RD := RD) (Λ := weights) t.val
  let d' := Diagram.cast d ds.symm dt.symm
  apply Submodule.subset_span
  refine ⟨d', all_layers_down_of_no_caps RD labels 0 d' (by simpa [d'] using hd), ?_⟩
  change _ = signedDownEntry P s t (P.castHom ds dt (P.diag d'))
  rw [Presentation.castHom_diag]
  congr 2

/-- Lower one maximal excursion in its exterior context. The allowed terms
have the same prefix and suffix, and every cut of the replacement is strictly
below the maximum. Membership is tested after imposing violated boundaries. -/
def LowersMaximalExcursions (s t : Ord) : Prop :=
  ∀ (n : ℕ) (pre mid post : List (Layer (signature RD labels))) (cup cap : Layer (signature RD labels))
    (h : Chain (W s) (pre ++ cup :: mid ++ cap :: post) (W t)),
    (∀ L ∈ pre ++ cup :: mid ++ cap :: post, cutHeight L.cod ≤ n) →
    (∃ l, cup.gen.2 = .black (.cup l)) → cutHeight cup.cod = n →
    (∀ L ∈ mid, cutHeight L.dom = n ∧ cutHeight L.cod = n) →
    cap.gen.2.IsCap → cutHeight cap.cod < n →
    E s t (Diagram.mk _ h) ∈ Submodule.span k
      {x | ∃ low : List (Layer (signature RD labels)),
        ∃ hl : Chain (W s) (pre ++ low ++ post) (W t),
          (∀ L ∈ low, cutHeight L.cod < n) ∧ x = E s t (Diagram.mk _ hl)}

/-- The two-parameter cap elimination induction, with ordinary lifts as its
height-zero base and arbitrary linear combinations in each peak replacement. -/
theorem downwardDiagramSpan_eq_top_of_lowering (s t : Ord) (lower : LowersMaximalExcursions P s t) :
    downwardDiagramSpan P s t = ⊤ := by
  apply downwardDiagramSpan_eq_top_of_diagrams
  intro d
  suffices H : ∀ n (ls : List (Layer (signature RD labels)))
      (h : Chain (W s) ls (W t)), (∀ L ∈ ls, cutHeight L.cod ≤ n) →
        E s t (Diagram.mk _ h) ∈ downwardDiagramSpan P s t by
    apply H ((cutHeights (Diagram.layers d)).sum) (Diagram.layers d) (Diagram.chain d)
    intro L hL
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨L,hL,rfl⟩)
  intro n
  induction n with
  | zero =>
    intro ls h hl
    exact downward_of_no_caps P s t _ (no_caps_at_zero h (cutHeight_down ..) hl)
  | succ n ih =>
    suffices H : ∀ r (ls : List (Layer (signature RD labels))) (h : Chain (W s) ls (W t)),
        (∀ L ∈ ls, cutHeight L.cod ≤ n+1) → (cutHeights ls).count (n+1) = r →
        E s t (Diagram.mk _ h) ∈ downwardDiagramSpan P s t from
      fun ls h hl => H _ ls h hl rfl
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ihr =>
      intro ls h hl hr
      by_cases hit : n+1 ∈ cutHeights ls
      · obtain ⟨pre,cup,mid,cap,post,rfl,hcup,hc,hm,hcap,he⟩ :=
          exists_maximal_excursion h (by rw [cutHeight_down]; omega) (by rw [cutHeight_down]; omega) hl hit
        refine Submodule.span_le.mpr ?_ (lower _ pre mid post cup cap h hl hcup hc hm hcap he)
        rintro _ ⟨low,hlow,hlt,rfl⟩
        apply ihr _ _ _ hlow _ rfl
        · have hlc : (cutHeights low).count (n+1) = 0 := List.count_eq_zero.mpr (by
            intro hmem
            obtain ⟨L,hL,hE⟩ := List.mem_map.mp hmem
            have := hlt L hL
            omega)
          simp only [cutHeights, List.map_append, List.map_cons, List.count_append, hc,
            List.count_cons_self, List.count_cons_of_ne he.ne] at hr ⊢
          change (List.map (fun L => cutHeight L.cod) low).count (n + 1) = 0 at hlc
          omega
        · intro L hL
          rcases List.mem_append.mp hL with hL | hL
          · rcases List.mem_append.mp hL with hL | hL
            · apply hl L; simp [hL]
            · exact le_of_lt (hlt L hL)
          · apply hl L; simp [hL]
      · apply ih _ h
        intro L hL
        have hb := hl L hL
        have hne : cutHeight L.cod ≠ n+1 := by
          intro he; apply hit; exact List.mem_map.mpr ⟨L,hL,he⟩
        omega

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (scalars : I → I → kˣ)
local notation "P₁" => addRedUpRelations RD labels k
  (addMixedBlackRelations RD labels k scalars (addDownRelations RD labels (affineCoverQ Q exponents) P))

/-- Local lowering of maximal excursions suffices for the surjectivity assertion
in Webster, arXiv:1309.3796v2, Lemma 4.28 at the fixed content. -/
theorem ordinaryToDownwardMatrix_surjective_of_lowering
    (h : ∀ s t : Ord, LowersMaximalExcursions (P₁) s t) :
    Function.Surjective (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)) := by
  intro M
  apply mem_range_ordinaryToDownwardMatrix_of_downwardDiagramSpan
  intro s t
  rw [downwardDiagramSpan_eq_top_of_lowering (P₁) s t (h s t)]
  exact Submodule.mem_top

end Categorification.Stendhal.DoubleDiagram
