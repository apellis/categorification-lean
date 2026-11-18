/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.DiagR
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleDownDiagram
import Categorification.WeightedKLR.RedStrands.DownwardCornerMap

/-!
# Ordinary generators in the all-down block

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.5, Definition 4.27 and Lemma 4.28. The ordinary boundary idempotents, dots
and crossings are represented by the corresponding signed layers in the
violating quotient. An affine KLR map with these generator images descends
through `T^λ` to the all-down block.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram TypeA
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {ℓ : ℕ}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  {k : Type*} [CommRing k] {ν : Multiset I}
  (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "A" => downwardMatrix P ν

/-- Interpret a signed layer with the displayed all-down boundaries. -/
def downLayer (s t : Ord) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ))
    (hs : u ++ g.bottom ++ v = (word s.val).map DoubleStrand.down)
    (ht : u ++ g.top ++ v = (word t.val).map DoubleStrand.down) : downObj P s ⟶ downObj P t :=
  (violatingFunctor P _).map (InducedCategory.homMk
    (P.layer (layer RD (Subtype.val ∘ Λ) 0 u g v) (layer_valid ..)
      ((layer_dom ..).trans (congrArg (obj RD (Subtype.val ∘ Λ) 0) hs))
      ((layer_cod ..).trans (congrArg (obj RD (Subtype.val ∘ Λ) 0) ht))))

/-- Interpret the black dot layer at a specified black position. -/
def downBlackDot (s : Ord) (a : Fin m) (i : I) (h : s.val.lbl a = .inl i) : End (downObj P s) :=
  have hw := congrArg (List.map DoubleStrand.down) (word_split s.val a)
  have hs : ((word s.val).take a).map DoubleStrand.down ++
      (Move.black (.dot (false, i))).bottom ++
      ((word s.val).drop (a + 1)).map DoubleStrand.down = (word s.val).map DoubleStrand.down := by
    simpa only [List.map_append, List.map_cons, List.map_nil, h, DoubleStrand.down,
      Move.bottom, KL3.Diagram.Shape.dom] using hw
  downLayer P s s _ (.black (.dot (false, i))) _ hs hs

/-- The dot on a physical downward black strand, in the violating quotient. -/
def downDot (s : Ord) (a : Fin m) : End (downObj P s) :=
  match h : s.val.lbl a with
  | .inr _ => 0
  | .inl i => downBlackDot P s a i h

theorem downDot_of_black (s : Ord) (a : Fin m) (i : I) (h : s.val.lbl a = .inl i) :
    downDot P s a = downBlackDot P s a i h := by
  unfold downDot
  split
  · rename_i r hr
    rw [h] at hr
    cases hr
  · rename_i i' hi
    have he : i' = i := Sum.inl.inj (hi.symm.trans h)
    subst i'
    rfl

theorem downDot_eq_zero_of_red (s : Ord) (a : Fin m) (h : (s.val.lbl a).isRight) :
    downDot P s a = 0 := by
  unfold downDot
  split
  · rfl
  · rename_i i hi
    simp [hi] at h

/-- The allowed adjacent crossings after orienting black strands downward. -/
abbrev downCrossMove (a b : I ⊕ Fin ℓ) : Option (Move I ℓ) := downMove (.cross a b)

private theorem downCrossMove_words {a b : I ⊕ Fin ℓ} {g : Move I ℓ}
    (h : downCrossMove a b = some g) :
    g.bottom = [DoubleStrand.down a, DoubleStrand.down b] ∧
      g.top = [DoubleStrand.down b, DoubleStrand.down a] := downMove_words h

/-- Interpret the physical crossing layer between the two adjacent-swap boundaries. -/
def downCrossLayer (s t : Ord) (j : ℕ) (hj : j + 1 < m) (ht : t.val = sadj m j • s.val)
    (g : Move I ℓ) (hg : downCrossMove (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩) = some g) :
    downObj P s ⟶ downObj P t :=
  have hg' := downCrossMove_words hg
  have hs := congrArg (List.map DoubleStrand.down) (word_split₂ s.val hj)
  have ht' := (congrArg (List.map DoubleStrand.down) (word_sadj s.val hj)).symm
  downLayer P s t ((word s.val).take j |>.map DoubleStrand.down) g
    ((word s.val).drop (j + 2) |>.map DoubleStrand.down)
    (by simpa only [hg'.1, List.map_append, List.map_cons, List.map_nil] using hs)
    (by simpa only [hg'.2, ht, List.map_append, List.map_cons, List.map_nil] using ht')

/-- A physical crossing of two downward black strands, a downward black and a red strand,
or a red and a downward black strand. An entry with incompatible endpoints is zero. -/
def downCross (s t : Ord) (j : ℕ) : downObj P s ⟶ downObj P t :=
  if hj : j + 1 < m then
    if ht : t.val = sadj m j • s.val then
      match hg : downCrossMove (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩) with
      | none => 0
      | some g => downCrossLayer P s t j hj ht g hg
    else 0
  else 0

theorem downCross_of_move (s t : Ord) (j : ℕ) (hj : j + 1 < m) (ht : t.val = sadj m j • s.val)
    (g : Move I ℓ) (hg : downCrossMove (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩) = some g) :
    downCross P s t j = downCrossLayer P s t j hj ht g hg := by
  unfold downCross
  rw [dite_eq_left hj, dite_eq_left ht]
  split
  · rename_i hnone
    rw [hg] at hnone
    cases hnone
  · rename_i g' hg'
    have h : g' = g := Option.some.inj (hg'.symm.trans hg)
    subst g'
    rfl

/-- Boundary idempotent, extended by zero for an unordered red loading. -/
def downE (s : Seq μ) : A := if h : IsRedOrdered s then MatEnd.single ⟨s, h⟩ ⟨s, h⟩ (𝟙 _) else 0

/-- The diagonal matrix of physical dot layers. -/
def downX (a : Fin m) : A := ∑ s : Ord, MatEnd.single s s (downDot P s a)

/-- The matrix of physical crossing layers. -/
def downΨ (j : ℕ) : A := fun s t => downCross P s t j

theorem downE_of_ordered (s : Ord) : downE P s.val = MatEnd.single s s (𝟙 _) := by
  rw [downE, dite_eq_left s.property]

theorem downE_of_unordered (s : Seq μ) (h : ¬ IsRedOrdered s) : downE P s = 0 := dite_eq_right h

theorem downE_of_violated (s : Seq μ) (h : IsViolated s) : downE P s = 0 := by
  by_cases hs : IsRedOrdered s
  · rw [downE, dite_eq_left hs, downObj_id_eq_zero P (⟨s, hs⟩ : Ord) h, MatEnd.single_zero]
  · exact downE_of_unordered P s hs

private theorem downE_apply_eq_zero_of_source_ne {s : Seq μ} {i j : Ord} (h : i.val ≠ s) :
    downE P s i j = 0 := by
  by_cases hs : IsRedOrdered s
  · rw [downE, dite_eq_left hs]
    exact MatEnd.single_apply_of_ne _ (fun he => h (congrArg Subtype.val he.1))
  · rw [downE_of_unordered P s hs, MatEnd.zero_apply]

private theorem mul_downE_apply (f : A) (s : Seq μ) (i j : Ord) :
    (f * downE P s) i j = if i.val = s then f i j else 0 := by
  rw [MatEnd.mul_apply]
  by_cases hi : i.val = s
  · rw [ite_eq_left hi, ← hi, downE_of_ordered P i, Finset.sum_eq_single i]
    · simp
    · intro t _ ht
      rw [MatEnd.single_apply_of_ne _ (fun h => ht h.2), Limits.zero_comp]
    · simp
  · rw [ite_eq_right hi]
    exact Finset.sum_eq_zero fun t _ => by
      rw [downE_apply_eq_zero_of_source_ne P hi, Limits.zero_comp]

private theorem downE_mul_apply (f : A) (s : Seq μ) (i j : Ord) :
    (downE P s * f) i j = if j.val = s then f i j else 0 := by
  rw [MatEnd.mul_apply]
  by_cases hj : j.val = s
  · rw [ite_eq_left hj, ← hj, downE_of_ordered P j, Finset.sum_eq_single j]
    · simp
    · intro t _ ht
      rw [MatEnd.single_apply_of_ne _ (fun h => ht h.1), Limits.comp_zero]
    · simp
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro t _
    by_cases hs : IsRedOrdered s
    · rw [downE, dite_eq_left hs]
      rw [MatEnd.single_apply_of_ne _ (fun he => hj (congrArg Subtype.val he.2)), Limits.comp_zero]
    · rw [downE_of_unordered P s hs, MatEnd.zero_apply, Limits.comp_zero]

theorem downE_mul_downE (s t : Seq μ) :
    downE P s * downE P t = if s = t then downE P s else 0 := by
  apply MatEnd.ext
  intro i j
  rw [mul_downE_apply]
  split_ifs with hi he he
  · rfl
  · exact downE_apply_eq_zero_of_source_ne P (fun h => he (h.symm.trans hi))
  · exact (downE_apply_eq_zero_of_source_ne P (fun h => hi (h.trans he))).symm
  · rfl

theorem sum_downE : (∑ s : Seq μ, downE P s) = 1 := by
  apply MatEnd.ext
  intro i j
  rw [MatEnd.sum_apply, Finset.sum_eq_single i.val, downE_of_ordered P i]
  · by_cases hij : i = j
    · subst j; simp
    · rw [MatEnd.one_apply_of_ne hij, MatEnd.single_apply_of_ne _ (fun h => hij h.2.symm)]
  · intro t _ ht
    exact downE_apply_eq_zero_of_source_ne P ht.symm
  · simp

theorem downX_apply_self (a : Fin m) (s : Ord) : downX P a s s = downDot P s a := by
  rw [downX, MatEnd.sum_apply, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    exact MatEnd.single_apply_of_ne _ (fun h => ht h.1.symm)
  · simp

theorem downX_apply_of_ne (a : Fin m) {s t : Ord} (h : s ≠ t) : downX P a s t = 0 := by
  rw [downX, MatEnd.sum_apply]
  exact Finset.sum_eq_zero fun r _ => MatEnd.single_apply_of_ne _ (fun hr => h (hr.1.trans hr.2.symm))

theorem downX_mul_downE (a : Fin m) (s : Seq μ) :
    downX P a * downE P s = downE P s * downX P a := by
  apply MatEnd.ext
  intro i j
  rw [mul_downE_apply, downE_mul_apply]
  by_cases hij : i = j
  · subst j; rfl
  · simp [downX_apply_of_ne P a hij]

theorem downX_mul_downE_of_red (a : Fin m) (s : Seq μ) (h : (s.lbl a).isRight) :
    downX P a * downE P s = 0 := by
  apply MatEnd.ext
  intro i j
  rw [mul_downE_apply, MatEnd.zero_apply]
  split_ifs with hi
  · by_cases hij : i = j
    · subst j
      rw [downX_apply_self, downDot_eq_zero_of_red P i a (hi.symm ▸ h)]
    · exact downX_apply_of_ne P a hij
  · rfl

theorem downΨ_apply_of_ne (j : ℕ) {s t : Ord} (h : t.val ≠ sadj m j • s.val) :
    downΨ P j s t = 0 := by
  by_cases hj : j + 1 < m <;> simp [downΨ, downCross, hj, h]

theorem downΨ_mul_downE (j : ℕ) (s : Seq μ) :
    downΨ P j * downE P s = downE P (sadj m j • s) * downΨ P j := by
  apply MatEnd.ext
  intro i t
  rw [mul_downE_apply, downE_mul_apply]
  by_cases ht : t.val = sadj m j • i.val
  · have he : i.val = s ↔ t.val = sadj m j • s := by
      rw [ht]
      exact (sadj_smul_injective j).eq_iff.symm
    rw [if_congr he rfl rfl]
  · simp [downΨ_apply_of_ne P j ht]

theorem downΨ_eq_zero {j : ℕ} (hj : m ≤ j + 1) : (downΨ P j : A) = 0 := by
  apply MatEnd.ext
  intro i t
  simp [downΨ, downCross, Nat.not_lt_of_ge hj]

theorem downΨ_mul_downE_of_red (j : ℕ) (hj : j + 1 < m) (s : Seq μ)
    (ha : (s.lbl ⟨j, by omega⟩).isRight) (hb : (s.lbl ⟨j + 1, hj⟩).isRight) :
    downΨ P j * downE P s = 0 := by
  apply MatEnd.ext
  intro i t
  rw [mul_downE_apply, MatEnd.zero_apply]
  split_ifs with he
  · have h₀ : (i.val.lbl ⟨j, by omega⟩).isRight := he.symm ▸ ha
    have h₁ : (i.val.lbl ⟨j + 1, hj⟩).isRight := he.symm ▸ hb
    rcases hleft : i.val.lbl ⟨j, by omega⟩ with a | r
    · simp [hleft] at h₀
    rcases hright : i.val.lbl ⟨j + 1, hj⟩ with b | p
    · simp [hright] at h₁
    apply downΨ_apply_of_ne P j
    intro ht
    have hlt : (⟨j, by omega⟩ : Fin m) < ⟨j + 1, hj⟩ := Fin.mk_lt_mk.2 (by omega)
    have hr : r < p := i.property _ _ _ _ hlt hleft hright
    have h' := t.property _ _ p r hlt
      (by rw [ht, KLRAlgebra.lbl_sadj_left hj]; exact hright)
      (by rw [ht, KLRAlgebra.lbl_sadj_right hj]; exact hleft)
    exact hr.not_gt h'
  · rfl

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (ρ : KLRAlgebra k (affineCoverQ Q exponents) (stendhalWeight ℓ ν) →ₐ[k] downwardMatrix P ν)
  (he : ∀ s : Seq (stendhalWeight ℓ ν), ρ (KLRAlgebra.e s) = downE P s)
  (hx : ∀ a : Fin (stendhalWeight ℓ ν).card, ρ (KLRAlgebra.x a) = downX P a)

include he hx in
private theorem allDownIdeal_le_ker : affineTensorIdeal Q exponents ν ≤
    TwoSidedIdeal.ker ρ.toRingHom := by
  apply TwoSidedIdeal.span_le.mpr
  rintro a (⟨s, j, hj, rfl⟩ | ⟨s, hs, rfl⟩)
  · apply (TwoSidedIdeal.mem_ker ρ.toRingHom).mpr
    change ρ (_ * _) = 0
    rw [map_mul, hx, he, downX_mul_downE_of_red P j s hj]
  · apply (TwoSidedIdeal.mem_ker ρ.toRingHom).mpr
    change ρ (KLRAlgebra.e s) = 0
    rw [he]
    rcases hs with hs | hs
    · exact downE_of_unordered P s hs
    · exact downE_of_violated P s hs

/-- Descend the ordinary affine map into the all-down block of Webster,
arXiv:1309.3796v2, Lemma 4.28. The red dots and the identities of violated
or unordered boundaries vanish for the displayed signed layers. -/
def allDownMap : TensorProductAlgebra k Q exponents ν →ₐ[k] A :=
  affineTensorLift ρ (allDownIdeal_le_ker P Q exponents ρ he hx)

theorem allDownMap_comp_affine : (allDownMap P Q exponents ρ he hx).comp
    (affineTensorProjection exponents ν) = ρ :=
  affineTensorLift_comp _ _

end Categorification.Stendhal.DoubleDiagram
