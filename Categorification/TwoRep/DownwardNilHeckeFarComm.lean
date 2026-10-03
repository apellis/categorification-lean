import Categorification.TwoRep.DownwardNilHecke

/-!
# Far commutativity on actual downward words

The native all-strand consumer is `KLR.NilHecke.IsNilHeckeFamily` (and `KLR.NilHecke.lift`).
This file supplies its three distant-commutativity relations for genuine local downward
operators, on one fixed left-associated word of any positive length. It does not assert
that the remaining local relations have already been propagated to every position.

Positions are counted from the rightmost factor `F r`. Out-of-range generators are zero.
The word has `n + 1` factors; this avoids an artificial identity factor on nonempty words.
No adjunction other than the supplied adjunctions used by `fDot` and `ffCross` is assumed.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe w v u

private theorem prefix_pair_comm {D : Type*} [Bicategory D]
    {a b c d : D} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (t : f ⟶ f) (s : g ≫ h ⟶ g ≫ h) :
    ((t ▷ g) ▷ h) ≫ ((α_ f g h).hom ≫ (f ◁ s) ≫ (α_ f g h).inv) =
      ((α_ f g h).hom ≫ (f ◁ s) ≫ (α_ f g h).inv) ≫ ((t ▷ g) ▷ h) := by
  simp only [Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

namespace StrongSl2
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The upper endpoint of the nonempty downward word. -/
abbrev fWordTop : ℕ → ℤ → ℤ
  | 0, r => r + 1
  | n + 1, r => fWordTop n (r + 1)

/-- The recursive endpoint is the expected weight-string index. -/
theorem fWordTop_eq (n : ℕ) (r : ℤ) : fWordTop n r = r + (n : ℤ) + 1 := by
  induction n generalizing r with
  | zero => simp [fWordTop]
  | succ n ih => rw [fWordTop, ih]; push_cast; ring

/-- The actual left-associated word with `n + 1` downward factors. -/
def fWord : (n : ℕ) → (r : ℤ) → (S.obj (fWordTop n r) ⟶ S.obj r)
  | 0, r => S.F r
  | n + 1, r => fWord n (r + 1) ≫ S.F r

/-- The actual dot at position `i`, zero outside the word. -/
def fWordDot : (n : ℕ) → (r : ℤ) → ℕ → ShiftedHom (S.fWord n r) (S.fWord n r) (2 : ℤ)
  | 0, r, 0 => S.fDot r
  | 0, _, _ + 1 => 0
  | n + 1, r, 0 => shWhiskerLeft (S.fWord n (r + 1)) (S.fDot r)
  | n + 1, r, i + 1 => shWhiskerRight (fWordDot n (r + 1) i) (S.F r)

/-- The actual crossing on the bottom pair. For a word with at least three factors,
the associator is essential and is included explicitly. -/
def fWordBottomCross : (n : ℕ) → (r : ℤ) →
    ShiftedHom (S.fWord (n + 1) r) (S.fWord (n + 1) r) (-2 : ℤ)
  | 0, r => S.ffCross r
  | n + 1, r =>
      (ShiftedHom.mk₀ (0 : ℤ) rfl
        (α_ (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r)).hom).comp
        ((shWhiskerLeft (S.fWord n (r + 1 + 1)) (S.ffCross r)).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            (α_ (S.fWord n (r + 1 + 1)) (S.F (r + 1)) (S.F r)).inv)
          (by norm_num : (0 : ℤ) + -2 = -2)) (by norm_num : (-2 : ℤ) + 0 = -2)

/-- Crossings on every adjacent pair, with zero outside the word. -/
def fWordCross : (n : ℕ) → (r : ℤ) → ℕ →
    ShiftedHom (S.fWord n r) (S.fWord n r) (-2 : ℤ)
  | 0, _, _ => 0
  | n + 1, r, 0 => S.fWordBottomCross n r
  | n + 1, r, i + 1 => shWhiskerRight (fWordCross n (r + 1) i) (S.F r)

/-- The recursive operators recover the previously proved genuine local braid generators. -/
theorem fWordCross_two_zero (r : ℤ) : S.fWordCross 2 r 0 = S.fffCrossRight r := rfl

theorem fWordCross_two_one (r : ℤ) : S.fWordCross 2 r 1 = S.fffCrossLeft r := rfl

/-- Out-of-range dots vanish, rather than introducing extra generators. -/
theorem fWordDot_eq_zero (n i : ℕ) (r : ℤ) (h : n < i) : S.fWordDot n r i = 0 := by
  induction n generalizing r i with
  | zero => cases i with
    | zero => omega
    | succ i => rfl
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i =>
      change shWhiskerRight (S.fWordDot n (r + 1) i) (S.F r) = 0
      rw [ih i (r + 1) (by omega)]
      exact ShiftedHom.map_zero _

/-- Out-of-range crossings vanish, as required by `KLR.NilHecke.IsNilHeckeFamily.d_zero`. -/
theorem fWordCross_eq_zero (n i : ℕ) (r : ℤ) (h : n ≤ i) : S.fWordCross n r i = 0 := by
  induction n generalizing r i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i =>
      change shWhiskerRight (S.fWordCross n (r + 1) i) (S.F r) = 0
      rw [ih i (r + 1) (by omega)]
      exact ShiftedHom.map_zero _

variable [GradedBicategory.ShiftCoherence B]
open GradedHomBicat

/-- Dots on every pair of positions commute on the actual word. -/
theorem fWordDot_comm (n i j : ℕ) (r : ℤ) :
    (S.fWordDot n r i).comp (S.fWordDot n r j) (by norm_num : (2 : ℤ) + 2 = 4) =
      (S.fWordDot n r j).comp (S.fWordDot n r i) (by norm_num : (2 : ℤ) + 2 = 4) := by
  induction n generalizing r i j with
  | zero =>
    cases i <;> cases j
    · rfl
    · change (S.fDot r).comp (0 : ShiftedHom (S.F r) (S.F r) (2 : ℤ)) _ =
        (0 : ShiftedHom (S.F r) (S.F r) (2 : ℤ)).comp (S.fDot r) _
      rw [ShiftedHom.comp_zero, ShiftedHom.zero_comp]
    · change (0 : ShiftedHom (S.F r) (S.F r) (2 : ℤ)).comp (S.fDot r) _ =
        (S.fDot r).comp (0 : ShiftedHom (S.F r) (S.F r) (2 : ℤ)) _
      rw [ShiftedHom.comp_zero, ShiftedHom.zero_comp]
    · rfl
  | succ n ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => exact (shWhisker_exchange (S.fWordDot n (r + 1) j) (S.fDot r)
          (by norm_num) (by norm_num)).symm
    | succ i =>
      cases j with
      | zero =>
        exact shWhisker_exchange (S.fWordDot n (r + 1) i) (S.fDot r)
          (by norm_num) (by norm_num)
      | succ j =>
        simpa only [fWordDot, fWord, fWordTop, shWhiskerRight_comp] using
          congrArg (fun t => shWhiskerRight t (S.F r)) (ih i j (r + 1))

private theorem fWordBottomCross_prefix_comm (n : ℕ) (r : ℤ) {d s : ℤ}
    (t : ShiftedHom (S.fWord n (r + 1 + 1)) (S.fWord n (r + 1 + 1)) d)
    (h₁ : -2 + d = s) (h₂ : d + -2 = s) :
    (shWhiskerRight (shWhiskerRight t (S.F (r + 1))) (S.F r)).comp
        (S.fWordBottomCross (n + 1) r) h₁ =
      (S.fWordBottomCross (n + 1) r).comp
        (shWhiskerRight (shWhiskerRight t (S.F (r + 1))) (S.F r)) h₂ := by
  apply of₂_injective s
  simp only [fWordBottomCross, fWord, ← of₂_comp_of₂, ← of₂_whiskerRight,
    ← incl₂_eq_of₂, ← associator_hom_eq, ← associator_inv_eq, ← whiskerLeft_of₂]
  exact prefix_pair_comm (D := GradedHomBicat B) (of₂ d t) (of₂ (-2) (S.ffCross r))

/-- Every crossing commutes with every dot not on its two strands. -/
theorem fWordCross_dot_comm (n j i : ℕ) (r : ℤ) (h₀ : i ≠ j) (h₁ : i ≠ j + 1) :
    (S.fWordCross n r j).comp (S.fWordDot n r i) (by norm_num : (2 : ℤ) + -2 = 0) =
      (S.fWordDot n r i).comp (S.fWordCross n r j) (by norm_num : (-2 : ℤ) + 2 = 0) := by
  induction n generalizing r i j with
  | zero =>
    change (0 : ShiftedHom (S.fWord 0 r) (S.fWord 0 r) (-2 : ℤ)).comp _ _ =
      (S.fWordDot 0 r i).comp (0 : ShiftedHom (S.fWord 0 r) (S.fWord 0 r) (-2 : ℤ)) _
    rw [ShiftedHom.zero_comp, ShiftedHom.comp_zero]
  | succ n ih =>
    cases j with
    | succ j =>
      cases i with
      | zero =>
        exact shWhisker_exchange (S.fWordCross n (r + 1) j) (S.fDot r)
          (by norm_num) (by norm_num)
      | succ i =>
        simpa only [fWordCross, fWordDot, fWord, shWhiskerRight_comp] using
          congrArg (fun t => shWhiskerRight t (S.F r))
            (ih j i (r + 1) (by omega) (by omega))
    | zero =>
      obtain ⟨i, rfl⟩ : ∃ a, i = a + 2 := ⟨i - 2, by omega⟩
      cases n with
      | zero =>
        rw [S.fWordDot_eq_zero 1 (i + 2) r (by omega)]
        rw [ShiftedHom.zero_comp, ShiftedHom.comp_zero]
      | succ n =>
        exact (S.fWordBottomCross_prefix_comm n r (S.fWordDot n (r + 1 + 1) i)
          (by norm_num) (by norm_num)).symm

/-- Crossings at every pair of disjoint adjacent positions commute, on the same actual
left-associated word. This includes the boundary cases where one crossing is zero. -/
theorem fWordCross_comm (n i j : ℕ) (r : ℤ) (h : i + 1 < j) :
    (S.fWordCross n r i).comp (S.fWordCross n r j) (by norm_num : (-2 : ℤ) + -2 = -4) =
      (S.fWordCross n r j).comp (S.fWordCross n r i) (by norm_num : (-2 : ℤ) + -2 = -4) := by
  induction n generalizing r i j with
  | zero => rfl
  | succ n ih =>
    cases i with
    | succ i =>
      obtain ⟨j, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
      simpa only [fWordCross, fWord, shWhiskerRight_comp] using
        congrArg (fun t => shWhiskerRight t (S.F r)) (ih i j (r + 1) (by omega))
    | zero =>
      obtain ⟨j, rfl⟩ : ∃ a, j = a + 2 := ⟨j - 2, by omega⟩
      cases n with
      | zero =>
        rw [S.fWordCross_eq_zero 1 (j + 2) r (by omega)]
        rw [ShiftedHom.zero_comp, ShiftedHom.comp_zero]
      | succ n =>
        exact (S.fWordBottomCross_prefix_comm n r (S.fWordCross n (r + 1 + 1) j)
          (by norm_num) (by norm_num)).symm

end StrongSl2
end Categorification.TwoRep
