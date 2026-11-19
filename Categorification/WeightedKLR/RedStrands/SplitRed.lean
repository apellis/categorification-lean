/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedLoading
import Categorification.KLR.Concat

/-!
# Splitting a red strand: the algebra map

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. Let `λ'_1, …, λ'_{ℓ+1}` be dominant weights and let `λ` be the sequence of
`ℓ` weights obtained by merging `λ'_c` and `λ'_{c+1}` into `λ'_c + λ'_{c+1}`. Replacing the red
strand `λ'_c + λ'_{c+1}` of a Stendhal diagram by two parallel red strands `λ'_c`, `λ'_{c+1}`
defines an algebra map from the Stendhal algebra of `λ` into the corner of the Stendhal algebra
of `λ'` cut out by the loadings in which the two red strands are adjacent.

This file constructs the generators of that corner and the relations they satisfy.

## Main definitions

* `mergeWeights Λ' c` : the weights `λ` with `λ'_c` and `λ'_{c+1}` merged.
* `splitIdem` : the sum of the idempotents of the split loadings.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv MvPolynomial

/-! ### Generic facts about Stendhal algebras -/

section Generic

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {L : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin L → I →₀ ℕ} {ν : Multiset I}

local notation "B" => StendhalAlgebraAllOrders k Q Λ ν
local notation "n" => Multiset.card (stendhalWeight L ν)

open StendhalAlgebraAllOrders

theorem aSum_e : (∑ s : Seq (stendhalWeight L ν), e s : B) = 1 := by
  simp only [e, ← map_sum, KLRAlgebra.sum_e, map_one]

theorem aψ_mul_e (j : ℕ) (s : Seq (stendhalWeight L ν)) :
    (ψ j * e s : B) = e (sadj n j • s) * ψ j := by
  rw [ψ, e, e, ← map_mul, KLRAlgebra.ψ_mul_e, map_mul]

theorem aψ_eq_zero (j : ℕ) (h : n ≤ j + 1) : (ψ j : B) = 0 := by
  rw [ψ, KLRAlgebra.ψ_eq_zero j h, map_zero]

theorem aψ_mul_ψ (j l : ℕ) (h : j + 1 < l) : (ψ j * ψ l : B) = ψ l * ψ j := by
  rw [ψ, ψ, ← map_mul, KLRAlgebra.ψ_mul_ψ j l h, map_mul]

theorem ax_mul_ψ (a : Fin n) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (x a * ψ j : B) = ψ j * x a := by
  rw [x, ψ, ← map_mul, KLRAlgebra.x_mul_ψ a j h₁ h₂, map_mul]

theorem ae_mul_e (s t : Seq (stendhalWeight L ν)) :
    (e s * e t : B) = if s = t then e s else 0 := e_mul_e s t

variable (k Q Λ ν) in
/-- Polynomials in the dots. -/
def polA : MvPolynomial (Fin n) k →ₐ[k] B :=
  (ofKLR k Q Λ ν).comp KLRAlgebra.pol

theorem polA_X (a : Fin n) : polA k Q Λ ν (X a) = x a := by
  simp [polA, x]

theorem e_commute_polA (s : Seq (stendhalWeight L ν)) (p : MvPolynomial (Fin n) k) :
    Commute (e s : B) (polA k Q Λ ν p) := by
  have := (KLRAlgebra.e_commute_pol (Q := stendhalQ Q Λ) s p).map (ofKLR k Q Λ ν)
  simpa [polA, e] using this

theorem ncEval_x_eq_polA {r : ℕ} (f : Fin r → Fin n) (p : MvPolynomial (Fin r) k) :
    ncEval (fun a => (x (f a) : B)) p = polA k Q Λ ν (rename f p) := by
  simp_rw [← polA_X]
  exact ncEval_algHom_X _ f p

/-- The quadratic relation in a Stendhal algebra. -/
theorem aψ_sq (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    (ψ j * ψ j * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then 0 else
        polA k Q Λ ν (rename ![⟨j, by omega⟩, ⟨j + 1, h⟩]
          (stendhalQ Q Λ (s.lbl ⟨j, by omega⟩) (s.lbl ⟨j + 1, h⟩))) * e s := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) j h s)
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j + 1, h⟩] :
      Fin 2 → KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight L ν)) =
      fun a => KLRAlgebra.x (![⟨j, by omega⟩, ⟨j + 1, h⟩] a) := by
    funext a; fin_cases a <;> rfl
  rw [hv, KLRAlgebra.ncEval_eq_pol] at key
  split_ifs at key ⊢ <;> simpa [ψ, e, polA] using key

/-- The braid relation in a Stendhal algebra. -/
theorem aBraid (j : ℕ) (h : j + 2 < n) (s : Seq (stendhalWeight L ν)) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 2, h⟩ ∧
          s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, by omega⟩ then
        polA k Q Λ ν (rename ![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩]
          (qbar (stendhalQ Q Λ (s.lbl ⟨j, by omega⟩) (s.lbl ⟨j + 1, by omega⟩)))) * e s
      else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.braid (Q := stendhalQ Q Λ) j h s)
  have hv : (![KLRAlgebra.x ⟨j, by omega⟩, KLRAlgebra.x ⟨j + 1, by omega⟩,
      KLRAlgebra.x ⟨j + 2, h⟩] : Fin 3 → KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight L ν)) =
      fun a => KLRAlgebra.x (![⟨j, by omega⟩, ⟨j + 1, by omega⟩, ⟨j + 2, h⟩] a) := by
    funext a; fin_cases a <;> rfl
  rw [hv, KLRAlgebra.ncEval_eq_pol] at key
  split_ifs at key ⊢ <;> simpa [ψ, e, polA] using key

theorem aDotCrossLeft (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    ((x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then e s else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_left (Q := stendhalQ Q Λ) j h s)
  split_ifs at key ⊢ <;> simpa [ψ, e, x] using key

theorem aDotCrossRight (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν)) :
    ((ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e s : B) =
      if s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩ then e s else 0 := by
  have key := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_right (Q := stendhalQ Q Λ) j h s)
  split_ifs at key ⊢ <;> simpa [ψ, e, x] using key

theorem ax_mul_e (a : Fin n) (s : Seq (stendhalWeight L ν)) : (x a * e s : B) = e s * x a := by
  rw [← polA_X]; exact (e_commute_polA s _).symm.eq

/-- A dot slides through a crossing of strands with different labels, from the right strand
to the left one. -/
theorem slideL (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν))
    (hs : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, h⟩) (r : ℕ) :
    (ψ j * x ⟨j + 1, h⟩ ^ r * e s : B) = x ⟨j, by omega⟩ ^ r * ψ j * e s := by
  have h1 : (ψ j * x ⟨j + 1, h⟩ * e s : B) = x ⟨j, by omega⟩ * ψ j * e s := by
    have := aDotCrossLeft (Q := Q) (Λ := Λ) j h s
    simp only [hs, ↓reduceIte, sub_mul, sub_eq_zero] at this
    exact this.symm
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, mul_assoc _ (x _) (e s), ax_mul_e, ← mul_assoc, ih,
      mul_assoc _ (e s), ← ax_mul_e, mul_assoc, mul_assoc, ← mul_assoc (ψ j), h1]
    simp only [pow_succ, mul_assoc]

/-- A dot slides through a crossing of strands with different labels, from the left strand
to the right one. -/
theorem slideR (j : ℕ) (h : j + 1 < n) (s : Seq (stendhalWeight L ν))
    (hs : s.lbl ⟨j, by omega⟩ ≠ s.lbl ⟨j + 1, h⟩) (r : ℕ) :
    (ψ j * x ⟨j, by omega⟩ ^ r * e s : B) = x ⟨j + 1, h⟩ ^ r * ψ j * e s := by
  have h1 : (ψ j * x ⟨j, by omega⟩ * e s : B) = x ⟨j + 1, h⟩ * ψ j * e s := by
    have := aDotCrossRight (Q := Q) (Λ := Λ) j h s
    simp only [hs, ↓reduceIte, sub_mul, sub_eq_zero] at this
    exact this
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, mul_assoc _ (x _) (e s), ax_mul_e, ← mul_assoc, ih,
      mul_assoc _ (e s), ← ax_mul_e, mul_assoc, mul_assoc, ← mul_assoc (ψ j), h1]
    simp only [pow_succ, mul_assoc]

end Generic

/-! ### The merged weights and the split idempotent -/

section Split

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (c : Fin ℓ)
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

/-- The weights `λ`: the weights `λ'` with `λ'_c` and `λ'_{c+1}` merged into
`λ'_c + λ'_{c+1}`. -/
def mergeWeights : Fin ℓ → I →₀ ℕ := fun r =>
  if r = c then Λ' c.castSucc + Λ' c.succ else Λ' (c.succ.succAbove r)

omit [DecidableEq I] in
theorem mergeWeights_self : mergeWeights c Λ' c = Λ' c.castSucc + Λ' c.succ := by
  simp [mergeWeights]

omit [DecidableEq I] in
theorem mergeWeights_of_ne {r : Fin ℓ} (h : r ≠ c) :
    mergeWeights c Λ' r = Λ' (c.succ.succAbove r) := by
  simp [mergeWeights, h]

omit [DecidableEq I] in
/-- Away from the red strand `λ_c`, the polynomials `Q` for `λ` and for `λ'` agree. -/
theorem stendhalQ_splitColor (y z : I ⊕ Fin ℓ) (hy : y ≠ .inr c) (hz : z ≠ .inr c) :
    stendhalQ Q (mergeWeights c Λ') y z = stendhalQ Q Λ' (splitColor c y) (splitColor c z) := by
  rcases y with i | r <;> rcases z with j | r'
  · rfl
  · have : r' ≠ c := fun h => hz (by rw [h])
    simp [mergeWeights_of_ne c Λ' this]
  · have : r ≠ c := fun h => hy (by rw [h])
    simp [mergeWeights_of_ne c Λ' this]
  · rfl

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "m'" => Multiset.card (stendhalWeight (ℓ + 1) ν)
local notation "A'" => StendhalAlgebraAllOrders k Q Λ' ν
local notation "e'" => StendhalAlgebraAllOrders.e (k := k) (Q := Q) (Λ := Λ') (ν := ν)
local notation "ψ'" => StendhalAlgebraAllOrders.ψ (k := k) (Q := Q) (Λ := Λ') (ν := ν)
local notation "x'" => StendhalAlgebraAllOrders.x (k := k) (Q := Q) (Λ := Λ') (ν := ν)

omit [DecidableEq I] in
theorem splitLoading_lbl_eq_new_iff [DecidableEq I] (s : Seq μ) (b : Fin m') :
    (splitLoading c s).lbl b = .inr c.succ ↔ b = newPos c s := by
  constructor
  · intro h
    rcases eq_newPos_or_splitPos c s b with hb | ⟨a, rfl⟩
    · exact hb
    · rw [splitLoading_lbl_splitPos] at h
      exact absurd h (splitColor_ne_new c _)
  · rintro rfl
    exact splitLoading_lbl_newPos c s

theorem splitLoading_injective : Function.Injective (splitLoading (ν := ν) c) := by
  intro s t h
  have hq : redPos c s = redPos c t := by
    have h1 := (splitLoading_lbl_eq_new_iff c t (newPos c s)).1
      (by rw [← h]; exact splitLoading_lbl_newPos c s)
    apply Fin.ext
    have := congrArg Fin.val h1
    simp only [newPos_val] at this
    omega
  apply Subtype.ext; funext a
  have hp : splitPos c s a = splitPos c t a := by
    apply Fin.ext; rw [splitPos_val, splitPos_val, hq]
  have : (splitLoading c s).lbl (splitPos c s a) = (splitLoading c t).lbl (splitPos c s a) := by
    rw [h]
  rw [splitLoading_lbl_splitPos, hp, splitLoading_lbl_splitPos] at this
  exact splitColor_injective c this

variable (Q ν) in
/-- The sum of the idempotents of the split loadings: the loadings in which the red strands
`λ'_c`, `λ'_{c+1}` are adjacent, in this order. -/
noncomputable def splitIdem : A' := ∑ s : Seq μ, e' (splitLoading c s)

theorem e_mul_splitIdem (t : Seq μ) :
    e' (splitLoading c t) * splitIdem c Q Λ' ν = e' (splitLoading c t) := by
  rw [splitIdem, Finset.mul_sum]
  simp_rw [StendhalAlgebraAllOrders.e_mul_e, (splitLoading_injective c).eq_iff]
  simp

theorem splitIdem_mul_e (t : Seq μ) :
    splitIdem c Q Λ' ν * e' (splitLoading c t) = e' (splitLoading c t) := by
  rw [splitIdem, Finset.sum_mul]
  simp_rw [StendhalAlgebraAllOrders.e_mul_e, (splitLoading_injective c).eq_iff]
  simp

theorem isIdempotentElem_splitIdem : IsIdempotentElem (splitIdem c Q Λ' ν) := by
  change splitIdem c Q Λ' ν * splitIdem c Q Λ' ν = splitIdem c Q Λ' ν
  change (∑ s : Seq μ, e' (splitLoading c s)) * splitIdem c Q Λ' ν = _
  rw [Finset.sum_mul, Finset.sum_congr rfl fun s _ => e_mul_splitIdem c Λ' s]
  rfl

theorem polA_commute_splitIdem (p : MvPolynomial (Fin m') k) :
    Commute (polA k Q Λ' ν p) (splitIdem c Q Λ' ν) :=
  Commute.sum_right _ _ _ fun _ _ => (e_commute_polA _ p).symm

/-! ### The image of a crossing -/

variable (Q ν) in
/-- The image of the crossing `ψ_j` on a loading whose red strand `λ_c` is at position `q`:
a crossing of two black strands, or a black strand crossing both red strands, or a red-red
crossing (which vanishes). -/
noncomputable def W (j q : ℕ) : A' :=
  if j + 1 < q then ψ' j else if j + 1 = q then ψ' (j + 1) * ψ' j
  else if j = q then ψ' j * ψ' (j + 1) else ψ' (j + 1)

theorem W_mul_e (j : ℕ) (hj : j + 1 < m) (t : Seq μ) :
    W Q Λ' ν j (redPos c t) * e' (splitLoading c t) =
      e' (splitLoading c (sadj m j • t)) * W Q Λ' ν j (redPos c t) := by
  unfold W
  split_ifs with h1 h2 h3
  · rw [splitLoading_sadj_left c t h1, aψ_mul_e]
  · rw [splitLoading_sadj_cross_left c t h2, mul_assoc, aψ_mul_e, ← mul_assoc, aψ_mul_e,
      mul_assoc]
  · rw [splitLoading_sadj_cross_right c t h3 hj, mul_assoc, aψ_mul_e, ← mul_assoc, aψ_mul_e,
      mul_assoc]
  · rw [splitLoading_sadj_right c t (by omega) hj, aψ_mul_e]

/-! ### The generators in the corner -/

variable (Q ν) in
/-- The corner cut out by the split idempotent. -/
abbrev SplitCorner : Type _ := (isIdempotentElem_splitIdem c (Q := Q) Λ' (ν := ν)).Corner

local notation "C" => SplitCorner c Q Λ' ν

noncomputable local instance : Algebra k C := KLR.cornerAlgebra _

open KLR in
/-- The image of the idempotent `e(s)`. -/
noncomputable def gE (s : Seq μ) : C :=
  Corner.mk (e' (splitLoading c s)) (by rw [splitIdem_mul_e, e_mul_splitIdem])

omit [DecidableEq I] in
@[simp] theorem val_gE [DecidableEq I] (s : Seq μ) :
    (gE c Λ' (Q := Q) s : C).val = e' (splitLoading c s) := rfl

end Split

end Categorification.Stendhal.SplitRed
