/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GalleryBasis.Corner

/-!
# The weighted KLR algebra on a family of loadings; equivalent loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Dependence on choice of loadings", Proposition 2.11.

## Encoding

Webster's algebra `W_B` on a set `B` of loadings has one idempotent `e_i` for each `i ∈ B` and
`e_j W_B e_i` the diagrams from `i` to `j`. In this library a diagram depends on its end loadings
only through their chambers (equivalence classes, `Loading.chamber_eq_iff`): the space of
diagrams from `i` to `j` is `e D * A * e C` in the gallery algebra `A = GalleryAlgebra k Γ ν`,
with `C`, `D` the (rank-ordered) full chambers of `i`, `j`. A family of loadings
`L : β → Loading Γ ν` may contain several equivalent loadings, which must still give distinct
idempotents; so the algebra on the family is the corner `ε · M · ε` of the matrix algebra
`M = Matrix β β A` at the diagonal idempotent `ε = diag(e(L b))_b` (`familyIdem`,
`FamilyAlgebra`): its `(c, b)` entry lies in `e(L c) A e(L b)`. For the family of all
chambers, one loading each, this is Webster's weighted KLR algebra `weightedKLR` (up to the
evident isomorphism); the same matrix-corner construction is used for the evenly spaced loadings
of Proposition 2.14.

## Proposition 2.11

If `L b` and `L b'` are equivalent, then the matrix units `u = E_{b b'}(e C)` and
`v = E_{b' b}(e C)` (`C` the common full chamber) satisfy `u v = e_b`, `v u = e_{b'}`
(`familyMove_mul_familyMove`); this is the straight-line path of Webster's proof, which in the
gallery algebra is the idempotent `e C` itself. Hence:

* `familyProjectiveEquiv`: the projective modules `W e_b` and `W e_{b'}` are isomorphic, as left
  `W`-modules (`W e_b` is the left ideal `Submodule.span W {e_b}`).
* The algebra with `b'` removed is the corner `f W f` at `f = 1 - e_{b'}` (`familyRemoveEquiv`),
  and `f` is a full idempotent: `1 = f + v f u` (`one_eq_familyIdemOff_add`), so `W f W = W`.
  By the standard criterion (a corner at a full idempotent is Morita equivalent to the ring),
  this is Webster's statement that the algebra is Morita equivalent to the one with `b'`
  excluded. Mathlib does not yet contain this criterion (it is listed as a TODO in
  `Mathlib.RingTheory.Morita.Basic`), so the Morita equivalence itself is recorded here through
  these two ring-theoretic facts.

## Main definitions and results

* `familyIdem`, `FamilyAlgebra`: the weighted KLR algebra on a family of loadings.
* `FamilyAlgebra.idemAt b`: the idempotent `e_b`.
* `spanSingletonEquivOfMul`: idempotents `e = u v`, `e' = v u` give isomorphic left ideals.
* `familyProjectiveEquiv`: Proposition 2.11, `W e_b ≅ W e_{b'}`.
* `familyRemoveEquiv`, `one_eq_familyIdemOff_add`: Proposition 2.11, the Morita part.
-/

namespace Categorification.WeightedKLR

open GalleryAlgebra

section LeftIdeal

variable {R : Type*} [Ring R]

/-- If `e = u v` and `e' = v u` with `u e' = u` and `v e = v`, then right multiplication by `u`
is an isomorphism of left ideals `R e ≃ R e'`, with inverse right multiplication by `v`. -/
noncomputable def spanSingletonEquivOfMul {e e' u v : R} (huv : u * v = e) (hvu : v * u = e')
    (hue : u * e' = u) (hve : v * e = v) :
    Submodule.span R {e} ≃ₗ[R] Submodule.span R {e'} :=
  have he : e * e = e := by rw [← huv, ← mul_assoc, mul_assoc u v u, hvu, hue]
  have he' : e' * e' = e' := by rw [← hvu, ← mul_assoc, mul_assoc v u v, huv, hve]
  have hx : ∀ {a x : R}, x ∈ Submodule.span R {a} → a * a = a → x * a = x := by
    intro a x hxa ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxa
    rw [smul_eq_mul, mul_assoc, ha]
  { toFun := fun x => ⟨x.1 * u, Submodule.mem_span_singleton.2
      ⟨x.1 * u, by rw [smul_eq_mul, mul_assoc, hue]⟩⟩
    map_add' := fun x y => Subtype.ext (add_mul _ _ _)
    map_smul' := fun c x => Subtype.ext (by simp [smul_eq_mul, mul_assoc])
    invFun := fun x => ⟨x.1 * v, Submodule.mem_span_singleton.2
      ⟨x.1 * v, by rw [smul_eq_mul, mul_assoc, hve]⟩⟩
    left_inv := fun x => Subtype.ext (by
      show x.1 * u * v = x.1
      rw [mul_assoc, huv, hx x.2 he])
    right_inv := fun x => Subtype.ext (by
      show x.1 * v * u = x.1
      rw [mul_assoc, hvu, hx x.2 he']) }

end LeftIdeal

section Diagonal

variable {β A : Type*} [Fintype β] [DecidableEq β] [Ring A]

theorem mem_corner_diagonal_iff {d : β → A} (hd : IsIdempotentElem (Matrix.diagonal d))
    {M : Matrix β β A} :
    M ∈ Subsemigroup.corner (Matrix.diagonal d) ↔ ∀ i j, d i * M i j = M i j ∧ M i j * d j = M i j := by
  rw [Subsemigroup.mem_corner_iff hd]
  constructor
  · rintro ⟨h₁, h₂⟩ i j
    exact ⟨by simpa [Matrix.diagonal_mul] using congrFun (congrFun h₁ i) j,
      by simpa [Matrix.mul_diagonal] using congrFun (congrFun h₂ i) j⟩
  · intro h
    exact ⟨Matrix.ext fun i j => by simp [Matrix.diagonal_mul, (h i j).1],
      Matrix.ext fun i j => by simp [Matrix.mul_diagonal, (h i j).2]⟩

theorem isIdempotentElem_diagonal {d : β → A} (hd : ∀ i, d i * d i = d i) :
    IsIdempotentElem (Matrix.diagonal d) := by
  rw [IsIdempotentElem, Matrix.diagonal_mul_diagonal]
  exact congrArg _ (funext hd)

end Diagonal

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}
  {β : Type*} [Fintype β] [DecidableEq β]

theorem e_mul_self (C : FullChamber Γ ν) : (e C * e C : GalleryAlgebra k Γ ν) = e C := by
  simp [e_mul_e]

variable (k) in
/-- The diagonal idempotent `diag(e(L b))_b` of `Matrix β β A`, `A` the gallery algebra. -/
noncomputable def familyIdem (L : β → Loading Γ ν) : Matrix β β (GalleryAlgebra k Γ ν) :=
  Matrix.diagonal fun b => e (L b).chamber.toFull

theorem isIdempotentElem_familyIdem (L : β → Loading Γ ν) :
    IsIdempotentElem (familyIdem k L) :=
  isIdempotentElem_diagonal fun _ => e_mul_self _

variable (k) in
/-- The weighted KLR algebra on the family of loadings `L` (one idempotent for each member of
the family, equivalent members included): the corner of `Matrix β β A` at `familyIdem`. Its
`(c, b)` entry lies in `e(L c) A e(L b)`, the diagrams from `L b` to `L c`. -/
abbrev FamilyAlgebra (L : β → Loading Γ ν) : Type _ :=
  (isIdempotentElem_familyIdem (k := k) L).Corner

namespace FamilyAlgebra

variable {L : β → Loading Γ ν}

theorem mem_iff {M : Matrix β β (GalleryAlgebra k Γ ν)} :
    M ∈ Subsemigroup.corner (familyIdem k L) ↔
      ∀ i j, e (L i).chamber.toFull * M i j = M i j ∧ M i j * e (L j).chamber.toFull = M i j :=
  mem_corner_diagonal_iff (isIdempotentElem_familyIdem L)

theorem val_mul (x y : FamilyAlgebra k L) : (x * y).1 = x.1 * y.1 := rfl
theorem val_one : (1 : FamilyAlgebra k L).1 = familyIdem k L := rfl
theorem val_add (x y : FamilyAlgebra k L) : (x + y).1 = x.1 + y.1 := rfl

/-- The matrix unit `E_{c b}(e C)` for loadings `L c`, `L b` in the same chamber, `C` their
full chamber: the straight-line diagram from `L b` to `L c`. -/
noncomputable def move (c b : β) (h : (L c).chamber = (L b).chamber) : FamilyAlgebra k L :=
  ⟨Matrix.single c b (e (L c).chamber.toFull), mem_iff.2 fun i j => by
    simp only [Matrix.single_apply]
    split_ifs with hij
    · obtain ⟨rfl, rfl⟩ := hij
      rw [← h]; exact ⟨e_mul_self _, e_mul_self _⟩
    · simp⟩

/-- The idempotent `e_b` of the loading `L b`. -/
noncomputable def idemAt (b : β) : FamilyAlgebra k L := move b b rfl

theorem move_mul_move (c b a : β) (h : (L c).chamber = (L b).chamber)
    (h' : (L b).chamber = (L a).chamber) :
    (move c b h * move b a h' : FamilyAlgebra k L) = move c a (h.trans h') := by
  apply Subtype.ext
  rw [val_mul]
  simp only [move, Matrix.single_mul_single_same]
  rw [h, e_mul_self]

theorem sum_idemAt : ∑ b, (idemAt b : FamilyAlgebra k L) = 1 := by
  apply Subtype.ext
  rw [val_one]
  have : ∀ s : Finset β, (∑ b ∈ s, (idemAt b : FamilyAlgebra k L)).1 =
      ∑ b ∈ s, Matrix.single b b (e (L b).chamber.toFull) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, val_add, ih]; rfl
  rw [this, familyIdem]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.sum_apply, Matrix.single_apply]
  · simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply, hij, ite_false]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exact absurd rfl hij

end FamilyAlgebra

open FamilyAlgebra

/-- The straight-line diagrams between equivalent loadings are mutually inverse:
`E_{b b'} E_{b' b} = e_b`. -/
theorem familyMove_mul_familyMove {L : β → Loading Γ ν} {b b' : β} (h : (L b).Equiv (L b')) :
    (move b b' ((Loading.chamber_eq_iff _ _).2 h) *
        move b' b ((Loading.chamber_eq_iff _ _).2 h).symm : FamilyAlgebra k L) = idemAt b :=
  move_mul_move _ _ _ _ _

/-- Webster, arXiv:1209.2463v4, Proposition 2.11 (first assertion): for equivalent loadings
`L b`, `L b'` of the family, the projective modules `W e_b` and `W e_{b'}` of the algebra `W` on
the family are isomorphic (right multiplication by the straight-line diagram from `L b'` to
`L b`). -/
noncomputable def familyProjectiveEquiv {L : β → Loading Γ ν} {b b' : β} (h : (L b).Equiv (L b')) :
    Submodule.span (FamilyAlgebra k L) {(idemAt b : FamilyAlgebra k L)} ≃ₗ[FamilyAlgebra k L]
      Submodule.span (FamilyAlgebra k L) {(idemAt b' : FamilyAlgebra k L)} :=
  have hc := (Loading.chamber_eq_iff _ _).2 h
  spanSingletonEquivOfMul (u := move b b' hc) (v := move b' b hc.symm)
    (move_mul_move _ _ _ _ _) (move_mul_move _ _ _ _ _) (move_mul_move _ _ _ _ _)
    (move_mul_move _ _ _ _ _)

/-! ### Removing a redundant loading -/

section Remove

variable {L : β → Loading Γ ν} (b' : β)

/-- The idempotent `f = 1 - e_{b'}`: the diagonal idempotent of the loadings other than `L b'`. -/
noncomputable def familyIdemOff : FamilyAlgebra k L :=
  ⟨Matrix.diagonal fun c => if c = b' then 0 else e (L c).chamber.toFull, mem_iff.2 fun i j => by
    simp only [Matrix.diagonal_apply]
    split_ifs <;> subst_vars <;> simp [e_mul_self]⟩

theorem familyIdemOff_add_idemAt :
    (familyIdemOff b' + idemAt b' : FamilyAlgebra k L) = 1 := by
  apply Subtype.ext
  rw [val_add, val_one]
  ext i j
  simp only [familyIdemOff, idemAt, move, familyIdem, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.single_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = b'
    · subst hi; simp
    · simp only [hi, ite_false]
      have h : ¬b' = i := fun h => hi h.symm
      simp only [and_self, h, ite_true, ite_false, add_zero]
  · have : ¬(b' = i ∧ b' = j) := fun h => hij (h.1.symm.trans h.2)
    simp [hij, this]

theorem isIdempotentElem_familyIdemOff :
    IsIdempotentElem (familyIdemOff (k := k) (L := L) b') := by
  apply Subtype.ext
  rw [val_mul]
  simp only [familyIdemOff, Matrix.diagonal_mul_diagonal]
  congr 1
  funext c
  split_ifs <;> simp [e_mul_self]

/-- Webster, arXiv:1209.2463v4, Proposition 2.11 (Morita part, fullness): if `L b'` is
equivalent to another member `L b` of the family, then `1 = f + v f u` with `f = 1 - e_{b'}`,
`u = E_{b b'}`, `v = E_{b' b}`; so the two-sided ideal generated by `f` is the whole algebra. -/
theorem one_eq_familyIdemOff_add {b : β} (hb : b ≠ b') (h : (L b).Equiv (L b')) :
    (1 : FamilyAlgebra k L) = familyIdemOff b' +
      move b' b ((Loading.chamber_eq_iff _ _).2 h).symm * familyIdemOff b' *
        move b b' ((Loading.chamber_eq_iff _ _).2 h) := by
  have hc := (Loading.chamber_eq_iff _ _).2 h
  have hf : (familyIdemOff b' * move b b' hc : FamilyAlgebra k L) = move b b' hc := by
    apply Subtype.ext
    rw [val_mul]
    ext i j
    simp only [familyIdemOff, move, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with h₁ h₂ <;> simp_all [e_mul_self]
  rw [mul_assoc, hf, move_mul_move, ← familyIdemOff_add_idemAt b']
  rfl

/-- The family with the member `b'` removed. -/
def familyRemove (L : β → Loading Γ ν) (b' : β) : {c // c ≠ b'} → Loading Γ ν :=
  fun c => L c.1

/-- Extension by zero of a matrix indexed by `{c // c ≠ b'}`. -/
def extendOff {A : Type*} [Zero A] (M : Matrix {c // c ≠ b'} {c // c ≠ b'} A) : Matrix β β A :=
  Matrix.of fun i j => if hi : i = b' then 0 else if hj : j = b' then 0 else M ⟨i, hi⟩ ⟨j, hj⟩

theorem sum_dite_ne {A : Type*} [AddCommMonoid A] (g : {c // c ≠ b'} → A) :
    ∑ x : β, (if hx : x = b' then 0 else g ⟨x, hx⟩) = ∑ y, g y := by
  rw [← Finset.sum_erase Finset.univ (a := b') (by simp),
    Finset.sum_subtype (Finset.univ.erase b') (p := fun x => x ≠ b') (by simp)]
  exact Finset.sum_congr rfl fun y _ => by simp [y.2]

theorem extendOff_mul {A : Type*} [Ring A] (M N : Matrix {c // c ≠ b'} {c // c ≠ b'} A) :
    extendOff b' (M * N) = extendOff b' M * extendOff b' N := by
  ext i j
  simp only [extendOff, Matrix.of_apply, Matrix.mul_apply]
  by_cases hi : i = b'
  · simp [hi]
  by_cases hj : j = b'
  · simp [hi, hj]
  · simp only [hi, hj, dite_false]
    rw [← sum_dite_ne b' (fun y => M ⟨i, hi⟩ y * N y ⟨j, hj⟩)]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = b' <;> simp [hx]

theorem extendOff_mem {M : FamilyAlgebra k (familyRemove L b')} :
    extendOff b' M.1 ∈ Subsemigroup.corner (familyIdem k L) := by
  have hM := (mem_iff.1 M.2)
  refine mem_iff.2 fun i j => ?_
  simp only [extendOff, Matrix.of_apply]
  split_ifs with hi hj
  · simp
  · simp
  · exact hM ⟨i, hi⟩ ⟨j, hj⟩

/-- The element of `W` extending an element of the algebra on the family without `b'`. -/
noncomputable def extendOffElt (M : FamilyAlgebra k (familyRemove L b')) : FamilyAlgebra k L :=
  ⟨extendOff b' M.1, extendOff_mem b'⟩

theorem extendOff_mem_corner {M : FamilyAlgebra k (familyRemove L b')} :
    extendOffElt b' M ∈
      Subsemigroup.corner (familyIdemOff (k := k) (L := L) b') := by
  rw [Subsemigroup.mem_corner_iff (isIdempotentElem_familyIdemOff b')]
  have hM := (mem_iff.1 M.2)
  constructor
  · apply Subtype.ext
    rw [val_mul]
    ext i j
    simp only [extendOffElt, familyIdemOff, extendOff, Matrix.diagonal_mul, Matrix.of_apply]
    split_ifs with hi hj <;> simp_all [familyRemove]
  · apply Subtype.ext
    rw [val_mul]
    ext i j
    simp only [extendOffElt, familyIdemOff, extendOff, Matrix.mul_diagonal, Matrix.of_apply]
    split_ifs with hi hj <;> simp_all [familyRemove]

theorem val_eq_zero_of_mem_corner {x : FamilyAlgebra k L}
    (hx : x ∈ Subsemigroup.corner (familyIdemOff (k := k) (L := L) b')) (i j : β)
    (hij : i = b' ∨ j = b') : x.1 i j = 0 := by
  rw [Subsemigroup.mem_corner_iff (isIdempotentElem_familyIdemOff b')] at hx
  rcases hij with rfl | rfl
  · have h1 : (familyIdemOff i * x : FamilyAlgebra k L).1 i j = x.1 i j := by rw [hx.1]
    rw [val_mul] at h1
    simpa [familyIdemOff, Matrix.diagonal_mul] using h1.symm
  · have h1 : (x * familyIdemOff j : FamilyAlgebra k L).1 i j = x.1 i j := by rw [hx.2]
    rw [val_mul] at h1
    simpa [familyIdemOff, Matrix.mul_diagonal] using h1.symm

/-- Webster, arXiv:1209.2463v4, Proposition 2.11 (Morita part, corner): the algebra on the
family with `L b'` removed is the corner `f W f`, `f = 1 - e_{b'}`, of the algebra `W` on the
family (extension of matrices by zero). -/
noncomputable def familyRemoveEquiv :
    FamilyAlgebra k (familyRemove L b') ≃+* (isIdempotentElem_familyIdemOff (k := k) (L := L) b').Corner where
  toFun M := ⟨extendOffElt b' M, extendOff_mem_corner b'⟩
  invFun x := ⟨Matrix.of fun i j => x.1.1 i.1 j.1, mem_iff.2 fun i j => by
    have := (mem_iff.1 x.1.2) i.1 j.1
    exact this⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    simp [extendOffElt, extendOff, i.2, j.2]
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    ext i j
    simp only [extendOffElt, extendOff, Matrix.of_apply]
    split_ifs with hi hj
    · exact (val_eq_zero_of_mem_corner b' x.2 i j (.inl hi)).symm
    · exact (val_eq_zero_of_mem_corner b' x.2 i j (.inr hj)).symm
    · rfl
  map_mul' M N := by
    apply Subtype.ext; apply Subtype.ext
    exact extendOff_mul b' M.1 N.1
  map_add' M N := by
    apply Subtype.ext; apply Subtype.ext
    ext i j
    show extendOff b' (M.1 + N.1) i j = extendOff b' M.1 i j + extendOff b' N.1 i j
    simp only [extendOff, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp

end Remove

end Categorification.WeightedKLR
