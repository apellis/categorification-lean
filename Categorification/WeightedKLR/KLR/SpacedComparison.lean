/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.KLR.SpacedCrossing
import Categorification.KLR.BasisTheorem

/-!
# The weighted KLR algebra of the evenly spaced loadings is a KLR algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Proposition 2.14.

For a weighted graph without loops (no loop of weight `0` at any colour and no edge whose head is
its tail), Webster identifies the weighted KLR algebra on the evenly spaced loadings
`B_s(i)` (`i ∈ Seq ν`, `s` larger than every `|ϑ_e|`) with the KLR algebra `R(ν)` for the
polynomials
`Q_{ij}(u, v) = ∏_{e : j → i} Q_e(u, v) · ∏_{e : i → j} Q_e(v, u)`,
where the product runs over the edges in both directions between `i` and `j` (`e : j → i` means
`t(e) = j`, `h(e) = i`). In the notation of `KLR.PolyRep` this is
`Q a b = P b a · P a b (v, u)` for `P a b = ∏_{e : a → b} Q_e` (`WeightedGraph.edgeProd`).

## The target algebra

Two different sequences `i ≠ j` can give equivalent loadings `B_s(i)`, `B_s(j)` (this happens
exactly when `i` and `j` differ by exchanging neighbouring positions of colours not joined by an
edge). The gallery algebra has one idempotent per equivalence class of loadings, so the
idempotents `e(i)` of `R(ν)` cannot be sent to distinct idempotents of the gallery algebra. The
weighted KLR algebra on the family of loadings `(B_s(i))_{i ∈ Seq ν}`, with one idempotent per
member of the family, is the corner `ε · M · ε` of the matrix algebra
`M = Matrix (Seq ν) (Seq ν) A` over the gallery algebra `A`, cut out by the diagonal idempotent
`ε = diag(e(B_s(i)))_i` (`spacedIdem`, `SpacedAlgebra`). Its `(j, i)` entry is the space of
elements of the weighted KLR algebra from `B_s(i)` to `B_s(j)`.

## Main definitions and results

* `IsIdempotentElem.Corner` is a `k`-algebra when the ambient ring is.
* `spacedIdem`, `SpacedAlgebra`: the weighted KLR algebra on the evenly spaced loadings.
* `spacedRep`: its polynomial representation on `Seq ν → k[y_t]`.
* `spacedHom`: the homomorphism `R(ν) → SpacedAlgebra` sending `e(i)` to the idempotent of
  `B_s(i)`, the dot `x_a` to the dot on the strand at position `a`, and the crossing `ψ_n` to the
  straight gallery `crossElt` exchanging the strands at positions `n` and `n + 1`.
* `spacedRep_spacedHom`: `spacedHom` intertwines the polynomial representations.
* `spacedHom_injective`: `spacedHom` is injective (Proposition 2.14, injectivity), over any
  commutative ring.
-/

namespace IsIdempotentElem

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] {e : A}

theorem corner_smul_mem (idem : IsIdempotentElem e) (c : R) {x : A}
    (hx : x ∈ Subsemigroup.corner e) : c • x ∈ Subsemigroup.corner e := by
  rw [Subsemigroup.mem_corner_iff idem] at hx ⊢
  rw [mul_smul_comm, smul_mul_assoc, hx.1, hx.2]
  exact ⟨rfl, rfl⟩

variable (idem : IsIdempotentElem e)

/-- The corner `e A e` of an `R`-algebra `A` is an `R`-algebra, with unit `e`. -/
noncomputable instance : Algebra R idem.Corner where
  smul c x := ⟨c • x.1, corner_smul_mem idem c x.2⟩
  algebraMap :=
    { toFun := fun c => ⟨c • e, corner_smul_mem idem c ((Subsemigroup.mem_corner_iff idem).2
        ⟨idem.eq, idem.eq⟩)⟩
      map_one' := Subtype.ext (one_smul R e)
      map_mul' := fun a b => Subtype.ext (by
        show (a * b) • e = (a • e) * (b • e)
        rw [smul_mul_smul_comm, idem.eq])
      map_zero' := Subtype.ext (zero_smul R e)
      map_add' := fun a b => Subtype.ext (add_smul a b e) }
  commutes' c x := Subtype.ext (by
    have hx := (Subsemigroup.mem_corner_iff idem).1 x.2
    show (c • e) * x.1 = x.1 * (c • e)
    rw [smul_mul_assoc, mul_smul_comm, hx.1, hx.2])
  smul_def' c x := Subtype.ext (by
    have hx := (Subsemigroup.mem_corner_iff idem).1 x.2
    show c • x.1 = (c • e) * x.1
    rw [smul_mul_assoc, hx.1])

theorem corner_val_smul (c : R) (x : idem.Corner) : (c • x : idem.Corner).1 = c • x.1 := rfl
theorem corner_val_mul (x y : idem.Corner) : (x * y : idem.Corner).1 = x.1 * y.1 := rfl
theorem corner_val_one : (1 : idem.Corner).1 = e := rfl
theorem corner_val_add (x y : idem.Corner) : (x + y : idem.Corner).1 = x.1 + y.1 := rfl
theorem corner_val_zero : (0 : idem.Corner).1 = 0 := rfl

end IsIdempotentElem

namespace Categorification.WeightedKLR

open Equiv MvPolynomial FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "ν'" => Multiset.toFinsupp ν

section Renaming

/-- Renaming the variables of `k[x_1, …, x_m]` to the strands, along the sequence `i`. -/
noncomputable abbrev seqRen (i : KLR.Seq ν) :
    MvPolynomial (Fin m) k →ₗ[k] PolyRing (Multiset.toFinsupp ν) k :=
  (rename i.strandAt).toLinearMap

theorem seqRen_injective (i : KLR.Seq ν) : Function.Injective (seqRen (k := k) i) :=
  rename_injective _ i.strandAt_injective

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The crossing operator of the evenly spaced loadings is the KLR crossing operator for
`P = edgeProd Γ`, after renaming variables to strands. -/
theorem crossOp_seqRen (t : KLR.Seq ν) (n : ℕ) (h : n + 1 < m) (g : MvPolynomial (Fin m) k) :
    crossOp k Γ t n h (seqRen t g) =
      seqRen (TypeA.sadj m n • t) (KLR.PolyRep.crossComp Γ.edgeProd n h t g) := by
  have hs0 := TypeA.sadj_apply_left h
  have hs1 := TypeA.sadj_apply_right h
  by_cases hc : t.1 ⟨n, by omega⟩ = t.1 ⟨n + 1, h⟩
  · simp only [crossOp, KLR.PolyRep.crossComp, KLR.Seq.lbl, hc, ↓reduceIte]
    rw [KLR.Seq.sadj_smul_of_eq t h hc]
    simp only [seqRen, AlgHom.toLinearMap_apply]
    rw [rename_ddiff t.strandAt_injective (by simp)]
  · simp only [crossOp, KLR.PolyRep.crossComp, KLR.Seq.lbl, hc, ↓reduceIte]
    simp only [seqRen, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply, LinearMap.comp_apply,
      map_mul, rename_rename]
    have hσ := KLR.Seq.lt_sadj_iff t h hc
    congr 3
    · funext c
      fin_cases c
      · show rightStrand t n h = (TypeA.sadj m n • t).strandAt ⟨n, by omega⟩
        rw [← hs1, KLR.Seq.strandAt_smul t _ hσ]
      · show leftStrand t n h = (TypeA.sadj m n • t).strandAt ⟨n + 1, h⟩
        rw [← hs0, KLR.Seq.strandAt_smul t _ hσ]
    · funext c
      exact (KLR.Seq.strandAt_smul t _ hσ c).symm

end Renaming

section Algebra

variable (k Γ ν) in
/-- The diagonal idempotent `diag(e(B_s(i)))_i` of the matrix algebra over the gallery algebra. -/
noncomputable def spacedIdem : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν') :=
  Matrix.diagonal fun i => e (spacedFull Γ i)

theorem isIdempotentElem_spacedIdem : IsIdempotentElem (spacedIdem k Γ ν) := by
  rw [IsIdempotentElem, spacedIdem, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [e_mul_e]

variable (k Γ ν) in
/-- The weighted KLR algebra on the family of evenly spaced loadings `(B_s(i))_{i ∈ Seq ν}`:
the corner of `Matrix (Seq ν) (Seq ν) A` (`A` the gallery algebra) at `spacedIdem`. Its
`(j, i)` entry lies in `e(B_s(j)) A e(B_s(i))`. -/
abbrev SpacedAlgebra : Type _ :=
  (isIdempotentElem_spacedIdem (k := k) (Γ := Γ) (ν := ν)).Corner

theorem SpacedAlgebra.e_mul (x : SpacedAlgebra k Γ ν) (j i : KLR.Seq ν) :
    e (spacedFull Γ j) * x.1 j i = x.1 j i := by
  have h := ((Subsemigroup.mem_corner_iff isIdempotentElem_spacedIdem).1 x.2).1
  have := congrFun (congrFun h j) i
  simpa [spacedIdem, Matrix.diagonal_mul] using this

theorem SpacedAlgebra.mul_e (x : SpacedAlgebra k Γ ν) (j i : KLR.Seq ν) :
    x.1 j i * e (spacedFull Γ i) = x.1 j i := by
  have h := ((Subsemigroup.mem_corner_iff isIdempotentElem_spacedIdem).1 x.2).2
  have := congrFun (congrFun h j) i
  simpa [spacedIdem, Matrix.mul_diagonal] using this

theorem galleryRep_apply_of_mul_e (hΓ : Γ.PSymm) {x : GalleryAlgebra k Γ ν'}
    {C : FullChamber Γ ν'} (hx : x * e C = x) (v : FullChamber Γ ν' → PolyRing ν' k) :
    galleryRep k hΓ x v = galleryRep k hΓ x (Pi.single C (v C)) := by
  conv_lhs => rw [← hx]
  rw [map_mul, galleryRep_e, Module.End.mul_apply, blk_apply, LinearMap.id_apply]

theorem galleryRep_apply_of_e_mul (hΓ : Γ.PSymm) {x : GalleryAlgebra k Γ ν'}
    {C : FullChamber Γ ν'} (hx : e C * x = x) (v : FullChamber Γ ν' → PolyRing ν' k) :
    galleryRep k hΓ x v = Pi.single C (galleryRep k hΓ x v C) := by
  conv_lhs => rw [← hx]
  rw [map_mul, galleryRep_e, Module.End.mul_apply, blk_apply, LinearMap.id_apply]

variable (k) in
/-- The polynomial representation of the matrix algebra over the gallery algebra on
`Seq ν → k[y_t]`: the entry `c j i` acts from the `i`-th copy, placed in the copy of
`B_s(i)`, to the `j`-th copy, read off at the copy of `B_s(j)`. -/
noncomputable def spacedOp (hΓ : Γ.PSymm)
    (c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) :
    Module.End k (KLR.Seq ν → PolyRing ν' k) :=
  LinearMap.pi fun j => ∑ i,
    (LinearMap.proj (R := k) (φ := fun _ : FullChamber Γ ν' => PolyRing ν' k) (spacedFull Γ j)) ∘ₗ
      galleryRep k hΓ (c j i) ∘ₗ
      LinearMap.single k (fun _ : FullChamber Γ ν' => PolyRing ν' k) (spacedFull Γ i) ∘ₗ
      LinearMap.proj (R := k) (φ := fun _ : KLR.Seq ν => PolyRing ν' k) i

theorem spacedOp_apply (hΓ : Γ.PSymm) (c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν'))
    (g : KLR.Seq ν → PolyRing ν' k) (j : KLR.Seq ν) :
    spacedOp k hΓ c g j =
      ∑ i, galleryRep k hΓ (c j i) (Pi.single (spacedFull Γ i) (g i)) (spacedFull Γ j) := by
  simp [spacedOp, LinearMap.sum_apply]

theorem spacedOp_single (hΓ : Γ.PSymm)
    (c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) (i : KLR.Seq ν)
    (p : PolyRing ν' k) (j : KLR.Seq ν) :
    spacedOp k hΓ c (Pi.single i p) j =
      galleryRep k hΓ (c j i) (Pi.single (spacedFull Γ i) p) (spacedFull Γ j) := by
  rw [spacedOp_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro i' _ hi'
    rw [Pi.single_eq_of_ne hi', Pi.single_zero, map_zero, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem spacedOp_add (hΓ : Γ.PSymm)
    (c d : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) :
    spacedOp k hΓ (c + d) = spacedOp k hΓ c + spacedOp k hΓ d := by
  refine LinearMap.ext fun g => funext fun j => ?_
  simp only [spacedOp_apply, LinearMap.add_apply, Pi.add_apply, Matrix.add_apply, map_add,
    ← Finset.sum_add_distrib]

theorem spacedOp_smul (hΓ : Γ.PSymm) (a : k)
    (c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) :
    spacedOp k hΓ (a • c) = a • spacedOp k hΓ c := by
  refine LinearMap.ext fun g => funext fun j => ?_
  simp only [spacedOp_apply, LinearMap.smul_apply, Pi.smul_apply, Matrix.smul_apply, map_smul,
    Finset.smul_sum]

theorem spacedOp_spacedIdem (hΓ : Γ.PSymm) : spacedOp k hΓ (spacedIdem k Γ ν) = 1 := by
  refine LinearMap.ext fun g => funext fun j => ?_
  rw [spacedOp_apply, Finset.sum_eq_single j]
  · simp [spacedIdem, galleryRep_e, blk_apply]
  · intro i _ hij
    simp [spacedIdem, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem spacedOp_mul (hΓ : Γ.PSymm)
    {c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')}
    (hc : ∀ j i, c j i * e (spacedFull Γ i) = c j i)
    (d : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) :
    spacedOp k hΓ (c * d) = spacedOp k hΓ c * spacedOp k hΓ d := by
  refine LinearMap.ext fun g => funext fun l => ?_
  have key : ∀ j, galleryRep k hΓ (c l j) (Pi.single (spacedFull Γ j) (spacedOp k hΓ d g j)) =
      ∑ i, galleryRep k hΓ (c l j)
        (galleryRep k hΓ (d j i) (Pi.single (spacedFull Γ i) (g i))) := by
    intro j
    rw [← map_sum, galleryRep_apply_of_mul_e hΓ (hc l j)
      (∑ i, galleryRep k hΓ (d j i) (Pi.single (spacedFull Γ i) (g i))),
      Finset.sum_apply, spacedOp_apply]
  rw [Module.End.mul_apply, spacedOp_apply, spacedOp_apply]
  simp only [key, Matrix.mul_apply, map_sum, map_mul, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply]
  exact Finset.sum_comm

end Algebra

section Rep

variable (k) in
/-- The polynomial representation of the weighted KLR algebra on the evenly spaced loadings. -/
noncomputable def spacedRep (hΓ : Γ.PSymm) :
    SpacedAlgebra k Γ ν →ₐ[k] Module.End k (KLR.Seq ν → PolyRing ν' k) :=
  AlgHom.ofLinearMap
    { toFun := fun x => spacedOp k hΓ x.1
      map_add' := fun x y => spacedOp_add hΓ x.1 y.1
      map_smul' := fun a x => spacedOp_smul hΓ a x.1 }
    (spacedOp_spacedIdem hΓ)
    (fun x y => spacedOp_mul hΓ (SpacedAlgebra.mul_e x) y.1)

theorem spacedRep_apply (hΓ : Γ.PSymm) (x : SpacedAlgebra k Γ ν) :
    spacedRep k hΓ x = spacedOp k hΓ x.1 := rfl

/-- The polynomial representation of the weighted KLR algebra on the evenly spaced loadings is
faithful, under the hypotheses of the basis theorem (for a graph without loops). -/
theorem spacedRep_injective (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ (Multiset.toFinsupp ν), IsRegular (w.factor (k := k))) :
    Function.Injective (spacedRep k hΓ (ν := ν)) := by
  intro x y hxy
  have hZ : Γ.NoZeroLoops := fun e he => absurd he (hE e)
  have h' : spacedOp k hΓ x.1 = spacedOp k hΓ y.1 := hxy
  apply Subtype.ext
  funext j i
  refine galleryRep_injective hD hZ hΓ hW (fun Q a b h _ _ => by simp [hl] at h) ?_
  refine LinearMap.ext fun v => ?_
  rw [galleryRep_apply_of_e_mul hΓ (SpacedAlgebra.e_mul x j i),
    galleryRep_apply_of_mul_e hΓ (SpacedAlgebra.mul_e x j i),
    galleryRep_apply_of_e_mul hΓ (SpacedAlgebra.e_mul y j i) v,
    galleryRep_apply_of_mul_e hΓ (SpacedAlgebra.mul_e y j i),
    ← spacedOp_single, ← spacedOp_single, h']

theorem spacedOp_sandwich (hΓ : Γ.PSymm)
    (c : Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')) :
    spacedOp k hΓ (spacedIdem k Γ ν * c * spacedIdem k Γ ν) = spacedOp k hΓ c := by
  refine LinearMap.ext fun g => funext fun j => ?_
  rw [spacedOp_apply, spacedOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [spacedIdem, Matrix.mul_diagonal, Matrix.diagonal_mul, galleryRep_e, blk_apply]

end Rep

section Generators

variable (k Γ) in
/-- The matrices of the generators of `R(ν)`: `e(i)` is the idempotent of `B_s(i)` in the
`(i, i)` entry, the dot `x_a` is the dot on the strand at position `a` of each `B_s(i)`, and the
crossing `ψ_n` has the crossing `crossElt` of `B_s(i)` in the `(s_n i, i)` entry. -/
noncomputable def genMat :
    KLR.Gen ν → Matrix (KLR.Seq ν) (KLR.Seq ν) (GalleryAlgebra k Γ ν')
  | .idem i => Matrix.single i i (e (spacedFull Γ i))
  | .dot a => Matrix.diagonal fun i => poly (X (i.strandAt a))
  | .cross n => if h : n + 1 < m then
      Matrix.of fun j i => if j = TypeA.sadj m n • i then crossElt k Γ i n h else 0
    else 0

variable (k Γ) in
/-- The generators of `R(ν)` in the weighted KLR algebra of the evenly spaced loadings. -/
noncomputable def genImg (g : KLR.Gen ν) : SpacedAlgebra k Γ ν :=
  ⟨spacedIdem k Γ ν * genMat k Γ g * spacedIdem k Γ ν, genMat k Γ g, rfl⟩

/-- Renaming the variables of each component along its sequence. -/
noncomputable def seqRenEquiv :
    KLR.PolyRep.Pol k ν ≃ₗ[k] (KLR.Seq ν → PolyRing (Multiset.toFinsupp ν) k) :=
  LinearEquiv.piCongrRight fun i => (renameEquiv k i.strandEquiv).toLinearEquiv

theorem seqRenEquiv_apply (f : KLR.PolyRep.Pol k ν) (i : KLR.Seq ν) :
    seqRenEquiv f i = seqRen i (f i) := rfl

theorem spacedOp_genMat (hΓ : Γ.PSymm) (hD : Γ.Dagger) (hl : ∀ c, Γ.loop c = none)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (g : KLR.Gen ν) :
    spacedOp k hΓ (genMat k Γ g) ∘ₗ seqRenEquiv.toLinearMap =
      seqRenEquiv.toLinearMap ∘ₗ KLR.PolyRep.genOp ν Γ.edgeProd g := by
  refine LinearMap.ext fun f => funext fun j => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, seqRenEquiv_apply]
  rcases g with i | a | n
  · simp only [genMat, KLR.PolyRep.genOp, KLR.PolyRep.opE_apply]
    rw [spacedOp_apply]
    by_cases hj : j = i
    · subst hj
      rw [Finset.sum_eq_single j, ite_eq_left rfl, Matrix.single_apply_same]
      · simp [galleryRep_e, blk_apply, seqRenEquiv_apply]
      · intro i' _ hi'
        rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hi'), map_zero, LinearMap.zero_apply,
          Pi.zero_apply]
      · intro h
        exact absurd (Finset.mem_univ j) h
    · rw [ite_eq_right hj, map_zero]
      refine Finset.sum_eq_zero fun i' _ => ?_
      rw [Matrix.single_apply_of_row_ne (Ne.symm hj), map_zero, LinearMap.zero_apply,
        Pi.zero_apply]
  · simp only [genMat, KLR.PolyRep.genOp, KLR.PolyRep.opX_apply]
    rw [spacedOp_apply, Finset.sum_eq_single j]
    · simp [galleryRep_poly, seqRenEquiv_apply, seqRen]
    · intro i' _ hi'
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hi'), map_zero, LinearMap.zero_apply,
        Pi.zero_apply]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · simp only [genMat, KLR.PolyRep.genOp]
    by_cases h : n + 1 < m
    · simp only [h, ↓reduceDIte, KLR.PolyRep.opΨ_apply _ _ h]
      rw [spacedOp_apply, Finset.sum_eq_single (TypeA.sadj m n • j)]
      · rw [Matrix.of_apply, ite_eq_left (by rw [smul_smul, TypeA.sadj_mul_self, one_smul]),
          galleryRep_crossElt hΓ hD hl hE, blk_apply, Pi.single_eq_same, seqRenEquiv_apply,
          crossOp_seqRen, smul_smul, TypeA.sadj_mul_self, one_smul, Pi.single_eq_same]
      · intro i' _ hi'
        rw [Matrix.of_apply, ite_eq_right, map_zero, LinearMap.zero_apply, Pi.zero_apply]
        rintro rfl
        apply hi'
        rw [smul_smul, TypeA.sadj_mul_self, one_smul]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · have h0 : KLR.PolyRep.opΨ (ν := ν) Γ.edgeProd n = 0 := KLR.PolyRep.opΨ_eq_zero _ (by omega)
      simp only [h, ↓reduceDIte, h0, LinearMap.zero_apply, Pi.zero_apply, map_zero]
      rw [spacedOp_apply]
      simp

end Generators

section Hom

namespace WeightedGraph

variable (Γ) in
/-- The polynomials `Q_{ab}(u, v) = ∏_{e : b → a} Q_e(u, v) · ∏_{e : a → b} Q_e(v, u)` of the
KLR algebra of Webster's Proposition 2.14, the product running over the edges between `a` and
`b` in both directions. -/
noncomputable def klrQ (a b : I) : MvPolynomial (Fin 2) k :=
  Γ.edgeProd b a * rename ![1, 0] (Γ.edgeProd a b)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Under Webster's standing hypothesis no `Q_e` vanishes. -/
theorem Standing.Q_ne_zero [Nontrivial k] (hS : Γ.Standing) (e : Γ.E) : Γ.Q e ≠ 0 := by
  obtain ⟨d, -, hQ, -⟩ := hS
  obtain ⟨c, c', hc⟩ := hQ e
  intro h0
  have := hc.2.2.1
  simp [h0] at this

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Standing.edgeProd_ne_zero [IsDomain k] (hS : Γ.Standing) (a b : I) :
    Γ.edgeProd a b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun e _ => hS.Q_ne_zero e

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Under Webster's standing hypothesis, `∏_{e : a → b} Q_e`, substituted into two distinct
variables of a polynomial ring in finitely many variables, is a non-zero-divisor, over any
commutative ring. -/
theorem Standing.isRegular_rename_edgeProd {σ : Type*} [Finite σ] (hS : Γ.Standing) (a b : I)
    {f : Fin 2 → σ} (hf : Function.Injective f) : IsRegular (rename f (Γ.edgeProd a b)) := by
  obtain ⟨d, hd, hQ, -⟩ := hS
  rw [edgeProd, map_prod]
  refine IsRegular.prod fun e _ => ?_
  obtain ⟨c, c', hc⟩ := hQ e
  exact isRegular_rename_of_isUnitHomogeneous hf (hd _) (hd _) hc

end WeightedGraph

theorem eq_of_comp_seqRenEquiv {A B : Module.End k (KLR.Seq ν → PolyRing ν' k)}
    (h : A ∘ₗ (seqRenEquiv (k := k) (ν := ν)).toLinearMap =
      B ∘ₗ (seqRenEquiv (k := k) (ν := ν)).toLinearMap) : A = B :=
  LinearMap.ext fun v => by simpa using LinearMap.congr_fun h (seqRenEquiv.symm v)

variable (k Γ ν) in
/-- The generators of `R(ν)` in the weighted KLR algebra of the evenly spaced loadings, on the
free algebra. -/
noncomputable def spacedFreeHom : FreeAlgebra k (KLR.Gen ν) →ₐ[k] SpacedAlgebra k Γ ν :=
  FreeAlgebra.lift k (genImg k Γ)

theorem spacedRep_spacedFreeHom (hΓ : Γ.PSymm) (hD : Γ.Dagger) (hl : ∀ c, Γ.loop c = none)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (x : FreeAlgebra k (KLR.Gen ν)) :
    spacedRep k hΓ (spacedFreeHom k Γ ν x) ∘ₗ seqRenEquiv.toLinearMap =
      seqRenEquiv.toLinearMap ∘ₗ KLR.PolyRep.freeRep ν Γ.edgeProd x := by
  induction x using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    refine LinearMap.ext fun f => ?_
    simp [Module.algebraMap_end_apply]
  | grade1 g =>
    rw [spacedFreeHom, FreeAlgebra.lift_ι_apply, KLR.PolyRep.freeRep, FreeAlgebra.lift_ι_apply,
      spacedRep_apply]
    show spacedOp k hΓ (spacedIdem k Γ ν * genMat k Γ g * spacedIdem k Γ ν) ∘ₗ _ = _
    rw [spacedOp_sandwich]
    exact spacedOp_genMat hΓ hD hl hE g
  | mul a b ha hb =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, hb, ← LinearMap.comp_assoc, ha, LinearMap.comp_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, LinearMap.add_comp, LinearMap.comp_add, ha, hb]

variable (k) in
/-- **Webster, Proposition 2.14** (the map): for a weighted graph without loops, the
homomorphism from the KLR algebra `R(ν)` for `Q = klrQ Γ` to the weighted KLR algebra on the
evenly spaced loadings `B_s(i)`, sending `e(i)` to the idempotent of `B_s(i)`, the dot `x_a` to
the dot on the strand at position `a`, and `ψ_n` to the straight crossing of the strands at
positions `n` and `n + 1` (`crossElt`, followed by the relabelling for strands of one colour).
The relations are checked in the faithful polynomial representation. -/
noncomputable def spacedHom (hS : Γ.Standing) (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) : KLR.KLRAlgebra k Γ.klrQ ν →ₐ[k] SpacedAlgebra k Γ ν :=
  RingQuot.liftAlgHom k ⟨spacedFreeHom k Γ ν, fun x y h =>
    spacedRep_injective hD hE hl hS.psymm hS.isRegular_factor (eq_of_comp_seqRenEquiv (by
      rw [spacedRep_spacedFreeHom hS.psymm hD hl hE, spacedRep_spacedFreeHom hS.psymm hD hl hE,
        KLR.PolyRep.freeRep_rel (Q := Γ.klrQ) (fun a b _ => rfl) h]))⟩

theorem spacedHom_mk (hS : Γ.Standing) (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (x : FreeAlgebra k (KLR.Gen ν)) :
    spacedHom k hS hD hE hl (KLR.KLRAlgebra.mk k Γ.klrQ ν x) = spacedFreeHom k Γ ν x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

/-- `spacedHom` intertwines the polynomial representation of the KLR algebra (KL I,
Proposition 2.3, for `P = edgeProd Γ`) with that of the weighted KLR algebra on the evenly spaced
loadings, after renaming the variables of the component `i` to the strands of `B_s(i)`. -/
theorem spacedRep_spacedHom (hS : Γ.Standing) (hD : Γ.Dagger) (hE : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ c, Γ.loop c = none) (x : KLR.KLRAlgebra k Γ.klrQ ν) :
    spacedRep k hS.psymm (spacedHom k hS hD hE hl x) ∘ₗ seqRenEquiv.toLinearMap =
      seqRenEquiv.toLinearMap ∘ₗ KLR.PolyRep.polyRep (P := Γ.edgeProd) (fun _ _ _ => rfl) x := by
  obtain ⟨x, rfl⟩ := KLR.KLRAlgebra.mk_surjective x
  have h := KLR.PolyRep.polyRep_mk (Q := Γ.klrQ) (P := Γ.edgeProd) (fun _ _ _ => rfl) x
  rw [spacedHom_mk]
  refine (spacedRep_spacedFreeHom hS.psymm hD hl hE x).trans ?_
  exact congrArg (seqRenEquiv.toLinearMap ∘ₗ ·) h.symm

/-- **Webster, Proposition 2.14** (injectivity): the homomorphism `spacedHom` from the KLR
algebra to the weighted KLR algebra on the evenly spaced loadings is injective, over any
commutative ring. Since `spacedHom` intertwines the polynomial representations, this is the
faithfulness of the polynomial representation of the KLR algebra (KL I, Corollary 2.6, over any
commutative ring for `P = edgeProd Γ`, whose substitutions into two variables are
non-zero-divisors by the standing hypothesis). -/
theorem spacedHom_injective (hS : Γ.Standing) (hD : Γ.Dagger)
    (hE : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ c, Γ.loop c = none) :
    Function.Injective (spacedHom k hS hD hE hl (ν := ν)) := by
  intro x y hxy
  apply KLR.polyRep_injective_of_isRegular (P := Γ.edgeProd) (fun a b _ => rfl)
    (fun a b _ f hf => hS.isRegular_rename_edgeProd a b hf)
  have hx := spacedRep_spacedHom hS hD hE hl x
  have hy := spacedRep_spacedHom hS hD hE hl y
  rw [hxy] at hx
  have h := hx.symm.trans hy
  exact LinearMap.ext fun f => seqRenEquiv.injective (LinearMap.congr_fun h f)

end Hom

end Categorification.WeightedKLR
