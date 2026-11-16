/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Juxtapose
import Categorification.WeightedKLR.GalleryBasis.Corner
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.ExternalTensor

/-!
# The juxtaposition map `ι_{ν';ν''}`, induction and restriction

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4
("Induction and restriction"), the paragraph before Definition 2.17: the map
`ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}` places a diagram for `ν'` to the left of a diagram
for `ν''`, far enough apart that no strand or ghost of one meets a strand or ghost of the other. It is not unital: it sends `1 ⊗ 1` to the idempotent
`e_{ν';ν''}`, the sum of the idempotents of the juxtaposed loadings, and `e_i ⊗ e_j` to `e_{i∘j}`.
Definition 2.17 defines `Ind M ⊠ N = W_ν ⊗_{W_{ν'} ⊗ W_{ν''}} M ⊠ N`, `Res L = e_{ν';ν''} L`.

On gallery algebras, the juxtaposition of chambers `C' ∘ C''` (`Juxtapose.chamber`) gives for each
`C''` a chamber embedding `C' ↦ C' ∘ C''`, hence an algebra map into the corner of
`∑_{C'} e (C' ∘ C'')` (`ChamberEmbedding.galleryHom`). These corners are orthogonal for distinct
`C''`, so the maps add up to an algebra map `leftHom` from the gallery algebra of `ν'` into the
corner of `juxtIdem = ∑_{C', C''} e (C' ∘ C'')`; similarly `rightHom` for `ν''`. The two commute
(`commute_leftHom_rightHom`): generators of the two sides commute because they act on disjoint
sets of strands, the case of two steps being the square relation for the independent hyperplanes
of the two sides. They therefore define an algebra map on the tensor product
(`galleryTensorHom`). Restricted to Webster's algebras (the corners at the rank-ordered chambers,
`WeightedKLRAlgebra`), this is the non-unital algebra map `inductionMap = ι_{ν';ν''}`, with
`ι(1 ⊗ 1) = splitIdem = e_{ν';ν''}` (`inductionMap_one`) and `ι(e C' ⊗ e C'') = e (C' ∘ C'')`
(`inductionMap_e_tmul_e`). The separation used is `Juxtapose.bound`, beyond which juxtaposition
crosses no hyperplane between the two sides.

Induction and restriction (`ind`, `res`) are induction and restriction along the non-unital map
`ι` (`InductionAlong.Ind`, `InductionAlong.Res`), applied to the external tensor product
`M ⊠ N` (`ExtTensor`); restriction is right adjoint to induction along `ι`
(`InductionAlong.adjunction`).

## Main definitions and results

* `IsIdempotentElem.cornerSum`: a sum of algebra maps into orthogonal corners.
* `Juxtapose.chamber_inj`, `Juxtapose.juxtIdem`.
* `Juxtapose.leftHom`, `Juxtapose.rightHom`, `Juxtapose.commute_leftHom_rightHom`.
* `Juxtapose.galleryTensorHom`, `Juxtapose.galleryTensorHom_e_tmul_e`.
* `Juxtapose.splitIdem`, `Juxtapose.inductionMap`, `Juxtapose.inductionMap_one`,
  `Juxtapose.inductionMap_e_tmul_e`.
* `Juxtapose.ind`, `Juxtapose.res`.
-/

open scoped TensorProduct

/-! ### Sums of maps into orthogonal corners -/

namespace IsIdempotentElem

variable {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]

/-- The inclusion of a corner, as a linear map. -/
def cornerVal {e : B} (idem : IsIdempotentElem e) : idem.Corner →ₗ[R] B where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mul_eq_zero_of_mem_corner {p q x y : B} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hpq : p * q = 0) (hx : x ∈ Subsemigroup.corner p)
    (hy : y ∈ Subsemigroup.corner q) : x * y = 0 := by
  rw [Subsemigroup.mem_corner_iff hp] at hx
  rw [Subsemigroup.mem_corner_iff hq] at hy
  rw [← hx.2, ← hy.1, mul_assoc, ← mul_assoc p, hpq, zero_mul, mul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → B} {E : B}

omit [DecidableEq ι] in
theorem sum_mul_of_mem_corner (hp : ∀ a, IsIdempotentElem (p a))
    (horth : ∀ a b, a ≠ b → p a * p b = 0) (hsum : ∑ a, p a = E) {a : ι} {x : B}
    (hx : x ∈ Subsemigroup.corner (p a)) : E * x = x := by
  have hx' := (Subsemigroup.mem_corner_iff (hp a)).1 hx
  rw [← hsum, Finset.sum_mul, Finset.sum_eq_single a, hx'.1]
  · intro b _ hb
    rw [← hx'.1, ← mul_assoc, horth b a hb, zero_mul]
  · simp

omit [DecidableEq ι] in
theorem mul_sum_of_mem_corner (hp : ∀ a, IsIdempotentElem (p a))
    (horth : ∀ a b, a ≠ b → p a * p b = 0) (hsum : ∑ a, p a = E) {a : ι} {x : B}
    (hx : x ∈ Subsemigroup.corner (p a)) : x * E = x := by
  have hx' := (Subsemigroup.mem_corner_iff (hp a)).1 hx
  rw [← hsum, Finset.mul_sum, Finset.sum_eq_single a, hx'.2]
  · intro b _ hb
    rw [← hx'.2, mul_assoc, horth a b (Ne.symm hb), mul_zero]
  · simp

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The sum of algebra maps into the corners of orthogonal idempotents `p a` with sum `E`, an
algebra map into the corner of `E`. -/
noncomputable def cornerSum (hp : ∀ a, IsIdempotentElem (p a))
    (horth : ∀ a b, a ≠ b → p a * p b = 0) (hE : IsIdempotentElem E) (hsum : ∑ a, p a = E)
    (φ : ∀ a, A →ₐ[R] (hp a).Corner) : A →ₐ[R] hE.Corner where
  toFun x := ⟨∑ a, (φ a x).1, by
    rw [Subsemigroup.mem_corner_iff hE, Finset.mul_sum, Finset.sum_mul]
    exact ⟨Finset.sum_congr rfl fun a _ => sum_mul_of_mem_corner hp horth hsum (φ a x).2,
      Finset.sum_congr rfl fun a _ => mul_sum_of_mem_corner hp horth hsum (φ a x).2⟩⟩
  map_one' := Subtype.ext (by
    show ∑ a, (φ a 1).1 = E
    simp only [map_one]
    exact hsum)
  map_mul' x y := Subtype.ext (by
    show ∑ a, (φ a (x * y)).1 = (∑ a, (φ a x).1) * ∑ a, (φ a y).1
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a, map_mul]
    · rfl
    · intro b _ hb
      exact mul_eq_zero_of_mem_corner (hp a) (hp b) (horth a b (Ne.symm hb)) (φ a x).2
        (φ b y).2
    · simp)
  map_zero' := Subtype.ext (by
    show ∑ a, (φ a 0).1 = 0
    simp only [map_zero]
    exact Finset.sum_const_zero)
  map_add' x y := Subtype.ext (by
    show ∑ a, (φ a (x + y)).1 = ∑ a, (φ a x).1 + ∑ a, (φ a y).1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [map_add]; rfl)
  commutes' c := Subtype.ext (by
    show ∑ a, (φ a (algebraMap R A c)).1 = c • E
    simp only [AlgHom.commutes]
    rw [← hsum, Finset.smul_sum]
    rfl)

omit [DecidableEq ι] in
theorem cornerSum_val (hp : ∀ a, IsIdempotentElem (p a))
    (horth : ∀ a b, a ≠ b → p a * p b = 0) (hE : IsIdempotentElem E) (hsum : ∑ a, p a = E)
    (φ : ∀ a, A →ₐ[R] (hp a).Corner) (x : A) :
    (cornerSum hp horth hE hsum φ x).1 = ∑ a, (φ a x).1 := rfl

end IsIdempotentElem

namespace Categorification.WeightedKLR

open MvPolynomial Equiv GalleryAlgebra IsIdempotentElem

namespace Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν' ν'' : I →₀ ℕ}

/-! ### Juxtaposed chambers and the idempotent `juxtIdem` -/

omit [DecidableEq I] in
theorem chamber_inj {C' D' : FullChamber Γ ν'} {C'' D'' : FullChamber Γ ν''} :
    chamber C' C'' = chamber D' D'' ↔ C' = D' ∧ C'' = D'' := by
  refine ⟨fun h => ⟨Subtype.ext (funext fun h' => ?_), Subtype.ext (funext fun h' => ?_)⟩,
    fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩
  · rw [← chamber_left C' C'' h', ← chamber_left D' D'' h', h]
  · rw [← chamber_right C' C'' h', ← chamber_right D' D'' h', h]

variable (k Γ ν' ν'') in
/-- The idempotent `∑_{C', C''} e (C' ∘ C'')`. -/
noncomputable def juxtIdem : GalleryAlgebra k Γ (ν' + ν'') :=
  ∑ C' : FullChamber Γ ν', ∑ C'' : FullChamber Γ ν'', e (chamber C' C'')

theorem e_mul_e_chamber (C' D' : FullChamber Γ ν') (C'' D'' : FullChamber Γ ν'') :
    (e (chamber C' C'') * e (chamber D' D'') : GalleryAlgebra k Γ (ν' + ν'')) =
      if C' = D' ∧ C'' = D'' then e (chamber C' C'') else 0 := by
  rw [e_mul_e]
  exact if_congr chamber_inj rfl rfl

theorem juxtIdem_mul_e (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    juxtIdem k Γ ν' ν'' * e (chamber C' C'') = e (chamber C' C'') := by
  rw [juxtIdem, Finset.sum_mul, Finset.sum_eq_single C', Finset.sum_mul,
    Finset.sum_eq_single C'', e_mul_e_chamber, ite_eq_left ⟨rfl, rfl⟩]
  · intro D'' _ hD
    rw [e_mul_e_chamber, ite_eq_right fun h => hD h.2]
  · simp
  · intro D' _ hD
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun D'' _ => by rw [e_mul_e_chamber, ite_eq_right fun h => hD h.1]
  · simp

theorem e_mul_juxtIdem (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    e (chamber C' C'') * juxtIdem k Γ ν' ν'' = e (chamber C' C'') := by
  rw [juxtIdem, Finset.mul_sum, Finset.sum_eq_single C', Finset.mul_sum,
    Finset.sum_eq_single C'', e_mul_e_chamber, ite_eq_left ⟨rfl, rfl⟩]
  · intro D'' _ hD
    rw [e_mul_e_chamber, ite_eq_right fun h => hD h.2.symm]
  · simp
  · intro D' _ hD
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun D'' _ => by rw [e_mul_e_chamber, ite_eq_right fun h => hD h.1.symm]
  · simp

theorem isIdempotentElem_juxtIdem : IsIdempotentElem (juxtIdem k Γ ν' ν'') := by
  show juxtIdem k Γ ν' ν'' * juxtIdem k Γ ν' ν'' = juxtIdem k Γ ν' ν''
  nth_rw 2 [juxtIdem]
  simp only [Finset.mul_sum, juxtIdem_mul_e]
  rfl

theorem juxtIdem_mul_poly (f : PolyRing (ν' + ν'') k) :
    juxtIdem k Γ ν' ν'' * poly f = poly f * juxtIdem k Γ ν' ν'' := by
  simp only [juxtIdem, Finset.sum_mul, Finset.mul_sum, e_mul_poly]

theorem leftIdem_orth (C'' D'' : FullChamber Γ ν'') (hne : C'' ≠ D'') :
    (leftChamberEmb (k := k) (ν' := ν') C'').idem * (leftChamberEmb D'').idem = 0 := by
  show (∑ A', e (chamber A' C'')) * (∑ B', e (chamber B' D'')) = 0
  rw [Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun A' _ => Finset.sum_eq_zero fun B' _ => by
    rw [e_mul_e_chamber, ite_eq_right fun h => hne h.2]

theorem rightIdem_orth (C' D' : FullChamber Γ ν') (hne : C' ≠ D') :
    (rightChamberEmb (k := k) (ν'' := ν'') C').idem * (rightChamberEmb D').idem = 0 := by
  show (∑ A'', e (chamber C' A'')) * (∑ B'', e (chamber D' B'')) = 0
  rw [Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun A'' _ => Finset.sum_eq_zero fun B'' _ => by
    rw [e_mul_e_chamber, ite_eq_right fun h => hne h.1]

theorem sum_leftIdem :
    ∑ C'' : FullChamber Γ ν'', (leftChamberEmb (k := k) (ν' := ν') C'').idem =
      juxtIdem k Γ ν' ν'' :=
  Finset.sum_comm

theorem sum_rightIdem :
    ∑ C' : FullChamber Γ ν', (rightChamberEmb (k := k) (ν'' := ν'') C').idem =
      juxtIdem k Γ ν' ν'' :=
  rfl

/-! ### The two algebra maps -/

variable (k Γ ν' ν'') in
/-- The gallery algebra of `ν'` acting on the left part of the juxtaposed diagrams. -/
noncomputable def leftHom :
    GalleryAlgebra k Γ ν' →ₐ[k] (isIdempotentElem_juxtIdem (k := k) (Γ := Γ) (ν' := ν')
      (ν'' := ν'')).Corner :=
  cornerSum (fun C'' => (leftChamberEmb C'').isIdempotentElem_idem)
    leftIdem_orth isIdempotentElem_juxtIdem sum_leftIdem
    (fun C'' => (leftChamberEmb C'').galleryHom)

variable (k Γ ν' ν'') in
/-- The gallery algebra of `ν''` acting on the right part of the juxtaposed diagrams. -/
noncomputable def rightHom :
    GalleryAlgebra k Γ ν'' →ₐ[k] (isIdempotentElem_juxtIdem (k := k) (Γ := Γ) (ν' := ν')
      (ν'' := ν'')).Corner :=
  cornerSum (fun C' => (rightChamberEmb C').isIdempotentElem_idem)
    rightIdem_orth isIdempotentElem_juxtIdem sum_rightIdem
    (fun C' => (rightChamberEmb C').galleryHom)

theorem leftHom_e (C' : FullChamber Γ ν') :
    (leftHom k Γ ν' ν'' (e C')).1 = ∑ C'', e (chamber C' C'') := by
  rw [leftHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_e]
  rfl

theorem leftHom_poly (f : PolyRing ν' k) :
    (leftHom k Γ ν' ν'' (poly f)).1 = poly (rename (inlStrand ν' ν'') f) * juxtIdem k Γ ν' ν'' := by
  rw [leftHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_poly]
  change ∑ C'', poly (rename (inlStrand ν' ν'') f) * (leftChamberEmb C'').idem = _
  rw [← Finset.mul_sum, sum_leftIdem]

theorem leftHom_t (A' B' : FullChamber Γ ν') :
    (leftHom k Γ ν' ν'' (t A' B')).1 = ∑ C'', t (chamber A' C'') (chamber B' C'') := by
  rw [leftHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_t]
  rfl

theorem leftHom_r (g : ColPerm ν') (A' : FullChamber Γ ν') :
    (leftHom k Γ ν' ν'' (r g A')).1 = ∑ C'', r (leftPerm ν' ν'' g) (chamber A' C'') := by
  rw [leftHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_r]
  rfl

theorem rightHom_e (C'' : FullChamber Γ ν'') :
    (rightHom k Γ ν' ν'' (e C'')).1 = ∑ C', e (chamber C' C'') := by
  rw [rightHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_e]
  rfl

theorem rightHom_poly (f : PolyRing ν'' k) :
    (rightHom k Γ ν' ν'' (poly f)).1 =
      poly (rename (inrStrand ν' ν'') f) * juxtIdem k Γ ν' ν'' := by
  rw [rightHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_poly]
  change ∑ C', poly (rename (inrStrand ν' ν'') f) * (rightChamberEmb C').idem = _
  rw [← Finset.mul_sum, sum_rightIdem]

theorem rightHom_t (A'' B'' : FullChamber Γ ν'') :
    (rightHom k Γ ν' ν'' (t A'' B'')).1 = ∑ C', t (chamber C' A'') (chamber C' B'') := by
  rw [rightHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_t]
  rfl

theorem rightHom_r (g : ColPerm ν'') (A'' : FullChamber Γ ν'') :
    (rightHom k Γ ν' ν'' (r g A'')).1 = ∑ C', r (rightPerm ν' ν'' g) (chamber C' A'') := by
  rw [rightHom, cornerSum_val]
  simp only [ChamberEmbedding.galleryHom_r]
  rfl

/-! ### Commutation of the two sides -/

theorem sum_mul_sum_eq {R α β : Type*} [Ring R] [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (X : α → R) (Y : β → R) (P : α → R) (Q : β → R) (a₀ : α) (b₀ : β)
    (hX : ∀ i, X i * P i = X i) (hY : ∀ j, Q j * Y j = Y j)
    (hPQ : ∀ i j, ¬(i = a₀ ∧ j = b₀) → P i * Q j = 0) :
    (∑ i, X i) * (∑ j, Y j) = X a₀ * Y b₀ := by
  have hz : ∀ i j, ¬(i = a₀ ∧ j = b₀) → X i * Y j = 0 := fun i j h => by
    rw [← hX i, ← hY j, mul_assoc, ← mul_assoc (P i), hPQ i j h, zero_mul, mul_zero]
  rw [Finset.sum_mul_sum, Finset.sum_eq_single a₀, Finset.sum_eq_single b₀]
  · exact fun j _ hj => hz _ _ fun h => hj h.2
  · simp
  · exact fun i _ hi => Finset.sum_eq_zero fun j _ => hz _ _ fun h => hi h.1
  · simp

/-- Two sums whose summands are supported on the juxtaposed chambers commute, provided the two
surviving products agree. -/
theorem commute_of_sums {x : GalleryAlgebra k Γ ν'} {y : GalleryAlgebra k Γ ν''}
    (X : FullChamber Γ ν'' → GalleryAlgebra k Γ (ν' + ν''))
    (Y : FullChamber Γ ν' → GalleryAlgebra k Γ (ν' + ν''))
    (a' b' : FullChamber Γ ν') (a'' b'' : FullChamber Γ ν'')
    (hx : (leftHom k Γ ν' ν'' x).1 = ∑ C'', X C'')
    (hy : (rightHom k Γ ν' ν'' y).1 = ∑ C', Y C')
    (hXr : ∀ C'', X C'' * e (chamber a' C'') = X C'')
    (hXl : ∀ C'', e (chamber b' C'') * X C'' = X C'')
    (hYr : ∀ C', Y C' * e (chamber C' a'') = Y C')
    (hYl : ∀ C', e (chamber C' b'') * Y C' = Y C')
    (h : X b'' * Y a' = Y b' * X a'') :
    Commute (leftHom k Γ ν' ν'' x) (rightHom k Γ ν' ν'' y) := by
  apply Subtype.ext
  show (leftHom k Γ ν' ν'' x).1 * (rightHom k Γ ν' ν'' y).1 =
    (rightHom k Γ ν' ν'' y).1 * (leftHom k Γ ν' ν'' x).1
  rw [hx, hy, sum_mul_sum_eq X Y (fun i => e (chamber a' i)) (fun j => e (chamber j b''))
      b'' a' hXr hYl ?_,
    sum_mul_sum_eq Y X (fun j => e (chamber j a'')) (fun i => e (chamber b' i)) b' a'' hYr hXl ?_,
    h]
  · intro j i hji
    rw [e_mul_e_chamber, ite_eq_right fun hh => hji ⟨hh.1, hh.2.symm⟩]
  · intro i j hij
    rw [e_mul_e_chamber, ite_eq_right fun hh => hij ⟨hh.2, hh.1.symm⟩]

theorem e_smul_mul_r {ν : I →₀ ℕ} (g : ColPerm ν) (C : FullChamber Γ ν) :
    (e (g • C) * r g C : GalleryAlgebra k Γ ν) = r g C := by
  rw [e_mul_r, ite_eq_left rfl]

omit [DecidableEq I] in
theorem smul_chamber_left (g : ColPerm ν') (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    leftPerm ν' ν'' g • chamber C' C'' = chamber (g • C') C'' :=
  (leftChamberEmb C'').smul_chamber g C'

omit [DecidableEq I] in
theorem smul_chamber_right (g : ColPerm ν'') (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    rightPerm ν' ν'' g • chamber C' C'' = chamber C' (g • C'') :=
  (rightChamberEmb C').smul_chamber g C''

omit [DecidableEq I] in
theorem rename_rightPerm_inl (g : ColPerm ν'') (f : PolyRing ν' k) :
    rename (rightPerm ν' ν'' g).1 (rename (inlStrand ν' ν'') f) = rename (inlStrand ν' ν'') f := by
  rw [rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => colPermProd_inl (1, g) s)

omit [DecidableEq I] in
theorem rename_leftPerm_inr (g : ColPerm ν') (f : PolyRing ν'' k) :
    rename (leftPerm ν' ν'' g).1 (rename (inrStrand ν' ν'') f) = rename (inrStrand ν' ν'') f := by
  rw [rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => colPermProd_inr (g, 1) s)

theorem rename_swap_inl {l r' : Strand (ν' + ν'')} (hl : ∀ s, inlStrand ν' ν'' s ≠ l)
    (hr : ∀ s, inlStrand ν' ν'' s ≠ r') (f : PolyRing ν' k) :
    rename (swap l r') (rename (inlStrand ν' ν'') f) = rename (inlStrand ν' ν'') f := by
  rw [rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => swap_apply_of_ne_of_ne (hl s) (hr s))

theorem rename_swap_inr {l r' : Strand (ν' + ν'')} (hl : ∀ s, inrStrand ν' ν'' s ≠ l)
    (hr : ∀ s, inrStrand ν' ν'' s ≠ r') (f : PolyRing ν'' k) :
    rename (swap l r') (rename (inrStrand ν' ν'') f) = rename (inrStrand ν' ν'') f := by
  rw [rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => swap_apply_of_ne_of_ne (hl s) (hr s))

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem stepFactor_eq_zero {ν : I →₀ ℕ} {l r' : Strand ν} (hlr : l ≠ r') {F : PolyRing ν k}
    (hF : rename (swap l r') F = F) : stepFactor Γ l r' F = 0 := by
  unfold stepFactor
  split
  · exact ddiff_eq_zero_of_rename_eq hlr hF
  · rw [hF, sub_self, mul_zero]

theorem poly_zero {ν : I →₀ ℕ} : (poly 0 : GalleryAlgebra k Γ ν) = 0 :=
  (polyHom k Γ ν).map_zero

/-- A polynomial in the strands of `ν'` commutes with a step of the right side. -/
theorem poly_mul_t_right (f : PolyRing ν' k) (C' : FullChamber Γ ν') (A'' B'' : FullChamber Γ ν'') :
    poly (rename (inlStrand ν' ν'') f) * t (chamber C' A'') (chamber C' B'') =
      (t (chamber C' A'') (chamber C' B'') * poly (rename (inlStrand ν' ν'') f) :
        GalleryAlgebra k Γ (ν' + ν'')) := by
  by_cases hA : ∃ h, A''.Adjacent B'' h
  · obtain ⟨h, hh⟩ := hA
    have ha := (rightChamberEmb C').adjacent_chamber hh
    rcases h with w | d
    · exact (t_mul_poly_inl (w := (rightEmb ν' ν'').wall w) ha _).symm
    · have ha' : (chamber C' A'').Adjacent (chamber C' B'') (.inr ((rightEmb ν' ν'').diag d)) := ha
      rw [t_mul_poly_inr ha', stepFactor_eq_zero (StrandEmbedding.left_ne_right _ _), poly_zero,
        zero_mul, add_zero]
      have hl : ∀ s, inlStrand ν' ν'' s ≠ ((rightEmb ν' ν'').diag d).left (chamber C' A'') := by
        intro s
        unfold Diag.left
        split_ifs
        · exact inlStrand_ne_inrStrand ν' ν'' s _
        · exact inlStrand_ne_inrStrand ν' ν'' s _
      have hr : ∀ s, inlStrand ν' ν'' s ≠ ((rightEmb ν' ν'').diag d).right (chamber C' A'') := by
        intro s
        unfold Diag.right
        split_ifs
        · exact inlStrand_ne_inrStrand ν' ν'' s _
        · exact inlStrand_ne_inrStrand ν' ν'' s _
      exact rename_swap_inl hl hr f
  · have h0 : (t (chamber C' A'') (chamber C' B'') : GalleryAlgebra k Γ (ν' + ν'')) = 0 :=
      t_eq_zero ((rightChamberEmb C').not_adjacent_chamber fun h hh => hA ⟨h, hh⟩)
    rw [h0, mul_zero, zero_mul]

/-- A polynomial in the strands of `ν''` commutes with a step of the left side. -/
theorem poly_mul_t_left (f : PolyRing ν'' k) (A' B' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    poly (rename (inrStrand ν' ν'') f) * t (chamber A' C'') (chamber B' C'') =
      (t (chamber A' C'') (chamber B' C'') * poly (rename (inrStrand ν' ν'') f) :
        GalleryAlgebra k Γ (ν' + ν'')) := by
  by_cases hA : ∃ h, A'.Adjacent B' h
  · obtain ⟨h, hh⟩ := hA
    have ha := (leftChamberEmb C'').adjacent_chamber hh
    rcases h with w | d
    · exact (t_mul_poly_inl (w := (leftEmb ν' ν'').wall w) ha _).symm
    · have ha' : (chamber A' C'').Adjacent (chamber B' C'') (.inr ((leftEmb ν' ν'').diag d)) := ha
      rw [t_mul_poly_inr ha', stepFactor_eq_zero (StrandEmbedding.left_ne_right _ _), poly_zero,
        zero_mul, add_zero]
      have hl : ∀ s, inrStrand ν' ν'' s ≠ ((leftEmb ν' ν'').diag d).left (chamber A' C'') := by
        intro s
        unfold Diag.left
        split_ifs
        · exact (inlStrand_ne_inrStrand ν' ν'' _ s).symm
        · exact (inlStrand_ne_inrStrand ν' ν'' _ s).symm
      have hr : ∀ s, inrStrand ν' ν'' s ≠ ((leftEmb ν' ν'').diag d).right (chamber A' C'') := by
        intro s
        unfold Diag.right
        split_ifs
        · exact (inlStrand_ne_inrStrand ν' ν'' _ s).symm
        · exact (inlStrand_ne_inrStrand ν' ν'' _ s).symm
      exact rename_swap_inr hl hr f
  · have h0 : (t (chamber A' C'') (chamber B' C'') : GalleryAlgebra k Γ (ν' + ν'')) = 0 :=
      t_eq_zero ((leftChamberEmb C'').not_adjacent_chamber fun h hh => hA ⟨h, hh⟩)
    rw [h0, mul_zero, zero_mul]

theorem poly_mul_r_right (f : PolyRing ν' k) (g : ColPerm ν'') (C : FullChamber Γ (ν' + ν'')) :
    poly (rename (inlStrand ν' ν'') f) * r (rightPerm ν' ν'' g) C =
      (r (rightPerm ν' ν'' g) C * poly (rename (inlStrand ν' ν'') f) :
        GalleryAlgebra k Γ (ν' + ν'')) := by
  rw [r_mul_poly, rename_rightPerm_inl]

theorem poly_mul_r_left (f : PolyRing ν'' k) (g : ColPerm ν') (C : FullChamber Γ (ν' + ν'')) :
    poly (rename (inrStrand ν' ν'') f) * r (leftPerm ν' ν'' g) C =
      (r (leftPerm ν' ν'' g) C * poly (rename (inrStrand ν' ν'') f) :
        GalleryAlgebra k Γ (ν' + ν'')) := by
  rw [r_mul_poly, rename_leftPerm_inr]

theorem poly_mul_poly_juxtIdem (F G : PolyRing (ν' + ν'') k) :
    poly F * (poly G * juxtIdem k Γ ν' ν'') = poly G * juxtIdem k Γ ν' ν'' * poly F := by
  rw [mul_assoc, juxtIdem_mul_poly, ← mul_assoc, ← mul_assoc, poly_mul_poly, poly_mul_poly,
    mul_comm]

theorem poly_comm_rightGen (f : PolyRing ν' k) (g : Gen k Γ ν'') :
    poly (rename (inlStrand ν' ν'') f) *
        (rightHom k Γ ν' ν'' (mk k Γ ν'' (FreeAlgebra.ι k g))).1 =
      (rightHom k Γ ν' ν'' (mk k Γ ν'' (FreeAlgebra.ι k g))).1 *
        poly (rename (inlStrand ν' ν'') f) := by
  cases g with
  | idem C'' =>
    rw [show mk k Γ ν'' (FreeAlgebra.ι k (.idem C'')) = e C'' from rfl, rightHom_e,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => (e_mul_poly _ _).symm
  | poly G =>
    rw [show mk k Γ ν'' (FreeAlgebra.ι k (.poly G)) = poly G from rfl, rightHom_poly]
    exact poly_mul_poly_juxtIdem _ _
  | step A'' B'' =>
    rw [show mk k Γ ν'' (FreeAlgebra.ι k (.step A'' B'')) = t A'' B'' from rfl, rightHom_t,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => poly_mul_t_right _ _ _ _
  | relabel g A'' =>
    rw [show mk k Γ ν'' (FreeAlgebra.ι k (.relabel g A'')) = r g A'' from rfl, rightHom_r,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => poly_mul_r_right _ _ _

theorem poly_comm_leftGen (f : PolyRing ν'' k) (g : Gen k Γ ν') :
    poly (rename (inrStrand ν' ν'') f) *
        (leftHom k Γ ν' ν'' (mk k Γ ν' (FreeAlgebra.ι k g))).1 =
      (leftHom k Γ ν' ν'' (mk k Γ ν' (FreeAlgebra.ι k g))).1 *
        poly (rename (inrStrand ν' ν'') f) := by
  cases g with
  | idem C' =>
    rw [show mk k Γ ν' (FreeAlgebra.ι k (.idem C')) = e C' from rfl, leftHom_e,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => (e_mul_poly _ _).symm
  | poly G =>
    rw [show mk k Γ ν' (FreeAlgebra.ι k (.poly G)) = poly G from rfl, leftHom_poly]
    exact poly_mul_poly_juxtIdem _ _
  | step A' B' =>
    rw [show mk k Γ ν' (FreeAlgebra.ι k (.step A' B')) = t A' B' from rfl, leftHom_t,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => poly_mul_t_left _ _ _ _
  | relabel g A' =>
    rw [show mk k Γ ν' (FreeAlgebra.ι k (.relabel g A')) = r g A' from rfl, leftHom_r,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => poly_mul_r_left _ _ _

theorem commute_leftHom_poly (f : PolyRing ν' k) (y : GalleryAlgebra k Γ ν'')
    (hy : poly (rename (inlStrand ν' ν'') f) * (rightHom k Γ ν' ν'' y).1 =
      (rightHom k Γ ν' ν'' y).1 * poly (rename (inlStrand ν' ν'') f)) :
    Commute (leftHom k Γ ν' ν'' (poly f)) (rightHom k Γ ν' ν'' y) := by
  have hm := (Subsemigroup.mem_corner_iff isIdempotentElem_juxtIdem).1 (rightHom k Γ ν' ν'' y).2
  apply Subtype.ext
  show (leftHom k Γ ν' ν'' (poly f)).1 * (rightHom k Γ ν' ν'' y).1 =
    (rightHom k Γ ν' ν'' y).1 * (leftHom k Γ ν' ν'' (poly f)).1
  rw [leftHom_poly, mul_assoc, hm.1, ← mul_assoc, ← hy, mul_assoc, hm.2]

theorem commute_rightHom_poly (f : PolyRing ν'' k) (x : GalleryAlgebra k Γ ν')
    (hx : poly (rename (inrStrand ν' ν'') f) * (leftHom k Γ ν' ν'' x).1 =
      (leftHom k Γ ν' ν'' x).1 * poly (rename (inrStrand ν' ν'') f)) :
    Commute (leftHom k Γ ν' ν'' x) (rightHom k Γ ν' ν'' (poly f)) := by
  have hm := (Subsemigroup.mem_corner_iff isIdempotentElem_juxtIdem).1 (leftHom k Γ ν' ν'' x).2
  apply Subtype.ext
  show (leftHom k Γ ν' ν'' x).1 * (rightHom k Γ ν' ν'' (poly f)).1 =
    (rightHom k Γ ν' ν'' (poly f)).1 * (leftHom k Γ ν' ν'' x).1
  rw [rightHom_poly, ← mul_assoc, ← hx, mul_assoc, hm.2, mul_assoc, hm.1]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem strands_nonempty {ν : I →₀ ℕ} (h : Hyp Γ ν) : h.strands.Nonempty := by
  rcases h with w | d <;> exact Finset.insert_nonempty _ _

/-- The square relation for a hyperplane of `ν'` and a hyperplane of `ν''`. -/
theorem t_square {A' B' : FullChamber Γ ν'} {A'' B'' : FullChamber Γ ν''} {h' : Hyp Γ ν'}
    {h'' : Hyp Γ ν''} (a' : A'.Adjacent B' h') (a'' : A''.Adjacent B'' h'') :
    (t (chamber B' A'') (chamber B' B'') * t (chamber A' A'') (chamber B' A'') :
        GalleryAlgebra k Γ (ν' + ν'')) =
      t (chamber A' B'') (chamber B' B'') * t (chamber A' A'') (chamber A' B'') := by
  have hd : Disjoint ((leftEmb ν' ν'').hyp h').strands ((rightEmb ν' ν'').hyp h'').strands := by
    rw [StrandEmbedding.strands_hyp, StrandEmbedding.strands_hyp, Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hu
    obtain ⟨b, -, hb⟩ := Finset.mem_map.1 hu'
    exact inlStrand_ne_inrStrand ν' ν'' a b hb.symm
  have hne : (leftEmb ν' ν'').hyp h' ≠ (rightEmb ν' ν'').hyp h'' := by
    intro heq
    rw [heq, Finset.disjoint_self_iff_empty] at hd
    exact (strands_nonempty _).ne_empty hd
  have := rel (Rel.square (k := k) (chamber A' A'') (chamber B' A'') (chamber A' B'')
    (chamber B' B'') _ _ hne (Or.inr hd) ((leftChamberEmb A'').adjacent_chamber a')
    ((rightChamberEmb B').adjacent_chamber a'') ((rightChamberEmb A').adjacent_chamber a'')
    ((leftChamberEmb B'').adjacent_chamber a'))
  simp only [map_mul] at this
  exact this

theorem commute_gen (g : Gen k Γ ν') (g' : Gen k Γ ν'') :
    Commute (leftHom k Γ ν' ν'' (mk k Γ ν' (FreeAlgebra.ι k g)))
      (rightHom k Γ ν' ν'' (mk k Γ ν'' (FreeAlgebra.ι k g'))) := by
  cases g with
  | poly f => exact commute_leftHom_poly f _ (poly_comm_rightGen f g')
  | idem C' =>
    cases g' with
    | poly f => exact commute_rightHom_poly f _ (poly_comm_leftGen f (.idem C'))
    | idem C'' =>
      exact commute_of_sums (fun C'' => e (chamber C' C'')) (fun C' => e (chamber C' C''))
        C' C' C'' C'' (leftHom_e C') (rightHom_e C'') (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) rfl
    | step A'' B'' =>
      exact commute_of_sums (fun C'' => e (chamber C' C''))
        (fun C' => t (chamber C' A'') (chamber C' B'')) C' C' A'' B'' (leftHom_e C')
        (rightHom_t A'' B'') (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _)
        (by rw [e_mul_t, t_mul_e])
    | relabel g A'' =>
      exact commute_of_sums (fun C'' => e (chamber C' C''))
        (fun C' => r (rightPerm ν' ν'' g) (chamber C' A'')) C' C' A'' (g • A'') (leftHom_e C')
        (rightHom_r g A'') (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) (fun _ => r_mul_e _ _)
        (fun C' => by rw [← smul_chamber_right, e_smul_mul_r])
        (by rw [← smul_chamber_right, e_smul_mul_r, r_mul_e])
  | step A' B' =>
    cases g' with
    | poly f => exact commute_rightHom_poly f _ (poly_comm_leftGen f (.step A' B'))
    | idem C'' =>
      exact commute_of_sums (fun C'' => t (chamber A' C'') (chamber B' C''))
        (fun C' => e (chamber C' C'')) A' B' C'' C'' (leftHom_t A' B') (rightHom_e C'')
        (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _) (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) (by rw [t_mul_e, e_mul_t])
    | step A'' B'' =>
      show Commute (leftHom k Γ ν' ν'' (t A' B')) (rightHom k Γ ν' ν'' (t A'' B''))
      by_cases h₁ : ∃ h, A'.Adjacent B' h
      swap
      · rw [t_eq_zero fun h hh => h₁ ⟨h, hh⟩, map_zero]
        exact Commute.zero_left _
      by_cases h₂ : ∃ h, A''.Adjacent B'' h
      swap
      · rw [t_eq_zero (C := A'') fun h hh => h₂ ⟨h, hh⟩, map_zero]
        exact Commute.zero_right _
      obtain ⟨h', a'⟩ := h₁
      obtain ⟨h'', a''⟩ := h₂
      exact commute_of_sums (fun C'' => t (chamber A' C'') (chamber B' C''))
        (fun C' => t (chamber C' A'') (chamber C' B'')) A' B' A'' B'' (leftHom_t A' B')
        (rightHom_t A'' B'') (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _)
        (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _) (t_square a' a'').symm
    | relabel g A'' =>
      exact commute_of_sums (fun C'' => t (chamber A' C'') (chamber B' C''))
        (fun C' => r (rightPerm ν' ν'' g) (chamber C' A'')) A' B' A'' (g • A'')
        (leftHom_t A' B') (rightHom_r g A'') (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _)
        (fun _ => r_mul_e _ _) (fun C' => by rw [← smul_chamber_right, e_smul_mul_r])
        (by rw [r_mul_t, smul_chamber_right, smul_chamber_right])
  | relabel g A' =>
    cases g' with
    | poly f => exact commute_rightHom_poly f _ (poly_comm_leftGen f (.relabel g A'))
    | idem C'' =>
      exact commute_of_sums (fun C'' => r (leftPerm ν' ν'' g) (chamber A' C''))
        (fun C' => e (chamber C' C'')) A' (g • A') C'' C'' (leftHom_r g A') (rightHom_e C'')
        (fun _ => r_mul_e _ _) (fun C'' => by rw [← smul_chamber_left, e_smul_mul_r])
        (fun _ => by rw [e_mul_e, ite_eq_left rfl]) (fun _ => by rw [e_mul_e, ite_eq_left rfl])
        (by rw [r_mul_e, ← smul_chamber_left, e_smul_mul_r])
    | step A'' B'' =>
      exact commute_of_sums (fun C'' => r (leftPerm ν' ν'' g) (chamber A' C''))
        (fun C' => t (chamber C' A'') (chamber C' B'')) A' (g • A') A'' B'' (leftHom_r g A')
        (rightHom_t A'' B'') (fun _ => r_mul_e _ _)
        (fun C'' => by rw [← smul_chamber_left, e_smul_mul_r])
        (fun _ => t_mul_e _ _) (fun _ => e_mul_t _ _)
        (by rw [r_mul_t, smul_chamber_left, smul_chamber_left])
    | relabel g' A'' =>
      exact commute_of_sums (fun C'' => r (leftPerm ν' ν'' g) (chamber A' C''))
        (fun C' => r (rightPerm ν' ν'' g') (chamber C' A'')) A' (g • A') A'' (g' • A'')
        (leftHom_r g A') (rightHom_r g' A'') (fun _ => r_mul_e _ _)
        (fun C'' => by rw [← smul_chamber_left, e_smul_mul_r]) (fun _ => r_mul_e _ _)
        (fun C' => by rw [← smul_chamber_right, e_smul_mul_r])
        (by rw [← smul_chamber_right g' A' A'', r_mul_r, ← smul_chamber_left g A' A'', r_mul_r,
          leftPerm_mul_rightPerm])

/-- The two sides commute. -/
theorem commute_leftHom_rightHom (x : GalleryAlgebra k Γ ν') (y : GalleryAlgebra k Γ ν'') :
    Commute (leftHom k Γ ν' ν'' x) (rightHom k Γ ν' ν'' y) := by
  obtain ⟨a, rfl⟩ := mk_surjective x
  obtain ⟨b, rfl⟩ := mk_surjective y
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    simp only [AlgHom.commutes]
    exact Algebra.commute_algebraMap_left _ _
  | grade1 g =>
    induction b using FreeAlgebra.induction with
    | grade0 c =>
      simp only [AlgHom.commutes]
      exact Algebra.commute_algebraMap_right _ _
    | grade1 g' => exact commute_gen g g'
    | mul a b ha hb =>
      rw [map_mul, map_mul]
      exact ha.mul_right hb
    | add a b ha hb =>
      rw [map_add, map_add]
      exact ha.add_right hb
  | mul a a' ha ha' =>
    rw [map_mul, map_mul]
    exact ha.mul_left ha'
  | add a a' ha ha' =>
    rw [map_add, map_add]
    exact ha.add_left ha'

/-! ### The map on the tensor product -/

variable (k Γ ν' ν'') in
/-- Juxtaposition on the tensor product of the gallery algebras. -/
noncomputable def galleryTensorHom :
    GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν'' →ₐ[k]
      (isIdempotentElem_juxtIdem (k := k) (Γ := Γ) (ν' := ν') (ν'' := ν'')).Corner :=
  Algebra.TensorProduct.lift (leftHom k Γ ν' ν'') (rightHom k Γ ν' ν'') commute_leftHom_rightHom

theorem galleryTensorHom_tmul (x : GalleryAlgebra k Γ ν') (y : GalleryAlgebra k Γ ν'') :
    galleryTensorHom k Γ ν' ν'' (x ⊗ₜ y) = leftHom k Γ ν' ν'' x * rightHom k Γ ν' ν'' y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `e C' ⊗ e C''` goes to the idempotent of the juxtaposed chamber `C' ∘ C''`. -/
theorem galleryTensorHom_e_tmul_e (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    (galleryTensorHom k Γ ν' ν'' (e C' ⊗ₜ e C'')).1 = e (chamber C' C'') := by
  rw [galleryTensorHom_tmul]
  show (leftHom k Γ ν' ν'' (e C')).1 * (rightHom k Γ ν' ν'' (e C'')).1 = _
  rw [leftHom_e, rightHom_e, sum_mul_sum_eq _ _ (fun i => e (chamber C' i))
    (fun j => e (chamber j C'')) C'' C' (fun _ => by rw [e_mul_e, ite_eq_left rfl])
    (fun _ => by rw [e_mul_e, ite_eq_left rfl]), e_mul_e, ite_eq_left rfl]
  intro i j hij
  rw [e_mul_e_chamber, ite_eq_right fun hh => hij ⟨hh.2, hh.1.symm⟩]

/-! ### Webster's map `ι_{ν';ν''}` -/

variable (k Γ ν' ν'') in
/-- Webster's idempotent `e_{ν';ν''}`: the sum of `e (C' ∘ C'')` over rank-ordered `C'`, `C''`. -/
noncomputable def splitIdem : GalleryAlgebra k Γ (ν' + ν'') :=
  ∑ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
    ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered, e (chamber C' C'')

theorem rankIdem_mul_splitIdem :
    rankIdem k Γ (ν' + ν'') * splitIdem k Γ ν' ν'' = splitIdem k Γ ν' ν'' := by
  simp only [splitIdem, Finset.mul_sum, rankIdem_mul_e]
  refine Finset.sum_congr rfl fun C' hC' => Finset.sum_congr rfl fun C'' hC'' => ite_eq_left ?_
  exact (isRankOrdered_chamber_iff C' C'').2 ⟨(Finset.mem_filter.1 hC').2,
    (Finset.mem_filter.1 hC'').2⟩

theorem splitIdem_mul_rankIdem :
    splitIdem k Γ ν' ν'' * rankIdem k Γ (ν' + ν'') = splitIdem k Γ ν' ν'' := by
  simp only [splitIdem, Finset.sum_mul, e_mul_rankIdem]
  refine Finset.sum_congr rfl fun C' hC' => Finset.sum_congr rfl fun C'' hC'' => ite_eq_left ?_
  exact (isRankOrdered_chamber_iff C' C'').2 ⟨(Finset.mem_filter.1 hC').2,
    (Finset.mem_filter.1 hC'').2⟩

variable (k Γ ν' ν'') in
/-- The underlying linear map of `ι_{ν';ν''}`, with values in the gallery algebra. -/
noncomputable def inductionLinear :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₗ[k] GalleryAlgebra k Γ (ν' + ν'') :=
  (cornerVal (R := k) isIdempotentElem_juxtIdem).comp
    ((galleryTensorHom k Γ ν' ν'').toLinearMap.comp
      (TensorProduct.map (cornerVal isIdempotentElem_rankIdem)
        (cornerVal isIdempotentElem_rankIdem)))

theorem inductionLinear_tmul (x : WeightedKLRAlgebra k Γ ν') (y : WeightedKLRAlgebra k Γ ν'') :
    inductionLinear k Γ ν' ν'' (x ⊗ₜ y) = (galleryTensorHom k Γ ν' ν'' (x.1 ⊗ₜ y.1)).1 := rfl

theorem galleryTensorHom_rankIdem :
    (galleryTensorHom k Γ ν' ν'' (rankIdem k Γ ν' ⊗ₜ rankIdem k Γ ν'')).1 =
      splitIdem k Γ ν' ν'' := by
  rw [rankIdem, rankIdem, TensorProduct.sum_tmul, map_sum, corner_val_sum]
  refine Finset.sum_congr rfl fun C' _ => ?_
  rw [TensorProduct.tmul_sum, map_sum, corner_val_sum]
  exact Finset.sum_congr rfl fun C'' _ => galleryTensorHom_e_tmul_e C' C''

theorem inductionLinear_mul (x y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    inductionLinear k Γ ν' ν'' (x * y) =
      inductionLinear k Γ ν' ν'' x * inductionLinear k Γ ν' ν'' y := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [add_mul, map_add, map_add, ha, hb, add_mul]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => rw [mul_add, map_add, map_add, hc, hd, mul_add]
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, inductionLinear_tmul, inductionLinear_tmul,
        inductionLinear_tmul]
      show (galleryTensorHom k Γ ν' ν'' ((a.1 * c.1) ⊗ₜ (b.1 * d.1))).1 = _
      rw [← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
      rfl

theorem inductionLinear_mem (z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    splitIdem k Γ ν' ν'' * inductionLinear k Γ ν' ν'' z = inductionLinear k Γ ν' ν'' z ∧
      inductionLinear k Γ ν' ν'' z * splitIdem k Γ ν' ν'' = inductionLinear k Γ ν' ν'' z := by
  have hone : inductionLinear k Γ ν' ν'' 1 = splitIdem k Γ ν' ν'' := by
    rw [Algebra.TensorProduct.one_def, inductionLinear_tmul]
    exact galleryTensorHom_rankIdem
  rw [← hone, ← inductionLinear_mul, ← inductionLinear_mul, one_mul, mul_one]
  exact ⟨rfl, rfl⟩

theorem inductionLinear_mem_corner
    (z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    inductionLinear k Γ ν' ν'' z ∈ Subsemigroup.corner (rankIdem k Γ (ν' + ν'')) := by
  rw [Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem]
  obtain ⟨h₁, h₂⟩ := inductionLinear_mem z
  refine ⟨?_, ?_⟩
  · rw [← h₁, ← mul_assoc, rankIdem_mul_splitIdem]
  · rw [← h₂, mul_assoc, splitIdem_mul_rankIdem]

variable (k Γ ν' ν'') in
/-- **Webster's map `ι_{ν';ν''} : W_{ν'} ⊗ W_{ν''} → W_{ν'+ν''}`**, juxtaposition of diagrams:
a non-unital algebra map. -/
noncomputable def inductionMap :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₙₐ[k]
      WeightedKLRAlgebra k Γ (ν' + ν'') where
  toFun z := ⟨inductionLinear k Γ ν' ν'' z, inductionLinear_mem_corner z⟩
  map_smul' c z := Subtype.ext (map_smul _ c z)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (inductionLinear_mul a b)

theorem inductionMap_tmul (x : WeightedKLRAlgebra k Γ ν') (y : WeightedKLRAlgebra k Γ ν'') :
    (inductionMap k Γ ν' ν'' (x ⊗ₜ y)).1 = (galleryTensorHom k Γ ν' ν'' (x.1 ⊗ₜ y.1)).1 := rfl

/-- `ι(1 ⊗ 1) = e_{ν';ν''}`. -/
theorem inductionMap_one : (inductionMap k Γ ν' ν'' 1).1 = splitIdem k Γ ν' ν'' := by
  rw [Algebra.TensorProduct.one_def, inductionMap_tmul]
  exact galleryTensorHom_rankIdem

/-- `ι(e C' ⊗ e C'') = e (C' ∘ C'')` for rank-ordered `C'` and `C''`. -/
theorem inductionMap_e_tmul_e {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (hC' : C'.IsRankOrdered) (hC'' : C''.IsRankOrdered) :
    (inductionMap k Γ ν' ν'' (⟨e C', (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
        ⟨by rw [rankIdem_mul_e, ite_eq_left hC'], by rw [e_mul_rankIdem, ite_eq_left hC']⟩⟩ ⊗ₜ
      ⟨e C'', (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
        ⟨by rw [rankIdem_mul_e, ite_eq_left hC''], by rw [e_mul_rankIdem, ite_eq_left hC'']⟩⟩)).1 =
      e (chamber C' C'') :=
  galleryTensorHom_e_tmul_e C' C''

/-! ### Induction and restriction -/

section IndRes

variable (k Γ ν' ν'')

/-- `ι_{ν';ν''}` as a non-unital ring homomorphism, the form used by `InductionAlong`. -/
noncomputable def inductionRingHom :
    WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'' →ₙ+*
      WeightedKLRAlgebra k Γ (ν' + ν'') where
  toFun := inductionMap k Γ ν' ν''
  map_mul' x y := map_mul (inductionMap k Γ ν' ν'') x y
  map_zero' := map_zero (inductionMap k Γ ν' ν'')
  map_add' x y := map_add (inductionMap k Γ ν' ν'') x y

/-- Webster's induction `Ind M ⊠ N = W_{ν'+ν''} ⊗_{W_{ν'} ⊗ W_{ν''}} (M ⊠ N)`: induction along
`ι_{ν';ν''}` of the external tensor product. -/
abbrev ind (M : Type*) [AddCommGroup M] [Module k M] [Module (WeightedKLRAlgebra k Γ ν') M]
    [IsScalarTower k (WeightedKLRAlgebra k Γ ν') M] (N : Type*) [AddCommGroup N] [Module k N]
    [Module (WeightedKLRAlgebra k Γ ν'') N] [IsScalarTower k (WeightedKLRAlgebra k Γ ν'') N] :=
  Categorification.InductionAlong.Ind
    (A := WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (B := WeightedKLRAlgebra k Γ (ν' + ν'')) (Categorification.ExtTensor k M N)
    (inductionRingHom k Γ ν' ν'')

/-- Webster's restriction `Res L = e_{ν';ν''} L`, a module over `W_{ν'} ⊗ W_{ν''}`. -/
abbrev res (L : Type*) [AddCommGroup L] [Module (WeightedKLRAlgebra k Γ (ν' + ν'')) L] :=
  Categorification.InductionAlong.Res
    (A := WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (B := WeightedKLRAlgebra k Γ (ν' + ν'')) (inductionRingHom k Γ ν' ν'') L

end IndRes

end Juxtapose

end Categorification.WeightedKLR
