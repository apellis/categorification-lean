/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Mathlib.RingTheory.Idempotents
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of idempotent pieces of modules

For an algebra `A` over a field `k`, an element `a : A` and an `A`-module `X` that is a
`k`-vector space compatibly, the piece `a X` is a `k`-subspace of `X` (`idemPiece`); its
dimension is `pieceDim k X a`. For a complete family of orthogonal idempotents the dimension of
`X` is the sum of the dimensions of its pieces (`finrank_eq_sum_pieceDim`). Piece dimensions are
invariant under isomorphisms, additive on products and on short exact sequences, and compatible
with restriction along a nonunital map.

This is the bookkeeping of the dimension count `dim Hom(P, -)` for projectives `P = A e` in the
proof of Webster, arXiv:1309.3796v3, Proposition 5.5: `Hom(A e, X) ≅ e X`.
-/

namespace Categorification

open InductionAlong

noncomputable section

variable (k : Type*) [Field k] {A : Type*} [Ring A] [Algebra k A]

section Piece

variable (X : Type*) [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]

/-- Multiplication by `a`, as a `k`-linear map. -/
def smulK (a : A) : X →ₗ[k] X where
  toFun x := a • x
  map_add' := smul_add a
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul A c x, ← algebraMap_smul A c (a • x), smul_smul, smul_smul,
      Algebra.commutes]

theorem smulK_apply (a : A) (x : X) : smulK k X a x = a • x := rfl

/-- The piece `a X` of `X`, as a subspace. -/
def idemPiece (a : A) : Submodule k X := LinearMap.range (smulK k X a)

/-- The dimension of the piece `a X`. -/
def pieceDim (a : A) : ℕ := Module.finrank k (idemPiece k X a)

theorem mem_idemPiece {a : A} {x : X} : x ∈ idemPiece k X a ↔ ∃ y : X, a • y = x :=
  Iff.rfl

theorem mem_idemPiece_iff_of_idem {a : A} (ha : IsIdempotentElem a) {x : X} :
    x ∈ idemPiece k X a ↔ a • x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    change a • a • y = a • y
    rw [smul_smul, ha.eq]
  · intro h
    exact ⟨x, h⟩

theorem finrank_eq_pieceDim_one : Module.finrank k X = pieceDim k X (1 : A) := by
  have : idemPiece k X (1 : A) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact ⟨x, one_smul A x⟩
  rw [pieceDim, this, finrank_top]

end Piece

section Decomposition

variable {X : Type*} [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]

/-- **The dimension of a module is the sum of the dimensions of its idempotent pieces.** -/
theorem finrank_eq_sum_pieceDim {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) [FiniteDimensional k X] :
    Module.finrank k X = ∑ i, pieceDim k X (e i) := by
  let f : X →ₗ[k] ((i : ι) → idemPiece k X (e i)) :=
    LinearMap.pi fun i => (smulK k X (e i)).rangeRestrict
  let g : ((i : ι) → idemPiece k X (e i)) →ₗ[k] X :=
    ∑ i, (idemPiece k X (e i)).subtype ∘ₗ LinearMap.proj i
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have : g (f x) = ∑ i, e i • x := by simp [f, g]; rfl
    rw [this, ← Finset.sum_smul, he.complete, one_smul]
  have hfg : ∀ y, f (g y) = y := by
    intro y
    funext j
    apply Subtype.ext
    have : (f (g y) j : X) = e j • (∑ i, (y i : X)) := by simp [f, g, Finset.smul_sum]; rfl
    rw [this, Finset.smul_sum]
    have hy : ∀ i, e i • (y i : X) = y i := fun i =>
      (mem_idemPiece_iff_of_idem k X (he.idem i)).1 (y i).2
    have hji : ∀ i, e j • (y i : X) = if j = i then (y i : X) else 0 := by
      intro i
      conv_lhs => rw [← hy i]
      rw [smul_smul]
      by_cases h : j = i
      · subst h; rw [(he.idem j).eq, hy]; simp
      · rw [he.ortho h, zero_smul]; simp [h]
    simp_rw [hji]
    simp
  let E : X ≃ₗ[k] ((i : ι) → idemPiece k X (e i)) :=
    { f with invFun := g, left_inv := hgf, right_inv := hfg }
  rw [E.finrank_eq, Module.finrank_pi_fintype]
  rfl

end Decomposition

section Invariance

variable {X Y Z : Type*} [AddCommGroup X] [Module A X] [Module k X] [IsScalarTower k A X]
  [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y]
  [AddCommGroup Z] [Module A Z] [Module k Z] [IsScalarTower k A Z]

/-- An `A`-linear map restricts to the pieces. -/
def pieceMap (f : X →ₗ[A] Y) (a : A) : idemPiece k X a →ₗ[k] idemPiece k Y a where
  toFun x := ⟨f x, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨f y, by rw [smulK_apply, ← map_smul, ← hy]; rfl⟩⟩
  map_add' x y := Subtype.ext (map_add f (x : X) y)
  map_smul' c x := Subtype.ext (by
    change f (c • (x : X)) = c • f x
    rw [← algebraMap_smul A c (x : X), map_smul, algebraMap_smul])

theorem pieceMap_apply (f : X →ₗ[A] Y) (a : A) (x : idemPiece k X a) :
    (pieceMap k f a x : Y) = f x := rfl

/-- Piece dimensions are invariant under isomorphisms. -/
theorem pieceDim_congr (f : X ≃ₗ[A] Y) (a : A) : pieceDim k X a = pieceDim k Y a := by
  let F : idemPiece k X a ≃ₗ[k] idemPiece k Y a :=
    { pieceMap k f.toLinearMap a with
      invFun := pieceMap k f.symm.toLinearMap a
      left_inv := fun x => Subtype.ext (f.symm_apply_apply (x : X))
      right_inv := fun x => Subtype.ext (f.apply_symm_apply (x : Y)) }
  exact F.finrank_eq

/-- Piece dimensions are additive on products. -/
theorem pieceDim_prod (a : A) [FiniteDimensional k X] [FiniteDimensional k Y] :
    pieceDim k (X × Y) a = pieceDim k X a + pieceDim k Y a := by
  let F : idemPiece k (X × Y) a ≃ₗ[k] idemPiece k X a × idemPiece k Y a :=
    { toFun := fun x => (⟨(x : X × Y).1, by
          obtain ⟨y, hy⟩ := x.2
          exact ⟨y.1, congrArg Prod.fst hy⟩⟩,
        ⟨(x : X × Y).2, by
          obtain ⟨y, hy⟩ := x.2
          exact ⟨y.2, congrArg Prod.snd hy⟩⟩)
      invFun := fun x => ⟨((x.1 : X), (x.2 : Y)), by
        obtain ⟨y, hy⟩ := x.1.2
        obtain ⟨z, hz⟩ := x.2.2
        exact ⟨(y, z), Prod.ext hy hz⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  rw [pieceDim, F.finrank_eq, Module.finrank_prod]
  rfl

/-- Piece dimensions of a finite power. -/
theorem pieceDim_pi (a : A) (n : ℕ) [FiniteDimensional k X] :
    pieceDim k (Fin n → X) a = n * pieceDim k X a := by
  let F : idemPiece k (Fin n → X) a ≃ₗ[k] (Fin n → idemPiece k X a) :=
    { toFun := fun x j => ⟨(x : Fin n → X) j, by
          obtain ⟨y, hy⟩ := x.2
          exact ⟨y j, congrFun hy j⟩⟩
      invFun := fun x => ⟨fun j => (x j : X), by
        choose y hy using fun j => (x j).2
        exact ⟨y, funext hy⟩⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  rw [pieceDim, F.finrank_eq, Module.finrank_pi_fintype]
  simp [pieceDim]

/-- **Piece dimensions are additive on short exact sequences.** -/
theorem pieceDim_of_exact {a : A} (ha : IsIdempotentElem a) (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [FiniteDimensional k Y] :
    pieceDim k Y a = pieceDim k X a + pieceDim k Z a := by
  let gr := pieceMap k g a
  let fr := pieceMap k f a
  have hgr : Function.Surjective gr := by
    rintro ⟨z, z', rfl⟩
    obtain ⟨y, rfl⟩ := hg z'
    exact ⟨⟨a • y, y, rfl⟩, Subtype.ext (g.map_smul a y)⟩
  have hfr : Function.Injective fr := fun x y h =>
    Subtype.ext (hf (congrArg (fun z : idemPiece k Y a => (z : Y)) h))
  have hker : LinearMap.ker gr = LinearMap.range fr := by
    ext y
    constructor
    · intro hy
      have hy' : g (y : Y) = 0 := congrArg (fun z : idemPiece k Z a => (z : Z)) hy
      obtain ⟨x, hx⟩ := (hfg (y : Y)).1 hy'
      have hya : a • (y : Y) = y := (mem_idemPiece_iff_of_idem k Y ha).1 y.2
      refine ⟨⟨a • x, x, rfl⟩, Subtype.ext ?_⟩
      change f (a • x) = (y : Y)
      rw [map_smul, hx, hya]
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      change g (f (x : X)) = 0
      exact (hfg _).2 ⟨_, rfl⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker gr
  rw [LinearMap.range_eq_top.2 hgr, finrank_top, hker, LinearMap.finrank_range_of_inj hfr] at h1
  rw [pieceDim, pieceDim, pieceDim, ← h1, add_comm]

end Invariance

section Restriction

variable {B : Type*} [Ring B] [Algebra k B] (φ : A →ₙₐ[k] B) (M : Type*) [AddCommGroup M]
  [Module B M] [Module k M] [IsScalarTower k B M]
  [Module k (Res (φ : A →ₙ+* B) M)] [IsScalarTower k A (Res (φ : A →ₙ+* B) M)]

/-- **Pieces of a restriction**: `a (Res φ M) ≅ φ(a) M`. -/
theorem pieceDim_res (a : A) :
    pieceDim k (Res (φ : A →ₙ+* B) M) a = pieceDim k M (φ a) := by
  have h1 : ∀ x : M, φ 1 • φ a • x = φ a • x := fun x => by
    rw [smul_smul, ← map_mul, one_mul]
  have hval : ∀ (c : k) (x : Res (φ : A →ₙ+* B) M), (c • x).val = c • x.val := by
    intro c x
    rw [← algebraMap_smul A c x, Res.val_smul, ← algebraMap_smul B c x.val]
    change φ (algebraMap k A c) • x.val = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc, Algebra.algebraMap_eq_smul_one,
      smul_assoc, one_smul]
    congr 1
    exact x.prop
  let F : idemPiece k (Res (φ : A →ₙ+* B) M) a ≃ₗ[k] idemPiece k M (φ a) :=
    { toFun := fun x => ⟨(x : Res (φ : A →ₙ+* B) M).val, by
          obtain ⟨y, hy⟩ := x.2
          exact ⟨y.val, (Res.val_smul a y).symm.trans (congrArg Res.val hy)⟩⟩
      invFun := fun x => ⟨Res.mk (x : M) (by
          obtain ⟨y, hy⟩ := x.2
          change φ 1 • (x : M) = _
          rw [← hy]; exact h1 y), by
        obtain ⟨y, hy⟩ := x.2
        have h11 : (φ 1 * φ 1 : B) = φ 1 := by rw [← map_mul, one_mul]
        have ha1 : (φ a * φ 1 : B) = φ a := by rw [← map_mul, mul_one]
        refine ⟨Res.mk (φ 1 • y) (by
          change φ 1 • φ 1 • y = φ 1 • y
          rw [smul_smul, h11]), Res.ext ?_⟩
        change φ a • φ 1 • y = _
        rw [smul_smul, ha1]
        exact hy⟩
      left_inv := fun x => Subtype.ext (Res.ext rfl)
      right_inv := fun x => rfl
      map_add' := fun x y => rfl
      map_smul' := fun c x => Subtype.ext (hval c x) }
  exact F.finrank_eq

end Restriction

end

end Categorification
