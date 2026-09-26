/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.KaroubiTransfer
import Categorification.Diagrams.KL3.K0UDot
import Categorification.Diagrams.KL3.IdempotentLift
import Categorification.Algebra.Graded.KrullSchmidt

/-!
# From `K₀` of a graded algebra to `K₀(U̇)`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4, end
of the proof of Theorem 1.1: "the idempotent `e_{r,r'}` is the image of `e_r ⊗ e_{r'} ⊗ 1` in
`R(ν) ⊗ R(ν') ⊗ Π_λ`, and the Grothendieck group of the latter is isomorphic to
`_𝒜f(ν) ⊗ _𝒜f(ν')`. Therefore `[E_{ν,-ν'}, e_{r,r'}]` is in the image of `_𝒜f(ν) ⊗ _𝒜f(ν')`".

Let `D` be transfer data (`Categorification.Diagrams.KL3.KaroubiTransfer`) for a graded algebra
`A` over a field with a graded dimension, acting on 1-morphisms `x_i` of `U̇(l, m)`. We construct
an additive map `Φ = transferK0 D : K₀(A) → K₀(U̇(l, m))` with

* `transferK0_ofIdempotent`: `Φ[A f] = [(x_i {0}, α(f))]` for every degree-zero idempotent
  `f ∈ eι i · A` (`TCorner`);
* `transferK0_smul`: `Φ(c x) = c̄ Φ(x)`, where `c ↦ c̄` is the involution `q ↦ q⁻¹` of `ℤ[q, q⁻¹]`
  (graded projective modules and 1-morphisms of `U̇` are shifted in opposite directions by
  equivalences of idempotents).

`Φ` is defined on the basis of indecomposable projectives (`Graded.K0.indecBasis`): the class of
`P_b` goes to the class of `(x_i {s}, α(f))` for a chosen idempotent `f` with `A f ≅ P_b {s}`;
the choice does not matter because equivalent idempotents give isomorphic 1-morphisms (`tIso`).
-/

noncomputable section

namespace Categorification.GradedBicat

open CategoryTheory CategoryTheory.Limits StringDiagrams Presentation KLR.Diagram Graded
open LaurentPolynomial

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {k : Type w} [Field k] {P : Presentation.{w, v} S k}
  {deg : S.Gen → ℤ} {l m : P.Bicat}

variable {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [HasGdim 𝒜]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {x : ι → Bicat.Hom l m} {eι : ι → A}
  (D : TransferData (deg := deg) 𝒜 x eι)

/-- Representing data for an indecomposable class: an idempotent `f` in a corner with
`A f ≅ P_b {s}`. -/
structure RepData (b : GProj.IndecClass 𝒜) where
  /-- The corner. -/
  i : ι
  /-- The idempotent. -/
  F : TCorner 𝒜 eι i
  /-- The shift. -/
  s : ℤ
  iso : Nonempty ((GProj.ofIdempotent F.f (show IsIdempotentElem F.f from F.idem) F.deg0).Iso
    (b.rep.shift s))

open Classical in
/-- The image of the class of `P_b`. -/
def transferVal (b : GProj.IndecClass 𝒜) : K0U P deg l m :=
  if h : Nonempty (RepData (𝒜 := 𝒜) (eι := eι) b) then
    (T h.some.s : LaurentPolynomial ℤ) • K0U.cl (tobj D h.some.F 0)
  else 0

/-- **The additive map `K₀(A) → K₀(U̇(l, m))`.** -/
def transferK0 : K0 𝒜 →+ K0U P deg l m where
  toFun y := ((K0.indecBasis 𝒜).repr y).sum fun b c => invert c • transferVal D b
  map_zero' := by simp
  map_add' y y' := by
    rw [map_add, Finsupp.sum_add_index']
    · intro b; simp
    · intro b c c'; rw [map_add, add_smul]

theorem transferK0_apply (y : K0 𝒜) :
    transferK0 D y = ((K0.indecBasis 𝒜).repr y).sum fun b c => invert c • transferVal D b := rfl

theorem transferK0_smul (c : LaurentPolynomial ℤ) (y : K0 𝒜) :
    transferK0 D (c • y) = invert c • transferK0 D y := by
  rw [transferK0_apply, transferK0_apply, map_smul, Finsupp.sum_smul_index',
    Finsupp.smul_sum]
  · refine Finsupp.sum_congr fun b _ => ?_
    rw [smul_eq_mul, map_mul, mul_smul]
  · intro b; simp

theorem transferK0_basis (b : GProj.IndecClass 𝒜) (s : ℤ) :
    transferK0 D ((T s : LaurentPolynomial ℤ) • K0.of b.rep) =
      (T (-s) : LaurentPolynomial ℤ) • transferVal D b := by
  rw [transferK0_smul, ← K0.indecBasis_apply, transferK0_apply, Basis.repr_self,
    Finsupp.sum_single_index (by simp), map_one, one_smul, invert_T]

omit [HasGdim 𝒜] in
theorem ofIdempotent_congr {f f' : A} (h : f = f') (hf : IsIdempotentElem f) (hf0 : f ∈ 𝒜 0)
    (hf' : IsIdempotentElem f') (hf0' : f' ∈ 𝒜 0) :
    K0.of (GProj.ofIdempotent f hf hf0) = K0.of (GProj.ofIdempotent f' hf' hf0') := by
  subst h; rfl

variable [HasFiniteBiproducts (UDotHom P deg l m)] [SetLike.GradedMonoid 𝒜]

omit [HasFiniteBiproducts (UDotHom P deg l m)] in
/-- **`Φ[A f] = [(x_i {0}, α(f))]` for an indecomposable `A f`.** -/
theorem transferK0_ofIdempotent_indec {i : ι} (G : TCorner 𝒜 eι i)
    (hind : (GProj.ofIdempotent G.f (show IsIdempotentElem G.f from G.idem) G.deg0).IsIndec A) :
    transferK0 D (K0.of (GProj.ofIdempotent G.f (show IsIdempotentElem G.f from G.idem) G.deg0)) =
      K0U.cl (tobj D G 0) := by
  classical
  obtain ⟨b, s, ⟨φ⟩⟩ := GProj.IndecClass.exists_iso_rep_shift hind
  have hne : Nonempty (RepData (𝒜 := 𝒜) (eι := eι) b) := ⟨⟨i, G, s, ⟨φ⟩⟩⟩
  rw [K0.of_eq_of_iso φ, ← K0.T_smul_of, transferK0_basis, transferVal, dif_pos hne]
  set R := hne.some
  obtain ⟨φ'⟩ := R.iso
  -- `A G.f ≅ (A R.F.f){s - R.s}`
  have ψ : (GProj.ofIdempotent G.f (show IsIdempotentElem G.f from G.idem) G.deg0).Iso
      ((GProj.ofIdempotent R.F.f (show IsIdempotentElem R.F.f from R.F.idem) R.F.deg0).shift
        (s - R.s)) :=
    (φ.trans ((GradedEquiv.ofEq (show (b.rep.shift s).grading =
        (b.rep.shift (R.s + (s - R.s))).grading by rw [add_sub_cancel])).trans
      (GMod.shiftShiftIso b.rep.toGMod R.s (s - R.s)).symm)).trans (φ'.symm.shift (s - R.s))
  obtain ⟨a, c, ha, hc, hpair⟩ := GProj.Iso.exists_isEquivPair ψ
  have e := tIso (D := D) G R.F hpair ha (by rwa [neg_neg]) 0
  show _ = SplitK0.of (tobj D G 0)
  rw [SplitK0.of_iso e, zero_add]
  show _ = K0U.cl (idemObj _ _ _ _ _)
  rw [K0U.idemObj_shift (t := -(s - R.s)), smul_smul, ← T_add]
  congr 2
  ring

/-- **`Φ[A f] = [(x_i {0}, α(f))]`** for every degree-zero idempotent `f ∈ eι i · A`. -/
theorem transferK0_ofIdempotent {i : ι} (F : TCorner 𝒜 eι i) :
    transferK0 D (K0.of (GProj.ofIdempotent F.f (show IsIdempotentElem F.f from F.idem) F.deg0)) =
      K0U.cl (tobj D F 0) := by
  classical
  obtain ⟨M, g, hg, hind, horth, hsum⟩ := Graded.exists_indec_decomp (𝒜 := 𝒜)
    (Module.finrank k (Graded.cornerZero (𝒜 := 𝒜) F.f) + 1) F.f F.idem F.deg0 (Nat.lt_succ_self _)
  let G : Fin M → TCorner 𝒜 eι i := fun j =>
    ⟨g j, (hg j).deg0, (hg j).idem.eq, by rw [← (hg j).left, ← mul_assoc, F.left]⟩
  have horth' : OrthogonalIdempotents g := ⟨fun j => (hg j).idem, fun j j' h => horth j j' h⟩
  have h1 := K0.of_ofIdempotent_sum horth' (fun j => (hg j).deg0) Finset.univ
  rw [ofIdempotent_congr hsum.symm F.idem F.deg0 horth'.isIdempotentElem_sum
    (Submodule.sum_mem _ fun j _ => (hg j).deg0), h1, map_sum]
  have e := tOrthIso (D := D) F G hsum (fun j j' h => horth j j' h) 0
  show _ = SplitK0.of (tobj D F 0)
  rw [SplitK0.of_iso e, SplitK0.of_biproduct]
  exact Finset.sum_congr rfl fun j _ => transferK0_ofIdempotent_indec D (G j) (hind j)

end Categorification.GradedBicat
