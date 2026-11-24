/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Loading traces in a right projective

Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3. A ring-theoretic interface
for identifying the unique simple quotient of a loading projective with
the quotient by a family of smaller loading projectives.
-/

namespace Categorification.Stendhal

open MulOpposite

variable {A : Type*} [Ring A] {e : A}

/-- The images in `eA` of maps from right projectives at the specified cuts.
A generator is the value of such a map on its generating idempotent. -/
def coevaluationTrace {J : Type*} (cut : J → A) : Submodule Aᵐᵒᵖ (rIdeal e) :=
  Submodule.span Aᵐᵒᵖ {x | ∃ j, x.val * cut j = x.val}

/-- Every trace generator is the image of the corresponding idempotent, and
every image from a cut projective belongs to the trace. -/
theorem coevaluationTrace_eq_iSup_range {J : Type*} (cut : J → A)
    (hcut : ∀ j, IsIdempotentElem (cut j)) :
    coevaluationTrace (e := e) cut =
      ⨆ j, ⨆ f : rIdeal (cut j) →ₗ[Aᵐᵒᵖ] rIdeal e, LinearMap.range f := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, hx⟩
    let f : rIdeal (cut j) →ₗ[Aᵐᵒᵖ] rIdeal e :=
      { toFun y := op y.val • x
        map_add' y z := add_smul (op y.val) (op z.val) x
        map_smul' b y := by
          apply Subtype.ext
          change x.val * (y.val * b.unop) = (x.val * y.val) * b.unop
          rw [mul_assoc] }
    exact (le_iSup (fun j => ⨆ f : rIdeal (cut j) →ₗ[Aᵐᵒᵖ] rIdeal e, LinearMap.range f) j)
      ((le_iSup (fun f : rIdeal (cut j) →ₗ[Aᵐᵒᵖ] rIdeal e => LinearMap.range f) f)
        ⟨⟨cut j, (hcut j).eq⟩, Subtype.ext hx⟩)
  · refine iSup_le fun j => iSup_le fun f => ?_
    rintro _ ⟨y, rfl⟩
    let g : rIdeal (cut j) := ⟨cut j, (hcut j).eq⟩
    have hg : op (cut j) • g = g := Subtype.ext (hcut j).eq
    have hg' : (f g).val * cut j = (f g).val := by
      exact congrArg Subtype.val ((f.map_smul (op (cut j)) g).symm.trans (congrArg f hg))
    have hy : op y.val • g = y := Subtype.ext y.property
    rw [← hy, f.map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hg'⟩)

/-- A character supported at the chosen loading kills the trace of all cuts
on which it vanishes. -/
theorem coevaluationTrace_le_characterKernel {J F : Type*} [Ring F]
    (cut : J → A) (χ : A →+* F) (hcut : ∀ j, χ (cut j) = 0) :
    coevaluationTrace (e := e) cut ≤
      { carrier := {x | χ x.val = 0}
        zero_mem' := map_zero χ
        add_mem' := by
          intro x y hx hy
          change χ x.val = 0 at hx
          change χ y.val = 0 at hy
          change χ (x.val + y.val) = 0
          rw [map_add, hx, hy, add_zero]
        smul_mem' := fun a x hx => by
          change χ (x.val * a.unop) = 0
          rw [map_mul, hx, zero_mul] } := by
  apply Submodule.span_le.mpr
  rintro x ⟨j, h⟩
  change χ x.val = 0
  rw [← h, map_mul, hcut j, mul_zero]

/-- The trace criterion for Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3.
The diagrammatic inputs are that character-zero vectors are in the cut trace
and that any character-nonzero vector can be completed to the generating
idempotent. The latter can be checked in the corner by multiplying on the
right first by the loading idempotent and then by a corner inverse. -/
theorem coevaluationTrace_eq_iff_simpleQuotient {J F : Type*} [Ring F] [Nontrivial F]
    (he : IsIdempotentElem e) (cut : J → A) (χ : A →+* F)
    (heχ : χ e = 1) (hcut : ∀ j, χ (cut j) = 0)
    (hzero : ∀ x : rIdeal e, χ x.val = 0 → x ∈ coevaluationTrace cut)
    (hunit : ∀ x : rIdeal e, χ x.val ≠ 0 → ∃ b : A, x.val * b = e)
    (N : Submodule Aᵐᵒᵖ (rIdeal e)) :
    N = coevaluationTrace cut ↔ IsSimpleModule Aᵐᵒᵖ (rIdeal e ⧸ N) := by
  let g : rIdeal e := ⟨e, he.eq⟩
  have hproper : coevaluationTrace (e := e) cut ≠ ⊤ := by
    intro h
    have hg : g ∈ coevaluationTrace cut := h ▸ Submodule.mem_top
    have hzero' : χ e = 0 := coevaluationTrace_le_characterKernel cut χ hcut hg
    exact one_ne_zero (heχ.symm.trans hzero')
  have hle (P : Submodule Aᵐᵒᵖ (rIdeal e)) (hp : P ≠ ⊤) : P ≤ coevaluationTrace cut := by
    intro x hx
    apply hzero
    by_contra hχ
    obtain ⟨b, hb⟩ := hunit x hχ
    have hg : g ∈ P := by
      have hb' : op b • x = g := Subtype.ext hb
      exact hb' ▸ P.smul_mem (op b) hx
    apply hp (eq_top_iff.mpr ?_)
    intro y _
    have hy : op y.val • g = y := Subtype.ext y.property
    exact hy ▸ P.smul_mem (op y.val) hg
  rw [isSimpleModule_iff_isCoatom, isCoatom_iff_ge_of_le]
  constructor
  · rintro rfl
    exact ⟨hproper, fun P hp _ => hle P hp⟩
  · rintro ⟨hn, hmax⟩
    exact le_antisymm (hle N hn) (hmax _ hproper (hle N hn))

section Bigon

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "ϕ" => tensorOfKLR Q Λ ν

/-- The mixed bigon factors the terminal dot power through the loading with
one more black strand to the left of the marked red. At red multiplicity one
it therefore kills a single terminal dot in the cut-trace quotient of
Webster, arXiv:1309.3796v2, §7.1, Lemma 7.3. -/
theorem bigon_mem_coevaluationTrace {J : Type*} (cut : J → T)
    (s : Seq μ) (p : ℕ) (hp : p + 1 < Multiset.card μ) (i : I) (r : Fin ℓ)
    (hr : s.lbl ⟨p, by omega⟩ = .inr r) (hi : s.lbl ⟨p + 1, hp⟩ = .inl i)
    (j : J) (hj : cut j = ϕ (KLRAlgebra.e (sadj (Multiset.card μ) p • s))) :
    ∃ z : rIdeal (ϕ (KLRAlgebra.e s)), z ∈ coevaluationTrace cut ∧
      z.val = ϕ (KLRAlgebra.x (Q := stendhalQ Q Λ) ⟨p + 1, hp⟩ ^ Λ r i * KLRAlgebra.e s) := by
  let a := (KLRAlgebra.ψ p : KLRAlgebra k (stendhalQ Q Λ) μ)
  let f := (KLRAlgebra.e s : KLRAlgebra k (stendhalQ Q Λ) μ)
  let g := (KLRAlgebra.e (sadj (Multiset.card μ) p • s) :
    KLRAlgebra k (stendhalQ Q Λ) μ)
  have hfg : f * a = a * g := KLRAlgebra.e_mul_ψ p s
  have hMul (u v : KLRAlgebra k (stendhalQ Q Λ) μ) : ϕ (u * v) = ϕ u * ϕ v := by
    simp only [tensorOfKLR, map_mul]
  have hleft : ϕ f * ϕ (f * a) = ϕ (f * a) := by
    rw [← hMul]
    rw [← mul_assoc, KLRAlgebra.e_mul_self]
  let v : rIdeal (ϕ f) := ⟨ϕ (f * a), hleft⟩
  have hvg : v.val * cut j = v.val := by
    rw [hj]
    change ϕ (f * a) * ϕ g = _
    rw [← hMul]
    rw [hfg, mul_assoc, KLRAlgebra.e_mul_self]
    exact congrArg (fun u => ϕ u) hfg.symm
  refine ⟨op (ϕ a) • v, Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hvg⟩), ?_⟩
  change ϕ (f * a) * ϕ a = _
  rw [← hMul]
  rw [mul_assoc, KLRAlgebra.e_mul_ψ_mul_ψ]
  apply congrArg (fun u => ϕ u)
  have hb := KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) p hp s
  rw [hr, hi] at hb
  simp only [reduceCtorEq, ↓reduceIte] at hb
  have hv : (![KLRAlgebra.x ⟨p, by omega⟩, KLRAlgebra.x ⟨p + 1, hp⟩] :
      Fin 2 → KLRAlgebra k (stendhalQ Q Λ) μ) =
      fun q => KLRAlgebra.x (![⟨p, by omega⟩, ⟨p + 1, hp⟩] q) := by
    funext q
    fin_cases q <;> rfl
  rw [stendhalQ_inr_inl, hv, KLRAlgebra.ncEval_eq_pol] at hb
  simp only [map_pow, MvPolynomial.rename_X, KLRAlgebra.pol_X] at hb
  exact hb

end Bigon

end Categorification.Stendhal
