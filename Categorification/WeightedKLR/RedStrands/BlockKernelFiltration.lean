/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelTensor
import Categorification.Algebra.IdempotentTraceFiltration

/-!
# Higher loading generators of the partial standard kernel

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21).
The kernel in the ordered loading projective is spanned over the ordered algebra
by diagrams cut through strictly higher retained-boundary loading idempotents.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun s : KLR.Seq μ => mk (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation "E" => fun κ => mk (redProj k Q Λ ν κ)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν

variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)

local notation "T" => IsIdempotentElem.Corner (ord (redWord t))
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)

/-- The projective kernel is the right span of its cuts at higher retained-boundary
loadings. The red order is held fixed at the cut. -/
theorem blockLoadingKernel_eq_span :
    K = Submodule.span Tᵐᵒᵖ {x : P | ∃ u : Seq μ, redWord u = redWord t ∧
      adjacentBlockRoot a b t < adjacentBlockRoot a b u ∧ ∃ z : V,
        x = blockLoadingRep Q Λ t (z * p u)} := by
  let G : Submodule Tᵐᵒᵖ P := Submodule.span Tᵐᵒᵖ {x : P | ∃ u : Seq μ,
    redWord u = redWord t ∧ adjacentBlockRoot a b t < adjacentBlockRoot a b u ∧
    ∃ z : V, x = blockLoadingRep Q Λ t (z * p u)}
  change K = G
  have hgen (u : Seq μ) (hu : redWord u = redWord t)
      (hh : adjacentBlockRoot a b t < adjacentBlockRoot a b u) :
      p u ∈ J := TwoSidedIdeal.subset_span ⟨u, hu, hh, rfl⟩
  apply le_antisymm
  · intro x hx
    change x.1.1 ∈ J at hx
    rw [← blockLoadingRep_self Q Λ t x]
    have step (v : V) (hv : v ∈ J) :
        ∀ z w : V, blockLoadingRep Q Λ t (z * v * w) ∈ G := by
      induction hv using TwoSidedIdeal.span_induction with
      | mem s hs =>
        obtain ⟨u, hu, hh, rfl⟩ := hs
        intro z w
        let d : T := ⟨E (redWord t) * w * E (redWord t), w, rfl⟩
        have hE : p u * E (redWord t) = p u := by
          rw [← map_mul, e_mul_redProj, ite_eq_left hu]
        have hcut : blockLoadingRep Q Λ t (z * p u * w) =
            op d • blockLoadingRep Q Λ t (z * p u) := by
          apply Subtype.ext; apply Subtype.ext
          change (blockLoadingRep Q Λ t (z * p u * w)).1.1 =
            (blockLoadingRep Q Λ t (z * p u)).1.1 * d.1
          calc
            _ = p t * (z * ((p u * E (redWord t)) * E (redWord t)) * w) * E (redWord t) := by
              rw [blockLoadingRep_val, hE, hE]
            _ = _ := by simp only [blockLoadingRep_val, d, mul_assoc]
        change blockLoadingRep Q Λ t (z * p u * w) ∈ G
        rw [hcut]
        exact G.smul_mem _ (Submodule.subset_span ⟨u, hu, hh, z, rfl⟩)
      | zero =>
        intro z w
        have hz : blockLoadingRep Q Λ t (0 : V) = 0 := by
          apply Subtype.ext; apply Subtype.ext
          rw [blockLoadingRep_val, mul_zero, zero_mul]
          rfl
        simpa only [mul_zero, zero_mul, hz] using G.zero_mem
      | add x y _ _ hx hy =>
        intro z w
        have hadd : blockLoadingRep Q Λ t (z * (x+y) * w) =
            blockLoadingRep Q Λ t (z*x*w) + blockLoadingRep Q Λ t (z*y*w) := by
          apply Subtype.ext; apply Subtype.ext
          change _ = (blockLoadingRep Q Λ t (z*x*w)).1.1 +
            (blockLoadingRep Q Λ t (z*y*w)).1.1
          simp only [blockLoadingRep_val, mul_add, add_mul]
        rw [hadd]
        exact G.add_mem (hx z w) (hy z w)
      | neg x _ hx =>
        intro z w
        have hneg : blockLoadingRep Q Λ t (z * (-x) * w) =
            -blockLoadingRep Q Λ t (z*x*w) := by
          apply Subtype.ext; apply Subtype.ext
          change _ = -(blockLoadingRep Q Λ t (z*x*w)).1.1
          simp only [blockLoadingRep_val, mul_neg, neg_mul]
        rw [hneg]
        exact @Submodule.neg_mem Tᵐᵒᵖ P _ (Submodule.addCommGroup (rIdeal (orderedLoadingIdem Q Λ t))) (Submodule.module (rIdeal (orderedLoadingIdem Q Λ t))) G _ (hx z w)
      | left_absorb z x _ hx =>
        intro u w
        simpa only [mul_assoc] using hx (u*z) w
      | right_absorb z x _ hx =>
        intro u w
        simpa only [mul_assoc] using hx u (z*w)
    simpa only [one_mul, mul_one] using step x.1.1 hx 1 1
  · apply Submodule.span_le.2
    rintro _ ⟨u, hu, hh, z, rfl⟩
    change (blockLoadingRep Q Λ t (z * p u)).1.1 ∈ J
    rw [blockLoadingRep_val]
    exact TwoSidedIdeal.mul_mem_right J _ _ (TwoSidedIdeal.mul_mem_left J _ _ (TwoSidedIdeal.mul_mem_left J _ _ (hgen u hu hh)))

/-- A higher loading projected to the same ordered corner as the source. -/
private def higherLoadingIdempotent (u : Seq μ) (hu : redWord u = redWord t) : T :=
  ⟨p u, (Subsemigroup.mem_corner_iff (ord (redWord t))).2
    ⟨by rw [← map_mul, redProj_mul_e, ite_eq_left hu],
     by rw [← map_mul, e_mul_redProj, ite_eq_left hu]⟩⟩

/-- The higher loading idempotents for the retained block boundary order. -/
def higherBlockLoadingIdempotents : Set Tᵐᵒᵖ :=
  {e | ∃ (u : Seq μ) (hu : redWord u = redWord t),
    adjacentBlockRoot a b t < adjacentBlockRoot a b u ∧
      e = op (higherLoadingIdempotent Q Λ t u hu)}

theorem higherBlockLoadingIdempotents_idempotent
    (e : Tᵐᵒᵖ) (he : e ∈ higherBlockLoadingIdempotents Q Λ t a b) :
    IsIdempotentElem e := by
  obtain ⟨u, hu, hh, rfl⟩ := he
  change op (higherLoadingIdempotent Q Λ t u hu * higherLoadingIdempotent Q Λ t u hu) =
    op (higherLoadingIdempotent Q Λ t u hu)
  congr 1
  apply Subtype.ext
  change p u * p u = p u
  rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_self]

/-- The partial standard kernel is the trace of the higher loading idempotents
on the source projective. -/
theorem blockLoadingKernel_eq_idempotentTrace :
    K = ModuleFiltration.idempotentTrace (higherBlockLoadingIdempotents Q Λ t a b)
      (ModuleCat.of Tᵐᵒᵖ P) := by
  rw [blockLoadingKernel_eq_span, ModuleFiltration.idempotentTrace]
  have cut (u : Seq μ) (hu : redWord u = redWord t) (z : V) :
      op (higherLoadingIdempotent Q Λ t u hu) • blockLoadingRep Q Λ t z =
        blockLoadingRep Q Λ t (z * p u) := by
    have hr : p u * E (redWord t) = p u := by
      rw [← map_mul, e_mul_redProj, ite_eq_left hu]
    have hl : E (redWord t) * p u = p u := by
      rw [← map_mul, redProj_mul_e, ite_eq_left hu]
    apply Subtype.ext; apply Subtype.ext
    change (blockLoadingRep Q Λ t z).1.1 * p u =
      (blockLoadingRep Q Λ t (z * p u)).1.1
    calc
      _ = p t * z * (E (redWord t) * p u) := by rw [blockLoadingRep_val, mul_assoc]
      _ = p t * z * (p u * E (redWord t)) := by rw [hl, hr]
      _ = _ := by simp only [blockLoadingRep_val, mul_assoc]
  congr 1
  ext x
  constructor
  · rintro ⟨u, hu, hh, z, rfl⟩
    exact ⟨_, ⟨u, hu, hh, rfl⟩, _, (cut u hu z).symm⟩
  · rintro ⟨_, ⟨u, hu, hh, rfl⟩, y, rfl⟩
    exact ⟨u, hu, hh, y.1.1, by rw [← cut u hu, blockLoadingRep_self]⟩

/-- The higher tail in a filtration separated by the retained boundary cuts
gives a filtration of the kernel in (6.21). The existence of a filtration
with this separation is an additional hypothesis. -/
theorem blockLoadingKernel_hasFiltration
    {ι : Type*} {L : ι → ModuleCat.{max u v} Tᵐᵒᵖ} {m n : List ι}
    (h : ModuleFiltration.HasFiltration L (m ++ n) (ModuleCat.of Tᵐᵒᵖ P))
    (hkill : ∀ c ∈ m, ∀ e ∈ higherBlockLoadingIdempotents Q Λ t a b,
      ∀ x : L c, e • x = 0)
    (hgen : ∀ c ∈ n, ModuleFiltration.idempotentTrace
      (higherBlockLoadingIdempotents Q Λ t a b) (L c) = ⊤) :
    ModuleFiltration.HasFiltration L n (ModuleCat.of Tᵐᵒᵖ K) := by
  have htrace := h.idempotentTrace (higherBlockLoadingIdempotents Q Λ t a b)
    (higherBlockLoadingIdempotents_idempotent Q Λ t a b) hkill hgen
  exact htrace.of_equiv (LinearEquiv.ofEq _ _ (blockLoadingKernel_eq_idempotentTrace Q Λ t a b).symm)

end Categorification.Stendhal.BraidedStendhalAlgebra
