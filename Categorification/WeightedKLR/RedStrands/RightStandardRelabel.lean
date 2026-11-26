/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightStandardReflection
import Categorification.WeightedKLR.RedStrands.GradedBraidingBimodule

/-!
# Relabelling the red strands of a standard module

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10. For a permutation `σ`
of the red labels, relabelling the red strands (`violRedPermEquiv`, `λ'_r = λ_{σ r}`) carries
the standard module `e(s) T^{λ ∘ σ} / U_s` at a loading `s` of the red order `κ` to the
standard module `e(σ s) V / U_{σ s}` at the relabelled loading, of red order `σ ∘ κ`
(`loadingStandardRelabel`). It intertwines the right actions of the corners through the
relabelling of corners (`loadingStandardRelabel_smul`), so the right `T^{λ ∘ σ}`-action on the
right standard module becomes right multiplication by `permCornerMap`
(`rightStandardRelabel_smul`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (σ : Perm (Fin ℓ))

local notation "μ" => stendhalWeight ℓ ν
local notation "f" => violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ
  (fun _ => rfl)
local notation "C'" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)

theorem violRedPermEquiv_e (s : Seq μ) :
    f (violMk k Q (Λ ∘ σ) ν (ofKLR k Q (Λ ∘ σ) ν (KLRAlgebra.e s))) =
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (Seq.redPerm σ s))) :=
  (violRedPermEquiv_violMk σ (fun _ => rfl) _).trans
    (congrArg (violMk k Q Λ ν) (redPermAlgEquiv_e σ (fun _ => rfl) s))

theorem violRedPermEquiv_redProj (κ : List (Fin ℓ)) :
    f (violMk k Q (Λ ∘ σ) ν (redProj k Q (Λ ∘ σ) ν κ)) =
      violMk k Q Λ ν (redProj k Q Λ ν (κ.map σ)) :=
  (violRedPermEquiv_violMk σ (fun _ => rfl) _).trans
    (congrArg (violMk k Q Λ ν) (redPermAlgEquiv_redProj σ (fun _ => rfl) κ))

theorem stendhalLT_redPerm_iff' (s t : Seq μ) :
    StendhalLT (Seq.redPerm σ s) (Seq.redPerm σ t) ↔ StendhalLT s t := by
  have hc (x : Seq μ) (r : Fin ℓ) (i : I) :
      blackCount (Seq.redPerm σ x) (σ r) i = blackCount x r i := by
    have hl (a : Fin (Multiset.card μ)) :
        (Seq.redPerm σ x).lbl a = .inl i ↔ x.lbl a = .inl i := by
      cases ha : x.lbl a <;> simp [ha]
    have hr (a : Fin (Multiset.card μ)) :
        (Seq.redPerm σ x).lbl a = .inr (σ r) ↔ x.lbl a = .inr r := by
      cases ha : x.lbl a <;> simp [ha, σ.injective.eq_iff]
    simp only [blackCount, hl, hr]
  have hle (x y : Seq μ) : StendhalLE (Seq.redPerm σ x) (Seq.redPerm σ y) ↔ StendhalLE x y := by
    constructor
    · intro h r i
      simpa only [hc] using h (σ r) i
    · intro h r i
      obtain ⟨r, rfl⟩ := σ.surjective r
      simpa only [hc] using h r i
  simp only [StendhalLT, hle]

/-- Relabelling the red strands matches the ideals of strictly higher loadings. -/
theorem violRedPermEquiv_mem_stendhalUpperIdeal_iff (s : Seq μ) (κ : List (Fin ℓ))
    (x : ViolQuotient k Q (Λ ∘ σ) ν) :
    f x ∈ stendhalUpperIdeal k Q Λ ν (Seq.redPerm σ s) (κ.map σ) ↔
      x ∈ stendhalUpperIdeal k Q (Λ ∘ σ) ν s κ := by
  constructor
  · intro hx
    have hle : stendhalUpperIdeal k Q Λ ν (Seq.redPerm σ s) (κ.map σ) ≤
        TwoSidedIdeal.comap (f).symm (stendhalUpperIdeal k Q (Λ ∘ σ) ν s κ) := by
      rw [stendhalUpperIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨v, hv, hlt, rfl⟩
      obtain ⟨w, rfl⟩ := (Seq.redPermEquiv σ).surjective v
      change redWord (Seq.redPerm σ w) = _ at hv
      change StendhalLT (Seq.redPerm σ s) (Seq.redPerm σ w) at hlt
      rw [redWord_redPerm, (List.map_injective_iff.2 σ.injective).eq_iff] at hv
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
      change (f).symm (violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (Seq.redPerm σ w)))) ∈ _
      rw [← violRedPermEquiv_e, AlgEquiv.symm_apply_apply]
      exact TwoSidedIdeal.subset_span ⟨w, hv, (stendhalLT_redPerm_iff' σ s w).1 hlt, rfl⟩
    have := hle hx
    rwa [TwoSidedIdeal.mem_comap, AlgEquiv.symm_apply_apply] at this
  · intro hx
    have hle : stendhalUpperIdeal k Q (Λ ∘ σ) ν s κ ≤
        TwoSidedIdeal.comap f (stendhalUpperIdeal k Q Λ ν (Seq.redPerm σ s) (κ.map σ)) := by
      rw [stendhalUpperIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨v, hv, hlt, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
      change f (violMk k Q (Λ ∘ σ) ν (ofKLR k Q (Λ ∘ σ) ν (KLRAlgebra.e v))) ∈ _
      rw [violRedPermEquiv_e]
      exact TwoSidedIdeal.subset_span ⟨Seq.redPerm σ v, by rw [redWord_redPerm, hv],
        (stendhalLT_redPerm_iff' σ s v).2 hlt, rfl⟩
    have := hle hx
    rwa [TwoSidedIdeal.mem_comap] at this

theorem violRedPermEquiv_mem_violCorner (s : Seq μ) (κ : List (Fin ℓ))
    (y : violCorner k Q (Λ ∘ σ) ν s κ) :
    f y.1 ∈ violCorner k Q Λ ν (Seq.redPerm σ s) (κ.map σ) := by
  have hy := mem_violCorner_iff.1 y.2
  refine mem_violCorner_iff.2 ⟨?_, ?_⟩
  · rw [← violRedPermEquiv_e, ← map_mul, hy.1]
  · rw [← violRedPermEquiv_redProj, ← map_mul, hy.2]

theorem violRedPermEquiv_symm_mem_violCorner (s : Seq μ) (κ : List (Fin ℓ))
    (y : violCorner k Q Λ ν (Seq.redPerm σ s) (κ.map σ)) :
    (f).symm y.1 ∈ violCorner k Q (Λ ∘ σ) ν s κ := by
  have hy := mem_violCorner_iff.1 y.2
  refine mem_violCorner_iff.2 ⟨?_, ?_⟩
  · apply (f).injective
    rw [map_mul, violRedPermEquiv_e, AlgEquiv.apply_symm_apply, hy.1]
  · apply (f).injective
    rw [map_mul, violRedPermEquiv_redProj, AlgEquiv.apply_symm_apply, hy.2]

/-- Relabelling the red strands on the cuts `e(s) V e_κ`. -/
def violCornerRelabel (s : Seq μ) (κ : List (Fin ℓ)) :
    violCorner k Q (Λ ∘ σ) ν s κ ≃+ violCorner k Q Λ ν (Seq.redPerm σ s) (κ.map σ) where
  toFun y := ⟨f y.1, violRedPermEquiv_mem_violCorner σ s κ y⟩
  invFun y := ⟨(f).symm y.1, violRedPermEquiv_symm_mem_violCorner σ s κ y⟩
  left_inv y := Subtype.ext ((f).symm_apply_apply y.1)
  right_inv y := Subtype.ext ((f).apply_symm_apply y.1)
  map_add' y z := Subtype.ext (map_add (f) y.1 z.1)

theorem violCornerRelabel_val (s : Seq μ) (κ : List (Fin ℓ))
    (y : violCorner k Q (Λ ∘ σ) ν s κ) : (violCornerRelabel σ s κ y).1 = f y.1 := rfl

theorem violCornerRelabel_mem_violStandardUpper_iff {s : Seq μ} {κ : List (Fin ℓ)}
    (hκ : redWord s = κ) (y : violCorner k Q (Λ ∘ σ) ν s κ) :
    violCornerRelabel σ s κ y ∈ violStandardUpper (Seq.redPerm σ s) (κ.map σ) ↔
      y ∈ violStandardUpper s κ := by
  subst hκ
  have hκ' : redWord (Seq.redPerm σ s) = (redWord s).map σ := redWord_redPerm σ s
  have key : ∀ (z : violCorner k Q Λ ν (Seq.redPerm σ s) ((redWord s).map σ)),
      z ∈ violStandardUpper (Seq.redPerm σ s) ((redWord s).map σ) ↔
        z.1 ∈ stendhalUpperIdeal k Q Λ ν (Seq.redPerm σ s) ((redWord s).map σ) := by
    rw [← hκ']
    exact mem_violStandardUpper_iff
  rw [key, mem_violStandardUpper_iff, violCornerRelabel_val,
    violRedPermEquiv_mem_stendhalUpperIdeal_iff]

/-- **Relabelling a standard module** (Webster, arXiv:1309.3796v2, §6.1, proof of
Corollary 6.10): for a loading `s` of the red order `κ`, relabelling the red strands along `σ`
identifies `e(s) T^{λ ∘ σ} / U_s` with `e(σ s) V / U_{σ s}`, a standard module at red order
`σ ∘ κ`. -/
def loadingStandardRelabel {s : Seq μ} {κ : List (Fin ℓ)} (hκ : redWord s = κ) :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ ≃+
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) (κ.map σ) :=
  QuotientAddGroup.congr _ _ (violCornerRelabel σ s κ) (by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (violCornerRelabel_mem_violStandardUpper_iff σ hκ y).2 hy
    · intro hz
      refine ⟨(violCornerRelabel σ s κ).symm z, ?_, (violCornerRelabel σ s κ).apply_symm_apply z⟩
      apply (violCornerRelabel_mem_violStandardUpper_iff σ hκ _).1
      rw [AddEquiv.apply_symm_apply]
      exact hz)

theorem loadingStandardRelabel_mk {s : Seq μ} {κ : List (Fin ℓ)} (hκ : redWord s = κ)
    (y : violCorner k Q (Λ ∘ σ) ν s κ) :
    loadingStandardRelabel σ hκ (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (violCornerRelabel σ s κ y) := rfl

/-- Relabelling intertwines the right actions of the corners `e_κ V e_κ` and
`e_{σκ} V e_{σκ}`. -/
theorem loadingStandardRelabel_smul {s : Seq μ} {κ : List (Fin ℓ)} (hκ : redWord s = κ)
    (c : (C' κ)ᵐᵒᵖ) (c' : (C (κ.map σ))ᵐᵒᵖ) (hc : c'.unop.1 = f c.unop.1)
    (z : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ σ) s κ) :
    loadingStandardRelabel σ hκ (c • z) = c' • loadingStandardRelabel σ hκ z := by
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, loadingStandardRelabel_mk, loadingStandardRelabel_mk,
      ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    rw [violCornerRelabel_val, violCorner_smul_val, violCorner_smul_val, map_mul, hc]
    rfl

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

/-- `loadingStandardRelabel` on the right standard module over `T^{λ ∘ σ}`. -/
def rightStandardRelabel {s : Seq μ} (hs : redWord s = List.finRange ℓ) :
    RightStandard (Λ ∘ σ) hρ hQ s ≃+
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) ((List.finRange ℓ).map σ) :=
  loadingStandardRelabel σ hs

theorem rightStandardRelabel_mk {s : Seq μ} (hs : redWord s = List.finRange ℓ)
    (y : violCorner k Q (Λ ∘ σ) ν s (List.finRange ℓ)) :
    rightStandardRelabel σ hρ hQ hs (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (violCornerRelabel σ s _ y) := rfl

/-- On the right standard module over `T^{λ ∘ σ}`, relabelling turns the right action of
`u ∈ T^{λ ∘ σ}` into right multiplication by `permCornerMap u`. -/
theorem rightStandardRelabel_smul {s : Seq μ}
    (hs : redWord s = List.finRange ℓ) (u : (TensorProductAlgebra k Q (Λ ∘ σ) ν)ᵐᵒᵖ)
    (c' : (C ((List.finRange ℓ).map σ))ᵐᵒᵖ)
    (hc : c'.unop.1 = permCornerMap Q Λ ν hρ hQ σ u.unop) (z : RightStandard (Λ ∘ σ) hρ hQ s) :
    rightStandardRelabel σ hρ hQ hs (u • z) = c' • rightStandardRelabel σ hρ hQ hs z :=
  loadingStandardRelabel_smul σ hs (rightCornerHom (Λ := Λ ∘ σ) (ν := ν) hρ hQ u) c' hc z

end Categorification.Stendhal.BraidedStendhalAlgebra
