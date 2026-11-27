/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CoarsePhiCount
import Categorification.WeightedKLR.RedStrands.BraidPartialStandardVanishing
import Categorification.WeightedKLR.RedStrands.BraidedStandardization

/-!
# The partial standard kernel over the corner is filtered by partial standards

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §6.1, proof
of Lemma 6.8: in the red order `λ` and for a merged pair `b < a`, the kernel of the loading
projective `e(s) (e_λ V e_λ)` onto its partial standard module has a finite filtration whose
subquotients are partial standard modules at loadings of the same red order with strictly
higher root (`exists_hasFiltration_blockLoadingKernelAt`).

The corner `e_λ V e_λ` is identified with `T^λ` (`violCornerEquiv`), and reflecting diagrams
turns right modules into left modules (`cornerReflectEquiv`). This carries the loading
projective, its kernel and its partial standard module to the left objects of
`Stendhal.leftPartialStandard`, where the filtration is
`Stendhal.exists_hasFiltration_leftPartialKernel`.

Route hypothesis, inherited from Lemma 5.19: `AllFiniteDeltaInjective`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "μ" => stendhalWeight ℓ ν
local notation "ord" => List.finRange ℓ
local notation "V" => ViolQuotient k Q Λ ν
local notation "C" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν ord)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "eλ" => violMk k Q Λ ν (redProj k Q Λ ν ord)

/-- A red order `κ` membership test for the partial standard kernel. -/
theorem mem_blockLoadingKernelAt_iff {s : Seq μ} {a b : Fin ℓ} {κ : List (Fin ℓ)}
    (hs : redWord s = κ) (x : rIdeal (orderedLoadingIdemAt Q Λ κ s hs)) :
    x ∈ blockLoadingKernelAt Q Λ s a b κ hs ↔
      x.1.1 ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b s) κ := by
  subst hs
  exact Iff.rfl

section Reflect

variable {ρ : Equiv.Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q)

/-- The corner `e_λ V e_λ` in the red order `λ` and `T^λ`, with diagrams reflected: right
modules over the corner become left `T^λ`-modules. -/
def cornerReflectEquiv : Cᵐᵒᵖ ≃+* T :=
  (RingEquiv.op (violCornerEquiv (k := k) (Q := Q) (Λ := Λ) (ν := ν) hρ hQ)).trans
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν).symm

theorem cornerReflectEquiv_op (x : C) :
    cornerReflectEquiv (Λ := Λ) hρ hQ (op x) = tensorFlip (violCornerEquiv hρ hQ x) := rfl

/-- The reflection carries a corner loading idempotent to the tensor loading idempotent. -/
theorem cornerReflectEquiv_loadingIdem {t : Seq μ} (ht : redWord t = ord) :
    cornerReflectEquiv (Λ := Λ) hρ hQ (op (orderedLoadingIdemAt Q Λ ord t ht)) =
      seqIdem Q Λ t ((redWord_eq_finRange_iff t).1 ht) := by
  rw [cornerReflectEquiv_op]
  have hid : orderedLoadingIdemAt Q Λ ord t ht =
      violCornerHom k Q Λ ν (cornerMk (ofKLR k Q Λ ν (KLRAlgebra.e t))) := by
    apply Subtype.ext
    rw [violCornerHom_val, cornerMk_e_val ht]
    rfl
  rw [hid, violCornerEquiv_violCornerHom, identityCornerHom_e ht, tensorFlip_mk_e]

/-- The loading projective `e(s) (e_λ V e_λ)` and the left projective `T^λ e(s)`. -/
def loadingProjectiveReflect {s : Seq μ} (hs : redWord s = ord) :
    rIdeal (orderedLoadingIdemAt Q Λ ord s hs) ≃ₛₗ[(cornerReflectEquiv (Λ := Λ) hρ hQ : Cᵐᵒᵖ →+* T)]
      lIdeal (seqIdem Q Λ s ((redWord_eq_finRange_iff s).1 hs)) := by
  let F := cornerReflectEquiv (Λ := Λ) hρ hQ
  let f := orderedLoadingIdemAt Q Λ ord s hs
  have hf : F (op f) = seqIdem Q Λ s ((redWord_eq_finRange_iff s).1 hs) :=
    cornerReflectEquiv_loadingIdem (Λ := Λ) hρ hQ hs
  refine { toFun := fun p => ⟨F (op p.1), ?_⟩
           invFun := fun p => ⟨unop (F.symm p.1), ?_⟩
           map_add' := fun x y => Subtype.ext (map_add F (op x.1) (op y.1))
           map_smul' := fun a x => Subtype.ext (map_mul F a (op x.1))
           left_inv := fun x => Subtype.ext (congrArg unop (F.symm_apply_apply (op x.1)))
           right_inv := fun x => Subtype.ext (F.apply_symm_apply x.1) }
  · change F (op p.1) * seqIdem Q Λ s _ = F (op p.1)
    rw [← hf, ← map_mul, ← op_mul, show f * p.1 = p.1 from p.2]
  · apply mem_rIdeal.2
    apply op_injective
    apply F.injective
    change F (op (f * (F.symm p.1).unop)) = F (F.symm p.1)
    rw [op_mul, op_unop, map_mul, hf, F.apply_symm_apply,
      show p.1 * seqIdem Q Λ s _ = p.1 from p.2]

theorem loadingProjectiveReflect_apply {s : Seq μ} (hs : redWord s = ord)
    (x : rIdeal (orderedLoadingIdemAt Q Λ ord s hs)) :
    (loadingProjectiveReflect (Λ := Λ) hρ hQ hs x : T) = cornerReflectEquiv (Λ := Λ) hρ hQ (op x.1) := rfl

/-- The compression `e_λ v e_λ` of an element of `V` to the corner. -/
private def compress (v : V) : C := ⟨eλ * v * eλ, v, rfl⟩

private theorem compress_add (v w : V) : compress (v + w) = compress v + compress w :=
  Subtype.ext (by change eλ * (v + w) * eλ = eλ * v * eλ + eλ * w * eλ; noncomm_ring)

private theorem compress_zero : compress (0 : V) = 0 :=
  Subtype.ext (by change eλ * 0 * eλ = 0; simp)

private theorem compress_neg (v : V) : compress (-v) = -compress v :=
  Subtype.ext (by change eλ * (-v) * eλ = -(eλ * v * eλ); noncomm_ring)

private theorem compress_of_corner (x : C) : compress x.1 = x := by
  apply Subtype.ext
  change eλ * x.1 * eλ = x.1
  rw [corner_mul_left (isIdempotentElem_violMk_redProj k Q Λ ν ord),
    corner_mul_right (isIdempotentElem_violMk_redProj k Q Λ ν ord)]

private theorem compress_loading {s t : Seq μ} (hs : redWord s = ord) (ht : redWord t = ord)
    (a b : V) :
    compress ((orderedLoadingIdemAt Q Λ ord s hs).1 * (a * (orderedLoadingIdemAt Q Λ ord t ht).1 *
      b)) = orderedLoadingIdemAt Q Λ ord s hs * compress a * orderedLoadingIdemAt Q Λ ord t ht *
        compress b := by
  have hp := isIdempotentElem_violMk_redProj k Q Λ ν ord
  set fs := orderedLoadingIdemAt Q Λ ord s hs
  set ft := orderedLoadingIdemAt Q Λ ord t ht
  apply Subtype.ext
  change eλ * (fs.1 * (a * ft.1 * b)) * eλ = fs.1 * (eλ * a * eλ) * ft.1 * (eλ * b * eλ)
  have h1 : eλ * fs.1 = fs.1 := corner_mul_left hp fs
  have h2 : fs.1 * eλ = fs.1 := corner_mul_right hp fs
  have h3 : eλ * ft.1 = ft.1 := corner_mul_left hp ft
  have h4 : ft.1 * eλ = ft.1 := corner_mul_right hp ft
  calc eλ * (fs.1 * (a * ft.1 * b)) * eλ = (eλ * fs.1) * a * ft.1 * b * eλ := by
        simp only [mul_assoc]
    _ = (fs.1 * eλ) * a * ((eλ * ft.1) * eλ) * b * eλ := by rw [h1, h2, h3, h4]
    _ = _ := by simp only [mul_assoc]

variable {a b : Fin ℓ}

/-- The reflection carries the partial standard kernel onto `leftPartialKernel`. -/
theorem map_blockLoadingKernelAt_eq {s : Seq μ} (hs : redWord s = ord) :
    (blockLoadingKernelAt Q Λ s a b ord hs).map (loadingProjectiveReflect (Λ := Λ) hρ hQ hs).toLinearMap =
      leftPartialKernel Q Λ a b s ((redWord_eq_finRange_iff s).1 hs) := by
  let F := cornerReflectEquiv (Λ := Λ) hρ hQ
  let E := loadingProjectiveReflect (Λ := Λ) hρ hQ hs
  let hs' := (redWord_eq_finRange_iff s).1 hs
  let J := blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b s) ord
  let U := leftPartialUpper Q Λ a b s hs'
  let fs := orderedLoadingIdemAt Q Λ ord s hs
  -- the forward inclusion
  have fwd : ∀ v ∈ J, ∀ c d : V, F (op (compress (fs.1 * (c * v * d)))) ∈ U := by
    intro v hv
    induction hv using TwoSidedIdeal.span_induction with
    | mem v hv =>
      obtain ⟨t, ht, hlt, rfl⟩ := hv
      intro c d
      have ht' := (redWord_eq_finRange_iff t).1 ht
      have he : (orderedLoadingIdemAt Q Λ ord t ht).1 =
          (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)) (KLRAlgebra.e t) := rfl
      rw [← he, compress_loading hs ht, op_mul, op_mul, op_mul, map_mul, map_mul, map_mul,
        cornerReflectEquiv_loadingIdem (Λ := Λ) hρ hQ ht, cornerReflectEquiv_loadingIdem (Λ := Λ) hρ hQ hs]
      have hm := seqIdem_mul_mul_seqIdem_mem_leftPartialUpper hs' ht' hlt (F (op (compress c)))
      have := U.smul_mem (F (op (compress d))) hm
      simpa only [smul_eq_mul, mul_assoc] using this
    | zero =>
      intro c d
      rw [mul_zero, zero_mul, mul_zero, compress_zero, op_zero, map_zero]
      exact U.zero_mem
    | add x y _ _ hx hy =>
      intro c d
      rw [mul_add, add_mul, mul_add, compress_add, op_add, map_add]
      exact U.add_mem (hx c d) (hy c d)
    | neg x _ hx =>
      intro c d
      rw [mul_neg, neg_mul, mul_neg, compress_neg, op_neg, map_neg]
      exact U.neg_mem (hx c d)
    | left_absorb e x _ hx =>
      intro c d
      simpa only [mul_assoc] using hx (c * e) d
    | right_absorb e x _ hx =>
      intro c d
      simpa only [mul_assoc] using hx c (e * d)
  -- the backward inclusion
  let Θ : T → V := fun y => (F.symm y).unop.1
  have hΘmul : ∀ c y : T, Θ (c * y) = Θ y * Θ c := fun c y => by
    change (F.symm (c * y)).unop.1 = _
    rw [map_mul, unop_mul]
    rfl
  have bwd : ∀ y ∈ U, Θ y ∈ J := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, ht', c, hlt, rfl⟩ := hy
      have ht := (redWord_eq_finRange_iff t).2 ht'
      have hΘt : Θ (seqIdem Q Λ t ht') =
          (AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)) (KLRAlgebra.e t) := by
        change (F.symm (seqIdem Q Λ t ht')).unop.1 = _
        rw [← cornerReflectEquiv_loadingIdem (Λ := Λ) hρ hQ ht, RingEquiv.symm_apply_apply]
        rfl
      rw [hΘmul, hΘmul, hΘt]
      exact J.mul_mem_left _ _ (J.mul_mem_left _ _ (TwoSidedIdeal.subset_span ⟨t, ht, hlt, rfl⟩))
    | zero => exact (by simp [Θ] : Θ 0 = 0) ▸ J.zero_mem
    | add x y _ _ hx hy =>
      have : Θ (x + y) = Θ x + Θ y := by simp only [Θ, map_add, unop_add]; rfl
      rw [this]
      exact J.add_mem hx hy
    | smul c y _ hy =>
      rw [smul_eq_mul, hΘmul]
      exact J.mul_mem_right _ _ hy
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_blockLoadingKernelAt_iff] at hx
    change F (op x.1) ∈ U
    have h := fwd _ hx 1 1
    rw [one_mul, mul_one, show fs.1 * x.1.1 = x.1.1 from congrArg Subtype.val x.2,
      compress_of_corner] at h
    exact h
  · intro hz
    refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
    rw [SetLike.mem_coe, mem_blockLoadingKernelAt_iff]
    have h := bwd _ hz
    exact h

instance (s : Seq μ) (hs : redWord s = ord) :
    AddCommGroup (rIdeal (orderedLoadingIdemAt Q Λ ord s hs)) :=
  Submodule.addCommGroup _

instance (s : Seq μ) (hs : redWord s = ord) :
    AddCommGroup (blockLoadingKernelAt Q Λ s a b ord hs) :=
  Submodule.addCommGroup _

/-- The partial standard kernel over the corner and `leftPartialKernel`. -/
def blockLoadingKernelReflect {s : Seq μ} (hs : redWord s = ord) :
    blockLoadingKernelAt Q Λ s a b ord hs ≃ₛₗ[(cornerReflectEquiv (Λ := Λ) hρ hQ : Cᵐᵒᵖ →+* T)]
      leftPartialKernel Q Λ a b s ((redWord_eq_finRange_iff s).1 hs) :=
  ((loadingProjectiveReflect (Λ := Λ) hρ hQ hs).submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_blockLoadingKernelAt_eq hρ hQ hs))

/-- The partial standard module over the corner and `leftPartialStandard`. -/
def blockPartialStandardReflect {s : Seq μ} (hs : redWord s = ord) :
    (rIdeal (orderedLoadingIdemAt Q Λ ord s hs) ⧸ blockLoadingKernelAt Q Λ s a b ord hs) ≃ₛₗ[
      (cornerReflectEquiv (Λ := Λ) hρ hQ : Cᵐᵒᵖ →+* T)]
      leftPartialStandard Q Λ a b s ((redWord_eq_finRange_iff s).1 hs) :=
  Submodule.Quotient.equiv _ _ (loadingProjectiveReflect (Λ := Λ) hρ hQ hs)
    (map_blockLoadingKernelAt_eq hρ hQ hs)

end Reflect

private def restrictSemilinear {A B M : Type} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] {N : ModuleCat.{0} B} (F : A ≃+* B)
    (e : M ≃ₛₗ[(F : A →+* B)] N) :
    M ≃ₗ[A] ((ModuleCat.restrictScalars (F : A →+* B)).obj N) where
  __ := e.toAddEquiv
  map_smul' := fun a x => e.map_smulₛₗ a x

variable {a b : Fin ℓ}

/-- **The partial standard kernel over the corner is filtered by partial standards**
(B. Webster, arXiv:1309.3796v3, §6.1, proof of Lemma 6.8): in the red order `λ` and for a
merged pair `b < a`, the kernel of the loading projective `e(s) (e_λ V e_λ)` onto its partial
standard module has a finite filtration whose subquotients are partial standard modules at
loadings of the same red order with strictly higher root. Route hypothesis:
`AllFiniteDeltaInjective`, from Lemma 5.19. -/
theorem exists_hasFiltration_blockLoadingKernelAt (hQ : KLRSymm Q)
    {D : QuantumGroup.CartanDatum I} (hR : IsRouquierQ D Q)
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ)
    (hba : b < a) {κ : List (Fin ℓ)} (hκ : κ = ord) (s : Seq μ) (hs : redWord s = κ) :
    ∃ l : List {v : Seq μ // redWord v = κ},
      (∀ v ∈ l, adjacentBlockRoot a b s < adjacentBlockRoot a b v.1) ∧
        ModuleFiltration.HasFiltration (fun v => blockPartialStandardAt Q Λ v.1 a b κ v.2) l
          (blockLoadingKernelObjAt Q Λ a b κ s hs) := by
  subst hκ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Equiv.Perm (Fin (Multiset.card μ)) → List ℕ, TypeA.IsReducedChoice ρ :=
    ⟨fun w => (TypeA.exists_reduced _ w).choose, fun w => (TypeA.exists_reduced _ w).choose_spec⟩
  have hs' := (redWord_eq_finRange_iff s).1 hs
  obtain ⟨l, hl, hfil⟩ := exists_hasFiltration_leftPartialKernel (Λ := Λ) hQ hR hall hba hs'
  let F := cornerReflectEquiv (Λ := Λ) hρ hQ
  let g : {t : Seq μ // IsRedOrdered t} → {v : Seq μ // redWord v = ord} := fun t =>
    ⟨t.1, (redWord_eq_finRange_iff _).2 t.2⟩
  refine ⟨l.map g, ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
    exact hl t ht
  refine ModuleFiltration.HasFiltration.relabel g ?_
  have h1 := hfil.restrictScalars (F : Cᵐᵒᵖ →+* T)
  refine (ModuleFiltration.HasFiltration.of_equiv h1
    (restrictSemilinear F (blockLoadingKernelReflect hρ hQ hs)).symm).mono_of_mem ?_
  intro t _
  exact ⟨(restrictSemilinear F (blockPartialStandardReflect hρ hQ (g t).2)).symm⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
