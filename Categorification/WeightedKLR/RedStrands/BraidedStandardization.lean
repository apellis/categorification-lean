/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Equiv.Fin.Rotate
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.BlackCountTransport
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorProj
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardEquiv

/-!
# Standardization at the Figure 5 loadings

Webster, arXiv:1309.3796v2, §5.1, Definitions 5.1 and 5.4, and §6.1, proof of Proposition 6.9.
We compare the right loading models used by the braid with the left-module calculations of
standardization. Relabelling red strands identifies the corner with the tensor product algebra,
and horizontal reflection converts the right action to the left action. With the internal
grading forgotten, the two endpoint comparisons compose with Definition 6.6 evaluated on the
Figure 5 loading projective.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite CornerEndomorphism
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section LoadingComparisons

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "μ" => stendhalWeight ℓ ν

omit [DecidableEq I] in
private theorem redWord_relabel {s : Seq μ} (hs : IsRedOrdered s) :
    redWord (Seq.redPerm σ s) = κ := by
  rw [redWord_redPerm, (redWord_eq_finRange_iff s).2 hs]

/-- Coefficient change for the two-sided reading of the diagrams: undo the relabelling of the
red order, then reflect diagrams to convert the right action into the left action. -/
def leftCoefficientEquiv : Cᵐᵒᵖ ≃+* T :=
  (RingEquiv.op (violCornerRedPermTensorEquiv (Λ₀ := Λ) hρ hQ σ)).trans
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ ∘ σ) ν).symm

private theorem redPermTensorEquiv_loadingIdem {s : Seq μ} (hs : IsRedOrdered s) :
    violCornerRedPermTensorEquiv (Λ₀ := Λ) hρ hQ σ
        (violLoadingIdem (redWord_relabel σ hs)) = seqIdem Q (Λ ∘ σ) s hs := by
  let e := violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν)
    σ (fun _ => rfl) (List.finRange ℓ)
  have h := (redWord_eq_finRange_iff s).2 hs
  have he : e (violLoadingIdem (k := k) (Q := Q) (Λ := Λ ∘ σ) h) =
      violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs) := by
    apply Subtype.ext
    change violRedPermEquiv σ (fun _ => rfl) (violMk k Q (Λ ∘ σ) ν
      (ofKLR k Q (Λ ∘ σ) ν (KLRAlgebra.e s))) =
        violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (Seq.redPerm σ s)))
    exact (violRedPermEquiv_violMk σ (fun _ => rfl) _).trans
      (congrArg (violMk k Q Λ ν) (redPermAlgEquiv_e σ (fun _ => rfl) s))
  change violCornerEquiv hρ hQ (e.symm _) = _
  rw [← he, RingEquiv.symm_apply_apply]
  have hid : violLoadingIdem (k := k) (Q := Q) (Λ := Λ ∘ σ) h =
      violCornerHom k Q (Λ ∘ σ) ν (cornerMk (ofKLR k Q (Λ ∘ σ) ν (KLRAlgebra.e s))) := by
    apply Subtype.ext
    rw [violCornerHom_val, cornerMk_e_val h]
    rfl
  rw [hid, violCornerEquiv_violCornerHom, identityCornerHom_e h]

private theorem leftCoefficientEquiv_loadingIdem {s : Seq μ} (hs : IsRedOrdered s) :
    leftCoefficientEquiv (Λ := Λ) hρ hQ σ (op (violLoadingIdem (redWord_relabel σ hs))) =
      seqIdem Q (Λ ∘ σ) s hs := by
  change tensorFlip (violCornerRedPermTensorEquiv (Λ₀ := Λ) hρ hQ σ
    (violLoadingIdem (redWord_relabel σ hs))) = _
  rw [redPermTensorEquiv_loadingIdem hρ hQ σ hs, tensorFlip_mk_e]

private def loadingProjectiveLeftEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)) ≃ₛₗ[
      (leftCoefficientEquiv (Λ := Λ) hρ hQ σ : Cᵐᵒᵖ →+* T)] lIdeal (seqIdem Q (Λ ∘ σ) s hs) := by
  let F := leftCoefficientEquiv (Λ := Λ) hρ hQ σ
  let f := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)
  have hf : F (op f) = seqIdem Q (Λ ∘ σ) s hs := leftCoefficientEquiv_loadingIdem hρ hQ σ hs
  refine { toFun := fun p => ⟨F (op p.1), ?_⟩
           invFun := fun p => ⟨unop (F.symm p.1), ?_⟩
           map_add' := fun x y => Subtype.ext (map_add F (op x.1) (op y.1))
           map_smul' := fun a x => Subtype.ext (map_mul F a (op x.1))
           left_inv := fun x => Subtype.ext (congrArg unop (F.symm_apply_apply (op x.1)))
           right_inv := fun x => Subtype.ext (F.apply_symm_apply x.1) }
  · change F (op p.1) * seqIdem Q (Λ ∘ σ) s hs = F (op p.1)
    rw [← hf, ← map_mul, ← op_mul, show f * p.1 = p.1 from p.2]
  · apply mem_rIdeal.2
    apply op_injective
    apply F.injective
    change F (op (f * (F.symm p.1).unop)) = F (F.symm p.1)
    rw [op_mul, op_unop, map_mul, hf, F.apply_symm_apply,
      show p.1 * seqIdem Q (Λ ∘ σ) s hs = p.1 from p.2]

private def diagonalCutProjectiveEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    violCorner k Q Λ ν (Seq.redPerm σ s) κ ≃ₗ[Cᵐᵒᵖ]
      rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)) := by
  let f := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)
  let hp := isIdempotentElem_violMk_redProj k Q Λ ν κ
  refine { toFun := fun x => ⟨⟨x.1, (Subsemigroup.mem_corner_iff hp).2 ?_⟩, ?_⟩
           invFun := fun x => ⟨x.1.val, mem_violCorner_iff.2
             ⟨congrArg Subtype.val x.2, corner_mul_right hp x.1⟩⟩
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · have hx := mem_violCorner_iff.1 x.2
    refine ⟨?_, hx.2⟩
    change _ * x.1 = x.1
    calc
      _ * x.1 = _ * (f.val * x.1) := congrArg (_ * ·) hx.1.symm
      _ = x.1 := (mul_assoc _ _ _).symm.trans
        ((congrArg (· * x.1) (corner_mul_left hp f)).trans hx.1)
  · exact Subtype.ext (mem_violCorner_iff.1 x.2).1

private theorem stendhalLT_redPerm_iff (s t : Seq μ) :
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

local notation "V" => ViolQuotient k Q Λ ν
local notation "eκ" => violMk k Q Λ ν (redProj k Q Λ ν κ)

private def compress (a : V) : C := ⟨eκ * a * eκ, a, rfl⟩

private theorem diagonalCut_upper_image {s : Seq μ} (hs : IsRedOrdered s) :
    let E := (diagonalCutProjectiveEquiv (Λ := Λ) σ hs).trans
      (loadingProjectiveLeftEquiv hρ hQ σ hs)
    ((violStandardUpper (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ).map E.toLinearMap).map
        (lIdeal (seqIdem Q (Λ ∘ σ) s hs)).subtype = leftUpper Q (Λ ∘ σ) s hs := by
  dsimp only
  let F := leftCoefficientEquiv (Λ := Λ) hρ hQ σ
  let E := (diagonalCutProjectiveEquiv (Λ := Λ) σ hs).trans (loadingProjectiveLeftEquiv hρ hQ σ hs)
  let f := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hs)
  let G := (lIdeal (seqIdem Q (Λ ∘ σ) s hs)).subtype.comp E.toLinearMap
  change ((violStandardUpper (Λ := Λ) (Seq.redPerm σ s) κ).map E.toLinearMap).map _ = _
  rw [← Submodule.map_comp, violStandardUpper, Submodule.map_span, leftUpper]
  congr 1
  have hG (j : Seq μ) (hj : IsRedOrdered j) (a : V)
      (y : violCorner k Q Λ ν (Seq.redPerm σ s) κ)
      (hy : y.1 = f.val * (a * (violLoadingIdem (k := k) (Q := Q) (Λ := Λ)
        (redWord_relabel σ hj)).val) * eκ) :
      G y = seqIdem Q (Λ ∘ σ) j hj * F (op (compress σ a)) * seqIdem Q (Λ ∘ σ) s hs := by
    let z := violLoadingIdem (k := k) (Q := Q) (Λ := Λ) (redWord_relabel σ hj)
    let hp := isIdempotentElem_violMk_redProj k Q Λ ν κ
    have hz : (diagonalCutProjectiveEquiv (Λ := Λ) σ hs y).1 = f * compress σ a * z := by
      apply Subtype.ext
      change y.1 = f.val * (eκ * a * eκ) * z.val
      change y.1 = f.val * (a * z.val) * eκ at hy
      have hfe : f.val * eκ = f.val := corner_mul_right hp f
      have hez : eκ * z.val = z.val := corner_mul_left hp z
      have hze : z.val * eκ = z.val := corner_mul_right hp z
      calc
        y.1 = f.val * (a * z.val) * eκ := hy
        _ = f.val * (a * z.val) := by rw [mul_assoc f.val, mul_assoc a, hze]
        _ = (f.val * eκ) * (a * (eκ * z.val)) := by rw [hfe, hez]
        _ = f.val * (eκ * a * eκ) * z.val := by simp only [mul_assoc]
    change F (op (diagonalCutProjectiveEquiv (Λ := Λ) σ hs y).1) = _
    rw [hz, op_mul, op_mul, map_mul F, map_mul F, mul_assoc,
      leftCoefficientEquiv_loadingIdem hρ hQ σ hs, leftCoefficientEquiv_loadingIdem hρ hQ σ hj]
  ext x
  constructor
  · rintro ⟨y, ⟨j, a, hj, hlt, rfl⟩, rfl⟩
    obtain ⟨j, rfl⟩ := (Seq.redPermEquiv σ).surjective j
    change redWord (Seq.redPerm σ j) = κ at hj
    rw [redWord_redPerm] at hj
    have hj' : IsRedOrdered j := (redWord_eq_finRange_iff _).1
      ((List.map_injective_iff.2 σ.injective) hj)
    exact ⟨j, hj', F (op (compress σ a)), (stendhalLT_redPerm_iff σ _ _).1 hlt, hG j hj' a _ rfl⟩
  · rintro ⟨j, hj, b, hlt, rfl⟩
    obtain ⟨a, ha⟩ := F.surjective b
    have ha' : compress σ a.unop.val = a.unop := by
      apply Subtype.ext
      change eκ * a.unop.val * eκ = a.unop.val
      rw [corner_mul_left (isIdempotentElem_violMk_redProj k Q Λ ν κ),
        corner_mul_right (isIdempotentElem_violMk_redProj k Q Λ ν κ)]
    refine ⟨_, ⟨Seq.redPerm σ j, a.unop.val, redWord_relabel σ hj,
      (stendhalLT_redPerm_iff σ _ _).2 hlt, rfl⟩, ?_⟩
    rw [hG j hj a.unop.val _ rfl, ha', op_unop, ha]

private def loadingStandardLeftEquiv {s : Seq μ} (hs : IsRedOrdered s) :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ s) κ ≃ₛₗ[
      (leftCoefficientEquiv (Λ := Λ) hρ hQ σ : Cᵐᵒᵖ →+* T)] leftStandard Q (Λ ∘ σ) s hs := by
  let E := (diagonalCutProjectiveEquiv (Λ := Λ) σ hs).trans (loadingProjectiveLeftEquiv hρ hQ σ hs)
  let J := lIdeal (seqIdem Q (Λ ∘ σ) s hs)
  refine Submodule.Quotient.equiv _ _ E ?_
  apply Submodule.map_injective_of_injective (f := J.subtype) Subtype.val_injective
  rw [Submodule.map_comap_subtype, inf_eq_right.2 (leftUpper_le_lIdeal Q (Λ ∘ σ) s hs)]
  exact diagonalCut_upper_image hρ hQ σ hs

private def leftStandardEquivProjectiveOfMax {p : ℕ} (Ω : Fin p → I →₀ ℕ) {γ : Multiset I}
    (x : Seq (stendhalWeight p γ)) (hx : IsRedOrdered x)
    (hmax : ∀ j : Seq (stendhalWeight p γ), IsRedOrdered j → ¬ IsViolated j → ¬ StendhalLT x j) :
    leftStandard Q Ω x hx ≃ₗ[TensorProductAlgebra k Q Ω γ] lIdeal (seqIdem Q Ω x hx) := by
  have hU : leftUpper Q Ω x hx = ⊥ := by
    refine le_antisymm (Submodule.span_le.2 ?_) bot_le
    rintro _ ⟨j, hj, a, hlt, rfl⟩
    by_cases hv : IsViolated j
    · have hz : seqIdem Q Ω j hj = 0 := by
        change (StendhalAlgebra.violatedIdeal k Q Ω γ).ringCon.mk' (StendhalAlgebra.e j hj) = 0
        rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
        exact TwoSidedIdeal.subset_span ⟨j, hj, hv, rfl⟩
      simp [hz]
    · exact (hmax j hj hv hlt).elim
  exact Submodule.quotEquivOfEqBot _ (by rw [hU, Submodule.comap_bot, Submodule.ker_subtype])

private theorem singleRed_not_lt {γ : Multiset I} (x j : Seq (stendhalWeight 1 γ))
    (hv : ¬ IsViolated j) : ¬ StendhalLT x j := by
  have h0 : 0 < Multiset.card (stendhalWeight 1 γ) := by simp [stendhalWeight]
  intro h
  apply h.2
  intro r i
  cases hj : j.lbl ⟨0, h0⟩ with
  | inl a => exact (hv ⟨h0, by simp [hj]⟩).elim
  | inr a =>
    obtain rfl := Subsingleton.elim a r
    rw [blackCount_eq_zero_of_first j h0 hj]
    exact Nat.zero_le _

private def exteriorProjectiveStd (Ω : Fin 2 → I →₀ ℕ) {θ β γ : Multiset I}
    (h : θ + β = γ) (x : Seq (stendhalWeight 1 θ)) (hx : IsRedOrdered x) (u : Seq β) :
    ModuleCat.{0} (TensorProductAlgebra k Q Ω γ) :=
  stdLayerModule Q Ω hQ (tensorLayer Q Ω h (oldProj Q Ω θ x hx) (cycProj Q Ω β u))

private def twoRedProjectiveStandardizationEquiv (Ω : Fin 2 → I →₀ ℕ) {θ β : Multiset I}
    (x : Seq (stendhalWeight 1 θ)) (hx : IsRedOrdered x) (u : Seq β) :
    exteriorProjectiveStd hQ Ω rfl x hx u ≃ₗ[TensorProductAlgebra k Q Ω (θ + β)]
      leftStandard Q Ω (twoPieceLoading θ β x u) (isRedOrdered_twoPieceLoading hx u) := by
  let e := leftStandardEquivProjectiveOfMax (Q := Q) (Ω ∘ Fin.castSucc) x hx
    (fun j _ hj => singleRed_not_lt x j hj)
  let f := tensorFactorCongr Q Ω
    (X := oldProj Q Ω θ x hx) (X' := ModuleCat.of _ (leftStandard Q (Ω ∘ Fin.castSucc) x hx))
    (Y := cycProj Q Ω β u) (Y' := cycProj Q Ω β u) e.symm (LinearEquiv.refl _ _)
  exact (stdLayerEquiv Q Ω hQ rfl f).trans (twoPieceStandardEquiv Q Ω hx u hQ)

private theorem twoPieceLoading_vacuumLast_not_lt {θ : Multiset I}
    (x : Seq (stendhalWeight 1 θ)) (u : Seq (0 : Multiset I))
    (j : Seq (stendhalWeight 2 (θ + 0))) (hj : IsRedOrdered j) (hv : ¬ IsViolated j) :
    ¬ StendhalLT (twoPieceLoading θ 0 x u) j := by
  intro h
  apply h.2
  intro r i
  have h0 : 0 < Multiset.card (stendhalWeight 2 (θ + 0)) := by simp [stendhalWeight]
  have hj' : redWord j = [0, 1] := (redWord_eq_finRange_iff _).2 hj
  fin_cases r
  · change blackCount j (0 : Fin 2) i ≤ blackCount (twoPieceLoading θ 0 x u) 0 i
    rw [blackCount_eq_zero_of_first j h0 (lbl_zero_of_not_isViolated h0 hv hj')]
    exact Nat.zero_le _
  · change blackCount j (Fin.last 1) i ≤ blackCount (twoPieceLoading θ 0 x u) (Fin.last 1) i
    rw [blackCount_twoPieceLoading_last]
    calc
      blackCount j (Fin.last 1) i ≤ (Finset.univ.filter fun a => j.lbl a = .inl i).card :=
        Finset.card_le_card fun a ha => Finset.mem_filter.2
          ⟨Finset.mem_univ a, (Finset.mem_filter.1 ha).2.1⟩
      _ = θ.count i := by
        rw [card_filter_lbl_eq]
        simp [stendhalWeight, Multiset.count_map_eq_count' _ _ Sum.inl_injective]

private def restrictSemilinearEquiv {A B M : Type} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] {N : ModuleCat.{0} B} (F : A ≃+* B)
    (e : M ≃ₛₗ[(F : A →+* B)] N) :
    M ≃ₗ[A] ((ModuleCat.restrictScalars (F : A →+* B)).obj N) where
  __ := e.toAddEquiv
  map_smul' := fun a x => e.map_smulₛₗ a x

end LoadingComparisons

section TwoRed

variable {I k : Type} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I} (hQ : KLRSymm Q)
  {Λ₂ : Fin 2 → I →₀ ℕ} {σ₂ : Perm (Fin 2)}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν))) → List ℕ}
  (hρ₂ : TypeA.IsReducedChoice ρ₂)
local notation "κ₂" => List.map σ₂ (List.finRange 2)
local notation "Ω₂" => Λ₂ ∘ σ₂
local notation "C₂" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ₂) (ν := ν) κ₂

/-- Webster's exterior-projective standardization (arXiv:1309.3796v2, §5.1, Definition 5.4),
read as a right module over its two-red corner by relabelling and reflecting diagrams. -/
def exteriorStandardizationRight {θ β : Multiset I} (hν : θ + β = ν)
    (x : Seq (stendhalWeight 1 θ)) (u : Seq β) : ModuleCat.{0} C₂ᵐᵒᵖ :=
  (ModuleCat.restrictScalars (leftCoefficientEquiv (Λ := Λ₂) hρ₂ hQ σ₂).toRingHom).obj
    (exteriorProjectiveStd hQ Ω₂ hν x (SingleRed.ordered θ x) u)

/-- The right loading standard, at a two-piece loading in the indicated red order, agrees
with the standardization of the exterior loading projectives. Setting the first black weight
to zero gives the upper endpoint of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9, Figure 5. -/
def loadingStandardEquivExteriorStandardization {θ β : Multiset I}
    (hν : θ + β = ν) (x : Seq (stendhalWeight 1 θ)) (u : Seq β) :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ₂)
        (Seq.redPerm σ₂ (Seq.cast (congrArg (stendhalWeight 2) hν) (twoPieceLoading θ β x u))) κ₂
      ≃ₗ[C₂ᵐᵒᵖ] exteriorStandardizationRight (Λ₂ := Λ₂) (σ₂ := σ₂) hQ hρ₂ hν x u := by
  subst ν
  let hx := SingleRed.ordered θ x
  exact restrictSemilinearEquiv (N := exteriorProjectiveStd hQ Ω₂ rfl x hx u)
    (leftCoefficientEquiv (Λ := Λ₂) hρ₂ hQ σ₂)
    ((loadingStandardLeftEquiv hρ₂ hQ σ₂ (isRedOrdered_twoPieceLoading hx u)).trans
      (twoRedProjectiveStandardizationEquiv hQ Ω₂ x hx u).symm)

/-- The loading right ideal at the lower endpoint of Webster, arXiv:1309.3796v2, §6.1,
Proposition 6.9, Figure 5, agrees with the standardization of the exterior projectives with
vacuum in the last factor. Every strictly higher ordered loading is violated, so the
standard quotient does not further reduce this projective. -/
def loadingProjectiveEquivExteriorStandardization {θ : Multiset I}
    (hν : θ + 0 = ν) (x : Seq (stendhalWeight 1 θ)) (u : Seq (0 : Multiset I)) :
    rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ₂) (redWord_relabel σ₂
      (isRedOrdered_seqCast (congrArg (stendhalWeight 2) hν)
        (isRedOrdered_twoPieceLoading (SingleRed.ordered θ x) u))))
      ≃ₗ[C₂ᵐᵒᵖ] exteriorStandardizationRight (Λ₂ := Λ₂) (σ₂ := σ₂) hQ hρ₂ hν x u := by
  subst ν
  let hx := SingleRed.ordered θ x
  let hs := isRedOrdered_twoPieceLoading hx u
  let e := leftStandardEquivProjectiveOfMax (Q := Q) Ω₂ _ hs (twoPieceLoading_vacuumLast_not_lt x u)
  let L := rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ₂) (redWord_relabel σ₂ hs))
  exact restrictSemilinearEquiv (M := ↥L) (N := exteriorProjectiveStd hQ Ω₂ rfl x hx u)
    (leftCoefficientEquiv (Λ := Λ₂) hρ₂ hQ σ₂)
    ((loadingProjectiveLeftEquiv hρ₂ hQ σ₂ hs).trans
      (e.symm.trans (twoRedProjectiveStandardizationEquiv hQ Ω₂ x hx u).symm))

end TwoRed

local notation "swapRed" => Equiv.swap (0 : Fin 2) 1

section FigureFiveGeometry

variable {I : Type} {ν : Multiset I}

private def emptyBlack : Seq (0 : Multiset I) := KLRAlgebra.Seq.ofList [] (by simp)

local notation "vacuum" => SingleRed.insertWord 0 (emptyBlack (I := I))
local notation "m₂" => Multiset.card (stendhalWeight 2 ν)

private def figureFiveLower (u : Seq ν) : Seq (stendhalWeight 2 ν) :=
  Seq.redPerm 1 (Seq.cast (congrArg (stendhalWeight 2) (add_zero ν))
    (twoPieceLoading ν 0 (SingleRed.insertWord ν u) emptyBlack))

private def figureFiveUpper (u : Seq ν) : Seq (stendhalWeight 2 ν) :=
  Seq.redPerm swapRed (Seq.cast (congrArg (stendhalWeight 2) (zero_add ν))
    (twoPieceLoading 0 ν vacuum u))

private theorem ofFn_cast {J : Type} {a b : Multiset J} (h : a = b) (u : Seq a) :
    List.ofFn (Seq.cast h u).lbl = List.ofFn u.lbl := by
  subst b
  rfl

private theorem ofFn_insertWord (u : Seq ν) :
    List.ofFn (SingleRed.insertWord ν u).lbl = .inr 0 :: (List.ofFn u.lbl).map .inl := by
  let z := SingleRed.insertWord ν u
  have hc : (stendhalWeight 1 ν).card = ν.card + 1 := by simp [stendhalWeight]
  have h₀ : z.lbl (Fin.cast hc.symm (0 : Fin (ν.card + 1))) = .inr 0 :=
    SingleRed.insertWord_head ν u
  have h₁ (i : Fin ν.card) : z.lbl (Fin.cast hc.symm i.succ) = .inl (u.lbl i) :=
    SingleRed.insertWord_black ν u i
  change List.ofFn z.lbl = _
  rw [List.ofFn_congr hc z.lbl, List.ofFn_succ, ← List.ofFn_comp']
  exact congrArg₂ List.cons h₀ (congrArg List.ofFn (funext h₁))

private theorem ofFn_emptyBlack : List.ofFn (emptyBlack (I := I)).lbl = [] :=
  List.ofFn_zero

private theorem figureFive_lower_word (u : Seq ν) :
    List.ofFn (figureFiveLower u).lbl = (.inr 0 :: (List.ofFn u.lbl).map .inl) ++ [.inr 1] := by
  rw [figureFiveLower, Seq.redPerm_one, ofFn_cast, ofFn_twoPieceLoading, ofFn_insertWord,
    ofFn_emptyBlack]
  simp [addRedColor, Function.comp_def]

private theorem figureFive_upper_word (u : Seq ν) :
    List.ofFn (figureFiveUpper u).lbl = .inr 1 :: .inr 0 :: (List.ofFn u.lbl).map .inl := by
  rw [figureFiveUpper]
  change List.ofFn (fun i => Sum.map id swapRed
    ((Seq.cast (congrArg (stendhalWeight 2) (zero_add ν))
      (twoPieceLoading 0 ν vacuum u)).lbl i)) = _
  rw [List.ofFn_comp', ofFn_cast, ofFn_twoPieceLoading, ofFn_insertWord, ofFn_emptyBlack]
  change .inr 1 :: .inr 0 :: ((List.ofFn u.lbl).map .inl).map (Sum.map id swapRed) = _
  simp [Function.comp_def]

private theorem figureFive_card : m₂ = ν.card + 2 := by simp [stendhalWeight]

private theorem figureFive_one_lt : 1 < m₂ := by rw [figureFive_card]; omega

private theorem figureFive_pos : 0 < m₂ := by rw [figureFive_card]; omega

private theorem figureFive_upper_zero (u : Seq ν) :
    (figureFiveUpper u).lbl ⟨0, figureFive_pos⟩ = .inr 1 := by
  simpa only [figureFive_upper_word, List.getElem_cons_zero] using
    (List.getElem_ofFn (f := (figureFiveUpper u).lbl) (i := 0)
      (by simpa only [List.length_ofFn] using (figureFive_pos (ν := ν)))).symm

private theorem figureFive_upper_one (u : Seq ν) :
    (figureFiveUpper u).lbl ⟨1, figureFive_one_lt⟩ = .inr 0 := by
  simpa only [figureFive_upper_word, List.getElem_cons_succ, List.getElem_cons_zero] using
    (List.getElem_ofFn (f := (figureFiveUpper u).lbl) (i := 1)
      (by simpa only [List.length_ofFn] using (figureFive_one_lt (ν := ν)))).symm

private theorem ofFn_rotate {J : Type} {n : ℕ} (f : Fin n → J) (hn : 0 < n) :
    List.ofFn (fun j => f (finRotate n j)) = (List.ofFn f).drop 1 ++ [f ⟨0, hn⟩] := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hs (i : Fin p) : finRotate (p + 1) i.castSucc = i.succ :=
    Fin.ext (coe_finRotate_of_ne_last (Fin.castSucc_ne_last i))
  rw [List.ofFn_succ' (f := fun j => f (finRotate (p + 1) j)), List.concat_eq_append]
  rw [List.ofFn_succ (f := f)]
  simp only [hs, finRotate_last, List.drop_succ_cons, List.drop_zero]
  rfl

private theorem figureFive_edge (u : Seq ν) :
    EdgeBraid figureFive_pos 1 (finRotate m₂)⁻¹ (figureFiveLower u) (figureFiveUpper u) := by
  have hmove : (finRotate m₂)⁻¹ • figureFiveUpper u = figureFiveLower u := by
    apply Subtype.ext
    apply List.ofFn_injective
    have hlabels : ((finRotate m₂)⁻¹ • figureFiveUpper u).lbl =
        fun j => (figureFiveUpper u).lbl (finRotate m₂ j) := by
      funext j
      rw [lbl_smul, inv_inv]
    change List.ofFn ((finRotate m₂)⁻¹ • figureFiveUpper u : KLR.Seq (stendhalWeight 2 ν)).lbl =
      List.ofFn (figureFiveLower u).lbl
    rw [hlabels, ofFn_rotate _ figureFive_pos, figureFive_upper_zero, figureFive_upper_word,
      figureFive_lower_word]
    simp only [List.drop_succ_cons, List.drop_zero]
  have hlast {n : ℕ} (hn : 0 < n) : finRotate n ⟨n - 1, by omega⟩ = ⟨0, hn⟩ := by
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact finRotate_last'
  refine ⟨hmove, ?_, ?_⟩
  · rw [← hmove, lbl_smul, inv_inv, hlast (figureFive_pos (ν := ν))]
    exact figureFive_upper_zero u
  · intro j hj
    have hshift {n : ℕ} (hn : 0 < n) (i : Fin n) (hi : i.val ≠ n - 1) :
        (finRotate n i).val = i.val + 1 := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact coe_finRotate_of_ne_last (fun h => hi (congrArg Fin.val h))
    rw [inv_inv]
    exact hshift figureFive_pos j hj

end FigureFiveGeometry

section DerivedFigureFive

open CategoryTheory DG
open scoped DG.DegreeZero

universe w

variable {I k : Type} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I} (hQ : KLRSymm Q)
  {Λ₂ : Fin 2 → I →₀ ℕ}
  {ρ₂ : Perm (Fin (Multiset.card (stendhalWeight 2 ν))) → List ℕ}
  (hρ₂ : TypeA.IsReducedChoice ρ₂)

local notation "vacuum" => SingleRed.insertWord 0 (emptyBlack (I := I))

private def inDegreeZeroIso {A M N : Type} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
    DGModuleCat.of A (InDegreeZero M) ≅ DGModuleCat.of A (InDegreeZero N) :=
  DGModuleCat.isoOfDGModuleEquiv (DGModuleEquiv.ofDegreeZero
    (show InDegreeZero M ≃ₗ[A] InDegreeZero N from e)
    (fun hx hn => ((InDegreeZero.mem_grading_iff _).1 hx).resolve_left hn)
    (InDegreeZero.d_apply _) InDegreeZero.mem_grading_zero (InDegreeZero.d_apply _))

private abbrev moduleInDegreeZero {A : Type} [Ring A] (M : ModuleCat.{0} A) : DGModuleCat A :=
  DGModuleCat.of A (InDegreeZero M)

local notation "R₀" => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ₂) (ν := ν) [0, 1])ᵐᵒᵖ
local notation "R₁" => (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ₂) (ν := ν) [1, 0])ᵐᵒᵖ
local notation "P₀" u:arg => exteriorStandardizationRight (Λ₂ := Λ₂) (σ₂ := 1) hQ hρ₂
  (add_zero ν) (SingleRed.insertWord ν u) emptyBlack
local notation "P₁" u:arg => exteriorStandardizationRight (Λ₂ := Λ₂) (σ₂ := swapRed) hQ hρ₂
  (zero_add ν) vacuum u

/-- Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9, Figure 5, for two red strands
and with the internal grading forgotten. The braiding functor of Definition 6.6 takes
`S(P_u ⊠ P_∅)` to `S(P_∅ ⊠ P_u)` in cohomological degree zero, with each
standardization read as a right module over its own red-order corner. -/
def braidingFunctorObjFigureFiveStandardizationIso (u : Seq ν)
    [HasDerivedCategory.{w} R₀] [HasDerivedCategory.{w} R₁] :
    (braidingFunctor.{w} k Q Λ₂ ν [0, 1] [1, 0]).obj
        (DG.DerivedCategory.Q.obj (moduleInDegreeZero (A := R₀) (P₀ u))) ≅
      DG.DerivedCategory.Q.obj (moduleInDegreeZero (A := R₁) (P₁ u)) := by
  have hs := (figureFive_edge u).redWord_source_twoRed figureFive_one_lt
    (figureFive_upper_zero u) (figureFive_upper_one u)
  let L := rIdeal (violLoadingIdem (k := k) (Q := Q) (Λ := Λ₂) hs)
  let U := ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ₂) (figureFiveUpper u) [1, 0]
  let X₀ : ModuleCat.{0} R₀ := P₀ u
  let X₁ : ModuleCat.{0} R₁ := P₁ u
  let eₛ := inDegreeZeroIso (A := R₀) (M := ↥L) (N := ↥X₀)
    (loadingProjectiveEquivExteriorStandardization (Λ₂ := Λ₂) (σ₂ := 1)
      hQ hρ₂ (add_zero ν) (SingleRed.insertWord ν u) emptyBlack)
  let eₜ := inDegreeZeroIso (A := R₁) (M := U) (N := ↥X₁)
    (loadingStandardEquivExteriorStandardization (Λ₂ := Λ₂) (σ₂ := swapRed)
      hQ hρ₂ (zero_add ν) vacuum u)
  exact (braidingFunctor.{w} k Q Λ₂ ν [0, 1] [1, 0]).mapIso (DG.DerivedCategory.Q.mapIso eₛ.symm) ≪≫
    braidingFunctorObjFigureFiveIso hρ₂ hQ figureFive_one_lt (figureFive_upper_zero u)
      (figureFive_upper_one u) (figureFive_edge u) ≪≫
    DG.DerivedCategory.Q.mapIso eₜ

end DerivedFigureFive

end Categorification.Stendhal.BraidedStendhalAlgebra
