/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStandardization
import Categorification.WeightedKLR.RedStrands.GradedBraidingBimodule
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip

set_option backward.isDefEq.respectTransparency false

/-!
# The corner `e_κ V e_κ` as a subspace of `V`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14. For the red order `κ = σ(1, …, ℓ)`, the corner `e_κ V e_κ` is the tensor product
algebra `T^{λ∘σ}` (`violCornerRedPermTensorEquiv`). We read this isomorphism as an injective,
multiplicative, `k`-linear map `ψ : T^{λ∘σ} → V` with image `e_κ V e_κ` (`cornerEmbed`), which
sends the idempotent of a red-ordered loading `s` to the idempotent of the relabelled loading
`σ • s` (`cornerEmbed_seqIdem`), and we transport the flip of `V` to an anti-involution of
`T^{λ∘σ}` (`cornerFlip`).

## Main results

* `cornerEmbed`: `ψ : T^{λ∘σ} → V`, with `cornerEmbed_mul`, `cornerEmbed_injective`,
  `exists_cornerEmbed_eq`.
* `cornerEmbed_seqIdem`: `ψ (e(s)) = e(σ • s)`.
* `cornerFlip`: the anti-involution of `T^{λ∘σ}` with `ψ (cornerFlip t) = flip (ψ t)`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv MulOpposite

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "T" => TensorProductAlgebra k Q (Λ ∘ σ) ν
local notation "V" => ViolQuotient k Q Λ ν
local notation "P" => violMk k Q Λ ν (redProj k Q Λ ν (List.map σ (List.finRange ℓ)))
local notation "φ" => violCornerRedPermTensorEquiv (Λ₀ := Λ) hρ hQ σ

private theorem violFlip_mul' (a b : V) : violFlip (a * b) = violFlip b * violFlip a :=
  congrArg unop (map_mul (violFlipHom k Q Λ ν) a b)

theorem cornerEmbed_smul (c : k) (t : T) :
    ((φ).symm (c • t)).1 = c • ((φ).symm t).1 := by
  rw [Algebra.smul_def, map_mul]
  change ((φ).symm (algebraMap k T c)).1 * ((φ).symm t).1 = _
  have h : ((φ).symm (algebraMap k T c)).1 = algebraMap k V c * P := by
    change violRedPermEquiv σ (fun _ => rfl)
      ((violCornerEquiv (Λ := Λ ∘ σ) hρ hQ).symm (algebraMap k T c)).1 = _
    have h0 : ((violCornerEquiv (Λ := Λ ∘ σ) hρ hQ).symm (algebraMap k T c)).1 =
        algebraMap k (ViolQuotient k Q (Λ ∘ σ) ν) c *
          violMk k Q (Λ ∘ σ) ν (redProj k Q (Λ ∘ σ) ν (List.finRange ℓ)) :=
      violCornerEquiv_symm_algebraMap_val hρ hQ c
    refine (congrArg (violRedPermEquiv σ (fun _ => rfl)) h0).trans ?_
    rw [map_mul]
    erw [AlgEquiv.commutes]
    erw [violRedPermEquiv_violMk, redPermAlgEquiv_redProj]
  obtain ⟨r, hr⟩ := ((φ).symm t).2
  rw [h, Algebra.smul_def, mul_assoc]
  congr 1
  rw [← hr]
  change P * (P * r * P) = P * r * P
  rw [← mul_assoc, ← mul_assoc, (isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) κ).map (violMk k Q Λ ν) |>.eq]

/-- The corner `e_κ V e_κ ≅ T^{λ∘σ}` as a map `T^{λ∘σ} → V`. -/
def cornerEmbed : T →ₗ[k] V where
  toFun t := ((φ).symm t).1
  map_add' a b := by rw [map_add]; rfl
  map_smul' c t := cornerEmbed_smul hρ hQ σ c t

theorem cornerEmbed_apply (t : T) : cornerEmbed (Λ := Λ) hρ hQ σ t = ((φ).symm t).1 := rfl

theorem cornerEmbed_mul (a b : T) :
    cornerEmbed (Λ := Λ) hρ hQ σ (a * b) = cornerEmbed (Λ := Λ) hρ hQ σ a * cornerEmbed (Λ := Λ) hρ hQ σ b := by
  rw [cornerEmbed_apply, map_mul]; rfl

theorem cornerEmbed_injective : Function.Injective (cornerEmbed (Λ := Λ) hρ hQ σ) := fun _ _ h =>
  (φ).symm.injective (Subtype.ext h)

theorem cornerEmbed_mem (t : T) :
    P * cornerEmbed (Λ := Λ) hρ hQ σ t * P = cornerEmbed (Λ := Λ) hρ hQ σ t := by
  obtain ⟨r, hr⟩ := ((φ).symm t).2
  rw [cornerEmbed_apply, ← hr]
  have hP := ((isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ).map
    (violMk k Q Λ ν)).eq
  change P * (P * r * P) * P = P * r * P
  simp only [← mul_assoc, hP]
  rw [mul_assoc _ P P, hP]

theorem exists_cornerEmbed_eq {v : V} (hv : P * v * P = v) :
    ∃ t : T, cornerEmbed (Λ := Λ) hρ hQ σ t = v :=
  ⟨φ ⟨v, v, hv⟩, by rw [cornerEmbed_apply, RingEquiv.symm_apply_apply]⟩

theorem cornerEmbed_one : cornerEmbed (Λ := Λ) hρ hQ σ 1 = P := by
  rw [cornerEmbed_apply, map_one]; rfl

/-- `ψ` sends the idempotent of a red-ordered loading `s` to that of `σ • s`. -/
theorem cornerEmbed_seqIdem {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s) :
    cornerEmbed (Λ := Λ) hρ hQ σ (seqIdem Q (Λ ∘ σ) s hs) =
      violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (Seq.redPerm σ s))) := by
  have h := leftCoefficientEquiv_loadingIdem (Λ := Λ) hρ hQ σ hs
  change tensorFlip (φ (violLoadingIdem (redWord_relabel σ hs))) = _ at h
  have h' : φ (violLoadingIdem (redWord_relabel σ hs)) = seqIdem Q (Λ ∘ σ) s hs := by
    rw [← tensorFlip_tensorFlip (φ _), h]
    exact tensorFlip_mk_e s hs
  rw [cornerEmbed_apply, ← h', RingEquiv.symm_apply_apply]
  rfl

theorem violFlip_cornerEmbed_mem (t : T) :
    P * violFlip (cornerEmbed (Λ := Λ) hρ hQ σ t) * P = violFlip (cornerEmbed (Λ := Λ) hρ hQ σ t) := by
  have hP : violFlip P = P := by rw [violFlip_violMk, flip_redProj]
  conv_rhs => rw [← cornerEmbed_mem hρ hQ σ t]
  rw [violFlip_mul', violFlip_mul', hP, mul_assoc]

theorem cornerEmbed_symm {v : V} (hv : P * v * P = v) :
    cornerEmbed (Λ := Λ) hρ hQ σ (φ ⟨v, v, hv⟩) = v := by
  rw [cornerEmbed_apply, RingEquiv.symm_apply_apply]

private theorem violFlip_add' (a b : V) : violFlip (a + b) = violFlip a + violFlip b :=
  congrArg unop (map_add (violFlipHom k Q Λ ν) a b)

private theorem violFlip_smul' (c : k) (a : V) : violFlip (c • a) = c • violFlip a :=
  congrArg unop (map_smul (violFlipHom k Q Λ ν) c a)

/-- The flip of `V`, transported to `T^{λ∘σ}` along `ψ`. -/
def cornerFlip : T →ₗ[k] T where
  toFun t := φ ⟨violFlip (cornerEmbed (Λ := Λ) hρ hQ σ t), _, violFlip_cornerEmbed_mem hρ hQ σ t⟩
  map_add' a b := by
    apply cornerEmbed_injective hρ hQ σ
    rw [cornerEmbed_symm, LinearMap.map_add (cornerEmbed (Λ := Λ) hρ hQ σ) (φ _) (φ _),
      cornerEmbed_symm, cornerEmbed_symm, LinearMap.map_add (cornerEmbed (Λ := Λ) hρ hQ σ) a b,
      violFlip_add']
    all_goals exact violFlip_cornerEmbed_mem hρ hQ σ _
  map_smul' c t := by
    apply cornerEmbed_injective hρ hQ σ
    rw [RingHom.id_apply, cornerEmbed_symm,
      LinearMap.map_smul (cornerEmbed (Λ := Λ) hρ hQ σ) c (φ _), cornerEmbed_symm,
      LinearMap.map_smul (cornerEmbed (Λ := Λ) hρ hQ σ) c t, violFlip_smul']
    all_goals exact violFlip_cornerEmbed_mem hρ hQ σ _

theorem cornerEmbed_cornerFlip (t : T) :
    cornerEmbed (Λ := Λ) hρ hQ σ (cornerFlip (Λ := Λ) hρ hQ σ t) = violFlip (cornerEmbed (Λ := Λ) hρ hQ σ t) := by
  change cornerEmbed (Λ := Λ) hρ hQ σ (φ _) = _
  rw [cornerEmbed_apply, RingEquiv.symm_apply_apply]

theorem cornerFlip_mul (a b : T) :
    cornerFlip (Λ := Λ) hρ hQ σ (a * b) = cornerFlip (Λ := Λ) hρ hQ σ b * cornerFlip (Λ := Λ) hρ hQ σ a := by
  apply cornerEmbed_injective hρ hQ σ
  rw [cornerEmbed_mul, cornerEmbed_cornerFlip, cornerEmbed_cornerFlip, cornerEmbed_cornerFlip,
    cornerEmbed_mul, violFlip_mul']

theorem cornerFlip_cornerFlip (t : T) : cornerFlip (Λ := Λ) hρ hQ σ (cornerFlip (Λ := Λ) hρ hQ σ t) = t := by
  apply cornerEmbed_injective hρ hQ σ
  rw [cornerEmbed_cornerFlip, cornerEmbed_cornerFlip, violFlip_violFlip]

end Categorification.Stendhal.BraidedStendhalAlgebra
