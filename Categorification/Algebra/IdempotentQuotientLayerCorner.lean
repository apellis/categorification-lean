/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentQuotientLayer

/-!
# Corners of a layer survive the passage to `V / ker p`

Let `p` be an idempotent endomorphism of `V` and `G ⊇ F` submodules preserved by `p`. If an
endomorphism `q` satisfies `p q = q = q p` (for example `q = e`, `p = Σ_{t ∈ T} e_t` with
`e` one of the orthogonal idempotents `e_t`), then the layer map
`G / F → p(G) / p(F)` (`idemLayerMap`) is injective on the corner `q̄ (G / F)`
(`idemLayerMap_injective_range`), and maps it onto the corner of the image layer
(`range_idemLayerMap_comp_subtype`). So the two corners are isomorphic
(`idemLayerCornerEquiv`).

This is the passage from the layer of the induced module to the layer of the partial
standardization, at one ordered loading, in the trace half of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v3, proof of Lemma 7.19.

## Main results

* `Categorification.subLayerAct_congr`, `Categorification.subLayerAct_comp_of_eq`,
  `Categorification.idemLayerMap_injective_range`, `Categorification.idemCorner_mem_ker`,
  `Categorification.idemCorner_mem_image`,
  `Categorification.range_idemLayerMap_comp_subtype`, `Categorification.idemLayerCornerEquiv`.
-/

namespace Categorification

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  (p q : V →ₗ[k] V) {G F : Submodule k V}

/-- `subLayerAct` depends only on the endomorphism. -/
theorem subLayerAct_congr {z z' : V →ₗ[k] V} (h : z = z') (hG : ∀ v ∈ G, z v ∈ G)
    (hF : ∀ v ∈ F, z v ∈ F) (hG' : ∀ v ∈ G, z' v ∈ G) (hF' : ∀ v ∈ F, z' v ∈ F) :
    subLayerAct z hG hF = subLayerAct z' hG' hF' := by
  subst h
  rfl

/-- If `p q = q`, then `p̄ q̄ = q̄` on every layer preserved by both. -/
theorem subLayerAct_comp_of_eq (hpq : ∀ v, p (q v) = q v) (hG : ∀ v ∈ G, p v ∈ G)
    (hF : ∀ v ∈ F, p v ∈ F) (hqG : ∀ v ∈ G, q v ∈ G) (hqF : ∀ v ∈ F, q v ∈ F)
    (y : SubLayer G F) :
    subLayerAct p hG hF (subLayerAct q hqG hqF y) = subLayerAct q hqG hqF y := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [subLayerAct_mk, subLayerAct_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (hpq v))

variable (hp : ∀ v, p (p v) = p v) (hG : ∀ v ∈ G, p v ∈ G) (hF : ∀ v ∈ F, p v ∈ F)
  (hqG : ∀ v ∈ G, q v ∈ G) (hqF : ∀ v ∈ F, q v ∈ F)

include hp hG hF in
/-- **The layer map is injective on the corner `q̄ (G / F)`** when `p q = q`. -/
theorem idemLayerMap_injective_range (hpq : ∀ v, p (q v) = q v) :
    Function.Injective
      ((idemLayerMap p (G := G) (F := F)).comp
        (LinearMap.range (subLayerAct q hqG hqF)).subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨w, y, rfl⟩ hw
  have h0 : subLayerAct q hqG hqF y ∈ LinearMap.ker (subLayerAct p hG hF) := by
    rw [← ker_idemLayerMap p hp hG hF]
    exact hw
  rw [LinearMap.mem_ker, subLayerAct_comp_of_eq p q hpq hG hF hqG hqF] at h0
  exact Subtype.ext h0

/-- `q` passes to `V / ker p` when `q p = q`. -/
theorem idemCorner_mem_ker (hqp : ∀ v, q (p v) = q v) :
    ∀ v ∈ LinearMap.ker p, q v ∈ LinearMap.ker p := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← hqp v, hv, map_zero, map_zero]

/-- `q` preserves the image in `V / ker p` of a submodule preserved by `q`. -/
theorem idemCorner_mem_image (hqp : ∀ v, q (p v) = q v) {H : Submodule k V}
    (hqH : ∀ v ∈ H, q v ∈ H) :
    ∀ w ∈ idemImage p H,
      (LinearMap.ker p).mapQ (LinearMap.ker p) q (idemCorner_mem_ker p q hqp) w ∈
        idemImage p H := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  exact Submodule.mem_map.2 ⟨q v, hqH v hv, rfl⟩

/-- **The image of the corner** `q̄ (G / F)` under the layer map is the corner of the layer of
`V / ker p` cut by the action of `q`. -/
theorem range_idemLayerMap_comp_subtype (hqp : ∀ v, q (p v) = q v) :
    LinearMap.range
        ((idemLayerMap p (G := G) (F := F)).comp
          (LinearMap.range (subLayerAct q hqG hqF)).subtype) =
      LinearMap.range (subLayerAct ((LinearMap.ker p).mapQ (LinearMap.ker p) q
          (idemCorner_mem_ker p q hqp))
        (idemCorner_mem_image p q hqp hqG) (idemCorner_mem_image p q hqp hqF)) := by
  ext z
  constructor
  · rintro ⟨⟨w, y, rfl⟩, rfl⟩
    exact ⟨idemLayerMap p y, (idemLayerMap_act p q (idemCorner_mem_ker p q hqp) hqG hqF y).symm⟩
  · rintro ⟨z', rfl⟩
    obtain ⟨y, rfl⟩ := idemLayerMap_surjective p z'
    exact ⟨⟨_, y, rfl⟩, idemLayerMap_act p q (idemCorner_mem_ker p q hqp) hqG hqF y⟩

/-- **The corners of the two layers are isomorphic**: `q̄ (G / F) ≅ q̄ (p(G) / p(F))`, by the
layer map, when `p q = q = q p`. -/
noncomputable def idemLayerCornerEquiv (hpq : ∀ v, p (q v) = q v) (hqp : ∀ v, q (p v) = q v) :
    LinearMap.range (subLayerAct q hqG hqF) ≃ₗ[k]
      LinearMap.range (subLayerAct ((LinearMap.ker p).mapQ (LinearMap.ker p) q
          (idemCorner_mem_ker p q hqp))
        (idemCorner_mem_image p q hqp hqG) (idemCorner_mem_image p q hqp hqF)) :=
  (LinearEquiv.ofInjective _ (idemLayerMap_injective_range p q hp hG hF hqG hqF hpq)).trans
    (LinearEquiv.ofEq _ _ (range_idemLayerMap_comp_subtype p q hqG hqF hqp))

theorem idemLayerCornerEquiv_apply (hpq : ∀ v, p (q v) = q v) (hqp : ∀ v, q (p v) = q v)
    (y : LinearMap.range (subLayerAct q hqG hqF)) :
    ((idemLayerCornerEquiv p q hp hG hF hqG hqF hpq hqp y : SubLayer _ _)) =
      idemLayerMap p (y : SubLayer G F) :=
  rfl

end Categorification
