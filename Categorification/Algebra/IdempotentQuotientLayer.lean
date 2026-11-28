/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Layers of a filtration after cutting by an idempotent

Let `p` be an idempotent endomorphism of a module `V` and `F ≤ G` submodules preserved by `p`.
In the quotient `V / ker p` the images `G'`, `F'` of `G`, `F` give the layer `G' / F'`. It is the
layer `G / F` cut down by `p`:

* the map `G / F → G' / F'` induced by the projection is surjective
  (`idemLayerMap_surjective`), with kernel the kernel of the action `p̄` of `p` on `G / F`
  (`ker_idemLayerMap`);
* hence `G' / F' ≅ (G / F) / ker p̄ ≅ p̄ (G / F)` (`idemLayerEquiv`, `idemLayerRangeEquiv`);
* the map commutes with every endomorphism of `V` preserving `ker p`, `G` and `F`
  (`idemLayerMap_act`).

This passes the layers of the Mackey filtration of an induced module to the partial
standardization, the quotient by the loadings with red strands out of order. It is used for the
trace half of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Lemma 7.19.
-/

namespace Categorification

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- The layer `G / F` of two submodules (`F` read inside `G`). -/
abbrev SubLayer (G F : Submodule k V) : Type _ := G ⧸ F.comap G.subtype

section Act

variable (z : V →ₗ[k] V) {G F : Submodule k V}

/-- The action on the layer `G / F` of an endomorphism preserving `G` and `F`. -/
def subLayerAct (hG : ∀ v ∈ G, z v ∈ G) (hF : ∀ v ∈ F, z v ∈ F) :
    SubLayer G F →ₗ[k] SubLayer G F :=
  Submodule.mapQ _ _ ((z.comp G.subtype).codRestrict G fun v => hG v v.2) fun _ hv => hF _ hv

theorem subLayerAct_mk (hG : ∀ v ∈ G, z v ∈ G) (hF : ∀ v ∈ F, z v ∈ F) (v : G) :
    subLayerAct z hG hF (Submodule.Quotient.mk v) = Submodule.Quotient.mk ⟨z v, hG v v.2⟩ :=
  rfl

end Act

variable (p : V →ₗ[k] V) {G F : Submodule k V}

/-- The image of a submodule in `V / ker p`. -/
abbrev idemImage (G : Submodule k V) : Submodule k (V ⧸ LinearMap.ker p) :=
  G.map (LinearMap.ker p).mkQ

/-- The map from the layer `G / F` to the layer of the images in `V / ker p`. -/
def idemLayerMap : SubLayer G F →ₗ[k] SubLayer (idemImage p G) (idemImage p F) :=
  Submodule.mapQ _ _
    ((((LinearMap.ker p).mkQ).comp G.subtype).codRestrict (idemImage p G)
      fun v => Submodule.mem_map_of_mem v.2)
    fun _ hv => Submodule.mem_map_of_mem hv

theorem idemLayerMap_mk (v : G) :
    idemLayerMap p (F := F) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨(LinearMap.ker p).mkQ v, Submodule.mem_map_of_mem v.2⟩ :=
  rfl

theorem idemLayerMap_surjective : Function.Surjective (idemLayerMap p (G := G) (F := F)) := by
  intro y
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  exact ⟨Submodule.Quotient.mk ⟨v, hv⟩, rfl⟩

variable (hp : ∀ v, p (p v) = p v) (hG : ∀ v ∈ G, p v ∈ G) (hF : ∀ v ∈ F, p v ∈ F)

include hp hG hF in
/-- **The kernel of the layer map** is the kernel of the action of `p` on the layer. -/
theorem ker_idemLayerMap :
    LinearMap.ker (idemLayerMap p (G := G) (F := F)) = LinearMap.ker (subLayerAct p hG hF) := by
  ext y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker, LinearMap.mem_ker, idemLayerMap_mk, subLayerAct_mk,
    Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.mem_comap]
  change (LinearMap.ker p).mkQ (v : V) ∈ idemImage p F ↔ p v ∈ F
  constructor
  · rintro hv
    obtain ⟨f, hf, he⟩ := Submodule.mem_map.1 hv
    have h0 : p (f - v) = 0 := by
      have := (Submodule.Quotient.eq (LinearMap.ker p)).1 he
      exact LinearMap.mem_ker.1 this
    have h1 : p v = p f := by rw [map_sub, sub_eq_zero] at h0; exact h0.symm
    rw [h1]
    exact hF f hf
  · intro hv
    refine Submodule.mem_map.2 ⟨p v, hv, ?_⟩
    refine (Submodule.Quotient.eq (LinearMap.ker p)).2 (LinearMap.mem_ker.2 ?_)
    rw [map_sub, hp, sub_self]

/-- **The layer after cutting by `p`** is the layer cut down by the action of `p`:
`G' / F' ≅ (G / F) / ker p̄`. -/
noncomputable def idemLayerEquiv :
    (SubLayer G F ⧸ LinearMap.ker (subLayerAct p hG hF)) ≃ₗ[k]
      SubLayer (idemImage p G) (idemImage p F) :=
  (Submodule.quotEquivOfEq _ _ (ker_idemLayerMap p hp hG hF).symm).trans
    ((idemLayerMap p).quotKerEquivOfSurjective (idemLayerMap_surjective p))

theorem idemLayerEquiv_mk (y : SubLayer G F) :
    idemLayerEquiv p hp hG hF (Submodule.Quotient.mk y) = idemLayerMap p y :=
  rfl

/-- The same layer as the image `p̄ (G / F)`. -/
noncomputable def idemLayerRangeEquiv :
    LinearMap.range (subLayerAct p hG hF) ≃ₗ[k] SubLayer (idemImage p G) (idemImage p F) :=
  ((subLayerAct p hG hF).quotKerEquivRange).symm.trans (idemLayerEquiv p hp hG hF)

theorem idemLayerRangeEquiv_apply (y : SubLayer G F) :
    idemLayerRangeEquiv p hp hG hF ⟨subLayerAct p hG hF y, y, rfl⟩ = idemLayerMap p y := by
  rw [idemLayerRangeEquiv, LinearEquiv.trans_apply]
  have : (subLayerAct p hG hF).quotKerEquivRange.symm ⟨subLayerAct p hG hF y, y, rfl⟩ =
      Submodule.Quotient.mk y :=
    (subLayerAct p hG hF).quotKerEquivRange.symm_apply_eq.2 rfl
  rw [this, idemLayerEquiv_mk]

omit hp hG hF

/-- **The layer map commutes with the actions** of an endomorphism `z` of `V` that preserves
`ker p`, `G` and `F`. -/
theorem idemLayerMap_act (z : V →ₗ[k] V) (hK : ∀ v ∈ LinearMap.ker p, z v ∈ LinearMap.ker p)
    (hzG : ∀ v ∈ G, z v ∈ G) (hzF : ∀ v ∈ F, z v ∈ F) (y : SubLayer G F) :
    idemLayerMap p (subLayerAct z hzG hzF y) =
      subLayerAct ((LinearMap.ker p).mapQ (LinearMap.ker p) z hK)
        (fun w hw => by
          obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
          exact Submodule.mem_map.2 ⟨z v, hzG v hv, rfl⟩)
        (fun w hw => by
          obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
          exact Submodule.mem_map.2 ⟨z v, hzF v hv, rfl⟩)
        (idemLayerMap p y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

end Categorification
