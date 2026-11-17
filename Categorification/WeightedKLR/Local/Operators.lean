/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Chambers
import Categorification.WeightedKLR.Local.StarRelabel
import Categorification.WeightedKLR.GalleryRep

/-!
# Polynomial operators in a local chart

Supporting operator identifications for roadmap A of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19. Renaming strands along the local refinement intertwines dots,
divided differences, loop crossings, and relabellings. These are the polynomial
representation operators used in the local-chart comparison.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The identification of dot polynomial rings induced by the strand identification. -/
def polyEquiv (p : Strand ν → 𝕜) : PolyRing (weight p) k ≃ₐ[k] PolyRing ν k :=
  renameEquiv k (strandEquiv p)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem polyEquiv_apply (p : Strand ν → 𝕜) (f : PolyRing (weight p) k) :
    polyEquiv p f = rename (strandEquiv p) f := rfl

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem polyEquiv_X (p : Strand ν → 𝕜) (s : Strand (weight p)) :
    polyEquiv (k := k) p (X s) = X (strandEquiv p s) :=
  rename_X _ _

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_ddiff (p : Strand ν → 𝕜) {s t : Strand (weight p)}
    (hst : s ≠ t) (f : PolyRing (weight p) k) :
    polyEquiv p (ddiff s t f) = ddiff (strandEquiv p s) (strandEquiv p t) (polyEquiv p f) :=
  rename_ddiff (strandEquiv p).injective hst f

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_rename_swap (p : Strand ν → 𝕜) (s t : Strand (weight p))
    (f : PolyRing (weight p) k) :
    polyEquiv p (rename (swap s t) f) =
      rename (swap (strandEquiv p s) (strandEquiv p t)) (polyEquiv p f) := by
  simp only [polyEquiv_apply, rename_rename]
  rw [(strandEquiv p).injective.swap_comp]

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_loopFactor (p : Strand ν → 𝕜) (P : MvPolynomial (Fin 2) k)
    (s t : Strand (weight p)) :
    polyEquiv p (loopFactor P s t) = loopFactor P (strandEquiv p s) (strandEquiv p t) := by
  rw [polyEquiv_apply, loopFactor, ← AlgHom.comp_apply, comp_aeval, loopFactor]
  congr 2
  funext j
  fin_cases j <;> simp

omit [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_psiOp (p : Strand ν → 𝕜) {s t : Strand (weight p)}
    (hst : s ≠ t) (f : PolyRing (weight p) k) :
    polyEquiv p (psiOp (graph Γ p) s t f) =
      psiOp Γ (strandEquiv p s) (strandEquiv p t) (polyEquiv p f) := by
  have hl : (graph Γ p).loop s.1 = Γ.loop (strandEquiv p s).1 := by
    change Γ.loop s.label.1 = Γ.loop (strandEquiv p s).label
    rw [strandEquiv_colour]
  cases h : Γ.loop (strandEquiv p s).1 with
  | none =>
    rw [psiOp_of_none (hl.trans h), psiOp_of_none h]
    exact polyEquiv_ddiff p hst f
  | some P =>
    rw [psiOp_of_some (hl.trans h), psiOp_of_some h, map_mul, map_sub,
      polyEquiv_loopFactor, polyEquiv_rename_swap]

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_ren (p : Strand ν → 𝕜) (g : ColPerm (weight p))
    (f : PolyRing (weight p) k) :
    polyEquiv p (ren g f) = ren (perm p g) (polyEquiv p f) := by
  simp only [ren, AlgHom.toLinearMap_apply, polyEquiv_apply, rename_rename]
  have h : (strandEquiv p) ∘ g.1 = (perm p g).1 ∘ (strandEquiv p) :=
    funext fun s => (perm_apply p g s).symm
  exact congrArg (fun φ : Strand (weight p) → Strand ν => rename φ f) h

omit [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_wallFactor (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p)) :
    polyEquiv p w.factor = (wall p w).factor := by
  exact polyEquiv_loopFactor p (Γ.Q w.edge.1) w.src w.tgt

omit [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_wallOp (p : Strand ν → 𝕜) (w : Wall (graph Γ p) (weight p))
    (σ σ' : Bool) (f : PolyRing (weight p) k) :
    polyEquiv p (wallOp w σ σ' f) = wallOp (wall p w) σ σ' (polyEquiv p f) := by
  unfold wallOp
  split_ifs
  · change polyEquiv p (w.factor * f) = (wall p w).factor * polyEquiv p f
    rw [map_mul, polyEquiv_wallFactor]
  · rfl

omit [IsStrictOrderedRing 𝕜] in
theorem polyEquiv_hypOp (p : Strand ν → 𝕜) (h : Hyp (graph Γ p) (weight p))
    (σ σ' : Bool) (f : PolyRing (weight p) k) :
    polyEquiv p (hypOp (graph Γ p) h σ σ' f) = hypOp Γ (hyp p h) σ σ' (polyEquiv p f) := by
  cases h with
  | inl w => exact polyEquiv_wallOp p w σ σ' f
  | inr d =>
    cases σ with
    | false => exact polyEquiv_psiOp p d.fst_ne_snd.symm f
    | true => exact polyEquiv_psiOp p d.fst_ne_snd f

theorem polyEquiv_stepOp (p : Strand ν → 𝕜)
    (C D : FullChamber (graph Γ p) (weight p)) (f : PolyRing (weight p) k) :
    polyEquiv p (stepOp (graph Γ p) C D f) =
      stepOp Γ (chamber p C) (chamber p D) (polyEquiv p f) := by
  classical
  by_cases ha : ∃ h, C.Adjacent D h
  · obtain ⟨h, hh⟩ := ha
    rw [stepOp_eq hh, stepOp_eq ((adjacent_chamber_iff p C D h).2 hh), chamber_hyp]
    exact polyEquiv_hypOp p h _ _ f
  · have hn : ∀ h, ¬ C.Adjacent D h := not_exists.1 ha
    rw [stepOp_of_not hn, stepOp_of_not (not_adjacent_chamber p hn),
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

omit [IsStrictOrderedRing 𝕜] in
/-- Pulling a relabelled configuration back to tangent coordinates commutes with relabelling. -/
theorem act_sub_base (p : Strand ν → 𝕜) (g : ColPerm (weight p)) (q : Strand ν → 𝕜) :
    (fun s => act (perm p g) q (strandEquiv p s) - p (strandEquiv p s)) =
      act g (fun s => q (strandEquiv p s) - p (strandEquiv p s)) := by
  funext s
  have hi : (perm p g).1.symm (strandEquiv p s) = strandEquiv p (g.1.symm s) := by
    have h := perm_apply p g⁻¹ s
    rw [map_inv] at h
    exact h
  change q ((perm p g).1.symm (strandEquiv p s)) - p (strandEquiv p s) =
    q (strandEquiv p (g.1.symm s)) - p (strandEquiv p (g.1.symm s))
  rw [hi, strandEquiv_coord p s, strandEquiv_coord p (g.1.symm s)]
  have hp : (g.1.symm s).label.2 = s.label.2 :=
    congrArg (fun a : (weight p).support => a.1.2) ((g⁻¹).2 s)
  rw [hp]

private theorem isGeneric_sub_base (p : Strand ν → 𝕜) {q : Strand ν → 𝕜}
    (hq : IsGeneric Γ q) :
    IsGeneric (graph Γ p) (fun s => q (strandEquiv p s) - p (strandEquiv p s)) := by
  intro h
  have hv : h.val (fun s => q (strandEquiv p s) - p (strandEquiv p s)) =
      (hyp p h).val q := (linearization Γ p).val_sub_base h q
  rw [hv]
  exact hq _

private theorem localChamber_ofPoint (p : Strand ν → 𝕜) (q : Strand ν → 𝕜)
    (hq : IsGeneric Γ q) :
    (linearization Γ p).localChamber (FullChamber.ofPoint q hq) =
      FullChamber.ofPoint (fun s => q (strandEquiv p s) - p (strandEquiv p s))
        (isGeneric_sub_base p hq) := by
  apply Subtype.ext
  funext h
  exact congrArg (fun x : 𝕜 => decide (0 < x)) ((linearization Γ p).val_sub_base h q).symm

/-- Restriction to the incident hyperplanes commutes with point-fixing relabellings. -/
theorem localChamber_perm_smul (p : Strand ν → 𝕜) (g : ColPerm (weight p))
    (C : FullChamber Γ ν) :
    (linearization Γ p).localChamber (perm p g • C) =
      g • (linearization Γ p).localChamber C := by
  obtain ⟨q, hq, rfl⟩ := C.exists_eq_ofPoint
  rw [FullChamber.smul_ofPoint (perm p g) hq, localChamber_ofPoint p,
    localChamber_ofPoint p, FullChamber.smul_ofPoint g]
  apply Subtype.ext
  exact congrArg (fullSigns (Γ := graph Γ p)) (act_sub_base p g q)

/-- Relabelling a local chamber is the same as relabelling its image in the original star. -/
theorem perm_smul_chamber (p : Strand ν → 𝕜) (g : ColPerm (weight p))
    (C : FullChamber (graph Γ p) (weight p)) :
    perm p g • chamber p C = chamber p (g • C) := by
  have hi : (perm p g • chamber p C).Incident p := by
    simpa only [perm_fix_config] using (chamber_incident p C).smul (perm p g)
  have h₁ := (linearization Γ p).chamber_localChamber (perm p g • chamber p C) hi
  have h₂ : (linearization Γ p).localChamber (perm p g • chamber p C) = g • C :=
    (localChamber_perm_smul p g (chamber p C)).trans
      (congrArg (fun D => g • D) ((linearization Γ p).localChamber_chamber C))
  exact h₁.symm.trans (congrArg (linearization Γ p).chamber h₂)

end Categorification.WeightedKLR.Local
