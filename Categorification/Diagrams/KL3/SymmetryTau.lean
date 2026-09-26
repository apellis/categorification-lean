/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryOmega

/-!
# The rotation `τ̃` of `U` by `180°`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.3.2,
paragraph "Rotation by `180°` (taking right adjoints)", eq. (3.46), and Remark 3.19.

KL III: "The symmetry of rotation by `180°` can also be realized by the 2-functor that sends a
1-morphism `1_μ x 1_λ` to its right adjoint `1_λ y 1_μ` and each 2-morphism
`ζ : 1_μ x 1_λ ⇒ 1_μ x' 1_λ` to its mate under the adjunctions […] That is, `ζ` is mapped to its
right dual `ζ*`. […] `τ̃ : U → U^coop`, `1_μ E_{s_1} ⋯ E_{s_m} 1_λ {t} ↦ 1_λ E_{-s_m} ⋯ E_{-s_1}
1_μ {-t + t'}`, `ζ ↦ ζ*`, where the degree shift `t'` […] ensures that `τ̃` is degree
preserving."

## Formalization

On each Hom category `U(a, b)`, `τ̃` is the library's rotation functor
`Pivotal.rotateFunctor a b : (a ⟶ b)ᵒᵖ ⥤ (b ⟶ a)` for the pivotal structure `pivotal RD k` of
`U` (duals: the dual words; biadjunctions: nested cups and caps; all 2-morphisms cyclic,
`isCyclic`). No relations need to be checked: mates are always well defined. The rotation
calculus of `Categorification.Diagrams.KL3.Rotation` computes it:

* `tauU_eq_mateL`, `rotU_eq_tauU`: `τ̃` is the normal-form rotation `rotU`;
* `rotU_dg`: on normal-form diagrams it reverses the order of the layers and rotates every
  generator (`rotSh`: the dot on `l` becomes the dot on `l*`, the upward and downward crossings
  are exchanged, cups become caps and caps become cups);
* `rotU_rotU`: `τ̃² = 1` (up to `x** = x`);
* `rotU_homDeg`: **the degree shift `t'`**: `τ̃` sends a 2-morphism of degree `d` from `E_s 1_μ` to
  `E_t 1_μ` to one of degree `d + t'`, with `t' = deg(nested cups of s) + deg(nested caps of t)`
  (`nCups`, `nCaps`; this is KL III's `t'`, determined by (3.42));
* `rotU_upDot`, `rotU_downDot`, `rotU_upCross`, `rotU_downCross`: the rotations of the dots and
  crossings (the downward generators are the rotations of the upward ones and vice versa,
  KL III (3.3) and `eq_cyclic_cross-gen`).

Remark 3.19 (`τ̃ ψ̃ ω̃ σ̃` fixes all diagrams and only affects the grading shifts) is the content of
`omegaL_eq_phi` (`Categorification.Diagrams.KL3.SymmetryOmega`), which shows `ω̃ = ψ̃ τ̃ σ̃` on
diagrams.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Opposite

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- **The rotation `τ̃` of KL III (3.46)** on the Hom category `U(a, b)`: the library's rotation
functor for the pivotal structure of `U`, `x ↦ x*`, `ζ ↦ ζ*` (the right mate). -/
def tauU (a b : U RD k) : (a ⟶ b)ᵒᵖ ⥤ (b ⟶ a) :=
  @Pivotal.rotateFunctor (U RD k) _ (pivotal RD k) a b

variable {RD k}

theorem tauU_obj {a b : U RD k} (x : a ⟶ b) :
    (tauU RD k a b).obj (op x) = (pres RD k).dualHom (inv RD).toColourDuality.pivotal x := rfl

/-- `τ̃` is the mate for the nested cups and caps. -/
theorem tauU_eq_mateL {a b : U RD k} {x x' : a ⟶ b} (f : x ⟶ x') :
    ((tauU RD k a b).map f.op : (pres RD k).obj _ ⟶ (pres RD k).obj _) = mateL RD k x x' f := rfl

/-- `rotU` is `τ̃` on normal forms. -/
theorem rotU_eq_tauU (μ ν : X) (s t : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    rotU RD k μ ν s t hs ht f = eqToHom (objEq RD k (dual_obH RD k μ ν t ht).symm) ≫
      ((tauU RD k _ _).map (show obH RD k μ ν s hs ⟶ obH RD k μ ν t ht from f).op :
        (pres RD k).obj _ ⟶ (pres RD k).obj _) ≫
      eqToHom (objEq RD k (dual_obH RD k μ ν s hs)) := rfl

/-! ## Rotations of the generators -/

section Generators

variable (μ : X) (i j : I)

/-- The rotated upward dot is the downward dot (KL III (3.3)). -/
theorem rotU_upDot :
    rotU RD k μ _ [up i] [up i] rfl rfl (dg RD k μ [up i] [up i] [([], .dot (up i), [])]) =
      dg RD k (wt RD μ [up i]) [dn i] [dn i] [([], .dot (dn i), [])] :=
  rotU_dg μ _ _ (by exact ⟨rfl, rfl⟩) rfl rfl

/-- The rotated downward dot is the upward dot. -/
theorem rotU_downDot :
    rotU RD k μ _ [dn i] [dn i] rfl rfl (dg RD k μ [dn i] [dn i] [([], .dot (dn i), [])]) =
      dg RD k (wt RD μ [dn i]) [up i] [up i] [([], .dot (up i), [])] :=
  rotU_dg μ _ _ (by exact ⟨rfl, rfl⟩) rfl rfl

/-- The rotated upward crossing is the downward crossing (KL III `eq_cyclic_cross-gen`). -/
theorem rotU_upCross (h : wt RD μ [up i, up j] = wt RD μ [up j, up i]) :
    rotU RD k μ _ [up i, up j] [up j, up i] rfl h.symm
        (dg RD k μ [up i, up j] [up j, up i] [([], .cross true i j, [])]) =
      dg RD k (wt RD μ [up i, up j]) [dn i, dn j] [dn j, dn i] [([], .cross false i j, [])] :=
  rotU_dg μ _ _ (by exact ⟨rfl, rfl⟩) rfl h.symm

/-- The rotated downward crossing is the upward crossing. -/
theorem rotU_downCross (h : wt RD μ [dn i, dn j] = wt RD μ [dn j, dn i]) :
    rotU RD k μ _ [dn i, dn j] [dn j, dn i] rfl h.symm
        (dg RD k μ [dn i, dn j] [dn j, dn i] [([], .cross false i j, [])]) =
      dg RD k (wt RD μ [dn i, dn j]) [up i, up j] [up j, up i] [([], .cross true i j, [])] :=
  rotU_dg μ _ _ (by exact ⟨rfl, rfl⟩) rfl h.symm

end Generators

/-! ## `τ̃² = 1` -/

theorem TR_dg_list {ν : X} {a a' b b' : List (Letter I)} (ha : a = a') (hb : b = b')
    (L : List (LayerData I)) :
    TR RD k (congrArg (ob RD ν) ha) (congrArg (ob RD ν) hb) (dg RD k ν a' b' L) = dg RD k ν a b L := by
  subst ha hb; exact TR_rfl _

/-- **`τ̃² = 1`**: rotating twice is the identity, up to the identification `t** = t` of
sequences. -/
theorem rotU_rotU (μ ν : X) (s t : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) :
    rotU RD k ν μ (rd t) (rd s) (wt_rd_of RD μ ν t ht) (wt_rd_of RD μ ν s hs)
        (rotU RD k μ ν s t hs ht f) =
      TR RD k (congrArg (ob RD μ) (rd_rd s)) (congrArg (ob RD μ) (rd_rd t)) f := by
  let φ := (rotU RD k ν μ (rd t) (rd s) (wt_rd_of RD μ ν t ht) (wt_rd_of RD μ ν s hs)).comp
    (rotU RD k μ ν s t hs ht)
  have key : φ = TR RD k (congrArg (ob RD μ) (rd_rd s)) (congrArg (ob RD μ) (rd_rd t)) :=
    hom_ext_dg RD k μ _ _ fun ls h => by
      show rotU RD k ν μ (rd t) (rd s) _ _ (rotU RD k μ ν s t hs ht (dg RD k μ s t ls)) = _
      rw [rotU_dg μ ν ls h hs ht, rotU_dg ν μ _ (sChain_rotLs h), rotLs_rotLs]
      exact (TR_dg_list (rd_rd s) (rd_rd t) ls).symm
  exact LinearMap.congr_fun key f

/-! ## The degree shift `t'` -/

section Degree

variable (RD) in
/-- The degree of a normal-form list of layers with rightmost region `μ`. -/
def degLs (μ : X) (ls : List (LayerData I)) : ℤ :=
  (ls.map fun x => sdeg RD (wt RD μ x.2.2) x.2.1).sum

theorem degLs_append (μ : X) (ls ms : List (LayerData I)) :
    degLs RD μ (ls ++ ms) = degLs RD μ ls + degLs RD μ ms := by
  simp [degLs]

theorem degLs_map_whL (ρ : X) (u v : List (Letter I)) (ls : List (LayerData I)) :
    degLs RD ρ (ls.map (whL u v)) = degLs RD (wt RD ρ v) ls := by
  simp only [degLs, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [whL, wt_append]

theorem degree_of_layers {a b : Obj (psig RD)} (D : a ⟶ b) (μ : X) (ls : List (LayerData I))
    (h : Diagram.layers D = layList RD μ ls) : Diagram.degree (deg RD) D = degLs RD μ ls := by
  simp only [Diagram.degree, h, layList, List.map_map, degLs]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact deg_gen RD _ _

/-- The rotation of a diagram of degree `d` has degree `d + t'`, with `t'` the degree of the
nested cups of the source and of the nested caps of the target. -/
theorem rotU_diag_mem (μ ν : X) {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (D : ob RD μ s ⟶ ob RD μ t) :
    rotU RD k μ ν s t hs ht ((pres RD k).diag D) ∈
      (pres RD k).homDeg (deg RD) (ob RD ν (rd t)) (ob RD ν (rd s))
        (Diagram.degree (deg RD) D + degLs RD ν (nCups s) + degLs RD μ (nCaps t)) := by
  obtain ⟨ls, h, rfl⟩ := exists_mkD RD μ D
  rw [← dg_of h, rotU_apply, degree_mkD]
  obtain ⟨D', hD', hl⟩ := isDg_mateL_nf (RD := RD) (k := k) μ ν s t hs ht ls h
  rw [hD']
  have hdeg : Diagram.degree (deg RD) D' =
      (ls.map fun x => sdeg RD (wt RD μ x.2.2) x.2.1).sum + degLs RD ν (nCups s) +
        degLs RD μ (nCaps t) := by
    rw [degree_of_layers D' ν _ hl, rotRaw, degLs_append, degLs_append, degLs_map_whL,
      degLs_map_whL, degLs_map_whL, wt_nil, wt_rd_of RD μ ν s hs]
    show _ = degLs RD μ ls + _ + _
    ring
  have ea := congrArg Bicat.Hom.obj (dual_obH RD k μ ν t ht)
  have eb := congrArg Bicat.Hom.obj (dual_obH RD k μ ν s hs)
  have hc := (pres RD k).diag_cast D' ea eb
  refine Eq.mpr (congrArg (· ∈ _) (show eqToHom _ ≫ (pres RD k).diag D' ≫ eqToHom _ =
    (pres RD k).diag (Diagram.cast D' ea eb) from hc.symm)) ?_
  refine diag_mem_homDeg' ?_
  rw [← hdeg]
  simp [Diagram.degree, Diagram.layers_cast]

/-- **`τ̃` is degree preserving up to the shift `t'`** (KL III (3.46): "the degree shift `t'` […]
ensures that `τ̃` is degree preserving"): the rotation of a 2-morphism `E_s 1_μ ⟶ E_t 1_μ` of
degree `d` has degree `d + t'`, `t' = deg(nested cups of s) + deg(nested caps of t)`. -/
theorem rotU_homDeg (μ ν : X) {s t : List (Letter I)} (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    {f : (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)} {d : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) (ob RD μ s) (ob RD μ t) d) :
    rotU RD k μ ν s t hs ht f ∈ (pres RD k).homDeg (deg RD) (ob RD ν (rd t)) (ob RD ν (rd s))
      (d + degLs RD ν (nCups s) + degLs RD μ (nCaps t)) := by
  obtain ⟨g, hg, rfl⟩ := Presentation.mem_homDeg_iff.1 hf
  clear hf
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨D, hD, rfl⟩ := hx
    rw [Presentation.lin_single, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := rotU_diag_mem (k := k) μ ν hs ht D
    rwa [show Diagram.degree (deg RD) D = d from hD] at this
  | zero => rw [Presentation.lin_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Presentation.lin_add, map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Presentation.lin_smul, map_smul]; exact Submodule.smul_mem _ r hx

end Degree

end Categorification.KL3.Diagram
