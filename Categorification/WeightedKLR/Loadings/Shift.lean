/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GalleryBasis.Corner

/-!
# Shifting the weighting by a coboundary

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Dependence on choice of loadings", Proposition 2.15.

For a `0`-chain `η : I → 𝕜`, moving every strand of colour `i` by `η_i` to the right turns the
loadings for the weighting `ϑ` into the loadings for the cohomologous weighting
`ϑ'_e = ϑ_e + η_{t(e)} - η_{h(e)}` (`WeightedGraph.shift`), preserving the relative position of
each strand and each ghost: the ghost of a strand `a` of colour `h(e)` sits at `x_a + ϑ_e` and
meets a strand `b` of colour `t(e)` when `x_b - x_a = ϑ_e`. So the two weighted KLR algebras are
isomorphic (`weightedKLRShiftEquiv`).

**Sign of the coboundary.** Webster prints the cohomologous weighting as
`ϑ_e + η_{h(e)} - η_{t(e)}`, with the strands moved to the right. With that sign the wall
equation `x_b - x_a = ϑ_e` changes by `2 (η_{t(e)} - η_{h(e)})` and the chambers are not preserved
(one edge `e`, `ϑ_e = 0`, `η_{h(e)} = 1`, `η_{t(e)} = 0`: the configuration `x_a = 0`,
`x_b = 1` lies on the positive side of the wall for `ϑ`, and after the move `x_a = 1`, `x_b = 1`
lies on the negative side of the wall for `ϑ_e = 1`). The proof in the source moves the ghost of
an edge `e` by `η_{t(e)}`, which is the sign used here; equivalently, the printed formula holds
when the strands are moved to the left. The statement here is the corrected one.

The gallery algebra depends on the weighting only through the set of full chambers, so the
isomorphism is a special case of `galleryWeightEquiv`: two weightings of the same graph with the
same full chambers give isomorphic gallery algebras, and isomorphic weighted KLR algebras
(`weightedKLRWeightEquiv`).

## Main results

* `WeightedGraph.withWeight`, `WeightedGraph.shift`.
* `galleryWeightEquiv`, `weightedKLRWeightEquiv`: same full chambers, isomorphic algebras.
* `Hyp.val_shift`: moving the strands of colour `i` by `η_i` carries the hyperplane equations for
  `Γ` to those for `Γ.shift η`; so the two weightings have the same full chambers
  (`sameChambers_shift`).
* `galleryShiftEquiv`, `weightedKLRShiftEquiv`: Proposition 2.15 (sign corrected).

The isomorphism is the identity on sign vectors: it sends the idempotent of the chamber of a
configuration `p` to the idempotent of the chamber of `p + η` (`galleryShiftEquiv_e`). The moved
configuration need not be injective (strands of different colours may meet), which is why the
statement is made on chambers rather than on Webster's loadings; each chamber contains loadings
(`exists_loading_mem_connectedComponentIn` over `ℝ`).
-/

namespace Categorification.WeightedKLR

open MvPolynomial GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]

namespace WeightedGraph

/-- The same graph with the weighting replaced by `w`. -/
abbrev withWeight (Γ : WeightedGraph I 𝕜 k) (w : Γ.E → 𝕜) : WeightedGraph I 𝕜 k :=
  { Γ with weight := w }

/-- The weighting shifted by the coboundary of the `0`-chain `η`:
`ϑ'_e = ϑ_e + η_{t(e)} - η_{h(e)}`. -/
abbrev shift (Γ : WeightedGraph I 𝕜 k) (η : I → 𝕜) : WeightedGraph I 𝕜 k :=
  Γ.withWeight fun e => Γ.weight e + η (Γ.tail e) - η (Γ.head e)

end WeightedGraph

variable {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ} {w : Γ.E → 𝕜}

local notation "Γ'" => Γ.withWeight w

variable (Γ ν w) in
/-- The weightings of `Γ` and `w` have the same full chambers. -/
def SameChambers : Prop :=
  ∀ σ : Hyp Γ ν → Bool, (∃ p, IsGeneric Γ p ∧ fullSigns p = σ) ↔
    ∃ p, IsGeneric (Γ.withWeight w) p ∧ fullSigns (Γ := Γ.withWeight w) p = σ

/-- A full chamber for `Γ` as a full chamber for the weighting `w`. -/
def FullChamber.transfer (hw : SameChambers Γ ν w) (C : FullChamber Γ ν) :
    FullChamber (Γ.withWeight w) ν :=
  ⟨C.1, (hw C.1).1 C.2⟩

section Transfer

variable (hw : SameChambers Γ ν w)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem FullChamber.transfer_inj {C D : FullChamber Γ ν} :
    C.transfer hw = D.transfer hw ↔ C = D :=
  ⟨fun h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h', fun h => h ▸ rfl⟩

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem FullChamber.transfer_injective : Function.Injective (FullChamber.transfer hw) :=
  fun _ _ h => (FullChamber.transfer_inj hw).1 h

omit [DecidableEq I] in
@[simp] theorem FullChamber.transfer_smul (g : ColPerm ν) (C : FullChamber Γ ν) :
    (g • C).transfer hw = g • C.transfer hw := by
  apply Subtype.ext
  funext h
  rcases h with _ | _ <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem FullChamber.transfer_bijective : Function.Bijective (FullChamber.transfer hw) :=
  ⟨FullChamber.transfer_injective hw, fun C' => ⟨⟨C'.1, (hw C'.1).2 C'.2⟩, rfl⟩⟩

variable (k) in
/-- The generators of the gallery algebra of `Γ` as generators for the weighting `w`. -/
def Gen.transfer : Gen k Γ ν → Gen k (Γ.withWeight w) ν
  | .idem C => .idem (C.transfer hw)
  | .poly f => .poly f
  | .step C C' => .step (C.transfer hw) (C'.transfer hw)
  | .relabel g C => .relabel g (C.transfer hw)

variable (k) in
/-- The map of free algebras induced by `Gen.transfer`. -/
noncomputable def freeTransfer :
    FreeAlgebra k (Gen k Γ ν) →ₐ[k] FreeAlgebra k (Gen k (Γ.withWeight w) ν) :=
  FreeAlgebra.lift k fun g => FreeAlgebra.ι k (g.transfer k hw)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem freeTransfer_fe (C : FullChamber Γ ν) :
    freeTransfer k hw (fe k Γ ν C) = fe k (Γ.withWeight w) ν (C.transfer hw) := by
  simp [freeTransfer, Gen.transfer]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem freeTransfer_fp (f : PolyRing ν k) :
    freeTransfer k hw (fp k Γ ν f) = fp k (Γ.withWeight w) ν f := by
  simp [freeTransfer, Gen.transfer]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem freeTransfer_ft (C C' : FullChamber Γ ν) :
    freeTransfer k hw (ft k Γ ν C C') =
      ft k (Γ.withWeight w) ν (C.transfer hw) (C'.transfer hw) := by
  simp [freeTransfer, Gen.transfer]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
@[simp] theorem freeTransfer_fr (g : ColPerm ν) (C : FullChamber Γ ν) :
    freeTransfer k hw (fr k Γ ν g C) = fr k (Γ.withWeight w) ν g (C.transfer hw) := by
  simp [freeTransfer, Gen.transfer]

/-- A hexagon of full chambers for `Γ` as a hexagon for the weighting `w`. -/
def Hexagon.transfer (H : Hexagon Γ ν) : Hexagon (Γ.withWeight w) ν where
  A₀ := H.A₀.transfer hw
  A₁ := H.A₁.transfer hw
  A₂ := H.A₂.transfer hw
  A₃ := H.A₃.transfer hw
  A₄ := H.A₄.transfer hw
  A₅ := H.A₅.transfer hw
  h₁ := H.h₁
  h₂ := H.h₂
  h₃ := H.h₃
  ne₁₂ := H.ne₁₂
  ne₁₃ := H.ne₁₃
  ne₂₃ := H.ne₂₃
  adj₀₁ := H.adj₀₁
  adj₁₂ := H.adj₁₂
  adj₂₃ := H.adj₂₃
  adj₀₅ := H.adj₀₅
  adj₅₄ := H.adj₅₄
  adj₄₃ := H.adj₄₃

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem freeTransfer_gal₁ (H : Hexagon Γ ν) :
    freeTransfer k hw (H.gal₁ k Γ ν) = (H.transfer hw).gal₁ k (Γ.withWeight w) ν := by
  simp [Hexagon.gal₁, Hexagon.transfer]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem freeTransfer_gal₂ (H : Hexagon Γ ν) :
    freeTransfer k hw (H.gal₂ k Γ ν) = (H.transfer hw).gal₂ k (Γ.withWeight w) ν := by
  simp [Hexagon.gal₂, Hexagon.transfer]

theorem freeTransfer_rel {a b : FreeAlgebra k (Gen k Γ ν)} (h : Rel k Γ ν a b) :
    mk k (Γ.withWeight w) ν (freeTransfer k hw a) =
      mk k (Γ.withWeight w) ν (freeTransfer k hw b) := by
  have hT : ∀ C : FullChamber Γ ν, (C.transfer hw).1 = C.1 := fun _ => rfl
  induction h with
  | idem_mul C D =>
    convert rel (Rel.idem_mul (k := k) (C.transfer hw) (D.transfer hw)) using 2
    · simp
    · by_cases hCD : C = D
      · subst hCD; simp
      · simp [hCD]
  | idem_sum =>
    rw [map_sum, map_one, map_sum, ← rel (Rel.idem_sum (k := k) (Γ := Γ.withWeight w) (ν := ν)),
      map_sum]
    simp only [freeTransfer_fe]
    exact Fintype.sum_bijective _ (FullChamber.transfer_bijective hw) _ _ fun _ => rfl
  | poly_add f g =>
    convert rel (Rel.poly_add (k := k) (Γ := Γ.withWeight w) f g) using 2 <;> simp
  | poly_mul f g =>
    convert rel (Rel.poly_mul (k := k) (Γ := Γ.withWeight w) f g) using 2 <;> simp
  | poly_C c =>
    convert rel (Rel.poly_C (k := k) (Γ := Γ.withWeight w) (ν := ν) c) using 2 <;> simp
  | poly_idem f C =>
    convert rel (Rel.poly_idem (k := k) f (C.transfer hw)) using 2 <;> simp
  | step_idem C C' =>
    convert rel (Rel.step_idem (k := k) (C.transfer hw) (C'.transfer hw)) using 2 <;> simp
  | step_zero C C' hC =>
    convert rel (Rel.step_zero (k := k) (C.transfer hw) (C'.transfer hw) hC) using 2 <;> simp
  | relabel_idem g C =>
    convert rel (Rel.relabel_idem (k := k) g (C.transfer hw)) using 2 <;> simp
  | relabel_one C =>
    convert rel (Rel.relabel_one (k := k) (C.transfer hw)) using 2 <;> simp
  | relabel_mul g g' C =>
    convert rel (Rel.relabel_mul (k := k) g g' (C.transfer hw)) using 2 <;> simp
  | relabel_poly g C f =>
    convert rel (Rel.relabel_poly (k := k) g (C.transfer hw) f) using 2 <;> simp
  | relabel_step g C C' =>
    convert rel (Rel.relabel_step (k := k) g (C.transfer hw) (C'.transfer hw)) using 2 <;> simp
  | wall_bigon C C' w' hC =>
    convert rel (Rel.wall_bigon (k := k) (C.transfer hw) (C'.transfer hw) w' hC) using 2 <;>
      simp
    rfl
  | diag_bigon C C' d hC =>
    have := rel (Rel.diag_bigon (k := k) (C.transfer hw) (C'.transfer hw) d hC)
    have hl : (Γ.withWeight w).loop d.fst.1 = Γ.loop d.fst.1 := rfl
    rw [hl] at this
    rcases hP : Γ.loop d.fst.1 with _ | P <;> simp only [hP] at this ⊢ <;>
      convert this using 2 <;> simp
    rfl
  | wall_poly C C' w' hC f =>
    convert rel (Rel.wall_poly (k := k) (C.transfer hw) (C'.transfer hw) w' hC f) using 2 <;>
      simp
  | diag_poly C C' d hC f =>
    convert rel (Rel.diag_poly (k := k) (C.transfer hw) (C'.transfer hw) d hC f) using 2 <;>
      simp
    rfl
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    convert rel (Rel.square (k := k) (C.transfer hw) (B.transfer hw) (B'.transfer hw)
      (D.transfer hw) h₁ h₂ hne (by rcases h₁ with _ | _ <;> rcases h₂ with _ | _ <;> exact hi) a₁ a₂ a₃ a₄) using 2 <;> simp
  | hex_walls H h₁ h₂ h₃ =>
    convert rel (Rel.hex_walls (k := k) (H.transfer hw) h₁ h₂ h₃) using 2 <;>
      simp [freeTransfer_gal₁, freeTransfer_gal₂]
  | hex_mid_diag H w' d h₁ h₂ h₃ hσ hA =>
    have hA' : d.refl • (H.transfer hw).A₀ = (H.transfer hw).A₃ := by
      show d.refl • H.A₀.transfer hw = H.A₃.transfer hw
      rw [← FullChamber.transfer_smul, hA]
    convert rel (Rel.hex_mid_diag (k := k) (H.transfer hw) w' d h₁ h₂ h₃ hσ hA') using 2 <;>
      simp [freeTransfer_gal₁, freeTransfer_gal₂, Hexagon.transfer]
    rfl
  | hex_end_diag H w' d h₂ hd hσ =>
    convert rel (Rel.hex_end_diag (k := k) (H.transfer hw) w' d h₂ hd hσ) using 2 <;>
      simp [freeTransfer_gal₁, freeTransfer_gal₂]
  | hex_diags H d₁ d₂ d₃ u v w' h₁ h₂ h₃ j₁ j₂ j₃ hA =>
    have hA' : d₂.refl • (H.transfer hw).A₀ = (H.transfer hw).A₃ := by
      show d₂.refl • H.A₀.transfer hw = H.A₃.transfer hw
      rw [← FullChamber.transfer_smul, hA]
    have := rel (Rel.hex_diags (k := k) (H.transfer hw) d₁ d₂ d₃ u v w' h₁ h₂ h₃ j₁ j₂ j₃ hA')
    have hl : (Γ.withWeight w).loop u.1 = Γ.loop u.1 := rfl
    rw [hl] at this
    rcases hP : Γ.loop u.1 with _ | P <;> simp only [hP] at this ⊢ <;>
      convert this using 2 <;>
      simp [freeTransfer_gal₁, freeTransfer_gal₂, Hexagon.loopCorrection, Hexagon.transfer]

variable (k) in
/-- The map of gallery algebras induced by the identity on sign vectors. -/
noncomputable def galleryTransfer :
    GalleryAlgebra k Γ ν →ₐ[k] GalleryAlgebra k (Γ.withWeight w) ν :=
  RingQuot.liftAlgHom k
    ⟨(mk k (Γ.withWeight w) ν).comp (freeTransfer k hw), fun _ _ h => freeTransfer_rel hw h⟩

theorem galleryTransfer_mk (x : FreeAlgebra k (Gen k Γ ν)) :
    galleryTransfer k hw (mk k Γ ν x) = mk k (Γ.withWeight w) ν (freeTransfer k hw x) :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem galleryTransfer_e (C : FullChamber Γ ν) :
    galleryTransfer k hw (e C) = e (C.transfer hw) := by
  rw [e, galleryTransfer_mk, freeTransfer_fe]; rfl

theorem galleryTransfer_rankIdem :
    galleryTransfer k hw (rankIdem k Γ ν) = rankIdem k (Γ.withWeight w) ν := by
  rw [rankIdem, rankIdem, map_sum, Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_bijective _ (FullChamber.transfer_bijective hw) _ _ fun C => ?_
  by_cases hC : C.IsRankOrdered
  · have hC' : (C.transfer hw).IsRankOrdered := hC
    simp [hC, hC']
  · have hC' : ¬(C.transfer hw).IsRankOrdered := hC
    simp [hC, hC']

end Transfer

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- The weightings `w` and `Γ.weight` of `Γ.withWeight w` have the same full chambers. -/
theorem SameChambers.symm (hw : SameChambers Γ ν w) :
    SameChambers (Γ.withWeight w) ν Γ.weight :=
  fun σ => (hw σ).symm

/-- Two weightings of a graph with the same full chambers have isomorphic gallery algebras. -/
noncomputable def galleryWeightEquiv (hw : SameChambers Γ ν w) :
    GalleryAlgebra k Γ ν ≃ₐ[k] GalleryAlgebra k (Γ.withWeight w) ν :=
  AlgEquiv.ofAlgHom (galleryTransfer k hw)
    (galleryTransfer k hw.symm : GalleryAlgebra k (Γ.withWeight w) ν →ₐ[k] GalleryAlgebra k Γ ν)
    (by
      apply RingQuot.ringQuot_ext'
      apply FreeAlgebra.hom_ext
      funext g
      show galleryTransfer k hw (galleryTransfer k hw.symm (mk k _ ν (FreeAlgebra.ι k g))) =
        mk k _ ν (FreeAlgebra.ι k g)
      rw [galleryTransfer_mk, galleryTransfer_mk]
      cases g <;> simp [freeTransfer, Gen.transfer] <;> rfl)
    (by
      apply RingQuot.ringQuot_ext'
      apply FreeAlgebra.hom_ext
      funext g
      show galleryTransfer k hw.symm (galleryTransfer k hw (mk k _ ν (FreeAlgebra.ι k g))) =
        mk k _ ν (FreeAlgebra.ι k g)
      rw [galleryTransfer_mk, galleryTransfer_mk]
      cases g <;> simp [freeTransfer, Gen.transfer] <;> rfl)

@[simp] theorem galleryWeightEquiv_e (hw : SameChambers Γ ν w) (C : FullChamber Γ ν) :
    galleryWeightEquiv hw (e C) = e (C.transfer hw) :=
  galleryTransfer_e hw C

/-- A ring isomorphism carrying the idempotent `e` to `e'` restricts to an isomorphism of the
corners. -/
def cornerEquivOfEq {A B : Type*} [Ring A] [Ring B] (f : A ≃+* B) {a : A} {b : B}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (hf : f a = b) :
    ha.Corner ≃+* hb.Corner where
  toFun x := ⟨f x.1, by
    have hx := x.2
    rw [Subsemigroup.mem_corner_iff ha] at hx
    rw [Subsemigroup.mem_corner_iff hb, ← hf, ← map_mul, ← map_mul, hx.1, hx.2]
    exact ⟨rfl, rfl⟩⟩
  invFun y := ⟨f.symm y.1, by
    have hy := y.2
    have hf' : f.symm b = a := by rw [← hf, RingEquiv.symm_apply_apply]
    rw [Subsemigroup.mem_corner_iff hb] at hy
    rw [Subsemigroup.mem_corner_iff ha, ← hf', ← map_mul, ← map_mul, hy.1, hy.2]
    exact ⟨rfl, rfl⟩⟩
  left_inv x := Subtype.ext (f.symm_apply_apply _)
  right_inv y := Subtype.ext (f.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul f x.1 y.1)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)

/-- Two weightings of a graph with the same full chambers have isomorphic weighted KLR
algebras. -/
noncomputable def weightedKLRWeightEquiv (hw : SameChambers Γ ν w) :
    WeightedKLRAlgebra k Γ ν ≃+* WeightedKLRAlgebra k (Γ.withWeight w) ν :=
  cornerEquivOfEq (galleryWeightEquiv hw).toRingEquiv _ _ (galleryTransfer_rankIdem hw)

/-! ### Shifting by a `0`-chain -/

section Shift

variable (η : I → 𝕜)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Moving every strand of colour `i` by `η_i` carries the hyperplane equations for `Γ` to those
for `Γ.shift η`. -/
theorem Hyp.val_shift (h : Hyp Γ ν) (p : Strand ν → 𝕜) :
    Hyp.val (Γ := Γ.shift η) h (fun s => p s + η s.label) = h.val p := by
  rcases h with w' | d
  · have h₁ : w'.src.label = Γ.head w'.edge := w'.2.1
    have h₂ : w'.tgt.label = Γ.tail w'.edge := w'.2.2.1
    show p w'.tgt + η w'.tgt.label - (p w'.src + η w'.src.label) -
      (Γ.weight w'.edge + η (Γ.tail w'.edge) - η (Γ.head w'.edge)) =
        p w'.tgt - p w'.src - Γ.weight w'.edge
    rw [h₁, h₂]
    ring
  · have h₁ : d.snd.label = d.fst.label := by
      simp only [Strand.label, Diag.fst, Diag.snd, d.2.1]
    show p d.snd + η d.snd.label - (p d.fst + η d.fst.label) = p d.snd - p d.fst
    rw [h₁]
    ring

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- `Γ` and `Γ.shift η` have the same full chambers. -/
theorem sameChambers_shift :
    SameChambers Γ ν (fun e => Γ.weight e + η (Γ.tail e) - η (Γ.head e)) := by
  intro σ
  constructor
  · rintro ⟨p, hp, hs⟩
    refine ⟨fun s => p s + η s.label, fun h => ?_, ?_⟩
    · exact (Hyp.val_shift (Γ := Γ) η h p).trans_ne (hp h)
    · rw [← hs]
      funext h
      exact congrArg (fun x => decide (0 < x)) (Hyp.val_shift (Γ := Γ) η h p)
  · rintro ⟨p, hp, hs⟩
    have key : ∀ h : Hyp Γ ν, h.val (fun s => p s - η s.label) =
        Hyp.val (Γ := Γ.shift η) h p := by
      intro h
      rw [← Hyp.val_shift η h]
      congr 1
      funext s
      ring
    refine ⟨fun s => p s - η s.label, fun h => ?_, ?_⟩
    · rw [key]; exact hp h
    · rw [← hs]
      funext h
      simp only [fullSigns]
      rw [key]

variable (k ν) in
/-- The gallery algebras of `Γ` and of `Γ.shift η` are isomorphic. -/
noncomputable def galleryShiftEquiv :
    GalleryAlgebra k Γ ν ≃ₐ[k] GalleryAlgebra k (Γ.shift η) ν :=
  galleryWeightEquiv (sameChambers_shift η)

/-- The isomorphism sends the chamber of a configuration `p` to the chamber of `p + η`. -/
theorem galleryShiftEquiv_e (p : Strand ν → 𝕜) (hp : IsGeneric Γ p) :
    galleryShiftEquiv k ν η (e (FullChamber.ofPoint p hp)) =
      e (FullChamber.ofPoint (Γ := Γ.shift η) (fun s => p s + η s.label)
        fun h => (Hyp.val_shift (Γ := Γ) η h p).trans_ne (hp h)) := by
  rw [galleryShiftEquiv, galleryWeightEquiv_e]
  congr 1
  apply Subtype.ext
  funext h
  exact (congrArg (fun x => decide (0 < x)) (Hyp.val_shift (Γ := Γ) η h p)).symm

variable (k ν) in
/-- Webster, arXiv:1209.2463v4, Proposition 2.15, with the sign of the coboundary corrected (see
the module docstring): for a `0`-chain `η`, moving each strand of colour `i` by `η_i` to the right
gives an isomorphism between the weighted KLR algebras for `ϑ` and for
`ϑ'_e = ϑ_e + η_{t(e)} - η_{h(e)}`. -/
noncomputable def weightedKLRShiftEquiv :
    WeightedKLRAlgebra k Γ ν ≃+* WeightedKLRAlgebra k (Γ.shift η) ν :=
  weightedKLRWeightEquiv (sameChambers_shift η)

end Shift

end Categorification.WeightedKLR
