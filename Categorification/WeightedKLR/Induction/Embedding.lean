/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.KLR.SpacedComparison

/-!
# Embedding an arrangement into a larger one

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Induction and restriction" (the map `ι_{ν';ν''}` defined before the definition of induction).

Webster's induction map places two diagrams side by side. On the gallery algebra this is an
algebra map built from an embedding of strands `j : Strand ν₁ → Strand ν` together with a map
`J` of full chambers which keeps the sides of the hyperplanes between strands in the image of
`j`, and fixes the sides of all other hyperplanes (`ChamberEmbedding`). Such data give an
algebra map from the gallery algebra of `ν₁` to the corner of the gallery algebra of `ν` cut
out by the idempotent `∑_C e (J C)` (`ChamberEmbedding.galleryHom`): it sends `e C` to `e (J C)`,
a polynomial to its renaming along `j`, a step `C → C'` to the step `J C → J C'` and a relabelling
by `g` to the relabelling by the extension `J.perm g` of `g`.

The relations of the gallery algebra are local, so each relation for `ν₁` maps to the same
relation for `ν` (`ChamberEmbedding.freeHom_rel`).

## Main definitions and results

* `StrandEmbedding`: a colour-preserving injection of strands preserving the rank order in each
  colour; `StrandEmbedding.hyp`: the induced map of hyperplanes.
* `ChamberEmbedding`: a strand embedding with a compatible map of full chambers and extension of
  relabellings.
* `ChamberEmbedding.idem`, `ChamberEmbedding.galleryHom`: the idempotent `∑_C e (J C)` and the
  algebra map into its corner.
* `ChamberEmbedding.galleryHom_e`, `galleryHom_poly`, `galleryHom_t`, `galleryHom_r`: the values on
  generators.
-/

namespace IsIdempotentElem

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {e : A} (idem : IsIdempotentElem e)

theorem corner_val_sub (x y : idem.Corner) : (x - y : idem.Corner).1 = x.1 - y.1 := rfl
theorem corner_val_neg (x : idem.Corner) : (-x : idem.Corner).1 = -x.1 := rfl

theorem corner_val_sum {ι : Type*} (s : Finset ι) (f : ι → idem.Corner) :
    (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, corner_val_add, ih]

theorem corner_val_algebraMap (c : R) : (algebraMap R idem.Corner c).1 = c • e := rfl

end IsIdempotentElem

namespace Categorification.WeightedKLR

open MvPolynomial Equiv GalleryAlgebra IsIdempotentElem

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν₁ ν : I →₀ ℕ}

/-- A colour-preserving injection of strands that preserves the rank order of the strands of each
colour. -/
structure StrandEmbedding (ν₁ ν : I →₀ ℕ) where
  /-- The map of strands. -/
  toFun : Strand ν₁ → Strand ν
  injective : Function.Injective toFun
  colour : ∀ s, ((toFun s).1 : I) = (s.1 : I)
  rank_lt : ∀ s t : Strand ν₁, s.1 = t.1 → s.2.val < t.2.val → (toFun s).2.val < (toFun t).2.val

namespace StrandEmbedding

instance : CoeFun (StrandEmbedding ν₁ ν) fun _ => Strand ν₁ → Strand ν := ⟨toFun⟩

variable (j : StrandEmbedding ν₁ ν)

omit [DecidableEq I] in
theorem fst_eq {s t : Strand ν₁} (h : s.1 = t.1) : (j s).1 = (j t).1 :=
  Subtype.ext (by rw [j.colour, j.colour, h])

omit [DecidableEq I] in
theorem rank_lt_iff {s t : Strand ν₁} (h : s.1 = t.1) :
    (j s).2.val < (j t).2.val ↔ s.2.val < t.2.val := by
  refine ⟨fun hlt => ?_, j.rank_lt s t h⟩
  by_contra hn
  rcases (not_lt.1 hn).lt_or_eq with h' | h'
  · exact absurd (j.rank_lt t s h.symm h') (not_lt.2 hlt.le)
  · have : t = s := Strand.ext_of h.symm h'
    subst this
    exact lt_irrefl _ hlt

/-- The wall of `ν` met by the image strands of a wall of `ν₁`. -/
def wall (w : Wall Γ ν₁) : Wall Γ ν :=
  ⟨(w.edge, j w.src, j w.tgt), by
    refine ⟨?_, ?_, fun h => w.2.2.2 (j.injective h)⟩
    · show ((j w.src).1 : I) = Γ.head w.edge
      rw [j.colour]
      exact w.2.1
    · show ((j w.tgt).1 : I) = Γ.tail w.edge
      rw [j.colour]
      exact w.2.2.1⟩

/-- The diagonal of `ν` of the image strands of a diagonal of `ν₁`. -/
def diag (d : Diag ν₁) : Diag ν :=
  ⟨(j d.fst, j d.snd), j.fst_eq d.2.1, j.rank_lt _ _ d.2.1 d.2.2⟩

/-- The map of hyperplanes induced by a strand embedding. -/
def hyp : Hyp Γ ν₁ → Hyp Γ ν := Sum.map j.wall j.diag

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_edge (w : Wall Γ ν₁) : (j.wall w).edge = w.edge := rfl
omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_src (w : Wall Γ ν₁) : (j.wall w).src = j w.src := rfl
omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem wall_tgt (w : Wall Γ ν₁) : (j.wall w).tgt = j w.tgt := rfl
omit [DecidableEq I] in
@[simp] theorem diag_fst (d : Diag ν₁) : (j.diag d).fst = j d.fst := rfl
omit [DecidableEq I] in
@[simp] theorem diag_snd (d : Diag ν₁) : (j.diag d).snd = j d.snd := rfl
omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem hyp_inl (w : Wall Γ ν₁) : j.hyp (.inl w) = .inl (j.wall w) := rfl
omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem hyp_inr (d : Diag ν₁) : j.hyp (Γ := Γ) (.inr d) = .inr (j.diag d) := rfl

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem wall_injective : Function.Injective (j.wall (Γ := Γ)) := by
  intro w w' h
  have h' := congrArg Subtype.val h
  simp only [wall, Prod.mk.injEq] at h'
  exact Subtype.ext (Prod.ext h'.1 (Prod.ext (j.injective h'.2.1) (j.injective h'.2.2)))

omit [DecidableEq I] in
theorem diag_injective : Function.Injective j.diag := by
  intro d d' h
  have h' := congrArg Subtype.val h
  simp only [diag, Prod.mk.injEq] at h'
  exact Subtype.ext (Prod.ext (j.injective h'.1) (j.injective h'.2))

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hyp_injective : Function.Injective (j.hyp (Γ := Γ)) :=
  j.wall_injective.sumMap j.diag_injective

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isLeft_hyp (h : Hyp Γ ν₁) : (j.hyp h).isLeft = h.isLeft := by
  rcases h with _ | _ <;> rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem strands_hyp (h : Hyp Γ ν₁) :
    (j.hyp h).strands = h.strands.map ⟨j, j.injective⟩ := by
  rcases h with w | d <;> simp [Hyp.strands, Finset.map_insert]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem independent_hyp {h h' : Hyp Γ ν₁} (hi : h.Independent h') :
    (j.hyp h).Independent (j.hyp h') := by
  rcases hi with hl | hd
  · left
    rw [j.isLeft_hyp, j.isLeft_hyp]
    exact hl
  · right
    rw [j.strands_hyp, j.strands_hyp]
    exact (Finset.disjoint_map _).2 hd

omit [DecidableEq I] in
theorem rename_aeval_pair (a b : Strand ν₁) (P : MvPolynomial (Fin 2) k) :
    rename j (aeval (Fin.cons (X a) (fun _ => X b) : Fin 2 → PolyRing ν₁ k) P) =
      aeval (Fin.cons (X (j a)) (fun _ => X (j b)) : Fin 2 → PolyRing ν k) P := by
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  fin_cases i <;> simp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem factor_wall (w : Wall Γ ν₁) : (j.wall w).factor = rename j w.factor :=
  (j.rename_aeval_pair w.src w.tgt _).symm

omit [DecidableEq I] in
theorem loopFactor_map (P : MvPolynomial (Fin 2) k) (a b : Strand ν₁) :
    loopFactor P (j a) (j b) = rename j (loopFactor P a b) :=
  (j.rename_aeval_pair a b P).symm

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem loop_eq (s : Strand ν₁) : Γ.loop (j s).1 = Γ.loop s.1 := by rw [j.colour]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem stepFactor_map {s t : Strand ν₁} (hst : s ≠ t) (f : PolyRing ν₁ k) :
    stepFactor Γ (j s) (j t) (rename j f) = rename j (stepFactor Γ s t f) := by
  have hl := j.loop_eq (Γ := Γ) s
  simp only [stepFactor, hl]
  rcases Γ.loop s.1 with _ | P
  · exact (rename_ddiff j.injective hst f).symm
  · simp only [map_mul, map_sub, j.loopFactor_map, rename_rename]
    rw [j.injective.swap_comp]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem diag_left {C : FullChamber Γ ν₁} {C' : FullChamber Γ ν} {d : Diag ν₁}
    (h : C'.1 (.inr (j.diag d)) = C.1 (.inr d)) : (j.diag d).left C' = j (d.left C) := by
  unfold Diag.left
  rw [h]
  split_ifs <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem diag_right {C : FullChamber Γ ν₁} {C' : FullChamber Γ ν} {d : Diag ν₁}
    (h : C'.1 (.inr (j.diag d)) = C.1 (.inr d)) : (j.diag d).right C' = j (d.right C) := by
  unfold Diag.right
  rw [h]
  split_ifs <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem left_ne_right (C : FullChamber Γ ν₁) (d : Diag ν₁) : d.left C ≠ d.right C := by
  unfold Diag.left Diag.right
  split_ifs
  · exact d.fst_ne_snd
  · exact d.fst_ne_snd.symm

omit [DecidableEq I] in
theorem joins_diag {d : Diag ν₁} {u v : Strand ν₁} (h : d.Joins u v) :
    (j.diag d).Joins (j u) (j v) := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨congrArg j h₁, congrArg j h₂⟩
  · exact Or.inr ⟨congrArg j h₁, congrArg j h₂⟩

theorem refl_apply (d : Diag ν₁) (s : Strand ν₁) : j (d.refl.1 s) = (j.diag d).refl.1 (j s) :=
  j.injective.map_swap d.fst d.snd s

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem wall_comap_refl (w : Wall Γ ν₁) (d : Diag ν₁) :
    j.wall (w.comap d.refl) = (j.wall w).comap (j.diag d).refl := by
  have key : ∀ s, j ((d.refl.1)⁻¹ s) = ((j.diag d).refl.1)⁻¹ (j s) := fun s => by
    show j ((swap d.fst d.snd)⁻¹ s) = (swap (j d.fst) (j d.snd))⁻¹ (j s)
    rw [swap_inv, swap_inv]
    exact j.injective.map_swap _ _ _
  apply Subtype.ext
  show (w.edge, j ((d.refl.1)⁻¹ w.src), j ((d.refl.1)⁻¹ w.tgt)) =
    (w.edge, ((j.diag d).refl.1)⁻¹ (j w.src), ((j.diag d).refl.1)⁻¹ (j w.tgt))
  rw [key, key]

end StrandEmbedding

/-- An embedding of the arrangement of `ν₁` into that of `ν`: a strand embedding, a map `J` of full
chambers keeping the sides of the image hyperplanes and fixing the sides of all other
hyperplanes, and an extension of relabellings compatible with `J`. -/
structure ChamberEmbedding (Γ : WeightedGraph I 𝕜 k) (ν₁ ν : I →₀ ℕ) extends
    StrandEmbedding ν₁ ν where
  /-- The map of full chambers. -/
  chamber : FullChamber Γ ν₁ → FullChamber Γ ν
  chamber_hyp : ∀ (C : FullChamber Γ ν₁) (h : Hyp Γ ν₁),
    (chamber C).1 (toStrandEmbedding.hyp h) = C.1 h
  chamber_of_not_mem : ∀ (C D : FullChamber Γ ν₁) (h : Hyp Γ ν),
    h ∉ Set.range (toStrandEmbedding.hyp (Γ := Γ)) → (chamber C).1 h = (chamber D).1 h
  /-- The extension of relabellings. -/
  perm : ColPerm ν₁ →* ColPerm ν
  perm_apply : ∀ g s, (perm g).1 (toFun s) = toFun (g.1 s)
  perm_apply_of_not_mem : ∀ g t, t ∉ Set.range toFun → (perm g).1 t = t
  smul_chamber : ∀ g C, perm g • chamber C = chamber (g • C)

namespace ChamberEmbedding

variable (J : ChamberEmbedding Γ ν₁ ν)

omit [DecidableEq I] in
theorem chamber_injective : Function.Injective J.chamber := by
  intro C D h
  apply Subtype.ext
  funext h'
  rw [← J.chamber_hyp C h', ← J.chamber_hyp D h', h]

omit [DecidableEq I] in
theorem adjacent_chamber {C D : FullChamber Γ ν₁} {h : Hyp Γ ν₁} (hC : C.Adjacent D h) :
    (J.chamber C).Adjacent (J.chamber D) (J.hyp h) := by
  refine ⟨by rw [J.chamber_hyp, J.chamber_hyp]; exact hC.1, fun h' hne => ?_⟩
  by_cases hr : h' ∈ Set.range (J.hyp (Γ := Γ))
  · obtain ⟨h'', rfl⟩ := hr
    rw [J.chamber_hyp, J.chamber_hyp]
    exact hC.2 h'' fun e => hne (e ▸ rfl)
  · exact J.chamber_of_not_mem C D h' hr

omit [DecidableEq I] in
theorem not_adjacent_chamber {C D : FullChamber Γ ν₁} (hC : ∀ h : Hyp Γ ν₁, ¬C.Adjacent D h)
    (h' : Hyp Γ ν) : ¬(J.chamber C).Adjacent (J.chamber D) h' := by
  intro hJ
  by_cases hr : h' ∈ Set.range (J.hyp (Γ := Γ))
  · obtain ⟨h, rfl⟩ := hr
    refine hC h ⟨?_, fun h'' hne => ?_⟩
    · rw [← J.chamber_hyp C h, ← J.chamber_hyp D h]
      exact hJ.1
    · rw [← J.chamber_hyp C h'', ← J.chamber_hyp D h'']
      exact hJ.2 _ fun e => hne (J.hyp_injective e)
  · exact hJ.1 (J.chamber_of_not_mem C D h' hr)

theorem perm_refl (d : Diag ν₁) : J.perm d.refl = (J.diag d).refl := by
  apply Subtype.ext
  apply Equiv.ext
  intro t
  by_cases ht : t ∈ Set.range J.toFun
  · obtain ⟨s, rfl⟩ := ht
    rw [J.perm_apply]
    exact J.refl_apply d s
  · rw [J.perm_apply_of_not_mem _ _ ht]
    show t = swap (J.toFun d.fst) (J.toFun d.snd) t
    rw [swap_apply_of_ne_of_ne (fun e => ht ⟨_, e.symm⟩) (fun e => ht ⟨_, e.symm⟩)]

omit [DecidableEq I] in
theorem rename_perm (g : ColPerm ν₁) (f : PolyRing ν₁ k) :
    rename (J.perm g).1 (rename J.toFun f) = rename J.toFun (rename g.1 f) := by
  rw [rename_rename, rename_rename]
  exact congrArg (fun φ => rename φ f) (funext fun s => J.perm_apply g s)

/-! ### The idempotent and the values on generators -/

/-- The idempotent `∑_C e (J C)`. -/
noncomputable def idem : GalleryAlgebra k Γ ν := ∑ C, e (J.chamber C)

theorem idem_mul_e (C : FullChamber Γ ν₁) : J.idem * e (J.chamber C) = e (J.chamber C) := by
  simp [idem, Finset.sum_mul, e_mul_e, J.chamber_injective.eq_iff]

theorem e_mul_idem (C : FullChamber Γ ν₁) : e (J.chamber C) * J.idem = e (J.chamber C) := by
  simp [idem, Finset.mul_sum, e_mul_e, J.chamber_injective.eq_iff]

theorem isIdempotentElem_idem : IsIdempotentElem J.idem := by
  show J.idem * J.idem = J.idem
  calc J.idem * J.idem = ∑ C, e (J.chamber C) * J.idem :=
        (Finset.sum_mul _ _ _ : (∑ C, e (J.chamber C)) * J.idem = _)
    _ = J.idem := by simp only [J.e_mul_idem]; rfl

theorem idem_mul_poly (f : PolyRing ν k) : J.idem * poly f = poly f * J.idem := by
  simp only [idem, Finset.sum_mul, Finset.mul_sum, e_mul_poly]

theorem idem_mul_t (C D : FullChamber Γ ν₁) :
    J.idem * t (J.chamber C) (J.chamber D) = t (J.chamber C) (J.chamber D) := by
  rw [← e_mul_t, ← mul_assoc, J.idem_mul_e]

theorem t_mul_idem (C D : FullChamber Γ ν₁) :
    t (J.chamber C) (J.chamber D) * J.idem = t (J.chamber C) (J.chamber D) := by
  rw [← t_mul_e, mul_assoc, J.e_mul_idem]

theorem idem_mul_r (g : ColPerm ν₁) (C : FullChamber Γ ν₁) :
    J.idem * r (J.perm g) (J.chamber C) = r (J.perm g) (J.chamber C) := by
  rw [r_eq, J.smul_chamber, ← mul_assoc, ← mul_assoc, J.idem_mul_e, ← J.smul_chamber, ← r_eq]

theorem r_mul_idem (g : ColPerm ν₁) (C : FullChamber Γ ν₁) :
    r (J.perm g) (J.chamber C) * J.idem = r (J.perm g) (J.chamber C) := by
  rw [← r_mul_e, mul_assoc, J.e_mul_idem]

/-- The values of the generators. -/
noncomputable def genVal : Gen k Γ ν₁ → GalleryAlgebra k Γ ν
  | .idem C => e (J.chamber C)
  | .poly f => poly (rename J.toFun f) * J.idem
  | .step C D => t (J.chamber C) (J.chamber D)
  | .relabel g C => r (J.perm g) (J.chamber C)

theorem genVal_mem (g : Gen k Γ ν₁) : J.genVal g ∈ Subsemigroup.corner J.idem := by
  rw [Subsemigroup.mem_corner_iff J.isIdempotentElem_idem]
  cases g with
  | idem C => exact ⟨J.idem_mul_e C, J.e_mul_idem C⟩
  | poly f =>
    refine ⟨?_, ?_⟩
    · show J.idem * (poly _ * J.idem) = poly _ * J.idem
      rw [← mul_assoc, J.idem_mul_poly, mul_assoc, J.isIdempotentElem_idem.eq]
    · show poly _ * J.idem * J.idem = poly _ * J.idem
      rw [mul_assoc, J.isIdempotentElem_idem.eq]
  | step C D => exact ⟨J.idem_mul_t C D, J.t_mul_idem C D⟩
  | relabel g C => exact ⟨J.idem_mul_r g C, J.r_mul_idem g C⟩

/-- The values of the generators, as elements of the corner of `J.idem`. -/
noncomputable def cornerGen (g : Gen k Γ ν₁) : J.isIdempotentElem_idem.Corner :=
  ⟨J.genVal g, J.genVal_mem g⟩

/-- The map of free algebras into the corner of `J.idem`. -/
noncomputable def freeHom :
    FreeAlgebra k (Gen k Γ ν₁) →ₐ[k] J.isIdempotentElem_idem.Corner :=
  FreeAlgebra.lift k J.cornerGen

@[simp] theorem freeHom_fe (C : FullChamber Γ ν₁) :
    (J.freeHom (fe k Γ ν₁ C)).1 = e (J.chamber C) := by
  rw [freeHom, fe, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeHom_fp (f : PolyRing ν₁ k) :
    (J.freeHom (fp k Γ ν₁ f)).1 = poly (rename J.toFun f) * J.idem := by
  rw [freeHom, fp, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeHom_ft (C D : FullChamber Γ ν₁) :
    (J.freeHom (ft k Γ ν₁ C D)).1 = t (J.chamber C) (J.chamber D) := by
  rw [freeHom, ft, FreeAlgebra.lift_ι_apply]
  rfl

@[simp] theorem freeHom_fr (g : ColPerm ν₁) (C : FullChamber Γ ν₁) :
    (J.freeHom (fr k Γ ν₁ g C)).1 = r (J.perm g) (J.chamber C) := by
  rw [freeHom, fr, FreeAlgebra.lift_ι_apply]
  rfl

/-- A hexagon of full chambers for `ν₁` as a hexagon for `ν`. -/
def hexagon (H : Hexagon Γ ν₁) : Hexagon Γ ν where
  A₀ := J.chamber H.A₀
  A₁ := J.chamber H.A₁
  A₂ := J.chamber H.A₂
  A₃ := J.chamber H.A₃
  A₄ := J.chamber H.A₄
  A₅ := J.chamber H.A₅
  h₁ := J.hyp H.h₁
  h₂ := J.hyp H.h₂
  h₃ := J.hyp H.h₃
  ne₁₂ := J.hyp_injective.ne H.ne₁₂
  ne₁₃ := J.hyp_injective.ne H.ne₁₃
  ne₂₃ := J.hyp_injective.ne H.ne₂₃
  adj₀₁ := J.adjacent_chamber H.adj₀₁
  adj₁₂ := J.adjacent_chamber H.adj₁₂
  adj₂₃ := J.adjacent_chamber H.adj₂₃
  adj₀₅ := J.adjacent_chamber H.adj₀₅
  adj₅₄ := J.adjacent_chamber H.adj₅₄
  adj₄₃ := J.adjacent_chamber H.adj₄₃

omit [DecidableEq I] in
@[simp] theorem hexagon_h₁ (H : Hexagon Γ ν₁) : (J.hexagon H).h₁ = J.hyp H.h₁ := rfl
omit [DecidableEq I] in
@[simp] theorem hexagon_h₂ (H : Hexagon Γ ν₁) : (J.hexagon H).h₂ = J.hyp H.h₂ := rfl
omit [DecidableEq I] in
@[simp] theorem hexagon_h₃ (H : Hexagon Γ ν₁) : (J.hexagon H).h₃ = J.hyp H.h₃ := rfl

theorem freeHom_gal₁ (H : Hexagon Γ ν₁) :
    (J.freeHom (H.gal₁ k Γ ν₁)).1 = GalleryAlgebra.mk k Γ ν ((J.hexagon H).gal₁ k Γ ν) := by
  simp [Hexagon.gal₁, hexagon, corner_val_mul]

theorem freeHom_gal₂ (H : Hexagon Γ ν₁) :
    (J.freeHom (H.gal₂ k Γ ν₁)).1 = GalleryAlgebra.mk k Γ ν ((J.hexagon H).gal₂ k Γ ν) := by
  simp [Hexagon.gal₂, hexagon, corner_val_mul]

theorem poly_idem_mul (f : PolyRing ν k) (x : GalleryAlgebra k Γ ν) (hx : J.idem * x = x) :
    poly f * J.idem * x = poly f * x := by
  rw [mul_assoc, hx]

theorem freeHom_rel {a b : FreeAlgebra k (Gen k Γ ν₁)} (h : Rel k Γ ν₁ a b) :
    J.freeHom a = J.freeHom b := by
  apply Subtype.ext
  induction h with
  | idem_mul C D =>
    by_cases hCD : C = D
    · subst hCD
      simp [corner_val_mul, e_mul_e]
    · simp [hCD, corner_val_mul, e_mul_e, J.chamber_injective.ne hCD, corner_val_zero]
  | idem_sum =>
    rw [map_sum, map_one, corner_val_sum, corner_val_one]
    simp only [freeHom_fe]
    rfl
  | poly_add f g =>
    simp only [map_add, corner_val_add, freeHom_fp, ← polyHom_apply, add_mul]
  | poly_mul f g =>
    simp only [map_mul, corner_val_mul, freeHom_fp]
    rw [mul_assoc, ← mul_assoc J.idem, J.idem_mul_poly, mul_assoc, J.isIdempotentElem_idem.eq,
      ← mul_assoc, poly_mul_poly]
  | poly_C c =>
    rw [freeHom_fp, AlgHom.commutes, corner_val_algebraMap, rename_C, ← polyHom_apply,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def]
  | poly_idem f C =>
    simp only [map_mul, corner_val_mul, freeHom_fp, freeHom_fe]
    rw [mul_assoc, J.idem_mul_e, ← mul_assoc (e _), e_mul_poly, mul_assoc, J.e_mul_idem]
  | step_idem C D =>
    simp only [map_mul, corner_val_mul, freeHom_fe, freeHom_ft]
    exact t_eq _ _
  | step_zero C D hC =>
    rw [freeHom_ft, map_zero, corner_val_zero]
    exact t_eq_zero (J.not_adjacent_chamber hC)
  | relabel_idem g C =>
    simp only [map_mul, corner_val_mul, freeHom_fe, freeHom_fr]
    rw [← J.smul_chamber]
    exact r_eq _ _
  | relabel_one C =>
    rw [freeHom_fr, freeHom_fe, map_one]
    exact r_one _
  | relabel_mul g g' C =>
    simp only [map_mul, corner_val_mul, freeHom_fr]
    rw [← J.smul_chamber, r_mul_r]
  | relabel_poly g C f =>
    simp only [map_mul, corner_val_mul, freeHom_fr, freeHom_fp]
    rw [← mul_assoc, r_mul_poly, mul_assoc, J.r_mul_idem, J.rename_perm, mul_assoc,
      J.idem_mul_r]
  | relabel_step g C C' =>
    simp only [map_mul, corner_val_mul, freeHom_fr, freeHom_ft]
    rw [r_mul_t, J.smul_chamber, J.smul_chamber]
  | wall_bigon C C' w hC =>
    simp only [map_mul, corner_val_mul, freeHom_fe, freeHom_ft, freeHom_fp]
    have := rel (Rel.wall_bigon (k := k) _ _ _ (J.adjacent_chamber hC))
    simp only [map_mul, mk_ft, mk_fp, mk_fe] at this
    rw [this, mul_assoc, J.idem_mul_e, ← J.factor_wall]
  | diag_bigon C C' d hC =>
    have := rel (Rel.diag_bigon (k := k) _ _ (J.diag d) (J.adjacent_chamber hC))
    have hl : Γ.loop (J.diag d).fst.1 = Γ.loop d.fst.1 := J.loop_eq d.fst
    have hL : (J.diag d).left (J.chamber C) = J.toFun (d.left C) :=
      J.diag_left (J.chamber_hyp C (.inr d))
    have hR : (J.diag d).right (J.chamber C) = J.toFun (d.right C) :=
      J.diag_right (J.chamber_hyp C (.inr d))
    rw [hl] at this
    rcases hP : Γ.loop d.fst.1 with _ | P <;> simp only [hP] at this ⊢
    · simp only [map_mul, corner_val_mul, freeHom_ft, map_zero, corner_val_zero]
      simpa using this
    · simp only [map_mul, corner_val_mul, freeHom_ft, freeHom_fp, freeHom_fr]
      simp only [map_mul, mk_ft, mk_fp, mk_fr] at this
      rw [this, hL, hR, ← J.perm_refl, mul_assoc (poly _) J.idem, J.idem_mul_r,
        ← J.loopFactor_map, map_neg,
        show (rename J.toFun) (2 : PolyRing ν₁ k) = 2 from map_ofNat _ 2]
  | wall_poly C C' w hC f =>
    simp only [map_mul, corner_val_mul, freeHom_ft, freeHom_fp]
    rw [← mul_assoc, t_mul_poly_inl (J.adjacent_chamber hC), mul_assoc, J.t_mul_idem,
      mul_assoc, J.idem_mul_t]
  | diag_poly C C' d hC f =>
    simp only [map_sub, map_mul, corner_val_sub, corner_val_mul, freeHom_ft, freeHom_fp,
      freeHom_fr]
    have h' := t_mul_poly_inr (k := k) (J.adjacent_chamber (h := .inr d) hC) (rename J.toFun f)
    rw [← mul_assoc, h', add_mul, mul_assoc (poly _) (t _ _), J.t_mul_idem,
      mul_assoc (poly _) (r _ _), ← J.perm_refl, J.r_mul_idem, mul_assoc (poly _) J.idem,
      J.idem_mul_t, add_sub_cancel_left, mul_assoc (poly _) J.idem, J.idem_mul_r]
    congr 2
    rw [J.diag_left (J.chamber_hyp C (.inr d)), J.diag_right (J.chamber_hyp C (.inr d)),
      J.stepFactor_map (StrandEmbedding.left_ne_right C d)]
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    simp only [map_mul, corner_val_mul, freeHom_ft]
    have := rel (Rel.square (k := k) _ _ _ _ _ _ (J.hyp_injective.ne hne)
      (J.independent_hyp hi) (J.adjacent_chamber a₁) (J.adjacent_chamber a₂)
      (J.adjacent_chamber a₃) (J.adjacent_chamber a₄))
    simpa only [map_mul, mk_ft] using this
  | hex_walls H h₁ h₂ h₃ =>
    rw [J.freeHom_gal₁, J.freeHom_gal₂]
    exact rel (Rel.hex_walls (J.hexagon H) (by rw [J.hexagon_h₁, J.isLeft_hyp]; exact h₁)
      (by rw [J.hexagon_h₂, J.isLeft_hyp]; exact h₂) (by rw [J.hexagon_h₃, J.isLeft_hyp]; exact h₃))
  | hex_mid_diag H w d h₁ h₂ h₃ hσ hA =>
    have hA' : (J.diag d).refl • (J.hexagon H).A₀ = (J.hexagon H).A₃ := by
      show (J.diag d).refl • J.chamber H.A₀ = J.chamber H.A₃
      rw [← J.perm_refl, J.smul_chamber, hA]
    have hσ' : (J.hexagon H).A₀.1 (.inl (J.wall w)) ≠
        (J.hexagon H).A₀.1 (.inl ((J.wall w).comap (J.diag d).refl)) := by
      show (J.chamber H.A₀).1 (J.hyp (.inl w)) ≠
        (J.chamber H.A₀).1 (.inl ((J.wall w).comap (J.diag d).refl))
      rw [← J.wall_comap_refl, ← J.hyp_inl, J.chamber_hyp, J.chamber_hyp]
      exact hσ
    have := rel (Rel.hex_mid_diag (J.hexagon H) (J.wall w) (J.diag d)
      (by rw [J.hexagon_h₁, h₁]; rfl) (by rw [J.hexagon_h₂, h₂]; rfl)
      (by rw [J.hexagon_h₃, h₃, J.hyp_inl, J.wall_comap_refl]) hσ' hA')
    simp only [map_sub, map_mul, mk_fp, mk_fr] at this
    simp only [map_sub, map_mul, corner_val_sub, corner_val_mul, freeHom_fp, freeHom_fr]
    rw [J.freeHom_gal₁, J.freeHom_gal₂, this, mul_assoc (poly _), J.idem_mul_r, J.perm_refl]
    congr 2
    have hA₁ : (J.hexagon H).A₁ = J.chamber H.A₁ := rfl
    rw [hA₁, J.diag_left (J.chamber_hyp H.A₁ (.inr d)),
      J.diag_right (J.chamber_hyp H.A₁ (.inr d)), J.factor_wall,
      J.stepFactor_map (StrandEmbedding.left_ne_right H.A₁ d)]
  | hex_end_diag H w d h₂ hd hσ =>
    rw [J.freeHom_gal₁, J.freeHom_gal₂]
    refine rel (Rel.hex_end_diag (J.hexagon H) (J.wall w) (J.diag d)
      (by rw [J.hexagon_h₂, h₂]; rfl) ?_ ?_)
    · rcases hd with ⟨e₁, e₃⟩ | ⟨e₁, e₃⟩
      · exact Or.inl ⟨by rw [J.hexagon_h₁, e₁]; rfl,
          by rw [J.hexagon_h₃, e₃, J.hyp_inl, J.wall_comap_refl]⟩
      · exact Or.inr ⟨by rw [J.hexagon_h₁, e₁, J.hyp_inl, J.wall_comap_refl],
          by rw [J.hexagon_h₃, e₃]; rfl⟩
    · show (J.chamber H.A₀).1 (J.hyp (.inl w)) =
        (J.chamber H.A₀).1 (.inl ((J.wall w).comap (J.diag d).refl))
      rw [← J.wall_comap_refl, ← J.hyp_inl, J.chamber_hyp, J.chamber_hyp]
      exact hσ
  | hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA =>
    have hA' : (J.diag d₂).refl • (J.hexagon H).A₀ = (J.hexagon H).A₃ := by
      show (J.diag d₂).refl • J.chamber H.A₀ = J.chamber H.A₃
      rw [← J.perm_refl, J.smul_chamber, hA]
    have := rel (Rel.hex_diags (J.hexagon H) (J.diag d₁) (J.diag d₂) (J.diag d₃) (J.toFun u)
      (J.toFun v) (J.toFun w) (by rw [J.hexagon_h₁, h₁]; rfl) (by rw [J.hexagon_h₂, h₂]; rfl)
      (by rw [J.hexagon_h₃, h₃]; rfl) (J.joins_diag j₁) (J.joins_diag j₂) (J.joins_diag j₃) hA')
    have hl : Γ.loop (J.toFun u).1 = Γ.loop u.1 := J.loop_eq u
    rw [hl] at this
    rw [map_sub, corner_val_sub, J.freeHom_gal₁, J.freeHom_gal₂, ← map_sub, this]
    rcases hP : Γ.loop u.1 with _ | P
    · rw [map_zero, map_zero, corner_val_zero]
    · simp only [Hexagon.loopCorrection, map_add, map_mul, mk_fp, mk_fr, mk_ft, corner_val_add,
        corner_val_mul, freeHom_fp, freeHom_fr, freeHom_ft, mul_assoc (poly _) J.idem,
        J.perm_refl, map_mul, map_neg, map_sub, J.loopFactor_map]
      simp only [← J.perm_refl, ← map_mul, J.idem_mul_r]
      rfl

/-! ### The algebra map -/

/-- The algebra map from the gallery algebra of `ν₁` into the corner of the gallery algebra of
`ν` cut out by `∑_C e (J C)`. -/
noncomputable def galleryHom : GalleryAlgebra k Γ ν₁ →ₐ[k] J.isIdempotentElem_idem.Corner :=
  RingQuot.liftAlgHom k ⟨J.freeHom, fun _ _ h => J.freeHom_rel h⟩

theorem galleryHom_mk (x : FreeAlgebra k (Gen k Γ ν₁)) :
    J.galleryHom (GalleryAlgebra.mk k Γ ν₁ x) = J.freeHom x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem galleryHom_e (C : FullChamber Γ ν₁) :
    (J.galleryHom (e C)).1 = e (J.chamber C) := by
  rw [e, galleryHom_mk, freeHom_fe]

@[simp] theorem galleryHom_poly (f : PolyRing ν₁ k) :
    (J.galleryHom (poly f)).1 = poly (rename J.toFun f) * J.idem := by
  rw [poly, galleryHom_mk, freeHom_fp]

@[simp] theorem galleryHom_t (C D : FullChamber Γ ν₁) :
    (J.galleryHom (t C D)).1 = t (J.chamber C) (J.chamber D) := by
  rw [t, galleryHom_mk, freeHom_ft]

@[simp] theorem galleryHom_r (g : ColPerm ν₁) (C : FullChamber Γ ν₁) :
    (J.galleryHom (r g C)).1 = r (J.perm g) (J.chamber C) := by
  rw [r, galleryHom_mk, freeHom_fr]

end ChamberEmbedding

end Categorification.WeightedKLR
