/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Embedding

/-!
# Juxtaposing two arrangements

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2, subsection
"Induction and restriction": the map `ι_{ν';ν''}` places a diagram for `ν'` to the left of a
diagram for `ν''`, separated by a distance larger than all weights and positions.

The strands of `ν' + ν''` are the strands of `ν'` followed by those of `ν''` in each colour
(`strandEquiv`). Placing a configuration `p''` for `ν''` at distance `c` to the right of a
configuration `p'` for `ν'` (`juxt p' p'' c`) gives, once `c` is at least `bound Γ p' p''`, a
generic configuration whose side of every hyperplane between a strand of `ν'` and a strand of
`ν''` is determined by the side of the strands: the hyperplane value is positive exactly when the
strand of `ν''` is the one that comes second in the hyperplane (`val_cross`). This gives the
juxtaposed chamber `chamber C' C''` (written `C' ∘ C''`), the extensions of relabellings
`leftPerm`, `rightPerm`, and the two chamber embeddings `leftChamberEmb C''` and
`rightChamberEmb C'` (`ChamberEmbedding`).

## Main definitions and results

* `strandEquiv`: the strands of `ν' + ν''` as the strands of `ν'` and of `ν''`.
* `juxt`, `bound`, `val_cross`, `isGeneric_juxt`.
* `chamber`, `chamber_left`, `chamber_right`, `chamber_cross`, `isRankOrdered_chamber_iff`.
* `colPermProd`, `leftPerm`, `rightPerm`.
* `leftChamberEmb`, `rightChamberEmb`.
-/

namespace Categorification.WeightedKLR

open Equiv

namespace Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  (ν' ν'' : I →₀ ℕ)

/-! ### Strands -/

omit [DecidableEq I] in
theorem mem_support_left {i : I} (h : i ∈ ν'.support) : i ∈ (ν' + ν'').support := by
  rw [Finsupp.mem_support_iff] at *
  rw [Finsupp.add_apply]
  omega

omit [DecidableEq I] in
theorem mem_support_right {i : I} (h : i ∈ ν''.support) : i ∈ (ν' + ν'').support := by
  rw [Finsupp.mem_support_iff] at *
  rw [Finsupp.add_apply]
  omega

/-- A strand of `ν'` as a strand of `ν' + ν''`: same colour and rank. -/
def inlStrand (s : Strand ν') : Strand (ν' + ν'') :=
  ⟨⟨s.1, mem_support_left ν' ν'' s.1.2⟩, ⟨s.2.val, by
    show s.2.val < (ν' + ν'') (s.1 : I)
    rw [Finsupp.add_apply]
    have := s.2.2
    omega⟩⟩

/-- A strand of `ν''` as a strand of `ν' + ν''`: same colour, rank shifted by `ν'`. -/
def inrStrand (s : Strand ν'') : Strand (ν' + ν'') :=
  ⟨⟨s.1, mem_support_right ν' ν'' s.1.2⟩, ⟨ν' s.1 + s.2.val, by
    show ν' (s.1 : I) + s.2.val < (ν' + ν'') (s.1 : I)
    rw [Finsupp.add_apply]
    have := s.2.2
    omega⟩⟩

/-- A strand of `ν' + ν''` comes from `ν'` or from `ν''`. -/
def splitStrand (t : Strand (ν' + ν'')) : Strand ν' ⊕ Strand ν'' :=
  if h : t.2.val < ν' t.1 then
    .inl ⟨⟨t.1, by rw [Finsupp.mem_support_iff]; omega⟩, ⟨t.2.val, h⟩⟩
  else
    .inr ⟨⟨t.1, by
        have h₂ : t.2.val < (ν' + ν'') (t.1 : I) := t.2.2
        have h₃ : (ν' + ν'') (t.1 : I) = ν' t.1 + ν'' t.1 := Finsupp.add_apply _ _ _
        rw [Finsupp.mem_support_iff]
        omega⟩,
      ⟨t.2.val - ν' t.1, by
        have h₂ : t.2.val < (ν' + ν'') (t.1 : I) := t.2.2
        have h₃ : (ν' + ν'') (t.1 : I) = ν' t.1 + ν'' t.1 := Finsupp.add_apply _ _ _
        show t.2.val - ν' (t.1 : I) < ν'' (t.1 : I)
        omega⟩⟩

/-- The strands of `ν' + ν''` are those of `ν'` followed by those of `ν''`. -/
def strandEquiv : Strand ν' ⊕ Strand ν'' ≃ Strand (ν' + ν'') where
  toFun := Sum.elim (inlStrand ν' ν'') (inrStrand ν' ν'')
  invFun := splitStrand ν' ν''
  left_inv := by
    rintro (s | s)
    · show splitStrand ν' ν'' (inlStrand ν' ν'' s) = .inl s
      unfold splitStrand
      split_ifs with h
      · exact congrArg Sum.inl (Strand.ext_of rfl rfl)
      · exact absurd s.2.2 h
    · show splitStrand ν' ν'' (inrStrand ν' ν'' s) = .inr s
      unfold splitStrand
      split_ifs with h
      · exact absurd h (show ¬ ν' (s.1 : I) + s.2.val < ν' (s.1 : I) by omega)
      · exact congrArg Sum.inr (Strand.ext_of rfl (by
          show ν' (s.1 : I) + s.2.val - ν' (s.1 : I) = s.2.val
          omega))
  right_inv := by
    intro t
    unfold splitStrand
    split_ifs with h
    · exact Strand.ext_of rfl rfl
    · exact Strand.ext_of rfl (by
        show ν' (t.1 : I) + (t.2.val - ν' (t.1 : I)) = t.2.val
        omega)

omit [DecidableEq I] in
@[simp] theorem strandEquiv_inl (s : Strand ν') :
    strandEquiv ν' ν'' (.inl s) = inlStrand ν' ν'' s := rfl

omit [DecidableEq I] in
@[simp] theorem strandEquiv_inr (s : Strand ν'') :
    strandEquiv ν' ν'' (.inr s) = inrStrand ν' ν'' s := rfl

omit [DecidableEq I] in
@[simp] theorem strandEquiv_symm_inl (s : Strand ν') :
    (strandEquiv ν' ν'').symm (inlStrand ν' ν'' s) = .inl s :=
  (strandEquiv ν' ν'').symm_apply_apply (.inl s)

omit [DecidableEq I] in
@[simp] theorem strandEquiv_symm_inr (s : Strand ν'') :
    (strandEquiv ν' ν'').symm (inrStrand ν' ν'' s) = .inr s :=
  (strandEquiv ν' ν'').symm_apply_apply (.inr s)

omit [DecidableEq I] in
theorem inlStrand_injective : Function.Injective (inlStrand ν' ν'') := fun a b h => by
  have h' : strandEquiv ν' ν'' (.inl a) = strandEquiv ν' ν'' (.inl b) := h
  exact Sum.inl_injective ((strandEquiv ν' ν'').injective h')

omit [DecidableEq I] in
theorem inrStrand_injective : Function.Injective (inrStrand ν' ν'') := fun a b h => by
  have h' : strandEquiv ν' ν'' (.inr a) = strandEquiv ν' ν'' (.inr b) := h
  exact Sum.inr_injective ((strandEquiv ν' ν'').injective h')

omit [DecidableEq I] in
theorem inlStrand_ne_inrStrand (a : Strand ν') (b : Strand ν'') :
    inlStrand ν' ν'' a ≠ inrStrand ν' ν'' b := fun h => by
  have h' : strandEquiv ν' ν'' (.inl a) = strandEquiv ν' ν'' (.inr b) := h
  exact Sum.inl_ne_inr ((strandEquiv ν' ν'').injective h')

/-- The strands of `ν'` inside `ν' + ν''`. -/
def leftEmb : StrandEmbedding ν' (ν' + ν'') where
  toFun := inlStrand ν' ν''
  injective := inlStrand_injective ν' ν''
  colour _ := rfl
  rank_lt _ _ _ h := h

/-- The strands of `ν''` inside `ν' + ν''`. -/
def rightEmb : StrandEmbedding ν'' (ν' + ν'') where
  toFun := inrStrand ν' ν''
  injective := inrStrand_injective ν' ν''
  colour _ := rfl
  rank_lt s t hst h := by
    have : ν' (s.1 : I) = ν' (t.1 : I) := by rw [hst]
    show ν' (s.1 : I) + s.2.val < ν' (t.1 : I) + t.2.val
    omega

/-! ### Juxtaposed configurations -/

variable {ν' ν''}

/-- The configuration `p'` followed by `p''` translated by `c`. -/
def juxt (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) : Strand (ν' + ν'') → 𝕜 :=
  fun t => Sum.elim p' (fun u => p'' u + c) ((strandEquiv ν' ν'').symm t)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem juxt_inl (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (s : Strand ν') :
    juxt p' p'' c (inlStrand ν' ν'' s) = p' s := by
  simp [juxt]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem juxt_inr (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (s : Strand ν'') :
    juxt p' p'' c (inrStrand ν' ν'' s) = p'' s + c := by
  simp [juxt]

variable (Γ) in
/-- A separation beyond which juxtaposition does not meet any hyperplane between the two sides. -/
def bound (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) : 𝕜 :=
  1 + ∑ s, |p' s| + ∑ s, |p'' s| + ∑ e, |Γ.weight e|

omit [DecidableEq I] in
theorem lt_bound_wall (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (a : Strand ν')
    (b : Strand ν'') (e : Γ.E) : |p' a| + |p'' b| + |Γ.weight e| < bound Γ p' p'' := by
  have h₁ := Finset.single_le_sum (f := fun s => |p' s|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ a)
  have h₂ := Finset.single_le_sum (f := fun s => |p'' s|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ b)
  have h₃ := Finset.single_le_sum (f := fun e => |Γ.weight e|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ e)
  unfold bound
  linarith

omit [DecidableEq I] in
theorem lt_bound_diag (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (a : Strand ν')
    (b : Strand ν'') : |p' a| + |p'' b| < bound Γ p' p'' := by
  have h₁ := Finset.single_le_sum (f := fun s => |p' s|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ a)
  have h₂ := Finset.single_le_sum (f := fun s => |p'' s|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ b)
  have h₃ : 0 ≤ ∑ e, |Γ.weight e| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold bound
  linarith

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem _root_.Categorification.WeightedKLR.StrandEmbedding.val_hyp {ν₁ ν : I →₀ ℕ}
    (j : StrandEmbedding ν₁ ν) (h : Hyp Γ ν₁) (q : Strand ν → 𝕜) :
    (j.hyp h).val q = h.val (q ∘ j) := by
  rcases h with _ | _ <;> rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem _root_.Categorification.WeightedKLR.Hyp.val_add_const {ν : I →₀ ℕ} (h : Hyp Γ ν)
    (p : Strand ν → 𝕜) (c : 𝕜) : h.val (fun s => p s + c) = h.val p := by
  rcases h with w | d
  · simp only [Hyp.val_inl, Wall.val]
    ring
  · simp only [Hyp.val_inr, Diag.val]
    ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_left (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (h : Hyp Γ ν') :
    ((leftEmb ν' ν'').hyp h).val (juxt p' p'' c) = h.val p' := by
  rw [StrandEmbedding.val_hyp]
  congr 1
  funext s
  exact juxt_inl p' p'' c s

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_right (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) (h : Hyp Γ ν'') :
    ((rightEmb ν' ν'').hyp h).val (juxt p' p'' c) = h.val p'' := by
  rw [StrandEmbedding.val_hyp, ← Hyp.val_add_const h p'' c]
  congr 1
  funext s
  exact juxt_inr p' p'' c s

/-- The side of a hyperplane between a strand of `ν'` and a strand of `ν''`: positive exactly
when the strand of `ν''` is the second strand of the hyperplane. -/
noncomputable def crossSign : Hyp Γ (ν' + ν'') → Bool
  | .inl w => ((strandEquiv ν' ν'').symm w.tgt).isRight
  | .inr _ => true

omit [DecidableEq I] in
/-- The hyperplanes between the two sides are not met by a juxtaposition at large separation,
and the side is `crossSign`. -/
theorem val_cross (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) {c : 𝕜}
    (hc : bound Γ p' p'' ≤ c) {h : Hyp Γ (ν' + ν'')}
    (hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)))
    (hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))) :
    h.val (juxt p' p'' c) ≠ 0 ∧ (0 < h.val (juxt p' p'' c) ↔ crossSign h = true) := by
  rcases h with w | d
  · rcases ha : (strandEquiv ν' ν'').symm w.src with a | a <;>
      rcases hb : (strandEquiv ν' ν'').symm w.tgt with b | b <;>
      have hsrc := (Equiv.symm_apply_eq _).1 ha <;> have htgt := (Equiv.symm_apply_eq _).1 hb
    · exfalso
      have h₁ : w.src.label = Γ.head w.edge := w.2.1
      have h₂ : w.tgt.label = Γ.tail w.edge := w.2.2.1
      rw [hsrc] at h₁
      rw [htgt] at h₂
      refine hl ⟨.inl ⟨(w.edge, a, b), h₁, h₂, fun e => w.2.2.2 ?_⟩, ?_⟩
      · have e' : a = b := e
        show w.src = w.tgt
        rw [hsrc, htgt, e']
      · exact congrArg Sum.inl (Subtype.ext (Prod.ext rfl (Prod.ext hsrc.symm htgt.symm)))
    · have hv : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) (juxt p' p'' c)
        = (p'' b + c) - p' a - Γ.weight w.edge := by
        show juxt p' p'' c w.tgt - juxt p' p'' c w.src - _ = _
        unfold juxt
        rw [ha, hb]
        rfl
      have hB := lt_bound_wall (Γ := Γ) p' p'' a b w.edge
      have h1 := neg_abs_le (p'' b)
      have h2 := le_abs_self (p' a)
      have h3 := le_abs_self (Γ.weight w.edge)
      have hpos : 0 < Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) (juxt p' p'' c) := by rw [hv]; linarith
      refine ⟨hpos.ne', iff_of_true hpos ?_⟩
      simp [crossSign, hb]
    · have hv : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) (juxt p' p'' c)
        = p' b - (p'' a + c) - Γ.weight w.edge := by
        show juxt p' p'' c w.tgt - juxt p' p'' c w.src - _ = _
        unfold juxt
        rw [ha, hb]
        rfl
      have hB := lt_bound_wall (Γ := Γ) p' p'' b a w.edge
      have h1 := neg_abs_le (p'' a)
      have h2 := le_abs_self (p' b)
      have h3 := neg_abs_le (Γ.weight w.edge)
      have hneg : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) (juxt p' p'' c) < 0 := by rw [hv]; linarith
      refine ⟨hneg.ne, iff_of_false (not_lt.2 hneg.le) ?_⟩
      simp [crossSign, hb]
    · exfalso
      have h₁ : w.src.label = Γ.head w.edge := w.2.1
      have h₂ : w.tgt.label = Γ.tail w.edge := w.2.2.1
      rw [hsrc] at h₁
      rw [htgt] at h₂
      refine hr ⟨.inl ⟨(w.edge, a, b), h₁, h₂, fun e => w.2.2.2 ?_⟩, ?_⟩
      · have e' : a = b := e
        show w.src = w.tgt
        rw [hsrc, htgt, e']
      · exact congrArg Sum.inl (Subtype.ext (Prod.ext rfl (Prod.ext hsrc.symm htgt.symm)))
  · have e₀ : d.fst.1 = d.snd.1 := d.2.1
    have r₀ : d.fst.2.val < d.snd.2.val := d.2.2
    rcases ha : (strandEquiv ν' ν'').symm d.fst with a | a <;>
      rcases hb : (strandEquiv ν' ν'').symm d.snd with b | b <;>
      have hf := (Equiv.symm_apply_eq _).1 ha <;> have hs := (Equiv.symm_apply_eq _).1 hb <;>
      rw [hf, hs] at e₀ r₀
    · exfalso
      have e₁ : ((strandEquiv ν' ν'' (.inl a)).1 : I) = (strandEquiv ν' ν'' (.inl b)).1 :=
        congrArg Subtype.val e₀
      refine hl ⟨.inr ⟨(a, b), Subtype.ext e₁, r₀⟩, ?_⟩
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hf.symm hs.symm))
    · have hv : Hyp.val (Sum.inr d : Hyp Γ (ν' + ν'')) (juxt p' p'' c) = (p'' b + c) - p' a := by
        show juxt p' p'' c d.snd - juxt p' p'' c d.fst = _
        unfold juxt
        rw [ha, hb]
        rfl
      have hB := lt_bound_diag (Γ := Γ) p' p'' a b
      have h1 := neg_abs_le (p'' b)
      have h2 := le_abs_self (p' a)
      have hpos : 0 < Hyp.val (Sum.inr d : Hyp Γ (ν' + ν'')) (juxt p' p'' c) := by rw [hv]; linarith
      exact ⟨hpos.ne', iff_of_true hpos rfl⟩
    · exfalso
      have hcol : ν' (a.1 : I) = ν' (b.1 : I) := by
        have : (a.1 : I) = (b.1 : I) := congrArg Subtype.val e₀
        rw [this]
      have r₁ : ν' (a.1 : I) + a.2.val < b.2.val := r₀
      have := b.2.2
      omega
    · exfalso
      have e₁ : ((strandEquiv ν' ν'' (.inr a)).1 : I) = (strandEquiv ν' ν'' (.inr b)).1 :=
        congrArg Subtype.val e₀
      have hcol : a.1 = b.1 := Subtype.ext e₁
      have hν : ν' (a.1 : I) = ν' (b.1 : I) := by rw [hcol]
      have r₁ : ν' (a.1 : I) + a.2.val < ν' (b.1 : I) + b.2.val := r₀
      refine hr ⟨.inr ⟨(a, b), hcol, by show a.2.val < b.2.val; omega⟩, ?_⟩
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hf.symm hs.symm))

omit [DecidableEq I] in
theorem isGeneric_juxt {p' : Strand ν' → 𝕜} {p'' : Strand ν'' → 𝕜} (hp' : IsGeneric Γ p')
    (hp'' : IsGeneric Γ p'') {c : 𝕜} (hc : bound Γ p' p'' ≤ c) :
    IsGeneric Γ (juxt p' p'' c) := by
  intro h
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hl
    rw [val_left]
    exact hp' h'
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hr
    rw [val_right]
    exact hp'' h'
  exact (val_cross p' p'' hc hl hr).1

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem fullSigns_juxt_left (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜)
    (h : Hyp Γ ν') : fullSigns (juxt p' p'' c) ((leftEmb ν' ν'').hyp h) = fullSigns p' h := by
  simp only [fullSigns, val_left]

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem fullSigns_juxt_right (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜)
    (h : Hyp Γ ν'') : fullSigns (juxt p' p'' c) ((rightEmb ν' ν'').hyp h) = fullSigns p'' h := by
  simp only [fullSigns, val_right]

omit [DecidableEq I] in
theorem fullSigns_juxt_cross (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) {c : 𝕜}
    (hc : bound Γ p' p'' ≤ c) {h : Hyp Γ (ν' + ν'')}
    (hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)))
    (hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))) :
    fullSigns (juxt p' p'' c) h = crossSign h := by
  rw [Bool.eq_iff_iff]
  simp only [fullSigns, decide_eq_true_iff]
  exact (val_cross p' p'' hc hl hr).2

/-! ### The juxtaposed chamber -/

/-- A configuration in a full chamber. -/
noncomputable def point {ν : I →₀ ℕ} (C : FullChamber Γ ν) : Strand ν → 𝕜 := C.2.choose

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem isGeneric_point {ν : I →₀ ℕ} (C : FullChamber Γ ν) : IsGeneric Γ (point C) :=
  C.2.choose_spec.1

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem fullSigns_point {ν : I →₀ ℕ} (C : FullChamber Γ ν) : fullSigns (Γ := Γ) (point C) = C.1 :=
  C.2.choose_spec.2

/-- The juxtaposition `C' ∘ C''` of two full chambers. -/
noncomputable def chamber (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    FullChamber Γ (ν' + ν'') :=
  .ofPoint (juxt (point C') (point C'') (bound Γ (point C') (point C'')))
    (isGeneric_juxt (isGeneric_point C') (isGeneric_point C'') le_rfl)

omit [DecidableEq I] in
theorem chamber_left (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') (h : Hyp Γ ν') :
    (chamber C' C'').1 ((leftEmb ν' ν'').hyp h) = C'.1 h := by
  show fullSigns _ _ = _
  rw [fullSigns_juxt_left, fullSigns_point]

omit [DecidableEq I] in
theorem chamber_right (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') (h : Hyp Γ ν'') :
    (chamber C' C'').1 ((rightEmb ν' ν'').hyp h) = C''.1 h := by
  show fullSigns _ _ = _
  rw [fullSigns_juxt_right, fullSigns_point]

omit [DecidableEq I] in
theorem chamber_cross (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') {h : Hyp Γ (ν' + ν'')}
    (hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)))
    (hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))) :
    (chamber C' C'').1 h = crossSign h :=
  fullSigns_juxt_cross _ _ le_rfl hl hr

omit [DecidableEq I] in
/-- Any juxtaposition at large separation of configurations in `C'` and `C''` lies in
`C' ∘ C''`. -/
theorem ofPoint_eq_chamber {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {p' : Strand ν' → 𝕜} {p'' : Strand ν'' → 𝕜} (hs' : fullSigns (Γ := Γ) p' = C'.1)
    (hs'' : fullSigns (Γ := Γ) p'' = C''.1) {c : 𝕜} (hc : bound Γ p' p'' ≤ c)
    (q : Strand (ν' + ν'') → 𝕜) (hq : IsGeneric Γ q) (hqe : q = juxt p' p'' c) :
    FullChamber.ofPoint q hq = chamber C' C'' := by
  subst hqe
  apply Subtype.ext
  funext h
  show fullSigns _ h = (chamber C' C'').1 h
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hl
    rw [fullSigns_juxt_left, chamber_left, hs']
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hr
    rw [fullSigns_juxt_right, chamber_right, hs'']
  rw [fullSigns_juxt_cross _ _ hc hl hr, chamber_cross _ _ hl hr]

omit [DecidableEq I] in
/-- `C' ∘ C''` is rank ordered exactly when `C'` and `C''` are. -/
theorem isRankOrdered_chamber_iff (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    (chamber C' C'').IsRankOrdered ↔ C'.IsRankOrdered ∧ C''.IsRankOrdered := by
  refine ⟨fun h => ⟨fun d => ?_, fun d => ?_⟩, fun ⟨h', h''⟩ d => ?_⟩
  · rw [← chamber_left C' C'' (.inr d)]
    exact h _
  · rw [← chamber_right C' C'' (.inr d)]
    exact h _
  by_cases hl : (.inr d : Hyp Γ (ν' + ν'')) ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h₀, hh⟩ := hl
    rcases h₀ with w | d'
    · exact absurd hh (by simp)
    · rw [← hh, chamber_left]
      exact h' d'
  by_cases hr : (.inr d : Hyp Γ (ν' + ν'')) ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h₀, hh⟩ := hr
    rcases h₀ with w | d'
    · exact absurd hh (by simp)
    · rw [← hh, chamber_right]
      exact h'' d'
  rw [chamber_cross C' C'' hl hr]
  rfl

/-! ### Extending relabellings -/

variable (ν' ν'') in
/-- Relabelling the two sides independently. -/
noncomputable def colPermProd : ColPerm ν' × ColPerm ν'' →* ColPerm (ν' + ν'') :=
  MonoidHom.codRestrict
    (((strandEquiv ν' ν'').permCongrHom.toMonoidHom.comp (Perm.sumCongrHom _ _)).comp
      (((ColPerm ν').subtype).prodMap (ColPerm ν'').subtype))
    (ColPerm (ν' + ν''))
    (fun g => by
      show ∀ t, _ = _
      intro t
      obtain ⟨x, rfl⟩ := (strandEquiv ν' ν'').surjective t
      rcases x with a | b
      · show (strandEquiv ν' ν'' (Perm.sumCongr g.1.1 g.2.1
            ((strandEquiv ν' ν'').symm (strandEquiv ν' ν'' (.inl a))))).1 = _
        rw [Equiv.symm_apply_apply]
        exact Subtype.ext (show ((g.1.1 a).1 : I) = (a.1 : I) from
          congrArg Subtype.val (g.1.2 a))
      · show (strandEquiv ν' ν'' (Perm.sumCongr g.1.1 g.2.1
            ((strandEquiv ν' ν'').symm (strandEquiv ν' ν'' (.inr b))))).1 = _
        rw [Equiv.symm_apply_apply]
        exact Subtype.ext (show ((g.2.1 b).1 : I) = (b.1 : I) from
          congrArg Subtype.val (g.2.2 b)))

omit [DecidableEq I] in
@[simp] theorem colPermProd_inl (g : ColPerm ν' × ColPerm ν'') (s : Strand ν') :
    (colPermProd ν' ν'' g).1 (inlStrand ν' ν'' s) = inlStrand ν' ν'' (g.1.1 s) := by
  show strandEquiv ν' ν'' (Perm.sumCongr g.1.1 g.2.1
    ((strandEquiv ν' ν'').symm (strandEquiv ν' ν'' (.inl s)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

omit [DecidableEq I] in
@[simp] theorem colPermProd_inr (g : ColPerm ν' × ColPerm ν'') (s : Strand ν'') :
    (colPermProd ν' ν'' g).1 (inrStrand ν' ν'' s) = inrStrand ν' ν'' (g.2.1 s) := by
  show strandEquiv ν' ν'' (Perm.sumCongr g.1.1 g.2.1
    ((strandEquiv ν' ν'').symm (strandEquiv ν' ν'' (.inr s)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

variable (ν' ν'') in
/-- A relabelling of `ν'` extended by the identity on the strands of `ν''`. -/
noncomputable def leftPerm : ColPerm ν' →* ColPerm (ν' + ν'') :=
  (colPermProd ν' ν'').comp (MonoidHom.inl _ _)

variable (ν' ν'') in
/-- A relabelling of `ν''` extended by the identity on the strands of `ν'`. -/
noncomputable def rightPerm : ColPerm ν'' →* ColPerm (ν' + ν'') :=
  (colPermProd ν' ν'').comp (MonoidHom.inr _ _)

omit [DecidableEq I] in
theorem leftPerm_mul_rightPerm (g : ColPerm ν') (h : ColPerm ν'') :
    leftPerm ν' ν'' g * rightPerm ν' ν'' h = rightPerm ν' ν'' h * leftPerm ν' ν'' g := by
  simp only [leftPerm, rightPerm, MonoidHom.comp_apply, ← map_mul, MonoidHom.inl_apply,
    MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one, one_mul]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem act_colPermProd (g : ColPerm ν' × ColPerm ν'') (p' : Strand ν' → 𝕜)
    (p'' : Strand ν'' → 𝕜) (c : 𝕜) :
    act (colPermProd ν' ν'' g) (juxt p' p'' c) = juxt (act g.1 p') (act g.2 p'') c := by
  funext t
  obtain ⟨x, rfl⟩ := (strandEquiv ν' ν'').surjective t
  have hinv : (colPermProd ν' ν'' g).1⁻¹ = (colPermProd ν' ν'' g⁻¹).1 := by
    rw [map_inv]
    rfl
  rcases x with a | b
  · show juxt p' p'' c ((colPermProd ν' ν'' g).1⁻¹ (inlStrand ν' ν'' a)) = _
    rw [hinv, colPermProd_inl, juxt_inl, strandEquiv_inl, juxt_inl]
    rfl
  · show juxt p' p'' c ((colPermProd ν' ν'' g).1⁻¹ (inrStrand ν' ν'' b)) = _
    rw [hinv, colPermProd_inr, juxt_inr, strandEquiv_inr, juxt_inr]
    rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem bound_act (g : ColPerm ν' × ColPerm ν'') (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) :
    bound Γ (act g.1 p') (act g.2 p'') = bound Γ p' p'' := by
  unfold bound act
  rw [Equiv.sum_comp (g.1.1⁻¹) (fun s => |p' s|), Equiv.sum_comp (g.2.1⁻¹) (fun s => |p'' s|)]

omit [DecidableEq I] in
/-- Relabelling the two sides relabels the juxtaposed chamber. -/
theorem colPermProd_smul_chamber (g : ColPerm ν' × ColPerm ν'') (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    colPermProd ν' ν'' g • chamber C' C'' = chamber (g.1 • C') (g.2 • C'') := by
  unfold chamber
  rw [FullChamber.smul_ofPoint]
  refine ofPoint_eq_chamber (p' := act g.1 (point C')) (p'' := act g.2 (point C''))
    ?_ ?_ (bound_act (Γ := Γ) g _ _).le _ _ (act_colPermProd g _ _ _)
  · rw [fullSigns_act (isGeneric_point C'), fullSigns_point]
    rfl
  · rw [fullSigns_act (isGeneric_point C''), fullSigns_point]
    rfl

/-! ### The two chamber embeddings -/

omit [DecidableEq I] in
theorem chamber_of_not_mem_left (C D : FullChamber Γ ν') (C'' : FullChamber Γ ν'')
    (h : Hyp Γ (ν' + ν'')) (hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))) :
    (chamber C C'').1 h = (chamber D C'').1 h := by
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hr
    rw [chamber_right, chamber_right]
  · rw [chamber_cross _ _ hl hr, chamber_cross _ _ hl hr]

omit [DecidableEq I] in
theorem chamber_of_not_mem_right (C' : FullChamber Γ ν') (C D : FullChamber Γ ν'')
    (h : Hyp Γ (ν' + ν'')) (hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))) :
    (chamber C' C).1 h = (chamber C' D).1 h := by
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hl
    rw [chamber_left, chamber_left]
  · rw [chamber_cross _ _ hl hr, chamber_cross _ _ hl hr]

/-- The chamber embedding `C' ↦ C' ∘ C''` of the arrangement of `ν'`. -/
noncomputable def leftChamberEmb (C'' : FullChamber Γ ν'') :
    ChamberEmbedding Γ ν' (ν' + ν'') where
  toStrandEmbedding := leftEmb ν' ν''
  chamber C' := chamber C' C''
  chamber_hyp C' h := chamber_left C' C'' h
  chamber_of_not_mem C D h hl := chamber_of_not_mem_left C D C'' h hl
  perm := leftPerm ν' ν''
  perm_apply g s := colPermProd_inl (g, 1) s
  perm_apply_of_not_mem g t ht := by
    obtain ⟨x, rfl⟩ := (strandEquiv ν' ν'').surjective t
    rcases x with a | b
    · exact absurd ⟨a, rfl⟩ ht
    · exact colPermProd_inr (g, 1) b
  smul_chamber g C' := by
    have := colPermProd_smul_chamber (Γ := Γ) (g, 1) C' C''
    rw [one_smul] at this
    exact this

/-- The chamber embedding `C'' ↦ C' ∘ C''` of the arrangement of `ν''`. -/
noncomputable def rightChamberEmb (C' : FullChamber Γ ν') :
    ChamberEmbedding Γ ν'' (ν' + ν'') where
  toStrandEmbedding := rightEmb ν' ν''
  chamber C'' := chamber C' C''
  chamber_hyp C'' h := chamber_right C' C'' h
  chamber_of_not_mem C D h hr := chamber_of_not_mem_right C' C D h hr
  perm := rightPerm ν' ν''
  perm_apply g s := colPermProd_inr (1, g) s
  perm_apply_of_not_mem g t ht := by
    obtain ⟨x, rfl⟩ := (strandEquiv ν' ν'').surjective t
    rcases x with a | b
    · exact colPermProd_inl (1, g) a
    · exact absurd ⟨b, rfl⟩ ht
  smul_chamber g C'' := by
    have := colPermProd_smul_chamber (Γ := Γ) (1, g) C' C''
    rw [one_smul] at this
    exact this

end Juxtapose

end Categorification.WeightedKLR
