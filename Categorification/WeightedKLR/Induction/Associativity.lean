/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Induction.Juxtapose

/-!
# Associativity and unit of the juxtaposition of chambers

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Proposition
2.18 (monoidality of induction). The monoidal structure on `⊕_ν W^ϑ_ν`-modules comes from the
associativity and unit of the map `ι_{ν';ν''}` that places two diagrams side by side. This file
proves the combinatorial core of these on idempotents: juxtaposition of full chambers is
associative, and the unique full chamber of `0` is a unit for it, after the identifications
`(ν₁ + ν₂) + ν₃ = ν₁ + (ν₂ + ν₃)`, `ν + 0 = ν` and `0 + ν = ν` of dimension vectors.

The juxtaposition `C' ∘ C''` depends only on the sides of the hyperplanes: a generic
configuration lies in `C' ∘ C''` when its strands of `ν'` lie in `C'`, its strands of `ν''` lie
in `C''`, and every strand of `ν''` lies to the right of every strand of `ν'` by more than the
total weight (`ofPoint_eq_chamber_of_separated`). Associativity follows by placing configurations
of the three chambers at positions `0`, `c` and `2c` for large `c`.

## Main results

* `castChamber`: transport of full chambers along an equality of dimension vectors.
* `ofPoint_eq_chamber_of_separated`.
* `castChamber_chamber_assoc`: `(C₁ ∘ C₂) ∘ C₃ = C₁ ∘ (C₂ ∘ C₃)`.
* `castChamber_chamber_zero_right`, `castChamber_chamber_zero_left`: `C ∘ ∅ = C = ∅ ∘ C`.

The module-level statements of Proposition 2.18 (the associativity and unit isomorphisms for
`ind`, coassociativity of `res`) are not proved here.
-/

namespace Categorification.WeightedKLR

namespace Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

/-! ### Transport along an equality of dimension vectors -/

/-- A full chamber for `ν` as a full chamber for `μ`, along `ν = μ`. -/
def castChamber {ν μ : I →₀ ℕ} (h : ν = μ) (C : FullChamber Γ ν) : FullChamber Γ μ := h ▸ C

/-- A strand of `ν` as a strand of `μ`, along `ν = μ`. -/
def castStrand {ν μ : I →₀ ℕ} (h : ν = μ) (s : Strand ν) : Strand μ := h ▸ s

omit [DecidableEq I] in
theorem castStrand_colour {ν μ : I →₀ ℕ} (h : ν = μ) (s : Strand ν) :
    ((castStrand h s).1 : I) = s.1 := by
  subst h
  rfl

omit [DecidableEq I] in
theorem castStrand_rank {ν μ : I →₀ ℕ} (h : ν = μ) (s : Strand ν) :
    (castStrand h s).2.val = s.2.val := by
  subst h
  rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isGeneric_comp_castStrand {ν μ : I →₀ ℕ} (h : ν = μ) {q : Strand ν → 𝕜}
    (hq : IsGeneric Γ q) : IsGeneric Γ (q ∘ castStrand h.symm) := by
  subst h
  exact hq

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem castChamber_ofPoint {ν μ : I →₀ ℕ} (h : ν = μ) (q : Strand ν → 𝕜)
    (hq : IsGeneric Γ q) :
    castChamber h (FullChamber.ofPoint q hq) =
      FullChamber.ofPoint (q ∘ castStrand h.symm) (isGeneric_comp_castStrand h hq) := by
  subst h
  rfl

/-! ### Separated configurations -/

variable {ν' ν'' : I →₀ ℕ}

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_comp_left (q : Strand (ν' + ν'') → 𝕜) (h : Hyp Γ ν') :
    ((leftEmb ν' ν'').hyp h).val q = h.val (q ∘ inlStrand ν' ν'') :=
  StrandEmbedding.val_hyp _ h q

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_comp_right (q : Strand (ν' + ν'') → 𝕜) (h : Hyp Γ ν'') :
    ((rightEmb ν' ν'').hyp h).val q = h.val (q ∘ inrStrand ν' ν'') :=
  StrandEmbedding.val_hyp _ h q

omit [DecidableEq I] in
/-- A configuration whose strands of `ν''` lie to the right of its strands of `ν'` by more than
the total weight meets no hyperplane between the two sides, and lies on the side `crossSign`. -/
theorem val_cross_of_separated (q : Strand (ν' + ν'') → 𝕜)
    (hsep : ∀ a b, q (inlStrand ν' ν'' a) + ∑ e, |Γ.weight e| < q (inrStrand ν' ν'' b))
    {h : Hyp Γ (ν' + ν'')}
    (hl : h ∉ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ)))
    (hr : h ∉ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))) :
    h.val q ≠ 0 ∧ (0 < h.val q ↔ crossSign h = true) := by
  have hW : ∀ e, |Γ.weight e| ≤ ∑ e, |Γ.weight e| := fun e =>
    Finset.single_le_sum (f := fun e => |Γ.weight e|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ e)
  have hW₀ : 0 ≤ ∑ e, |Γ.weight e| := Finset.sum_nonneg fun _ _ => abs_nonneg _
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
    · have hv : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) q
          = q (inrStrand ν' ν'' b) - q (inlStrand ν' ν'' a) - Γ.weight w.edge := by
        show q w.tgt - q w.src - _ = _
        rw [hsrc, htgt]
        rfl
      have hs := hsep a b
      have h3 := le_abs_self (Γ.weight w.edge)
      have h4 := hW w.edge
      have hpos : 0 < Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) q := by rw [hv]; linarith
      refine ⟨hpos.ne', iff_of_true hpos ?_⟩
      simp [crossSign, hb]
    · have hv : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) q
          = q (inlStrand ν' ν'' b) - q (inrStrand ν' ν'' a) - Γ.weight w.edge := by
        show q w.tgt - q w.src - _ = _
        rw [hsrc, htgt]
        rfl
      have hs := hsep b a
      have h3 := neg_abs_le (Γ.weight w.edge)
      have h4 := hW w.edge
      have hneg : Hyp.val (Sum.inl w : Hyp Γ (ν' + ν'')) q < 0 := by rw [hv]; linarith
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
    · have hv : Hyp.val (Sum.inr d : Hyp Γ (ν' + ν'')) q
          = q (inrStrand ν' ν'' b) - q (inlStrand ν' ν'' a) := by
        show q d.snd - q d.fst = _
        rw [hf, hs]
        rfl
      have h5 := hsep a b
      have hpos : 0 < Hyp.val (Sum.inr d : Hyp Γ (ν' + ν'')) q := by rw [hv]; linarith
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
/-- A generic configuration lies in `C' ∘ C''` when its strands of `ν'` lie in `C'`, its strands
of `ν''` lie in `C''`, and its strands of `ν''` lie to the right of those of `ν'` by more than the
total weight. -/
theorem ofPoint_eq_chamber_of_separated {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    (q : Strand (ν' + ν'') → 𝕜) (hq : IsGeneric Γ q)
    (hs' : fullSigns (Γ := Γ) (q ∘ inlStrand ν' ν'') = C'.1)
    (hs'' : fullSigns (Γ := Γ) (q ∘ inrStrand ν' ν'') = C''.1)
    (hsep : ∀ a b, q (inlStrand ν' ν'' a) + ∑ e, |Γ.weight e| < q (inrStrand ν' ν'' b)) :
    FullChamber.ofPoint q hq = chamber C' C'' := by
  apply Subtype.ext
  funext h
  show fullSigns q h = (chamber C' C'').1 h
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hl
    rw [chamber_left, ← hs']
    simp only [fullSigns, val_comp_left]
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨h', rfl⟩ := hr
    rw [chamber_right, ← hs'']
    simp only [fullSigns, val_comp_right]
  rw [chamber_cross _ _ hl hr, Bool.eq_iff_iff]
  simp only [fullSigns, decide_eq_true_iff]
  exact (val_cross_of_separated q hsep hl hr).2

omit [DecidableEq I] in
/-- A configuration is generic when its two sides are generic and they are separated by more
than the total weight. -/
theorem isGeneric_of_separated (q : Strand (ν' + ν'') → 𝕜)
    (h' : IsGeneric Γ (q ∘ inlStrand ν' ν'')) (h'' : IsGeneric Γ (q ∘ inrStrand ν' ν''))
    (hsep : ∀ a b, q (inlStrand ν' ν'' a) + ∑ e, |Γ.weight e| < q (inrStrand ν' ν'' b)) :
    IsGeneric Γ q := by
  intro h
  by_cases hl : h ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨g, rfl⟩ := hl
    rw [val_comp_left]
    exact h' g
  by_cases hr : h ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
  · obtain ⟨g, rfl⟩ := hr
    rw [val_comp_right]
    exact h'' g
  exact (val_cross_of_separated q hsep hl hr).1

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem juxt_comp_inl (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) :
    juxt p' p'' c ∘ inlStrand ν' ν'' = p' :=
  funext fun s => juxt_inl p' p'' c s

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem juxt_comp_inr (p' : Strand ν' → 𝕜) (p'' : Strand ν'' → 𝕜) (c : 𝕜) :
    juxt p' p'' c ∘ inrStrand ν' ν'' = fun s => p'' s + c :=
  funext fun s => juxt_inr p' p'' c s

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem fullSigns_add_const {ν : I →₀ ℕ} (p : Strand ν → 𝕜) (c : 𝕜) :
    fullSigns (Γ := Γ) (fun s => p s + c) = fullSigns p := by
  funext h
  simp only [fullSigns, Hyp.val_add_const]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isGeneric_add_const {ν : I →₀ ℕ} {p : Strand ν → 𝕜} (hp : IsGeneric Γ p) (c : 𝕜) :
    IsGeneric Γ (fun s => p s + c) := fun h => by
  rw [Hyp.val_add_const]
  exact hp h

omit [DecidableEq I] in
theorem abs_le_sum {ν : I →₀ ℕ} (p : Strand ν → 𝕜) (s : Strand ν) : |p s| ≤ ∑ t, |p t| :=
  Finset.single_le_sum (f := fun t => |p t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

omit [DecidableEq I] in
theorem sum_abs_nonneg {ν : I →₀ ℕ} (p : Strand ν → 𝕜) : 0 ≤ ∑ t, |p t| :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq I] in
/-- Every strand of `ν' + ν''` comes from `ν'` or from `ν''`. -/
theorem strand_cases (t : Strand (ν' + ν'')) :
    (∃ s, t = inlStrand ν' ν'' s) ∨ ∃ s, t = inrStrand ν' ν'' s := by
  obtain ⟨u, rfl⟩ := (strandEquiv ν' ν'').surjective t
  rcases u with s | s
  · exact .inl ⟨s, rfl⟩
  · exact .inr ⟨s, rfl⟩

/-! ### Associativity -/

variable (ν₁ ν₂ ν₃ : I →₀ ℕ)

omit [DecidableEq I] in
theorem castStrand_inl_inl (s : Strand ν₁) :
    castStrand (add_assoc ν₁ ν₂ ν₃).symm (inlStrand ν₁ (ν₂ + ν₃) s) =
      inlStrand (ν₁ + ν₂) ν₃ (inlStrand ν₁ ν₂ s) :=
  Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)

omit [DecidableEq I] in
theorem castStrand_inr_inl (s : Strand ν₂) :
    castStrand (add_assoc ν₁ ν₂ ν₃).symm (inrStrand ν₁ (ν₂ + ν₃) (inlStrand ν₂ ν₃ s)) =
      inlStrand (ν₁ + ν₂) ν₃ (inrStrand ν₁ ν₂ s) :=
  Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)

omit [DecidableEq I] in
theorem castStrand_inr_inr (s : Strand ν₃) :
    castStrand (add_assoc ν₁ ν₂ ν₃).symm (inrStrand ν₁ (ν₂ + ν₃) (inrStrand ν₂ ν₃ s)) =
      inrStrand (ν₁ + ν₂) ν₃ s := by
  refine Strand.ext_of (Subtype.ext (castStrand_colour _ _)) ?_
  rw [castStrand_rank]
  show ν₁ (s.1 : I) + (ν₂ (s.1 : I) + s.2.val) = (ν₁ + ν₂) (s.1 : I) + s.2.val
  rw [Finsupp.add_apply]
  omega

variable {ν₁ ν₂ ν₃}

omit [DecidableEq I] in
/-- Juxtaposition of full chambers is associative:
`(C₁ ∘ C₂) ∘ C₃ = C₁ ∘ (C₂ ∘ C₃)` along `(ν₁ + ν₂) + ν₃ = ν₁ + (ν₂ + ν₃)`. -/
theorem castChamber_chamber_assoc (C₁ : FullChamber Γ ν₁) (C₂ : FullChamber Γ ν₂)
    (C₃ : FullChamber Γ ν₃) :
    castChamber (add_assoc ν₁ ν₂ ν₃) (chamber (chamber C₁ C₂) C₃) =
      chamber C₁ (chamber C₂ C₃) := by
  set p₁ := point C₁
  set p₂ := point C₂
  set p₃ := point C₃
  set W := ∑ e, |Γ.weight e|
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c := 1 + W + (∑ t, |p₁ t| + ∑ t, |p₂ t| + ∑ t, |p₃ t|)
  have h₁ := abs_le_sum p₁
  have h₂ := abs_le_sum p₂
  have h₃ := abs_le_sum p₃
  have n₁ := sum_abs_nonneg p₁
  have n₂ := sum_abs_nonneg p₂
  have n₃ := sum_abs_nonneg p₃
  have g₁ := isGeneric_point C₁
  have g₂ := isGeneric_point C₂
  have g₃ := isGeneric_point C₃
  -- separation of two of the three configurations, `p₂` (or `p₃`) shifted by `c`
  have sep₁₂ : ∀ a b, juxt p₁ p₂ c (inlStrand ν₁ ν₂ a) + W < juxt p₁ p₂ c (inrStrand ν₁ ν₂ b) := by
    intro a b
    rw [juxt_inl, juxt_inr]
    have := h₁ a; have := h₂ b; have := le_abs_self (p₁ a); have := neg_abs_le (p₂ b)
    linarith
  have sep₂₃ : ∀ a b, juxt p₂ p₃ c (inlStrand ν₂ ν₃ a) + W < juxt p₂ p₃ c (inrStrand ν₂ ν₃ b) := by
    intro a b
    rw [juxt_inl, juxt_inr]
    have := h₂ a; have := h₃ b; have := le_abs_self (p₂ a); have := neg_abs_le (p₃ b)
    linarith
  have G₁₂ : IsGeneric Γ (juxt p₁ p₂ c) := isGeneric_of_separated _
    (by rw [juxt_comp_inl]; exact g₁) (by rw [juxt_comp_inr]; exact isGeneric_add_const g₂ c)
    sep₁₂
  have G₂₃ : IsGeneric Γ (juxt p₂ p₃ c) := isGeneric_of_separated _
    (by rw [juxt_comp_inl]; exact g₂) (by rw [juxt_comp_inr]; exact isGeneric_add_const g₃ c)
    sep₂₃
  have E₁₂ : FullChamber.ofPoint _ G₁₂ = chamber C₁ C₂ := ofPoint_eq_chamber_of_separated _ _
    (by rw [juxt_comp_inl]; exact fullSigns_point C₁)
    (by rw [juxt_comp_inr, fullSigns_add_const]; exact fullSigns_point C₂) sep₁₂
  have E₂₃ : FullChamber.ofPoint _ G₂₃ = chamber C₂ C₃ := ofPoint_eq_chamber_of_separated _ _
    (by rw [juxt_comp_inl]; exact fullSigns_point C₂)
    (by rw [juxt_comp_inr, fullSigns_add_const]; exact fullSigns_point C₃) sep₂₃
  -- the two bracketings of the configuration `p₁, p₂ + c, p₃ + 2c`
  set qL := juxt (juxt p₁ p₂ c) p₃ (2 * c)
  set qR := juxt p₁ (juxt p₂ p₃ c) c
  have sepL : ∀ a b, qL (inlStrand (ν₁ + ν₂) ν₃ a) + W < qL (inrStrand (ν₁ + ν₂) ν₃ b) := by
    intro a b
    simp only [qL, juxt_inr, juxt_inl]
    have := h₃ b; have := neg_abs_le (p₃ b)
    rcases strand_cases a with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [juxt_inl]
      have := h₁ s; have := le_abs_self (p₁ s)
      linarith
    · rw [juxt_inr]
      have := h₂ s; have := le_abs_self (p₂ s)
      linarith
  have sepR : ∀ a b, qR (inlStrand ν₁ (ν₂ + ν₃) a) + W < qR (inrStrand ν₁ (ν₂ + ν₃) b) := by
    intro a b
    simp only [qR, juxt_inr, juxt_inl]
    have := h₁ a; have := le_abs_self (p₁ a)
    rcases strand_cases b with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [juxt_inl]
      have := h₂ s; have := neg_abs_le (p₂ s)
      linarith
    · rw [juxt_inr]
      have := h₃ s; have := neg_abs_le (p₃ s)
      linarith
  have genL : IsGeneric Γ qL := isGeneric_of_separated _
    (by rw [juxt_comp_inl]; exact G₁₂) (by rw [juxt_comp_inr]; exact isGeneric_add_const g₃ _)
    sepL
  have genR : IsGeneric Γ qR := isGeneric_of_separated _
    (by rw [juxt_comp_inl]; exact g₁) (by rw [juxt_comp_inr]; exact isGeneric_add_const G₂₃ _)
    sepR
  have EL : FullChamber.ofPoint qL genL = chamber (chamber C₁ C₂) C₃ :=
    ofPoint_eq_chamber_of_separated _ _
      (by rw [juxt_comp_inl]; exact congrArg Subtype.val E₁₂)
      (by rw [juxt_comp_inr, fullSigns_add_const]; exact fullSigns_point C₃) sepL
  have ER : FullChamber.ofPoint qR genR = chamber C₁ (chamber C₂ C₃) :=
    ofPoint_eq_chamber_of_separated _ _
      (by rw [juxt_comp_inl]; exact fullSigns_point C₁)
      (by rw [juxt_comp_inr, fullSigns_add_const]; exact congrArg Subtype.val E₂₃) sepR
  have hq : qL ∘ castStrand (add_assoc ν₁ ν₂ ν₃).symm = qR := by
    funext t
    simp only [Function.comp_apply]
    rcases strand_cases t with ⟨s, rfl⟩ | ⟨u, rfl⟩
    · rw [castStrand_inl_inl]
      simp only [qL, qR, juxt_inl]
    · rcases strand_cases u with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · rw [castStrand_inr_inl]
        simp only [qL, qR, juxt_inl, juxt_inr]
      · rw [castStrand_inr_inr]
        simp only [qL, qR, juxt_inr]
        ring
  rw [← EL, ← ER, castChamber_ofPoint]
  exact Subtype.ext (congrArg fullSigns hq)

/-! ### Unit -/

variable {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- The unique full chamber of `0` is a right unit for juxtaposition. -/
theorem castChamber_chamber_zero_right (C : FullChamber Γ ν) (C₀ : FullChamber Γ 0) :
    castChamber (add_zero ν) (chamber C C₀) = C := by
  rw [chamber, castChamber_ofPoint]
  apply Subtype.ext
  rw [← fullSigns_point C]
  show fullSigns _ = _
  congr 1
  funext t
  simp only [Function.comp_apply]
  have : castStrand (add_zero ν).symm t = inlStrand ν 0 t :=
    Strand.ext_of (Subtype.ext (castStrand_colour _ _)) (castStrand_rank _ _)
  rw [this, juxt_inl]

omit [DecidableEq I] in
/-- The unique full chamber of `0` is a left unit for juxtaposition. -/
theorem castChamber_chamber_zero_left (C₀ : FullChamber Γ 0) (C : FullChamber Γ ν) :
    castChamber (zero_add ν) (chamber C₀ C) = C := by
  rw [chamber, castChamber_ofPoint]
  apply Subtype.ext
  rw [← fullSigns_point C, ← fullSigns_add_const (point C) (bound Γ (point C₀) (point C))]
  show fullSigns _ = _
  congr 1
  funext t
  simp only [Function.comp_apply]
  have : castStrand (zero_add ν).symm t = inrStrand 0 ν t := by
    refine Strand.ext_of (Subtype.ext (castStrand_colour _ _)) ?_
    rw [castStrand_rank]
    show t.2.val = (0 : I →₀ ℕ) (t.1 : I) + t.2.val
    rw [Finsupp.zero_apply, zero_add]
  rw [this, juxt_inr]

end Juxtapose

end Categorification.WeightedKLR
