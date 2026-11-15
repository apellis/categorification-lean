/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Arrangement

/-!
# Relabelling strands of one colour

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1.

Strands keep their labels along a diagram (`Arrangement.lean`), so when two strands of one
colour cross, the configuration leaves the rank-ordered region. The group of
colour-preserving permutations of the strands acts on configurations, and hence on full
chambers, by relabelling. Crossing the diagonal `x_s = x_{s'}` from a full chamber `C`
lands in the image of `C` under the transposition of `s` and `s'`.

## Main definitions

* `ColPerm ν`: the colour-preserving permutations of `Strand ν`.
* `act g p`: the configuration `p ∘ g⁻¹`.
* `Hyp.comap g h`, `Hyp.reverses g h`: the hyperplane `h` read in the old labels, and
  whether this reverses its orientation (a diagonal whose two strands change rank order).
* The action of `ColPerm ν` on `FullChamber Γ ν` (`FullChamber.smul_ofPoint`).
* `Diag.refl d`: the transposition of the two strands of the diagonal `d`.

## Main results

* `FullChamber.Adjacent.exists_facet`: two full chambers adjacent across `h` share a point of
  `h` on no other hyperplane.
* `FullChamber.Adjacent.refl_smul`: crossing the diagonal `d` from `C` gives `d.refl • C`.
-/

namespace Categorification.WeightedKLR

open Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- Two strands of the same colour and the same rank are equal. -/
theorem Strand.ext_of {s t : Strand ν} (h₁ : s.1 = t.1) (h₂ : s.2.val = t.2.val) : s = t := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  simp only at h₁ h₂
  subst h₁
  cases Fin.ext h₂
  rfl

variable (ν) in
/-- The permutations of the strands preserving colours. -/
def ColPerm : Subgroup (Perm (Strand ν)) where
  carrier := {g | ∀ s, (g s).1 = s.1}
  mul_mem' {g h} hg hh := by
    have hg' : ∀ s, (g s).1 = s.1 := hg
    have hh' : ∀ s, (h s).1 = s.1 := hh
    show ∀ s, (g (h s)).1 = s.1
    intro s
    rw [hg', hh']
  one_mem' := by
    show ∀ s : Strand ν, ((1 : Perm (Strand ν)) s).1 = s.1
    intro s
    rfl
  inv_mem' {g} hg := by
    have hg' : ∀ s, (g s).1 = s.1 := hg
    show ∀ s, (g⁻¹ s).1 = s.1
    intro s
    have := hg' (g⁻¹ s)
    have e : g (g⁻¹ s) = s := g.apply_symm_apply s
    rw [e] at this
    exact this.symm

omit [DecidableEq I] in
theorem mem_colPerm {g : Perm (Strand ν)} : g ∈ ColPerm ν ↔ ∀ s, (g s).1 = s.1 := Iff.rfl

namespace ColPerm

omit [DecidableEq I] in
@[simp] theorem apply_fst (g : ColPerm ν) (s : Strand ν) : (g.1 s).1 = s.1 := g.2 s

omit [DecidableEq I] in
@[simp] theorem inv_apply_fst (g : ColPerm ν) (s : Strand ν) : (g.1⁻¹ s).1 = s.1 :=
  (g⁻¹).2 s

end ColPerm

/-- Relabelling a configuration: the strand `g s` sits where `s` sat. -/
def act (g : ColPerm ν) (p : Strand ν → 𝕜) : Strand ν → 𝕜 := fun t => p (g.1⁻¹ t)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem act_one (p : Strand ν → 𝕜) : act 1 p = p := rfl

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem act_mul (g h : ColPerm ν) (p : Strand ν → 𝕜) : act (g * h) p = act g (act h p) := by
  funext t
  simp only [act, Subgroup.coe_mul, mul_inv_rev, Perm.mul_apply]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem act_lineMap (g : ColPerm ν) (p p' : Strand ν → 𝕜) (t : 𝕜) :
    act g ((1 - t) • p + t • p') = (1 - t) • act g p + t • act g p' := rfl

/-- The wall `w` read in the labels before relabelling by `g`. -/
def Wall.comap (g : ColPerm ν) (w : Wall Γ ν) : Wall Γ ν :=
  ⟨(w.edge, g.1⁻¹ w.src, g.1⁻¹ w.tgt), by
    refine ⟨?_, ?_, ?_⟩
    · simp only [Strand.label, ColPerm.inv_apply_fst]
      exact w.2.1
    · simp only [Strand.label, ColPerm.inv_apply_fst]
      exact w.2.2.1
    · exact fun h => w.2.2.2 ((g.1⁻¹).injective h)⟩

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.val_act (g : ColPerm ν) (w : Wall Γ ν) (p : Strand ν → 𝕜) :
    w.val (act g p) = (w.comap g).val p := rfl

/-- The diagonal `d` read in the labels before relabelling by `g`, and whether the rank order of
its two strands is reversed. -/
def Diag.comap (g : ColPerm ν) (d : Diag ν) : Diag ν × Bool :=
  if h : (g.1⁻¹ d.fst).2.val < (g.1⁻¹ d.snd).2.val then
    (⟨(g.1⁻¹ d.fst, g.1⁻¹ d.snd), by
      show (g.1⁻¹ d.fst).1 = (g.1⁻¹ d.snd).1
      rw [ColPerm.inv_apply_fst, ColPerm.inv_apply_fst]
      exact d.2.1, h⟩, false)
  else
    (⟨(g.1⁻¹ d.snd, g.1⁻¹ d.fst), by
      show (g.1⁻¹ d.snd).1 = (g.1⁻¹ d.fst).1
      rw [ColPerm.inv_apply_fst, ColPerm.inv_apply_fst]
      exact d.2.1.symm,
      lt_of_le_of_ne (not_lt.1 h) fun e =>
        d.fst_ne_snd ((g.1⁻¹).injective (Strand.ext_of (by
          rw [ColPerm.inv_apply_fst, ColPerm.inv_apply_fst]
          exact d.2.1.symm) e)).symm⟩,
      true)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Diag.val_act (g : ColPerm ν) (d : Diag ν) (p : Strand ν → 𝕜) :
    d.val (act g p) = if (d.comap g).2 then -(d.comap g).1.val p else (d.comap g).1.val p := by
  by_cases h : (g.1⁻¹ d.fst).2.val < (g.1⁻¹ d.snd).2.val
  · simp only [Diag.comap, h, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [Diag.comap, h, ↓reduceDIte, ↓reduceIte]
    simp only [Diag.val, Diag.fst, Diag.snd, act]
    ring

namespace Hyp

/-- The hyperplane `h` read in the labels before relabelling by `g`. -/
def comap (g : ColPerm ν) : Hyp Γ ν → Hyp Γ ν
  | .inl w => .inl (w.comap g)
  | .inr d => .inr (d.comap g).1

/-- Whether relabelling by `g` reverses the orientation of `h`. -/
def reverses (g : ColPerm ν) : Hyp Γ ν → Bool
  | .inl _ => false
  | .inr d => (d.comap g).2

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_act (g : ColPerm ν) (h : Hyp Γ ν) (p : Strand ν → 𝕜) :
    h.val (act g p) = if h.reverses g then -(h.comap g).val p else (h.comap g).val p := by
  rcases h with w | d
  · simp [reverses, comap, val, Wall.val_act]
  · exact Diag.val_act g d p

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Hyperplane values are affine along segments. -/
theorem val_lineMap (h : Hyp Γ ν) (p p' : Strand ν → 𝕜) (t : 𝕜) :
    h.val ((1 - t) • p + t • p') = (1 - t) * h.val p + t * h.val p' := by
  rcases h with w | d
  · simp only [val, Wall.val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [val, Diag.val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_segment (h : Hyp Γ ν) (q x : Strand ν → 𝕜) (t : 𝕜) :
    h.val ((1 - t) • q + t • x) = h.val q + t * (h.val x - h.val q) := by
  rw [val_lineMap]
  ring

end Hyp

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsGeneric.act {p : Strand ν → 𝕜} (hp : IsGeneric Γ p) (g : ColPerm ν) :
    IsGeneric Γ (act g p) := by
  intro h
  rw [Hyp.val_act]
  split_ifs
  · exact neg_ne_zero.2 (hp _)
  · exact hp _

/-- The action of a relabelling on sign vectors. -/
def signMap (g : ColPerm ν) (σ : Hyp Γ ν → Bool) : Hyp Γ ν → Bool := fun h =>
  if h.reverses g then !σ (h.comap g) else σ (h.comap g)

omit [DecidableEq I] in
theorem fullSigns_act {p : Strand ν → 𝕜} (hp : IsGeneric Γ p) (g : ColPerm ν) :
    fullSigns (Γ := Γ) (act g p) = signMap g (fullSigns p) := by
  funext h
  simp only [fullSigns, signMap, Hyp.val_act]
  split_ifs
  · rcases lt_or_gt_of_ne (hp (h.comap g)) with hx | hx
    · simp [hx, not_lt.2 hx.le]
    · simp [hx, not_lt.2 hx.le]
  · rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem fullSigns_eq_of {z : Strand ν → 𝕜} {σ : Hyp Γ ν → Bool}
    (h : ∀ h, h.val z ≠ 0 ∧ (0 < h.val z ↔ σ h = true)) :
    IsGeneric Γ z ∧ fullSigns z = σ :=
  ⟨fun h' => (h h').1, funext fun h' => by simp [fullSigns, (h h').2]⟩

namespace FullChamber

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem exists_eq_ofPoint (C : FullChamber Γ ν) :
    ∃ p, ∃ hp : IsGeneric Γ p, C = ofPoint p hp := by
  obtain ⟨p, hp, hs⟩ := C.2
  exact ⟨p, hp, Subtype.ext hs.symm⟩

instance : SMul (ColPerm ν) (FullChamber Γ ν) where
  smul g C := ⟨signMap g C.1, by
    obtain ⟨p, hp, hs⟩ := C.2
    exact ⟨act g p, hp.act g, by rw [fullSigns_act hp, hs]⟩⟩

omit [DecidableEq I] in
theorem smul_ofPoint (g : ColPerm ν) {p : Strand ν → 𝕜} (hp : IsGeneric Γ p) :
    g • ofPoint p hp = ofPoint (act g p) (hp.act g) :=
  Subtype.ext (fullSigns_act hp g).symm

instance : MulAction (ColPerm ν) (FullChamber Γ ν) where
  one_smul C := by
    obtain ⟨p, hp, rfl⟩ := C.exists_eq_ofPoint
    rw [smul_ofPoint]
    rfl
  mul_smul g h C := by
    obtain ⟨p, hp, rfl⟩ := C.exists_eq_ofPoint
    rw [smul_ofPoint, smul_ofPoint, smul_ofPoint]
    apply Subtype.ext
    show fullSigns (act (g * h) p) = fullSigns (act g (act h p))
    rw [act_mul]

end FullChamber

/-! ### Small perturbations -/

omit [DecidableEq I] in
theorem exists_pos_small {ι : Type*} [Fintype ι] (a c c' : ι → 𝕜) :
    ∃ t : 𝕜, 0 < t ∧ t ≤ 1 ∧ ∀ i, a i ≠ 0 → |t * c i| < |a i| ∧ |t * c' i| < |a i| := by
  set S := ∑ i, (|c i| + |c' i|) / |a i| with hS_def
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have h1S : 0 < 1 + S := by linarith
  refine ⟨1 / (1 + S), one_div_pos.2 h1S, (div_le_one h1S).2 (by linarith), fun i hi => ?_⟩
  have hai : 0 < |a i| := abs_pos.2 hi
  have hle : (|c i| + |c' i|) / |a i| ≤ S :=
    Finset.single_le_sum (f := fun i => (|c i| + |c' i|) / |a i|)
      (fun j _ => div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
      (Finset.mem_univ i)
  rw [div_le_iff₀ hai] at hle
  have key : ∀ x : 𝕜, |x| ≤ |c i| + |c' i| → |1 / (1 + S) * x| < |a i| := by
    intro x hx
    rw [abs_mul, abs_of_pos (one_div_pos.2 h1S), div_mul_eq_mul_div, one_mul,
      div_lt_iff₀ h1S]
    nlinarith [abs_nonneg (c i), abs_nonneg (c' i)]
  exact ⟨key _ (le_add_of_nonneg_right (abs_nonneg _)),
    key _ (le_add_of_nonneg_left (abs_nonneg _))⟩

omit [DecidableEq I] in
theorem pos_add_iff_of_abs_lt {a b : 𝕜} (ha : a ≠ 0) (hb : |b| < |a|) :
    (0 < a + b ↔ 0 < a) ∧ a + b ≠ 0 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hb
  rcases lt_or_gt_of_ne ha with h | h
  · rw [abs_of_neg h] at h1 h2
    have hab : a + b < 0 := by linarith
    exact ⟨⟨fun h' => (lt_asymm h' hab).elim, fun h' => (lt_asymm h' h).elim⟩, hab.ne⟩
  · rw [abs_of_pos h] at h1 h2
    have hab : 0 < a + b := by linarith
    exact ⟨⟨fun _ => h, fun _ => hab⟩, hab.ne'⟩

omit [DecidableEq I] in
theorem convex_sign {x y t : 𝕜} (hx : x ≠ 0) (hxy : 0 < x ↔ 0 < y) (ht0 : 0 < t)
    (ht1 : t < 1) : (1 - t) * x + t * y ≠ 0 ∧ (0 < (1 - t) * x + t * y ↔ 0 < x) := by
  have h1 : 0 < 1 - t := sub_pos.2 ht1
  rcases lt_or_gt_of_ne hx with h | h
  · have hy : y ≤ 0 := not_lt.1 fun hy => (lt_asymm h (hxy.2 hy)).elim
    have : (1 - t) * x + t * y < 0 := by
      linarith [mul_neg_of_pos_of_neg h1 h, mul_nonneg ht0.le (neg_nonneg.2 hy)]
    exact ⟨this.ne, ⟨fun h' => (lt_asymm h' this).elim, fun h' => (lt_asymm h' h).elim⟩⟩
  · have hy := hxy.1 h
    have : 0 < (1 - t) * x + t * y := by linarith [mul_pos h1 h, mul_pos ht0 hy]
    exact ⟨this.ne', ⟨fun _ => h, fun _ => this⟩⟩

omit [DecidableEq I] in
theorem exists_zero_on_segment {a b : 𝕜} (ha : a ≠ 0) (hb : b ≠ 0) (hs : ¬(0 < a ↔ 0 < b)) :
    ∃ t : 𝕜, 0 < t ∧ t < 1 ∧ (1 - t) * a + t * b = 0 := by
  rcases lt_or_gt_of_ne ha with h | h
  · have hb' : 0 < b := by
      rcases lt_or_gt_of_ne hb with h' | h'
      · exact (hs ⟨fun x => (lt_asymm x h).elim, fun x => (lt_asymm x h').elim⟩).elim
      · exact h'
    have hd : 0 < b - a := by linarith
    refine ⟨-a / (b - a), div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith), ?_⟩
    have := div_mul_cancel₀ (-a) hd.ne'
    linear_combination this
  · have hb' : b < 0 := by
      rcases lt_or_gt_of_ne hb with h' | h'
      · exact h'
      · exact (hs ⟨fun _ => h', fun _ => h⟩).elim
    have hd : 0 < a - b := by linarith
    refine ⟨a / (a - b), div_pos h hd, (div_lt_one hd).2 (by linarith), ?_⟩
    have := div_mul_cancel₀ a hd.ne'
    linear_combination -this

/-! ### Crossing a diagonal -/

/-- The transposition of the two strands of a diagonal. -/
def Diag.refl (d : Diag ν) : ColPerm ν :=
  ⟨swap d.fst d.snd, mem_colPerm.2 fun s => by
    rcases eq_or_ne s d.fst with rfl | h1
    · rw [swap_apply_left]
      exact d.2.1.symm
    rcases eq_or_ne s d.snd with rfl | h2
    · rw [swap_apply_right]
      exact d.2.1
    · rw [swap_apply_of_ne_of_ne h1 h2]⟩

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Diag.val_act_refl (d : Diag ν) (p : Strand ν → 𝕜) : d.val (act d.refl p) = -d.val p := by
  show p ((swap d.fst d.snd)⁻¹ d.snd) - p ((swap d.fst d.snd)⁻¹ d.fst) = -(p d.snd - p d.fst)
  rw [swap_inv, swap_apply_left, swap_apply_right]
  ring

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Diag.act_refl_of {d : Diag ν} {q : Strand ν → 𝕜} (hq : q d.fst = q d.snd) :
    act d.refl q = q := by
  funext s
  show q ((swap d.fst d.snd)⁻¹ s) = q s
  rw [swap_inv]
  rcases eq_or_ne s d.fst with rfl | h1
  · rw [swap_apply_left]
    exact hq.symm
  rcases eq_or_ne s d.snd with rfl | h2
  · rw [swap_apply_right]
    exact hq
  · rw [swap_apply_of_ne_of_ne h1 h2]

namespace FullChamber

omit [DecidableEq I] in
/-- Two full chambers adjacent across `h₀` share a point of `h₀` lying on no other hyperplane,
on the side of `C` (equivalently of `C'`) of each of them. -/
theorem Adjacent.exists_facet {C C' : FullChamber Γ ν} {h₀ : Hyp Γ ν} (hC : Adjacent C C' h₀) :
    ∃ q : Strand ν → 𝕜, h₀.val q = 0 ∧
      ∀ h, h ≠ h₀ → h.val q ≠ 0 ∧ (0 < h.val q ↔ C.1 h = true) := by
  obtain ⟨p, hp, hs⟩ := C.2
  obtain ⟨p', hp', hs'⟩ := C'.2
  have key : ∀ h, C.1 h = C'.1 h ↔ (0 < h.val p ↔ 0 < h.val p') := by
    intro h
    rw [← hs, ← hs']
    simp [fullSigns]
  obtain ⟨t, ht0, ht1, hq⟩ :=
    exists_zero_on_segment (hp h₀) (hp' h₀) fun hiff => hC.1 ((key h₀).2 hiff)
  refine ⟨(1 - t) • p + t • p', by rw [Hyp.val_lineMap]; exact hq, fun h hh => ?_⟩
  rw [Hyp.val_lineMap]
  have := convex_sign (hp h) ((key h).1 (hC.2 h hh)) ht0 ht1
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hs]
  simp [fullSigns]

/-- Crossing the diagonal `d` from the full chamber `C` leads to `d.refl • C`: the
configurations after the crossing are those of `C` with the two strands of `d` exchanged. -/
theorem Adjacent.refl_smul {C C' : FullChamber Γ ν} {d : Diag ν} (hC : Adjacent C C' (.inr d)) :
    d.refl • C = C' := by
  obtain ⟨q, hq0, hq⟩ := hC.exists_facet
  obtain ⟨p, hp, hs⟩ := C.2
  have hx0 : d.val p ≠ 0 := hp (.inr d)
  have hd' : C'.1 (.inr d) = !C.1 (.inr d) := by
    have h1 := hC.1
    generalize C.1 (.inr d) = u at h1 ⊢
    generalize C'.1 (.inr d) = u' at h1 ⊢
    cases u <;> cases u' <;> simp_all
  obtain ⟨t, ht0, -, ht⟩ := exists_pos_small (fun h : Hyp Γ ν => h.val q)
    (fun h => h.val p - h.val q) (fun h => h.val (act d.refl p) - h.val q)
  have hrC : IsGeneric Γ ((1 - t) • q + t • p) ∧ fullSigns ((1 - t) • q + t • p) = C.1 := by
    refine fullSigns_eq_of fun h => ?_
    by_cases hh : h = .inr d
    · subst hh
      rw [Hyp.val_lineMap, hq0, mul_zero, zero_add, Hyp.val_inr]
      refine ⟨mul_ne_zero ht0.ne' hx0, ?_⟩
      rw [← hs]
      simp only [fullSigns, Hyp.val_inr]
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · have : ¬0 < t * d.val p := not_lt.2 (mul_neg_of_pos_of_neg ht0 hx).le
        simp [this, not_lt.2 hx.le]
      · simp [mul_pos ht0 hx, hx]
    · rw [Hyp.val_segment]
      have h1 := pos_add_iff_of_abs_lt (hq h hh).1 (ht h (hq h hh).1).1
      exact ⟨h1.2, h1.1.trans (hq h hh).2⟩
  have hrC' : IsGeneric Γ ((1 - t) • q + t • act d.refl p) ∧
      fullSigns ((1 - t) • q + t • act d.refl p) = C'.1 := by
    refine fullSigns_eq_of fun h => ?_
    by_cases hh : h = .inr d
    · subst hh
      rw [Hyp.val_lineMap, hq0, mul_zero, zero_add, Hyp.val_inr, Diag.val_act_refl, mul_neg]
      refine ⟨neg_ne_zero.2 (mul_ne_zero ht0.ne' hx0), ?_⟩
      rw [hd', ← hs]
      simp only [fullSigns, Hyp.val_inr]
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · have : 0 < -(t * d.val p) := neg_pos.2 (mul_neg_of_pos_of_neg ht0 hx)
        simp [this, not_lt.2 hx.le]
      · have : ¬0 < -(t * d.val p) := not_lt.2 (neg_nonpos.2 (mul_pos ht0 hx).le)
        simp [this, hx]
    · rw [Hyp.val_segment]
      have h1 := pos_add_iff_of_abs_lt (hq h hh).1 (ht h (hq h hh).1).2
      refine ⟨h1.2, h1.1.trans ((hq h hh).2.trans ?_)⟩
      rw [hC.2 h hh]
  have hqd : q d.fst = q d.snd := by
    have : d.val q = 0 := hq0
    rw [Diag.val, sub_eq_zero] at this
    exact this.symm
  have e : ofPoint _ hrC.1 = C := Subtype.ext hrC.2
  have e' : ofPoint _ hrC'.1 = C' := Subtype.ext hrC'.2
  rw [← e', ← e, smul_ofPoint]
  apply Subtype.ext
  show fullSigns (act d.refl ((1 - t) • q + t • p)) = fullSigns ((1 - t) • q + t • act d.refl p)
  rw [act_lineMap, Diag.act_refl_of hqd]

end FullChamber

end Categorification.WeightedKLR
