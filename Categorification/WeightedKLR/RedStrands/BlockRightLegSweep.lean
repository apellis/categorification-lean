/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockSlide

/-!
# Cancellation along the right leg of an interval exit

In Webster, arXiv:1309.3796v2, §6.1, after (6.21), the right leg moves the
second source red left through the intervening black strands. Its descending
crossing word factors through the individual loading projectors. Consequently a
one-crossing ideal membership test on the supported sources composes along this leg.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA

variable {I : Type} {k : Type*} [CommRing k] [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "desc" p:arg d:arg => List.reverse (List.range' p d)

/-- Loading reached when the red at position `p` of the exit is moved `d` places
to the right. Right multiplication by the descending leg returns to the exit. -/
def rightLegSweepLoading (s : Seq μ) (p d : ℕ) : Seq μ :=
  wordProd m (desc p d) • s

private theorem desc_succ (p d : ℕ) : desc p (d+1) = (p+d) :: desc p d := by
  rw [List.range'_concat]
  simp

omit [DecidableEq I] in
theorem rightLegSweepLoading_succ (s : Seq μ) (p d : ℕ) :
    rightLegSweepLoading s p (d+1) = sadj m (p+d) • rightLegSweepLoading s p d := by
  simp only [rightLegSweepLoading, desc_succ, wordProd_cons, mul_smul]

omit [DecidableEq I] in
/-- Each red–black step in the descending leg has the indicated source labels
and preserves the red order. -/
theorem rightLegSweepLoading_support (s : Seq μ) (p d : ℕ) (hd : p+d < m) (b : Fin ℓ)
    (hred : s.lbl ⟨p,by omega⟩ = .inr b)
    (hblack : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨p+z+1,by omega⟩ = .inl i) :
    (rightLegSweepLoading s p d).lbl ⟨p+d,hd⟩ = .inr b ∧
      redWord (rightLegSweepLoading s p d) = redWord s ∧
      ∀ z, (hz : z < d) → (rightLegSweepLoading s p (z+1)).lbl ⟨p+z,by omega⟩ = s.lbl ⟨p+z+1,by omega⟩ := by
  induction d with
  | zero => simp [rightLegSweepLoading, hred]
  | succ d ih =>
    have hj : p+d+1 < m := by omega
    obtain ⟨hr,ho,hprev⟩ := ih (by omega) hred (fun z hz => hblack z (by omega))
    have fixed : (rightLegSweepLoading s p d).lbl ⟨p+d+1,hj⟩ = s.lbl ⟨p+d+1,hj⟩ := by
      unfold rightLegSweepLoading
      rw [lbl_smul, ← wordProd_reverse, List.reverse_reverse]
      apply congrArg s.lbl
      apply wordProd_apply_of_forall_ne
      intro j hj'
      have := List.mem_range'.1 hj'
      dsimp
      constructor <;> omega
    obtain ⟨i,hi⟩ := hblack d (by omega)
    have hstep : redWord (rightLegSweepLoading s p (d+1)) = redWord (rightLegSweepLoading s p d) := by
      rw [rightLegSweepLoading_succ]
      apply redWord_sadj_smul _ hj
      rw [fixed, hi]
      simp
    refine ⟨?_, hstep.trans ho, ?_⟩
    · change (rightLegSweepLoading s p (d+1)).lbl ⟨p+d+1,hj⟩ = _
      rw [rightLegSweepLoading_succ, lbl_sadj, sadj_apply_right hj]
      exact hr
    · intro z hz
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hz) with hz' | rfl
      · exact hprev z hz'
      · rw [rightLegSweepLoading_succ, lbl_sadj, sadj_apply_left hj, fixed]

variable {A : Type*} [Ring A] [Algebra k A]
variable (φ : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν) →ₐ[k] A) (J : TwoSidedIdeal A)

private theorem sweep_mem (s t : Seq μ) (p d : ℕ)
    (step : ∀ z < d, ∀ x : A, φ (e t) * x * φ (e (rightLegSweepLoading s p (z+1))) = x →
      x * φ (ψ (p+z) * e (rightLegSweepLoading s p z)) ∈ J → x ∈ J)
    (x : A) (hx : φ (e t) * x * φ (e (rightLegSweepLoading s p d)) = x)
    (hm : x * φ (ψw (desc p d) * e s) ∈ J) : x ∈ J := by
  induction d generalizing x with
  | zero =>
    have he : φ (e t) * x * φ (e s) = x := by simpa [rightLegSweepLoading] using hx
    have hr : x * φ (e s) = x := by
      calc _ = (φ (e t) * x * φ (e s)) * φ (e s) := congrArg (· * φ (e s)) he.symm
           _ = x := by rw [mul_assoc _ (φ (e s)), ← map_mul φ, e_mul_self, he]
    simpa only [List.range'_zero, List.reverse_nil, ψw_nil, one_mul, hr] using hm
  | succ d ih =>
    let v := rightLegSweepLoading s p d
    let g := (ψ (p+d) * e v : R)
    have factor : g * (ψw (desc p d) * e s) = ψw (desc p (d+1)) * e s := by
      have cut : (e v * (ψw (desc p d) * e s) : R) = ψw (desc p d) * e s := by
        rw [← mul_assoc, e_mul_ψw]
        simp only [v, rightLegSweepLoading, inv_smul_smul, mul_assoc, e_mul_self]
      rw [desc_succ, ψw_cons]
      change ψ (p+d) * e v * _ = _
      rw [mul_assoc, cut, mul_assoc]
    have hleft : φ (e t) * x = x := by
      calc _ = φ (e t) * (φ (e t) * x * φ (e (rightLegSweepLoading s p (d+1)))) := congrArg (φ (e t) * ·) hx.symm
           _ = x := by rw [← mul_assoc, ← mul_assoc, ← map_mul φ, e_mul_self, hx]
    apply step d (by omega) x hx
    apply ih (fun z hz => step z (by omega)) (x * φ g)
    · change φ (e t) * (x * φ g) * φ (e v) = _
      rw [← mul_assoc (φ (e t)), hleft, mul_assoc, ← map_mul φ]
      change x * φ (ψ (p+d) * e v * e v) = _
      rw [mul_assoc, e_mul_self]
    · rwa [mul_assoc, ← map_mul φ, factor]

/-- A one-crossing membership test for a black immediately before the red `b`
composes through the actual descending sweep word. The ideal and quotient map
can in particular be the source higher ideal in the violated quotient, or the
zero ideal after passage to that quotient. -/
theorem mem_ideal_of_rightLegSweep (s t : Seq μ) (p d : ℕ) (hd : p+d < m) (b : Fin ℓ)
    (horder : redWord s = redWord t) (hred : s.lbl ⟨p,by omega⟩ = .inr b)
    (hblack : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨p+z+1,by omega⟩ = .inl i)
    (step : ∀ (j : ℕ) (hj : j+1 < m) (v : Seq μ) (i : I),
      redWord (sadj m j • v) = redWord t →
      (sadj m j • v).lbl ⟨j,by omega⟩ = .inl i → (sadj m j • v).lbl ⟨j+1,hj⟩ = .inr b →
      ∀ x : A, φ (e t) * x * φ (e (sadj m j • v)) = x → x * φ (ψ j * e v) ∈ J → x ∈ J)
    (x : A) (hx : φ (e t) * x * φ (e (rightLegSweepLoading s p d)) = x)
    (hm : x * φ (ψw (desc p d) * e s) ∈ J) : x ∈ J := by
  apply sweep_mem Q Λ φ J s t p d _ x hx hm
  intro z hz
  have h := rightLegSweepLoading_support s p (z+1) (by omega) b hred (fun q hq => hblack q (by omega))
  obtain ⟨i,hi⟩ := hblack z hz
  have hbl := (h.2.2 z (by omega)).trans hi
  rw [rightLegSweepLoading_succ] at hbl
  rw [rightLegSweepLoading_succ] at h
  simpa only [rightLegSweepLoading_succ] using
    step (p+z) (by omega) (rightLegSweepLoading s p z) i (h.2.1.trans horder) hbl h.1

private theorem desc_lowers (N p d : ℕ) (hd : p+d < N) (z : ℕ) (hz : z < d) :
    wordProd N (desc p d) ⟨p+z+1,by omega⟩ = ⟨p+z,by omega⟩ := by
  induction d with
  | zero => omega
  | succ d ih =>
    rw [desc_succ, wordProd_cons, Equiv.Perm.mul_apply]
    have hj : p+d+1 < N := by omega
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hz) with hz' | rfl
    · rw [ih (by omega) hz', sadj_apply_of_ne _ (by dsimp; omega) (by dsimp; omega)]
    · rw [wordProd_apply_of_forall_ne, sadj_apply_right hj]
      intro a ha
      have := List.mem_range'.1 (List.mem_reverse.1 ha)
      dsimp
      constructor <;> omega

/-- Cancellation for the extreme right exit of the interval. The upper joint is
the loading of the full extreme path; the red and black labels in the hypotheses
are read in the original exchanged-bottom loading. -/
theorem mem_ideal_of_intervalRightLeg (s t : Seq μ) (p d : ℕ) (hd : p+d+1 < m) (b : Fin ℓ)
    (hb : s.lbl ⟨p,by omega⟩ = .inr b)
    (hc : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨p+1+z,by omega⟩ = .inl i)
    (step : ∀ (j : ℕ) (hj : j+1 < m) (v : Seq μ) (i : I),
      redWord (sadj m j • v) = redWord t →
      (sadj m j • v).lbl ⟨j,by omega⟩ = .inl i → (sadj m j • v).lbl ⟨j+1,hj⟩ = .inr b →
      ∀ x : A, φ (e t) * x * φ (e (sadj m j • v)) = x → x * φ (ψ j * e v) ∈ J → x ∈ J) :
    let w := p :: List.range' (p+1) d
    let v := wordProd m w • s
    let u := wordProd m (desc (p+1) d ++ w) • s
    redWord v = redWord t → ∀ x : A, φ (e t) * x * φ (e u) = x →
      x * φ (ψw (desc (p+1) d) * e v) ∈ J → x ∈ J := by
  intro w v u ho x hx hm
  have hv : v = sadj m p • (wordProd m (List.range' (p+1) d) • s) := by
    simp only [v,w,wordProd_cons,mul_smul]
  have hu : u = rightLegSweepLoading v (p+1) d := by
    simp only [u,v,rightLegSweepLoading,wordProd_append,mul_smul]
  apply mem_ideal_of_rightLegSweep Q Λ φ J v t (p+1) d (by omega) b ho _ _ step x (hu ▸ hx) hm
  · rw [hv,lbl_sadj,sadj_apply_right (show p+1 < m by omega),lbl_smul,← wordProd_reverse]
    rw [wordProd_apply_of_forall_ne]
    · exact hb
    · intro j hj
      have := List.mem_range'.1 (List.mem_reverse.1 hj)
      dsimp
      constructor <;> omega
  · intro z hz
    rw [hv,lbl_sadj,sadj_apply_of_ne _ (by dsimp; omega) (by dsimp; omega),
      lbl_smul,← wordProd_reverse,desc_lowers m (p+1) d (by omega) z hz]
    exact hc z hz

end Categorification.Stendhal.BraidedStendhalAlgebra
