/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidAction

/-!
# The generators of `T̃^λ` acting on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. In the model `L ⊗ e T̃^{λ⁺}` of
`K̃^{λ⁺}_λ` with the maximum just before the red strand `λ_{j+1}` (`CupCap.MidModel`), the
generators of `T̃^λ` act through diagrams of `λ⁺` placed above the elements of the model. On a
loading `s` of `λ`, with the maximum at `c = midPos s`:

* the idempotent `e(s)` is the window idempotent `E_s` of `λ⁺`;
* a dot is the same dot of `λ⁺`, moved past the window if its strand is right of `λ_{j+1}`;
* a crossing away from `λ_{j+1}` is the same crossing of `λ⁺`;
* the crossing of a black strand at `c - 1` with `λ_{j+1}` is the crossing of the black strand
  with `λ_{j+1}` in `λ⁺`, after the black strand passed under the maximum (`underLeft`);
* the crossing of `λ_{j+1}` with a black strand of colour `i` at `c + 1` is the crossing in
  `λ⁺`, followed by the passage of the black strand under the maximum (`underRight`), divided by
  the scalar `κ_i` of (max1) (`Ring.inverse`, a route choice: the scalars are units in Webster's
  setting);
* crossings of `λ_{j+1}` with red strands, and crossings out of range, act by zero.

Each of these diagrams slides through the diagrams at the maximum, up to diagrams in which a strand
leaves the window (`CupCap.MidSlides`), so it acts on the model (`CupCap.midEnd`). With the
`k`-module structure of the model through the scalars of `T̃^{λ⁺}`, the sliding diagrams form a
subalgebra of `λ⁺` acting through an algebra map (`CupCap.midEndAlg`).

## Main definitions

* `CupCap.midSlidesSub`: the subalgebra of sliding diagrams.
* `CupCap.midEndAlg`: its action on the model.
* `CupCap.midIdem`, `CupCap.midDot`, `CupCap.midCrossAt`, `CupCap.midCross`: the diagrams of the
  generators.
* `CupCap.midGenImage`: the generators of the KLR algebra of `λ` in the subalgebra.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Generators

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

theorem eSum_mul_midMapKLR (s : Seq (stendhalWeight ℓ ν)) (w : Rc) :
    E s * μ w = ι s (midPos j s) (midPos_le j s) w := by
  rw [← insertMap_one Q Λ Λc s (midPos_le j s), insertMap_mul_midMapKLR, one_mul]

theorem midMapKLR_mul_eSum (s : Seq (stendhalWeight ℓ ν)) (w : Rc) :
    μ w * E s = ι s (midPos j s) (midPos_le j s) w :=
  (insertMap_eq_midMapKLR_mul s w).symm

omit [DecidableEq I] in
theorem dotPos_val' (n : Fin (m + 1)) (a : Fin m) :
    (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a).val =
      if a.val < n then a.val else a.val + N := by
  rw [dotPos, Fin.val_cast, insertPos_inl_val, Multiset.card_map]

omit [DecidableEq I] in
theorem crossPos_self (p : ℕ) : crossPos p N p = p + N := by
  simp [crossPos]

/-- A crossing away from the window carries the exit diagrams along. -/
theorem ψ_crossPos_mul_mem_exitSpan (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < n ∨ n ≤ p) {y : Rp} (hy : y ∈ exitSpan Q Λ Λc j hj s n hn) :
    KLRAlgebra.ψ (crossPos n N p) * y ∈ exitSpan Q Λ Λc j hj (sadj m p • s) n hn := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    rw [← mul_assoc, ψ_crossPos_mul_insertMap s hn hp, mul_assoc]
    exact mem_exitSpan _ hn hz _
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

variable (j hj Q Λ Λc ν ν₀)

/-- The idempotent `e(t)` of `λ`, as the window idempotent of `λ⁺`. -/
def midIdem (t : Seq (stendhalWeight ℓ ν)) : Rp := E t

/-- The dot on the strand `a` of `λ`, as a dot of `λ⁺`. -/
def midDot (a : Fin m) : Rp :=
  ∑ s : Seq (stendhalWeight ℓ ν),
    KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
      ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a) * E s

/-- The crossing `ψ_p` of `λ` on the loading `s` of `λ`, as a diagram of `λ⁺`. -/
def midCrossAt (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) : Rp :=
  if hp : p + 1 < m then
    if p + 1 = midPos j s then
      match s.lbl ⟨p, by omega⟩ with
      | .inl _ => KLRAlgebra.ψ (p + N) * underLeft N p * E s
      | .inr _ => 0
    else if p = midPos j s then
      match s.lbl ⟨p + 1, hp⟩ with
      | .inl i => Ring.inverse (cupScalar Q ν₀ i) •
          (underRight N p * KLRAlgebra.ψ (p + N) * E s)
      | .inr _ => 0
    else KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s
  else 0

/-- The crossing `ψ_p` of `λ`, as a diagram of `λ⁺`. -/
def midCross (p : ℕ) : Rp :=
  ∑ s : Seq (stendhalWeight ℓ ν), midCrossAt j hj Q Λ Λc ν ν₀ s p

variable {j hj Q Λ Λc ν ν₀}

theorem midSlides_midIdem (t : Seq (stendhalWeight ℓ ν)) :
    MidSlides j hj Q Λ Λc ν ν₀ (midIdem j hj Q Λ Λc ν ν₀ t) := fun w => by
  rw [midIdem, eSum_mul_midMapKLR, midMapKLR_mul_eSum, sub_self]
  exact zero_mem _

theorem midSlides_dot_eSum (s : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    MidSlides j hj Q Λ Λc ν ν₀ (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
      ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a) * E s) := fun w => by
  set d := dotPos (j := j) (hj := hj) (ν₀ := ν₀)
    ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a
  have hd : d.val < midPos j s ∨ midPos j s + N ≤ d.val := by
    have := dotPos_val' (j := j) (hj := hj) (ν₀ := ν₀)
      ⟨midPos j s, Nat.lt_succ_of_le (midPos_le j s)⟩ a
    simp only at this
    split_ifs at this <;> omega
  rw [mul_assoc, eSum_mul_midMapKLR, (commute_x_eSum d _).eq, ← mul_assoc,
    midMapKLR_mul_eSum, (commute_x_insertMap s (midPos_le j s) d hd w).eq, sub_self]
  exact zero_mem _

theorem midSlides_midDot (a : Fin m) :
    MidSlides j hj Q Λ Λc ν ν₀ (midDot j hj Q Λ Λc ν ν₀ a) :=
  MidSlides.sum _ fun s _ => midSlides_dot_eSum s a

/-- A crossing away from `λ_{j+1}` commutes with the diagrams at the maximum. -/
theorem midSlides_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    MidSlides j hj Q Λ Λc ν ν₀ (KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s) := fun w => by
  have hp' : p + 1 < midPos j s ∨ midPos j s ≤ p := by omega
  have hm := midPos_sadj_of_far j s hp hf
  rw [mul_assoc, eSum_mul_midMapKLR, ψ_crossPos_mul_insertMap s _ hp',
    ψ_crossPos_mul_eSum s _ hp', ← mul_assoc,
    insertSet_congr' (sadj m p • s) (midPos_le j s) (midPos_le j (sadj m p • s)) hm.symm,
    midMapKLR_mul_eSum,
    insertMap_congr' (sadj m p • s) (midPos_le j s) (midPos_le j (sadj m p • s)) hm.symm,
    sub_self]
  exact zero_mem _

/-- The crossing of a black strand at `c - 1` with `λ_{j+1}` slides through the diagrams at the
maximum. -/
theorem midSlides_left (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) :
    MidSlides j hj Q Λ Λc ν ν₀ (KLRAlgebra.ψ (p + N) * underLeft N p * E s) := fun w => by
  have hq : p + 1 ≤ m := hp.le
  have hm := midPos_sadj_left j s hp hc
  have hD := slidesLeft (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hq w
  unfold SlidesLeft at hD
  have hE : (E s : Rp) = Eat s (p + 1) hq :=
    congrArg _ (insertSet_congr' s (midPos_le j s) hq hc.symm)
  have hι : ι s (midPos j s) (midPos_le j s) w = ι s (p + 1) hq w :=
    insertMap_congr' s (midPos_le j s) hq hc.symm w
  have hψ : (KLRAlgebra.ψ (p + N) : Rp) = KLRAlgebra.ψ (crossPos p N p) := by
    rw [crossPos_self]
  have h1 : KLRAlgebra.ψ (p + N) * underLeft N p * E s * μ w =
      KLRAlgebra.ψ (p + N) * (underLeft N p * ι s (p + 1) hq w) := by
    rw [mul_assoc, eSum_mul_midMapKLR, hι, mul_assoc]
  have h2 : μ w * (KLRAlgebra.ψ (p + N) * underLeft N p * E s) =
      KLRAlgebra.ψ (p + N) * (ι s p (Nat.le_of_succ_le hq) w * underLeft N p) := by
    rw [hE, hψ]
    simp only [mul_assoc]
    rw [underLeft_mul_eSum, ← mul_assoc (KLRAlgebra.ψ _),
      ψ_crossPos_mul_eSum s _ (Or.inr le_rfl)]
    simp only [← mul_assoc]
    rw [insertSet_congr' (sadj m p • s) _ (midPos_le j (sadj m p • s)) hm.symm,
      midMapKLR_mul_eSum,
      insertMap_congr' (sadj m p • s) (midPos_le j (sadj m p • s)) (Nat.le_of_succ_le hq) hm,
      ← ψ_crossPos_mul_insertMap s _ (Or.inr le_rfl), mul_assoc]
  rw [h1, h2, ← mul_sub, ← neg_sub, mul_neg]
  refine neg_mem (mem_midExit (sadj m p • s) ?_)
  rw [exitSpan_congr' (sadj m p • s) (midPos_le j (sadj m p • s)) (Nat.le_of_succ_le hq) hm, hψ]
  exact ψ_crossPos_mul_mem_exitSpan s _ (Or.inr le_rfl) hD

/-- The crossing of `λ_{j+1}` at `c` with a black strand at `c + 1` slides through the diagrams
at the maximum. -/
theorem midSlides_right (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) :
    MidSlides j hj Q Λ Λc ν ν₀ (underRight N p * KLRAlgebra.ψ (p + N) * E s) := fun w => by
  have hq : p + 1 ≤ m := hp.le
  have hp0 : p ≤ m := by omega
  have hm := midPos_sadj_right j s hp hc
  have hD := slides (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (sadj m p • s) hq w
  unfold Slides at hD
  have hE : (E s : Rp) = Eat s p hp0 :=
    congrArg _ (insertSet_congr' s (midPos_le j s) hp0 hc.symm)
  have hι : ι s (midPos j s) (midPos_le j s) w = ι s p hp0 w :=
    insertMap_congr' s (midPos_le j s) hp0 hc.symm w
  have hψ : (KLRAlgebra.ψ (p + N) : Rp) = KLRAlgebra.ψ (crossPos p N p) := by
    rw [crossPos_self]
  have h1 : underRight N p * KLRAlgebra.ψ (p + N) * E s * μ w =
      underRight N p * ι (sadj m p • s) p hp0 w * KLRAlgebra.ψ (p + N) := by
    rw [mul_assoc, eSum_mul_midMapKLR, hι, mul_assoc, hψ,
      ψ_crossPos_mul_insertMap s _ (Or.inr le_rfl), mul_assoc]
  have h2 : μ w * (underRight N p * KLRAlgebra.ψ (p + N) * E s) =
      ι (sadj m p • s) (p + 1) hq w * underRight N p * KLRAlgebra.ψ (p + N) := by
    rw [hE, hψ]
    simp only [mul_assoc]
    rw [ψ_crossPos_mul_eSum s _ (Or.inr le_rfl), ← mul_assoc (underRight N p),
      underRight_mul_eSum Q Λ Λc _ hq]
    simp only [← mul_assoc]
    rw [insertSet_congr' (sadj m p • s) hq (midPos_le j (sadj m p • s)) hm.symm,
      midMapKLR_mul_eSum,
      insertMap_congr' (sadj m p • s) (midPos_le j (sadj m p • s)) hq hm]
  rw [h1, h2, ← sub_mul, ← neg_sub, neg_mul]
  refine neg_mem (mem_midExit (sadj m p • s) ?_)
  rw [exitSpan_congr' (sadj m p • s) (midPos_le j (sadj m p • s)) hq hm]
  exact exitSpan_mul_right _ hq hD _

theorem midSlides_midCrossAt (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    MidSlides j hj Q Λ Λc ν ν₀ (midCrossAt j hj Q Λ Λc ν ν₀ s p) := by
  have h0 : MidSlides j hj Q Λ Λc ν ν₀ (0 : Rp) := by
    simpa using MidSlides.smul (0 : k) (MidSlides.one (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) (ν₀ := ν₀))
  unfold midCrossAt
  split_ifs with hp h1 h2
  · split
    · exact midSlides_left s hp h1
    · exact h0
  · split
    · exact (midSlides_right s hp h2).smul _
    · exact h0
  · exact midSlides_far s hp (by omega)
  · exact h0

theorem midSlides_midCross (p : ℕ) :
    MidSlides j hj Q Λ Λc ν ν₀ (midCross j hj Q Λ Λc ν ν₀ p) :=
  MidSlides.sum _ fun s _ => midSlides_midCrossAt s p

variable (j hj Q Λ Λc ν ν₀) in
/-- **The sliding diagrams of `λ⁺`**, a subalgebra. -/
def midSlidesSub : Subalgebra k Rp where
  carrier := {Y | MidSlides j hj Q Λ Λc ν ν₀ Y}
  mul_mem' := MidSlides.mul
  add_mem' := MidSlides.add
  algebraMap_mem' c := by
    change MidSlides j hj Q Λ Λc ν ν₀ (algebraMap k Rp c)
    rw [Algebra.algebraMap_eq_smul_one]
    exact MidSlides.smul c MidSlides.one

theorem mem_midSlidesSub {Y : Rp} :
    Y ∈ midSlidesSub j hj Q Λ Λc ν ν₀ ↔ MidSlides j hj Q Λ Λc ν ν₀ Y := Iff.rfl

variable (j hj Q Λ Λc ν ν₀) in
/-- **The generators of the KLR algebra of `λ`**, as sliding diagrams of `λ⁺`. -/
def midGenImage : Gen (stendhalWeight ℓ ν) → midSlidesSub j hj Q Λ Λc ν ν₀
  | .idem t => ⟨midIdem j hj Q Λ Λc ν ν₀ t, midSlides_midIdem t⟩
  | .dot a => ⟨midDot j hj Q Λ Λc ν ν₀ a, midSlides_midDot a⟩
  | .cross p => ⟨midCross j hj Q Λ Λc ν ν₀ p, midSlides_midCross p⟩

end Generators

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Algebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

instance : Module k (MidModel j hj Q Λ Λc ν ν₀ L) :=
  Module.compHom _ (algebraMap k Tpᵐᵒᵖ)

theorem midModel_algebraMap_smul (c : k) (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    c • y = algebraMap k Tpᵐᵒᵖ c • y := rfl

instance : IsScalarTower k Tpᵐᵒᵖ (MidModel j hj Q Λ Λc ν ν₀ L) where
  smul_assoc c b y := by
    change (c • b) • y = algebraMap k Tpᵐᵒᵖ c • b • y
    rw [← mul_smul, ← Algebra.smul_def]

instance : SMulCommClass Tpᵐᵒᵖ k (MidModel j hj Q Λ Λc ν ν₀ L) where
  smul_comm b c y := by
    rw [midModel_algebraMap_smul, midModel_algebraMap_smul, ← mul_smul, ← mul_smul,
      Algebra.commutes]

instance : SMulCommClass k Tpᵐᵒᵖ (MidModel j hj Q Λ Λc ν ν₀ L) := SMulCommClass.symm _ _ _

variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

theorem midEnd_smul (c : k) {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midEnd L hL (hY.smul c) y = c • midEnd L hL hY y := by
  induction y using Ind.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', smul_add]
  | tmul z v =>
    rw [midEnd, midEnd, natMapOn_tmul, natMapOn_tmul, midModel_algebraMap_smul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    change z.1 * midElt j hj Q Λ Λc ν ν₀ (c • Y) =
      algebraMap k Tpᵐᵒᵖ c * (z.1 * midElt j hj Q Λ Λc ν ν₀ Y)
    rw [midElt, midElt, map_smul, mul_smul_comm, smul_mul_assoc, op_smul, mul_smul_comm]
    exact Algebra.smul_def (A := Tpᵐᵒᵖ) c _

/-- **The action of the sliding diagrams on the model**, as an algebra map. -/
def midEndAlg : midSlidesSub j hj Q Λ Λc ν ν₀ →ₐ[k] Module.End k (MidModel j hj Q Λ Λc ν ν₀ L)
    where
  toFun Y := (midEnd L hL (mem_midSlidesSub.1 Y.2)).restrictScalars k
  map_one' := by
    change (midEnd L hL (MidSlides.one (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
      (ν := ν) (ν₀ := ν₀))).restrictScalars k = 1
    rw [midEnd_one]; rfl
  map_mul' Y Y' := by
    change (midEnd L hL ((mem_midSlidesSub.1 Y.2).mul
      (mem_midSlidesSub.1 Y'.2))).restrictScalars k = _
    rw [midEnd_mul hL (mem_midSlidesSub.1 Y.2) (mem_midSlidesSub.1 Y'.2)]; rfl
  map_zero' := by
    ext y
    change midEnd L hL (mem_midSlidesSub.1 (0 : midSlidesSub j hj Q Λ Λc ν ν₀).2) y = 0
    rw [midEnd_eq_of_eq hL _ (MidSlides.smul (0 : k) MidSlides.one) (zero_smul k (1 : Rp)).symm,
      midEnd_smul, zero_smul]
    exact MidSlides.one
  map_add' Y Y' := by
    change (midEnd L hL ((mem_midSlidesSub.1 Y.2).add
      (mem_midSlidesSub.1 Y'.2))).restrictScalars k = _
    rw [midEnd_add hL (mem_midSlidesSub.1 Y.2) (mem_midSlidesSub.1 Y'.2)]; rfl
  commutes' c := by
    ext y
    rw [Module.algebraMap_end_apply]
    change midEnd L hL (mem_midSlidesSub.1 (algebraMap k (midSlidesSub j hj Q Λ Λc ν ν₀) c).2)
      y = c • y
    rw [midEnd_eq_of_eq hL _ (MidSlides.smul c MidSlides.one) (Algebra.algebraMap_eq_smul_one c),
      midEnd_smul, midEnd_one, LinearMap.id_apply]
    exact MidSlides.one

theorem midEndAlg_apply (Y : midSlidesSub j hj Q Λ Λc ν ν₀) (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midEndAlg L hL Y y = midEnd L hL (mem_midSlidesSub.1 Y.2) y := rfl

/-- Sliding diagrams differing by diagrams in which a strand leaves the window act alike. -/
theorem midEndAlg_eq_of_sub_mem {Y Y' : midSlidesSub j hj Q Λ Λc ν ν₀}
    (h : (Y : Rp) - Y' ∈ midExit j hj Q Λ Λc ν ν₀) : midEndAlg L hL Y = midEndAlg L hL Y' := by
  ext y
  rw [midEndAlg_apply, midEndAlg_apply,
    midEnd_congr hL (mem_midSlidesSub.1 Y.2) (mem_midSlidesSub.1 Y'.2) h]

end Algebra

end Categorification.Stendhal.CupCap
