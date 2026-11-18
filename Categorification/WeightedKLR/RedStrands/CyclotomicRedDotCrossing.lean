/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedCrossing
import Categorification.WeightedKLR.RedStrands.CyclotomicRedDotVacuum
import Categorification.WeightedKLR.RedStrands.CyclotomicRedDotBalanced

/-!
# The reverse dot-power crossing in the cyclotomic action

Webster, arXiv:1309.3796v2, Theorem 4.25, p. 41. The reverse crossing
multiplies a lift of the algebra factor of an induced tensor by the power of the
last dot prescribed by the red weight. The two composites with the cyclotomic
quotient give the bigons in (4.2).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra CyclotomicAction CategoryTheory Polynomial InductionAlong MulOpposite

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]}
  (hab : ∀ i, a i ∣ b i) (i : I) {β γ : Multiset I} (h : {i} + β = γ) (d : ℕ)

local notation "π" => cyclotomicRedProjection Q hab
local notation "ρ" => cyclotomicRedPullback Q hab
local notation "p" => cyclotomicRedCornerProjection Q hab i h
local notation "φa" => lastEmb Q a i h
local notation "φb" => lastEmb Q b i h

private theorem intertwinesDotPow (c : I → k[X]) :
    Intertwines (lastEmb Q c i h) (lastEmb Q c i h) (dotElt Q c i h ^ d) :=
  fun r => (Commute.pow_right (intertwines_dotElt Q c i h r) d).eq

private theorem dotPow_eq (c : I → k[X]) :
    (End.of (dot.{u,v,w} Q c i h)) ^ d = natTrans (intertwinesDotPow Q i h d c) := by
  induction d with
  | zero =>
    change 𝟙 _ = natTrans _
    rw [← natTrans_unit (lastEmb Q c i h)]
    exact natTrans_eq_of_unit_mul _ _ (by simp [unit_mul_unit])
  | succ d ih =>
    rw [pow_succ']
    change _ ≫ dot Q c i h = _
    rw [ih, dot, natTrans_comp]
    exact natTrans_congr _ (pow_succ _ _).symm

private theorem dotPow_tmul (c : I → k[X]) (M : ModuleCat.{max u v w} (CycKLR k Q c β))
    (z : Corner (lastEmb Q c i h)) (n : M) :
    (((End.of (dot Q c i h)) ^ d).app M) (Ind.tmul z n) =
      Ind.tmul (cornerMul (intertwinesDotPow Q i h d c) z) n := by
  rw [dotPow_eq, natTrans_app_tmul]

/-- The kernel criterion needed for the last-dot power to descend to induction
after a red weight change. -/
private def DotKernel : Prop :=
  ∀ (M : ModuleCat.{max u v w} (CycKLR k Q a β)) (x : CycKLR k Q b γ), π γ x = 0 →
    ∀ n : M, Ind.tmul (N := (ρ β).obj M) ((x * dotElt Q b i h ^ d) • unitGen (φb)) n = 0

variable (H : DotKernel.{u,v,w} Q hab i h d)

private def liftedTensor (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (z : Corner (φa)) (n : M) : (ind Q b i h).obj ((ρ β).obj M) :=
  (((End.of (dot Q b i h)) ^ d).app ((ρ β).obj M))
    (Ind.tmul (N := (ρ β).obj M) ((cyclotomicRedCornerProjection_surjective Q hab i h z).choose) n)

include H in
set_option backward.isDefEq.respectTransparency false in
private theorem liftedTensor_proj (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (z : Corner (φb)) (n : M) :
    liftedTensor Q hab i h d M (p z) n =
      (((End.of (dot Q b i h)) ^ d).app ((ρ β).obj M))
        (Ind.tmul (N := (ρ β).obj M) z n) := by
  let y := (cyclotomicRedCornerProjection_surjective Q hab i h (p z)).choose
  have hy : p y = p z := (cyclotomicRedCornerProjection_surjective Q hab i h (p z)).choose_spec
  have hz : π γ (y.val - z.val) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hy
  have hk := H M (y.val - z.val) hz n
  unfold liftedTensor
  change ((End.of (dot Q b i h) ^ d).app ((ρ β).obj M)) (Ind.tmul (N := (ρ β).obj M) y n) = _
  rw [dotPow_tmul, dotPow_tmul, ← sub_eq_zero]
  have he : ((y.val - z.val) * dotElt Q b i h ^ d) • unitGen (φb) =
      cornerMul (intertwinesDotPow Q i h d b) y - cornerMul (intertwinesDotPow Q i h d b) z := by
    apply Subtype.ext
    change ((y.val - z.val) * dotElt Q b i h ^ d) * φb 1 = _
    rw [sub_mul, sub_mul]
    exact congrArg₂ (· - ·) (cornerMul (intertwinesDotPow Q i h d b) y).prop
      (cornerMul (intertwinesDotPow Q i h d b) z).prop
  rw [he, sub_eq_add_neg, Ind.add_tmul, Ind.neg_tmul] at hk
  simpa only [sub_eq_add_neg] using hk

private theorem proj_add (z t : Corner (φb)) : p (z + t) = p z + p t :=
  Subtype.ext (map_add (π γ) z.val t.val)

private theorem proj_op (r : CycKLR k Q b β) (z : Corner (φb)) :
    p (op r • z) = op (π β r) • p z := Subtype.ext (by
  change π γ (z.val * φb r) = π γ z.val * φa (π β r)
  rw [map_mul, cyclotomicRedProjection_lastEmb])

private theorem proj_smul (r : CycKLR k Q b γ) (z : Corner (φb)) :
    p (r • z) = π γ r • p z := Subtype.ext (map_mul (π γ) r z.val)

set_option backward.isDefEq.respectTransparency false in
private def dotLiftAdd (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    Ind M (φa) →+ (ind Q b i h).obj ((ρ β).obj M) :=
  Ind.liftAdd (liftedTensor Q hab i h d M)
    (fun z t n => by
      obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
      obtain ⟨w, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h t
      rw [← proj_add, liftedTensor_proj Q hab i h d H, liftedTensor_proj Q hab i h d H,
        liftedTensor_proj Q hab i h d H, Ind.add_tmul (N := (ρ β).obj M), map_add])
    (fun z m n => by
      obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
      simp only [liftedTensor_proj Q hab i h d H]
      exact (congrArg _ (Ind.tmul_add (N := (ρ β).obj M) y m n)).trans (map_add _ _ _))
    (fun z r n => by
      obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
      obtain ⟨s, rfl⟩ := cyclotomicRedProjection_surjective Q hab β r
      rw [← proj_op, liftedTensor_proj Q hab i h d H, liftedTensor_proj Q hab i h d H,
        Ind.op_smul_tmul (N := (ρ β).obj M)]
      rfl)

include H in
set_option backward.isDefEq.respectTransparency false in
private theorem dotLiftAdd_smul (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (r : CycKLR k Q b γ) (t : Ind M φa) :
    dotLiftAdd Q hab i h d H M (π γ r • t) = r • dotLiftAdd Q hab i h d H M t := by
  induction t using Ind.induction_on (φ := φa) (N := M) with
  | zero => simp only [smul_zero, map_zero]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]
  | tmul z n =>
    obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
    rw [Ind.smul_tmul, ← proj_smul]
    change liftedTensor Q hab i h d M (p (r • y)) n = r • liftedTensor Q hab i h d M (p y) n
    rw [liftedTensor_proj Q hab i h d H, liftedTensor_proj Q hab i h d H, ← Ind.smul_tmul,
      map_smul]

private def dotCrossApp (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    (ind Q a i h ⋙ ρ γ).obj M ⟶ (ρ β ⋙ ind Q b i h).obj M :=
  ModuleCat.ofHom (X := (ind Q a i h ⋙ ρ γ).obj M) (Y := (ρ β ⋙ ind Q b i h).obj M) {
    toFun t := dotLiftAdd Q hab i h d H M t
    map_add' := map_add _
    map_smul' := dotLiftAdd_smul Q hab i h d H M }

include H in
private theorem dotCrossApp_tmul (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (z : Corner φb) (n : M) :
    dotCrossApp Q hab i h d H M (Ind.tmul (N := M) (p z) n) =
      ((End.of (dot Q b i h) ^ d).app ((ρ β).obj M))
        (Ind.tmul (N := (ρ β).obj M) z n) :=
  liftedTensor_proj Q hab i h d H M z n

include H in
set_option backward.isDefEq.respectTransparency false in
private theorem highBigonApp (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    (cyclotomicRedDownQuotient Q hab i h).app M ≫ dotCrossApp Q hab i h d H M =
      (End.of (dot Q b i h) ^ d).app ((ρ β).obj M) := by
  apply ModuleCat.hom_ext
  apply Ind.ext
  intro z n
  exact (congrArg (dotCrossApp Q hab i h d H M)
    (cyclotomicRedDownQuotient_tmul Q hab i h M z n)).trans (dotCrossApp_tmul Q hab i h d H M z n)

include H in
private def dotCrossNat : ind Q a i h ⋙ ρ γ ⟶ ρ β ⋙ ind Q b i h where
  app := dotCrossApp Q hab i h d H
  naturality {M N} f := by
    let q := cyclotomicRedDownQuotient Q hab i h
    have : Epi (q.app M) := (ModuleCat.epi_iff_surjective _).2
      (cyclotomicRedDownQuotient_surjective Q hab i h M)
    apply (cancel_epi (q.app M)).mp
    rw [← Category.assoc, ← q.naturality, Category.assoc, highBigonApp,
      ← Category.assoc, highBigonApp]
    exact (End.of (dot Q b i h) ^ d).naturality ((ρ β).map f)

include H in
set_option backward.isDefEq.respectTransparency false in
private theorem lowBigonApp (M : ModuleCat.{max u v w} (CycKLR k Q a β)) :
    dotCrossApp Q hab i h d H M ≫ (cyclotomicRedDownQuotient Q hab i h).app M =
      (ρ γ).map ((End.of (dot Q a i h) ^ d).app M) := by
  apply ModuleCat.hom_ext
  ext t
  induction t using Ind.induction_on (φ := φa) (N := M) with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul z n =>
    obtain ⟨y, rfl⟩ := cyclotomicRedCornerProjection_surjective Q hab i h z
    change (cyclotomicRedDownQuotient Q hab i h).app M
      (dotCrossApp Q hab i h d H M (Ind.tmul (N := M) (p y) n)) =
      ((End.of (dot Q a i h) ^ d).app M) (Ind.tmul (N := M) (p y) n)
    rw [dotCrossApp_tmul, dotPow_tmul, cyclotomicRedDownQuotient_tmul, dotPow_tmul]
    apply congrArg (Ind.tmul (N := M) · n)
    apply Subtype.ext
    change π γ (y.val * dotElt Q b i h ^ d) = π γ y.val * dotElt Q a i h ^ d
    exact (map_mul _ _ _).trans (congrArg (π γ y.val * ·) ((map_pow _ _ _).trans
      (congrArg (· ^ d) (cyclotomicRedProjection_mk Q hab _))))

variable (hi : b i = X ^ d * a i)

include hi in
private theorem dotKernel_of_parameters : DotKernel.{u,v,w} Q hab i h d := by
  subst γ
  by_cases hβ : β = 0
  · subst β
    intro M x hx n
    rw [cyclotomicRedDotKernel_zero Q hab i d hi x hx, zero_smul]
    exact Ind.zero_tmul (N := (ρ 0).obj M) n
  · exact cyclotomicRedDotKernel_pos Q hab i (β := β) (Multiset.card_pos.mpr hβ) d hi

/-- The reverse crossing lifts the algebra factor of an induced tensor and
multiplies it by the added dot power. -/
def cyclotomicRedDotCrossing (hi : b i = X ^ d * a i) :
    ind.{u,v,w} Q a i h ⋙ ρ γ ⟶ ρ β ⋙ ind Q b i h :=
  dotCrossNat Q hab i h d (dotKernel_of_parameters Q hab i h d hi)

set_option backward.isDefEq.respectTransparency false in
/-- For any lift of the corner factor, the reverse crossing multiplies that lift
on the right by the last dot power and preserves the module vector. -/
theorem cyclotomicRedDotCrossing_tmul (M : ModuleCat.{max u v w} (CycKLR k Q a β))
    (z : Corner φb) (n : M) :
    (cyclotomicRedDotCrossing Q hab i h d hi).app M (Ind.tmul (N := M) (p z) n) =
      Ind.tmul (N := (ρ β).obj M) ((z.val * dotElt Q b i h ^ d) • unitGen φb) n := by
  change dotCrossApp Q hab i h d _ M _ = _
  rw [dotCrossApp_tmul, dotPow_tmul Q i h d b ((ρ β).obj M) z n]
  apply congrArg (Ind.tmul (N := (ρ β).obj M) · n)
  exact Subtype.ext (cornerMul (intertwinesDotPow Q i h d b) z).prop.symm

/-- The quotient followed by the reverse crossing gives the last dot power on
the higher-weight induction, Webster (4.2). -/
theorem cyclotomicRedDownQuotient_dotCrossing :
    cyclotomicRedDownQuotient.{u,v,w} Q hab i h ≫ cyclotomicRedDotCrossing Q hab i h d hi =
      Functor.whiskerLeft (ρ β) (End.of (dot Q b i h) ^ d) := by
  apply NatTrans.ext
  funext M
  exact highBigonApp Q hab i h d (dotKernel_of_parameters Q hab i h d hi) M

/-- The reverse crossing followed by the quotient gives the last dot power on
the lower-weight induction, Webster (4.2). -/
theorem cyclotomicRedDotCrossing_downQuotient :
    cyclotomicRedDotCrossing.{u,v,w} Q hab i h d hi ≫ cyclotomicRedDownQuotient Q hab i h =
      Functor.whiskerRight (End.of (dot Q a i h) ^ d) (ρ γ) := by
  apply NatTrans.ext
  funext M
  exact lowBigonApp Q hab i h d (dotKernel_of_parameters Q hab i h d hi) M

end Categorification.Stendhal
