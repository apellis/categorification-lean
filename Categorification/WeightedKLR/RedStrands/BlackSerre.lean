/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackProjectionK0
import Categorification.KLR.ReindexWordK0

/-!
# The quantum Serre relations for Stendhal black induction

Webster, arXiv:1309.3796v2, §4.6 after Theorem 4.31, and Theorem 4.38:
the black lowering generators act on the full sum of projective weight groups
and satisfy the integral quantum Serre relations.
-/
noncomputable section
namespace Categorification.Stendhal
open scoped DirectSum
open KLR KLRAlgebra Categorification.Graded QuantumGroup Finset LaurentPolynomial KL2
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)
local notation "di" => fun i => C.dot i i / 2
local notation "H" => affineCoverGrading Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "D" => hQ.gradingDatum
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "LP" => LaurentPolynomial ℤ
local notation "fam" => fun β : Multiset I => K0 (tensorProductGrade G β)
local notation "lift" => totalProjectionK0 Λ C hQ

private theorem word_power {J : Type*} [DecidableEq J] {S : J → J → MvPolynomial (Fin 2) k}
    (B : GradingDatum S) (i : J) (n : ℕ) : B.clsW [i] ^ n = B.clsW (List.replicate n i) := by
  induction n with
  | zero => simpa only [List.replicate_zero, pow_zero] using B.clsW_nil.symm
  | succ n ih => rw [pow_succ', ih, ← B.clsW_append, List.replicate_succ]; rfl

private theorem cover_serre {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range (C.serreN i j + 1), ((-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) (C.serreN i j) a) •
      ((H).clsW [Sum.inl i] ^ a * (H).clsW [Sum.inl j] * (H).clsW [Sum.inl i] ^ (C.serreN i j - a)) = 0 := by
  let F : (D).K0R →ₗ[LP] (H).K0R := GradingDatum.reindexWordK0 (f := Sum.inl (β := Fin ℓ)) Sum.inl_injective D H
    (fun _ => rfl) (fun _ _ => rfl)
  have key (w : List I) : F ((D).clsW w) = (H).clsW (w.map Sum.inl) :=
    GradingDatum.reindexWordK0_clsW _ _ _ _ _ w
  have h := (congrArg (fun x => F x) (CycKLR.affine_clsW_serre hQ hij)).trans F.map_zero
  rw [map_sum F] at h
  simp only [map_smul, word_power, ← GradingDatum.clsW_append, key, List.map_append,
    List.map_replicate, List.map_cons, List.map_nil] at h
  simpa only [word_power, ← GradingDatum.clsW_append] using h

private def InRedWeight (x : (H).K0R) : Prop :=
  ∃ (ν : Multiset I) (y : K0 ((H).grade (stendhalWeight ℓ ν))),
    x = DirectSum.lof LP _ (H).K0fam (stendhalWeight ℓ ν) y

private theorem inRedWeight_of_cast {δ : Multiset (I ⊕ Fin ℓ)} (ν : Multiset I)
    (h : δ = stendhalWeight ℓ ν) (x : K0 ((H).grade δ)) :
    InRedWeight Λ C hQ (DirectSum.of (H).K0fam δ x) := by
  subst δ
  exact ⟨ν, x, rfl⟩

private theorem inRedWeight_mul (i : I) {x : (H).K0R} (hx : InRedWeight Λ C hQ x) :
    InRedWeight Λ C hQ (x * (H).clsW [Sum.inl i]) := by
  obtain ⟨ν, y, rfl⟩ := hx
  let μ := stendhalWeight ℓ ν
  let σ : Multiset (I ⊕ Fin ℓ) := ([Sum.inl i] : List (I ⊕ Fin ℓ))
  change InRedWeight Λ C hQ (DirectSum.of (H).K0fam μ y * (H).clsW [Sum.inl i])
  rw [GradingDatum.clsW, (H).K0R_of_mul_of]
  exact inRedWeight_of_cast Λ C hQ (({i} : Multiset I) + ν)
    ((add_comm μ σ).trans (stendhalWeight_black_cons (ℓ := ℓ) i ν)) _

private theorem inRedWeight_pow (i : I) {x : (H).K0R} (hx : InRedWeight Λ C hQ x) (n : ℕ) :
    InRedWeight Λ C hQ (x * (H).clsW [Sum.inl i] ^ n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ, ← mul_assoc]; exact inRedWeight_mul Λ C hQ i ih

private theorem lower_projection (i : I) {x : (H).K0R} (hx : InRedWeight Λ C hQ x) :
    blackLower G i (lift x) = lift (x * (H).clsW [Sum.inl i]) := by
  obtain ⟨ν, y, rfl⟩ := hx
  exact blackLower_totalProjectionK0_lof Λ C hQ i ν y

private theorem lower_pow_projection (i : I) {x : (H).K0R} (hx : InRedWeight Λ C hQ x) (n : ℕ) :
    (blackLower G i ^ n) (lift x) = lift (x * (H).clsW [Sum.inl i] ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, lower_projection _ _ _ _ (inRedWeight_pow Λ C hQ i hx n),
      pow_succ, mul_assoc]

/-- On the projection of an expanded homogeneous word, iterated intrinsic lowering
appends the specified number of black strands (Webster, arXiv:1309.3796v2, §4.6). -/
theorem blackLower_pow_totalProjectionK0_word (i : I) (n : ℕ) (ν : Multiset I)
    (w : List (I ⊕ Fin ℓ)) (hw : (w : Multiset _) = stendhalWeight ℓ ν) :
    (blackLower G i ^ n) (lift ((H).clsW w)) =
      lift ((H).clsW (w ++ List.replicate n (.inl i))) := by
  have hx : InRedWeight Λ C hQ ((H).clsW w) := by
    rw [(H).clsW_eq w hw]
    exact ⟨ν, _, rfl⟩
  rw [lower_pow_projection _ _ _ _ hx n, word_power, GradingDatum.clsW_append]

/-- Class of the affine nilHecke divided projective on a single block of black strands. -/
def affineDividedBlack (i : I) (n : ℕ) : (H).K0R :=
  let w : List ((I ⊕ Fin ℓ) × ℕ) := [(Sum.inl i, n)]
  let hs := affineCoverGrading_cross_symm Λ hQ.gradingDatum di (dotDegree C hQ)
    (fun i j => congrArg Neg.neg (C.symm i j))
  DirectSum.of (H).K0fam (expandDiv w : Multiset _) (K0.of ((H).dividedProjective hs (affineCoverCartan C ℓ) w rfl))

private theorem affine_black_factorial (i : I) (n : ℕ) :
    (H).clsW [Sum.inl i] ^ n = qfact (tUnit (C.dot i i / 2)) n • affineDividedBlack Λ C hQ i n := by
  let w : List ((I ⊕ Fin ℓ) × ℕ) := [(Sum.inl i, n)]
  let hs := affineCoverGrading_cross_symm Λ hQ.gradingDatum di (dotDegree C hQ)
    (fun i j => congrArg Neg.neg (C.symm i j))
  have hX := affineCoverGrading_dot Λ hQ.gradingDatum di (dotDegree C hQ) C (fun _ => rfl)
  have he : expandDiv w = List.replicate n (Sum.inl i) := by simp [w, expandDiv]
  rw [word_power, ← he, GradingDatum.clsW]
  change DirectSum.of (H).K0fam _ (K0.of _) = _
  rw [show K0.of ((H).projP (Seq.ofList (expandDiv w) rfl)) = _ from
    (H).of_expanded_eq_factorial hs (affineCoverCartan C ℓ) hX w rfl, DirectSum.of_smul]
  congr 1
  change qfact (tUnit (C.dot i i / 2)) n * 1 = _
  rw [mul_one]

/-- Iterating black induction on an affine lift gives the quantum factorial times the
projection of its product with the shifted black nilHecke projective (Webster, §4.6). -/
theorem blackLower_pow_projection_factorial (i : I) (n : ℕ) (ν : Multiset I)
    (x : K0 ((H).grade (stendhalWeight ℓ ν))) :
    (blackLower G i ^ n) (DirectSum.lof LP _ fam ν (projectionK0 Λ C hQ ν x)) =
      qfact (tUnit (C.dot i i / 2)) n •
        lift (DirectSum.of (H).K0fam (stendhalWeight ℓ ν) x * affineDividedBlack Λ C hQ i n) := by
  rw [← totalProjectionK0_lof, lower_pow_projection _ _ _ _ ⟨ν, x, rfl⟩,
    affine_black_factorial, mul_smul_comm, map_smul]
  rfl

/-- Every projective class obtained by iterating the same black lowering operator
is divisible by its integral quantum factorial (Webster, §4.6 and §4.7). -/
theorem exists_blackLower_pow_eq_qfact_smul (i : I) (n : ℕ) (z : ⨁ ν : Multiset I, fam ν) :
    ∃ y, (blackLower G i ^ n) z = qfact (tUnit (C.dot i i / 2)) n • y := by
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb, smul_add]⟩
  | of ν x =>
    obtain ⟨v, rfl⟩ := projectionK0_surjective Λ C hQ ν x
    exact ⟨_, blackLower_pow_projection_factorial Λ C hQ i n ν v⟩

/-- The integral graded projective group is torsion-free over the Laurent integers
for each finite red family (Webster, arXiv:1309.3796v2, proof of Theorem 4.38). -/
theorem totalK0_smul_injective {r : LP} (hn : r ≠ 0) :
    Function.Injective ((r • ·) : DirectSum (Multiset I) fam → _) := by
  intro x y h
  apply DFinsupp.ext
  intro ν
  let μ := stendhalWeight ℓ ν
  have hs := affineCoverQ_symm Λ (fun a b hab => (hQ.symm a b hab).symm)
  have hX := affineCoverGrading_dot Λ hQ.gradingDatum di (dotDegree C hQ) C (fun _ => rfl)
  let := (H).hasGdim_grade' (ν := μ) hs (fun a => (hX a).symm ▸ (affineCoverCartan C ℓ).dot_self_pos a)
  let := hasGdim_of_surjective ((H).grade μ) (tensorProductGrade G ν) (affineTensorProjection Λ ν)
    (projection_graded Λ C hQ ν) (affineTensorProjection_surjective (Q := Q) Λ ν)
  exact smul_right_injective (K0 (tensorProductGrade G ν)) hn (DFinsupp.ext_iff.mp h ν)

private theorem blackFactorial_injective (i : I) (n : ℕ) :
    Function.Injective ((qfact (tUnit (C.dot i i / 2)) n • ·) : DirectSum (Multiset I) fam → _) := by
  apply totalK0_smul_injective
  intro h
  exact C.qfact_ne_zero i n (by rw [PreF.vi, ← KL2Gamma.qToV_qfact_tUnit, h, map_zero])

private def divideEnd {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (r : R) (hr : Function.Injective ((r • ·) : M → M)) (f : Module.End R M)
    (hf : ∀ x, ∃ y, f x = r • y) : Module.End R M where
  toFun x := (hf x).choose
  map_add' x y := by
    apply hr
    change r • (hf (x+y)).choose = r • ((hf x).choose + (hf y).choose)
    rw [← (hf (x+y)).choose_spec, smul_add, ← (hf x).choose_spec, ← (hf y).choose_spec, map_add]
  map_smul' a x := by
    apply hr
    change r • (hf (a • x)).choose = r • (a • (hf x).choose)
    rw [← (hf (a • x)).choose_spec, smul_comm r, ← (hf x).choose_spec, map_smul]


/-- The integral divided lowering operator for the full ordered family of red strands
(Webster, arXiv:1309.3796v2, §4.6 and Theorem 4.38). Its value on a homogeneous
affine lift is the projection of the nilHecke divided projective. -/
def blackDividedLower (i : I) (n : ℕ) : Module.End LP (DirectSum (Multiset I) fam) :=
  divideEnd (qfact (tUnit (C.dot i i / 2)) n) (blackFactorial_injective Λ C hQ i n)
    (blackLower G i ^ n) (exists_blackLower_pow_eq_qfact_smul Λ C hQ i n)

/-- Iterated black induction equals the integral quantum factorial times divided
induction on all projective classes (Webster, arXiv:1309.3796v2, §4.6). -/
theorem blackLower_pow_eq_qfact_smul (i : I) (n : ℕ) :
    blackLower G i ^ n = qfact (tUnit (C.dot i i / 2)) n • blackDividedLower Λ C hQ i n := by
  apply LinearMap.ext
  intro x
  exact (exists_blackLower_pow_eq_qfact_smul Λ C hQ i n x).choose_spec

/-- On a lifted homogeneous class the divided lowering operator appends the shifted
affine nilHecke projective (Webster, arXiv:1309.3796v2, §4.6). -/
theorem blackDividedLower_projection (i : I) (n : ℕ) (ν : Multiset I)
    (x : K0 ((H).grade (stendhalWeight ℓ ν))) :
    blackDividedLower Λ C hQ i n (DirectSum.lof LP _ fam ν (projectionK0 Λ C hQ ν x)) =
      lift (DirectSum.of (H).K0fam (stendhalWeight ℓ ν) x * affineDividedBlack Λ C hQ i n) := by
  apply blackFactorial_injective Λ C hQ i n
  have h := blackLower_pow_projection_factorial Λ C hQ i n ν x
  rw [blackLower_pow_eq_qfact_smul, LinearMap.smul_apply] at h
  exact h

/-- Intrinsic right black-strand induction on the integral projective Grothendieck
group satisfies the quantum Serre relation in every red family (Webster, §4.6
and Theorem 4.38; Rouquier, arXiv:0812.5023v1, Proposition 4.2). -/
theorem blackLower_serre {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range (C.serreN i j + 1), ((-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) (C.serreN i j) a) •
      ((blackLower G i)^(C.serreN i j - a) * blackLower G j * (blackLower G i)^a) = 0 := by
  let N := C.serreN i j
  let c (a : ℕ) := (-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) N a
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of ν z =>
    obtain ⟨x, rfl⟩ := projectionK0_surjective Λ C hQ ν z
    let y := DirectSum.lof LP _ (H).K0fam (stendhalWeight ℓ ν) x
    have hy : InRedWeight Λ C hQ y := ⟨ν, x, rfl⟩
    change (∑ a ∈ range (N+1), c a • ((blackLower G i)^(N-a) * blackLower G j * (blackLower G i)^a))
      (DirectSum.lof LP _ fam ν (projectionK0 Λ C hQ ν x)) = 0
    rw [← totalProjectionK0_lof]
    change (∑ a ∈ range (N+1), c a • ((blackLower G i)^(N-a) * blackLower G j * (blackLower G i)^a)) (lift y) = 0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      lower_pow_projection _ _ _ i hy, lower_projection _ _ _ j (inRedWeight_pow Λ C hQ i hy _),
      lower_pow_projection _ _ _ i (inRedWeight_mul Λ C hQ j (inRedWeight_pow Λ C hQ i hy _))]
    simp_rw [mul_assoc y, ← map_smul, ← mul_smul_comm]
    rw [← map_sum, ← Finset.mul_sum]
    have h := cover_serre Λ C hQ hij
    change ∑ a ∈ range (N+1), c a • _ = 0 at h
    simpa only [mul_assoc, mul_smul_comm, mul_zero, map_zero] using congrArg (fun b => lift (y * b)) h


private theorem blackFactorial_end_injective (i : I) (n : ℕ) :
    Function.Injective ((qfact (tUnit (C.dot i i / 2)) n • ·) : Module.End LP (DirectSum (Multiset I) fam) → _) := by
  intro f g h
  exact LinearMap.ext fun x => blackFactorial_injective Λ C hQ i n (LinearMap.congr_fun h x)

/-- The intrinsic divided lowering maps satisfy Lusztig's divided quantum Serre relation
on all tensor product projective classes (Webster, arXiv:1309.3796v2, §4.6 and Theorem 4.38). -/
theorem blackDividedLower_serre {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range (C.serreN i j + 1), (-1 : LP)^a •
      (blackDividedLower Λ C hQ i (C.serreN i j - a) * blackLower G j * blackDividedLower Λ C hQ i a) = 0 := by
  let N := C.serreN i j
  let v := tUnit (C.dot i i / 2)
  apply blackFactorial_end_injective Λ C hQ i N
  change qfact v N • (∑ a ∈ range (N + 1), (-1 : LP)^a •
    (blackDividedLower Λ C hQ i (N - a) * blackLower G j * blackDividedLower Λ C hQ i a)) = qfact v N • 0
  rw [smul_zero, Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (blackLower_serre Λ C hQ hij)
  have h := qbinom_mul_qfact v (N-a) a
  rw [Nat.sub_add_cancel (show a ≤ N by simpa only [mem_range, Nat.lt_succ_iff] using ha)] at h
  rw [blackLower_pow_eq_qfact_smul, blackLower_pow_eq_qfact_smul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  rw [← h]
  ring

/-- Consecutive divided powers multiply by the integral quantum binomial coefficient
(Webster, arXiv:1309.3796v2, §4.6, and Lusztig, Introduction to Quantum Groups, §1.3.1). -/
theorem blackDividedLower_mul (i : I) (a b : ℕ) :
    blackDividedLower Λ C hQ i a * blackDividedLower Λ C hQ i b =
      qbinom (tUnit (C.dot i i / 2)) (a+b) b • blackDividedLower Λ C hQ i (a+b) := by
  let v := tUnit (C.dot i i / 2)
  apply blackFactorial_end_injective Λ C hQ i a
  apply blackFactorial_end_injective Λ C hQ i b
  change qfact v b • (qfact v a • (blackDividedLower Λ C hQ i a * blackDividedLower Λ C hQ i b)) =
    qfact v b • (qfact v a • (qbinom v (a+b) b • blackDividedLower Λ C hQ i (a+b)))
  rw [← smul_mul_assoc, ← mul_smul_comm, ← blackLower_pow_eq_qfact_smul,
    ← blackLower_pow_eq_qfact_smul, ← pow_add, blackLower_pow_eq_qfact_smul]
  simp only [smul_smul]
  apply congrArg (fun r : LP => r • blackDividedLower Λ C hQ i (a+b))
  change qfact v (a+b) = _
  rw [← qbinom_mul_qfact v a b]
  ring

end Categorification.Stendhal
