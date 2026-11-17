/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDividedProjectives
import Categorification.KLR.Rouquier.K0Relations
import Categorification.KLR.Prop32Mult

/-!
# Quantum Serre relations for cyclotomic induction on graded projective classes

Webster, arXiv:1309.3796v2, Definition 3.15 and Proposition 3.21, and Rouquier,
arXiv:0812.5023v1, §4.1.1, Proposition 4.2. The lowering functor adds a
black strand on the right by the cyclotomic induction bimodule.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open Categorification.Graded KLRAlgebra KLRAlgebra.AbsentColour MulOpposite QuantumGroup
open scoped TensorProduct

section Principal

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)

local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ j
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ ((Singleton.singleton i : Multiset I) + β)
local notation "Mc" => IndCorner Q i aΛ β
local notation "ι" => cyclotomicLast Q i aΛ β
local notation "srcGr" => grade G Λ β
local notation "dstGr" => grade G Λ ((Singleton.singleton i : Multiset I) + β)

private def indMul (e : Rl) : BalancedTensor k Su Rl Mc (leftIdeal e) →ₗ[Su] Su :=
  (lIdeal (lastIdem Q i aΛ β)).subtype.comp <|
    (BalancedTensor.rid k Su Rl Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem indMul_tmul (e : Rl) (b : Mc) (x : leftIdeal e) :
    indMul Λ i β e (BalancedTensor.tmul b x) = b.val * ι x.val := rfl

private def indPrincipalEquiv {e : Rl} (he : IsIdempotentElem e) :
    BalancedTensor k Su Rl Mc (leftIdeal e) ≃ₗ[Su] leftIdeal (ι e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (indMul Λ i β e).codRestrict (leftIdeal (ι e)) fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      change (b.val * ι x.val) * ι e = b.val * ι x.val
      rw [mul_assoc, ← map_mul, mem_leftIdeal.mp x.2]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have inc (z : leftIdeal (ι e)) : z.val ∈ lIdeal (lastIdem Q i aΛ β) := by
    change z.val * ι 1 = z.val
    conv_lhs => rw [← mem_leftIdeal.mp z.property, mul_assoc, ← map_mul, mul_one]
    exact z.property
  let g : leftIdeal (ι e) →ₗ[Su] BalancedTensor k Su Rl Mc (leftIdeal e) :=
    { toFun := fun b => BalancedTensor.tmul (⟨b.val, inc b⟩ : Mc) p
      map_add' := fun x y => BalancedTensor.add_tmul (⟨x.val, inc x⟩ : Mc) (⟨y.val, inc y⟩ : Mc) p
      map_smul' := fun c x => BalancedTensor.smul_tmul' c (⟨x.val, inc x⟩ : Mc) p }
  apply LinearEquiv.ofLinearMap f g
  · ext x
    exact x.property
  · apply BalancedTensor.extB
    intro b x
    change BalancedTensor.tmul (op x.val • b) p = BalancedTensor.tmul b x
    rw [BalancedTensor.op_smul_tmul]
    exact congrArg (BalancedTensor.tmul b) (Subtype.ext (mem_leftIdeal.mp x.property))

/-- Right induction takes a degree-zero principal projective to the principal
projective of the last-strand image of its idempotent (Webster, Definition 3.15). -/
theorem indK0_ofIdempotent {e : Rl} (he : IsIdempotentElem e) (he0 : e ∈ srcGr 0) :
    indK0 G Λ i β (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dstGr) (ι e) (he.map (ι)) (cyclotomicLast_mem_grade G Λ i β he0)) := by
  rw [indK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (indPrincipalEquiv Λ i β he) ?_
  intro d y hy
  change indMul Λ i β e y ∈ dstGr d
  apply balancedGrading_map_mem dstGr ((indMul Λ i β e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, indMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dstGr) hz (cyclotomicLast_mem_grade G Λ i β hx)

end Principal

section Naturality

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) (Λ : I → ℕ) (i : I)
local notation "LP" => LaurentPolynomial ℤ
local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "fam" => (fun ν => K0 (grade G Λ ν))
local notation "Si" => (Singleton.singleton i : Multiset I)

private theorem projected_lof_cast {β γ : Multiset I} (h : β = γ) (e : KLRAlgebra k Q β)
    (he : IsIdempotentElem e) (h₀ : e ∈ G.grade β 0) :
    DirectSum.lof LP _ fam γ (K0.of (GProj.ofIdempotent (𝒜 := grade G Λ γ)
      (mk k Q aΛ γ (castKLR Q h e)) ((he.map (castKLR Q h)).map (mk k Q aΛ γ))
      (Graded.mem_map_of_mem _ _ (G.castKLR_mem_grade h h₀)))) =
    DirectSum.lof LP _ fam β (K0.of (GProj.ofIdempotent (𝒜 := grade G Λ β)
      (mk k Q aΛ β e) (he.map _) (Graded.mem_map_of_mem _ _ h₀))) := by
  subst γ
  rfl

private theorem lower_quotient_principal (β : Multiset I) {e : KLRAlgebra k Q β}
    (he : IsIdempotentElem e) (h₀ : e ∈ G.grade β 0) :
    lower G Λ i (totalQuotientK0 G Λ (DirectSum.lof LP _ G.K0fam β (K0.of (GProj.ofIdempotent e he h₀)))) =
      totalQuotientK0 G Λ (DirectSum.of G.K0fam β (K0.of (GProj.ofIdempotent e he h₀)) * G.clsW [i]) := by
  rw [totalQuotientK0_lof, lower_lof, quotientK0_ofIdempotent, indK0_ofIdempotent G Λ i β
    (he.map (mk k Q aΛ β)) (Graded.mem_map_of_mem _ _ h₀)]
  have hroot : G.clsW [i] = DirectSum.of G.K0fam Si (K0.of (GProj.ofIdempotent (𝒜 := G.grade Si)
      1 IsIdempotentElem.one SetLike.GradedOne.one_mem)) := by
    rw [G.clsW_eq [i] (rfl : ([i] : Multiset I) = Si)]
    apply congrArg (DirectSum.of G.K0fam Si)
    exact K0.of_ofIdempotent_congr (𝒜 := G.grade Si) (e_single (Q := Q) i _) _ _ _ _
  rw [hroot, G.K0R_of_mul_of, G.indK0_ofIdempotent]
  change _ = totalQuotientK0 G Λ (DirectSum.lof LP _ G.K0fam _ _)
  rw [totalQuotientK0_lof, quotientK0_ofIdempotent]
  have hcast := projected_lof_cast G Λ (add_comm β Si) (concat Q β Si (e ⊗ₜ[k] 1))
    (GradingDatum.concat_idem he IsIdempotentElem.one) (G.concat_mem_grade_zero h₀ SetLike.GradedOne.one_mem)
  refine Eq.trans ?_ hcast
  apply congrArg (DirectSum.lof LP _ fam (Si + β))
  apply K0.of_ofIdempotent_congr
  exact cyclotomicLast_mk Q i aΛ β e

/-- On all affine classes, extension to the cyclotomic quotient intertwines
right multiplication by the singleton class with the actual lowering functor
(Webster, Definition 3.15 and proof of Proposition 3.21). -/
theorem lower_totalQuotientK0 (hsym : KLRSymm Q) (hX : ∀ a, 0 < G.degX a) (x : G.K0R) :
    lower G Λ i (totalQuotientK0 G Λ x) = totalQuotientK0 G Λ (x * G.clsW [i]) := by
  let V : Submodule LP G.K0R :=
    { carrier := {z | lower G Λ i (totalQuotientK0 G Λ z) = totalQuotientK0 G Λ (z * G.clsW [i])}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        change lower G Λ i (totalQuotientK0 G Λ (a + b)) = _
        simpa only [map_add, add_mul] using congrArg₂ (· + ·) ha hb
      smul_mem' := fun c a ha => by
        change lower G Λ i (totalQuotientK0 G Λ (c • a)) = _
        simpa only [map_smul, smul_mul_assoc] using congrArg (c • ·) ha }
  change x ∈ V
  induction x using DirectSum.induction_on with
  | zero => exact V.zero_mem
  | add a b ha hb => exact V.add_mem ha hb
  | @of β y =>
    let := G.hasGdim_grade' (ν := β) hsym hX
    let l := DirectSum.lof LP _ G.K0fam β
    have H : ⊤ ≤ V.comap l := by
      rw [← K0.span_indec (G.grade β)]
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      obtain ⟨e, he, he0, j, ⟨u⟩⟩ := b.isIndec_rep.exists_iso_ofIdempotent
      change K0.of b.rep ∈ V.comap l
      rw [K0.of_eq_of_iso u, ← K0.T_smul_of]
      exact (V.comap l).smul_mem _ (lower_quotient_principal G Λ i β he he0)
    exact H (Submodule.mem_top (x := y))

end Naturality

section Serre

open KL2 KL2Gamma Finset LaurentPolynomial

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {C : CartanDatum I} (hQ : IsRouquierQ C Q)

local notation "G" => hQ.gradingDatum
local notation "LP" => LaurentPolynomial ℤ

private theorem clsW_replicate (i : I) (n : ℕ) : (G).clsW (List.replicate n i) = (G).clsW [i] ^ n := by
  induction n with
  | zero => simpa only [List.replicate_zero, pow_zero] using (G).clsW_nil
  | succ n ih =>
    rw [List.replicate_succ, pow_succ', ← ih]
    exact (G).clsW_append [i] (List.replicate n i)

/-- The undivided quantum Serre relation in the affine induction algebra, with
the full quantum binomial coefficients (Rouquier, §4.1.1, Proposition 4.2). -/
theorem affine_clsW_serre {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range (C.serreN i j + 1), ((-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) (C.serreN i j) a) •
      ((G).clsW [i] ^ a * (G).clsW [j] * (G).clsW [i] ^ (C.serreN i j - a)) = 0 := by
  classical
  let N := (C).serreN i j
  have hN : N = (C).dij i j + 1 := serreN_eq_dij hij
  let d : ℕ → List (I × ℕ) := fun a => [(i, a), (j, 1), (i, N - a)]
  let ν : Multiset I := (j :: List.replicate N i : List I)
  have hm : ν.card = N + 1 := by simp [ν]
  have hexp (a : ℕ) : expandDiv (d a) = List.replicate a i ++ j :: List.replicate (N - a) i := by
    simp [d, expandDiv]
  have hν (a : ℕ) (ha : a ≤ N) : (expandDiv (d a) : Multiset I) = ν := by
    rw [hexp]
    apply Multiset.coe_eq_coe.2
    refine List.perm_middle.trans ?_
    rw [← List.replicate_add, show a + (N - a) = N by omega]
  let t : Seq ν := KLRAlgebra.Seq.ofList (j :: List.replicate N i) rfl
  have hpN : 0 + N < ν.card := by omega
  have htlabel (r : Fin ν.card) : t.lbl r = if (r : ℕ) = 0 then j else i := by
    change (KLRAlgebra.Seq.ofList (List.replicate 0 i ++ j :: List.replicate N i) rfl).lbl r = _
    rw [KLRAlgebra.Seq.ofList_lbl, getElem_midL]
  have ht₀ : ∀ r : Fin ν.card, (r : ℕ) = 0 → t.lbl r = j := by
    intro r hr
    rw [htlabel, ite_eq_left hr]
  have ht : ∀ r : Fin ν.card, (0 : ℕ) < r → (r : ℕ) ≤ 0 + N → t.lbl r = i := by
    intro r hr _
    rw [htlabel, ite_eq_right (by omega)]
  have hSeq (a : ℕ) (ha : a ≤ N) : serreSeq t 0 a = KLRAlgebra.Seq.ofList (expandDiv (d a)) (hν a ha) := by
    apply Subtype.ext
    funext r
    change (serreSeq t 0 a).lbl r = (KLRAlgebra.Seq.ofList (expandDiv (d a)) (hν a ha)).lbl r
    rw [lbl_serreSeq hpN ht₀ ht ha r, KLRAlgebra.Seq.ofList_lbl]
    have hr : (r : ℕ) ≤ N := by have := r.2; omega
    simp only [zero_add, Nat.zero_le, hr, and_self, ite_true]
    have he := getElem_midL i j a (N - a) (r : ℕ) (by
      simp only [List.length_append, List.length_replicate, List.length_cons]
      omega)
    simpa only [hexp a, KLRAlgebra.Seq.ofList_lbl] using he.symm
  have hIdem (a : ℕ) :
      (divIdem (serreSeq t 0 a) (blocksDiv (d a) 0) : KLRAlgebra k Q ν) =
        divIdem (serreSeq t 0 a) [(0, a), (a + 1, N - a)] := by
    rw [← divIdem_bigBlocks _ (blocksDiv (d a) 0),
      ← divIdem_bigBlocks _ [(0, a), (a + 1, N - a)]]
    congr 1
    by_cases h1 : 2 ≤ a <;> by_cases h2 : 2 ≤ N - a <;>
      simp [d, blocksDiv, bigBlocks, h1, h2]
  let sh : ℕ → ℤ := fun a => divAngle2 C (d a)
  have hshform (a : ℕ) : sh a = (C).dot i i / 2 * ((a.choose 2 : ℕ) + ((N - a).choose 2 : ℕ) : ℤ) := by
    simpa only [sh, d, List.nil_append, List.append_nil, divAngle2, List.map_nil, List.sum_nil, zero_add]
      using divAngle2_serre C [] [] i j a (N - a)
  have hsh : ∀ a, a < N → sh (a + 1) = sh a +
      (-((N - a - 1 : ℕ) : ℤ) * (C).dot i i - (C).dot i j) := by
    intro a ha
    rw [hshform, hshform]
    have e1 : ((a + 1).choose 2 : ℤ) = (a.choose 2 : ℕ) + a := by
      rw [NilHecke.choose_two_succ]; push_cast; ring
    have e2 : ((N - a).choose 2 : ℤ) = ((N - (a + 1)).choose 2 : ℕ) + ((N - a - 1 : ℕ) : ℤ) := by
      rw [show N - a = (N - (a + 1)) + 1 by omega, NilHecke.choose_two_succ]
      push_cast
      rw [show N - (a + 1) = N - a - 1 by omega]
    have e3 : ((N - a - 1 : ℕ) : ℤ) = N - a - 1 := by omega
    obtain ⟨r, hr⟩ := (C).dot_self_even i
    have e4 : (C).dot i i / 2 = r := by omega
    have e5 := (C).two_mul_dot_eq hij
    change 2 * (C).dot i j = (C).dot i i * (1 - (N : ℤ)) at e5
    rw [e1, e2, e3, e4]
    rw [hr] at e5 ⊢
    have e6 : (C).dot i j = r * (1 - N) := by linarith
    linear_combination e6
  let P (a : ℕ) : K0 ((G).grade ν) := if ha : a ≤ N then
    K0.of (GProj.ofIdempotent (hflip (Rouquier.etop t 0 N a : KLRAlgebra k Q ν))
      (Rouquier.isIdempotentElem_hflip_etop hpN ht₀ ht ha)
      (Rouquier.hflip_etop_mem_grade hpN ht₀ ht G (fun _ _ => rfl) ha)) else 0
  have hP (a : ℕ) (ha : a ≤ N) : P a =
      K0.of (GProj.ofIdempotent (hflip (Rouquier.etop t 0 N a : KLRAlgebra k Q ν))
        (Rouquier.isIdempotentElem_hflip_etop hpN ht₀ ht ha)
        (Rouquier.hflip_etop_mem_grade hpN ht₀ ht G (fun _ _ => rfl) ha)) := dite_eq_left ha
  let hs (x y : I) : (G).degΨ x y = (G).degΨ y x := congrArg Neg.neg (C.symm x y)
  have hclass (a : ℕ) (ha : a ≤ N) :
      K0.of ((G).dividedProjective hs C (d a) (hν a ha)) = (T (-sh a) : LP) • P a := by
    rw [GradingDatum.dividedProjective, ← K0.T_smul_of, hP a ha]
    apply congrArg ((T (-sh a) : LP) • ·)
    apply K0.of_ofIdempotent_congr
    apply congrArg hflip
    rw [← hSeq a ha, Rouquier.etop_eq_divIdem]
    simpa only [Nat.zero_add] using hIdem a
  let v := tUnit (C.dot i i / 2)
  have hfact (a : ℕ) (ha : a ≤ N) :
      qbinom v N a * divQFact2 C (d a) = qfact v N := by
    have h := qbinom_mul_qfact v (N - a) a
    rw [Nat.sub_add_cancel ha] at h
    simpa [d, divQFact2, v, mul_comm, mul_assoc, mul_left_comm] using h
  let L := DirectSum.lof LP _ (G).K0fam ν
  have key (a : ℕ) (ha' : a ∈ range (N + 1)) :
      ((-1 : LP)^a * qbinom v N a) • ((G).clsW [i] ^ a * (G).clsW [j] * (G).clsW [i] ^ (N - a)) =
        qfact v N • L (((-1 : LP)^a * (T (-sh a) : LP)) • P a) := by
    have ha : a ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using ha'
    have hw : (G).clsW [i] ^ a * (G).clsW [j] * (G).clsW [i] ^ (N - a) =
        (G).clsW (expandDiv (d a)) := by
      rw [← clsW_replicate hQ, ← clsW_replicate hQ, ← (G).clsW_append, ← (G).clsW_append, hexp]
      simp
    rw [hw, (G).clsW_eq (expandDiv (d a)) (hν a ha)]
    change _ • L (K0.of _) = _
    rw [show K0.of ((G).projP (Seq.ofList (expandDiv (d a)) (hν a ha))) = _ from
      (G).of_expanded_eq_factorial hs C (fun _ => rfl) (d a) (hν a ha), hclass a ha]
    simp only [map_smul, smul_smul]
    congr 1
    calc
      _ = (-1 : LP)^a * (qbinom v N a * divQFact2 C (d a)) * (T (-sh a) : LP) := by ring
      _ = _ := by rw [hfact a ha]; ring
  change ∑ a ∈ range (N + 1), _ = _
  rw [sum_congr rfl key, ← Finset.smul_sum, ← map_sum,
    Rouquier.K0_serre_window hpN ht₀ ht hQ hij hN sh hsh P hP, map_zero, smul_zero]

private theorem lower_pow_totalQuotientK0 (Λ : I → ℕ) (i : I) (n : ℕ) (x : (G).K0R) :
    ((lower G Λ i)^n) (totalQuotientK0 G Λ x) = totalQuotientK0 G Λ (x * (G).clsW [i] ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, lower_totalQuotientK0 G Λ i
      (fun a b hab => (hQ.symm a b hab).symm) C.dot_self_pos, pow_succ, mul_assoc]

/-- The quantum Serre relation for the actual (undivided) cyclotomic induction
operators, integrally on all weights and all projective classes
(Webster, Proposition 3.21; Rouquier, §4.1.1, Proposition 4.2). -/
theorem lower_serre (Λ : I → ℕ) {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range (C.serreN i j + 1), ((-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) (C.serreN i j) a) •
      ((lower G Λ i)^(C.serreN i j - a) * lower G Λ j * (lower G Λ i)^a) = 0 := by
  let N := C.serreN i j
  let c (a : ℕ) := (-1 : LP)^a * qbinom (tUnit (C.dot i i / 2)) N a
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := totalQuotientK0_surjective G Λ
    (fun a b hab => (hQ.symm a b hab).symm) C.dot_self_pos z
  change (∑ a ∈ range (N + 1), c a • ((lower G Λ i)^(N - a) * lower G Λ j * (lower G Λ i)^a))
    (totalQuotientK0 G Λ x) = 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    lower_pow_totalQuotientK0 hQ, lower_totalQuotientK0 G Λ j
      (fun a b hab => (hQ.symm a b hab).symm) C.dot_self_pos]
  simp_rw [mul_assoc x, ← map_smul, ← mul_smul_comm]
  rw [← map_sum, ← Finset.mul_sum]
  have h := affine_clsW_serre hQ hij
  change ∑ a ∈ range (N + 1), c a • _ = 0 at h
  simpa only [mul_assoc, mul_smul_comm, mul_zero, map_zero] using congrArg (fun m => totalQuotientK0 G Λ (x * m)) h

end Serre

end Categorification.KLR.CycKLR
