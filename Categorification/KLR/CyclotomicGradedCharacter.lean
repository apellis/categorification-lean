/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentEquivalence
import Categorification.KLR.CyclotomicGrading
import Categorification.KLR.CyclotomicFinite
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.Gamma

/-!
# Graded dimensions of cyclotomic KLR corners

J. Hu and L. Shi, arXiv:2108.05508v5, Theorem 1.1, and Kang–Kashiwara,
arXiv:1102.4677v4, Theorem 5.2. When a common final colour is absent from
the lower root content, the lower `FE` term vanishes. The `EF` corner is
the sum of the lower algebra shifted by successive powers of the last dot.
This section of the recursion allows the lower colours to repeat and to
interact with the final colour. Iterating the recursion gives the closed product
for a diagonal word of pairwise distinct colours in Hu–Shi, Theorem 1.1.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra.AbsentColour

open Categorification.Graded DirectSum Polynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) (Λ : I → ℕ)
  (i : I) (β : Multiset I)

local notation "aΛ" => (fun j => Polynomial.X ^ Λ j : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Ri" => KLRAlgebra k Q Si
local notation "Rl" => CycKLR k Q aΛ β
local notation "S" => CycKLR k Q aΛ (Si + β)

/-- In the finite dot-unit sum from KK Theorem 5.2 the `r`th map has degree
`r • degX i`, for the homogeneous cyclotomic polynomial `X ^ Λ i`. -/
theorem dotUnitTerm_mem_grade (r : ℕ) {d : ℤ} {x : Rl}
    (hx : x ∈ CycKLR.grade G Λ β d) :
    (dotUnitTerm Q i aΛ β r x : S) ∈ CycKLR.grade G Λ (Si + β) (d + r • G.degX i) := by
  obtain ⟨u, hu, rfl⟩ := hx
  let p : Fin (Multiset.card Si) := ⟨0, by simp⟩
  let v := (KLRAlgebra.x p : Ri) ^ r
  have hdot : (KLRAlgebra.x p : Ri) ∈ G.grade Si (G.degX i) := by
    let s : Seq Si := default
    have H := G.x_mul_e_mem_grade p s
    have hs : s.lbl p = i := Multiset.mem_singleton.mp (s.mem p)
    rw [e_eq_one, mul_one, hs] at H
    exact H
  have hv : v ∈ G.grade Si (r • G.degX i) := SetLike.pow_mem_graded r hdot
  have H := G.castKLR_mem_grade (add_comm β Si) (G.concat_tmul_mem_grade hu hv)
  have he : (dotUnitTerm Q i aΛ β r (CycKLR.mk k Q aΛ β u) : S) =
      CycKLR.mk k Q aΛ (Si + β) (cLL Q i β (u ⊗ₜ v)) := by
    change cyclotomicLast Q i aΛ β (CycKLR.mk k Q aΛ β u) * _ * cyclotomicLast Q i aΛ β 1 = _
    rw [cyclotomicLast_mk, cyclotomicLast_one, cLL_tmul, cLL_one_tmul]
    simp only [v, map_pow, singlePoly_x, Polynomial.aeval_X, map_mul, mul_assoc]
  change (dotUnitTerm Q i aΛ β r (CycKLR.mk k Q aΛ β u) : S) ∈ _
  rw [he]
  exact Graded.mem_map_of_mem _ _ H

private def gradeProjection {A : Type*} [AddCommGroup A] [Module k A] (𝒜 : ℤ → Submodule k A)
    [Decomposition 𝒜] (d : ℤ) : Module.End k A :=
  (𝒜 d).subtype ∘ₗ DirectSum.component k _ (fun n => ↥(𝒜 n)) d ∘ₗ (decomposeLinearEquiv 𝒜).toLinearMap

private theorem dotUnitTerm_projection (r : ℕ) (d : ℤ) (z : Rl) :
    gradeProjection (CycKLR.grade G Λ (Si + β)) d (dotUnitTerm Q i aΛ β r z : S) =
      (dotUnitTerm Q i aΛ β r
        (gradeProjection (Graded.shift (CycKLR.grade G Λ β) (r • G.degX i)) d z) : S) := by
  let F := (cornerSub Q i aΛ β).subtype ∘ₗ dotUnitTerm Q i aΛ β r
  have h : PreservesGrading (Graded.shift (CycKLR.grade G Λ β) (r • G.degX i))
      (CycKLR.grade G Λ (Si + β)) F := by
    intro j x hx
    change (dotUnitTerm Q i aΛ β r x : S) ∈ _
    simpa only [sub_add_cancel] using
      (dotUnitTerm_mem_grade G Λ i β r (d := j - r • G.degX i) hx)
  exact decompose_map h z d

private theorem dotUnitSum_val (n : ℕ) (v : Fin n → Rl) :
    (dotUnitSum Q i aΛ β n v : S) = ∑ j : Fin n, (dotUnitTerm Q i aΛ β (j : ℕ) (v j) : S) := by
  simp only [dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum]

variable [Nontrivial k] (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (hwWeight : X)
  (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) hwWeight)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hi : i ∉ β)

local notation "m" => Int.toNat (RD.pair (RD.iY i) (hwWeight - Multiset.sum (Multiset.map RD.iX β)))

include hsym hQ hΛ hdeg hi in
/-- The ungraded dot-unit equivalence for an absent colour restricts to each
degree, with the `j`th coefficient shifted by the degree of the `j`th dot power. -/
theorem dotUnitSum_mem_grade_iff (d : ℤ) (v : Fin m → Rl) :
    (dotUnitSum Q i aΛ β m v : S) ∈ CycKLR.grade G Λ (Si + β) d ↔
      ∀ j : Fin m, v j ∈ CycKLR.grade G Λ β (d - (j : ℕ) • G.degX i) := by
  constructor
  · intro hv
    let v' (j : Fin m) := gradeProjection (Graded.shift (CycKLR.grade G Λ β)
      ((j : ℕ) • G.degX i)) d (v j)
    have H : dotUnitSum Q i aΛ β m v' = dotUnitSum Q i aΛ β m v := by
      apply Subtype.ext
      rw [dotUnitSum_val]
      calc
        _ = ∑ j : Fin m, gradeProjection (CycKLR.grade G Λ (Si + β)) d
            (dotUnitTerm Q i aΛ β (j : ℕ) (v j) : S) :=
          Finset.sum_congr rfl fun j _ => (dotUnitTerm_projection G Λ i β j d _).symm
        _ = gradeProjection (CycKLR.grade G Λ (Si + β)) d (dotUnitSum Q i aΛ β m v : S) := by
          rw [dotUnitSum_val, map_sum]
        _ = _ := decompose_of_mem_same _ hv
    have hnat : (((aΛ i).natDegree : ℕ) : ℤ) = RD.pair (RD.iY i) hwWeight := by
      simpa using hΛ
    have eqv := (dotUnitSum_bijective Q i β hsym aΛ hQ (fun j => monic_X_pow _) RD hwWeight
      hnat hdeg hi).injective H
    intro j
    rw [← congrFun eqv j]
    exact (decompose (Graded.shift (CycKLR.grade G Λ β) ((j : ℕ) • G.degX i)) (v j) d).2
  · intro hv
    rw [dotUnitSum_val]
    refine Submodule.sum_mem _ fun j _ => ?_
    simpa only [sub_add_cancel] using dotUnitTerm_mem_grade G Λ i β (j : ℕ) (hv j)

section Cuts

omit [Nontrivial k]

/-- The common new final colour in the two sequences in Hu–Shi's formula. -/
def appendColour (s : Seq β) : Seq (Si + β) :=
  Seq.cast (add_comm β Si) (s.append (default : Seq Si))

private abbrev seqIdem {γ : Multiset I} (s : Seq γ) := CycKLR.mk k Q aΛ γ (e s)

private theorem seqIdem_mul_self {γ : Multiset I} (s : Seq γ) :
    seqIdem (Q := Q) Λ s * seqIdem Λ s = seqIdem Λ s := by
  change CycKLR.mk k Q aΛ γ _ * CycKLR.mk k Q aΛ γ _ = _
  rw [← map_mul, e_mul_self]

private theorem corner_mem_iff_fixed {γ : Multiset I} (s t : Seq γ) (z : CycKLR k Q aΛ γ) :
    z ∈ CycKLR.corner k Q aΛ s t ↔ seqIdem Λ s * (z * seqIdem Λ t) = z := by
  constructor
  · rintro ⟨u, rfl⟩
    change seqIdem Λ s * ((seqIdem Λ s * (u * seqIdem Λ t)) * seqIdem Λ t) = _
    simp only [mul_assoc, seqIdem_mul_self]
    rw [← mul_assoc, seqIdem_mul_self]
    rfl
  · intro h
    exact ⟨z, h⟩

private theorem last_seqIdem (s : Seq β) :
    cyclotomicLast Q i aΛ β (seqIdem Λ s) = seqIdem Λ (appendColour i β s) := by
  rw [seqIdem, cyclotomicLast_mk, cL_e]
  rfl

private theorem append_corner_le (s t : Seq β) :
    CycKLR.corner k Q aΛ (appendColour i β s) (appendColour i β t) ≤ cornerSub Q i aΛ β := by
  rintro z ⟨u, rfl⟩
  let A := seqIdem (Q := Q) Λ (appendColour i β s)
  let B := seqIdem (Q := Q) Λ (appendColour i β t)
  let T := CycKLR.mk k Q aΛ (Si + β) (cL Q i β 1)
  change T * (A * (u * B)) = A * (u * B) ∧ (A * (u * B)) * T = A * (u * B)
  have hL : T * A = A := by
    dsimp only [T, A]
    rw [← cyclotomicLast_one, ← last_seqIdem, ← map_mul, one_mul]
  have hR : B * T = B := by
    dsimp only [T, B]
    rw [← cyclotomicLast_one, ← last_seqIdem, ← map_mul, mul_one]
  exact ⟨by rw [← mul_assoc, hL], by rw [mul_assoc, mul_assoc, hR]⟩

private theorem dotUnitSum_cut (n : ℕ) (s t : Seq β) (v : Fin n → Rl) :
    (dotUnitSum Q i aΛ β n (fun j => seqIdem Λ s * (v j * seqIdem Λ t)) : S) =
      seqIdem Λ (appendColour i β s) *
        ((dotUnitSum Q i aΛ β n v : S) * seqIdem Λ (appendColour i β t)) := by
  rw [dotUnitSum_left, dotUnitSum_right, corner_smul_val, corner_op_smul_val, MulOpposite.unop_op,
    last_seqIdem, last_seqIdem]

end Cuts

include hsym hQ hΛ hdeg hi in
private theorem dotUnitSum_mem_corner_iff (s t : Seq β) (v : Fin m → Rl) :
    (dotUnitSum Q i aΛ β m v : S) ∈ CycKLR.corner k Q aΛ (appendColour i β s) (appendColour i β t) ↔
      ∀ j, v j ∈ CycKLR.corner k Q aΛ s t := by
  rw [corner_mem_iff_fixed, ← dotUnitSum_cut]
  simp only [corner_mem_iff_fixed]
  have inj := (dotUnitSum_bijective Q i β hsym aΛ hQ (fun j => monic_X_pow _) RD hwWeight
    (by simpa using hΛ) hdeg hi).injective
  exact ⟨fun h j => congrFun (inj (Subtype.ext h)) j, fun h => congrArg
    (fun w => (dotUnitSum Q i aΛ β m w : S)) (funext h)⟩

/-- The finite dot-unit maps identify the degree-`d` part of an appended
sequence corner with the indicated graded pieces of the lower corner.
This is the common-final-absent-colour recursion underlying Hu–Shi,
arXiv:2108.05508v5, Theorem 1.1, proved using KK Theorem 5.2. -/
def appendedCornerGradeEquiv (s t : Seq β) (d : ℤ) :
    ((j : Fin m) → ↥(CycKLR.grade G Λ β (d - (j : ℕ) • G.degX i) ⊓ CycKLR.corner k Q aΛ s t)) ≃ₗ[k]
      ↥(CycKLR.grade G Λ (Si + β) d ⊓ CycKLR.corner k Q aΛ (appendColour i β s) (appendColour i β t)) := by
  let D (j : Fin m) := CycKLR.grade G Λ β (d - (j : ℕ) • G.degX i) ⊓ CycKLR.corner k Q aΛ s t
  let V := CycKLR.grade G Λ (Si + β) d ⊓ CycKLR.corner k Q aΛ (appendColour i β s) (appendColour i β t)
  let F := dotUnitSum Q i aΛ β m
  let jn : ((j : Fin m) → ↥(D j)) →ₗ[k] (Fin m → Rl) :=
    LinearMap.pi fun j => (D j).subtype ∘ₗ LinearMap.proj j
  have hF : Function.Bijective F := dotUnitSum_bijective Q i β hsym aΛ hQ
    (fun _ => monic_X_pow _) RD hwWeight (by simpa using hΛ) hdeg hi
  have hmem (v : Fin m → Rl) : (F v : S) ∈ V ↔ ∀ j, v j ∈ D j := by
    change (_ ∈ CycKLR.grade G Λ (Si + β) d ∧ _ ∈ CycKLR.corner k Q aΛ _ _) ↔ _
    rw [dotUnitSum_mem_grade_iff G Λ i β hsym hQ RD hwWeight hΛ hdeg hi,
      dotUnitSum_mem_corner_iff Λ i β hsym hQ RD hwWeight hΛ hdeg hi]
    exact ⟨fun ⟨hg, hc⟩ j => ⟨hg j, hc j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  let f : ((j : Fin m) → ↥(D j)) →ₗ[k] V :=
    ((cornerSub Q i aΛ β).subtype ∘ₗ F ∘ₗ jn).codRestrict V (fun z => (hmem _).mpr fun j => (z j).2)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    have h : F (jn x) = F (jn y) := Subtype.ext (congrArg (fun a : V => (a : S)) hxy)
    funext j
    exact Subtype.ext (congrFun (hF.injective h) j)
  · intro z
    let w : Corner Q i aΛ β := ⟨z.val, append_corner_le Λ i β s t z.property.2⟩
    obtain ⟨v, hv⟩ := hF.surjective w
    have hv' : (F v : S) = z.val := congrArg Subtype.val hv
    have hz := (hmem v).mp (hv' ▸ z.property)
    exact ⟨fun j => ⟨v j, hz j⟩, Subtype.ext hv'⟩

end Categorification.KLR.KLRAlgebra.AbsentColour

namespace Categorification.KLR.KLRAlgebra.AbsentColour

open Polynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) (Λ : I → ℕ)
    (i : I) (β : Multiset I) (hsym : KLRSymm Q)
    (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
    {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : QuantumGroup.UDot.WeightDatum C X Y) (hwWeight : X)
    (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) hwWeight)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hi : i ∉ β)

local notation "aΛ" => (fun j => Polynomial.X ^ Λ j : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "m" => Int.toNat (RD.pair (RD.iY i) (hwWeight - Multiset.sum (Multiset.map RD.iX β)))

include hsym hQ hΛ hdeg hi in
/-- Hu–Shi, arXiv:2108.05508v5, Theorem 1.1, common final absent colour:
each coefficient of the new corner is the sum of the shifted coefficients
of the lower corner. In the Cartan grading the shifts are `2 d_i j`, giving
the factor `q_i^(m-1) [m]_i`. The two lower words can differ and have arbitrary
multiplicities; the new colour may interact with every earlier colour. -/
theorem finrank_appendedCornerGrade (s t : Seq β) (d : ℤ) :
    Module.finrank k ↥(CycKLR.grade G Λ (Si + β) d ⊓
        CycKLR.corner k Q aΛ (appendColour i β s) (appendColour i β t)) =
      ∑ j : Fin m, Module.finrank k ↥(CycKLR.grade G Λ β (d - (j : ℕ) • G.degX i) ⊓
        CycKLR.corner k Q aΛ s t) := by
  have hQ' (j l : I) (h : j ≠ l) : IsUnit (polyInY (Q j l)).leadingCoeff := by
    obtain ⟨c, hc, he⟩ := hQ j l h
    rw [he]
    exact hc.map Polynomial.C
  let _ := CycKLR.module_finite (ν := β) hQ' (fun j => monic_X_pow (R := k) (Λ j))
  rw [← (appendedCornerGradeEquiv G Λ i β hsym hQ RD hwWeight hΛ hdeg hi s t d).finrank_eq,
    Module.finrank_pi_fintype]

end Categorification.KLR.KLRAlgebra.AbsentColour

namespace Categorification.KLR.KLRAlgebra.AbsentColour

open Polynomial DirectSum

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) (Λ : I → ℕ)
    {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : QuantumGroup.UDot.WeightDatum C X Y) (hwWeight : X)

local notation "aΛ" => (fun j => Polynomial.X ^ Λ j : I → Polynomial k)

private theorem emptyDiagonal (s : Seq (0 : Multiset I)) (d : ℤ) :
    Module.finrank k ↥(CycKLR.grade G Λ 0 d ⊓ CycKLR.corner k Q aΛ s s) =
      (1 : LaurentPolynomial ℕ).coeff d := by
  let A := CycKLR k Q aΛ (0 : Multiset I)
  let E := cyclotomicZeroEquiv Q aΛ
  have hg (x : A) : x ∈ CycKLR.grade G Λ 0 0 := by
    obtain ⟨c, rfl⟩ := E.symm.surjective x
    change algebraMap k A c ∈ _
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (SetLike.one_mem_graded _)
  have hc : CycKLR.corner k Q aΛ s s = ⊤ := by
    apply top_unique
    intro x _
    refine ⟨x, ?_⟩
    change CycKLR.mk k Q aΛ _ (e s) * (x * CycKLR.mk k Q aΛ _ (e s)) = x
    simp [e_eq_one]
  rw [hc, inf_top_eq]
  by_cases hd : d = 0
  · subst d
    rw [show CycKLR.grade G Λ 0 0 = ⊤ from top_unique fun x _ => hg x,
      finrank_top, E.toLinearEquiv.finrank_eq]
    simp
  · have hbot : CycKLR.grade G Λ 0 d = ⊥ := by
      apply bot_unique
      intro x hx
      exact (decompose_of_mem_same _ hx).symm.trans (decompose_of_mem_ne _ (hg x) (Ne.symm hd))
    rw [hbot, finrank_bot]
    change 0 = (Finsupp.single 0 1 : ℤ →₀ ℕ) d
    exact Eq.symm (Finsupp.single_eq_of_ne (b := (1 : ℕ)) hd)

/-- The geometric factor at a position of a multiplicity-free diagonal word.
Its upper bound is Hu–Shi's prefix pairing `N^Λ(1,ν,t)` (arXiv:2108.05508v5,
Definition 3.2), and each dot contributes degree `G.degX i`. -/
def diagonalFactor (prior : List I) (i : I) : LaurentPolynomial ℕ :=
  ∑ j : Fin (RD.pair (RD.iY i) (hwWeight - (prior.map RD.iX).sum)).toNat,
    AddMonoidAlgebra.single ((j : ℕ) • G.degX i) 1

omit [DecidableEq I] in
private theorem diagonalFactors_append (word : List I) (i : I) :
    ((word ++ [i]).mapIdx (fun t j => diagonalFactor G RD hwWeight ((word ++ [i]).take t) j)).prod =
      (word.mapIdx (fun t j => diagonalFactor G RD hwWeight (word.take t) j)).prod *
        diagonalFactor G RD hwWeight word i := by
  rw [List.mapIdx_append_one, List.prod_append]
  simp only [List.take_append_of_le_length (Nat.le_refl _), List.take_length, List.prod_singleton]
  congr 2
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro t ht
  rw [List.take_append_of_le_length ht.le]

omit [DecidableEq I] in
private theorem seq_ofList_cast {β γ : Multiset I} (word : List I)
    (h : (word : Multiset I) = β) (e : β = γ) :
    Seq.cast e (Seq.ofList word h) = Seq.ofList word (h.trans e) := by
  subst e
  rfl

omit [DecidableEq I] in
private theorem appendColour_ofList (word : List I) (i : I)
    (h : ((word ++ [i] : List I) : Multiset I) = {i} + (word : Multiset I)) :
    appendColour i (word : Multiset I) (Seq.ofList word rfl) = Seq.ofList (word ++ [i]) h := by
  have ea := KLGamma.seq_ofList_append word [i] (Multiset.coe_add word [i]).symm
  have es : (default : Seq ({i} : Multiset I)) = Seq.ofList [i] rfl := Subsingleton.elim ..
  exact (congrArg (fun z : Seq ({i} : Multiset I) =>
      Seq.cast (add_comm _ _) ((Seq.ofList word rfl).append z)) es).trans
    ((congrArg (Seq.cast (add_comm (word : Multiset I) ({i} : Multiset I))) ea.symm).trans
      (seq_ofList_cast ..))

variable (hsym : KLRSymm Q)
    (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) hwWeight)
    (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

include hsym hQ hΛ hdeg in
/-- Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 and Definition 3.2, equation (3.3),
for a diagonal word of pairwise distinct colours. The identity is the only
permutation fixing the word. Its contribution is a product over positions
of the geometric sums `diagonalFactor`, with the pairing computed on the
preceding prefix. For the Cartan grading each factor is
`q_i^(N-1) [N]_i`, including the zero factor when `N = 0`. -/
theorem finrank_diagonalCornerGrade_of_nodup (word : List I) (hnd : word.Nodup)
    {β : Multiset I} (hβ : (word : Multiset I) = β) (d : ℤ) :
    Module.finrank k ↥(CycKLR.grade G Λ β d ⊓
      CycKLR.corner k Q aΛ (Seq.ofList word hβ) (Seq.ofList word hβ)) =
      (word.mapIdx (fun t i => diagonalFactor G RD hwWeight (word.take t) i)).prod.coeff d := by
  induction word using List.reverseRecOn generalizing β d with
  | nil =>
    subst β
    exact emptyDiagonal G Λ _ d
  | append_singleton word i ih =>
    have he : ((word ++ [i] : List I) : Multiset I) = {i} + (word : Multiset I) :=
      (Multiset.coe_add word [i]).symm.trans (add_comm _ _)
    obtain rfl : β = {i} + (word : Multiset I) := hβ.symm.trans he
    have hi : i ∉ (word : Multiset I) := fun hm =>
      (List.nodup_append.mp hnd).2.2 i hm i (by simp) rfl
    rw [← appendColour_ofList word i hβ, finrank_appendedCornerGrade G Λ i _ hsym hQ RD hwWeight
      (hΛ i) (hdeg i) hi, diagonalFactors_append, diagonalFactor, Finset.mul_sum,
      AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [AddMonoidAlgebra.coeff_mul_single_apply, mul_one, ← sub_eq_add_neg,
      Multiset.map_coe, Multiset.sum_coe]
    exact Finset.sum_congr rfl fun j _ => ih hnd.of_append_left rfl _
end Categorification.KLR.KLRAlgebra.AbsentColour
