/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection
import Categorification.KLR.CyclotomicMixedInversionTensor
import Categorification.KLR.CyclotomicK0
import Categorification.KLR.CyclotomicMixedMate.MixedCrossing
import Categorification.WeightedKLR.RedStrands.DividedProjectives

/-!
# The distinct-colour crossing spans the mixed Stendhal corner

Webster, arXiv:1309.3796v2, Lemma 4.35, distinct-colour case. The affine
single-crossing Mackey decomposition projects to a spanning family for the
rectangular corner with different final black labels at its two ends.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra MixedAffine MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
local notation "S" => affineCoverQ Q Λ

private def projectAt {γ : Multiset (I ⊕ Fin ℓ)} {ν : Multiset I} (h : γ = stendhalWeight ℓ ν) :
    KLRAlgebra k S γ →ₐ[k] TensorProductAlgebra k Q Λ ν :=
  (affineTensorProjection Λ ν).comp (castKLR S h).toAlgHom

private theorem projectAt_cast {γ δ : Multiset (I ⊕ Fin ℓ)} {ν : Multiset I}
    (h : γ = δ) (h' : δ = stendhalWeight ℓ ν) (x : KLRAlgebra k S γ) :
    projectAt Λ h' (castAlg S h x) = projectAt Λ (h.trans h') x := by subst δ; rfl

/-- Append a right black strand when the two orders of adding black weight
are identified by `h`. -/
def appendBlackAt (i : I) {ν β : Multiset I} (h : ({i} : Multiset I) + ν = β) :
    TensorProductAlgebra k Q Λ ν →ₙₐ[k] TensorProductAlgebra k Q Λ β :=
  h ▸ appendBlack Q Λ i ν

private theorem proj_inc (i : I) {γ : Multiset (I ⊕ Fin ℓ)} {ν β : Multiset I}
    (h : γ = stendhalWeight ℓ ν) (hb : ({i} : Multiset I) + ν = β)
    (h' : γ + {Sum.inl i} = stendhalWeight ℓ β) (x : KLRAlgebra k S γ) :
    projectAt Λ h' (Lower.inc S γ (Sum.inl i) x) = appendBlackAt Λ i hb (projectAt Λ h x) := by
  subst β
  subst γ
  change affineTensorProjection Λ _ (castKLR S _ _) =
    appendBlack Q Λ i ν (affineTensorProjection Λ ν x)
  rw [appendBlack_affineTensorProjection, cL_eq_cast]
  have hc {a b c : Multiset (I ⊕ Fin ℓ)} (e : a = b) (f : b = c) (z : KLRAlgebra k S a) :
      castKLR S f (castKLR S e z) = castKLR S (e.trans f) z := by subst c; subst b; rfl
  rw [hc]
  rfl

variable (ν : Multiset I) (i j : I)
local notation "μ" => stendhalWeight ℓ ν
local notation "b" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "c" => (Sum.inl j : I ⊕ Fin ℓ)
local notation "νi" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νj" => ((Singleton.singleton j : Multiset I) + ν)
local notation "δ" => ((Singleton.singleton i : Multiset I) + νj)
local notation "L" => TensorProductAlgebra k Q Λ νj
local notation "R" => TensorProductAlgebra k Q Λ νi
local notation "U" => TensorProductAlgebra k Q Λ δ

omit [DecidableEq I] in
private theorem wt_one (a : I) : μ + {Sum.inl a} = stendhalWeight ℓ (({a} : Multiset I) + ν) := by
  rw [add_comm, stendhalWeight_black_cons]

private theorem proj_unitInc (a : I) :
    projectAt (Q := Q) Λ (wt_one ν a) (Lower.inc S μ (Sum.inl a) 1) = appendBlack Q Λ a ν 1 :=
  (proj_inc Λ a rfl rfl (wt_one ν a) 1).trans
    (congrArg (appendBlack Q Λ a ν) (map_one (projectAt (Q := Q) Λ (ν := ν) rfl)))

omit [DecidableEq I] in
private theorem wt_two : (μ + {c}) + {b} = stendhalWeight ℓ δ := by
  rw [wt_one, wt_one]

omit [DecidableEq I] in
private theorem wt_swap : ({j} : Multiset I) + νi = δ := by ac_rfl

local notation "π" => projectAt (Q := Q) Λ (wt_two (ℓ := ℓ) ν i j)
local notation "p" => appendBlack (k := k) Q Λ i νj
local notation "r" => appendBlackAt (Q := Q) Λ j (wt_swap ν i j)
local notation "sq" => weightSquare μ b c

private theorem proj_top (x : KLRAlgebra k S (μ + {c})) :
    π (concat S (μ + {c}) {b} (x ⊗ₜ[k] 1)) = p (projectAt Λ (wt_one (ℓ := ℓ) ν j) x) :=
  proj_inc Λ i (wt_one ν j) rfl (wt_two ν i j) x

private theorem proj_bot (y : KLRAlgebra k S (μ + {b})) :
    π (botConcat S sq (y ⊗ₜ[k] 1)) = r (projectAt Λ (wt_one (ℓ := ℓ) ν i) y) := by
  rw [botConcat_apply, projectAt_cast]
  exact proj_inc Λ j (wt_one ν i) (wt_swap ν i j) _ y

/-- The signed terminal crossing interchanging the last black colours in the
mixed corner (Webster, arXiv:1309.3796v2, Lemma 4.35). -/
def mixedBlackCrossing : U := π (-ψ (Multiset.card μ))

private theorem proj_tau (hsym : KLRSymm Q) (hij : i ≠ j)
    (x : Lower.Left S μ c) (y : Lower.Right S μ b) :
    π (Lower.tauEquiv S μ b c (affineCoverQ_symm Λ hsym) (Sum.inl_injective.ne hij)
      (BalancedTensor.tmul x y)).val = p (projectAt Λ (wt_one ν j) (x : _)) *
        mixedBlackCrossing Λ ν i j * r (projectAt Λ (wt_one ν i) (y : _)) := by
  rw [Lower.tauEquiv_tmul, map_mul, map_mul, proj_top, proj_bot]
  rfl

/-- Coefficients from the two lower black weights span the entire distinct-colour
restriction–induction corner after imposing all red and violating relations
(Webster, arXiv:1309.3796v2, Lemma 4.35; KL I, Proposition 2.18). -/
theorem mixedBlackCorner_mem_span (hsym : KLRSymm Q) (hij : i ≠ j) (z : U)
    (hz : p 1 * z * r 1 = z) :
    z ∈ Submodule.span k {t | ∃ (x : L) (y : R), x * appendBlack Q Λ j ν 1 = x ∧
      appendBlack Q Λ i ν 1 * y = y ∧ t = p x * mixedBlackCrossing Λ ν i j * r y} := by
  let W := Submodule.span k {t | ∃ (x : L) (y : R), x * appendBlack Q Λ j ν 1 = x ∧
    appendBlack Q Λ i ν 1 * y = y ∧ t = p x * mixedBlackCrossing Λ ν i j * r y}
  have surj : Function.Surjective π := (affineTensorProjection_surjective Λ _).comp (castKLR S _).surjective
  obtain ⟨u, hu⟩ := surj z
  let left := oneConcat S (μ + {c}) {b}
  let right := botOne S sq
  have hl : π left = p 1 := by
    rw [show left = concat S (μ + {c}) {b} (1 ⊗ₜ[k] 1) from (concat_one (Q := S) ..).symm,
      proj_top, map_one]
  have hr : π right = r 1 := by
    rw [show right = botConcat S sq (1 ⊗ₜ[k] 1) from (botConcat_one sq).symm,
      proj_bot, map_one]
  let w : bimod S sq := ⟨left * u * right, (mem_bimod sq).mpr (by
    change left * (left * u * right) * right = _
    have hleft : left * left = left := oneConcat_idem.eq
    have hright : right * right = right := (botOne_idem sq).eq
    calc left * (left * u * right) * right = (left * left) * u * (right * right) := by noncomm_ring
         _ = _ := by rw [hleft, hright])⟩
  have hw : π w.val = z := by change π (left * u * right) = _; rw [map_mul, map_mul, hl, hr, hu, hz]
  let H := Lower.tauEquiv S μ b c (affineCoverQ_symm Λ hsym) (Sum.inl_injective.ne hij)
  obtain ⟨a, ha⟩ := H.surjective w
  rw [← hw, ← ha]
  change π (H a).val ∈ W
  clear ha
  induction a using BalancedTensor.induction_on with
  | zero => rw [map_zero, Submodule.coe_zero, map_zero]; exact W.zero_mem
  | add a d ha hd => rw [map_add, Submodule.coe_add, map_add]; exact W.add_mem ha hd
  | tmul x y =>
    rw [show π (H (BalancedTensor.tmul x y)).val = _ from proj_tau Λ ν i j hsym hij x y]
    refine Submodule.subset_span ⟨_, _, ?_, ?_, rfl⟩
    · have e := congrArg (projectAt (Q := Q) Λ (wt_one ν j)) (CornerTensor.left_mem _ x)
      rw [map_mul, proj_unitInc Λ ν j] at e
      exact e
    · have e := congrArg (projectAt (Q := Q) Λ (wt_one ν i)) (CornerTensor.right_mem _ _ y)
      change projectAt (Q := Q) Λ (wt_one ν i) (Lower.inc S μ b 1 * (y : _)) = _ at e
      rw [map_mul, proj_unitInc Λ ν i] at e
      exact e


local notation "fj" => appendBlack Q Λ j ν
local notation "fi" => appendBlack Q Λ i ν
local notation "PL" => projectAt (Q := Q) Λ (wt_one (ℓ := ℓ) ν j)
local notation "PR" => projectAt (Q := Q) Λ (wt_one (ℓ := ℓ) ν i)
local notation "ML" => CornerTensor.Left fj
local notation "MR" => CornerTensor.Right fi (AlgHom.id k R)
local notation "χ" => mixedBlackCrossing (Q := Q) Λ ν i j

private theorem lift_left (x : ML) : ∃ a : Lower.Left S μ c, PL (a : _) = (x : L) := by
  have surj : Function.Surjective PL := (affineTensorProjection_surjective Λ _).comp (castKLR S _).surjective
  obtain ⟨v, hv⟩ := surj (x : L)
  let g := Lower.inc S μ c
  have hg : g 1 * g 1 = g 1 := by rw [← map_mul, mul_one]
  refine ⟨⟨v * g 1, by change (v * g 1) * g 1 = _; rw [mul_assoc, hg]⟩, ?_⟩
  change PL (v * Lower.inc S μ c 1) = _
  rw [map_mul, hv, proj_unitInc Λ ν j]
  exact CornerTensor.left_mem _ x

private theorem lift_right (y : MR) : ∃ a : Lower.Right S μ b, PR (a : _) = (y : R) := by
  have surj : Function.Surjective PR := (affineTensorProjection_surjective Λ _).comp (castKLR S _).surjective
  obtain ⟨v, hv⟩ := surj (y : R)
  let g := Lower.inc S μ b
  have hg : g 1 * g 1 = g 1 := by rw [← map_mul, mul_one]
  refine ⟨⟨g 1 * v, by change (g 1) * (g 1 * v) = _; rw [← mul_assoc, hg]⟩, ?_⟩
  change PR (Lower.inc S μ b 1 * v) = _
  rw [map_mul, hv, proj_unitInc Λ ν i]
  exact CornerTensor.right_mem _ _ y

private def mixedBil : ML →ₗ[k] MR →ₗ[k] U :=
  LinearMap.mk₂ k (fun x y => p (x : L) * χ * r (y : R))
    (fun x z y => by change p ((x : L) + z) * χ * r (y : R) = _; rw [map_add, add_mul, add_mul])
    (fun a x y => by change p (a • (x : L)) * χ * r (y : R) = _; rw [map_smul, smul_mul_assoc, smul_mul_assoc])
    (fun x y z => by change _ * r ((y : R) + z) = _; rw [map_add, mul_add])
    (fun a x y => by change _ * r (a • (y : R)) = _; rw [map_smul, mul_smul_comm])

private theorem mixedBil_balanced (hsym : KLRSymm Q) (hij : i ≠ j)
    (x : ML) (a : TensorProductAlgebra k Q Λ ν) (y : MR) :
    mixedBil (Q := Q) Λ ν i j (op a • x) y = mixedBil (Q := Q) Λ ν i j x (a • y) := by
  obtain ⟨u, hu⟩ := affineTensorProjection_surjective (Q := Q) Λ ν a
  obtain ⟨t, ht⟩ := lift_left (Q := Q) Λ ν j x
  obtain ⟨v, hv⟩ := lift_right (Q := Q) Λ ν i y
  let F := Lower.tauEquiv S μ b c (affineCoverQ_symm Λ hsym) (Sum.inl_injective.ne hij)
  have h := congrArg (fun z : Lower.Source S μ b c => π (F z).val)
    (BalancedTensor.op_smul_tmul (B := KLRAlgebra k S (μ + {c})) t u v)
  change π (F (BalancedTensor.tmul (op u • t) v)).val = π (F (BalancedTensor.tmul t (u • v))).val at h
  rw [show π (F (BalancedTensor.tmul (op u • t) v)).val = _ from proj_tau Λ ν i j hsym hij _ _,
    show π (F (BalancedTensor.tmul t (u • v))).val = _ from proj_tau Λ ν i j hsym hij _ _] at h
  change p (PL ((t : _) * Lower.inc S μ c u)) * χ * r (PR (v : _)) =
    p (PL (t : _)) * χ * r (PR (Lower.inc S μ b u * (v : _))) at h
  rw [map_mul PL, map_mul PR, proj_inc Λ j rfl rfl (wt_one ν j), proj_inc Λ i rfl rfl (wt_one ν i)] at h
  change p ((PL (t : _)) * fj (affineTensorProjection Λ ν u)) * χ * r (PR (v : _)) =
    p (PL (t : _)) * χ * r (fi (affineTensorProjection Λ ν u) * PR (v : _)) at h
  rw [hu, ht, hv] at h
  exact h

/-- The lower balanced tensor of induction and restriction corners in the
distinct-colour mixed relation (Webster, arXiv:1309.3796v2, Lemma 4.35). -/
abbrev MixedBlackTensor := BalancedTensor k L (TensorProductAlgebra k Q Λ ν) ML MR

/-- The signed terminal crossing acting on the lower balanced tensor lands in
the upper algebra (Webster, arXiv:1309.3796v2, Lemma 4.35). -/
def mixedBlackMap (hsym : KLRSymm Q) (hij : i ≠ j) : MixedBlackTensor (Q := Q) Λ ν i j →ₗ[k] U :=
  BalancedTensor.lift (mixedBil Λ ν i j) (mixedBil_balanced Λ ν i j hsym hij)

/-- The mixed crossing map is onto the rectangular corner selected by the
two terminal black colours, for any ordered set of red strands (Webster,
arXiv:1309.3796v2, Lemma 4.35). -/
theorem exists_mixedBlackMap_eq (hsym : KLRSymm Q) (hij : i ≠ j) (z : U)
    (hz : p 1 * z * r 1 = z) : ∃ t, mixedBlackMap Λ ν i j hsym hij t = z := by
  apply (Submodule.span_le.mpr ?_ : Submodule.span k _ ≤ LinearMap.range (mixedBlackMap Λ ν i j hsym hij))
    (mixedBlackCorner_mem_span Λ ν i j hsym hij z hz)
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact ⟨BalancedTensor.tmul (⟨x, hx⟩ : ML) (⟨y, hy⟩ : MR), rfl⟩

/-- The image of the balanced crossing consists exactly of the upper-weight diagrams
whose terminal black label is `i` on the left and `j` on the right (Webster,
arXiv:1309.3796v2, Lemma 4.35, distinct-colour case). -/
theorem mem_range_mixedBlackMap_iff (hsym : KLRSymm Q) (hij : i ≠ j) (z : U) :
    z ∈ LinearMap.range (mixedBlackMap Λ ν i j hsym hij) ↔ p 1 * z * r 1 = z := by
  refine ⟨?_, exists_mixedBlackMap_eq Λ ν i j hsym hij z⟩
  rintro ⟨t, rfl⟩
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, mul_zero, zero_mul]
  | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
  | tmul x y =>
    change p 1 * (p (x : L) * χ * r (y : R)) * r 1 = _
    calc p 1 * (p (x : L) * χ * r (y : R)) * r 1 = (p 1 * p (x : L)) * χ * (r (y : R) * r 1) := by
           noncomm_ring
         _ = _ := by rw [← map_mul, ← map_mul, one_mul, mul_one]; rfl


section Grading
open KLRAlgebra.AbsentColour QuantumGroup
variable {F : Type*} [Field F] {S' : I → I → MvPolynomial (Fin 2) F}
    (C : CartanDatum I) (hQ : IsRouquierQ C S')
local notation "di" => fun a => C.dot a a / 2
local notation "H" => affineCoverGrading Λ hQ.gradingDatum di (dotDegree C hQ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum di (dotDegree C hQ)

private theorem proj_cL (a : I) {γ : Multiset (I ⊕ Fin ℓ)} {α β : Multiset I}
    (h : γ = stendhalWeight ℓ α) (hb : ({a} : Multiset I) + α = β)
    (hh : {Sum.inl a} + γ = stendhalWeight ℓ β) (z : KLRAlgebra k S γ) :
    projectAt Λ hh (cL S (Sum.inl a) γ z) = appendBlackAt Λ a hb (projectAt Λ h z) := by
  rw [cL_eq_cast]
  have hcast {γγ δδ : Multiset (I ⊕ Fin ℓ)} (e : γγ = δδ) (f : δδ = stendhalWeight ℓ β)
      (u : KLRAlgebra k S γγ) : projectAt Λ f (castKLR S e u) = projectAt Λ (e.trans f) u := by subst δδ; rfl
  rw [hcast]
  exact proj_inc Λ a h hb _ z

private theorem affine_signed_mem {J : Type*} [DecidableEq J] {q : J → J → MvPolynomial (Fin 2) k}
    (D : GradingDatum q) (γ : Multiset J) (a t' : J) :
    MixedCrossing.crossingElement q γ a t' ∈ D.grade ({a} + ({t'} + γ)) (D.degΨ a t') := by
  rw [MixedCrossing.crossingElement, neg_mul]
  apply Submodule.neg_mem
  rw [← sum_e (k := k) (Q := q) (ν := γ), map_sum, map_sum, Finset.mul_sum]
  apply Submodule.sum_mem
  intro s _
  change ψ _ * castKLR q _ (cL q t' _ (cL q a γ (e s))) ∈ _
  rw [cL_e, cL_e, castKLR_e]
  let h := MixedCrossing.square γ a t'
  let v := Seq.cast h (MixedCrossing.doubleSeq γ t' a s)
  have h₁ : v.lbl ⟨γ.card, by simp⟩ = a := MixedCrossing.doubleSeq_apply_mid γ t' a s _ rfl
  have h₂ : v.lbl ⟨γ.card + 1, by simp⟩ = t' := MixedCrossing.doubleSeq_apply_last γ t' a s _ rfl
  change ψ γ.card * e v ∈ D.grade _ (D.degΨ a t')
  simpa only [h₁, h₂] using D.ψ_mul_e_mem_grade (j := γ.card) (by simp) v

private theorem mixed_cut_mem :
    mixedBlackCrossing (Q := S') Λ ν i j *
      appendBlackAt (Q := S') Λ j (wt_swap ν i j) (appendBlack S' Λ i ν 1) ∈
      tensorProductGrade G δ (- C.dot i j) := by
  let sq' := MixedCrossing.square μ b c
  have hw : {b} + ({c} + μ) = stendhalWeight ℓ δ := by rw [stendhalWeight_black_cons, stendhalWeight_black_cons]
  let proj := projectAt (Q := S') Λ hw
  have hz := projection_graded Λ C hQ δ ((H).castKLR_mem_grade hw (affine_signed_mem H μ b c))
  change proj (MixedCrossing.crossingElement (affineCoverQ S' Λ) μ b c) ∈
    tensorProductGrade G δ (- C.dot i j) at hz
  rw [MixedCrossing.crossingElement, map_mul] at hz
  have hψ : proj (-ψ (Multiset.card μ)) = mixedBlackCrossing Λ ν i j := by
    change affineTensorProjection Λ δ (castKLR (affineCoverQ S' Λ) _ (-ψ _) ) =
      affineTensorProjection Λ δ (castKLR (affineCoverQ S' Λ) _ (-ψ _))
    simp only [map_neg, castKLR_ψ]
  rw [hψ] at hz
  have hc {α β : Multiset (I ⊕ Fin ℓ)} (e : α = β) (f : β = stendhalWeight ℓ δ)
      (z : KLRAlgebra F (affineCoverQ S' Λ) α) :
      projectAt Λ f (castKLR (affineCoverQ S' Λ) e z) = projectAt Λ (e.trans f) z := by subst β; rfl
  change _ * projectAt Λ hw (castKLR (affineCoverQ S' Λ) sq'
    (cL (affineCoverQ S' Λ) c _ (cL (affineCoverQ S' Λ) b μ 1))) ∈ _ at hz
  rw [hc, proj_cL Λ j (stendhalWeight_black_cons (ℓ := ℓ) i ν) (wt_swap ν i j),
    proj_cL Λ i rfl rfl, map_one (projectAt (Q := S') Λ (ν := ν) rfl)] at hz
  exact hz

/-- The mixed crossing applied to homogeneous coefficient diagrams has degree
`-i·j` before normalizing restriction (Webster, arXiv:1309.3796v2, Lemma 4.35). -/
theorem mixedBlackMap_tmul_mem_grade (hij : i ≠ j)
    (x : CornerTensor.Left (appendBlack S' Λ j ν))
    (y : CornerTensor.Right (appendBlack S' Λ i ν) (AlgHom.id F _))
    {d f : ℤ} (hx : (x : TensorProductAlgebra F S' Λ νj) ∈ tensorProductGrade G νj d)
    (hy : (y : TensorProductAlgebra F S' Λ νi) ∈ tensorProductGrade G νi f) :
    mixedBlackMap Λ ν i j (fun a a' hab => (hQ.symm a a' hab).symm) hij (BalancedTensor.tmul x y) ∈
      tensorProductGrade G δ (d + (- C.dot i j) + f) := by
  let top := appendBlack S' Λ i νj
  let bot := appendBlackAt (Q := S') Λ j (wt_swap ν i j)
  let cut := appendBlack S' Λ i ν 1
  let cross := mixedBlackCrossing (Q := S') Λ ν i j
  have hcut : cut * (y : _) = y := CornerTensor.right_mem _ _ y
  have hh : top (x : _) * cross * bot (y : _) = top (x : _) * (cross * bot cut) * bot (y : _) := by
    rw [mul_assoc (top (x : _)) (cross * _), mul_assoc cross, ← map_mul, hcut, mul_assoc]
  change top (x : _) * cross * bot (y : _) ∈ _
  rw [hh]
  apply SetLike.GradedMul.mul_mem (A := tensorProductGrade G δ)
    (SetLike.GradedMul.mul_mem (A := tensorProductGrade G δ) (appendBlack_mem_grade S' Λ i νj G hx)
      (mixed_cut_mem Λ ν i j C hQ))
  have hg {α β : Multiset I} (h : ({j} : Multiset I) + α = β) {u : TensorProductAlgebra F S' Λ α}
      (hu : u ∈ tensorProductGrade G α f) :
      appendBlackAt Λ j h u ∈ tensorProductGrade G β f := by
    subst β
    exact appendBlack_mem_grade S' Λ j α G hu
  exact hg _ hy

end Grading

end Categorification.Stendhal
