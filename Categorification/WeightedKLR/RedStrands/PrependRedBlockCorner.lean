/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedBlockInjective
import Categorification.WeightedKLR.RedStrands.PrependRedInjective
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
import Categorification.WeightedKLR.RedStrands.BraidedStendhal
import Categorification.KLR.CyclotomicSplit

/-!
# The block algebra fills the corner `S_α e_α`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.26, for root functions with `α(0) ≠ 0`: every element of `S_α e_α` is `β · [e_α]`
for an element `β` of the block algebra of Proposition 5.3.

## Main results

* `Graded.isHomogeneousSubspace_span_of_homogeneous`.
* `StendhalAlgebra.val_blockHom_mem_stendhalGrade`: the block maps preserve degrees.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Graded

open DirectSum

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]

/-- The span of a set of homogeneous elements is a homogeneous subspace. -/
theorem isHomogeneousSubspace_span_of_homogeneous {s : Set A} (hs : ∀ x ∈ s, ∃ n, x ∈ 𝒜 n) :
    IsHomogeneousSubspace 𝒜 (Submodule.span k s) := by
  classical
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hs x hx
    by_cases h : m = n
    · subst h
      rw [decompose_of_mem_same _ hm]
      exact Submodule.subset_span hx
    · rw [decompose_of_mem_ne _ hm h]
      exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]
    exact Submodule.smul_mem _ c hx

end Categorification.Graded

namespace Categorification.KLR.KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

/-- The KLR algebra of the zero weight consists of scalars. -/
theorem exists_eq_algebraMap_of_zero (a : KLRAlgebra k Q 0) : ∃ c : k, a = algebraMap k _ c := by
  induction a using klr_induction with
  | hadd u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c + d, (map_add _ c d).symm⟩
  | hmul u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c * d, (map_mul _ c d).symm⟩
  | hr r => exact ⟨r, rfl⟩
  | he s =>
    refine ⟨1, ?_⟩
    rw [map_one, ← sum_e, Finset.sum_eq_single s (fun b _ hb => (hb (Subsingleton.elim _ _)).elim)
      (fun h => (h (Finset.mem_univ _)).elim)]
  | hx b => exact b.elim0
  | hψ j => exact ⟨0, by rw [map_zero]; exact ψ_eq_zero j (by simp)⟩

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra StendhalAlgebra MulOpposite DirectSum Categorification.Graded

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section BlackGrading

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ}

/-- The restriction of a grading of `T̃^λ` to the black labels. -/
def stendhalBlackGrading (G : GradingDatum (stendhalQ Q Λ)) : GradingDatum Q where
  degX i := G.degX (.inl i)
  degΨ i j := G.degΨ (.inl i) (.inl j)
  degΨ_self i := G.degΨ_self (.inl i)
  isWeightedHomogeneous i j hij :=
    G.isWeightedHomogeneous (.inl i) (.inl j) (fun he => hij (Sum.inl_injective he))

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- **The block maps preserve degrees**: for a grading of `T̃^λ`, the block map of `b_j`
sends homogeneous diagrams of the black restriction to homogeneous elements of the same
degree. -/
theorem val_blockHom_mem_stendhalGrade (G : GradingDatum (stendhalQ Q Λ)) {ν : Multiset I}
    {b : Fin (ℓ + 1) → Multiset I} (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1)
    {a : KLRAlgebra k Q (b ⟨j, hj⟩)} {d : ℤ} (ha : a ∈ (stendhalBlackGrading G).grade _ d) :
    (blockHom Q Λ hb j hj a).val ∈ stendhalGrade G ν d := by
  change (blockHom Q Λ hb j hj a).val.val ∈ allOrdersGrade G ν d
  rw [val_val_blockHom]
  apply Graded.mem_map_of_mem
  exact (blockEmb hb j hj).valHom_mem_grade G
    (SingleRed.reindex_mem_grade _ Sum.inl_injective G (stendhalBlackGrading G)
      (fun _ => rfl) (fun _ _ => rfl) ha)

end BlackGrading

section BlockSpan

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}
  (G : GradingDatum (stendhalQ Q Λ)) (hb : blockPrefix b (ℓ + 1) = ν)

local notation "T̃" => StendhalAlgebra k Q Λ ν
local notation "eα" => (rootIdem Q Λ (blockRoot b) : T̃)

/-- The images of homogeneous diagrams under the block maps. -/
def blockGens : Set T̃ :=
  {x | ∃ (j : ℕ) (hj : j < ℓ + 1) (d : ℤ) (a : KLRAlgebra k Q (b ⟨j, hj⟩)),
    a ∈ (stendhalBlackGrading G).grade _ d ∧ x = (blockHom Q Λ hb j hj a).val}

/-- The span of the products of block diagrams, cut by `e_α`. -/
def blockSpan : Submodule k T̃ :=
  Submodule.span k ((· * eα) '' Submonoid.closure (blockGens G hb))

theorem rootIdem_mem_stendhalGrade (α : Fin ℓ → I → ℕ) :
    (rootIdem Q Λ α : T̃) ∈ stendhalGrade G ν 0 := by
  change (∑ s ∈ rootSet ν α, StendhalAlgebraAllOrders.e s) ∈ allOrdersGrade G ν 0
  exact Submodule.sum_mem _ fun s _ => Graded.mem_map_of_mem _
    (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).toLinearMap (G.e_mem_grade s)

theorem blockGens_corner {x : T̃} (hx : x ∈ blockGens G hb) : eα * x = x ∧ x * eα = x := by
  obtain ⟨j, hj, d, a, -, rfl⟩ := hx
  exact (Subsemigroup.mem_corner_iff (isIdempotentElem_rootIdem _)).1 (blockHom Q Λ hb j hj a).2

theorem rootIdem_mul_comm_of_mem_closure {x : T̃} (hx : x ∈ Submonoid.closure (blockGens G hb)) :
    eα * x = x * eα := by
  induction hx using Submonoid.closure_induction with
  | mem x hx => rw [(blockGens_corner G hb hx).1, (blockGens_corner G hb hx).2]
  | one => rw [mul_one, one_mul]
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]

theorem homogeneous_of_mem_closure {x : T̃} (hx : x ∈ Submonoid.closure (blockGens G hb)) :
    ∃ n, x ∈ stendhalGrade G ν n := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, d, a, ha, rfl⟩ := hx
    exact ⟨d, val_blockHom_mem_stendhalGrade G hb j hj ha⟩
  | one => exact ⟨0, SetLike.GradedOne.one_mem⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, SetLike.GradedMul.mul_mem hm hn⟩

/-- The block span is a homogeneous subspace. -/
theorem isHomogeneousSubspace_blockSpan :
    IsHomogeneousSubspace (stendhalGrade G ν) (blockSpan G hb) := by
  refine isHomogeneousSubspace_span_of_homogeneous _ ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨n, hn⟩ := homogeneous_of_mem_closure G hb hx
  exact ⟨n + 0, SetLike.GradedMul.mul_mem hn (rootIdem_mem_stendhalGrade G _)⟩

theorem rootIdem_mem_blockSpan : eα ∈ blockSpan G hb :=
  Submodule.subset_span ⟨1, Submonoid.one_mem _, one_mul _⟩

theorem mul_mem_blockSpan {x y : T̃} (hx : x ∈ blockSpan G hb) (hy : y ∈ blockSpan G hb) :
    x * y ∈ blockSpan G hb := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      refine Submodule.subset_span ⟨x * y, Submonoid.mul_mem _ hx hy, ?_⟩
      change x * y * eα = x * eα * (y * eα)
      rw [← mul_assoc (x * eα) y eα, mul_assoc x eα y, rootIdem_mul_comm_of_mem_closure G hb hy,
        ← mul_assoc x y eα, mul_assoc (x * y) eα eα, (isIdempotentElem_rootIdem _).eq]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem rootIdem_mul_of_mem_blockSpan {x : T̃} (hx : x ∈ blockSpan G hb) : eα * x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    change eα * (x * eα) = x * eα
    rw [← mul_assoc, rootIdem_mul_comm_of_mem_closure G hb hx, mul_assoc,
      (isIdempotentElem_rootIdem _).eq]
  | zero => rw [mul_zero]
  | add x y _ _ h h' => rw [mul_add, h, h']
  | smul c x _ h => rw [mul_smul_comm, h]

theorem mul_rootIdem_of_mem_blockSpan {x : T̃} (hx : x ∈ blockSpan G hb) : x * eα = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    change x * eα * eα = x * eα
    rw [mul_assoc, (isIdempotentElem_rootIdem _).eq]
  | zero => rw [zero_mul]
  | add x y _ _ h h' => rw [add_mul, h, h']
  | smul c x _ h => rw [smul_mul_assoc, h]

/-- Every block diagram lies in the block span. -/
theorem val_blockHom_mem_blockSpan (j : ℕ) (hj : j < ℓ + 1) (a : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    (blockHom Q Λ hb j hj a).val ∈ blockSpan G hb := by
  classical
  rw [← sum_support_decompose ((stendhalBlackGrading G).grade (b ⟨j, hj⟩)) a, map_sum]
  change (KLR.cornerVal _) (∑ d ∈ _, _) ∈ _
  rw [map_sum]
  refine Submodule.sum_mem _ fun d _ => ?_
  have hg : (blockHom Q Λ hb j hj (decompose ((stendhalBlackGrading G).grade _) a d)).val ∈
      blockGens G hb := ⟨j, hj, d, _, (decompose _ a d).2, rfl⟩
  refine Submodule.subset_span ⟨_, Submonoid.subset_closure hg, ?_⟩
  exact (blockGens_corner G hb hg).2

end BlockSpan

section BlockSpanAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}
  (G : GradingDatum (stendhalQ Q Λ)) (hb : blockPrefix b (ℓ + 1) = ν)

local notation "T̃" => StendhalAlgebra k Q Λ ν
local notation "eα" => (rootIdem Q Λ (blockRoot b) : T̃)

/-- Each block diagram acts through the block algebra. -/
theorem exists_blockAction_eq_rootBlockAction (j : ℕ) (hj : j < ℓ + 1)
    (a : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    ∃ β, blockAction Q Λ hb β = rootBlockAction Q Λ hb j hj a := by
  cases j with
  | zero => exact ⟨a ⊗ₜ 1, blockAction_tmul_one hb a⟩
  | succ r =>
    exact ⟨1 ⊗ₜ PiTensorProduct.singleAlgHom ⟨r, by omega⟩ (CycKLR.mk k Q _ _ a),
      blockAction_one_tmul_single hb ⟨r, by omega⟩ a⟩

theorem exists_blockAction_mk_of_mem_closure {x : T̃}
    (hx : x ∈ Submonoid.closure (blockGens G hb)) :
    ∃ β, ∀ (z : T̃) (hz : eα * z = z),
      (blockAction Q Λ hb β (rootStandardMk Q Λ _ z hz)).1 = Submodule.Quotient.mk (x * z) := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, d, a, -, rfl⟩ := hx
    obtain ⟨β, hβ⟩ := exists_blockAction_eq_rootBlockAction hb j hj a
    exact ⟨β, fun z hz => by rw [hβ, rootBlockAction_apply]; rfl⟩
  | one => exact ⟨1, fun z hz => by rw [map_one, one_mul]; rfl⟩
  | mul x y hx' hy' hx hy =>
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', hβ'⟩ := hy
    refine ⟨β * β', fun z hz => ?_⟩
    have hyz : eα * (y * z) = y * z := by
      rw [← mul_assoc, rootIdem_mul_comm_of_mem_closure G hb hy', mul_assoc, hz]
    have h1 : blockAction Q Λ hb β' (rootStandardMk Q Λ _ z hz) =
        rootStandardMk Q Λ _ (y * z) hyz := Subtype.ext (hβ' z hz)
    rw [map_mul, Module.End.mul_apply, h1, hβ, mul_assoc]

/-- **The block span acts through the block algebra**: left multiplication on `S_α` by an
element of the corner lying in the block span is the action of an element of the block
algebra of Proposition 5.3. -/
theorem exists_blockAction_eq_rootAction
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot b)).Corner)
    (hc : c.val ∈ blockSpan G hb) :
    ∃ β, blockAction Q Λ hb β = rootAction Q Λ (blockRoot b) c := by
  have key : ∀ x ∈ blockSpan G hb, ∃ β, ∀ (z : T̃) (hz : eα * z = z),
      (blockAction Q Λ hb β (rootStandardMk Q Λ _ z hz)).1 = Submodule.Quotient.mk (x * z) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨β, hβ⟩ := exists_blockAction_mk_of_mem_closure G hb hx
      exact ⟨β, fun z hz => by rw [hβ z hz, mul_assoc, hz]⟩
    | zero => exact ⟨0, fun z hz => by rw [map_zero, zero_mul]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨β, hβ⟩ := hx
      obtain ⟨β', hβ'⟩ := hy
      exact ⟨β + β', fun z hz => by
        rw [map_add, LinearMap.add_apply, Submodule.coe_add, hβ z hz, hβ' z hz, add_mul,
          Submodule.Quotient.mk_add]⟩
    | smul r x _ hx =>
      obtain ⟨β, hβ⟩ := hx
      exact ⟨r • β, fun z hz => by
        rw [smul_mul_assoc, Submodule.Quotient.mk_smul, ← hβ z hz, map_smul]
        rfl⟩
  obtain ⟨β, hβ⟩ := key _ hc
  refine ⟨β, sub_eq_zero.1 (eq_zero_of_apply_rootStandardUnit _ _ ?_)⟩
  rw [LinearMap.sub_apply, sub_eq_zero]
  apply Subtype.ext
  unfold rootStandardUnit
  rw [rootAction_mk]
  exact (hβ _ _).trans rfl

include G hb in
/-- The elements of the corner `e_α T̃^λ e_α` lying in the block span. -/
def blockSpanCorner :
    Subalgebra k (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot b)).Corner where
  carrier := {c | c.val ∈ blockSpan G hb}
  mul_mem' hx hy := mul_mem_blockSpan G hb hx hy
  add_mem' hx hy := Submodule.add_mem (blockSpan G hb) hx hy
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    show (r • (1 : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν)
      (blockRoot b)).Corner)).val ∈ blockSpan G hb
    exact Submodule.smul_mem _ r (rootIdem_mem_blockSpan G hb)

/-- **Every element of the block algebra acts by an element of the block span.** -/
theorem exists_rootAction_eq_blockAction (β : BlockAlgebra k Q Λ b) :
    ∃ c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot b)).Corner,
      c.val ∈ blockSpan G hb ∧ blockAction Q Λ hb β = rootAction Q Λ (blockRoot b) c := by
  let P := ((blockSpanCorner G hb).map (rootAction (ν := ν) Q Λ (blockRoot b))).comap
    (blockAction (b := b) Q Λ hb)
  have hP : P = ⊤ := by
    refine PiTensorProduct.tensor_subalgebra_eq_top P (fun a => ?_) (fun r c => ?_)
    · exact ⟨blockHom Q Λ hb 0 (Nat.succ_pos ℓ) a, val_blockHom_mem_blockSpan G hb 0 _ a,
        ((blockAction_tmul_one hb a).trans (rootBlockAction_apply hb 0 _ a)).symm⟩
    · obtain ⟨u, rfl⟩ := CycKLR.mk_surjective c
      exact ⟨blockHom Q Λ hb (r.val + 1) (Nat.succ_lt_succ r.2) u,
        val_blockHom_mem_blockSpan G hb _ _ u,
        ((blockAction_one_tmul_single hb r u).trans (rootBlockAction_apply hb _ _ u)).symm⟩
  obtain ⟨c, hc, h⟩ := (hP ▸ Algebra.mem_top : β ∈ P)
  exact ⟨c, hc, h.symm⟩

end BlockSpanAction

end Categorification.Stendhal
