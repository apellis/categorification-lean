/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedBlockInjective
import Categorification.WeightedKLR.RedStrands.PrependRedInjective
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
import Categorification.WeightedKLR.RedStrands.BraidedStendhal
import Categorification.KLR.CyclotomicSplit
import Categorification.WeightedKLR.RedStrands.TildeLayerIso

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


section ZeroAction

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- An element of the corner acting by zero on `S_α` lies in `U_α`. -/
theorem val_mem_rootUpper_of_rootAction_eq_zero (α : Fin ℓ → I → ℕ)
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α).Corner)
    (hc : rootAction Q Λ α c = 0) : c.val ∈ rootUpper (ν := ν) Q Λ α := by
  have h := congrArg Subtype.val (LinearMap.congr_fun hc (rootStandardUnit Q Λ ν α))
  change Submodule.Quotient.mk (c.val * rootIdem Q Λ α) =
    (0 : StendhalAlgebra k Q Λ ν ⧸ rootUpper (ν := ν) Q Λ α) at h
  rw [Submodule.Quotient.mk_eq_zero, KLR.Corner.val_mul_E] at h
  exact h

/-- **Proposition 5.26 for `b_0 = 0`, in right-module form**: every element of the corner acts
on `S_α` through the block algebra. -/
theorem exists_blockAction_eq_rootAction_of_zero (hQ : KLRSymm Q) {n : ℕ} (hn : 0 < n)
    (Λ : Fin n → I →₀ ℕ) {b : Fin (n + 1) → Multiset I} {ν : Multiset I}
    (hb : blockPrefix b (n + 1) = ν) (hb0 : b 0 = 0)
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot b)).Corner) :
    ∃ β, blockAction Q Λ hb β = rootAction Q Λ (blockRoot b) c := by
  subst hb
  have hα : RootNonViolated (ν := blockPrefix b (n + 1)) (blockRoot b) :=
    rootNonViolated_blockRoot hn hb0
  obtain ⟨β, hβ⟩ := (bijective_leftBlockActionOf Q Λ b hα hQ hb0).2
    (rootReflectConj Q Λ hα (rootAction Q Λ (blockRoot b) c))
  refine ⟨β, LinearMap.ext fun v => (rootReflectEquiv Q Λ hα).injective ?_⟩
  have h := LinearMap.congr_fun hβ (rootReflectEquiv Q Λ hα v)
  rw [leftBlockActionOf, AlgHom.comp_apply, rootReflectConj_apply, rootReflectConj_apply] at h
  exact h

end ZeroAction

section Lift

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}
  (G : GradingDatum (stendhalQ Q Λ)) (hb : blockPrefix b (ℓ + 1) = ν)

local notation "T̃" => StendhalAlgebra k Q Λ ν
local notation "T̃₀" => StendhalAlgebra k Q (Λ ∘ Fin.succ) ν
local notation "φ" => prependRedStendhal Q Λ ν
local notation "G₀" => restrictFirstRedGrading Q Λ G
local notation "e'" => (rootIdem Q Λ (blockRoot (consBlocks b)) : T̃)
local notation "eα" => (rootIdem Q (Λ ∘ Fin.succ) (blockRoot b) : T̃₀)

omit [DecidableEq I] in
theorem rootIdem_consBlocks [DecidableEq I] : e' = φ eα :=
  (prependRedStendhal_rootIdem_of_eq (blockRoot_consBlocks b)).symm

theorem exists_prependRed_eq_of_mem_closure {y : T̃}
    (hy : y ∈ Submonoid.closure (blockGens G (blockPrefix_consBlocks_eq b hb))) :
    ∃ x ∈ blockSpan G₀ hb, φ x = y * e' := by
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
    have hg := (blockGens_corner G (blockPrefix_consBlocks_eq b hb) hy).2
    rw [hg]
    obtain ⟨j, hj, d, a, -, rfl⟩ := hy
    cases j with
    | zero =>
      obtain ⟨c, hc⟩ := KLRAlgebra.exists_eq_algebraMap_of_zero (Q := Q) (k := k) a
      have ha : a = algebraMap k (KLRAlgebra k Q (consBlocks b ⟨0, hj⟩)) c := hc
      rw [ha]
      refine ⟨c • eα, Submodule.smul_mem _ c (rootIdem_mem_blockSpan G₀ hb), ?_⟩
      rw [map_smul, ← rootIdem_consBlocks, Algebra.smul_def]
      exact (congrArg Subtype.val
        (algHom_commutes_of _ _ (blockHom Q Λ (blockPrefix_consBlocks_eq b hb) 0 hj) c)).symm
    | succ j =>
      refine ⟨(blockHom Q (Λ ∘ Fin.succ) hb j (Nat.lt_of_succ_lt_succ hj) a).val,
        val_blockHom_mem_blockSpan G₀ hb _ _ a, Subtype.ext ?_⟩
      exact ((prependBlockVal_apply b hb j _ a).symm.trans
        ((prependBlockVal_eq b hb j _ a).trans (consBlockVal_apply b hb j _ a)))
  | one => exact ⟨eα, rootIdem_mem_blockSpan G₀ hb, by rw [one_mul, rootIdem_consBlocks]⟩
  | mul y z _ hz' hy hz =>
    obtain ⟨x, hx, h⟩ := hy
    obtain ⟨x', hx', h'⟩ := hz
    refine ⟨x * x', mul_mem_blockSpan G₀ hb hx hx', ?_⟩
    have hc := rootIdem_mul_comm_of_mem_closure G (blockPrefix_consBlocks_eq b hb) hz'
    rw [map_mul, h, h', mul_assoc y, ← mul_assoc e' z e', hc, mul_assoc z,
      (isIdempotentElem_rootIdem _).eq, mul_assoc]

/-- **The block span lifts along adding the red strand**: every element of the block span for
the blocks `0, b_0, …, b_ℓ` is the image of an element of the block span for `b`. -/
theorem exists_prependRed_eq_of_mem_blockSpan {y : T̃}
    (hy : y ∈ blockSpan G (blockPrefix_consBlocks_eq b hb)) :
    ∃ x ∈ blockSpan G₀ hb, φ x = y := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    exact exists_prependRed_eq_of_mem_closure G hb hy
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, hx, h⟩ := hy
    obtain ⟨x', hx', h'⟩ := hz
    exact ⟨x + x', add_mem hx hx', by rw [map_add, h, h']⟩
  | smul r y _ hy =>
    obtain ⟨x, hx, h⟩ := hy
    exact ⟨r • x, Submodule.smul_mem _ r hx, by rw [map_smul, h]⟩

theorem prependRed_val_mem_corner
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) (blockRoot b)).Corner) :
    e' * φ c.val * e' = φ c.val := by
  rw [rootIdem_consBlocks, ← map_mul, ← map_mul, KLR.Corner.E_mul_val, KLR.Corner.val_mul_E]

/-- **The homogeneous case of the surjectivity in Proposition 5.26** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.26): if the grading of all red orders vanishes below
`-c₀` and `⟨α_i^∨, λ₀⟩ deg x_i > n + 2c₀` for every black label `i`, every element of degree
`n` of the corner `e_α T̃^λ e_α` acts on `S_α` through the block algebra. -/
theorem exists_blockAction_eq_rootAction_of_mem_grade (hQ : KLRSymm Q) {c₀ n : ℤ}
    (hc₀ : ∀ m < -c₀, allOrdersGrade G₀ ν m = ⊥)
    (hΛ : ∀ i ∈ ν, n + 2 * c₀ < Λ 0 i * G.degX (.inl i))
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) (blockRoot b)).Corner)
    (hcn : c.val ∈ stendhalGrade G₀ ν n) :
    ∃ β, blockAction Q (Λ ∘ Fin.succ) hb β = rootAction Q (Λ ∘ Fin.succ) (blockRoot b) c := by
  classical
  have hb' := blockPrefix_consBlocks_eq b hb
  let c' : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν)
      (blockRoot (consBlocks b))).Corner := KLR.Corner.mk (φ c.val) (prependRed_val_mem_corner c)
  obtain ⟨β', hβ'⟩ := exists_blockAction_eq_rootAction_of_zero hQ (Nat.succ_pos ℓ) Λ hb'
    (consBlocks_zero b) c'
  obtain ⟨w', hw', hβw'⟩ := exists_rootAction_eq_blockAction G hb' β'
  obtain ⟨x, hx, hxw⟩ := exists_prependRed_eq_of_mem_blockSpan G hb hw'
  have hU' : φ (c.val - x) ∈ rootUpper Q Λ (blockRoot (consBlocks b)) := by
    have h0 : rootAction Q Λ (blockRoot (consBlocks b)) (c' - w') = 0 := by
      rw [map_sub, ← hβ', hβw', sub_self]
    have h1 := val_mem_rootUpper_of_rootAction_eq_zero _ _ h0
    rwa [KLR.Corner.val_sub, KLR.Corner.val_mk, ← hxw, ← map_sub] at h1
  generalize hyc : (c.1 : T̃₀) = y at hU' hcn
  let φL : T̃₀ →ₗ[k] T̃ :=
    { toFun := φ, map_add' := map_add φ, map_smul' := map_smul φ }
  have hgr : PreservesGrading (stendhalGrade G₀ ν) (stendhalGrade G ν) φL :=
    fun _ _ hz => prependRedStendhal_mem_grade Q Λ ν G hz
  let xn : T̃₀ := decompose (stendhalGrade G₀ ν) x n
  have hxn : xn ∈ blockSpan G₀ hb := isHomogeneousSubspace_blockSpan G₀ hb n x hx
  have hcxn : y - xn ∈ stendhalGrade G₀ ν n :=
    sub_mem hcn (decompose (stendhalGrade G₀ ν) x n).2
  have hdc : (decompose (stendhalGrade G₀ ν) (y - x) n : T̃₀) = y - xn := by
    have h1 := decompose_of_mem_same (stendhalGrade G₀ ν) hcn
    have h2 := map_sub (GradedRing.proj (stendhalGrade G₀ ν) n) y x
    simp only [GradedRing.proj_apply] at h2
    rw [h2, h1]
  have hU'n : φ (y - xn) ∈ rootUpper Q Λ (blockRoot (consBlocks b)) := by
    have h := isHomogeneousSubspace_rootUpper Q ν G (blockRoot (consBlocks b)) n _ hU'
    have h2 := decompose_map hgr (y - x) n
    change (decompose (stendhalGrade G ν) (φ (y - x)) n : T̃) = φ _ at h2
    rw [h2, hdc] at h
    exact h
  rw [blockRoot_consBlocks] at hU'n
  have hU := mem_rootUpper_of_prependRedStendhal_mem Q Λ ν G hc₀ hΛ (blockRoot b) hcxn hU'n
  let w : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ ∘ Fin.succ) (ν := ν) (blockRoot b)).Corner :=
    KLR.Corner.mk xn (by
      rw [rootIdem_mul_of_mem_blockSpan G₀ hb hxn, mul_rootIdem_of_mem_blockSpan G₀ hb hxn])
  obtain ⟨β, hβ⟩ := exists_blockAction_eq_rootAction G₀ hb w hxn
  refine ⟨β, hβ.trans ?_⟩
  have h0 : rootAction Q (Λ ∘ Fin.succ) (blockRoot b) (w - c) = 0 := by
    refine rootAction_eq_zero_of_mul_mem _ _ ?_
    rw [KLR.Corner.val_mul_E, KLR.Corner.val_sub, KLR.Corner.val_mk]
    change xn - c.1 ∈ _
    rw [hyc, ← neg_sub]
    exact neg_mem hU
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Lift


section Surjective

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {ℓ : ℕ} {Λ₀ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}

/-- **The corner acts through the block algebra** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.26, any first block `b_0`): for symmetric `Q` and a grading of `T̃^λ` in which
dots have positive degree, every element of `e_α T̃^λ e_α` acts on `S_α` as an element of the
block algebra `R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` of Proposition 5.3. A homogeneous
element is compared with its image after adding a red strand `λ₀` on the left, large in its
degree, where the first block is empty. -/
theorem exists_blockAction_eq_rootAction_of_grading (hQ : KLRSymm Q)
    (G' : GradingDatum (stendhalQ Q Λ₀)) (hG' : ∀ a, 0 < G'.degX a)
    (hb : blockPrefix b (ℓ + 1) = ν)
    (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ₀) (ν := ν) (blockRoot b)).Corner) :
    ∃ β, blockAction Q Λ₀ hb β = rootAction Q Λ₀ (blockRoot b) c := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_allOrdersGrade_eq_bot G' ν (stendhalQ_symm Q Λ₀ hQ) hG'
  have hhom : ∀ (n : ℤ)
      (c : (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ₀) (ν := ν) (blockRoot b)).Corner),
      c.1 ∈ stendhalGrade G' ν n → ∃ β, blockAction Q Λ₀ hb β = rootAction Q Λ₀ (blockRoot b) c := by
    intro n c hcn
    let N : ℕ := (n + 2 * c₀).toNat + 1
    let l0 : I →₀ ℕ := N • Multiset.toFinsupp ν
    have hres := restrict_extGrading Q Λ₀ l0 G'
    have hΛ : ∀ i ∈ ν, n + 2 * c₀ < ((Fin.cons l0 Λ₀ : Fin (ℓ + 1) → I →₀ ℕ) 0 i : ℤ) *
        (extGrading Q Λ₀ l0 G').degX (.inl i) := by
      intro i hi
      have h1 : N ≤ l0 i := by
        change N ≤ N * Multiset.count i ν
        exact Nat.le_mul_of_pos_right N (Multiset.count_pos.2 hi)
      have h2 : 1 ≤ G'.degX (.inl i) := hG' _
      change n + 2 * c₀ < (l0 i : ℤ) * G'.degX (.inl i)
      have h3 : (N : ℤ) ≤ l0 i := by exact_mod_cast h1
      have h4 : (l0 i : ℤ) ≤ l0 i * G'.degX (.inl i) :=
        le_mul_of_one_le_right (Int.natCast_nonneg _) h2
      have h5 : (N : ℤ) = ((n + 2 * c₀).toNat : ℤ) + 1 := by simp [N]
      omega
    exact exists_blockAction_eq_rootAction_of_mem_grade (Λ := Fin.cons l0 Λ₀)
      (extGrading Q Λ₀ l0 G') hb hQ (hres ▸ hc₀) hΛ c (hres ▸ hcn)
  have hE := rootIdem_mem_stendhalGrade (ν := ν) G' (blockRoot b)
  have hce : (rootIdem (ν := ν) Q Λ₀ (blockRoot b)) * c.1 *
      rootIdem (ν := ν) Q Λ₀ (blockRoot b) = c.1 := by
    have h1 : (rootIdem (ν := ν) Q Λ₀ (blockRoot b)) * c.1 = c.1 :=
      KLR.Corner.E_mul_val c
    have h2 : c.1 * (rootIdem (ν := ν) Q Λ₀ (blockRoot b)) = c.1 :=
      KLR.Corner.val_mul_E c
    rw [h1, h2]
  have hmem : ∀ n : ℤ, (rootIdem (ν := ν) Q Λ₀ (blockRoot b)) *
      (decompose (stendhalGrade G' ν) c.1 n : StendhalAlgebra k Q Λ₀ ν) *
      rootIdem (ν := ν) Q Λ₀ (blockRoot b) = decompose (stendhalGrade G' ν) c.1 n := by
    intro n
    rw [← decompose_mul_of_mem_zero_left _ hE, ← decompose_mul_of_mem_zero_right _ hE, hce]
  let cn : ℤ → (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ₀) (ν := ν) (blockRoot b)).Corner :=
    fun n => KLR.Corner.mk _ (hmem n)
  have hsum : c = ∑ n ∈ (decompose (stendhalGrade G' ν) c.1).support, cn n := by
    apply KLR.Corner.ext
    rw [KLR.Corner.val_sum]
    exact (sum_support_decompose (stendhalGrade G' ν) c.1).symm
  have hmemS : rootAction Q Λ₀ (blockRoot b) c ∈ (blockAction Q Λ₀ hb).range := by
    rw [hsum, map_sum]
    refine Subalgebra.sum_mem _ fun n _ => ?_
    obtain ⟨β, hβ⟩ := hhom n (cn n) (decompose (stendhalGrade G' ν) c.1 n).2
    exact ⟨β, hβ⟩
  obtain ⟨β, hβ⟩ := hmemS
  exact ⟨β, hβ⟩

end Surjective

end Categorification.Stendhal
