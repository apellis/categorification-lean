/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TildeStandardStratification
import Categorification.Algebra.DerivedTensorStratifyingQuotient
import Categorification.Algebra.ModuleFiltrationIdempotents

/-!
# `T̃^λ → T^λ` is a homological epimorphism

The quotient map `T̃^λ → T^λ` of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3 (Definition 4.7) has no higher Tor:
`Tor^{T̃^λ}_n(T^λ, X) = 0` for `n ≠ 0` and every right `T^λ`-module `X`, in particular
`X = T^λ` (`isZero_derivedTensorHomology_tensorProductAlgebra`,
`isZero_derivedTensorHomology_tensorProductAlgebra_self`). Webster does not state this; it is
the input that identifies derived tensor products over `T̃^λ` and over `T^λ`.

The proof uses the standard stratification of `T̃^λ` (Corollary 5.23,
`tildeOrderedStandardCovers`):

* the loadings whose leftmost strand is black (the violated loadings) form a set closed
  upwards in Webster's order (`isUpperLoadingSet_violated`), and the violated ideal `V` is the
  stratum ideal of this set (`mem_violatedIdeal_iff_mem_stratumIdeal`);
* so `V = ⊕_s V e(s)` has a finite filtration by standard modules `S̃_u`, `u` violated
  (`exists_hasFiltration_violated`);
* the standards `S̃_u`, `u` violated, have no Tor at all with a module killed by the violated
  idempotents, and `0 → V → T̃^λ → T^λ → 0` gives the claim
  (`isZero_derivedTensorHomology_quotient_of_stratum`).

Left `T̃^λ`-modules are right modules over the opposite ring, which is how the derived tensor
product of `Categorification.derivedTensor` reads its coefficient; the ordered covers are
transported along `T̃^λ ≃ (T̃^λ)ᵐᵒᵖᵐᵒᵖ`.

Hypotheses on the grading as in `tildeOrderedStandardCovers`: the grading on `T̃^λ` with all
red orders is bounded below (`hc`) and black dots have positive degree (`hpos`); Webster's
grading satisfies both. Route hypothesis: `AllFiniteDeltaInjective`, inherited from
`phiLayerEquiv`.

## Main results

* `isUpperLoadingSet_violated`, `mem_violatedIdeal_iff_mem_stratumIdeal`,
  `exists_hasFiltration_violated`.
* `isZero_derivedTensorHomology_tensorProductAlgebra`,
  `isZero_derivedTensorHomology_tensorProductAlgebra_self`.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR TypeA Equiv ModuleFiltration MulOpposite DG

open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "B" => StendhalAlgebra k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν

/-- **The violated loadings form a set closed upwards** in Webster's order: if the leftmost
strand of `u` is black and `u ≤ v`, then the leftmost strand of `v` is black, since otherwise
`v` has no black strand left of its leftmost (red) strand. -/
theorem isUpperLoadingSet_violated : IsUpperLoadingSet {u : Seq μ | IsViolated u} := by
  rintro u v ⟨h0, hu⟩ huv
  refine ⟨h0, ?_⟩
  rcases hv : v.lbl ⟨0, h0⟩ with i | r
  · rfl
  · exfalso
    rcases hu' : u.lbl ⟨0, h0⟩ with j | r'
    · have hle := huv r j
      have hpos : 0 < blackCount u r j := by
        refine Finset.card_pos.2 ⟨⟨0, h0⟩, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hu', fun b hb => ?_⟩
        rcases Nat.eq_zero_or_pos b.val with hb0 | hb0
        · rw [show b = ⟨0, h0⟩ from Fin.ext hb0, hu'] at hb
          exact absurd hb Sum.inl_ne_inr
        · exact Fin.lt_def.2 hb0
      have hzero : blackCount v r j = 0 := by
        refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a ha => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact absurd (Fin.lt_def.1 (ha.2 ⟨0, h0⟩ hv)) (Nat.not_lt_zero _)
      omega
    · rw [hu'] at hu
      exact absurd hu (by simp)

/-- The stratum ideal of the violated loadings, as a two-sided ideal. -/
def violatedStratumTwoSided : TwoSidedIdeal B :=
  TwoSidedIdeal.mk' (stratumIdeal Q Λ {u : Seq μ | IsViolated u} : Set B)
    (Submodule.zero_mem _) (Submodule.add_mem _) (Submodule.neg_mem _)
    (fun {x _} hy => Submodule.smul_mem _ x hy)
    (fun {_ y} hx => stratumIdeal_mul_mem hx y)

/-- **The violated ideal is the stratum ideal of the violated loadings.** -/
theorem mem_violatedIdeal_iff_mem_stratumIdeal (x : B) :
    x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν ↔
      x ∈ stratumIdeal Q Λ {u : Seq μ | IsViolated u} := by
  constructor
  · intro hx
    have hle : StendhalAlgebra.violatedIdeal k Q Λ ν ≤ violatedStratumTwoSided := by
      refine TwoSidedIdeal.span_le.2 ?_
      rintro _ ⟨i, hi, hv, rfl⟩
      rw [SetLike.mem_coe, violatedStratumTwoSided, TwoSidedIdeal.mem_mk']
      have := e_mul_mem_stratumIdeal (Q := Q) (Λ := Λ) hi (Γ := {u : Seq μ | IsViolated u}) hv 1
      rwa [mul_one] at this
    exact (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ x).1 (hle hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, b, hv, rfl⟩ := hx
      exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.subset_span ⟨u, hu, hv, rfl⟩)
    | zero => exact TwoSidedIdeal.zero_mem _
    | add x y _ _ hx hy => exact TwoSidedIdeal.add_mem _ hx hy
    | smul a x _ hx => exact TwoSidedIdeal.mul_mem_left _ _ _ hx

/-- Right multiplication by `e(t)` on the violated ideal. -/
def violatedRightMul (t : {t : Seq μ // IsRedOrdered t}) :
    Module.End B (stratumIdeal Q Λ {u : Seq μ | IsViolated u}) where
  toFun v := ⟨v.1 * StendhalAlgebra.e t.1 t.2, stratumIdeal_mul_mem v.2 _⟩
  map_add' v w := Subtype.ext (add_mul v.1 w.1 _)
  map_smul' a v := Subtype.ext (mul_assoc a v.1 _)

/-- The image of right multiplication by `e(t)` on `V` is `V e(t) = P̃_{violated}`, as a
submodule of `T̃^λ e(t)`. -/
def rangeViolatedRightMulEquiv (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (t : {t : Seq μ // IsRedOrdered t}) :
    LinearMap.range (violatedRightMul (Q := Q) (Λ := Λ) t) ≃ₗ[B]
      phiStratumSub Q Λ ρ t.2 {u : Seq μ | IsViolated u} :=
  (({ toFun := fun x => ⟨⟨x.1.1, by
        obtain ⟨v, hv⟩ := x.2
        change x.1.1 * StendhalAlgebra.e t.1 t.2 = x.1.1
        rw [← hv]
        change v.1 * StendhalAlgebra.e t.1 t.2 * StendhalAlgebra.e t.1 t.2 =
          v.1 * StendhalAlgebra.e t.1 t.2
        rw [mul_assoc, stendhalAlgebra_e_mul_e_self]⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, ⟨⟨y.1.1, y.2⟩, Subtype.ext y.1.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } :
    LinearMap.range (violatedRightMul (Q := Q) (Λ := Λ) t) ≃ₗ[B]
      (stratumIdeal Q Λ {u : Seq μ | IsViolated u}).comap
        (lIdeal (StendhalAlgebra.e t.1 t.2 : B)).subtype)).trans
    (LinearEquiv.ofEq _ _
      (comap_stratumIdeal_eq_phiStratumSub ρ hρ t.2 isUpperLoadingSet_violated))

/-- A filtration all of whose labels satisfy `p` is a filtration by the labels in `p`. -/
private theorem hasFiltration_exists_subtype {ι : Type*} {p : ι → Prop} {L : ι → ModuleCat.{0} B}
    {l : List ι} {Y : ModuleCat.{0} B} (h : HasFiltration L l Y) (hl : ∀ c ∈ l, p c) :
    ∃ l' : List {c // p c}, HasFiltration (fun c => L c.1) l' Y := by
  induction h with
  | zero hY => exact ⟨[], .zero hY⟩
  | cons f g l c hf hfg hg _ hZ ih =>
    obtain ⟨l', hl'⟩ := ih fun d hd => hl d (List.mem_cons_of_mem _ hd)
    exact ⟨⟨c, hl c List.mem_cons_self⟩ :: l', .cons f g l' _ hf hfg hg hl' hZ⟩

variable {C : QuantumGroup.CartanDatum I}

/-- **The violated ideal has a standard filtration** by standard modules `S̃_u` with `u`
violated (from Webster, arXiv:1309.3796v3, Corollary 5.23). Hypotheses as in
`exists_hasFiltration_phiStratumSub`. Route hypothesis: `AllFiniteDeltaInjective`. -/
theorem exists_hasFiltration_violated
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) :
    ∃ l : List {t : Seq μ // IsRedOrdered t}, (∀ t ∈ l, IsViolated t.1) ∧
      HasFiltration (fun t : {t : Seq μ // IsRedOrdered t} =>
        ModuleCat.of B (tildeStandard Q Λ t.1 t.2)) l
        (ModuleCat.of B (stratumIdeal Q Λ {u : Seq μ | IsViolated u})) := by
  classical
  let L : {t : Seq μ // IsRedOrdered t} → ModuleCat B := fun t =>
    ModuleCat.of B (tildeStandard Q Λ t.1 t.2)
  let L' : {t : {t : Seq μ // IsRedOrdered t} // IsViolated t.1} → ModuleCat B :=
    fun t => L t.1
  have key : ∃ l : List {t : {t : Seq μ // IsRedOrdered t} // IsViolated t.1},
      HasFiltration L' l (ModuleCat.of B (stratumIdeal Q Λ {u : Seq μ | IsViolated u})) := by
    refine exists_hasFiltration_of_orthogonal
      (M := ModuleCat.of B (stratumIdeal Q Λ {u : Seq μ | IsViolated u}))
      (violatedRightMul (Q := Q) (Λ := Λ)) Finset.univ ?_ ?_ ?_ fun t _ => ?_
    · intro t _
      refine LinearMap.ext fun x => Subtype.ext ?_
      change x.1 * StendhalAlgebra.e t.1 t.2 * StendhalAlgebra.e t.1 t.2 =
        x.1 * StendhalAlgebra.e t.1 t.2
      rw [mul_assoc, stendhalAlgebra_e_mul_e_self]
    · intro t _ u _ htu
      refine LinearMap.ext fun x => Subtype.ext ?_
      change x.1 * StendhalAlgebra.e u.1 u.2 * StendhalAlgebra.e t.1 t.2 = 0
      have h0 : (StendhalAlgebra.e u.1 u.2 * StendhalAlgebra.e t.1 t.2 : B) = 0 := by
        apply Subtype.ext
        change StendhalAlgebraAllOrders.e u.1 * StendhalAlgebraAllOrders.e t.1 = 0
        have hne : u.1 ≠ t.1 := fun h => htu (Subtype.ext h).symm
        simp [StendhalAlgebraAllOrders.e_mul_e, hne]
      rw [mul_assoc, h0, mul_zero]
    · refine LinearMap.ext fun x => Subtype.ext ?_
      rw [LinearMap.sum_apply, Submodule.coe_sum]
      change (∑ t : {t : Seq μ // IsRedOrdered t}, x.1 * StendhalAlgebra.e t.1 t.2) = x.1
      rw [← Finset.mul_sum, sum_stendhalAlgebra_e_eq_one, mul_one]
    · obtain ⟨l, hl, hF⟩ := exists_hasFiltration_phiStratumSub hQ hR hall G' ρ₀ hρ₀ hc hpos t.2
        isUpperLoadingSet_violated
      obtain ⟨l', hl'⟩ := hasFiltration_exists_subtype
        (p := fun t : {t : Seq μ // IsRedOrdered t} => IsViolated t.1) hF hl
      exact ⟨l', hl'.of_equiv (rangeViolatedRightMulEquiv ρ₀ hρ₀ t).symm⟩
  obtain ⟨l, hl⟩ := key
  refine ⟨l.map Subtype.val, fun t ht => ?_, HasFiltration.relabel (L := L) Subtype.val hl⟩
  obtain ⟨t', -, rfl⟩ := List.mem_map.1 ht
  exact t'.2

section Tor

universe w

private theorem stendhalLT_trans' {a b c : Seq μ} (hab : StendhalLT a b) (hbc : StendhalLT b c) :
    StendhalLT a c :=
  ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca => hab.2 fun r i => (hbc.1 r i).trans
    (hca r i)⟩

/-- Webster's order on red-ordered loadings is well-founded downwards. -/
theorem wellFounded_stendhalLT_flip :
    WellFounded fun a b : {t : Seq μ // IsRedOrdered t} => StendhalLT b.1 a.1 := by
  have : IsTrans {t : Seq μ // IsRedOrdered t} fun a b => StendhalLT b.1 a.1 :=
    ⟨fun _ _ _ hab hbc => stendhalLT_trans' hbc hab⟩
  have : Std.Irrefl fun a b : {t : Seq μ // IsRedOrdered t} => StendhalLT b.1 a.1 :=
    ⟨fun _ h => h.2 h.1⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- A left `T̃^λ`-module as a right module over `(T̃^λ)ᵐᵒᵖ`, the form of the coefficient of
`derivedTensor`. -/
abbrev tildeCoefficient (M : ModuleCat.{0} B) : ModuleCat.{0} Bᵐᵒᵖᵐᵒᵖ :=
  (ModuleCat.restrictScalars (RingEquiv.opOp B).symm.toRingHom).obj M

/-- `T^λ` as a left `T̃^λ`-module. -/
abbrev tensorProductAlgebraLeft : ModuleCat.{0} B :=
  (ModuleCat.restrictScalars (TensorProductAlgebra.mk Q Λ ν).toRingHom).obj (ModuleCat.of T T)

/-- `T^λ` as a right `T̃^λ`-module. -/
abbrev tensorProductAlgebraRight : ModuleCat.{0} Bᵐᵒᵖ :=
  (ModuleCat.restrictScalars (TensorProductAlgebra.mk Q Λ ν).toRingHom.op).obj
    (ModuleCat.of Tᵐᵒᵖ T)

theorem tensorProductAlgebra_mk_eq_zero_iff (x : B) :
    TensorProductAlgebra.mk Q Λ ν x = 0 ↔ x ∈ StendhalAlgebra.violatedIdeal k Q Λ ν := by
  change (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk' x = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

variable [HasDerivedCategory.{w, 0} ℤ]
  [HasDerivedCategory.{w, 0} (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- **`T̃^λ → T^λ` has no higher Tor**: for every right `T̃^λ`-module `X` killed by the
idempotents of the violated loadings (that is, every right `T^λ`-module), the derived tensor
`T^λ ⊗ᴸ_{T̃^λ} X` has no cohomology outside degree `0`. The proof uses the standard
stratification of `T̃^λ` (Webster, arXiv:1309.3796v3, Corollary 5.23); the statement is not
in Webster. Hypotheses on the grading as in `tildeOrderedStandardCovers`. Route hypothesis:
`AllFiniteDeltaInjective`. -/
theorem isZero_derivedTensorHomology_tensorProductAlgebra
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (X : ModuleCat.{0} Bᵐᵒᵖ)
    (hX : ∀ (u : Seq μ) (hu : IsRedOrdered u), IsViolated u →
      ∀ x : X, (op (StendhalAlgebra.e u hu : B)) • x = 0) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor ℤ n).obj
      ((derivedTensor.{w} ℤ Bᵐᵒᵖ (tildeCoefficient (tensorProductAlgebraLeft (Q := Q)
        (Λ := Λ) (ν := ν)))).obj
          (DG.DerivedCategory.Q.obj (DGModuleCat.of Bᵐᵒᵖ (InDegreeZero X))))) := by
  let σ := RingEquiv.opOp B
  let D := (tildeOrderedStandardCovers hQ hR hall G' ρ₀ hρ₀ hc hpos).transport σ
  obtain ⟨l, hl, hF⟩ := exists_hasFiltration_violated hQ hR hall G' ρ₀ hρ₀ hc hpos
  let V := stratumIdeal Q Λ {u : Seq μ | IsViolated u}
  let f : tildeCoefficient (ModuleCat.of B V) →ₗ[Bᵐᵒᵖᵐᵒᵖ] Bᵐᵒᵖᵐᵒᵖ :=
    { toFun := fun v => σ (show V from v).1
      map_add' := fun v w => map_add σ (show V from v).1 (show V from w).1
      map_smul' := fun b v => by
        change σ (σ.symm b * (show V from v).1) = b * σ (show V from v).1
        rw [map_mul, RingEquiv.apply_symm_apply] }
  let g : Bᵐᵒᵖᵐᵒᵖ →ₗ[Bᵐᵒᵖᵐᵒᵖ] tildeCoefficient (tensorProductAlgebraLeft (Q := Q)
      (Λ := Λ) (ν := ν)) :=
    { toFun := fun b => (TensorProductAlgebra.mk Q Λ ν (σ.symm b) : T)
      map_add' := fun b b' => by
        change TensorProductAlgebra.mk Q Λ ν (σ.symm (b + b')) =
          TensorProductAlgebra.mk Q Λ ν (σ.symm b) + TensorProductAlgebra.mk Q Λ ν (σ.symm b')
        rw [map_add, map_add]
      map_smul' := fun b b' => by
        change TensorProductAlgebra.mk Q Λ ν (σ.symm (b * b')) =
          TensorProductAlgebra.mk Q Λ ν (σ.symm b) * TensorProductAlgebra.mk Q Λ ν (σ.symm b')
        rw [map_mul, map_mul] }
  refine isZero_derivedTensorHomology_quotient_of_stratum D
    wellFounded_stendhalLT_flip {t | IsViolated t.1}
    (fun a b ha hab => isUpperLoadingSet_violated ha hab.1)
    (fun t _ => by
      change IsIdempotentElem (σ (StendhalAlgebra.e t.1 t.2))
      rw [IsIdempotentElem, ← map_mul, stendhalAlgebra_e_mul_e_self])
    (V := tildeCoefficient (ModuleCat.of B V)) (M := ModuleCat.of Bᵐᵒᵖᵐᵒᵖ Bᵐᵒᵖᵐᵒᵖ)
    hl (hF.restrictScalars σ.symm.toRingHom) f g ?_ ?_ ?_ X
    (fun t ht x => hX t.1 t.2 ht x) n hn
  · intro v w h
    exact Subtype.ext (σ.injective h)
  · intro b
    change TensorProductAlgebra.mk Q Λ ν (σ.symm b) = 0 ↔ _
    rw [tensorProductAlgebra_mk_eq_zero_iff, mem_violatedIdeal_iff_mem_stratumIdeal]
    constructor
    · intro hb
      exact ⟨(⟨σ.symm b, hb⟩ : V), by change σ (σ.symm b) = b; exact σ.apply_symm_apply b⟩
    · rintro ⟨v, rfl⟩
      change σ.symm (σ (show V from v).1) ∈ V
      rw [RingEquiv.symm_apply_apply]
      exact (show V from v).2
  · intro t
    obtain ⟨a, ha⟩ := (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.mk'_surjective
      (show T from t)
    exact ⟨σ a, by
      change TensorProductAlgebra.mk Q Λ ν (σ.symm (σ a)) = _
      rw [RingEquiv.symm_apply_apply]
      exact ha⟩

/-- **`Tor^{T̃^λ}_n(T^λ, T^λ) = 0` for `n ≠ 0`**: the quotient map `T̃^λ → T^λ` is a
homological epimorphism. Hypotheses as in `isZero_derivedTensorHomology_tensorProductAlgebra`.
Route hypothesis: `AllFiniteDeltaInjective`. -/
theorem isZero_derivedTensorHomology_tensorProductAlgebra_self
    (hQ : KLRSymm Q) (hR : IsRouquierQ C Q)
    (hall : ∀ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ hQ)
    (G' : KLR.GradingDatum (stendhalQ Q Λ)) (ρ₀ : Perm (Fin m) → List ℕ)
    (hρ₀ : ∀ w : Perm (Fin m), TypeA.IsReduced m (ρ₀ w) ∧ TypeA.wordProd m (ρ₀ w) = w)
    {c : ℤ} (hc : ∀ m' < -c, allOrdersGrade G' ν m' = ⊥)
    (hpos : ∀ i ∈ ν, 0 < G'.degX (.inl i)) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor ℤ n).obj
      ((derivedTensor.{w} ℤ Bᵐᵒᵖ (tildeCoefficient (tensorProductAlgebraLeft (Q := Q)
        (Λ := Λ) (ν := ν)))).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of Bᵐᵒᵖ
          (InDegreeZero (tensorProductAlgebraRight (Q := Q) (Λ := Λ) (ν := ν))))))) := by
  refine isZero_derivedTensorHomology_tensorProductAlgebra hQ hR hall G' ρ₀ hρ₀ hc hpos _
    (fun u hu hv x => ?_) n hn
  have h0 : TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e u hu) = 0 :=
    (tensorProductAlgebra_mk_eq_zero_iff _).2
      (TwoSidedIdeal.subset_span ⟨u, hu, hv, rfl⟩)
  change op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e u hu)) • (show T from x) = 0
  rw [h0, MulOpposite.op_zero, zero_smul]

end Tor

end Categorification.Stendhal
