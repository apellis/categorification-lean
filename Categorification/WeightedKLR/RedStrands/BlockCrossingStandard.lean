/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingGenerator
import Categorification.WeightedKLR.RedStrands.BlockPartialStandardTensor

/-!
# The crossed partial standard is a standard module

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10), the reduction to two red strands. Let `s` be a loading of the row in the crossed order
and `s'` a loading in the uncrossed order, and let `c` generate the summand of the crossing
bimodule at `s`, with bottom idempotent the loading idempotent of `s'`
(`BlockCut.Generator`). Left multiplication by the stacked generator `d` maps the corner
`e(s') V e_{κ₀}` onto the cut quotient `e(s) V e_{κ₀} / J` of step 2 (`generatorStack`,
`generatorStack_surjective`), and its kernel is the span of the local two-red relations stacked
on the uncrossed column (`mem_ker_generatorStack_iff`).

Webster's proof states that partial standardization of the local standard module is the global
standard module. Here this is the explicit hypothesis `StackedStandard`: the standard relations
at `s'` are exactly the corner elements whose class lies in the stacked local relations.
Under it, the cut quotient is the standard module at `s'` (`braidCutQuotientEquivStandard`).
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
variable {k : Type v} [CommRing k]
variable {I : Type} [DecidableEq I] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "D₀" => orderedProduct Q Λ botOrd Bs
local notation "D₁" => orderedProduct Q Λ topOrd Bs
local notation "ι₀" => orderedInclusion Q Λ hQ botOrd Bs
local notation "ι₁" => orderedInclusion Q Λ hQ topOrd Bs
local notation "C" => crossingProduct Q Λ hQ M f β L
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "S₁" => orderedColumn Q Λ hQ topOrd L M f β h
local notation "act" => blockProductAction Q Λ L M f β h
local notation "Z" => BalancedTensor k D₁ D₀ (BlockCut.space C) S₀
local notation "stk" => crossingStack Q Λ hQ L M f β h
local notation "Col" => blockColumn Q Λ L M f β h
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "p" => violMk k Q Λ ν (redProj k Q Λ ν κ₀)
local notation "F" => stackBlocks Q Λ L M f β h
local notation "pe" t => violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e t))

private abbrev columnGroup (σ : (B : RedBlock I ℓ) → Equiv.Perm (Fin B.size)) :
    AddCommGroup (orderedColumn Q Λ hQ σ L M f β h) := Submodule.addCommGroup _
attribute [local instance] columnGroup

/-- The local relations `H`, stacked on the uncrossed column and read in the quotient by the
higher cuts. -/
def stackedRelations (H : Submodule k D₀) : Submodule k (J).ringCon.Quotient :=
  (BalancedTensor.spanSmul (N := S₀) H).map ((Col).subtype ∘ₗ (S₀).subtype)

variable {Q Λ hQ L M f β h}

private theorem stack_loading (s : Loadings Bs) :
    F (loadingIdem Q Λ Bs s) = (pe (Seq.cast h (place Bs s))) :=
  stackBlocks_loadingIdem Q Λ L M f β h s

private theorem q_eq_zero (z : V) : q z = 0 ↔ z ∈ J := by
  change (J).ringCon.mk' z = 0 ↔ _
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

private theorem stack_one_mul_loading (s : Loadings Bs) :
    F 1 * (pe (Seq.cast h (place Bs s))) =
      (pe (Seq.cast h (place Bs s))) := by
  rw [← stack_loading s, ← map_mul, one_mul]

private theorem loading_mul_stack_one (s : Loadings Bs) :
    (pe (Seq.cast h (place Bs s))) * F 1 =
      (pe (Seq.cast h (place Bs s))) := by
  rw [← stack_loading s, ← map_mul, mul_one]

private theorem act_loading (s : Loadings Bs) (z : Col) :
    (act (projection Q Λ Bs (loadingIdem Q Λ Bs s)) z).1 =
      q ((pe (Seq.cast h (place Bs s)))) * z.1 := by
  rw [blockProductAction_projection, stack_loading]

/-- A corner element `e(s) v e_{κ₀}` as an element of the block column. -/
private def toColumn (s : Loadings Bs) (y : violCorner k Q Λ ν (Seq.cast h (place Bs s)) κ₀) : Col :=
  ⟨q y.1, y.1, by
    have hy := mem_violCorner_iff.1 y.2
    change q (F 1 * (y.1 * p)) = q y.1
    rw [hy.2]
    conv_lhs => rw [← hy.1, ← mul_assoc, stack_one_mul_loading]
    rw [hy.1]⟩

private theorem act_toColumn (s : Loadings Bs)
    (y : violCorner k Q Λ ν (Seq.cast h (place Bs s)) κ₀) :
    act (projection Q Λ Bs (loadingIdem Q Λ Bs s)) (toColumn s y) = toColumn s y := by
  apply Subtype.ext
  rw [act_loading]
  change q _ * q y.1 = q y.1
  rw [← map_mul, (mem_violCorner_iff.1 y.2).1]

/-- A representative in the diagram algebra of the inclusion of `c`. -/
private def genRep (c : (C).space) : diagrams Q Λ Bs :=
  (projection_surjective Q Λ Bs ((C).incl c)).choose

private theorem projection_genRep (c : (C).space) :
    projection Q Λ Bs (genRep c) = (C).incl c :=
  (projection_surjective Q Λ Bs ((C).incl c)).choose_spec

variable (h) in
/-- The stacked generator `e(s) d e(s')`, a diagram in the violated quotient. -/
def stackedGenerator (c : (C).space) (s s' : Loadings Bs) : V :=
  (pe (Seq.cast h (place Bs s))) * F (genRep c) * (pe (Seq.cast h (place Bs s')))

/-- **Stacking the generator is multiplication by the stacked generator.** -/
theorem crossingStack_tmul_eq_mul {c : (C).space} {e : quotients Q Λ Bs} {τ : D₀}
    {H : Submodule k D₀} (g : (C).Generator (LinearMap.ofClass ι₀) c e τ H)
    (he : ι₁ 1 * e = e) {s s' : Loadings Bs} (hes : e = projection Q Λ Bs (loadingIdem Q Λ Bs s))
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s')) (z : S₀) (hz : τ • z = z) :
    ((stk (BalancedTensor.tmul c z)).1).1 = q (stackedGenerator h c s s') * z.1.1 := by
  have hfix : (C).lproj e c = c := by
    have hf := g.fix τ
    rwa [g.right] at hf
  have h1 := act_crossingStack_tmul h e he c z
  rw [hfix] at h1
  have h2 : z.1.1 = q (pe (Seq.cast h (place Bs s'))) * z.1.1 := by
    have h3 := congrArg (fun w : S₀ => w.1.1) hz
    change (act (ι₀ τ) z.1).1 = z.1.1 at h3
    rw [hτs, act_loading] at h3
    exact h3.symm
  rw [← h1, hes, act_loading, crossingStack_tmul, ← projection_genRep,
    blockProductAction_projection, stackedGenerator, map_mul, map_mul, mul_assoc, mul_assoc]
  congr 2
/-- The stacked generator acts on the corner at `s'` as any representative of the generator
fixed on the left by the loading idempotent at `s`. -/
theorem stackedGenerator_mul_eq {c : (C).space} {s s' : Loadings Bs} {x : diagrams Q Λ Bs}
    (hx : projection Q Λ Bs x = (C).incl c) (hsx : loadingIdem Q Λ Bs s * x = x)
    (y : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀) :
    q (stackedGenerator h c s s' * y.1) = q (F x * y.1) := by
  have hy := (mem_violCorner_iff.1 y.2).1
  have e1 := blockProductAction_projection Q Λ L M f β h (genRep c) (toColumn s' y)
  have e2 := blockProductAction_projection Q Λ L M f β h x (toColumn s' y)
  rw [projection_genRep, ← hx, e2] at e1
  change q (F x) * q y.1 = q (F (genRep c)) * q y.1 at e1
  rw [stackedGenerator, mul_assoc, mul_assoc, hy, map_mul, map_mul (q) (F (genRep c)), ← e1,
    ← map_mul, ← map_mul, ← mul_assoc, ← stack_loading s, ← map_mul, hsx]

local notation "Uc" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₀

variable (h) in
/-- Left multiplication by the stacked generator, from the corner at `s'` to the corner at
`s`. -/
def generatorStack (c : (C).space) (s s' : Loadings Bs) :
    violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀ →ₗ[Ucᵐᵒᵖ]
      violCorner k Q Λ ν (Seq.cast h (place Bs s)) κ₀ where
  toFun x := ⟨stackedGenerator h c s s' * x.1, mem_violCorner_iff.2 ⟨by
      rw [stackedGenerator, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul,
        KLRAlgebra.e_mul_self],
      by rw [mul_assoc, (mem_violCorner_iff.1 x.2).2]⟩⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change _ * (x.1 * a.unop.val) = (_ * x.1) * a.unop.val
    rw [mul_assoc])

theorem generatorStack_val (c : (C).space) (s s' : Loadings Bs)
    (x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀) :
    (generatorStack h c s s' x).1 = stackedGenerator h c s s' * x.1 := rfl

/-- The retained root of a placed nonviolated loading is the boundary count of the row. -/
theorem adjacentBlockRoot_place {s : Loadings Bs} (hs : ¬ Violated Bs s)
    (ht : redWord (Seq.cast h (place Bs s)) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst) :
    adjacentBlockRoot (f 0) (f 1) (Seq.cast h (place Bs s)) = α := by
  have hn : (κ₀).Nodup :=
    ((List.Perm.swap (f 0) (f 1) (M.map Prod.fst)).append_left (L.map Prod.fst)).nodup_iff.1
      (ht ▸ redWord_nodup _)
  funext r i
  change blockBlackCount (Seq.cast h (place Bs s)) (cut (f 0) (f 1) r) i = _
  have hc {u w : Multiset (I ⊕ Fin ℓ)} (e : u = w) (z : Seq u) (X : Finset (Fin ℓ)) :
      blockBlackCount (Seq.cast e z) X i = blockBlackCount z X i := by subst w; rfl
  rw [hc]; exact count_place_of_not_violated r i s (aligned_adjacent L M f β hn) hs
private theorem toColumn_mem {τ : D₀} {s' : Loadings Bs}
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s'))
    (x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀) : toColumn s' x ∈ S₀ := by
  refine ⟨toColumn s' x, ?_⟩
  change act (ι₀ 1) (toColumn s' x) = toColumn s' x
  conv_lhs => rw [← act_toColumn s' x, ← hτs, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    one_mul, hτs, act_toColumn]

/-- **The kernel of stacking the generator** (Webster, arXiv:1309.3796v2, §6.1, proof of
Proposition 6.9). The stacked generator kills a corner element modulo the higher cuts exactly
when the element lies in the stacked local relations. -/
theorem stackedGenerator_mul_eq_zero_iff {c : (C).space} {e : quotients Q Λ Bs} {τ : D₀}
    {H : Submodule k D₀} (g : (C).Generator (LinearMap.ofClass ι₀) c e τ H)
    (he : ι₁ 1 * e = e) (hτ : IsIdempotentElem τ) {s s' : Loadings Bs}
    (hes : e = projection Q Λ Bs (loadingIdem Q Λ Bs s))
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s'))
    (x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀) :
    q (stackedGenerator h c s s' * x.1) = 0 ↔ q x.1 ∈ stackedRelations Q Λ hQ L M f β h H := by
  let z : S₀ := ⟨toColumn s' x, toColumn_mem hτs x⟩
  have hz : τ • z = z := Subtype.ext (by
    change act (ι₀ τ) (toColumn s' x) = toColumn s' x
    rw [hτs, act_toColumn])
  have hk := crossingStack_tmul_eq_mul g he hes hτs z hz
  have hq : q (stackedGenerator h c s s' * x.1) = ((stk (BalancedTensor.tmul c z)).1).1 := by
    rw [hk, map_mul]; rfl
  rw [hq]
  have hinj := crossingStack_injective Q Λ hQ L M f β h
  constructor
  · intro h0
    have hs0 : stk (BalancedTensor.tmul c z) = 0 := Subtype.ext (Subtype.ext h0)
    have ht0 : (BalancedTensor.tmul c z : Z) = 0 :=
      hinj (hs0.trans (map_zero (stk)).symm)
    exact ⟨z, mem_spanSmul_of_tmul_eq_zero h g hτ hz ht0, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext (Subtype.ext hwz)
    rw [hwz'] at hw
    have ht0 := tmul_eq_zero_of_mem_spanSmul h g hw
    have hs0 : stk (BalancedTensor.tmul c z) = 0 := (congrArg (stk) ht0).trans (map_zero (stk))
    exact congrArg (fun w : S₁ => w.1.1) hs0
/-- **Every corner element is a stack of the generator** (Webster, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.9): modulo the higher cuts, every element of `e(s) V e_{κ₀}` is the
stacked generator times an element of `e(s') V e_{κ₀}`. -/
theorem exists_stackedGenerator_mul {c : (C).space} {e : quotients Q Λ Bs} {τ : D₀}
    {H : Submodule k D₀} (g : (C).Generator (LinearMap.ofClass ι₀) c e τ H)
    (he : ι₁ 1 * e = e) (hτ : IsIdempotentElem τ) {s s' : Loadings Bs}
    (hes : e = projection Q Λ Bs (loadingIdem Q Λ Bs s))
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s'))
    (y : violCorner k Q Λ ν (Seq.cast h (place Bs s)) κ₀) :
    ∃ x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀,
      q (stackedGenerator h c s s' * x.1) = q y.1 := by
  have hw : act e (toColumn s y) = toColumn s y := by rw [hes, act_toColumn]
  have hw1 : toColumn s y ∈ S₁ := by
    refine ⟨toColumn s y, ?_⟩
    change act (ι₁ 1) (toColumn s y) = toColumn s y
    conv_lhs => rw [← hw, ← Module.End.mul_apply, ← map_mul, he, hw]
  obtain ⟨z, hz⟩ := exists_stack_generator h g he ⟨toColumn s y, hw1⟩
  let z' : S₀ := τ • z
  have hz' : τ • z' = z' := by
    change τ • τ • z = τ • z
    rw [smul_smul, hτ.eq]
  have hcz : (BalancedTensor.tmul c z' : Z) = BalancedTensor.tmul c z := by
    rw [← BalancedTensor.op_smul_tmul]
    congr 1
    exact g.right
  obtain ⟨v, hv⟩ := z.1.2
  have hzv : z'.1.1 = q ((pe (Seq.cast h (place Bs s'))) * v * p) := by
    change (act (ι₀ τ) z.1).1 = _
    rw [hτs, act_loading, ← hv]
    change q (pe (Seq.cast h (place Bs s'))) * q (F 1 * (v * p)) = _
    rw [← map_mul]
    congr 1
    rw [← mul_assoc, loading_mul_stack_one, mul_assoc]
  let x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀ :=
    ⟨(pe (Seq.cast h (place Bs s'))) * v * p, mem_violCorner_iff.2 ⟨by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, KLRAlgebra.e_mul_self], by
      rw [mul_assoc, ← map_mul, (isIdempotentElem_redProj κ₀).eq]⟩⟩
  refine ⟨x, ?_⟩
  have h1 := crossingStack_tmul_eq_mul g he hes hτs z' hz'
  rw [hcz, ← hz, hw, hzv] at h1
  rw [map_mul]
  exact h1.symm
variable (hQ h) in
/-- **Partial standardization of the local standard is the global standard** (Webster,
arXiv:1309.3796v2, §6.1, proof of Proposition 6.9, where it is used without proof). The
standard relations at the loading `s'` are the corner elements whose class modulo the higher
cuts lies in the local relations `H` stacked on the uncrossed column. This is an explicit
hypothesis of Proposition 6.9; the tensor-product roadmap tracks its removal. -/
def StackedStandard (H : Submodule k D₀) (s' : Loadings Bs) : Prop :=
  ∀ x : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀,
    x ∈ violStandardUpper (Seq.cast h (place Bs s')) κ₀ ↔
      q x.1 ∈ stackedRelations Q Λ hQ L M f β h H

/-- **The cut quotient of step 2 is the standard module at the output loading** (Webster,
arXiv:1309.3796v2, §6.1, proof of Proposition 6.9, the reduction to two red strands). Left
multiplication by the stacked generator identifies the standard module at `s'` with the cut
`e(s) V e_{κ₀}` modulo the diagrams through higher loadings of the uncrossed order. It uses the
explicit hypothesis `StackedStandard`. -/
def braidCutQuotientEquivStandard {c : (C).space} {e : quotients Q Λ Bs} {τ : D₀}
    {H : Submodule k D₀} (g : (C).Generator (LinearMap.ofClass ι₀) c e τ H)
    (he : ι₁ 1 * e = e) (hτ : IsIdempotentElem τ) {s s' : Loadings Bs}
    (hes : e = projection Q Λ Bs (loadingIdem Q Λ Bs s))
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s')) (hs : ¬ Violated Bs s)
    (ht : redWord (Seq.cast h (place Bs s)) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h H s') :
    ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.cast h (place Bs s')) κ₀ ≃ₗ[Ucᵐᵒᵖ]
      BraidCutQuotient Q Λ (Seq.cast h (place Bs s)) (f 0) (f 1) κ₀ := by
  let Φ := braidCutMk Q Λ (Seq.cast h (place Bs s)) (f 0) (f 1) κ₀ ∘ₗ generatorStack h c s s'
  have hroot := adjacentBlockRoot_place hs ht
  have hmem (w : violCorner k Q Λ ν (Seq.cast h (place Bs s)) κ₀) :
      w ∈ braidCutUpper Q Λ (Seq.cast h (place Bs s)) (f 0) (f 1) κ₀ ↔ q w.1 = 0 := by
    change w.1 ∈ blockUpperIdeal k Q Λ ν (f 0) (f 1)
      (adjacentBlockRoot (f 0) (f 1) (Seq.cast h (place Bs s))) κ₀ ↔ _
    rw [hroot, q_eq_zero]
  have hker : LinearMap.ker Φ = violStandardUpper (Seq.cast h (place Bs s')) κ₀ := by
    ext x
    rw [LinearMap.mem_ker, hstd x]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hmem, generatorStack_val]
    exact stackedGenerator_mul_eq_zero_iff g he hτ hes hτs x
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨y, rfl⟩ := braidCutMk_surjective Q Λ (Seq.cast h (place Bs s)) (f 0) (f 1) κ₀ w
    obtain ⟨x, hx⟩ := exists_stackedGenerator_mul g he hτ hes hτs y
    refine ⟨x, (Submodule.Quotient.eq _).2 ((hmem _).2 ?_)⟩
    change q (stackedGenerator h c s s' * x.1 - y.1) = 0
    rw [map_sub, hx, sub_self]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)

theorem braidCutQuotientEquivStandard_mk {c : (C).space} {e : quotients Q Λ Bs} {τ : D₀}
    {H : Submodule k D₀} (g : (C).Generator (LinearMap.ofClass ι₀) c e τ H)
    (he : ι₁ 1 * e = e) (hτ : IsIdempotentElem τ) {s s' : Loadings Bs}
    (hes : e = projection Q Λ Bs (loadingIdem Q Λ Bs s))
    (hτs : ι₀ τ = projection Q Λ Bs (loadingIdem Q Λ Bs s')) (hs : ¬ Violated Bs s)
    (ht : redWord (Seq.cast h (place Bs s)) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst)
    (hstd : StackedStandard hQ h H s') (y : violCorner k Q Λ ν (Seq.cast h (place Bs s')) κ₀) :
    braidCutQuotientEquivStandard g he hτ hes hτs hs ht hstd
        ((violStandardUpper (Seq.cast h (place Bs s')) κ₀).mkQ y) =
      braidCutMk Q Λ (Seq.cast h (place Bs s)) (f 0) (f 1) κ₀ (generatorStack h c s s' y) :=
  rfl
end Categorification.Stendhal.RedBlock
