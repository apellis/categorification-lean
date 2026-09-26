/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Theorem321

/-!
# KL I, Theorem 3.21 on arbitrary graded modules: the isomorphism of functors

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, end of §3.2 (TeX lines ~2313–2346), **Theorem 3.21**: a relation
`∑_k u_k θ(k) = ∑_ℓ v_ℓ θ'(ℓ)` in `_𝒜 f` gives "an isomorphism of projectives
`⊕_k P_{θ(k)}^{⊕ u_k} ≅ ⊕_ℓ P_{θ'(ℓ)}^{⊕ v_ℓ}` inducing an isomorphism of functors
`⊕_k 𝓕_{θ(k)}^{⊕ u_k} ≅ ⊕_ℓ 𝓕_{θ'(ℓ)}^{⊕ v_ℓ}`" on `R-mod`.

`Categorification.KLR.Theorem321` proves the statement on `R-pmod`. Here we treat arbitrary
graded modules (not necessarily finitely generated or projective), following the paper's
mechanism: the functors are induction with a fixed projective, `M ↦ Ind (X ⊠ M)`, so an
isomorphism of the projectives `X ≅ X'` induces an isomorphism of functors.

## Main definitions and results

For a `GradingDatum G` (any KLR algebra with a grading) and bundled graded modules
`X ∈ R(μ)-gmod`, `M ∈ R(ν)-gmod`:

* `GradingDatum.indGMod G X M = Ind_{μ,ν} (X ⊠ M)` as a graded `R(μ + ν)`-module, with
  `GradingDatum.indGModMap G X f = Ind (X ⊠ f)` for `R(ν)`-linear `f` (degree-preserving if `f`
  is, `indGModMap_preservesGrading`; functorial, `indGModMap_id`, `indGModMap_comp`).
* `GradingDatum.indGModCongrLeft G e M : Ind (X ⊠ M) ≅ Ind (X' ⊠ M)` for `e : X ≅ X'`, **natural
  in `M`** (`indGModCongrLeft_naturality`).
* Additivity in `X`: `indGModProdLeft`, `indGModShiftLeft`, `subsingleton_indGMod`
  (`Ind (0 ⊠ M) = 0`); transport of weights: `indGModCastLeft`.
* `GradingDatum.indGModAssocIso`, `GradingDatum.indGModUnitIso` : associativity and unitality
  of induction as graded isomorphisms (after transport along `(μ₁ + μ₂) + ν = μ₁ + (μ₂ + ν)`,
  `0 + ν = ν`).

For the KL I algebras (`klGradingDatum k Γ`, `k` a field):

* `KLGamma.funFM`, `KLGamma.funThetaM` : `𝓕_i^{(a)} M = Ind (P_{i^{(a)}} ⊠ M)` and
  `𝓕_θ = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}` on graded modules.
* `KLGamma.indProjDivIso` : `Ind (P_θ ⊠ M) ≅ 𝓕_θ(M)` for every graded module `M` (it uses
  `P_{θθ'} ≅ Ind (P_θ ⊠ P_{θ'})`, which follows from Theorem 1.1 and Krull–Schmidt).
* **`KLGamma.theorem_3_21_natIso`** : for a relation `∑ q^n θ_d = ∑ q^{n'} θ_{d'}` in `_𝒜 f` and
  every weight `μ`, an isomorphism `Φ_M : Ind (X ⊠ M) ≅ Ind (X' ⊠ M)` for all graded modules `M`,
  where `X = ⊕_{(n, d), |d| = μ} P_d{n}` and `X' = ⊕_{(n', d'), |d'| = μ} P_{d'}{n'}`
  (`KLGamma.sumP`); **`KLGamma.theorem_3_21_natIso_naturality`** : `Φ` is natural in `M` (for all
  `R(ν)`-linear maps `f : M → M'`).
* **`KLGamma.theorem_3_21_gmod`** : `Ind (X ⊠ M) ≅ ⊕_{(n, d), |d| = μ} 𝓕_d(M){n}`
  (`KLGamma.sumFM`), hence `⊕_{(n, d), |d| = μ} 𝓕_d(M){n} ≅ ⊕_{(n', d'), |d'| = μ} 𝓕_{d'}(M){n'}`
  for **every** graded module `M`.

The identification `Ind (X ⊠ M) ≅ ⊕ 𝓕_d(M){n}` is proved objectwise; its naturality in `M` (and
hence the naturality of the composite `⊕ 𝓕_d(M){n} ≅ ⊕ 𝓕_{d'}(M){n'}`) is not formalized. The
natural isomorphism is between the functors `Ind (X ⊠ −)` and `Ind (X' ⊠ −)`.

As everywhere for `f`, the quantum Gabber–Kac theorem is an explicit hypothesis `hGK`.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open KLRAlgebra MulOpposite Graded

namespace GradingDatum

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q)

/-! ### Transport along equalities of weights -/

section Cast

variable {G}

/-- Transport of a graded `R(μ)`-module along `μ = μ'`. -/
def castGMod {μ μ' : Multiset I} (h : μ = μ') (M : GMod (G.grade μ)) : GMod (G.grade μ') :=
  h ▸ M

@[simp] theorem castGMod_rfl {μ : Multiset I} (M : GMod (G.grade μ)) : castGMod rfl M = M := rfl

/-- `castGMod h' (castGMod h M) ≅ castGMod (h.trans h') M`. -/
def castGModTransIso {μ μ' μ'' : Multiset I} (h : μ = μ') (h' : μ' = μ'')
    (M : GMod (G.grade μ)) : (castGMod h' (castGMod h M)).Iso (castGMod (h.trans h') M) := by
  subst h; subst h'; exact GradedEquiv.refl _

/-- Transport of an isomorphism. -/
def castGModIso {μ μ' : Multiset I} (h : μ = μ') {M N : GMod (G.grade μ)} (e : M.Iso N) :
    (castGMod h M).Iso (castGMod h N) := by
  subst h; exact e

/-- An isomorphism of underlying `k`-modules which is semilinear along `castKLR : R(μ) ≃ R(μ')`
and degree-preserving is a graded isomorphism `castGMod h X ≅ Y`. -/
def castGModIsoOfLinearEquiv {μ μ' : Multiset I} (h : μ = μ') (X : GMod (G.grade μ))
    (Y : GMod (G.grade μ')) (φ : X.carrier ≃ₗ[k] Y.carrier)
    (hφ : ∀ (b : KLRAlgebra k Q μ) (x : X.carrier), φ (b • x) = castKLR Q h b • φ x)
    (hgr : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → φ x ∈ Y.grading d) :
    (castGMod h X).Iso Y := by
  subst h
  exact GradedEquiv.ofPreserves
    (φ.toAddEquiv.toLinearEquiv fun b x => (hφ b x).trans (by rw [castKLR_rfl]; rfl))
    (fun _ _ hx => hgr hx)

end Cast

/-! ### Induction of graded modules -/

section IndGMod

variable {μ ν : Multiset I}

/-- **`Ind_{μ,ν} (X ⊠ M)`** for graded modules `X ∈ R(μ)-gmod`, `M ∈ R(ν)-gmod`, as a graded
`R(μ + ν)`-module (KL I §2.6). -/
def indGMod (X : GMod (G.grade μ)) (M : GMod (G.grade ν)) : GMod (G.grade (μ + ν)) where
  carrier := Ind Q μ ν (ExtTensor k X.carrier M.carrier)
  grading := G.indGrading μ ν (ExtTensor.grading X.grading M.grading)
  decomposition := balancedDecomposition (tensorGrading (G.grade μ) (G.grade ν))
    (fun _ _ _ _ hm ht => G.op_smul_mem_bimodGrading hm ht)
  gradedSMul := gradedSMul_balanced (G.grade (μ + ν))

theorem indProj_toGMod (P : GProj (G.grade μ)) (P' : GProj (G.grade ν)) :
    (G.indProj P P').toGMod = G.indGMod P.toGMod P'.toGMod := rfl

/-- `Ind (X ⊠ f)` for an `R(ν)`-linear map `f : M → M'`. -/
def indGModMap (X : GMod (G.grade μ)) {M M' : GMod (G.grade ν)} (f : M.carrier →ₗ[KLRAlgebra k Q ν] M'.carrier) :
    (G.indGMod X M).carrier →ₗ[KLRAlgebra k Q (μ + ν)] (G.indGMod X M').carrier :=
  BalancedTensor.mapRight (ExtTensor.map LinearMap.id f)

@[simp] theorem indGModMap_tmul (X : GMod (G.grade μ)) {M M' : GMod (G.grade ν)}
    (f : M.carrier →ₗ[KLRAlgebra k Q ν] M'.carrier) (r : IndBimod Q μ ν) (x : X.carrier)
    (m : M.carrier) :
    G.indGModMap X f (BalancedTensor.tmul r (ExtTensor.tmul x m)) =
      BalancedTensor.tmul r (ExtTensor.tmul x (f m)) := rfl

theorem indGModMap_id (X : GMod (G.grade μ)) (M : GMod (G.grade ν)) :
    G.indGModMap X (LinearMap.id : M.carrier →ₗ[KLRAlgebra k Q ν] M.carrier) = LinearMap.id := by
  rw [indGModMap, ExtTensor.map_id, BalancedTensor.mapRight_id]

theorem indGModMap_comp (X : GMod (G.grade μ)) {M M' M'' : GMod (G.grade ν)}
    (f : M.carrier →ₗ[KLRAlgebra k Q ν] M'.carrier)
    (g : M'.carrier →ₗ[KLRAlgebra k Q ν] M''.carrier) :
    G.indGModMap X (g.comp f) = (G.indGModMap X g).comp (G.indGModMap X f) := by
  rw [indGModMap, indGModMap, indGModMap, ← BalancedTensor.mapRight_comp, ← ExtTensor.map_comp,
    LinearMap.id_comp]

/-- `Ind (X ⊠ f)` is degree-preserving if `f` is. -/
theorem indGModMap_preservesGrading (X : GMod (G.grade μ)) {M M' : GMod (G.grade ν)}
    {f : M.carrier →ₗ[KLRAlgebra k Q ν] M'.carrier} (hf : PreservesGrading M.grading M'.grading f) :
    PreservesGrading (G.indGMod X M).grading (G.indGMod X M').grading (G.indGModMap X f) :=
  fun _ _ hy => mapRight_mem_balancedGrading (B := KLRAlgebra k Q (μ + ν))
    (ℳ := G.bimodGrading μ ν)
    (ExtTensor.map_preservesGrading (f := (LinearMap.id : X.carrier →ₗ[KLRAlgebra k Q μ] _))
      (fun _ _ h => h) hf) hy

/-- **`Ind (X ⊠ M) ≅ Ind (X' ⊠ M)`** for an isomorphism `e : X ≅ X'`. -/
def indGModCongrLeft {X X' : GMod (G.grade μ)} (e : X.Iso X') (M : GMod (G.grade ν)) :
    (G.indGMod X M).Iso (G.indGMod X' M) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr e.toLinearEquiv
    (LinearEquiv.refl _ M.carrier))) fun _ y hy =>
      mapRight_mem_balancedGrading (B := KLRAlgebra k Q (μ + ν)) (ℳ := G.bimodGrading μ ν)
        (ExtTensor.map_preservesGrading e.preservesGrading (fun _ _ h => h)) (y := y) hy

/-- `Ind (X ⊠ M) ≅ Ind (X ⊠ M')` for an isomorphism `e : M ≅ M'`. -/
def indGModCongrRight (X : GMod (G.grade μ)) {M M' : GMod (G.grade ν)} (e : M.Iso M') :
    (G.indGMod X M).Iso (G.indGMod X M') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr
    (LinearEquiv.refl _ X.carrier) e.toLinearEquiv)) fun _ y hy =>
      mapRight_mem_balancedGrading (B := KLRAlgebra k Q (μ + ν)) (ℳ := G.bimodGrading μ ν)
        (ExtTensor.map_preservesGrading (fun _ _ h => h) e.preservesGrading) (y := y) hy

/-- **Naturality**: the isomorphism `Ind (X ⊠ M) ≅ Ind (X' ⊠ M)` induced by `e : X ≅ X'`
commutes with `Ind (X ⊠ f)`, `Ind (X' ⊠ f)` for every `R(ν)`-linear `f : M → M'`. -/
theorem indGModCongrLeft_naturality {X X' : GMod (G.grade μ)} (e : X.Iso X')
    {M M' : GMod (G.grade ν)} (f : M.carrier →ₗ[KLRAlgebra k Q ν] M'.carrier)
    (y : (G.indGMod X M).carrier) :
    G.indGModCongrLeft e M' (G.indGModMap X f y) =
      G.indGModMap X' f (G.indGModCongrLeft e M y) := by
  change BalancedTensor.mapRight _ (BalancedTensor.mapRight _ y) =
    BalancedTensor.mapRight _ (BalancedTensor.mapRight _ y)
  rw [← LinearMap.comp_apply, ← BalancedTensor.mapRight_comp, ← LinearMap.comp_apply,
    ← BalancedTensor.mapRight_comp]
  congr 2
  change ExtTensor.map _ _ ∘ₗ ExtTensor.map _ _ = ExtTensor.map _ _ ∘ₗ ExtTensor.map _ _
  rw [← ExtTensor.map_comp, ← ExtTensor.map_comp]
  rfl

/-- `Ind ((X₁ ⊕ X₂) ⊠ M) ≅ Ind (X₁ ⊠ M) ⊕ Ind (X₂ ⊠ M)`. -/
def indGModProdLeft (X₁ X₂ : GMod (G.grade μ)) (M : GMod (G.grade ν)) :
    (G.indGMod (X₁.prod X₂) M).Iso ((G.indGMod X₁ M).prod (G.indGMod X₂ M)) :=
  let e := (BalancedTensor.congrRight (ExtTensor.prodLeft (k := k)
    (P := X₁.carrier) (P' := X₂.carrier) (Q := M.carrier) (A := KLRAlgebra k Q μ)
    (B := KLRAlgebra k Q ν))).trans
      (BalancedTensor.prodRight _ _ _ _ _ _)
  GradedEquiv.ofPreserves e fun _ y hy => balancedGrading_map_mem (B := KLRAlgebra k Q (μ + ν))
      (ℳ := G.bimodGrading μ ν)
      (Graded.prod (G.indGMod X₁ M).grading (G.indGMod X₂ M).grading)
      (e.toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => mem_prod.2
        ⟨tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading
          (𝒰 := Graded.prod X₁.grading X₂.grading)
          (𝒱 := M.grading) (𝒰' := X₁.grading)
          (f := LinearMap.fst _ X₁.carrier X₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.1) (fun _ _ h => h) hn),
         tmul_mem_balancedGrading hm (ExtTensor.map_preservesGrading
          (𝒰 := Graded.prod X₁.grading X₂.grading)
          (𝒱 := M.grading) (𝒰' := X₂.grading)
          (f := LinearMap.snd _ X₁.carrier X₂.carrier) (g := LinearMap.id)
          (fun _ _ h => h.2) (fun _ _ h => h) hn)⟩) (y := y) hy

/-- `Ind (X{a} ⊠ M) ≅ Ind (X ⊠ M){a}`. -/
def indGModShiftLeft (X : GMod (G.grade μ)) (M : GMod (G.grade ν)) (a : ℤ) :
    (G.indGMod (X.shift a) M).Iso ((G.indGMod X M).shift a) :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight (ExtTensor.congr
      (LinearEquiv.refl (KLRAlgebra k Q μ) X.carrier)
      (LinearEquiv.refl _ M.carrier))) fun _ y hy => by
    have h := mapRight_mem_balancedGrading (B := KLRAlgebra k Q (μ + ν))
      (ℳ := G.bimodGrading μ ν) (𝒩' := ExtTensor.grading (shift X.grading a) M.grading)
      (ExtTensor.map_preservesGrading
        (f := (LinearEquiv.refl (KLRAlgebra k Q μ) X.carrier).toLinearMap)
        (𝒰 := shift X.grading a) (𝒰' := shift X.grading a)
        (fun _ _ h => h)
        (g := (LinearEquiv.refl (KLRAlgebra k Q ν) M.carrier).toLinearMap)
        (fun _ _ h => h)) (y := y) hy
    rw [ExtTensor.grading_shift_left, balancedGrading_shift_right] at h
    exact h

/-- `Ind (Z ⊠ M) = 0` if `Z = 0`. -/
instance subsingleton_indGMod (Z : GMod (G.grade μ)) [Subsingleton Z.carrier]
    (M : GMod (G.grade ν)) : Subsingleton (G.indGMod Z M).carrier := by
  have hE : Subsingleton (ExtTensor k Z.carrier M.carrier) := by
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ t : ExtTensor k Z.carrier M.carrier, t = 0 := fun t => by
      induction t using ExtTensor.induction_on with
      | zero => rfl
      | tmul z m =>
        rw [Subsingleton.elim z 0]
        exact TensorProduct.zero_tmul _ _
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h0 x, h0 y]
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ t : (G.indGMod Z M).carrier, t = 0 := fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rfl
    | tmul r z =>
      rw [Subsingleton.elim z 0]
      exact BalancedTensor.tmul_zero _
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [h0 x, h0 y]

/-- `Ind (castGMod h X ⊠ M) ≅ castGMod h (Ind (X ⊠ M))`. -/
def indGModCastLeft {μ' : Multiset I} (h : μ = μ') (X : GMod (G.grade μ)) (M : GMod (G.grade ν)) :
    (G.indGMod (castGMod h X) M).Iso (castGMod (congrArg (· + ν) h) (G.indGMod X M)) := by
  subst h; exact GradedEquiv.refl _

/-- **Associativity of induction** as a graded isomorphism:
`Ind (Ind (X₁ ⊠ X₂) ⊠ M) ≅ Ind (X₁ ⊠ Ind (X₂ ⊠ M))`, after transport along
`(μ₁ + μ₂) + ν = μ₁ + (μ₂ + ν)`. -/
def indGModAssocIso {μ₁ μ₂ : Multiset I} (X₁ : GMod (G.grade μ₁)) (X₂ : GMod (G.grade μ₂))
    (M : GMod (G.grade ν)) :
    (castGMod (add_assoc μ₁ μ₂ ν) (G.indGMod (G.indGMod X₁ X₂) M)).Iso
      (G.indGMod X₁ (G.indGMod X₂ M)) :=
  castGModIsoOfLinearEquiv _ _ _ (assocEquiv Q μ₁ μ₂ ν X₁.carrier X₂.carrier M.carrier)
    (fun b x => assocEquiv_smul X₁.carrier X₂.carrier M.carrier b x)
    (fun _ _ hx => G.assocFwd_mem_grading X₁.grading X₂.grading M.grading hx)

/-- **Unitality of induction** as a graded isomorphism: `Ind (R(0) ⊠ M) ≅ M`, after transport
along `0 + ν = ν`. -/
def indGModUnitIso (M : GMod (G.grade ν)) :
    (castGMod (zero_add ν) (G.indGMod (GMod.regular (G.grade 0)) M)).Iso M :=
  castGModIsoOfLinearEquiv _ _ _ (unitLEquiv Q ν M.carrier)
    (fun b x => unitLEquiv_smul M.carrier b x)
    (fun _ _ hx => G.unitLFwd_mem_grading M.grading hx)

end IndGMod

end GradingDatum

/-- Any two zero graded modules are isomorphic. -/
def _root_.Categorification.Graded.GMod.isoOfSubsingleton {k : Type*} [CommRing k] {A : Type*}
    [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A} (X Y : GMod 𝒜) [Subsingleton X.carrier]
    [Subsingleton Y.carrier] : X.Iso Y :=
  GradedEquiv.ofLinearMaps (0 : X.carrier →ₗ[A] Y.carrier) (0 : Y.carrier →ₗ[A] X.carrier)
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    (fun _ _ _ => by rw [LinearMap.zero_apply]; exact zero_mem _)
    (fun _ _ _ => by rw [LinearMap.zero_apply]; exact zero_mem _)

/-! ### The functors `𝓕_θ` on graded modules (KL I algebras) -/

namespace KLGamma

open LaurentPolynomial QuantumGroup GradingDatum

variable {I : Type*} [DecidableEq I] (k : Type*) [Field k] (Γ : SimpleGraph I)
  [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-- **`𝓕_i^{(a)} M = Ind (P_{i^{(a)}} ⊠ M)`** on graded modules, from `R(ν)-gmod` to
`R(ai + ν)-gmod` (KL I §3.2, TeX line ~2316). -/
def funFM (i : I) (a : ℕ) {ν : Multiset I} (M : GMod ((Gkl).grade ν)) :
    GMod ((Gkl).grade (wtDiv [(i, a)] + ν)) :=
  (Gkl).indGMod (projDiv k Γ [(i, a)] rfl).toGMod M

/-- **`𝓕_θ = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}`** on graded modules (KL I §3.2, TeX lines
~2321–2324). -/
def funThetaM : (d : List (I × ℕ)) → {ν : Multiset I} → GMod ((Gkl).grade ν) →
    GMod ((Gkl).grade (wtDiv d + ν))
  | [], _, M => castGMod (by rw [wtDiv_nil, zero_add]) M
  | q :: d, _, M => castGMod (by rw [wtDiv_cons q d, add_assoc]) (funFM k Γ q.1 q.2 (funThetaM d M))

/-- `P_∅ ≅ R(0)`. -/
theorem nonempty_iso_projDiv_nil :
    Nonempty ((projDiv k Γ [] rfl).Iso (GProj.regular ((Gkl).grade 0))) := by
  refine K0.of_eq_of_iff.1 (DirectSum.of_injective (β := (Gkl).K0fam) 0 ?_)
  exact (clsDiv_nil k Γ).trans (Gkl).K0R_one

theorem castProj_toGMod {μ μ' : Multiset I} (h : μ = μ') (P : GProj ((Gkl).grade μ)) :
    (castProj h P).toGMod = castGMod h P.toGMod := by
  subst h; rfl

/-- `P_{i^{(a)} d} ≅ Ind (P_{i^{(a)}} ⊠ P_d)` (from `[P_{i^{(a)} d}] = [P_{i^{(a)}}] [P_d]` and
Krull–Schmidt), transported to the weight `|i^{(a)} d|`. -/
theorem nonempty_iso_projDiv_cons (q : I × ℕ) (d : List (I × ℕ)) :
    Nonempty ((projDiv k Γ (q :: d) rfl).toGMod.Iso
      (castGMod (wtDiv_cons q d).symm
        ((Gkl).indGMod (projDiv k Γ [q] rfl).toGMod (projDiv k Γ d rfl).toGMod))) := by
  obtain ⟨e⟩ := K0.of_eq_of_iff.1 (DirectSum.of_injective (β := (Gkl).K0fam) (wtDiv (q :: d))
    (show DirectSum.of (Gkl).K0fam (wtDiv (q :: d)) (K0.of (projDiv k Γ (q :: d) rfl)) =
      DirectSum.of (Gkl).K0fam (wtDiv (q :: d)) (K0.of (castProj (wtDiv_cons q d).symm
        ((Gkl).indProj (projDiv k Γ [q] rfl) (projDiv k Γ d rfl)))) by
      rw [of_castProj, ← (Gkl).K0R_of_of_mul_of_of]
      exact clsDiv_cons k Γ q d))
  change (projDiv k Γ (q :: d) rfl).toGMod.Iso (castProj _ _).toGMod at e
  rw [castProj_toGMod] at e
  exact ⟨e⟩

/-- `castGMod h X ≅ X` for `h : μ = μ`. -/
def castGModSelfIso {μ : Multiset I} (h : μ = μ) (X : GMod ((Gkl).grade μ)) :
    (castGMod h X).Iso X :=
  GradedEquiv.refl _

/-- **`Ind (P_θ ⊠ M) ≅ 𝓕_θ(M)`** for every graded module `M` and every divided-power
monomial `θ = d`. -/
def indProjDivIso : (d : List (I × ℕ)) → {ν : Multiset I} → (M : GMod ((Gkl).grade ν)) →
    ((Gkl).indGMod (projDiv k Γ d rfl).toGMod M).Iso (funThetaM k Γ d M)
  | [], ν, M =>
    ((Gkl).indGModCongrLeft (nonempty_iso_projDiv_nil k Γ).some M).trans
      ((castGModSelfIso k Γ rfl _).symm.trans
        ((castGModTransIso (zero_add ν) (zero_add ν).symm _).symm.trans
          (castGModIso (zero_add ν).symm ((Gkl).indGModUnitIso M))))
  | q :: d, ν, M =>
    ((Gkl).indGModCongrLeft (nonempty_iso_projDiv_cons k Γ q d).some M).trans <|
      ((Gkl).indGModCastLeft (wtDiv_cons q d).symm _ M).trans <|
        (castGModTransIso (add_assoc (wtDiv [q]) (wtDiv d) ν)
          (by rw [wtDiv_cons q d, add_assoc]) _).symm.trans <|
          (castGModIso (by rw [wtDiv_cons q d, add_assoc])
            ((Gkl).indGModAssocIso (projDiv k Γ [q] rfl).toGMod (projDiv k Γ d rfl).toGMod M)).trans <|
            castGModIso (by rw [wtDiv_cons q d, add_assoc])
              ((Gkl).indGModCongrRight (projDiv k Γ [q] rfl).toGMod (indProjDivIso d M))

/-- `Ind (P_d ⊠ M) ≅ 𝓕_d(M)` for `P_d = projDiv d h` of any weight `μ = |d|`. -/
def indProjDivIso' {μ ν : Multiset I} (d : List (I × ℕ)) (h : wtDiv d = μ)
    (M : GMod ((Gkl).grade ν)) :
    ((Gkl).indGMod (projDiv k Γ d h).toGMod M).Iso
      (castGMod (congrArg (· + ν) h) (funThetaM k Γ d M)) := by
  subst h; exact indProjDivIso k Γ d M

/-! ### Theorem 3.21 on graded modules -/

/-- **`⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(M){n}`** for a graded `R(ν)`-module `M` (the weight-`(μ + ν)`
part of `⊕_k 𝓕_{θ(k)}^{⊕ u_k} M`). -/
def sumFM (μ : Multiset I) {ν : Multiset I} (M : GMod ((Gkl).grade ν)) :
    List (ℤ × List (I × ℕ)) → GMod ((Gkl).grade (μ + ν))
  | [] => (GProj.zeroObj ((Gkl).grade (μ + ν))).toGMod
  | x :: L =>
    if h : wtDiv x.2 = μ then
      ((castGMod (congrArg (· + ν) h) (funThetaM k Γ x.2 M)).shift x.1).prod (sumFM μ M L)
    else sumFM μ M L

/-- **`Ind (X ⊠ M) ≅ ⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(M){n}`** for `X = ⊕_{(n, d) ∈ L, |d| = μ} P_d{n}`
(`sumP`) and every graded module `M`. -/
def indSumPIso (μ : Multiset I) {ν : Multiset I} (M : GMod ((Gkl).grade ν)) :
    (L : List (ℤ × List (I × ℕ))) → ((Gkl).indGMod (sumP k Γ μ L).toGMod M).Iso (sumFM k Γ μ M L)
  | [] => by
    haveI : Subsingleton (sumP k Γ μ []).toGMod.carrier :=
      inferInstanceAs (Subsingleton (GProj.zeroObj ((Gkl).grade μ)).carrier)
    haveI : Subsingleton (sumFM k Γ μ M []).carrier :=
      inferInstanceAs (Subsingleton (GProj.zeroObj ((Gkl).grade (μ + ν))).carrier)
    exact GMod.isoOfSubsingleton _ _
  | x :: L =>
    if h : wtDiv x.2 = μ then by
      rw [sumP, sumFM, dif_pos h, dif_pos h]
      exact ((Gkl).indGModProdLeft _ _ M).trans (GradedEquiv.prodCongr
        (((Gkl).indGModShiftLeft _ M x.1).trans ((indProjDivIso' k Γ x.2 h M).shift x.1))
        (indSumPIso μ M L))
    else by
      rw [sumP, sumFM, dif_neg h, dif_neg h]
      exact indSumPIso μ M L

/-- **KL I, Theorem 3.21 (isomorphism of functors)**: for a relation
`∑_{(n, d) ∈ L} q^n θ_d = ∑_{(n', d') ∈ L'} q^{n'} θ_{d'}` in `_𝒜 f` and a weight `μ`, the
isomorphism of projectives `X ≅ X'` (`theorem_3_21_proj`, `X = ⊕_{|d| = μ} P_d{n}`,
`X' = ⊕_{|d'| = μ} P_{d'}{n'}`) induces isomorphisms `Ind (X ⊠ M) ≅ Ind (X' ⊠ M)` for all graded
modules `M`. They are natural in `M` (`theorem_3_21_natIso_naturality`). -/
def theorem_3_21_natIso (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I)
    {ν : Multiset I} (M : GMod ((Gkl).grade ν)) :
    ((Gkl).indGMod (sumP k Γ μ L).toGMod M).Iso ((Gkl).indGMod (sumP k Γ μ L').toGMod M) :=
  (Gkl).indGModCongrLeft (theorem_3_21_proj k Γ hGK hrel μ).some M

/-- Naturality of `theorem_3_21_natIso` in `M`: it commutes with `Ind (X ⊠ f)`, `Ind (X' ⊠ f)` for
every `R(ν)`-linear `f : M → M'`. -/
theorem theorem_3_21_natIso_naturality (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I)
    {ν : Multiset I} {M M' : GMod ((Gkl).grade ν)}
    (f : M.carrier →ₗ[KLRAlgebra k (klQ Γ) ν] M'.carrier)
    (y : ((Gkl).indGMod (sumP k Γ μ L).toGMod M).carrier) :
    theorem_3_21_natIso k Γ hGK hrel μ M' ((Gkl).indGModMap _ f y) =
      (Gkl).indGModMap _ f (theorem_3_21_natIso k Γ hGK hrel μ M y) :=
  (Gkl).indGModCongrLeft_naturality _ f y

/-- **KL I, Theorem 3.21 on all graded modules (objectwise)**: for a relation
`∑_{(n, d) ∈ L} q^n θ_d = ∑_{(n', d') ∈ L'} q^{n'} θ_{d'}` in `_𝒜 f` (coefficients in
`ℕ[q, q⁻¹]`), every weight `μ` and every graded `R(ν)`-module `M` (not necessarily finitely
generated or projective),
`⊕_{(n, d) ∈ L, |d| = μ} 𝓕_d(M){n} ≅ ⊕_{(n', d') ∈ L', |d'| = μ} 𝓕_{d'}(M){n'}`
as graded `R(μ + ν)`-modules, where `𝓕_d = 𝓕_{i_1}^{(a_1)} ∘ ⋯ ∘ 𝓕_{i_r}^{(a_r)}`. -/
theorem theorem_3_21_gmod (hGK : PreF.GabberKac (KL.C Γ).dot vQ (KL.C Γ).c)
    {L L' : List (ℤ × List (I × ℕ))} (hrel : relSum Γ L = relSum Γ L') (μ : Multiset I)
    {ν : Multiset I} (M : GMod ((Gkl).grade ν)) :
    Nonempty ((sumFM k Γ μ M L).Iso (sumFM k Γ μ M L')) :=
  ⟨(indSumPIso k Γ μ M L).symm.trans
    ((theorem_3_21_natIso k Γ hGK hrel μ M).trans (indSumPIso k Γ μ M L'))⟩

end KLGamma

end Categorification.KLR
