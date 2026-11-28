/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndLayerMap
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingRange

/-!
# Module maps on the layers of a partial standardization at a cut

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the cut side of
(T_w) in the form of the partial standardization).

A module map `g : N → N` over the factor algebras of a cut preserves the Mackey filtration of
`Ind N` and of `𝕊(N)` (`cutShuffleMap_mem_indMackeyFiltLower`,
`cutStandardMap_mem_cutMackeyFiltLower`), so it acts on their layers (`cutShuffleLayerMap`,
`cutStandardLayerMap`). The layer map `Ind → 𝕊` intertwines the two actions, `indLayerCastEquiv`
carries the first to `KLRAlgebra.indMackeyLayerMap`, and both commute with the elements
preserving the filtration. For an idempotent `g` and an ordered loading `l`, the corner
equivalence `cutLoadingIndLayerEquiv` therefore restricts to
`g · e(l) · 𝕊Lay ≃ g · e(l) · Lay` (`cutLoadingIndLayerMapEquiv`).

Webster's proof does not spell this out. No new hypothesis.

## Main definitions

* `Categorification.submoduleEquivOfMemIff`, `Stendhal.cutShuffleLayerMap`,
  `Stendhal.cutStandardLayerMap`, `Stendhal.cutLoadingIndLayerMapEquiv`.

## Main results

* `Categorification.mem_map_range_iff_of_comm`, `Categorification.map_mem_range_of_comm`,
  `Categorification.apply_eq_of_mem_range_of_idem`.
* `Stendhal.cutMackeyLayerMap_cutShuffleLayerMap`, `Stendhal.indLayerCastEquiv_cutShuffleLayerMap`,
  `Stendhal.cutShuffleLayerMap_act`, `Stendhal.cutStandardLayerMap_act`,
  `Stendhal.cutStandardLayerMap_idem`, `Stendhal.cutLayerAct_e_idem`,
  `Stendhal.cutLoadingIndLayerEquiv_layerMap`.
-/

noncomputable section

namespace Categorification

/-- For commuting idempotents `C`, `E`: `x ∈ E(range C) ↔ C x = x ∧ E x = x`. -/
theorem mem_map_range_iff_of_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (C E : M →ₗ[R] M) (hCE : ∀ x, C (E x) = E (C x)) (hC : ∀ x, C (C x) = C x)
    (hE : ∀ x, E (E x) = E x) (x : M) :
    x ∈ (LinearMap.range C).map E ↔ C x = x ∧ E x = x := by
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨by rw [hCE, hC], hE _⟩
  · rintro ⟨h1, h2⟩
    exact ⟨C x, ⟨x, rfl⟩, by rw [h1, h2]⟩

/-- A map commuting with `C` preserves `range C`. -/
theorem map_mem_range_of_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (C E : M →ₗ[R] M) (hCE : ∀ x, E (C x) = C (E x)) {x : M} (hx : x ∈ LinearMap.range C) :
    E x ∈ LinearMap.range C := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨E t, (hCE t).symm⟩

theorem map_range_le_range_of_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (C E : M →ₗ[R] M) (hCE : ∀ x, E (C x) = C (E x)) :
    (LinearMap.range C).map E ≤ LinearMap.range C := by
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_range_of_comm C E hCE hx

theorem apply_eq_of_mem_range_of_idem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (C : M →ₗ[R] M) (hC : ∀ x, C (C x) = C x) {x : M}
    (hx : x ∈ LinearMap.range C) : C x = x := by
  obtain ⟨t, rfl⟩ := hx
  exact hC t

/-- A linear equivalence `A ≃ B` of submodules restricts to `P ≃ P'` for `P ≤ A`, `P' ≤ B` with
`a ∈ P ↔ E a ∈ P'`. -/
def submoduleEquivOfMemIff {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] {A P : Submodule R M} {B P' : Submodule R M'}
    (E : A ≃ₗ[R] B) (hP : P ≤ A) (hP' : P' ≤ B)
    (h : ∀ a : A, (a : M) ∈ P ↔ (E a : M') ∈ P') : P ≃ₗ[R] P' where
  toFun p := ⟨E ⟨p, hP p.2⟩, (h _).1 p.2⟩
  map_add' p p' := Subtype.ext (by
    change (E (⟨p, hP p.2⟩ + ⟨p', hP p'.2⟩) : M') = _
    rw [map_add]
    rfl)
  map_smul' c p := Subtype.ext (by
    change (E (c • ⟨p, hP p.2⟩) : M') = _
    rw [map_smul]
    rfl)
  invFun p' := ⟨E.symm ⟨p', hP' p'.2⟩,
    (h _).2 (by rw [LinearEquiv.apply_symm_apply]; exact p'.2)⟩
  left_inv p := Subtype.ext (by
    change ((E.symm (E ⟨p, hP p.2⟩)) : M) = p
    rw [LinearEquiv.symm_apply_apply])
  right_inv p' := Subtype.ext (by
    change ((E (E.symm ⟨p', hP' p'.2⟩)) : M') = p'
    rw [LinearEquiv.apply_symm_apply])

theorem submoduleEquivOfMemIff_apply {R M M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] {A P : Submodule R M} {B P' : Submodule R M'}
    (E : A ≃ₗ[R] B) (hP : P ≤ A) (hP' : P' ≤ B)
    (h : ∀ a : A, (a : M) ∈ P ↔ (E a : M') ∈ P') (p : P) :
    (submoduleEquivOfMemIff E hP hP' h p : M') = E ⟨p, hP p.2⟩ :=
  rfl

namespace Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable (g : N →ₗ[cutFactorAlgebra Q Λ θ β] N)

theorem cutShuffleMap_mem_indMackeyFilt {n c : ℕ} {y : CutShuffle Q Λ θ β N}
    (hy : y ∈ indMackeyFilt Q Λ θ β N n c) :
    cutShuffleMap Q Λ θ β g y ∈ indMackeyFilt Q Λ θ β N n c :=
  mapRight_mem_indMackeyStep (cutInputHom Q Λ θ β g) hy

theorem cutShuffleMap_mem_indMackeyFiltLower {n c : ℕ} {y : CutShuffle Q Λ θ β N}
    (hy : y ∈ indMackeyFiltLower Q Λ θ β N n c) :
    cutShuffleMap Q Λ θ β g y ∈ indMackeyFiltLower Q Λ θ β N n c := by
  cases c with
  | zero =>
    change y ∈ (⊥ : Submodule k _) at hy
    rw [Submodule.mem_bot] at hy
    rw [hy, map_zero]
    exact zero_mem _
  | succ c => exact cutShuffleMap_mem_indMackeyFilt g hy

/-- The lower steps of the Mackey filtration of `𝕊(N)` are natural in `N`. -/
theorem cutStandardMap_mem_cutMackeyFiltLower {n c : ℕ} {v : CutStandard Q Λ θ β N}
    (hv : v ∈ cutMackeyFiltLower Q Λ θ β N n c) :
    cutStandardMap Q Λ θ β g v ∈ cutMackeyFiltLower Q Λ θ β N n c := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨cutShuffleMap Q Λ θ β g y, cutShuffleMap_mem_indMackeyFiltLower g hy, rfl⟩

theorem cutShuffleMap_idem (hg : ∀ x, g (g x) = g x) (y : CutShuffle Q Λ θ β N) :
    cutShuffleMap Q Λ θ β g (cutShuffleMap Q Λ θ β g y) = cutShuffleMap Q Λ θ β g y := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b x =>
    rw [cutShuffleMap, BalancedTensor.mapRight_tmul, BalancedTensor.mapRight_tmul]
    exact congrArg (BalancedTensor.tmul b) (hg x)
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

variable (n c : ℕ)

/-- The action of a module map `g` on the layer `F_c / F_{c-1}` of `Ind N`. -/
def cutShuffleLayerMap :
    SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) →ₗ[k]
      SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c) :=
  subLayerAct ((cutShuffleMap Q Λ θ β g).restrictScalars k)
    (fun _ hy => cutShuffleMap_mem_indMackeyFilt g hy)
    (fun _ hy => cutShuffleMap_mem_indMackeyFiltLower g hy)

/-- **The action of a module map** `g` on the layer `F_c(𝕊) / F_{c-1}(𝕊)` of `𝕊(N)`. -/
def cutStandardLayerMap :
    SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) →ₗ[k]
      SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c) :=
  subLayerAct (cutStandardMap Q Λ θ β g)
    (fun _ hv => cutStandardMap_mem_cutMackeyFilt g hv)
    (fun _ hv => cutStandardMap_mem_cutMackeyFiltLower g hv)

/-- The layer map `Ind → 𝕊` intertwines the actions of `g`. -/
theorem cutMackeyLayerMap_cutShuffleLayerMap
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    cutMackeyLayerMap Q Λ θ β N n c (cutShuffleLayerMap g n c y) =
      cutStandardLayerMap g n c (cutMackeyLayerMap Q Λ θ β N n c y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

/-- `indLayerCastEquiv` carries the action of `g` to `KLRAlgebra.indMackeyLayerMap`. -/
theorem indLayerCastEquiv_cutShuffleLayerMap
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    indLayerCastEquiv Q Λ θ β N n c (cutShuffleLayerMap g n c y) =
      indMackeyLayerMap (cutInputHom Q Λ θ β g) n c (indLayerCastEquiv Q Λ θ β N n c y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

variable {n} in
/-- The action of `g` on the layers of `Ind N` commutes with the elements preserving the
filtration. -/
theorem cutShuffleLayerMap_act {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z)
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    cutShuffleLayerMap g n c (indLayerAct hz c y) =
      indLayerAct hz c (cutShuffleLayerMap g n c y) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  exact (cutShuffleMap Q Λ θ β g).map_smul z (v : CutShuffle Q Λ θ β N)

variable (hQ : KLRSymm Q)

theorem cutStandardLayerMap_mk (v : cutMackeyFilt Q Λ θ β N n c) :
    cutStandardLayerMap g n c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g v,
        cutStandardMap_mem_cutMackeyFilt g v.2⟩ :=
  rfl

variable {n} in
theorem cutStandardLayerMap_act {z : KLRAlgebra k S (α + δ)}
    (hz : PreservesMackeyFilt n (Multiset.card α) z)
    (y : SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c)) :
    cutStandardLayerMap g n c (cutLayerAct hQ hz c y) =
      cutLayerAct hQ hz c (cutStandardLayerMap g n c y) := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
  have h1 : cutLayerAct hQ hz c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) v,
        cutMackeyFilt_action hQ hz v.2⟩ := rfl
  have h2 : cutStandardLayerMap g n c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g v,
        cutStandardMap_mem_cutMackeyFilt g v.2⟩ := rfl
  have h := cutStandardMap_action Q Λ θ β hQ g (affineToTensor Q Λ θ β z)
    (v : CutStandard Q Λ θ β N)
  have h3 : cutStandardLayerMap g n c (Submodule.Quotient.mk
      ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) v,
        cutMackeyFilt_action hQ hz v.2⟩) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g
        (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) v),
        cutStandardMap_mem_cutMackeyFilt g (cutMackeyFilt_action hQ hz v.2)⟩ := rfl
  have h4 : cutLayerAct hQ hz c (Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g v,
        cutStandardMap_mem_cutMackeyFilt g v.2⟩) =
      Submodule.Quotient.mk ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z)
        (cutStandardMap Q Λ θ β g v),
        cutMackeyFilt_action hQ hz (cutStandardMap_mem_cutMackeyFilt g v.2)⟩ := rfl
  exact (congrArg (cutStandardLayerMap g n c) h1).trans (h3.trans
    ((congrArg Submodule.Quotient.mk (Subtype.ext h)).trans
      (h4.symm.trans (congrArg (cutLayerAct hQ hz c) h2).symm)))

/-- For idempotent `g` the action on the layers of `𝕊(N)` is idempotent. -/
theorem cutStandardLayerMap_idem (hg : ∀ x, g (g x) = g x)
    (y : SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c)) :
    cutStandardLayerMap g n c (cutStandardLayerMap g n c y) = cutStandardLayerMap g n c y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
  have h2 : cutStandardLayerMap g n c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g v,
        cutStandardMap_mem_cutMackeyFilt g v.2⟩ := rfl
  have h2' : cutStandardLayerMap g n c (Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g v,
        cutStandardMap_mem_cutMackeyFilt g v.2⟩) =
      Submodule.Quotient.mk ⟨cutStandardMap Q Λ θ β g (cutStandardMap Q Λ θ β g v),
        cutStandardMap_mem_cutMackeyFilt g (cutStandardMap_mem_cutMackeyFilt g v.2)⟩ := rfl
  have hgg : cutStandardMap Q Λ θ β g (cutStandardMap Q Λ θ β g (v : CutStandard Q Λ θ β N)) =
      cutStandardMap Q Λ θ β g v := by
    obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ (v : CutStandard Q Λ θ β N)
    rw [← hu]
    exact congrArg (Submodule.mkQ _) (cutShuffleMap_idem g hg u)
  exact (congrArg (cutStandardLayerMap g n c) h2).trans
    (h2'.trans ((congrArg Submodule.Quotient.mk (Subtype.ext hgg)).trans h2.symm))

variable {n} in
/-- `e(l)` acts idempotently on the layers of `𝕊(N)`. -/
theorem cutLayerAct_e_idem (l : Seq (α + δ))
    (y : SubLayer (cutMackeyFilt Q Λ θ β N n c) (cutMackeyFiltLower Q Λ θ β N n c)) :
    cutLayerAct hQ (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c
        (cutLayerAct hQ (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c
          y) =
      cutLayerAct hQ (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c
        y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
  have h1 : cutLayerAct hQ (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l)
      c (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l)) v,
        cutMackeyFilt_action hQ (preservesMackeyFilt_e l) v.2⟩ := rfl
  have h1' : cutLayerAct hQ (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l)
      c (Submodule.Quotient.mk
        ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l)) v,
        cutMackeyFilt_action hQ (preservesMackeyFilt_e l) v.2⟩) =
      Submodule.Quotient.mk ⟨cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l))
        (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l)) v),
        cutMackeyFilt_action hQ (preservesMackeyFilt_e l)
          (cutMackeyFilt_action hQ (preservesMackeyFilt_e l) v.2)⟩ := rfl
  have hAA : cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l))
      (cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l)) (v : CutStandard Q Λ θ β N)) =
      cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β (e l)) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, e_mul_self]
  exact (congrArg _ h1).trans
    (h1'.trans ((congrArg Submodule.Quotient.mk (Subtype.ext hAA)).trans h1.symm))

theorem cutLoadingIndLayerEquiv_apply_cutLoadingLayerEquiv (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β)
    (u : LinearMap.range (indLayerAct (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c)) :
    (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c
        (cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c u) :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) =
      indLayerCastEquiv Q Λ θ β N n c u := by
  have h := cutLoadingIndLayerEquiv_symm_apply (Λ := Λ) (N := N) hQ l hl n c u
  have h' := ((LinearEquiv.symm_apply_eq _).1 h).symm
  exact congrArg Subtype.val h'

/-- **`cutLoadingIndLayerEquiv` intertwines the actions of `g`.** -/
theorem cutLoadingIndLayerEquiv_layerMap (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β)
    (y : LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c))
    (hy : cutStandardLayerMap g n c (y : SubLayer _ _) ∈ LinearMap.range (cutLayerAct hQ
        (N := N) (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c)) :
    (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c ⟨_, hy⟩ :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) =
      indMackeyLayerMap (cutInputHom Q Λ θ β g) n c
        (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c y) := by
  have hu1 : cutMackeyLayerMap Q Λ θ β N n c
      ((cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm y : SubLayer _ _) = y :=
    (cutLoadingLayerEquiv_apply (Λ := Λ) (N := N) hQ l hl n c
      ((cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm y)).symm.trans
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ y))
  have hmem : cutShuffleLayerMap g n c
      ((cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm y : SubLayer _ _) ∈
      LinearMap.range (indLayerAct (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c) :=
    map_mem_range_of_comm _ _ (cutShuffleLayerMap_act g c _)
      ((cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm y).2
  have hu2 : cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c ⟨_, hmem⟩ = ⟨_, hy⟩ :=
    Subtype.ext ((cutLoadingLayerEquiv_apply (Λ := Λ) (N := N) hQ l hl n c ⟨_, hmem⟩).trans
      ((cutMackeyLayerMap_cutShuffleLayerMap g n c _).trans
        (congrArg (cutStandardLayerMap g n c) hu1)))
  have e1 : (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c ⟨_, hy⟩ :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) =
      (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c
        (cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c ⟨_, hmem⟩) :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) :=
    congrArg (fun t : LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e
      (Q := S) (n := n) (n'' := Multiset.card α) l) c) =>
      (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c t :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c)) hu2.symm
  have e2 : (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c y :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) =
      (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c
        (cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c
          ((cutLoadingLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).symm y)) :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c) :=
    congrArg (fun t : LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e
      (Q := S) (n := n) (n'' := Multiset.card α) l) c) =>
      (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c t :
        IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c)) (LinearEquiv.apply_symm_apply _ y).symm
  exact e1.trans
    ((cutLoadingIndLayerEquiv_apply_cutLoadingLayerEquiv n c hQ l hl ⟨_, hmem⟩).trans
      ((indLayerCastEquiv_cutShuffleLayerMap g n c _).trans
        (congrArg (indMackeyLayerMap (cutInputHom Q Λ θ β g) n c)
          ((cutLoadingIndLayerEquiv_apply_cutLoadingLayerEquiv n c hQ l hl _).symm.trans
            e2.symm))))

/-- **The corner of an ordered loading moved by an idempotent module map** (Webster v3,
Lemma 7.19, trace half, step L5): for idempotent `g`, `cutLoadingIndLayerEquiv` restricts to
`g · (e(l) · 𝕊Lay) ≃ₗ g · (e(l) · Lay)`, the layers of `𝕊(N)` and of `Ind N`. -/
def cutLoadingIndLayerMapEquiv (hg : ∀ x, g (g x) = g x) (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β) :
    (LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c)).map (cutStandardLayerMap g n c) ≃ₗ[k]
      (LinearMap.range (indMackeyLayerAct (CutInput Q Λ θ β N) (e l)
        (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c)).map
        (indMackeyLayerMap (cutInputHom Q Λ θ β g) n c) :=
  submoduleEquivOfMemIff (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c)
    (map_range_le_range_of_comm _ _ (cutStandardLayerMap_act g c hQ _))
    (map_range_le_range_of_comm _ _ (indMackeyLayerMap_act (cutInputHom Q Λ θ β g) _ _ c))
    (fun y => by
      have hC := apply_eq_of_mem_range_of_idem _ (cutLayerAct_e_idem c hQ l) y.2
      have hy := map_mem_range_of_comm _ _ (cutStandardLayerMap_act g c hQ _) y.2
      have hC' := apply_eq_of_mem_range_of_idem _
        (indMackeyLayerAct_e_idem (CutInput Q Λ θ β N) l c)
        (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c y).2
      have hE := cutLoadingIndLayerEquiv_layerMap g n c hQ l hl y hy
      refine (mem_map_range_iff_of_comm _ _
          (fun t => (cutStandardLayerMap_act g c hQ _ t).symm)
          (cutLayerAct_e_idem c hQ l) (cutStandardLayerMap_idem g n c hg) _).trans
        (Iff.trans ?_ (mem_map_range_iff_of_comm _ _
          (fun t => (indMackeyLayerMap_act (cutInputHom Q Λ θ β g) _ _ c t).symm)
          (indMackeyLayerAct_e_idem (CutInput Q Λ θ β N) l c)
          (indMackeyLayerMap_idem (cutInputHom Q Λ θ β g) (LinearMap.ext fun x => hg x) n c)
          _).symm)
      refine ⟨fun h => ⟨hC', ?_⟩, fun h => ⟨hC, ?_⟩⟩
      · exact hE.symm.trans (congrArg (fun t : LinearMap.range (cutLayerAct hQ (N := N)
          (preservesMackeyFilt_e (Q := S) (n := n) (n'' := Multiset.card α) l) c) =>
          (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c t :
            IndMackeyLayer S α δ (CutInput Q Λ θ β N) n c)) (Subtype.ext h.2))
      · have h2 := (cutLoadingIndLayerEquiv (Λ := Λ) (N := N) hQ l hl n c).injective
          (Subtype.ext (hE.trans h.2))
        exact congrArg Subtype.val h2)

end Stendhal
end Categorification
