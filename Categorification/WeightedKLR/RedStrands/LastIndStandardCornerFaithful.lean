/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstIndCornerFaithful
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingChain
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

set_option backward.isDefEq.respectTransparency false

/-!
# `S(₂Fᵢ T^{λ'} e(t))` has no nonzero submodule killed by `e⁰`

Background for B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Theorem 5.30, (2) ⇒ (3), and Corollary 5.32 (v2: Theorem 5.27 and
Corollary 5.29). For a red-ordered red-first loading `t` of `T^{λ'}` and a colour `i`, the
standardization `S(₂Fᵢ T^{λ'} e(t))` has no nonzero submodule killed by the red-first idempotent
`e⁰` (`eq_zero_of_redFirstIdem_smul_lastIndStandardT`), at the standard Khovanov–Lauda
parameters.

The proof is by induction on the number of black strands of `t`. Without black strands, `e⁰`
acts as the identity (`isCornerFaithfulModule_lastIndBase`). Otherwise `t = (t', j)`, and

* `T^{λ'} e(t', j) ≅ ₁Fⱼ T^{λ'} e(t')` (`redFactorModuleAppendEquiv`);
* `₂Fᵢ ₁Fⱼ ≅ ₁Fⱼ ₂Fᵢ`, since the two inductions act on different tensor factors
  (`lastIndRightFirstIndLeftEquiv`);
* `δ₁ : S(₁Fⱼ Z) → Fⱼ S(Z)` is injective (proof of Proposition 5.5,
  `firstIndDeltaInjective_std`);
* `Fⱼ` preserves the property (`isCornerFaithfulModule_firstIndF`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong FirstWeight KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}

local notation "Si" j => (Singleton.singleton j : Multiset I)

section Commute

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- Appending black strands to the two tensor factors commutes. -/
theorem parabolicRightHom_comp_leftAppendHom (i j : I) (θ : Multiset I) :
    (parabolicRightHom Q Λ i ((Si j) + θ) 0).comp (leftAppendHom Q Λ j θ 0) =
      (leftAppendHom Q Λ j θ ((Si i) + 0)).comp (parabolicRightHom Q Λ i θ 0) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a c => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Induction along equal maps. -/
private def indCongrHom {A B : Type} [Ring A] [Ring B] {φ ψ : A →ₙ+* B} (h : φ = ψ)
    (N : Type) [AddCommGroup N] [Module A N] : Ind N φ ≃ₗ[B] Ind N ψ := by
  subst h; exact LinearEquiv.refl _ _

variable (θ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ 0) N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ 0) N]

/-- **`₂Fᵢ ₁Fⱼ N ≅ ₁Fⱼ ₂Fᵢ N`**: the two black inductions act on different tensor factors. -/
def lastIndRightFirstIndLeftEquiv (i j : I) :
    LastIndRight Q Λ i ((Si j) + θ) 0 (FirstIndLeft Q Λ j θ 0 N) ≃ₗ[
      parabolicFactorAlgebra Q Λ ((Si j) + θ) ((Si i) + 0)]
      FirstIndLeft Q Λ j θ ((Si i) + 0) (LastIndRight Q Λ i θ 0 N) :=
  ((compEquiv N (leftAppendHom Q Λ j θ 0) (parabolicRightHom Q Λ i ((Si j) + θ) 0)).trans
    (indCongrHom (parabolicRightHom_comp_leftAppendHom Q Λ i j θ) N)).trans
    (compEquiv N (parabolicRightHom Q Λ i θ 0) (leftAppendHom Q Λ j θ ((Si i) + 0))).symm

end Commute

section Conj

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (j : I) (θ : Multiset I)

local notation "old" => Λ ∘ Fin.castSucc

private theorem cast_cast_symm_apply {m : ℕ} (Λ' : Fin m → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (x : TensorProductAlgebra k Q Λ' ν') :
    castTensorProductAlgebra Q Λ' h (castTensorProductAlgebra Q Λ' h.symm x) = x := by
  subst h; rfl

/-- The idempotent of a loading, transported along an equality of black weights. -/
theorem castTensorProductAlgebra_mk_e {m : ℕ} (Λ' : Fin m → I →₀ ℕ) {ν ν' : Multiset I}
    (h : ν = ν') (s : Seq (stendhalWeight m ν)) (hs : IsRedOrdered s)
    (t : Seq (stendhalWeight m ν')) (ht : IsRedOrdered t)
    (hst : Seq.cast (congrArg (stendhalWeight m) h) s = t) :
    castTensorProductAlgebra Q Λ' h (TensorProductAlgebra.mk Q Λ' ν (StendhalAlgebra.e s hs)) =
      TensorProductAlgebra.mk Q Λ' ν' (StendhalAlgebra.e t ht) := by
  subst h; subst hst; rfl

/-- Appending the black strand `j` to `T^{λ'}`, landing in the weight `(j + θ) + 0`. -/
def appendBlackOldCast :
    TensorProductAlgebra k Q (old) (θ + 0) →ₙ+* TensorProductAlgebra k Q (old) (((Si j) + θ) + 0) :=
  (NonUnitalRingHomClass.toNonUnitalRingHom
    (castTensorProductAlgebra Q (old) (firstInd_blackWeight j θ 0))).comp
    (appendBlackOldHom Q Λ j (θ + 0))

theorem appendBlackOldCast_emptyFactorToOld (t : parabolicFactorAlgebra Q Λ θ 0) :
    appendBlackOldCast Q Λ j θ ((emptyFactorToOld Q Λ θ).toRingEquiv t) =
      (emptyFactorToOld Q Λ ((Si j) + θ)).toRingEquiv (leftAppendHom Q Λ j θ 0 t) := by
  change castTensorProductAlgebra Q (old) (firstInd_blackWeight j θ 0)
    (appendBlackOldHom Q Λ j (θ + 0) (emptyFactorToOld Q Λ θ t)) = _
  rw [appendBlackOld_emptyFactorToOld, emptyFactorToOldFirst, AlgEquiv.trans_apply,
    cast_cast_symm_apply]
  rfl

variable {θ}

/-- **`T^{λ'} e(t', j) ≅ ₁Fⱼ T^{λ'} e(t')`** as modules over `T^{λ'} ⊗ R^{λ_ℓ}_0`: appending a
black strand on the right is induction along `appendBlack` (Webster, arXiv:1309.3796v2, §4.6). -/
def redFactorModuleAppendEquiv {u' : Seq (stendhalWeight ℓ (θ + 0))} (hu' : IsRedOrdered u')
    {u : Seq (stendhalWeight ℓ (((Si j) + θ) + 0))} (hu : IsRedOrdered u)
    (hrel : appendBlackOldCast Q Λ j θ (oldIdem Q Λ θ u' hu') =
      oldIdem Q Λ ((Si j) + θ) u hu) :
    FirstIndLeft Q Λ j θ 0 (redFactorModule Q Λ θ u' hu').carrier ≃ₗ[
      parabolicFactorAlgebra Q Λ ((Si j) + θ) 0] (redFactorModule Q Λ ((Si j) + θ) u hu).carrier :=
  let e₀ : (redFactorModule Q Λ θ u' hu').carrier ≃+ lIdeal (oldIdem Q Λ θ u' hu') :=
    { toFun := fun n => n
      invFun := fun n => n
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : FirstIndLeft Q Λ j θ 0 (redFactorModule Q Λ θ u' hu').carrier ≃+
      lIdeal (oldIdem Q Λ ((Si j) + θ) u hu) :=
    (Ind.transport (emptyFactorToOld Q Λ θ).toRingEquiv
      (emptyFactorToOld Q Λ ((Si j) + θ)).toRingEquiv
      (appendBlackOldCast_emptyFactorToOld Q Λ j θ) e₀ (fun _ _ => rfl)).trans
      ((indLIdealEquiv (appendBlackOldCast Q Λ j θ)
        (isIdempotentElem_mk_e u' hu')).toAddEquiv.trans
        (LinearEquiv.ofEq _ _ (congrArg lIdeal hrel)).toAddEquiv)
  { E with
    map_smul' := fun b x => by
      change (LinearEquiv.ofEq _ _ (congrArg lIdeal hrel)) (indLIdealEquiv _
          (isIdempotentElem_mk_e u' hu') (Ind.transport _ _
            (appendBlackOldCast_emptyFactorToOld Q Λ j θ) e₀ (fun _ _ => rfl) (b • x))) =
        emptyFactorToOld Q Λ ((Si j) + θ) b • (LinearEquiv.ofEq _ _ (congrArg lIdeal hrel))
          (indLIdealEquiv _ (isIdempotentElem_mk_e u' hu') (Ind.transport _ _
            (appendBlackOldCast_emptyFactorToOld Q Λ j θ) e₀ (fun _ _ => rfl) x))
      rw [Ind.transport_smul, map_smul, map_smul]
      rfl }

end Conj

section Transfer

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (j : I) (θ β : Multiset I) (Z : Type) [AddCommGroup Z] [Module k Z]
  [Module (parabolicFactorAlgebra Q Λ θ β) Z] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) Z]
  (X : Type) [AddCommGroup X] [Module k X]
  [Module (parabolicFactorAlgebra Q Λ (({j} : Multiset I) + θ) β) X]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({j} : Multiset I) + θ) β) X]

/-- The composite `S(X) → S(₁Fⱼ Z) → Fⱼ S(Z)` is semilinear along the identification of black
weights. -/
theorem firstIndDeltaT_parabolicStandardMap_smul
    (g : X →ₗ[parabolicFactorAlgebra Q Λ ((Si j) + θ) β] FirstIndLeft Q Λ j θ β Z)
    (t : TensorProductAlgebra k Q Λ (((Si j) + θ) + β))
    (m : ParabolicStandardT Q Λ ((Si j) + θ) β X hQ) :
    firstIndDeltaT Q Λ j θ β Z hQ (parabolicStandardMap Q Λ ((Si j) + θ) β g (t • m)) =
      (castTensorProductAlgebra Q Λ (firstInd_blackWeight j θ β)).symm t •
        firstIndDeltaT Q Λ j θ β Z hQ (parabolicStandardMap Q Λ ((Si j) + θ) β g m) := by
  have key : parabolicStandardMap Q Λ ((Si j) + θ) β g (t • m) =
      parabolicStandardAction Q Λ ((Si j) + θ) β (FirstIndLeft Q Λ j θ β Z) hQ
        (castTensorProductAlgebra Q Λ (firstInd_blackWeight j θ β)
          ((castTensorProductAlgebra Q Λ (firstInd_blackWeight j θ β)).symm t))
        (parabolicStandardMap Q Λ ((Si j) + θ) β g m) := by
    rw [AlgEquiv.apply_symm_apply]
    exact parabolicStandardMap_action Q Λ ((Si j) + θ) β hQ g t m
  exact (congrArg (firstIndDeltaT Q Λ j θ β Z hQ) key).trans
    ((firstIndDeltaT Q Λ j θ β Z hQ).map_smul _ _)

/-- If `X` embeds into `₁Fⱼ Z`, `δ₁` is injective for `Z`, and `Fⱼ S(Z)` has no nonzero submodule
killed by `e⁰`, then neither has `S(X)`. -/
theorem isCornerFaithfulModule_of_firstIndLeft
    (g : X →ₗ[parabolicFactorAlgebra Q Λ ((Si j) + θ) β] FirstIndLeft Q Λ j θ β Z)
    (hg : Function.Injective g) (hδ : FirstIndDeltaInjective Q Λ j θ β Z hQ)
    (h : IsCornerFaithfulModule (redFirstIdem Q Λ ((Si j) + (θ + β)))
      (FirstIndF Q Λ j θ β Z hQ)) :
    IsCornerFaithfulModule (redFirstIdem Q Λ (((Si j) + θ) + β))
      (ParabolicStandardT Q Λ ((Si j) + θ) β X hQ) :=
  IsCornerFaithfulModule.of_injective_ringEquiv
    (castTensorProductAlgebra Q Λ (firstInd_blackWeight j θ β)).symm.toRingEquiv
    (castTensorProductAlgebra_symm_redFirstIdem Q Λ _)
    ((firstIndDeltaT Q Λ j θ β Z hQ).toAddMonoidHom.comp
      (parabolicStandardMap Q Λ ((Si j) + θ) β g).toAddMonoidHom)
    ((show Function.Injective (firstIndDeltaT Q Λ j θ β Z hQ) from hδ).comp
      (parabolicStandardMap_injective Q Λ _ _ hQ g hg))
    (firstIndDeltaT_parabolicStandardMap_smul Q Λ hQ j θ β Z X g) h

end Transfer

section Main

variable {C : QuantumGroup.CartanDatum I}
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
  (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

theorem isRedFirst_seqCast {ν ν' : Multiset I} (h : ν = ν') (s : Seq (stendhalWeight ℓ ν))
    (hs : IsRedFirst s) : IsRedFirst (Seq.cast (congrArg (stendhalWeight ℓ) h) s) := by
  subst h; exact hs

include hR in
/-- **The induction step**: if `t = (t', j)`, the property for `S(₂Fᵢ T^{λ'} e(t'))` gives it for
`S(₂Fᵢ T^{λ'} e(t))`, through `S(₂Fᵢ ₁Fⱼ N) ≅ S(₁Fⱼ ₂Fᵢ N) ↪ Fⱼ S(₂Fᵢ N)`. -/
theorem isCornerFaithfulModule_lastIndRight_append (i j : I) {θ : Multiset I}
    {u' : Seq (stendhalWeight ℓ (θ + 0))} (hu' : IsRedOrdered u')
    {u : Seq (stendhalWeight ℓ (((Si j) + θ) + 0))} (hu : IsRedOrdered u)
    (hrel : appendBlackOldCast QL Λ j θ (oldIdem QL Λ θ u' hu') =
      oldIdem QL Λ ((Si j) + θ) u hu)
    (h : IsCornerFaithfulModule (redFirstIdem QL Λ (θ + ((Si i) + 0)))
      (ParabolicStandardT QL Λ θ ((Si i) + 0)
        (LastIndRight QL Λ i θ 0 (redFactorModule QL Λ θ u' hu').carrier) hQs)) :
    IsCornerFaithfulModule (redFirstIdem QL Λ (((Si j) + θ) + ((Si i) + 0)))
      (ParabolicStandardT QL Λ ((Si j) + θ) ((Si i) + 0)
        (LastIndRight QL Λ i ((Si j) + θ) 0 (redFactorModule QL Λ ((Si j) + θ) u hu).carrier)
        hQs) := by
  have : FiniteDimensional k (redFactorModule QL Λ θ u' hu').carrier :=
    finiteDimensional_redFactorModule QL hR Λ θ u' hu'
  have : FiniteDimensional k
      (LastIndRight QL Λ i θ 0 (redFactorModule QL Λ θ u' hu').carrier) :=
    finiteDimensional_lastIndRight (Λ := Λ) i θ 0 (redFactorModule QL Λ θ u' hu').carrier hR
  let G : LastIndRight QL Λ i ((Si j) + θ) 0 (redFactorModule QL Λ ((Si j) + θ) u hu).carrier ≃ₗ[
      parabolicFactorAlgebra QL Λ ((Si j) + θ) ((Si i) + 0)]
      FirstIndLeft QL Λ j θ ((Si i) + 0)
        (LastIndRight QL Λ i θ 0 (redFactorModule QL Λ θ u' hu').carrier) :=
    (Ind.mapEquiv (φ := parabolicRightHom QL Λ i ((Si j) + θ) 0)
      (redFactorModuleAppendEquiv QL Λ j hu' hu hrel).symm).trans
      (lastIndRightFirstIndLeftEquiv QL Λ θ (redFactorModule QL Λ θ u' hu').carrier i j)
  exact isCornerFaithfulModule_of_firstIndLeft QL Λ hQs j θ ((Si i) + 0) _ _ G.toLinearMap
    G.injective (firstIndDeltaInjective_std (Λ := Λ) hR hQs j θ ((Si i) + 0) _)
    (isCornerFaithfulModule_firstIndF hR hQs Λ j θ ((Si i) + 0) _ h)
include hR in
/-- The induction on the number of black strands. -/
theorem isCornerFaithfulModule_lastIndRight_redFactorModule (i : I) :
    ∀ (n : ℕ) (θ : Multiset I), Multiset.card θ = n →
      ∀ (u : Seq (stendhalWeight ℓ (θ + 0))) (hu : IsRedOrdered u), IsRedFirst u →
        IsCornerFaithfulModule (redFirstIdem QL Λ (θ + ((Si i) + 0)))
          (ParabolicStandardT QL Λ θ ((Si i) + 0)
            (LastIndRight QL Λ i θ 0 (redFactorModule QL Λ θ u hu).carrier) hQs) := by
  intro n
  induction n with
  | zero =>
    intro θ hθ u hu _
    obtain rfl := Multiset.card_eq_zero.mp hθ
    exact isCornerFaithfulModule_lastIndBase QL Λ i hQs _
  | succ n ih =>
    intro θ hθ u hu hrf
    have hpos : 0 < Multiset.card (θ + 0) := by simp [hθ]
    obtain ⟨j, hj⟩ := exists_terminal_inl_of_isRedFirst hpos u hrf
    have hjm : j ∈ θ := by simpa using mem_of_lbl_eq_inl u _ hj
    obtain ⟨θ', rfl⟩ := exists_eq_singleton_add_of_mem hjm
    have w := firstInd_blackWeight j θ' 0
    let s := Seq.cast (congrArg (stendhalWeight ℓ) w.symm) u
    have hsu : Seq.cast (congrArg (stendhalWeight ℓ) w) s = u :=
      Subtype.ext (funext fun a => by simp [s, Seq.cast_apply])
    have hs : IsRedOrdered s := (isRedOrdered_cast _ u).2 hu
    have hst : s.lbl (terminalPos (ν := (Si j) + (θ' + 0)) (ℓ := ℓ) (by simp)) = .inl j := by
      refine Eq.trans ?_ hj
      change u.1 _ = u.1 _
      exact Seq.apply_congr u (by simp [terminalPos, cardinal_weight])
    obtain ⟨u', hu', hu'eq⟩ := exists_appendBlack_terminal s hst hs
    have hrf' : IsRedFirst u' := by
      rw [← isRedFirst_appendBlackLoading_iff j (θ' + 0) u', hu'eq]
      exact isRedFirst_seqCast w.symm u hrf
    have hrel : appendBlackOldCast QL Λ j θ' (oldIdem QL Λ θ' u' hu') =
        oldIdem QL Λ ((Si j) + θ') u hu := by
      change castTensorProductAlgebra QL (Λ ∘ Fin.castSucc) (firstInd_blackWeight j θ' 0)
        (appendBlack QL (Λ ∘ Fin.castSucc) j (θ' + 0)
          (TensorProductAlgebra.mk QL (Λ ∘ Fin.castSucc) (θ' + 0) (StendhalAlgebra.e u' hu'))) = _
      rw [appendBlack_mk_e]
      exact castTensorProductAlgebra_mk_e QL _ _ _ _ u hu (by rw [hu'eq]; exact hsu)
    have hcard : Multiset.card θ' = n := by
      simp only [Multiset.card_add, Multiset.card_singleton] at hθ
      omega
    exact isCornerFaithfulModule_lastIndRight_append hR hQs Λ i j hu' hu hrel
      (ih θ' hcard u' hu' hrf')

include hR in
/-- **No nonzero submodule of `S(₂Fᵢ T^{λ'} e(t))` is killed by `e⁰`** (Webster,
arXiv:1309.3796v3, proof of Theorem 5.30, (2) ⇒ (3), and Corollary 5.32; v2: Theorem 5.27 and
Corollary 5.29), at the standard Khovanov–Lauda parameters, for a red-ordered red-first loading
`t` of `T^{λ'}`. -/
theorem eq_zero_of_redFirstIdem_smul_lastIndStandardT (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight ℓ (θ + 0))) (hu : IsRedOrdered u) (hrf : IsRedFirst u)
    (m : LastIndStandardT QL Λ i θ 0 (redFactorModule QL Λ θ u hu).carrier hQs)
    (hm : ∀ a, (redFirstIdem QL Λ ((Si i) + (θ + 0)) * a) • m = 0) : m = 0 :=
  IsCornerFaithfulModule.of_injective_ringEquiv
    (castTensorProductAlgebra QL Λ (lastInd_blackWeight i θ 0)).toRingEquiv
    (castTensorProductAlgebra_redFirstIdem QL Λ _)
    (M := LastIndStandardT QL Λ i θ 0 (redFactorModule QL Λ θ u hu).carrier hQs)
    (M' := ParabolicStandardT QL Λ θ ((Si i) + 0)
      (LastIndRight QL Λ i θ 0 (redFactorModule QL Λ θ u hu).carrier) hQs)
    { toFun := fun x => x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    (fun _ _ h => h) (fun _ _ => rfl)
    (isCornerFaithfulModule_lastIndRight_redFactorModule hR hQs Λ i _ θ rfl u hu hrf) m hm

end Main

end Categorification.Stendhal
