/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRestrictionProjective
import Categorification.KLR.CyclotomicGradedRestriction

/-! # Raising on the projective Grothendieck group of the tensor product algebra

Webster, arXiv:1309.3796v2, §4.6, Definition 4.30 and Theorem 4.31:
restriction at the rightmost black strand acts on projectives. The degree
normalization uses the total red highest weight and the lower black content,
as in Kang–Kashiwara, arXiv:1102.4677v4, §6, immediately before Lemma 6.1.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR Categorification.Graded DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
    (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)
    (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => tensorProductGrade G νᵢ
local notation "dst" => tensorProductGrade G ν
local notation "φ" => appendBlack Q Λ i ν
local notation "LP" => LaurentPolynomial ℤ

/-- The unshifted restriction of a graded projective at a black strand of
colour `i` (Webster, arXiv:1309.3796v2, Definition 4.30). -/
def blackResProj (P : GProj src) : GProj dst where
  __ := blackResMod i ν G P.toGMod
  finite := finite_blackRes i ν P.carrier C hQ
  projective := projective_blackRes i ν C hQ P.carrier

local notation "res" => blackResProj G i ν C hQ

private def resCongr {P P' : GProj src} (e : P.Iso P') : (res P).Iso (res P') where
  toLinearEquiv :=
    { toFun := fun x => ⟨e x.1, (e.toLinearEquiv.map_smul (φ 1) x.1).symm.trans (congrArg e x.2)⟩
      invFun := fun y => ⟨e.symm y.1, (e.symm.toLinearEquiv.map_smul (φ 1) y.1).symm.trans (congrArg e.symm y.2)⟩
      map_add' := fun x y => Subtype.ext (e.toLinearEquiv.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (e.toLinearEquiv.map_smul (φ r) x.1)
      left_inv := fun x => Subtype.ext (e.toLinearEquiv.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.toLinearEquiv.apply_symm_apply y.1) }
  map_mem' _ _ hx := e.map_mem hx
  symm_map_mem' _ _ hx := e.symm_map_mem' hx

private def resProd (P P' : GProj src) : (res (P.prod P')).Iso ((res P).prod (res P')) where
  toLinearEquiv :=
    { toFun := fun x => (⟨x.1.1,congrArg Prod.fst x.2⟩,⟨x.1.2,congrArg Prod.snd x.2⟩)
      invFun := fun y => ⟨(y.1.1,y.2.1),Prod.ext y.1.2 y.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

private def resShift (P : GProj src) (d : ℤ) : (res (P.shift d)).Iso ((res P).shift d) where
  toLinearEquiv := LinearEquiv.refl _ _
  map_mem' _ _ hx := hx
  symm_map_mem' _ _ hx := hx

private def blackResAdd : K0 src →+ K0 dst :=
  K0.lift (fun P => K0.of (res P))
    (fun _ _ e => K0.of_eq_of_iso (resCongr G i ν C hQ e))
    (fun P P' => (K0.of_eq_of_iso (resProd G i ν C hQ P P')).trans (K0.of_prod ..))

/-- Raw restriction on the projective Grothendieck groups of adjacent black weights. -/
def blackResK0 : K0 src →ₗ[LP] K0 dst where
  __ := blackResAdd G i ν C hQ
  map_smul' := K0.map_smul_of_shift (blackResAdd G i ν C hQ) fun d x => by
    induction x using K0.induction_on with
    | of P =>
      simp only [K0.shiftHom_of,blackResAdd,K0.lift_of]
      exact K0.of_eq_of_iso (resShift G i ν C hQ P d)
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | neg x hx => simp only [map_neg,hx]

@[simp] theorem blackResK0_of (P : GProj src) :
    blackResK0 G i ν C hQ (K0.of P) = K0.of (res P) := by
  change blackResAdd G i ν C hQ (K0.of P) = _
  exact K0.lift_of _ _ _ _

/-- The projective raising normalization for ordered red weights. -/
def blackRaiseK0 : K0 src →ₗ[LP] K0 dst :=
  (LaurentPolynomial.T (CycKLR.raiseShift (fun j => ∑ r, Λ r j) i ν C) : LP) • blackResK0 G i ν C hQ

local notation "K" => fun β : Multiset I => K0 (tensorProductGrade G β)
local notation "total" => ⨁ β : Multiset I, K β

private def blackRaiseComponent (β : Multiset I) : K β →ₗ[LP] total :=
  if h : i ∈ β then
    let e : {i} + β.erase i = β := (Multiset.singleton_add ..).trans (Multiset.cons_erase h)
    e ▸ (DirectSum.lof LP _ K (β.erase i) ∘ₗ blackRaiseK0 G i (β.erase i) C hQ :
      K ({i} + β.erase i) →ₗ[LP] total)
  else 0

/-- The raising generator induced by black restriction on the sum of all
projective weight groups (Webster, arXiv:1309.3796v2, §4.6, Theorem 4.31). -/
def blackRaise : total →ₗ[LP] total :=
  DirectSum.toModule LP _ _ (blackRaiseComponent G i C hQ)

@[simp] theorem blackRaise_lof (x : K νᵢ) :
    blackRaise G i C hQ (DirectSum.lof LP _ K νᵢ x) =
      DirectSum.lof LP _ K ν (blackRaiseK0 G i ν C hQ x) := by
  rw [blackRaise,DirectSum.toModule_lof,blackRaiseComponent,dite_eq_left (show i ∈ νᵢ by simp)]
  have eval (μ : Multiset I) (hμ : μ = ν) (he : {i} + μ = νᵢ) :
      (he ▸ (DirectSum.lof LP _ K μ ∘ₗ blackRaiseK0 G i μ C hQ : K ({i} + μ) →ₗ[LP] total)) x =
        DirectSum.lof LP _ K ν (blackRaiseK0 G i ν C hQ x) := by subst μ; rfl
  apply eval
  rw [Multiset.singleton_add,Multiset.erase_cons_head]

@[simp] theorem blackRaise_lof_of_notMem (h : i ∉ ν) (x : K ν) :
    blackRaise G i C hQ (DirectSum.lof LP _ K ν x) = 0 := by
  rw [blackRaise,DirectSum.toModule_lof,blackRaiseComponent,dite_eq_right h,LinearMap.zero_apply]

end Categorification.Stendhal
