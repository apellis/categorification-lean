/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingStack
import Categorification.WeightedKLR.RedStrands.BraidedStandardModule
import Categorification.WeightedKLR.RedStrands.StandardPartialKernel

/-!
# Cyclic generators of exterior block coefficients

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10), the reduction to two red strands by Lemma 6.8. Let `X` be a space of horizontal
coefficients (`BlockCut`) on which a ground-ring algebra `D` acts on the right through a linear
map into the ambient algebra. A *generator* of the summand of `X` cut out by a top idempotent
`e` is an element `c` such that

* the summand `e X` is the cyclic module `c D` (`Generator.fix`, `Generator.gen`);
* if `c a = 0` then `τ a` lies in a prescribed subspace `H` of relations, for a bottom
  idempotent `τ` (`Generator.ann`).

The exterior tensor of two generators is a generator (`Generator.tensor`), with the relations
`H₁ ⊗ τ₂ D₂ + τ₁ D₁ ⊗ H₂`. The annihilator computation is the right exactness of the tensor
product over the ground ring (`TensorProduct.map_ker`), applied to the cyclic summands, which
are split by the top projections.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Categorification.Stendhal.RedBlock

open scoped TensorProduct

universe v
variable {k : Type v} [CommRing k]

namespace BlockCut

variable {R D : Type v} [Ring R] [Algebra k R] [Ring D] [Algebra k D] {p q : R}
  (C : BlockCut (k := k) R p q)

/-- Right multiplication of a coefficient by the image of an element of `D`. -/
def rmul (r : D →ₗ[k] R) (c : C.space) : D →ₗ[k] C.space :=
  C.cut ∘ₗ LinearMap.mulLeft k (C.incl c) ∘ₗ r

theorem rmul_apply (r : D →ₗ[k] R) (c : C.space) (a : D) :
    C.rmul r c a = C.cut (C.incl c * r a) := rfl

/-- Left multiplication of a coefficient by an element of the ambient algebra. -/
def lproj (e : R) : C.space →ₗ[k] C.space :=
  C.cut ∘ₗ LinearMap.mulLeft k e ∘ₗ C.incl

theorem lproj_apply (e : R) (x : C.space) : C.lproj e x = C.cut (e * C.incl x) := rfl

/-- **A cyclic generator of a top summand.** The summand of `X` cut out by `e` is `c D`, and
the bottom idempotent `τ` carries the annihilator of `c` into the relations `H`. -/
structure Generator (r : D →ₗ[k] R) (c : C.space) (e : R) (τ : D) (H : Submodule k D) :
    Prop where
  fix : ∀ a, C.lproj e (C.rmul r c a) = C.rmul r c a
  gen : LinearMap.range (C.lproj e) ≤ LinearMap.range (C.rmul r c)
  ann : ∀ a, C.rmul r c a = 0 → τ * a ∈ H

section Tensor

variable {R₂ D₂ : Type v} [Ring R₂] [Algebra k R₂] [Ring D₂] [Algebra k D₂] {p₂ q₂ : R₂}
  (C₂ : BlockCut (k := k) R₂ p₂ q₂)

theorem rmul_tensor (r : D →ₗ[k] R) (r₂ : D₂ →ₗ[k] R₂) (c : C.space) (c₂ : C₂.space) :
    (C.tensor C₂).rmul (TensorProduct.map r r₂) (c ⊗ₜ c₂) =
      TensorProduct.map (C.rmul r c) (C₂.rmul r₂ c₂) := by
  apply TensorProduct.ext'
  intro a b
  change TensorProduct.map C.cut C₂.cut (TensorProduct.map C.incl C₂.incl (c ⊗ₜ c₂) *
    TensorProduct.map r r₂ (a ⊗ₜ b)) = _
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    TensorProduct.map_tmul]
  rfl

theorem lproj_tensor (e : R) (e₂ : R₂) :
    (C.tensor C₂).lproj (e ⊗ₜ e₂) = TensorProduct.map (C.lproj e) (C₂.lproj e₂) := by
  apply TensorProduct.ext'
  intro x y
  change TensorProduct.map C.cut C₂.cut ((e ⊗ₜ e₂) * TensorProduct.map C.incl C₂.incl (x ⊗ₜ y)) = _
  rw [TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.map_tmul]
  rfl

/-- The relations of an exterior tensor of generators. -/
def tensorRelations (τ : D) (τ₂ : D₂) (H : Submodule k D) (H₂ : Submodule k D₂) :
    Submodule k (D ⊗[k] D₂) :=
  Submodule.span k (Set.image2 (· ⊗ₜ ·) H (Set.range (τ₂ * ·))) ⊔
    Submodule.span k (Set.image2 (· ⊗ₜ ·) (Set.range (τ * ·)) H₂)

variable {C C₂}

private theorem range_map_le {M M₂ N N₂ P P₂ : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M₂] [Module k M₂] [AddCommGroup N] [Module k N] [AddCommGroup N₂]
    [Module k N₂] [AddCommGroup P] [Module k P] [AddCommGroup P₂] [Module k P₂]
    {f : M →ₗ[k] N} {f₂ : M₂ →ₗ[k] N₂} {g : P →ₗ[k] N} {g₂ : P₂ →ₗ[k] N₂}
    (h : LinearMap.range f ≤ LinearMap.range g) (h₂ : LinearMap.range f₂ ≤ LinearMap.range g₂) :
    LinearMap.range (TensorProduct.map f f₂) ≤ LinearMap.range (TensorProduct.map g g₂) := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul x y =>
    obtain ⟨a, ha⟩ := h ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := h₂ ⟨y, rfl⟩
    exact ⟨a ⊗ₜ b, by rw [TensorProduct.map_tmul, TensorProduct.map_tmul, ha, hb]⟩

/-- **Exterior tensor of generators** (Webster, arXiv:1309.3796v2, §6.1, the bimodule before
Lemma 6.8 and the proof of Proposition 6.9). The annihilator of `c ⊗ c₂` is the sum of the
two annihilators tensored with the other factor. -/
theorem Generator.tensor {r : D →ₗ[k] R} {r₂ : D₂ →ₗ[k] R₂} {c : C.space} {c₂ : C₂.space}
    {e : R} {e₂ : R₂} {τ : D} {τ₂ : D₂} {H : Submodule k D} {H₂ : Submodule k D₂}
    (g : C.Generator r c e τ H) (g₂ : C₂.Generator r₂ c₂ e₂ τ₂ H₂) :
    (C.tensor C₂).Generator (TensorProduct.map r r₂) (c ⊗ₜ c₂) (e ⊗ₜ e₂) (τ ⊗ₜ τ₂)
      (tensorRelations τ τ₂ H H₂) := by
  have hr := rmul_tensor C C₂ r r₂ c c₂
  have hl := lproj_tensor C C₂ e e₂
  let f := C.rmul r c
  let f₂ := C₂.rmul r₂ c₂
  refine ⟨fun a => ?_, ?_, fun a ha => ?_⟩
  · have key : TensorProduct.map (C.lproj e) (C₂.lproj e₂) ∘ₗ TensorProduct.map f f₂ =
        TensorProduct.map f f₂ := by
      rw [← TensorProduct.map_comp]
      congr 1
      · exact LinearMap.ext g.fix
      · exact LinearMap.ext g₂.fix
    rw [hr, hl]
    exact LinearMap.congr_fun key a
  · rw [hr, hl]
    exact range_map_le g.gen g₂.gen
  · -- Factor each multiplication through its cyclic summand.
    let s := f.rangeRestrict
    let s₂ := f₂.rangeRestrict
    have hs : Function.Surjective s := f.surjective_rangeRestrict
    have hs₂ : Function.Surjective s₂ := f₂.surjective_rangeRestrict
    let ρ : C.space →ₗ[k] LinearMap.range f :=
      (C.lproj e).codRestrict _ fun x => g.gen ⟨x, rfl⟩
    let ρ₂ : C₂.space →ₗ[k] LinearMap.range f₂ :=
      (C₂.lproj e₂).codRestrict _ fun x => g₂.gen ⟨x, rfl⟩
    have hρ : ρ ∘ₗ (LinearMap.range f).subtype = LinearMap.id := by
      apply LinearMap.ext; rintro ⟨_, a, rfl⟩
      exact Subtype.ext (g.fix a)
    have hρ₂ : ρ₂ ∘ₗ (LinearMap.range f₂).subtype = LinearMap.id := by
      apply LinearMap.ext; rintro ⟨_, a, rfl⟩
      exact Subtype.ext (g₂.fix a)
    have hinj : Function.Injective (TensorProduct.map (LinearMap.range f).subtype
        (LinearMap.range f₂).subtype) := by
      apply Function.LeftInverse.injective (g := TensorProduct.map ρ ρ₂)
      intro z
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hρ, hρ₂, TensorProduct.map_id,
        LinearMap.id_apply]
    have hfac : TensorProduct.map f f₂ = TensorProduct.map (LinearMap.range f).subtype
        (LinearMap.range f₂).subtype ∘ₗ TensorProduct.map s s₂ := by
      rw [← TensorProduct.map_comp]; rfl
    have hker : a ∈ LinearMap.ker (TensorProduct.map s s₂) := by
      rw [LinearMap.mem_ker]
      apply hinj
      rw [← LinearMap.comp_apply, ← hfac, map_zero, ← hr]
      exact ha
    rw [TensorProduct.map_ker (LinearMap.exact_subtype_ker_map s) hs
      (LinearMap.exact_subtype_ker_map s₂) hs₂] at hker
    -- Multiply the kernel generators on the left by `τ ⊗ τ₂`.
    let m := LinearMap.mulLeft k (τ ⊗ₜ[k] τ₂ : D ⊗[k] D₂)
    have first (w : D ⊗[k] LinearMap.ker s₂) :
        m (LinearMap.lTensor D (LinearMap.ker s₂).subtype w) ∈ tensorRelations τ τ₂ H H₂ := by
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | tmul x y =>
        apply Submodule.mem_sup_right
        apply Submodule.subset_span
        refine ⟨τ * x, ⟨x, rfl⟩, τ₂ * y.1, g₂.ann y.1 ?_, ?_⟩
        · exact congrArg Subtype.val (LinearMap.mem_ker.1 y.2)
        · change _ = (τ ⊗ₜ[k] τ₂) * (x ⊗ₜ y.1)
          rw [Algebra.TensorProduct.tmul_mul_tmul]
    have second (w : LinearMap.ker s ⊗[k] D₂) :
        m (LinearMap.rTensor D₂ (LinearMap.ker s).subtype w) ∈ tensorRelations τ τ₂ H H₂ := by
      induction w using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
      | tmul x y =>
        apply Submodule.mem_sup_left
        apply Submodule.subset_span
        refine ⟨τ * x.1, g.ann x.1 ?_, τ₂ * y, ⟨y, rfl⟩, ?_⟩
        · exact congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
        · change _ = (τ ⊗ₜ[k] τ₂) * (x.1 ⊗ₜ y)
          rw [Algebra.TensorProduct.tmul_mul_tmul]
    have hle : LinearMap.range (LinearMap.lTensor D (LinearMap.ker s₂).subtype) ⊔
        LinearMap.range (LinearMap.rTensor D₂ (LinearMap.ker s).subtype) ≤
        (tensorRelations τ τ₂ H H₂).comap m := by
      refine sup_le ?_ ?_
      · rintro _ ⟨w, rfl⟩
        exact first w
      · rintro _ ⟨w, rfl⟩
        exact second w
    exact hle hker

end Tensor

end BlockCut


section Factors

open KLR BraidedStendhalAlgebra

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)

local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "TA" B => TensorProductAlgebra k Q ((Λ ∘ RedBlock.label B) ∘
  (1 : Equiv.Perm (Fin (RedBlock.size B)))) (RedBlock.black B)

/-- **The regular factor at an unchanged red strand** is generated by a loading idempotent,
with no relations. -/
theorem spectatorCut_generator (x : Fin ℓ × Multiset I) (τ : TA (spectator x))
    (hτ : IsIdempotentElem τ) :
    (spectatorCut Q Λ hQ x).Generator
      (LinearMap.ofClass (orderedValue Q Λ hQ botOrd (spectator x))) τ
      (orderedValue Q Λ hQ botOrd (spectator x) τ) τ ⊥ := by
  have hr (a : TA (spectator x)) :
      (spectatorCut Q Λ hQ x).rmul (LinearMap.ofClass (orderedValue Q Λ hQ botOrd (spectator x)))
        τ a = τ * a := by
    change orderedRetraction Q Λ hQ botOrd (spectator x)
      (orderedValue Q Λ hQ botOrd (spectator x) τ * orderedValue Q Λ hQ botOrd (spectator x) a) = _
    rw [← map_mul]; exact orderedRetraction_value Q Λ hQ botOrd (spectator x) _
  have hl (a : TA (spectator x)) :
      (spectatorCut Q Λ hQ x).lproj (orderedValue Q Λ hQ botOrd (spectator x) τ) a = τ * a := by
    change orderedRetraction Q Λ hQ botOrd (spectator x)
      (orderedValue Q Λ hQ botOrd (spectator x) τ * orderedValue Q Λ hQ botOrd (spectator x) a) = _
    rw [← map_mul]; exact orderedRetraction_value Q Λ hQ botOrd (spectator x) _
  refine ⟨fun a => ?_, ?_, fun a ha => ?_⟩
  · rw [hr, hl, ← mul_assoc, hτ.eq]
  · rintro _ ⟨y, rfl⟩
    exact ⟨y, by rw [hr, hl]⟩
  · rw [hr] at ha
    rw [ha]; exact zero_mem _


section Pair

variable (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "μ₂" => stendhalWeight 2 β
local notation "m₂" => Multiset.card (stendhalWeight 2 β)
local notation "q₂" => violMk k Q (Λ ∘ f) β
local notation "ι₂" => ofKLR k Q (Λ ∘ f) β
local notation "ov" => orderedValue Q Λ hQ botOrd B₂

/-- The standard relations at a two-red loading `t`, as diagrams of the uncrossed ordered
algebra: their images lie in the ideal of loadings strictly above `t`. -/
def pairRelations (t : Seq μ₂) : Submodule k (TA B₂) :=
  ((stendhalUpperIdeal k Q (Λ ∘ f) β t [0, 1]).asIdeal.restrictScalars k).comap
    (LinearMap.ofClass ov)

theorem mem_pairRelations {t : Seq μ₂} {a : TA B₂} :
    a ∈ pairRelations Q Λ hQ f β t ↔ ov a ∈ stendhalUpperIdeal k Q (Λ ∘ f) β t [0, 1] := by
  rw [pairRelations, Submodule.mem_comap, Submodule.restrictScalars_mem, TwoSidedIdeal.mem_asIdeal]
  rfl

/-- The Figure 5 diagram `ψ_g e(t)` as a coefficient of the two-red crossing bimodule. -/
def pairGen (ρ : Equiv.Perm (Fin m₂) → List ℕ) (g : Equiv.Perm (Fin m₂)) (t : Seq μ₂) :
    (pairCut Q Λ hQ f β).space :=
  (pairCut Q Λ hQ f β).cut (q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t)))

private theorem finRange_map_one : (List.finRange 2).map ((1 : Equiv.Perm (Fin 2)) : Fin 2 → Fin 2) =
    [0, 1] := by decide

private theorem finRange_map_rev : (List.finRange 2).map (Fin.revPerm : Equiv.Perm (Fin 2)) =
    [1, 0] := by decide

private theorem mem_stendhalUpperIdeal_of_mem {ν : Multiset I} {Λ' : Fin ℓ → I →₀ ℕ}
    {t : Seq (stendhalWeight ℓ ν)} {κ : List (Fin ℓ)} (hκ : redWord t = κ)
    (x : violCorner k Q Λ' ν t κ) (hx : x ∈ violStandardUpper t κ) :
    x.1 ∈ stendhalUpperIdeal k Q Λ' ν t κ := by
  subst hκ
  exact (mem_violStandardUpper_iff x).1 hx

/-- **The two-red factor of Proposition 6.9** (Webster, arXiv:1309.3796v2, §6.1, Figure 5).
At the loading `s` of the swapped order, the summand of the crossing bimodule is generated by
the Figure 5 diagram, and the annihilator of that diagram is carried by `e(t)` into the
standard relations at `t`. Both facts are the two-red isomorphism
`violLoadingStandardEquivBraidCorner`. -/
theorem pairCut_generator {ρ : Equiv.Perm (Fin m₂) → List ℕ} (hρ : TypeA.IsReducedChoice ρ)
    {s t : Seq μ₂} {g : Equiv.Perm (Fin m₂)} (h1 : 1 < m₂)
    (ht₀ : t.lbl ⟨0, by omega⟩ = .inr 0) (ht₁ : t.lbl ⟨1, h1⟩ = .inr 1)
    (hb : EdgeBraid (show 0 < m₂ by omega) 0 g s t) (hs : redWord s = [1, 0])
    (ht : redWord t = [0, 1]) :
    (pairCut Q Λ hQ f β).Generator (LinearMap.ofClass ov) (pairGen Q Λ hQ f β ρ g t)
      (q₂ (ι₂ (KLRAlgebra.e s))) (tensorOfKLR Q (Λ ∘ f) β (KLRAlgebra.e t))
      (pairRelations Q Λ hQ f β t) := by
  let P₀ : quotientAlgebra Q Λ B₂ := q₂ (redProj k Q (Λ ∘ f) β [0, 1])
  let P₁ : quotientAlgebra Q Λ B₂ := q₂ (redProj k Q (Λ ∘ f) β [1, 0])
  let es : quotientAlgebra Q Λ B₂ := q₂ (ι₂ (KLRAlgebra.e s))
  let et : quotientAlgebra Q Λ B₂ := q₂ (ι₂ (KLRAlgebra.e t))
  let c : quotientAlgebra Q Λ B₂ := q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t))
  have hP0 : ov 1 = P₀ := by
    rw [orderedValue_one]
    exact congrArg (fun κ => q₂ (redProj k Q (Λ ∘ f) β κ)) finRange_map_one
  have hP1 : orderedValue Q Λ hQ topOrd B₂ 1 = P₁ := by
    rw [orderedValue_one]
    exact congrArg (fun κ => q₂ (redProj k Q (Λ ∘ f) β κ)) finRange_map_rev
  have hψ : (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t :
      KLRAlgebra k (stendhalQ Q (Λ ∘ f)) μ₂) =
      KLRAlgebra.e s * (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t) := by
    rw [KLRAlgebra.ψw_mul_e, (hρ g).2, hb.smul_eq, ← mul_assoc, KLRAlgebra.e_mul_self]
  have hsc : es * c = c := by
    change q₂ (ι₂ (KLRAlgebra.e s)) * q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t)) =
      q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t))
    rw [← map_mul q₂, ← map_mul ι₂, ← hψ]
  have hct : c * et = c := by
    change q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t)) * q₂ (ι₂ (KLRAlgebra.e t)) =
      q₂ (ι₂ (KLRAlgebra.ψw (ρ g) * KLRAlgebra.e t))
    rw [← map_mul q₂, ← map_mul ι₂, mul_assoc, KLRAlgebra.e_mul_self]
  have hP1s : P₁ * es = es := by
    have h := congrArg q₂ (redProj_mul_e (k := k) (Q := Q) (Λ := Λ ∘ f) (ν := β) [1, 0] s)
    rw [ite_eq_left hs, map_mul] at h
    exact h
  have hP0t : P₀ * et = et := by
    have h := congrArg q₂ (redProj_mul_e (k := k) (Q := Q) (Λ := Λ ∘ f) (ν := β) [0, 1] t)
    rw [ite_eq_left ht, map_mul] at h
    exact h
  have htP0 : et * P₀ = et := by
    have h := congrArg q₂ (e_mul_redProj (k := k) (Q := Q) (Λ := Λ ∘ f) (ν := β) [0, 1] t)
    rw [ite_eq_left ht, map_mul] at h
    exact h
  have hP1c : P₁ * c = c := by
    calc P₁ * c = P₁ * (es * c) := by rw [hsc]
      _ = c := by rw [← mul_assoc, hP1s, hsc]
  have hcP0 : c * P₀ = c := by
    calc c * P₀ = c * et * P₀ := by rw [hct]
      _ = c := by rw [mul_assoc, htP0, hct]
  have hcval : (pairGen Q Λ hQ f β ρ g t).1 = c := by
    change orderedValue Q Λ hQ topOrd B₂ 1 * c * ov 1 = c
    rw [hP1, hP0, hP1c, hcP0]
  have hov (a : TA B₂) : ov a * P₀ = ov a := by
    rw [← hP0, ← map_mul, mul_one]
  have hr (a : TA B₂) :
      ((pairCut Q Λ hQ f β).rmul (LinearMap.ofClass ov) (pairGen Q Λ hQ f β ρ g t) a).1 =
        c * ov a := by
    change orderedValue Q Λ hQ topOrd B₂ 1 * ((pairGen Q Λ hQ f β ρ g t).1 * ov a) * ov 1 = _
    rw [hcval, hP0, mul_assoc _ _ P₀, mul_assoc c, hov, hP1, ← mul_assoc, hP1c]
  have hl (x : (pairCut Q Λ hQ f β).space) :
      ((pairCut Q Λ hQ f β).lproj es x).1 = es * x.1 := by
    obtain ⟨X, hX⟩ := x
    have hX2 : (X : quotientAlgebra Q Λ B₂) * ov 1 = X := hX.2
    change orderedValue Q Λ hQ topOrd B₂ 1 * (es * X) * ov 1 = es * X
    rw [hP1, ← mul_assoc, hP1s, mul_assoc, hX2]
  let iso := violLoadingStandardEquivBraidCorner (k := k) (Q := Q) (Λ₂ := Λ ∘ f) hρ hQ h1 ht₀ ht₁ hb
  refine ⟨fun a => Subtype.ext ?_, ?_, fun a ha => ?_⟩
  · rw [hl, hr, ← mul_assoc, hsc]
  · rintro _ ⟨x, rfl⟩
    have hx : (x.1 : quotientAlgebra Q Λ B₂) * P₀ = x.1 := by rw [← hP0]; exact x.2.2
    have hes : es * es = es := by
      change q₂ (ι₂ (KLRAlgebra.e s)) * q₂ (ι₂ (KLRAlgebra.e s)) = q₂ (ι₂ (KLRAlgebra.e s))
      rw [← map_mul q₂, ← map_mul ι₂, KLRAlgebra.e_mul_self]
    have hw₁ : es * (es * (x.1 : quotientAlgebra Q Λ B₂)) = es * x.1 := by
      rw [← mul_assoc, hes]
    have hw₂ : es * (x.1 : quotientAlgebra Q Λ B₂) * P₀ = es * x.1 := by
      rw [mul_assoc, hx]
    let w : violCorner k Q (Λ ∘ f) β s [0, 1] := ⟨es * x.1, mem_violCorner_iff.2 ⟨hw₁, hw₂⟩⟩
    obtain ⟨y, hy⟩ := iso.surjective w
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hval := violLoadingStandardEquivBraidCorner_mk hρ hQ h1 ht₀ ht₁ hb y'
    rw [hy] at hval
    have hy' := mem_violCorner_iff.1 y'.2
    have hy1 : et * (y'.1 : quotientAlgebra Q Λ B₂) = y'.1 := hy'.1
    have hy2 : (y'.1 : quotientAlgebra Q Λ B₂) * P₀ = y'.1 := hy'.2
    have hval' : (w.1 : quotientAlgebra Q Λ B₂) = c * y'.1 := hval
    have key : ov 1 * (y'.1 : quotientAlgebra Q Λ B₂) * ov 1 = y'.1 := by
      rw [hP0, mul_assoc, hy2, ← hy1, ← mul_assoc, hP0t]
    refine ⟨orderedRetraction Q Λ hQ botOrd B₂ y'.1, Subtype.ext ?_⟩
    rw [hr, hl, orderedValue_retraction, key]
    exact hval'.symm
  · have ha' : c * ov a = 0 := by rw [← hr, ha]; rfl
    have het : et * et = et := by
      change q₂ (ι₂ (KLRAlgebra.e t)) * q₂ (ι₂ (KLRAlgebra.e t)) = q₂ (ι₂ (KLRAlgebra.e t))
      rw [← map_mul q₂, ← map_mul ι₂, KLRAlgebra.e_mul_self]
    have hy₁ : et * (et * ov a) = et * ov a := by rw [← mul_assoc, het]
    have hy₂ : et * ov a * P₀ = et * ov a := by rw [mul_assoc, hov]
    let y' : violCorner k Q (Λ ∘ f) β t [0, 1] := ⟨et * ov a, mem_violCorner_iff.2 ⟨hy₁, hy₂⟩⟩
    have h0 : iso (Submodule.Quotient.mk y') = 0 := by
      apply Subtype.ext
      rw [violLoadingStandardEquivBraidCorner_mk]
      change c * (et * ov a) = 0
      rw [← mul_assoc, hct, ha']
    have hmk : (Submodule.Quotient.mk y' : ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ ∘ f) t
        [0, 1]) = 0 := iso.injective (h0.trans (map_zero iso).symm)
    have hmem := mem_stendhalUpperIdeal_of_mem Q ht y' ((Submodule.Quotient.mk_eq_zero _).1 hmk)
    have htf : redWord t = List.finRange 2 := ht.trans (by decide)
    rw [mem_pairRelations, map_mul, orderedValue_identity_e Q Λ hQ B₂ t htf]
    exact hmem

end Pair

/-! ### Rows of factors -/

namespace BlockCut

variable {R D : Type v} [Ring R] [Algebra k R] [Ring D] [Algebra k D] {p q : R}
  {C : BlockCut (k := k) R p q}

/-- A generator depends on the action map only through its values. -/
theorem Generator.congr_map {r r' : D →ₗ[k] R} {c : C.space} {e : R} {τ : D}
    {H : Submodule k D} (g : C.Generator r c e τ H) (h : ∀ a, r a = r' a) :
    C.Generator r' c e τ H := by
  have : r = r' := LinearMap.ext h
  exact this ▸ g

end BlockCut

/-- The local idempotent of a spectator loading, in the uncrossed algebra of the spectator. -/
def spectatorIdem (x : Fin ℓ × Multiset I) (σ : Seq (spectator x).localWeight) :
    TA (spectator x) :=
  orderedRetraction Q Λ hQ botOrd (spectator x)
    (violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
      (KLRAlgebra.e σ)))

omit [DecidableEq I] in
private theorem redWord_spectator (x : Fin ℓ × Multiset I) (σ : Seq (spectator x).localWeight) :
    redWord σ = [0] := by
  have hp : (redWord σ).Perm (List.finRange 1) :=
    (List.perm_ext_iff_of_nodup (redWord_nodup _) (List.nodup_finRange _)).2
      fun r => by simp [mem_redWord]
  exact List.perm_singleton.1 (hp.trans (List.Perm.of_eq rfl))

theorem orderedValue_spectatorIdem (x : Fin ℓ × Multiset I) (σ : Seq (spectator x).localWeight) :
    orderedValue Q Λ hQ botOrd (spectator x) (spectatorIdem Q Λ hQ x σ) =
      violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
        (KLRAlgebra.e σ)) := by
  have h1 : orderedValue Q Λ hQ botOrd (spectator x) 1 =
      violMk k Q (Λ ∘ (spectator x).label) x.2 (redProj k Q (Λ ∘ (spectator x).label) x.2 [0]) := by
    rw [orderedValue_one]; rfl
  rw [spectatorIdem, orderedValue_retraction, h1]
  have hl := congrArg (violMk k Q (Λ ∘ (spectator x).label) x.2)
    (redProj_mul_e (k := k) (Q := Q) (Λ := Λ ∘ (spectator x).label) (ν := x.2) [0] σ)
  have hr := congrArg (violMk k Q (Λ ∘ (spectator x).label) x.2)
    (e_mul_redProj (k := k) (Q := Q) (Λ := Λ ∘ (spectator x).label) (ν := x.2) [0] σ)
  rw [ite_eq_left (redWord_spectator x σ), map_mul] at hl hr
  rw [hl, hr]

theorem isIdempotentElem_spectatorIdem (x : Fin ℓ × Multiset I)
    (σ : Seq (spectator x).localWeight) : IsIdempotentElem (spectatorIdem Q Λ hQ x σ) := by
  have hi : Function.Injective (orderedValue Q Λ hQ botOrd (spectator x)) := fun a b h => by
    rw [← orderedRetraction_value Q Λ hQ botOrd (spectator x) a, h,
      orderedRetraction_value]
  apply hi
  change orderedValue Q Λ hQ botOrd (spectator x) (_ * _) = _
  rw [map_mul, orderedValue_spectatorIdem, ← map_mul, ← map_mul, KLRAlgebra.e_mul_self]

/-- The spectator factor, generated by the idempotent of a spectator loading. -/
theorem spectatorCut_generator_loading (x : Fin ℓ × Multiset I)
    (σ : Seq (spectator x).localWeight) :
    (spectatorCut Q Λ hQ x).Generator
      (LinearMap.ofClass (orderedValue Q Λ hQ botOrd (spectator x))) (spectatorIdem Q Λ hQ x σ)
      (violMk k Q (Λ ∘ (spectator x).label) x.2 (ofKLR k Q (Λ ∘ (spectator x).label) x.2
        (KLRAlgebra.e σ))) (spectatorIdem Q Λ hQ x σ) ⊥ := by
  have g := spectatorCut_generator Q Λ hQ x _ (isIdempotentElem_spectatorIdem Q Λ hQ x σ)
  rwa [orderedValue_spectatorIdem] at g

/-- The tensor of the spectator loading idempotents along a list of spectators. -/
def spectatorsIdem : (M : List (Fin ℓ × Multiset I)) → Loadings (M.map spectator) →
    orderedProduct Q Λ botOrd (M.map spectator)
  | [], _ => 1
  | x :: xs, s => spectatorIdem Q Λ hQ x s.1 ⊗ₜ spectatorsIdem xs s.2

/-- `spectatorsIdem` as a coefficient of the spectator factors. -/
def spectatorsGen : (M : List (Fin ℓ × Multiset I)) → Loadings (M.map spectator) →
    (spectatorCuts Q Λ hQ M).space
  | [], _ => (1 : ULift.{0} k)
  | x :: xs, s => (spectatorIdem Q Λ hQ x s.1 ⊗ₜ spectatorsGen xs s.2 :
      (TA (spectator x)) ⊗[k] (spectatorCuts Q Λ hQ xs).space)

/-- The relations of a row of spectators (all trivial, recorded as iterated tensor
relations). -/
def spectatorsRelations : (M : List (Fin ℓ × Multiset I)) → Loadings (M.map spectator) →
    Submodule k (orderedProduct Q Λ botOrd (M.map spectator))
  | [], _ => ⊥
  | x :: xs, s => BlockCut.tensorRelations (spectatorIdem Q Λ hQ x s.1) (spectatorsIdem Q Λ hQ xs s.2)
      ⊥ (spectatorsRelations xs s.2)

theorem spectatorCuts_generator : ∀ (M : List (Fin ℓ × Multiset I)) (s : Loadings (M.map spectator)),
    (spectatorCuts Q Λ hQ M).Generator
      (LinearMap.ofClass (orderedInclusion Q Λ hQ botOrd (M.map spectator)))
      (spectatorsGen Q Λ hQ M s) (projection Q Λ (M.map spectator) (loadingIdem Q Λ _ s))
      (spectatorsIdem Q Λ hQ M s) (spectatorsRelations Q Λ hQ M s)
  | [], _ => by
    refine ⟨fun a => ?_, ?_, fun a ha => ?_⟩
    · show (1 : ULift.{0} k) * ((1 : ULift.{0} k) * (show ULift.{0} k from a)) =
        (1 : ULift.{0} k) * (show ULift.{0} k from a)
      rw [one_mul]
    · rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · have ha' : (1 : ULift.{0} k) * (show ULift.{0} k from a) = 0 := ha
      show (1 : ULift.{0} k) * (show ULift.{0} k from a) ∈ (⊥ : Submodule k (ULift.{0} k))
      rw [ha']; exact zero_mem _
  | x :: xs, s => by
    have g := ((spectatorCut_generator_loading Q Λ hQ x s.1).tensor
      (spectatorCuts_generator xs s.2)).congr_map (r' := LinearMap.ofClass
        (orderedInclusion Q Λ hQ botOrd ((x :: xs).map spectator))) fun _ => rfl
    exact g


section Row

variable (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)

/-- The generator of the crossing bimodule of a row: spectator idempotents flanking a
two-red coefficient `cp`. -/
def rowGen (cp : (pairCut Q Λ hQ f β).space) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      (crossingProduct Q Λ hQ M f β L).space
  | [], s => (cp ⊗ₜ spectatorsGen Q Λ hQ M s.2 :
      (pairCut Q Λ hQ f β).space ⊗[k] (spectatorCuts Q Λ hQ M).space)
  | x :: xs, s => (spectatorIdem Q Λ hQ x s.1 ⊗ₜ rowGen cp xs s.2 :
      (TA (spectator x)) ⊗[k] (crossingProduct Q Λ hQ M f β xs).space)

/-- The top idempotent of a row: spectator loading idempotents flanking `ep`. -/
def rowTop (ep : quotientAlgebra Q Λ B₂) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      quotients Q Λ (adjacentRow L M f β)
  | [], s => (ep ⊗ₜ projection Q Λ _ (loadingIdem Q Λ _ s.2) :
      quotientAlgebra Q Λ B₂ ⊗[k] quotients Q Λ (M.map spectator))
  | x :: xs, s => (violMk k Q (Λ ∘ (spectator x).label) x.2
      (ofKLR k Q (Λ ∘ (spectator x).label) x.2 (KLRAlgebra.e s.1)) ⊗ₜ rowTop ep xs s.2 :
      quotientAlgebra Q Λ (spectator x) ⊗[k] quotients Q Λ (adjacentRow xs M f β))

/-- The bottom idempotent of a row: spectator loading idempotents flanking `τp`. -/
def rowTau (τp : TA B₂) :
    (L : List (Fin ℓ × Multiset I)) → Loadings (adjacentRow L M f β) →
      orderedProduct Q Λ botOrd (adjacentRow L M f β)
  | [], s => (τp ⊗ₜ spectatorsIdem Q Λ hQ M s.2 :
      (TA B₂) ⊗[k] orderedProduct Q Λ botOrd (M.map spectator))
  | x :: xs, s => (spectatorIdem Q Λ hQ x s.1 ⊗ₜ rowTau τp xs s.2 :
      (TA (spectator x)) ⊗[k] orderedProduct Q Λ botOrd (adjacentRow xs M f β))

/-- The relations of a row, from the relations `Hp` of the two-red factor. -/
def rowRelations (τp : TA B₂) (Hp : Submodule k (TA B₂)) :
    (L : List (Fin ℓ × Multiset I)) → (s : Loadings (adjacentRow L M f β)) →
      Submodule k (orderedProduct Q Λ botOrd (adjacentRow L M f β))
  | [], s => BlockCut.tensorRelations τp (spectatorsIdem Q Λ hQ M s.2) Hp
      (spectatorsRelations Q Λ hQ M s.2)
  | x :: xs, s => BlockCut.tensorRelations (spectatorIdem Q Λ hQ x s.1) (rowTau Q Λ hQ M f β τp xs s.2)
      ⊥ (rowRelations τp Hp xs s.2)

/-- **The generator of the crossing bimodule of a row** (Webster, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.9): a generator of the two-red factor, tensored with the spectator
loading idempotents. -/
theorem crossingProduct_generator {cp : (pairCut Q Λ hQ f β).space}
    {ep : quotientAlgebra Q Λ B₂} {τp : TA B₂} {Hp : Submodule k (TA B₂)}
    (hp : (pairCut Q Λ hQ f β).Generator
      (LinearMap.ofClass (orderedValue Q Λ hQ botOrd B₂)) cp ep τp Hp) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)),
      (crossingProduct Q Λ hQ M f β L).Generator
        (LinearMap.ofClass (orderedInclusion Q Λ hQ botOrd (adjacentRow L M f β)))
        (rowGen Q Λ hQ M f β cp L s) (rowTop Q Λ M f β ep L s) (rowTau Q Λ hQ M f β τp L s)
        (rowRelations Q Λ hQ M f β τp Hp L s)
  | [], s => by
    have g := (hp.tensor (spectatorCuts_generator Q Λ hQ M s.2)).congr_map (r' :=
      LinearMap.ofClass (orderedInclusion Q Λ hQ botOrd (adjacentRow [] M f β))) fun _ => rfl
    exact g
  | x :: xs, s => by
    have g := ((spectatorCut_generator_loading Q Λ hQ x s.1).tensor
      (crossingProduct_generator hp xs s.2)).congr_map (r' := LinearMap.ofClass
        (orderedInclusion Q Λ hQ botOrd (adjacentRow (x :: xs) M f β))) fun _ => rfl
    exact g

end Row

end Factors

end Categorification.Stendhal.RedBlock
