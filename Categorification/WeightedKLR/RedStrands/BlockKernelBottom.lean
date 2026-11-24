/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelCut
import Categorification.WeightedKLR.RedStrands.PairedRedColumn

/-!
# Bottom loading components of the tensor kernel

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21). At a bottom
loading where the two crossing red strands occupy consecutive positions, take their
crossing as the common last factor. After moving its ordered coefficient into `K` by
balancing, Proposition 6.4 detects the upper factor of an affine relation. This
eliminates these loading components of the kernel, not the components with a black
strand between the two bottom reds.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (s : KLR.Seq (stendhalWeight ℓ ν))
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "p" => fun j => ofKLR k Q Λ ν (KLRAlgebra.e j)
local notation "E" => redProj k Q Λ ν (redWord t)
local notation "F" => redProj k Q Λ ν (redWord s)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "B" => RedBlock.crossingSpace (k := k) (mk E) (mk F)
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "Z" => BalancedTensor k k T K B
local notation "U" => blockKernelUpper Q Λ t a b
local notation "mult" => blockKernelCutStack Q Λ t a b (redWord s)
local notation "cl" => blockKernelCut Q Λ t a b (redWord s)
local notation "upper" => blockKernelUpperClass Q Λ t a b
local notation "lower" => blockKernelLowerClass Q Λ t (redWord s)

private def loadingOnLower : B →ₗ[k] B :=
  ((LinearMap.mulRight k (mk (p s))).comp (B).subtype).codRestrict B fun y => by
    change mk E * (y.1 * mk (p s)) = y.1 * mk (p s) ∧ y.1 * mk (p s) * mk F = y.1 * mk (p s)
    constructor
    · rw [← mul_assoc, y.2.1]
    · rw [mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left rfl]

/-- Right multiplication at the bottom by `e(s)` on the tensor with upper factor `K`. -/
def blockKernelBottom : Z →ₗ[k] Z :=
  BalancedTensor.lift ((BalancedTensor.mkBil k k T K B).compl₂ (loadingOnLower Q Λ t s))
    (fun x r y => by
      change BalancedTensor.tmul (op r • x) _ = BalancedTensor.tmul x _
      rw [BalancedTensor.op_smul_tmul]
      apply congrArg; exact Subtype.ext (mul_assoc r.1 y.1 (mk (p s))).symm)

local notation "botMap" => blockKernelBottom Q Λ t a b s

private def prefixMap : U →ₗ[k] A :=
  LinearMap.mulRight k E ∘ₗ LinearMap.mulLeft k (p t) ∘ₗ (U).subtype
local notation "pre" => prefixMap Q Λ t a b

private theorem upper_val (x : U) : (upper x).1.1.1 = mk (pre x) := by
  change (blockLoadingRep Q Λ t (mk x.1)).1.1 = mk (p t * x.1 * E)
  rw [blockLoadingRep_val, map_mul, map_mul]

private theorem slide_last (x : U) (y C d : A) (hl : E*d = d) (hr : d*E = d)
    (hc : E*C = C) (hc' : C*F = C) (hy : E*y*p s = d*C) :
    ∃ v : U, pre v = pre x * d ∧
      botMap (cl (x ⊗ₜ y)) = BalancedTensor.tmul (upper v) (lower C) := by
  let v : U := ⟨x.1*d, by
    change mk (x.1*d) ∈ blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
    rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ x.2⟩
  have hpre : pre v = pre x * d := by
    change p t * (x.1*d) * E = p t * x.1 * E * d
    simp only [mul_assoc,hl,hr]
  let r : T := ⟨mk d, (Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
    ⟨by rw [← map_mul,hl],by rw [← map_mul,hr]⟩⟩
  have hu : op r • upper x = upper v := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (upper x).1.1.1 * mk d = (upper v).1.1.1
    rw [upper_val,upper_val,hpre,map_mul]
  have hb : loadingOnLower Q Λ t s (lower y) = r • lower C := by
    apply Subtype.ext
    change mk (E*y*F) * mk (p s) = mk d * mk (E*C*F)
    rw [hc,hc',← map_mul,← map_mul,← hy,mul_assoc _ F,redProj_mul_e,ite_eq_left rfl]
  refine ⟨v,hpre,?_⟩
  change BalancedTensor.tmul (upper x) (loadingOnLower Q Λ t s (lower y)) = _
  rw [hb, ← BalancedTensor.op_smul_tmul, hu]

private theorem gather_pure (u : KLR.Seq (stendhalWeight ℓ ν)) (C : A) (hc : E*C = C)
    (hs : C*p s = C) (hd : ∀ y : A, ∃ d : A, E*d = d ∧ d*E = d ∧ d*p u = d ∧ E*y*p s = d*C)
    (x : U) (y : A) : ∃ v : U, pre v * p u = pre v ∧
      mult (x ⊗ₜ y) * p s = pre v * C ∧ botMap (cl (x ⊗ₜ y)) = BalancedTensor.tmul (upper v) (lower C) := by
  have hc' : C*F = C := by rw [← hs, mul_assoc,e_mul_redProj,ite_eq_left rfl]
  let d := (hd y).choose
  have hd' := (hd y).choose_spec
  have slid := slide_last Q Λ t a b s x y C d hd'.1 hd'.2.1 hc hc' hd'.2.2.2
  let v := slid.choose
  have hv : pre v = pre x * d := slid.choose_spec.1
  have hu : d*p u = d := hd'.2.2.1
  have hy : E*y*p s = d*C := hd'.2.2.2
  have hl : E*d = d := hd'.1
  refine ⟨v,by rw [hv,mul_assoc,hu],?_,slid.choose_spec.2⟩
  rw [blockKernelCutStack_tmul,hv]
  change p t * x.1 * E * (y*F) * p s = p t * x.1 * E * d * C
  rw [mul_assoc _ (y*F), mul_assoc y F,redProj_mul_e,ite_eq_left rfl]
  rw [mul_assoc (p t * x.1) E, ← mul_assoc E y,hy, mul_assoc _ E d,hl,mul_assoc]
  simp only [mul_assoc]

private theorem gather_linear {X Y D W : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup D] [Module k D] [AddCommGroup W] [Module k W]
    (l r m : X →ₗ[k] D) (c : X →ₗ[k] W) (d : X ⊗[k] Y →ₗ[k] D) (f : X ⊗[k] Y →ₗ[k] W)
    (base : ∀ x y, ∃ v, l v = r v ∧ d (x ⊗ₜ y) = m v ∧ f (x ⊗ₜ y) = c v)
    (z : X ⊗[k] Y) : ∃ v, l v = r v ∧ d z = m v ∧ f z = c v := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    obtain ⟨v,hv,hm,hb⟩ := hz
    obtain ⟨v',hv',hm',hb'⟩ := hz'
    exact ⟨v+v',by rw [map_add,map_add,hv,hv'],by rw [map_add,map_add,hm,hm'],
      by rw [map_add,map_add,hb,hb']⟩
  | tmul x y => exact base x y

private theorem gather_last (u : KLR.Seq (stendhalWeight ℓ ν)) (C : A) (hc : E*C = C)
    (hs : C*p s = C) (hd : ∀ y : A, ∃ d : A, E*d = d ∧ d*E = d ∧ d*p u = d ∧ E*y*p s = d*C)
    (z : U ⊗[k] A) : ∃ v : U, pre v * p u = pre v ∧
      mult z * p s = pre v * C ∧ botMap (cl z) = BalancedTensor.tmul (upper v) (lower C) :=
  gather_linear (k := k) (X := U) (Y := A) (D := A) (W := Z)
    ((LinearMap.mulRight k (p u)).comp pre) pre ((LinearMap.mulRight k C).comp pre)
    (((BalancedTensor.mkBil k k T K B).flip (lower C)).comp upper)
    ((LinearMap.mulRight k (p s)).comp mult) ((botMap).comp cl)
    (gather_pure Q Λ t a b s u C hc hs hd) z

private theorem bottom_of_zero (u : KLR.Seq (stendhalWeight ℓ ν)) (C : A) (hc : E*C = C)
    (hs : C*p s = C) (hd : ∀ y : A, ∃ d : A, E*d = d ∧ d*E = d ∧ d*p u = d ∧ E*y*p s = d*C)
    (cancel : ∀ d : A, E*d = d → d*p u = d → d*C = 0 → mk d = 0)
    (z : U ⊗[k] A) (hz : mult z = 0) : botMap (cl z) = 0 := by
  have H := gather_last Q Λ t a b s u C hc hs hd z
  let v := H.choose
  have he : E * pre v = pre v := by
    change E * (p t * v.1 * E) = p t * v.1 * E
    rw [← mul_assoc, ← mul_assoc, redProj_mul_e, ite_eq_left rfl]
  have zero : mk (pre v) = 0 := cancel _ he H.choose_spec.1
    (H.choose_spec.2.1.symm.trans (by rw [hz,zero_mul]))
  have hupper : upper v = 0 := Subtype.ext (Subtype.ext (Subtype.ext ((upper_val Q Λ t a b v).trans zero)))
  have vanish := congrArg (fun x : K => (BalancedTensor.tmul x (lower C) : Z)) hupper
  exact H.choose_spec.2.2.trans (vanish.trans (BalancedTensor.zero_tmul (lower C)))

private theorem le_ker_of_markings {X Y D W : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup D] [Module k D] [AddCommGroup W] [Module k W]
    (i : Y →ₗ[k] D) (f : Y →ₗ[k] Y) (m : X →ₗ[k] W) (c : X →ₗ[k] Y)
    (h : LinearMap.ker i = (LinearMap.ker m).map c) (hz : ∀ z, m z = 0 → f (c z) = 0) :
    LinearMap.ker i ≤ LinearMap.ker f := by rw [h]; rintro _ ⟨z,hz',rfl⟩; exact hz z hz'

/-- **Consecutive bottom positions in (6.21)** (Webster v2, Lemma 6.8, §6.1).
A class killed in the projective tensor has zero component at the exchanged bottom
loading `s` if the two reds are physically adjacent there. `t` and all spectator and
black contents are otherwise arbitrary; no projectivity of the braiding is assumed. -/
theorem ker_blockKernelTensorInclusion_le_ker_bottom (hQ : KLRSymm Q)
    (L M : List (Fin ℓ)) (ht : redWord t = L ++ a :: b :: M)
    (u : KLR.Seq (stendhalWeight ℓ ν)) (hu : redWord u = redWord t)
    (n : ℕ) (hn : n+1 < (stendhalWeight ℓ ν).card)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,hn⟩ = .inr b)
    (hs : sadj (stendhalWeight ℓ ν).card n • u = s) :
    LinearMap.ker (blockKernelTensorInclusion Q Λ t a b (redWord s)) ≤ LinearMap.ker botMap := by
  have H := exists_pairedRedColumn (Q := Q) (Λ := Λ) hQ hn ha hb (hu.trans ht)
  rw [hs, ← ht] at H
  exact le_ker_of_markings (k := k) (X := U ⊗[k] A) (Y := Z) (W := A)
    (D := BalancedTensor k k T (rIdeal (orderedLoadingIdem Q Λ t)) B)
    (blockKernelTensorInclusion Q Λ t a b (redWord s)) botMap mult cl
    (ker_blockKernelTensorInclusion_eq_map Q Λ t a b (redWord s) hQ)
    (bottom_of_zero Q Λ t a b s u H.choose H.choose_spec.1 H.choose_spec.2.1
      H.choose_spec.2.2.1 H.choose_spec.2.2.2)

end Categorification.Stendhal.BraidedStendhalAlgebra
