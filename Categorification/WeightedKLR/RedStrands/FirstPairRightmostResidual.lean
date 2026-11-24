/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairRightmostWeightOne
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The middle partial-standard quotient of the second spectator-crossing image

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
At final spectator weight one, the image of the second crossing modulo
the image of the strictly higher terminal kernel is the actual middle
partial standard.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

private theorem projective_of_exact_with_retraction {S V P I : Type*} [Semiring S]
    [AddCommGroup V] [AddCommGroup P] [AddCommGroup I]
    [Module S V] [Module S P] [Module S I]
    (incl : V →ₗ[S] P) (out : P →ₗ[S] I) (ret : P →ₗ[S] V)
    (hex : Function.Exact incl out) (surj : Function.Surjective out)
    (split : ret.comp incl = LinearMap.id) (projective : Module.Projective S P) :
    Module.Projective S I := by
  let : Module.Projective S P := projective
  have inj : Function.Injective incl := by
    intro x y eq
    exact (LinearMap.congr_fun split x).symm.trans
      ((congrArg ret eq).trans (LinearMap.congr_fun split y))
  obtain ⟨sectionMap,hsec⟩ := ((hex.split_tfae inj surj).out 2 1 rfl rfl).mp ⟨ret,split⟩
  exact Module.Projective.of_split sectionMap out hsec

private abbrev quotientModule {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (K : Submodule S M) : ModuleCat S :=
  ModuleCat.of S (M ⧸ K)

private abbrev quotientImageModule {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (K : Submodule S M) : ModuleCat S :=
  quotientModule (K.map f.rangeRestrict)

/-- Passing to the image of a linear map preserves the quotient by a
submodule containing the kernel. -/
private def quotientImageEquiv {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (f : M →ₗ[S] N) (K : Submodule S M)
    (h : LinearMap.ker f ≤ K) :
        quotientImageModule f K ≃ₗ[S] quotientModule K := by
  let image := K.map f.rangeRestrict
  let g := image.mkQ.comp f.rangeRestrict
  have hg : Function.Surjective g := by
    apply image.mkQ_surjective.comp
    rintro ⟨_, ⟨x, hx⟩⟩
    exact ⟨x, Subtype.ext hx⟩
  have hk : LinearMap.ker g = K := by
    ext x
    change g x = 0 ↔ x ∈ K
    rw [show g x = image.mkQ (f.rangeRestrict x) from rfl]
    change Submodule.Quotient.mk (f.rangeRestrict x) = 0 ↔ x ∈ K
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      obtain ⟨y, hy, eq⟩ := Submodule.mem_map.mp hx
      have diff : x - y ∈ LinearMap.ker f := by
        apply LinearMap.mem_ker.mpr
        rw [map_sub, show f y = f x from congrArg Subtype.val eq, sub_self]
      exact (sub_add_cancel x y) ▸ K.add_mem (h diff) hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  exact (g.quotKerEquivOfSurjective hg).symm.trans (Submodule.quotEquivOfEq _ _ hk)

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA MvPolynomial MulOpposite

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "B" => firstPairOneAfterSpectator true
local notation "D" => sadj N 3 • B
local notation "Rtop" => firstPairTwoAfterSpectator

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" s:arg => F (e s)
local notation "δ" => (ψw [3,2] * e B : A)
local notation "β" => (ψ 3 * e D : A)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν (redWord B)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord B))
local notation "T" => IsIdempotentElem.Corner ord
local notation "P" => rIdeal (orderedLoadingIdem Q Λ B)
private theorem firstPair_rightmost_same_order : redWord Rtop = redWord B := by decide

local notation "P'" =>
  rIdeal (orderedLoadingIdemAt Q Λ (redWord B) Rtop firstPair_rightmost_same_order)
local notation "K" => blockLoadingKernel Q Λ B 0 1
local notation "J" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 B) (redWord B)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

private theorem firstPair_secondCrossing_left :
    p Rtop * F δ = F δ := by
  have step : wordProd N [3,2] • B = Rtop := by decide +kernel
  rw [← map_mul F, ← step, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc,e_mul_self]

private theorem firstPair_secondCrossing_right :
    F δ * p B = F δ := by
  rw [← map_mul F,mul_assoc,e_mul_self]

private def secondSpectatorCrossingInCorner : T := by
  have Rcut := (Subsemigroup.mem_corner_iff ord).1
    (orderedLoadingIdemAt Q Λ (redWord B) Rtop firstPair_rightmost_same_order).2
  have Bcut := (Subsemigroup.mem_corner_iff ord).1 (orderedLoadingIdem Q Λ B).2
  change E * p Rtop = p Rtop ∧ p Rtop * E = p Rtop at Rcut
  change E * p B = p B ∧ p B * E = p B at Bcut
  have left := firstPair_secondCrossing_left Q Λ
  have right := firstPair_secondCrossing_right Q Λ
  refine ⟨F δ, (Subsemigroup.mem_corner_iff ord).2 ⟨?_,?_⟩⟩
  · calc
      E * F δ = E * (p Rtop * F δ) := congrArg (E * ·) left.symm
      _ = F δ := by rw [← mul_assoc, Rcut.1, left]
  · calc
      F δ * E = (F δ * p B) * E := congrArg (· * E) right.symm
      _ = F δ := by rw [mul_assoc, Bcut.2, right]

/-- The second spectator crossing as a map of loading projectives in the
original ordered corner. -/
def firstPairSecondSpectatorCrossing : P →ₗ[Tᵐᵒᵖ] P' where
  toFun y := ⟨secondSpectatorCrossingInCorner Q Λ * y.1, by
    apply Subtype.ext
    change p Rtop * (F δ * y.1.1) = F δ * y.1.1
    rw [← mul_assoc,firstPair_secondCrossing_left Q Λ]⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' c y := Subtype.ext (mul_assoc (secondSpectatorCrossingInCorner Q Λ) y.1 c.unop).symm

local notation "f" => firstPairSecondSpectatorCrossing Q Λ

private theorem firstPairSecondSpectatorCrossing_val (x : P) :
    (f x).1.1 = F δ * x.1.1 := rfl

private theorem firstPair_secondCrossing_kernel_le (one : Λ 2 () = 1) :
    LinearMap.ker f ≤ K := by
  intro y hy
  have l : p B * y.1.1 = y.1.1 := congrArg (fun z : T => z.1) y.2
  have z : F δ * y.1.1 = 0 :=
    (firstPairSecondSpectatorCrossing_val Q Λ y).symm.trans
      (congrArg (fun v : P' => v.1.1) (LinearMap.mem_ker.mp hy))
  obtain ⟨w, _, hw⟩ :=
    firstPairRightmost_secondCrossing_kernel_of_weight_one Q Λ one y.1.1 l z
  change y.1.1 ∈ J
  have strict : adjacentBlockRoot 0 1 B < adjacentBlockRoot 0 1 D := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 0 1 D 2 () ≤ adjacentBlockRoot 0 1 B 2 ()) (h 2 ())
  have dMem : p D ∈ J := TwoSidedIdeal.subset_span ⟨D, by decide, strict, rfl⟩
  have bMem : F β ∈ J := by
    rw [map_mul F]
    exact TwoSidedIdeal.mul_mem_left J _ _ dMem
  exact hw ▸ TwoSidedIdeal.mul_mem_right J _ w bMem

set_option backward.isDefEq.respectTransparency false in
/-- The second spectator-crossing image modulo the image of the strictly
higher terminal kernel, in the original red-order corner. -/
def firstPairSecondSpectatorCrossingResidual : ModuleCat Tᵐᵒᵖ := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup P' := Submodule.addCommGroup P'
  let : Module Tᵐᵒᵖ P' := Submodule.module P'
  exact quotientImageModule (S := Tᵐᵒᵖ) (M := P) («N» := P') f K

set_option backward.isDefEq.respectTransparency false in
/-- At final spectator weight one, the second-crossing image modulo the
image of the terminal higher kernel is the actual middle partial standard. -/
def firstPairSecondSpectatorCrossing_residualEquiv (one : Λ 2 () = 1) :
    firstPairSecondSpectatorCrossingResidual Q Λ ≃ₗ[Tᵐᵒᵖ]
      blockPartialStandardAt Q Λ B 0 1 (redWord B) rfl := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup P' := Submodule.addCommGroup P'
  let : Module Tᵐᵒᵖ P' := Submodule.module P'
  have e := quotientImageEquiv (S := Tᵐᵒᵖ) (M := P) («N» := P') f K
    (firstPair_secondCrossing_kernel_le Q Λ one)
  exact e

section NilHeckeRange

local notation "KR" => blockLoadingKernel Q Λ Rtop 0 1
local notation "JR" => blockUpperIdeal k Q Λ ν 0 1 (adjacentBlockRoot 0 1 Rtop) (redWord Rtop)

set_option backward.isDefEq.respectTransparency false in
private def rightmostNilHeckeMap : KR →ₗ[Tᵐᵒᵖ] KR :=
  blockLoadingKernel_nilHeckeCrossing Q Λ Rtop 0 1 3 (by decide) (by decide)

local notation "τR" => rightmostNilHeckeMap Q Λ

private theorem firstPair_secondCrossing_leg :
    F (hflip (ψw (rightPairWord 2 true) * e Rtop : A)) = F δ := by
  apply congrArg F
  rw [hflip_mul,hflip_e,hflip_ψw]
  change (e Rtop : A) * ψw [3,2] = δ
  have h : (wordProd N [3,2])⁻¹ • Rtop = B := by decide +kernel
  rw [e_mul_ψw,h]

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_secondCrossing_in_rightmostKernel (x : P) :
    f x ∈ KR := by
  have strict : adjacentBlockRoot 0 1 Rtop < adjacentBlockRoot 0 1 B := by
    apply lt_of_le_not_ge
    · intro r i
      fin_cases r <;> cases i <;> decide
    · intro h
      exact (by decide : ¬ adjacentBlockRoot 0 1 B 2 () ≤ adjacentBlockRoot 0 1 Rtop 2 ())
        (h 2 ())
  have source : p B ∈ JR := TwoSidedIdeal.subset_span ⟨B, by decide, strict, rfl⟩
  have coeff : F δ ∈ JR :=
    firstPair_secondCrossing_right Q Λ ▸ TwoSidedIdeal.mul_mem_left JR _ _ source
  change (f x).1.1 ∈ JR
  rw [firstPairSecondSpectatorCrossing_val Q Λ]
  exact TwoSidedIdeal.mul_mem_right JR _ _ coeff

set_option backward.isDefEq.respectTransparency false in
private def secondCrossingIntoRightmostKernel : P →ₗ[Tᵐᵒᵖ] KR :=
  LinearMap.codRestrict KR f (firstPair_secondCrossing_in_rightmostKernel Q Λ)

local notation "g" => secondCrossingIntoRightmostKernel Q Λ

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_secondCrossingIntoRightmostKernel_val (x : P) :
    (AddHom.toFun (LinearMap.toAddHom g) x).1.1.1 = F δ * x.1.1 :=
  firstPairSecondSpectatorCrossing_val Q Λ x

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_secondCrossing_range_eq_nilHecke (hQ : KLRSymm Q) :
    LinearMap.range g = LinearMap.range τR := by
  ext z
  have iff := firstPairTwoAfter_nilHecke_range_iff Q Λ hQ z
  change z ∈ LinearMap.range τR ↔
    ∃ y : V, p B * y = y ∧ y * E = y ∧
      z.1.1.1 = F (hflip (ψw (rightPairWord 2 true) * e Rtop : A)) * y at iff
  rw [firstPair_secondCrossing_leg Q Λ] at iff
  rw [iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1.1, congrArg (fun v : T => v.1) y.2,
      CornerEndomorphism.corner_mul_right ord y.1,
      firstPair_secondCrossingIntoRightmostKernel_val Q Λ y⟩
  · rintro ⟨y,left,right,eq⟩
    have Bcut := (Subsemigroup.mem_corner_iff ord).1 (orderedLoadingIdem Q Λ B).2
    change E * p B = p B ∧ p B * E = p B at Bcut
    have leftE : E * y = y := by
      calc
        E * y = E * (p B * y) := congrArg (E * ·) left.symm
        _ = y := by rw [← mul_assoc,Bcut.1,left]
    let c : T := ⟨y,(Subsemigroup.mem_corner_iff ord).2 ⟨leftE,right⟩⟩
    let w : P := ⟨c,Subtype.ext left⟩
    refine ⟨w,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (firstPair_secondCrossingIntoRightmostKernel_val Q Λ w).trans eq.symm

set_option backward.isDefEq.respectTransparency false in
private def secondCrossingRangeEquivSupport :
    LinearMap.range f ≃ₗ[Tᵐᵒᵖ] LinearMap.range g := by
  let map : LinearMap.range g →ₗ[Tᵐᵒᵖ] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) ((KR).subtype.comp (LinearMap.range g).subtype)
      (by rintro ⟨z,⟨x,rfl⟩⟩; exact ⟨x,rfl⟩)
  refine (LinearEquiv.ofBijective map ⟨?_,?_⟩).symm
  · intro x y eq
    have val : (map x).1 = (map y).1 := congrArg (fun v : LinearMap.range f => v.1) eq
    apply Subtype.ext
    apply Subtype.ext
    exact val
  · rintro ⟨z,⟨x,rfl⟩⟩
    exact ⟨⟨g x, x, rfl⟩,rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The second spectator-crossing image is the summand in the actual
rightmost higher kernel's nilHecke splitting. -/
def firstPairSecondSpectatorCrossing_rangeEquivNilHecke (hQ : KLRSymm Q) :
    LinearMap.range f ≃ₗ[Tᵐᵒᵖ] LinearMap.range τR :=
  (secondCrossingRangeEquivSupport Q Λ).trans
    (LinearEquiv.ofEq _ _ (firstPair_secondCrossing_range_eq_nilHecke Q Λ hQ))

end NilHeckeRange

section TerminalMap

private theorem firstPair_terminal_same_order : redWord D = redWord B := by decide

local notation "PD" =>
  rIdeal (orderedLoadingIdemAt Q Λ (redWord B) D firstPair_terminal_same_order)

private def supportedCornerMul {s t : Seq μ} (hs : redWord s = redWord B)
    (ht : redWord t = redWord B) (c : V) (left : p t * c = c) (right : c * p s = c) :
    rIdeal (orderedLoadingIdemAt Q Λ (redWord B) s hs) →ₗ[Tᵐᵒᵖ]
      rIdeal (orderedLoadingIdemAt Q Λ (redWord B) t ht) := by
  have sl := (Subsemigroup.mem_corner_iff ord).1 (orderedLoadingIdemAt Q Λ (redWord B) s hs).2
  have tl := (Subsemigroup.mem_corner_iff ord).1 (orderedLoadingIdemAt Q Λ (redWord B) t ht).2
  change E * p s = p s ∧ p s * E = p s at sl
  change E * p t = p t ∧ p t * E = p t at tl
  have el : E * c = c := by
    calc
      E * c = E * (p t * c) := congrArg (E * ·) left.symm
      _ = c := by rw [← mul_assoc,tl.1,left]
  have er : c * E = c := by
    calc
      c * E = (c * p s) * E := congrArg (· * E) right.symm
      _ = c := by rw [mul_assoc,sl.2,right]
  let cT : T := ⟨c,(Subsemigroup.mem_corner_iff ord).2 ⟨el,er⟩⟩
  exact
    { toFun := fun x => ⟨cT * x.1, by
        apply Subtype.ext
        change p t * (c * x.1.1) = c * x.1.1
        rw [← mul_assoc,left]⟩
      map_add' := fun x y => Subtype.ext (mul_add cT x.1 y.1)
      map_smul' := fun r x => Subtype.ext (mul_assoc cT x.1 r.unop).symm }

private theorem firstPair_terminalCrossing_left : p B * F β = F β := by
  have shift : sadj N 3 • D = B := sadj_smul_smul ..
  rw [← map_mul F,ψ_mul_e,shift,← mul_assoc,e_mul_self]

private theorem firstPair_terminalCrossing_right : F β * p D = F β := by
  rw [← map_mul F,mul_assoc,e_mul_self]

/-- The terminal crossing into the one-after-spectator loading, over
the original ordered corner. -/
def firstPairTerminalSpectatorCrossing : PD →ₗ[Tᵐᵒᵖ] P :=
  supportedCornerMul Q Λ firstPair_terminal_same_order rfl (F β)
    (firstPair_terminalCrossing_left Q Λ) (firstPair_terminalCrossing_right Q Λ)

local notation "bmap" => firstPairTerminalSpectatorCrossing Q Λ

private theorem firstPair_terminalSpectatorCrossing_val (x : PD) :
    (bmap x).1.1 = F β * x.1.1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual higher-cut kernel at the middle loading is exactly the
terminal crossing image inside its loading projective. -/
theorem firstPairTerminalSpectatorCrossing_range (hQ : KLRSymm Q) :
    LinearMap.range bmap = K := by
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    change (bmap u).1.1 ∈ J
    rw [firstPair_terminalSpectatorCrossing_val Q Λ]
    have strict : adjacentBlockRoot 0 1 B < adjacentBlockRoot 0 1 D := by
      apply lt_of_le_not_ge
      · intro r i
        fin_cases r <;> cases i <;> decide
      · intro h
        exact (by decide : ¬ adjacentBlockRoot 0 1 D 2 () ≤ adjacentBlockRoot 0 1 B 2 ())
          (h 2 ())
    have dMem : p D ∈ J := TwoSidedIdeal.subset_span ⟨D, by decide, strict, rfl⟩
    have bMem : F β ∈ J := by
      rw [map_mul F]
      exact TwoSidedIdeal.mul_mem_left J _ _ dMem
    exact TwoSidedIdeal.mul_mem_right J _ _ bMem
  · intro hz
    have left := congrArg (fun x : T => x.1) z.2
    have right : z.1.1 * E = z.1.1 := CornerEndomorphism.corner_mul_right ord z.1
    obtain ⟨u,hu,rep⟩ := firstPairOneAfter_blockKernel_principal Q Λ true hQ z.1.1 hz left
    have Dcut := (Subsemigroup.mem_corner_iff ord).1
      (orderedLoadingIdemAt Q Λ (redWord B) D firstPair_terminal_same_order).2
    change E * p D = p D ∧ p D * E = p D at Dcut
    let v := u * E
    have vl : p D * v = v := by
      change p D * (u * E) = u * E
      rw [← mul_assoc,hu]
    have el : E * v = v := by
      calc
        E * v = E * (p D * v) := congrArg (E * ·) vl.symm
        _ = v := by rw [← mul_assoc,Dcut.1,vl]
    have er : v * E = v := by
      change (u * E) * E = u * E
      rw [mul_assoc,(ord).eq]
    let d : T := ⟨v,(Subsemigroup.mem_corner_iff ord).2 ⟨el,er⟩⟩
    let x : PD := ⟨d,Subtype.ext vl⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [firstPair_terminalSpectatorCrossing_val Q Λ]
    change F β * (u * E) = z.1.1
    rw [← mul_assoc,rep,right]

set_option backward.isDefEq.respectTransparency false in
/-- The lower submodule of the second-crossing image is the composite
image of the two spectator crossings from the terminal projective. -/
theorem firstPairSpectatorCompositeImage_eq (hQ : KLRSymm Q) :
    LinearMap.range ((LinearMap.rangeRestrict f).comp bmap) =
      (K).map (LinearMap.rangeRestrict f) := by
  rw [LinearMap.range_comp, firstPairTerminalSpectatorCrossing_range Q Λ hQ]

section TerminalProduct

local notation "τ" => (ψ 2 * e D : A)
local notation "σ" => (ψw [3,3] * e D : A)
local notation "double" => (ψw [2,3] * e D : A)

private theorem firstPair_terminal_beta_left :
    (e B : A) * β = β := by
  have s : sadj N 3 • D = B := sadj_smul_smul ..
  rw [ψ_mul_e, s, ← mul_assoc, e_mul_self]

private theorem firstPair_terminal_tau_left :
    (e D : A) * τ = τ := by
  have s : sadj N 2 • D = D := by decide +kernel
  rw [ψ_mul_e, s, ← mul_assoc, e_mul_self]

private theorem firstPair_terminal_sigma_left :
    (e D : A) * σ = σ := by
  have s : wordProd N [3,3] • D = D := by decide +kernel
  have sinv : (wordProd N [3,3])⁻¹ • D = D := by
    calc
      _ = (wordProd N [3,3])⁻¹ • (wordProd N [3,3] • D) :=
        congrArg ((wordProd N [3,3])⁻¹ • ·) s.symm
      _ = _ := inv_smul_smul ..
  rw [← mul_assoc, e_mul_ψw, sinv, mul_assoc, e_mul_self]

private theorem firstPair_terminal_gamma_beta : γ * β = τ * σ := by
  have aux : ((ψw [2,3] : A) * β) = (ψ 2 : A) * σ := by
    simp only [ψw_cons, ψw_nil, mul_one, mul_assoc]
  rw [mul_assoc (ψw [2,3]), firstPair_terminal_beta_left Q Λ,
    mul_assoc (ψ 2), firstPair_terminal_sigma_left Q Λ]
  exact aux

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_terminal_delta_beta : δ * β = double * τ := by
  have h₂ : (D).lbl ⟨2, by decide⟩ = Sum.inl () := by decide
  have h₄ : (D).lbl ⟨4, by decide⟩ = Sum.inr 2 := by decide
  have ne : (Sum.inl () : Unit ⊕ Fin 3) ≠ Sum.inr 2 := by decide
  have br := braid (Q := stendhalQ Q Λ) 2 (by decide) D
  rw [h₂,h₄] at br
  simp [ne] at br
  let c : A := ψ 2 * ψ 3 * ψ 2
  let d : A := ψ 3 * ψ 2 * ψ 3
  have br₀ : (c - d) * e D = 0 := br
  have eq : c * e D = d * e D := sub_eq_zero.mp ((sub_mul c d (e D)).symm.trans br₀)
  rw [mul_assoc (ψw [3,2]),firstPair_terminal_beta_left Q Λ,
    mul_assoc (ψw [2,3]),firstPair_terminal_tau_left Q Λ]
  simpa only [ψw_cons, ψw_nil, mul_one, mul_assoc] using (show (ψ 3 * ψ 2 * ψ 3 : A) * e D = (ψ 2 * ψ 3 * ψ 2 : A) * e D from eq.symm)

private theorem firstPair_terminal_tau_sq : τ * τ = 0 := by
  have equal : (D).lbl ⟨2, by decide⟩ = (D).lbl ⟨3, by decide⟩ := by decide
  have sq := ψ_sq (Q := stendhalQ Q Λ) 2 (by decide) D
  rw [ite_eq_left equal] at sq
  rw [mul_assoc (ψ 2),firstPair_terminal_tau_left Q Λ,← mul_assoc (ψ 2)]
  exact sq


local notation "α" => (ψ 3 * e B : A)
local notation "dot₃" => (x (⟨3,by decide⟩ : Fin N) : A)
local notation "dot₂" => (x (⟨2,by decide⟩ : Fin N) : A)

private theorem firstPair_terminal_alpha_left : (e D : A) * α = α := by
  rw [ψ_mul_e,← mul_assoc,e_mul_self]

private theorem firstPair_terminal_gamma_factor : γ = τ * α := by
  rw [mul_assoc (ψ 2),firstPair_terminal_alpha_left Q Λ]
  simp only [ψw_cons,ψw_nil,mul_one,mul_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_terminal_weightOne_return (one : Λ 2 () = 1) :
    σ = (dot₃ * e D : A) := by
  have labels₃ : (D).lbl ⟨3,by decide⟩ = .inl () := by decide
  have labels₄ : (D).lbl ⟨4,by decide⟩ = .inr 2 := by decide
  have sq := ψ_sq (Q := stendhalQ Q Λ) 3 (by decide) D
  rw [labels₃,labels₄,ite_eq_right Sum.inl_ne_inr,stendhalQ_inl_inr,one,pow_one] at sq
  let dots : Fin 2 → Fin N := ![⟨3,by decide⟩,⟨4,by decide⟩]
  have indices : ![dot₃,(x ⟨4,by decide⟩ : A)] = fun a => x (dots a) := by
    funext a
    fin_cases a <;> rfl
  have ev : ncEval ![dot₃,(x ⟨4,by decide⟩ : A)] (X 0 : MvPolynomial (Fin 2) k) = dot₃ := by
    rw [indices]
    calc
      _ = x (dots 0) := by
        simpa only [rename_X,pol_X] using
          (ncEval_eq_pol (Q := stendhalQ Q Λ) dots (X 0 : MvPolynomial (Fin 2) k))
      _ = dot₃ := congrArg (fun a : Fin N => (x a : A)) (show dots 0 = ⟨3,by decide⟩ from rfl)
  have raw : ((ψ 3 * ψ 3 : A) * e D) = dot₃ * e D := sq.trans (congrArg (· * e D) ev)
  simpa only [ψw_cons,ψw_nil,mul_one,mul_assoc] using raw

set_option backward.isDefEq.respectTransparency false in
private theorem firstPair_terminal_weightOne_section (one : Λ 2 () = 1) :
    -(γ * β * τ) = τ := by
  have dleft : (e D : A) * (dot₃ * e D) = dot₃ * e D := by
    rw [← mul_assoc,← x_mul_e,mul_assoc,e_mul_self]
  have relation : (dot₂ * τ - τ * (dot₃ * e D) : A) = e D := by
    calc
      _ = (dot₂ * ψ 2 - ψ 2 * dot₃) * e D := by
        rw [mul_assoc (ψ 2) (e D), dleft]
        simp only [mul_assoc,sub_mul]
      _ = _ := by rw [dot_cross_left 2 (by decide : 2+1 < N),ite_eq_left (by decide)]
  have h := congrArg (· * τ) relation
  rw [sub_mul,mul_assoc dot₂,firstPair_terminal_tau_sq Q Λ,mul_zero,zero_sub,
    firstPair_terminal_tau_left Q Λ] at h
  rw [firstPair_terminal_gamma_beta Q Λ, firstPair_terminal_weightOne_return Q Λ one]
  exact h

end TerminalProduct

local notation "τD" => (ψ 2 * e D : A)

private theorem terminal_nilHecke_left : p D * F τD = F τD :=
  (map_mul F _ _).symm.trans (congrArg F (firstPair_terminal_tau_left Q Λ))

/-- The equal-black crossing on the terminal loading projective. -/
def firstPairTerminalNilHeckeCrossing : PD →ₗ[Tᵐᵒᵖ] PD :=
  supportedCornerMul Q Λ firstPair_terminal_same_order firstPair_terminal_same_order (F τD)
    (terminal_nilHecke_left Q Λ) (by rw [← map_mul F,mul_assoc,e_mul_self])

local notation "tauTerm" => firstPairTerminalNilHeckeCrossing Q Λ

private theorem terminal_nilHecke_val (y : PD) :
    (tauTerm y).1.1 = F τD * y.1.1 := rfl


local notation "α" => (ψ 3 * e B : A)
local notation "γ" => (ψw [2,3] * e B : A)
local notation "ρ" => (ψ 2 * e Rtop : A)

private def middleToTerminalReturn : P →ₗ[Tᵐᵒᵖ] PD :=
  supportedCornerMul Q Λ rfl firstPair_terminal_same_order (-F α)
    (by rw [mul_neg, ← map_mul F, firstPair_terminal_alpha_left Q Λ])
    (by rw [neg_mul, ← map_mul F, mul_assoc,e_mul_self])

private theorem middleToTerminalReturn_val (y : P) :
    (middleToTerminalReturn Q Λ y).1.1 = (-F α) * y.1.1 := rfl

/-- At final spectator weight one, the negative other braid path maps the
middle loading projective to the terminal nilHecke image. -/
def middleToTerminalNilHeckeImage : P →ₗ[Tᵐᵒᵖ] LinearMap.range tauTerm :=
  (LinearMap.rangeRestrict tauTerm).comp (middleToTerminalReturn Q Λ)

local notation "sectionRet" => middleToTerminalNilHeckeImage Q Λ

private theorem middleToTerminalNilHeckeImage_val (y : P) :
    (sectionRet y).1.1.1 = -(F γ * y.1.1) := by
  change (tauTerm (middleToTerminalReturn Q Λ y)).1.1 = _
  rw [terminal_nilHecke_val Q Λ,middleToTerminalReturn_val Q Λ,neg_mul,mul_neg,← mul_assoc,← map_mul F,
    ← firstPair_terminal_gamma_factor Q Λ]

/-- The terminal spectator crossing on the divided terminal summand. -/
def terminalNilHeckeImageToMiddle : LinearMap.range tauTerm →ₗ[Tᵐᵒᵖ] P :=
  (bmap).comp (LinearMap.range tauTerm).subtype

local notation "incl" => terminalNilHeckeImageToMiddle Q Λ

private theorem terminalNilHeckeImageToMiddle_val (z : LinearMap.range tauTerm) :
    (incl z).1.1 = F β * z.1.1.1 :=
  firstPair_terminalSpectatorCrossing_val Q Λ z.1

private theorem terminalImage_split (one : Λ 2 () = 1) (z : LinearMap.range tauTerm) :
    sectionRet (incl z) = z := by
  obtain ⟨x,hx⟩ := z.2
  have value : F τD * x.1.1 = z.1.1.1 :=
    (terminal_nilHecke_val Q Λ x).symm.trans (congrArg (fun v : PD => v.1.1) hx)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [middleToTerminalNilHeckeImage_val Q Λ,terminalNilHeckeImageToMiddle_val Q Λ,← value]
  simpa only [map_neg,map_mul F,neg_mul,mul_assoc] using
    congrArg (fun c : A => F c * x.1.1) (firstPair_terminal_weightOne_section Q Λ one)

/-- The divided terminal summand includes into the middle loading
projective by a split monomorphism. -/
theorem terminalNilHeckeImageToMiddle_split (one : Λ 2 () = 1) :
    (sectionRet).comp incl = LinearMap.id :=
  LinearMap.ext (terminalImage_split Q Λ one)

set_option backward.isDefEq.respectTransparency false in
/-- At spectator weight one, the kernel of the second crossing consists
exactly of the divided terminal summand embedded by the first crossing. -/
theorem terminalNilHeckeImage_range_eq_secondCrossing_ker (one : Λ 2 () = 1) :
    LinearMap.range incl = LinearMap.ker f := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨x,hx⟩ := z.2
    have value : F τD * x.1.1 = z.1.1.1 :=
      (terminal_nilHecke_val Q Λ x).symm.trans (congrArg (fun v : PD => v.1.1) hx)
    have kill : (δ * β) * τD = 0 := by
      rw [firstPair_terminal_delta_beta Q Λ,mul_assoc,firstPair_terminal_tau_sq Q Λ,mul_zero]
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    apply Subtype.ext
    change (f (incl z)).1.1 = (0 : V)
    rw [firstPairSecondSpectatorCrossing_val Q Λ,terminalNilHeckeImageToMiddle_val Q Λ,← value]
    simpa only [map_mul F,map_zero,mul_assoc,zero_mul] using
      congrArg (fun c : A => F c * x.1.1) kill
  · intro hy
    have zero : F δ * y.1.1 = 0 := (firstPairSecondSpectatorCrossing_val Q Λ y).symm.trans
      (congrArg (fun z : P' => z.1.1) (LinearMap.mem_ker.mp hy))
    have yleft : p B * y.1.1 = y.1.1 := congrArg (fun z : T => z.1) y.2
    have relation : F ρ * F δ - F β * F γ = p B := by
      calc
        _ = F (ρ * δ) - F (β * γ) :=
          congrArg₂ (· - ·) (map_mul F ρ δ).symm (map_mul F β γ).symm
        _ = F (ρ * δ - β * γ) := (map_sub F _ _).symm
        _ = p B := congrArg F (firstPair_rightmost_weightOne_braid Q Λ one)
    have br := congrArg (fun c : V => c * y.1.1) relation
    rw [sub_mul,mul_assoc (F ρ),mul_assoc (F β),zero,mul_zero,zero_sub,yleft] at br
    refine ⟨sectionRet y,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [terminalNilHeckeImageToMiddle_val Q Λ,middleToTerminalNilHeckeImage_val Q Λ,mul_neg]
    exact br


set_option backward.isDefEq.respectTransparency false in
/-- At final spectator weight one, the second crossing image is a direct
summand of the middle loading projective. -/
theorem firstPairSecondSpectatorCrossing_range_projective_of_weight_one (one : Λ 2 () = 1) :
    Module.Projective Tᵐᵒᵖ (LinearMap.range f) := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let : AddCommGroup P' := Submodule.addCommGroup P'
  let : Module Tᵐᵒᵖ P' := Submodule.module P'
  let : AddCommGroup PD := Submodule.addCommGroup PD
  let : Module Tᵐᵒᵖ PD := Submodule.module PD
  let domain : Submodule Tᵐᵒᵖ PD := LinearMap.range tauTerm
  let image : Submodule Tᵐᵒᵖ P' := LinearMap.range f
  let : AddCommGroup domain := Submodule.addCommGroup (R := Tᵐᵒᵖ) (M := PD) domain
  let : Module Tᵐᵒᵖ domain := Submodule.module (R := Tᵐᵒᵖ) (M := PD) domain
  let : AddCommGroup image := Submodule.addCommGroup (R := Tᵐᵒᵖ) (M := P') image
  let : Module Tᵐᵒᵖ image := Submodule.module (R := Tᵐᵒᵖ) (M := P') image
  let out : P →ₗ[Tᵐᵒᵖ] image := LinearMap.rangeRestrict f
  have hex : Function.Exact incl out := by
    rw [LinearMap.exact_iff, show LinearMap.ker out = LinearMap.ker f from LinearMap.ker_rangeRestrict f]
    exact (terminalNilHeckeImage_range_eq_secondCrossing_ker Q Λ one).symm
  have surj : Function.Surjective out := by
    rintro ⟨_,⟨x,hx⟩⟩
    exact ⟨x,Subtype.ext hx⟩
  exact projective_of_exact_with_retraction incl out sectionRet hex surj
    (terminalNilHeckeImageToMiddle_split Q Λ one) (blockLoading_projective Q Λ B)

set_option backward.isDefEq.respectTransparency false in
/-- The entire rightmost higher-cut kernel is projective when the final
spectator pairing is one. -/
theorem firstPairRightmost_blockLoadingKernel_projective_of_weight_one (hQ : KLRSymm Q)
    (one : Λ 2 () = 1) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k Q Λ ν (redWord Rtop)).Cornerᵐᵒᵖ
      (blockLoadingKernel Q Λ Rtop 0 1) := by
  let : Module.Projective Tᵐᵒᵖ (LinearMap.range f) :=
    firstPairSecondSpectatorCrossing_range_projective_of_weight_one Q Λ one
  let equiv := firstPairSecondSpectatorCrossing_rangeEquivNilHecke Q Λ hQ
  let image := LinearMap.range (rightmostNilHeckeMap Q Λ)
  let : Module.Projective Tᵐᵒᵖ image := Module.Projective.of_equiv equiv
  let : Module.Projective Tᵐᵒᵖ (image × image) := inferInstance
  let split : blockLoadingKernel Q Λ Rtop 0 1 ≃ₗ[Tᵐᵒᵖ] image × image :=
    firstPairTwoAfter_equiv_nilHeckeRangeProd Q Λ
  change Module.Projective Tᵐᵒᵖ (blockLoadingKernel Q Λ Rtop 0 1)
  exact Module.Projective.of_equiv split.symm

end TerminalMap

end Categorification.Stendhal.BraidedStendhalAlgebra
