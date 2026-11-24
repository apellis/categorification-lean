/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairRightmostWeightOne
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
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

end TerminalMap

end Categorification.Stendhal.BraidedStendhalAlgebra
