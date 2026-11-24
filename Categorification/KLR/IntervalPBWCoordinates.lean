/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.BasisTheoremGeneral
import Categorification.TypeA.IntervalPBW

/-!
# Exterior coefficients in an interval PBW decomposition

For the interleaved relation in Webster, arXiv:1309.3796v2, §6.1, after (6.21),
one can test an affine relation separately at each sorted exterior permutation.
The local terms use the chosen reduced word for the interval permutation and
arbitrary bottom dots on all strands. Colours may repeat within and
outside the interval.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {ν : Multiset I}
    {p n r : ℕ} (h : p+(n+r)=ν.card)

local notation "m" => Multiset.card ν
local notation "R" => KLRAlgebra k Q ν
local notation "S" t:arg => Perm (Fin t)

/-- The interval summands before attaching an exterior word. Dots at all ambient
positions and all bottom loadings are allowed. -/
def intervalPBWSpan : Submodule k R :=
  Submodule.span k {x | ∃ (s : Seq ν) (v : S n) (d : Fin m →₀ ℕ),
    x = ψw (shiftWord p (TypeA.canWord n v)) * pol (monomial d 1) * e s}

local notation "M" => intervalPBWSpan Q (ν := ν) (p := p) (n := n)

theorem intervalPBWSpan_monomial (s : Seq ν) (v : S n) (d : Fin m →₀ ℕ) :
    (ψw (shiftWord p (TypeA.canWord n v)) * pol (monomial d 1) * e s : R) ∈ M :=
  Submodule.subset_span ⟨s,v,d,rfl⟩

/-- Every ambient bottom polynomial gives an interval coefficient. -/
theorem intervalPBWSpan_polynomial (s : Seq ν) (v : S n) (f : MvPolynomial (Fin m) k) :
    (ψw (shiftWord p (TypeA.canWord n v)) * pol f * e s : R) ∈ M := by
  let F := (LinearMap.mulRight k (e s : R)).comp
    ((LinearMap.mulLeft k (ψw (shiftWord p (TypeA.canWord n v)) : R)).comp pol.toLinearMap)
  have hl : ⊤ ≤ (M).comap F := by
    rw [← (basisMonomials (Fin m) k).span_eq, Submodule.span_le]
    rintro _ ⟨d,rfl⟩
    exact intervalPBWSpan_monomial Q s v d
  exact hl (Submodule.mem_top (x := f))

variable (hQ : KLRSymm Q)
local notation "B" => basisOfSymm (ν := ν) hQ (rightIntervalWord h) (rightIntervalWord_choice h)

/-- Extract the interval diagram belonging to one exterior permutation. -/
def intervalPBWCoefficient (u : S m) : R →ₗ[k] M := by
  classical
  exact (B).constr k fun b =>
    let c := rightIntervalSplit h b.2.1
    if c.1 = u then
      ⟨ψw (shiftWord p (TypeA.canWord n c.2)) * pol (monomial b.2.2 1) * e b.1,
        intervalPBWSpan_monomial Q b.1 c.2 b.2.2⟩
    else 0

local notation "G" => intervalPBWCoefficient Q h hQ

private theorem intervalPBWCoefficient_basis (u : S m)
    (s : Seq ν) (w : S m) (d : Fin m →₀ ℕ) :
    G u ((B) (s,w,d)) =
      if (rightIntervalSplit h w).1 = u then
        ⟨ψw (shiftWord p (TypeA.canWord n (rightIntervalSplit h w).2)) * pol (monomial d 1) * e s,
          intervalPBWSpan_monomial Q s _ d⟩
      else 0 := by
  unfold intervalPBWCoefficient
  rw [Module.Basis.constr_basis]

/-- Attaching any sorted exterior word identifies its local interval span
inside the ambient algebra. Extracting a different exterior coefficient kills it. -/
theorem intervalPBWCoefficient_mul (u t : S m) (hu : StrictMono (fun i : Fin n => u ⟨p+i.val,by omega⟩)) (z : M) :
    G t (ψw (TypeA.canWord m u) * z.val) = if u = t then z else 0 := by
  classical
  apply Subtype.ext
  obtain ⟨x,hx⟩ := z
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,v,d,rfl⟩ := hx
    have split : rightIntervalSplit h (u * intervalPerm h v) = (u,v) := by
      rw [rightIntervalSplit_mul, rightIntervalSplit_of_sorted h u hu, one_mul]
    have basis : ψw (TypeA.canWord m u) * (ψw (shiftWord p (TypeA.canWord n v)) * pol (monomial d 1) * e s) =
        (B) (s,u * intervalPerm h v,d) := by
      rw [basisOfSymm_apply, rightIntervalWord, split, ψw_append]
      simp only [mul_assoc]
    rw [basis, intervalPBWCoefficient_basis, split]
  | zero =>
    simp only [mul_zero, map_zero, Submodule.coe_zero]
    split <;> rfl
  | add x y hx hy ix iy =>
    simp only [mul_add, map_add, Submodule.coe_add]
    split at * <;> simp_all
  | smul a x hx ix =>
    simp only [mul_smul_comm, map_smul, SetLike.val_smul]
    split at * <;> simp_all

private theorem intervalPBWCoefficient_loading_basis (u : S m) (t s b : Seq ν) (w : S m) (d : Fin m →₀ ℕ) :
    (G u (e t * (B) (b,w,d) * e s)).val = e (u⁻¹ • t) * (G u ((B) (b,w,d))).val * e s := by
  classical
  have hl : e t * (B) (b,w,d) = if w⁻¹ • t = b then (B) (b,w,d) else 0 := by
    rw [basisOfSymm_apply, e_mul_gen, (rightIntervalWord_choice h w).2]
  have hr : (B) (b,w,d) * e s = if b = s then (B) (b,w,d) else 0 := by
    rw [basisOfSymm_apply, gen_mul_e]
  rw [hl, intervalPBWCoefficient_basis]
  by_cases hu : (rightIntervalSplit h w).1 = u
  · rw [ite_eq_left hu]
    let v := (rightIntervalSplit h w).2
    have hw : u * intervalPerm h v = w := hu ▸ rightIntervalSplit_factor h w
    have hlocal := validWord_canWord n v
    have hp : wordProd m (shiftWord p (TypeA.canWord n v)) = intervalPerm h v := by
      rw [wordProd_shiftWord h (hlocal.of_le (by omega)), wordProd_eq_blockPerm_left (n' := r) rfl hlocal,
        wordProd_canWord, intervalPerm]
    have same : (wordProd m (shiftWord p (TypeA.canWord n v)))⁻¹ • (u⁻¹ • t) = w⁻¹ • t := by
      rw [hp, ← mul_smul, ← mul_inv_rev, hw]
    change _ = e (u⁻¹ • t) * (ψw (shiftWord p (TypeA.canWord n v)) * pol (monomial d 1) * e b) * e s
    rw [e_mul_gen,same]
    split
    · rw [hr,gen_mul_e]
      split
      · rw [intervalPBWCoefficient_basis,ite_eq_left hu]
      · rw [map_zero,Submodule.coe_zero]
    · rw [zero_mul,map_zero,Submodule.coe_zero]
  · rw [ite_eq_right hu,Submodule.coe_zero,mul_zero,zero_mul]
    split
    · rw [hr]
      split
      · rw [intervalPBWCoefficient_basis,ite_eq_right hu,Submodule.coe_zero]
      · rw [map_zero,Submodule.coe_zero]
    · rw [zero_mul,map_zero,Submodule.coe_zero]

/-- The source loading of an exterior coefficient is pulled back through its
exterior permutation. Its bottom loading is unchanged. -/
theorem intervalPBWCoefficient_loading (u : S m) (t s : Seq ν) (x : R) :
    (G u (e t * x * e s)).val = e (u⁻¹ • t) * (G u x).val * e s := by
  classical
  let F := (M).subtype.comp (G u)
  let cut (v : Seq ν) := (LinearMap.mulRight k (e s : R)).comp (LinearMap.mulLeft k (e v))
  have eq : F.comp (cut t) = (cut (u⁻¹ • t)).comp F := by
    apply (B).ext
    rintro ⟨b,w,d⟩
    simpa only [F,cut,LinearMap.comp_apply,LinearMap.mulRight_apply,LinearMap.mulLeft_apply,
      Submodule.subtype_apply] using intervalPBWCoefficient_loading_basis Q h hQ u t s b w d
  exact LinearMap.congr_fun eq x

/-- Reattaching the exterior words reconstructs every affine diagram from its
interval coefficients with arbitrary bottom colours and dots. -/
theorem sum_intervalPBWCoefficient (x : R) :
    ∑ u : S m, ψw (TypeA.canWord m u) * (G u x).val = x := by
  classical
  let F : R →ₗ[k] R := ∑ u : S m, (LinearMap.mulLeft k (ψw (TypeA.canWord m u) : R)).comp
    ((M).subtype.comp (G u))
  have eq : F = LinearMap.id := by
    apply (B).ext
    rintro ⟨s,w,d⟩
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.subtype_apply, intervalPBWCoefficient_basis, LinearMap.id_apply]
    rw [Finset.sum_eq_single (rightIntervalSplit h w).1]
    · rw [ite_eq_left rfl, basisOfSymm_apply, rightIntervalWord, ψw_append]
      simp only [mul_assoc]
    · intro u _ hu
      rw [ite_eq_right (Ne.symm hu), Submodule.coe_zero, mul_zero]
    · simp
  simpa only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Submodule.subtype_apply,
    LinearMap.id_apply] using LinearMap.congr_fun eq x

include hQ in
/-- Finite relations in the raw algebra split into the independent interval
relations at the sorted exterior representatives. -/
theorem intervalPBW_sum_eq_zero_iff (T : Finset (S m)) (hT : ∀ u ∈ T, StrictMono (fun i : Fin n => u ⟨p+i.val,by omega⟩))
    (z : S m → M) :
    (∑ u ∈ T, ψw (TypeA.canWord m u) * (z u).val : R) = 0 ↔ ∀ u ∈ T, z u = 0 := by
  classical
  constructor
  · intro he t ht
    have eq := congrArg (G t) he
    rw [map_sum, map_zero] at eq
    simpa only [Finset.sum_congr rfl (fun u hu => intervalPBWCoefficient_mul Q h hQ u t (hT u hu) (z u)),
      Finset.sum_ite_eq' T t z, ite_eq_left ht] using eq
  · intro he
    apply Finset.sum_eq_zero
    intro u hu
    rw [he u hu, Submodule.coe_zero, mul_zero]

include hQ in
/-- An affine relation between several interval exits can be tested independently
at every exterior permutation, whenever the local products lie in the interval
span. The multiplier at each exit can be a different diagram. -/
theorem intervalPBW_exit_relation_iff {η : Type*} (T : Finset (S m))
    (hT : ∀ u ∈ T, StrictMono (fun i : Fin n => u ⟨p+i.val,by omega⟩)) (L : Finset η)
    (z : S m → η → M) (leg : η → R)
    (hloc : ∀ u ∈ T, ∀ a ∈ L, (z u a).val * leg a ∈ M) :
    (∑ a ∈ L, (∑ u ∈ T, ψw (TypeA.canWord m u) * (z u a).val) * leg a) = 0 ↔
      ∀ u ∈ T, (∑ a ∈ L, (z u a).val * leg a) = 0 := by
  classical
  let y (u : S m) : M := if hu : u ∈ T then
    ⟨∑ a ∈ L, (z u a).val * leg a, (M).sum_mem (fun a ha => hloc u hu a ha)⟩ else 0
  have val (u : S m) (hu : u ∈ T) : (y u).val = ∑ a ∈ L, (z u a).val * leg a := by simp [y,hu]
  have ext : (∑ a ∈ L, (∑ u ∈ T, ψw (TypeA.canWord m u) * (z u a).val) * leg a) =
      ∑ u ∈ T, ψw (TypeA.canWord m u) * (y u).val := by
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    rw [val u hu, Finset.mul_sum]
  rw [ext, intervalPBW_sum_eq_zero_iff Q h hQ T hT y]
  constructor
  · intro he u hu
    exact (val u hu).symm.trans (congrArg Subtype.val (he u hu))
  · intro he u hu
    exact Subtype.ext ((val u hu).trans (he u hu))

end Categorification.KLR.KLRAlgebra
