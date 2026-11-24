/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Mackey
import Categorification.KLR.IntervalConcat
import Categorification.KLR.IntervalPBWCoordinates

/-!
# Interval multiplication with exterior dots

Right multiplication by diagrams embedded between fixed exterior loadings
preserves the ambient interval PBW span. Each such product expands in
exterior loading and exponent coordinates with coefficients in the local
KLR algebra.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra

open MvPolynomial Equiv TypeA
open scoped TensorProduct

variable {I k : Type} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {α β γ : Multiset I}

local notation "K" => KLRAlgebra k Q
local notation "A" => K (α + (β + γ))
local notation "M" => intervalPBWSpan Q (ν := α + (β + γ)) (p := α.card) (n := β.card)

/-- Insert a local diagram with fixed, possibly dotted, spectator loadings. -/
def intervalSpectatorConcat (l : Seq α) (r : Seq γ)
    (f : MvPolynomial (Fin α.card) k) (g : MvPolynomial (Fin γ.card) k) :
    K β →ₗ[k] A :=
  (concat Q α (β + γ)).comp
    (((TensorProduct.mk k _ _) (pol f * e l)).comp
      ((concat Q β γ).comp ((TensorProduct.mk k _ _).flip (pol g * e r))))

theorem intervalSpectatorConcat_apply (l : Seq α) (r : Seq γ)
    (f : MvPolynomial (Fin α.card) k) (g : MvPolynomial (Fin γ.card) k) (x : K β) :
    intervalSpectatorConcat Q l r f g x =
      concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
        concat Q β γ (x ⊗ₜ[k] (pol g * e r))) := rfl

theorem intervalSpectatorConcat_mul_intervalConcat (l : Seq α) (r : Seq γ)
    (f : MvPolynomial (Fin α.card) k) (g : MvPolynomial (Fin γ.card) k) (x y : K β) :
    intervalSpectatorConcat Q l r f g x * intervalConcat Q l r y =
      intervalSpectatorConcat Q l r f g (x * y) := by
  rw [intervalSpectatorConcat_apply, intervalConcat_apply, ← concat_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_assoc (pol f : K α) (e l) (e l), e_mul_self,
    ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_assoc (pol g : K γ) (e r) (e r), e_mul_self, intervalSpectatorConcat_apply]

private theorem concat_interval_spectator_polynomials
    (f : MvPolynomial (Fin α.card) k) (g : MvPolynomial (Fin β.card) k)
    (h : MvPolynomial (Fin γ.card) k) {w : List ℕ}
    (hw : ValidWord β.card w) (l : Seq α) (s : Seq β) (r : Seq γ) :
    concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ ((ψw w * pol g * e s) ⊗ₜ[k] (pol h * e r))) =
    ψw (shiftWord α.card w) *
      pol (rename (Seq.posL (β + γ)) f *
        rename (Seq.posR α) (rename (Seq.posL γ) g * rename (Seq.posR β) h)) *
      e (l.append (s.append r)) := by
  have hw' : ValidWord (β + γ).card w := by
    intro j hj
    have h := hw j hj
    rw [Multiset.card_add]
    omega
  have inner := concat_ψw_pol_e (Q := Q) hw (validWord_nil γ.card) g h s r
  simp only [shiftWord, List.map_nil, List.append_nil, ψw_nil, one_mul] at inner
  rw [inner]
  simpa only [ψw_nil, one_mul, List.nil_append] using
    (concat_ψw_pol_e (Q := Q) (validWord_nil α.card) hw' f (rename (Seq.posL γ) g * rename (Seq.posR β) h)
      l (s.append r))

private theorem concat_spectators_mem_intervalPBWSpan (hQ : KLRSymm Q)
    (l : Seq α) (r : Seq γ) (f : MvPolynomial (Fin α.card) k)
    (h : MvPolynomial (Fin γ.card) k) (z : K β) :
    concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ (z ⊗ₜ[k] (pol h * e r))) ∈ M := by
  let F : K β →ₗ[k] A := (concat Q α (β + γ)).comp
    (((TensorProduct.mk k _ _) (pol f * e l)).comp
      ((concat Q β γ).comp ((TensorProduct.mk k _ _).flip (pol h * e r))))
  let B := basisOfSymm hQ (canWord β.card)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)
  change z ∈ (M).comap F
  have hs : ⊤ ≤ (M).comap F := by
    rw [← B.span_eq, Submodule.span_le]
    rintro _ ⟨⟨s, v, d⟩, rfl⟩
    change concat Q α (β + γ) ((pol f * e l) ⊗ₜ[k]
      concat Q β γ (B (s, v, d) ⊗ₜ[k] (pol h * e r))) ∈ M
    rw [show B (s, v, d) = _ from basisOfSymm_apply ..,
      concat_interval_spectator_polynomials Q f _ h (validWord_canWord _ v) l s r]
    exact intervalPBWSpan_polynomial Q _ v _
  exact hs (Submodule.mem_top (x := z))

private theorem intervalPBWSpan_mul_intervalConcat_mem (l : Seq α) (r : Seq γ)
    (P : Submodule k A)
    (hP : ∀ (a : Fin α.card →₀ ℕ) (c : Fin γ.card →₀ ℕ) (z : K β),
      intervalSpectatorConcat Q l r (monomial a 1) (monomial c 1) z ∈ P)
    (x : M) (y : K β) : x.val * intervalConcat Q l r y ∈ P := by
  classical
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | zero => simp
  | add x z hx hz hx' hz' => rw [add_mul]; exact add_mem hx' hz'
  | smul c x hx hx' => rw [smul_mul_assoc]; exact P.smul_mem c hx'
  | mem x hx =>
    obtain ⟨s, v, d, rfl⟩ := hx
    change (ψw (shiftWord α.card (canWord β.card v)) * pol (monomial d 1) * e s : A) *
      intervalConcat Q l r y ∈ P
    by_cases hs : ∃ t : Seq β, s = l.append (t.append r)
    · obtain ⟨t, rfl⟩ := hs
      obtain ⟨⟨a, bc⟩, rfl⟩ := (expEquiv α (β + γ)).surjective d
      obtain ⟨⟨b, c⟩, rfl⟩ := (expEquiv β γ).surjective bc
      rw [monomial_expEquiv, monomial_expEquiv,
        ← concat_interval_spectator_polynomials Q _ _ _ (validWord_canWord _ v) l t r]
      rw [← intervalSpectatorConcat_apply, intervalSpectatorConcat_mul_intervalConcat]
      exact hP _ _ _
    · have hf (t : Seq β) : intervalConcat Q l r (e t : K β) = e (l.append (t.append r)) := by
        rw [intervalConcat_apply, concat_e_tmul_e, concat_e_tmul_e]
      have hfix : intervalConcat Q l r y =
          (∑ t : Seq β, e (l.append (t.append r))) * intervalConcat Q l r y := by
        have hu : (∑ t : Seq β, e (l.append (t.append r)) : A) =
            intervalConcat Q l r (1 : K β) := by
          simp_rw [← hf]
          rw [← map_sum, sum_e]
        rw [hu, ← intervalConcat_mul, one_mul]
      have hz : (e s : A) * intervalConcat Q l r y = 0 := by
        conv_lhs => arg 2; rw [hfix]
        rw [← mul_assoc, Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
        intro t _
        rw [e_mul_e, ite_eq_right (fun he => hs ⟨t, he⟩)]
      rw [mul_assoc, hz, mul_zero]
      exact zero_mem _

/-- Multiplying an ambient interval coefficient by a local interval diagram
preserves the interval span, including arbitrary dots on the exterior.
This is used in the kernel test following (6.21) in Webster v2, Lemma 6.8. -/
theorem intervalPBWSpan_mul_intervalConcat (hQ : KLRSymm Q) (l : Seq α) (r : Seq γ)
    (x : M) (y : K β) : x.val * intervalConcat Q l r y ∈ M :=
  intervalPBWSpan_mul_intervalConcat_mem Q l r M
    (fun a c z => concat_spectators_mem_intervalPBWSpan Q hQ l r
      (monomial a 1) (monomial c 1) z) x y

private theorem exteriorCoordinate (hQ : KLRSymm Q) {ν : Multiset I}
    (s : Seq ν) (a : Fin ν.card →₀ ℕ) :
    ∃ f : K ν →ₗ[k] k, ∀ t : Seq ν, ∀ b : Fin ν.card →₀ ℕ,
      f (pol (monomial b 1) * e t) = if (t, b) = (s, a) then 1 else 0 := by
  classical
  let B := basisOfSymm hQ (canWord ν.card)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)
  refine ⟨B.coord (s, 1, a), ?_⟩
  intro t b
  have hb : B (t, 1, b) = pol (monomial b 1) * e t := by
    rw [show B (t, 1, b) = _ from basisOfSymm_apply ..]
    simp [canWord_one]
  rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : (t, b) = (s, a)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp
  · have h' : (t, (1 : Perm (Fin ν.card)), b) ≠ (s, 1, a) := fun he =>
      h (congrArg (fun z : Seq ν × Perm (Fin ν.card) × (Fin ν.card →₀ ℕ) => (z.1, z.2.2)) he)
    simp [h, Ne.symm h']

/-- A finite sum of interval diagrams separates at every exterior loading and
monomial exponent, including independent dots on both sides. -/
theorem sum_intervalSpectatorConcat_eq_zero_iff (hQ : KLRSymm Q)
    (L : Finset (Seq α × (Fin α.card →₀ ℕ)))
    (R : Finset (Seq γ × (Fin γ.card →₀ ℕ)))
    (z : (Seq α × (Fin α.card →₀ ℕ)) →
      (Seq γ × (Fin γ.card →₀ ℕ)) → K β) :
    (∑ a ∈ L, ∑ b ∈ R,
      intervalSpectatorConcat Q a.1 b.1 (monomial a.2 1) (monomial b.2 1) (z a b)) = 0 ↔
      ∀ a ∈ L, ∀ b ∈ R, z a b = 0 := by
  classical
  constructor
  · intro hz a ha b hb
    obtain ⟨left, hleft⟩ := exteriorCoordinate Q hQ a.1 a.2
    obtain ⟨right, hright⟩ := exteriorCoordinate Q hQ b.1 b.2
    let f (a' : Seq α × (Fin α.card →₀ ℕ)) : K α := pol (monomial a'.2 1) * e a'.1
    let g (b' : Seq γ × (Fin γ.card →₀ ℕ)) : K γ := pol (monomial b'.2 1) * e b'.1
    let C : K α ⊗[k] K (β + γ) →ₗ[k] K (β + γ) :=
      (TensorProduct.lid k _).toLinearMap.comp (left.rTensor _)
    let D : K β ⊗[k] K γ →ₗ[k] K β :=
      (TensorProduct.rid k _).toLinearMap.comp (right.lTensor _)
    have hc (a' : Seq α × (Fin α.card →₀ ℕ)) (t : K (β + γ)) :
        C (f a' ⊗ₜ[k] t) = if a' = a then t else 0 := by
      change left (f a') • t = _
      rw [show left (f a') = _ from hleft a'.1 a'.2]
      split <;> simp_all
    have hd (b' : Seq γ × (Fin γ.card →₀ ℕ)) (t : K β) :
        D (t ⊗ₜ[k] g b') = if b' = b then t else 0 := by
      change right (g b') • t = _
      rw [show right (g b') = _ from hright b'.1 b'.2]
      split <;> simp_all
    have houter : (∑ a' ∈ L, ∑ b' ∈ R,
        f a' ⊗ₜ[k] concat Q β γ (z a' b' ⊗ₜ[k] g b')) = 0 := by
      apply concat_injective hQ
      simpa only [map_sum, map_zero, intervalSpectatorConcat_apply] using hz
    have hmiddle := congrArg C houter
    simp only [map_zero, map_sum, hc] at hmiddle
    have hinner : (∑ b' ∈ R, z a b' ⊗ₜ[k] g b') = 0 := by
      apply concat_injective hQ
      rw [map_sum, map_zero]
      rw [Finset.sum_eq_single_of_mem a ha (fun c _ hc' =>
        Finset.sum_eq_zero (fun _ _ => ite_eq_right hc'))] at hmiddle
      simpa using hmiddle
    have he := congrArg D hinner
    simpa [map_sum, hd, hb] using he
  · intro h
    exact Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
      rw [h a ha b hb, map_zero]

/-- Realize finitely many exterior sectors as an ambient interval diagram. -/
def intervalSpectatorSum :
    (((Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) →₀ K β) →ₗ[k] A :=
  Finsupp.lsum k fun j => intervalSpectatorConcat Q j.1.1 j.2.1
    (monomial j.1.2 1) (monomial j.2.2 1)

/-- A product with an embedded interval diagram has a finite expansion
in exterior dot monomials and local KLR coefficients. -/
theorem exists_intervalSpectatorSum_mul_intervalConcat (l : Seq α) (r : Seq γ)
    (x : M) (y : K β) :
    ∃ z : ((Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) →₀ K β,
      (∀ j ∈ z.support, j.1.1 = l ∧ j.2.1 = r) ∧
      intervalSpectatorSum Q z = x.val * intervalConcat Q l r y := by
  classical
  let P := Finsupp.supported (K β) k
    {j : (Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ)) |
      j.1.1 = l ∧ j.2.1 = r}
  have h := intervalPBWSpan_mul_intervalConcat_mem Q l r
    (P.map (intervalSpectatorSum Q)) (fun a c z => by
      refine ⟨Finsupp.single ((l, a), (r, c)) z, ?_, Finsupp.lsum_single _ _ _ _⟩
      exact Finsupp.single_mem_supported k z ⟨rfl, rfl⟩) x y
  obtain ⟨z, hz, he⟩ := h
  exact ⟨z, (Finsupp.mem_supported k z).mp hz, he⟩

/-- The exterior loading and exponent coordinates have independent images. -/
theorem intervalSpectatorSum_injective (hQ : KLRSymm Q) :
    Function.Injective (intervalSpectatorSum (α := α) (β := β) (γ := γ) Q) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro z hz
  change intervalSpectatorSum Q z = 0 at hz
  let L := z.support.image Prod.fst
  let R := z.support.image Prod.snd
  have hs : z.support ⊆ L ×ˢ R := by
    intro j hj
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hj, Finset.mem_image_of_mem _ hj⟩
  have hzero : (∑ a ∈ L, ∑ b ∈ R,
      intervalSpectatorConcat Q a.1 b.1 (monomial a.2 1) (monomial b.2 1) (z (a, b))) = 0 := by
    let F (j : (Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) : A :=
      intervalSpectatorConcat Q j.1.1 j.2.1 (monomial j.1.2 1) (monomial j.2.2 1) (z j)
    change (∑ a ∈ L, ∑ b ∈ R, F (a, b)) = 0
    rw [← Finset.sum_product L R F]
    rw [intervalSpectatorSum, Finsupp.lsum_apply, Finsupp.sum] at hz
    rwa [Finset.sum_subset hs (fun j _ hj => by rw [Finsupp.notMem_support_iff.mp hj, map_zero])] at hz
  have hz' := (sum_intervalSpectatorConcat_eq_zero_iff Q hQ L R
    (fun a b => z (a, b))).mp hzero
  ext j
  by_cases hj : j ∈ z.support
  · obtain ⟨hl, hr⟩ := Finset.mem_product.mp (hs hj)
    exact hz' j.1 hl j.2 hr
  · exact Finsupp.notMem_support_iff.mp hj

/-- One finite expansion handles multiplication by every local interval leg
at the given exterior loadings. -/
theorem exists_intervalSpectatorExpansion (l : Seq α) (r : Seq γ) (x : M) :
    ∃ (L : Finset (Fin α.card →₀ ℕ)) (R : Finset (Fin γ.card →₀ ℕ))
      (z : (Fin α.card →₀ ℕ) → (Fin γ.card →₀ ℕ) → K β),
      ∀ y : K β, x.val * intervalConcat Q l r y =
        ∑ a ∈ L, ∑ b ∈ R,
          intervalSpectatorConcat Q l r (monomial a 1) (monomial b 1) (z a b * y) := by
  classical
  obtain ⟨z, hs, hz⟩ := exists_intervalSpectatorSum_mul_intervalConcat Q l r x (1 : K β)
  let L := z.support.image fun j => j.1.2
  let R := z.support.image fun j => j.2.2
  let E : ((Fin α.card →₀ ℕ) × (Fin γ.card →₀ ℕ)) ↪
      ((Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) :=
    ⟨fun p => ((l, p.1), (r, p.2)), fun _ _ h => congrArg (fun j => (j.1.2, j.2.2)) h⟩
  have he (a : Fin α.card →₀ ℕ) (b : Fin γ.card →₀ ℕ) : E (a, b) = ((l, a), (r, b)) := rfl
  have hsub : z.support ⊆ (L ×ˢ R).map E := by
    intro j hj
    obtain ⟨hl, hr⟩ := hs j hj
    refine Finset.mem_map.mpr ⟨(j.1.2, j.2.2), Finset.mem_product.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_image_of_mem _ hj, Finset.mem_image_of_mem _ hj⟩
    · rcases j with ⟨⟨l', a⟩, ⟨r', b⟩⟩
      rw [he]
      exact Prod.ext (Prod.ext hl.symm rfl) (Prod.ext hr.symm rfl)
  let F (j : (Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) : A :=
    intervalSpectatorConcat Q j.1.1 j.2.1 (monomial j.1.2 1) (monomial j.2.2 1) (z j)
  have hsum : intervalSpectatorSum Q z = ∑ a ∈ L, ∑ b ∈ R, F ((l, a), (r, b)) := by
    rw [intervalSpectatorSum, Finsupp.lsum_apply, Finsupp.sum]
    change ∑ j ∈ z.support, F j = _
    rw [Finset.sum_subset hsub (fun j _ hj => by
      dsimp only [F]
      rw [Finsupp.notMem_support_iff.mp hj, map_zero])]
    rw [Finset.sum_map, Finset.sum_product L R (fun p => F (E p))]
    simp only [he]
  refine ⟨L, R, fun a b => z ((l, a), (r, b)), fun y => ?_⟩
  calc
    _ = (x.val * intervalConcat Q l r 1) * intervalConcat Q l r y := by
      rw [mul_assoc, ← intervalConcat_mul, one_mul]
    _ = _ := by
      rw [← hz, hsum]
      simp only [Finset.sum_mul, F, intervalSpectatorConcat_mul_intervalConcat]

/-- A relation with fixed spectator loadings and arbitrary exterior dots holds
exactly when every pair of exterior exponents gives a relation in the local algebra. -/
theorem intervalSpectatorConcat_exit_relation_iff {η : Type} (hQ : KLRSymm Q)
    (l : Seq α) (r : Seq γ) (T : Finset η)
    (L : Finset (Fin α.card →₀ ℕ)) (R : Finset (Fin γ.card →₀ ℕ))
    (x : η → (Fin α.card →₀ ℕ) → (Fin γ.card →₀ ℕ) → K β) (y : η → K β) :
    (∑ i ∈ T, (∑ a ∈ L, ∑ b ∈ R,
      intervalSpectatorConcat Q l r (monomial a 1) (monomial b 1) (x i a b)) *
        intervalConcat Q l r (y i)) = 0 ↔
      ∀ a ∈ L, ∀ b ∈ R, (∑ i ∈ T, x i a b * y i) = 0 := by
  classical
  let lEmb : (Fin α.card →₀ ℕ) ↪ Seq α × (Fin α.card →₀ ℕ) :=
    ⟨fun a => (l, a), fun _ _ h => congrArg Prod.snd h⟩
  let rEmb : (Fin γ.card →₀ ℕ) ↪ Seq γ × (Fin γ.card →₀ ℕ) :=
    ⟨fun b => (r, b), fun _ _ h => congrArg Prod.snd h⟩
  have order :
      (∑ i ∈ T, ∑ a ∈ L, ∑ b ∈ R,
        intervalSpectatorConcat Q l r (monomial a 1) (monomial b 1) (x i a b * y i)) =
      ∑ a ∈ L, ∑ b ∈ R, ∑ i ∈ T,
        intervalSpectatorConcat Q l r (monomial a 1) (monomial b 1) (x i a b * y i) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  simp_rw [Finset.sum_mul, intervalSpectatorConcat_mul_intervalConcat]
  rw [order]
  simp_rw [← map_sum]
  have hl (a : Fin α.card →₀ ℕ) : lEmb a = (l, a) := rfl
  have hr (b : Fin γ.card →₀ ℕ) : rEmb b = (r, b) := rfl
  simpa [hl, hr] using
    (sum_intervalSpectatorConcat_eq_zero_iff Q hQ (L.map lEmb) (R.map rEmb)
      (fun a b => ∑ i ∈ T, x i a.2 b.2 * y i))

/-- Sector coefficients multiply on the right in the local KLR algebra. -/
theorem intervalSpectatorSum_right_mul (l : Seq α) (r : Seq γ) (z : ((Seq α × (Fin α.card →₀ ℕ)) × (Seq γ × (Fin γ.card →₀ ℕ))) →₀ K β)
    (hz : ∀ j ∈ z.support, j.1.1 = l ∧ j.2.1 = r) (y : K β) :
    intervalSpectatorSum Q z * intervalConcat Q l r y =
      intervalSpectatorSum Q (z.mapRange (· * y) (zero_mul y)) := by
  classical
  simp only [intervalSpectatorSum, Finsupp.lsum_apply]
  rw [Finsupp.sum_mapRange_index (fun _ => map_zero _)]
  unfold Finsupp.sum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hl, hr⟩ := hz j hj
  change intervalSpectatorConcat Q j.1.1 j.2.1 (monomial j.1.2 1) (monomial j.2.2 1) (z j) *
      intervalConcat Q l r y = intervalSpectatorConcat Q j.1.1 j.2.1 (monomial j.1.2 1) (monomial j.2.2 1) (z j * y)
  rw [hl, hr, intervalSpectatorConcat_mul_intervalConcat]

end Categorification.KLR.KLRAlgebra
