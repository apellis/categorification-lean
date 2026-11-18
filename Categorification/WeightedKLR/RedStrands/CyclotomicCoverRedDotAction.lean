/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverRestrictionKernel
import Categorification.KLR.CyclotomicAction.Restriction

/-!
# Red dots under cyclotomic induction and restriction

For the red-dot relation used in Webster, arXiv:1309.3796v2, §4.1,
Definition 4.5, and the vacuum-action calculation of arXiv:1309.3796v3,
§4.6, Lemma 4.29, a red colour occurs once. Its dot acts by the
central sum of all dots of that colour. A corner inclusion carrying the
central sum to the upper central sum times the corner idempotent intertwines
these actions on induction and on restriction. At the final tensor-product
block, projection annihilates the red central sum.
The cited injectivity argument is the one revised in version 3; arXiv:1309.3796v2,
§4.5, Lemma 4.28, argues via Lemma 4.26 instead.
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra KLR.CyclotomicAction InductionAlong

universe u v w

section Modules

variable {A B : Type u} [Ring A] [Ring B]

/-- A central ring element acts naturally on all left modules. -/
def centralModuleAction (a : A) (ha : ∀ z, Commute z a) :
    𝟭 (ModuleCat.{w} A) ⟶ 𝟭 (ModuleCat A) where
  app M := ModuleCat.ofHom {
    toFun := fun m => a • m
    map_add' := smul_add a
    map_smul' := fun r m => by
      change a • r • m = r • a • m
      rw [smul_smul, smul_smul, (ha r).eq] }
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext (fun m => (f.hom.map_smul a m).symm))

/-- Tensor balancing transports a central action across induction. -/
theorem ind_map_centralModuleAction (φ : A →ₙ+* B)
    (a : A) (ha : ∀ z, Commute z a) (b : B) (hb : ∀ z, Commute z b)
    (h : φ a = b * φ 1) (M : ModuleCat.{max u w} A) :
    (functor φ).map ((centralModuleAction a ha).app M) =
      (centralModuleAction b hb).app ((functor φ).obj M) := by
  apply ModuleCat.hom_ext
  apply Ind.ext
  intro z n
  change Ind.tmul z (a • n) = b • Ind.tmul z n
  rw [← Ind.op_smul_tmul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change z.val * φ a = b * z.val
  rw [h, ← mul_assoc, (hb z.val).eq, mul_assoc, z.property]

/-- On restriction the corner idempotent acts as the identity. -/
theorem res_map_centralModuleAction (φ : A →ₙ+* B)
    (a : A) (ha : ∀ z, Commute z a) (b : B) (hb : ∀ z, Commute z b)
    (h : φ a = b * φ 1) (M : ModuleCat.{max u w} B) :
    (resFunctor φ).map ((centralModuleAction b hb).app M) =
      (centralModuleAction a ha).app ((resFunctor φ).obj M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply InductionAlong.Res.ext
  change b • z.val = φ a • z.val
  rw [h, mul_smul, z.prop]

/-- A central element in the kernel acts by zero after extension of scalars. -/
theorem ind_map_centralModuleAction_eq_zero (φ : A →ₙ+* B)
    (a : A) (ha : ∀ z, Commute z a) (h : φ a = 0) (M : ModuleCat.{max u w} A) :
    (functor φ).map ((centralModuleAction a ha).app M) = 0 := by
  apply ModuleCat.hom_ext
  apply Ind.ext
  intro z n
  change Ind.tmul z (a • n) = 0
  rw [← Ind.op_smul_tmul]
  have hz : MulOpposite.op a • z = 0 := Subtype.ext (by
    change z.val * φ a = 0
    rw [h, mul_zero])
  rw [hz, Ind.zero_tmul]

end Modules

section Cyclotomic

variable {C : Type u} {k : Type v} [DecidableEq C] [CommRing k]
  (S : C → C → MvPolynomial (Fin 2) k) (p : C → Polynomial k)
  {β γ : Multiset C}

/-- The coloured dot sum in the cyclotomic quotient. -/
def cyclotomicColourDot (β : Multiset C) (c : C) : CycKLR k S p β :=
  CycKLR.mk k S p β (colourDot c)

theorem cyclotomicColourDot_commute [IsDomain k] {P : C → C → MvPolynomial (Fin 2) k}
    (hSP : ∀ a b, a ≠ b → S a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (c : C) (z : CycKLR k S p β) :
    Commute z (cyclotomicColourDot S p β c) := by
  obtain ⟨z, rfl⟩ := CycKLR.mk_surjective z
  exact (commute_colourDot hSP hP c z).map (CycKLR.mk k S p β)

/-- The compatibility required by both module-action transport formulas. -/
theorem lastEmb_cyclotomicColourDot (i c : C) (h : {i} + β = γ)
    (hex : ∀ s : Seq β, ∃ a, s.lbl a = c)
    (hlo : ∀ (s : Seq β) a b, s.lbl a = c → s.lbl b = c → a = b)
    (hhi : ∀ (s : Seq γ) a b, s.lbl a = c → s.lbl b = c → a = b) :
    lastEmb S p i h (cyclotomicColourDot S p β c) =
      cyclotomicColourDot S p γ c * lastEmb S p i h 1 := by
  subst γ
  change AbsentColour.cyclotomicLast S i p β (CycKLR.mk k S p β (colourDot c)) = _
  rw [AbsentColour.cyclotomicLast_mk, cL_colourDot i c hex hlo hhi, map_mul]
  exact congrArg (_ * ·) (AbsentColour.cyclotomicLast_one S i p β).symm

/-- The last dot on a newly inserted unique colour agrees with the upper
central coloured dot on its induction idempotent. -/
theorem dotElt_cut_eq_cyclotomicColourDot (c : C) (h : {c} + β = γ)
    (hu : ∀ (s : Seq γ) a b, s.lbl a = c → s.lbl b = c → a = b) :
    dotElt S p c h * lastEmb S p c h 1 =
      cyclotomicColourDot S p γ c * lastEmb S p c h 1 := by
  subst γ
  let j : Fin (Multiset.card ({c} + β : Multiset C)) := ⟨β.card, lastPos_lt c β⟩
  change CycKLR.mk k S p _ (x j) * AbsentColour.cyclotomicLast S c p β 1 =
    CycKLR.mk k S p _ (colourDot c) * AbsentColour.cyclotomicLast S c p β 1
  rw [AbsentColour.cyclotomicLast_one, ← map_mul, ← map_mul]
  apply congrArg
  rw [cL_one, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  let t := Seq.cast (add_comm β ({c} : Multiset C)) (s.append default)
  have hj : t.lbl j = c := by
    let a : Fin (Multiset.card ({c} : Multiset C)) := ⟨0, by simp⟩
    have hj' : Fin.cast (congrArg Multiset.card (add_comm β ({c} : Multiset C)).symm) j =
        Seq.posR β a := Fin.ext (by change β.card = β.card + 0; omega)
    change (s.append (default : Seq ({c} : Multiset C))).1 (Fin.cast _ j) = c
    rw [hj', Seq.append_posR]
    exact Multiset.mem_singleton.mp ((default : Seq ({c} : Multiset C)).mem a)
  exact (colourDot_mul_e c t j hj (fun b hb => hu t b j hb hj)).symm

/-- On every induced module, the natural dot of a newly inserted unique
colour acts by the upper central coloured dot. -/
theorem dot_app_eq_centralModuleAction (c : C) (h : {c} + β = γ)
    (hu : ∀ (s : Seq γ) a b, s.lbl a = c → s.lbl b = c → a = b)
    (hc : ∀ z, Commute z (cyclotomicColourDot S p γ c))
    (M : ModuleCat.{max (max u v) w} (CycKLR k S p β)) :
    (dot S p c h).app M =
      (centralModuleAction _ hc).app ((ind S p c h).obj M) := by
  apply ModuleCat.hom_ext
  apply Ind.ext
  intro z n
  change Ind.tmul (cornerMul _ z) n = cyclotomicColourDot S p γ c • Ind.tmul z n
  rw [Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  let φ := lastEmb S p c h
  let d := dotElt S p c h
  let D := cyclotomicColourDot S p γ c
  change z.val * d = D * z.val
  have hε : z.val * φ 1 = z.val := z.property
  have hcomm : φ 1 * d = d * φ 1 := intertwines_dotElt S p c h 1
  calc
    z.val * d = z.val * (φ 1 * d) := by rw [← mul_assoc, hε]
    _ = z.val * (D * φ 1) := by rw [hcomm, dotElt_cut_eq_cyclotomicColourDot S p c h hu]
    _ = D * z.val := by rw [← mul_assoc, (hc z.val).eq, mul_assoc, hε]

omit [DecidableEq C] in
private theorem exists_position {c : C} (hc : c ∈ β) (s : Seq β) : ∃ a, s.lbl a = c := by
  rw [← s.2] at hc
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp hc
  exact ⟨a, ha⟩

private theorem unique_position {c : C} (hc : β.count c = 1)
    (s : Seq β) (a b : Fin β.card) (ha : s.lbl a = c) (hb : s.lbl b = c) : a = b := by
  have hcnt : β.count c ≤ 1 := hc.le
  rw [← s.2, Multiset.count_map] at hcnt
  have hf : (Finset.univ.filter (fun a => c = s.lbl a)).card ≤ 1 := hcnt
  exact Finset.card_le_one_iff.mp hf (by simp [ha]) (by simp [hb])

/-- A signed context to the right of a unique red strand. Its induction
and restriction steps may have any distinct colour. Indexing by block
content omits the zero blocks produced by restriction at an absent colour. -/
inductive ColourDotContext (c : C) : Multiset C → Multiset C → Type u where
  | nil (β : Multiset C) : ColourDotContext c β β
  | ind {β γ : Multiset C} (step : ColourDotContext c β γ) (j : C) (hj : c ≠ j) :
      ColourDotContext c β ({j} + γ)
  | res {β γ : Multiset C} (step : ColourDotContext c β ({j} + γ)) (hj : c ≠ j) :
      ColourDotContext c β γ

namespace ColourDotContext

variable {c : C}

/-- Composite of the actual induction and restriction functors. -/
def eval : {β γ : Multiset C} → ColourDotContext c β γ →
    ModuleCat.{max (max u v) w} (CycKLR k S p β) ⥤
    ModuleCat.{max (max u v) w} (CycKLR k S p γ)
  | _, _, .nil _ => 𝟭 _
  | _, _, .ind t j _ => eval t ⋙ CyclotomicAction.ind S p j rfl
  | _, _, .res (j := j) t _ => eval t ⋙ CyclotomicAction.res S p j rfl

theorem count_eq (step : ColourDotContext c β γ) : γ.count c = β.count c := by
  induction step with
  | nil => rfl
  | ind _ j hj ih => simpa [Multiset.count_singleton, hj] using ih
  | res _ hj ih => simpa [Multiset.count_singleton, hj] using ih

/-- The dot on the unique strand is the same central action after an
arbitrary signed suffix, including a mixture of induction and restriction. -/
theorem eval_map_centralModuleAction (step : ColourDotContext c β γ) (hβ : β.count c = 1)
    (hc : ∀ δ (z : CycKLR k S p δ), Commute z (cyclotomicColourDot S p δ c))
    (M : ModuleCat.{max (max u v) w} (CycKLR k S p β)) :
    (eval S p step).map ((centralModuleAction _ (hc β)).app M) =
      (centralModuleAction _ (hc γ)).app ((eval S p step).obj M) := by
  induction step with
  | nil => rfl
  | @ind β γ t j hj ih =>
    change (CyclotomicAction.ind S p j rfl).map ((eval S p t).map _) = _
    rw [ih hβ M]
    have hγ := t.count_eq.trans hβ
    have hγ' : ({j} + γ : Multiset C).count c = 1 := by
      simpa [Multiset.count_singleton, hj] using hγ
    apply ind_map_centralModuleAction
    exact lastEmb_cyclotomicColourDot S p j c rfl
      (exists_position (Multiset.count_pos.mp (by omega : 0 < γ.count c)))
      (unique_position hγ) (unique_position hγ')
  | @res j β γ t hj ih =>
    change (CyclotomicAction.res S p j rfl).map ((eval S p t).map _) = _
    rw [ih hβ M]
    have hγ' := t.count_eq.trans hβ
    have hγ : γ.count c = 1 := by simpa [Multiset.count_singleton, hj] using hγ'
    apply res_map_centralModuleAction
    exact lastEmb_cyclotomicColourDot S p j c rfl
      (exists_position (Multiset.count_pos.mp (by omega : 0 < γ.count c)))
      (unique_position hγ) (unique_position hγ')

end ColourDotContext

end Cyclotomic

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)
  (ν : Multiset I) (C : QuantumGroup.CartanDatum I)

/-- The red central action vanishes under the final tensor-product projection. -/
theorem cyclotomicCoverToTensor_colourDot (r : Fin ℓ) :
    cyclotomicCoverToTensor (Q := Q) Λ ν C
      (cyclotomicColourDot (cyclotomicCoverQ C Λ Q) cyclotomicCoverPolynomial
        (stendhalWeight ℓ ν) (.inr r)) = 0 := by
  apply (TwoSidedIdeal.mem_ker (cyclotomicCoverToTensor (Q := Q) Λ ν C).toRingHom).mp
  rw [cyclotomicCoverToTensor_ker, cyclotomicColourDot, colourDot_eq_sum, map_sum]
  apply sum_mem
  intro s _
  rw [map_sum]
  apply sum_mem
  intro a _
  split_ifs with h
  · apply TwoSidedIdeal.subset_span
    exact Or.inl ⟨s, a, by simp [h], rfl⟩
  · rw [map_zero]
    exact TwoSidedIdeal.zero_mem _

section SignedRedDot

variable {J : Type u} {K : Type v} [DecidableEq J] [Field K] {m : ℕ}
  {Q₀ : J → J → MvPolynomial (Fin 2) K} (Λ₀ : Fin m → J →₀ ℕ)
  (ν₀ : Multiset J) (C₀ : QuantumGroup.CartanDatum J)

local notation "S" => cyclotomicCoverQ C₀ Λ₀ Q₀
local notation "p" => cyclotomicCoverPolynomial (k := K) (I := J) (ℓ := m)
local notation "π" => RingHom.toNonUnitalRingHom (AlgHom.toRingHom (cyclotomicCoverToTensor (Q := Q₀) Λ₀ ν₀ C₀))
local notation "μ" => stendhalWeight m ν₀

/-- In the extended cyclotomic action evaluated on a module, a red dot in
any signed suffix acts by zero after projection to tensor-product modules.
The module on the left of the red strand is arbitrary. -/
theorem cyclotomicCover_project_signedRedDot (hQ : IsRouquierQ C₀ Q₀) (r : Fin m)
    {β γ : Multiset (J ⊕ Fin m)} (h : {Sum.inr r} + β = γ)
    (step : ColourDotContext (.inr r) γ μ)
    (M : ModuleCat.{max (max u v) w} (CycKLR K S p β)) :
    (functor π).map ((step.eval S p).map ((dot S p (.inr r) h).app M)) = 0 := by
  let c : J ⊕ Fin m := Sum.inr r
  have hS := isRouquierQ_cyclotomicCoverQ C₀ Λ₀ Q₀ hQ
  obtain ⟨P, hSP, hP⟩ := exists_factorization_of_isRouquierQ hS
  have hc (δ : Multiset (J ⊕ Fin m)) (z : CycKLR K S p δ) :
      Commute z (cyclotomicColourDot S p δ c) := cyclotomicColourDot_commute S p hSP hP c z
  have hμ : Multiset.count c μ = 1 := by
    classical
    have hblack : (ν₀.map (Sum.inl : J → J ⊕ Fin m)).count c = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp [c])
    rw [stendhalWeight, Multiset.count_add, hblack, zero_add]
    apply le_antisymm (Multiset.nodup_iff_count_le_one.mp
      (Finset.univ.nodup.map Sum.inr_injective) _)
    exact Multiset.count_pos.mpr (by simp [c])
  have hγ : γ.count c = 1 := step.count_eq.symm.trans hμ
  rw [dot_app_eq_centralModuleAction S p _ h (unique_position hγ) (hc γ),
    step.eval_map_centralModuleAction S p hγ hc]
  apply ind_map_centralModuleAction_eq_zero
  exact cyclotomicCoverToTensor_colourDot Λ₀ ν₀ C₀ r

end SignedRedDot

end Categorification.Stendhal
