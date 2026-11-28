/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingStdStandardBasis
import Categorification.WeightedKLR.RedStrands.BlocksStandardRows
import Categorification.WeightedKLR.RedStrands.PartialStandardizationPlusStaged

/-!
# The standard basis of `S_+`, in stages

Webster, arXiv:1309.3796v3, §5.1, the partial standardizations after Definition 5.4, in the
staged induced model; used in §7.3, proof of Lemma 7.19, for the standard basis of the partial
standardization `S_+ = 𝕊^{λ_1; …; λ_j; μ μ*; λ_{j+1}; …; λ_ℓ}` (`plusStagedStd`). Webster
states no basis of a partial standardization.

`S_+` is the three-block partial standardization `𝕊^{A;M;R}` applied after the singleton
standardizations of the first and the last block (`plusOuterStd`). Accordingly:

* the row conditions of the singleton stages are flattened into one set of conditions for each
  coordinate (`singConds`, `singAdm_iff`);
* the outer standardizations have coordinates indexed by pairs `(t, h)` of tuples of shuffles of
  the last and the first block (`plusOuterCoord`), they determine the element
  (`plusOuterCoord_injective`), and the coordinate families are those satisfying the conditions
  of both blocks (`mem_range_plusOuterCoord_iff`); the conditions of the last block act through
  the spectator;
* a pure tensor `e(a) ⊗ b ⊗ e(c)` of the algebra of the three blocks, with loading idempotents
  in the outer blocks, acts on the coordinate `(t, h)` by `L_{h,a} ⊗ b ⊗ L_{t,c}`
  (`plusOuterCoord_smul_tmul`);
* `S_+(N)` has coordinates indexed by `(u_out, u_in, t, h)` (`plusStagedCoord`), which
  determine the element (`plusStagedCoord_injective`), and the coordinate families are those
  whose rows are the outer coordinates of a three-block coordinate family
  (`mem_range_plusStagedCoord_iff`); the three-block conditions are stated on the preimages.

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.singConds`, `Stendhal.CupCap.plusOuterCoord`, `Stendhal.CupCap.plusBlocksCoord`,
  `Stendhal.CupCap.plusStagedCoord`.

## Main results

* `Stendhal.singAdm_iff`, `Stendhal.tensorLoad_relabel`.
* `Stendhal.CupCap.plusOuterCoord_injective`, `Stendhal.CupCap.mem_range_plusOuterCoord_iff`,
  `Stendhal.CupCap.plusOuterCoord_smul_tmul`.
* `Stendhal.CupCap.plusStagedCoord_injective`, `Stendhal.CupCap.mem_range_plusStagedCoord_iff`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

/-! ### Flattened row conditions of the singleton stages -/

section Flat

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- The conditions on the coordinate `i` of the standardization with singleton blocks: the row
elements `E_{i_k, u_k}` of all stages, in the algebra of the singleton blocks. -/
def singConds : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) → singIdx n θ →
    Set (singAlg Q n Λ θ)
  | 0, _, _, _ => ∅
  | n + 1, Λ, θ, (i, u) => insert (singRow Q n Λ θ i u)
      ((fun x => (x ⊗ₜ[k] (1 : singLast Q Λ θ) : singAlg Q (n + 1) Λ θ)) ''
        singConds n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i)

/-- **The row conditions, flattened**: a family is admissible iff every coordinate `G i` is
fixed by `x ⊗ 1` for every condition `x` on `i`. -/
theorem singAdm_iff : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (G : singIdx n θ → M) →
    (singAdm Q n Λ θ E M G ↔ ∀ i, ∀ x ∈ singConds Q n Λ θ i, (x ⊗ₜ[k] (1 : E)) • G i = G i)
  | 0, _, _, _, _, _ => ⟨fun _ _ x hx => absurd hx (Set.notMem_empty x), fun _ => trivial⟩
  | n + 1, Λ, θ, E, M, G => by
    change ((∀ u, singAdm Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
      (singInnerIn Q n Λ θ E M) fun i => singMToInner Q n Λ θ E M (G (i, u))) ∧
      ∀ i u, (singRow Q n Λ θ i u ⊗ₜ[k] (1 : E)) • G (i, u) = G (i, u)) ↔ _
    simp only [singAdm_iff n]
    constructor
    · rintro ⟨h1, h2⟩ ⟨i, u⟩ x hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · exact h2 i u
      · exact h1 u i y hy
    · intro h
      exact ⟨fun u i y hy => h (i, u) _ (Or.inr ⟨y, hy, rfl⟩),
        fun i u => h (i, u) _ (Or.inl rfl)⟩

end Flat

/-! ### Loading idempotents under relabelling -/

theorem tensorLoad_relabel {I k : Type*} [DecidableEq I] [CommRing k]
    (Q : I → I → MvPolynomial (Fin 2) k) {n : ℕ} {Λ₁ Λ₂ : Fin n → I →₀ ℕ} (h : Λ₁ = Λ₂)
    (ν : Multiset I) (c : Seq (stendhalWeight n ν)) :
    relabelTensorProductAlgebra Q h ν (tensorLoad Q Λ₁ ν c) = tensorLoad Q Λ₂ ν c := by
  subst h
  rfl

theorem tensorRotate_tmul {k : Type u} [CommRing k] {A B C : Type u} [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] [Ring C] [Algebra k C] (a : A) (b : B) (c : C) :
    tensorRotate (k := k) A B C (a ⊗ₜ[k] (b ⊗ₜ[k] c)) = b ⊗ₜ[k] (c ⊗ₜ[k] a) :=
  rfl

theorem tensorRotate_symm_tmul {k : Type u} [CommRing k] {A B C : Type u} [Ring A] [Algebra k A]
    [Ring B] [Algebra k B] [Ring C] [Algebra k C] (a : A) (b : B) (c : C) :
    (tensorRotate (k := k) A B C).symm (b ⊗ₜ[k] (c ⊗ₜ[k] a)) = a ⊗ₜ[k] (b ⊗ₜ[k] c) :=
  (AlgEquiv.symm_apply_eq _).2 rfl

theorem tmul_smul_split {R A B M : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [AddCommMonoid M] [Module (A ⊗[R] B) M] (a : A) (b : B) (m : M) :
    (a ⊗ₜ[R] b) • m = (a ⊗ₜ[R] (1 : B)) • ((1 : A) ⊗ₜ[R] b) • m := by
  rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem tmul_one_mul_one_tmul {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Semiring B] [Algebra R B] (a : A) (b : B) :
    ((a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) : A ⊗[R] B) = a ⊗ₜ[R] b := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-! ### Coordinates of the outer standardizations -/

namespace CupCap

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (j : ℕ) (hj : j ≤ ℓ)
  (β : Multiset I) (θh : Fin j → Multiset I) (θt : Fin (ℓ - j) → Multiset I)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- The algebra of the first block after its standardization. -/
local notation "Hd" => TensorProductAlgebra k Q (Λ ∘ Fin.castLE hj) (singWeight j θh)
/-- The algebra of the last block after its standardization. -/
local notation "Tl" => TensorProductAlgebra k Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt)
local notation "Cp" => TensorProductAlgebra k Q Λc β
local notation "St" => singAlg Q (ℓ - j) (plusTailLabels Λ j hj) θt

variable (N : ModuleCat.{u} (plusSingAlg Q Λ Λc j hj β θh θt))

/-- The standardization of the first block, with the pair and the last block as spectator. -/
abbrev plusHeadObj : ModuleCat.{u} (Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k)) :=
  (singStd Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St))).obj N

/-- The standardization of the first block, as a module over the last block and the rest. -/
abbrev plusMidObj : ModuleCat.{u} (St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :=
  (ModuleCat.restrictScalars.{u} (show St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k) →+*
      Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k) from
    (tensorRotate (k := k) St Hd Cp).toAlgHom.toRingHom)).obj (plusHeadObj Q hQ Λ Λc j hj β θh θt N)

/-- An element of the middle stage as an element of the standardization of the first block. -/
def plusMidToHead : plusMidObj Q hQ Λ Λc j hj β θh θt N →+ plusHeadObj Q hQ Λ Λc j hj β θh θt N :=
  AddMonoidHom.id _

/-- An element of the standardization of the first block as an element of the middle stage. -/
def plusHeadToMid : plusHeadObj Q hQ Λ Λc j hj β θh θt N →+ plusMidObj Q hQ Λ Λc j hj β θh θt N :=
  AddMonoidHom.id _

/-- The last stage of the outer standardizations, before the final rotation. -/
abbrev plusTailObj : ModuleCat.{u} (Tl ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :=
  (singStd Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))).obj
    (plusMidObj Q hQ Λ Λc j hj β θh θt N)

/-- An element of the outer standardizations as an element of their last stage. -/
def plusOuterToTail :
    (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N →+ plusTailObj Q hQ Λ Λc j hj β θh θt N :=
  AddMonoidHom.id _

/-- The algebra of the three blocks acts on the last stage through the rotation. -/
theorem plusOuterToTail_smul
    (d : plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt))
    (y : (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N) :
    plusOuterToTail Q hQ Λ Λc j hj β θh θt N (d • y) =
      ((tensorRotate (k := k) Tl Hd Cp).symm d :
        Tl ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) •
        plusOuterToTail Q hQ Λ Λc j hj β θh θt N y :=
  rfl

/-- **The coordinates of the outer standardizations of `S_+`**: the coordinate `(t, h)` is the
coordinate `h` of the first block of the coordinate `t` of the last block. -/
def plusOuterCoord (y : (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N)
    (p : singIdx (ℓ - j) θt × singIdx j θh) : N :=
  singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N
    (plusMidToHead Q hQ Λ Λc j hj β θh θt N
      (singCoord Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))
        (plusMidObj Q hQ Λ Λc j hj β θh θt N) (plusOuterToTail Q hQ Λ Λc j hj β θh θt N y) p.1))
      p.2

theorem plusOuterCoord_injective :
    Function.Injective (plusOuterCoord Q hQ Λ Λc j hj β θh θt N) := fun _ _ h =>
  singCoord_injective Q hQ (ℓ - j) _ _ _ _ (funext fun t =>
    singCoord_injective Q hQ j _ _ _ _ (funext fun h' => congrFun h (t, h')))

/-- An element of the last block acts on the middle stage through the spectator of the first
block. -/
theorem plusMidObj_smul (x : St) (w : plusMidObj Q hQ Λ Λc j hj β θh θt N) :
    plusMidToHead Q hQ Λ Λc j hj β θh θt N
        ((x ⊗ₜ[k] (1 : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :
          St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) • w) =
      (((1 : Hd) ⊗ₜ[k] ((1 : Cp) ⊗ₜ[k] x : Cp ⊗[k] St) :
        Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k)) •
          plusMidToHead Q hQ Λ Λc j hj β θh θt N w) := by
  change (tensorRotate (k := k) St Hd Cp (x ⊗ₜ[k] ((1 : Hd) ⊗ₜ[k] (1 : Cp))) •
    plusMidToHead Q hQ Λ Λc j hj β θh θt N w) = _
  rw [tensorRotate_tmul]

/-- **The coordinate families of the outer standardizations**: the conditions of the first
block, and the conditions of the last block acting through the spectator. -/
theorem mem_range_plusOuterCoord_iff (G : singIdx (ℓ - j) θt × singIdx j θh → N) :
    G ∈ Set.range (plusOuterCoord Q hQ Λ Λc j hj β θh θt N) ↔
      (∀ t h, ∀ x ∈ singConds Q j (Λ ∘ Fin.castLE hj) θh h,
        (x ⊗ₜ[k] (1 : (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k))) • G (t, h) = G (t, h)) ∧
      ∀ t h, ∀ x ∈ singConds Q (ℓ - j) (plusTailLabels Λ j hj) θt t,
        ((1 : singAlg Q j (Λ ∘ Fin.castLE hj) θh) ⊗ₜ[k]
          ((1 : Cp) ⊗ₜ[k] x : Cp ⊗[k] St)) • G (t, h) = G (t, h) := by
  have hspect : ∀ (w : plusMidObj Q hQ Λ Λc j hj β θh θt N) (x : St) h,
      singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N
          (plusMidToHead Q hQ Λ Λc j hj β θh θt N
            ((x ⊗ₜ[k] (1 : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :
              St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) • w)) h =
        ((1 : singAlg Q j (Λ ∘ Fin.castLE hj) θh) ⊗ₜ[k] ((1 : Cp) ⊗ₜ[k] x : Cp ⊗[k] St)) •
          singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N
            (plusMidToHead Q hQ Λ Λc j hj β θh θt N w) h := fun w x h => by
    rw [plusMidObj_smul]
    exact singCoord_spect Q hQ j _ _ _ N _ _ h
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun t => ?_, fun t h x hx => ?_⟩
    · have := (mem_range_singCoord_iff Q hQ j (Λ ∘ Fin.castLE hj) θh _ N _).1
        ⟨plusMidToHead Q hQ Λ Λc j hj β θh θt N (singCoord Q hQ (ℓ - j) (plusTailLabels Λ j hj)
          θt (AlgCat.of k (Hd ⊗[k] Cp)) (plusMidObj Q hQ Λ Λc j hj β θh θt N) y t), rfl⟩
      exact (singAdm_iff Q j _ _ _ N _).1 this
    · have hw := (singAdm_iff Q (ℓ - j) _ _ _ _ _).1
        ((mem_range_singCoord_iff Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt _ _ _).1 ⟨y, rfl⟩) t x hx
      exact (hspect _ x h).symm.trans (congrArg (fun w => singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh
        (AlgCat.of k (Cp ⊗[k] St)) N (plusMidToHead Q hQ Λ Λc j hj β θh θt N w) h) hw)
  · rintro ⟨h1, h2⟩
    choose w hw using fun t => (mem_range_singCoord_iff Q hQ j (Λ ∘ Fin.castLE hj) θh _ N
      (fun h => G (t, h))).2 ((singAdm_iff Q j _ _ _ N _).2 (h1 t))
    have hfix : ∀ t, ∀ x ∈ singConds Q (ℓ - j) (plusTailLabels Λ j hj) θt t,
        (x ⊗ₜ[k] (1 : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k))) •
          plusHeadToMid Q hQ Λ Λc j hj β θh θt N (w t) =
          plusHeadToMid Q hQ Λ Λc j hj β θh θt N (w t) := fun t x hx =>
      singCoord_injective Q hQ j _ _ _ N (funext fun h => (hspect _ x h).trans
        ((congrArg _ (congrFun (hw t) h)).trans ((h2 t h x hx).trans (congrFun (hw t) h).symm)))
    obtain ⟨y, hy⟩ := (mem_range_singCoord_iff Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt _ _
      fun t => plusHeadToMid Q hQ Λ Λc j hj β θh θt N (w t)).2
        ((singAdm_iff Q (ℓ - j) _ _ _ _ _).2 hfix)
    refine ⟨y, funext fun ⟨t, h⟩ => ?_⟩
    change singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N
      (plusMidToHead Q hQ Λ Λc j hj β θh θt N (singCoord Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt
        (AlgCat.of k (Hd ⊗[k] Cp)) (plusMidObj Q hQ Λ Λc j hj β θh θt N) y t)) h = _
    rw [hy]
    exact congrFun (hw t) h

/-- The first block: a pure tensor `e(a) ⊗ x` with a loading idempotent acts on the coordinate
`h` by `L_{h,a} ⊗ x`. -/
theorem plusHeadCoord_smul_tmul (cA : Seq (stendhalWeight j (singWeight j θh))) (x : Cp ⊗[k] St)
    (z : plusHeadObj Q hQ Λ Λc j hj β θh θt N) (h : singIdx j θh) :
    singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N
        ((tensorLoad Q (Λ ∘ Fin.castLE hj) (singWeight j θh) cA ⊗ₜ[k]
          (x : (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k))) • z) h =
      (singLoad Q j (Λ ∘ Fin.castLE hj) θh h cA ⊗ₜ[k]
          (x : (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k))) •
        singCoord Q hQ j (Λ ∘ Fin.castLE hj) θh (AlgCat.of k (Cp ⊗[k] St)) N z h := by
  rw [tmul_smul_split, singCoord_load, singCoord_spect, ← mul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The last block: a pure tensor `a ⊗ b ⊗ e(c)` with a loading idempotent in the last block acts
on the coordinate `t` of the last block by `L_{t,c} ⊗ (a ⊗ b)`. -/
theorem plusTailCoord_smul_tmul (cC : Seq (stendhalWeight (ℓ - j) (singWeight (ℓ - j) θt)))
    (a : Hd) (b : Cp) (y : (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N)
    (t : singIdx (ℓ - j) θt) :
    singCoord Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))
        (plusMidObj Q hQ Λ Λc j hj β θh θt N) (plusOuterToTail Q hQ Λ Λc j hj β θh θt N
          (((a ⊗ₜ[k] (b ⊗ₜ[k] tensorLoad Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt) cC) :
            plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt))) • y)) t =
      (singLoad Q (ℓ - j) (plusTailLabels Λ j hj) θt t cC ⊗ₜ[k]
          ((a ⊗ₜ[k] b : Hd ⊗[k] Cp) : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k))) •
        singCoord Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))
          (plusMidObj Q hQ Λ Λc j hj β θh θt N) (plusOuterToTail Q hQ Λ Λc j hj β θh θt N y) t := by
  have e : ((tensorRotate (k := k) Tl Hd Cp).symm
      (a ⊗ₜ[k] (b ⊗ₜ[k] tensorLoad Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt) cC)) :
        Tl ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) =
      tensorLoad Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt) cC ⊗ₜ[k]
        ((a ⊗ₜ[k] b : Hd ⊗[k] Cp) : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :=
    tensorRotate_symm_tmul _ _ _
  rw [plusOuterToTail_smul, e, tmul_smul_split]
  rw [singCoord_load Q hQ (ℓ - j) (plusTailLabels Λ j hj) θt (AlgCat.of k (Hd ⊗[k] Cp))
    (plusMidObj Q hQ Λ Λc j hj β θh θt N),
    singCoord_spect, ← mul_smul, tmul_one_mul_one_tmul]

/-- The middle stage: `x ⊗ (a ⊗ b)` acts on the first block as `a ⊗ (b ⊗ x)`. -/
theorem plusMidObj_smul_tmul (x : St) (a : Hd) (b : Cp) (w : plusMidObj Q hQ Λ Λc j hj β θh θt N) :
    plusMidToHead Q hQ Λ Λc j hj β θh θt N
        ((x ⊗ₜ[k] ((a ⊗ₜ[k] b : Hd ⊗[k] Cp) : (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) :
          St ⊗[k] (AlgCat.of k (Hd ⊗[k] Cp) : AlgCat.{u} k)) • w) =
      ((a ⊗ₜ[k] ((b ⊗ₜ[k] x : Cp ⊗[k] St) : (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k)) :
        Hd ⊗[k] (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k)) •
          plusMidToHead Q hQ Λ Λc j hj β θh θt N w) := by
  change (tensorRotate (k := k) St Hd Cp (x ⊗ₜ[k] (a ⊗ₜ[k] b)) •
    plusMidToHead Q hQ Λ Λc j hj β θh θt N w) = _
  rw [tensorRotate_tmul]

/-- **The action of the algebra of the three blocks on the coordinates**: a pure tensor
`e(a) ⊗ b ⊗ e(c)`, with loading idempotents in the first and the last block, acts on the
coordinate `(t, h)` by `L_{h,a} ⊗ b ⊗ L_{t,c}`. -/
theorem plusOuterCoord_smul_tmul (cA : Seq (stendhalWeight j (singWeight j θh)))
    (b : Cp) (cC : Seq (stendhalWeight (ℓ - j) (singWeight (ℓ - j) θt)))
    (y : (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N)
    (t : singIdx (ℓ - j) θt) (h : singIdx j θh) :
    plusOuterCoord Q hQ Λ Λc j hj β θh θt N
        (((tensorLoad Q (Λ ∘ Fin.castLE hj) (singWeight j θh) cA ⊗ₜ[k]
          (b ⊗ₜ[k] tensorLoad Q (plusTailLabels Λ j hj) (singWeight (ℓ - j) θt) cC)) :
          plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)) • y) (t, h) =
      (singLoad Q j (Λ ∘ Fin.castLE hj) θh h cA ⊗ₜ[k]
          ((b ⊗ₜ[k] singLoad Q (ℓ - j) (plusTailLabels Λ j hj) θt t cC : Cp ⊗[k] St) :
            (AlgCat.of k (Cp ⊗[k] St) : AlgCat.{u} k))) •
        plusOuterCoord Q hQ Λ Λc j hj β θh θt N y (t, h) := by
  unfold plusOuterCoord
  rw [plusTailCoord_smul_tmul, plusMidObj_smul_tmul, plusHeadCoord_smul_tmul]

/-! ### Coordinates of `S_+` -/

/-- The outer standardizations of `N`. -/
abbrev plusOuterObj :
    ModuleCat.{u} (plusFactorAlgCat Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)) :=
  (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N

local notation "PIn" => PlusInput Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)
  (PlusWrap Q Λ Λc j hj (singWeight j θh) β (singWeight (ℓ - j) θt)
    (plusOuterObj Q hQ Λ Λc j hj β θh θt N))
local notation "PInner" => CutInput Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β
  (singWeight (ℓ - j) θt) (BlocksInner Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
    (singWeight (ℓ - j) θt) PIn)
local notation "PShO" => Shuffle (Seq.card_add'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j
    (singWeight j θh)))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (2 + (ℓ - j))
    (β + singWeight (ℓ - j) θt))))
local notation "PShI" => Shuffle (Seq.card_add'
  (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 β))
  (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j)
    (singWeight (ℓ - j) θt))))

/-- An element of `S_+(N)` as an element of the partial standardization with three blocks. -/
def plusStagedToBlocks : (plusStagedStd Q hQ Λ Λc j hj β θh θt).obj N →+
    BlocksStandard Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β (singWeight (ℓ - j) θt)
      PIn hQ :=
  AddMonoidHom.id _

/-- An inner coordinate of the partial standardization with three blocks, as an element of the
outer standardizations. -/
def plusInnerToOuter : PInner →+ (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N :=
  AddMonoidHom.id _

/-- An element of the outer standardizations, as an inner coordinate. -/
def plusOuterToInner : (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N →+ PInner :=
  AddMonoidHom.id _

/-- The three-block shuffle coordinates of an element of `S_+(N)`. -/
def plusBlocksCoord (z : (plusStagedStd Q hQ Λ Λc j hj β θh θt).obj N) (u : PShO) (v : PShI) :
    PInner :=
  (blocksStandardShuffleEquiv Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
    (singWeight (ℓ - j) θt) PIn hQ (plusStagedToBlocks Q hQ Λ Λc j hj β θh θt N z) :
      PShO → PShI → PInner) u v

/-- **The coordinates of `S_+(N)`**: the coordinate `(u_out, u_in, t, h)` is the coordinate
`(t, h)` of the outer standardizations of the three-block coordinate `(u_out, u_in)`. -/
def plusStagedCoord (z : (plusStagedStd Q hQ Λ Λc j hj β θh θt).obj N) (u : PShO) (v : PShI)
    (p : singIdx (ℓ - j) θt × singIdx j θh) : N :=
  plusOuterCoord Q hQ Λ Λc j hj β θh θt N
    (plusInnerToOuter Q hQ Λ Λc j hj β θh θt N (plusBlocksCoord Q hQ Λ Λc j hj β θh θt N z u v)) p

theorem plusStagedCoord_injective :
    Function.Injective (plusStagedCoord Q hQ Λ Λc j hj β θh θt N) := fun z z' h => by
  have hb : plusBlocksCoord Q hQ Λ Λc j hj β θh θt N z =
      plusBlocksCoord Q hQ Λ Λc j hj β θh θt N z' :=
    funext fun u => funext fun v => plusOuterCoord_injective Q hQ Λ Λc j hj β θh θt N
      (funext fun p => congrFun (congrFun (congrFun h u) v) p)
  exact (blocksStandardShuffleEquiv Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
    (singWeight (ℓ - j) θt) PIn hQ).injective (Subtype.ext hb)

/-- **The coordinate families of `S_+(N)`**: a family `G` is the coordinate family of an element
iff its rows `G(u_out, u_in)` are the coordinates of elements `F(u_out, u_in)` of the outer
standardizations that form a three-block coordinate family (the conditions of
`mem_blocksShuffleCoords_iff`). The elements `F(u_out, u_in)` are unique
(`plusOuterCoord_injective`), and the conditions on them are in coordinates by
`mem_range_plusOuterCoord_iff` and `plusOuterCoord_smul_tmul`. -/
theorem mem_range_plusStagedCoord_iff
    (G : PShO → PShI → singIdx (ℓ - j) θt × singIdx j θh → N) :
    G ∈ Set.range (plusStagedCoord Q hQ Λ Λc j hj β θh θt N) ↔
      ∃ F : PShO → PShI → (plusOuterStd Q hQ Λ Λc j hj β θh θt).obj N,
        (∀ u v, plusOuterCoord Q hQ Λ Λc j hj β θh θt N (F u v) = G u v) ∧
        (∀ u v, cutShuffleIdem Q (blocksTailLabels (plusBlockLabels Λ Λc j hj)) β
            (singWeight (ℓ - j) θt) v • plusOuterToInner Q hQ Λ Λc j hj β θh θt N (F u v) =
          plusOuterToInner Q hQ Λ Λc j hj β θh θt N (F u v)) ∧
        ∀ u v, blocksRowIdem Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
            (singWeight (ℓ - j) θt) u v •
            innerVal Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β (singWeight (ℓ - j) θt)
              PIn (plusOuterToInner Q hQ Λ Λc j hj β θh θt N (F u v)) =
          innerVal Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β (singWeight (ℓ - j) θt)
            PIn (plusOuterToInner Q hQ Λ Λc j hj β θh θt N (F u v)) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun u v => plusInnerToOuter Q hQ Λ Λc j hj β θh θt N
      (plusBlocksCoord Q hQ Λ Λc j hj β θh θt N z u v), fun _ _ => rfl,
      (mem_blocksShuffleCoords_iff Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
        (singWeight (ℓ - j) θt) PIn hQ _).1 (blocksStandardShuffleEquiv Q
          (plusBlockLabels Λ Λc j hj) (singWeight j θh) β (singWeight (ℓ - j) θt) PIn hQ
            (plusStagedToBlocks Q hQ Λ Λc j hj β θh θt N z)).2⟩
  · rintro ⟨F, hF, h1, h2⟩
    have hmem := (mem_blocksShuffleCoords_iff Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
      (singWeight (ℓ - j) θt) PIn hQ
        (fun u v => plusOuterToInner Q hQ Λ Λc j hj β θh θt N (F u v))).2 ⟨h1, h2⟩
    refine ⟨(blocksStandardShuffleEquiv Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
      (singWeight (ℓ - j) θt) PIn hQ).symm ⟨_, hmem⟩, funext fun u => funext fun v => ?_⟩
    change plusOuterCoord Q hQ Λ Λc j hj β θh θt N (plusInnerToOuter Q hQ Λ Λc j hj β θh θt N
      (((blocksStandardShuffleEquiv Q (plusBlockLabels Λ Λc j hj) (singWeight j θh) β
        (singWeight (ℓ - j) θt) PIn hQ ((blocksStandardShuffleEquiv Q (plusBlockLabels Λ Λc j hj)
          (singWeight j θh) β (singWeight (ℓ - j) θt) PIn hQ).symm ⟨_, hmem⟩)) :
            PShO → PShI → PInner) u v)) = G u v
    rw [LinearEquiv.apply_symm_apply]
    exact hF u v

end CupCap

end Categorification.Stendhal
