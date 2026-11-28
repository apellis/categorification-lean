/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlocksStandardBasis
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons

/-!
# The standard basis of the standardization with singleton blocks, in stages

Webster, arXiv:1309.3796v3, §5.1, the standardization of Definition 5.4 with one block for each
red strand, in the staged induced model (`singStd`); used in §7.3, proof of Lemma 7.19, for the
standard basis of `S_+` (Webster states no basis of a partial standardization). Each stage is a
partial standardization at a cut with a spectator, so by the shuffle decomposition of a cut
(`cutStandardShuffleEquiv`), iterated, an element of `singStd n M` is determined by its family
of coordinates `G : Idx_n → M`, where `Idx_n` is the set of tuples `(u_1, …, u_n)` of shuffles,
one for each stage (`singIdx`, `singCoord`, `singCoord_injective`). The coordinate families are
exactly those satisfying, at every stage, a row condition `E_{i,u} G(i, u) = G(i, u)`
(`singAdm`, `mem_range_singCoord_iff`), with `E_{i,u}` an explicit element of the algebra of the
singleton blocks (`singRow`). The spectator acts coordinatewise (`singCoord_spect`) and a
loading idempotent `e(c)` of `T^λ(θ_1 + ⋯ + θ_n)` acts on the coordinate `i` by an explicit
element `L_{i,c}` of the algebra of the singleton blocks (`singCoord_load`).

The single stage is the shuffle decomposition of a cut with a spectator (`cutSpectCoord`): the
spectator acts coordinatewise, `e(t)` acts on the coordinate `u` by `1_{u t} ⊗ 1`, and the
coordinate families are those fixed coordinatewise by `ε_u ⊗ 1`.

Any commutative ring `k`, symmetric `Q`.

## Main definitions

* `Stendhal.tensorLoad`: the loading idempotent `e(c)` of `T^λ(ν)`.
* `Stendhal.cutSpectCoord`: the shuffle coordinates of a cut with a spectator.
* `Stendhal.singIdx`, `Stendhal.singCoord`, `Stendhal.singLoad`, `Stendhal.singRow`,
  `Stendhal.singAdm`.

## Main results

* `Stendhal.cutSpectCoord_spect`, `Stendhal.cutSpectCoord_load`,
  `Stendhal.mem_range_cutSpectCoord_iff`.
* `Stendhal.singCoord_spect`, `Stendhal.singCoord_load`, `Stendhal.singCoord_injective`,
  `Stendhal.mem_range_singCoord_iff`.
-/

universe u

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

/-! ### Loading idempotents of `T^λ` -/

section Load

variable {I k : Type*} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- The loading idempotent `e(c)` of `T^λ(ν)`, for a loading `c` of all strands. -/
def tensorLoad {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) (c : Seq (stendhalWeight n ν)) :
    TensorProductAlgebra k Q Λ ν :=
  TensorProductAlgebra.mk Q Λ ν
    (orderProjection Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν (e c)))

variable {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)

omit [DecidableEq I] in
private theorem seq_cast_cast_symm {J : Type*} {μ μ' : Multiset J} (h : μ = μ') (c : Seq μ') :
    Seq.cast h (Seq.cast h.symm c) = c := by
  subst h; rfl

/-- The loading idempotents of the first block of a cut. -/
theorem cutPrefixProjection_e (p : Seq α) :
    cutPrefixProjection Q Λ θ (e p) = tensorLoad Q (Λ ∘ Fin.castAdd r) θ
      ((redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r) θ).equiv.symm p) := by
  have h : (relabelEquiv (redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r)
      θ)).symm (e p) = e ((redSubfamilyRelabel Q Λ (Fin.castAdd r) (Fin.castAdd_injective a r)
        θ).equiv.symm p) :=
    (AlgEquiv.symm_apply_eq _).2 ((relabelHom_e (redSubfamilyRelabel Q Λ (Fin.castAdd r)
      (Fin.castAdd_injective a r) θ) _).trans (by rw [Equiv.apply_symm_apply])).symm
  simp only [cutPrefixProjection, redSubfamilyProjection, tensorLoad, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, h]

/-- The loading idempotents of `T^λ(θ + β)` are images of affine loading idempotents. -/
theorem tensorLoad_eq_affineToTensor (c : Seq (stendhalWeight (a + r) (θ + β))) :
    tensorLoad Q Λ (θ + β) c = affineToTensor Q Λ θ β
      (e (Seq.cast (cutInputWeights_add (a := a) (r := r) θ β).symm c)) := by
  have h := seq_cast_cast_symm (cutInputWeights_add (a := a) (r := r) θ β) c
  simp only [affineToTensor, tensorLoad, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_e, h]

/-- `((a ⊗ 1) ⊗ 1) ((1 ⊗ b) ⊗ 1) = (a ⊗ b) ⊗ 1` in a triple tensor product of algebras. -/
theorem tmul_one_tmul_mul_one_tmul_tmul {R A B C : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Ring B] [Algebra R B] [Ring C] [Algebra R C] (a : A) (b : B) :
    (((a ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) * (((1 : A) ⊗ₜ[R] b) ⊗ₜ[R] (1 : C)) :
      (A ⊗[R] B) ⊗[R] C) = (a ⊗ₜ[R] b) ⊗ₜ[R] (1 : C) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    mul_one]

end Load

/-! ### Shuffle coordinates of a cut with a spectator -/

section Spect

variable {I k : Type u} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
  (E : AlgCat.{u} k) (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "Sh" => Shuffle (Seq.card_add' α δ)

variable (X : ModuleCat.{u} (cutSpectAlgebra Q Λ θ β E))

/-- The input of the cut with a spectator, as a module over the affine block algebra. -/
abbrev CutSpectIn : Type u := CutInput Q Λ θ β (CutSpectInput Q Λ θ β E X)

/-- **The shuffle coordinates of a cut with a spectator**, with values in the input module. -/
def cutSpectCoord : (cutSpectFunctor Q Λ θ β E hQ).obj X →+ (Sh → X) where
  toFun z u := (show X from
    (cutStandardShuffleEquiv Q Λ θ β _ hQ z : Sh → CutSpectIn Q Λ θ β E X) u)
  map_zero' := by
    funext u
    exact congrFun (congrArg Subtype.val (map_zero (cutStandardShuffleEquiv Q Λ θ β
      (CutSpectInput Q Λ θ β E X) hQ))) u
  map_add' z z' := by
    funext u
    exact congrFun (congrArg Subtype.val (map_add (cutStandardShuffleEquiv Q Λ θ β
      (CutSpectInput Q Λ θ β E X) hQ) z z')) u

theorem cutSpectCoord_injective : Function.Injective (cutSpectCoord Q Λ θ β E hQ X) :=
  fun _ _ h => (cutStandardShuffleEquiv Q Λ θ β _ hQ).injective (Subtype.ext h)

/-- The spectator acts on the shuffle coordinates coordinatewise. -/
theorem cutSpectCoord_spect (z : (cutSpectFunctor Q Λ θ β E hQ).obj X) (x : E) (u : Sh) :
    cutSpectCoord Q Λ θ β E hQ X
        (((1 : TensorProductAlgebra k Q Λ (θ + β)) ⊗ₜ[k] x) • z) u =
      cutSpectTmul Q Λ θ β E 1 x • cutSpectCoord Q Λ θ β E hQ X z u := by
  have h1 : ((1 : TensorProductAlgebra k Q Λ (θ + β)) ⊗ₜ[k] x) • z =
      cutStandardMap Q Λ θ β (cutSpectEnd Q Λ θ β E X x)
        (show CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E X) from z) := by
    change cutStandardAction Q Λ θ β _ hQ 1 (cutSpectAction Q Λ θ β E X x z) = _
    rw [map_one]
    rfl
  refine (congrArg (fun w => (cutStandardShuffleEquiv Q Λ θ β (CutSpectInput Q Λ θ β E X) hQ w :
    Sh → CutSpectIn Q Λ θ β E X) u) h1).trans ?_
  exact (cutStandardShuffleEquiv_map Q Λ θ β hQ _ _ u).trans rfl

/-- An affine block idempotent acts on the input of the cut with a spectator through the block
algebra. -/
theorem cutSpectIn_smul (b : TensorKLR (stendhalQ Q Λ) α δ) (y : CutSpectIn Q Λ θ β E X) :
    (show X from b • y) = cutSpectTmul Q Λ θ β E (cutInputMap Q Λ θ β b) 1 • (show X from y) :=
  rfl

/-- **A loading idempotent acts on the shuffle coordinates of a cut with a spectator**: `e(t)`
acts on the coordinate `u` by `1_{u t} ⊗ 1`. -/
theorem cutSpectCoord_load (z : (cutSpectFunctor Q Λ θ β E hQ).obj X) (t : Seq (α + δ))
    (u : Sh) :
    cutSpectCoord Q Λ θ β E hQ X ((affineToTensor Q Λ θ β (e t) ⊗ₜ[k] (1 : E)) • z) u =
      cutSpectTmul Q Λ θ β E (cutInputMap Q Λ θ β (concatIdem (Q := stendhalQ Q Λ) (u.1 • t))) 1 •
        cutSpectCoord Q Λ θ β E hQ X z u := by
  have h1 : (affineToTensor Q Λ θ β (e t) ⊗ₜ[k] (1 : E)) • z =
      cutStandardAction Q Λ θ β _ hQ (affineToTensor Q Λ θ β (e t))
        (show CutStandard Q Λ θ β (CutSpectInput Q Λ θ β E X) from z) := by
    change cutStandardAction Q Λ θ β _ hQ _ (cutSpectAction Q Λ θ β E X 1 z) = _
    rw [map_one]
    rfl
  refine (congrArg (fun w => (cutStandardShuffleEquiv Q Λ θ β (CutSpectInput Q Λ θ β E X) hQ w :
    Sh → CutSpectIn Q Λ θ β E X) u) h1).trans ?_
  exact (cutStandardShuffleEquiv_action_e Q Λ θ β hQ t _ u).trans rfl

/-- **The coordinate families of a cut with a spectator**: `g` is a family of shuffle
coordinates iff `ε_u ⊗ 1` fixes `g u` for every `u`. -/
theorem mem_range_cutSpectCoord_iff (g : Sh → X) :
    g ∈ Set.range (cutSpectCoord Q Λ θ β E hQ X) ↔
      ∀ u, cutSpectTmul Q Λ θ β E (cutInputMap Q Λ θ β (cutShuffleIdem Q Λ θ β u)) 1 • g u =
        g u := by
  have hin : ∀ h : Sh → CutSpectIn Q Λ θ β E X, h ∈ cutShuffleCoords Q Λ θ β
      (CutSpectInput Q Λ θ β E X) ↔ ∀ u, cutShuffleIdem Q Λ θ β u • h u = h u := fun h => by
    simp only [cutShuffleCoords, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    exact forall_congr' fun u => cutShuffleIdem_mem_range_iff _ _ _ _ _ u (h u)
  constructor
  · rintro ⟨z, rfl⟩
    exact (hin _).1 (cutStandardShuffleEquiv Q Λ θ β _ hQ z).2
  · intro hg
    refine ⟨(cutStandardShuffleEquiv Q Λ θ β _ hQ).symm ⟨fun u => g u, (hin _).2 hg⟩, ?_⟩
    funext u
    exact congrFun (congrArg Subtype.val
      ((cutStandardShuffleEquiv Q Λ θ β (CutSpectInput Q Λ θ β E X) hQ).apply_symm_apply
        ⟨fun u => g u, (hin _).2 hg⟩)) u

end Spect

/-! ### Coordinates of the standardization in stages -/

section Stages

variable {I k : Type u} [DecidableEq I] [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

/-- The shuffles of the last stage `n | 1` of the standardization of `n + 1` singleton blocks. -/
abbrev singSh (n : ℕ) (θ : Fin (n + 1) → Multiset I) : Type :=
  Shuffle (Seq.card_add'
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
      (stendhalWeight n (singWeight n (θ ∘ Fin.castSucc))))
    (Multiset.map (Sum.map (id : I → I) (Fin.natAdd n)) (stendhalWeight 1 (θ (Fin.last n)))))

/-- The index set of the coordinates of the standardization of `n` singleton blocks: one
shuffle for each stage. -/
def singIdx : (n : ℕ) → (Fin n → Multiset I) → Type
  | 0, _ => Unit
  | n + 1, θ => singIdx n (θ ∘ Fin.castSucc) × singSh n θ

/-- The spectator algebra of the inner stages. -/
abbrev singSpect (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) : AlgCat.{u} k :=
  AlgCat.of k (singLast Q Λ θ ⊗[k] E)

/-- The module `M`, restricted to the algebra of the inner stages and their spectator. -/
abbrev singInnerIn (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    ModuleCat.{u} (singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k]
      singSpect Q n Λ θ E) :=
  (ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E)).obj M

/-- The module of the inner stages of the standardization of `n + 1` singleton blocks. -/
abbrev singInner (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :=
  (singStd Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (AlgCat.of k (singLast Q Λ θ ⊗[k] E))).obj
    ((ModuleCat.restrictScalars.{u} (singAssocIn Q n Λ θ E)).obj M)

/-- The input of the last cut of the standardization of `n + 1` singleton blocks. -/
abbrev singCutIn (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :=
  (ModuleCat.restrictScalars.{u} (singAssocOut Q n Λ θ E)).obj (singInner Q hQ n Λ θ E M)

/-- The shuffle coordinates of the last cut of the standardization of `n + 1` singleton
blocks. -/
def singCutCoord (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    (singStd Q hQ (n + 1) Λ θ E).obj M →+ (singSh n θ → singCutIn Q hQ n Λ θ E M) :=
  cutSpectCoord (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ
    (singCutIn Q hQ n Λ θ E M)

/-- An element of the input of the last cut, as an element of the module of the inner
stages. -/
def singCutToInner (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    singCutIn Q hQ n Λ θ E M →+ singInner Q hQ n Λ θ E M :=
  AddMonoidHom.id _

/-- An element of the restriction of `M` to the inner stages, as an element of `M`. -/
def singInnerToM (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    singInnerIn Q n Λ θ E M →+ M :=
  AddMonoidHom.id _

/-- **The coordinates of the standardization in stages**: the coordinate `(i, u)` of an
element of `singStd (n + 1) M` is the coordinate `i` of its shuffle coordinate `u` at the last
stage. -/
def singCoord : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (singStd Q hQ n Λ θ E).obj M → singIdx n θ → M
  | 0, _, _, _, _ => fun z _ => z
  | n + 1, Λ, θ, E, M => fun z p => singInnerToM Q n Λ θ E M
      (singCoord n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
        (singInnerIn Q n Λ θ E M)
        (singCutToInner Q hQ n Λ θ E M (singCutCoord Q hQ n Λ θ E M z p.2)) p.1)

theorem singCoord_succ (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (z : (singStd Q hQ (n + 1) Λ θ E).obj M) (i : singIdx n (θ ∘ Fin.castSucc))
    (u : singSh n θ) :
    singCoord Q hQ (n + 1) Λ θ E M z (i, u) = singInnerToM Q n Λ θ E M
      (singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
        (singInnerIn Q n Λ θ E M)
        (singCutToInner Q hQ n Λ θ E M (singCutCoord Q hQ n Λ θ E M z u)) i) :=
  rfl

theorem singCoord_zero : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) → (i : singIdx n θ) →
    singCoord Q hQ n Λ θ E M 0 i = 0
  | 0, _, _, _, _, _ => rfl
  | n + 1, Λ, θ, E, M, (i, u) => by
    rw [singCoord_succ, map_zero, Pi.zero_apply]
    exact singCoord_zero n _ _ _ _ i

theorem singCoord_add : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (z z' : (singStd Q hQ n Λ θ E).obj M) → (i : singIdx n θ) →
    singCoord Q hQ n Λ θ E M (z + z') i =
      singCoord Q hQ n Λ θ E M z i + singCoord Q hQ n Λ θ E M z' i
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, Λ, θ, E, M, z, z', (i, u) => by
    rw [singCoord_succ, singCoord_succ, singCoord_succ, map_add, Pi.add_apply]
    exact singCoord_add n _ _ _ _ _ _ i

/-- The coordinates, as an additive map. -/
def singCoordHom (n : ℕ) (Λ : Fin n → I →₀ ℕ) (θ : Fin n → Multiset I) (E : AlgCat.{u} k)
    (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) :
    (singStd Q hQ n Λ θ E).obj M →+ (singIdx n θ → M) where
  toFun := singCoord Q hQ n Λ θ E M
  map_zero' := funext (singCoord_zero Q hQ n Λ θ E M)
  map_add' z z' := funext (singCoord_add Q hQ n Λ θ E M z z')

theorem singCoord_sum {ι : Type*} (s : Finset ι) (n : ℕ) (Λ : Fin n → I →₀ ℕ)
    (θ : Fin n → Multiset I) (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E))
    (z : ι → (singStd Q hQ n Λ θ E).obj M) (i : singIdx n θ) :
    singCoord Q hQ n Λ θ E M (∑ j ∈ s, z j) i = ∑ j ∈ s, singCoord Q hQ n Λ θ E M (z j) i := by
  have := congrFun (map_sum (singCoordHom Q hQ n Λ θ E M) z s) i
  rwa [Finset.sum_apply] at this

/-- The action on the input of the last cut, through the inner stages. -/
theorem singCutIn_smul (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (P : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)))
    (C : singLast Q Λ θ) (x : E) (y : singCutIn Q hQ n Λ θ E M) :
    singCutToInner Q hQ n Λ θ E M
        (cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E
          (P ⊗ₜ[k] C) x • y) =
      ((P ⊗ₜ[k] (C ⊗ₜ[k] x : singLast Q Λ θ ⊗[k] E) :
          TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
            singSpect Q n Λ θ E)) • singCutToInner Q hQ n Λ θ E M y :=
  rfl

/-- The action on the restriction of the module to the inner stages. -/
theorem singInnerIn_smul (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (b : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) (C : singLast Q Λ θ) (x : E)
    (m : singInnerIn Q n Λ θ E M) :
    singInnerToM Q n Λ θ E M ((b ⊗ₜ[k] (C ⊗ₜ[k] x : singLast Q Λ θ ⊗[k] E) :
        singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k] singSpect Q n Λ θ E) • m) =
      (((b ⊗ₜ[k] C : singAlg Q (n + 1) Λ θ) ⊗ₜ[k] x : singAlg Q (n + 1) Λ θ ⊗[k] E)) •
        singInnerToM Q n Λ θ E M m :=
  rfl

/-- **The spectator acts coordinatewise.** -/
theorem singCoord_spect : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (z : (singStd Q hQ n Λ θ E).obj M) → (x : E) → (i : singIdx n θ) →
    singCoord Q hQ n Λ θ E M
        (((1 : TensorProductAlgebra k Q Λ (singWeight n θ)) ⊗ₜ[k] x) • z) i =
      ((1 : singAlg Q n Λ θ) ⊗ₜ[k] x) • singCoord Q hQ n Λ θ E M z i
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, Λ, θ, E, M, z, x, (i, u) => by
    rw [singCoord_succ, singCoord_succ]
    have h1 : singCutCoord Q hQ n Λ θ E M
        (((1 : TensorProductAlgebra k Q Λ (singWeight (n + 1) θ)) ⊗ₜ[k] x) • z) u =
        cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E
          1 x • singCutCoord Q hQ n Λ θ E M z u :=
      cutSpectCoord_spect (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ (singCutIn Q hQ n Λ θ E M) z x u
    have h2 := singCutIn_smul Q hQ n Λ θ E M 1 1 x (singCutCoord Q hQ n Λ θ E M z u)
    rw [← Algebra.TensorProduct.one_def] at h2
    rw [h1, h2, singCoord_spect n]
    exact singInnerIn_smul Q n Λ θ E M 1 1 x _

/-- The weight of the first block of the last cut. -/
local notation "αS" n "," θ => Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
  (stendhalWeight n (singWeight n (θ ∘ Fin.castSucc)))
/-- The weight of the last block of the last cut. -/
local notation "δS" n "," θ => Multiset.map (Sum.map (id : I → I) (Fin.natAdd n))
  (stendhalWeight 1 (θ (Fin.last n)))

/-- The image of `1_t` in the coordinate `i` of the inner stages, for an affine loading `t` of
the last cut: `∑_{a b = t} L_{i, a} ⊗ e(b)`. -/
def singCutLoad (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (L : Seq (stendhalWeight n (singWeight n (θ ∘ Fin.castSucc))) →
      singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc))
    (t : Seq ((αS n, θ) + (δS n, θ))) : singAlg Q (n + 1) Λ θ :=
  ∑ p ∈ Finset.univ.filter (fun p : Seq (αS n, θ) × Seq (δS n, θ) => p.1.append p.2 = t),
    L ((redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective n 1)
        (singWeight n (θ ∘ Fin.castSucc))).equiv.symm p.1) ⊗ₜ[k]
      cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p.2)

/-- **The action of a loading idempotent on the coordinates**: the element `L_{i,c}` of the
algebra of the singleton blocks by which `e(c)` acts on the coordinate `i`. -/
def singLoad : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) → singIdx n θ →
    Seq (stendhalWeight n (singWeight n θ)) → singAlg Q n Λ θ
  | 0, Λ, _, _, c => tensorLoad Q Λ 0 c
  | n + 1, Λ, θ, (i, u), c => singCutLoad Q n Λ θ
      (singLoad n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i)
      (u.1 • Seq.cast (cutInputWeights_add (a := n) (r := 1)
        (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))).symm c)

theorem cutSpectTmul_sum {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
    (E : AlgCat.{u} k) {ι : Type*} (s : Finset ι) (d : ι → cutFactorAlgebra Q Λ θ β) (x : E) :
    cutSpectTmul Q Λ θ β E (∑ j ∈ s, d j) x = ∑ j ∈ s, cutSpectTmul Q Λ θ β E (d j) x :=
  TensorProduct.sum_tmul _ _ _

/-- The product of the actions of the two blocks of the last cut on the restriction of `M`. -/
theorem singInnerToM_smul_smul (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (L : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) (S : singLast Q Λ θ)
    (m : singInnerIn Q n Λ θ E M) :
    singInnerToM Q n Λ θ E M ((L ⊗ₜ[k] (1 : singSpect Q n Λ θ E)) •
      (((1 : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) ⊗ₜ[k]
        (S ⊗ₜ[k] (1 : E) : singLast Q Λ θ ⊗[k] E) :
          singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k] singSpect Q n Λ θ E) • m)) =
      (((L ⊗ₜ[k] S : singAlg Q (n + 1) Λ θ) ⊗ₜ[k] (1 : E) : singAlg Q (n + 1) Λ θ ⊗[k] E)) •
        singInnerToM Q n Λ θ E M m := by
  change (((L ⊗ₜ[k] (1 : singLast Q Λ θ) : singAlg Q (n + 1) Λ θ) ⊗ₜ[k] (1 : E) :
      singAlg Q (n + 1) Λ θ ⊗[k] E) •
    ((((1 : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) ⊗ₜ[k] S :
      singAlg Q (n + 1) Λ θ) ⊗ₜ[k] (1 : E) : singAlg Q (n + 1) Λ θ ⊗[k] E) •
        singInnerToM Q n Λ θ E M m)) = _
  exact (mul_smul _ _ _).symm.trans (congrArg (· • _)
    (tmul_one_tmul_mul_one_tmul_tmul (R := k) L S (C := E)))

/-- The coordinates of `(e(a) ⊗ e(b)) • y` at the last cut, given the action of loading
idempotents on the coordinates of the inner stages. -/
theorem singCoord_cutTmul_of_load (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ)
    (θ : Fin (n + 1) → Multiset I) (E : AlgCat.{u} k)
    (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (hL : ∀ (z : singInner Q hQ n Λ θ E M)
      (c : Seq (stendhalWeight n (singWeight n (θ ∘ Fin.castSucc)))) i,
      singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
          (singInnerIn Q n Λ θ E M)
          ((tensorLoad Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) c ⊗ₜ[k]
            (1 : singSpect Q n Λ θ E)) • z) i =
        (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i c ⊗ₜ[k]
            (1 : singSpect Q n Λ θ E)) •
          singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
            (singInnerIn Q n Λ θ E M) z i)
    (p₁ : Seq (αS n, θ)) (p₂ : Seq (δS n, θ)) (y : singCutIn Q hQ n Λ θ E M)
    (i : singIdx n (θ ∘ Fin.castSucc)) :
    singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
        (singInnerIn Q n Λ θ E M) (singCutToInner Q hQ n Λ θ E M
          (cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
            E (cutPrefixProjection (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (e p₁)
              ⊗ₜ[k] cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂)) 1 • y)) i =
      (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i
          ((redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective n 1)
            (singWeight n (θ ∘ Fin.castSucc))).equiv.symm p₁) ⊗ₜ[k]
          (1 : singSpect Q n Λ θ E)) •
        (((1 : singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)) ⊗ₜ[k]
          (cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂) ⊗ₜ[k] (1 : E) :
            singLast Q Λ θ ⊗[k] E) :
          singAlg Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) ⊗[k] singSpect Q n Λ θ E) •
          singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
            (singInnerIn Q n Λ θ E M) (singCutToInner Q hQ n Λ θ E M y) i) := by
  have hp : cutPrefixProjection (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (e p₁) =
      tensorLoad Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc))
        ((redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective n 1)
          (singWeight n (θ ∘ Fin.castSucc))).equiv.symm p₁) :=
    cutPrefixProjection_e Q Λ _ p₁
  have h1 := singCutIn_smul Q hQ n Λ θ E M
    (cutPrefixProjection (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (e p₁))
    (cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂)) 1 y
  have h2 : ((cutPrefixProjection (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (e p₁) ⊗ₜ[k]
        (cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂) ⊗ₜ[k] (1 : E) :
          singLast Q Λ θ ⊗[k] E) :
        TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) ⊗[k]
          singSpect Q n Λ θ E)) =
      (tensorLoad Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc))
        ((redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective n 1)
          (singWeight n (θ ∘ Fin.castSucc))).equiv.symm p₁) ⊗ₜ[k]
            (1 : singSpect Q n Λ θ E)) *
        ((1 : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc))) ⊗ₜ[k]
          (cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂) ⊗ₜ[k] (1 : E) :
            singLast Q Λ θ ⊗[k] E)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (fun q : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
      (singWeight n (θ ∘ Fin.castSucc)) => q ⊗ₜ[k] (cutSuffixProjection (a := n) (r := 1) Q Λ
        (θ (Fin.last n)) (e p₂) ⊗ₜ[k] (1 : E) : singLast Q Λ θ ⊗[k] E)) hp
  have hA := h1.trans ((congrArg (· • singCutToInner Q hQ n Λ θ E M y) h2).trans
    (mul_smul _ _ (singCutToInner Q hQ n Λ θ E M y)))
  exact (congrArg (fun w => singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
    (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M) w i) hA).trans ((hL _ _ i).trans
      (congrArg _ (singCoord_spect Q hQ n _ _ _ _ _ _ i)))

/-- The coordinates of `1_t • y` at the last cut, given the action of loading idempotents on the
coordinates of the inner stages. -/
theorem singCoord_concatIdem_of_load (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ)
    (θ : Fin (n + 1) → Multiset I) (E : AlgCat.{u} k)
    (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E))
    (hL : ∀ (z : singInner Q hQ n Λ θ E M)
      (c : Seq (stendhalWeight n (singWeight n (θ ∘ Fin.castSucc)))) i,
      singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
          (singInnerIn Q n Λ θ E M)
          ((tensorLoad Q (Λ ∘ Fin.castSucc) (singWeight n (θ ∘ Fin.castSucc)) c ⊗ₜ[k]
            (1 : singSpect Q n Λ θ E)) • z) i =
        (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i c ⊗ₜ[k]
            (1 : singSpect Q n Λ θ E)) •
          singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
            (singInnerIn Q n Λ θ E M) z i)
    (t : Seq ((αS n, θ) + (δS n, θ))) (y : singCutIn Q hQ n Λ θ E M)
    (i : singIdx n (θ ∘ Fin.castSucc)) :
    singInnerToM Q n Λ θ E M (singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M)
        (singCutToInner Q hQ n Λ θ E M
          (cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
            E (cutInputMap (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
              (θ (Fin.last n)) (concatIdem (Q := stendhalQ Q Λ) t)) 1 • y)) i) =
      (singCutLoad Q n Λ θ (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i) t ⊗ₜ[k]
        (1 : E)) • singInnerToM Q n Λ θ E M (singCoord Q hQ n (Λ ∘ Fin.castSucc)
          (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M)
          (singCutToInner Q hQ n Λ θ E M y) i) := by
  have hsum : (singCutLoad Q n Λ θ (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i) t ⊗ₜ[k]
      (1 : E) : singAlg Q (n + 1) Λ θ ⊗[k] E) =
      ∑ p ∈ Finset.univ.filter (fun p : Seq (αS n, θ) × Seq (δS n, θ) => p.1.append p.2 = t),
        ((singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i
          ((redSubfamilyRelabel Q Λ (Fin.castAdd 1) (Fin.castAdd_injective n 1)
            (singWeight n (θ ∘ Fin.castSucc))).equiv.symm p.1) ⊗ₜ[k]
          cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p.2) :
            singAlg Q (n + 1) Λ θ) ⊗ₜ[k] (1 : E)) :=
    TensorProduct.sum_tmul _ _ _
  rw [concatIdem, map_sum, cutSpectTmul_sum, Finset.sum_smul, map_sum, singCoord_sum, map_sum,
    hsum]
  refine Eq.trans ?_ Finset.sum_smul.symm
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨p₁, p₂⟩ := p
  have h0 : cutInputMap (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
      (e p₁ ⊗ₜ[k] e p₂) =
      cutPrefixProjection (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (e p₁) ⊗ₜ[k]
        cutSuffixProjection (a := n) (r := 1) Q Λ (θ (Fin.last n)) (e p₂) :=
    Algebra.TensorProduct.map_tmul _ _ _ _
  rw [h0]
  exact (congrArg (singInnerToM Q n Λ θ E M)
    (singCoord_cutTmul_of_load Q hQ n Λ θ E M hL p₁ p₂ y i)).trans
      (singInnerToM_smul_smul Q n Λ θ E M _ _ _)

/-- **A loading idempotent acts on the coordinates**: `e(c)` acts on the coordinate `i` by
`L_{i,c}`. -/
theorem singCoord_load : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (z : (singStd Q hQ n Λ θ E).obj M) → (c : Seq (stendhalWeight n (singWeight n θ))) →
    (i : singIdx n θ) →
    singCoord Q hQ n Λ θ E M ((tensorLoad Q Λ (singWeight n θ) c ⊗ₜ[k] (1 : E)) • z) i =
      (singLoad Q n Λ θ i c ⊗ₜ[k] (1 : E)) • singCoord Q hQ n Λ θ E M z i
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, Λ, θ, E, M, z, c, (i, u) => by
    rw [singCoord_succ, singCoord_succ]
    have h1 : singCutCoord Q hQ n Λ θ E M
        ((tensorLoad Q Λ (singWeight (n + 1) θ) c ⊗ₜ[k] (1 : E)) • z) u =
        cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E
          (cutInputMap (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
            (concatIdem (Q := stendhalQ Q Λ) (u.1 • Seq.cast (cutInputWeights_add (a := n)
              (r := 1) (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))).symm c))) 1 •
          singCutCoord Q hQ n Λ θ E M z u := by
      have h0 : tensorLoad Q Λ (singWeight (n + 1) θ) c = affineToTensor (a := n) (r := 1) Q Λ
          (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) (e (Seq.cast (cutInputWeights_add
            (a := n) (r := 1) (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))).symm c)) :=
        tensorLoad_eq_affineToTensor Q Λ _ _ c
      rw [h0]
      exact cutSpectCoord_load (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)) E hQ (singCutIn Q hQ n Λ θ E M) z _ u
    rw [h1]
    exact singCoord_concatIdem_of_load Q hQ n Λ θ E M
      (fun z c i => singCoord_load n _ _ _ _ z c i) _ _ i

/-- **The coordinates determine the element.** -/
theorem singCoord_injective : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    Function.Injective (singCoord Q hQ n Λ θ E M)
  | 0, _, _, _, _ => fun _ _ h => congrFun h ()
  | n + 1, Λ, θ, E, M => fun z z' h => by
    refine cutSpectCoord_injective (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
      (θ (Fin.last n)) E hQ (singCutIn Q hQ n Λ θ E M) (funext fun u => ?_)
    exact singCoord_injective n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _ _
      (funext fun i => congrFun h (i, u))

/-- The image of the cut-down idempotent `ε_u` of the last cut in the coordinate `i` of the inner
stages: `E_{i,u} = ∑_{s red-ordered} ∑_{a b = u s} L_{i, a} ⊗ e(b)`. -/
def singRow (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (i : singIdx n (θ ∘ Fin.castSucc)) (u : singSh n θ) : singAlg Q (n + 1) Λ θ :=
  ∑ s ∈ cutOrderedLoadings (a := n) (r := 1) (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)),
    singCutLoad Q n Λ θ (singLoad Q n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) i) (u.1 • s)

/-- `ε_u` in the coordinates of the inner stages. -/
theorem singCoord_cutShuffleIdem (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ)
    (θ : Fin (n + 1) → Multiset I) (E : AlgCat.{u} k)
    (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) (u : singSh n θ)
    (y : singCutIn Q hQ n Λ θ E M) (i : singIdx n (θ ∘ Fin.castSucc)) :
    singInnerToM Q n Λ θ E M (singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
        (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M)
        (singCutToInner Q hQ n Λ θ E M
          (cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n))
            E (cutInputMap (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
              (θ (Fin.last n)) (cutShuffleIdem (a := n) (r := 1) Q Λ
                (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) u)) 1 • y)) i) =
      (singRow Q n Λ θ i u ⊗ₜ[k] (1 : E)) • singInnerToM Q n Λ θ E M (singCoord Q hQ n
          (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M)
          (singCutToInner Q hQ n Λ θ E M y) i) := by
  have hsum : (singRow Q n Λ θ i u ⊗ₜ[k] (1 : E) : singAlg Q (n + 1) Λ θ ⊗[k] E) =
      ∑ s ∈ cutOrderedLoadings (a := n) (r := 1) (singWeight n (θ ∘ Fin.castSucc))
        (θ (Fin.last n)), (singCutLoad Q n Λ θ (singLoad Q n (Λ ∘ Fin.castSucc)
          (θ ∘ Fin.castSucc) i) (u.1 • s) ⊗ₜ[k] (1 : E) : singAlg Q (n + 1) Λ θ ⊗[k] E) :=
    TensorProduct.sum_tmul _ _ _
  rw [cutShuffleIdem, map_sum, cutSpectTmul_sum, Finset.sum_smul, map_sum, singCoord_sum, map_sum,
    hsum]
  refine Eq.trans ?_ Finset.sum_smul.symm
  exact Finset.sum_congr rfl fun s _ => singCoord_concatIdem_of_load Q hQ n Λ θ E M
    (fun z c i => singCoord_load Q hQ n _ _ _ _ z c i) _ y i

/-- An element of `M` as an element of its restriction to the inner stages. -/
def singMToInner (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    M →+ singInnerIn Q n Λ θ E M :=
  AddMonoidHom.id _

/-- An element of the module of the inner stages as an element of the input of the last cut. -/
def singInnerToCut (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (θ : Fin (n + 1) → Multiset I)
    (E : AlgCat.{u} k) (M : ModuleCat.{u} (singAlg Q (n + 1) Λ θ ⊗[k] E)) :
    singInner Q hQ n Λ θ E M →+ singCutIn Q hQ n Λ θ E M :=
  AddMonoidHom.id _

/-- **The admissible coordinate families**: at every stage, the row condition
`E_{i,u} G(i, u) = G(i, u)`. -/
def singAdm : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (singIdx n θ → M) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, Λ, θ, E, M, G =>
    (∀ u, singAdm n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E)
      (singInnerIn Q n Λ θ E M) fun i => singMToInner Q n Λ θ E M (G (i, u))) ∧
    ∀ i u, (singRow Q n Λ θ i u ⊗ₜ[k] (1 : E)) • G (i, u) = G (i, u)

/-- **The standard basis of the standardization with singleton blocks, in stages**: a family
`G : Idx_n → M` is the family of coordinates of an element of `singStd n M` iff it satisfies the
row condition at every stage. -/
theorem mem_range_singCoord_iff : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (θ : Fin n → Multiset I) →
    (E : AlgCat.{u} k) → (M : ModuleCat.{u} (singAlg Q n Λ θ ⊗[k] E)) →
    (G : singIdx n θ → M) →
    (G ∈ Set.range (singCoord Q hQ n Λ θ E M) ↔ singAdm Q n Λ θ E M G)
  | 0, _, _, _, _, G => ⟨fun _ => trivial, fun _ => ⟨G (), funext fun _ => rfl⟩⟩
  | n + 1, Λ, θ, E, M, G => by
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨fun u => (mem_range_singCoord_iff n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _ _ _).1
        ⟨singCutToInner Q hQ n Λ θ E M (singCutCoord Q hQ n Λ θ E M z u), rfl⟩, fun i u => ?_⟩
      have hz := (mem_range_cutSpectCoord_iff (a := n) (r := 1) Q Λ
        (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ (singCutIn Q hQ n Λ θ E M)
        (singCutCoord Q hQ n Λ θ E M z)).1 ⟨z, rfl⟩ u
      rw [singCoord_succ, ← singCoord_cutShuffleIdem]
      exact congrArg (fun y => singInnerToM Q n Λ θ E M (singCoord Q hQ n (Λ ∘ Fin.castSucc)
        (θ ∘ Fin.castSucc) (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M)
        (singCutToInner Q hQ n Λ θ E M y) i)) hz
    · rintro ⟨h1, h2⟩
      choose y hy using fun u =>
        (mem_range_singCoord_iff n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _ _ _).2 (h1 u)
      have hfix : ∀ u, cutSpectTmul (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
          (θ (Fin.last n)) E (cutInputMap (a := n) (r := 1) Q Λ (singWeight n (θ ∘ Fin.castSucc))
            (θ (Fin.last n)) (cutShuffleIdem (a := n) (r := 1) Q Λ
              (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) u)) 1 •
            singInnerToCut Q hQ n Λ θ E M (y u) = singInnerToCut Q hQ n Λ θ E M (y u) :=
        fun u => singCoord_injective Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc) _ _
          (funext fun i => by
            have := singCoord_cutShuffleIdem Q hQ n Λ θ E M u
              (singInnerToCut Q hQ n Λ θ E M (y u)) i
            refine this.trans ?_
            have hyu := congrFun (hy u) i
            change (singRow Q n Λ θ i u ⊗ₜ[k] (1 : E)) •
              singInnerToM Q n Λ θ E M (singCoord Q hQ n (Λ ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
                (singSpect Q n Λ θ E) (singInnerIn Q n Λ θ E M) (y u) i) = _
            rw [hyu]
            exact (h2 i u).trans hyu.symm)
      obtain ⟨z, hz⟩ : ∃ z : (singStd Q hQ (n + 1) Λ θ E).obj M,
          singCutCoord Q hQ n Λ θ E M z = fun u => singInnerToCut Q hQ n Λ θ E M (y u) :=
        (mem_range_cutSpectCoord_iff (a := n) (r := 1) Q Λ
          (singWeight n (θ ∘ Fin.castSucc)) (θ (Fin.last n)) E hQ (singCutIn Q hQ n Λ θ E M)
          fun u => singInnerToCut Q hQ n Λ θ E M (y u)).2 hfix
      refine ⟨z, funext fun ⟨i, u⟩ => ?_⟩
      rw [singCoord_succ, hz]
      exact congrFun (hy u) i

end Stages

end Categorification.Stendhal
