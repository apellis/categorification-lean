/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizedResolution
import Categorification.WeightedKLR.RedStrands.LastRedStandardCut
import Categorification.Algebra.Graded.UpResolutionHead

/-!
# Simple heads of standard modules in `C↑`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.28 (step for several red strands). The simple module at a cut `θ + β` with factor
class `b` is the head of the standardization `S(b)`: it is a subquotient of `S(b)`
(`exists_headAtCut_isUngradedSubquotient`), and a lift `ε` of the sector idempotent of the cut
acts on `S(b)` with image no larger than on the head (`epsDim_standardization_le`). The other
composition factors of `S(b)` killed by `ε` sit at cuts with fewer black strands before the last
red strand. So, by induction on that number, resolutions in `C↑` of the simple tops of the two
factor algebras give resolutions of the simple tops of `T^λ_ν` (`topsResolvable_of_factors`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra Categorification.Graded DirectSum GProj
open scoped TensorProduct Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)

local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "𝓓" => tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)

/-- The top of a factor class, as a finite graded module. -/
def factorTop (b : IndecClass 𝓓) (hb : FiniteDimensional k b.top) : GFin 𝓓 :=
  { toGMod := b.top
    finiteDimensional := hb }

section Tops

variable {A : Type} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- Every graded simple top over `𝒜` has a graded projective resolution in `C↑`. -/
def TopsResolvable : Prop :=
  ∀ (s : IndecClass 𝒜) (hs : FiniteDimensional k s.top), ∃ c : ℤ,
    Nonempty (GFin.UpResolution ({ toGMod := s.top, finiteDimensional := hs } : GFin 𝒜) c)

end Tops

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
include hR

/-- The head of the standardization of a factor class at its cut is a subquotient of it. -/
theorem exists_headAtCut_isUngradedSubquotient (b : IndecClass 𝓓)
    (hb : FiniteDimensional k b.top) :
    ∃ s, HeadAtCut Λ (θ+β) G ⟨(θ,β),rfl⟩ b s ∧
      GFin.IsUngradedSubquotient T s.top
        (standardizationGFin Λ G θ β hsym (factorTop Λ G θ β b hb)).carrier := by
  obtain ⟨s, hs, X, g, hg, hgq⟩ := exists_headAtCut_subquotient Λ (θ+β) G hR ⟨(θ,β),rfl⟩ b
    (lastRedStandardInducedCut Λ G hsym θ β b)
  refine ⟨s, hs, ⟨{ carrier := (X : Set (lastRedStandardInducedCut Λ G hsym θ β b).carrier)
                    add_mem' := X.add_mem
                    zero_mem' := X.zero_mem
                    smul_mem' := fun t _ hx => X.smul_mem ((smallerSuffixIdeal Q Λ
                      (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)).ringCon.mkₐ k t) hx },
    { toFun := fun x => g ⟨x.1, x.2⟩
      map_add' := fun x y => map_add g ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
      map_smul' := fun t x => hgq t ⟨x.1, x.2⟩ }, fun y => ?_⟩⟩
  obtain ⟨x, rfl⟩ := hg y
  exact ⟨⟨x.1, x.2⟩, rfl⟩

omit hR in
/-- A lift of the sector idempotent of the cut `θ + β` maps `S(b)` into the fixed vectors of the
sector. -/
theorem standardization_smul_mem_idemSubspace (b : IndecClass 𝓓)
    (t : lastRedCutKLR (Q := Q) Λ (θ+β) ⟨(θ,β),rfl⟩)
    (ht : (smallerSuffixIdeal Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)).ringCon.mkₐ k
      (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t) =
      lastRedLayerAction Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.content (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.length (θ+β) ⟨(θ,β),rfl⟩ ℓ) 1)
    (z : (lastRedStandardInducedCut Λ G hsym θ β b).carrier) :
    (smallerSuffixIdeal Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)).ringCon.mkₐ k
        (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t) • z ∈
      idemSubspace k (lastRedStandardInducedCut Λ G hsym θ β b).carrier
        (lastRedLayerAction Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)
          (LastRedWeightSplit.content (θ+β) ⟨(θ,β),rfl⟩ ℓ)
          (LastRedWeightSplit.length (θ+β) ⟨(θ,β),rfl⟩ ℓ) 1) := by
  change _ • (_ • z) = _ • z
  rw [ht, smul_smul, ← map_mul, one_mul]

omit hR in
/-- A lift `ε` of the sector idempotent of the cut acts on `S(b)` with image of dimension at most
that of its image on the head at the cut. -/
theorem epsDim_standardization_le (b : IndecClass 𝓓) (hb : FiniteDimensional k b.top)
    {s : IndecClass (tensorProductGrade G (θ+β))} (hus : HeadAtCut Λ (θ+β) G ⟨(θ,β),rfl⟩ b s)
    (hs : FiniteDimensional k s.top) (t : lastRedCutKLR (Q := Q) Λ (θ+β) ⟨(θ,β),rfl⟩)
    (ht : (smallerSuffixIdeal Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)).ringCon.mkₐ k
      (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t) =
      lastRedLayerAction Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.content (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.length (θ+β) ⟨(θ,β),rfl⟩ ℓ) 1) :
    GFin.epsDim k (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t)
        (standardizationGFin Λ G θ β hsym (factorTop Λ G θ β b hb)) ≤
      GFin.epsDim k (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t)
        ({ toGMod := s.top, finiteDimensional := hs } : GFin (tensorProductGrade G (θ+β))) := by
  let V := lastRedStandardInducedCut Λ G hsym θ β b
  let f := hus.1.some
  let r := V.recover.some.restrictScalars k
  set ε := lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t
  let S := standardizationGFin Λ G θ β hsym (factorTop Λ G θ β b hb)
  let ι : LinearMap.range (GFin.smulLin (k := k) ε S.carrier) →ₗ[k]
      boundaryFixed (lastRedLayerAction Q Λ (LastRedWeightSplit.position (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.content (θ+β) ⟨(θ,β),rfl⟩ ℓ)
        (LastRedWeightSplit.length (θ+β) ⟨(θ,β),rfl⟩ ℓ)) V.carrier :=
    { toFun := fun x => ⟨x.1, by
        obtain ⟨y, hy⟩ := x.2
        rw [← hy]
        exact standardization_smul_mem_idemSubspace Λ G θ β hsym b t ht y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ := LinearMap.codRestrict (LinearMap.range (GFin.smulLin (k := k) ε s.top))
    (f.incl ∘ₗ r.symm.toLinearMap ∘ₗ ι) fun x => ⟨f.incl (r.symm (ι x)), by
      change ε • f.incl (r.symm (ι x)) = f.incl (r.symm (ι x))
      rw [f.intertwines _ 1 ht, one_smul]⟩
  have hφ : Function.Injective φ := fun x y h => by
    have h1 := congrArg Subtype.val h
    have h2 := r.symm.injective (f.injective h1)
    have h3 : (ι x).1 = (ι y).1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  exact LinearMap.finrank_le_finrank_of_injective hφ

/-- **Standardization step of Webster, arXiv:1309.3796v3, proof of Theorem 5.28.** For
Rouquier parameters and nonnegative dot degrees, if the simple tops over the tensor product
algebras with the first `ℓ` red strands and over the cyclotomic KLR algebras of the last red
strand have resolutions in `C↑`, then so do the simple tops over `T^λ_ν`. A simple `L` is the
head at its cut `θ + β` of the standardization `S(b)` of a factor simple, which has a resolution;
the other composition factors of `S(b)` killed by the sector idempotent lie at cuts with fewer
black strands before the last red strand. -/
theorem topsResolvable_of_factors (hG : ∀ a, 0 ≤ G.degX a)
    (h₁ : ∀ θ : Multiset I, TopsResolvable (tensorProductGrade (restrictRedGrading Q Λ G) θ))
    (h₂ : ∀ β : Multiset I,
      TopsResolvable (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))
    (ν : Multiset I) : TopsResolvable (tensorProductGrade G ν) := by
  have hsym := hR.klrSymm
  have induce := nonempty_lastRedInducedCut Λ ν G hsym
  suffices key : ∀ (n : ℕ) (u : LastRedWeightSplit ν)
      (b : IndecClass (lastRedFactorGrading Λ ν G u))
      (s : IndecClass (tensorProductGrade G ν)), Multiset.card u.1.1 = n → HeadAtCut Λ ν G u b s →
      ∀ hs : FiniteDimensional k s.top, ∃ c : ℤ, Nonempty (GFin.UpResolution
        ({ toGMod := s.top, finiteDimensional := hs } : GFin (tensorProductGrade G ν)) c) by
    intro s hs
    obtain ⟨⟨u, x⟩, rfl⟩ := (lastRedHeadEquiv Λ ν G hR induce).surjective s
    exact key _ u _ _ rfl (lastRedHeadEquiv_headAtCut Λ ν G hR induce u x) hs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u b s hn hus hs
  rcases u with ⟨⟨θ, β⟩, hu⟩
  subst hu
  have := tensorProductAlgebra_finite Λ (θ+β) hR
  let := HasGdim.of_finiteDimensional (tensorProductGrade G (θ+β))
  -- The factor simple `b` and the resolution of its standardization.
  have H := lastRedLayerSource_tensorK0Hyp hR (Λ ∘ Fin.castSucc) θ (Λ (Fin.last ℓ)) β
    (restrictRedGrading Q Λ G) (restrictBlackGrading Q Λ G)
  have hb : FiniteDimensional k b.top := H.fdC b
  have := tensorProductAlgebra_finite (Λ ∘ Fin.castSucc) θ hR
  have := lastRedFinal_finite hR (Λ (Fin.last ℓ)) β
  let := HasGdim.of_finiteDimensional (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  let := HasGdim.of_finiteDimensional
    (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)
  obtain ⟨c₁, ⟨R₁⟩⟩ := h₁ θ (H.fst b) (H.fdA _)
  obtain ⟨c₂, ⟨R₂⟩⟩ := h₂ β (H.snd b) (H.fdB _)
  obtain ⟨e⟩ := H.top_iso b
  have Rb : GFin.UpResolution (factorTop Λ G θ β b hb) (c₁ + c₂ - H.shift b) :=
    ((R₁.extTensor R₂).shift (H.shift b)).congr e.symm
  obtain ⟨C₀, hC₀⟩ := exists_upResolution_standardizationGFin Λ G θ β hsym hR hG
  obtain ⟨RS⟩ := hC₀ _ _ Rb
  -- The head lemma at the sector idempotent of the cut.
  obtain ⟨t₀, ht₀⟩ := lastRedCutConcat_exists_lift (Q := Q) Λ (θ+β) ⟨(θ,β),rfl⟩
  obtain ⟨s₀, hs₀, hsub⟩ := exists_headAtCut_isUngradedSubquotient Λ G θ β hsym hR b hb
  have hss : s₀ = s := (lastRedHeadEquiv_of_headAtCut Λ (θ+β) G hR induce hs₀).symm.trans
    (lastRedHeadEquiv_of_headAtCut Λ (θ+β) G hR induce hus)
  subst hss
  refine GFin.exists_upResolution_of_head (lastRedCutConcat Λ (θ+β) ⟨(θ,β),rfl⟩ t₀) _
    (IndecClass.isGradedSimple_top s₀)
    (HeadAtCut.exists_smul_ne_zero Λ (θ+β) G hus t₀ ht₀) _ hsub
    (epsDim_standardization_le Λ G θ β hsym b hb hus hs t₀ ht₀) ⟨_, ⟨RS⟩⟩ ?_
  -- Lower strata.
  intro L' hL' hL'S hε
  obtain ⟨s', a, ⟨e'⟩⟩ := IndecClass.exists_gradedEquiv_top_shift hL'
  obtain ⟨⟨v, x'⟩, hv⟩ := (lastRedHeadEquiv Λ (θ+β) G hR induce).surjective s'
  have hv' := lastRedHeadEquiv_headAtCut Λ (θ+β) G hR induce v x'
  rw [hv] at hv'
  -- An element killing `L'` kills the top of `s'`.
  have hkill : ∀ c : TensorProductAlgebra k Q Λ (θ+β), (∀ y : L'.carrier, c • y = 0) →
      ∀ z : s'.top, c • z = 0 :=
    fun c hc z => by
      have h0 := hc (e'.toLinearEquiv.symm z)
      rw [← map_smul, LinearEquiv.map_eq_zero_iff] at h0
      exact h0
  have hle : v.1.1 ≤ θ := by
    by_contra hnot
    obtain ⟨t, ht⟩ := lastRedCutConcat_exists_lift (Q := Q) Λ (θ+β) v
    obtain ⟨z, hz⟩ := HeadAtCut.exists_smul_ne_zero Λ (θ+β) G hv' t ht
    have hS : ∀ y : (standardizationGFin Λ G θ β hsym (factorTop Λ G θ β b hb)).carrier,
        lastRedCutConcat Λ (θ+β) v t • y = 0 := fun y =>
      LinearMap.congr_fun (parabolicStandardAction_other_concat_eq_zero Q Λ θ β b.top hsym
        v.1.1 v.1.2 v.2 hnot t) y
    exact hz (hkill _ (GFin.smul_eq_zero_of_isSubquotient hL'S hS) z)
  have hne : v.1.1 ≠ θ := by
    intro heq
    have hv0 : v = ⟨(θ,β),rfl⟩ := Subtype.ext (Prod.ext heq
      (add_left_cancel (show θ + v.1.2 = θ + β by have h := v.2; rwa [heq] at h)))
    subst hv0
    obtain ⟨z, hz⟩ := HeadAtCut.exists_smul_ne_zero Λ (θ+β) G hv' t₀ ht₀
    exact hz (hkill _ hε z)
  have hlt : Multiset.card v.1.1 < n := hn ▸ Multiset.card_lt_card (lt_of_le_of_ne hle hne)
  have hs' : FiniteDimensional k s'.top :=
    Module.Finite.trans (TensorProductAlgebra k Q Λ (θ+β)) s'.top
  obtain ⟨c', ⟨R'⟩⟩ := ih _ hlt v _ s' rfl hv' hs'
  exact ⟨_, ⟨(R'.shift a).congr e'.symm⟩⟩

section Induction

omit hR in
/-- With no black strands, `T^λ_0 ≅ k`, so every module is projective and every simple top has
a resolution in `C↑`. -/
theorem topsResolvable_vacuum {n : ℕ} {Λ' : Fin n → I →₀ ℕ} (G' : GradingDatum (stendhalQ Q Λ')) :
    TopsResolvable (tensorProductGrade G' 0) := by
  intro s hs
  have : IsSemisimpleRing (TensorProductAlgebra k Q Λ' 0) :=
    (tensorProductAlgebraZeroEquiv Q Λ').symm.toRingEquiv.isSemisimpleRing
  have := Module.projective_of_isSemisimpleRing (TensorProductAlgebra k Q Λ' 0) s.top
  obtain ⟨L, U, hLU⟩ := exists_bounds (ℳ := s.top.grading)
  exact ⟨_, ⟨GFin.UpResolution.ofProjective _ (m := L) fun j hj => hLU j (Or.inl hj)⟩⟩

omit hR in
/-- With no red strands and a nonzero black weight the algebra is zero, so there are no simple
tops. -/
theorem topsResolvable_noRed (G' : GradingDatum (stendhalQ Q (Fin.elim0 : Fin 0 → I →₀ ℕ)))
    {ν : Multiset I} (hν : ν ≠ 0) : TopsResolvable (tensorProductGrade G' ν) := by
  intro s _
  have := subsingleton_emptyTensorAlgebra Q hν
  have : Subsingleton s.top := Module.subsingleton (TensorProductAlgebra k Q Fin.elim0 ν) _
  exact absurd (IndecClass.isGradedSimple_top s).nontrivial (not_nontrivial _)

/-- **Webster, arXiv:1309.3796v3, Theorem 5.28, reduced to one red strand.** For Rouquier
parameters and nonnegative dot degrees, if the graded simple modules over every cyclotomic KLR
algebra `R^μ_β` (one red strand) have resolutions in `C↑`, then so do the graded simple modules
over every tensor product algebra `T^λ_ν`. The hypothesis is the one-red-strand case of
Theorem 5.28, whose printed proof has a gap (see the roadmap); it is tracked for removal. -/
theorem topsResolvable_of_cyclotomic
    (hcyc : ∀ (G' : GradingDatum Q), (∀ i, 0 ≤ G'.degX i) → ∀ (μ : I → ℕ) (β : Multiset I),
      TopsResolvable (CycKLR.grade G' μ β)) :
    ∀ (n : ℕ) (Λ' : Fin n → I →₀ ℕ) (G' : GradingDatum (stendhalQ Q Λ')),
      (∀ a, 0 ≤ G'.degX a) → ∀ ν : Multiset I, TopsResolvable (tensorProductGrade G' ν) := by
  intro n
  induction n with
  | zero =>
    intro Λ' G' _ ν
    obtain rfl : Λ' = Fin.elim0 := funext fun i => i.elim0
    by_cases hν : ν = 0
    · subst hν
      exact topsResolvable_vacuum G'
    · exact topsResolvable_noRed G' hν
  | succ n ih =>
    intro Λ' G' hG' ν
    exact topsResolvable_of_factors Λ' G' hR hG'
      (fun θ => ih _ _ (fun _ => hG' _) θ)
      (fun β => hcyc _ (fun _ => hG' _) _ β) ν

end Induction

end Categorification.Stendhal
