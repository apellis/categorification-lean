/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingWords
import Categorification.WeightedKLR.RedStrands.BlockCrossingCut

/-!
# Cutting a global braided diagram before the standard quotient

Webster, arXiv:1309.3796v2, §6.1, ordinary comparison in the proof of Lemma 6.8.
At each top loading use Proposition 6.4 with reduced words whose upper factor lies in the
juxtaposed block algebras. Cutting the resulting basis vectors and extending linearly gives
a map out of the braided Stendhal algebra itself, not just out of marked diagrams. Stacking
recovers the projection to the exchanged-top standard column. This identity alone does not
descend the cut through the global violated and higher-loading ideals.
-/
noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra TypeA Equiv BraidedStendhalAlgebra MvPolynomial
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (hQ : KLRSymm Q)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
local notation "Bs" => adjacentRow L M f β
local notation "κ₀" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "Braid" => BraidedStendhalAlgebra k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "F" => stackBlocks Q Λ L M f β h
local notation "botOrd" => (fun (_ : RedBlock I ℓ) => 1)
local notation "topOrd" => (fun (_ : RedBlock I ℓ) => Fin.revPerm)
local notation "D₀" => orderedProduct Q Λ botOrd Bs
local notation "D₁" => orderedProduct Q Λ topOrd Bs
local notation "S₀" => orderedColumn Q Λ hQ botOrd L M f β h
local notation "S₁" => orderedColumn Q Λ hQ topOrd L M f β h
local notation "C" => crossingProduct Q Λ hQ M f β L
local notation "Z" => BalancedTensor k D₁ D₀ (BlockCut.space C) S₀
local notation "E₀" => orderedIdem Q Λ botOrd Bs
local notation "rep" => orderedColumnRep Q Λ hQ L M f β h topOrd
local notation "stk" => crossingStack Q Λ hQ L M f β h
local notation "p" => redIdem k Q Λ (ν := ν) κ₀
local notation "mk" => violMk k Q Λ ν
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1)
  (fun r i => boundaryCount (cut (f 0) (f 1) r) i Bs) κ₀
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)

private theorem topWords (s : Loadings Bs) (w : Perm (Fin m)) :
    let t := Seq.cast h (place Bs s)
    ∃ A D, (IsReduced m (A ++ D) ∧ wordProd m (A ++ D) = w) ∧
      (redWord (w⁻¹ • t) = κ₀ → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧ F x = π (e t * ψw A)) := by
  intro t
  by_cases ho : redWord (w⁻¹ • t) = κ₀
  · obtain ⟨A,D,hw,hx⟩ := exists_reduced_crossing_cut Q Λ L M f β h s (w⁻¹ • t) ho w
    exact ⟨A,D,hw,fun _ => hx (smul_inv_smul w t)⟩
  · exact ⟨[],canWord m w,⟨isReduced_canWord _ _,wordProd_canWord _ _⟩,fun hh => (ho hh).elim⟩

private theorem sandwich_std (i t : Seq μ) (A : List ℕ) (d : Fin m →₀ ℕ) :
    let z : R := ψw A * pol (monomial d 1) * e i
    e t * z * p = if (wordProd m A)⁻¹ • t = i ∧ redWord i = κ₀ then z else 0 := by
  dsimp only
  rw [e_mul_gen]
  split_ifs <;> simp_all [mul_assoc,e_mul_redIdem]

private def cutGenerator (t j : Seq μ) (w : Perm (Fin m)) (d : Fin m →₀ ℕ) (A D : List ℕ)
    (hx : redWord (w⁻¹ • t) = κ₀ → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧ F x = π (e t * ψw A)) : Z :=
  if hb : w⁻¹ • t = j ∧ redWord j = κ₀ then
    crossingCut Q Λ hQ L M f β h ((hx (hb.1 ▸ hb.2)).choose ⊗ₜ π (ψw D * pol (monomial d 1) * e j))
  else 0

private theorem stack_generator (t j : Seq μ) (w : Perm (Fin m)) (d : Fin m →₀ ℕ) (A D : List ℕ)
    (hw : wordProd m (A ++ D) = w)
    (hx : redWord (w⁻¹ • t) = κ₀ → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧ F x = π (e t * ψw A)) :
    stk (cutGenerator Q Λ hQ L M f β h t j w d A D hx) =
      rep (π (e t * (ψw (A ++ D) * pol (monomial d 1) * e j) * p)) := by
  rw [sandwich_std,hw,cutGenerator]
  split_ifs with hb
  · obtain ⟨hx₀,hX⟩ := (hx (hb.1 ▸ hb.2)).choose_spec
    rw [crossingStack_cut, ← map_mul F, hx₀, hX, ← map_mul]
    apply congrArg (fun z : R => rep (π z))
    have H := e_mul_gen (Q := stendhalQ Q Λ) t (A ++ D) (monomial d 1) j
    rw [hw, ite_eq_left hb.1] at H
    simpa only [ψw_append, mul_assoc] using H
  · exact (map_zero stk).trans (((congrArg rep (map_zero π)).trans (map_zero rep)).symm)

private theorem cutGenerator_bottom_zero (t j : Seq μ) (w : Perm (Fin m)) (d : Fin m →₀ ℕ) (A D : List ℕ)
    (hx : redWord (w⁻¹ • t) = κ₀ → ∃ x : diagrams Q Λ Bs, x * E₀ = x ∧ F x = π (e t * ψw A))
    (hj : q (π (e j)) = 0) : cutGenerator Q Λ hQ L M f β h t j w d A D hx = 0 := by
  unfold cutGenerator; split_ifs with hb
  · let v : R := ψw D * pol (monomial d 1)
    have H : orderedColumnRep Q Λ hQ L M f β h botOrd (π (v * e j)) = 0 := by
      apply Subtype.ext; apply Subtype.ext
      rw [orderedColumnRep_val]
      change q (F E₀ * (π (v * e j) * π p)) = 0
      rw [map_mul π, map_mul (q), map_mul (q), map_mul (q), hj, mul_zero, zero_mul, mul_zero]
    rw [crossingCut_tmul, H, BalancedTensor.tmul_zero]
  · rfl

private def loadingCut (s : Loadings Bs) : {g : Braid →ₗ[k] Z //
    (∀ y, stk (g y) = rep (F (loadingIdem Q Λ Bs s) * (mk y * π p))) ∧
    ∀ i : Seq μ, q (π (e i)) = 0 → ∀ y, g (y * ofKLR k Q Λ ν (e i)) = 0} := by
  classical
  let t := Seq.cast h (place Bs s)
  choose A D hw hx using topWords Q Λ L M f β h s
  let ρ := fun w => A w ++ D w
  let basis' := BraidedStendhalAlgebra.basis (Λ := Λ) hQ ρ hw
  let gen (b : BlackIdx (ℓ := ℓ) ν) : Z := cutGenerator Q Λ hQ L M f β h t b.1.1 b.1.2.1
    b.1.2.2 (A b.1.2.1) (D b.1.2.1) (hx b.1.2.1)
  let g := basis'.constr k gen
  let P : Braid →ₗ[k] S₁ := (rep).comp ((LinearMap.mulLeft k (F (loadingIdem Q Λ Bs s))).comp
    ((LinearMap.mulRight k (π p)).comp (mk).toLinearMap))
  refine ⟨g,?_,?_⟩
  swap
  · intro i hi y
    apply LinearMap.congr_fun (g := (0 : Braid →ₗ[k] Z)) (f := g.comp (LinearMap.mulRight k (ofKLR k Q Λ ν (e i)))) _ y
    apply basis'.ext; intro b
    change g (basis' b * ofKLR k Q Λ ν (e i)) = 0
    have mul_basis : basis' b * ofKLR k Q Λ ν (e i) = if b.1.1 = i then basis' b else 0 := by
      rw [show basis' b = _ from BraidedStendhalAlgebra.basis_apply hQ ρ hw b, ← map_mul, gen_mul_e]
      split_ifs <;> first | rfl | exact map_zero _
    rw [mul_basis]; split_ifs with hj
    · rw [show g (basis' b) = gen b from Module.Basis.constr_basis basis' k gen b]
      exact cutGenerator_bottom_zero Q Λ hQ L M f β h _ _ _ _ _ _ _ (hj ▸ hi)
    · exact map_zero g
  intro y
  apply LinearMap.congr_fun (g := P) (f := (LinearMap.restrictScalars k stk).comp g) _ y
  apply basis'.ext
  intro b
  let j := b.1.1
  let w := b.1.2.1
  let d := b.1.2.2
  change stk (g (basis' b)) = rep (F (loadingIdem Q Λ Bs s) * (mk (basis' b) * π p))
  rw [show g (basis' b) = gen b from Module.Basis.constr_basis basis' k gen b, stackBlocks_loadingIdem,
    show basis' b = _ from BraidedStendhalAlgebra.basis_apply hQ ρ hw b]
  change _ = rep (π (e t) * (π (ψw (ρ w) * pol (monomial d 1) * e j) * π p))
  rw [← map_mul, ← map_mul, ← mul_assoc]
  exact stack_generator Q Λ hQ L M f β h t j w d (A w) (D w) (hw w).2 (hx w)

/-- Sum over the tuples of local loadings, including the scalar empty product. -/
private def sumAt {E : Type*} [AddCommMonoid E] : (row : List (RedBlock I ℓ)) → (Loadings row → E) → E
  | [], g => g PUnit.unit
  | B :: row, g => ∑ s : Seq B.localWeight, sumAt row (fun u => g (s,u))

omit [DecidableEq I] in
private theorem map_sumAt {E E' : Type*} [AddCommMonoid E] [AddCommMonoid E'] (a : E →+ E') :
    ∀ (row : List (RedBlock I ℓ)) (g : Loadings row → E), a (sumAt row g) = sumAt row (fun s => a (g s))
  | [], _ => rfl
  | _ :: row, g => by simp only [sumAt, map_sum, map_sumAt a row]

private theorem sumAt_idem {E : Type*} [AddCommMonoid E] [Module k E] : ∀ (row : List (RedBlock I ℓ))
    (g : diagrams Q Λ row →ₗ[k] E), sumAt row (fun s => g (loadingIdem Q Λ row s)) = g 1
  | [], _ => rfl
  | B :: row, g => by
    let l s := ofKLR k Q (Λ ∘ B.label) B.black (e s)
    have step (s : Seq B.localWeight) := sumAt_idem row (g.comp (TensorProduct.mk k _ _ (l s)))
    have hs : ∑ s, l s = 1 := by dsimp [l]; rw [← map_sum,sum_e,map_one]
    change (∑ s, sumAt row (fun u => g (l s ⊗ₜ loadingIdem Q Λ row u))) = _
    simp only [LinearMap.comp_apply,TensorProduct.mk_apply] at step
    simp_rw [step]
    rw [← map_sum, ← TensorProduct.sum_tmul, hs]; rfl

/-- Cut a global braided diagram by expanding in the adapted, red-dot-free basis of Prop. 6.4
at each top loading. The input is *before* the violated and partial-standard relations. -/
def crossingDiagramCut : Braid →ₗ[k] Z := sumAt Bs fun s => (loadingCut Q Λ hQ L M f β h s).1

/-- **Stack after cutting an unmarked representative** (Webster, proof of Lemma 6.8).
On the global braided algebra the composite is the projection onto the exchanged-top
standard column, including the violated and higher relations. -/
theorem crossingStack_diagramCut (y : Braid) : stk (crossingDiagramCut Q Λ hQ L M f β h y) = rep (mk y) := by
  let ev : (Braid →ₗ[k] Z) →+ S₁ := (LinearMap.restrictScalars k stk).toAddMonoidHom.comp
    (LinearMap.applyₗ (M₂ := Z) y).toAddMonoidHom
  change ev (sumAt Bs _) = _
  rw [map_sumAt]
  change sumAt Bs (fun s => stk ((loadingCut Q Λ hQ L M f β h s).1 y)) = _
  simp_rw [(loadingCut Q Λ hQ L M f β h _).2.1]
  let g := (rep).comp ((LinearMap.mulRight k (mk y * π p)).comp (LinearMap.ofClass F))
  change sumAt Bs (fun s => g (loadingIdem Q Λ Bs s)) = _
  rw [sumAt_idem]
  apply Subtype.ext; apply Subtype.ext
  change (rep (F 1 * (mk y * π p))).1.1 = _
  rw [orderedColumnRep_val, orderedColumnRep_val]
  have hp : π p * π p = π p := bottomIdempotent Q Λ L M f
  have H (u : diagrams Q Λ Bs) : F u * ((F 1 * (mk y * π p)) * π p) = F u * (mk y * π p) := by
    rw [mul_assoc (F 1), mul_assoc (mk y), hp, ← mul_assoc, ← map_mul, mul_one]
  exact congrArg _ (H _)

/-- **Surjectivity of ordinary stacking** (Webster, arXiv:1309.3796v2, proof of Lemma 6.8).
Every exchanged-top column class is obtained by cutting a braided representative. -/
theorem crossingStack_surjective : Function.Surjective stk := by
  intro z
  obtain ⟨v,rfl⟩ := orderedColumnRep_surjective Q Λ hQ L M f β h topOrd z
  obtain ⟨y,rfl⟩ := violMk_surjective v
  exact ⟨crossingDiagramCut Q Λ hQ L M f β h y, crossingStack_diagramCut Q Λ hQ L M f β h y⟩

/-- A violated or higher idempotent at the *bottom endpoint* is killed by the cut itself,
not merely by restacking it. This does not put the idempotent at an arbitrary interior height. -/
theorem crossingDiagramCut_mul_loading (i : Seq μ) (hi : q (π (e i)) = 0) (y : Braid) :
    crossingDiagramCut Q Λ hQ L M f β h (y * ofKLR k Q Λ ν (e i)) = 0 := by
  let ev := (LinearMap.applyₗ (M₂ := Z) (y * ofKLR k Q Λ ν (e i)) : (Braid →ₗ[k] Z) →ₗ[k] Z).toAddMonoidHom
  change ev (sumAt Bs _) = 0
  rw [map_sumAt]
  change sumAt Bs (fun s => (loadingCut Q Λ hQ L M f β h s).1 _) = 0
  simp_rw [(loadingCut Q Λ hQ L M f β h _).2.2 i hi]
  exact sumAt_idem Q Λ Bs (0 : diagrams Q Λ Bs →ₗ[k] Z)

end Categorification.Stendhal.RedBlock
