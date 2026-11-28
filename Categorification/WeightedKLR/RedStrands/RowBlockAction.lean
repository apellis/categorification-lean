/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockAction
import Categorification.WeightedKLR.RedStrands.RowQuotientCoordinates

/-!
# The block action on a standard column, for any aligned row

Webster, arXiv:1309.3796v3, §5.1 after Definition 5.4 and §6.1, proof of Lemma 6.9 (v2:
Lemma 6.8). For an aligned row of red blocks whose loadings all have red order `κ`, the
external product of the local violated quotients acts on the column of order `κ` modulo
`blockUpperIdeal a b α κ` by juxtaposition, and the quotient coordinates separate that column.
For a row of singleton blocks and `a = b` the column is a full standard module.

* `rowBlockProductAction`, `rowBlockProductAction_projection`.
* `rowColumn_eq_zero_of_quotient_coordinates`, `exists_rowColumn_coordinate_embedding`.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR KLRAlgebra BraidedStendhalAlgebra

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (Bs : List (RedBlock I ℓ)) (a b : Fin ℓ) (κ : List (Fin ℓ)) {ν : Multiset I}
local notation "α" => fun r i => boundaryCount (cut a b r) i Bs
local notation "J" => blockUpperIdeal k Q Λ ν a b α κ
local notation "V" => ViolQuotient k Q Λ ν
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "p" => violMk k Q Λ ν (redProj k Q Λ ν κ)
variable (h : weightSum Bs = stendhalWeight ℓ ν)

/-- Stack a juxtaposition of the row in the ambient violated quotient. -/
def rowStackBlocks : diagrams Q Λ Bs →ₙₐ[k] V where
  toFun x := π (castKLR (stendhalQ Q Λ) h (juxtapose Q Λ Bs x))
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by simp only [map_smul, MonoidHom.id_apply]
  map_mul' x y := by simp only [juxtapose_mul, map_mul]

local notation "F" => rowStackBlocks Q Λ Bs h

theorem rowStackBlocks_loadingIdem (s : Loadings Bs) :
    F (loadingIdem Q Λ Bs s) = π (e (Seq.cast h (place Bs s))) := by
  change π (castKLR _ h _) = _
  rw [juxtapose_loadingIdem, castKLR_e]

/-- Diagrams with a juxtaposed top and bottom order `κ`, modulo the higher cuts of `κ`. -/
def rowColumn : Submodule k (J).ringCon.Quotient :=
  LinearMap.range ((q).toLinearMap ∘ₗ LinearMap.mulLeft k (F 1) ∘ₗ LinearMap.mulRight k p)

local notation "N" => rowColumn Q Λ Bs a b κ h

private def rowStackEnd (x : diagrams Q Λ Bs) : Module.End k N :=
  (LinearMap.mulLeft k (q (F x))).restrict fun z hz => by
    obtain ⟨v,rfl⟩ := hz
    refine ⟨F x * v, ?_⟩
    change q (F 1 * (F x * v * p)) = q (F x) * q (F 1 * (v * p))
    rw [← map_mul, mul_assoc (F x) v p, ← mul_assoc (F 1) (F x), ← mul_assoc (F x) (F 1),
      ← map_mul, ← map_mul, one_mul, mul_one]

private def rowStackAction : diagrams Q Λ Bs →ₐ[k] Module.End k N where
  toFun := rowStackEnd Q Λ Bs a b κ h
  map_one' := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change q (F 1) * q (F 1 * (v*p)) = q (F 1 * (v*p))
    rw [← map_mul, ← mul_assoc, ← map_mul, one_mul]
  map_zero' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F 0) * z.1 = 0
    rw [map_zero F, map_zero (q), zero_mul]
  map_add' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F (x+y)) * z.1 = q (F x) * z.1 + q (F y) * z.1
    rw [map_add, map_add, add_mul]
  map_mul' x y := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    change q (F (x*y)) * z.1 = q (F x) * (q (F y) * z.1)
    rw [map_mul, map_mul, mul_assoc]
  commutes' c := by
    apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
    change q (F (algebraMap k _ c)) * q (F 1 * (v*p)) = c • q (F 1 * (v*p))
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, smul_mul_assoc, ← map_mul,
      ← mul_assoc, ← map_mul, one_mul]

variable (hal : Aligned a b Bs) (hκ : ∀ s : Loadings Bs, redWord (Seq.cast h (place Bs s)) = κ)

include hal hκ in
private theorem rowStackAction_violated (s : Loadings Bs) (hv : Violated Bs s) :
    rowStackAction Q Λ Bs a b κ h (loadingIdem Q Λ Bs s) = 0 := by
  let t := Seq.cast h (place Bs s)
  have hu := root_lt_of_violated h hal s hv
  apply LinearMap.ext; rintro ⟨_,v,rfl⟩; apply Subtype.ext
  change q (F (loadingIdem Q Λ Bs s)) * q (F 1 * (v*p)) = 0
  rw [rowStackBlocks_loadingIdem, ← map_mul, ← mul_assoc (F 1), ← mul_assoc]
  change (J).ringCon.mk' (π (e t) * (F 1 * v) * p) = 0
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.mul_mem_right _ _ _ (TwoSidedIdeal.mul_mem_right _ _ _
    (TwoSidedIdeal.subset_span ⟨t, hκ s, hu, rfl⟩))

/-- **The action by horizontal juxtaposition, for any aligned row** (Webster,
arXiv:1309.3796v3, proof of Lemma 6.9). A local violation acts by zero on the column. -/
def rowBlockProductAction : quotients Q Λ Bs →ₐ[k] Module.End k N :=
  (exists_factor (C := Module.End k N) Q Λ Bs (rowStackAction Q Λ Bs a b κ h)
    (rowStackAction_violated Q Λ Bs a b κ h hal hκ)).choose

/-- On representatives the action is left multiplication by the juxtaposition. -/
theorem rowBlockProductAction_projection (x : diagrams Q Λ Bs) (z : N) :
    (rowBlockProductAction Q Λ Bs a b κ h hal hκ (projection Q Λ Bs x) z).1 = q (F x) * z.1 := by
  rw [rowBlockProductAction, (exists_factor (C := Module.End k N) Q Λ Bs _
    (rowStackAction_violated Q Λ Bs a b κ h hal hκ)).choose_spec]
  rfl

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "P" => projection Q Λ Bs
local notation "raw" => ofKLR k Q Λ ν
local notation "mk" => violMk k Q Λ ν

include hal hκ in
/-- **The quotient coordinates separate the column** (Webster, arXiv:1309.3796v3, proof of
Lemma 6.9). Reconstruction and the block action show that an element of the column whose
coordinates all vanish is zero. -/
theorem rowColumn_eq_zero_of_quotient_coordinates {n : ℕ}
    (g : Fin n → R →ₗ[k] diagrams Q Λ Bs) (w : Fin n → R)
    (G : Fin n → (J).ringCon.Quotient →ₗ[k] quotients Q Λ Bs)
    (hG : ∀ j y, G j (q (mk (raw y))) = P (g j y))
    (hunit : ∀ j y, g j (rowStack Q Λ Bs h 1 * y) = g j y)
    (rebuild : ∀ y, q (mk (raw (rowStack Q Λ Bs h 1 * y))) =
      ∑ j, q (mk (raw (rowStack Q Λ Bs h (g j y) * w j))))
    (x : N) (hx : ∀ j, G j x.1 = 0) : x = 0 := by
  classical
  let π' := (mk).comp raw
  let eκ : R := redIdem k Q Λ κ
  let S := rowStack Q Λ Bs h
  have surjπ : Function.Surjective π' := violMk_surjective.comp ofKLR_surjective
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨y, rfl⟩ := surjπ v
  let z := y * eκ
  have rep : x.1 = q (π' (S 1 * z)) := by
    change q (F 1 * (π' y * p)) = x.1 at hv
    rw [← hv, map_mul π' (S 1) z, map_mul π' y eκ]
    rfl
  have coeff_zero (j : Fin n) : P (g j z) = 0 := by
    have hc := hx j
    rw [rep] at hc
    change G j (q (mk (raw (S 1 * z)))) = 0 at hc
    rwa [hG, hunit] at hc
  have sum_rep : x.1 = ∑ j, q (F (g j z) * π' (w j)) := by
    calc
      _ = q (π' (S 1 * z)) := rep
      _ = ∑ j, q (π' (S (g j z) * w j)) := rebuild z
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul π']
        rfl
  have right_fixed : x.1 * q p = x.1 := by
    change q (F 1 * (π' y * p)) = x.1 at hv
    have hp : IsIdempotentElem p := (isIdempotentElem_redProj κ).map _
    rw [← hv, ← map_mul (q), mul_assoc, mul_assoc, hp.eq]
  apply Subtype.ext
  change x.1 = 0
  rw [← right_fixed, sum_rep, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  let u : N := ⟨q (F 1 * (π' (w j) * p)), ⟨π' (w j), rfl⟩⟩
  have act := rowBlockProductAction_projection Q Λ Bs a b κ h hal hκ (g j z) u
  have act_zero : rowBlockProductAction Q Λ Bs a b κ h hal hκ (P (g j z)) u = 0 := by
    calc
      _ = rowBlockProductAction Q Λ Bs a b κ h hal hκ 0 u :=
        congrArg (fun v : quotients Q Λ Bs => rowBlockProductAction Q Λ Bs a b κ h hal hκ v u)
          (coeff_zero j)
      _ = 0 := LinearMap.congr_fun (map_zero (rowBlockProductAction Q Λ Bs a b κ h hal hκ)) u
  calc
    _ = q (F (g j z)) * u.1 := by
      change q (F (g j z) * π' (w j)) * q p =
        q (F (g j z)) * q (F 1 * (π' (w j) * p))
      rw [← map_mul (q), ← map_mul (q), mul_assoc _ (π' (w j)) p,
        ← mul_assoc (F (g j z)) (F 1), ← map_mul F, mul_one]
    _ = _ := act.symm
    _ = 0 := congrArg (fun v : N => v.1) act_zero

include hal hκ in
/-- The quotient coordinates embed the column of an aligned row into a finite product of
copies of the block quotients (Webster, arXiv:1309.3796v3, proof of Lemma 6.9). -/
theorem exists_rowColumn_coordinate_embedding (hQ : KLRSymm Q) :
    ∃ n, ∃ Fc : N →ₗ[k] (Fin n → quotients Q Λ Bs), Function.Injective Fc := by
  classical
  obtain ⟨n, _, g, w, G, _, hG, _, _, _, _, _, hunit, _, _, rebuild⟩ :=
    exists_rowStack_quotient_coordinates_with_indexed_projectors Q Λ Bs a b α κ hQ h
      (violated_of_aligned_shuffleLoading Bs a b κ hal h (fun v _ => hκ v))
  let read : N →ₗ[k] (Fin n → quotients Q Λ Bs) :=
    LinearMap.pi fun j => (G j).comp (N).subtype
  refine ⟨n, read, (LinearMap.ker_eq_bot (f := read)).1 (LinearMap.ker_eq_bot'.2 ?_)⟩
  intro x hx
  exact rowColumn_eq_zero_of_quotient_coordinates Q Λ Bs a b κ h hal hκ g w G hG hunit rebuild x
    (fun j => congrFun hx j)

end Categorification.Stendhal.RedBlock
