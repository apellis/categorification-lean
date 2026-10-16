/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumCorner
import Categorification.TwoRep.FurledEvaluation
import Categorification.KLR.Unfurling.Nondeg

/-!
# Semilinear evaluation on the cyclotomic vacuum

Supporting Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of Theorem `nondegenerate`, “Triviality of a relation”. The map `theta` evaluates
positive-word morphisms at an object of the furled family, includes the chosen input
lift, projects onto all output lifts, and reads their cyclotomic vacuum coordinates.
The output is the actual unfurled cyclotomic quotient, with scalar extension explicit.

`theta_toUEnd` proves its KLR component on every element, using `lgen`, `lproj`,
`wgen`, `wcoord` and the completed action under `gamma`. The explicit weight and object
equalities connect a block of the furled family to the product vacuum. The formula does
not assume a basis-image equation. `theta_toUEnd_basis` specializes this to the KLR basis.
`unfurledEvalOfVacuum` constructs the consumer structure and proves `map_basis` from the
categorical bubble scalar equation on the vacuum and scalar algebraic independence.
Specializing the displayed weight/object equalities and bubble equation to the generic
KL family remains separate; the final nondegeneracy theorem is not asserted here.
-/

noncomputable section
namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits QuantumGroup UDot TwoRep TwoRep.RouqFamily KLRAlgebra Unfurling

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

variable {I₂ : Type u} [DecidableEq I₂] {C₂ : CartanDatum I₂} {X₂ Y₂ : Type u₁}
  [AddCommGroup X₂] [AddCommGroup Y₂] {RD₂ : WeightDatum C₂ X₂ Y₂}
  {T : RouqFamily (B := LinearCat.{v, max (max u v) w, max (max u v) w + 1} k) RD₂}
  {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k} (H₂ : RouqUpKLR T Q₂) (hQ₂ : KLRSymm Q₂)
  {μ : X} (μ₂ : X₂) (V₀ : weightSpace.{u, v, w} Q a RD Λ μ)
  (h0 : blockWeight RD Λ 0 = μ) (v₀ : V₀ ⟨0, h0⟩)
  {Ψ₀ : V₀ ⟨0, h0⟩ →ₗ[CycKLR k Q a 0] CycKLR k Q a 0} (hΨ₀ : Ψ₀ v₀ = 1)
  (V : (homProduct k (S) T).obj (μ, μ₂)) (z : (T.obj (-μ₂) : Type _))
  (hz : V.obj.obj z = familyObj hQ hlead ha hΛ hdeg V₀) {ν : Multiset I}
  (M : ℕ)
  (haM : ∀ i ∈ ν, a i = Polynomial.X ^ M)


variable {I₀ : Type*} {P : I₀ → I₀ → MvPolynomial (Fin 2) k}
  (D : UnfurlingDatum k P (I ⊕ I₂))
  (hprodD : prodQ Q Q₂ = unfQ (k := k) D.arrows)

private def weightCoord {A B : weightSpace Q a RD Λ μ} (b : WeightBlocks RD Λ μ)
    (v : A b) (q : B b →ₗ[CycKLR k Q a b.1] CycKLR k Q a b.1) :
    (A ⟶ B) →ₗ[k] CycKLR k Q a b.1 where
  toFun f := q ((f b).hom v)
  map_add' f g := by
    change q ((f b).hom v + (g b).hom v) = _
    exact map_add q _ _
  map_smul' c f := by
    change q (algebraMap k (CycKLR k Q a b.1) c • (f b).hom v) = c • q ((f b).hom v)
    rw [map_smul, smul_eq_mul, Algebra.smul_def]

private theorem whisker_add {A : Type*} [Category A] [Preadditive A]
    {a b c d : A} (p : a ⟶ b) (q : c ⟶ d) (f g : b ⟶ c) :
    p ≫ (f + g) ≫ q = p ≫ f ≫ q + p ≫ g ≫ q := by
  simp only [Preadditive.add_comp, Preadditive.comp_add]

private theorem whisker_smul {A : Type*} [Category A] [Preadditive A] [Linear k A]
    {a b c d : A} (p : a ⟶ b) (q : c ⟶ d) (r : k) (f : b ⟶ c) :
    p ≫ (r • f) ≫ q = r • (p ≫ f ≫ q) := by
  simp only [Linear.smul_comp, Linear.comp_smul]

/-- Read the coordinate of a morphism on the generator of the product vacuum word. -/
def vacuumCoord (t s : Seq ν) :
    (((homProduct k (S) T).wordCellAt (μ, μ₂) (wtop RD μ ν, μ₂)
      (wtop_map_inl μ μ₂ ν) (Seq.map Sum.inl t)).obj.obj V ⟶
     ((homProduct k (S) T).wordCellAt (μ, μ₂) (wtop RD μ ν, μ₂)
      (wtop_map_inl μ μ₂ ν) (Seq.map Sum.inl s)).obj.obj V) →ₗ[k] UnfCyc D (ν.map Sum.inl) M := by
  let A : weightSpace Q a RD Λ (wtop RD μ ν) :=
    ((S).wordCell μ t).obj.obj (familyObj hQ hlead ha hΛ hdeg V₀)
  let B : weightSpace Q a RD Λ (wtop RD μ ν) :=
    ((S).wordCell μ s).obj.obj (familyObj hQ hlead ha hΛ hdeg V₀)
  let F : (((homProduct k (S) T).wordCellAt (μ, μ₂) (wtop RD μ ν, μ₂)
      (wtop_map_inl μ μ₂ ν) (Seq.map Sum.inl t)).obj.obj V ⟶
     ((homProduct k (S) T).wordCellAt (μ, μ₂) (wtop RD μ ν, μ₂)
      (wtop_map_inl μ μ₂ ν) (Seq.map Sum.inl s)).obj.obj V) →ₗ[k] (A ⟶ B) :=
    { toFun f := eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz t).symm ≫
          f.hom.app z ≫
          eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz s)
      map_add' f g := whisker_add _ _ (f.hom.app z) (g.hom.app z)
      map_smul' c f := whisker_smul _ _ c (f.hom.app z) }
  exact (CycKLR.relabelEquiv (inlRelabel hprodD) (inlRelabel_cyc hprodD M haM)).toLinearMap.comp
    ((weightCoord (A := A) (B := B) (topBlk h0) (wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ t)
      (wcoord hQ hlead ha hΛ hdeg V₀ h0 Ψ₀ s)).comp F)

include H₂ hQ₂ hΨ₀ in
/-- Completed cover action is read by the cyclotomic strand-reversal map. -/
theorem vacuumCoord_klrComplAt
    (H : RouqUpKLR (homProduct k (S) T) (unfQ (k := k) D.arrows))
    (hnil : ∀ (c : I ⊕ I₂) {x y : X × X₂} (h : x + (RD.prod RD₂).iX c = y),
      IsNilpotent (End.of ((homProduct k (S) T).dot c h)))
    (harr : ∀ a ∈ ν.map Sum.inl, ∀ b ∈ ν.map Sum.inl, D.arrows a b = 0)
    (hnd : (ν.map (Sum.inl (β := I₂))).Nodup)
    (f : UnfCompl D (ν.map Sum.inl)) (t s : Seq ν) :
    vacuumCoord hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD t s
      (((klrComplAt H (μ, μ₂) (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν) hnil
          (unfGrading (k := k) D.arrows) f) (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V) =
      cycFlip D harr hnd M (cycMk D _ M (e (Seq.map Sum.inl s)) * cycLift D harr hnd M f *
        cycMk D _ M (e (Seq.map Sum.inl t))) :=
  relabel_wcoord_klrComplAt_inl_wgen hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz
    M haM D hprodD H hnil harr hnd f t s

universe u₀
section Furled
open KLR.Diagram KL3.Diagram
variable [DecidableEq I₀] {C₀ : CartanDatum I₀}
  {X₀ Y₀ : Type u₀} [AddCommGroup X₀] [AddCommGroup Y₀]
  {RD₀ : WeightDatum C₀ X₀ Y₀} (Φ : Furling (RD.prod RD₂) RD₀)
  (hπ : ∀ i, Φ.π i = D.π i)
  [∀ x, HasFiniteBiproducts (((homProduct k (S) T).obj x) : Type _)]
  {μg : X₀} (Vg : ∀ β : Φ.Blk μg, Furling.blkCat Φ (homProduct k (S) T) β.1)
  (β : Φ.Blk μg)
  (δ : Φ.Blk (wtop RD₀ μg ((ν.map Sum.inl).map D.π)))
  (hδ : β.1 + Furling.blkSum (ν.map Sum.inl) = δ.1)
  (hx : Φ.wtT β.1 = (μ, μ₂)) (hy : Φ.wtT δ.1 = (wtop RD μ ν, μ₂))
  (hV : hx ▸ Vg β = V)
  (G : RouqFamily (B := LinearCat.{v, max (max u v) w + 1, max (max u v) w + 1} k) RD₀)
  (hG : G.toRouqData = Furling.rouqData Φ (homProduct k (S) T) D)
  (HG : RouqUpKLR G (klQ2 k C₀)) (MG : BrundanMixedInversion G)
  {k₀ : Type*} [Field k₀] [Algebra k₀ k]

/-- The vacuum coordinate of a single output lift of a positive-word morphism. -/
def thetaEntry (t s : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π)) :
    ((pres RD₀ k₀).obj (ob RD₀ μg (ups (word (down D.π rfl (Seq.map Sum.inl t))))) ⟶
      (pres RD₀ k₀).obj (ob RD₀ μg (ups (word j)))) →ₛₗ[algebraMap k₀ k]
        UnfCyc D (ν.map Sum.inl) M :=
  (vacuumCoord hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD t s).comp
    ((wordHomTransport (homProduct k (S) T) hx hy
      (Furling.wtop_lift μg δ β ⟨ν.map Sum.inl, rfl⟩ hδ) (wtop_map_inl μ μ₂ ν)
      (Vg β) V hV (Seq.map Sum.inl t) (Seq.map Sum.inl s)).toLinearMap.comp
      (Furling.upCorner hπ Vg δ β ⟨ν.map Sum.inl, rfl⟩ hδ G hG HG MG
        (Seq.map Sum.inl t) (Seq.map Sum.inl s) j))

/-- Semilinear evaluation at the vacuum, summing the coordinates of the output lifts. -/
def theta (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π)) :
    ((pres RD₀ k₀).obj (ob RD₀ μg (ups (word (down D.π rfl (Seq.map Sum.inl t))))) ⟶
      (pres RD₀ k₀).obj (ob RD₀ μg (ups (word j)))) →ₛₗ[algebraMap k₀ k]
        UnfCyc D (ν.map Sum.inl) M := by
  classical
  exact ∑ s : {s : Seq ν // down D.π rfl (Seq.map Sum.inl s) = j},
    thetaEntry hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t s.1 j

/-- A scalar input endomorphism factors out of the sum of all vacuum coordinates. -/
theorem theta_comp_of_scalar (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π))
    (b : End ((pres RD₀ k₀).obj (ob RD₀ μg (ups (word (down D.π rfl (Seq.map Sum.inl t)))))))
    (f : (pres RD₀ k₀).obj (ob RD₀ μg (ups (word (down D.π rfl (Seq.map Sum.inl t))))) ⟶
      (pres RD₀ k₀).obj (ob RD₀ μg (ups (word j)))) (c : k)
    (hb : (Furling.evalBlk Φ (homProduct k (S) T) Vg δ).map
      (G.upEvalData HG MG (Furling.rouqData Φ (homProduct k (S) T) D) hG μg b) = c • 𝟙 _) :
    theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j (b ≫ f) =
    c • theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j f := by
  classical
  simp only [theta, LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [thetaEntry, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Furling.upCorner_comp_of_scalar hπ Vg δ β ⟨ν.map Sum.inl, rfl⟩ hδ G hG HG MG _ _ j b f c hb,
    map_smul, map_smul]

variable
  (H : RouqUpKLR (homProduct k (S) T) (unfQ (k := k) D.arrows))
  (hnil : ∀ (c : I ⊕ I₂) {x y : X × X₂} (h : x + (RD.prod RD₂).iX c = y),
    IsNilpotent (End.of ((homProduct k (S) T).dot c h)))
  (hzero : ∀ (β : (I ⊕ I₂) →₀ ℤ) (c : I ⊕ I₂) {y : X × X₂}
    (h : Φ.wtT β + (RD.prod RD₂).iX c = y), ¬ Φ.rel β c →
      IsZero ((homProduct k (S) T).E c h))
  (harr : ∀ a ∈ ν.map Sum.inl, ∀ b ∈ ν.map Sum.inl, D.arrows a b = 0)
  (hnd : (ν.map (Sum.inl (β := I₂))).Nodup)
  (hPQ : ∀ a b, a ≠ b → klQ2 k C₀ a b = P b a * MvPolynomial.rename ![1, 0] (P a b))

include H₂ hQ₂ hΨ₀ hzero H hnil in
/-- The KLR image of one vacuum coordinate, including scalar extension. -/
theorem thetaEntry_toUEnd (r : KLRAlgebra k₀ (klQ2 k₀ C₀) ((ν.map Sum.inl).map D.π))
    (t s : Seq ν) {j : Seq ((ν.map Sum.inl).map D.π)}
    (hs : down D.π rfl (Seq.map Sum.inl s) = j) :
    thetaEntry hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t s j (toUEnd RD₀ k₀ μg _ r (down D.π rfl (Seq.map Sum.inl t)) j) =
    cycFlip D harr hnd M (cycMk D _ M (e (Seq.map Sum.inl s)) *
      cycGamma D harr rfl hnd M hPQ
        (mapRingHom (algebraMap k₀ k) (fun i j _ => map_klQ2 C₀ _ i j) r) *
      cycMk D _ M (e (Seq.map Sum.inl t))) := by
  change vacuumCoord hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD t s
    (wordHomTransport (homProduct k (S) T) hx hy _ _ (Vg β) V hV _ _
      (Furling.upCorner hπ Vg δ β ⟨ν.map Sum.inl, rfl⟩ hδ G hG HG MG _ _ j _)) = _
  rw [Furling.upCorner_toUEnd hπ Vg δ β ⟨ν.map Sum.inl, rfl⟩ hδ H hnil hzero G hG HG MG hPQ r _ _ hs,
    wordHomTransport_klrComplAt]
  exact vacuumCoord_klrComplAt hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz
    M haM D hprodD H hnil harr hnd _ t s

private theorem sum_cycMk_inl (j : Seq ((ν.map Sum.inl).map D.π)) :
    (∑ s : {s : Seq ν // down D.π rfl (Seq.map Sum.inl s) = j},
      cycMk D _ M (e (Seq.map Sum.inl s.1))) = cycGamma D harr rfl hnd M hPQ (e j) := by
  classical
  rw [cycGamma_e]
  rw [Finset.sum_subtype (p := fun s : Seq (ν.map Sum.inl) => down D.π rfl s = j)
    (Finset.univ.filter (fun s : Seq (ν.map Sum.inl) => down D.π rfl s = j))
    (fun s => by simp)]
  let E : {s : Seq ν // down D.π rfl (Seq.map Sum.inl s) = j} ≃
      {s : Seq (ν.map Sum.inl) // down D.π rfl s = j} :=
    (Seq.mapEquiv Sum.inl_injective ν).subtypeEquiv (fun _ => Iff.rfl)
  exact Fintype.sum_equiv E _ _ (fun _ => rfl)

include H₂ hQ₂ hΨ₀ hzero H hnil in
/-- The entire vacuum evaluation of a KLR diagram, not just one matrix entry. -/
theorem theta_toUEnd (r : KLRAlgebra k₀ (klQ2 k₀ C₀) ((ν.map Sum.inl).map D.π))
    (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π)) :
    theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j (toUEnd RD₀ k₀ μg _ r (down D.π rfl (Seq.map Sum.inl t)) j) =
    cycFlip D harr hnd M (cycGamma D harr rfl hnd M hPQ
        (mapRingHom (algebraMap k₀ k) (fun i j _ => map_klQ2 C₀ _ i j) (e j * r)) *
      cycMk D _ M (e (Seq.map Sum.inl t))) := by
  classical
  simp only [theta, LinearMap.sum_apply]
  calc
    _ = ∑ s : {s : Seq ν // down D.π rfl (Seq.map Sum.inl s) = j},
        cycFlip D harr hnd M (cycMk D _ M (e (Seq.map Sum.inl s.1)) *
          cycGamma D harr rfl hnd M hPQ
            (mapRingHom (algebraMap k₀ k) (fun i j _ => map_klQ2 C₀ _ i j) r) *
          cycMk D _ M (e (Seq.map Sum.inl t))) := by
      apply Finset.sum_congr rfl
      intro s _
      exact thetaEntry_toUEnd hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz M haM D
        hprodD Φ hπ Vg β δ hδ hx hy hV G hG HG MG H hnil hzero harr hnd hPQ r t s.1 s.2
    _ = _ := by
      rw [← map_sum, ← Finset.sum_mul, ← Finset.sum_mul, sum_cycMk_inl M D harr hnd hPQ j]
      rw [map_mul (mapRingHom (algebraMap k₀ k) (fun i j _ => map_klQ2 C₀ _ i j)),
        mapRingHom_e, map_mul (cycGamma D harr rfl hnd M hPQ)]

omit [DecidableEq I] [DecidableEq I₂] in
private theorem mapRingHom_crossWord
    (ρ : List ℕ) :
    mapRingHom (ν := ((ν.map Sum.inl).map D.π)) (algebraMap k₀ k)
      (fun i j _ => map_klQ2 C₀ _ i j) (ψw ρ) = ψw ρ := by
  induction ρ with
  | nil => simp only [ψw_nil, map_one]
  | cons j ρ ih => rw [ψw_cons, map_mul, mapRingHom_ψ, ih, ψw_cons]

include H₂ hQ₂ hΨ₀ hzero H hnil in
/-- The KLR basis-image component of the constructed semilinear vacuum evaluation. -/
theorem theta_toUEnd_basis
    (ρ : Equiv.Perm (Fin ((ν.map Sum.inl).map D.π).card) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced ((ν.map Sum.inl).map D.π).card (ρ w) ∧
      TypeA.wordProd ((ν.map Sum.inl).map D.π).card (ρ w) = w)
    (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π))
    (w : Equiv.Perm (Fin ((ν.map Sum.inl).map D.π).card))
    (u : Fin ((ν.map Sum.inl).map D.π).card →₀ ℕ)
    (hw : w • down D.π rfl (Seq.map Sum.inl t) = j) :
    theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j
      (toUEnd RD₀ k₀ μg _
        (KL2.basis ρ hρ (down D.π rfl (Seq.map Sum.inl t), w, u))
        (down D.π rfl (Seq.map Sum.inl t)) j) =
    cycFlip D harr hnd M (cycGamma D harr rfl hnd M hPQ
      (ψw (ρ w) * pol (MvPolynomial.monomial u 1) * e (down D.π rfl (Seq.map Sum.inl t))) *
        cycMk D _ M (e (Seq.map Sum.inl t))) := by
  rw [theta_toUEnd hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz M haM D
    hprodD Φ hπ Vg β δ hδ hx hy hV G hG HG MG H hnil hzero harr hnd hPQ]
  rw [KL2.basis_apply, e_mul_gen, (hρ w).2, ← hw, inv_smul_smul, ite_eq_left rfl]
  simp only [map_mul, mapRingHom_e, mapRingHom_pol, MvPolynomial.map_monomial, map_one,
    mapRingHom_crossWord]

include H₂ hQ₂ hΨ₀ hzero H hnil in
/-- The basis-image equation follows from the scalar bubble action on the input word.
This hypothesis is a single evaluated bubble equation, not an assumed basis-image formula. -/
theorem theta_phi_basis_of_bubble
    (ρ : Equiv.Perm (Fin ((ν.map Sum.inl).map D.π).card) → List ℕ)
    (hρ : ∀ w, TypeA.IsReduced ((ν.map Sum.inl).map D.π).card (ρ w) ∧
      TypeA.wordProd ((ν.map Sum.inl).map D.π).card (ρ w) = w)
    (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π))
    (w : Equiv.Perm (Fin ((ν.map Sum.inl).map D.π).card))
    (u : Fin ((ν.map Sum.inl).map D.π).card →₀ ℕ)
    (hw : w • down D.π rfl (Seq.map Sum.inl t) = j)
    (p : PiLam I₀ k₀) (c : k)
    (hb : (Furling.evalBlk Φ (homProduct k (S) T) Vg δ).map
      (G.upEvalData HG MG (Furling.rouqData Φ (homProduct k (S) T) D) hG μg
        (bubAt RD₀ k₀ μg (ups (word (down D.π rfl (Seq.map Sum.inl t))))
          (bubMap RD₀ k₀ μg p).val)) = c • 𝟙 _) :
    theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j
      (phi RD₀ k₀ μg _
        (KL2.basis ρ hρ (down D.π rfl (Seq.map Sum.inl t), w, u) ⊗ₜ[k₀] p)
        (down D.π rfl (Seq.map Sum.inl t)) j) =
    c • cycFlip D harr hnd M (cycGamma D harr rfl hnd M hPQ
      (ψw (ρ w) * pol (MvPolynomial.monomial u 1) * e (down D.π rfl (Seq.map Sum.inl t))) *
        cycMk D _ M (e (Seq.map Sum.inl t))) := by
  rw [phi_tmul_apply,
    theta_comp_of_scalar hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ V z hz M haM D hprodD Φ hπ Vg β δ hδ
      hx hy hV G hG HG MG t j _ _ c hb]
  exact congrArg (c • ·) (theta_toUEnd_basis hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz M haM D
    hprodD Φ hπ Vg β δ hδ hx hy hV G hG HG MG H hnil hzero harr hnd hPQ ρ hρ t j w u hw)

attribute [local instance] ScalarRestriction.linearCatHom
  ScalarRestriction.precompLinear ScalarRestriction.postcompLinear

include H₂ hQ₂ hΨ₀ hzero H hnil in
/-- Assemble the evaluation consumed by the nondegeneracy argument from the constructed
vacuum map. The remaining bubble input is its evaluated scalar action, not `map_basis`.
The weight and object identifications above must be supplied for the chosen vacuum. -/
def unfurledEvalOfVacuum (t : Seq ν) (j : Seq ((ν.map Sum.inl).map D.π)) (N : ℕ)
    (hM : N ≤ M) (bub : PiLam I₀ k₀ →ₐ[k₀] k)
    (hind : AlgebraicIndependent k₀ fun p : {p : I₀ × ℕ // p.2 < N} => bub (MvPolynomial.X p.1))
    (hb : ∀ p : PiLam I₀ k₀, (G.bubbleMap HG.brundan_kl_restrictScalars MG μg p).hom.app
      (G.dataObj (Furling.rouqData Φ (homProduct k (S) T) D) hG μg Vg) = bub p • 𝟙 _) :
    UnfurledEval RD₀ k₀ μg (down D.π rfl (Seq.map Sum.inl t)) j N where
  L := k
  J := I ⊕ I₂
  P := P
  hPQ := hPQ
  D := D
  ν' := ν.map Sum.inl
  hν := rfl
  hnd := hnd
  harr := harr
  t := Seq.map Sum.inl t
  ht := rfl
  M := M
  hM := hM
  bub := bub
  bub_indep := hind
  Θ := theta hQ hlead ha hΛ hdeg μ₂ V₀ h0 v₀ (Ψ₀ := Ψ₀) V z hz M haM D hprodD Φ hπ Vg β δ hδ
    hx hy hV G hG HG MG t j
  ρ := cycFlip D harr hnd M
  ρ_injective := cycFlip_injective D harr hnd M
  map_basis w u m hw :=
    theta_phi_basis_of_bubble hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz M haM D
      hprodD Φ hπ Vg β δ hδ hx hy hV G hG HG MG H hnil hzero harr hnd hPQ
      (ρc _) (hρc _) t j w u hw (MvPolynomial.monomial m 1) _ (by
        have he := G.upEvalData_bubMap_of_scalar HG MG
          (Furling.rouqData Φ (homProduct k (S) T) D) hG μg Vg
          (down D.π rfl (Seq.map Sum.inl t)) (MvPolynomial.monomial m 1) _ (hb _)
        exact congrFun he δ)

end Furled
end Categorification.KLR.CyclotomicAction
