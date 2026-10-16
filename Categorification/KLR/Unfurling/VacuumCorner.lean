/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumProduct
import Categorification.KLR.ReindexSymmetries
import Categorification.KLR.Unfurling.CycFlip

/-!
# The KLR corner at the vacuum, in the unfurled cyclotomic quotient

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: on the words `Ẽ_t 𝕍` with labels `Ĩ₋` of the product
representation of `g̃`, the action of `R̂(ν̃)` is read off the cyclotomic quotient `𝖱^Λ(ν̃)`.

Let `D` be an unfurling datum on `I ⊕ I₂`, `W` the cyclotomic family on the labels `I` (with
parameters agreeing with `unfQ D.arrows` on `I`), `T` a Rouquier family on `I₂`, and `P` the
product family `Hom(T(-x₂), W(x₁))`, with `prodQ Q Q₂ = unfQ D.arrows`. Let `V`, `z` be objects
of `P` and of `T(-μ₂)` such that `V(z)` is a vacuum module, and let `ν` be a weight of `I` whose
image `ν̃ = ν.map inl` has pairwise distinct labels without arrows among them, and cyclotomic
level `a_i = y^M` on the labels of `ν`. Then for every `f ∈ R̂(ν̃)` the coordinate of the
`(inl ∘ t, inl ∘ s)` entry of the completed action of `f` at `V`, `z`, read through `wgen` and
`wcoord` and relabelled from `R^Λ(ν)` to `𝖱^Λ(ν̃) = UnfCyc D ν̃ M`, is
`cycFlip (e(inl ∘ s) · cycLift f · e(inl ∘ t))` (`relabel_wcoord_klrComplAt_inl_wgen`). For
`f = γ(r)` the middle factor is `cycGamma r` (`cycGamma` is `cycLift ∘ γ` by definition).

This composes `CyclotomicAction.wcoord_klrComplAt_inl_wgen` (the left colours of the product,
the Yoneda evaluation and the coordinates at the vacuum), the truncation
`GradingDatum.completionLift_eq_trunc` of `cycLift`, the relabelling of `hflip ∘ σ`
(`CycKLR.relabelEquiv_mk_hflip_sigma`) and `cycFlip_mk`.
-/

noncomputable section

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory QuantumGroup UDot TwoRep TwoRep.RouqFamily KLRAlgebra Unfurling

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
  {Q' : I ⊕ I₂ → I ⊕ I₂ → MvPolynomial (Fin 2) k} (hQ' : KLRSymm Q')
  (hprod : prodQ Q Q₂ = Q') (M : ℕ)
  (haM : ∀ i ∈ ν, a i = Polynomial.X ^ M)

include hprod in
omit [DecidableEq I] [DecidableEq I₂] in
theorem prodQ_inl_eq (a' b' : I) (_ : a' ≠ b') : Q' (Sum.inl a') (Sum.inl b') = Q a' b' := by
  rw [← hprod]; rfl

include hprod in
/-- The relabelling of sequences along `inl`, from the parameters of `W` to `Q'`. -/
abbrev inlRelabel : SeqRelabel k Q Q' ν (ν.map Sum.inl) :=
  SeqRelabel.ofInjectiveOf Sum.inl_injective Q' Q (prodQ_inl_eq hprod) ν

include haM in
omit [DecidableEq I] [DecidableEq I₂] in
theorem inlRelabel_cyc (i : Seq ν) (h : 0 < Multiset.card ν) :
    (fun _ => Polynomial.X ^ M : I ⊕ I₂ → Polynomial k)
        (((inlRelabel hprod (ν := ν)).equiv i).lbl (Fin.cast (inlRelabel hprod).card_eq ⟨0, h⟩)) =
      a (i.lbl ⟨0, h⟩) :=
  (haM _ (i.mem _)).symm

include H₂ hQ₂ hΨ₀ hQ' in
/-- The relabelled coordinates of the left colours at the vacuum, for an element of the KLR
algebra of the parameters `Q'`. -/
theorem relabel_wcoord_klrActAt_inl_wgen (H : RouqUpKLR (homProduct k (S) T) Q')
    (x : KLRAlgebra k Q' (ν.map Sum.inl)) (t s : Seq ν) :
    CycKLR.relabelEquiv (inlRelabel hprod) (inlRelabel_cyc hprod M haM)
      (wcoord hQ hlead ha hΛ hdeg V₀ h0 Ψ₀ s
        (((eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz t).symm ≫
          (((klrActAt H (μ, μ₂) (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν) x)
            (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V).hom.app z ≫
          eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz s))
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ t))) =
      CycKLR.mk k Q' (fun _ => Polynomial.X ^ M) (ν.map Sum.inl)
        (hflip (sigma hQ' (e (Seq.map Sum.inl s) * x * e (Seq.map Sum.inl t)))) := by
  subst hprod
  obtain ⟨r, rfl⟩ := (KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q Q₂) ν).surjective x
  rw [wcoord_klrActAt_inl_wgen hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ V z hz hΨ₀ r t s,
    CycKLR.relabelEquiv_mk_hflip_sigma _ _ hQ hQ' (SeqRelabel.ofInjectiveOf_rev _ _ _ _ _)]
  have hx : relabelHom (inlRelabel rfl) (e s * r * e t) =
      e (Seq.map Sum.inl s) * KLRAlgebra.reindexEquiv Sum.inl_injective (prodQ Q Q₂) ν r *
        e (Seq.map Sum.inl t) := by
    rw [map_mul, map_mul, relabelHom_e, relabelHom_e]
    rfl
  exact congrArg (fun y => CycKLR.mk k _ _ _ (hflip (sigma hQ' y))) hx

include H₂ hQ₂ hΨ₀ haM in
/-- **The KLR corner at the vacuum** (B. Webster, arXiv:1603.06311v3, used in the proof of the
theorem with label `nondegenerate`). In the product family `P = Hom(T(-x₂), W(x₁))` with `W`
cyclotomic and parameters `prodQ Q Q₂ = unfQ D.arrows`, at objects `V`, `z` with `V(z)` the
vacuum, for a weight `ν` whose image `ν̃ = ν.map inl` has pairwise distinct labels without arrows
among them and level `a_i = y^M` on its labels: for every `f ∈ R̂(ν̃)`, the coordinate at `s` of
the `(inl ∘ t, inl ∘ s)` entry of the completed action of `f` applied to the generator at `t`,
relabelled to `𝖱^Λ(ν̃)`, is `cycFlip (e(inl ∘ s) · cycLift f · e(inl ∘ t))`. -/
theorem relabel_wcoord_klrComplAt_inl_wgen {I₀ : Type*} {P : I₀ → I₀ → MvPolynomial (Fin 2) k}
    (D : UnfurlingDatum k P (I ⊕ I₂)) (hprodD : prodQ Q Q₂ = unfQ (k := k) D.arrows)
    (H : RouqUpKLR (homProduct k (S) T) (unfQ (k := k) D.arrows))
    (hnil : ∀ (c : I ⊕ I₂) {x y : X × X₂} (h : x + (RD.prod RD₂).iX c = y),
      IsNilpotent (End.of ((homProduct k (S) T).dot c h)))
    (harr : ∀ a ∈ ν.map Sum.inl, ∀ b ∈ ν.map Sum.inl, D.arrows a b = 0)
    (hnd : (ν.map (Sum.inl (β := I₂))).Nodup)
    (f : UnfCompl D (ν.map Sum.inl)) (t s : Seq ν) :
    CycKLR.relabelEquiv (inlRelabel hprodD) (inlRelabel_cyc hprodD M haM)
      (wcoord hQ hlead ha hΛ hdeg V₀ h0 Ψ₀ s
        (((eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz t).symm ≫
          (((klrComplAt H (μ, μ₂) (wtop RD μ ν, μ₂) (wtop_map_inl μ μ₂ ν) hnil
              (unfGrading (k := k) D.arrows) f)
            (Seq.map Sum.inl t) (Seq.map Sum.inl s)).hom.app V).hom.app z ≫
          eqToHom (wordCellAt_map_inl_vacuum hQ hlead ha hΛ hdeg μ₂ V₀ V z hz s))
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V₀ h0 v₀ t))) =
      cycFlip D harr hnd M (cycMk D _ M (e (Seq.map Sum.inl s)) * cycLift D harr hnd M f *
        cycMk D _ M (e (Seq.map Sum.inl t))) := by
  obtain ⟨N₀, hN₀⟩ := klrComplAt_eq_klrActAt_trunc H (μ, μ₂) (wtop RD μ ν, μ₂)
    (wtop_map_inl μ μ₂ ν) hnil (unfGrading (k := k) D.arrows)
  set N := max N₀ ((unfGrading (k := k) D.arrows).truncBound (ν.map Sum.inl) M)
  rw [hN₀ N (le_max_left _ _) f, cycLift,
    GradingDatum.completionLift_eq_trunc _ _ _ (le_max_right _ _) f, ← map_mul, ← map_mul,
    cycFlip_mk]
  exact relabel_wcoord_klrActAt_inl_wgen hQ hlead ha hΛ hdeg H₂ hQ₂ μ₂ V₀ h0 v₀ hΨ₀ V z hz
    (unfQ_klrSymm D.arrows) hprodD M haM H _ t s

end Categorification.KLR.CyclotomicAction
