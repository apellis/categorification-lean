/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumFurlingLabelsDual

/-!
# Nilpotency of the dots at a highest or lowest weight object

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. The evaluation of the bubbles of `g` at one block
(`cw_app_furled`, `ccw_app_furled`) takes as input the cyclotomic vanishing of the dot of each
label on the summands of `F_i E_i M` and `E_i F_i M`. This file derives it from Rouquier's data of
the label, as in the sl₂ argument of J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, §3:

* if `h ≥ 0` and `F E V = 0`, the dot `y` on `E F V` satisfies `y^h = 0` (`dotAt_pow_eq_zero`):
  the caps `yᵐ ≫ κ` (`m < h`) and the `♠`-cups decompose the identity of `E F V`, and
  `yʲ ≫ κ = 0` for `j ≥ h`;
* if `h ≤ 0` and `E F V = 0`, the dot `y` on `E V` satisfies `y^{-h} = 0`
  (`dot_app_pow_eq_zero`): the `♣`-caps and the dotted cups decompose the identity of `F E V`, so
  the unit followed by `F(y^{-h})` vanishes, and `y^{-h} = 0` by adjunction.

For a furled action of `g` at a block `β₀`, the dot of `g` on the summand of an edge is `ϖ_a(y)`,
so `ϖ_a(y) - ϖ_a(0)` is nilpotent of the same order (`labelDot_sub_pow_eq_zero`,
`labelDotIn_sub_pow_eq_zero`). With these, the bubbles of `g` at a block where every label is
highest or lowest weight are evaluated by `cw_app_vacuum` and `ccw_app_vacuum`.

## Main results

* `pow_eq_zero_of_chain_counit`, `comp_pow_eq_zero_of_chain_unit`,
  `aeval_sub_coeff_zero_pow_eq_zero`.
* `dotAt_pow_eq_zero`, `dot_app_pow_eq_zero`.
* `labelDot_sub_pow_eq_zero`, `labelDotIn_sub_pow_eq_zero`.
* `cw_app_vacuum`, `ccw_app_vacuum`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep TwoRep.Furling

/-! ## Nilpotency from a decomposition of the identity -/

section Chain

variable {C : Type*} [Category C] [Preadditive C]

/-- If the caps `Dᵐ ≫ κ` (`m < N`) and maps `g_m` decompose the identity of `P`, with
`g_m ≫ D^{m'} ≫ κ = δ_{m m'}` for all `m'`, then `D^N = 0`. -/
theorem pow_eq_zero_of_chain_counit {V P : C} (κ : P ⟶ V) (D : End P) (N : ℕ)
    (g : ℕ → (V ⟶ P)) (htot : ∑ m ∈ Finset.range N, ((D ^ m : End P) ≫ κ) ≫ g m = 𝟙 P)
    (hcc : ∀ m m', m < N → g m ≫ (D ^ m' : End P) ≫ κ = if m' = m then 𝟙 V else 0) :
    (D ^ N : End P) = 0 := by
  have h1 : ∀ j, N ≤ j → (D ^ j : End P) ≫ κ = 0 := by
    intro j hj
    rw [← Category.id_comp ((D ^ j : End P) ≫ κ), ← htot, Preadditive.sum_comp]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    rw [Category.assoc, hcc m j hm']
    simp only [show ¬ j = m by omega, ↓reduceIte, Limits.comp_zero]
  refine (Category.comp_id _).symm.trans ?_
  rw [← htot, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  have e : (D ^ N : End P) ≫ (D ^ m : End P) = (D ^ (m + N) : End P) := (pow_add D m N).symm
  rw [← Category.assoc, ← Category.assoc, e, h1 _ (by omega), Limits.zero_comp]

/-- If the maps `c_m` and the dotted cups `κ ≫ Dᵐ` (`m < N`) decompose the identity of `P`, with
`κ ≫ D^{m'} ≫ c_m = δ_{m m'}` for all `m'`, then `κ ≫ D^N = 0`. -/
theorem comp_pow_eq_zero_of_chain_unit {V P : C} (κ : V ⟶ P) (D : End P) (N : ℕ)
    (c : ℕ → (P ⟶ V)) (htot : ∑ m ∈ Finset.range N, c m ≫ κ ≫ (D ^ m : End P) = 𝟙 P)
    (hcc : ∀ m m', m < N → κ ≫ (D ^ m' : End P) ≫ c m = if m' = m then 𝟙 V else 0) :
    κ ≫ (D ^ N : End P) = 0 := by
  rw [← Category.comp_id (κ ≫ (D ^ N : End P)), ← htot, Preadditive.comp_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  rw [Category.assoc, ← Category.assoc (D ^ N : End P), ← Category.assoc κ, hcc m N hm']
  simp only [show ¬ N = m by omega, ↓reduceIte, Limits.zero_comp]

end Chain

/-- If `D^n = 0`, then `(p(D) - p(0))^n = 0`. -/
theorem aeval_sub_coeff_zero_pow_eq_zero {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : A) {n : ℕ} (hD : D ^ n = 0) (p : Polynomial R) :
    (Polynomial.aeval D p - algebraMap R A (p.coeff 0)) ^ n = 0 := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h : Polynomial.aeval D p - algebraMap R A (p.coeff 0) = D * Polynomial.aeval D q := by
    rw [← Polynomial.aeval_C, ← map_sub, hq, map_mul, Polynomial.aeval_X]
  have hc : Commute D (Polynomial.aeval D q) := by
    have := congrArg (Polynomial.aeval D) (mul_comm Polynomial.X q)
    rw [map_mul, map_mul, Polynomial.aeval_X] at this
    exact this
  rw [h, hc.mul_pow, hD, zero_mul]

/-! ## Rouquier's data at a highest or lowest weight object -/

section Loc

universe w v u

variable {k : Type w} [CommRing k] {C₁ C₂ C₃ : LinearCat.{w, v, u} k}
  {E₁ : C₁ ⟶ C₂} {R₁ : C₂ ⟶ C₁} {E₂ : C₂ ⟶ C₃} {R₂ : C₃ ⟶ C₂}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (V : (C₂ : Type u))

include L in
/-- **The dot at a highest weight object**: if `h ≥ 0`, `F E V = 0`, the dots are nilpotent and
`End V` is reduced, then `y^h = 0` on `E F V`. -/
theorem dotAt_pow_eq_zero (hh : 0 ≤ h) (hY : IsZero (R₂.obj.obj (E₂.obj.obj V))) {n : ℕ}
    (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) [IsReduced (End V)] :
    (dotAt (R₁ := R₁) (x₁ := x₁) V ^ h.toNat : End _) = 0 :=
  pow_eq_zero_of_chain_counit (adj₁.counit.hom.app V) (dotAt V) h.toNat
    (fun m => (L.cupN m).hom.app V) (sum_capD_cupN_app L V hh hY)
    (fun _ m' hm => cupN_app_capD_app L V hx₁ hx₂ hm m')

include L in
/-- **The dot at a lowest weight object**: if `h ≤ 0`, `E F V = 0`, the dots are nilpotent and
`End V` is reduced, then `y^{-h} = 0` on `E V`. -/
theorem dot_app_pow_eq_zero (hh : h ≤ 0) (hY : IsZero (E₁.obj.obj (R₁.obj.obj V))) {n : ℕ}
    (hx₁ : powComp x₁ n = 0) (hx₂ : powComp x₂ n = 0) [IsReduced (End V)] :
    ((show End (E₂.obj.obj V) from x₂.hom.app V) ^ (-h).toNat : End (E₂.obj.obj V)) = 0 := by
  have key := comp_pow_eq_zero_of_chain_unit (adj₂.unit.hom.app V)
    (dotAt₂ (x₂ := x₂) (R₂ := R₂) V) (-h).toNat (fun m => (L.capN m).hom.app V)
    (sum_capN_cupD_app L V hh hY) (fun _ m' hm => cupD_app_capN_app L V hx₁ hx₂ hm m')
  have hpow : (dotAt₂ (x₂ := x₂) (R₂ := R₂) V ^ (-h).toNat : End _) =
      R₂.obj.map ((show End (E₂.obj.obj V) from x₂.hom.app V) ^ (-h).toNat :
        End (E₂.obj.obj V)) :=
    (map_pow (R₂.obj.mapEnd (E₂.obj.obj V)) (show End (E₂.obj.obj V) from x₂.hom.app V)
      (-h).toNat).symm
  have : R₂.obj.Additive := R₂.property.1
  apply (LinearCat.toAdjunction adj₂).homEquiv V (E₂.obj.obj V) |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero,
    Limits.comp_zero]
  exact (congrArg (adj₂.unit.hom.app V ≫ ·) hpow).symm.trans key

end Loc

/-! ## The dots of a furled action on the summands of an edge -/

universe wk u₁ u₂ u₃ u₄ v₁

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y] {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y} (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)

section Out

variable (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l')
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1)

/-- **The dot of `g` on the summand of an edge out of a lowest weight block**: if the label of
`e` has weight `≤ 0` at the source of `e` and `E_a F_a M = 0` there, then
`(ϖ_a(y) - ϖ_a(0))^m = 0` on `E_a M` for `m ≥ -⟨h_a, wt e.src⟩`. -/
theorem labelDot_sub_pow_eq_zero
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (e : Φ.Edge i l) [IsReduced (End (M e.src))]
    (hh : RDc.pair (RDc.iY e.lbl) (Φ.wtT e.src.1) ≤ 0)
    (hY : IsZero ((S.E e.lbl (sub_add_cancel (Φ.wtT e.src.1) (RDc.iX e.lbl))).obj.obj
      ((S.F e.lbl (sub_add_cancel (Φ.wtT e.src.1) (RDc.iX e.lbl))).obj.obj (M e.src))))
    (m : ℕ) (hm : (-RDc.pair (RDc.iY e.lbl) (Φ.wtT e.src.1)).toNat ≤ m) :
    ((labelDot Φ S ϖ i h M e - algebraMap k _ ((ϖ e.lbl).coeff 0)) ^ m :
      End ((Φ.Ea S h e (e.tgt h) rfl).obj (M e.src))) = 0 := by
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLocOut_nilpotent Φ S i h hnilS e
  have hD := dot_app_pow_eq_zero (labelLocOut Φ S i h e) (M e.src) hh hY hx₁ hx₂
  have key := aeval_sub_coeff_zero_pow_eq_zero _ hD (ϖ e.lbl)
  rw [← aeval_hom_app] at key
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, key, zero_mul]

/-- The same vanishing when `E_a M = 0` at the source of `e`. -/
theorem labelDot_sub_pow_eq_zero_of_isZero (e : Φ.Edge i l)
    (hZ : IsZero ((Φ.Ea S h e (e.tgt h) rfl).obj (M e.src))) (c : k) (m : ℕ) :
    ((labelDot Φ S ϖ i h M e - algebraMap k _ c) ^ m :
      End ((Φ.Ea S h e (e.tgt h) rfl).obj (M e.src))) = 0 :=
  hZ.eq_of_src _ _

end Out

section In

variable (ϖ : J → Polynomial k) (i : I) {l₀ l : X} (h₀ : l₀ + RD.iX i = l)
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- **The dot of `g` on the summand of an edge into a highest weight block**: if the label of
`p` has weight `≥ 0` at `β₀` and `F_b E_b M = 0` there, then `(ϖ_b(y) - ϖ_b(0))^m = 0` on
`E_b F_b M` for `m ≥ ⟨h_b, wt β₀⟩`. -/
theorem labelDotIn_sub_pow_eq_zero
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    [IsReduced (End (M β₀))] (p : InEdge Φ i h₀ β₀)
    (hh : 0 ≤ RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1))
    (hY : IsZero ((S.F p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj
      ((S.E p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj (M β₀))))
    (m : ℕ) (hm : (RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1)).toNat ≤ m) :
    ((labelDotIn Φ S ϖ i h₀ M β₀ p - algebraMap k _ ((ϖ p.1.lbl).coeff 0)) ^ m :
      End (WIn Φ S i h₀ M β₀ p)) = 0 := by
  obtain ⟨e, rfl⟩ := p
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLoc_nilpotent Φ S i h₀ hnilS e
  have hD := dotAt_pow_eq_zero (labelLoc Φ S i h₀ e) (M (e.tgt h₀)) hh hY hx₁ hx₂
  have key := aeval_sub_coeff_zero_pow_eq_zero _ hD (ϖ e.lbl)
  rw [← aeval_hom_app] at key
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, key, zero_mul]

/-- The same vanishing when `F_b M = 0` at the source of `p`. -/
theorem labelDotIn_sub_pow_eq_zero_of_isZero (p : InEdge Φ i h₀ β₀)
    (hZ : IsZero ((Φ.Fa S h₀ p.1 β₀ p.2).obj (M β₀))) (c : k) (m : ℕ) :
    ((labelDotIn Φ S ϖ i h₀ M β₀ p - algebraMap k _ c) ^ m : End (WIn Φ S i h₀ M β₀ p)) = 0 :=
  (Functor.map_isZero _ hZ).eq_of_src _ _

end In

/-! ## The bubbles of a furled action at a vacuum block -/

section Bubbles

variable [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] (ϖ : J → Polynomial k) (i : I)
  {l₀ l l' : X} (h₀ : l₀ + RD.iX i = l) (h : l + RD.iX i = l')
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- **The clockwise bubbles of a furled action at a vacuum block** (Webster, arXiv:1603.06311v3,
proof of the theorem with label `nondegenerate`). Let `M` be concentrated at the block `β₀`, at a
weight `λ` of `g` with `⟨h_i, λ⟩ ≤ 0`, with `End M_{β₀}` reduced and the dots of `S̃` nilpotent.
Suppose that every label of colour `i` relevant at `β₀` is either lowest weight for `M_{β₀}`
(weight `≤ 0` and `E_a F_a M_{β₀} = 0`) or kills it (`E_a M_{β₀} = 0`), and that the labels of
positive weight at `β₀` of the edges into `β₀` are highest weight for `M_{β₀}`
(`F_b E_b M_{β₀} = 0`). If the constant terms `ϖ_c(0)` of the labels of colour `i` are distinct
and the linear coefficients of the positive labels are nonzero, then the clockwise bubble with
`m` dots acts on `M_{β₀}` by
`[t^{m+1+⟨h_i,λ⟩}] ∏_b (1 - ϖ_b(0) t)^{Λ_b} ∏ₐ (1 - ϖ_a(0) t)^{-h_a}`, with
`Λ_b = max(⟨h_b, wt β₀⟩, 0)` over the edges into `β₀` and `h_a = max(-⟨h_a, wt β₀⟩, 0)` over the
edges out of `β₀`, provided `∑ₐ h_a = -⟨h_i, λ⟩ + ∑_b Λ_b > 0`. -/
theorem cw_app_vacuum {τ : Φ.E S i h₀ ≫ Φ.E S i h ⟶ Φ.E S i h₀ ≫ Φ.E S i h} {hl : ℤ}
    (L : RouqLoc (Φ.adj S i h₀) (Φ.adj S i h) (dot Φ S ϖ i h₀) (dot Φ S ϖ i h) τ hl)
    (hhl : hl ≤ 0) (hM : ∀ β, β ≠ β₀ → IsZero (M β)) [IsReduced (End (M β₀))]
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (hout : ∀ p : OutEdge Φ i β₀,
      (RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1) ≤ 0 ∧
        IsZero ((S.E p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.lbl))).obj.obj
          ((S.F p.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.lbl))).obj.obj (M β₀)))) ∨
      IsZero ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src)))
    (hY : ∀ p : PosInEdge Φ i h₀ β₀,
      IsZero ((S.F p.1.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.1.lbl = _)).obj.obj
        ((S.E p.1.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.1.lbl = _)).obj.obj (M β₀))))
    (hinj : Set.InjOn (fun c => (ϖ c).coeff 0) {c | Φ.π c = i})
    (hβ : ∀ p : PosInEdge Φ i h₀ β₀, (ϖ p.1.1.lbl).coeff 1 ≠ 0)
    (hN : ∑ a : OutEdge Φ i β₀, (-RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat = (-hl).toNat +
      ∑ b : InEdge Φ i h₀ β₀, (RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat)
    (hNpos : 0 < ∑ a : OutEdge Φ i β₀, (-RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat)
    {R : Type*} [CommRing R] [Algebra k R] (ev : End (M β₀) →ₐ[k] R) (m : ℕ) :
    ev ((L.cw m).hom.app M β₀) = algebraMap k R (lwSeq (-hl).toNat
      ((∏ b : InEdge Φ i h₀ β₀, (1 - PowerSeries.C ((ϖ b.1.lbl).coeff 0) * PowerSeries.X) ^
          (RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat) *
        ((∏ a : OutEdge Φ i β₀, oneSubUnit ((ϖ a.1.lbl).coeff 0) ^
          (-((-RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat : ℤ)) : (PowerSeries k)ˣ) :
            PowerSeries k)) m) := by
  refine cw_app_furled Φ S ϖ i h₀ h M β₀ L hhl hM hnilS (fun a => (ϖ a.1.lbl).coeff 0)
    (fun a => (-RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat) ?_ hY ?_ ?_ hβ hN hNpos ev m
  · intro p n hn
    obtain ⟨e, he⟩ := p
    subst he
    rcases hout ⟨e, rfl⟩ with ⟨hh, hZ⟩ | hZ
    · exact labelDot_sub_pow_eq_zero Φ S ϖ i h M hnilS e hh hZ n hn
    · exact labelDot_sub_pow_eq_zero_of_isZero Φ S ϖ i h M e hZ _ n
  · intro p q hpq
    have hl : p.1.1.lbl = q.1.1.lbl := hinj p.1.1.π_lbl q.1.1.π_lbl hpq
    refine Subtype.ext (Subtype.ext (Edge.ext ?_ hl))
    have h1 := congrArg Subtype.val (p.1.2.trans q.1.2.symm)
    simp only [Edge.tgt_val, hl] at h1
    exact Subtype.ext (add_right_cancel h1)
  · intro a b ha heq
    have hl : a.1.lbl = b.1.1.lbl := hinj a.1.π_lbl b.1.1.π_lbl heq
    have hb := b.2
    rw [← hl] at hb
    omega

/-- **The counterclockwise bubbles of a furled action at a vacuum block** (Webster,
arXiv:1603.06311v3, proof of the theorem with label `nondegenerate`): the mirror of
`cw_app_vacuum`, at a weight `λ` of `g` with `⟨h_i, λ⟩ ≥ 0`. Every label of an edge into `β₀` is
either highest weight for `M_{β₀}` (weight `≥ 0` and `F_b E_b M_{β₀} = 0`) or kills it
(`F_b M_{β₀} = 0`), and the labels of negative weight at `β₀` of the edges out of `β₀` are lowest
weight for `M_{β₀}` (`E_a F_a M_{β₀} = 0`). -/
theorem ccw_app_vacuum {τ : Φ.E S i h₀ ≫ Φ.E S i h ⟶ Φ.E S i h₀ ≫ Φ.E S i h} {hl : ℤ}
    (L : RouqLoc (Φ.adj S i h₀) (Φ.adj S i h) (dot Φ S ϖ i h₀) (dot Φ S ϖ i h) τ hl)
    (hhl : 0 ≤ hl) (hM : ∀ β, β ≠ β₀ → IsZero (M β)) [IsReduced (End (M β₀))]
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (hin : ∀ p : InEdge Φ i h₀ β₀,
      (0 ≤ RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1) ∧
        IsZero ((S.F p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj
          ((S.E p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj (M β₀)))) ∨
      IsZero ((Φ.Fa S h₀ p.1 β₀ p.2).obj (M β₀)))
    (hY : ∀ p : NegOutEdge Φ i β₀,
      IsZero ((S.E p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.1.lbl))).obj.obj
        ((S.F p.1.1.lbl (sub_add_cancel (Φ.wtT β₀.1) (RDc.iX p.1.1.lbl))).obj.obj (M β₀))))
    (hinj : Set.InjOn (fun c => (ϖ c).coeff 0) {c | Φ.π c = i})
    (hβ : ∀ p : NegOutEdge Φ i β₀, (ϖ p.1.1.lbl).coeff 1 ≠ 0)
    (hN : ∑ a : InEdge Φ i h₀ β₀, (RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat = hl.toNat +
      ∑ b : OutEdge Φ i β₀, (-RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat)
    (hNpos : 0 < ∑ a : InEdge Φ i h₀ β₀, (RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat)
    {R : Type*} [CommRing R] [Algebra k R] (ev : End (M β₀) →ₐ[k] R) (m : ℕ) :
    ev ((L.ccw m).hom.app M β₀) = algebraMap k R (lwSeq hl.toNat
      ((∏ b : OutEdge Φ i β₀, (1 - PowerSeries.C ((ϖ b.1.lbl).coeff 0) * PowerSeries.X) ^
          (-RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat) *
        ((∏ a : InEdge Φ i h₀ β₀, oneSubUnit ((ϖ a.1.lbl).coeff 0) ^
          (-((RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat : ℤ)) : (PowerSeries k)ˣ) :
            PowerSeries k)) m) := by
  refine ccw_app_furled Φ S ϖ i h₀ h M β₀ L hhl hM hnilS (fun a => (ϖ a.1.lbl).coeff 0)
    (fun a => (RDc.pair (RDc.iY a.1.lbl) (Φ.wtT β₀.1)).toNat) ?_ hY ?_ ?_ hβ hN hNpos ev m
  · intro p n hn
    rcases hin p with ⟨hh, hZ⟩ | hZ
    · exact labelDotIn_sub_pow_eq_zero Φ S ϖ i h₀ M β₀ hnilS p hh hZ n hn
    · exact labelDotIn_sub_pow_eq_zero_of_isZero Φ S ϖ i h₀ M β₀ p hZ _ n
  · intro p q hpq
    have hl : p.1.1.lbl = q.1.1.lbl := hinj p.1.1.π_lbl q.1.1.π_lbl hpq
    exact Subtype.ext (Subtype.ext (Edge.ext (p.1.2.trans q.1.2.symm) hl))
  · intro a b ha heq
    have hl : a.1.lbl = b.1.1.lbl := hinj a.1.π_lbl b.1.1.π_lbl heq
    have hb := b.2
    rw [← hl] at hb
    omega

end Bubbles

end Categorification.KLR.Unfurling
