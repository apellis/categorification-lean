/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumFurling
import Categorification.KLR.Unfurling.VacuumRouqBubbles

/-!
# The labels of a furled action at one block, and its clockwise bubbles

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. For the furled action of `g` (`TwoRep.Furling`) on an object
`M` of weight `λ` concentrated at one block `β₀`, this file supplies the label data of
`cw_app_eq_lwSeq` at `β₀` from the Rouquier family `S̃` of the cover:

* the lowest weight labels are the relevant edges `e : β₀ → β₀ + a` out of `β₀`: on the summand
  `F_a E_a M_{β₀}` of `F_i E_i M` the dot of `g` is `ϖ_a(y)`, and if `(ϖ_a(y) - z_a)^{h_a} = 0` on
  `E_a M_{β₀}`, then `∏ₐ (D - z_a)^{h_a} = 0` on `F_i E_i M` at `β₀` (`aeval_feDot_eq_zero`), so
  `D - z` is invertible for every other scalar `z` (`exists_feDot_inverse`);
* the highest weight labels are the relevant edges `e : β₀ - b → β₀` into `β₀`: the `♠`-cups of
  Rouquier's data of the label `b` at the weight of `β₀`, followed by the inclusion of the summand
  of `e` into `E_i F_i M`, form a chain of length `⟨h_b, wt β₀⟩` (`chainIn`), on which the dot of
  `g` acts by `ϖ_b(y)` (`chainIn_dot_sub`) and the counit of `g` by the counit of the label
  (`chainIn_counit`).

The main result `cw_app_furled` evaluates the clockwise bubbles of Rouquier's data of `g` at
`M_{β₀}`, for a weight `⟨h_i, λ⟩ ≤ 0`.

## Main results

* `aeval_feDot_eq_zero`, `exists_feDot_inverse`.
* `chainIn`, `chainIn_counit`, `chainIn_dot_sub`.
* `cw_app_furled`.
-/

noncomputable section

namespace Categorification.KLR.Unfurling

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep TwoRep.Furling

universe wk u₁ u₂ u₃ u₄ v₁

/-! ## Intertwining polynomials -/

section Comp

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

omit [Preadditive C] [Linear L C] in
/-- If `g` intertwines `P` and `D`, it intertwines their powers. -/
theorem comp_pow_of_comp {X Y : C} (g : X ⟶ Y) (P : End X) (D : End Y) (hg : g ≫ D = P ≫ g)
    (n : ℕ) : g ≫ (D ^ n : End Y) = (P ^ n : End X) ≫ g := by
  induction n with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.comp_id, Category.id_comp]
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ← Category.assoc, hg, Category.assoc, ih,
      Category.assoc]

/-- If `g` intertwines `P` and `D`, it intertwines `q(P)` and `q(D)`. -/
theorem comp_aeval {X Y : C} (g : X ⟶ Y) (P : End X) (D : End Y) (hg : g ≫ D = P ≫ g)
    (q : Polynomial L) :
    g ≫ (Polynomial.aeval D q : End Y) = (Polynomial.aeval P q : End X) ≫ g := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, Preadditive.comp_add, Preadditive.add_comp, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def]
    change g ≫ (a • (D ^ n : End Y) : Y ⟶ Y) = (a • (P ^ n : End X) : X ⟶ X) ≫ g
    rw [Linear.comp_smul, Linear.smul_comp, comp_pow_of_comp g P D hg n]

omit [Linear L C] in
/-- A power of a nilpotent power is zero. -/
theorem powComp_eq_zero_of_le {X : C} (f : X ⟶ X) {n m : ℕ} (h : powComp f n = 0)
    (hnm : n ≤ m) : powComp f m = 0 := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => rw [powComp_succ, ih, zero_comp]

/-- A section of a summand followed by a cap: `(c ≫ G(j) ≫ g) ≫ κ = c ≫ κ'` when `g ≫ κ` is
`G(π) ≫ κ'` and `j ≫ π = 1`. -/
theorem comp_map_comp_eq {D : Type*} [Category D] {D' : Type*} [Category D'] (G : D ⥤ D')
    {A B : D} {V Z : D'} (c : V ⟶ G.obj A) (j : A ⟶ B) (π : B ⟶ A) (g : G.obj B ⟶ Z)
    (κ : Z ⟶ V) (κ' : G.obj A ⟶ V) (hg : g ≫ κ = G.map π ≫ κ') (hj : j ≫ π = 𝟙 A) :
    (c ≫ G.map j ≫ g) ≫ κ = c ≫ κ' := by
  rw [Category.assoc, Category.assoc, hg, ← Category.assoc (G.map j), ← G.map_comp, hj,
    G.map_id, Category.id_comp]

/-- Moving a shifted dot through a section of a summand. -/
theorem comp_map_comp_sub {D : Type*} [Category D] (G : D ⥤ C)
    {A B : D} {V Z : C} (c : V ⟶ G.obj A) (j : A ⟶ B) (g : G.obj B ⟶ Z) (Dz : End Z)
    (ηA : End (G.obj A)) (ηB : End (G.obj B)) (hg : g ≫ Dz = ηB ≫ g)
    (hj : G.map j ≫ ηB = ηA ≫ G.map j) (a : L) :
    (c ≫ G.map j ≫ g) ≫ (Dz - algebraMap L (End Z) a : End Z) =
      (c ≫ (ηA - algebraMap L (End (G.obj A)) a : End (G.obj A))) ≫ G.map j ≫ g := by
  rw [Category.assoc, Category.assoc, comp_sub_algebraMap g ηB Dz hg, ← Category.assoc (G.map j),
    comp_sub_algebraMap (G.map j) ηA ηB hj, Category.assoc, Category.assoc]

end Comp

/-- Polynomials in a 2-endomorphism, evaluated at an object. -/
theorem aeval_hom_app {k : Type wk} [CommRing k] {C₁ C₂ : LinearCat.{wk, v₁, u₂} k}
    {E : C₁ ⟶ C₂} (x : End E) (p : Polynomial k) (V : (C₁ : Type u₂)) :
    (Polynomial.aeval x p).hom.app V =
      Polynomial.aeval (R := k) (A := End (E.obj.obj V)) (x.hom.app V) p := by
  let φ : End E →ₐ[k] End (E.obj.obj V) :=
    { toFun := fun f => f.hom.app V, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  exact (Polynomial.aeval_algHom_apply φ x p).symm

variable {k : Type wk} [Field k]
  {J : Type u₁} {I : Type*} {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y] {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y} (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc)
  [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]

/-! ## Evaluation at one block -/

section Eval

variable {l : X} (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- Evaluation of the endo-1-morphisms of the category of `g` of weight `λ` at `M`, at the
block `β₀`. -/
def blkEval : (Φ.obj S l ⟶ Φ.obj S l) ⥤ (Φ.blkCat S β₀.1 : Type u₂) where
  obj f := f.obj.obj M β₀
  map η := η.hom.app M β₀

instance : (blkEval Φ S M β₀).Additive where
  map_add := rfl

end Eval

/-! ## The lowest weight labels: edges out of the block -/

section Out

variable (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l')
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- If `M` vanishes off `β₀` and `(ϖ_a(y) - c)^m = 0` on `E_a M_{β₀}` for an edge `e` out of
`β₀`, then `(D - c)^m = 0` on `E_i M` at the target of `e`. -/
theorem dot_app_sub_pow_eq_zero (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (e : Φ.Edge i l)
    (he : e.src = β₀) (c : k) (m : ℕ)
    (hnil : ((labelDot Φ S ϖ i h M e - algebraMap k _ c) ^ m :
      End ((Φ.Ea S h e (e.tgt h) rfl).obj (M e.src))) = 0) :
    (((show End ((Φ.E S i h).obj.obj M (e.tgt h)) from (dot Φ S ϖ i h).hom.app M (e.tgt h)) -
        algebraMap k _ c) ^ m :
      End ((Φ.E S i h).obj.obj M (e.tgt h))) = 0 := by
  refine biproduct.hom_ext' _ _ fun e' => ?_
  rw [comp_zero]
  refine (comp_sub_algebraMap_pow (genE Φ S i h M e') _ _ (genE_dot Φ S ϖ i h M e') c m).trans ?_
  by_cases hs : e'.1.src = β₀
  · obtain ⟨e', he'⟩ := e'
    have hss : e'.src = e.src := hs.trans he.symm
    have hl : e'.lbl = e.lbl := by
      have h1 := congrArg Subtype.val he'
      simp only [Edge.tgt_val, hss] at h1
      exact Finsupp.single_left_injective one_ne_zero (add_left_cancel h1)
    obtain rfl : e' = e := Edge.ext hss hl
    exact (congrArg (· ≫ genE Φ S i h M ⟨e', he'⟩) hnil).trans zero_comp
  · exact (Functor.map_isZero _ (hM _ hs)).eq_of_src _ _

/-- The cyclotomic vanishing on a whole summand of `F_i E_i M` at `β₀`, for `M` vanishing off
`β₀`. -/
theorem feDotAt_sub_pow_eq_zero (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (p : OutEdge Φ i β₀) (c : k)
    (m : ℕ) (hnil : ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ c) ^ m :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0) :
    ((feDotAt Φ S ϖ i h M β₀ p - algebraMap k _ c) ^ m : End (feSummand Φ S i h M β₀ p)) = 0 := by
  have key : (Φ.incSrc S p.1 β₀ p.2).map ((Φ.Fa S h p.1 (p.1.tgt h) rfl).map
      (((show End ((Φ.E S i h).obj.obj M (p.1.tgt h)) from
        (dot Φ S ϖ i h).hom.app M (p.1.tgt h)) -
        algebraMap k _ c) ^ m :
        End ((Φ.E S i h).obj.obj M (p.1.tgt h)))) = 0 := by
    rw [dot_app_sub_pow_eq_zero Φ S ϖ i h M β₀ hM p.1 p.2 c m hnil, Functor.map_zero,
      Functor.map_zero]
  rw [map_sub_algebraMap_pow, map_sub_algebraMap_pow] at key
  exact key

/-- **The dot of `g` on `F_i E_i M` at `β₀`** is killed by `∏ₐ (X - z_a)^{h_a}` over the edges out
of `β₀`, if `M` vanishes off `β₀` and `(ϖ_a(y) - z_a)^{h_a} = 0` on `E_a M_{β₀}`. -/
theorem aeval_feDot_eq_zero (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (z : OutEdge Φ i β₀ → k)
    (hp : OutEdge Φ i β₀ → ℕ)
    (hnil : ∀ p, ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ (z p)) ^ hp p :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0) :
    (Polynomial.aeval (feDot Φ S ϖ i h M β₀)
      (∏ p, (Polynomial.X - Polynomial.C (z p)) ^ hp p) : End (feAt Φ S i h M β₀)) = 0 := by
  refine biproduct.hom_ext' _ _ fun p => ?_
  rw [comp_zero]
  refine (comp_aeval _ _ _ (ι_feDot Φ S ϖ i h M β₀ p) _).trans ?_
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun p => (Polynomial.X - Polynomial.C (z p)) ^ hp p)
    (Finset.mem_univ p)
  rw [hr, map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    feDotAt_sub_pow_eq_zero Φ S ϖ i h M β₀ hM p (z p) (hp p) (hnil p), zero_mul, zero_comp]

/-- **`D - z` is invertible on `F_i E_i M` at `β₀`** for a scalar `z` different from the `z_a`
with `h_a ≠ 0`. -/
theorem exists_feDot_inverse (hM : ∀ β, β ≠ β₀ → IsZero (M β)) (z : OutEdge Φ i β₀ → k)
    (hp : OutEdge Φ i β₀ → ℕ)
    (hnil : ∀ p, ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ (z p)) ^ hp p :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0)
    (zb : k) (hzb : ∀ p, hp p ≠ 0 → z p ≠ zb) :
    ∃ w : End (feAt Φ S i h M β₀),
      (feDot Φ S ϖ i h M β₀ - algebraMap k _ zb) * w = 1 ∧
        w * (feDot Φ S ϖ i h M β₀ - algebraMap k _ zb) = 1 :=
  exists_inverse_sub_algebraMap _ _ (aeval_feDot_eq_zero Φ S ϖ i h M β₀ hM z hp hnil) zb (by
    rw [isUnit_iff_ne_zero, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro p _
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    by_cases h0 : hp p = 0
    · rw [h0, pow_zero]; exact one_ne_zero
    · exact pow_ne_zero _ (sub_ne_zero.mpr (hzb p h0).symm))

end Out

/-! ## The highest weight labels: edges into the block -/

section In

variable (ϖ : J → Polynomial k) (i : I) {l₀ l : X} (h₀ : l₀ + RD.iX i = l)
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- The relevant edges of the colour `i` into the block `β₀`. -/
abbrev InEdge := {e : Φ.Edge i l₀ // e.tgt h₀ = β₀}

instance : Fintype (InEdge Φ i h₀ β₀) := Fintype.ofFinite _

/-- The inclusion of the summand of an edge into `F_i N`. -/
abbrev injF (N : ∀ γ : Φ.Blk l, Φ.blkCat S γ.1) (e : Φ.Edge i l₀) :
    (Φ.Fa S h₀ e (e.tgt h₀) rfl).obj (N (e.tgt h₀)) ⟶ (Φ.F S i h₀).obj.obj N e.src :=
  biproduct.ι (fun p : {e' : Φ.Edge i l₀ // e'.src = e.src} =>
    (Φ.incSrc S p.1 e.src p.2).obj ((blockRes (Edge.tgt h₀) (Φ.Fa S h₀)).obj N p.1)) ⟨e, rfl⟩

theorem injF_projF (N : ∀ γ : Φ.Blk l, Φ.blkCat S γ.1) (e : Φ.Edge i l₀) :
    injF Φ S i h₀ N e ≫ projF Φ S i h₀ N e = 𝟙 _ :=
  biproduct.ι_π_self _ _

/-- Rouquier's data of the label of an edge into a block, at the weight of that block. -/
abbrev labelLoc (e : Φ.Edge i l₀) :=
  S.loc e.lbl (wt_tgt h₀ e rfl) (rfl : Φ.wtT (e.tgt h₀).1 + RDc.iX e.lbl = _)

/-- The `m`-th `♠`-cup of the label of an edge `e` into a block, in `E_i F_i M`. -/
def cIn (e : Φ.Edge i l₀) (m : ℕ) :
    M (e.tgt h₀) ⟶ (Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) (e.tgt h₀) :=
  ((labelLoc Φ S i h₀ e).cupN m).hom.app (M (e.tgt h₀)) ≫
    (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
      genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩

/-- **The chains of a highest weight label**: the `m`-th `♠`-cup of the label of an edge into
`β₀`, in `E_i F_i M` at `β₀`. -/
def chainIn (p : InEdge Φ i h₀ β₀) (m : ℕ) :
    M β₀ ⟶ (Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀ := by
  obtain ⟨e, he⟩ := p
  subst he
  exact cIn Φ S i h₀ M e m

omit [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)] in
/-- A common nilpotency order of the two dots of the label of an edge into a block. -/
theorem exists_labelLoc_nilpotent
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (e : Φ.Edge i l₀) :
    ∃ n, powComp (S.dot e.lbl (wt_tgt h₀ e rfl)) n = 0 ∧
      powComp (S.dot e.lbl (rfl : Φ.wtT (e.tgt h₀).1 + RDc.iX e.lbl = _)) n = 0 := by
  obtain ⟨n₁, h₁⟩ := hnil e.lbl (wt_tgt h₀ e rfl)
  obtain ⟨n₂, h₂⟩ := hnil e.lbl (rfl : Φ.wtT (e.tgt h₀).1 + RDc.iX e.lbl = _)
  exact ⟨n₁ + n₂, powComp_eq_zero_of_le _ h₁ (Nat.le_add_right _ _),
    powComp_eq_zero_of_le _ h₂ (Nat.le_add_left _ _)⟩

/-- **The counit of `g` on the chains**: `c_{b,m} ≫ κ = δ_{m,0}` (Brundan (3.6) for the label,
with the bubbles of the label vanishing at `M_{β₀}`). -/
theorem chainIn_counit
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    [IsReduced (End (M β₀))] (p : InEdge Φ i h₀ β₀) (m : ℕ)
    (hm : m < (RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1)).toNat) :
    chainIn Φ S i h₀ M β₀ p m ≫ (Φ.adj S i h₀).counit.hom.app M β₀ =
      if m = 0 then 𝟙 _ else 0 := by
  obtain ⟨e, rfl⟩ := p
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLoc_nilpotent Φ S i h₀ hnil e
  have key := cupN_app_capD_app (labelLoc Φ S i h₀ e) (M (e.tgt h₀)) hx₁ hx₂ hm 0
  rw [pow_zero, End.one_def] at key
  refine (comp_map_comp_eq (Φ.Ea S h₀ e (e.tgt h₀) rfl) _ (injF Φ S i h₀ M e)
    (projF Φ S i h₀ M e) _ _ _ (genE_counit Φ S i h₀ M e) (injF_projF Φ S i h₀ M e)).trans ?_
  refine Eq.trans ?_ (key.trans ?_)
  · exact (congrArg _ (Category.id_comp _)).symm
  · by_cases hm0 : m = 0
    · subst hm0; rfl
    · simp only [hm0, Ne.symm hm0, ↓reduceIte]
      rfl

/-- **The dot of `g` on the chains**: `c_{b,m} ≫ (D - ϖ_b(0)) = ∑_{j<m} [ϖ_b]_{m-j} c_{b,j}`. -/
theorem chainIn_dot_sub
    (hnil : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    [IsReduced (End (M β₀))] (p : InEdge Φ i h₀ β₀)
    (hh : 0 ≤ RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1))
    (hY : IsZero ((S.F p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj
      ((S.E p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj (M β₀))))
    (m : ℕ) (hm : m < (RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1)).toNat) :
    chainIn Φ S i h₀ M β₀ p m ≫
      ((show End ((Φ.E S i h₀).obj.obj ((Φ.F S i h₀).obj.obj M) β₀) from
          (dot Φ S ϖ i h₀).hom.app ((Φ.F S i h₀).obj.obj M) β₀) -
        algebraMap k _ ((ϖ p.1.lbl).coeff 0)) =
      ∑ j ∈ Finset.range m, (ϖ p.1.lbl).coeff (m - j) • chainIn Φ S i h₀ M β₀ p j := by
  obtain ⟨e, rfl⟩ := p
  obtain ⟨n, hx₁, hx₂⟩ := exists_labelLoc_nilpotent Φ S i h₀ hnil e
  have key := cupN_app_aeval_sub (labelLoc Φ S i h₀ e) (M (e.tgt h₀)) hh hY hx₁ hx₂ (ϖ e.lbl) hm
  let η := (Polynomial.aeval
    (show End (S.E e.lbl (wt_tgt h₀ e rfl)) from S.dot e.lbl (wt_tgt h₀ e rfl)) (ϖ e.lbl)).hom
  have hη : η.app ((Φ.Fa S h₀ e (e.tgt h₀) rfl).obj (M (e.tgt h₀))) =
      Polynomial.aeval (dotAt (x₁ := S.dot e.lbl (wt_tgt h₀ e rfl)) (M (e.tgt h₀))) (ϖ e.lbl) :=
    aeval_hom_app _ _ _
  refine (comp_map_comp_sub (Φ.Ea S h₀ e (e.tgt h₀) rfl) _ (injF Φ S i h₀ M e)
    (genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩) _
    (Polynomial.aeval (dotAt (x₁ := S.dot e.lbl (wt_tgt h₀ e rfl)) (M (e.tgt h₀))) (ϖ e.lbl))
    (η.app ((Φ.F S i h₀).obj.obj M e.src))
    (genE_dot Φ S ϖ i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩)
    ((η.naturality _).trans (congrArg (· ≫ _) hη)) _).trans ?_
  refine (congrArg (· ≫ (Φ.Ea S h₀ e (e.tgt h₀) rfl).map (injF Φ S i h₀ M e) ≫
    genE Φ S i h₀ ((Φ.F S i h₀).obj.obj M) ⟨e, rfl⟩) key).trans ?_
  refine (Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  exact (Linear.smul_comp _ _ _ _ _ _).trans rfl

end In

/-! ## The clockwise bubbles of a furled action at one block -/

section Bubbles

variable (ϖ : J → Polynomial k) (i : I) {l₀ l l' : X} (h₀ : l₀ + RD.iX i = l)
  (h : l + RD.iX i = l') (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- **The clockwise bubbles of a furled action at one block** (Webster, arXiv:1603.06311v3,
proof of the theorem with label `nondegenerate`). Let `L` be Rouquier's data of the colour `i`
for the furled action of `g` at a weight `λ` with `⟨h_i, λ⟩ ≤ 0`, and let `M` be concentrated at
the block `β₀`, with `End M_{β₀}` reduced and the dots of `S̃` nilpotent. Suppose

* for the relevant edges `a` out of `β₀`: `(ϖ_a(y) - z_a)^{h_a} = 0` on `E_a M_{β₀}`;
* for the relevant edges `b` into `β₀`: the label `b` has weight `Λ_b = ⟨h_b, wt β₀⟩ ≥ 0` at
  `β₀`, `F_b E_b M_{β₀} = 0`, the constant terms `ϖ_b(0)` are distinct and differ from the `z_a`
  with `h_a ≠ 0`, and the linear coefficients `[ϖ_b]_1` are nonzero;
* `∑ₐ h_a = -⟨h_i, λ⟩ + ∑_b Λ_b > 0`.

Then the clockwise bubble with `m` dots acts on `M_{β₀}` by
`[t^{m+1+⟨h_i,λ⟩}] ∏_b (1 - ϖ_b(0) t)^{Λ_b} ∏ₐ (1 - z_a t)^{-h_a}`. -/
theorem cw_app_furled {τ : Φ.E S i h₀ ≫ Φ.E S i h ⟶ Φ.E S i h₀ ≫ Φ.E S i h} {hl : ℤ}
    (L : RouqLoc (Φ.adj S i h₀) (Φ.adj S i h) (dot Φ S ϖ i h₀) (dot Φ S ϖ i h) τ hl)
    (hhl : hl ≤ 0) (hM : ∀ β, β ≠ β₀ → IsZero (M β)) [IsReduced (End (M β₀))]
    (hnilS : ∀ (c : J) {x y : Xc} (hc : x + RDc.iX c = y), ∃ n, powComp (S.dot c hc) n = 0)
    (z : OutEdge Φ i β₀ → k) (hp : OutEdge Φ i β₀ → ℕ)
    (hnil : ∀ p m, hp p ≤ m → ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ (z p)) ^ m :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0)
    (hhb : ∀ p : InEdge Φ i h₀ β₀, 0 ≤ RDc.pair (RDc.iY p.1.lbl) (Φ.wtT β₀.1))
    (hY : ∀ p : InEdge Φ i h₀ β₀,
      IsZero ((S.F p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj
        ((S.E p.1.lbl (rfl : Φ.wtT β₀.1 + RDc.iX p.1.lbl = _)).obj.obj (M β₀))))
    (hzb : Function.Injective fun p : InEdge Φ i h₀ β₀ => (ϖ p.1.lbl).coeff 0)
    (hsep : ∀ a (b : InEdge Φ i h₀ β₀), hp a ≠ 0 → z a ≠ (ϖ b.1.lbl).coeff 0)
    (hβ : ∀ p : InEdge Φ i h₀ β₀, (ϖ p.1.lbl).coeff 1 ≠ 0)
    (hN : ∑ a, hp a = (-hl).toNat +
      ∑ b : InEdge Φ i h₀ β₀, (RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat)
    (hNpos : 0 < ∑ a, hp a) {R : Type*} [CommRing R] [Algebra k R] (ev : End (M β₀) →ₐ[k] R)
    (m : ℕ) :
    ev ((L.cw m).hom.app M β₀) = algebraMap k R (lwSeq (-hl).toNat
      ((∏ b : InEdge Φ i h₀ β₀, (1 - PowerSeries.C ((ϖ b.1.lbl).coeff 0) * PowerSeries.X) ^
          (RDc.pair (RDc.iY b.1.lbl) (Φ.wtT β₀.1)).toNat) *
        ((∏ a, oneSubUnit (z a) ^ (-(hp a : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k)) m) := by
  classical
  have hw := fun b : InEdge Φ i h₀ β₀ => exists_feDot_inverse Φ S ϖ i h M β₀ hM z hp
    (fun p => hnil p (hp p) le_rfl) ((ϖ b.1.lbl).coeff 0) (fun a ha => hsep a b ha)
  refine cw_app_eq_lwSeq L (blkEval Φ S M β₀) hhl ev (Wa := fun _ => feAt Φ S i h M β₀)
    (feProj Φ S i h M β₀) (fun _ => 𝟙 _) (fun p => feUnit Φ S i h M β₀ ≫ feProj Φ S i h M β₀ p)
    (fun p => feDot Φ S ϖ i h M β₀ - algebraMap k _ (z p)) z hp ?_ ?_ ?_
    (fun b => (ϖ b.1.lbl).coeff 0) hzb _ (fun b => (hw b).choose) ?_ ?_ (chainIn Φ S i h₀ M β₀)
    (fun b m j => (ϖ b.1.lbl).coeff (m - j)) ?_ ?_ ?_ hN hNpos m
  · exact (Finset.sum_congr rfl fun a _ => Category.comp_id _).trans (feProj_sum Φ S i h M β₀)
  · intro n p
    change (feUnit Φ S i h M β₀ ≫ (feDot Φ S ϖ i h M β₀ ^ n : End _)) ≫ feProj Φ S i h M β₀ p =
      (feUnit Φ S i h M β₀ ≫ feProj Φ S i h M β₀ p) ≫
        ((algebraMap k _ (z p) + (feDot Φ S ϖ i h M β₀ - algebraMap k _ (z p))) ^ n : End _)
    rw [add_sub_cancel, Category.assoc, Category.assoc,
      ← End.mul_def (feProj Φ S i h M β₀ p), ← End.mul_def _ (feProj Φ S i h M β₀ p),
      ((feDot_comm_feProj Φ S ϖ i h M β₀ p).pow_left n).eq]
  · intro p m hm
    exact (Category.assoc _ _ _).trans
      (unit_feProj_feDot_sub_pow Φ S ϖ i h M β₀ p (z p) m (hnil p m hm))
  · intro b; exact (hw b).choose_spec.1
  · intro b; exact (hw b).choose_spec.2
  · intro b m hm
    exact chainIn_dot_sub Φ S ϖ i h₀ M β₀ hnilS b (hhb b) (hY b) m hm
  · intro b m _
    rw [Nat.add_sub_cancel_left]
    exact hβ b
  · intro b m hm
    exact chainIn_counit Φ S i h₀ M β₀ hnilS b m hm

end Bubbles

end Categorification.KLR.Unfurling
