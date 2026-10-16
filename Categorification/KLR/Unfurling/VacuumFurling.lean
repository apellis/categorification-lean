/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.VacuumBubbles
import Categorification.TwoRep.Furling

/-!
# Clockwise bubbles of a furled action on one block

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the bubbles of the colour `i` act on the generating object
`𝕍` through the coefficients of `∏_{a over i} (1 - z_a t)^{-Λ_a}`.

This file specializes `ev_comp_eq_coeff` to the furled action `TwoRep.Furling` on an object `M`
of weight `λ`, at one block `β₀`. There `F_i E_i M` is the sum over the relevant edges
`e : β₀ → β₀ + a` of `F_a E_a M_{β₀}` (`feAt`). The dot of `g` acts diagonally on this sum
(`feDot_comm_feProj`), as `ϖ_a(y)` on the summand of the label `a` (`genE_dot`). The cup of `g`
on that summand is the cup of `E_a ⊣ F_a` (`unit_projF`). So suppose that `ϖ_a(y) - z_a` is
nilpotent of order `h_a` on `E_a M_{β₀}`, as on a cyclotomic quotient. Then the clockwise
bubbles `cup ≫ dotⁿ ≫ d` of `g` at `M_{β₀}` are determined by their values in degrees below
`N = ∑ h_a`, the dual-basis values of Rouquier's isomorphism (`ev_unit_feDot_pow_comp`):

  `ev (cup ≫ dotⁿ ≫ d) = [t^{n+1-N}] ∏_e (1 - z_e t)^{-h_e}`.

## Main results

* `feProj_sum`, `feDot_comm_feProj`: the summands of `F_i E_i M` at `β₀` and the dot.
* `unit_feProj_feDot_sub_pow`: the cyclotomic vanishing on a summand.
* `ev_unit_feDot_pow_comp`: the values of the bubbles.
-/

open CategoryTheory CategoryTheory.Limits PowerSeries

noncomputable section

namespace Categorification.KLR.Unfurling

open TwoRep TwoRep.Furling

universe wk u₁ u₂ u₃ u₄ v₁

/-! ## Powers of shifted endomorphisms -/

section Shift

variable {L : Type*} [CommRing L] {C : Type*} [Category C] [Preadditive C] [Linear L C]

theorem comp_sub_algebraMap {X Y : C} (g : X ⟶ Y) (P : End X) (D : End Y)
    (hg : g ≫ D = P ≫ g) (c : L) :
    g ≫ (D - algebraMap L (End Y) c : End Y) = (P - algebraMap L (End X) c : End X) ≫ g := by
  rw [Preadditive.comp_sub, Preadditive.sub_comp, hg, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, Linear.comp_smul, Linear.smul_comp, End.one_def,
    End.one_def, Category.comp_id, Category.id_comp]

/-- If `g` intertwines `P` and `D`, it intertwines `(P - c)^m` and `(D - c)^m`. -/
theorem comp_sub_algebraMap_pow {X Y : C} (g : X ⟶ Y) (P : End X) (D : End Y)
    (hg : g ≫ D = P ≫ g) (c : L) (m : ℕ) :
    g ≫ ((D - algebraMap L (End Y) c) ^ m : End Y) =
      ((P - algebraMap L (End X) c) ^ m : End X) ≫ g := by
  induction m with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.comp_id, Category.id_comp]
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ← Category.assoc,
      comp_sub_algebraMap g P D hg c, Category.assoc, ih, Category.assoc]

/-- A linear functor commutes with `(D - c)^m`. -/
theorem map_sub_algebraMap_pow {C' : Type*} [Category C'] [Preadditive C'] [Linear L C']
    (G : C ⥤ C') [G.Additive] [G.Linear L] {Y : C} (D : End Y) (c : L) (m : ℕ) :
    G.map ((D - algebraMap L (End Y) c) ^ m : End Y) =
      (((show End (G.obj Y) from G.map D) - algebraMap L (End (G.obj Y)) c) ^ m : End (G.obj Y)) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, G.map_id]
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, G.map_comp, ih, G.map_sub,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, G.map_smul, End.one_def,
      End.one_def, G.map_id]

end Shift

/-! ## The summands of `F_i E_i M` at a block -/

variable {k : Type wk} [CommRing k]
  {J : Type u₁} {I : Type*} {Cc : QuantumGroup.CartanDatum J} {C : QuantumGroup.CartanDatum I}
  {Xc Yc : Type u₃} [AddCommGroup Xc] [AddCommGroup Yc] {X Y : Type u₄} [AddCommGroup X]
  [AddCommGroup Y] {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {RD : QuantumGroup.UDot.WeightDatum C X Y} (Φ : Furling RDc RD)
  (S : RouqFamily (B := LinearCat.{wk, v₁, u₂} k) RDc) [∀ x, HasFiniteBiproducts (S.obj x : Type u₂)]
  (ϖ : J → Polynomial k) (i : I) {l l' : X} (h : l + RD.iX i = l')
  (M : ∀ β : Φ.Blk l, Φ.blkCat S β.1) (β₀ : Φ.Blk l)

/-- The relevant edges of the colour `i` out of the block `β₀`. -/
abbrev OutEdge := {e : Φ.Edge i l // e.src = β₀}

instance : Fintype (OutEdge Φ i β₀) := Fintype.ofFinite _

/-- The summand of the edge `p` of `F_i E_i M` at the block `β₀`. -/
abbrev feSummand (p : OutEdge Φ i β₀) : Φ.blkCat S β₀.1 :=
  (Φ.incSrc S p.1 β₀ p.2).obj ((Φ.Fa S h p.1 (p.1.tgt h) rfl).obj
    ((Φ.E S i h).obj.obj M (p.1.tgt h)))

/-- `F_i E_i M` at the block `β₀`, the sum of the summands of the relevant edges. -/
abbrev feAt : Φ.blkCat S β₀.1 := (Φ.F S i h).obj.obj ((Φ.E S i h).obj.obj M) β₀

theorem feAt_eq : feAt Φ S i h M β₀ = ⨁ feSummand Φ S i h M β₀ := rfl

/-- The cup of `g` (the unit of `E_i ⊣ F_i`) at the block `β₀`. -/
def feUnit : M β₀ ⟶ feAt Φ S i h M β₀ := (Φ.adj S i h).unit.hom.app M β₀

/-- The dot of `g` on `F_i E_i M` at the block `β₀`. -/
def feDot : End (feAt Φ S i h M β₀) :=
  (Φ.F S i h).obj.map ((dot Φ S ϖ i h).hom.app M) β₀

/-- The idempotent of the summand of the edge `p`. -/
def feProj (p : OutEdge Φ i β₀) : End (feAt Φ S i h M β₀) :=
  biproduct.π (feSummand Φ S i h M β₀) p ≫ biproduct.ι (feSummand Φ S i h M β₀) p

theorem feProj_sum : ∑ p, feProj Φ S i h M β₀ p = 𝟙 (feAt Φ S i h M β₀) := by
  refine biproduct.hom_ext' _ _ fun j => ?_
  rw [Preadditive.comp_sum]
  erw [Category.comp_id]
  rw [Finset.sum_eq_single j]
  · erw [feProj, ← Category.assoc, biproduct.ι_π_self, Category.id_comp]
  · intro p _ hp
    erw [feProj, ← Category.assoc, biproduct.ι_π_ne _ (Ne.symm hp), zero_comp]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The component of the dot on the summand of `p`. -/
abbrev feDotAt (p : OutEdge Φ i β₀) : End (feSummand Φ S i h M β₀ p) :=
  (Φ.incSrc S p.1 β₀ p.2).map ((Φ.Fa S h p.1 (p.1.tgt h) rfl).map
    ((dot Φ S ϖ i h).hom.app M (p.1.tgt h)))

theorem feDot_π (p : OutEdge Φ i β₀) :
    feDot Φ S ϖ i h M β₀ ≫ biproduct.π (feSummand Φ S i h M β₀) p =
      biproduct.π (feSummand Φ S i h M β₀) p ≫ feDotAt Φ S ϖ i h M β₀ p := by
  unfold feDot
  exact biproduct.map_π (f := feSummand Φ S i h M β₀) (g := feSummand Φ S i h M β₀)
    (fun p => feDotAt Φ S ϖ i h M β₀ p) p

theorem ι_feDot (p : OutEdge Φ i β₀) :
    biproduct.ι (feSummand Φ S i h M β₀) p ≫ feDot Φ S ϖ i h M β₀ =
      feDotAt Φ S ϖ i h M β₀ p ≫ biproduct.ι (feSummand Φ S i h M β₀) p := by
  unfold feDot
  exact biproduct.ι_map (f := feSummand Φ S i h M β₀) (g := feSummand Φ S i h M β₀)
    (fun p => feDotAt Φ S ϖ i h M β₀ p) p

/-- The dot of `g` acts diagonally on the summands. -/
theorem feDot_comm_feProj (p : OutEdge Φ i β₀) :
    Commute (feDot Φ S ϖ i h M β₀) (feProj Φ S i h M β₀ p) := by
  rw [Commute, SemiconjBy, End.mul_def, End.mul_def, feProj, Category.assoc, ι_feDot,
    ← Category.assoc, ← Category.assoc, feDot_π, Category.assoc]

/-- The dot `ϖ_a(y)` on `E_a M_{β₀}`, for the label `a` of an edge out of `β₀`. -/
abbrev labelDot (e : Φ.Edge i l) : End ((Φ.Ea S h e (e.tgt h) rfl).obj (M e.src)) :=
  (Polynomial.aeval (show End (S.E e.lbl (wt_tgt h e rfl)) from S.dot e.lbl (wt_tgt h e rfl))
    (ϖ e.lbl)).hom.app (M e.src)

/-- **The cyclotomic vanishing on a summand**: if `(ϖ_a(y) - z)^m = 0` on `E_a M_{β₀}`, the cup
of `g` followed by the idempotent of the summand of `a` is killed by `(dot - z)^m`. -/
theorem unit_feProj_feDot_sub_pow (p : OutEdge Φ i β₀) (c : k) (m : ℕ)
    (hnil : ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ c) ^ m :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0) :
    feUnit Φ S i h M β₀ ≫ feProj Φ S i h M β₀ p ≫
      ((feDot Φ S ϖ i h M β₀ - algebraMap k _ c) ^ m : End (feAt Φ S i h M β₀)) = 0 := by
  obtain ⟨e, rfl⟩ := p
  have h1 : feProj Φ S i h M e.src ⟨e, rfl⟩ ≫
      ((feDot Φ S ϖ i h M e.src - algebraMap k _ c) ^ m : End (feAt Φ S i h M e.src)) =
        biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩ ≫
          ((feDotAt Φ S ϖ i h M e.src ⟨e, rfl⟩ - algebraMap k _ c) ^ m : End _) ≫
            biproduct.ι (feSummand Φ S i h M e.src) ⟨e, rfl⟩ := by
    rw [feProj, Category.assoc]
    congr 1
    exact comp_sub_algebraMap_pow (Y := feAt Φ S i h M e.src) _ _ _
      (ι_feDot Φ S ϖ i h M e.src ⟨e, rfl⟩) c m
  have h2 : feUnit Φ S i h M e.src ≫ biproduct.π (feSummand Φ S i h M e.src) ⟨e, rfl⟩ =
      (Φ.adjA S h e (e.tgt h) rfl).unit.app (M e.src) ≫
        (Φ.Fa S h e (e.tgt h) rfl).map (genE Φ S i h M ⟨e, rfl⟩) :=
    unit_projF Φ S i h M e
  have hg := comp_sub_algebraMap_pow (genE Φ S i h M ⟨e, rfl⟩) (labelDot Φ S ϖ i h M e)
    ((dot Φ S ϖ i h).hom.app M (e.tgt h)) (genE_dot Φ S ϖ i h M ⟨e, rfl⟩) c m
  rw [hnil, zero_comp] at hg
  have hF := congrArg (Φ.Fa S h e (e.tgt h) rfl).map hg
  rw [Functor.map_comp, Functor.map_zero, map_sub_algebraMap_pow] at hF
  have h3 : (Φ.Fa S h e (e.tgt h) rfl).map (genE Φ S i h M ⟨e, rfl⟩) ≫
      ((feDotAt Φ S ϖ i h M e.src ⟨e, rfl⟩ - algebraMap k _ c) ^ m : End _) = 0 := hF
  rw [h1, ← Category.assoc, h2]
  erw [Category.assoc, ← Category.assoc ((Φ.Fa S h e (e.tgt h) rfl).map (genE Φ S i h M ⟨e, rfl⟩)),
    h3, zero_comp, comp_zero]

/-- **The clockwise bubbles of a furled action on one block** (Webster, arXiv:1603.06311v3,
proof of the theorem with label `nondegenerate`). Let `z_e` and `h_e` be scalars and
multiplicities on the relevant edges `e` of the colour `i` out of the block `β₀`, with
`(ϖ_a(y) - z_e)^{h_e} = 0` on `E_a M_{β₀}` (`a` the label of `e`). Suppose an algebra map `ev`
from `End M_{β₀}` to a commutative ring sends `cup ≫ dot^t ≫ d` to `δ_{t, N-1}` for
`t < N = ∑_e h_e > 0`. Then for every `n`

  `ev (cup ≫ dotⁿ ≫ d) = [t^{n+1-N}] ∏_e (1 - z_e t)^{-h_e}`   (`0` if `n + 1 < N`). -/
theorem ev_unit_feDot_pow_comp (z : OutEdge Φ i β₀ → k) (hp : OutEdge Φ i β₀ → ℕ)
    (hnil : ∀ p m, hp p ≤ m → ((labelDot Φ S ϖ i h M p.1 - algebraMap k _ (z p)) ^ m :
      End ((Φ.Ea S h p.1 (p.1.tgt h) rfl).obj (M p.1.src))) = 0)
    {R : Type*} [CommRing R] [Algebra k R] (ev : End (M β₀) →ₐ[k] R)
    (d : feAt Φ S i h M β₀ ⟶ M β₀) (hN : 0 < ∑ p, hp p)
    (hd : ∀ t < ∑ p, hp p, ev (feUnit Φ S i h M β₀ ≫
      (feDot Φ S ϖ i h M β₀ ^ t : End (feAt Φ S i h M β₀)) ≫ d) =
        if t + 1 = ∑ p, hp p then 1 else 0) (n : ℕ) :
    ev (feUnit Φ S i h M β₀ ≫ (feDot Φ S ϖ i h M β₀ ^ n : End (feAt Φ S i h M β₀)) ≫
      d) = if ∑ p, hp p ≤ n + 1 then
        algebraMap k R (coeff (n + 1 - ∑ p, hp p)
          ((∏ p, oneSubUnit (z p) ^ (-(hp p : ℤ)) : (PowerSeries k)ˣ) : PowerSeries k))
        else 0 := by
  have key := ev_comp_eq_coeff (V := M β₀) (Wa := fun _ => feAt Φ S i h M β₀)
    (feProj Φ S i h M β₀) (fun _ => 𝟙 _)
    (fun p => feUnit Φ S i h M β₀ ≫ feProj Φ S i h M β₀ p)
    (fun p => feDot Φ S ϖ i h M β₀ - algebraMap k _ (z p)) z hp
    (fun n => feUnit Φ S i h M β₀ ≫ (feDot Φ S ϖ i h M β₀ ^ n : End _)) d ev
    (by simp only [Category.comp_id]; exact feProj_sum Φ S i h M β₀)
    (fun n p => by
      rw [add_sub_cancel, Category.assoc, Category.assoc,
        ← End.mul_def (feProj Φ S i h M β₀ p), ← End.mul_def _ (feProj Φ S i h M β₀ p),
        ((feDot_comm_feProj Φ S ϖ i h M β₀ p).pow_left n).eq])
    (fun p m hm => by
      rw [Category.assoc]
      exact unit_feProj_feDot_sub_pow Φ S ϖ i h M β₀ p (z p) m (hnil p m hm))
    hN (fun t ht => by rw [Category.assoc]; exact hd t ht) n
  rwa [Category.assoc] at key

end Categorification.KLR.Unfurling
