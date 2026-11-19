/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLNegligible
import Categorification.KLR.CyclotomicAction.GlobalFamily
import Categorification.TwoRep.RouqModel

/-!
# Repeated red strands vanish on red-bounded blocks

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. In the cyclotomic
family of the extended datum, a red colour enters a block only through
cyclotomic induction. A composite of inductions and restrictions in which the
red colour `c` is induced at least twice, and never restricted, lands in
blocks containing `c` at least twice. Its components at the blocks in which
each red colour occurs at most once are therefore zero objects, and every
2-morphism into it is red-negligible (`RedNegligible.of_zeroBelow`).

`ZeroBelow c m N` says that the blocks of `N` with fewer than `m` strands of
colour `c` are zero; induction at `c` raises `m` by one
(`zeroBelow_globalE`), and induction or restriction at another colour keeps it
(`zeroBelow_globalE`, `zeroBelow_globalF`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR KLRAlgebra KLR.CyclotomicAction TwoRep
  QuantumGroup

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)

/-- The blocks of `N` with fewer than `m` strands of colour `c` are zero objects. -/
def ZeroBelow (c : I) (m : ℕ) {x : X}
    (N : ∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)) : Prop :=
  ∀ β : WeightBlocks RD Λ x, β.1.count c < m → IsZero (N β)

variable {Q a RD Λ}

theorem zeroBelow_zero (c : I) {x : X}
    (N : ∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)) :
    ZeroBelow.{u, v, w} Q a RD Λ c 0 N := fun _ h => absurd h (Nat.not_lt_zero _)

theorem ZeroBelow.mono {c : I} {m m' : ℕ} (hm : m' ≤ m) {x : X}
    {N : ∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)}
    (hN : ZeroBelow.{u, v, w} Q a RD Λ c m N) : ZeroBelow.{u, v, w} Q a RD Λ c m' N :=
  fun β hβ => hN β (lt_of_lt_of_le hβ hm)

/-- **Induction at `i` adds one strand of colour `i` to every block.** -/
theorem zeroBelow_globalE {c : I} {m : ℕ} (i : I) {x y : X} (h : x + RD.iX i = y)
    {N : ∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)}
    (hN : ZeroBelow.{u, v, w} Q a RD Λ c m N) :
    ZeroBelow.{u, v, w} Q a RD Λ c (m + if c = i then 1 else 0)
      ((globalE.{u, v, w} Q a RD Λ i h).obj.obj N) := by
  intro δ hδ
  change IsZero (⨁ fun p : {β // blockSucc RD Λ i h β = δ} =>
    (indBlock Q a RD Λ i h p.1 δ p.2).obj (N p.1))
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext' _ _ fun p => ?_
  rw [Category.comp_id, comp_zero]
  refine (Functor.map_isZero _ (hN p.1 ?_)).eq_of_src _ _
  have e := congrArg (Multiset.count c) (blockSucc_eq RD Λ i p.2)
  rw [Multiset.count_add, Multiset.count_singleton] at e
  omega

/-- **Restriction at a colour other than `c`** keeps the number of strands of colour `c`. -/
theorem zeroBelow_globalF {c : I} {m : ℕ} (i : I) (hi : i ≠ c) {x y : X}
    (h : x + RD.iX i = y)
    {N : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)}
    (hN : ZeroBelow.{u, v, w} Q a RD Λ c m N) :
    ZeroBelow.{u, v, w} Q a RD Λ c m ((globalF.{u, v, w} Q a RD Λ i h).obj.obj N) := by
  intro β hβ
  change IsZero ((resBlock Q a RD Λ i h β _ rfl).obj (N (blockSucc RD Λ i h β)))
  refine Functor.map_isZero _ (hN _ ?_)
  rw [blockSucc_val, Multiset.count_add, Multiset.count_singleton]
  simp only [Ne.symm hi, ite_false]
  omega

/-- **2-morphisms into a functor whose blocks with fewer than two strands of a red colour
vanish are red-negligible.** -/
theorem RedNegligible.of_zeroBelow
    {hc : ∀ δ c (z : CycKLR k Q a δ), Commute z (cyclotomicColourDot Q a δ c)} {Rd : Set I}
    {Z : LinearCat.{v, max (max u v) w, max (max u v) w + 1} k} {y : X}
    {F G : Z ⟶ weightSpace.{u, v, w} Q a RD Λ y} (α : F ⟶ G) {c : I} (hcR : c ∈ Rd)
    (hG : ∀ M, ZeroBelow.{u, v, w} Q a RD Λ c 2 (G.obj.obj M)) :
    RedNegligible Q a hc Rd RD Λ α := fun M β hβ => by
  have h1 := hβ c hcR
  rw [(hG M β (by omega)).eq_of_tgt (α.hom.app M β) 0]
  exact zero_mem _

/-! ### Words of the cyclotomic family -/

section Words

open Bicategory UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

variable
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

/-- The strand of colour `col`: an upward strand of colour `c` adds a strand of colour `c` to
every block, any other strand except a downward one of colour `c` keeps their number. -/
theorem zeroBelow_strandAt {c : I} (col : Col I X) (hcol : col.l ≠ (false, c)) {x y : X}
    (hx : (psig RD).colourTgt col = x) (hy : (psig RD).colourSrc col = y) {m : ℕ}
    {N : ∀ β : WeightBlocks RD Λ x, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)}
    (hN : ZeroBelow.{u, v, w} Q a RD Λ c m N) :
    ZeroBelow.{u, v, w} Q a RD Λ c (m + if col.l = (true, c) then 1 else 0)
      (((Fam).model.strandAt col x y hx hy).obj.obj N) := by
  rcases col with ⟨⟨_ | _, i⟩, r⟩
  · have hi : i ≠ c := fun h => hcol (by rw [h])
    subst hx hy
    have := zeroBelow_globalF (Q := Q) (a := a) (m := m) i hi
      (TwoRep.RouqFamily.dn_reg (RD := RD) i rfl rfl) hN
    have e : (if ((false, i) : Letter I) = (true, c) then 1 else 0) = 0 := by simp
    rw [e, add_zero]
    exact this
  · subst hx hy
    have := zeroBelow_globalE (Q := Q) (a := a) (c := c) (m := m) i
      (TwoRep.RouqFamily.up_reg (RD := RD) i rfl rfl) hN
    have e : (if ((true, i) : Letter I) = (true, c) then 1 else 0) =
        if c = i then 1 else 0 := by simp [eq_comm]
    rw [e]
    exact this

/-- **The image of a word** adds to every block as many strands of colour `c` as the word has
upward strands of colour `c`, provided it has no downward strand of colour `c`. -/
theorem zeroBelow_word {c : I} {s t : X} (w : List (Col I X)) (hw : (psig RD).ok s w)
    (e : (psig RD).endR s w = t) (hdown : ∀ col ∈ w, col.l ≠ (false, c)) {m : ℕ}
    {N : ∀ β : WeightBlocks RD Λ t, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1)}
    (hN : ZeroBelow.{u, v, w} Q a RD Λ c m N) :
    ZeroBelow.{u, v, w} Q a RD Λ c (m + w.countP fun col => col.l = (true, c))
      (((Fam).model.lift.map (fw s w t hw e)).obj.obj
        (id N : ((Fam).model.lift.obj (fo (S := psig RD) t)).carrier)) := by
  induction w generalizing s with
  | nil =>
    cases e
    exact hN
  | cons col w ih =>
    cases w with
    | nil =>
      have := zeroBelow_strandAt hQ hlead ha hΛ hdeg col
        (hdown col (List.mem_cons_self ..)) e hw.1 hN
      simp only [List.countP_cons, List.countP_nil, decide_eq_true_eq, zero_add]
      exact this
    | cons col' w =>
      have h₁ := ih hw.2 e (fun x hx => hdown x (List.mem_cons_of_mem _ hx))
      have h₂ := zeroBelow_strandAt hQ hlead ha hΛ hdeg col
        (hdown col (List.mem_cons_self ..)) rfl hw.1 h₁
      rw [List.countP_cons, ← add_assoc]
      simp only [decide_eq_true_eq]
      exact h₂

end Words

end Categorification.Stendhal
