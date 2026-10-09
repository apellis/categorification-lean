/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelQStrong
import Categorification.TwoRep.ModelSl2Interp
import Categorification.Diagrams.BicatInterpPull
import Categorification.Diagrams.StrictMate
import Categorification.Diagrams.KL3.StringEmbed

/-!
# The single-label relations in the model of a `Q`-strong 2-representation

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Theorem 1.1: the relations of `U_Q(g)` involving strands of a single label `i`
follow from the case `g = sl₂` (Theorem 5.5, applied to the restriction of the `Q`-strong
2-representation to the `α_i`-strings, "by rescaling degrees" when `d_i ≠ 1`, CL §2.6.1 and §5).
Here this reduction is made precise for the model of `Categorification.TwoRep.ModelQStrong` (any
Cartan datum, dots normalized to `r_i = 1`):

* the restriction `S.toStrongSl2 i b` of `S` to the `α_i`-string through a base point `b` is a
  strong 2-representation of `sl₂` on `Regrade B (d_i)` (`B` with the grading shift `⟨n⟩`
  replaced by `⟨d_i n⟩`); its `sl₂` model (`ModelSl2`) lives in `K^•(Regrade B (d_i))`, and is
  pushed forward to `K^•(B)` along the comparison `cmp B C i` (`Regrade.comparison`, which sends
  a 2-morphism of degree `n` to the same 2-morphism of degree `d_i n`;
  `Diagrams/BicatInterpPush`);
* the model of `S`, pulled back along the relabelling `StringEmbed.strSig` of `U(sl₂)` along the
  string (`Diagrams/BicatInterpPull`), *is* that pushforward: same objects, equal strand images
  (`pull_strandAt_eq`) and corresponding generator images (`pull_gen_heq`, from the comparisons
  `dotQ_heq`, `crossQ_heq`, `dotDnQ_heq`, `crossDnQ_heq`, `adjL_heqG`, `adjR_heqG`; mates and
  composite adjunctions commute with the comparison, `Diagrams/StrictMate`);
* hence a linear combination of diagrams of `U(sl₂)` killed by the `sl₂` model is, relabelled
  along the string, killed by the model of `S` (`killed_of_sl2`, `killed_rel`);
* every weight is reached along the string through its base point, in the regions of the parity
  of the string (`exists_string`, `ip_sw`), so every relation of KL III's `U` (Definition 3.1)
  involving a single label `i` is killed by the model (`StrongSl2.relations_killed`, CL Theorem
  5.5 for `sl₂`).

## Main results

* `QStrong.pull_strandAt_eq`, `QStrong.pull_gen_heq`, `QStrong.killed_of_sl2`;
* `QStrong.killed_cycDotR`, `killed_cycDotL`, `killed_cycCrossR`, `killed_cycCrossL` (labels
  `i`, `i`), `killed_cwNeg`, `killed_ccwNeg`, `killed_cwOne`, `killed_ccwOne`, `killed_curlR`,
  `killed_curlL`, `killed_decompEF`, `killed_decompFE`, `killed_klr_sqEq`, `killed_klr_slideLEq`,
  `killed_klr_slideREq`, `killed_klr_braid` (labels `i i i`): the single-label relations of
  `pres RD k` (with `r_i = 1`, as for the normalized dots) are killed, each read with its own outer
  regions.

Comparisons of 2-morphisms elaborated in different files are stated with all implicit objects
explicit (`heq_mate_gr`, `heq_mate₂_gr`): otherwise unification of the graded-Hom 2-morphism
types unfolds the 2-morphisms themselves and does not terminate in reasonable time.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u u₁

theorem heq_conj {D : Type*} [Category D] {A A' B' B'' : D} (p : A = A') (q : B' = B'')
    (f : A' ⟶ B') : eqToHom p ≫ f ≫ eqToHom q ≍ f := by
  subst p q; simp

/-! ## Comparison with the restrictions to strings

(Stated without opening `StringDiagrams`: elaborating 2-morphisms of the graded-Hom bicategory in a
context with the instances of the diagram library leads to instance paths whose unification is
very slow.) -/

section Compare

open QuantumGroup UDot GradedHomBicat
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable {S : QStrong B C RD k Q}

theorem qi_two (T : StrongSl2 k B) (n : ℤ) : T.qi (2 + n) = T.qi n + 1 := by
  unfold StrongSl2.qi; omega

theorem qi_n₀ (T : StrongSl2 k B) (r : ℤ) : T.qi (T.n₀ + 2 * r) = r := by
  unfold StrongSl2.qi; omega

theorem heq_transportLeft {a b : GradedHomBicat B} {R R' : b ⟶ a} {E : a ⟶ b} (hR : R = R')
    (adj : R ⊣ E) : transportLeft hR adj ≍ adj := by
  subst hR; rfl

theorem heq_adj_unit {a b : GradedHomBicat B} {R R' : b ⟶ a} {E E' : a ⟶ b} (hR : R' = R)
    (hE : E' = E) {adj : R ⊣ E} {adj' : R' ⊣ E'} (hadj : adj' ≍ adj) :
    adj'.unit ≍ adj.unit ∧ adj'.counit ≍ adj.counit := by
  subst hR hE; subst hadj; exact ⟨HEq.rfl, HEq.rfl⟩

theorem heq_mate_gr {a b a' b' : GradedHomBicat B} {R : b ⟶ a} {E : a ⟶ b} {R' : b' ⟶ a'}
    {E' : a' ⟶ b'} (ha : a' = a) (hb : b' = b) (hR : HEq R' R) (hE : HEq E' E)
    {adj : R ⊣ E} {adj' : R' ⊣ E'} (hadj : adj' ≍ adj)
    {x : E ⟶ E} {x' : E' ⟶ E'} (hx : x' ≍ x) :
    (Bicategory.conjugateEquiv adj' adj').symm x' ≍ (Bicategory.conjugateEquiv adj adj).symm x := by
  subst ha hb; subst hR hE; subst hadj; subst hx; rfl

theorem heq_mate₂_gr {a b c a' b' c' : GradedHomBicat B} {R₁ : c ⟶ b} {E₁ : b ⟶ c}
    {R₂ : b ⟶ a} {E₂ : a ⟶ b} {R₁' : c' ⟶ b'} {E₁' : b' ⟶ c'} {R₂' : b' ⟶ a'} {E₂' : a' ⟶ b'}
    (ha : a' = a) (hb : b' = b) (hc : c' = c) (hR₁ : HEq R₁' R₁) (hE₁ : HEq E₁' E₁)
    (hR₂ : HEq R₂' R₂) (hE₂ : HEq E₂' E₂) {adj₁ : R₁ ⊣ E₁} {adj₁' : R₁' ⊣ E₁'} {adj₂ : R₂ ⊣ E₂}
    {adj₂' : R₂' ⊣ E₂'} (h₁ : adj₁' ≍ adj₁) (h₂ : adj₂' ≍ adj₂) {x : E₂ ≫ E₁ ⟶ E₂ ≫ E₁}
    {x' : E₂' ≫ E₁' ⟶ E₂' ≫ E₁'} (hx : x' ≍ x) :
    (Bicategory.conjugateEquiv (adj₁'.comp adj₂') (adj₁'.comp adj₂')).symm x' ≍
      (Bicategory.conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂)).symm x := by
  subst ha hb hc; subst hR₁ hE₁ hR₂ hE₂; subst h₁ h₂; subst hx; rfl

variable (B C) in
/-- The comparison `K^•(Regrade B (d_i)) → K^•(B)` of graded-Hom bicategories
(`Regrade.comparison`). -/
abbrev cmp (i : I) : StrictPseudofunctor (GradedHomBicat (Regrade B (di C i))) (GradedHomBicat B) :=
  Regrade.comparison (di C i)

variable (S) in
theorem gEc_eq (i : I) (b : X) (a c : ℤ) (p : a + 1 = c)
    (h : b + a • RD.iX i + RD.iX i = b + c • RD.iX i) :
    (cmp B C i).map ((S.toStrongSl2 i b).gEc a c p) = S.Eg i h := by
  subst p; rfl

variable (S) in
theorem gRc_eq (i : I) (b : X) (a c : ℤ) (p : a + 1 = c)
    (h : b + a • RD.iX i + RD.iX i = b + c • RD.iX i) :
    (cmp B C i).map ((S.toStrongSl2 i b).gRc a c p) = S.Rg i h := by
  subst p; exact grR_toStrongSl2 S i b a h

variable (S) in
theorem dotQ_heq (i : I) (b : X) (r c : ℤ) (p : r + 1 = c)
    (h : b + r • RD.iX i + RD.iX i = b + c • RD.iX i) :
    S.dotQ i h ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gDot r c p) := by
  subst p
  refine heq_of_eq ?_
  rw [show (S.toStrongSl2 i b).gDot r (r + 1) rfl = (((S.rQ i)⁻¹ : kˣ) : k) •
      of₂ 2 ((S.toStrongSl2 i b).dot r) from rfl]
  erw [Regrade.comparison_map₂_smul, Regrade.comparison_map₂_of₂]
  show (((S.rQ i)⁻¹ : kˣ) : k) • of₂ (C.dot i i) (S.dot i h) = _
  congr 1
  exact GradedHomCat.homOf_congr (dot_eq_di C i) _

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  [GradedBicategory.IsLinear B k] in
theorem heq_mapAdjunction {a b : B} {E : a ⟶ b} {F : b ⟶ a} {n n' : ℤ} (e : n = n')
    (adj : Bicategory.Adjunction E (F⟦n⟧)) :
    (mapAdjunction (shiftAdj e adj)).unit ≍ (mapAdjunction adj).unit ∧
      (mapAdjunction (shiftAdj e adj)).counit ≍ (mapAdjunction adj).counit := by
  subst e; exact ⟨HEq.rfl, HEq.rfl⟩

variable (S) in
theorem crossQ_heq (i : I) (b : X) (r c d : ℤ) (p₁ : r + 1 = c) (p₂ : c + 1 = d) {n : X}
    (hn : n = b + c • RD.iX i) (h₁ : b + r • RD.iX i + RD.iX i = n)
    (h₂ : n + RD.iX i = b + d • RD.iX i) (h₃ : b + r • RD.iX i + RD.iX i = n)
    (h₄ : n + RD.iX i = b + d • RD.iX i) :
    S.crossQ i i h₁ h₂ h₃ h₄ ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gCross r c d p₁ p₂) := by
  subst hn p₁ p₂
  refine heq_of_eq ?_
  rw [show (S.toStrongSl2 i b).gCross r (r + 1) (r + 1 + 1) rfl rfl =
      of₂ (-2) ((S.toStrongSl2 i b).cross r) from rfl]
  erw [Regrade.comparison_map₂_of₂]
  show of₂ (-C.dot i i) (S.cross i i h₁ h₂ h₃ h₄) = _
  exact GradedHomCat.homOf_congr (by rw [dot_eq_di]; ring) _

theorem adjLAux_rfl (i : I) (b : X) (r : ℤ) (h : b + r • RD.iX i + RD.iX i = b + (r + 1) • RD.iX i) :
    adjLAux (S := S) i b r rfl rfl h =
      transportLeft (grR_toStrongSl2 S i b r h)
        ((cmp B C i).mapAdjunction ((S.toStrongSl2 i b).leftAdjN r)) :=
  rfl

theorem adjL_heq' (i : I) (b : X) (hb : strBase RD i b = b) (r : ℤ)
    (h : b + r • RD.iX i + RD.iX i = b + (r + 1) • RD.iX i) :
    adjL (S := S) i h ≍
      (cmp B C i).mapAdjunction (StrongSl2.gAdjL (S.toStrongSl2 i b) r (r + 1) rfl) := by
  rw [adjL_eq (S := S) i b hb r rfl rfl h, adjLAux_rfl]
  exact heq_transportLeft _ _

theorem adjL_heqP (i : I) (b : X) (hb : strBase RD i b = b) (r c : ℤ) (p : r + 1 = c)
    (h : b + r • RD.iX i + RD.iX i = b + c • RD.iX i) :
    adjL (S := S) i h ≍ (cmp B C i).mapAdjunction (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p) := by
  subst p
  exact adjL_heq' (S := S) i b hb r h

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  [GradedBicategory.IsLinear B k] in
theorem heq_eqToHom_conj {D : Type*} [Category D] {A A' B' B'' : D} (p : A = A') (q : B' = B'')
    {f : A' ⟶ B'} {g : A ⟶ B''} (h : g ≍ f) : g ≍ eqToHom p ≫ f ≫ eqToHom q :=
  h.trans (heq_conj p q f).symm

theorem adjL_heq (i : I) (b : X) (hb : strBase RD i b = b) (r c : ℤ) (p : r + 1 = c)
    (h : b + r • RD.iX i + RD.iX i = b + c • RD.iX i) :
    (adjL (S := S) i h).unit ≍
        (cmp B C i).map₂ (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p).unit ∧
      (adjL (S := S) i h).counit ≍
        (cmp B C i).map₂ (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p).counit := by
  have := heq_adj_unit (gRc_eq S i b r c p h).symm (gEc_eq S i b r c p h).symm
    (adjL_heqP (S := S) i b hb r c p h)
  rw [StrictPseudofunctor.mapAdjunction_unit', StrictPseudofunctor.mapAdjunction_counit'] at this
  exact ⟨this.1.trans (heq_conj _ _ _), this.2.trans (heq_conj _ _ _)⟩

theorem adjR_heq (i : I) (b : X) (r c : ℤ) (p : r + 1 = c)
    (h : b + r • RD.iX i + RD.iX i = b + c • RD.iX i) :
    (S.adjR i h).unit ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gAdjE r c p).unit ∧
      (S.adjR i h).counit ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gAdjE r c p).counit := by
  subst p
  have := heq_mapAdjunction (E := S.E i h) (F := S.F i h)
    (by rw [pair_string] :
      di C i * (RD.pair (RD.iY i) (b + r • RD.iX i) + 1) =
        di C i * (RD.pair (RD.iY i) b + 2 * r + 1))
    (S.adj i h)
  refine ⟨this.1.symm.trans (heq_of_eq ?_), this.2.symm.trans (heq_of_eq ?_)⟩
  · exact (Regrade.compMap₂_incl (di C i) _).symm
  · exact (Regrade.compMap₂_incl (di C i) _).symm

theorem dotDnQ_heq (i : I) (b : X) (hb : strBase RD i b = b) (r c : ℤ) (p : r + 1 = c)
    (h : b + r • RD.iX i + RD.iX i = b + c • RD.iX i) :
    dotDnQ (S := S) i h ≍ (cmp B C i).map₂ (StrongSl2.gDotR (S.toStrongSl2 i b) r c p) := by
  unfold StrongSl2.gDotR
  rw [Diagrams.BicatInterp.sp_map₂_conjugateEquiv_symm]
  exact (heq_mate_gr (a := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj r)))
    (b := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj c)))
    (a' := of (S.obj (b + r • RD.iX i))) (b' := of (S.obj (b + c • RD.iX i))) (by subst p; rfl)
    (by subst p; rfl) (heq_of_eq (gRc_eq S i b r c p h).symm)
    (heq_of_eq (gEc_eq S i b r c p h).symm) (adjL_heqP (S := S) i b hb r c p h)
    (dotQ_heq S i b r c p h))

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  [GradedBicategory.IsLinear B k] in
theorem heq_adj_comp {a b c a' b' c' : GradedHomBicat B} {R₁ : c ⟶ b} {E₁ : b ⟶ c}
    {R₂ : b ⟶ a} {E₂ : a ⟶ b} {R₁' : c' ⟶ b'} {E₁' : b' ⟶ c'} {R₂' : b' ⟶ a'} {E₂' : a' ⟶ b'}
    (ha : a' = a) (hb : b' = b) (hc : c' = c) (hR₁ : HEq R₁' R₁) (hE₁ : HEq E₁' E₁)
    (hR₂ : HEq R₂' R₂) (hE₂ : HEq E₂' E₂) {adj₁ : R₁ ⊣ E₁} {adj₁' : R₁' ⊣ E₁'} {adj₂ : R₂ ⊣ E₂}
    {adj₂' : R₂' ⊣ E₂'} (h₁ : adj₁' ≍ adj₁) (h₂ : adj₂' ≍ adj₂) :
    adj₁'.comp adj₂' ≍ adj₁.comp adj₂ := by
  subst ha hb hc; subst hR₁ hE₁ hR₂ hE₂; subst h₁ h₂; rfl

omit [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  [GradedBicategory.IsLinear B k] in
theorem heq_mate_gr' {a b a' b' : GradedHomBicat B} {R : b ⟶ a} {E : a ⟶ b} {R' : b' ⟶ a'}
    {E' : a' ⟶ b'} (ha : a' = a) (hb : b' = b) (hR : HEq R' R) (hE : HEq E' E)
    {adj : R ⊣ E} {adj' : R' ⊣ E'} (hadj : adj' ≍ adj)
    {x : E ⟶ E} {x' : E' ⟶ E'} (hx : x' ≍ x) :
    (Bicategory.conjugateEquiv adj' adj').symm x' ≍ (Bicategory.conjugateEquiv adj adj).symm x := by
  subst ha hb; subst hR hE; subst hadj; subst hx; rfl

theorem crossDnQ_heq (Sc : KL3.Diagram.CL.CLScalars C k) (i : I) (b : X)
    (hb : strBase RD i b = b) (r c d : ℤ) (p₁ : r + 1 = c) (p₂ : c + 1 = d) {n : X}
    (hn : n = b + c • RD.iX i) (hj : n + RD.iX i = b + d • RD.iX i)
    (hi : b + r • RD.iX i + RD.iX i = n) :
    crossDnQ (S := S) Sc i i hj hi hj hi ≍
      (cmp B C i).map₂ (StrongSl2.gCrossR (S.toStrongSl2 i b) r c d p₁ p₂) := by
  subst hn
  unfold crossDnQ StrongSl2.gCrossR
  rw [Sc.t_self, inv_one, Units.val_one, one_smul, Diagrams.BicatInterp.sp_map₂_conjugateEquiv_symm]
  have hcomp := Diagrams.BicatInterp.sp_mapAdjunction_comp_heq (cmp B C i)
    (StrongSl2.gAdjL (S.toStrongSl2 i b) c d p₂) (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p₁)
  refine heq_mate_gr' (a := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj r)))
    (b := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj d)))
    (a' := of (S.obj (b + r • RD.iX i))) (b' := of (S.obj (b + d • RD.iX i)))
    (by subst p₁ p₂; rfl) (by subst p₁ p₂; rfl) ?_ ?_
    ((heq_adj_comp (a := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj r)))
      (b := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj c)))
      (c := (cmp B C i).obj (of ((S.toStrongSl2 i b).obj d)))
      (a' := of (S.obj (b + r • RD.iX i))) (b' := of (S.obj (b + c • RD.iX i)))
      (c' := of (S.obj (b + d • RD.iX i))) (by subst p₁ p₂; rfl) (by subst p₁ p₂; rfl)
      (by subst p₁ p₂; rfl)
      (heq_of_eq (gRc_eq S i b c d p₂ hj).symm) (heq_of_eq (gEc_eq S i b c d p₂ hj).symm)
      (heq_of_eq (gRc_eq S i b r c p₁ hi).symm) (heq_of_eq (gEc_eq S i b r c p₁ hi).symm)
      (adjL_heqP (S := S) i b hb c d p₂ hj) (adjL_heqP (S := S) i b hb r c p₁ hi)).trans
        hcomp.symm)
    (crossQ_heq S i b r c d p₁ p₂ (n := b + c • RD.iX i) rfl hi hj hi hj)
  · subst p₁ p₂
    exact heq_of_eq (congrArg₂ (· ≫ ·) (gRc_eq S i b _ _ rfl hj) (gRc_eq S i b _ _ rfl hi)).symm
  · subst p₁ p₂
    exact heq_of_eq (congrArg₂ (· ≫ ·) (gEc_eq S i b _ _ rfl hi) (gEc_eq S i b _ _ rfl hj)).symm

theorem adjL_heqG (i : I) (b : X) (hb : strBase RD i b = b) (r c : ℤ) (p : r + 1 = c) {x y : X}
    (hx : x = b + r • RD.iX i) (hy : y = b + c • RD.iX i) (h : x + RD.iX i = y) :
    (adjL (S := S) i h).unit ≍
        (cmp B C i).map₂ (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p).unit ∧
      (adjL (S := S) i h).counit ≍
        (cmp B C i).map₂ (StrongSl2.gAdjL (S.toStrongSl2 i b) r c p).counit := by
  subst hx hy
  exact adjL_heq (S := S) i b hb r c p h

theorem adjR_heqG (i : I) (b : X) (r c : ℤ) (p : r + 1 = c) {x y : X}
    (hx : x = b + r • RD.iX i) (hy : y = b + c • RD.iX i) (h : x + RD.iX i = y) :
    (S.adjR i h).unit ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gAdjE r c p).unit ∧
      (S.adjR i h).counit ≍ (cmp B C i).map₂ ((S.toStrongSl2 i b).gAdjE r c p).counit := by
  subst hx hy
  exact adjR_heq (S := S) i b r c p h

end QStrong

end Compare

section Model

open GradedHomBicat
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {Q : I → I → MvPolynomial (Fin 2) k}

namespace QStrong

variable {S : QStrong B C RD k Q}

/-! ## The relabelling along a string -/

variable (S) in
/-- The relabelling of `U(sl₂)` along the `α_i`-string through `b`, with `q = qi` of the
restriction of `S` to that string. -/
abbrev strφ (i : I) (b : X) : SigMap (psig sl2RootDatum) (psig RD) :=
  StringEmbed.strSig RD i b (S.toStrongSl2 i b).qi (qi_two _)

/-- **The pulled-back model has the strand images of the `sl₂` model.** -/
theorem pull_strandAt_eq (i : I) (b : X) :
    (S.model.pull (strφ S i b).toColourMap).strandAt =
      ((S.toStrongSl2 i b).model.push (cmp B C i)).strandAt := by
  funext c x y hx hy
  obtain ⟨⟨e, u⟩, r⟩ := c
  cases e
  · exact (gRc_eq S i b _ _ _ _).symm
  · exact (gEc_eq S i b _ _ _ _).symm

/-! ## Equation lemmas for the generator images of the model -/

section EqLemmas

variable (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh dotDnQ crossDnQ adjL dotQ crossQ

theorem genImg_dot_true (i : I) (r a b : X) (ha hb hd hde hc hce) :
    (genImg (S := S) Sc).gen (.gen (.dot ⟨(true, i), r⟩)) a b ha hb hd hde hc hce =
      S.dotQ i (up_reg i hde hd.1) := rfl

theorem genImg_dot_false (i : I) (r a b : X) (ha hb hd hde hc hce) :
    (genImg (S := S) Sc).gen (.gen (.dot ⟨(false, i), r⟩)) a b ha hb hd hde hc hce =
      dotDnQ (S := S) i (dn_reg i hde hd.1) := rfl

theorem genImg_cross_true (i j : I) (ν a b : X) (ha hb hd) (hde : ν = b) (hc hce) :
    (genImg (S := S) Sc).gen (.gen (.cross true i j ν)) a b ha hb hd hde hc hce =
      S.crossQ i j (l := b) (n := sh RD ((true, j) : Letter I) + ν) (m := a)
        (n' := sh RD ((true, i) : Letter I) + ν) (by rw [← hde]; exact cross_up_reg j ν)
        (cross_up_reg' i j hd.1) (by rw [← hde]; exact cross_up_reg i ν)
        (cross_up_swap i j hd.1) := by
  subst hde; rfl

theorem genImg_cross_false (i j : I) (ν a b : X) (ha hb hd) (hde : ν = b) (hc hce) :
    (genImg (S := S) Sc).gen (.gen (.cross false i j ν)) a b ha hb hd hde hc hce =
      crossDnQ (S := S) Sc i j (a := a) (n := sh RD ((false, i) : Letter I) + ν)
        (n' := sh RD ((false, j) : Letter I) + ν) (b := b)
        (by rw [← hde]; exact cross_dn_reg j ν) (cross_dn_reg' i j hd.1)
        (by rw [← hde]; exact cross_dn_reg i ν) (cross_dn_swap i j hd.1) := by
  subst hde; rfl

theorem genImg_cup_true (i : I) (r a : X) (ha hb hd hc hce) :
    (genImg (S := S) Sc).gen (.cup ⟨(true, i), r⟩) a a ha hb hd rfl hc hce =
      (adjL (S := S) i (up_reg i rfl ha)).unit := rfl

theorem genImg_cup_false (i : I) (r a : X) (ha hb hd hc hce) :
    (genImg (S := S) Sc).gen (.cup ⟨(false, i), r⟩) a a ha hb hd rfl hc hce =
      (S.adjR i (dn_reg i rfl ha)).unit := rfl

theorem genImg_cap_true (i : I) (r a : X) (ha hb hd hde hc) :
    (genImg (S := S) Sc).gen (.cap ⟨(true, i), r⟩) a a ha hb hd hde hc rfl =
      (adjL (S := S) i (up_reg i hde rfl)).counit := rfl

theorem genImg_cap_false (i : I) (r a : X) (ha hb hd hde hc) :
    (genImg (S := S) Sc).gen (.cap ⟨(false, i), r⟩) a a ha hb hd hde hc rfl =
      (S.adjR i (dn_reg i hde rfl)).counit := rfl

end EqLemmas

/-! ## The pulled-back generator images -/

section PullGen

variable (Sc : CL.CLScalars C k)

attribute [local irreducible] KL3.Diagram.sh in
theorem StrongSl2_genImg_cross_false (T : StrongSl2 k B) (ν a b : ℤ) (ha hb hd)
    (hde : ν = b) (hc hce) :
    (StrongSl2.genImg T).gen (.gen (.cross false () () ν)) a b ha hb hd hde hc hce =
      StrongSl2.gCrossR T (T.qi a) (T.qi (sh sl2RootDatum ((false, ()) : Letter Unit) + ν))
        (T.qi b)
        (by
          obtain rfl : sh sl2RootDatum ((false, ()) : Letter Unit) +
            (sh sl2RootDatum ((false, ()) : Letter Unit) + ν) = a := hd.1
          exact T.qi_sh_false () _)
        (by rw [← hde]; exact T.qi_sh_false () ν) := by
  subst hde
  simp only [StrongSl2.genImg]
  congr 1

theorem pg_dot_false (i : I) (b : X) (hb : strBase RD i b = b) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.gen (.dot ⟨(false, u), r⟩)) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.gen (.dot ⟨(false, u), r⟩)) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  rw [StrongSl2.genImg_dot_false]
  erw [genImg_dot_false]
  exact (dotDnQ_heq (S := S) i b hb ((S.toStrongSl2 i b).qi a) ((S.toStrongSl2 i b).qi c) _
    _).symm

theorem pg_dot_true (i : I) (b : X) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.gen (.dot ⟨(true, u), r⟩)) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.gen (.dot ⟨(true, u), r⟩)) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  erw [genImg_dot_true, StrongSl2.genImg_dot_true]
  refine HEq.symm ?_
  exact dotQ_heq S i b _ _ _ _

theorem pg_cross_false (i : I) (b : X) (hb : strBase RD i b = b) (u u' : Unit) (ν a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.gen (.cross false u u' ν)) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.gen (.cross false u u' ν)) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hde
  erw [StrongSl2_genImg_cross_false _ _ _ _ _ _ _ rfl]
  erw [genImg_cross_false (S := S) Sc i i _ _ _ _ _ _ rfl]
  exact (crossDnQ_heq (S := S) Sc i b hb ((S.toStrongSl2 i b).qi a)
    ((S.toStrongSl2 i b).qi (sh sl2RootDatum ((false, ()) : Letter Unit) + ν))
    ((S.toStrongSl2 i b).qi ν) _ _
    ((StringEmbed.sh_sl RD i b (S.toStrongSl2 i b).qi (qi_two _) (false, ()) _).trans rfl) _ _).symm

theorem pg_cross_true (i : I) (b : X) (u u' : Unit) (ν a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.gen (.cross true u u' ν)) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.gen (.cross true u u' ν)) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hde
  erw [genImg_cross_true (S := S) Sc i i _ _ _ _ _ _ rfl, StrongSl2.genImg_cross_true]
  refine HEq.symm ?_
  exact crossQ_heq S i b _ _ _ _ _
    ((StringEmbed.sh_sl RD i b (S.toStrongSl2 i b).qi (qi_two _) (true, ()) _).trans rfl) _ _ _ _

theorem pg_cup_false (i : I) (b : X) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.cup ⟨(false, u), r⟩) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.cup ⟨(false, u), r⟩) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hde
  erw [genImg_cup_false, StrongSl2.genImg_cup_false]
  refine HEq.symm ?_
  exact (adjR_heqG (S := S) i b _ _ _ rfl rfl _).1

theorem pg_cup_true (i : I) (b : X) (hb : strBase RD i b = b) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.cup ⟨(true, u), r⟩) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.cup ⟨(true, u), r⟩) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hde
  erw [genImg_cup_true, StrongSl2.genImg_cup_true]
  refine HEq.symm ?_
  exact (adjL_heqG (S := S) i b hb _ _ _ rfl rfl _).1

theorem pg_cap_false (i : I) (b : X) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.cap ⟨(false, u), r⟩) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.cap ⟨(false, u), r⟩) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hce
  erw [genImg_cap_false, StrongSl2.genImg_cap_false]
  refine HEq.symm ?_
  exact (adjR_heqG (S := S) i b _ _ _ ((StringEmbed.sh_sl RD i b (S.toStrongSl2 i b).qi (qi_two _) (false, ()) _).trans rfl)
    rfl _).2

theorem pg_cap_true (i : I) (b : X) (hb : strBase RD i b = b) (u : Unit) (r a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen (.cap ⟨(true, u), r⟩) a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen (.cap ⟨(true, u), r⟩) a c ha hb' hd hde hc hce := by
  refine (heq_conj _ _ _).trans ?_
  simp only [GenImg.push]
  refine HEq.symm ((heq_conj _ _ _).trans ?_)
  subst hce
  erw [genImg_cap_true, StrongSl2.genImg_cap_true]
  refine HEq.symm ?_
  exact (adjL_heqG (S := S) i b hb _ _ _ rfl
    ((StringEmbed.sh_sl RD i b (S.toStrongSl2 i b).qi (qi_two _) (true, ()) _).trans rfl) _).2


/-- **The pulled-back generator images are those of the `sl₂` model.** -/
theorem pull_gen_heq (i : I) (b : X) (hb : strBase RD i b = b) (g : (psig sl2RootDatum).Gen)
    (a c : ℤ) (ha hb' hd hde hc hce) :
    ((genImg (S := S) Sc).pull (strφ S i b)).gen g a c ha hb' hd hde hc hce ≍
      ((StrongSl2.genImg (S.toStrongSl2 i b)).push (cmp B C i)).gen g a c ha hb' hd hde hc
        hce := by
  rcases g with (⟨⟨⟨e, u⟩, r⟩⟩ | ⟨e, u, u', ν⟩) | ⟨⟨e, u⟩, r⟩ | ⟨⟨e, u⟩, r⟩ <;> cases e
  · exact pg_dot_false (S := S) Sc i b hb u r a c ha hb' hd hde hc hce
  · exact pg_dot_true (S := S) Sc i b u r a c ha hb' hd hde hc hce
  · exact pg_cross_false (S := S) Sc i b hb u u' ν a c ha hb' hd hde hc hce
  · exact pg_cross_true (S := S) Sc i b u u' ν a c ha hb' hd hde hc hce
  · exact pg_cup_false (S := S) Sc i b u r a c ha hb' hd hde hc hce
  · exact pg_cup_true (S := S) Sc i b hb u r a c ha hb' hd hde hc hce
  · exact pg_cap_false (S := S) Sc i b u r a c ha hb' hd hde hc hce
  · exact pg_cap_true (S := S) Sc i b hb u r a c ha hb' hd hde hc hce

/-- **Transfer from the `sl₂` model**: a linear combination of diagrams of `U(sl₂)` killed by the
`sl₂` model of the restriction of `S` to the `α_i`-string through a base point `b` is, relabelled
along the string, killed by the model of `S`. -/
theorem killed_of_sl2 (i : I) (b : X) (hb : strBase RD i b = b) {μ : ℤ}
    {s t : List (Letter Unit)} (f : LinDiagram k (ob sl2RootDatum μ s) (ob sl2RootDatum μ t))
    (hst : KL3.Diagram.wt sl2RootDatum μ t = KL3.Diagram.wt sl2RootDatum μ s)
    (hf : (freeLift k (interp (StrongSl2.genImg (S.toStrongSl2 i b))
      (KL3.Diagram.wt sl2RootDatum μ s : ℤ) μ).functor).map f = 0) :
    (freeLift k (interp (genImg (S := S) Sc) (KL3.Diagram.wt RD (StringEmbed.sw RD i b
      (S.toStrongSl2 i b).qi μ) (s.map (StringEmbed.sl i)) : X)
      (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi μ : X)).functor).map
      (StringEmbed.Psi RD i b (S.toStrongSl2 i b).qi (qi_two _) f) = 0 := by
  have ha : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ s : ℤ) μ
      (ob sl2RootDatum μ s) :=
    ⟨ok_wd _ μ s, endR_wd _ μ s, rfl⟩
  have hb₂ : Cond (S := psig sl2RootDatum) (KL3.Diagram.wt sl2RootDatum μ s : ℤ) μ
      (ob sl2RootDatum μ t) := by
    refine ⟨?_, ?_, hst⟩
    · show (psig sl2RootDatum).ok _ (wd sl2RootDatum μ t)
      rw [← hst]; exact ok_wd _ μ t
    · show (psig sl2RootDatum).endR _ (wd sl2RootDatum μ t) = μ
      rw [← hst]; exact endR_wd _ μ t
  have h0 := freeLift_push_eq_zero (cmp B C i) (StrongSl2.genImg (S.toStrongSl2 i b))
    (fun x y => map_add (Regrade.compMap₂ _ _ _) x y)
    (fun r x => Regrade.comparison_map₂_smul _ k r x) ha hb₂ f hf
  have h1 := freeLift_eq_zero_of_strand_heq _ (pull_strandAt_eq i b) _ _
    (pull_gen_heq (S := S) Sc i b hb) _ _ f h0
  have h2 := freeLift_pull_eq_zero (strφ S i b) (genImg (S := S) Sc) ha hb₂ f h1
  exact freeLift_cast_eq_zero (genImg (S := S) Sc) (StringEmbed.wt_map RD i b _ (qi_two _) μ s) rfl
    _ _ _ h2

end PullGen

/-! ## The single-label relations -/

section Single

variable (Sc : CL.CLScalars C k)

theorem n₀_toStrongSl2 (i : I) (b : X) :
    (S.toStrongSl2 i b).n₀ = RD.pair (RD.iY i) b := rfl

/-- Every weight is the image of a region of the right parity along the string through its base
point. -/
theorem exists_string (i : I) (x : X) : ∃ (b : X) (n : ℤ), strBase RD i b = b ∧
    StringEmbed.sw RD i b (S.toStrongSl2 i b).qi n = x ∧
      ∃ q : ℤ, n = RD.pair (RD.iY i) b + 2 * q := by
  refine ⟨strBase RD i x, RD.pair (RD.iY i) (strBase RD i x) + 2 * strIdx RD i x,
    strBase_strBase i x, ?_, _, rfl⟩
  unfold StringEmbed.sw
  rw [← n₀_toStrongSl2 (S := S) i (strBase RD i x), qi_n₀]
  exact strBase_add_strIdx i x

theorem ip_sw (i : I) (b : X) {n : ℤ} (hn : ∃ q : ℤ, n = RD.pair (RD.iY i) b + 2 * q) :
    ip RD i (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi n) = n := by
  obtain ⟨q, rfl⟩ := hn
  unfold StringEmbed.sw
  rw [← n₀_toStrongSl2 (S := S) i b, qi_n₀, n₀_toStrongSl2 (S := S)]
  simp only [ip, map_add, map_zsmul, RD.pair_iY_iX_self, smul_eq_mul]
  ring

theorem par_wt {n₀ n : ℤ} (hn : ∃ q : ℤ, n = n₀ + 2 * q) :
    ∀ t : List (Letter Unit), ∃ q : ℤ, KL3.Diagram.wt sl2RootDatum n t = n₀ + 2 * q
  | [] => hn
  | ⟨e, u⟩ :: t => by
    obtain ⟨q, hq⟩ := par_wt hn t
    rw [KL3.Diagram.wt_cons, hq]
    cases e
    · exact ⟨q - 1, by rw [StringEmbed.sh_S2_false]; ring⟩
    · exact ⟨q + 1, by rw [StringEmbed.sh_S2_true]; ring⟩

theorem freeLift_regions_eq_zero {S' : Signature} {M : Model S' (GradedHomBicat B)}
    (G : GenImg M) {s₀ s₀' t₀ t₀' : S'.Region} (hs : s₀ = s₀') (ht : t₀ = t₀') {a b : Obj S'}
    (f : LinDiagram k a b) (hf : (freeLift k (interp G s₀ t₀).functor).map f = 0) :
    (freeLift k (interp G s₀' t₀').functor).map f = 0 := by
  subst hs ht; exact hf

/-- The transfer of a single relation from the `sl₂` model. -/
theorem killed_rel (i : I) (b : X) (hb : strBase RD i b = b) {μ : ℤ}
    {s t : List (Letter Unit)} (f₂ : LinDiagram k (ob sl2RootDatum μ s) (ob sl2RootDatum μ t))
    (f : LinDiagram k (ob RD (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi μ)
      (s.map (StringEmbed.sl i)))
      (ob RD (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi μ) (t.map (StringEmbed.sl i))))
    (hΨ : StringEmbed.Psi RD i b (S.toStrongSl2 i b).qi (qi_two _) f₂ = f)
    (hst : KL3.Diagram.wt sl2RootDatum μ t = KL3.Diagram.wt sl2RootDatum μ s)
    (hf₂ : (freeLift k (interp (StrongSl2.genImg (S.toStrongSl2 i b))
      (ob sl2RootDatum μ s).start (ob sl2RootDatum μ s).endR).functor).map f₂ = 0) :
    (freeLift k (interp (genImg (S := S) Sc)
      (ob RD (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi μ)
        (s.map (StringEmbed.sl i))).start
      (ob RD (StringEmbed.sw RD i b (S.toStrongSl2 i b).qi μ)
        (s.map (StringEmbed.sl i))).endR).functor).map f = 0 := by
  subst hΨ
  have h := killed_of_sl2 (S := S) Sc i b hb f₂ hst
    (freeLift_regions_eq_zero _ rfl (endR_wd _ μ s) f₂ hf₂)
  exact freeLift_regions_eq_zero _ rfl (endR_wd _ _ _).symm _ h

end Single

section SingleRel

variable (Sc : CL.CLScalars C k)

theorem killed_cycDotR (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cycDotR i μ : Rel RD)).start
      (Rel.dom (.cycDotR i μ : Rel RD)).endR).functor).map (relation k (.cycDotR i μ : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.cycDotR () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cycDotR RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cycDotR () n : Rel sl2RootDatum))
      (par_wt hn [dn ()]))

theorem killed_cycDotL (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cycDotL i μ : Rel RD)).start
      (Rel.dom (.cycDotL i μ : Rel RD)).endR).functor).map (relation k (.cycDotL i μ : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.cycDotL () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cycDotL RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cycDotL () n : Rel sl2RootDatum))
      (par_wt hn [dn ()]))

theorem killed_cycCrossR (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cycCrossR i i μ : Rel RD)).start
      (Rel.dom (.cycCrossR i i μ : Rel RD)).endR).functor).map (relation k (.cycCrossR i i μ : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.cycCrossR () () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cycCrossR RD i b (S.toStrongSl2 i b).qi (qi_two _) k () () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cycCrossR () () n : Rel sl2RootDatum))
      (par_wt hn [dn (), dn ()]))

theorem killed_cycCrossL (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cycCrossL i i μ : Rel RD)).start
      (Rel.dom (.cycCrossL i i μ : Rel RD)).endR).functor).map (relation k (.cycCrossL i i μ : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.cycCrossL () () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cycCrossL RD i b (S.toStrongSl2 i b).qi (qi_two _) k () () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cycCrossL () () n : Rel sl2RootDatum))
      (par_wt hn [dn (), dn ()]))

theorem killed_curlR (i : I) (lam : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.curlR i lam : Rel RD)).start
      (Rel.dom (.curlR i lam : Rel RD)).endR).functor).map (relation k (.curlR i lam : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  exact killed_rel (S := S) Sc i b hb (relation k (.curlR () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_curlR RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n (ip_sw i b hn)) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.curlR () n : Rel sl2RootDatum))
      (par_wt hn [up ()]))

theorem killed_curlL (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.curlL i μ : Rel RD)).start
      (Rel.dom (.curlL i μ : Rel RD)).endR).functor).map (relation k (.curlL i μ : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.curlL () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_curlL RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n (ip_sw i b (par_wt hn [up ()]))) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.curlL () n : Rel sl2RootDatum))
      (par_wt hn [up ()]))

theorem killed_decompEF (i : I) (lam : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.decompEF i lam : Rel RD)).start
      (Rel.dom (.decompEF i lam : Rel RD)).endR).functor).map (relation k (.decompEF i lam : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  exact killed_rel (S := S) Sc i b hb (relation k (.decompEF () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_decompEF RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n (ip_sw i b hn)) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.decompEF () n : Rel sl2RootDatum))
      (par_wt hn [up (), dn ()]))

theorem killed_decompFE (i : I) (lam : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.decompFE i lam : Rel RD)).start
      (Rel.dom (.decompFE i lam : Rel RD)).endR).functor).map (relation k (.decompFE i lam : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  exact killed_rel (S := S) Sc i b hb (relation k (.decompFE () n : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_decompFE RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n (ip_sw i b hn)) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.decompFE () n : Rel sl2RootDatum))
      (par_wt hn [dn (), up ()]))

theorem killed_cwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < ip RD i lam - 1) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cwNeg i lam α h : Rel RD)).start
      (Rel.dom (.cwNeg i lam α h : Rel RD)).endR).functor).map (relation k (.cwNeg i lam α h : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  have h₂ : (α : ℤ) < ip sl2RootDatum () n - 1 := by
    rw [StringEmbed.ip_S2]; rw [ip_sw i b hn] at h; exact h
  exact killed_rel (S := S) Sc i b hb (relation k (.cwNeg () n α h₂ : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cwNeg RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n α h₂ h) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cwNeg () n α h₂ : Rel sl2RootDatum))
      (par_wt hn []))

theorem killed_ccwNeg (i : I) (lam : X) (α : ℕ) (h : (α : ℤ) < -ip RD i lam - 1) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.ccwNeg i lam α h : Rel RD)).start
      (Rel.dom (.ccwNeg i lam α h : Rel RD)).endR).functor).map (relation k (.ccwNeg i lam α h : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  have h₂ : (α : ℤ) < -ip sl2RootDatum () n - 1 := by
    rw [StringEmbed.ip_S2]; rw [ip_sw i b hn] at h; exact h
  exact killed_rel (S := S) Sc i b hb (relation k (.ccwNeg () n α h₂ : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_ccwNeg RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n α h₂ h) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.ccwNeg () n α h₂ : Rel sl2RootDatum))
      (par_wt hn []))

theorem killed_cwOne (i : I) (lam : X) (h : 1 ≤ ip RD i lam) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.cwOne i lam h : Rel RD)).start
      (Rel.dom (.cwOne i lam h : Rel RD)).endR).functor).map (relation k (.cwOne i lam h : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  have h₂ : 1 ≤ ip sl2RootDatum () n := by
    rw [StringEmbed.ip_S2]; rw [ip_sw i b hn] at h; exact h
  exact killed_rel (S := S) Sc i b hb (relation k (.cwOne () n h₂ : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_cwOne RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n h₂ h (ip_sw i b hn)) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.cwOne () n h₂ : Rel sl2RootDatum))
      (par_wt hn []))

theorem killed_ccwOne (i : I) (lam : X) (h : ip RD i lam ≤ -1) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.ccwOne i lam h : Rel RD)).start
      (Rel.dom (.ccwOne i lam h : Rel RD)).endR).functor).map (relation k (.ccwOne i lam h : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i lam
  have h₂ : ip sl2RootDatum () n ≤ -1 := by
    rw [StringEmbed.ip_S2]; rw [ip_sw i b hn] at h; exact h
  exact killed_rel (S := S) Sc i b hb (relation k (.ccwOne () n h₂ : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_ccwOne RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n h₂ h (ip_sw i b hn)) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.ccwOne () n h₂ : Rel sl2RootDatum))
      (par_wt hn []))

theorem killed_klr_sqEq (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.sqEq i) : Rel RD)).start
      (Rel.dom (.klr μ (.sqEq i) : Rel RD)).endR).functor).map (relation k (.klr μ (.sqEq i) : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.klr n (.sqEq ()) : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_klr_sqEq RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.klr n (.sqEq ()) : Rel sl2RootDatum))
      (par_wt hn [up (), up ()]))

theorem killed_klr_slideLEq (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.slideLEq i) : Rel RD)).start
      (Rel.dom (.klr μ (.slideLEq i) : Rel RD)).endR).functor).map (relation k (.klr μ (.slideLEq i) : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.klr n (.slideLEq ()) : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_klr_slideLEq RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.klr n (.slideLEq ()) : Rel sl2RootDatum))
      (par_wt hn [up (), up ()]))

theorem killed_klr_slideREq (i : I) (μ : X) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.slideREq i) : Rel RD)).start
      (Rel.dom (.klr μ (.slideREq i) : Rel RD)).endR).functor).map (relation k (.klr μ (.slideREq i) : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.klr n (.slideREq ()) : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_klr_slideREq RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.klr n (.slideREq ()) : Rel sl2RootDatum))
      (par_wt hn [up (), up ()]))

theorem killed_klr_braid (i : I) (μ : X) (h : ¬ (i = i ∧ i ≠ i)) :
    (freeLift k (interp (genImg (S := S) Sc) (Rel.dom (.klr μ (.braid i i i h) : Rel RD)).start
      (Rel.dom (.klr μ (.braid i i i h) : Rel RD)).endR).functor).map (relation k (.klr μ (.braid i i i h) : Rel RD)) = 0 := by
  obtain ⟨b, n, hb, rfl, hn⟩ := exists_string (S := S) i μ
  exact killed_rel (S := S) Sc i b hb (relation k (.klr n (.braid () () () (fun h' => h'.2 rfl)) : Rel sl2RootDatum)) _
    (StringEmbed.Ψ_rel_klr_braid RD i b (S.toStrongSl2 i b).qi (qi_two _) k () n _ h) rfl
    (StrongSl2.relations_killed (S.toStrongSl2 i b) (.inr (.klr n (.braid () () () (fun h' => h'.2 rfl)) : Rel sl2RootDatum))
      (par_wt hn [up (), up (), up ()]))

end SingleRel

end QStrong

end Model

end Categorification.TwoRep
