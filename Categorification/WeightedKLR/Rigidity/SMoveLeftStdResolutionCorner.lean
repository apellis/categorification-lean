/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroFixed

/-!
# The diagonal corner of `SMove.leftStd` along a standard resolution

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. Let `s` be the diagonal loading
of the three red strands, `s = t λ_3 ∅` (every black strand left of the last red strand). For a
standard layer `S(M)` of a split `θ + β = ν` at `λ_3` with `β ≠ 0`, `SMove.leftStd S(M)` is the
standard layer of the split `(0 + θ) + β` (`SMove.leftStdStdLayerIso`), killed by `e(s)` since
`ν ≰ θ` (`loadingIdem_smul_stdLayerModule_eq_zero`). So `e(s)` kills `SMove.leftStd` of every
term `M_n`, `n ≥ 1`, of a resolution as in Proposition 7.8 (`exists_stdResolution`), hence of
the kernel of `M_0 → L`, and since `SMove.leftStd` is exact,

  `dim e(s) SMove.leftStd M_0 = dim e(s) SMove.leftStd L`

(`SMove.finrank_fixSub_leftStd_stdResolution_zero`). No route hypotheses beyond those of the
resolution (supplied as data).

## Main results

* `ModuleExactFunctor.smul_obj_eq_zero_of_surjective`, `smul_obj_pi_eq_zero`,
  `smul_obj_eq_zero_of_isZero`: the elements of the target ring killing `F X` (generic).
* `SMove.seqIdem_smul_leftStd_stdLayerModule_eq_zero`.
* `SMove.finrank_fixSub_leftStd_stdResolution_zero`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Limits KLR Equiv BraidedStendhalAlgebra

section Generic

variable {R S : Type} [Ring R] [Ring S] (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S)

/-- If `a` kills `F Y` and `F g : F Y → F Z` is surjective, then `a` kills `F Z`. -/
theorem smul_obj_eq_zero_of_surjective {Y Z : ModuleCat.{0} R} (g : Y ⟶ Z)
    (hg : Function.Surjective (F.map g).hom) (a : S) (h : ∀ y : F.obj Y, a • y = 0)
    (z : F.obj Z) : a • z = 0 := by
  obtain ⟨y, rfl⟩ := hg z
  rw [← (F.map g).hom.map_smul, h y, map_zero]

/-- An additive functor sends a zero object to a module killed by everything. -/
theorem smul_obj_eq_zero_of_isZero [F.Additive] {X : ModuleCat.{0} R} (hX : IsZero X) (a : S)
    (x : F.obj X) : a • x = 0 := by
  have : Subsingleton (F.obj X) := ModuleCat.subsingleton_of_isZero (F.map_isZero hX)
  exact Subsingleton.elim _ _

/-- If `a` kills `F M_i` for every `i`, then `a` kills `F (∏ M_i)`, `F` additive. -/
theorem smul_obj_pi_eq_zero [F.Additive] {J : Type} [Fintype J] (M : J → ModuleCat.{0} R)
    (a : S) (h : ∀ i (y : F.obj (M i)), a • y = 0)
    (x : F.obj (ModuleCat.of R (∀ i, M i))) : a • x = 0 := by
  classical
  let ι : ∀ i, M i ⟶ ModuleCat.of R (∀ i, M i) := fun i =>
    ModuleCat.ofHom (LinearMap.single R (fun i => M i) i)
  let p : ∀ i, ModuleCat.of R (∀ i, M i) ⟶ M i := fun i =>
    ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun i => M i) i)
  have hid : ∑ i, p i ≫ ι i = 𝟙 (ModuleCat.of R (∀ i, M i)) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
    change (∑ i, p i ≫ ι i).hom f = f
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    exact Finset.univ_sum_single f
  have hx : x = ∑ i, (F.map (ι i)).hom ((F.map (p i)).hom x) := by
    conv_lhs => rw [← (show (F.map (𝟙 _)).hom x = x by rw [F.map_id]; rfl), ← hid]
    rw [F.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    simp only [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hx, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← (F.map (ι i)).hom.map_smul, h i, map_zero]

/-- **Corners along a surjection with killed kernel**: if `g : M → M'` is `A`-linear and
surjective, `f` is idempotent and `f x = 0` whenever `g x = 0`, then `g` restricts to an
isomorphism `f M ≅ f M'` of `k`-spaces. -/
theorem finrank_fixSub_eq_of_surjective {A : Type*} [Ring A] (k : Type*) [CommRing k]
    [Algebra k A] {M M' : Type*} [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [AddCommGroup M'] [Module A M'] [Module k M'] [IsScalarTower k A M']
    (g : M →ₗ[A] M') (hg : Function.Surjective g) {f : A} (hf : IsIdempotentElem f)
    (hker : ∀ x, g x = 0 → f • x = 0) :
    Module.finrank k (fixSub k M f) = Module.finrank k (fixSub k M' f) := by
  let φ : fixSub k M f →ₗ[k] fixSub k M' f :=
    { toFun := fun x => ⟨g x.1, by rw [mem_fixSub, ← g.map_smul, mem_fixSub.mp x.2]⟩
      map_add' := fun x y => Subtype.ext (g.map_add x.1 y.1)
      map_smul' := fun c x => Subtype.ext (g.map_smul_of_tower c x.1) }
  refine (LinearEquiv.ofBijective φ ⟨fun x y hxy => ?_, fun z => ?_⟩).finrank_eq
  · have h0 : g (x.1 - y.1) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Subtype.val hxy
    have h1 := hker _ h0
    rw [smul_sub, mem_fixSub.mp x.2, mem_fixSub.mp y.2, sub_eq_zero] at h1
    exact Subtype.ext h1
  · obtain ⟨x, hx⟩ := hg z.1
    refine ⟨⟨f • x, smul_mem_fixSub hf x⟩, Subtype.ext ?_⟩
    change g (f • x) = z.1
    rw [g.map_smul, hx, mem_fixSub.mp z.2]

end Generic

namespace SMove

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}

local notation "Λ₂₃" => (Λ ∘ Fin.natAdd 1 : Fin (1 + 1) → I →₀ ℕ)
local notation "Λ₃" => (Λ ∘ Fin.cast (Nat.add_assoc 1 1 1) : Fin (1 + 1 + 1) → I →₀ ℕ)

/-- The diagonal loading `t λ_3 ∅` of the three red strands, for a loading `t` of the first
two red strands carrying all of `ν`. -/
abbrev diagonalTwoPiece (d : {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t}) :
    {t : Seq (stendhalWeight (1 + 1 + 1) ν) // IsRedOrdered t} :=
  twoPieceLabel (add_zero ν) (default : Seq (0 : Multiset I)) d

/-- **`e(s)` kills `SMove.leftStd` of a standard layer with a black strand on the last red
strand** (Webster, arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): for a standard layer
`c` at `λ_3` of `T^{λ_2, λ_3}(ν)` with `|θ| < |ν|` and the diagonal loading `s = t λ_3 ∅`,
`e(s)` is zero on `SMove.leftStd S(c)`. -/
theorem seqIdem_smul_leftStd_stdLayerModule_eq_zero (c : StdLayer Q Λ₂₃ ν)
    (hc : Multiset.card c.θ < Multiset.card ν)
    (d : {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t})
    (x : (leftStd Q hQ Λ ν).obj (stdLayerModule Q Λ₂₃ hQ c)) :
    seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2 • x = 0 := by
  obtain ⟨θ, β, h, M⟩ := c
  subst h
  let e := leftStdStdLayerIso Q hQ Λ M
  have hn : ¬ (θ + β) ≤ 0 + θ := fun hle => by
    have := Multiset.card_le_card hle
    simp only [zero_add] at this
    exact absurd hc (not_lt.mpr this)
  have h0 := loadingIdem_smul_stdLayerModule_eq_zero (ℓ := 1 + 1) Q Λ₃ hQ _ (add_zero (θ + β))
    hn d.2 (default : Seq (0 : Multiset I)) (diagonalTwoPiece d).2 (e.hom.hom x)
  have hx : x = e.inv.hom (e.hom.hom x) := by
    change x = (e.hom ≫ e.inv).hom x
    rw [e.hom_inv_id]
    rfl
  rw [hx]
  exact ((e.inv.hom.map_smul _ _).symm.trans (congrArg e.inv.hom h0)).trans (map_zero _)

/-- `e(s)` kills `SMove.leftStd` of a sum of standard layers at a position `q + 1`, `q < |ν|`. -/
theorem seqIdem_smul_leftStd_stdSum_eq_zero {q : ℕ} (hq : q < Multiset.card ν)
    (X : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν)) (hX : StdSum Q Λ₂₃ hQ (q + 1) X)
    (d : {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t})
    (x : (leftStd Q hQ Λ ν).obj X) :
    seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2 • x = 0 := by
  obtain ⟨J, _, c, hcq, -, ⟨eX⟩⟩ := hX
  refine smul_obj_eq_zero_of_surjective (leftStd Q hQ Λ ν) eX.inv ?_ _ ?_ x
  · exact (moduleExactFunctor_leftStd Q hQ Λ ν).surjective _
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · refine smul_obj_pi_eq_zero (leftStd Q hQ Λ ν) (fun i => stdLayerModule Q Λ₂₃ hQ (c i)) _
      fun i y => seqIdem_smul_leftStd_stdLayerModule_eq_zero Q hQ Λ (c i) ?_ d y
    have := hcq i
    omega

variable {L : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)}
  (S : ℕ → ShortComplex (ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) ν)))
  (h0 : Nonempty ((S 0).X₃ ≅ L)) (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁))
  (hS : ∀ n, (S n).ShortExact)
  (hstd : ∀ n ≤ Multiset.card ν,
    StdSum Q (Λ ∘ Fin.natAdd 1) hQ (Multiset.card ν + 1 - n) (S n).X₂)
  (hz : ∀ n, Multiset.card ν < n → IsZero (S n).X₂)

include hs hS hstd hz in
/-- `e(s)` kills `SMove.leftStd` of the kernel `(S 0).X₁ ≅ (S 1).X₃` of `M_0 → L`. -/
theorem seqIdem_smul_leftStd_stdResolution_one_eq_zero
    (d : {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t})
    (x : (leftStd Q hQ Λ ν).obj (S 0).X₁) :
    seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2 • x = 0 := by
  have hex := moduleExactFunctor_leftStd Q hQ Λ ν
  have h₂ : ∀ y : (leftStd Q hQ Λ ν).obj (S 1).X₂,
      seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2 • y = 0 := by
    by_cases hn : 1 ≤ Multiset.card ν
    · have hX := hstd 1 hn
      rw [show Multiset.card ν + 1 - 1 = (Multiset.card ν - 1) + 1 by omega] at hX
      exact seqIdem_smul_leftStd_stdSum_eq_zero Q hQ Λ (by omega) _ hX d
    · exact smul_obj_eq_zero_of_isZero (leftStd Q hQ Λ ν) (hz 1 (by omega)) _
  have h₃ := smul_obj_eq_zero_of_surjective (leftStd Q hQ Λ ν) (S 1).g
    (hex.surjective _ ((ModuleCat.epi_iff_surjective _).mp (hS 1).epi_g)) _ h₂
  obtain ⟨e⟩ := hs 0
  exact smul_obj_eq_zero_of_surjective (leftStd Q hQ Λ ν) e.hom
    (hex.surjective _ ((ModuleCat.epi_iff_surjective _).mp inferInstance)) _ h₃ x

include h0 hs hS hstd hz in
/-- **The diagonal corner of `SMove.leftStd M_0` is that of `SMove.leftStd L`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22, `Tor₀` of the diagonal pair): for a
resolution of `L` as in Proposition 7.8 (the data of `exists_stdResolution`) and the diagonal
loading `s = t λ_3 ∅`, `dim e(s) SMove.leftStd M_0 = dim e(s) SMove.leftStd L`. -/
theorem finrank_fixSub_leftStd_stdResolution_zero
    (d : {t : Seq (stendhalWeight (1 + 1) ν) // IsRedOrdered t}) :
    Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj (S 0).X₂)
        (seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2)) =
      Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj L)
        (seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2)) := by
  have hex := moduleExactFunctor_leftStd Q hQ Λ ν
  have hidem : IsIdempotentElem (seqIdem Q Λ (diagonalTwoPiece d).1 (diagonalTwoPiece d).2) :=
    seqIdem_mul_self Q Λ _ _
  obtain ⟨eL⟩ := h0
  refine (finrank_fixSub_eq_of_surjective k ((leftStd Q hQ Λ ν).map (S 0).g).hom
    (hex.surjective _ ((ModuleCat.epi_iff_surjective _).mp (hS 0).epi_g)) hidem
    fun x hx => ?_).trans (finrank_fixSub_eq_of_surjective k ((leftStd Q hQ Λ ν).map eL.hom).hom
    (hex.surjective _ ((ModuleCat.epi_iff_surjective _).mp inferInstance)) hidem
    fun x hx => ?_)
  · obtain ⟨y, rfl⟩ := (hex.exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      _).mp (hS 0).exact) x).mp hx
    rw [← ((leftStd Q hQ Λ ν).map (S 0).f).hom.map_smul,
      seqIdem_smul_leftStd_stdResolution_one_eq_zero Q hQ Λ S hs hS hstd hz d y, map_zero]
  · have hinj := hex.injective eL.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
    rw [show x = 0 from hinj (hx.trans (map_zero _).symm), smul_zero]

end SMove

end Categorification.Stendhal
