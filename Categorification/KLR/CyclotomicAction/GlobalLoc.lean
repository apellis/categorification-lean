/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.KangKashiwara
import Categorification.KLR.CyclotomicAction.GlobalSlides
import Categorification.TwoRep.SumInvPointwise

/-!
# Rouquier's local data on weight spaces

Rouquier's local data (`TwoRep.RouqLoc`, Brundan, arXiv:1501.00350v1, (1.8), (1.9)) for the
weight-indexed cyclotomic Rouquier family of KL III Thm. 1.2, at a weight `y` with Brundan weight
`⟨h_i, y⟩`: `globalLoc`. This is Kang–Kashiwara's Theorem 5.2 (arXiv:1102.4677v4, §4.2, §5)
assembled over the blocks of the weight space.

The rightward crossing, the dotted caps and the dotted cups at a weight space are block diagonal:
on a block `β`, they are the corresponding maps for the cyclotomic induction and restriction
functors of `β`, through the generators of the composites `F_i E_i` and `E_i F_i` (`sigma_app`,
`capD_app`, `cupD_app`). These generators are isomorphisms, as each block of `F_i E_i` and
`E_i F_i` has at most one summand. On a block `β = {i} + γ`, the inverses come from
`blockLoc`. On a block without a strand of colour `i`, `F_i E_i` vanishes and `⟨h_i, y⟩ ≤ 0`
(as `Λ` is dominant), and the inverses come from Kang–Kashiwara's dotted units `blockBoundary`.
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {A : Type w₁} {Dd : Type w₂} (s : A → Dd)
  {C : A → Type u₁} [∀ a, Category.{v₁} (C a)] {D : Dd → Type u₂} [∀ d, Category.{v₂} (D d)]
  [∀ d, Finite {a // s a = d}] [∀ d, Preadditive (D d)] [∀ d, HasFiniteBiproducts (D d)]

/-- Powers of a blockwise transformation on the generators of a block sum. -/
theorem blockι_powComp_blockSumMap {L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d}
    (α : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⟶ L a d h) (M : ∀ a, C a) {d : Dd}
    (p : {a // s a = d}) (n : ℕ) :
    blockι s L M p ≫ (powComp (blockSumMap s α) n).app M d =
      (powComp (α p.1 d p.2) n).app (M p.1) ≫ blockι s L M p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [powComp_succ, powComp_succ, NatTrans.comp_app, NatTrans.comp_app]
    change blockι s L M p ≫ (powComp (blockSumMap s α) n).app M d ≫ (blockSumMap s α).app M d = _
    rw [← Category.assoc, ih, Category.assoc, blockι_blockSumMap, Category.assoc]

theorem AdditiveCat.powComp_hom {A B : AdditiveCat} {F : A ⟶ B} (η : F ⟶ F) (n : ℕ) :
    (powComp η n).hom = powComp η.hom n :=
  map_powComp (ObjectProperty.ι _) η n

section Single

variable (L : ∀ (a : A) (d : Dd), s a = d → C a ⥤ D d)

/-- On a block with a single summand, the generator of the block sum is an isomorphism. -/
@[simps]
noncomputable def blockιIso (M : ∀ a, C a) {d : Dd} (p : {a // s a = d}) (hp : ∀ q, q = p) :
    (L p.1 d p.2).obj (M p.1) ≅ (blockSum s L).obj M d where
  hom := blockι s L M p
  inv := biproduct.π (fun q : {a // s a = d} => (L q.1 d q.2).obj (M q.1)) p
  hom_inv_id := biproduct.ι_π_self _ _
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun q => ?_
    obtain rfl := hp q
    simp

/-- Evaluation of the 1-cells `C ⟶ D` of `AdditiveCat` at an object of `C`. -/
def AdditiveCat.homEval {C D : AdditiveCat.{v₁, u₁}} (M : C) : (C ⟶ D) ⥤ D :=
  AdditiveFunctor.forget C D ⋙ (evaluation C D).obj M

@[simp] theorem AdditiveCat.homEval_map {C D : AdditiveCat.{v₁, u₁}} (M : C) {F G : C ⟶ D}
    (η : F ⟶ G) : (AdditiveCat.homEval M).map η = η.hom.app M := rfl

/-- A block with no summands is zero. -/
theorem blockSum_obj_isZero (M : ∀ a, C a) {d : Dd} (hd : IsEmpty {a // s a = d}) :
    IsZero ((blockSum s L).obj M d) := by
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun q => isEmptyElim q

end Single

end Categorification.TwoRep

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory TwoRep QuantumGroup
  KLRAlgebra.AbsentColour

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)

/-- **The dotted cups on weight spaces, blockwise.** -/
theorem cupD_app (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) (m : ℕ) :
    ((globalAdj.{u, v, w} Q a RD Λ i h).unit ≫
        powComp (globalDot Q a RD Λ i h) m ▷ globalF Q a RD Λ i h).hom.app M β =
      ((adjA.{u, v, w} Q a i (blockSucc_step RD Λ i h β)).unit ≫
          powComp (dotA Q a i (blockSucc_step RD Λ i h β)) m ▷
            resA Q a i (blockSucc_step RD Λ i h β)).hom.app (M β) ≫
        (resBlock Q a RD Λ i h β _ rfl).map
          (blockι (blockSucc RD Λ i h) (indBlock Q a RD Λ i h) M ⟨β, rfl⟩) := by
  change (indResAdj Q a i (blockSucc_step RD Λ i h β)).unit.app (M β) ≫
      (resBlock Q a RD Λ i h β _ rfl).map
        (blockι (blockSucc RD Λ i h) (indBlock Q a RD Λ i h) M ⟨β, rfl⟩) ≫
      (resBlock Q a RD Λ i h β _ rfl).map
        ((powComp (globalDot Q a RD Λ i h) m).hom.app M (blockSucc RD Λ i h β)) =
    ((indResAdj Q a i (blockSucc_step RD Λ i h β)).unit.app (M β) ≫
      (res Q a i (blockSucc_step RD Λ i h β)).map
        ((powComp (dotA Q a i (blockSucc_step RD Λ i h β)) m).hom.app (M β))) ≫
      (resBlock Q a RD Λ i h β _ rfl).map
        (blockι (blockSucc RD Λ i h) (indBlock Q a RD Λ i h) M ⟨β, rfl⟩)
  rw [LinearCat.powComp_hom, AdditiveCat.powComp_hom, Category.assoc]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ i h)
    (fun _ _ hβ => dot Q a i (blockSucc_eq RD Λ i hβ)) M ⟨β, rfl⟩ m
  exact congrArg (_ ≫ ·) (((resBlock Q a RD Λ i h β _ rfl).map_comp _ _).symm.trans
    ((congrArg (resBlock Q a RD Λ i h β _ rfl).map key).trans
      ((resBlock Q a RD Λ i h β _ rfl).map_comp _ _)))

/-- **The dotted caps on weight spaces, blockwise**, on the generator of `F_i E_i` at the block
`{i} + γ`. -/
theorem capD_app (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) (m : ℕ) :
    blockι (blockSucc RD Λ i h) (indBlock Q a RD Λ i h) ((globalF Q a RD Λ i h).obj.obj M)
        ⟨γ, rfl⟩ ≫
      (globalF.{u, v, w} Q a RD Λ i h ◁ powComp (globalDot Q a RD Λ i h) m ≫
        (globalAdj Q a RD Λ i h).counit).hom.app M (blockSucc RD Λ i h γ) =
      (resA.{u, v, w} Q a i (blockSucc_step RD Λ i h γ) ◁
          powComp (dotA Q a i (blockSucc_step RD Λ i h γ)) m ≫
        (adjA Q a i (blockSucc_step RD Λ i h γ)).counit).hom.app (M (blockSucc RD Λ i h γ)) := by
  change _ ≫ (powComp (globalDot Q a RD Λ i h) m).hom.app ((globalF Q a RD Λ i h).obj.obj M)
      (blockSucc RD Λ i h γ) ≫ biproduct.desc _ =
    (powComp (dotA Q a i (blockSucc_step RD Λ i h γ)) m).hom.app _ ≫
      (indResAdj Q a i (blockSucc_step RD Λ i h γ)).counit.app (M (blockSucc RD Λ i h γ))
  rw [LinearCat.powComp_hom, AdditiveCat.powComp_hom]
  have key := blockι_powComp_blockSumMap (blockSucc RD Λ i h)
    (fun _ _ hβ => dot Q a i (blockSucc_eq RD Λ i hβ)) ((globalF Q a RD Λ i h).obj.obj M)
    ⟨γ, rfl⟩ m
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (biproduct.ι_desc _ _))))

/-- The generator of `E_i E_i` on `F_i E_i` followed by the counit. -/
theorem gen₂_counit (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    Eq (gen₂ (b := blockSucc RD Λ i h₁ γ) (d := blockSucc RD Λ i h₂ (blockSucc RD Λ i h₁ γ))
        (blockSucc RD Λ i h₁) (blockSucc RD Λ i h₂) (indBlock.{u, v, w} Q a RD Λ i h₁)
        (indBlock Q a RD Λ i h₂) ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M)
        γ rfl rfl ≫
      (blockSum (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂)).map
        ((blockCounitNat (blockSucc RD Λ i h₁)
          (fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))).app M)
        (blockSucc RD Λ i h₂ (blockSucc RD Λ i h₁ γ)))
      ((indBlock Q a RD Λ i h₂ (blockSucc RD Λ i h₁ γ)
          (blockSucc RD Λ i h₂ (blockSucc RD Λ i h₁ γ)) rfl).map
          ((indResAdj Q a i (blockSucc_step RD Λ i h₁ γ)).counit.app
            (M (blockSucc RD Λ i h₁ γ))) ≫
        blockι (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂) M ⟨blockSucc RD Λ i h₁ γ, rfl⟩) := by
  rw [gen₂, Category.assoc, blockι_map, ← Category.assoc, ← Functor.map_comp]
  congr 2
  exact biproduct.ι_desc _ _

/-- **The rightward crossing on weight spaces, blockwise**: on the generator of `F_i E_i` at the
block `{i} + γ`, it is the rightward crossing of the cyclotomic block functors at `{i} + γ`,
followed by the generator of `E_i F_i`. -/
theorem sigma_app (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    Eq (blockι (blockSucc RD Λ i h₁) (indBlock.{u, v, w} Q a RD Λ i h₁)
        ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M) ⟨γ, rfl⟩ ≫
      (RightwardCrossing.sigma (globalAdj Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M
        (blockSucc RD Λ i h₁ γ))
      ((RightwardCrossing.sigma (adjA Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).unit
          (sameCrossA Q a i (blockSucc_step RD Λ i h₁ γ)
            (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ)))
          (adjA Q a i (blockSucc_step RD Λ i h₁ γ)).counit).hom.app (M (blockSucc RD Λ i h₁ γ)) ≫
        (resBlock Q a RD Λ i h₂ (blockSucc RD Λ i h₁ γ) _ rfl).map
          (blockι (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂) M ⟨blockSucc RD Λ i h₁ γ, rfl⟩)) := by
  rw [LinearCat.sigma_hom, AdditiveCat.sigma_hom]
  have hU := (indResAdj.{u, v, w} Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).unit_naturality
    (blockι (blockSucc RD Λ i h₁) (indBlock.{u, v, w} Q a RD Λ i h₁)
        ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M) ⟨γ, rfl⟩)
  have hT := gen₂_globalCross Q a RD Λ i i h₁ h₂ h₁ h₂
    ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M) γ rfl rfl rfl rfl
  have hC := gen₂_counit Q a RD Λ i h₁ h₂ M γ
  rw [signedCross_self] at hT
  have key := (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hT).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))))
  change blockι (blockSucc RD Λ i h₁) (indBlock.{u, v, w} Q a RD Λ i h₁)
        ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M) ⟨γ, rfl⟩ ≫
      (((indResAdj.{u, v, w} Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).unit.app
          ((blockSum (blockSucc RD Λ i h₁) (indBlock Q a RD Λ i h₁)).obj
            ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M) (blockSucc RD Λ i h₁ γ)) ≫
        (res Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).map
          (blockι (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂)
            ((blockSum (blockSucc RD Λ i h₁) (indBlock Q a RD Λ i h₁)).obj
              ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M))
            ⟨blockSucc RD Λ i h₁ γ, rfl⟩)) ≫
        (res Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).map
          ((globalCross Q a RD Λ i i h₁ h₂ h₁ h₂).hom.app
            ((blockRes (blockSucc RD Λ i h₁) (resBlock Q a RD Λ i h₁)).obj M)
            (blockSucc RD Λ i h₂ (blockSucc RD Λ i h₁ γ)))) ≫
      (res Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).map
        ((blockSum (blockSucc RD Λ i h₂) (indBlock Q a RD Λ i h₂)).map
          ((blockCounitNat (blockSucc RD Λ i h₁)
            (fun _ _ hβ => indResAdj.{u, v, w} Q a i (blockSucc_eq RD Λ i hβ))).app M)
          (blockSucc RD Λ i h₂ (blockSucc RD Λ i h₁ γ))) = _
  simp only [Category.assoc]
  erw [← reassoc_of% hU]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  have key' := congrArg (res Q a i (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).map key
  erw [key']
  simp only [Functor.map_comp]
  rfl


/-- The blocks of weight `y` containing a strand of colour `i` are those of the form `{i} + γ`. -/
theorem exists_blockSucc_of_mem (i : I) {x y : X} (h : x + RD.iX i = y)
    (β : WeightBlocks RD Λ y) (hi : i ∈ β.1) : ∃ γ, blockSucc RD Λ i h γ = β := by
  have h2 : blockWeight RD Λ (β.1.erase i) + RD.iX i = x + RD.iX i := by
    rw [← blockWeight_cons, Multiset.singleton_add, Multiset.cons_erase hi, β.2, h]
  refine ⟨⟨β.1.erase i, add_right_cancel h2⟩, Subtype.ext ?_⟩
  rw [blockSucc_val, Multiset.singleton_add, Multiset.cons_erase hi]

omit [DecidableEq I] in
theorem isEmpty_of_not_mem (i : I) {x y : X} (h : x + RD.iX i = y)
    (β : WeightBlocks RD Λ y) (hi : i ∉ β.1) :
    IsEmpty {γ : WeightBlocks RD Λ x // blockSucc RD Λ i h γ = β} :=
  ⟨fun ⟨γ, hγ⟩ => hi (by
    rw [← hγ, blockSucc_val]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i)))⟩

omit [DecidableEq I] in
/-- Kang–Kashiwara's weight `⟨h_i, Λ - β⟩` is minus the pairing with the weight of the block. -/
theorem blockLoc_weight (i : I) {y : X} (β : WeightBlocks RD Λ y) :
    -(RD.pair (RD.iY i) (Λ - (β.1.map RD.iX).sum)) = RD.pair (RD.iY i) y := by
  have hβ := β.2
  unfold blockWeight at hβ
  rw [← map_neg, neg_sub, hβ]

omit [DecidableEq I] in
/-- On a block without a strand of colour `i`, the pairing `⟨h_i, y⟩` is nonpositive. -/
theorem pair_nonpos_of_not_mem
    (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
    (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (i : I) {y : X} (β : WeightBlocks RD Λ y) (hi : i ∉ β.1) :
    RD.pair (RD.iY i) y ≤ 0 := by
  have key : ∀ s : Multiset I, i ∉ s → RD.pair (RD.iY i) (s.map RD.iX).sum ≤ 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons j s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.sum_cons, map_add]
      have hj : j ≠ i := fun e => hs (e ▸ Multiset.mem_cons_self _ _)
      have h1 := hdeg i j hj
      have h2 := ih (fun e => hs (Multiset.mem_cons_of_mem e))
      omega
  have h1 := key _ hi
  have h2 := hΛ i
  have hβ := β.2
  unfold blockWeight at hβ
  rw [← hβ, map_sub]
  omega

/-- The generator of `F_i E_i` at the block `{i} + γ`, as an isomorphism. -/
def capIso (i : I) {x y : X} (h : x + RD.iX i = y)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :=
  blockιIso (blockSucc RD Λ i h) (indBlock.{u, v, w} Q a RD Λ i h)
    ((blockRes (blockSucc RD Λ i h) (resBlock Q a RD Λ i h)).obj M) ⟨γ, rfl⟩
    fun _ => Subsingleton.elim _ _

/-- The generator of `E_i F_i` at the block `β`, as an isomorphism. -/
def cupIso (i : I) {y z : X} (h : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) :=
  (resBlock Q a RD Λ i h β _ rfl).mapIso
    (blockιIso (blockSucc RD Λ i h) (indBlock.{u, v, w} Q a RD Λ i h) M ⟨β, rfl⟩
      fun _ => Subsingleton.elim _ _)

/-- With no dotted units, `E_i F_i` vanishes. -/
theorem isZero_of_coefficients (i : I) {β δ : Multiset I} (h : {i} + β = δ) {n : ℕ}
    (B : RouqBoundary.Coefficients (adjA.{u, v, w} Q a i h) (dotA Q a i h) n) (hn : n = 0)
    (N : ModuleCat.{max (max u v) w} (CycKLR k Q a β)) :
    IsZero ((res Q a i h).obj ((ind Q a i h).obj N)) := by
  subst hn
  have t := congrArg (fun η => η.hom.app N) B.total
  simp at t
  exact (IsZero.iff_id_eq_zero _).2 t.symm

section Loc

variable {Q a} (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

/-- Brundan (1.8) on the weight space at `y`, at a block `{i} + γ`. -/
def locPosInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    SumInvTo ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M
        (blockSucc RD Λ i h₁ γ))
      (fun n => (globalF.{u, v, w} Q a RD Λ i h₁ ◁ powComp (globalDot Q a RD Λ i h₁) n ≫
        (globalAdj Q a RD Λ i h₁).counit).hom.app M (blockSucc RD Λ i h₁ γ))
      (RD.pair (RD.iY i) y).toNat := by
  have hw := blockLoc_weight RD Λ i (blockSucc RD Λ i h₁ γ)
  haveI : (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1) (M (blockSucc RD Λ i h₁ γ))).Additive :=
    ⟨rfl⟩
  let S₀ := ((blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (blockSucc_step RD Λ i h₁ γ)
      (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).invPos
        (by rw [hw]; exact hpos)).map
      (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1) (M (blockSucc RD Λ i h₁ γ)))
  refine (S₀.conj
      (capIso Q a RD Λ i h₁ M γ).symm (cupIso Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ))
      (Iso.refl _) ?_ ?_).congr rfl rfl (by rw [hw])
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (sigma_app Q a RD Λ i h₁ h₂ M γ))))
  · intro m
    exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((capD_app Q a RD Λ i h₁ M γ m).trans (Category.comp_id _).symm))))

/-- Brundan (1.9) on the weight space at `y`, at a block `{i} + γ`. -/
def locNegInterior (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (γ : WeightBlocks RD Λ x) :
    SumInvFrom ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M
        (blockSucc RD Λ i h₁ γ))
      (fun n => ((globalAdj.{u, v, w} Q a RD Λ i h₂).unit ≫
        powComp (globalDot Q a RD Λ i h₂) n ▷ globalF Q a RD Λ i h₂).hom.app M
          (blockSucc RD Λ i h₁ γ))
      (-RD.pair (RD.iY i) y).toNat := by
  have hw := blockLoc_weight RD Λ i (blockSucc RD Λ i h₁ γ)
  haveI : (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1) (M (blockSucc RD Λ i h₁ γ))).Additive :=
    ⟨rfl⟩
  let S₀ := ((blockLoc.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i (blockSucc_step RD Λ i h₁ γ)
      (blockSucc_step RD Λ i h₂ (blockSucc RD Λ i h₁ γ))).invNeg
        (by rw [hw]; exact hneg)).map
      (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1)
        (D := blockCat.{u, v, w} Q a (blockSucc RD Λ i h₁ γ).1) (M (blockSucc RD Λ i h₁ γ)))
  refine (S₀.conj (cupIso Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ))
      (capIso Q a RD Λ i h₁ M γ).symm (Iso.refl _) ?_ ?_).congr rfl rfl (by rw [hw])
  · exact (Category.id_comp _).symm.trans
      ((congrArg (· ≫ _) (capIso Q a RD Λ i h₁ M γ).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (sigma_app Q a RD Λ i h₁ h₂ M γ))))
  · intro m
    exact (cupD_app Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ) m).trans (Category.id_comp _).symm

/-- Brundan (1.8) on the weight space at `y`, at a block without a strand of colour `i`. -/
def locPosBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) (hi : i ∉ β.1) :
    SumInvTo ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (fun n => (globalF.{u, v, w} Q a RD Λ i h₁ ◁ powComp (globalDot Q a RD Λ i h₁) n ≫
        (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat := by
  have h0 : RD.pair (RD.iY i) y = 0 :=
    le_antisymm (pair_nonpos_of_not_mem Q a RD Λ hΛ hdeg i β hi) hpos
  have hY := isZero_of_coefficients Q a i _
    (blockBoundary.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i hi (blockSucc_step RD Λ i h₂ β))
    (by rw [← blockLoc_weight RD Λ i β, neg_eq_zero] at h0; rw [h0]; rfl) (M β)
  refine SumInvTo.congr (n := 0) (SumInvTo.ofIsZero _ _ ?_ ?_) rfl rfl (by rw [h0]; rfl)
  · exact blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ i h₁ β hi)
  · exact hY.of_iso (cupIso Q a RD Λ i h₂ M β).symm

/-- Brundan (1.9) on the weight space at `y`, at a block without a strand of colour `i`:
Kang–Kashiwara's dotted units. -/
def locNegBoundary (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) (hi : i ∉ β.1) :
    SumInvFrom ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (fun n => ((globalAdj.{u, v, w} Q a RD Λ i h₂).unit ≫
        powComp (globalDot Q a RD Λ i h₂) n ▷ globalF Q a RD Λ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat := by
  let B := blockBoundary.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i hi (blockSucc_step RD Λ i h₂ β)
  haveI : (AdditiveCat.homEval (C := blockCat.{u, v, w} Q a β.1)
        (D := blockCat.{u, v, w} Q a β.1) (M β)).Additive := ⟨rfl⟩
  let Φ := AdditiveCat.homEval (C := blockCat.{u, v, w} Q a β.1)
    (D := blockCat.{u, v, w} Q a β.1) (M β)
  refine ((SumInvFrom.ofIsZero ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M β ≫
          (cupIso Q a RD Λ i h₂ M β).inv)
      (fun m => Φ.map (RouqBoundary.cupD (adjA.{u, v, w} Q a i (blockSucc_step RD Λ i h₂ β))
        (dotA Q a i (blockSucc_step RD Λ i h₂ β)) m))
      (blockSum_obj_isZero _ _ _ (isEmpty_of_not_mem RD Λ i h₁ β hi))
      (fun m => Φ.map (B.coeff m)) ?_ ?_).conj (cupIso Q a RD Λ i h₂ M β) (Iso.refl _)
      (Iso.refl _) ?_ ?_).congr rfl rfl (by rw [← blockLoc_weight RD Λ i β, neg_neg])
  · refine (Finset.sum_congr rfl fun m _ => (Φ.map_comp _ _).symm).trans ?_
    exact (Φ.map_sum _ _).symm.trans ((congrArg Φ.map B.total).trans (Φ.map_id _))
  · intro m m' hm hm'
    refine (Φ.map_comp _ _).symm.trans ((congrArg Φ.map (B.entry m m' hm hm')).trans ?_)
    split_ifs
    · exact Φ.map_id _
    · exact Φ.map_zero _ _
  · exact (Category.comp_id _).symm.trans
      ((congrArg (_ ≫ ·) (cupIso Q a RD Λ i h₂ M β).inv_hom_id.symm).trans
        ((Category.assoc _ _ _).symm.trans (Category.id_comp _).symm))
  · intro m
    exact (cupD_app Q a RD Λ i h₂ M β m).trans (Category.id_comp _).symm

/-- Brundan (1.8) on the weight space at `y`, blockwise. -/
def locPos (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hpos : 0 ≤ RD.pair (RD.iY i) y)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) :
    SumInvTo ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (fun n => (globalF.{u, v, w} Q a RD Λ i h₁ ◁ powComp (globalDot Q a RD Λ i h₁) n ≫
        (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ i h₁ γ = β) => by
      subst hγ; exact locPosInterior RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hpos M γ) _
      (exists_blockSucc_of_mem RD Λ i h₁ β hi).choose_spec
  else locPosBoundary RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hpos M β hi

/-- Brundan (1.9) on the weight space at `y`, blockwise. -/
def locNeg (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z)
    (hneg : RD.pair (RD.iY i) y ≤ 0)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) :
    SumInvFrom ((RightwardCrossing.sigma (globalAdj.{u, v, w} Q a RD Λ i h₂).unit
        (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (globalAdj Q a RD Λ i h₁).counit).hom.app M β)
      (fun n => ((globalAdj.{u, v, w} Q a RD Λ i h₂).unit ≫
        powComp (globalDot Q a RD Λ i h₂) n ▷ globalF Q a RD Λ i h₂).hom.app M β)
      (-RD.pair (RD.iY i) y).toNat :=
  if hi : i ∈ β.1 then
    (fun γ (hγ : blockSucc RD Λ i h₁ γ = β) => by
      subst hγ; exact locNegInterior RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hneg M γ) _
      (exists_blockSucc_of_mem RD Λ i h₁ β hi).choose_spec
  else locNegBoundary RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M β hi

/-- **Kang–Kashiwara, Theorem 5.2, on weight spaces**: Rouquier's local data for the
weight-indexed cyclotomic family at the weight `y` (KL III Thm. 1.2; Brundan (1.8), (1.9)), with
Brundan weight `⟨h_i, y⟩`. -/
def globalLoc (i : I) {x y z : X} (h₁ : x + RD.iX i = y) (h₂ : y + RD.iX i = z) :
    RouqLoc (globalAdj.{u, v, w} Q a RD Λ i h₁) (globalAdj Q a RD Λ i h₂)
      (globalDot Q a RD Λ i h₁) (globalDot Q a RD Λ i h₂)
      (globalCross Q a RD Λ i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) y) where
  slide_left := globalCross_slide_left_self Q a RD Λ i h₁ h₂
  slide_right := globalCross_slide_right_self Q a RD Λ i h₁ h₂
  invPos hpos := SumInvTo.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvTo.ofApp fun M => SumInvTo.pi fun β =>
      locPos RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hpos M β)
  invNeg hneg := SumInvFrom.ofFullyFaithful (LinearCat.homForget _ _)
    (SumInvFrom.ofApp fun M => SumInvFrom.pi fun β =>
      locNeg RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ hneg M β)

end Loc

end

end Categorification.KLR.CyclotomicAction
