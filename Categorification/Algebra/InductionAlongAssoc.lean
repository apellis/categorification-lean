/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensor

/-!
# Associativity and unit isomorphisms for induction along tensor products

Let `φ₁₂ : A₁ ⊗ A₂ → B₁₂`, `φ₂₃ : A₂ ⊗ A₃ → B₂₃`, `ψ : B₁₂ ⊗ A₃ → D` and `ψ' : A₁ ⊗ B₂₃ → D'`
be nonunital maps of `k`-algebras, and `c : D ≅ D'` an isomorphism with
`c (ψ (φ₁₂ (x ⊗ y) ⊗ z)) = ψ' (x ⊗ φ₂₃ (y ⊗ z))`. This file proves the module-level
consequences: induction `Ind (Ind (M ⊠ N) ⊠ P) ≅ Ind (M ⊠ Ind (N ⊠ P))` and restriction
`Res (Res L) ≅ Res (Res L')` are associative, and induction from the regular module of a unit
algebra is trivial. These are the general forms of the module statements in
B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18 (and of Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 3.1).

## Main definitions

* `Ind.mapEquiv`: induction of an isomorphism of modules.
* `Res.compEquiv`: `Res_φ (Res_ψ M) ≅ Res_{ψ ∘ φ} M`.
* `Res.transport`: restriction along ring isomorphisms intertwining two maps.
* `indAssoc`: `Ind_ψ (Ind_{φ₁₂} (M ⊠ N) ⊠ P) ≅ Ind_{ψ'} (M ⊠ Ind_{φ₂₃} (N ⊠ P))`, semilinear
  along `c`.
* `resCoassoc`: `Res_{φ₁₂ ⊗ id} (Res_ψ L) ≅ Res_{id ⊗ φ₂₃} (Res_{ψ'} L')`, semilinear along the
  associator of `A₁ ⊗ A₂ ⊗ A₃`.
* `indUnitLeft`, `indUnitRight`: `Ind_ψ (A₀ ⊠ M) ≅ M` when `c (ψ (1 ⊗ a)) = a`, and the mirror.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

/-! ### Functoriality in isomorphisms -/

section MapEquiv

variable {A B : Type u} [Ring A] [Ring B] {φ : A →ₙ+* B} {N N' : Type w} [AddCommGroup N]
  [Module A N] [AddCommGroup N'] [Module A N']

/-- Induction of an isomorphism of modules. -/
def Ind.mapEquiv (g : N ≃ₗ[A] N') : Ind N φ ≃ₗ[B] Ind N' φ :=
  LinearEquiv.ofLinearMap (Ind.map g.toLinearMap) (Ind.map g.symm.toLinearMap)
    (Ind.ext fun z n => by
      rw [LinearMap.comp_apply, Ind.map_tmul, Ind.map_tmul, LinearMap.id_apply]
      simp)
    (Ind.ext fun z n => by
      rw [LinearMap.comp_apply, Ind.map_tmul, Ind.map_tmul, LinearMap.id_apply]
      simp)

@[simp] theorem Ind.mapEquiv_tmul (g : N ≃ₗ[A] N') (z : Corner φ) (n : N) :
    Ind.mapEquiv g (Ind.tmul z n) = Ind.tmul z (g n) := rfl

end MapEquiv

/-! ### Restriction along a composite and along isomorphisms -/

section ResComp

variable {A B C : Type u} [Ring A] [Ring B] [Ring C] (φ : A →ₙ+* B) (ψ : B →ₙ+* C)
  (M : Type w) [AddCommGroup M] [Module C M]

variable {M} in
theorem Res.comp_fixed {m : M} (h : ψ (φ 1) • m = m) : ψ 1 • m = m := by
  rw [← h, smul_smul, ← map_mul, one_mul]

/-- **Restriction along a composite**: `Res_φ (Res_ψ M) ≅ Res_{ψ ∘ φ} M`. -/
def Res.compEquiv : Res φ (Res ψ M) ≃ₗ[A] Res (ψ.comp φ) M where
  toFun m := Res.mk m.val.val (congrArg Res.val m.prop)
  invFun m := Res.mk (Res.mk m.val (Res.comp_fixed φ ψ m.prop)) (Res.ext m.prop)
  map_add' _ _ := Res.ext rfl
  map_smul' _ _ := Res.ext rfl
  left_inv _ := Res.ext (Res.ext rfl)
  right_inv _ := Res.ext rfl

@[simp] theorem Res.val_compEquiv (m : Res φ (Res ψ M)) :
    (Res.compEquiv φ ψ M m).val = m.val.val := rfl

end ResComp

section ResTransport

variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B'] {φ : A →ₙ+* B}
  {φ' : A' →ₙ+* B'} (a : A ≃+* A') (c : B ≃+* B') (h : ∀ t, φ' (a t) = c (φ t))
  {M M' : Type w} [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M']
  (e : M ≃+ M') (he : ∀ (b : B) m, e (b • m) = c b • e m)

include h he

/-- **Transport of restriction** along ring isomorphisms intertwining `φ` and `φ'` and a
semilinear isomorphism of modules. It is semilinear along `a` (`Res.transport_smul`). -/
def Res.transport : Res φ M ≃+ Res φ' M' where
  toFun m := Res.mk (e m.val) (by rw [← map_one a, h, ← he, m.prop])
  invFun m := Res.mk (e.symm m.val) (by
    apply e.injective
    rw [he, e.apply_symm_apply, show c (φ 1) = φ' 1 by rw [← h, map_one], m.prop])
  left_inv m := Res.ext (e.symm_apply_apply _)
  right_inv m := Res.ext (e.apply_symm_apply _)
  map_add' m m' := Res.ext (map_add e m.val m'.val)

@[simp] theorem Res.val_transport (m : Res φ M) :
    (Res.transport a c h e he m).val = e m.val := rfl

theorem Res.transport_smul (t : A) (m : Res φ M) :
    Res.transport a c h e he (t • m) = a t • Res.transport a c h e he m :=
  Res.ext (by
    change e (φ t • m.val) = φ' (a t) • e m.val
    rw [he, h])

end ResTransport

/-! ### Associativity -/

section Assoc

variable (k : Type*) [CommRing k] {A₁ A₂ A₃ B₁₂ B₂₃ D D' : Type u}
  [Ring A₁] [Algebra k A₁] [Ring A₂] [Algebra k A₂] [Ring A₃] [Algebra k A₃]
  [Ring B₁₂] [Algebra k B₁₂] [Ring B₂₃] [Algebra k B₂₃] [Ring D] [Algebra k D]
  [Ring D'] [Algebra k D']
  (φ₁₂ : A₁ ⊗[k] A₂ →ₙ+* B₁₂) (hφ₁₂ : ∀ (r : k) (t : A₁ ⊗[k] A₂), φ₁₂ (r • t) = r • φ₁₂ t)
  (φ₂₃ : A₂ ⊗[k] A₃ →ₙ+* B₂₃) (hφ₂₃ : ∀ (r : k) (t : A₂ ⊗[k] A₃), φ₂₃ (r • t) = r • φ₂₃ t)
  (ψ : B₁₂ ⊗[k] A₃ →ₙ+* D) (ψ' : A₁ ⊗[k] B₂₃ →ₙ+* D') (c : D ≃ₐ[k] D')
  (hc : ∀ x y z, c (ψ (φ₁₂ (x ⊗ₜ y) ⊗ₜ z)) = ψ' (x ⊗ₜ φ₂₃ (y ⊗ₜ z)))

include hc in
/-- The two composites `ψ ∘ (φ₁₂ ⊗ id)` and `ψ' ∘ (id ⊗ φ₂₃)` agree along the associator and
`c`. -/
theorem assoc_intertwines (t : (A₁ ⊗[k] A₂) ⊗[k] A₃) :
    (ψ'.comp (tensorRight k A₁ φ₂₃ hφ₂₃)) (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃ t) =
      c.toRingEquiv ((ψ.comp (tensorLeft k A₃ φ₁₂ hφ₁₂)) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul t₁₂ z =>
    induction t₁₂ using TensorProduct.inductionOn with
    | tmul x y =>
      rw [Algebra.TensorProduct.assoc_tmul]
      exact (hc x y z).symm
    | add s s' hs hs' => rw [TensorProduct.add_tmul, map_add, map_add, hs, hs', map_add, map_add]
  | add s s' hs hs' => rw [map_add, map_add, hs, hs', map_add, map_add]

variable (M N P : Type w) [AddCommGroup M] [Module k M] [Module A₁ M] [IsScalarTower k A₁ M]
  [AddCommGroup N] [Module k N] [Module A₂ N] [IsScalarTower k A₂ N]
  [AddCommGroup P] [Module k P] [Module A₃ P] [IsScalarTower k A₃ P]

/-- The associator `(M ⊠ N) ⊠ P ≅ M ⊠ (N ⊠ P)` of external tensor products. -/
def extAssoc : ExtTensor k (ExtTensor k M N) P ≃+ ExtTensor k M (ExtTensor k N P) :=
  (TensorProduct.assoc k M N P).toAddEquiv

theorem extAssoc_tmul_tmul (m : M) (n : N) (p : P) :
    extAssoc k M N P (ExtTensor.tmul (ExtTensor.tmul m n) p) =
      ExtTensor.tmul m (ExtTensor.tmul n p) := rfl

/-- The associator of external tensor products is semilinear along the associator of
`A₁ ⊗ A₂ ⊗ A₃`. -/
theorem extAssoc_smul (t : (A₁ ⊗[k] A₂) ⊗[k] A₃) (x : ExtTensor k (ExtTensor k M N) P) :
    extAssoc k M N P (t • x) = Algebra.TensorProduct.assoc k k k A₁ A₂ A₃ t •
      extAssoc k M N P x := by
  induction t using TensorProduct.inductionOn with
  | tmul t₁₂ z =>
    induction t₁₂ using TensorProduct.inductionOn with
    | tmul a₁ a₂ =>
      induction x using ExtTensor.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul y p =>
        induction y using ExtTensor.induction_on with
        | zero => rw [ExtTensor.zero_tmul, smul_zero, map_zero, smul_zero]
        | tmul m n =>
          rw [ExtTensor.smul_tmul, ExtTensor.smul_tmul, extAssoc_tmul_tmul, extAssoc_tmul_tmul,
            Algebra.TensorProduct.assoc_tmul, ExtTensor.smul_tmul, ExtTensor.smul_tmul]
        | add y y' hy hy' => rw [ExtTensor.add_tmul, smul_add, map_add, hy, hy', map_add, smul_add]
      | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
    | add s s' hs hs' => rw [TensorProduct.add_tmul, add_smul, map_add, hs, hs', map_add, add_smul]
  | add s s' hs hs' => rw [add_smul, map_add, hs, hs', map_add, add_smul]

/-- `extIndLeft` with target written as `Ind`, the form composed with `compEquiv`. -/
def extIndLeftInd :
    ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P ≃ₗ[B₁₂ ⊗[k] A₃]
      Ind (ExtTensor k (ExtTensor k M N) P) (tensorLeft k A₃ φ₁₂ hφ₁₂) :=
  extIndLeft k A₃ φ₁₂ hφ₁₂ (ExtTensor k M N) P

/-- `extIndRight` with target written as `Ind`. -/
def extIndRightInd :
    ExtTensor k M (IndK k (ExtTensor k N P) φ₂₃) ≃ₗ[A₁ ⊗[k] B₂₃]
      Ind (ExtTensor k M (ExtTensor k N P)) (tensorRight k A₁ φ₂₃ hφ₂₃) :=
  extIndRight k A₁ φ₂₃ hφ₂₃ (ExtTensor k N P) M

/-- The first half of `indAssoc`: `Ind_ψ (Ind (M ⊠ N) ⊠ P) ≅ Ind_{ψ ∘ (φ₁₂ ⊗ id)} ((M ⊠ N) ⊠ P)`. -/
def indAssocLeft :
    Ind (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ ≃ₗ[D]
      Ind (ExtTensor k (ExtTensor k M N) P) (ψ.comp (tensorLeft k A₃ φ₁₂ hφ₁₂)) :=
  (Ind.mapEquiv (extIndLeftInd k φ₁₂ hφ₁₂ M N P)).trans
    (compEquiv (ExtTensor k (ExtTensor k M N) P) (tensorLeft k A₃ φ₁₂ hφ₁₂) ψ)

/-- The second half of `indAssoc`:
`Ind_{ψ' ∘ (id ⊗ φ₂₃)} (M ⊠ (N ⊠ P)) ≅ Ind_{ψ'} (M ⊠ Ind (N ⊠ P))`. -/
def indAssocRight :
    Ind (ExtTensor k M (ExtTensor k N P)) (ψ'.comp (tensorRight k A₁ φ₂₃ hφ₂₃)) ≃ₗ[D']
      Ind (ExtTensor k M (IndK k (ExtTensor k N P) φ₂₃)) ψ' :=
  (compEquiv (ExtTensor k M (ExtTensor k N P)) (tensorRight k A₁ φ₂₃ hφ₂₃) ψ').symm.trans
    (Ind.mapEquiv (extIndRightInd k φ₂₃ hφ₂₃ M N P).symm)

include hc in
/-- **Associativity of induction** (the module form of Webster, arXiv:1209.2463v4, §2.4,
Proposition 2.18): `Ind_ψ (Ind_{φ₁₂} (M ⊠ N) ⊠ P) ≅ Ind_{ψ'} (M ⊠ Ind_{φ₂₃} (N ⊠ P))`, an additive
isomorphism semilinear along `c` (`indAssoc_smul`). -/
def indAssoc :
    IndK k (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ ≃+
      IndK k (ExtTensor k M (IndK k (ExtTensor k N P) φ₂₃)) ψ' :=
  ((indAssocLeft k φ₁₂ hφ₁₂ ψ M N P).toAddEquiv.trans
    (Ind.transport (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
      (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc) (extAssoc k M N P)
      (extAssoc_smul k M N P))).trans
    (indAssocRight k φ₂₃ hφ₂₃ ψ' M N P).toAddEquiv

theorem indAssoc_smul (d : D) (x : IndK k (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ) :
    indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P (d • x) =
      c d • indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P x := by
  have key : ∀ y : Ind (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ,
      indAssocRight k φ₂₃ hφ₂₃ ψ' M N P (Ind.transport
        (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
        (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc) (extAssoc k M N P)
        (extAssoc_smul k M N P) (indAssocLeft k φ₁₂ hφ₁₂ ψ M N P (d • y))) =
      c d • indAssocRight k φ₂₃ hφ₂₃ ψ' M N P (Ind.transport
        (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
        (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc) (extAssoc k M N P)
        (extAssoc_smul k M N P) (indAssocLeft k φ₁₂ hφ₁₂ ψ M N P y)) := fun y => by
    rw [map_smul, Ind.transport_smul, map_smul]
    rfl
  exact key x

/-- `indAssoc` as a `k`-linear isomorphism. -/
def indAssocLinear :
    IndK k (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ ≃ₗ[k]
      IndK k (ExtTensor k M (IndK k (ExtTensor k N P) φ₂₃)) ψ' :=
  { indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P with
    map_smul' := fun r x => by
      change indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P (algebraMap k D r • x) =
        algebraMap k D' r • indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P x
      rw [indAssoc_smul, AlgEquiv.commutes] }

variable (L : Type w) [AddCommGroup L] [Module D L] (L' : Type w) [AddCommGroup L']
  [Module D' L'] (e : L ≃+ L') (he : ∀ (d : D) l, e (d • l) = c d • e l)

include hc he in
/-- **Coassociativity of restriction** (the module form of Webster, arXiv:1209.2463v4, §2.4,
Proposition 2.18): `Res_{φ₁₂ ⊗ id} (Res_ψ L) ≅ Res_{id ⊗ φ₂₃} (Res_{ψ'} L')` for a `c`-semilinear
isomorphism `L ≅ L'`; it is semilinear along the associator (`resCoassoc_smul`). -/
def resCoassoc :
    Res (tensorLeft k A₃ φ₁₂ hφ₁₂) (Res ψ L) ≃+ Res (tensorRight k A₁ φ₂₃ hφ₂₃) (Res ψ' L') :=
  ((Res.compEquiv (tensorLeft k A₃ φ₁₂ hφ₁₂) ψ L).toAddEquiv.trans
    (Res.transport (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
      (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc) e he)).trans
    (Res.compEquiv (tensorRight k A₁ φ₂₃ hφ₂₃) ψ' L').symm.toAddEquiv

@[simp] theorem val_resCoassoc (m : Res (tensorLeft k A₃ φ₁₂ hφ₁₂) (Res ψ L)) :
    (resCoassoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc L L' e he m).val.val = e m.val.val := rfl

theorem resCoassoc_smul (t : (A₁ ⊗[k] A₂) ⊗[k] A₃)
    (m : Res (tensorLeft k A₃ φ₁₂ hφ₁₂) (Res ψ L)) :
    resCoassoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc L L' e he (t • m) =
      Algebra.TensorProduct.assoc k k k A₁ A₂ A₃ t •
        resCoassoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc L L' e he m := by
  let G₁ := Res.compEquiv (tensorLeft k A₃ φ₁₂ hφ₁₂) ψ L
  let T := Res.transport (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
    (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc) e he
  let G₂ := (Res.compEquiv (tensorRight k A₁ φ₂₃ hφ₂₃) ψ' L').symm
  change G₂ (T (G₁ (t • m))) = _ • G₂ (T (G₁ m))
  rw [map_smul G₁, Res.transport_smul, map_smul G₂]
  rfl

end Assoc

/-! ### Units -/

section UnitLeft

variable (k : Type*) [CommRing k] {A₀ A D : Type u} [Ring A₀] [Algebra k A₀] [Ring A]
  [Algebra k A] [Ring D] [Algebra k D] (ψ : A₀ ⊗[k] A →ₙ+* D)
  (hψ : ∀ (r : k) (t : A₀ ⊗[k] A), ψ (r • t) = r • ψ t) (c : D ≃ₐ[k] A)
  (hc : ∀ a, c (ψ (1 ⊗ₜ a)) = a)
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

include hc in
theorem unitLeft_map_one : ψ 1 = 1 :=
  c.injective (by rw [Algebra.TensorProduct.one_def, hc, map_one])

include hc in
theorem unitLeft_map_one_tmul (a : A) : ψ (1 ⊗ₜ a) = c.symm a :=
  c.injective (by rw [hc, c.apply_symm_apply])

variable {M} in
/-- For fixed `z`, the bilinear map `(x, m) ↦ c(z ψ(x ⊗ 1)) m`. -/
def unitLeftPair (z : Corner ψ) : A₀ →ₗ[k] M →ₗ[k] M :=
  LinearMap.mk₂ k (fun x m => c (z.1 * ψ (x ⊗ₜ 1)) • m)
    (fun x x' m => by rw [TensorProduct.add_tmul, map_add, mul_add, map_add, add_smul])
    (fun r x m => by
      rw [← TensorProduct.smul_tmul', hψ, mul_smul_comm, map_smul, smul_assoc])
    (fun x m m' => smul_add _ m m')
    (fun r x m => smul_comm _ r m)

variable {M} in
/-- For fixed `z`, the map `x ⊗ m ↦ c(z ψ(x ⊗ 1)) m` on `A₀ ⊠ M`. -/
def unitLeftInner (z : Corner ψ) : ExtTensor k A₀ M →+ M :=
  (ExtTensor.lift (unitLeftPair k ψ hψ c z)).toAddMonoidHom

theorem unitLeftInner_tmul (z : Corner ψ) (x : A₀) (m : M) :
    unitLeftInner k ψ hψ c z (ExtTensor.tmul x m) = c (z.1 * ψ (x ⊗ₜ 1)) • m := rfl

theorem unitLeftInner_add (z z' : Corner ψ) (x : ExtTensor k A₀ M) :
    unitLeftInner k ψ hψ c (z + z') x = unitLeftInner k ψ hψ c z x + unitLeftInner k ψ hψ c z' x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul x m =>
    rw [unitLeftInner_tmul, unitLeftInner_tmul, unitLeftInner_tmul]
    change c ((z.1 + z'.1) * _) • m = _
    rw [add_mul, map_add, add_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem unitLeftInner_smul (d : D) (z : Corner ψ) (x : ExtTensor k A₀ M) :
    unitLeftInner k ψ hψ c (d • z) x = c d • unitLeftInner k ψ hψ c z x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul x m =>
    rw [unitLeftInner_tmul, unitLeftInner_tmul]
    change c (d * z.1 * _) • m = _
    rw [mul_assoc, map_mul, mul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

include hc in
theorem unitLeftInner_op_smul (z : Corner ψ) (t : A₀ ⊗[k] A) (x : ExtTensor k A₀ M) :
    unitLeftInner k ψ hψ c (op t • z) x = unitLeftInner k ψ hψ c z (t • x) := by
  induction t using TensorProduct.inductionOn with
  | tmul x' a =>
    induction x using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | tmul x₀ m =>
      rw [ExtTensor.smul_tmul, unitLeftInner_tmul, unitLeftInner_tmul, smul_eq_mul]
      change c (z.1 * ψ (x' ⊗ₜ a) * ψ (x₀ ⊗ₜ 1)) • m = _
      have h : z.1 * ψ (x' ⊗ₜ a) * ψ (x₀ ⊗ₜ 1) = z.1 * ψ ((x' * x₀) ⊗ₜ 1) * ψ (1 ⊗ₜ a) := by
        rw [mul_assoc, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc,
          ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, map_mul, hc, mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]
  | add t t' ht ht' =>
    rw [op_add, add_smul, unitLeftInner_add, ht, ht', add_smul, map_add]

/-- The forward map `z ⊗ (x ⊗ m) ↦ c(z ψ(x ⊗ 1)) m`. -/
def indUnitLeftFwd : Ind (ExtTensor k A₀ M) ψ →+ M :=
  Ind.liftAdd (fun z x => unitLeftInner k ψ hψ c z x)
    (fun z z' x => unitLeftInner_add k ψ hψ c M z z' x) (fun _ x x' => map_add _ x x')
    (fun z t x => unitLeftInner_op_smul k ψ hψ c hc M z t x)

theorem indUnitLeftFwd_smul (d : D) (y : Ind (ExtTensor k A₀ M) ψ) :
    indUnitLeftFwd k ψ hψ c hc M (d • y) = c d • indUnitLeftFwd k ψ hψ c hc M y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z x => rw [Ind.smul_tmul]; exact unitLeftInner_smul k ψ hψ c M d z x
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]

/-- The inverse map `m ↦ ψ(1) ⊗ (1 ⊗ m)`. -/
def indUnitLeftBwd : M →+ Ind (ExtTensor k A₀ M) ψ :=
  AddMonoidHom.mk' (fun m => Ind.tmul (unitGen ψ) (ExtTensor.tmul (1 : A₀) m))
    (fun m m' => by rw [ExtTensor.tmul_add, Ind.tmul_add])

/-- **Left unit of induction**: `Ind_ψ (A₀ ⊠ M) ≅ M` when `c (ψ (1 ⊗ a)) = a`, semilinear
along `c` (`indUnitLeft_smul`). The module form of the unit statement of Webster,
arXiv:1209.2463v4, §2.4, Proposition 2.18. -/
def indUnitLeft : IndK k (ExtTensor k A₀ M) ψ ≃+ M where
  toFun := indUnitLeftFwd k ψ hψ c hc M
  invFun := indUnitLeftBwd k ψ M
  left_inv y := by
    change indUnitLeftBwd k ψ M (indUnitLeftFwd k ψ hψ c hc M y) = y
    induction y using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z x =>
      induction x using ExtTensor.induction_on with
      | zero => rw [Ind.tmul_zero, map_zero, map_zero]
      | tmul x₀ m =>
        change Ind.tmul (unitGen ψ) (ExtTensor.tmul (1 : A₀) (c (z.1 * ψ (x₀ ⊗ₜ 1)) • m)) =
          Ind.tmul z (ExtTensor.tmul x₀ m)
        have e1 : (ExtTensor.tmul (1 : A₀) (c (z.1 * ψ (x₀ ⊗ₜ 1)) • m) : ExtTensor k A₀ M) =
            ((1 : A₀) ⊗ₜ[k] c (z.1 * ψ (x₀ ⊗ₜ 1))) • ExtTensor.tmul (1 : A₀) m := by
          rw [ExtTensor.smul_tmul, one_smul]
        have e2 : (op ((1 : A₀) ⊗ₜ[k] c (z.1 * ψ (x₀ ⊗ₜ 1))) • unitGen ψ : Corner ψ) =
            op (x₀ ⊗ₜ[k] (1 : A)) • z := Subtype.ext (by
          change ψ 1 * ψ (1 ⊗ₜ c (z.1 * ψ (x₀ ⊗ₜ 1))) = z.1 * ψ (x₀ ⊗ₜ 1)
          have h1 : ψ 1 = 1 := unitLeft_map_one k ψ c hc
          exact (congrArg (· * ψ (1 ⊗ₜ c (z.1 * ψ (x₀ ⊗ₜ 1)))) h1).trans
            (by rw [one_mul, unitLeft_map_one_tmul k ψ c hc, c.symm_apply_apply]))
        have e3 : ((x₀ ⊗ₜ[k] (1 : A)) • ExtTensor.tmul (1 : A₀) m : ExtTensor k A₀ M) =
            ExtTensor.tmul x₀ m := by
          rw [ExtTensor.smul_tmul, smul_eq_mul, mul_one, one_smul]
        rw [e1, ← Ind.op_smul_tmul, e2, Ind.op_smul_tmul, e3]
      | add x x' hx hx' => rw [Ind.tmul_add, map_add, map_add, hx, hx']
    | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  right_inv m := by
    change c (ψ 1 * ψ (1 ⊗ₜ 1)) • m = m
    rw [← Algebra.TensorProduct.one_def, unitLeft_map_one k ψ c hc, one_mul, map_one, one_smul]
  map_add' := map_add (indUnitLeftFwd k ψ hψ c hc M)

theorem indUnitLeft_smul (d : D) (y : IndK k (ExtTensor k A₀ M) ψ) :
    indUnitLeft k ψ hψ c hc M (d • y) = c d • indUnitLeft k ψ hψ c hc M y :=
  indUnitLeftFwd_smul k ψ hψ c hc M d y

theorem indUnitLeft_symm_apply (m : M) :
    (indUnitLeft k ψ hψ c hc M).symm m = Ind.tmul (unitGen ψ) (ExtTensor.tmul (1 : A₀) m) :=
  rfl

/-- `indUnitLeft` as a `k`-linear isomorphism. -/
def indUnitLeftLinear : IndK k (ExtTensor k A₀ M) ψ ≃ₗ[k] M :=
  { indUnitLeft k ψ hψ c hc M with
    map_smul' := fun r y => by
      change indUnitLeft k ψ hψ c hc M (algebraMap k D r • y) = r • indUnitLeft k ψ hψ c hc M y
      rw [indUnitLeft_smul, AlgEquiv.commutes, algebraMap_smul] }

end UnitLeft

section UnitRight

variable (k : Type*) [CommRing k] {A₀ A D : Type u} [Ring A₀] [Algebra k A₀] [Ring A]
  [Algebra k A] [Ring D] [Algebra k D] (ψ : A ⊗[k] A₀ →ₙ+* D)
  (hψ : ∀ (r : k) (t : A ⊗[k] A₀), ψ (r • t) = r • ψ t) (c : D ≃ₐ[k] A)
  (hc : ∀ a, c (ψ (a ⊗ₜ 1)) = a)
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

include hc in
theorem unitRight_map_one : ψ 1 = 1 :=
  c.injective (by rw [Algebra.TensorProduct.one_def, hc, map_one])

include hc in
theorem unitRight_map_tmul_one (a : A) : ψ (a ⊗ₜ 1) = c.symm a :=
  c.injective (by rw [hc, c.apply_symm_apply])

variable {M} in
/-- For fixed `z`, the bilinear map `(m, x) ↦ c(z ψ(1 ⊗ x)) m`. -/
def unitRightPair (z : Corner ψ) : M →ₗ[k] A₀ →ₗ[k] M :=
  LinearMap.mk₂ k (fun m x => c (z.1 * ψ (1 ⊗ₜ x)) • m)
    (fun m m' x => smul_add _ m m')
    (fun r m x => smul_comm _ r m)
    (fun m x x' => by rw [TensorProduct.tmul_add, map_add, mul_add, map_add, add_smul])
    (fun r m x => by
      rw [TensorProduct.tmul_smul, hψ, mul_smul_comm, map_smul, smul_assoc])

variable {M} in
/-- For fixed `z`, the map `m ⊗ x ↦ c(z ψ(1 ⊗ x)) m` on `M ⊠ A₀`. -/
def unitRightInner (z : Corner ψ) : ExtTensor k M A₀ →+ M :=
  (ExtTensor.lift (unitRightPair k ψ hψ c z)).toAddMonoidHom

theorem unitRightInner_tmul (z : Corner ψ) (m : M) (x : A₀) :
    unitRightInner k ψ hψ c z (ExtTensor.tmul m x) = c (z.1 * ψ (1 ⊗ₜ x)) • m := rfl

theorem unitRightInner_add (z z' : Corner ψ) (x : ExtTensor k M A₀) :
    unitRightInner k ψ hψ c (z + z') x =
      unitRightInner k ψ hψ c z x + unitRightInner k ψ hψ c z' x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul m x =>
    rw [unitRightInner_tmul, unitRightInner_tmul, unitRightInner_tmul]
    change c ((z.1 + z'.1) * _) • m = _
    rw [add_mul, map_add, add_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem unitRightInner_smul (d : D) (z : Corner ψ) (x : ExtTensor k M A₀) :
    unitRightInner k ψ hψ c (d • z) x = c d • unitRightInner k ψ hψ c z x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul m x =>
    rw [unitRightInner_tmul, unitRightInner_tmul]
    change c (d * z.1 * _) • m = _
    rw [mul_assoc, map_mul, mul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

include hc in
theorem unitRightInner_op_smul (z : Corner ψ) (t : A ⊗[k] A₀) (x : ExtTensor k M A₀) :
    unitRightInner k ψ hψ c (op t • z) x = unitRightInner k ψ hψ c z (t • x) := by
  induction t using TensorProduct.inductionOn with
  | tmul a x' =>
    induction x using ExtTensor.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]
    | tmul m x₀ =>
      rw [ExtTensor.smul_tmul, unitRightInner_tmul, unitRightInner_tmul, smul_eq_mul]
      change c (z.1 * ψ (a ⊗ₜ x') * ψ (1 ⊗ₜ x₀)) • m = _
      have h : z.1 * ψ (a ⊗ₜ x') * ψ (1 ⊗ₜ x₀) = z.1 * ψ (1 ⊗ₜ (x' * x₀)) * ψ (a ⊗ₜ 1) := by
        rw [mul_assoc, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc,
          ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h, map_mul, hc, mul_smul]
    | add x y hx hy => rw [map_add, hx, hy, smul_add, map_add]
  | add t t' ht ht' =>
    rw [op_add, add_smul, unitRightInner_add, ht, ht', add_smul, map_add]

/-- The forward map `z ⊗ (m ⊗ x) ↦ c(z ψ(1 ⊗ x)) m`. -/
def indUnitRightFwd : Ind (ExtTensor k M A₀) ψ →+ M :=
  Ind.liftAdd (fun z x => unitRightInner k ψ hψ c z x)
    (fun z z' x => unitRightInner_add k ψ hψ c M z z' x) (fun _ x x' => map_add _ x x')
    (fun z t x => unitRightInner_op_smul k ψ hψ c hc M z t x)

theorem indUnitRightFwd_smul (d : D) (y : Ind (ExtTensor k M A₀) ψ) :
    indUnitRightFwd k ψ hψ c hc M (d • y) = c d • indUnitRightFwd k ψ hψ c hc M y := by
  induction y using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z x => rw [Ind.smul_tmul]; exact unitRightInner_smul k ψ hψ c M d z x
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]

/-- The inverse map `m ↦ ψ(1) ⊗ (m ⊗ 1)`. -/
def indUnitRightBwd : M →+ Ind (ExtTensor k M A₀) ψ :=
  AddMonoidHom.mk' (fun m => Ind.tmul (unitGen ψ) (ExtTensor.tmul m (1 : A₀)))
    (fun m m' => by rw [ExtTensor.add_tmul, Ind.tmul_add])

/-- **Right unit of induction**: `Ind_ψ (M ⊠ A₀) ≅ M` when `c (ψ (a ⊗ 1)) = a`, semilinear
along `c` (`indUnitRight_smul`). The module form of the unit statement of Webster,
arXiv:1209.2463v4, §2.4, Proposition 2.18. -/
def indUnitRight : IndK k (ExtTensor k M A₀) ψ ≃+ M where
  toFun := indUnitRightFwd k ψ hψ c hc M
  invFun := indUnitRightBwd k ψ M
  left_inv y := by
    change indUnitRightBwd k ψ M (indUnitRightFwd k ψ hψ c hc M y) = y
    induction y using Ind.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul z x =>
      induction x using ExtTensor.induction_on with
      | zero => rw [Ind.tmul_zero, map_zero, map_zero]
      | tmul m x₀ =>
        change Ind.tmul (unitGen ψ) (ExtTensor.tmul (c (z.1 * ψ (1 ⊗ₜ x₀)) • m) (1 : A₀)) =
          Ind.tmul z (ExtTensor.tmul m x₀)
        have e1 : (ExtTensor.tmul (c (z.1 * ψ (1 ⊗ₜ x₀)) • m) (1 : A₀) : ExtTensor k M A₀) =
            (c (z.1 * ψ (1 ⊗ₜ x₀)) ⊗ₜ[k] (1 : A₀)) • ExtTensor.tmul m (1 : A₀) := by
          rw [ExtTensor.smul_tmul, one_smul]
        have e2 : (op (c (z.1 * ψ (1 ⊗ₜ x₀)) ⊗ₜ[k] (1 : A₀)) • unitGen ψ : Corner ψ) =
            op ((1 : A) ⊗ₜ[k] x₀) • z := Subtype.ext (by
          change ψ 1 * ψ (c (z.1 * ψ (1 ⊗ₜ x₀)) ⊗ₜ 1) = z.1 * ψ (1 ⊗ₜ x₀)
          have h1 : ψ 1 = 1 := unitRight_map_one k ψ c hc
          exact (congrArg (· * ψ (c (z.1 * ψ (1 ⊗ₜ x₀)) ⊗ₜ 1)) h1).trans
            (by rw [one_mul, unitRight_map_tmul_one k ψ c hc, c.symm_apply_apply]))
        have e3 : (((1 : A) ⊗ₜ[k] x₀) • ExtTensor.tmul m (1 : A₀) : ExtTensor k M A₀) =
            ExtTensor.tmul m x₀ := by
          rw [ExtTensor.smul_tmul, smul_eq_mul, mul_one, one_smul]
        rw [e1, ← Ind.op_smul_tmul, e2, Ind.op_smul_tmul, e3]
      | add x x' hx hx' => rw [Ind.tmul_add, map_add, map_add, hx, hx']
    | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  right_inv m := by
    change c (ψ 1 * ψ (1 ⊗ₜ 1)) • m = m
    rw [← Algebra.TensorProduct.one_def, unitRight_map_one k ψ c hc, one_mul, map_one, one_smul]
  map_add' := map_add (indUnitRightFwd k ψ hψ c hc M)

theorem indUnitRight_smul (d : D) (y : IndK k (ExtTensor k M A₀) ψ) :
    indUnitRight k ψ hψ c hc M (d • y) = c d • indUnitRight k ψ hψ c hc M y :=
  indUnitRightFwd_smul k ψ hψ c hc M d y

/-- `indUnitRight` as a `k`-linear isomorphism. -/
def indUnitRightLinear : IndK k (ExtTensor k M A₀) ψ ≃ₗ[k] M :=
  { indUnitRight k ψ hψ c hc M with
    map_smul' := fun r y => by
      change indUnitRight k ψ hψ c hc M (algebraMap k D r • y) =
        r • indUnitRight k ψ hψ c hc M y
      rw [indUnitRight_smul, AlgEquiv.commutes, algebraMap_smul] }

end UnitRight

end InductionAlong

end

end Categorification
