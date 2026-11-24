/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelBottom

/-!
# Injectivity on a bottom column of the braiding bimodule

Webster, arXiv:1309.3796v2, §6.1, proof after (6.21) in Lemma 6.8. A loading column
`B e(s)` splits off the braiding as a left module over the *source* ordered algebra.
When the exchanged reds occupy consecutive positions of `s`, tensoring the higher
submodule inclusion with this column is injective. This is the actual inclusion on
both balanced tensors, not a statement about its image in a diagram quotient.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (s : KLR.Seq (stendhalWeight ℓ ν))
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "E" => mk (redProj k Q Λ ν (redWord t))
local notation "F" => mk (redProj k Q Λ ν (redWord s))
local notation "p" => mk (ofKLR k Q Λ ν (KLRAlgebra.e s))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "B" => RedBlock.crossingSpace (k := k) E F
local notation "C" => RedBlock.crossingSpace (k := k) E p
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b

private local instance {R : Type*} [Ring R] [Algebra k R] {u v : R} (hu : IsIdempotentElem u) :
    IsScalarTower k hu.Corner (RedBlock.crossingSpace (k := k) u v) where
  smul_assoc c r x := Subtype.ext (smul_mul_assoc c r.1 x.1)

private def columnIn : C →ₗ[T] B where
  toFun x := ⟨x.1,x.2.1,by
    calc x.1 * F = (x.1 * p) * F := congrArg (· * F) x.2.2.symm
         _ = x.1 := by rw [mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left rfl, x.2.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem loading_sq : p * p = p := by rw [← map_mul,← map_mul,KLRAlgebra.e_mul_self]

private def columnOut : B →ₗ[T] C where
  toFun x := ⟨x.1 * p, by rw [← mul_assoc,x.2.1], by rw [mul_assoc,loading_sq]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 p)
  map_smul' r x := Subtype.ext (mul_assoc r.1 x.1 p)

/-- The map in (6.21) on the right loading `s`, formed by tensoring `K ↪ e(t)T`
with `B e(s)` over `T`. -/
def blockKernelColumnInclusion : BalancedTensor k k T K C →ₗ[k] BalancedTensor k k T P C :=
  BalancedTensor.mapLeftBimodule k C ((K).subtype.restrictScalars k) (fun _ _ => rfl)

local notation "emb" => BalancedTensor.mapRight (k := k) («B» := k) (M := K) (columnIn Q Λ t s)
local notation "out" => BalancedTensor.mapRight (k := k) («B» := k) (M := K) (columnOut Q Λ t s)
local notation "botMap" => blockKernelBottom Q Λ t a b s

private theorem recoverColumn : (out).comp ((botMap).comp emb) = LinearMap.id := by
  apply BalancedTensor.ext; intro x y
  change BalancedTensor.tmul x _ = (BalancedTensor.tmul x y : BalancedTensor k k T K C)
  apply congrArg; apply Subtype.ext
  change (y.1 * p) * p = y.1
  rw [y.2.2,y.2.2]

local notation "embP" => BalancedTensor.mapRight (k := k) («B» := k) (M := P) (columnIn Q Λ t s)

private theorem includeColumn (z : BalancedTensor k k T K C) :
    blockKernelTensorInclusion Q Λ t a b (redWord s) (emb z) = embP (blockKernelColumnInclusion Q Λ t a b s z) :=
  LinearMap.congr_fun (show (blockKernelTensorInclusion Q Λ t a b (redWord s)).comp emb =
    (embP).comp (blockKernelColumnInclusion Q Λ t a b s) from BalancedTensor.ext fun _ _ => rfl) z

private theorem columnInjective {X Y U D : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup U] [Module k U] [AddCommGroup D] [Module k D]
    (i : X →ₗ[k] Y) (j : U →ₗ[k] D) (b : U →ₗ[k] U)
    (u : X →ₗ[k] U) (v : Y →ₗ[k] D) (w : U →ₗ[k] X) (hu : w.comp (b.comp u) = LinearMap.id)
    (H : LinearMap.ker j ≤ LinearMap.ker b) (hn : ∀ z, j (u z) = v (i z)) : Function.Injective i := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have zero : j (u z) = 0 := (hn z).trans (hz ▸ map_zero _)
  have hb : b (u z) = 0 := H zero
  exact (LinearMap.congr_fun hu z).symm.trans ((congrArg w hb).trans (map_zero _))

/-- A single bottom loading is a split summand on both sides of the tensor
inclusion. Used to restrict the first-black-weight proof of the kernel test
following Webster v2, (6.21), to an interleaved loading. -/
theorem blockKernelColumnInclusion_injective_of_tensor
    (hi : Function.Injective (blockKernelTensorInclusion Q Λ t a b (redWord s))) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) :=
  columnInjective (k := k) (X := BalancedTensor k k T K C) (Y := BalancedTensor k k T P C)
    (U := BalancedTensor k k T K B) (D := BalancedTensor k k T P B)
    (blockKernelColumnInclusion Q Λ t a b s) (blockKernelTensorInclusion Q Λ t a b (redWord s))
    botMap emb embP out (recoverColumn Q Λ t a b s)
    (fun _ hx => (congrArg (fun z => botMap z) (hi (hx.trans (map_zero _).symm))).trans (map_zero _))
    (includeColumn Q Λ t a b s)

/-- Read a relation between two marked cuts in the loading column when the full
kernel inclusion has been proved injective. In the first weight this identifies
the relations of the two-exit presentation following Webster v2, (6.21). -/
theorem blockKernelColumn_pair_eq_zero_iff
    (hi : Function.Injective (blockKernelTensorInclusion Q Λ t a b (redWord s)))
    (x y : K) (l r : C) :
    (BalancedTensor.tmul x l + BalancedTensor.tmul y r : BalancedTensor k k T K C) = 0 ↔
      x.1.1.1 * l.1 + y.1.1.1 * r.1 = 0 := by
  let f := ((blockLoadingTensorStack Q Λ t (redWord s)).comp
    (blockKernelTensorInclusion Q Λ t a b (redWord s))).comp emb
  have retract (z : BalancedTensor k k T K C) := LinearMap.congr_fun (recoverColumn Q Λ t a b s) z
  have he : Function.Injective emb := fun z w h => (retract z).symm.trans
    ((congrArg (fun v => out (botMap v)) h).trans (retract w))
  have hf : Function.Injective f := (blockLoadingTensorStack_injective Q Λ t (redWord s)).comp (hi.comp he)
  have val : f (BalancedTensor.tmul x l + BalancedTensor.tmul y r) = x.1.1.1*l.1 + y.1.1.1*r.1 :=
    map_add f _ _
  exact ⟨fun h => val.symm.trans ((congrArg f h).trans (map_zero f)),fun h => hf (val.trans (h.trans (map_zero f).symm))⟩

/-- **Injectivity in (6.21) at consecutive exchanged reds.** Webster v2, §6.1, Lemma
6.8. The top may be any source loading, with arbitrary spectators and black contents.
The consecutive-position restriction is only on the bottom column; the proof uses a
common last red crossing, which need not exist when the bottom reds enclose a black. -/
theorem blockKernelColumnInclusion_injective (hQ : KLRSymm Q)
    (L M : List (Fin ℓ)) (ht : redWord t = L ++ a :: b :: M)
    (u : KLR.Seq (stendhalWeight ℓ ν)) (hu : redWord u = redWord t)
    (n : ℕ) (hn : n+1 < (stendhalWeight ℓ ν).card)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,hn⟩ = .inr b)
    (hs : sadj (stendhalWeight ℓ ν).card n • u = s) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) :=
  columnInjective (k := k) (X := BalancedTensor k k T K C) (Y := BalancedTensor k k T P C)
    (U := BalancedTensor k k T K B) (D := BalancedTensor k k T P B)
    (blockKernelColumnInclusion Q Λ t a b s) (blockKernelTensorInclusion Q Λ t a b (redWord s))
    botMap emb embP out (recoverColumn Q Λ t a b s)
    (ker_blockKernelTensorInclusion_le_ker_bottom Q Λ t a b s hQ L M ht u hu n hn ha hb hs)
    (includeColumn Q Λ t a b s)


open scoped BigOperators

section BottomFamily

variable (κ' : List (Fin ℓ))
local notation "μ" => stendhalWeight ℓ ν
local notation "Sκ" => {u : KLR.Seq μ // redWord u=κ'}
local notation "Bκ" => RedBlock.crossingSpace (k := k) E (mk (redProj k Q Λ ν κ'))
local notation "Cof" => fun u : KLR.Seq μ =>
  RedBlock.crossingSpace (k := k) E (mk (ofKLR k Q Λ ν (KLRAlgebra.e u)))
local notation "pof" => fun u : KLR.Seq μ => mk (ofKLR k Q Λ ν (KLRAlgebra.e u))
local notation "Full" => blockKernelTensorInclusion Q Λ t a b κ'

@[instance_reducible] private noncomputable def bottomFamilyFintype : Fintype Sκ := by
  classical
  exact inferInstance

attribute [local instance 1100] bottomFamilyFintype

private def familyIn (u : Sκ) : Cof u.1 →ₗ[T] Bκ := by
  obtain ⟨u,hu⟩ := u
  subst κ'
  exact columnIn Q Λ t u

private def familyOut (u : Sκ) : Bκ →ₗ[T] Cof u.1 := by
  obtain ⟨u,hu⟩ := u
  subst κ'
  exact columnOut Q Λ t u

private theorem family_value (u : Sκ) (y : Bκ) :
    (familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y)).1=y.1*pof u.1 := by
  obtain ⟨u,hu⟩ := u
  subst κ'
  rfl

private def cutK (u : Sκ) : BalancedTensor k k T K Bκ →ₗ[k] BalancedTensor k k T K (Cof u.1) :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := K) (familyOut Q Λ t κ' u)

private def cutP (u : Sκ) : BalancedTensor k k T P Bκ →ₗ[k] BalancedTensor k k T P (Cof u.1) :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := P) (familyOut Q Λ t κ' u)

private def putK (u : Sκ) : BalancedTensor k k T K (Cof u.1) →ₗ[k] BalancedTensor k k T K Bκ :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := K) (familyIn Q Λ t κ' u)

private theorem column_square (u : Sκ) :
    (blockKernelColumnInclusion Q Λ t a b u.1).comp (cutK Q Λ t a b κ' u) =
      (cutP Q Λ t κ' u).comp Full := by
  apply BalancedTensor.ext
  intro z y
  rfl

private theorem family_sum (y : Bκ) :
    (∑ u : Sκ, familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y))=y := by
  classical
  apply Subtype.ext
  change (Bκ).subtype (∑ u : Sκ, familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y))=y.1
  rw [map_sum]
  simp only [Submodule.subtype_apply,family_value,← Finset.mul_sum]
  have all : (∑ u : Sκ, pof u.1) = mk (redProj k Q Λ ν κ') := by
    calc
      _ = ∑ u ∈ Finset.univ.map (Function.Embedding.subtype (fun u : KLR.Seq μ => redWord u = κ')), pof u := by
        rw [Finset.sum_map]
        rfl
      _ = _ := by rw [Finset.univ_map_subtype, redProj, redIdem, map_sum, map_sum]
  rw [all]
  exact y.2.2

private theorem put_cut_tmul (u : Sκ) (x : K) (y : Bκ) :
    putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u (BalancedTensor.tmul x y)) =
      BalancedTensor.tmul x (familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y)) := by
  rfl

private theorem put_cut_add (u : Sκ) (x y : BalancedTensor k k T K Bκ) :
    putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u (x+y)) =
      putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u x) +
        putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u y) :=
  (congrArg (putK Q Λ t a b κ' u) (map_add (cutK Q Λ t a b κ' u) x y)).trans
    (map_add (putK Q Λ t a b κ' u) _ _)

private theorem tensor_family_sum (z : BalancedTensor k k T K Bκ) :
    (∑ u : Sκ, putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u z))=z := by
  classical
  induction z using BalancedTensor.induction_on with
  | zero => simp only [map_zero,Finset.sum_const_zero]
  | tmul x y =>
    calc
      _ = ∑ u : Sκ, BalancedTensor.tmul x (familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y)) :=
        Finset.sum_congr rfl (fun u _ => put_cut_tmul Q Λ t a b κ' u x y)
      _ = BalancedTensor.tmul x (∑ u : Sκ, familyIn Q Λ t κ' u (familyOut Q Λ t κ' u y)) :=
        (BalancedTensor.tmul_sum Finset.univ x _).symm
      _ = _ := congrArg (BalancedTensor.tmul (k := k) («B» := k) (A := T) x)
        (family_sum Q Λ t κ' y)
  | add x y hx hy =>
    let g (z : BalancedTensor k k T K Bκ) (u : Sκ) :=
      putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u z)
    change (∑ u : Sκ, g (x+y) u) = x+y
    calc
      _ = ∑ u : Sκ, (g x u + g y u) :=
        Finset.sum_congr rfl (fun u _ => put_cut_add Q Λ t a b κ' u x y)
      _ = (∑ u : Sκ, g x u) + ∑ u : Sκ, g y u := Finset.sum_add_distrib
      _ = _ := congrArg₂ (· + ·) hx hy

private theorem column_zero_of_full (u : Sκ) (z : BalancedTensor k k T K Bκ)
    (hz : Full z=0) :
    blockKernelColumnInclusion Q Λ t a b u.1 (cutK Q Λ t a b κ' u z) = 0 :=
  (LinearMap.congr_fun (column_square Q Λ t a b κ' u) z).trans
    ((congrArg (cutP Q Λ t κ' u) hz).trans (map_zero (cutP Q Λ t κ' u)))

/-- The kernel inclusion over the full bottom red order is injective if it is
injective on each of its idempotent loading columns. -/
theorem blockKernelTensorInclusion_injective_of_columns
    (h : ∀ u : KLR.Seq μ, redWord u=κ' →
      Function.Injective (blockKernelColumnInclusion Q Λ t a b u)) :
    Function.Injective Full := by
  classical
  apply (injective_iff_map_eq_zero Full).mpr
  intro z hz
  have hc (u : Sκ) : cutK Q Λ t a b κ' u z=0 :=
    h u.1 u.2 ((column_zero_of_full Q Λ t a b κ' u z hz).trans
      (map_zero (blockKernelColumnInclusion Q Λ t a b u.1)).symm)
  calc
    z = ∑ u : Sκ, putK Q Λ t a b κ' u (cutK Q Λ t a b κ' u z) :=
      (tensor_family_sum Q Λ t a b κ' z).symm
    _ = ∑ _ : Sκ, (0 : BalancedTensor k k T K Bκ) :=
      Finset.sum_congr rfl (fun u _ => (congrArg (putK Q Λ t a b κ' u) (hc u)).trans
        (map_zero (putK Q Λ t a b κ' u)))
    _ = 0 := Finset.sum_const_zero

end BottomFamily

end Categorification.Stendhal.BraidedStendhalAlgebra
