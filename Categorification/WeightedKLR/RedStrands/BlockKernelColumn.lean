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

local notation "Bκ" κ => RedBlock.crossingSpace (k := k) E (mk (redProj k Q Λ ν κ))

private def columnInOrder (κ : List (Fin ℓ)) (hs : redWord s = κ) : C →ₗ[T] Bκ κ where
  toFun x := ⟨x.1,x.2.1,by
    change x.1 * mk (redProj k Q Λ ν κ) = x.1
    rw [← x.2.2, mul_assoc, ← map_mul, e_mul_redProj, ite_eq_left hs, x.2.2]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private abbrev columnIn : C →ₗ[T] B := columnInOrder Q Λ t s (redWord s) rfl

private theorem loading_sq : p * p = p := by rw [← map_mul,← map_mul,KLRAlgebra.e_mul_self]

private def columnOutOrder (κ : List (Fin ℓ)) : (Bκ κ) →ₗ[T] C where
  toFun x := ⟨x.1 * p, by rw [← mul_assoc,x.2.1], by rw [mul_assoc,loading_sq]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 p)
  map_smul' r x := Subtype.ext (mul_assoc r.1 x.1 p)

private abbrev columnOut : B →ₗ[T] C := columnOutOrder Q Λ t s (redWord s)

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

private abbrev orderedLoadings (κ : List (Fin ℓ)) : Finset (KLR.Seq (stendhalWeight ℓ ν)) :=
  Finset.univ.filter fun u => redWord u = κ

private theorem columnAssembly_sum (κ : List (Fin ℓ)) (y : Bκ κ) :
    ∑ u ∈ (orderedLoadings κ).attach,
      columnInOrder Q Λ t u.1 κ (Finset.mem_filter.mp u.2).2
        (columnOutOrder Q Λ t u.1 κ y) = y := by
  classical
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  change (∑ u ∈ (orderedLoadings κ).attach, y.1 * mk (ofKLR k Q Λ ν (KLRAlgebra.e u.1))) = y.1
  rw [Finset.sum_attach (orderedLoadings κ) (fun u => y.1 * mk (ofKLR k Q Λ ν (KLRAlgebra.e u)))]
  rw [← Finset.mul_sum, ← map_sum, ← map_sum]
  exact y.2.2

private abbrev projectKernel (κ : List (Fin ℓ)) (u : KLR.Seq (stendhalWeight ℓ ν)) :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := K) (columnOutOrder Q Λ t u κ)

private abbrev projectLoading (κ : List (Fin ℓ)) (u : KLR.Seq (stendhalWeight ℓ ν)) :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := P) (columnOutOrder Q Λ t u κ)

private abbrev restoreKernel (κ : List (Fin ℓ)) (u : ↥(orderedLoadings (ν := ν) κ)) :=
  BalancedTensor.mapRight (k := k) («B» := k) (M := K)
    (columnInOrder Q Λ t u.1 κ (Finset.mem_filter.mp u.2).2)

private theorem project_kernel_tensor (κ : List (Fin ℓ)) (u : KLR.Seq (stendhalWeight ℓ ν)) :
    (blockKernelColumnInclusion Q Λ t a b u).comp (projectKernel Q Λ t a b κ u) =
      (projectLoading Q Λ t κ u).comp (blockKernelTensorInclusion Q Λ t a b κ) :=
  BalancedTensor.extB fun _ _ => rfl

private theorem sum_kernel_tensor (κ : List (Fin ℓ)) :
    (∑ u ∈ (orderedLoadings (ν := ν) κ).attach,
      (restoreKernel Q Λ t a b κ u).comp (projectKernel Q Λ t a b κ u.1)) =
      (LinearMap.id : BalancedTensor k k T K (Bκ κ) →ₗ[k] _) := by
  apply BalancedTensor.extB
  intro x y
  refine (LinearMap.sum_apply (orderedLoadings (ν := ν) κ).attach
    (fun u => (restoreKernel Q Λ t a b κ u).comp (projectKernel Q Λ t a b κ u.1))
    (BalancedTensor.tmul x y)).trans ?_
  change (∑ u ∈ (orderedLoadings (ν := ν) κ).attach, BalancedTensor.mkBil k k T K (Bκ κ) x
      (columnInOrder Q Λ t u.1 κ (Finset.mem_filter.mp u.2).2
        (columnOutOrder Q Λ t u.1 κ y))) = BalancedTensor.mkBil k k T K (Bκ κ) x y
  let lift := BalancedTensor.mkBil k k T K (Bκ κ) x
  let cut (u : ↥(orderedLoadings (ν := ν) κ)) :=
    columnInOrder Q Λ t u.1 κ (Finset.mem_filter.mp u.2).2 (columnOutOrder Q Λ t u.1 κ y)
  have hcut : ∑ u ∈ (orderedLoadings (ν := ν) κ).attach, cut u = y :=
    columnAssembly_sum Q Λ t κ y
  exact (map_sum lift cut (orderedLoadings (ν := ν) κ).attach).symm.trans (congrArg lift hcut)

/-- The degree-one kernel test in Webster v2, §6.1, Lemma 6.8, (6.21), follows
from the tests in all bottom loading columns of the exchanged red order. -/
theorem blockKernelTensorInclusion_injective_of_columns (κ : List (Fin ℓ))
    (hcol : ∀ u : KLR.Seq (stendhalWeight ℓ ν), redWord u = κ →
      Function.Injective (blockKernelColumnInclusion Q Λ t a b u)) :
    Function.Injective (blockKernelTensorInclusion Q Λ t a b κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hzero (u : ↥(orderedLoadings (ν := ν) κ)) : projectKernel Q Λ t a b κ u.1 z = 0 := by
    refine hcol u.1 (Finset.mem_filter.mp u.2).2 ?_
    calc
      blockKernelColumnInclusion Q Λ t a b u.1 (projectKernel Q Λ t a b κ u.1 z) =
          projectLoading Q Λ t κ u.1 (blockKernelTensorInclusion Q Λ t a b κ z) :=
        LinearMap.congr_fun (project_kernel_tensor Q Λ t a b κ u.1) z
      _ = projectLoading Q Λ t κ u.1 0 := congrArg (projectLoading Q Λ t κ u.1) hz
      _ = 0 := map_zero (projectLoading Q Λ t κ u.1)
      _ = blockKernelColumnInclusion Q Λ t a b u.1 0 := (map_zero _).symm
  have hsum := LinearMap.congr_fun (sum_kernel_tensor Q Λ t a b κ) z
  have heval := LinearMap.sum_apply (orderedLoadings (ν := ν) κ).attach
    (fun u => (restoreKernel Q Λ t a b κ u).comp (projectKernel Q Λ t a b κ u.1)) z
  refine hsum.symm.trans (heval.trans (Finset.sum_eq_zero fun u _ => ?_))
  exact (congrArg (restoreKernel Q Λ t a b κ u) (hzero u)).trans (map_zero _)

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

/-- A violated bottom loading has zero coefficient column and gives an
injective balanced inclusion. -/
theorem blockKernelColumnInclusion_injective_of_violated_bottom (hs : IsViolated s) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) := by
  have lower (y : C) : y = 0 := by
    apply Subtype.ext
    have hy := y.2.2
    change y.1 * p = y.1 at hy
    have hp : p = 0 := violMk_e hs
    exact hy.symm.trans ((congrArg (fun z : V => y.1 * z) hp).trans (mul_zero _))
  have zero (z : BalancedTensor k k T K C) : z = 0 := by
    induction z using BalancedTensor.induction_on with
    | zero => rfl
    | tmul x y =>
      have h := congrArg (BalancedTensor.tmul (k := k) («B» := k) (A := T) x) (lower y)
      exact h.trans (BalancedTensor.tmul_zero x)
    | add x y hx hy =>
      exact (congrArg₂ (fun s t : BalancedTensor k k T K C => s+t) hx hy).trans (zero_add 0)
  intro x y _
  exact (zero x).trans (zero y).symm

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


section PrincipalHigherCorner

local notation "μ" => stendhalWeight ℓ ν
local notation "pof" => fun v : KLR.Seq μ => mk (ofKLR k Q Λ ν (KLRAlgebra.e v))
local notation "ordT" => isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
local notation "inc" => blockKernelColumnInclusion Q Λ t a b s

private theorem block_loading_order_support (t u : KLR.Seq μ) (hu : redWord u=redWord t) :
    let r := mk (redProj k Q Λ ν (redWord t))
    r*(pof u)=pof u ∧ (pof u)*r=pof u := by
  dsimp only
  constructor
  · rw [← map_mul, redProj_mul_e, ite_eq_left hu]
  · rw [← map_mul, e_mul_redProj, ite_eq_left hu]

private theorem principalRep_val (u : KLR.Seq μ) (c : V) (cl : pof t*c=c) (cr : c*pof u=c)
    (hu : redWord u=redWord t) : (blockLoadingRep Q Λ t c).1.1=c := by
  rw [blockLoadingRep_val,cl]
  calc
    c*E = (c*pof u)*E := congrArg (·*E) cr.symm
    _ = _ := by rw [mul_assoc,(block_loading_order_support Q Λ t u hu).2,cr]

private def principalGenerator (u : KLR.Seq μ) (c : V) (hc : c ∈ J) (cl : pof t*c=c)
    (cr : c*pof u=c) (hu : redWord u=redWord t) : K := by
  refine ⟨blockLoadingRep Q Λ t c,?_⟩
  change (blockLoadingRep Q Λ t c).1.1 ∈ J
  rw [principalRep_val Q Λ t u c cl cr hu]
  exact hc

private theorem principalCoefficient
    (u : KLR.Seq μ) (hu : redWord u = redWord t) (c : V) (g : K) (val : g.1.1.1 = c)
    (factor : ∀ x : V, x ∈ J → pof t * x = x → ∃ y : V, pof u * y = y ∧ c * y = x)
    (x : K) : ∃ r : T, pof u * r.1 = r.1 ∧ MulOpposite.op r • g = x := by
  have raw : pof t*x.1.1.1=x.1.1.1 := congrArg (fun y : T => y.1) x.1.2
  obtain ⟨v,hv,hcv⟩ := factor _ x.2 raw
  have vR : E*v=v := calc
    _ = E*(pof u*v) := congrArg (E*·) hv.symm
    _ = _ := by rw [← mul_assoc,(block_loading_order_support Q Λ t u hu).1,hv]
  let r : T := ⟨v*E,(Subsemigroup.mem_corner_iff ordT).2
    ⟨by rw [← mul_assoc,vR],by rw [mul_assoc,(ordT).eq]⟩⟩
  refine ⟨r,by change pof u*(v*E)=v*E; rw [← mul_assoc,hv],?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change g.1.1.1*(v*E)=x.1.1.1
  rw [val,← mul_assoc,hcv]
  exact CornerEndomorphism.corner_mul_right ordT x.1.1

/-- A cyclic higher corner reduces the tensor inclusion to cancellation of
one left factor on the corresponding corner of the violated quotient. -/
theorem blockKernelColumnInclusion_injective_of_principal_factor
    (u : KLR.Seq μ) (hu : redWord u=redWord t) (c : V) (hc : c ∈ J) (cl : pof t*c=c) (cr : c*pof u=c)
    (factor : ∀ x : V, x ∈ J → pof t*x=x → ∃ y : V, pof u*y=y ∧ c*y=x)
    (cancel : ∀ y : V, pof u*y=y → y*pof s=y → c*y=0 → y=0) :
    Function.Injective inc := by
  let g := principalGenerator Q Λ t a b u c hc cl cr hu
  have val : g.1.1.1=c := principalRep_val Q Λ t u c cl cr hu
  have coefficient := principalCoefficient Q Λ t a b u hu c g val factor
  have single (z : BalancedTensor k k T K C) :
      ∃ y : C, pof u*y.1=y.1 ∧ z=BalancedTensor.tmul g y := by
    induction z using BalancedTensor.induction_on with
    | zero => exact ⟨0,mul_zero _,(BalancedTensor.tmul_zero g).symm⟩
    | tmul x l =>
      obtain ⟨r,hr,part⟩ := coefficient x
      have rep := congrArg (fun w : K => (BalancedTensor.tmul w l : BalancedTensor k k T K C)) part
      exact ⟨r • l,by change pof u*(r.1*l.1)=r.1*l.1; rw [← mul_assoc,hr],
        rep.symm.trans (BalancedTensor.op_smul_tmul g r l)⟩
    | add x y hx hy =>
      obtain ⟨l,hl,el⟩ := hx
      obtain ⟨r,hr,er⟩ := hy
      have raw : pof u*(l.1+r.1)=l.1+r.1 := by rw [mul_add,hl,hr]
      exact ⟨l+r,raw,(congrArg₂ (·+·) el er).trans (BalancedTensor.tmul_add g l r).symm⟩
  apply (injective_iff_map_eq_zero inc).mpr
  intro z hz
  obtain ⟨y,hy,hrep⟩ := single z
  let stack := (blockLoadingTensorStack Q Λ t (redWord s)).comp embP
  have obs : stack (inc z)=0 := (congrArg stack hz).trans (map_zero stack)
  have raw : g.1.1.1*y.1=0 := (congrArg (fun x => stack (inc x)) hrep).symm.trans obs
  have cz := (congrArg (·*y.1) val).symm.trans raw
  have y0 : y=0 := Subtype.ext (cancel y.1 hy y.2.2 cz)
  exact hrep.trans ((congrArg (fun l : C => BalancedTensor.tmul g l) y0).trans
    (BalancedTensor.tmul_zero g))

/-- A principal higher coefficient that detects zero on the source corner
identifies the higher kernel with a loading projective. -/
theorem blockLoadingKernel_projective_of_principal_factor
    (u : KLR.Seq μ) (hu : redWord u = redWord t) (c : V) (hc : c ∈ J)
    (cl : pof t * c = c) (cr : c * pof u = c)
    (factor : ∀ x : V, x ∈ J → pof t * x = x → ∃ y : V, pof u * y = y ∧ c * y = x)
    (cancel : ∀ y : V, pof u * y = y → y * E = y → c * y = 0 → y = 0) :
    Module.Projective Tᵐᵒᵖ K := by
  let U : T := ⟨pof u, (Subsemigroup.mem_corner_iff ordT).2
    (block_loading_order_support Q Λ t u hu)⟩
  have hU : IsIdempotentElem U :=
    Subtype.ext (((show IsIdempotentElem (KLRAlgebra.e u : KLRAlgebra k (stendhalQ Q Λ) μ) from
      KLRAlgebra.e_mul_self _).map (ofKLR k Q Λ ν)).map mk).eq
  let g := principalGenerator Q Λ t a b u c hc cl cr hu
  have val : g.1.1.1 = c := principalRep_val Q Λ t u c cl cr hu
  let f : rIdeal U →ₗ[Tᵐᵒᵖ] K :=
    { toFun := fun d => MulOpposite.op d.1 • g
      map_add' := fun d e => by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change _ * (d.1.1 + e.1.1) = _ * d.1.1 + _ * e.1.1
        exact mul_add _ _ _
      map_smul' := fun r d => by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        change _ * (d.1.1 * r.unop.1) = (_ * d.1.1) * r.unop.1
        exact (mul_assoc _ _ _).symm }
  have hinj : Function.Injective f := by
    intro d e hde
    let delta := d - e
    have hδ : f delta = 0 := (f.map_sub d e).trans (sub_eq_zero.mpr hde)
    have hz : c * delta.1.1 = 0 := by
      rw [← val]
      exact congrArg (fun z : K => z.1.1.1) hδ
    have hleft : pof u * delta.1.1 = delta.1.1 := congrArg (fun z : T => z.1) delta.2
    have hright : delta.1.1 * E = delta.1.1 := CornerEndomorphism.corner_mul_right ordT delta.1
    have hzero : delta = 0 := Subtype.ext (Subtype.ext (cancel _ hleft hright hz))
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨r, hr, hrep⟩ := principalCoefficient Q Λ t a b u hu c g val factor x
    exact ⟨⟨r, Subtype.ext hr⟩, hrep⟩
  let : Module.Projective Tᵐᵒᵖ (rIdeal U) := rIdeal_projective hU
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end PrincipalHigherCorner

end Categorification.Stendhal.BraidedStendhalAlgebra
