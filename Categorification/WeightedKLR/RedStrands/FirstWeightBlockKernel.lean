/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockExitDivision
import Categorification.WeightedKLR.RedStrands.BraidedAppendFlip
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.WeightedKLR.RedStrands.InterleavedColumn

/-!
# The higher kernel with one black strand

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, kernel test after (6.21).
In the first black weight there is only one black strand *in the whole diagram*.
Relative to a fixed top, all strictly higher loadings have it further left. PBW
division at successive forced crossings presents the higher row with one generator.
The same division on the globally violated ideal detects that generator on the
crossing bimodule. The proof works at positive pairings, without cancelling dots in
the violated algebra or assuming that an unmarked braid coefficient is higher.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (i : I)
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "β" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ β
local notation "m" => Multiset.card μ
local notation "raw" => ofKLR k Q Λ β
local notation "mk" => violMk k Q Λ β
local notation "V" => ViolQuotient k Q Λ β
local notation "π" => AlgHom.comp mk raw
local notation "p" => fun s : KLR.Seq μ => π (e s)

omit [DecidableEq I] in
private theorem only_black (s : KLR.Seq μ) {x y : Fin m} {a b : I}
    (hx : s.lbl x = .inl a) (hy : s.lbl y = .inl b) : x = y := by
  classical
  have eq (z : Fin m) {c : I} (h : s.lbl z = .inl c) : c = i := by
    have mem := s.mem z; change s.lbl z ∈ μ at mem; rw [h] at mem
    simpa [stendhalWeight] using mem
  have nd : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]; simp [stendhalWeight,List.nodup_ofFn,Sum.inr_injective]
  exact Multiset.inj_on_of_nodup_map nd x (by simp) y (by simp) (hx.trans ((congrArg Sum.inl ((eq x hx).trans (eq y hy).symm)).trans hy.symm))

variable (a b : Fin ℓ) (α : Fin ℓ → I → ℕ) (κ : List (Fin ℓ))
local notation "root" => adjacentBlockRoot a b (ν := β)
local notation "J" => blockUpperIdeal k Q Λ β a b α κ
variable (s : KLR.Seq (stendhalWeight ℓ (Singleton.singleton i : Multiset I))) (j : ℕ)
    (hj : j+1 < (stendhalWeight ℓ (Singleton.singleton i : Multiset I)).card)
local notation "v" => sadj m j • s
local notation "c" => π (ψ j * e s)

omit [DecidableEq I] in
private theorem violated_descent {d : I} (hi : s.lbl ⟨j+1,hj⟩ = .inl d)
    (u : KLR.Seq μ) (hu : IsViolated u) (w : Perm (Fin m)) (hw : w • s = u) :
    w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ := by
  subst u; obtain ⟨h,hb⟩ := hu
  obtain ⟨d',hd⟩ : ∃ d', (w • s).lbl ⟨0,h⟩ = .inl d' := by
    cases he : (w • s).lbl ⟨0,h⟩ with
    | inl z => exact ⟨z,rfl⟩
    | inr r => simp [he] at hb
  have h0 := only_black i (w • s) (x := w ⟨j+1,hj⟩) (by simpa [lbl_smul] using hi) hd
  apply lt_of_le_of_ne (by rw [h0]; exact Nat.zero_le _)
  exact w.injective.ne (by intro h; have := congrArg Fin.val h; simp at this)

private theorem higher_descent {d : I} {r : Fin ℓ} (hr : s.lbl ⟨j,by omega⟩ = .inr r)
    (hi : s.lbl ⟨j+1,hj⟩ = .inl d) (hs : redWord s = κ) (hn : ¬α < root s)
    (u : KLR.Seq μ) (ho : redWord u = κ) (hh : α < root u) (w : Perm (Fin m)) (hw : w • s = u) :
    w ⟨j+1,hj⟩ < w ⟨j,by omega⟩ := by
  subst u; by_contra! h
  have ord := (redWord_smul_eq_iff s w 1).1 (by rw [one_smul,hs,ho])
  apply hn (hh.trans_le ?_)
  intro q color
  unfold adjacentBlockRoot blockBlackCount
  refine Finset.card_le_card_of_injOn w.symm ?_ w.symm.injective.injOn
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine ⟨hx.1,fun y r' hr' hy => ?_⟩
  have eq := only_black i s hx.1 hi
  have wx : w ⟨j+1,hj⟩ = x := by rw [← eq]; exact w.apply_symm_apply x
  have lt : x < w y := hx.2 (w y) r' hr' (by simpa [lbl_smul] using hy)
  rw [eq]; by_contra! he
  have yl : y.val ≤ j := by
    have ne : y ≠ ⟨j+1,hj⟩ := by rintro rfl; rw [hi] at hy; contradiction
    exact Nat.le_of_lt_succ (lt_of_le_of_ne he (fun e => ne (Fin.ext e)))
  rcases lt_or_eq_of_le yl with hlt | hEq
  · have wy := (ord y ⟨j,by omega⟩ r' r hy hr).2 (show y < ⟨j,by omega⟩ from hlt)
    exact (not_lt_of_ge (wy.le.trans h)) (wx ▸ lt)
  · rw [show y = ⟨j,by omega⟩ from Fin.ext hEq] at lt
    exact (not_lt_of_ge h) (wx ▸ lt)

/-- Saturation at a one-black ordered exit in Webster v2, (6.21). Membership
of the crossed coefficient alone implies membership of its joint coefficient.
Neither the right exit nor the joint is assumed to be a higher loading. -/
theorem firstWeight_exit_saturated (hQ : KLRSymm Q) {r : Fin ℓ} {d : I}
    (hr : s.lbl ⟨j,by omega⟩ = .inr r) (hi : s.lbl ⟨j+1,hj⟩ = .inl d)
    (hs : redWord s = κ) (z : V) (hz : z*c ∈ J) : z*p v ∈ J := by
  by_cases hn : α < root s
  · exact (J).mul_mem_left _ _ (TwoSidedIdeal.subset_span ⟨v,
      (redWord_sadj_smul s hj (by simp [hi])).trans hs,
      hn.trans_le (adjacentBlockRoot_le_left_cross a b s j hj r d hr hi),rfl⟩)
  obtain ⟨y,hy,he⟩ := exists_exitIdeal_factor Q Λ s j hj mk violMk_surjective hQ
    (fun u => redWord u = κ ∧ α < root u)
    (fun u h => higher_descent i a b α κ s j hj hr hi hs hn u h.1 h.2) (z := z*c)
    (by simpa only [blockUpperIdeal,and_assoc,AlgHom.comp_apply] using hz)
  change z*c*p s = y*c at he
  rw [mul_assoc,← map_mul π,mul_assoc,e_mul_self] at he
  have eq := viol_exit_cross_cancel Q Λ s j hj hQ d r hr hi (violated_descent i s j hj hi) (z-y)
    (by change (z-y)*c = 0; rw [sub_mul,he,sub_self])
  change (z-y)*p v = 0 at eq
  rw [sub_mul,sub_eq_zero] at eq
  rw [eq]; apply (J).mul_mem_right
  simpa only [blockUpperIdeal,and_assoc,AlgHom.comp_apply] using hy

/-- A PBW generator from `s` to the first higher loading reached by moving the
black left, or to the global violation if no higher cut is reached first. -/
private def HasExitGenerator : Prop := ∃ (u : KLR.Seq μ) (g : V), redWord u = κ ∧
    g ∈ J ∧ p u*g = g ∧ g*p s = g ∧
    (∀ z ∈ J, ∃ d : V, z*p s = d*g) ∧ (∀ z : V, z*g = 0 → z*p u = 0)

private theorem generator_at (hs : redWord s = κ) (h : p s ∈ J) : HasExitGenerator i Q Λ a b α κ s := by
  have idem : p s*p s = p s := by rw [← map_mul π,e_mul_self]
  exact ⟨s,p s,hs,h,idem,idem,fun z _ => ⟨z,rfl⟩,fun _ => id⟩

private theorem higher_generator (hQ : KLRSymm Q) (n : ℕ) (hn : n < m) (d : I)
    (hb : s.lbl ⟨n,hn⟩ = .inl d) (hs : redWord s = κ) : HasExitGenerator i Q Λ a b α κ s := by
  induction n generalizing s with
  | zero =>
    apply generator_at _ _ _ _ _ _ _ _ hs
    have hv : IsViolated s := ⟨hn,by simp [hb]⟩
    change mk (raw (e s)) ∈ J; rw [violMk_e hv]; exact (J).zero_mem
  | succ n ih =>
    by_cases hh : α < root s
    · exact generator_at _ _ _ _ _ _ _ _ hs (TwoSidedIdeal.subset_span ⟨s,hs,hh,rfl⟩)
    let u := sadj m n • s
    obtain ⟨r,hr⟩ : ∃ r, s.lbl ⟨n,by omega⟩ = .inr r := by
      cases eq : s.lbl ⟨n,by omega⟩ with
      | inr r => exact ⟨r,rfl⟩
      | inl d' => have he := congrArg Fin.val (only_black i s eq hb); simp at he
    have hu : redWord u = κ := (redWord_sadj_smul s hn (by simp [hb])).trans hs
    have moved : u.lbl ⟨n,by omega⟩ = .inl d := by change (sadj m n • s).lbl _ = _; rw [lbl_sadj,sadj_apply_left hn,hb]
    obtain ⟨h,g,ho,hg,eg,ge,gen,det⟩ := ih u (by omega) moved hu
    let C := π (ψ n * e s)
    have cs : C*p s = C := by change π _ * π _ = _; rw [← map_mul π,mul_assoc,e_mul_self]
    have uc : p u*C = C := by
      change π (e (sadj m n • s)) * π (ψ n * e s) = _
      rw [← map_mul π,ψ_mul_e n s,← mul_assoc,e_mul_self]; exact congrArg π (ψ_mul_e n s).symm
    refine ⟨h,g*C,ho,(J).mul_mem_right _ _ hg,by rw [← mul_assoc,eg],by rw [mul_assoc,cs],?_,?_⟩
    · intro z hz
      obtain ⟨y,hy,he⟩ := exists_exitIdeal_factor Q Λ s n hn mk violMk_surjective hQ
        (fun l => redWord l = κ ∧ α < root l)
        (fun l hl => higher_descent i a b α κ s n hn hr hb hs hh l hl.1 hl.2) (z := z)
        (by simpa only [blockUpperIdeal,and_assoc,AlgHom.comp_apply] using hz)
      obtain ⟨x,hx⟩ := gen y (by simpa only [blockUpperIdeal,and_assoc,AlgHom.comp_apply] using hy)
      change z*p s = y*C at he
      exact ⟨x,by rw [he,← mul_assoc,← hx,mul_assoc,uc]⟩
    · intro z hz
      apply det
      have eq := viol_exit_cross_cancel Q Λ s n hn hQ d r hr hb (violated_descent i s n hn hb) (z*g)
        (by change z*g*C = 0; rwa [mul_assoc])
      change z*g*p u = 0 at eq; rwa [mul_assoc,ge] at eq

private theorem upper_flip {x : V} (h : x ∈ J) : violFlip x ∈ J := by
  rw [blockUpperIdeal,TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  induction h using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨_,⟨l,-,_,⟨u,hu,hh,rfl⟩,rfl⟩,d,-,rfl⟩ := hx
    change (violFlipHom k Q Λ β (_ * _ * _)).unop ∈ J
    simp only [map_mul,unop_mul]
    apply (J).mul_mem_left; apply (J).mul_mem_right
    change violFlip (mk (raw (e u))) ∈ J
    rw [violFlip_violMk,flip_e]; exact TwoSidedIdeal.subset_span ⟨u,hu,hh,rfl⟩
  | zero => simpa only [violFlip,map_zero,unop_zero] using (J).zero_mem
  | add _ _ _ _ hx hy => simpa only [violFlip,map_add,unop_add] using (J).add_mem hx hy
  | neg _ _ hx => simpa only [violFlip,map_neg,unop_neg] using (J).neg_mem hx

private theorem reflect_mul (x y : V) : violFlip (x*y) = violFlip y * violFlip x :=
  congrArg unop (map_mul (violFlipHom k Q Λ β) x y)
private theorem reflect_p (u : KLR.Seq μ) : violFlip (p u) = p u := congrArg mk (flip_e _)

variable (t : KLR.Seq (stendhalWeight ℓ (Singleton.singleton i : Multiset I))) (κ' : List (Fin ℓ))
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "E" => mk (redProj k Q Λ β (redWord t))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ β (redWord t))
local notation "B" => RedBlock.crossingSpace (k := k) E (mk (redProj k Q Λ β κ'))
local notation "Z" => BalancedTensor k k T K B
local notation "inc" => blockKernelTensorInclusion Q Λ t a b κ'

private theorem cyclic_mark (hQ : KLRSymm Q) : ∃ (u : KLR.Seq μ) (g : K),
    (∀ x : K, ∃ d : T, x = op d • g) ∧ (∀ y : B, g.1.1.1 * y.1 = 0 → p u*y.1 = 0) ∧
    redWord u = redWord t ∧ g.1.1.1*p u = g.1.1.1 := by
  have hm : Sum.inl i ∈ Finset.univ.val.map t.lbl := by
    rw [show Finset.univ.val.map t.lbl = μ from t.2]; simp [stendhalWeight]
  obtain ⟨⟨n,hn⟩,-,hi⟩ := Multiset.mem_map.1 hm
  obtain ⟨u,f,hu,hf,uf,ft,gen,det⟩ := higher_generator i Q Λ a b (root t) (redWord t) t hQ n hn i hi rfl
  let G := violFlip f
  have eG : p t*G = G := by simpa only [reflect_mul,reflect_p] using congrArg violFlip ft
  have Gu : G*p u = G := by simpa only [reflect_mul,reflect_p] using congrArg violFlip uf
  have uE : p u*E = p u := (map_mul mk _ _).symm.trans (congrArg mk ((e_mul_redProj _ _).trans (ite_eq_left hu)))
  have GE : G*E = G := by conv_lhs => rw [← Gu,mul_assoc,uE,Gu]
  have val : (blockLoadingRep Q Λ t G).1.1 = G := (blockLoadingRep_val Q Λ t G).trans ((congrArg (· * E) eG).trans GE)
  let g : K := ⟨blockLoadingRep Q Λ t G,by change _ ∈ blockUpperIdeal k Q Λ β a b (root t) (redWord t); rw [val]; exact upper_flip i Q Λ a b _ _ hf⟩
  refine ⟨u,g,?_,?_,hu,by change (blockLoadingRep Q Λ t G).1.1 * p u = _; rw [val,Gu]⟩
  · intro x
    obtain ⟨d,hd⟩ := gen (violFlip x.1.1.1) (upper_flip i Q Λ a b _ _ x.2)
    have eq := congrArg violFlip hd
    simp only [reflect_mul,reflect_p,violFlip_violFlip] at eq
    have left : p t * x.1.1.1 = x.1.1.1 := congrArg Subtype.val x.1.2
    rw [left] at eq
    refine ⟨⟨E * violFlip d * E,_,rfl⟩,Subtype.ext (Subtype.ext (Subtype.ext ?_))⟩
    change x.1.1.1 = (blockLoadingRep Q Λ t G).1.1 * (E * violFlip d * E)
    rw [val,← mul_assoc,← mul_assoc,GE,← eq]; exact (CornerEndomorphism.corner_mul_right _ x.1.1).symm
  · intro y hy
    change (blockLoadingRep Q Λ t G).1.1 * y.1 = 0 at hy
    rw [val] at hy
    have zero : violFlip (0 : V) = 0 := congrArg unop (map_zero (violFlipHom k Q Λ β))
    have h := congrArg violFlip hy
    change violFlip (violFlip f * y.1) = violFlip 0 at h
    rw [reflect_mul,violFlip_violFlip,zero] at h
    have ret := congrArg violFlip (det (violFlip y.1) h)
    rwa [reflect_mul,reflect_p,violFlip_violFlip,zero] at ret

private theorem cyclic_tensor {S M N : Type*} [Ring S] [AddCommGroup M] [Module k M]
    [Module Sᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module S N]
    (g : M) (gen : ∀ x : M, ∃ d : S, x = op d • g) (z : BalancedTensor k k S M N) :
    ∃ y : N, z = BalancedTensor.tmul g y := by
  induction z using BalancedTensor.induction_on with
  | zero => exact ⟨0,(BalancedTensor.tmul_zero g).symm⟩
  | tmul x y => obtain ⟨d,rfl⟩ := gen x; exact ⟨d • y,BalancedTensor.op_smul_tmul _ _ _⟩
  | add x y hx hy => obtain ⟨l,rfl⟩ := hx; obtain ⟨w,rfl⟩ := hy; exact ⟨l+w,(BalancedTensor.tmul_add _ _ _).symm⟩

private theorem injective_of_generator {S M N W : Type*} [Ring S] [AddCommGroup M] [Module k M]
    [Module Sᵐᵒᵖ M] [AddCommGroup N] [Module k N] [Module S N] [AddCommGroup W] [Module k W]
    (f : BalancedTensor k k S M N →ₗ[k] W) (g : M) (U : S)
    (gen : ∀ x : M, ∃ d : S, x = op d • g) (cut : op U • g = g)
    (det : ∀ y : N, f (BalancedTensor.tmul g y) = 0 → U • y = 0) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
  intro z hz; obtain ⟨y,rfl⟩ := cyclic_tensor g gen z
  have h := det y hz
  rw [← cut,BalancedTensor.op_smul_tmul,h,BalancedTensor.tmul_zero]

/-- **First black weight of the kernel test after (6.21)** (Webster v2, Lemma 6.8).
There is a single black strand in total, but arbitrary red spectators, top and bottom
order, pairings and commutative ground ring. All mixed and same-exit stack relations
are balanced relations in `K ⊗_T B`. This does not treat additional black strands. -/
theorem firstWeight_blockKernelTensorInclusion_injective (hQ : KLRSymm Q) : Function.Injective inc := by
  let result := cyclic_mark i Q Λ a b t κ' hQ
  let u : KLR.Seq μ := result.choose
  let g : K := result.choose_spec.choose
  have facts := result.choose_spec.choose_spec
  have hu : redWord u = redWord t := facts.2.2.1
  let U : T := ⟨p u,(Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ β (redWord t))).2
    ⟨(map_mul mk _ _).symm.trans (congrArg mk ((redProj_mul_e _ _).trans (ite_eq_left hu))),
     (map_mul mk _ _).symm.trans (congrArg mk ((e_mul_redProj _ _).trans (ite_eq_left hu)))⟩⟩
  have ug : op U • g = g := Subtype.ext (Subtype.ext (Subtype.ext facts.2.2.2))
  have test (y : B) (hy : inc (BalancedTensor.tmul g y) = 0) : U • y = 0 :=
    Subtype.ext (facts.2.1 y ((blockKernelTensorInclusion_eq_zero_iff Q Λ t a b κ' _).1 hy))
  exact injective_of_generator (k := k) (S := T) (M := K) (N := B) inc g U facts.1 ug test

/-- The actual loading-column inclusion for (6.21) in the first black weight,
including `b i a` with both pairings positive. -/
theorem firstWeight_blockKernelColumnInclusion_injective (hQ : KLRSymm Q) :
    Function.Injective (blockKernelColumnInclusion Q Λ t a b s) :=
  blockKernelColumnInclusion_injective_of_tensor Q Λ t a b s
    (firstWeight_blockKernelTensorInclusion_injective i Q Λ a b t (redWord s) hQ)

local notation "seam" => fun j => op (blockSeamWord Q Λ t [j])
local notation "leg" => fun w : List ℕ => blockKernelLowerClass Q Λ t κ' (raw (ψw w * e s))

/-- The mixed syzygy at `b i a` in the first black weight (Webster v2,
Lemma 6.8 after (6.21)). Only the two products of the arbitrary projective
coefficient `u` must belong to `K`. Neither `u ∈ K` nor strictness of either
exit is an input. -/
theorem firstWeight_blockKernel_mixedExit (hQ : KLRSymm Q) (h : j+2 < m)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (ha : s.lbl ⟨j+2,h⟩ = .inr a)
    (hl : redWord (wordProd m [j+1,j] • s) = redWord t)
    (hr : redWord (wordProd m [j,j+1] • s) = redWord t)
    (u : rIdeal (orderedLoadingIdem Q Λ t)) (hx : seam j • u ∈ K) (hy : seam (j+1) • u ∈ K) :
    (BalancedTensor.tmul (⟨_,hx⟩ : K) (leg [j+1,j]) : Z) =
      BalancedTensor.tmul (⟨_,hy⟩ : K) (leg [j,j+1]) := by
  apply firstWeight_blockKernelTensorInclusion_injective i Q Λ a b t κ' hQ
  simpa only [mul_one,blockKernelTensorInclusion_tmul] using
    blockLoadingBraid_slide Q Λ t a b κ' s j h u hb ha hl hr 1

local notation "C" => RedBlock.crossingSpace (k := k) E (p s)

private theorem pair_presentation {X Y D : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y]
    [Module k Y] [AddCommGroup D] (l r : X →ₗ[k] Y) (a b : X → D)
    (gen : ∀ z, ∃ x y, z = l x + r y) (rel : ∀ x y, l x + r y = 0 ↔ a x + b y = 0) :
    Function.Surjective (l.coprod r) ∧ ∀ x y, (x,y) ∈ LinearMap.ker (l.coprod r) ↔ a x + b y = 0 :=
  ⟨fun z => by obtain ⟨x,y,h⟩ := gen z; exact ⟨(x,y),h.symm⟩,rel⟩

/-- The two-exit presentation of the marked loading column in the first black
weight of Webster v2, Lemma 6.8. The coefficients are in `K`, not the projective.
The kernel is tested on a pair of ordinary diagram products in the globally
violated algebra. A relation supported at a single exit is included. -/
theorem firstWeight_interleavedColumn_presentation (hQ : KLRSymm Q) (h : j+2 < m) {L M : List (Fin ℓ)}
    (ht : redWord t = L ++ a :: b :: M) (hb : s.lbl ⟨j,by omega⟩ = .inr b) (ha : s.lbl ⟨j+2,h⟩ = .inr a)
    (hl : redWord (wordProd m [j+1,j] • s) = redWord t) (hr : redWord (wordProd m [j,j+1] • s) = redWord t) :
    let l := interleavedLeg Q Λ s t _ hl
    let r := interleavedLeg Q Λ s t _ hr
    let f : K × K →ₗ[k] BalancedTensor k k T K C := ((BalancedTensor.mkBil k k T K C).flip l).coprod
      ((BalancedTensor.mkBil k k T K C).flip r)
    Function.Surjective f ∧ ∀ x y : K, (x,y) ∈ LinearMap.ker f ↔ x.1.1.1*l.1 + y.1.1.1*r.1 = 0 := by
  intro l r f
  exact pair_presentation ((BalancedTensor.mkBil k k T K C).flip l) ((BalancedTensor.mkBil k k T K C).flip r)
    (fun x => x.1.1.1*l.1) (fun y => y.1.1.1*r.1) (exists_interleavedKernelColumn_exits Q Λ s j h t a b hQ ht hb ha hl hr)
    (fun x y => blockKernelColumn_pair_eq_zero_iff Q Λ t a b s
      (firstWeight_blockKernelTensorInclusion_injective i Q Λ a b t (redWord s) hQ) x y l r)

end Categorification.Stendhal.BraidedStendhalAlgebra
