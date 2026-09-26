/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.Diagrams.KL3.Surjectivity
import Categorification.Diagrams.KL3.KaroubiKLR
import Categorification.Diagrams.KL3.KaroubiTransfer
import Categorification.Diagrams.KL3.MatEndBlock
import Categorification.Algebra.Graded.TensorGdim

/-!
# The action `α : R(ν) ⊗ R(ν') → END_U(E_{ν,-ν'} 1_λ)` (KL III (3.36))

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.4
(TeX `\subsubsection{Endomorphisms of $\cal{E}_{\nu,-\nu'}{\mathbf 1}_{\lambda}$}`), (3.35)–(3.36):

> `E_{ν,-ν'} 1_λ := ⨁_{i ∈ Seq(ν), j ∈ Seq(ν')} E_{i-j} 1_λ` […] There is a homomorphism
> `α : R(ν) ⊗_k R(ν') ⊗_k Π_λ → END_U(E_{ν,-ν'} 1_λ)`.

We construct the part `R(ν) ⊗ R(ν') → END_U(E_{ν,-ν'} 1_λ)` of `α` (the bubbles are central and
are treated separately with `bubAt`), as an algebra homomorphism to the matrix algebra
`MatEnd (fun (i, j) => E_{+i} E_{-j} 1_λ)`:

* `alphaUp`: `R(ν)` acts on the upward strands, by `ϕ_{ν, λ - ν'_X}` (`toUEnd`) placed to the
  left of the downward strands (`plcL`);
* `alphaDn`: `R(ν')` acts on the downward strands, by the KLR diagrams on downward strands
  (`downFunctor`, with the signs `(-1)^{#ii-crossings}` of KL III (3.31)) placed to the right of
  the upward strands;
* `alphaUp_comm_alphaDn`: the two actions commute (interchange law);
* `alpha := alphaUp ⊗ alphaDn`, and `alphaData`: the transfer data of
  `Categorification.Diagrams.KL3.KaroubiTransfer` for `R(ν) ⊗ R(ν')` with the tensor product
  grading (`alpha` preserves degrees, and sends `e_i ⊗ e_j` to the matrix unit of `(i, j)`).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation KLR KLR.Diagram MatEnd
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [Field k] [DecidableEq I]

section Transport

variable (μ : X) (ν ν' : Multiset I)

/-- The objects `E_{+i} E_{-j} 1_μ`, `(i, j) ∈ Seq ν × Seq ν'`. -/
abbrev ZS : KLR.Seq ν × KLR.Seq ν' → (pres RD k).Presented :=
  fun p => (pres RD k).obj (ob RD μ (ups (word p.1) ++ dns (word p.2)))

omit [DecidableEq I] in
theorem wt_ups_word_eq (μ' : X) (s s' : KLR.Seq ν) :
    wt RD μ' (ups (word s')) = wt RD μ' (ups (word s)) := by
  rw [wt_ups_word, wt_ups_word]

omit [DecidableEq I] in
theorem plcL_id (μ' : X) (u v s : List (Letter I)) :
    plcL RD k μ' u v s s (𝟙 _) = 𝟙 _ := by
  rw [← dg_nil (RD := RD) (k := k) (wt RD μ' v) s, plcL_dg, List.map_nil, dg_nil]

/-- The upward transport: place a 2-morphism `E_i 1_{μ - j_X} ⟶ E_{i'} 1_{μ - j_X}` to the left
of the downward strands `F_j`. -/
def upTransport : BlockTransport (k := k) (Equiv.prodComm (KLR.Seq ν') (KLR.Seq ν))
    (fun t s => (pres RD k).obj (ob RD (wt RD μ (dns (word t))) (ups (word s))))
    (ZS RD k μ ν ν') where
  F t s s' := plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
  map_comp t s s' s'' f g :=
    (plcL_comp RD k μ [] (dns (word t)) (wt_ups_word_eq RD ν _ s s')
      (wt_ups_word_eq RD ν _ s' s'') f g).symm
  map_id t s := plcL_id RD k μ [] (dns (word t)) (ups (word s))

omit [DecidableEq I] in
theorem ob_append_nil (μ' : X) (w : List (Letter I)) : ob RD μ' (w ++ []) = ob RD μ' w := by
  rw [List.append_nil]

omit [DecidableEq I] in
theorem wt_dns (μ' : X) (l : List I) : wt RD μ' (dns l) = -wsum RD l + μ' := by
  induction l with
  | nil => simp [wsum]
  | cons i l ih =>
    simp only [dns, List.map_cons, wt_cons] at ih ⊢
    rw [ih]
    simp [wsum, sh, dn, sgn]
    abel

omit [DecidableEq I] in
theorem wsum_word (s : KLR.Seq ν) : wsum RD (word s) = wν RD ν := by
  have h := wt_ups_word (RD := RD) (μ := (0 : X)) s
  rw [wt_ups] at h
  simpa using h

omit [DecidableEq I] in
theorem wt_dns_word (μ' : X) (t : KLR.Seq ν') : wt RD μ' (dns (word t)) = -wν RD ν' + μ' := by
  rw [wt_dns, wsum_word]

omit [DecidableEq I] in
theorem wt_dns_word_eq (μ' : X) (t t' : KLR.Seq ν') :
    wt RD μ' (dns (word t')) = wt RD μ' (dns (word t)) := by
  rw [wt_dns_word, wt_dns_word]

omit [DecidableEq I] in
/-- `TR` is compatible with composition. -/
theorem TR_comp' {a a' b b' c c' : Obj (psig RD)} (ea : a = a') (eb : b = b') (ec : c = c')
    (f : (pres RD k).obj a' ⟶ (pres RD k).obj b') (g : (pres RD k).obj b' ⟶ (pres RD k).obj c') :
    TR RD k ea eb f ≫ TR RD k eb ec g = TR RD k ea ec (f ≫ g) := by
  subst ea eb ec; simp [TR_apply]

omit [DecidableEq I] in
theorem TR_id' {a a' : Obj (psig RD)} (ea : a = a') : TR RD k ea ea (𝟙 _) = 𝟙 _ := by
  subst ea; simp [TR_apply]

/-- The objects `E_{-j} 1_μ` in the form produced by `downFunctor`. -/
abbrev XD (t : KLR.Seq ν') : (pres RD k).Presented :=
  (downFunctor RD k μ).obj ((KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t)))

/-- The downward placement map. -/
def dnF (s : KLR.Seq ν) (t t' : KLR.Seq ν') :
    (XD RD k μ ν' t ⟶ XD RD k μ ν' t') →ₗ[k] (ZS RD k μ ν ν' (s, t) ⟶ ZS RD k μ ν ν' (s, t')) :=
  (TR RD k (ob_append_nil RD μ _).symm (ob_append_nil RD μ _).symm).comp
    ((plcL RD k μ (ups (word s)) [] (dns (word t)) (dns (word t'))).comp
      (TR RD k (omega_ob_ups μ (word t)).symm (omega_ob_ups μ (word t')).symm))

theorem dnF_apply (s : KLR.Seq ν) (t t' : KLR.Seq ν') (g : XD RD k μ ν' t ⟶ XD RD k μ ν' t') :
    dnF RD k μ ν ν' s t t' g = TR RD k (ob_append_nil RD μ _).symm (ob_append_nil RD μ _).symm
      (plcL RD k μ (ups (word s)) [] (dns (word t)) (dns (word t'))
        (TR RD k (omega_ob_ups μ (word t)).symm (omega_ob_ups μ (word t')).symm g)) := rfl

/-- The downward transport: identify `ω̃(E_{+j} 1_{-μ})` with `E_{-j} 1_μ` and place a 2-morphism
`E_{-j} 1_μ ⟶ E_{-j'} 1_μ` to the right of the upward strands `E_i`. -/
def dnTransport : BlockTransport (k := k) (Equiv.refl (KLR.Seq ν × KLR.Seq ν'))
    (fun _ t => XD RD k μ ν' t) (ZS RD k μ ν ν') where
  F s t t' := dnF RD k μ ν ν' s t t'
  map_comp s t t' t'' f g := by
    show dnF RD k μ ν ν' s t t'' (f ≫ g) = dnF RD k μ ν ν' s t t' f ≫ dnF RD k μ ν ν' s t' t'' g
    rw [dnF_apply, dnF_apply, dnF_apply]
    symm
    rw [TR_comp', plcL_comp RD k μ (ups (word s)) [] (wt_dns_word_eq RD ν' _ t t')
      (wt_dns_word_eq RD ν' _ t' t''), TR_comp']
  map_id s t := by
    show dnF RD k μ ν ν' s t t (𝟙 _) = 𝟙 _
    rw [dnF_apply]
    erw [TR_id', plcL_id, TR_id']

end Transport

/-! ## The actions on upward and on downward strands -/

section Actions

variable (μ : X) (ν ν' : Multiset I)

/-- **`R(ν)` acting on the upward strands of `E_{+i} E_{-j} 1_μ`.** -/
def alphaUp : KLR.R2 k C ν →ₐ[k] MatEnd (ZS RD k μ ν ν') :=
  matBlockMap (Equiv.prodComm (KLR.Seq ν') (KLR.Seq ν)) (upTransport RD k μ ν ν')
    (fun t => toUEnd RD k (wt RD μ (dns (word t))) ν)

/-- **`R(ν')` acting on the downward strands of `E_{+i} E_{-j} 1_μ`** (KL III (3.31): the KLR
diagrams on downward strands, with the sign `(-1)` for every crossing of equally labelled
strands). -/
def alphaDn : KLR.R2 k C ν' →ₐ[k] MatEnd (ZS RD k μ ν ν') :=
  matBlockMap (Equiv.refl _) (dnTransport RD k μ ν ν')
    (fun _ => (matEndMap k (downFunctor RD k μ) _).comp
      (diagREquiv k (KLR.klQ2 k C) ν').toAlgHom)

theorem alphaUp_apply (r : KLR.R2 k C ν) (s s' : KLR.Seq ν) (t : KLR.Seq ν') :
    alphaUp RD k μ ν ν' r (s, t) (s', t) =
      plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
        ((upFunctor RD k (wt RD μ (dns (word t)))).map ((diagREquiv k (KLR.klQ2 k C) ν r) s s')) :=
  matBlockMap_apply_block (Equiv.prodComm (KLR.Seq ν') (KLR.Seq ν)) (upTransport RD k μ ν ν') _ r t s s'

theorem alphaUp_apply_ne (r : KLR.R2 k C ν) (s s' : KLR.Seq ν) {t t' : KLR.Seq ν'} (h : t ≠ t') :
    alphaUp RD k μ ν ν' r (s, t) (s', t') = 0 :=
  matBlockMap_apply_ne (Equiv.prodComm (KLR.Seq ν') (KLR.Seq ν)) (upTransport RD k μ ν ν') _ r s s' h

theorem alphaDn_apply (r : KLR.R2 k C ν') (s : KLR.Seq ν) (t t' : KLR.Seq ν') :
    alphaDn RD k μ ν ν' r (s, t) (s, t') = dnF RD k μ ν ν' s t t'
      ((downFunctor RD k μ).map ((diagREquiv k (KLR.klQ2 k C) ν' r) t t')) :=
  matBlockMap_apply_block (Equiv.refl _) (dnTransport RD k μ ν ν') _ r s t t'

theorem alphaDn_apply_ne (r : KLR.R2 k C ν') {s s' : KLR.Seq ν} (t t' : KLR.Seq ν') (h : s ≠ s') :
    alphaDn RD k μ ν ν' r (s, t) (s', t') = 0 :=
  matBlockMap_apply_ne (Equiv.refl _) (dnTransport RD k μ ν ν') _ r t t' h

/-! ### Entries on diagrams -/

omit [DecidableEq I] in
/-- Linear maps out of a Hom space of the diagrammatic KLR category agreeing on diagrams are
equal. -/
theorem klr_hom_ext {a b : Obj (KLR.Diagram.sig I)} {M : Type*} [AddCommGroup M] [Module k M]
    (φ ψ : ((KLR.Diagram.pres k (KLR.klQ2 k C)).obj a ⟶
      (KLR.Diagram.pres k (KLR.klQ2 k C)).obj b) →ₗ[k] M)
    (h : ∀ d : a ⟶ b, φ ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d) =
      ψ ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) : φ = ψ := by
  ext f
  obtain ⟨F, rfl⟩ := (KLR.Diagram.pres k (KLR.klQ2 k C)).lin_surjective f
  induction F using Finsupp.induction_linear with
  | zero => simp only [Presentation.lin_zero, map_zero]
  | add F₁ F₂ h₁ h₂ => rw [Presentation.lin_add, map_add, map_add, h₁, h₂]
  | single d r => rw [Presentation.lin_single, map_smul, map_smul, h d]

omit [DecidableEq I] in
theorem upF_diag (t : KLR.Seq ν') (s s' : KLR.Seq ν)
    (d : KLR.Diagram.ob (word s) ⟶ KLR.Diagram.ob (word s')) :
    plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
      ((upFunctor RD k (wt RD μ (dns (word t)))).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) =
      dg RD k μ (ups (word s) ++ dns (word t)) (ups (word s') ++ dns (word t))
        (((Diagram.layers d).map upLD).map (whL [] (dns (word t)))) := by
  rw [upFunctor_diag, upDiag_eq_dg]
  exact plcL_dg RD k μ [] (dns (word t)) (ups (word s)) (ups (word s')) _

theorem dnF_diag (s : KLR.Seq ν) (t t' : KLR.Seq ν')
    (d : KLR.Diagram.ob (word t) ⟶ KLR.Diagram.ob (word t')) :
    dnF RD k μ ν ν' s t t' ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) =
      ((Sig.sgnS ((Diagram.layers d).map upLD) : ℤ) : k) •
        dg RD k μ (ups (word s) ++ dns (word t)) (ups (word s) ++ dns (word t'))
          (((Diagram.layers d).map dnLD).map (whL (ups (word s)) [])) := by
  rw [dnF_apply, downFunctor_diag, map_smul]
  erw [TR_TR]
  rw [map_smul, map_smul]
  congr 1
  erw [plcL_dg]
  exact TR_dg (RD := RD) (k := k) μ (List.append_nil _).symm (List.append_nil _).symm _

omit [DecidableEq I] in
theorem dnShape_dom (g : KLR.Diagram.Gen I) : (dnShape g).dom = dns g.dom := by
  cases g <;> rfl

omit [DecidableEq I] in
theorem dnShape_cod (g : KLR.Diagram.Gen I) : (dnShape g).cod = dns g.cod := by
  cases g <;> rfl

omit [DecidableEq I] in
theorem sChain_dnLD {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : SChain (dns a.word) (ls.map dnLD) (dns b.word) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    refine ⟨?_, ?_⟩
    · simp [dnLD, dnShape_dom, dns]
    · have := ih hc
      simpa [dnLD, dnShape_cod, dns] using this

/-- **The interchange law for the two actions**, on KLR morphisms. -/
theorem up_dn_interchange (s s' : KLR.Seq ν) (t t' : KLR.Seq ν')
    (D : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s)) ⟶
      (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s')))
    (D' : (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t)) ⟶
      (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t'))) :
    dnF RD k μ ν ν' s t t' ((downFunctor RD k μ).map D') ≫
        plcL RD k μ [] (dns (word t')) (ups (word s)) (ups (word s'))
          ((upFunctor RD k (wt RD μ (dns (word t')))).map D) =
      plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
          ((upFunctor RD k (wt RD μ (dns (word t)))).map D) ≫
        dnF RD k μ ν ν' s' t t' ((downFunctor RD k μ).map D') := by
  -- linearity in `D'`, then in `D`
  have key := klr_hom_ext k
    ((Linear.rightComp k _ (plcL RD k μ [] (dns (word t')) (ups (word s)) (ups (word s'))
      ((upFunctor RD k (wt RD μ (dns (word t')))).map D))).comp
      ((dnF RD k μ ν ν' s t t').comp ((downFunctor RD k μ).mapLinearMap k
        (X := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t)))
        (Y := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t'))))))
    ((Linear.leftComp k _ (plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
      ((upFunctor RD k (wt RD μ (dns (word t)))).map D))).comp
      ((dnF RD k μ ν ν' s' t t').comp ((downFunctor RD k μ).mapLinearMap k
        (X := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t)))
        (Y := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word t')))))) (fun d' => ?_)
  · exact LinearMap.congr_fun key D'
  have key' := klr_hom_ext k
    ((Linear.leftComp k _ (dnF RD k μ ν ν' s t t'
      ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d')))).comp
      ((plcL RD k μ [] (dns (word t')) (ups (word s)) (ups (word s'))).comp
        ((upFunctor RD k (wt RD μ (dns (word t')))).mapLinearMap k
          (X := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s)))
          (Y := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s'))))))
    ((Linear.rightComp k _ (dnF RD k μ ν ν' s' t t'
      ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d')))).comp
      ((plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))).comp
        ((upFunctor RD k (wt RD μ (dns (word t)))).mapLinearMap k
          (X := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s)))
          (Y := (KLR.Diagram.pres k (KLR.klQ2 k C)).obj (KLR.Diagram.ob (word s')))))) (fun d => ?_)
  · exact LinearMap.congr_fun key' D
  change dnF RD k μ ν ν' s t t' ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d')) ≫
      plcL RD k μ [] (dns (word t')) (ups (word s)) (ups (word s'))
        ((upFunctor RD k (wt RD μ (dns (word t')))).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) =
    plcL RD k μ [] (dns (word t)) (ups (word s)) (ups (word s'))
        ((upFunctor RD k (wt RD μ (dns (word t)))).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d)) ≫
      dnF RD k μ ν ν' s' t t' ((downFunctor RD k μ).map ((KLR.Diagram.pres k (KLR.klQ2 k C)).diag d'))
  rw [dnF_diag, dnF_diag, upF_diag, upF_diag, Linear.smul_comp, Linear.comp_smul]
  congr 1
  have hA : SChain (ups (word s)) ((Diagram.layers d).map upLD) (ups (word s')) :=
    sChain_upLD (Diagram.chain d)
  have hB : SChain (dns (word t)) ((Diagram.layers d').map dnLD) (dns (word t')) :=
    sChain_dnLD (Diagram.chain d')
  rw [dg_comp (by simpa using hB.whisk (ups (word s)) []) (by simpa using hA.whisk [] (dns (word t'))),
    dg_comp (by simpa using hA.whisk [] (dns (word t))) (by simpa using hB.whisk (ups (word s')) [])]
  have := dg_interchange (RD := RD) (k := k) (μ := μ) (S := ups (word s) ++ dns (word t))
    (T := ups (word s') ++ dns (word t')) [] [] hA hB
  simpa using this.symm

end Actions




/-! ## The action of `R(ν) ⊗ R(ν')` -/

section Alpha

variable (μ : X) (ν ν' : Multiset I)

/-- **The two actions commute** (interchange law). -/
theorem alphaUp_mul_alphaDn (r : KLR.R2 k C ν) (r' : KLR.R2 k C ν') :
    alphaUp RD k μ ν ν' r * alphaDn RD k μ ν ν' r' = alphaDn RD k μ ν ν' r' * alphaUp RD k μ ν ν' r := by
  ext ⟨s, t⟩ ⟨s', t'⟩
  rw [MatEnd.mul_apply, MatEnd.mul_apply, Finset.sum_eq_single (s, t'),
    Finset.sum_eq_single (s', t)]
  · rw [alphaDn_apply, alphaUp_apply, alphaUp_apply, alphaDn_apply]
    exact up_dn_interchange RD k μ ν ν' s s' t t' _ _
  · rintro ⟨a, b⟩ _ hab
    by_cases hb : b = t
    · subst hb
      have ha : a ≠ s' := fun h => hab (by rw [h])
      rw [alphaDn_apply_ne RD k μ ν ν' r' _ _ ha, Limits.comp_zero]
    · rw [alphaUp_apply_ne RD k μ ν ν' r _ _ (Ne.symm hb), Limits.zero_comp]
  · simp
  · rintro ⟨a, b⟩ _ hab
    by_cases ha : a = s
    · subst ha
      have hb : b ≠ t' := fun h => hab (by rw [h])
      rw [alphaUp_apply_ne RD k μ ν ν' r _ _ hb, Limits.comp_zero]
    · rw [alphaDn_apply_ne RD k μ ν ν' r' _ _ (Ne.symm ha), Limits.zero_comp]
  · simp

/-- **KL III (3.36), without the bubbles**: the action
`α : R(ν) ⊗ R(ν') → END_U(E_{ν,-ν'} 1_μ) = ⨁_{(i,j),(i',j')} HOM_U(E_{+i} E_{-j} 1_μ, E_{+i'} E_{-j'} 1_μ)`
of `R(ν)` on the upward and of `R(ν')` on the downward strands. -/
def alpha : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν' →ₐ[k] MatEnd (ZS RD k μ ν ν') :=
  Algebra.TensorProduct.lift (alphaUp RD k μ ν ν') (alphaDn RD k μ ν ν')
    fun r r' => alphaUp_mul_alphaDn RD k μ ν ν' r r'

theorem alpha_tmul (r : KLR.R2 k C ν) (r' : KLR.R2 k C ν') :
    alpha RD k μ ν ν' (r ⊗ₜ r') = alphaUp RD k μ ν ν' r * alphaDn RD k μ ν ν' r' :=
  Algebra.TensorProduct.lift_tmul _ _ _ r r'

theorem alphaUp_e (s : KLR.Seq ν) :
    alphaUp RD k μ ν ν' (KLRAlgebra.e s) = ∑ t, MatEnd.single (s, t) (s, t) (𝟙 _) := by
  rw [alphaUp, matBlockMap_eq_of_single _ _ _ _ s (fun t => toUEnd_e RD k _ ν s)]
  rfl

theorem alphaDn_e (t : KLR.Seq ν') :
    alphaDn RD k μ ν ν' (KLRAlgebra.e t) = ∑ s, MatEnd.single (s, t) (s, t) (𝟙 _) := by
  rw [alphaDn, matBlockMap_eq_of_single _ _ _ _ t (fun _ => ?_)]
  · rfl
  · show matEndMap k (downFunctor RD k μ) _ (diagREquiv k (KLR.klQ2 k C) ν' (KLRAlgebra.e t)) = _
    rw [diagREquiv_e, DiagR.E, matEndMap_single, CategoryTheory.Functor.map_id]

/-- `α(e_i ⊗ e_j)` is the matrix unit of `(i, j)`. -/
theorem alpha_e (s : KLR.Seq ν) (t : KLR.Seq ν') :
    alpha RD k μ ν ν' (KLRAlgebra.e s ⊗ₜ KLRAlgebra.e t) = MatEnd.single (s, t) (s, t) (𝟙 _) := by
  rw [alpha_tmul, alphaUp_e, alphaDn_e, Finset.sum_mul_sum, Finset.sum_eq_single t,
    Finset.sum_eq_single s]
  · rw [MatEnd.single_mul_single, Category.comp_id]
  · intro s'' _ hs
    exact MatEnd.single_mul_single_of_ne _ _ (fun h => hs (by simp only [Prod.mk.injEq] at h; exact h.1))
  · simp
  · intro t'' _ ht
    refine Finset.sum_eq_zero fun s'' _ => ?_
    exact MatEnd.single_mul_single_of_ne _ _ (fun h => ht (by simp only [Prod.mk.injEq] at h; exact h.2.symm))
  · simp

end Alpha

/-! ## Degrees -/

section Degrees

open GradedBicat

variable (μ : X) (ν ν' : Multiset I)

variable {RD k} in
omit [DecidableEq I] in
theorem TR_mem_homDeg {a a' b b' : Obj (psig RD)} (ea : a = a') (eb : b = b') {d : ℤ}
    {f : (pres RD k).obj a' ⟶ (pres RD k).obj b'} (hf : f ∈ (pres RD k).homDeg (deg RD) a' b' d) :
    TR RD k ea eb f ∈ (pres RD k).homDeg (deg RD) a b d := by
  rw [TR_apply]
  have h := comp_mem_homDeg (comp_mem_homDeg (eqToHom_mem_homDeg (P := pres RD k) (deg := deg RD) ea)
    hf) (eqToHom_mem_homDeg (P := pres RD k) (deg := deg RD) eb.symm)
  simpa [Category.assoc] using h

variable {μ ν ν'} in
theorem alphaUp_mem {d : ℤ} {r : KLR.R2 k C ν} (hr : r ∈ (klGradingDatum2 k C).grade ν d)
    (p q : KLR.Seq ν × KLR.Seq ν') :
    alphaUp RD k μ ν ν' r p q ∈ (pres RD k).homDeg (deg RD) (ob RD μ (ups (word p.1) ++ dns (word p.2)))
      (ob RD μ (ups (word q.1) ++ dns (word q.2))) d := by
  obtain ⟨s, t⟩ := p
  obtain ⟨s', t'⟩ := q
  by_cases h : t = t'
  · subst h
    rw [alphaUp_apply]
    have h1 : (upFunctor RD k (wt RD μ (dns (word t)))).map
        ((diagREquiv k (KLR.klQ2 k C) ν r) s s') ∈
        HomD RD k (wt RD μ (dns (word t))) (ups (word s)) (ups (word s')) d :=
      upEnt_mem (RD := RD) (k := k) (μ := wt RD μ (dns (word t))) hr s s'
    have h2 := plcL_mem μ [] (dns (word t)) (ups (word s)) (ups (word s')) h1
    exact h2
  · rw [alphaUp_apply_ne RD k μ ν ν' r s s' h]
    exact Submodule.zero_mem _

variable {μ ν ν'} in
theorem alphaDn_mem {d : ℤ} {r : KLR.R2 k C ν'} (hr : r ∈ (klGradingDatum2 k C).grade ν' d)
    (p q : KLR.Seq ν × KLR.Seq ν') :
    alphaDn RD k μ ν ν' r p q ∈ (pres RD k).homDeg (deg RD) (ob RD μ (ups (word p.1) ++ dns (word p.2)))
      (ob RD μ (ups (word q.1) ++ dns (word q.2))) d := by
  obtain ⟨s, t⟩ := p
  obtain ⟨s', t'⟩ := q
  by_cases h : s = s'
  · subst h
    rw [alphaDn_apply, dnF_apply]
    refine TR_mem_homDeg _ _ ?_
    refine plcL_mem μ (ups (word s)) [] (dns (word t)) (dns (word t')) ?_
    refine TR_mem_homDeg _ _ ?_
    exact omegaU_homDeg (upEnt_mem (RD := RD) (k := k) (μ := -μ) hr t t')
  · rw [alphaDn_apply_ne RD k μ ν ν' r t t' h]
    exact Submodule.zero_mem _

/-- Matrices all of whose entries have degree `d`. -/
def matDegS (d : ℤ) : Submodule k (MatEnd (ZS RD k μ ν ν')) where
  carrier := {f | ∀ p q, f p q ∈ (pres RD k).homDeg (deg RD) (ob RD μ (ups (word p.1) ++ dns (word p.2)))
      (ob RD μ (ups (word q.1) ++ dns (word q.2))) d}
  add_mem' hf hg p q := Submodule.add_mem _ (hf p q) (hg p q)
  zero_mem' _ _ := Submodule.zero_mem _
  smul_mem' r _ hf p q := Submodule.smul_mem _ r (hf p q)

variable {μ ν ν'} in
/-- **`α` preserves degrees** (tensor product grading on `R(ν) ⊗ R(ν')`). -/
theorem alpha_mem {d : ℤ} {r : KLR.R2 k C ν ⊗[k] KLR.R2 k C ν'}
    (hr : r ∈ Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν') d)
    (p q : KLR.Seq ν × KLR.Seq ν') :
    alpha RD k μ ν ν' r p q ∈ (pres RD k).homDeg (deg RD) (ob RD μ (ups (word p.1) ++ dns (word p.2)))
      (ob RD μ (ups (word q.1) ++ dns (word q.2))) d := by
  have := Graded.tensorGrading_map_mem _ _ (matDegS RD k μ ν ν')
    (alpha RD k μ ν ν').toLinearMap (fun i j m n hm hn => ?_) hr
  · exact this p q
  intro p q
  show (alpha RD k μ ν ν' (m ⊗ₜ n)) p q ∈ _
  rw [alpha_tmul, MatEnd.mul_apply, add_comm]
  exact Submodule.sum_mem _ fun j _ => comp_mem_homDeg (alphaDn_mem RD k hn p j)
    (alphaUp_mem RD k hm j q)

end Degrees

/-! ## Transfer data -/

section Data

open GradedBicat

variable (μ : X) (ν ν' : Multiset I)

/-- The left weight `λ + ν_X - ν'_X` of `E_{+i} E_{-j} 1_λ`. -/
abbrev rhoS : X := wν RD ν + (-wν RD ν' + μ)

omit [DecidableEq I] in
theorem wt_ZS (p : KLR.Seq ν × KLR.Seq ν') :
    wt RD μ (ups (word p.1) ++ dns (word p.2)) = rhoS RD μ ν ν' := by
  rw [wt_append, wt_dns_word, wt_ups_word]

/-- The 1-morphisms `E_{+i} E_{-j} 1_μ` of `U`. -/
abbrev xS (p : KLR.Seq ν × KLR.Seq ν') :
    Bicat.Hom (wtObj RD k (rhoS RD μ ν ν')) (wtObj RD k μ) :=
  nfHom RD k (rhoS RD μ ν ν') μ (ups (word p.1) ++ dns (word p.2)) (wt_ZS RD μ ν ν' p)

/-- **The transfer data of `α`** (for `Categorification.Diagrams.KL3.KaroubiTransfer`):
`R(ν) ⊗ R(ν')` with the tensor product grading acts on `⨁_{(i,j)} E_{+i} E_{-j} 1_μ` by `α`,
`e_i ⊗ e_j` acting as the matrix unit of `(i, j)`. -/
def alphaData : TransferData (P := pres RD k) (deg := deg RD)
    (Graded.tensorGrading ((klGradingDatum2 k C).grade ν) ((klGradingDatum2 k C).grade ν'))
    (xS RD k μ ν ν') (fun p => KLRAlgebra.e p.1 ⊗ₜ KLRAlgebra.e p.2) where
  α := alpha RD k μ ν ν'
  α_e p := alpha_e RD k μ ν ν' p.1 p.2
  α_mem hr i j := alpha_mem RD k hr i j

theorem alphaData_α : (alphaData RD k μ ν ν').α = alpha RD k μ ν ν' := rfl

end Data

end Categorification.KL3.Diagram
