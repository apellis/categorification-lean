import Categorification.Spec.Webster.Cor521

/-!
# Sanity checks for the Webster definition cards

Small facts about the definitions in the trusted base of the Webster specification files,
referenced from `docs/Faithfulness/cards/`.
-/

namespace Faithfulness.WebsterSanity

open Categorification Categorification.Stendhal Categorification.KLR Categorification.KL3.Diagram
open scoped Classical

/-- Webster's preorder on loadings is reflexive (card `standard-module.md`). -/
theorem stendhalLE_refl {I : Type} {ℓ : ℕ} {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ) :
    StendhalLE s s :=
  fun _ _ => le_rfl

/-- Its strict part is irreflexive, so `U_s` never contains the generator through `t = s`
(card `standard-module.md`). -/
theorem not_stendhalLT_self {I : Type} {ℓ : ℕ} {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ) :
    ¬ StendhalLT s s :=
  fun h => h.2 h.1

end Faithfulness.WebsterSanity
