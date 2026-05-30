module

public import VeryWeakSubintuitionistic.Modal.Syntax

@[expose] public section

namespace Modal

variable {α : Type*}

abbrev Axioms (α) := Finset (Formula α)

end Modal

end section
