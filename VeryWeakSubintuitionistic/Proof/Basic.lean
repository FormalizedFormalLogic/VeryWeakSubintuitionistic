module

public import VeryWeakSubintuitionistic.Syntax

@[expose] public section

variable {α : Type*}

abbrev Axioms (α) := Finset (Formula α)

end section
