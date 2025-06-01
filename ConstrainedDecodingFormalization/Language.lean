import Mathlib.Computability.Language

universe u
variable { α : Type u }

def Language.prefixes (l : Language α) : Language α :=
    { w | ∃ v ∈ l, w <+: v }
