import Mathlib.Computability.Language

def Language.prefixes (l : Language α) : Language α := 
    { w | ∃ v ∈ l, w <+: v }
