variable { α }

def IsPartition ( parts : List (List α) ) ( base: List α ) :=
    (∀ part ∈ parts, ¬part.isEmpty) ∧ parts.flatten = base
