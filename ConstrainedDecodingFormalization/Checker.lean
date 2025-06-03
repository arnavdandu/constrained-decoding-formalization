import ConstrainedDecodingFormalization.Language
import ConstrainedDecodingFormalization.Lexing
import Mathlib.Computability.Language

universe u v

variable { α : Type u }  { β : Type v } [ BEq α ] [ BEq β ]
abbrev Checker ( β ) [ BEq β ] := List β → Ch β → Bool

-- set of intermediate strings produced by a language model under a given constraint
def checkerAllows ( c: Checker β ) (w : List β) : Bool :=
  match w with
  | [] => true
  | v :: ts =>
    c ts v && checkerAllows c ts

def checkerAccepts ( c: Checker β ) (w : List β) : Bool :=
  checkerAllows c w && c w .eos = true

def checkerIntermediateLanguage ( c: Checker β ) : Language β :=
    { bs | checkerAllows c bs  }

def checkerLanguage ( c: Checker β ) : Language β :=
    { bs | checkerAccepts c bs }

def checkerAllowsTermination ( c : Checker β ) : Prop :=
      ∀ w, checkerAllows c w →
        ∃ (w' : List β), checkerAccepts c w' ∧ w.isPrefixOf w'

def checkerPathIndependent ( c : Checker β ) (flatten : β → List α) : Prop :=
      ∀ w₁ w₂, w₁.flatMap flatten = w₂.flatMap flatten ->
         checkerAllows c w₁ = checkerAllows c w₂

def checkerSound (c : Checker β ) (flatten : β → List α) : Prop := checkerAllowsTermination c ∧ checkerPathIndependent c flatten

def checkerComplete (c : Checker β ) ( l: Language β) : Prop :=
    checkerLanguage c = l ∧ checkerIntermediateLanguage c = l.prefixes
