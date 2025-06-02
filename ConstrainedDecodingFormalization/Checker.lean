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
    c ts v = true && checkerAllows c ts

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

--
-- partial def constrained_decoding ( ) := by sorry
  -- given
  -- a constrained lexing automata (symbols )
  -- a context free grammar of the symbols
  -- a language model
  -- we construct our pipeline by building lexer and parser combination
  -- analyze the given states to find inverse realizable terminal sequences
  -- do acceptance based off of that


-- main theorems (all require further refinement of lexer/parser)

-- 1. if recognized by the lexer and parser, then in the constrained language


-- 2. all prefixes are prefixes in the lexer/parser language

-- 3. if in the constrained language, then recognized by the lexer and parser
def checkerComplete (c : Checker α β ) ( l: Language α) : Prop :=
    checkerLanguage c = l ∧ checkerIntermediateLanguage c = l.prefixes
