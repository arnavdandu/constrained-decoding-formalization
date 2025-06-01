import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Language
import Mathlib.Computability.Language

universe u v

variable { α : Type u }  { β : Type v } [ BEq α ] [ BEq β ] [ t: Vocabulary α β ]
abbrev Checker ( α β ) [ BEq α ] [ BEq β ] [ Vocabulary α β ] := List α → β → Bool

-- set of intermediate strings produced by a language model under a given constraint
def checkerAllows ( c: Checker α β ) (w : List β) : Bool :=
  match w with
  | [] => true
  | v :: ts =>
    c (ts.flatMap t.flatten) v = true && checkerAllows c ts

def checkerAccepts ( c: Checker α β ) (w : List β) : Bool :=
  checkerAllows c w && c (w.flatMap t.flatten) t.eos = true


def checkerIntermediateLanguage ( c: Checker α β ) : Language α :=
    { w | ∃ bs, checkerAllows c bs ∧ bs.flatMap t.flatten = w }

def checkerLanguage ( c: Checker α β ) : Language α :=
    { w | ∃ bs, checkerAccepts c bs ∧ bs.flatMap t.flatten = w }

abbrev LanguageModel := List α → β


def checkerAllowsTermination ( c : Checker α β ) : Prop :=
      ∀ w, checkerAllows c w →
        ∃ w', checkerAccepts c w' ∧ w.isPrefixOf w'

def checkerPathIndependent ( c : Checker α β ) : Prop :=
      ∀ w₁ w₂, w₁.flatMap t.flatten = w₂.flatMap t.flatten ->
         checkerAllows c w₁ = checkerAllows c w₂

def checkerSound (c : Checker α β ) : Prop := checkerAllowsTermination c ∧ checkerPathIndependent c

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
