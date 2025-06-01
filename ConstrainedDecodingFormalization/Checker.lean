import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Language
import Mathlib.Computability.Language

universe u v

variable { α : Type u }  { β : Type v } [ BEq α ] [ BEq β ] [ t: Vocabulary α β ]
abbrev Checker ( α β ) [ BEq α ] [ BEq β ] [ Vocabulary α β ] := List α → β → Bool

-- set of intermediate strings produced by a language model under a given constraint
inductive CheckerIntermediateLanguage ( c: Checker α β ) : List α → Prop where
 | empty : CheckerIntermediateLanguage c []
 | build { v ts } ( h: CheckerIntermediateLanguage c ts ) ( cv: c ts v = true ) : CheckerIntermediateLanguage c (ts ++ (t.flatten v))
inductive CheckerIntermediateLanguageI ( c: Checker α β ) : List α → Prop where
 | empty : CheckerIntermediateLanguageI c []
 | build { v ts } ( h: CheckerIntermediateLanguageI c ts ) ( cv: c ts v = true ) : CheckerIntermediateLanguageI c (ts ++ (t.flatten v))


-- set of final strings produced by a language model under a given constraint
inductive CheckerLanguage ( c: Checker α β ) : List α → Prop where
 | mk { ts } ( h: CheckerIntermediateLanguage c ts ) ( e: c ts t.eos = true ) : CheckerLanguage c ts
inductive CheckerLanguageI ( c: Checker α β ) : List α → Prop where
 | mk { ts } ( h: CheckerIntermediateLanguageI c ts ) ( e: c ts t.eos = true ) : CheckerLanguageI c ts

def checkerIntermediateLanguage ( c: Checker α β ) : Language α :=
    { w | CheckerIntermediateLanguageI c w }

def checkerLanguage ( c: Checker α β ) : Language α :=
    { w | CheckerIntermediateLanguageI c w }

abbrev LanguageModel := List α → β


def checkerAllowsTermination ( c : Checker α β ) : Prop :=
      ∀ w, CheckerIntermediateLanguage c w →
        ∃ w', CheckerLanguage c w' ∧ w.isPrefixOf w'

def checkerPathIndependent ( c : Checker α β ) : Prop :=
      ∀ w, CheckerIntermediateLanguage c w →
          ∀ w', (∃ v, w = w' ++ t.flatten v) →
            CheckerIntermediateLanguage c w'

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
