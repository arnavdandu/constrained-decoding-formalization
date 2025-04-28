import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Language
import Mathlib.Computability.Language


variable { α β } [ BEq α ] [ BEq β ] [ t: Vocabulary α β ] 
abbrev Checker ( α β ) [ BEq α ] [ BEq β ] [ Vocabulary α β ] := List α → β → Bool 

-- set of intermediate strings produced by a language model under a given constraint
inductive CheckerIntermediateLanguageI ( c: Checker α β ) : List α → Prop where 
 | empty : CheckerIntermediateLanguageI c [] 
 | build { v ts } ( h: CheckerIntermediateLanguageI c ts ) ( cv: c ts v = true ) : CheckerIntermediateLanguageI c (ts ++ (t.flatten v))


-- set of final strings produced by a language model under a given constraint
inductive CheckerLanguageI ( c: Checker α β ) : List α → Prop where 
 | mk { ts } ( h: CheckerIntermediateLanguageI c ts ) ( e: c ts t.eos = true ) : CheckerLanguageI c ts 

def checkerIntermediateLanguage ( c: Checker α β ) : Language α := 
    { w | CheckerIntermediateLanguageI c w }

def checkerLanguage ( c: Checker α β ) : Language α := 
    { w | CheckerIntermediateLanguageI c w }

abbrev LanguageModel := List α → β


def checkerAllowsTermination ( c : Checker α β ) : Prop := 
      ∀ w, CheckerIntermediateLanguageI c w → 
        ∃ w', CheckerLanguageI c w' ∧ w.isPrefixOf w'

def checkerPathIndependent ( c : Checker α β ) : Prop := 
      ∀ w, CheckerIntermediateLanguageI c w → 
          ∀ w', (∃ v, w = w' ++ t.flatten v) → 
            CheckerIntermediateLanguageI c w'

def checkerSound (c : Checker α β ) : Prop := checkerAllowsTermination c ∧ checkerPathIndependent c

def checkerComplete (c : Checker α β ) ( l: Language α) : Prop := 
    checkerLanguage c = l ∧ checkerIntermediateLanguage c = l.prefixes
