import ConstrainedDecodingFormalization.Lexing
import Mathlib

universe u v
variable { α : Type u } { Γ : Type v } [ BEq α ]

def cfgSentences (cfg : ContextFreeGrammar Γ) (l : (Lexer α Γ) ) : Language α :=
    { w |
      match l w with
      | some (terminals, []) => terminals ∈ cfg.language
      | _ => False
    }

def cfgSentencesPre (cfg : ContextFreeGrammar Γ) (l : (Lexer α Γ) ) : Language α :=
    { w | ∃ v ∈ cfgSentences cfg l, w <+: v }
