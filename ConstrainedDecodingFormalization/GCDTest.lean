import ConstrainedDecodingFormalization.GrammarConstrainedDecoding
import ConstrainedDecodingFormalization.Checker
import ConstrainedDecodingFormalization.RealizableSequence
import Mathlib.Tactic

-- Example finite types
abbrev Vocab := Fin 5
abbrev Chr := Fin 3
abbrev Digit := Fin 3
abbrev LexerState := Fin 3
abbrev ParserState := Fin 2
abbrev StackSym := Fin 2


-- Lexer automaton that reads single digit
def simpleFSA : FSA Chr LexerState :=
{
  start := 0,
  step := fun s c =>
    match s, c with
    | 0, 0 => some 1
    | 0, 1 => some 2
    | 1, 0 => some 1
    | 2, 1 => some 2
    | _, _ => none,
  accept := [1, 2]
}

def termMap : LexerState → Option Digit
| 1 => some 0
| 2 => some 1
| _ => none

def hterm_proof : ∀ s, s ∈ simpleFSA.accept ↔ (termMap s).isSome :=
  by
    intro s
    simp_all [simpleFSA, termMap]
    split <;> simp_all

def term_inj_proof : ∀ s₁ s₂ t, termMap s₁ = some t ∧ termMap s₂ = some t → s₁ = s₂ :=
  by
    intros s₁ s₂ t h
    fin_cases s₁ <;> (fin_cases s₂ <;> first | simp_all [termMap])
    all_goals (have ⟨u, v⟩ := h; rw[←u] at v; contradiction)


def simpleLexer : LexerSpec Chr Digit LexerState :=
{
  automaton := simpleFSA,
  term := termMap,
  hterm := hterm_proof,
  term_inj := term_inj_proof
}

def simplePDA : PDA (Ch Digit) StackSym ParserState :=
{
  start := 0,
  step := fun s g =>
    match s, g with
    | 0, ExtChar.char 0 => some ([], [1, 0], 1)
    | 0, ExtChar.eos    => some ([], [], 0)

    | 1, ExtChar.char 0 => some ([], [1], 1)
    | 1, ExtChar.char 1 => some ([1], [], 1)
    | 1, ExtChar.eos => some ([0], [], 0)
    | _, _ => none,
  accept := [0]
}

def tokens : List (Token (Ch Chr) (Ch Vocab)) := [
  { symbol := ExtChar.char 0
    string := [ExtChar.char 0]
  },
  { symbol := ExtChar.char 1
    string := [ExtChar.char 1]
  },
  { symbol := ExtChar.char 2
    string := [ExtChar.char 1, ExtChar.char 1]
  },
  { symbol := ExtChar.char 3
    string := [ExtChar.char 2]
  },
  { symbol := ExtChar.eos
    string := [ExtChar.eos]
  },
]

def detok := Detokenizing.BuildDetokenizingFST tokens
def full_fst := FST.compose detok (BuildLexingFST simpleLexer)
def checker := GCDChecker simpleLexer tokens simplePDA

#eval [0, 1] ∈ simpleFSA.accepts
#eval [0, 0] ∈ simpleFSA.accepts
#eval [1, 0] ∈ simpleFSA.accepts
#eval [1, 1] ∈ simpleFSA.accepts

#eval simplePDA.evalFrom (some (simplePDA.start, [])) [.char 0]
#eval simplePDA.evalFrom (some (simplePDA.start, [])) [.char 1]
#eval simplePDA.evalFrom (some (simplePDA.start, [])) [.char 0, .char 0, .char 1, .char 1]
#eval simplePDA.step 1  (.char 1)
#eval simplePDA.fullStep (some (1, [0, 1])) (.char 1)
#eval full_fst.eval [.char 0, .char 0, .char 1, .eos]
#eval (PreprocessParser full_fst simplePDA) 1 1
#eval (BuildInverseTokenSpannerTable full_fst).1
#eval (BuildInverseTokenSpannerTable full_fst).2 [.char 0, .char 1] (.unit, 1)
#eval checkerAllows checker []
#eval checkerAllows checker [0]
#eval checkerAllows checker [1]
#eval checker [0] (.char 1)
#eval checkerAllows checker [0, 1]
#eval checkerAllows checker [1, 1, 0, 0, 0, 1, 1]
#eval checkerAccepts checker []
