import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary

open Classical List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ] [BEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

inductive Character (β)
| char : β → Character β
| eos  : Character β
deriving DecidableEq

abbrev Ch := Character

structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term_sym : Γ

-- A recognizer for a token: returns true if the input is a valid token
noncomputable def isToken (specs : List (LexerSpec α Γ σ)) (xs : List α) : Option Γ :=
  specs.findSome? fun s =>
    let nfa : NFA α σ := s.automaton
    if xs ∈ nfa.accepts then some s.term_sym else none

-- A predicate for prefix of any token
def isPrefix (specs : List (LexerSpec α Γ σ)) (xs : List α) : Prop :=
  specs.any fun s =>
    let nfa : NFA α σ := s.automaton
    ∃ ys, NFA.accepts nfa (xs ++ ys)

inductive LexRel (specs : List (LexerSpec (Ch α) (Ch Γ) σ)) :
    List (Ch α) → List (Ch Γ) → List (Ch α) → Prop
  | empty :
      LexRel specs [] [] []

  -- When the next character is EOS, and wr recognizes a token
  | done {wr tj} :
      isToken specs wr = some tj →
      LexRel specs (wr ++ [Character.eos]) [tj] []

  -- When next character is NOT EOS:
  -- (emit) If wr ∈ L(A^j) but (wr ++ c) is no longer a prefix of any token
  | emit {wr c cs tj T} :
      c ≠ Character.eos →
      isToken specs wr = some tj →
      ¬ isPrefix specs (wr ++ [c]) →
      LexRel specs (c :: cs) T [] →
      LexRel specs (wr ++ c :: cs) (tj :: T) wr

  -- (extend) If (wr ++ c) is still a valid prefix of some token
  | extend {wr c cs T} :
      c ≠ Character.eos →
      isPrefix specs (wr ++ [c]) →
      LexRel specs cs T (wr ++ [c]) →
      LexRel specs (c :: cs) T wr

def Lexer (α : Type u) (Γ : Type v) := List α -> Option (List Γ × List α)

noncomputable def PartialLex (specs : List (LexerSpec (Ch α) (Ch Γ) σ)) (w : List (Ch α)) : Option (List (Ch Γ) × List (Ch α)) :=
   if h : ∃ out : List (Ch Γ) × List (Ch α), LexRel specs w out.1 out.2 then
     some (choose h)
   else none

#check ((PartialLex _) : Lexer _ _)

abbrev Token (α : Type u) := List α

def BuildLexingFST (fsa : FSA (Ch α) σ) (tokens : List (Token (Ch α))) : FST (Ch α) (Token (Ch α)) σ := Id.run do
  let Q := fsa.states
  let trans := fsa.transitions
  let alph := fsa.alph
  let q0 := fsa.start

  let F' := [q0]

  let mut trans' : List (σ × (Ch α) × (List σ × List (Token (Ch α)))) := trans.map (fun (q, c, q') => (q, c, (q', [])))
  for s in Q do
    for T in tokens do
      for q in fsa.evalFrom s T do
        for c in alph do
          for q' in Q do
            if ∃ q'' ∈ Q, q'' ∉ fsa.step q c ∧ q' ∈ (fsa.step q0 c) then
              trans' := trans'.insert (q, c, ([q'], [T]))
        trans' := trans'.insert (q, Character.eos, ([q0], [T, [Character.eos]]))

  ⟨alph, tokens, Q, q0, FST.mkStep trans', F'⟩
