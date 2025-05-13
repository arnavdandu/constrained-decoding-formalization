import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Partition

open Classical List RegularExpression

universe u v w

abbrev RE := RegularExpression

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ] [BEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

inductive Character (α : Type u)
| char : α → Character α
| eos  : Character α
deriving DecidableEq, Repr

/-
structure Token1 where
  chars: List (Character α)
  eos_last : chars.getLast? = some .eos
deriving DecidableEq, Repr
-/

abbrev Ch := Character

#check FSA (Ch α) (Ch α)

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

inductive LexRel (P : RE (Ch α)) (specs : List (LexerSpec (Ch α) (Ch Γ) (St P))) :
    List (Ch α) → List (Ch Γ) → List (Ch α) → Prop
  | empty :
      LexRel P specs [] [] []

  -- When the next character is EOS, and wr recognizes a token
  | done {wr ws ts tj} :
      LexRel P specs ws ts wr →
      isToken specs wr = some tj →
      LexRel P specs (ws ++ [.eos]) (ts ++ [tj]) []

  -- When next character is NOT EOS:
  -- (emit) If wr ∈ L(A^j) but (wr ++ c) is no longer a prefix of any token
  | emit {wr c cs tj T} :
      c ≠ Character.eos →
      isToken specs wr = some tj →
      ¬ isPrefix specs (wr ++ [c]) →
      LexRel P specs (c :: cs) T [] →
      LexRel P specs (wr ++ c :: cs) (tj :: T) wr

  -- (extend) If (wr ++ c) is still a valid prefix of some token
  | extend {wr c cs T} :
      c ≠ Character.eos →
      isPrefix specs (wr ++ [c]) →
      LexRel P specs cs T (wr ++ [c]) →
      LexRel P specs (c :: cs) T wr

def Lexer (α : Type u) (Γ : Type v) := List α -> Option (List Γ × List α)

noncomputable def PartialLex (P : RE (Ch α)) (specs : List (LexerSpec (Ch α) (Ch Γ) (St P))) (w : List (Ch α)) :
    Option (List (Ch Γ) × List (Ch α)) :=
   if h : ∃ out : List (Ch Γ) × List (Ch α), LexRel P specs w out.1 out.2 then
     some (choose h)
   else none

abbrev Token (α : Type u) := List α

noncomputable def BuildLexingFST (fsa : FSA (Ch α) (St P)) (tokens : List (Token (Ch α))) : FST (Ch α) (Token (Ch α)) (St P) := Id.run do
  let Q := fsa.states
  let trans := fsa.transitions
  let alph := fsa.alph
  let q0 := fsa.start

  let F' := [q0]

  let mut trans' : List ((St P) × (Ch α) × (List (St P) × List (Token (Ch α)))) := trans.map (fun (q, c, q') => (q, c, (q', [])))
  for s in Q do
    for T in tokens do
      for q in fsa.evalFrom s T do
        for c in alph do
          for q' in Q do
            if ∃ q'' ∈ Q, q'' ∉ fsa.step q c ∧ q' ∈ (fsa.step q0 c) then
              trans' := trans'.insert (q, c, ([q'], [T]))
        trans' := trans'.insert (q, .eos, ([q0], [T, [.eos]]))

  ⟨alph, tokens, Q, q0, FST.mkStep trans', F'⟩

def PartialLexSplit (P : RE (Ch α))
    (specs : List (LexerSpec (Ch α) (Ch Γ) (St P))) (w : List (Ch α)) :
    match PartialLex P specs (w ++ [.eos]) with
    | some (tokens, unlexed) =>
      -- exists a partition corresponding to the output of partial lex
      unlexed = [] ∧
      ∃ p, IsPartition p w ∧ p.length = tokens.length ∧
        ∀ t ∈ (List.zip tokens p), ∃ spec ∈ specs, t.fst = spec.term_sym ∧ t.snd ∈ spec.automaton.accepts
    | none =>
      -- there is no possible partitions in which we can lex it
      ∀ p, IsPartition p w → ∃ x ∈ p, ∀ lexer ∈ specs, x ∉ lexer.automaton.accepts
      := by
  split
  case h_1 tokens unlexed heq =>
    simp[PartialLex] at heq
    rcases heq
    case intro w1 h =>
    cases w1
    case intro w' h' =>
    cases h'
    case intro w'' h'' =>
    sorry
  case h_2 =>
    sorry

def LexingFST_eq_PartialLex := 0
def soundnessLemma := 0
def completenessLemma := 0

#check RegularExpression (Ch Char)

def mkchar {α : Type u} (x : α) : Character α := Character.char x
def REchar {α : Type u} (x : α) : RE (Character α) := char (mkchar x)

def ab_plus : RE (Ch Char) :=
  comp (REchar 'a') (comp (REchar 'b') (star (REchar 'b')))

def ac_plus : RE (Ch Char) :=
  comp (REchar 'a') (comp (REchar 'c') (star (REchar 'c')))

def test_re : RE (Ch Char) :=
  plus ab_plus ac_plus

#eval [mkchar 'a', mkchar 'b'] ∈ (test_re).matches'
#eval [mkchar 'a', mkchar 'c'] ∈ (test_re).matches'
#eval [mkchar 'a', mkchar 'b', mkchar 'b', mkchar 'b'] ∈ (test_re).matches'

#check (toεNFA test_re)
