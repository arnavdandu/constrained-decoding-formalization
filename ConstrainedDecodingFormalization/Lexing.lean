import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum

import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Partition

open List RegularExpression

universe u v w

abbrev RE := RegularExpression

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ]
  [BEq α] [BEq σ] [LawfulBEq σ] [LawfulBEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype σ] [Fintype Γ]

/-- Extend character alphabet with EOS symbol-/
inductive ExtChar (α : Type u)
| char : α → ExtChar α
| eos  : ExtChar α
deriving DecidableEq, Repr

instance {α} : Coe (α) (ExtChar α) := ⟨fun a => ExtChar.char a⟩

abbrev Ch := ExtChar

variable (P : RE (Ch α))

@[ext]
structure Terminal (α : Type u) (Γ : Type v)  where
  expr : RegularExpression α
  symbol : Γ
deriving Repr

def LexingFSA := P.toεNFA.toNFA


structure LexerSpecification (α Γ σ) where
  automaton : FSA α σ
  term_sym : Γ

-- A recognizer for a token: returns true if the input is a valid token
def isToken (specs : List (LexerSpecification α Γ σ)) (xs : List α) : Option Γ :=
  --letI := Classical.propDecidable
  specs.findSome? fun s =>
    if xs ∈ s.automaton.accepts then some s.term_sym else none

-- A predicate for prefix of any token (Note: decidability not proven yet. Will probably need to do something similar as acceptance decidability.)
def isPrefix (specs : List (LexerSpecification α Γ σ)) (xs : List α) : Prop :=
  ∃ s ∈ specs, FSA.isPrefix s.automaton xs


inductive LexRel (specs : List (LexerSpecification (Ch α) Γ σ)) :
    List (Ch α) → List (Ch Γ) → List (Ch α) → Prop
  | empty :
      LexRel specs [] [] []

  -- When the next character is EOS, and wr recognizes a token
  | done {wr ws ts tj} :
      LexRel specs ws ts wr →
      isToken specs wr = some tj →
      LexRel specs (ws ++ [.eos]) (ts ++ [.char tj]) []

  -- When next character is NOT EOS:
  -- (emit) If wr ∈ L(A^j) but (wr ++ c) is no longer a prefix of any token
  | emit {wr c cs tj T} :
      c ≠ .eos →
      isToken specs wr = some tj →
      ¬ isPrefix specs (wr ++ [c]) →
      LexRel specs (c :: cs) T [] →
      LexRel specs (wr ++ c :: cs) (tj :: T) wr

  -- (extend) If (wr ++ c) is still a valid prefix of some token
  | extend {wr c cs T} :
      c ≠ .eos →
      isPrefix specs (wr ++ [c]) →
      LexRel specs cs T (wr ++ [c]) →
      LexRel specs (c :: cs) T wr

def Lexer (α : Type u) (Γ : Type v) := List α -> Option (List Γ × List α)

-- Retain the noncomputable version for proofs
noncomputable def PartialLex (specs :  List (LexerSpecification (Ch α) Γ σ)) (w : List (Ch α)) :
    Option (List (Ch Γ) × List (Ch α)) :=
  letI := Classical.propDecidable
   if h : ∃ out : List (Ch Γ) × List (Ch α), LexRel specs w out.1 out.2 then
     some (Classical.choose h)
   else none

--instance : DecidableEq (Γ × St P) := by apply instDecidableEqProd

/-- Given a lexing automaton `A`, build a character-to-token lexing FST with output over `Γ`
    For the lexing FSA, we'll use the convention that each terminal symbol is attached to an accept state (see Fig. 1) -/
def BuildLexingFST (A : FSA (Ch α) (Ch Γ × σ)) :
    FST (Ch α) (Ch Γ) (Ch Γ × σ) := Id.run do
  let Q := A.states
  let trans := A.transitions
  let alph := A.alph
  let q0 := A.start
  let F := A.accept

  let oalph := (F.map (fun (x, _) => x)).eraseDups.filter (fun c => c ≠ .eos)

  let F' := [q0]
  let mut trans' := trans.map (fun (q, c, s) =>
    match s with
    | none => (q, c, none)
    | some q' => (q, c, (q', ([] : List (Ch Γ))))
  )

  for q in F do
    let T := q.1
    for c in alph do
      for q' in Q do
        if A.step q c = none ∧ A.step q0 c = q' then
          trans' := trans'.insert (q, c, some (q', [T]))
    trans' := trans'.insert (q, .eos, some (q0, [T, .eos]))

  ⟨alph, oalph, Q, q0, FST.mkStep trans', F'⟩


def PartialLexSplit (specs : List (LexerSpecification (Ch α) Γ σ)) (w : List (Ch α)) :
    match PartialLex specs (w ++ [.eos]) with
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

/-
#check RegularExpression (Ch Char)

def mkchar {α : Type u} (x : α) : ExtChar α := ExtChar.char x
def REchar {α : Type u} (x : α) : RE (ExtChar α) := char (mkchar x)

def ab_plus : RE (Ch Char) :=
  comp (REchar 'a') (comp (REchar 'b') (star (REchar 'b')))

def ac_plus : RE (Ch Char) :=
  comp (REchar 'a') (comp (REchar 'c') (star (REchar 'c')))

def test_re : RE (Ch Char) :=
  plus ab_plus ac_plus

#eval [mkchar 'a', mkchar 'b'] ∈ (test_re).matches'
#eval (test_re)
#eval [mkchar 'a', mkchar 'c'] ∈ (test_re).matches'
#eval [mkchar 'a', mkchar 'b', mkchar 'b', mkchar 'b'] ∈ (test_re).matches'
-/








--#eval ((toεNFA test_re).start)
