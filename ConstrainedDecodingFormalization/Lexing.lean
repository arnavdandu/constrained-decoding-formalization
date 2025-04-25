import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

import ConstrainedDecodingFormalization.Automata

open Classical List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]
  (EOS : α)


structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term_sym : Γ

-- A recognizer for a token: returns true if the input is a valid token
noncomputable def isToken (specs : List (LexerSpec α Γ σ)) (xs : List α) : Option Γ :=
  specs.findSome? fun s =>
    let nfa : NFA α σ := s.automaton
    if nfa.eval xs ⊆ nfa.accept then some s.term_sym else none

noncomputable def isToken_comp (specs : List (LexerSpec α Γ σ)) (xs : List α) : Option Γ :=
  specs.findSome? fun s =>
    let dfa : DFA α (Set σ) := s.automaton
    if dfa.eval xs ∈ dfa.accept then some s.term_sym else none

-- A predicate for prefix of any token
def isPrefix (specs : List (LexerSpec α Γ σ)) (xs : List α) : Prop :=
  specs.any fun s =>
    let nfa : NFA α σ := s.automaton
    ∃ ys, NFA.accepts nfa (xs ++ ys)

inductive LexRel (specs : List (LexerSpec α Γ σ)) :
    List α → List Γ → List α → Prop
  | empty :
      LexRel specs [] [] []

  -- (T₁...Tₖ T^j, ε) if c = EOS and wr ∈ L(A^j)
  | done {wr tj} :
      isToken specs wr = some tj →
      LexRel specs wr [tj] []

  -- (T₁...Tₖ, wrc) if c ≠ EOS and wrc ∈ L_prefix(A^i) for some i
  -- → (T₁...Tₖ T^j, c :: cs) if wr ∈ L(A^j) but wrc ∉ L_prefix(A^i) for all i.
  | emit {wr c cs tj T} :
      isToken specs wr = some tj →
      ¬ isPrefix specs (wr ++ [c]) →
      LexRel specs (c :: cs) T [] →
      LexRel specs (wr ++ c :: cs) (tj :: T) wr

  -- (T₁...Tₖ, wrc) if c ≠ EOS and wrc ∈ L_prefix(A^i) for some i.
  | extend {wr c cs T} :
      isPrefix specs (wr ++ [c]) →
      LexRel specs cs T (wr ++ [c]) →
      LexRel specs (c :: cs) T wr

def Lexer ( α : Type u ) ( Γ : Type v) := List α -> Option (List Γ × List α)

noncomputable def PartialLex (specs : List (LexerSpec α Γ σ)) (w : List α) : Option (List Γ × List α) :=
   if h : ∃ out : List Γ × List α, LexRel specs w out.1 out.2 then
     some (choose h)
   else none

#check ((PartialLex _) : Lexer _ _)


def BuildLexingFST (fsa : FSA α σ) (oalph : List α) : FST α α σ := Id.run do
  let Q := fsa.states
  let trans := fsa.transitions
  let alph := fsa.alph
  let q0 := fsa.start

  let F' := [q0]

  let mut trans' : List (σ × α × (List σ × List α)) := trans.map (fun (q, c, q') => (q, c, (q', [])))
  for q in Q do
    for T in oalph do
      if not (fsa.step q T).isEmpty then
        for c in alph do
          for q' in Q do
            if ∃ q'' ∈ Q, q'' ∉ fsa.step q c ∧ q' ∈ (fsa.step q0 c) then
              trans' := trans'.insert (q, c, ([q'], [T]))
        trans' := trans'.insert (q, EOS, ([q0], [T, EOS]))

  ⟨alph, oalph, Q, q0, FST.mkStep trans', F'⟩
