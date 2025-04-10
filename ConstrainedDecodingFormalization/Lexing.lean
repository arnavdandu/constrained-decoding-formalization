import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Std.Data.HashSet
--import Mathlib.Data.Set.Finite

universe u v w

#check Language

section Symbols
variable
  [BEq α] [BEq σ]
  {α : Type u} {β : Type u} {σ : Type v}
  (EOS : List α)

structure FSA (α σ) where
  alph : α
  states : List σ
  start : List σ
  step : σ → α → List σ
  accept : List σ

structure FST (α β σ) where
  alph : α
  oalph : β
  states : List σ
  start : List σ
  step : σ → α → (List σ × β)
  accept : List σ


open Std

instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨λ fsa => {
  start := (FSA.start fsa).toFinset
  step := λ q a => (FSA.step fsa q a).toFinset
  accept := (FSA.accept fsa).toFinset
}⟩

structure LexerSpec (α β σ) where
  automaton : FSA α σ
  term_sym : β

-- A recognizer for a token: returns true if the input is a valid token
def isToken : List α → Option β := sorry

-- A predicate for prefix of any token
def isPrefix : List α → Prop := sorry

noncomputable def NFA.prefixAccepts {α σ} (nfa : NFA α σ) (xs : List α) : Prop :=
  ∃ ys, NFA.accepts nfa (xs ++ ys)

noncomputable def PartialLexer [DecidableEq σ] (specs : List (LexerSpec α β σ)) (EOS : List α) : List α → Option (List β × List α) :=
  letI := Classical.propDecidable

  let isToken (xs : List α) : Option β :=
    specs.findSome? fun s =>
      let nfa : NFA α σ := s.automaton
      if NFA.accepts nfa xs then some s.term_sym else none

  let isPrefix (xs : List α) : Prop :=
    specs.any fun s =>
      let nfa : NFA α σ := s.automaton
      NFA.prefixAccepts nfa xs

  sorry

end Symbols
