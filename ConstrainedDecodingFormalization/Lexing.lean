import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Std.Data.HashSet
--import Mathlib.Data.Set.Finite

open Classical

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
noncomputable def isToken (specs : List (LexerSpec α β σ)) (xs : List α) : Option β :=
  specs.findSome? fun s =>
    let nfa : NFA α σ := s.automaton
    if NFA.accepts nfa xs then s.term_sym else none

-- A predicate for prefix of any token
noncomputable def isPrefix (specs : List (LexerSpec α β σ)) (xs : List α) : Prop :=
  specs.any fun s =>
    let nfa : NFA α σ := s.automaton
    ∃ ys, NFA.accepts nfa (xs ++ ys)

inductive LexRel (specs : List (LexerSpec α β σ)) :
    List α → List β → List α → Prop
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

noncomputable def PartialLex (specs : List (LexerSpec α β σ)) (w : List α) : Option (List β × List α) :=
  if h : ∃ out : List β × List α, LexRel specs w out.1 out.2 then
    some (choose h)
  else none

end Symbols
