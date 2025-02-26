import Mathlib.Computability.NFA
import Mathlib.Computability.DFA

universe u v w

/-- A FST is a set of states (`σ`), a transition function from state to state that outputs a sequence
  of elements (`List β`) on transition, labelled by the alphabet (`step`), a set of starting states (`start`) and
  a set of acceptance states (`accept`). Note the transition function sends a state to a `Set` of states.
  These are the states that it may be sent to. -/
structure FST (α : Type u) (β : Type w) (σ : Type v) where
  step : σ → α → (σ × List β)
  start : Set σ
  accept : Set σ

structure Lexer (α : Type u) (β : Type w) where
  lex : List α → (List β × List α)

def lex (α : Type u) (β : Type w) (tokenize : α → Option β) : List α → (List β × List α)
  | [] => ([], [])
  | c :: cs =>
      match tokenize c with
      | some t =>
          let (tokens, rest) := lex α β tokenize cs
          (t :: tokens, rest)
      | none => ([], c :: cs)

variable {α : Type u} {σ σ' : Type v} {β : Type w} (M : FST α β σ)

#check NFA
#check FST

instance [Inhabited σ] : Inhabited (FST α β σ) :=
  ⟨FST.mk (fun _ _ => (default, [])) ∅ ∅⟩

def one_lookahead (Lexer : Lexer α β) : Prop :=
  ∀ (w : List α) (c : α),
    let (tokens, r) := Lexer.lex w;
    let (tokens', r') := Lexer.lex (w ++ [c]);
    (∃ (t : β), tokens' = tokens ++ [t] ∧ r' = [c]) ∨
    (tokens' = tokens ∧ r' = r ++ [c])

class Lexer.IsOneLookahead (Lexer : Lexer α β) : Prop where
  one_lookahead : one_lookahead Lexer
