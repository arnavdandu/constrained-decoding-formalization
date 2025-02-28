import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Std.Data.HashSet
--import Mathlib.Data.Set.Finite

universe u v w

--set_option diagnostics true

structure FSA (α : Type u) (σ : Type v) where
  input : Finset α
  states : Finset σ
  start : σ
  step : σ → α → Finset σ
  accept : Finset σ

structure FSA_list (α : Type u) (σ : Type v) where
  input : List α
  states : List σ
  start : σ
  step : σ → α → List σ
  accept : List σ

/-- A FST is a set of states (`σ`), a transition function from state to state that outputs a sequence
  of elements (`List β`) on transition, labelled by the alphabet (`step`), a set of starting states (`start`) and
  a set of acceptance states (`accept`). Note the transition function sends a state to a `Set` of states.
  These are the states that it may be sent to. -/
structure FST (α : Type u) (β : Type w) (σ : Type v) where
  input : Finset α
  output : Finset β
  states : Finset σ
  start : σ
  step : σ → α → (Finset σ × List β)
  accept : Finset σ

structure FST_list (α : Type u) (β : Type w) (σ : Type v) where
  input : List α
  output : List β
  states : List σ
  start : σ
  step : σ → α → (List σ × List β)
  accept : List σ

structure Lexer (α : Type u) (β : Type w) where
  lex : List α → (List β × List α)


variable {α : Type u} {σ σ' : Type v} {β : Type w} (M : FST α β σ)
variable (EOS : α)

#check NFA
#check FST
#check String

open Std

instance [Inhabited σ] : Inhabited (FSA α σ) :=
  ⟨FSA.mk ∅ ∅ default (fun _ _ => default) ∅⟩

instance [Inhabited σ] : Inhabited (FST α β σ) :=
  ⟨FST.mk ∅ ∅ ∅ default (fun _ _ => (default, [])) ∅⟩

def one_lookahead (Lexer : Lexer α β) : Prop :=
  ∀ (w : List α) (c : α),
    let (tokens, r) := Lexer.lex w;
    let (tokens', r') := Lexer.lex (w ++ [c]);
    (∃ (t : β), tokens' = tokens ++ [t] ∧ r' = [c]) ∨
    (tokens' = tokens ∧ r' = r ++ [c])

class Lexer.IsOneLookahead (Lexer : Lexer α β) : Prop where
  one_lookahead : one_lookahead Lexer

noncomputable def build_lexing_fst_iter (A : FSA α σ) (output : Finset α) [DecidableEq σ] [BEq α] : FST α α σ := Id.run do
  let Q := A.states
  let δ := A.step
  let q0 := A.start

  let Ffst := {q0}

  -- δfst := {q -- (c,ε) --> q' | q -- c --> q' ∈ δ}
  let mut δfst : List (σ × α × σ × List α) := []
  for q in Q.toList do
    for c in A.input.toList do
      for q' in (δ q c).toList do
        δfst := δfst ++ [(q, c, q', [])]

  -- for state q that recognizes language token T do
  for q in Q.toList do
    for T in output.toList do
      if (δ q T).Nonempty then
        -- for (c, q') s.t.
        for c in A.input.toList do
          -- q0 -- c --> q' ∈ δ
          for q' in (δ q0 c).toList do
            -- ∃q'' s.t. q -- c --> q'' ∉ δ
            if (Q \ δ q c).Nonempty then
              δfst := δfst ++ [(q, c, q', [T])]
        δfst := δfst ++ [(q, EOS, q0, [T, EOS])]

  -- create step function
  let step (s : σ) (c : α) : (Finset σ × List α) :=
    let nextTransitions := δfst.filter (fun (s₁, a, _, _) => s₁ == s ∧ a == c)
    let nextStates := nextTransitions.map (fun (_, _, s₂, _) => s₂) |>.toFinset
    let outputSymbols := nextTransitions.foldl (fun acc (_, _, _, o) => acc ++ o) []
    (nextStates, outputSymbols)

  ⟨A.input, output, Q, q0, step, Ffst⟩

noncomputable def build_lexing_fst_func (A : FSA α σ) (output : Finset α) [DecidableEq σ] [BEq α] : FST α α σ :=
  let Q := A.states
  let δ := A.step
  let q0 := A.start

  let Ffst := {q0}

  -- {q -- (c,ε) --> q' | q -- c --> q' ∈ δ}
  let δfst₁ := Q.toList.flatMap (fun q =>
    A.input.toList.flatMap (fun c =>
      (δ q c).toList.map (fun q' => (q, c, q', [])) -- (c, ε) transition
    )
  )


  let δfst₂ := Q.toList.flatMap (fun q =>
    output.toList.flatMap (fun T =>
      if (δ q T).Nonempty then
        let transitions := A.input.toList.flatMap (fun c =>
          (δ q0 c).toList.filterMap (fun q' =>
            if (Q \ δ q c).Nonempty then some (q, c, q', [T]) else none
          )
        )
        transitions ++ [(q, EOS, q0, [T, EOS])]
      else []
    )
  )

  let δfst := δfst₁ ++ δfst₂

  -- create step function
  let step (s : σ) (c : α) : (Finset σ × List α) :=
    let nextTransitions := δfst.filter (fun (s₁, a, _, _) => (s₁ == s) && (a == c))
    let nextStates := nextTransitions.map (fun (_, _, s₂, _) => s₂) |>.toFinset
    let outputSymbols := nextTransitions.foldl (fun acc (_, _, _, o) => acc ++ o) []
    (nextStates, outputSymbols)

  ⟨A.input, output, Q, q0, step, Ffst⟩

def build_lexing_fst_list (A : FSA_list α σ) (output : List α) [DecidableEq σ] [BEq α] : FST_list α α σ :=
  let Q := A.states
  let δ := A.step
  let q0 := A.start

  let Ffst := {q0}

  -- {q -- (c,ε) --> q' | q -- c --> q' ∈ δ}
  let δfst₁ := Q.flatMap (fun q =>
    A.input.flatMap (fun c =>
      (δ q c).map (fun q' => (q, c, q', [])) -- (c, ε) transition
    )
  )


  let δfst₂ := Q.flatMap (fun q =>
    output.flatMap (fun T =>
      if ¬(δ q T).isEmpty then
        let transitions := A.input.flatMap (fun c =>
          (δ q0 c).filterMap (fun q' =>
            if ¬(Q \ δ q c).isEmpty then some (q, c, q', [T]) else none
          )
        )
        transitions ++ [(q, EOS, q0, [T, EOS])]
      else []
    )
  )

  let δfst := δfst₁ ++ δfst₂

  -- create step function
  let step (s : σ) (c : α) : (List σ × List α) :=
    let nextTransitions := δfst.filter (fun (s₁, a, _, _) => (s₁ == s) && (a == c))
    let nextStates := nextTransitions.map (fun (_, _, s₂, _) => s₂)
    let outputSymbols := nextTransitions.foldl (fun acc (_, _, _, o) => acc ++ o) []
    (nextStates, outputSymbols)

  ⟨A.input, output, Q, q0, step, Ffst⟩
