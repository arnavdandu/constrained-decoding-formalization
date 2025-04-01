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

variable (EOS : α)

--set_option diagnostics true
open RegularExpression

--ab+
#check (char 'a') * (char 'b' * star (char 'b'))

--ac+
#check (char 'a') * (char 'c' * star (char 'c'))

structure FSA (α : Type u) (σ : Type v) where
  input : List α
  states : List σ
  start : σ
  step : σ → α → List σ
  accept : List σ

structure FST (α : Type u) (β : Type w) (σ : Type v) where
  input : List α
  output : List β
  states : List σ
  start : σ
  step : σ → α → (List σ × List β)
  accept : List σ

structure Lexer (α : Type u) (β : Type w) where
  lex : List α → (List β × List α)

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

section Symbols
variable {α : Type u}

abbrev Word (α : Type u) := List α -- for input/output symbols
abbrev Vocab (α : Type u) := List (Word α)
abbrev State (α : Type u) := List α
abbrev Next (α : Type u) := List (State α)
abbrev Output (α : Type u):= List (List α)

noncomputable def build_detokenizing_fst (V : Vocab α) [BEq α] : FST (Word α) (Word α) (State α) := Id.run do
  let q_ε := ([] : List α)
  let mut Q := [q_ε]
  let F := [q_ε]
  let q₀ := q_ε
  let mut δ := []

  for s in V do
    let k := s.length
    let mut q_prev := q_ε
    if h : k > 0 then
      for i in [1:k] do
        if h' : i < k then
          let q_c1_i := s.take i
          let q_ci := [s[i]]
          Q := Q ++ [q_c1_i]
          δ := δ ++ [(q_prev, q_ε, [q_ci], [q_c1_i])]
          q_prev := q_c1_i
        let q_c1_k := s.take k
        let q_ck := [s[k - 1]]
        δ := δ ++ [(q_prev, q_c1_k, [q_ck], [q_ε])]

  let step : State α → Word α → (Next α × Output α) := fun state input =>
      let transitions := δ.filter (fun (q₁, a, q₂, o) => q₁ == state ∧ a == input)
      let nextStates := transitions.map (fun (_, _, q₂, _) => if h : q₂.length > 0 then q₂[0] else [])
      let outputs := transitions.map (fun (_, _, _, o) => if h : o.length > 0 then o[0] else [])
      (nextStates, outputs)


  ⟨V, V, Q, q₀, step, F⟩

end Symbols


def build_lexing_fst (A : FSA α σ) (output : List α) [DecidableEq σ] [BEq α] : FST α α σ :=
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

def build_lexing_fst_iter (A : FSA α σ) (output : List α) [DecidableEq σ] [BEq α] : FST α α σ := Id.run do
  let Q := A.states
  let δ := A.step
  let q₀ := A.start

  let Ffst := {q₀}

  -- δfst := {q -- (c,ε) --> q' | q -- c --> q' ∈ δ}
  let mut δfst : List (σ × α × σ × List α) := []
  for q in Q do
    for c in A.input do
      for q' in (δ q c) do
        δfst := δfst ++ [(q, c, q', [])]

  -- for state q that recognizes language token T do
  for q in Q do
    for T in output do
      if (δ q T).isEmpty then
        -- for (c, q') s.t.
        for c in A.input do
          -- q0 -- c --> q' ∈ δ
          for q' in (δ q₀ c) do
            -- ∃q'' s.t. q -- c --> q'' ∉ δ
            if (Q \ δ q c).isEmpty then
              δfst := δfst ++ [(q, c, q', [T])]
        δfst := δfst ++ [(q, EOS, q₀, [T, EOS])]

  -- create step function
  let step (s : σ) (c : α) : (List σ × List α) :=
    let nextTransitions := δfst.filter (fun (s₁, a, _, _) => s₁ == s ∧ a == c)
    let nextStates := nextTransitions.map (fun (_, _, s₂, _) => s₂)
    let outputSymbols := nextTransitions.foldl (fun acc (_, _, _, o) => acc ++ o) []
    (nextStates, outputSymbols)

  ⟨A.input, output, Q, q₀, step, Ffst⟩

/-
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
-/
