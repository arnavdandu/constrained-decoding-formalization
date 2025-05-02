import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Lexing
import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic

open Classical List

universe u v w

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ] [BEq α] [BEq Γ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

#check Vocabulary (Ch α) (Γ)

section Symbols
variable {α : Type u}

abbrev Vocab (α : Type u) := List (Token α)
abbrev State (α : Type u) := List α
abbrev Next (α : Type u) := List (State α)
abbrev Output (α : Type u):= List (List α)

--def VocabStr [Vocabulary (Ch α) (Γ)] (x : V) : List (Ch α) :=
 -- sorry

#check Language (Ch α)

instance TokenVocab [BEq (Ch α)] [DecidableEq (Ch α)] : Vocabulary (Ch α) (Token (Ch α)) where
  flatten := id
  embed a := [a]
  eos := []
  fe a := by simp
  empty b := by simp [Vocabulary.eos]

noncomputable def characterAlphabetSet (α : Type u) [Fintype (Ch α)] : List (Ch α) :=
  (Finset.univ : Finset (Ch α)).toList

noncomputable def BuildDetokenizingFST (V : Vocab (Ch α)) [Fintype (Ch α)] : εFST (Token (Ch α)) (Ch α) (State (Ch α)) := Id.run do
  let q_ε := ([] : List (Ch α))
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
          Q := Q.insert q_c1_i
          δ := δ.insert (q_prev, none, ([q_c1_i], q_ci))
          q_prev := q_c1_i
        let q_c1_k := s.take k
        let q_ck := [s[k - 1]]
        δ := δ.insert (q_prev, q_c1_k, ([q_ck], q_ε))

  ⟨V, characterAlphabetSet α, Q, q₀, FST.mkStep δ, F⟩

end Symbols
#check Vocabulary
