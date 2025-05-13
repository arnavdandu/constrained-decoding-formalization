import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Vocabulary
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Range

open Classical List RegularExpression

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

  let oalph := (List.flatten V).dedup

  for s in V do
    let k := s.length
    let mut q_prev := q_ε
    if h : k > 0 then
      for i in [1:k-1] do
        if h' : i < k then
          let q_c1_i := s.take i
          let c_i := [s[i]]
          Q := Q.insert q_c1_i
          δ := δ.insert (q_prev, none, ([q_c1_i], c_i))
          q_prev := q_c1_i
        let c1_k := s.take k
        let c_k := [s[k - 1]]
        δ := δ.insert (q_prev, c1_k, ([q_ε], c_k))

  ⟨V, oalph, Q, q₀, FST.mkStep δ, F⟩

noncomputable def evalTokenLevelFST (q : State (Ch α)) (T : Token (Ch α)) (fst_lex : FST (Ch α) (Token (Ch α)) (St P)) (fst_detok : εFST (Token (Ch α)) (Ch α) (State (Ch α))) :
    List (St P) × List (Token (Ch α)) :=
  let detok_out := (fst_detok.step q T).2
  fst_lex.eval detok_out

noncomputable def BuildTokenLevelFST (fst_lex : FST (Ch α) (Token (Ch α)) (St P)) (fst_detok : εFST (Token (Ch α)) (Ch α) (State (Ch α))) :
    FST (Token (Ch α)) (Token (Ch α)) σ := Id.run do

  let Q_in := fst_detok.states
  let Q_comp := fst_lex.states
  let alph := fst_detok.alph
  let oalph := fst_lex.oalph
  let mut trans := fst_lex.stepList
  let q₀ := fst_lex.start
  let F := fst_lex.accept

  for T in alph do
    let lex_out := (evalTokenLevelFST fst_detok.start T fst_lex fst_detok)


  sorry

noncomputable def BuildInverseTokenSpannerTable (fst_comp : FST (Token (Ch α)) (Token (Ch α)) σ) : σ × List (Token (Ch α)) → List (Token (Ch α)) := Id.run do
  sorry


end Symbols
