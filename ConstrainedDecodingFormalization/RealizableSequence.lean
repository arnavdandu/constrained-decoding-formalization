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
variable {α : Type u} {Γ : Type v} { σ0 σ1 σ2 : Type w}

abbrev Vocab (α : Type u) := List (Token α)
abbrev State (α : Type u) := List α
abbrev Next (α : Type u) := List (State α)
abbrev Output (α : Type u):= List (List α)

abbrev Re (Γ : Type v) := List (List Γ)
abbrev FSTDetok (α : Type u) (σ : Type w) := εFST (Token (Ch α)) (Ch α)  σ
abbrev FSTLex (α : Type u) (Γ : Type v) (σ : Type w) := FST (Ch α) Γ σ
abbrev FSTComp (α : Type u) (Γ : Type v) (σ : Type w) := FST (Token (Ch α)) Γ σ

section Symbols

variable
  [DecidableEq α] [DecidableEq σ0] [DecidableEq σ1] [DecidableEq σ2] 
  [DecidableEq Γ] [BEq α] [BEq Γ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

#check Vocabulary (Ch α) (Γ)

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

noncomputable def BuildDetokenizingFST (V : Vocab (Ch α)) [Fintype (Ch α)] : FSTDetok α (State (Ch α)) := Id.run do
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

noncomputable def evalTokenLevelFST (q : σ1) (T : Token (Ch α)) (fst_lex : FSTLex α Γ σ0) (fst_detok : FSTDetok α σ1) :
    List σ0 × List Γ :=
  let detok_out := (fst_detok.step q T).2
  fst_lex.eval detok_out

noncomputable def BuildTokenLevelFST (fst_lex : FSTLex α Γ σ0) (fst_detok : FSTDetok α σ1) :
    FST (Token (Ch α)) Γ (σ0 × σ1) := Id.run do

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

def RealizableSequences (fst_comp : FSTComp α Γ σ2) : Set (List Γ) := 
  -- all possible transitions, adjoined with singleton transitions afterwards
  { Ts' | ∃ q_0 t Ts q_1 T, 
          fst_comp.step q_0 t = ([q_1], Ts) ∧ 
          T ∈ fst_comp.singleProducible q_1 ∧
          Ts' = Ts ++ [T] }


def InverseTokenSpannerTable (fst_comp : FSTComp α Γ σ2) : List Γ → σ2 → (Set (Token (Ch α))) := 
  fun rs st => 
    if h : rs ≠ [] then 
      let Ts := rs.dropLast
      let T := rs.getLast h
      { t | ∃ q_1, 
            fst_comp.step st t = ([q_1], Ts) ∧ 
            T ∈ fst_comp.singleProducible q_1 }
    else ∅

def BuildInverseTokenSpannerTable (fst_comp : FSTComp α Γ σ2) : Re Γ × (List Γ → σ2 → (List (Token (Ch α)))) := Id.run do
  sorry

def itst_fst_eq_rs (fst_comp : FSTComp α Γ σ2) : (BuildInverseTokenSpannerTable fst_comp).fst.toFinset = RealizableSequences fst_comp := by sorry

def itst_snd_eq_itst (fst_comp : FSTComp α Γ σ2) : 
    ∀ rs s, ((BuildInverseTokenSpannerTable fst_comp).snd rs s).toFinset = InverseTokenSpannerTable fst_comp rs s := by sorry

end Symbols

theorem rs_ne_empty (fst_comp : FSTComp α Γ σ2) : [] ∉ RealizableSequences fst_comp := by 
  simp_all[RealizableSequences] 

