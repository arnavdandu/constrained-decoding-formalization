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

noncomputable def BuildTokenLevelFST (fst_lex : FSTLex α Γ σ0) (fst_detok : FSTDetok α σ1) :
    FST (Token (Ch α)) Γ (σ0 × σ1) := Id.run do
  sorry

def RealizableSequences (fst_comp : FSTComp α Γ σ2) : Set (List Γ) :=
  -- all possible transitions, adjoined with singleton transitions afterwards
  { Ts' | ∃ q_0 t Ts q_1 T,
          fst_comp.step q_0 t = (q_1, Ts) ∧
          T ∈ fst_comp.singleProducible q_1 ∧
          Ts' = Ts ++ [T] }


def InverseTokenSpannerTable (fst_comp : FSTComp α Γ σ2) : List Γ → σ2 → (Set (Token (Ch α))) :=
  fun rs st =>
    if h : rs ≠ [] then
      let Ts := rs.dropLast
      let T := rs.getLast h
      { t | ∃ q_1,
            fst_comp.step st t = (some (q_1, Ts)) ∧
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
