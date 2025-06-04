import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.Language
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

import ConstrainedDecodingFormalization.RegularExpressionsToEpsilonNFA
import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Partition

open List RegularExpression

universe u v w

abbrev RE := RegularExpression

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ] [DecidableEq Γ]
  [BEq α] [BEq σ] [LawfulBEq σ] [LawfulBEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype σ] [Fintype Γ]

/-- Extend character alphabet with EOS symbol-/
inductive ExtChar (α : Type u)
| char : α → ExtChar α
| eos  : ExtChar α
deriving DecidableEq, Repr

instance {α} : Coe (α) (ExtChar α) := ⟨fun a => ExtChar.char a⟩
instance [e: FinEnum α] : FinEnum (ExtChar α) where
  card := FinEnum.card α + 1
  equiv :=
    let e := e.equiv
    { toFun := fun x =>
        match x with
        | ExtChar.eos     => ⟨FinEnum.card α, Nat.lt_succ_self _⟩
        | ExtChar.char a  => ⟨e a, Nat.lt_succ_of_lt (Fin.is_lt (e a))⟩
      invFun := fun i =>
        if h : i.val < FinEnum.card α then ExtChar.char (e.symm ⟨i.val, h⟩)
        else ExtChar.eos
      left_inv := by
        intro x
        cases x with
        | eos =>
          simp
        | char a =>
          simp
      right_inv := by
        intro ⟨i, hi⟩
        by_cases h : i < FinEnum.card α
        · simp [h]
        · have : i = FinEnum.card α := by
            linarith
          subst this
          simp [h]
      }
  decEq := by infer_instance

abbrev Ch := ExtChar

variable (P : RE (Ch α))

@[ext]
structure Terminal (α : Type u) (Γ : Type v)  where
  expr : RegularExpression α
  symbol : Γ
deriving Repr

def LexingFSA := P.toεNFA.toNFA

@[ext]
structure Token (α : Type u) (Γ : Type v) where
  symbol : Γ
  string : List α
deriving Repr, DecidableEq

def List.terminalSymbols (terminals : List (Terminal α Γ)) : List Γ :=
  terminals.map (fun t => t.symbol)

def List.sequence {α : Type u} (tokens : List (Token α Γ)) : List Γ :=
  tokens.map (fun t => t.symbol)

structure LexerSpec (α Γ σ) where
  automaton : FSA α σ
  term: σ → Option Γ
  hterm: ∀ s, s ∈ automaton.accept ↔ (term s).isSome
  term_inj: ∀ s₁ s₂ t, term s₁ = some t ∧ term s₂ = some t → s₁ = s₂

structure LexerSpecification (α Γ σ) where
  automaton : FSA α σ
  term_sym : Γ

-- A recognizer for a token: returns true if the input is a valid token
def isToken (specs : List (LexerSpecification α Γ σ)) (xs : List α) : Option Γ :=
  --letI := Classical.propDecidable
  specs.findSome? fun s =>
    if xs ∈ s.automaton.accepts then some s.term_sym else none

-- A predicate for prefix of any token (Note: decidability not proven yet. Will probably need to do something similar as acceptance decidability.)
def isPrefix (specs : List (LexerSpecification α Γ σ)) (xs : List α) : Prop :=
  ∃ s ∈ specs, FSA.isPrefix s.automaton xs


inductive LexRel (specs : List (LexerSpecification (Ch α) Γ σ)) :
    List (Ch α) → List (Ch Γ) → List (Ch α) → Prop
  | empty :
      LexRel specs [] [] []

  -- When the next character is EOS, and wr recognizes a token
  | done {wr ws ts tj} :
      LexRel specs ws ts wr →
      isToken specs wr = some tj →
      LexRel specs (ws ++ [.eos]) (ts ++ [.char tj]) []

  -- When next character is NOT EOS:
  -- (emit) If wr ∈ L(A^j) but (wr ++ c) is no longer a prefix of any token
  | emit {wr c cs tj T} :
      c ≠ .eos →
      isToken specs wr = some tj →
      ¬ isPrefix specs (wr ++ [c]) →
      LexRel specs (c :: cs) T [] →
      LexRel specs (wr ++ c :: cs) (tj :: T) wr

  -- (extend) If (wr ++ c) is still a valid prefix of some token
  | extend {wr c cs T} :
      c ≠ .eos →
      isPrefix specs (wr ++ [c]) →
      LexRel specs cs T (wr ++ [c]) →
      LexRel specs (c :: cs) T wr

def Lexer (α : Type u) (Γ : Type v) := List α -> Option (List Γ × List α)

-- Retain the noncomputable version for proofs
noncomputable def PartialLex (specs :  List (LexerSpecification (Ch α) Γ σ)) (w : List (Ch α)) :
    Option (List (Ch Γ) × List (Ch α)) :=
  letI := Classical.propDecidable
   if h : ∃ out : List (Ch Γ) × List (Ch α), LexRel specs w out.1 out.2 then
     some (Classical.choose h)
   else none

--instance : DecidableEq (Γ × St P) := by apply instDecidableEqProd

/-- Given a lexing automaton `A`, build a character-to-token lexing FST with output over `Γ`
    For the lexing FSA, we'll use the convention that each terminal symbol is attached to an accept state (see Fig. 1) -/
def BuildLexingFST (spec: LexerSpec α Γ σ) :
    FST (Ch α) (Ch Γ) σ := Id.run do
  let ⟨A, term, hterm, _⟩ := spec

  let q0 := A.start
  let F := A.accept

  let step := fun (q : σ) (c : Ch α) =>
    match c with
    | ExtChar.char c =>
      if h : (A.step q c).isSome then
        some ((A.step q c).get h, [])
      else if h : q ∈ F then
        let T := (term q).get <| ((hterm q).mp h)
        A.step q0 c |>.map (fun q' => (q', [ExtChar.char T]))
      else
        none
    | ExtChar.eos =>
      if h : q ∈ F then
        let T := (term q).get <| ((hterm q).mp h)
        some (q0, [T, .eos])
      else
        none

  ⟨q0, step, [q0]⟩


-- def PartialLexSplit (spec : LexerSpec α Γ σ) (w : List α) :
--     match PartialLex specs (w.map (λ c => ExtChar.char c) ++ [.eos]) with
--     | some (tokens, unlexed) =>
--       -- exists a partition corresponding to the output of partial lex
--       unlexed = [] ∧
--       ∃ p, IsPartition p w ∧ p.length = tokens.length ∧
--         ∀ t ∈ (List.zip tokens p), ∃ spec ∈ specs, t.fst = spec.term_sym ∧ t.snd ∈ spec.automaton.accepts
--     | none =>
--       -- there is no possible partitions in which we can lex it
--       ∀ p, IsPartition p w → ∃ x ∈ p, ∀ lexer ∈ specs, x ∉ lexer.automaton.accepts
--       := by
--   split
--   case h_1 tokens unlexed heq =>
--     simp[PartialLex] at heq
--     rcases heq
--     case intro w1 h =>
--     cases w1
--     case intro w' h' =>
--     cases h'
--     case intro w'' h'' =>
--     sorry
--   case h_2 =>
--     sorry
