import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import ConstrainedDecodingFormalization.CFG

structure PDA (Γ π σ) where
  alph : List Γ
  states : List σ
  start : σ
  -- if top of stack matches first, replace with second
  step : σ → Γ → Option (List π × List π × σ)
  accept : List σ

-- inspired by Mathlib DFA
namespace PDA

variable { Γ π σ } [ BEq π ] ( P : PDA Γ π σ )

instance [Inhabited σ] : Inhabited (PDA Γ π σ) :=
  ⟨PDA.mk default default default (fun _ _ => none) default⟩


def evalFrom ( s: σ ) ( st : List π ) : List Γ → Option (σ × List π) :=
  List.foldl ( fun s a => do
      let (s, st) ← s
      let (top, replace, dst) ← P.step s a
      -- if the top prefix of stack matches top, replace
      if st.isPrefixOf top then
        pure (dst, replace ++ st.drop top.length)
      else
        none
    ) (some (s, st))

@[simp]
theorem evalFrom_nil (s : σ) : P.evalFrom s [] [] = some (s, []) :=
  rfl

def evalFull : List Γ → Option (σ × List π) :=
  fun w => (P.evalFrom P.start [] w)

def eval : List Γ → Option σ :=
  fun w => (P.evalFrom P.start [] w).map Prod.fst

def acceptsFrom ( s: σ ) (st : List π ) : Language Γ :=
  { w | ∃ f, (P.evalFrom s st w).map Prod.fst = some f ∧ f ∈ P.accept }

def accepts : Language Γ := P.acceptsFrom P.start []

-- strings that are not rejected early
def intermediate : Language Γ :=
  { w | P.eval w ≠ none }

def pruned : Prop :=
  -- for all states that are reachable,
  -- can we eventually reach an accepting state?
  ∀ s st, (∃ w, P.evalFull w = some (s, st)) → (∃ v, v ∈ P.acceptsFrom s st)

-- Theorems: stack invarinace
-- todo once we reformulate FSA?
theorem stackInvariance : 0 = 0 := sorry

theorem prunedIntermediateEqPrefix ( h : P.pruned ) :
  P.intermediate = P.accepts.prefixes :=
  sorry

-- builds parser from cfg
def CFGStackAlphabet := Nat
variable [ BEq CFGStackAlphabet ]
def CFGState := Nat
def fromCFG ( C : ContextFreeGrammar Γ ) : PDA Γ CFGStackAlphabet CFGState :=
  sorry

-- build is correct
theorem fromCFGCorrect ( C: ContextFreeGrammar Γ ) :
  C.language = (fromCFG C).accepts := sorry

theorem fromCFGPruned ( C: ContextFreeGrammar Γ ) :
  (fromCFG C).pruned := sorry

end PDA
