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
  [BEq α] [BEq σ] [BEq β]
  {α : Type u} {β : Type u} {σ : Type v}
  [DecidableEq α] [DecidableEq σ] [DecidableEq β]
  [Inhabited α] [Inhabited β]
  (EOS : α)

structure FSA (α σ) where
  alph : List α
  states : List σ
  start : List σ
  step : σ → α → List σ
  accept : List σ

def FSA.transitions (fsa : FSA α σ) : List (σ × α × List σ) :=
  fsa.states.flatMap (fun q =>
    (fsa.alph.map (fun c =>
        (q, c, fsa.step q c)
       )
    )
  )

def FSA.mkStep (transitions : List (σ × α × List σ)) : σ → α → List σ :=
  fun s a =>
    transitions.filterMap (fun (s', a', ts) =>
      if s = s' && a = a' then some ts else none
    )
    |> List.flatten


structure FST (α β σ) where
  alph : List α
  oalph : List β
  states : List σ
  start : List σ
  step : σ → α → (List σ × List β)
  accept : List σ

def FST.transitions (fst : FST α β σ) : List (σ × α × (List σ × List β)) :=
  fst.states.flatMap (fun q =>
    (fst.alph.map (fun c =>
        (q, c, fst.step q c)
       )
    )
  )

def FST.mkStep (transitions : List (σ × α × (List σ × β))) : σ → α → (List σ × β) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD ([], default)

open Std

instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => {
  start := (FSA.start fsa).toFinset
  step := fun q a => (FSA.step fsa q a).toFinset
  accept := (FSA.accept fsa).toFinset
}⟩

structure LexerSpec (α β σ) where
  automaton : FSA α σ
  term_sym : β


-- A recognizer for a token: returns true if the input is a valid token
noncomputable def isToken (specs : List (LexerSpec α β σ)) (xs : List α) : Option β :=
  specs.findSome? fun s =>
    let nfa : NFA α σ := s.automaton
    if (NFA.accepts nfa) xs then s.term_sym else none

-- A predicate for prefix of any token
def isPrefix (specs : List (LexerSpec α β σ)) (xs : List α) : Prop :=
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

def BuildLexingFST (fsa : FSA α σ) (oalph : List α) (h : fsa.start.length = 1) : FST α α σ := Id.run do
  let Q := fsa.states
  let trans := fsa.transitions
  let alph := fsa.alph
  let q0 := fsa.start[0]

  let F' := [q0]

  let mut trans' : List (σ × α × (List σ × List α)) := trans.map (fun (q, c, q') => (q, c, (q', [])))
  for q in Q do
    for T in oalph do
      if (fsa.step q T).length > 0 then -- if q recognizes T ∈ Γ
        for c in alph do
          let next := fsa.step q c
          for q' in next do
            for q'' in Q do
              if not (List.elem q'' next) && List.elem q' (fsa.step q0 c) then
                trans' := trans' ++ [(q, c, ([q], [T]))]
        trans' := trans' ++ [(q, EOS, ([q0], [T, EOS]))]

  ⟨alph, oalph, Q, F', FST.mkStep trans', F'⟩


end Symbols
