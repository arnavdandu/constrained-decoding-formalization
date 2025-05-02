import Mathlib.Computability.NFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Basic

universe u v w y

variable
  {α : Type u} {Γ : Type v} {σ : Type w} 
  [DecidableEq α] [DecidableEq σ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ]

structure FSA (α σ) where
  alph : List α
  states : List σ
  start : σ
  step : σ → α → List σ
  accept : List σ

variable (A : FSA α σ)

#check List.flatten []

def FSA.transitions (fsa : FSA α σ) : List (σ × α × List σ) :=
  fsa.states.flatMap (fun q =>
    (fsa.alph.map (fun c =>
        (q, c, fsa.step q c)
      )
    )
  )

def FSA.mkStep (transitions : List (σ × α × List σ)) : σ → α → List σ :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD ([])

def FSA.stepList (S : List σ) (a : α) : List σ :=
  (S.flatMap (fun s => A.step s a)).eraseDups

def FSA.evalFrom (start : σ) : List α → List σ :=
  List.foldl A.stepList [start]

def FSA.eval : List α → List σ :=
  A.evalFrom A.start

def FSA.acceptsFrom ( s: σ ) : Language α :=
  { w | ∃ f ∈ A.evalFrom s w, f ∈ A.accept }

def FSA.accepts : Language α := A.acceptsFrom A.start
  

structure FST (α Γ σ) where
  alph : List α
  oalph : List Γ
  states : List σ
  start : σ
  step : σ → α → (List σ × List Γ)
  accept : List σ

def FST.transitions (fst : FST α Γ σ) : List (σ × α × (List σ × List Γ)) :=
  fst.states.flatMap (fun q =>
    (fst.alph.map (fun c =>
        (q, c, fst.step q c)
      )
    )
  )

def FST.mkStep (transitions : List (σ × α × (List σ × Γ))) : σ → α → (List σ × Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD ([], default)

instance : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => {
  start := {fsa.start}
  step := fun q a => (FSA.step fsa q a).toFinset
  accept := (FSA.accept fsa).toFinset
}⟩

instance : Coe (FSA α σ) (DFA α (Set σ)) := ⟨fun fsa => (fsa : NFA α σ).toDFA⟩

