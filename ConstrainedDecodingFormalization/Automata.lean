import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PFun

universe u v w y

variable
  {α : Type u} {Γ : Type v} {σ : Type w}
  [DecidableEq α] [DecidableEq σ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ] [Fintype σ]

structure FSA (α σ) where
  alph : List α
  states : List σ
  start : σ
  step : σ → α → Option σ
  accept : List σ

namespace FSA

variable (A : FSA α σ)

instance : DecidableEq (FSA α σ) := fun M N =>
  let toFun (fsa : FSA α σ) := (fsa.alph, fsa.states, fsa.start, fsa.step, fsa.accept)

  have h₁ : Decidable (toFun M = toFun N) := by
    simp_all only [Prod.mk.injEq, toFun]
    exact instDecidableAnd

  have h_inj : ∀ a b : FSA α σ, toFun a = toFun b → a = b := by
      intro a b h_eq
      cases a
      cases b
      simp only [toFun] at h_eq
      simp only [mk.injEq]
      simp_all only [Prod.mk.injEq, and_self, toFun]

  if h : toFun M = toFun N then
    isTrue (by exact h_inj M N h)
  else
    isFalse (by intro hMN; apply h; simp [toFun, hMN])

def transitions (fsa : FSA α σ) : List (σ × α × Option σ) :=
  fsa.states.flatMap (fun q =>
    (fsa.alph.map (fun c =>
        (q, c, fsa.step q c)
      )
    )
  )

def mkStep (transitions : List (σ × α × Option σ)) : σ → α → Option σ :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD (default)

def stepList (S : List σ) (a : α) : List (Option σ) :=
  (S.map (fun s => A.step s a)).eraseDups

def evalFrom (s : σ) (l : List α) : Option σ :=
  match s, l with
  | s, [] => s
  | s, a :: as =>
    match (A.step s a) with
    | none => none
    | some s' => evalFrom s' as

def eval : List α → Option σ :=
  A.evalFrom A.start

def acceptsFrom ( s: σ ) : Language α :=
  { w | ∃ f ∈ A.evalFrom s w, f ∈ A.accept }

def accepts : Language α := A.acceptsFrom A.start

/-- A word ` w ` is accepted at ` q ` if there is ` q' ` such that ` evalFrom q w = q' `-/
def accepted (s : σ) (w : List α) : Prop := A.evalFrom s w ≠ none

def toDFA : DFA α (Option σ) :=
  let step : Option σ → α → Option σ
    | none, _ => none
    | some s, a => A.step s a

  let accept := A.accept.map (fun s => some s)

  ⟨step, A.start, accept.toFinset.toSet⟩



end FSA

structure FST (α Γ σ) where
  alph : List α
  oalph : List Γ
  states : List σ
  start : σ
  step : σ → α → (Option σ × List Γ)
  accept : List σ

namespace FST

def transitions (fst : FST α Γ σ) : List (σ × α × (Option σ × List Γ)) :=
  fst.states.flatMap (fun q =>
    (fst.alph.map (fun c =>
        (q, c, fst.step q c)
      )
    )
  )

def mkStep (transitions : List (σ × α × (Option σ × List Γ))) : σ → α → (Option σ × List Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _) => s = s' && a = a')
    |>.map (fun (_, _, ts) => ts)
    |>.getD (none, [])

variable (M : FST α Γ σ)

def evalFrom (s : σ) (l : List α) : Option σ × List Γ :=
  match s, l with
  | s, [] => (s, [])
  | s, a :: as =>
    match (M.step s a) with
    | (none, _) => (none, [])
    | (some s', T) => ((evalFrom s' as).1, (evalFrom s' as).2 ++ T)

def eval (input : List α) : Option σ × List Γ :=
  M.evalFrom M.start input

def producible (q : σ) : Language Γ :=
    { t | ∃ w, (M.evalFrom q w).snd = t }

def singleProducible (q : σ) : Set Γ :=
    { t | ∃ w, (M.evalFrom q w).snd = [t] }

end FST

-- same as FST, but Option α allows for ε-transitions
structure εFST (α Γ σ) where
  alph : List α
  oalph : List Γ
  states : List σ
  start : σ
  step : σ → Option α → (Option σ × List Γ)
  accept : List σ

namespace εFST


end εFST


instance : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => {
  start := {fsa.start}
  step := fun q a => (FSA.step fsa q a).toFinset
  accept := (FSA.accept fsa).toFinset
}⟩

instance : Coe (FSA α σ) (DFA α (Set σ)) := ⟨fun fsa => (fsa : NFA α σ).toDFA⟩
