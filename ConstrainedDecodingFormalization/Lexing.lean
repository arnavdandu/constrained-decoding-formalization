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

section Symbols
variable
  [BEq α] [BEq σ]
  {α : Type u} {β : Type u} {σ : Type v}
  (EOS : α)

structure FSA (α) (σ) where
  alph : α
  states : List σ
  start : List σ
  step : σ → α → List σ
  accept : List σ

structure FST (α) (β) (σ) where
  alph : α
  oalph : β
  states : List σ
  start : List σ
  step : σ → α → (List σ × β)
  accept : List σ


open Std

instance [BEq σ] [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨λ fsa => {
  start := (FSA.start fsa).toFinset
  step := λ q a => (FSA.step fsa q a).toFinset
  accept := (FSA.accept fsa).toFinset
}⟩

end Symbols
