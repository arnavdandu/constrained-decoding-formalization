import Mathlib.Computability.Language
import Mathlib.Data.Set.Basic
import Mathlib.Computability.ContextFreeGrammar
import ConstrainedDecodingFormalization.CFG

-- helpers related to prefixes
section PrefixHelper
universe u
variable { α : Type u }
open List

theorem isPrefix_merge [ BEq α ] [ LawfulBEq α] ( xs ys zs : List α ) (h : ys <+: zs) :
      match xs.isPrefixOf? ys with
      | some rem => xs.isPrefixOf? zs = rem ++ zs.drop ys.length
      | none => True
  := by
  split
  case h_2 => constructor
  case h_1 rem heq =>
    have y_x_rem : xs ++ rem = ys := List.append_eq_of_isPrefixOf?_eq_some heq
    have x_p_y : xs <+: ys := Exists.intro rem y_x_rem
    have x_isp_z : xs.isPrefixOf zs := List.isPrefixOf_iff_prefix.mpr (List.IsPrefix.trans x_p_y h)
    cases h_xs_isp?_zs : xs.isPrefixOf? zs with
    | some rem' =>
      have xs_rem'_zs := List.append_eq_of_isPrefixOf?_eq_some h_xs_isp?_zs
      have xs_rem_ys : ys ++ zs.drop ys.length = zs := List.prefix_iff_eq_append.mp h
      conv at xs_rem_ys =>
        lhs
        lhs
        rw[←y_x_rem]
      rw[←xs_rem_ys] at xs_rem'_zs
      simp at xs_rem'_zs
      simp
      assumption
    | none =>
      have true : (xs.isPrefixOf? zs).isSome = true := by
        rw[(List.isSome_isPrefixOf?_eq_isPrefixOf xs zs)]
        assumption
      have false : (xs.isPrefixOf? zs).isSome = false := by
        rw[h_xs_isp?_zs]
        apply Option.isSome_none
      simp_all

end PrefixHelper

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

def fullStep ( s : Option (σ × List π) ) (t : Γ ) : Option ( σ × List π ) := do
  let (s, st) ← s
  let (top, replace, dst) ← P.step s t
  -- if the top prefix of stack matches top, replace
  if let some rem := top.isPrefixOf? st then
    pure (dst, replace ++ rem)
  else
    none

@[simp]
theorem fullStep_none ( t : Γ ) : P.fullStep none t = none :=
  by rfl

theorem fullStep_stackInvariance [ LawfulBEq π  ] : ∀ s st st' t, st <+: st' →
   match P.fullStep (some (s, st)) t with
  | some (sn, stn) => P.fullStep (some (s, st')) t = some (sn, stn ++ st'.drop st.length)
  | none => True
  := by
  intro s st st' t
  intro pfx
  split
  case h_2 => constructor
  case h_1 heq =>
  simp_all[fullStep]
  cases h : P.step s t with
  | some step =>
    have (top, rep, dst) := step
    simp[h] at heq
    split at heq
    case some.h_2 => contradiction
    rename_i top_pfx_st
    simp at heq
    simp[←heq]
    have partition := isPrefix_merge top st st' pfx
    simp only [top_pfx_st] at partition
    simp[partition]
  | none =>
    simp[h] at heq


def evalFrom ( s: Option ( σ × List π ) ) : List Γ → Option (σ × List π) :=
  List.foldl ( fun s a => do fullStep P s a) s

@[simp]
theorem evalFrom_nil (s : σ) (st : List π) : P.evalFrom (some (s, st)) [] = some (s, st) :=
  rfl

@[simp]
theorem evalFrom_cons (s : σ) (st : List π) (head: Γ) (tail : List Γ) : P.evalFrom (some (s, st)) (head :: tail) = P.evalFrom (P.fullStep ( some (s, st) ) head) tail := by
  simp[evalFrom]

@[simp]
theorem evalFrom_none  ( w : List Γ ) : P.evalFrom none w = none := by
  induction w
  rfl
  rename_i h t ih
  have : P.evalFrom none (h :: t) = P.evalFrom (P.fullStep none h) t := by rfl
  simp[this, fullStep_none, ih]


def evalFull : List Γ → Option (σ × List π) :=
  fun w => (P.evalFrom (some (P.start, [])) w)

def eval : List Γ → Option σ :=
  fun w => (P.evalFrom (some (P.start, [])) w).map Prod.fst

def acceptsFrom ( s: σ ) (st : List π ) : Language Γ :=
  { w | ∃ f, (P.evalFrom (some (s, st)) w).map Prod.fst = some f ∧ f ∈ P.accept }

def accepts : Language Γ := P.acceptsFrom P.start []

-- strings that are not rejected early
def intermediate : Language Γ :=
  { w | P.eval w ≠ none }

def pruned : Prop :=
  -- for all states that are reachable,
  -- can we eventually reach an accepting state?
  ∀ s st, (∃ w, P.evalFull w = some (s, st)) → (∃ v, v ∈ P.acceptsFrom s st)

-- removes all stack operations
def toFSA : FSA Γ σ :=
  FSA.mk P.alph P.states P.start
    (fun st a => match P.step st a with
      | some (_, _, dst) => some dst
      | none => none)
    P.accept

-- refactor this lemma so that it matches
-- evalFrom instead of stepList
lemma fullStep_evalFrom [DecidableEq σ] :
  ∀ s st t,
    match P.fullStep (some (s, st)) t with
    | some (s', _) => P.toFSA.step s t = some s'
    | none => True
  := by
  intro s st t
  split
  case h_2 heq => constructor
  simp [PDA.toFSA, FSA.evalFrom]
  rename_i heq
  simp [PDA.fullStep] at heq
  split
  case h_1.h_1 heq' =>
    simp [heq'] at heq
    split at heq <;> try contradiction
    simp_all
  case h_1.h_2 heq' =>
    simp [heq'] at heq


lemma overApproximationLemma [DecidableEq σ] :
  ∀ w dst' s st,
    P.evalFrom (some (s, st)) w = some dst' →
    P.toFSA.evalFrom s w = some dst'.fst := by
  intro w dst' s st h
  induction w generalizing dst' s st
  case nil =>
    simp [toFSA, FSA.evalFrom]
    simp [evalFrom] at h
    simp [←h]
  case cons head tail ih =>
    simp only [PDA.evalFrom_cons] at h

    generalize h1 : P.fullStep (some (s, st)) head = trans at h
    cases trans with
    | none =>
      simp at h
    | some next =>
      have ih' := ih _ _ _ h
      simp_all [FSA.evalFrom]
      generalize h2p : P.toFSA.step s head = u at *
      have := P.fullStep_evalFrom s st head
      simp_all


theorem overApproximation [DecidableEq σ] :
  ∀ w s st, w ∉ P.toFSA.acceptsFrom s → w ∉ P.acceptsFrom s st := by
  intro w s st
  contrapose
  simp
  intro wap
  simp[acceptsFrom] at wap
  obtain ⟨dst, ⟨⟨stk_f, h_eval⟩, h_accept⟩⟩ := wap
  simp [FSA.acceptsFrom]
  exists dst
  constructor
  have := P.overApproximationLemma w (dst, stk_f) s st h_eval
  simp [this]
  have : P.toFSA.accept = P.accept := by rfl
  simp[this, h_accept]


lemma stackInvariance_lem [ LawfulBEq π ] : ∀ w s st st',
  st <+: st' →
    match P.evalFrom (some (s, st)) w with
    | some (sf, stf) =>
        P.evalFrom (some (s, st')) w = some (sf, stf ++ st'.drop st.length)
    | none => True := by
  intro w s st st'
  intro pfx
  induction w generalizing s st st'
  case nil =>
    split
    case h_1 heq =>
      simp[evalFrom] at heq
      simp[heq.left, ←heq.right]
      exact Eq.symm (List.prefix_iff_eq_append.mp pfx)
    case h_2 heq => contradiction
  case cons h t ih =>
    have fs_si := P.fullStep_stackInvariance s st st' h pfx
    split
    -- we were able to tranisition properly using st
    -- so must be able to tranisition using the larger st'
    case h_1 heq =>
      simp at heq
      simp
      generalize h2 : P.fullStep (some (s, st)) h = step at *
      cases step
      case some step' =>
        simp_all
        have step_pfx : step'.2 <+: (step'.2 ++ List.drop st.length st') := by
          simp_all
        have ih' := ih step'.1 step'.2 (step'.2 ++ List.drop st.length st') step_pfx
        simp[heq] at ih'
        exact ih'
      case none =>
        -- impossible
        simp at heq
    -- we couldn't transition properly using st
    -- but we can't say anything about using the larger st'
    case h_2 heq =>
      simp

theorem stackInvariance [ LawfulBEq π ] : ∀ w s st st',
  st <+: st' → w ∈ P.acceptsFrom s st → w ∈ P.acceptsFrom s st'  := by
  intro w s st st'
  intro pfx
  intro wap
  simp[acceptsFrom] at wap
  obtain ⟨dst, ⟨⟨stk_f, h_eval⟩, h_accept⟩⟩ := wap
  have := P.stackInvariance_lem w s st st' pfx
  simp[h_eval] at this
  simp[acceptsFrom]
  constructor
  case w => exact dst
  constructor
  constructor
  repeat assumption

theorem acceptEmptyStk_acceptAll [ LawfulBEq π ] : ∀ w s st,
  w ∈ P.acceptsFrom s [] → w ∈ P.acceptsFrom s st := by
  intro w s st
  apply stackInvariance
  simp


lemma evalFull_append :
  ∀ w x, P.evalFull (w ++ x) = P.evalFrom (P.evalFull w) x := by
  intro w x
  simp[evalFull, evalFrom]

theorem pruned_intermediate_eq_prefix ( h : P.pruned ) :
  P.intermediate = P.accepts.prefixes := by
  simp[pruned, evalFull] at h
  apply Set.ext
  intro x
  apply Iff.intro
  case mp =>
    intro h_x
    simp[intermediate] at h_x
    cases h' : P.evalFrom (some (P.start, [])) x with
    | some sp'  =>
      have (s', st') := sp'
      have ⟨fin, hfin⟩ := h s' st' x h'
      simp[acceptsFrom] at hfin
      obtain ⟨s'', ⟨⟨st'', h2⟩, s''_acc⟩⟩ := hfin
      -- so then x ++ fin is in accepts
      have := P.evalFull_append x fin
      simp[evalFull, h', h2] at this
      have acc : (x ++ fin) ∈ P.accepts := by
        simp_all[accepts, acceptsFrom]
        exists s''
        apply And.intro
        exists st''
        exact s''_acc
      have pfx : x <+: (x ++ fin) := by simp
      simp[Language.prefixes]
      exists (x ++ fin)
    | none =>
      simp[eval] at h_x
      contradiction
  case mpr =>
    intro h_x
    simp[Language.prefixes] at h_x
    simp[intermediate, eval]
    cases h' : P.evalFrom (some (P.start, [])) x with
    | some x =>
      simp
    | none =>
      obtain ⟨fin, ⟨fin_acc, x_pfx_fin⟩⟩ := h_x
      simp[accepts, acceptsFrom] at fin_acc
      obtain ⟨s'', ⟨⟨st'', h2⟩, s''_acc⟩⟩ := fin_acc
      obtain ⟨tail, htail⟩ := x_pfx_fin
      have := P.evalFull_append x tail
      simp[evalFull, h', htail] at this
      rw[this] at h2
      contradiction

end PDA
