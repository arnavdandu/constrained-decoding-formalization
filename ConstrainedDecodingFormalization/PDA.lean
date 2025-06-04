import ConstrainedDecodingFormalization.Automata
import ConstrainedDecodingFormalization.Language
import Mathlib.Computability.Language
import Mathlib.Data.Set.Basic
import Mathlib.Computability.ContextFreeGrammar

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

structure PDA (Γ : Type u) ( π : Type v) ( σ : Type w) where
  start : σ
  step : σ → Γ → Set (List π × List π × σ)
  accept : Set σ

-- inspired by Mathlib DFA
namespace PDA

variable { Γ π σ } [ BEq π ] ( P : PDA Γ π σ )

instance [Inhabited σ] [Inhabited π] : Inhabited (PDA Γ π σ) :=
  ⟨PDA.mk default (fun _ _=> ∅) default⟩

def fullStep (S : Set (σ × List π)) (t : Γ) : Set (σ × List π) :=
  ⋃ s_st ∈ S,
    let (s, st) := s_st
    ⋃ tr ∈ P.step s t,
      let (top, replace, dst) := tr
      match top.isPrefixOf? st with
      | some rem => {(dst, replace ++ rem)}
      | none => ∅

@[simp]
theorem fullStep_none ( t : Γ ) : P.fullStep ∅ t = ∅ :=
  by simp[fullStep]


private theorem fullStep_stackInvariance [ LawfulBEq π  ] : ∀ s st sn stn st' t, st <+: st' →
   (sn, stn) ∈ P.fullStep {(s, st)} t →
   (sn, stn ++ st'.drop st.length) ∈ P.fullStep {(s, st')} t
  := by
  intro s st sn stn st' t
  intro pfx
  simp_all[fullStep]
  intro top rep dst _
  split <;> simp_all
  rename_i rem heq
  intro hsn hdst
  exists top, rep, dst
  constructor
  assumption
  have partition := isPrefix_merge top st st' pfx
  have p := List.isPrefixOf?_eq_some_iff_append_eq.mpr heq
  simp[p] at partition
  have p2 := List.isPrefixOf?_eq_some_iff_append_eq.mpr partition
  simp[p2]


def evalFrom ( s: Set ( σ × List π ) ) : List Γ → Set (σ × List π) :=
  List.foldl ( fun s a => fullStep P s a) s

@[simp]
theorem evalFrom_nil (s : σ) (st : List π) : P.evalFrom {(s, st)} [] = {(s, st)} :=
  rfl

@[simp]
theorem evalFrom_cons (S : Set (σ × List π)) (head: Γ) (tail : List Γ) : P.evalFrom S (head :: tail) = P.evalFrom (P.fullStep S head) tail := by
  simp[evalFrom]

@[simp]
theorem evalFrom_none  ( w : List Γ ) : P.evalFrom {} w = {} := by
  induction w
  rfl
  rename_i h t ih
  have : P.evalFrom {} (h :: t) = P.evalFrom (P.fullStep {} h) t := by rfl
  simp[this, fullStep_none, ih]

@[simp]
theorem fullStep_subset (u: Set (σ × List π)) (v: Set (σ × List π)) (h: u ⊆ v) ( w : Γ )
  : P.fullStep u w ⊆ P.fullStep v w := by
  simp only[fullStep]
  exact Set.biUnion_mono h fun x a ⦃a⦄ a => a

@[simp]
theorem evalFrom_subset (u: Set (σ × List π)) (v: Set (σ × List π)) (h: u ⊆ v) ( w : List Γ )
  : P.evalFrom u w ⊆ P.evalFrom v w := by
  induction w generalizing u v
  case nil =>
    exact h
  case cons head tail ih =>
    have := P.fullStep_subset u v h head
    simp[this, ih]

def evalFull : List Γ → Set (σ × List π) :=
  fun w => (P.evalFrom {(P.start, [])} w)

def eval : List Γ → Set σ :=
  fun w => Prod.fst '' (P.evalFrom {(P.start, [])} w)

def acceptsFrom ( s: σ ) (st : List π ) : Language Γ :=
  { w | ∃ f, f ∈ Prod.fst '' (P.evalFrom {(s, st)} w) ∧ f ∈ P.accept }

def accepts : Language Γ := P.acceptsFrom P.start []

-- strings that are not rejected early
def intermediate : Language Γ :=
  { w | P.eval w ≠ ∅ }

def pruned : Prop :=
  -- for all states that are reachable,
  -- can we eventually reach an accepting state?
  ∀ s st, (∃ w, (s, st) ∈ P.evalFull w) → (∃ v, v ∈ P.acceptsFrom s st)

-- removes all stack operations
def toNFA : NFA Γ σ :=
  NFA.mk
    (fun st a => (fun q => q.2.2) '' P.step st a)
    {P.start}
    P.accept

lemma evalFrom_iff_exists :
  ∀ S s w, s ∈ P.evalFrom S w ↔ ∃ u, u ∈ S ∧ s ∈ P.evalFrom {u} w :=
  by
  have triv_dir : ∀ S s w, (∃ u, u ∈ S ∧ s ∈ P.evalFrom {u} w) → s ∈ P.evalFrom S w := by
    intro S s w h_p
    obtain ⟨u, h_u⟩ := h_p
    have : {u} ⊆ S := by simp[h_u.left]
    apply evalFrom_subset
    assumption
    exact h_u.right
  intro S s w
  apply Iff.intro
  case mpr =>
    exact triv_dir S s w
  case mp =>
  simp[evalFrom]
  induction w generalizing S s
  case nil =>
    simp
    intro h_u
    exists s.fst, s.snd
  case cons head tail ih =>
    intro hp
    have ih' := ih (P.fullStep S head) s hp
    have ⟨s', st', hs, hf⟩ := ih'
    simp[fullStep] at hs
    obtain ⟨s0, st0, h⟩ := hs
    exists s0, st0
    constructor
    exact h.left
    obtain ⟨top, replace, dst, htrans⟩ := h.right
    simp
    suffices (s', st') ∈ P.fullStep {(s0, st0)} head by
      have ss : P.evalFrom {(s', st')} tail ⊆ P.evalFrom {(s0, st0)} (head :: tail) := by
        simp[evalFrom]
        apply evalFrom_subset
        simp[this]
      have s_mem : s ∈ P.evalFrom {(s', st')} tail := by
        simp[evalFrom]
        exact hf
      have := ss s_mem
      simp[evalFrom] at this
      exact this
    simp[fullStep]
    exact h.right


lemma fullStep_evalFrom [DecidableEq σ] :
  ∀ S s' st' t,
    (s', st') ∈ P.fullStep S t →
      s' ∈ (P.toNFA.stepSet (Prod.fst '' S) t)
  := by
  intro S s' st' t
  simp [PDA.toNFA, NFA.stepSet]
  intro hmem
  simp [PDA.fullStep] at hmem
  obtain ⟨s, st, hmem'⟩ := hmem
  obtain ⟨top, replace, dst, h⟩ := hmem'.right
  have s_next := h.right
  split at s_next <;> simp_all
  exists s
  constructor
  exists st
  exact hmem'.left
  exists top
  exists replace

lemma overApproximationLemma [DecidableEq σ] :
  ∀ w S s' st',
    (s', st') ∈ P.evalFrom S w →
      s' ∈ P.toNFA.evalFrom (Prod.fst '' S) w
  := by
  intro w S s' st' h

  have subset_lem1 : ∀ u v head, u ⊆ v →
    P.toNFA.stepSet u head ⊆ P.toNFA.stepSet v head := by
      intro u v head uh
      simp[NFA.stepSet, uh]
      exact fun i i_1 => Set.subset_iUnion₂_of_subset i (uh i_1) fun ⦃a⦄ a => a

  have subset_lem : ∀ u v w, u ⊆ v →
    List.foldl P.toNFA.stepSet u w ⊆ List.foldl P.toNFA.stepSet  v w
    :=  by
      intro u v w uh
      induction w generalizing u v
      case nil =>
        exact uh
      case cons head tail ih =>
        have := subset_lem1 u v head uh
        simp[this, ih]

  induction w generalizing S s' st'
  case nil =>
    simp [toNFA, NFA.evalFrom]
    simp [evalFrom] at h
    exists st'
  case cons head tail ih =>
    simp only [PDA.evalFrom_cons] at h

    have ih' := ih _ _ _ h
    simp [NFA.evalFrom, List.foldl]
    let trans_pda := Prod.fst '' P.fullStep S head
    let trans_nfa := (P.toNFA.stepSet (Prod.fst '' S) head)
    have p_s_n : trans_pda ⊆ trans_nfa := by
      intro p h_p
      simp[trans_pda, fullStep] at h_p
      obtain ⟨st'', s0, st0, h0, top, replace, dst, h_s⟩ := h_p
      simp[trans_nfa, toNFA, NFA.stepSet]
      exists s0
      constructor
      exists st0
      exists top, replace
      have g := h_s.right
      split at g <;> simp_all
    have pda_sub := subset_lem trans_pda trans_nfa tail p_s_n
    suffices s' ∈ List.foldl P.toNFA.stepSet trans_pda tail by
      exact
        subset_lem trans_pda (P.toNFA.stepSet (Prod.fst '' S) head) tail p_s_n
          (ih (P.fullStep S head) s' st' h)
    exact ih'

theorem overApproximation [DecidableEq σ] :
  ∀ w, w ∉ P.toNFA.accepts → w ∉ P.accepts := by
  intro w
  contrapose
  simp
  intro wap
  simp[accepts, acceptsFrom] at wap
  obtain ⟨dst, ⟨⟨stk_f, h_eval⟩, h_accept⟩⟩ := wap
  simp [NFA.accepts]
  exists dst
  constructor
  have : P.toNFA.accept = P.accept := by rfl
  simp[this, h_accept]
  have dst_nfa := P.overApproximationLemma w {(P.start, [])} dst stk_f h_eval
  simp[Set.image] at dst_nfa
  simp[NFA.eval]
  exact dst_nfa

lemma stackInvariance_lem [ LawfulBEq π ] : ∀ s st sn stn st' w, st <+: st' →
   (sn, stn) ∈ P.evalFrom {(s, st)} w →
   (sn, stn ++ st'.drop st.length) ∈ P.evalFrom {(s, st')} w := by
  intro s st sn stn st' w
  intro pfx
  induction w generalizing s st st'
  case nil =>
    simp
    intro h h2
    constructor
    assumption
    rw[h2]
    exact List.prefix_iff_eq_append.mp pfx
  case cons h t ih =>
    intro h_p
    simp at h_p
    obtain ⟨step, hstep⟩ := (P.evalFrom_iff_exists (P.fullStep {(s, st)} h) _ t).mp h_p
    have step_pfx : step.2 <+: (step.2 ++ List.drop st.length st') := by simp_all
    have ih' := ih step.1 step.2 (step.2 ++ List.drop st.length st') step_pfx hstep.right
    have fs_si := P.fullStep_stackInvariance s st step.fst step.snd st' h pfx hstep.left
    simp at ih' ⊢
    apply evalFrom_subset
    case intro.u => exact {(step.1, step.2 ++ List.drop st.length st')}
    exact Set.singleton_subset_iff.mpr fs_si
    exact ih'

theorem stackInvariance [ LawfulBEq π ] : ∀ w s st st',
  st <+: st' → w ∈ P.acceptsFrom s st → w ∈ P.acceptsFrom s st'  := by
  intro w s st st'
  intro pfx
  intro wap
  simp[acceptsFrom] at wap
  obtain ⟨dst, ⟨⟨stk_f, h_eval⟩, h_accept⟩⟩ := wap
  have := P.stackInvariance_lem s st dst stk_f st' w pfx h_eval
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
    cases h' : P.evalFrom {(P.start, [])} x with
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
