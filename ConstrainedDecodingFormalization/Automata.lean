import Mathlib.Computability.NFA
import Mathlib.Computability.EpsilonNFA
import Mathlib.Computability.DFA
import Mathlib.Computability.RegularExpressions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.PFun

universe u v w y

variable
  {α : Type u} {Γ : Type v} {σ : Type w}



structure FSA (α σ) where
  alph : List α
  states : List σ
  start : σ
  step : σ → α → Option σ
  accept : List σ

namespace FSA

variable (A : FSA α σ)

def evalFrom (s : σ) (l : List α) : Option σ :=
  match s, l with
  | s, [] => s
  | s, a :: as =>
    match (A.step s a) with
    | none => none
    | some s' => evalFrom s' as


@[simp]
theorem evalFrom_nil (s : σ) : A.evalFrom s [] = s := rfl

theorem evalFrom_cons (s : σ) (x : α) (xs : List α) (h : (A.step s x).isSome) :
    A.evalFrom s (x :: xs) = A.evalFrom ((A.step s x).get h) (xs) := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨a, h_s⟩ := h
  simp_all only [evalFrom, Option.get_some]

theorem evalFrom_none (s : σ) (l : List α) :
    A.evalFrom s l = none → ∃ (s' : σ) (a : α), A.step s' a = none := by
  contrapose!
  intro h
  induction l generalizing s
  case nil =>
    exact Option.isSome_iff_ne_none.mp rfl
  case cons ih =>
    expose_names
    rw [evalFrom_cons]
    refine ih ((A.step s head).get ?_)
    exact Option.isSome_iff_ne_none.mpr (h s head)

theorem evalFrom_some (s : σ) (l : List α) :
    (∀ (s' : σ) (a : α), A.step s' a ≠ none) → (A.evalFrom s l).isSome := by
  contrapose!
  simp [evalFrom_none]
  apply evalFrom_none

def eval : List α → Option σ :=
  A.evalFrom A.start

def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f ∈ A.evalFrom s w, f ∈ A.accept }

def accepts : Language α := A.acceptsFrom A.start



def prefixLanguage : Language α :=
  {x | ∃ y ∈ A.accepts, x ++ y ∈ A.accepts }

def isPrefix (w : List α) : Prop := w ∈ A.prefixLanguage

theorem mem_accepts {x : List α} (h : (A.eval x).isSome) : x ∈ A.accepts ↔ (A.eval x).get h ∈ A.accept := by
  constructor
  ·
    intro h'
    unfold accepts acceptsFrom at h'
    simp at h'
    obtain ⟨f, hf₁, hf₂⟩ := h'
    have : (A.eval x).get h = f := by
      unfold eval at *
      rw [Option.get_of_mem h hf₁]
    rwa [this]
  ·
    intro ha
    unfold accepts acceptsFrom
    simp
    exists (A.eval x).get h
    constructor
    · unfold eval
      rw [@Option.coe_get]
    · exact ha


variable [DecidableEq σ]

instance (l : List α) : Decidable ( (A.eval l).isSome ) := inferInstance

instance [BEq σ] [LawfulBEq σ] (l : List α) {h : (A.eval l).isSome} :
  Decidable ((A.eval l).get h ∈ A.accept) :=
  List.instDecidableMemOfLawfulBEq ((A.eval l).get h) A.accept

instance [BEq σ] [LawfulBEq σ] (l : List α) : Decidable (l ∈ A.accepts) :=
  if h : (A.eval l).isSome then
    let s := (A.eval l).get h
    if h2 : s ∈ A.accept then
      isTrue ((mem_accepts A h).mpr h2)
    else
      isFalse ((mem_accepts A h).not.mpr h2)
  else
    isFalse (by
      intro h_contra
      simp [accepts, acceptsFrom, eval] at h_contra
      cases h_contra with
      | intro f hf =>
        have : (A.eval l).isSome := Option.isSome_iff_exists.mpr ⟨f, hf.1⟩
        contradiction
    )


--instance [BEq σ] [LawfulBEq σ] (l : List α) : Decidable (l ∈ A.prefixLanguage) :=
  --sorry

def toDFA : DFA α (Option σ) :=
  let step : Option σ → α → Option σ := fun s a =>
    match s, a with
    | none, _ => none
    | some x, a =>
      match (A.step x a) with
      | none => none
      | some s' => s'

  let accept := A.accept.map (fun s => some s)

  ⟨step, A.start, accept.toFinset.toSet⟩

lemma toDFA_none_not_accept : none ∉ A.toDFA.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_iff_accept : some a ∈ A.toDFA.accept ↔ a ∈ A.accept := by
  simp_all [toDFA]

@[simp]
lemma toDFA_none_is_fail : ∀ (a : α), A.toDFA.step none a = none := by
  exact fun a => rfl

lemma toDFA_step_correct : ∀ (s : σ) (a : α), A.toDFA.step (some s) a = A.step s a := by
  refine fun s a => ?_
  simp [toDFA]
  split <;> rename_i heq <;> exact id (Eq.symm heq)

lemma toDFA_evalFrom_step_cons (s : σ) (x : α) (xs : List α) :
    A.toDFA.evalFrom (some s) (x :: xs) = A.toDFA.evalFrom (A.toDFA.step s x) (xs) := by
  simp [DFA.evalFrom]


theorem toDFA_evalFrom_correct : ∀ (s : σ) (l : List α), A.toDFA.evalFrom (some s) l = A.evalFrom s l := by
  refine fun s l => ?_
  simp [DFA.evalFrom]
  induction l generalizing s
  case nil =>
    unfold List.foldl
    simp
  case cons ih =>
    simp [List.foldl]
    expose_names
    cases h : A.step s head
    ·
      simp [evalFrom, h, toDFA_step_correct]
      exact List.foldl_fixed' (congrFun rfl) tail
    ·
      simp [evalFrom, h, toDFA_step_correct]
      apply ih


theorem toDFA_correct : A.toDFA.accepts = A.accepts := by
  ext x
  simp only [DFA.mem_accepts, mem_accepts]
  have h₀ : A.toDFA.start = some (A.start) := by simp [toDFA]
  cases h : A.eval x
  .
    have : A.toDFA.eval x = none := by simp_all [eval, DFA.eval, h₀, toDFA_evalFrom_correct, h]
    simp_all [acceptsFrom, h, eval, accepts]
    refine (iff_false_right ?_).mpr (by apply toDFA_none_not_accept)
    have : ¬(∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept) := by
      push_neg
      refine fun f => ?_
      simp [h]
    exact fun a => this a
  .
    have : (A.eval x).isSome := by simp [h]
    rw [Option.isSome_iff_exists] at this
    obtain ⟨a, h'⟩ := this
    have : A.toDFA.eval x = a := by
      have : A.toDFA.evalFrom (some A.start) x = A.evalFrom A.start x :=
        by apply toDFA_evalFrom_correct
      simp_all only [h, DFA.eval, Option.some.injEq, eval, this, h']
    simp_all [this, accept, DFA.eval]
    constructor <;> rw [←h] at * <;> intro m
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by
        constructor <;> simp_all only [eval, Option.some.injEq]
        apply And.intro
        · exact rfl
        · simp_all [m, toDFA]
      exact this
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by apply m
      obtain ⟨f, h1, h2⟩ := this
      simp_all only [Option.some.injEq, eval, this, h2]

variable
  [DecidableEq α]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ] [Fintype σ]

instance : DecidableEq (FSA α σ) := fun M N =>
  let toProd (fsa : FSA α σ) := (fsa.alph, fsa.states, fsa.start, fsa.step, fsa.accept)

  have h₁ : Decidable (toProd M = toProd N) := by
    simp_all only [Prod.mk.injEq, toProd]
    exact instDecidableAnd

  have h_inj : ∀ a b : FSA α σ, toProd a = toProd b → a = b := by
    intro a b h_eq
    cases a
    cases b
    simp [toProd] at h_eq
    simp [mk.injEq]
    simp_all [Prod.mk.injEq, and_self, toProd]

  if h : toProd M = toProd N then
    isTrue (by exact h_inj M N h)
  else
    isFalse (by intro hMN; apply h; simp [toProd, hMN])

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

/-- A word ` w ` is accepted at ` q ` if there is ` q' ` such that ` evalFrom q w = q' `-/
def accepted (s : σ) (w : List α) : Prop := A.evalFrom s w ≠ none



def toNFA : NFA α σ where
  step s a := (A.step s a).elim ∅ (fun s => {s})
  start := {A.start}
  accept := A.accept.toFinset

#check Singleton
#check Subsingleton





omit [DecidableEq α] [Inhabited α] [Fintype α] [Fintype σ]
@[simp]
lemma toNFA_step_Subsingleton (A : FSA α σ) (s : σ) (a : α) :
    Subsingleton (A.toNFA.step s a) := by
  simp [toNFA, Option.elim]
  split
  simp_all
  exact Set.subsingleton_empty

lemma toNFA_evalFrom_step_cons (s : σ) (x : α) (xs : List α) :
    A.toNFA.evalFrom {s} (x :: xs) = A.toNFA.evalFrom (A.toNFA.step s x) (xs) := by
  simp [NFA.evalFrom, NFA.stepSet]

lemma toNFA_evalFrom_step_cons_empty (x : α) (xs : List α) :
    A.toNFA.evalFrom ∅ (x :: xs) = A.toNFA.evalFrom ∅ (xs) := by
  simp [NFA.evalFrom, NFA.stepSet]

lemma toNFA_evalFrom_empty (x : List α) :
    A.toNFA.evalFrom ∅ x = ∅ := by
  simp [NFA.evalFrom]
  rw [List.foldl.eq_def]
  split; rfl
  expose_names
  induction l
  case nil =>
    rw [←NFA.evalFrom]
    simp [NFA.evalFrom_nil]
  case cons ih =>
    rw [←NFA.evalFrom] at *
    simp_all [NFA.evalFrom_nil, toNFA_evalFrom_step_cons_empty]

lemma toNFA_evalFrom_Subsingleton (A : FSA α σ) (s : σ) (l : List α) :
    Subsingleton (A.toNFA.evalFrom {s} l) := by
  have h : ∀ (S : Set σ), A.toNFA.evalFrom S [] = S := by exact (fun S => rfl)
  induction l generalizing s
  case nil =>
    rw [h {s}]
    exact Unique.instSubsingleton
  case cons a as ih =>
    simp_all only [NFA.evalFrom_nil, implies_true]
    rw [toNFA_evalFrom_step_cons]
    have h₁ : ∀ (c : α) (s : σ), A.toNFA.step s c = (A.step s c).elim ∅ (fun s => {s}) := by intro c; exact fun s => rfl
    rw [h₁]
    simp only [Option.elim]
    split
    dsimp
    apply ih _
    simp only [NFA.evalFrom, NFA.stepSet, NFA.stepSet_empty]
    rw [List.foldl.eq_def]
    split
    exact IsEmpty.instSubsingleton
    rw [←NFA.evalFrom]
    simp [NFA.stepSet_empty, toNFA_evalFrom_empty]





end FSA

structure FST (α Γ σ) where
  alph : List α
  oalph : List Γ
  states : List σ
  start : σ
  step : σ → α → (Option σ × List Γ)
  accept : List σ

namespace FST

variable
  (M : FST α Γ σ)
  [DecidableEq α] [DecidableEq σ]
  [Inhabited α] [Inhabited Γ]
  [Fintype α] [Fintype Γ] [Fintype σ]

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


instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => fsa.toNFA⟩

instance [DecidableEq σ] : Coe (FSA α σ) (DFA α (Option σ)) := ⟨fun fsa => fsa.toDFA⟩
