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

lemma reject_none {x : List α} (h : (A.eval x).isNone) : x ∉ A.accepts := by
  simp only [Option.isNone_iff_eq_none] at h
  by_contra h'
  simp only [accepts, acceptsFrom] at h'
  obtain ⟨f, hf₁, hf₂⟩ := h'
  unfold eval at h
  rw [h] at hf₁
  exact Option.not_mem_none f hf₁

theorem mem_accepts {x : List α} (h : (A.eval x).isSome) : x ∈ A.accepts ↔ (A.eval x).get h ∈ A.accept := by
  constructor
  ·
    intro h'
    obtain ⟨f, hf₁, hf₂⟩ := h'
    have : (A.eval x).get h = f := by
      exact Option.get_of_mem h hf₁
    rwa [this]
  ·
    intro ha
    exists (A.eval x).get h
    constructor
    · simp [eval, Option.coe_get]
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

@[simp]
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

@[simp]
theorem toDFA_eval_correct : ∀ (l : List α), A.toDFA.eval l = A.eval l := by
  refine fun l => ?_
  simp [eval, DFA.eval]
  have : A.toDFA.start = some (A.start) := by exact rfl
  simp_all only [toDFA_evalFrom_correct]

theorem toDFA_correct : A.toDFA.accepts = A.accepts := by
  ext x
  simp only [DFA.mem_accepts, mem_accepts]
  cases h : A.eval x
  .
    have : A.toDFA.eval x = none := by simp_all only [toDFA_eval_correct]
    simp_all [acceptsFrom, h, eval, accepts]
    refine (iff_false_right ?_).mpr (by apply toDFA_none_not_accept)
    have : ¬(∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept) := by
      simp_all only [reduceCtorEq, false_and, exists_false, not_false_eq_true]
    exact fun a => this a
  .
    have : (A.eval x).isSome := by simp [h]
    rw [Option.isSome_iff_exists] at this
    obtain ⟨a, h'⟩ := this
    have : A.toDFA.eval x = a := by
      simp_all only [Option.some.injEq, toDFA_eval_correct]
    simp_all only [Option.some.injEq, DFA.eval, toDFA_iff_accept]
    constructor <;> rw [←h] at * <;> intro m
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by
        constructor <;> simp_all only [eval, Option.some.injEq]
        apply And.intro
        · exact rfl
        · simp_all only [toDFA, List.coe_toFinset, List.mem_map]
      exact this
    .
      have : ∃ f, A.evalFrom A.start x = some f ∧ f ∈ A.accept := by exact m
      obtain ⟨f, h1, h2⟩ := this
      simp_all only [eval, Option.some.injEq]

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

def transitions (fsa : FSA α σ) : List (σ × α × σ) :=
  fsa.states.flatMap (fun q =>
    fsa.alph.flatMap (fun c =>
        match fsa.step q c with
        | none => []
        | some ts => [(q, c, ts)]
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
  alph: List α
  states : List σ
  start : σ
  step : σ → α → Option (σ × List Γ)
  accept : List σ

namespace FST

variable
  (M : FST α Γ σ)

/-- `M.evalFrom` evaluates the list of characters `l` starting at `s`, and returns the final state
  along with the contents of the output tape if all transitions are valid.
  If a transition doesn't exist at any character of `l`, return `(none, [])`.  -/
def evalFrom (s : σ) (l : List α) : Option (σ × List Γ) :=
  match l with
  | [] => some (s, [])
  | a :: as =>
    match (M.step s a) with
    | none => none
    | some (s', S) =>
      match evalFrom s' as with
      | none => none
      | some (s'', T) => (s'', S ++ T)

def eval (input : List α) : Option (σ × List Γ) :=
  M.evalFrom M.start input

@[simp]
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = some (s, []) := rfl

private lemma evalFrom_cons_fst (s : σ) (x : α) (xs : List α)
  (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s (x :: xs) = some r) (h₂ : M.evalFrom s' xs = some t) :
    r.1 = t.1 := by
  simp_all only [evalFrom, Option.some.injEq]
  subst h₁
  simp_all only

private lemma evalFrom_cons_snd (s : σ) (x : α) (xs : List α)
  (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s (x :: xs) = some r) (h₂ : M.evalFrom s' xs = some t) :
    r.2 = S ++ t.2 := by
  simp_all only [evalFrom, Option.some.injEq]
  subst h₁
  simp_all only

theorem evalFrom_singleton (s : σ) (a : α) (h : M.step s a = some (s', S)) :
    M.evalFrom s [a] = M.step s a := by
  simp_all [evalFrom]

@[simp]
theorem evalFrom_cons (s : σ) (x : α) (xs : List α)
  (h₀ : M.step s x = some (s', S)) (h₁ : M.evalFrom s (x :: xs) = some r) (h₂ : M.evalFrom s' xs = some t) :
    (M.evalFrom s (x :: xs)) = (t.1, S ++ t.2) := by
  simp_all only [evalFrom]

theorem evalFrom_append (s : σ) (xs ys : List α) : M.evalFrom s (xs ++ ys) =
  match M.evalFrom s xs with
  | none => none
  | some t => (M.evalFrom t.1 ys).map (fun (s', ts) => (s', t.2 ++ ts)) := by
  induction xs generalizing s
  case nil => simp [evalFrom]
  case cons head tail ih =>
    cases h : M.step s head with
    | none => simp [evalFrom, h]
    | some sp =>
      simp[evalFrom, h, ih]
      cases h' : M.evalFrom sp.1 tail with
      | none => simp [h']
      | some sp2 =>
        simp [h']
        cases h2 : M.evalFrom sp2.1 ys <;> simp [h2]

def acceptsFrom (s : σ) : Language α :=
  { w | ∃ f ∈ M.evalFrom s w, f.1 ∈ M.accept }

def accepts : Language α := M.acceptsFrom M.start

def transducesTo (w : List α) (v : List Γ) : Prop :=
  if h : ((M.eval w).isSome) then
    ((M.eval w).get h).2 = v ∧ ((M.eval w).get h).1 ∈ M.accept
  else
    False

lemma reject_none {x : List α} (h : (M.eval x).isNone) : x ∉ M.accepts := by
  simp only [Option.isNone_iff_eq_none] at h
  by_contra h'
  simp only [accepts, acceptsFrom] at h'
  obtain ⟨f, hf₁, hf₂⟩ := h'
  unfold eval at h
  rw [h] at hf₁
  exact Option.not_mem_none f hf₁

theorem mem_accepts {x : List α} (h : (M.eval x).isSome) : x ∈ M.accepts ↔ ((M.eval x).get h).1 ∈ M.accept := by
  constructor
  ·
    intro h'
    obtain ⟨f, hf₁, hf₂⟩ := h'
    have : (M.eval x).get h = f := by
      exact Option.get_of_mem h hf₁
    rwa [this]
  ·
    intro ha
    exists (M.eval x).get h
    constructor
    · simp [eval, Option.coe_get]
    · exact ha

def producible (q : σ) : Language Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = t) }

def singleProducible (q : σ) : Set Γ :=
    { t | ∃ w, (∃ r ∈ M.evalFrom q w, r.2 = [t]) }

universe u_1 u_2


def compose_fun_step { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (x : α) : Option ((σ × τ) × List β) :=
  match M₁.step s₁ x with
  | none => none
  | some (s₁', S) =>
    match (M₂.evalFrom s₂ S) with
    | none => none
    | some (s₂', T) => ((s₁', s₂'), T)

/-- The composition of two FSTs `M₁`, `M₂` with `M₁.oalph = M₂.alph` gives a new FST `M'`, where
  `M'.alph = M₁.alph`, `M'.oalph = M₂.oalph` and `M'.eval w = M₂.eval (M₁.eval w)` -/
def compose {β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) : FST α β (σ × τ) :=
  let start : σ × τ := (M₁.start, M₂.start)
  let states := M₁.states.flatMap (fun s₁ =>
    M₂.states.map (fun s₂ =>
      (s₁, s₂)
    )
  )
  let accept := M₁.accept.flatMap (fun s₁ =>
    M₂.accept.map (fun s₂ =>
      (s₁, s₂)
    )
  )
  let step : (σ × τ) → α → Option ((σ × τ) × List β) := fun s a =>
    match s, a with
    | (s₁, s₂), a => compose_fun_step M₁ M₂ s₁ s₂ a

  ⟨M₁.alph, states, start, step, accept⟩

def compose_fun_evalFrom { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : List α) : Option ((σ × τ) × List β) :=
  match M₁.evalFrom s₁ w with
  | none => none
  | some (s₁', S) =>
    match (M₂.evalFrom s₂ S) with
    | none => none
    | some (s₂', T) => ((s₁', s₂'), T)

-- todo make this less casework, very bad right now
lemma compose_fun_step_cons { β : Type u_1 } { τ : Type u_2 }
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (s₁ : σ) (s₂ : τ) (w : α) (ws : List α) :
    compose_fun_evalFrom M₁ M₂ s₁ s₂ (w :: ws) =
      match compose_fun_step M₁ M₂ s₁ s₂ w with
      | none => none
      | some ((s₁', s₂'), T) =>
        (compose_fun_evalFrom M₁ M₂ s₁' s₂' ws).map (fun ((s₁'', s₂''), T') => ((s₁'', s₂''), T ++ T'))
  := by
  simp[compose_fun_evalFrom, compose_fun_step]
  simp[evalFrom]
  cases h₁ : M₁.step s₁ w with
  | none =>
    simp[evalFrom, h₁]
  | some sp =>
    simp
    cases h₃ : M₂.evalFrom s₂ sp.2 with
    | none =>
      split <;> simp_all[h₃]
      rename_i T' h_eq
      split at h_eq <;> simp_all
      rename_i T'' _
      have := M₂.evalFrom_append s₂ sp.2 T''
      simp_all
    | some sp2 =>
      split <;> simp_all[h₃]
      next h_eq =>
        split at h_eq <;> simp_all
      next h_eq =>
        split at h_eq <;> simp_all
        rename_i T'' _
        have := M₂.evalFrom_append s₂ sp.2 T''
        simp_all
        split <;> simp_all
        rename_i heq'
        cases h₄ : M₂.evalFrom sp2.1 T'' with
        | none => simp_all[h₄]
        | some dst =>
          simp_all[h₄]
          obtain ⟨a, ⟨b, hab⟩⟩ := heq'
          simp_all

def compose_fun_eval {β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) : Option (List β) :=
  (compose_fun_evalFrom M₁ M₂ M₁.start M₂.start w).map Prod.snd

def compose_correct { β : Type u_1 } { τ : Type u_2 } (M₁ : FST α Γ σ) (M₂ : FST Γ β τ) (w : List α) :
  ((M₁.compose M₂).eval w).map Prod.snd = compose_fun_eval M₁ M₂ w := by
  simp[eval, compose_fun_eval]
  have lem :
    ∀ { s₁ s₂ },
      (M₁.compose M₂).evalFrom (s₁, s₂) w = compose_fun_evalFrom M₁ M₂ s₁ s₂ w  := by
    intro s₁ s₂
    induction w generalizing s₁ s₂
    simp_all[compose_fun_evalFrom]
    case cons head tail ih =>
      have := compose_fun_step_cons M₁ M₂ s₁ s₂ head tail
      simp[←ih] at this
      rw[this]
      simp[evalFrom]
      conv =>
        pattern M₁.compose M₂
        simp[compose]
      simp
      split <;> simp_all
      simp[Option.map]
      split <;> simp_all
  exact congrArg (Option.map Prod.snd) lem


def mkStep [DecidableEq α] [DecidableEq σ] (transitions : List (σ × α × σ × List Γ)) : σ → α → Option (σ × List Γ) :=
  fun s a =>
    transitions.find? (fun (s', a', _, _) => s = s' && a = a')
    |>.map (fun (_, _, ts, word) => (ts, word))
    |>.getD (default)

variable {β τ}
  (M₁ : FST α Γ σ) (M₂ : FST Γ β τ)


variable (A : FSA α σ)


end FST

instance [DecidableEq σ] : Coe (FSA α σ) (NFA α σ) := ⟨fun fsa => fsa.toNFA⟩

instance [DecidableEq σ] : Coe (FSA α σ) (DFA α (Option σ)) := ⟨fun fsa => fsa.toDFA⟩
