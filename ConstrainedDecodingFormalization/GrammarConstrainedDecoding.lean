import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.RealizableSequence
-- Actual implementation of grammar constrained decoding

universe u v w z
variable { α : Type u } { Γ : Type u } { π : Type v } { σ : Type w } { σ0 : Type z }

variable [ BEq π ] [ DecidableEq σ ] [DecidableEq Γ ] [ DecidableEq α ]

abbrev PPTable (α σ σ0 Γ):= (σ → σ0 → (List (Token (Ch α)) × List (List Γ)))

def PreprocessParser (fst_comp : FSTComp α Γ σ0) (p : PDA Γ π σ) : PPTable α σ σ0 Γ := 
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp 
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom (some (qp, [])) s).isSome)
    let rejected := re.filter (λ s => s ∈ accepted ∧ (p.toFSA.evalFrom qp s) = [])
    let dependent := (re \ accepted) \ rejected
    fun qa => 
      let accepted_a := (re.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a)

def ComputeValidTokenMask (P : PDA Γ π σ) (itst : List Γ → σ0 → (List (Token (Ch α)))) (table : PPTable α σ σ0 Γ) (qa : σ0) (qp : σ) (st : List π) : List (Token (Ch α)) := Id.run do
  let mut accepted := (table qp qa).fst
  for d in (table qp qa).snd do
    if (P.evalFrom (some (qp, st)) d).isSome then 
      accepted := accepted ++ (itst d qa)

  accepted.dedup

-- if in compute valid token mask, parser would accept it
-- we want something a bit stronger than this, basically having to do with the
-- assumption about all terminal sequences being realizable
theorem accept_if_ComputedValidTokenMask (P : PDA Γ π σ) (fst_comp : FSTComp α Γ σ0) : 
  ∀ st qa qp v, 
    v ∈ (ComputeValidTokenMask P (BuildInverseTokenSpannerTable fst_comp).snd (PreprocessParser fst_comp P) qa qp st) →
    -- jointly evaluating, it is still accepted
    -- P.evalFrom qp st (all new symbols)
    True
  := by sorry

-- if compute valid token mask rejects it, 
-- the parser would reject it (now or in the future)
-- so it must mean there is no way to get to an accepting state 
theorem ComputedValidTokenMask_complete : 0 = 0 := by sorry

