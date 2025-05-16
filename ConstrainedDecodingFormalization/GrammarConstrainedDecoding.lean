import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.RealizableSequence
-- Actual implementation of grammar constrained decoding

universe u v w z
variable { α : Type u } { Γ : Type u } { π : Type v } { σ : Type w } { σ0 : Type z }

variable [ BEq π ] [ DecidableEq σ ] [DecidableEq Γ ] [ DecidableEq α ]

def PreprocessParser (fst_comp : FSTComp α Γ σ0) (p : PDA Γ π σ) : 
      (σ → σ0 → (List (Token (Ch α)) × List (List Γ))) := 
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


