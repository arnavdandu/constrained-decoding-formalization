import ConstrainedDecodingFormalization.PDA
import ConstrainedDecodingFormalization.Lexing
import ConstrainedDecodingFormalization.RealizableSequence
-- Actual implementation of grammar constrained decoding

universe u v w x y z
variable { α : Type u } { β : Type x } { Γ : Type y } { π : Type v } { σp : Type w } { σa : Type z }

variable [ BEq π ]
  [ FinEnum σp ] [ FinEnum Γ ] [ FinEnum α ] [ FinEnum σa ]
  [ DecidableEq σp ] [DecidableEq β] [DecidableEq Γ ] [ DecidableEq α ]

abbrev PPTable (α σp σa Γ) := (σp → σa → (List α × List (List Γ) × List (List Γ)))

def PreprocessParser (fst_comp : FST α Γ σa) (p : PDA Γ π σp) : PPTable α σp σa Γ :=
  let (re, tist) := BuildInverseTokenSpannerTable fst_comp
  fun qp =>
    let accepted := re.filter (λ s => (p.evalFrom (some (qp, [])) s).isSome)
    let rejected := re.filter (λ s => s ∈ accepted ∧ (p.toFSA.evalFrom qp s) = none)
    let dependent := (re \ accepted) \ rejected
    fun qa =>
      let accepted_a := (accepted.map (fun tok => (tist tok qa))).foldl List.append []
      let accepted_a := accepted_a.dedup
      let dependent_a := dependent.filter (fun tok => (tist tok qa) ≠ [])
      let dependent_a := dependent_a.dedup
      (accepted_a, dependent_a, accepted)

def ComputeValidTokenMask (P : PDA Γ π σp) (itst : List Γ → σa → List α) (table : PPTable α σp σa Γ) (qa : σa) (qp : σp) (st : List π) : List α := Id.run do
  let mut accepted := (table qp qa).fst
  for d in (table qp qa).2.1 do
    if (P.evalFrom (some (qp, st)) d).isSome then
      accepted := accepted ++ (itst d qa)

  accepted.dedup


-- TODO use more consistent notions of variable names
/- lexer spec is the automata in terms of the characters
   we also have the actual tokens
   and then the parser
-/
def GCDChecker
   [FinEnum (Ch β)] [FinEnum σp] [FinEnum σa] [FinEnum π] [FinEnum (Ch Γ)] [FinEnum α]
   (spec: LexerSpec α Γ σa) (tokens: List (Token (Ch α) (Ch β))) (parser: PDA (Ch Γ) π σp) : List β → Ch β → Bool :=
  let detok := Detokenizing.BuildDetokenizingFST tokens
  let fst := BuildLexingFST spec
  let comb := FST.compose detok fst

  let pp_table : PPTable (Ch β) σp (Unit × σa) (Ch Γ) := PreprocessParser comb parser
  let ⟨_, itst⟩ := BuildInverseTokenSpannerTable comb

  fun curr cand =>
    match comb.eval curr with
    | none => false
    | some (q_fst, terms) =>
      match parser.evalFrom (some (parser.start, [])) terms with
      | none => false
      | some (q_parse, st) =>
        let mask := ComputeValidTokenMask parser itst pp_table q_fst q_parse st
        mask.contains cand

-- we want to say that accepted if and only if
-- theres a realizable sequence that's accepted
-- theorem accept_if_ComputedValidTokenMask (P : PDA Γ π σ) (fst_comp : FSTComp α Γ σ0) :
--   ∀ st qa qp v,
--     v ∈ (ComputeValidTokenMask P (BuildInverseTokenSpannerTable fst_comp).snd (PreprocessParser fst_comp P) qa qp st) →
--     -- jointly evaluating, it is still accepted
--     -- P.evalFrom qp st (all new symbols)
--     True
--   := by sorry

-- if compute valid token mask rejects it,
-- the parser would reject it (now or in the future)
-- so it must mean there is no way to get to an accepting state
-- theorem ComputedValidTokenMask_complete : 0 = 0 := by sorry
