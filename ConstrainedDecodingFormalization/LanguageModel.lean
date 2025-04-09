universe u v

-- States that β is a valid LLM token set over the base alphabet α
class Token ( α: Type u ) ( β: Type v ) where 
  flatten : β → List α
  embed: α → β 
  eos: β
  
  fe: ∀ a, flatten (embed a) = [a]
  empty: ∀ b, flatten b = [] ↔ b = eos

abbrev Constrainer ( α β ) [ Token α β ] := List α → β → Bool 

-- set of intermediate strings produced by a language model under a given constraint
inductive ConstrainedPrefixLanguage { α β } [ t: Token α β ] ( c: Constrainer α β ) : List α → Prop where 
 | empty : ConstrainedPrefixLanguage c [] 
 | build { v ts } ( h: ConstrainedPrefixLanguage c ts ) ( cv: c ts v = true ) : ConstrainedPrefixLanguage c (ts ++ (t.flatten v))

-- set of final strings produced by a language model under a given constraint
inductive ConstrainedLanguage { α β } [ t: Token α β ] ( c: Constrainer α β ) : List α → Prop where 
 | mk { ts } ( h: ConstrainedPrefixLanguage c ts ) ( e: c ts t.eos = true ) : ConstrainedLanguage c ts 


abbrev LanguageModel ( α β ) [ Token α β ] := List α → β


--  
partial def constrained_decoding ( ) := by sorry
  -- given 
  -- a constrained lexing automata (symbols )
  -- a context free grammar of the symbols 
  -- a language model 
  -- we construct our pipeline by building lexer and parser combination 
  -- analyze the given states to find inverse realizable terminal sequences
  -- do acceptance based off of that
  

-- main theorems (all require further refinement of lexer/parser)

-- 1. if recognized by the lexer and parser, then in the constrained language


-- 2. all prefixes are prefixes in the lexer/parser language

-- 3. if in the constrained language, then recognized by the lexer and parser


