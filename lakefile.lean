import Lake
open Lake DSL

package "constrained-decoding-formalization" where
  version := v!"0.1.0"

lean_lib «ConstrainedDecodingFormalization» where
  -- add library configuration options here

require "leanprover-community" / "mathlib"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

  
