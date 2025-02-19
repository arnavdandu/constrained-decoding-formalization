import Lake
open Lake DSL

package "constrained-decoding-formalization" where
  version := v!"0.1.0"

lean_lib «ConstrainedDecodingFormalization» where
  -- add library configuration options here

@[default_target]
lean_exe "constrained-decoding-formalization" where
  root := `Main
