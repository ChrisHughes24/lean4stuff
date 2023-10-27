import Lake
open Lake DSL

package stuff {
  -- add package configuration options here
}

lean_lib Stuff {
  -- add library configuration options here
}

@[default_target]
lean_exe stuff {
  root := `Main
}

require «mathlib» from git  "https://github.com/leanprover-community/mathlib4" @ "02b5c76bd21cfdd03202290be0c950882abfdf34"
