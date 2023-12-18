import Lake
open Lake DSL

package «test3» {
  -- add package configuration options here
}

lean_lib «Test3» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @"23550c1e3b21f7f3312acb901cef261f51219f72"

@[default_target]
lean_exe «test3» {
  root := `Main
}
