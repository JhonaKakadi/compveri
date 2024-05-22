import Lake
open Lake DSL

package «relational_algebra» where
  -- add package configuration options here

lean_lib «RelationalAlgebra» where
  -- add library configuration options here

@[default_target]
lean_exe «relational_algebra» where
  root := `Main
