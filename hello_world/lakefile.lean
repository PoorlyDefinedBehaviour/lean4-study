import Lake
open Lake DSL

package «hello_world» where
  -- add package configuration options here

lean_lib «HelloWorld» where
  -- add library configuration options here

@[default_target]
lean_exe «hello_world» where
  root := `Main
