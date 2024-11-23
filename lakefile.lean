import Lake
open Lake DSL

package «order» where
  -- add package configuration options here

lean_lib «Order» where
  -- add library configuration options here

@[default_target]
lean_exe «order» where
  root := `Main
