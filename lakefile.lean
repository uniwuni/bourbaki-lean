import Lake
open Lake DSL

package «lean-bourbaki» {
  -- add package configuration options here
  
}


@[default_target]
lean_lib «LeanBourbaki» 


meta if get_config? doc = some "yes" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"