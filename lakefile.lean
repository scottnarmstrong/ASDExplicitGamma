import Lake

open Lake DSL

package ASDExplicitGamma

require superdiffusion_formalization from git
  "https://github.com/scottnarmstrong/Superdiffusion.git" @ "880be9a90376a8fcf233b71d2716d55be46e9b5f"

@[default_target]
lean_lib ASDExplicitGamma where
  globs := #[.andSubmodules `ASDExplicitGamma]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- The axiom report of the main theorems. Not a default target: build it with
`lake build ASDExplicitGammaAudit`. -/
lean_lib ASDExplicitGammaAudit where
  globs := #[.submodules `ASDExplicitGammaAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
