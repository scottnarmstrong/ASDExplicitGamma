module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part011
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B84 : ModeBlockData :=
  ⟨⟨189, 199, (68558643834440466229/5000000000000000000000 : ℚ), (348096383789118411/2500000000000000000000 : ℚ)⟩, [
    (189, modeDataJ4M190),
    (190, modeDataJ4M191),
    (191, modeDataJ4M192),
    (192, modeDataJ4M193),
    (193, modeDataJ4M194),
    (194, modeDataJ4M195),
    (195, modeDataJ4M196),
    (196, modeDataJ4M197),
    (197, modeDataJ4M198),
    (198, modeDataJ4M199)], (4284915239652529139/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b84 : entryChecks 4 bflatBlockJ4B84.entries = true := by
  simp only [entryChecks,bflatBlockJ4B84,List.all_cons,List.all_nil,
    mode_checked_j4_m190,
    mode_checked_j4_m191,
    mode_checked_j4_m192,
    mode_checked_j4_m193,
    mode_checked_j4_m194,
    mode_checked_j4_m195,
    mode_checked_j4_m196,
    mode_checked_j4_m197,
    mode_checked_j4_m198,
    mode_checked_j4_m199,Bool.and_self]
theorem block_mass_checked_j4_b84 : blockMassCheck bflatBlockJ4B84 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
