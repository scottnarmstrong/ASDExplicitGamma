module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B86 : ModeBlockData :=
  ⟨⟨210, 221, (19305408985558607597/2000000000000000000000 : ℚ), (157878970687566117/1250000000000000000000 : ℚ)⟩, [
    (210, modeDataJ4M211),
    (211, modeDataJ4M212),
    (212, modeDataJ4M213),
    (213, modeDataJ4M214),
    (214, modeDataJ4M215),
    (215, modeDataJ4M216),
    (216, modeDataJ4M217),
    (217, modeDataJ4M218),
    (218, modeDataJ4M219),
    (219, modeDataJ4M220),
    (220, modeDataJ4M221)], (48263522463896518987/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b86 : entryChecks 4 bflatBlockJ4B86.entries = true := by
  simp only [entryChecks,bflatBlockJ4B86,List.all_cons,List.all_nil,
    mode_checked_j4_m211,
    mode_checked_j4_m212,
    mode_checked_j4_m213,
    mode_checked_j4_m214,
    mode_checked_j4_m215,
    mode_checked_j4_m216,
    mode_checked_j4_m217,
    mode_checked_j4_m218,
    mode_checked_j4_m219,
    mode_checked_j4_m220,
    mode_checked_j4_m221,Bool.and_self]
theorem block_mass_checked_j4_b86 : blockMassCheck bflatBlockJ4B86 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
