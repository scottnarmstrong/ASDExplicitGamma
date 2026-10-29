module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B114 : ModeBlockData :=
  ⟨⟨214, 219, (234477583109476679/5000000000000000000000 : ℚ), (55223059753727321/1250000000000000000000 : ℚ)⟩, [
    (214, modeDataJ3M215),
    (215, modeDataJ3M216),
    (216, modeDataJ3M217),
    (217, modeDataJ3M218),
    (218, modeDataJ3M219)], (468955166218953353/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b114 : entryChecks 3 bflatBlockJ3B114.entries = true := by
  simp only [entryChecks,bflatBlockJ3B114,List.all_cons,List.all_nil,
    mode_checked_j3_m215,
    mode_checked_j3_m216,
    mode_checked_j3_m217,
    mode_checked_j3_m218,
    mode_checked_j3_m219,Bool.and_self]
theorem block_mass_checked_j3_b114 : blockMassCheck bflatBlockJ3B114 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
