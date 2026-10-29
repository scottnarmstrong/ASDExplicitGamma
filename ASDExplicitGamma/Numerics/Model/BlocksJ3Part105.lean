module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part010
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B105 : ModeBlockData :=
  ⟨⟨175, 179, (562194501008126357/10000000000000000000000 : ℚ), (535811015422493671/10000000000000000000000 : ℚ)⟩, [
    (175, modeDataJ3M176),
    (176, modeDataJ3M177),
    (177, modeDataJ3M178),
    (178, modeDataJ3M179)], (562194501008126353/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b105 : entryChecks 3 bflatBlockJ3B105.entries = true := by
  simp only [entryChecks,bflatBlockJ3B105,List.all_cons,List.all_nil,
    mode_checked_j3_m176,
    mode_checked_j3_m177,
    mode_checked_j3_m178,
    mode_checked_j3_m179,Bool.and_self]
theorem block_mass_checked_j3_b105 : blockMassCheck bflatBlockJ3B105 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
