module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B73 : ModeBlockData :=
  ⟨⟨82, 84, (22927674689883895203/10000000000000000000000 : ℚ), (750772200217761729/5000000000000000000000 : ℚ)⟩, [
    (82, modeDataJ3M83),
    (83, modeDataJ3M84)], (22927674689883895201/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b73 : entryChecks 3 bflatBlockJ3B73.entries = true := by
  simp only [entryChecks,bflatBlockJ3B73,List.all_cons,List.all_nil,
    mode_checked_j3_m83,
    mode_checked_j3_m84,Bool.and_self]
theorem block_mass_checked_j3_b73 : blockMassCheck bflatBlockJ3B73 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
