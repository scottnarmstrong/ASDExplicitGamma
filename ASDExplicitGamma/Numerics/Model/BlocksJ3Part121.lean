module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B121 : ModeBlockData :=
  ⟨⟨249, 255, (200559307269284813/5000000000000000000000 : ℚ), (77747164167029201/2000000000000000000000 : ℚ)⟩, [
    (249, modeDataJ3M250),
    (250, modeDataJ3M251),
    (251, modeDataJ3M252),
    (252, modeDataJ3M253),
    (253, modeDataJ3M254),
    (254, modeDataJ3M255)], (20055930726928481/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b121 : entryChecks 3 bflatBlockJ3B121.entries = true := by
  simp only [entryChecks,bflatBlockJ3B121,List.all_cons,List.all_nil,
    mode_checked_j3_m250,
    mode_checked_j3_m251,
    mode_checked_j3_m252,
    mode_checked_j3_m253,
    mode_checked_j3_m254,
    mode_checked_j3_m255,Bool.and_self]
theorem block_mass_checked_j3_b121 : blockMassCheck bflatBlockJ3B121 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
