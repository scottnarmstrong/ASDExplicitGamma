module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part012
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B112 : ModeBlockData :=
  ⟨⟨204, 209, (530763422873578899/10000000000000000000000 : ℚ), (486824559344940223/10000000000000000000000 : ℚ)⟩, [
    (204, modeDataJ3M205),
    (205, modeDataJ3M206),
    (206, modeDataJ3M207),
    (207, modeDataJ3M208),
    (208, modeDataJ3M209)], (265381711436789447/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b112 : entryChecks 3 bflatBlockJ3B112.entries = true := by
  simp only [entryChecks,bflatBlockJ3B112,List.all_cons,List.all_nil,
    mode_checked_j3_m205,
    mode_checked_j3_m206,
    mode_checked_j3_m207,
    mode_checked_j3_m208,
    mode_checked_j3_m209,Bool.and_self]
theorem block_mass_checked_j3_b112 : blockMassCheck bflatBlockJ3B112 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
