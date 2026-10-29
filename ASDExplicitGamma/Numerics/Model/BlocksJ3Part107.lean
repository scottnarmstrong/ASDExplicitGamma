module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B107 : ModeBlockData :=
  ⟨⟨183, 187, (515820117880947979/10000000000000000000000 : ℚ), (122167536926583949/2500000000000000000000 : ℚ)⟩, [
    (183, modeDataJ3M184),
    (184, modeDataJ3M185),
    (185, modeDataJ3M186),
    (186, modeDataJ3M187)], (20632804715237919/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b107 : entryChecks 3 bflatBlockJ3B107.entries = true := by
  simp only [entryChecks,bflatBlockJ3B107,List.all_cons,List.all_nil,
    mode_checked_j3_m184,
    mode_checked_j3_m185,
    mode_checked_j3_m186,
    mode_checked_j3_m187,Bool.and_self]
theorem block_mass_checked_j3_b107 : blockMassCheck bflatBlockJ3B107 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
