module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B72 : ModeBlockData :=
  ⟨⟨100, 106, (71958380686254877879/2500000000000000000000 : ℚ), (322478325666297573/2000000000000000000000 : ℚ)⟩, [
    (100, modeDataJ4M101),
    (101, modeDataJ4M102),
    (102, modeDataJ4M103),
    (103, modeDataJ4M104),
    (104, modeDataJ4M105),
    (105, modeDataJ4M106)], (28783352274501951151/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b72 : entryChecks 4 bflatBlockJ4B72.entries = true := by
  simp only [entryChecks,bflatBlockJ4B72,List.all_cons,List.all_nil,
    mode_checked_j4_m101,
    mode_checked_j4_m102,
    mode_checked_j4_m103,
    mode_checked_j4_m104,
    mode_checked_j4_m105,
    mode_checked_j4_m106,Bool.and_self]
theorem block_mass_checked_j4_b72 : blockMassCheck bflatBlockJ4B72 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
