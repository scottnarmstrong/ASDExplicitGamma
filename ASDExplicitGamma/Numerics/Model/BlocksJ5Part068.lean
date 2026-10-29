module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B68 : ModeBlockData :=
  ⟨⟨97, 107, (120087428590540659003/5000000000000000000000 : ℚ), (38310323111968943/1000000000000000000000 : ℚ)⟩, [
    (97, modeDataJ5M98),
    (98, modeDataJ5M99),
    (99, modeDataJ5M100),
    (100, modeDataJ5M101),
    (101, modeDataJ5M102),
    (102, modeDataJ5M103),
    (103, modeDataJ5M104),
    (104, modeDataJ5M105),
    (105, modeDataJ5M106),
    (106, modeDataJ5M107)], (60043714295270329499/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b68 : entryChecks 5 bflatBlockJ5B68.entries = true := by
  simp only [entryChecks,bflatBlockJ5B68,List.all_cons,List.all_nil,
    mode_checked_j5_m98,
    mode_checked_j5_m99,
    mode_checked_j5_m100,
    mode_checked_j5_m101,
    mode_checked_j5_m102,
    mode_checked_j5_m103,
    mode_checked_j5_m104,
    mode_checked_j5_m105,
    mode_checked_j5_m106,
    mode_checked_j5_m107,Bool.and_self]
theorem block_mass_checked_j5_b68 : blockMassCheck bflatBlockJ5B68 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
