module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B53 : ModeBlockData :=
  ⟨⟨53, 54, (36151432428444695253/5000000000000000000000 : ℚ), (328339838064786411/2000000000000000000000 : ℚ)⟩, [
    (53, modeDataJ3M54)], (14460572971377878101/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b53 : entryChecks 3 bflatBlockJ3B53.entries = true := by
  simp only [entryChecks,bflatBlockJ3B53,List.all_cons,List.all_nil,
    mode_checked_j3_m54,Bool.and_self]
theorem block_mass_checked_j3_b53 : blockMassCheck bflatBlockJ3B53 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
