module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B14 : ModeBlockData :=
  ⟨⟨14, 15, (63436610614488084901/2000000000000000000000 : ℚ), (2248809350070276689/1250000000000000000000 : ℚ)⟩, [
    (14, modeDataJ2M15)], (39647881634055053063/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b14 : entryChecks 2 bflatBlockJ2B14.entries = true := by
  simp only [entryChecks,bflatBlockJ2B14,List.all_cons,List.all_nil,
    mode_checked_j2_m15,Bool.and_self]
theorem block_mass_checked_j2_b14 : blockMassCheck bflatBlockJ2B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
