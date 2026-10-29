module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part005
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B71 : ModeBlockData :=
  ⟨⟨95, 100, (251665214882441093541/10000000000000000000000 : ℚ), (276519028516053743/2000000000000000000000 : ℚ)⟩, [
    (95, modeDataJ4M96),
    (96, modeDataJ4M97),
    (97, modeDataJ4M98),
    (98, modeDataJ4M99),
    (99, modeDataJ4M100)], (7864537965076284173/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b71 : entryChecks 4 bflatBlockJ4B71.entries = true := by
  simp only [entryChecks,bflatBlockJ4B71,List.all_cons,List.all_nil,
    mode_checked_j4_m96,
    mode_checked_j4_m97,
    mode_checked_j4_m98,
    mode_checked_j4_m99,
    mode_checked_j4_m100,Bool.and_self]
theorem block_mass_checked_j4_b71 : blockMassCheck bflatBlockJ4B71 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
