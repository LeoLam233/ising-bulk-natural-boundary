import IsingBulk.Joint.Isotropic.LowSurjection
import IsingBulk.Joint.Isotropic.AnalyticHomeomorph

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

def exteriorDisk : Set ℂ := {s | 1 < ‖s‖}
def outerRootDomain : Set ℂ := {v | 1 < ‖v‖ ∧ 1 < ‖sinhJoukowski v‖}

theorem exteriorDisk_isOpen : IsOpen exteriorDisk :=
  isOpen_lt continuous_const continuous_norm

theorem joukowski_analyticAt {v : ℂ} (hv : v ≠ 0) :
    AnalyticAt ℂ sinhJoukowski v :=
  (analyticAt_id.sub (analyticAt_id.inv hv)).div analyticAt_const (by norm_num)

theorem outerRootDomain_isOpen : IsOpen outerRootDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  have hv0 : v ≠ 0 := by intro h; norm_num [h, outerRootDomain] at hv
  have h₁ := (isOpen_lt continuous_const continuous_norm).mem_nhds hv.1
  have h₂ := (joukowski_analyticAt hv0).continuousAt.norm.eventually_const_lt hv.2
  exact inter_mem h₁ h₂

theorem joukowski_hasDerivAt {v : ℂ} (hv : v ≠ 0) :
    HasDerivAt sinhJoukowski ((1+v⁻¹^2)/2) v := by
  change HasDerivAt (fun x : ℂ => (x-x⁻¹)/2) _ v
  convert ((hasDerivAt_id v).sub ((hasDerivAt_id v).inv hv)).div_const (2:ℂ) using 1 <;>
    simp [div_eq_mul_inv, inv_pow]

theorem joukowski_deriv_ne_zero {v : ℂ} (hv : 1 < ‖v‖) :
    deriv sinhJoukowski v ≠ 0 := by
  have hv0 : v ≠ 0 := by intro h; norm_num [h, outerRootDomain] at hv
  rw [(joukowski_hasDerivAt hv0).deriv]
  apply div_ne_zero _ (by norm_num)
  intro he
  have hpow : v⁻¹^2 = -1 := by linear_combination he
  have hn := congrArg norm hpow
  simp only [norm_pow, norm_inv, norm_neg, norm_one] at hn
  have hi : ‖v‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv
  nlinarith [inv_nonneg.mpr (norm_nonneg v)]

theorem joukowski_bijOn : Set.BijOn sinhJoukowski outerRootDomain exteriorDisk := by
  refine ⟨fun _ hv => hv.2, joukowski_injOn_outer.mono (fun _ hv => hv.1), ?_⟩
  intro s hs
  change 1 < ‖s‖ at hs
  obtain ⟨v,hv,hvs⟩ := exists_outer_joukowski_root hs
  exact ⟨v,⟨hv,by simpa only [hvs] using hs⟩,hvs⟩

def exteriorRootHomeomorph : outerRootDomain ≃ₜ exteriorDisk :=
  analyticBijOnHomeomorph outerRootDomain_isOpen exteriorDisk_isOpen joukowski_bijOn
    (fun v hv => joukowski_analyticAt (by intro h; norm_num [h, outerRootDomain] at hv))
    (fun _ hv => joukowski_deriv_ne_zero hv.1)

@[simp] theorem exteriorRootHomeomorph_apply (v : outerRootDomain) :
    (exteriorRootHomeomorph v : ℂ) = sinhJoukowski v := rfl

end
end IsingBulk.Joint
