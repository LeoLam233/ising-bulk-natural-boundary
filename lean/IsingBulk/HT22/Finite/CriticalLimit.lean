import IsingBulk.HT22.First.LocalLimit.SignedPrimeCharts
import IsingBulk.HT22.Geometry.CriticalShapeCutoff
import IsingBulk.HT22.Physical.FiniteAssembly.LocalizedRight
namespace IsingBulk.HT22.Finite
noncomputable section
open Complex Set Filter Metric IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open IsingBulk.PrimeFamily Arithmetic LocalLimit Geometry IsingBulk.Preferred22
open Physical.FiniteAssembly
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem prime_actual_critical_cutoff_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (B : PreferredCoareaBump (primeBranchData hp hp5 ha))
    (δB : ℝ) (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData (primeBranchData hp hp5 ha) B δB rcut) :
    ∃ R : ℝ,0<R ∧ ∀ χ : (Fin (p-1) → ℝ) → ℝ,
      Continuous χ → χ (fun _ => -(primeBranchData hp hp5 ha).alpha)=1 →
      (∀ u,0≤χ u ∧ χ u≤1) →
      (∀ u,χ u≠0 → ‖u-(fun _ => -(primeBranchData hp hp5 ha).alpha)‖<R) →
      ∀ τ : ℝ,Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
        (localizedRightIntegral (negativeSide (angle p a)) (p-1) τ B.p B.m rcut χ)
        (radialParameter (primeBranchData hp hp5 ha).alpha ε))
        (𝓝[>] 0) (𝓝 ((1/2:ℂ)*physicalCriticalLeadingCoefficient p (angle p a))) := by
  let d := primeBranchData hp hp5 ha
  let negative := negativeSide (angle p a)
  have he : p-1+1=p := by omega
  obtain ⟨Rl,hRl,hlim⟩ := prime_physicalCritical_lower_limit hp hp5 ha
  obtain ⟨Rs,hRs,hshape⟩ := criticalShapeCutoff_support_radius (p-1) negative d.alpha hRl
  obtain ⟨l,hl⟩ := primeBranchData_critical_mean hp hp5 ha
  obtain ⟨Rp,hRp,hplateau⟩ := signed_critical_localized_integral (p-1) negative d B δB rcut hcut l
    (by simpa only [he] using hl)
  refine ⟨min Rs Rp,lt_min hRs hRp,?_⟩
  intro χ hχ hχ0 hχb hχsupp τ
  let χs := criticalShapeCutoff negative d.alpha χ
  have hs : ∀ x,χs x≠0 → ‖x‖<Rl := hshape χ (fun u hu =>
    (hχsupp u hu).trans_le (min_le_left _ _))
  have ht := hlim χs (criticalShapeCutoff_continuous _ _ _ hχ)
    (by simpa only [χs,criticalShapeCutoff_zero] using hχ0)
    (criticalShapeCutoff_bound _ _ _ hχb) hs
  have hid : localizedRightIntegral negative (p-1) τ B.p B.m rcut χ=
      physicalCriticalLocalIntegral negative d.alpha χs := by
    funext t
    rw [localizedRightIntegral_eq_lifted negative (p-1) d B τ rcut hcut.2.2.2.1 χ t]
    rw [hplateau (fun u => (χ u:ℂ)) (fun u hu =>
      (hχsupp u (ofReal_ne_zero.mp hu)).trans_le (min_le_right _ _)) τ t]
    dsimp only [χs]
    cases negative with
    | false => exact critical_free_integral_positive d.alpha χ t
    | true => exact critical_free_integral_negative d.alpha χ t
  dsimp only [negative,d] at hid
  rw [hid]
  simpa only [iteratedDeriv_eq_iterate] using ht

end
end IsingBulk.HT22.Finite
