import IsingBulk.Anisotropic.NegativeDominance.ParticleSeriesRanges
import IsingBulk.Anisotropic.NegativeDominance.PointwiseParticlePartition

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology BigOperators

/-- Assemble the entire infinite physical particle sum from per-particle
low, nonresonant, middle and high estimates. Constants precede every index. -/
theorem particle_estimates_eventual_ranges (B rootB : ℂ→ℂ) (phi : ℝ)
    {p : ℕ} (hp : 0<p) (hpOdd : Odd p)
    {a Dlow aG : ℝ} (ha : 0<a) (hDlow : 0≤Dlow) (haG : 0<aG) (CG Chigh : ℝ)
    (coeff : ℕ→ℕ→ℂ) (eta : ℕ→ℝ) (heta : ∀ᶠj : ℕ in atTop,0≤eta j)
    (heven : ∀j N,¬Odd N → coeff j N=0)
    (hlow : ∀j N,Odd N → ‖coeff j N‖≤Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j)
    (hnonres : ∀j N,Odd N → ¬p∣N →
      ‖coeff j N‖≤Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
    (hmiddle : ∀ᶠj : ℕ in atTop,∀N,
      N∈(resonantMiddleIndices p j).image (resonantParticle p) →
      ‖coeff j N-particleMiddleModel B rootB phi p j N‖≤
        eta j*‖particleMiddleModel B rootB phi p j N‖+
        Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
    (hhigh : ∀ᶠj : ℕ in atTop,∀N : ℕ,Odd N → p∣N → Real.log j<(N : ℝ) →
      (j : ℝ)/Real.sqrt (Real.log j)<(N : ℝ)^2 →
      ‖coeff j N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2)+
        Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1))) :
    ∃D C : ℝ,0<D ∧ ∀ᶠj : ℕ in atTop,
      Summable (coeff j) ∧ HasCoefficientRanges (fun j=>∑'N,coeff j N) B rootB phi p a D C eta j := by
  obtain ⟨D,C,hD,hassemble⟩ := particle_series_ranges B rootB phi hp ha hDlow haG CG Chigh
  refine ⟨D,C,hD,?_⟩
  have ht : Tendsto (fun j : ℕ=>Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [heta,hmiddle,hhigh,ht.eventually (eventually_ge_atTop (max 1024 (32*Chigh))),eventually_ge_atTop (1 : ℕ)]
    with j hη hm hh hlogs hj
  have hlog : 1024≤Real.log (j : ℝ) := (le_max_left _ _).trans hlogs
  have hCh : 32*Chigh≤Real.log (j : ℝ) := (le_max_right _ _).trans hlogs
  have hlog0 : 0≤Real.log (j : ℝ) := by linarith
  have hsqrt : 1≤Real.sqrt (Real.log (j : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ)≤Real.log j by linarith)
  obtain ⟨low,mid,high,err,heq,hlzero,hlbound,hmbound,hhzero,hhbound,hebound⟩ :=
    pointwise_particle_partition B rootB phi hp hpOdd hlog0 hsqrt (eta j) hη (coeff j)
      (fun N=>Dlow*(N : ℝ)^2*((N : ℝ)^3/a)^j)
      (fun N=>Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+Chigh*(N : ℝ)^2))
      (fun N=>Real.exp (-aG*(N : ℝ)^2+((j : ℝ)+1)*Real.log N+CG*((j : ℝ)+1)))
      (by intro N; positivity) (fun _=>(Real.exp_pos _).le) (fun _=>(Real.exp_pos _).le)
      (heven j) (hlow j) hm hh (hnonres j)
  have hout := hassemble j ⌊Real.log (j : ℝ)⌋₊ (Nat.floor_le hlog0)
    (by exact_mod_cast (show 0<j by omega)) hlog hCh eta hη (coeff j) low mid high err heq hlzero
    (fun N _=>hlbound N) hmbound hhzero (fun N _ _=>hhbound N) hebound
  exact hout

end
end IsingBulk.Anisotropic.NegativeDominance
