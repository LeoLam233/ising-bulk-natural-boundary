import IsingBulk.Anisotropic.RegularEdges.MatchedSummability

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
open scoped Topology

/-- Linear and N log N losses consume only half a genuine Gaussian exponent.
The threshold depends on fixed constants, never on the Taylor order. -/
theorem eventually_gaussian_entropy_absorb (a C D : ℝ) (ha : 0<a) (hC : 0≤C) (hD : 0≤D) :
    ∀ᶠ N : ℕ in atTop,
      -a*(N : ℝ)^2+C*N*Real.log ((N : ℝ)+1)+D*N+D≤-(a/2)*(N : ℝ)^2 := by
  let d := a/(4*(C+1))
  have hd : 0<d := by dsimp [d]; positivity
  have hde : 4*(C+1)*d=a := by dsimp [d]; field_simp
  have hCd : C*d≤a/4 := by nlinarith
  let E := |d-1-Real.log d|
  let F := C*E+2*D
  have hE : 0≤E := abs_nonneg _
  have hF : 0≤F := by dsimp [F]; positivity
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (max 1 (4*F/a))] with N hN
  have hN1 : (1 : ℝ)≤N := (le_max_left _ _).trans hN
  have hNF : 4*F/a≤(N : ℝ) := (le_max_right _ _).trans hN
  have hlog := logarithm_linear_majorant hd N
  have hlog' : Real.log ((N : ℝ)+1)≤d*N+E := hlog.trans (by dsimp [E]; linarith [le_abs_self (d-1-Real.log d)])
  have hlogN := mul_le_mul_of_nonneg_left hlog' (show 0≤C*(N : ℝ) by positivity)
  have hquadratic := mul_le_mul_of_nonneg_right hCd (sq_nonneg (N : ℝ))
  have hDN := mul_le_mul_of_nonneg_left hN1 hD
  have hFN := mul_le_mul_of_nonneg_left ((div_le_iff₀ ha).mp hNF) (show (0 : ℝ)≤N by positivity)
  dsimp [F] at hFN
  nlinarith only [hlogN,hquadratic,hDN,hFN]

/-- Finitely many initial indices are absorbed without dropping any index. -/
theorem exists_uniform_additive_slack {f g : ℕ→ℝ}
    (h : ∀ᶠ N in atTop, f N≤g N) :
    ∃E : ℝ,0<E ∧ ∀N,f N≤g N+E := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp h
  let E : ℝ := 1+∑N∈Finset.range N₀,max 0 (f N-g N)
  have hsum : 0≤∑N∈Finset.range N₀,max 0 (f N-g N) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hE : 0<E := by dsimp [E]; linarith
  refine ⟨E,hE,fun N => ?_⟩
  by_cases hn : N₀≤N
  · exact (hN₀ N hn).trans (le_add_of_nonneg_right hE.le)
  have hmem : N∈Finset.range N₀ := Finset.mem_range.mpr (by omega)
  have hh := Finset.single_le_sum (fun k (_hk : k∈Finset.range N₀) => le_max_left (0 : ℝ) (f k-g k)) hmem
  have ht := le_max_right (0 : ℝ) (f N-g N)
  dsimp [E]
  linarith

/-- Global Gaussian absorption with a fixed constant handles all particle
indices, including the finite exceptional segment. -/
theorem gaussian_entropy_global (a C D : ℝ) (ha : 0<a) (hC : 0≤C) (hD : 0≤D) :
    ∃E : ℝ,0<E ∧ ∀N : ℕ,
      -a*(N : ℝ)^2+C*N*Real.log ((N : ℝ)+1)+D*N+D≤-(a/2)*(N : ℝ)^2+E :=
  exists_uniform_additive_slack (eventually_gaussian_entropy_absorb a C D ha hC hD)

end
end IsingBulk.Anisotropic.NegativeDominance
