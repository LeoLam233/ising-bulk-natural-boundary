import IsingBulk.HT.Lie.SignedOriginalFlux
import IsingBulk.HT.Lie.ExteriorWindow

/-! A constructed geometric full-collision face sum for the genuine signed
Lie descendants. The relative-coordinate normal flux keeps all vector
components, including the center correction Fi-Fq. No pointwise flux bound
or vanishing-flux certificate is an assumption of the endpoint below. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1200000

theorem signed_shape_flux_vanishes {d : LocalBranchData} (B : BranchEstimates d)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (M j : ℕ) (hM : 2*j+2 < M) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n : ℕ, 2*j+1 ≤ (n+2)*(n+1) →
      0 < ((n+2)*(n+1)-(2*j+1))+n → ∀ p q : Fin (n+2), p ≠ q →
      ∀ center : Fin (n+2), ∀ c : ℝ, |c| ≤ r/2 →
      Tendsto (fun ρ => shapeCubeFlux center c ρ
        (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j p q))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨G,C,hG,hC,E,a,A,rF,hE,ha,hA,hrF,hflux⟩ := signed_original_flux_bound B M j hM
  obtain ⟨rD,hrD,hdata⟩ := allBranchExterior_original_density_data d
  obtain ⟨zeta,rK,hzeta,hrK,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rF (min rD rK)
  have hr : 0 < r := lt_min hrF (lt_min hrD hrK)
  have hFr : r ≤ rF := min_le_left _ _
  have hDr : r ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hKr : r ≤ rK := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n horder hpower p q hpq center c hc
  let σ := Complex.exp (Complex.I*(α:ℂ))
  let K := microcoreCube (n+2) r
  have hK : IsCompact K := microcoreCube_compact (n+2) r
  have hdensity : ContinuousOn (signedExteriorKernelDensity σ d ε) K := by
    apply signed_kernel_density_continuousOn σ d K
    · intro u hu
      exact (hdata ε hε (hεr.trans hDr) (n+1) u
        (fun i => ((mem_microcoreCube r u).mp hu i).trans hDr)).1
    · intro u hu
      exact (hgap ε hε (hεr.trans hKr) α (n+1) u
        (fun i => ((mem_microcoreCube r u).mp hu i).trans hKr)).1
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hdensity
  have hkernel (u : Fin (n+2) → ℝ) (hu : u∈K) :
      signedExteriorKernelDensity σ d ε u ≤ max 0 D := by
    have hh := hD u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (signed_kernel_density_nonneg σ d ε u)] at hh
    exact hh.trans (le_max_right _ _)
  let H := max 1 (B.magnitudeUpper/Real.sqrt ε)
  have hH : 1 ≤ H := le_max_left _ _
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let P := (n+2)*(n+1)-(2*j+1)
  let L := originalFluxCost j (n+2) G C E a A H
  have hL : 0 ≤ L := by
    dsimp [L,originalFluxCost,allBranchExteriorNearNumeratorCost]
    positivity
  let Cflux := L*2^P*max 0 D
  apply shapeCubeFlux_tendsto_zero center c _ Cflux P hpower
  have hr2 : 0 < r/2 := half_pos hr
  have hHinv : 0 < (2*H)⁻¹ := inv_pos.mpr (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds hr2),
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds hHinv)]
    with ρ hρ hρr hρ1 hρH
  change 0 < ρ at hρ
  change ρ < r/2 at hρr
  change ρ < 1/2 at hρ1
  change ρ < (2*H)⁻¹ at hρH
  intro i upper y hy l
  let u := shapePoint center c (cubeFacePoint i upper ρ y)
  have hu (k : Fin (n+2)) : |u k| ≤ r := by
    have hh := shapePoint_coordinate_bound center c hρ.le _ (cubeFacePoint_mem i upper hρ.le y hy) k
    dsimp [u]
    linarith
  have hdu : 0 < allBranchExteriorDiameter u :=
    hρ.trans_le (shape_face_diameter_lower center c i upper hρ.le y)
  have hdu2 : allBranchExteriorDiameter u ≤ 2*ρ :=
    shape_point_diameter_upper center c hρ.le _ (cubeFacePoint_mem i upper hρ.le y hy)
  have hHD : H*allBranchExteriorDiameter u ≤ 1 := by
    have hsmall : ρ*(2*H) < 1 :=
      (lt_div_iff₀ (by positivity : (0:ℝ)<2*H)).mp (by simpa only [one_div] using hρH)
    nlinarith [mul_le_mul_of_nonneg_left hdu2 hHpos.le]
  have hb := hflux ε hε (hεr.trans hFr) σ (n+1) horder p q hpq u
    (fun k => (hu k).trans hFr) hdu (by linarith) H hH (le_max_right _ _) hHD l
  have huK : u∈K := (mem_microcoreCube r u).mpr hu
  have hpow : allBranchExteriorDiameter u^P ≤ (2*ρ)^P := pow_le_pow_left₀ hdu.le hdu2 P
  change ‖signedOriginalFlux σ d ε M j p q u l‖ ≤ Cflux*ρ^P
  apply hb.trans
  calc
    _ ≤ L*(2*ρ)^P*max 0 D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hL) (hkernel u huK)
        (signed_kernel_density_nonneg σ d ε u) (mul_nonneg hL (pow_nonneg (by positivity) P))
    _ = _ := by dsimp [Cflux]; rw [mul_pow]; ring


theorem signed_shape_flux_power_bound {d : LocalBranchData} (B : BranchEstimates d)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (M j : ℕ) (hM : 2*j+2 < M) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n : ℕ, 2*j+1 ≤ (n+2)*(n+1) →
      ∀ p q : Fin (n+2), p ≠ q → ∀ center : Fin (n+2),
      ∃ Cflux : ℝ, 0 ≤ Cflux ∧ ∀ᶠ ρ in 𝓝[>] (0:ℝ), ∀ c : ℝ, |c| ≤ r/2 →
        ‖shapeCubeFlux center c ρ
          (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j p q)‖ ≤
          Cflux*ρ^(((n+2)*(n+1)-(2*j+1))+n) := by
  obtain ⟨G,C,hG,hC,E,a,A,rF,hE,ha,hA,hrF,hflux⟩ := signed_original_flux_bound B M j hM
  obtain ⟨rD,hrD,hdata⟩ := allBranchExterior_original_density_data d
  obtain ⟨zeta,rK,hzeta,hrK,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rF (min rD rK)
  have hr : 0 < r := lt_min hrF (lt_min hrD hrK)
  have hFr : r ≤ rF := min_le_left _ _
  have hDr : r ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hKr : r ≤ rK := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n horder p q hpq center
  let σ := Complex.exp (Complex.I*(α:ℂ))
  let K := microcoreCube (n+2) r
  have hK : IsCompact K := microcoreCube_compact (n+2) r
  have hdensity : ContinuousOn (signedExteriorKernelDensity σ d ε) K := by
    apply signed_kernel_density_continuousOn σ d K
    · intro u hu
      exact (hdata ε hε (hεr.trans hDr) (n+1) u
        (fun i => ((mem_microcoreCube r u).mp hu i).trans hDr)).1
    · intro u hu
      exact (hgap ε hε (hεr.trans hKr) α (n+1) u
        (fun i => ((mem_microcoreCube r u).mp hu i).trans hKr)).1
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hdensity
  have hkernel (u : Fin (n+2) → ℝ) (hu : u∈K) :
      signedExteriorKernelDensity σ d ε u ≤ max 0 D := by
    have hh := hD u hu
    rw [Real.norm_eq_abs,abs_of_nonneg (signed_kernel_density_nonneg σ d ε u)] at hh
    exact hh.trans (le_max_right _ _)
  let H := max 1 (B.magnitudeUpper/Real.sqrt ε)
  have hH : 1 ≤ H := le_max_left _ _
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let P := (n+2)*(n+1)-(2*j+1)
  let L := originalFluxCost j (n+2) G C E a A H
  have hL : 0 ≤ L := by
    dsimp [L,originalFluxCost,allBranchExteriorNearNumeratorCost]
    positivity
  let Cflux := L*2^P*max 0 D
  refine ⟨4*(n+1:ℝ)*Cflux*2^n,by dsimp [Cflux]; positivity,?_⟩
  have hr2 : 0 < r/2 := half_pos hr
  have hHinv : 0 < (2*H)⁻¹ := inv_pos.mpr (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds hr2),
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    (continuousWithinAt_id : ContinuousWithinAt (fun ρ : ℝ => ρ) (Ioi 0) 0).tendsto.eventually (gt_mem_nhds hHinv)]
    with ρ hρ hρr hρ1 hρH
  change 0 < ρ at hρ
  change ρ < r/2 at hρr
  change ρ < 1/2 at hρ1
  change ρ < (2*H)⁻¹ at hρH
  intro c hc
  apply shapeCubeFlux_norm_le center c _ Cflux P hρ.le
  intro i upper y hy l
  let u := shapePoint center c (cubeFacePoint i upper ρ y)
  have hu (k : Fin (n+2)) : |u k| ≤ r := by
    have hh := shapePoint_coordinate_bound center c hρ.le _ (cubeFacePoint_mem i upper hρ.le y hy) k
    dsimp [u]
    linarith
  have hdu : 0 < allBranchExteriorDiameter u :=
    hρ.trans_le (shape_face_diameter_lower center c i upper hρ.le y)
  have hdu2 : allBranchExteriorDiameter u ≤ 2*ρ :=
    shape_point_diameter_upper center c hρ.le _ (cubeFacePoint_mem i upper hρ.le y hy)
  have hHD : H*allBranchExteriorDiameter u ≤ 1 := by
    have hsmall : ρ*(2*H) < 1 :=
      (lt_div_iff₀ (by positivity : (0:ℝ)<2*H)).mp (by simpa only [one_div] using hρH)
    nlinarith [mul_le_mul_of_nonneg_left hdu2 hHpos.le]
  have hb := hflux ε hε (hεr.trans hFr) σ (n+1) horder p q hpq u
    (fun k => (hu k).trans hFr) hdu (by linarith) H hH (le_max_right _ _) hHD l
  have huK : u∈K := (mem_microcoreCube r u).mpr hu
  have hpow : allBranchExteriorDiameter u^P ≤ (2*ρ)^P := pow_le_pow_left₀ hdu.le hdu2 P
  change ‖signedOriginalFlux σ d ε M j p q u l‖ ≤ Cflux*ρ^P
  apply hb.trans
  calc
    _ ≤ L*(2*ρ)^P*max 0 D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow hL) (hkernel u huK)
        (signed_kernel_density_nonneg σ d ε u) (mul_nonneg hL (pow_nonneg (by positivity) P))
    _ = _ := by dsimp [Cflux]; rw [mul_pow]; ring

/-- The HT odd-particle window supplies the strict face-power margin. -/
theorem ht_shape_flux_vanishes {d : LocalBranchData} (B : BranchEstimates d)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (M p j : ℕ)
    (hp : 1 ≤ p) (hj : j ≤ (p^2-1)/2) (hM : 2*((p^2-1)/2)+2 < M) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n : ℕ, p+2 ≤ n+2 → ∀ a b : Fin (n+2), a ≠ b →
      ∀ center : Fin (n+2), ∀ c : ℝ, |c| ≤ r/2 →
      Tendsto (fun ρ => shapeCubeFlux center c ρ
        (signedOriginalFlux (Complex.exp (Complex.I*(α:ℂ))) d ε M j a b))
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨r,hr,hflux⟩ := signed_shape_flux_vanishes B hcsmall M j (by omega)
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n hN a b hab center c hc
  have ho : 2*j+1 ≤ (n+2)*(n+1) := by
    have hh := exterior_source_degree (N := n+2) hp hN hj
    simpa only [show n+2-1=n+1 by omega] using hh
  have hn : 0 < n := by omega
  exact hflux ε hε hεr α n ho (by omega) a b hab center c hc

end
end IsingBulk.HT.Lie
