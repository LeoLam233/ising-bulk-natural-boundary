import IsingBulk.AnisoF002.C03.NegativePaperWindowScale

/-!
# One physical first-winding comparison for every fixed positive inner radius

All analytic constants and the density radius are chosen first. Any fixed
positive compact lower radius is then permitted, with only the eventual
particle threshold depending on it. This permits the literal cutoff
R_N=sqrt(s-pi²/N) for an independently constructed sufficiently small s.
The original real-cycle measure, complete model phase and exact paper
order window are retained. Earlier verified comparison sources remain
unchanged.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology

set_option maxHeartbeats 2400000 in
theorem exists_uniform_physical_first_winding_comparison_all_cutoffs {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ0 : 0 < φ) (hφpi : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ σ C Kρ Kp M E : ℝ,
      0 < σ ∧ σ ≤ 1 ∧ 0 < C ∧ 0 < Kρ ∧ 0 < Kp ∧ 768 * Kp * σ ≤ 1 ∧
      0 < M ∧ 0 < E ∧
      ∀ Rmin : ℝ, 0 < Rmin → ∀ᶠ l : ℕ in atTop,
        ∃ p : PhysicalFirstWindingData b B φ (2 * l + 1) σ C Kρ Kp,
          ∀ (j : ℕ) (R : ℝ),
            M * (((2 * l + 1 : ℕ) : ℝ)) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) →
            Real.log (j : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) →
            Rmin ≤ R → R < σ →
            IntegrableOn (p.physicalResidueIntegrand (j + 1)) (Metric.closedBall 0 R)
              (independentMeasure (2 * l)) ∧
            let model := modelCoefficient (2 * l + 1) j (B (windingTau (2 * l + 1) : ℂ))
              (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
                (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
            ‖2 * p.physicalResidueIntegral (j + 1) R - (Complex.sqrt (B 0) / b 0) * model‖ ≤
              E * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) * ‖model‖ := by
  obtain ⟨σ, C, Kρ, Kp, hσ, hσ1, hC, hKρ, hKp, hKσ, hdata⟩ :=
    exists_physical_first_winding_data_for_full_radial_split hb hB hφ0 hφpi hBi hbsq
  let X : ℝ := 2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)
  let M : ℝ := (8 + 32 * X) ^ 2
  let A : ℝ := angularPerturbationConstant * X
  let D : ℝ := curvatureErrorConstant (‖B 0‖ + 1) (Real.cos φ) (Real.sin φ)
  let E : ℝ := (A + 1) * Real.exp (2 * D ^ 2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 < A := mul_pos angularPerturbationConstant_pos hX
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : 0 < E := mul_pos (by linarith) (Real.exp_pos _)
  refine ⟨σ, C, Kρ, Kp, M, E, hσ, hσ1, hC, hKρ, hKp, hKσ, hM, hE, ?_⟩
  intro Rmin hRmin
  have hB0 : B 0 ≠ 0 := by intro he; simp [he] at hBi
  have hBn : ∀ᶠ n : ℕ in atTop, B (windingTau n : ℂ) ≠ 0 :=
    (tendsto_anisotropy_at_centers B hB.continuousAt).eventually
      (eventually_ne_nhds hB0)
  have hBK : ∀ᶠ n : ℕ in atTop, ‖B (windingTau n : ℂ)‖ ≤ ‖B 0‖ + 1 :=
    (tendsto_anisotropy_at_centers B hB.continuousAt).norm.eventually
      (eventually_le_nhds (by linarith))
  have hphase : ∀ᶠ n : ℕ in atTop, 2 * D ≤ (n : ℝ) ^ 2 :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hspace : ∀ᶠ n : ℕ in atTop, 1024 / (Rmin) ^ 2 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  have hcenter := eventually_global_center_density hB hφ0 hφpi hBi hbsq
  have hsign := (eventually_global_center_root_sign hb hB hBi hbsq).2
  have ht : Tendsto (fun l : ℕ => 2 * l + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    exact eventually_atTop.mpr ⟨k, fun l hl => by omega⟩
  filter_upwards [ht.eventually hdata, ht.eventually hBn, ht.eventually hBK,
    ht.eventually hphase, ht.eventually hspace, ht.eventually hcenter,
    ht.eventually hsign, eventually_gt_atTop (1 : ℕ)]
    with l hlData hlBn hlBK hlPhase hlSpace hlCenter hlSign hl
  obtain ⟨p⟩ := hlData.1
  refine ⟨p, ?_⟩
  intro j R hj hlog hRlow hRσ
  have hN : (0 : ℝ) < ((2 * l + 1 : ℕ) : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * l + 1 by omega)
  have hN4 : (4 : ℝ) ≤ ((2 * l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ 2 * l + 1 by omega)
  obtain ⟨hk0, hδ, hδ1, hδsq, hsmall, h64⟩ := order_scale_bounds hN hX.le hj
  have hk64 : 64 * (2 * l + 1) ^ 2 ≤ j + 1 := by exact_mod_cast h64
  have hkN : (((2 * l + 1 : ℕ) : ℝ)) ^ 2 ≤ ((j + 1 : ℕ) : ℝ) := by nlinarith
  have hR0 : 0 < R := (by positivity : 0 < Rmin).trans_le hRlow
  have hRcentral : 1024 * ((2 * l + 1 : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) < R ^ 2 := by
    calc
      _ ≤ 1024 * ((2 * l + 1 : ℕ) : ℝ) / (((2 * l + 1 : ℕ) : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hN) hkN
      _ = 1024 / ((2 * l + 1 : ℕ) : ℝ) := by field_simp
      _ < (Rmin) ^ 2 := by
        apply (div_lt_iff₀ hN).mpr
        have hh := (div_lt_iff₀ (sq_pos_of_pos (by positivity : 0 < Rmin))).mp hlSpace
        nlinarith
      _ ≤ R ^ 2 := by nlinarith
  have hshape : radialShape (2 * l) = (particleExponent (2 * l + 1) : ℝ) := by
    rw [particleExponent_odd, radialShape_even_dimension (by omega)]
  have he := p.complete_physical_relative_pole_comparison (by omega) hshape hk64
    hσ hσ1 hKρ.le hKp.le hKσ hlData.2.1 hlData.2.2 hR0 hRσ hRcentral
      hδ hδ1 hδsq hsmall hlBK hlPhase
  have hj1 : 1 ≤ j := by
    have hNnat : 1 ≤ (2 * l + 1) ^ 2 := by nlinarith
    omega
  have hlogwide := log_succ_le_double_bound hj1 hN1 hlog
  have htail := gaussian_radial_tail_le_double_log_scale hN4 hk0 hlogwide
  have hcost := phase_factor_uniform_bound (C := D) hN1
  have hε :
      (A * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) +
        Real.exp (-(((2 * l + 1 : ℕ) : ℝ)) ^ 2 / 4)) *
          Real.exp (2 * D ^ 2 / (((2 * l + 1 : ℕ) : ℝ)) ^ 2) ≤
        E * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ ((A + 1) * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ))) *
          Real.exp (2 * D ^ 2) :=
        mul_le_mul (by nlinarith) hcost (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [E]; ring
  have he' : ‖p.compactPoleIntegral (j + 1) R - p.fullQuadraticPeriod (j + 1)‖ ≤
      (E * (((2 * l + 1 : ℕ) : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ))) *
        ‖p.fullQuadraticPeriod (j + 1)‖ :=
    he.trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
  have hαj : 2 * l * (l + 1) ≤ j := by
    have hh := particleExponent_le_sq (2 * l + 1)
    rw [particleExponent_odd] at hh
    have hNsq : 4 ≤ (2 * l + 1) ^ 2 := by nlinarith
    omega
  have hidx : 2 * l * (l + 1) + (j - 2 * l * (l + 1)) = j := Nat.add_sub_of_le hαj
  have hφ : Real.sin φ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi).ne'
  have hm := p.twice_physical_residue_model_error (by omega) (j - 2 * l * (l + 1))
    (hlCenter ⟨l, rfl⟩) hlBn (hbsq _) hφ hσ hRσ
      (by simpa only [hidx] using he')
  refine ⟨p.physicalResidueIntegrand_integrableOn (j + 1) hσ hσ1 hKp.le
    (by nlinarith : 48 * Kp * σ ≤ 1) hRσ, ?_⟩
  simpa only [hidx, hlSign] using hm

end
end IsingBulk.AnisoF002.NegativeHT
