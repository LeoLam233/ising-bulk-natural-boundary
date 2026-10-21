import IsingBulk.HT.First.OddActualLocalMeanAsymptotic
import IsingBulk.First.SourceAsymptoticAttachment
import IsingBulk.First.SelectedYCutoffs
import IsingBulk.First.SwappedChartCoefficient

/-! The actual two ordered HT charts, using one constructed fixed cutoff.
No LT boundedness assertion at the critical derivative k−1 is imported. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter Set IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem attach_local_odd_asymptotic {n : ℕ} {alpha beta : ℝ}
    {U : Set (Fin n → ℝ)} (c : CompatibleYCutoffData n alpha beta U)
    (a : OrderedChartData) (j : ℕ) (L : ℂ)
    (hlocal : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => (deriv^[j] (localizedSmoothMeanIntegral a (liftShapeCutoff c.chi)
        (fun v => (c.eta v:ℂ)) (-(Real.sin a.theta/4)*epsilon) c.delta))
          (radialParameter a.theta epsilon) - (epsilon:ℂ)⁻¹*L)
      (fun epsilon => (epsilon:ℂ)⁻¹)) :
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => radialWeightedDerivative n j a.theta
        (fixedYChartWeight a.alpha c.chi c.eta) epsilon - (epsilon:ℂ)⁻¹*L)
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
  obtain ⟨e,he,_,hmargin⟩ := radial_disk_source_trace_margin a.sin_theta_pos
  apply hlocal.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds] with epsilon hp hsmall
  have hr1 : Real.exp (-(Real.sin a.theta/4)*epsilon) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [mul_pos a.sin_theta_pos hp]
  have hm := (hmargin epsilon hp hsmall (radialParameter a.theta epsilon)
    (by simpa using mul_pos (show 0 < Real.sin a.theta/16 from div_pos a.sin_theta_pos (by norm_num)) hp)).2
  rw [radialWeightedDerivative,c.source_localizedSmoothMean_derivative a _ _ hr1 hm j]

theorem odd_selected_local_pair_asymptotic {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    let n := p-1
    let k := derivativeOrder (n+1)
    let A := selectedOrderedChart ha hb
    (-I*localLeadingCoefficient A n k) ≠ 0 ∧
    ∃ (U : Set (Fin n → ℝ)) (c : CompatibleYCutoffData n A.alpha A.beta U),
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.leftWeight epsilon -
          (epsilon:ℂ)⁻¹*(-I*localLeadingCoefficient A n k))
        (fun epsilon => (epsilon:ℂ)⁻¹) ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => radialWeightedDerivative n k A.theta c.rightWeight epsilon -
          (epsilon:ℂ)⁻¹*(-I*localLeadingCoefficient A n k))
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let n := p-1
  let A := selectedOrderedChart ha hb
  let k := derivativeOrder (n+1)
  have hN : n+1=p := by dsimp [n]; have := hp.two_le; omega
  have hn : 1 ≤ n := by dsimp [n]; have := hp.two_le; omega
  have ho : Odd (n+1) := by rw [hN]; exact hp.odd_of_ne_two (by omega)
  have hNc : (n+1:ℂ)=((p:ℕ):ℂ) := by exact_mod_cast hN
  have hAlpha : exp (-(n+1:ℂ)*(A.alpha:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_odd_lower_center_root hp ha
  have hBeta : exp (-(n+1:ℂ)*(A.beta:ℂ)*I)=1 := by
    rw [hNc]
    exact selected_odd_lower_center_root hp hb
  obtain ⟨hL,Da,hDa,hA⟩ := actual_local_mean_odd_asymptotic hn A ho hAlpha hBeta
  obtain ⟨_,Db,hDb,hB⟩ := actual_local_mean_odd_asymptotic hn A.swap ho hBeta hAlpha
  have hCut : 0 < compatibleCutoffDeltaBound A.alpha A.beta :=
    selected_cutoff_delta_bound_pos hp ha hb hab
  let D := min Da (min Db (compatibleCutoffDeltaBound A.alpha A.beta))
  have hD : 0 < D := lt_min hDa (lt_min hDb hCut)
  let delta := D/2
  have hd : 0 < delta := half_pos hD
  have hdD : delta ≤ D := (half_lt_self hD).le
  have hdA : delta ≤ Da := hdD.trans (min_le_left _ _)
  have hdB : delta ≤ Db := hdD.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdCut : delta ≤ compatibleCutoffDeltaBound A.alpha A.beta :=
    hdD.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Ra,hRa,hPA⟩ := hA delta hd hdA
  obtain ⟨Rb,hRb,hPB⟩ := hB delta hd hdB
  let R := min Ra Rb
  have hR : 0 < R := lt_min hRa hRb
  let U := sourceShapeBall n R
  obtain ⟨c,hcd,hcH⟩ := exists_compatibleYCutoffData_at_delta n A.alpha A.beta
    (sourceShapeBall_mem_nhds_zero n hR) (show (0:ℝ)<1 by norm_num) hd hdCut
  have hη : Continuous (fun v => (c.eta v:ℂ)) := Complex.continuous_ofReal.comp c.eta_smooth.continuous
  have hη1 : ∀ v : ℝ, |v| ≤ delta → (c.eta v:ℂ)=1 := by
    intro v hv
    rw [c.eta_one v (by rwa [hcd]),ofReal_one]
  have hχ := liftShapeCutoff_continuous c.chi_smooth.continuous
  have hχ0 := liftShapeCutoff_zero (show c.chi 0=1 from c.chi_one.eq_of_nhds)
  have hχb := liftShapeCutoff_norm_le_one c.chi_range
  have hχs : ∀ x, liftShapeCutoff c.chi x ≠ 0 → ‖x‖ < R := by
    apply liftShapeCutoff_support
    intro t ht
    exact c.chi_support (subset_closure ht)
  have hpa := hPA (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχ0 hχb
    (fun x hx => (hχs x hx).trans_le (min_le_left _ _))
  have hpb := hPB (fun v => (c.eta v:ℂ)) hη hη1 (liftShapeCutoff c.chi) hχ hχ0 hχb
    (fun x hx => (hχs x hx).trans_le (min_le_right _ _))
  have hleft := attach_local_odd_asymptotic c A k ((-I*localLeadingCoefficient A n k))
    (by simpa only [hcd] using hpa)
  have hright := attach_local_odd_asymptotic c A.swap k ((-I*localLeadingCoefficient A.swap n k))
    (by simpa only [hcd] using hpb)
  rw [localLeadingCoefficient_swap] at hright
  exact ⟨hL,U,c,hleft,hright⟩

end
end IsingBulk.HT.First
