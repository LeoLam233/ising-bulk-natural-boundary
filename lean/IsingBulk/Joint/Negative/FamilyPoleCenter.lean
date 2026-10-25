import IsingBulk.Joint.Negative.FamilyIdentities

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open scoped Topology BigOperators

theorem compact_family_pole_center_bounds (B : ℂ×E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀eta∈K,AnalyticAt ℂ B (0,eta)) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ eta∈K,∀ (n : ℕ), n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∀ v : Config n, ‖v‖<δ →
      ‖poleAverage (familyMember B eta) phi hphi d (1-Complex.cos d) v‖≤M*‖v‖ ∧
      (ZeroMean v → ‖poleAverage (familyMember B eta) phi hphi d (1-Complex.cos d) v‖≤M*averageSquaredNorm v) := by
  obtain ⟨r,M,hr,hM,hbound⟩ := compact_family_factor_bounds B phi hphi hK hB
  obtain ⟨s,hs,hident⟩ := compact_family_factor_identities B phi hphi hK hB
  let R := min r s
  have hR : 0<R := lt_min hr hs
  have ht : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<R/2 := by
    have hc : ContinuousAt (fun d : ℂ => ‖1-Complex.cos d‖) 0 := by fun_prop
    exact hc.eventually_lt continuousAt_const (by simpa using half_pos hR)
  obtain ⟨η,hη,hτ⟩ := Metric.mem_nhds_iff.mp ht
  let δ := min (R/2) η
  have hδ : 0<δ := lt_min (half_pos hR) hη
  refine ⟨δ,M,hδ,hM,?_⟩
  intro eta heta n hn d hd v hv
  have hdR : ‖d‖<R := hd.trans_le (min_le_left _ _) |>.trans (half_lt_self hR)
  have hvR : ‖v‖<R := hv.trans_le (min_le_left _ _) |>.trans (half_lt_self hR)
  have hτR : ‖1-Complex.cos d‖<R :=
    (hτ (show d∈ball (0:ℂ) η by simpa using hd.trans_le (min_le_right _ _))).trans (half_lt_self hR)
  have hp (i : Fin n) : ‖(((1-Complex.cos d),d,v i):ScalarTriple)‖<R := by
    simp only [Prod.norm_def,max_lt_iff]
    exact ⟨hτR,hdR,(norm_le_pi_norm v i).trans_lt hvR⟩
  have hi (i : Fin n) := hident eta heta ((1-Complex.cos d),d,v i) ((hp i).trans_le (min_le_right _ _))
  have hb (i : Fin n) := hbound eta heta ((1-Complex.cos d),d,v i) ((hp i).trans_le (min_le_left _ _))
  constructor
  · change ‖mean (fun i => negativePhase (familyMember B eta) phi hphi (1-Complex.cos d) (d+v i)-(phi:ℂ)*Complex.I)‖≤_
    apply (norm_mean_le hn _).trans
    apply pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (norm_nonneg v)) |>.mpr
    intro i
    have hh := (hi i).1
    simp only [phaseIncrement,negativePhase_center] at hh
    rw [hh,norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb i).1 (norm_nonneg _)).trans
      (by nlinarith [norm_le_pi_norm v i])
  · intro hv0
    exact poleAverage_zeroMean_bound (familyMember B eta) phi hphi d v hv0
      (fun i => (hi i).1) (fun i => (hi i).2) (fun i => (hb i).2)

end
end IsingBulk.Joint.Negative
