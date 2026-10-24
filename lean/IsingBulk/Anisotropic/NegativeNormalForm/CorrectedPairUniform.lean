import IsingBulk.Anisotropic.NegativeNormalForm.MeanPairBounds
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarRootCenterControl
import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem correctedSeparablePairFactor_uniform (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ n : ℕ, n≠0 → ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖d‖<r → ‖v‖<r → ZeroMean v → ∀ i j,
      ‖correctedSeparablePairFactor B phi hphi t d v i j-1‖≤
        C*(‖t-(1-Complex.cos d)‖+‖d‖*(‖v i‖+‖v j‖)+‖v i‖^2+‖v j‖^2+absoluteEnergy v/(n:ℝ)) := by
  obtain ⟨rp,Lp,hrp,hLp,hpair⟩ := rootPair_uniform_bounds B phi hphi hB hBn
  obtain ⟨rm,Lm,hrm,hLm,hmean⟩ := actual_mean_separable_refined_bound B phi hphi hB hBn
  obtain ⟨rc,Lc,hrc,hLc,hcenter⟩ := phaseRootEnergy_center_lipschitz B phi hphi hB hBn
  obtain ⟨rs,Ls,hrs,_hLs,hroot,_hLip⟩ := phaseRootEnergy_uniform_small B phi hphi hB hBn (1/4) (by norm_num)
  let r := min rs (min rp (min rm (min rc 1)))
  have hr : 0<r := lt_min hrs (lt_min hrp (lt_min hrm (lt_min hrc (by norm_num))))
  have hrs' : r≤rs := min_le_left _ _
  have hrp' : r≤rp := (min_le_right _ _).trans (min_le_left _ _)
  have hrm' : r≤rm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrc' : r≤rc := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr1 : r≤1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let C := Lc+Lp+48*Lm*Lp
  have hprod : 0≤48*Lm*Lp := by positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨r,C,hr,hC,?_⟩
  intro n hn t d v ht hd hv hzero i j
  have hnpos : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let S : Config n := fun k => rootScalar B phi hphi (t,(d,v k))
  have hS (k : Fin n) : ‖S k-1‖≤1/4 :=
    (hroot (t,(d,v k)) (max_lt (ht.trans_le hrs') (max_lt (hd.trans_le hrs') ((norm_le_pi_norm v k).trans_lt (hv.trans_le hrs'))))).2
  have hp := hpair t d (v i) (v j) (ht.trans_le hrp') (hd.trans_le hrp')
    ((norm_le_pi_norm v i).trans_lt (hv.trans_le hrp')) ((norm_le_pi_norm v j).trans_lt (hv.trans_le hrp'))
  have hm := hmean n t d v (ht.trans_le hrm') (hd.trans_le hrm') (hv.trans_le hrm') hzero
  have hcn := hcenter d t (hd.trans_le hrc') (ht.trans_le hrc')
  have hq : 0≤absoluteEnergy v := by unfold absoluteEnergy; positivity
  have hmu : ‖mean (fun k => v k*S k)‖≤2*Lm/(n:ℝ)*absoluteEnergy v := by
    apply hm.trans
    have hd1 := hd.trans_le hr1
    have hv1 := hv.trans_le hr1
    have harg : Lm*(‖d‖+‖v‖)≤2*Lm := by nlinarith
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right harg hnpos.le) hq
  have hD : ‖rootPairSlope B phi hphi t d (v i) (v j)‖≤3*Lp := by
    apply hp.2.2.1.trans
    have hi := (norm_le_pi_norm v i).trans (hv.trans_le hr1).le
    have hj := (norm_le_pi_norm v j).trans (hv.trans_le hr1).le
    have hd1 := (hd.trans_le hr1).le
    nlinarith
  have hcorr := rankOne_pair_term_bound hn S hS (mean (fun k => v k*S k))
    (rootPairSlope B phi hphi t d (v i) (v j)) i j
  have hcorr' : ‖rankOneCoefficient (meanCoefficients S)*mean (fun k => v k*S k)*
      (rootPairSlope B phi hphi t d (v i) (v j)/(S i*S j*(∑ k,(S k)⁻¹)))‖≤
      (48*Lm*Lp)*(absoluteEnergy v/(n:ℝ)) := by
    apply hcorr.trans
    calc
      _ ≤ 8*(2*Lm/(n:ℝ)*absoluteEnergy v)*(3*Lp) := by gcongr
      _ = _ := by ring
  let A := ‖d‖*(‖v i‖+‖v j‖)+‖v i‖^2+‖v j‖^2
  have hA : 0≤A := by dsimp [A]; positivity
  have hbase : ‖separablePairFactor B phi hphi t d (v i) (v j)-1‖≤
      Lp*A+Lc*‖t-(1-Complex.cos d)‖ := by
    have he : separablePairFactor B phi hphi t d (v i) (v j)-1=
        (separablePairFactor B phi hphi t d (v i) (v j)-rootScalar B phi hphi (t,(d,0)))+
        (rootScalar B phi hphi (t,(d,0))-1) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hp.2.2.2 hcn)
  have hfull : ‖correctedSeparablePairFactor B phi hphi t d v i j-1‖≤
      Lp*A+Lc*‖t-(1-Complex.cos d)‖+(48*Lm*Lp)*(absoluteEnergy v/(n:ℝ)) := by
    unfold correctedSeparablePairFactor
    rw [add_sub_right_comm]
    exact (norm_add_le _ _).trans (add_le_add hbase hcorr')
  apply hfull.trans
  have hpC : Lp≤C := by dsimp [C]; linarith
  have hcC : Lc≤C := by dsimp [C]; linarith
  have hmC : 48*Lm*Lp≤C := by dsimp [C]; linarith
  calc
    _ ≤ C*A+C*‖t-(1-Complex.cos d)‖+C*(absoluteEnergy v/(n:ℝ)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hpC hA)
        (mul_le_mul_of_nonneg_right hcC (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right hmC (div_nonneg hq hnpos.le))
    _ = _ := by dsimp [A]; ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
