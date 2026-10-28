import IsingBulk.HT22.Transport.FieldNeighborhood.SourceBall

/-! # Original one-body jets control the actual source pair derivatives

This closes the pair-derivative inputs of the residual-ball estimate from
literal inverse partial derivatives; no residual derivative is hypothesized.
-/
namespace IsingBulk.HT22
noncomputable section
open Set Geometry
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exact joint differential of the inverse evaluated at one coordinate. -/
theorem sourceInverseCoordinate_fderiv_apply {N : ℕ}
    (x h : SourcePoint N) (i : Fin N)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 i)) :
    fderiv ℂ (sourceInverseCoordinate i) x h =
      h.1*sourceInverseT x.1 (x.2 i)+h.2 i*sourceInverseV x.1 (x.2 i) := by
  let L : SourcePoint N →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))
  have hh := hU.differentiableAt.hasFDerivAt.comp x L.hasFDerivAt
  have he := congrArg (fun F : SourcePoint N →L[ℂ] ℂ => F h) hh.fderiv
  change fderiv ℂ (sourceInverseCoordinate i) x h =
    fderiv ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 i) (h.1,h.2 i) at he
  rw [he, show (h.1,h.2 i) = h.1 • ((1,0) : ℂ × ℂ)+h.2 i • ((0,1) : ℂ × ℂ) by
    ext <;> simp]
  rw [map_add, map_smul, map_smul]
  change h.1*inverseTJoint (x.1,x.2 i)+h.2 i*inverseVJoint (x.1,x.2 i) = _
  rw [inverseTJoint_eq x.1 (x.2 i) hU, inverseVJoint_eq x.1 (x.2 i) hU]

/-- A first-coordinate difference retains its small H scale because the
fixed-v parameter derivative is itself a difference of original Ut values. -/
theorem sourceInversePair_fderiv_bound {N : ℕ} (x : SourcePoint N)
    (i j : Fin N) (C H d : ℝ) (hC : 0≤C) (hH : 0≤H) (hdH : d≤H)
    (hU : ∀ k, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 k))
    (hv : ∀ k, ‖sourceInverseV x.1 (x.2 k)‖≤C*H)
    (ht : ‖sourceInverseT x.1 (x.2 i)-sourceInverseT x.1 (x.2 j)‖≤C*d) :
    ‖fderiv ℂ (fun z => sourceInverseCoordinate i z-sourceInverseCoordinate j z) x‖≤3*C*H := by
  have hdi := (sourceInverseCoordinate_analyticAt x i (hU i)).differentiableAt
  have hdj := (sourceInverseCoordinate_analyticAt x j (hU j)).differentiableAt
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [fderiv_fun_sub hdi hdj]
  change ‖fderiv ℂ (sourceInverseCoordinate i) x h-
    fderiv ℂ (sourceInverseCoordinate j) x h‖≤_
  rw [sourceInverseCoordinate_fderiv_apply x h i (hU i),
    sourceInverseCoordinate_fderiv_apply x h j (hU j)]
  have he : h.1*sourceInverseT x.1 (x.2 i)+h.2 i*sourceInverseV x.1 (x.2 i)-
      (h.1*sourceInverseT x.1 (x.2 j)+h.2 j*sourceInverseV x.1 (x.2 j)) =
      h.1*(sourceInverseT x.1 (x.2 i)-sourceInverseT x.1 (x.2 j))+
      h.2 i*sourceInverseV x.1 (x.2 i)-h.2 j*sourceInverseV x.1 (x.2 j) := by ring
  rw [he]
  have hp : ‖h.1‖≤‖h‖ := norm_fst_le h
  have hi : ‖h.2 i‖≤‖h‖ := (norm_le_pi_norm h.2 i).trans (norm_snd_le h)
  have hj : ‖h.2 j‖≤‖h‖ := (norm_le_pi_norm h.2 j).trans (norm_snd_le h)
  calc
    _ ≤ ‖h.1*(sourceInverseT x.1 (x.2 i)-sourceInverseT x.1 (x.2 j))‖+
        ‖h.2 i*sourceInverseV x.1 (x.2 i)‖+‖h.2 j*sourceInverseV x.1 (x.2 j)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖h‖*(C*H)+‖h‖*(C*H)+‖h‖*(C*H) := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul hp (ht.trans (mul_le_mul_of_nonneg_left hdH hC)) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hi (hv i) (norm_nonneg _) (norm_nonneg _)))
        (mul_le_mul hj (hv j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The inverse-V coordinate projection has norm at most one, independently of N. -/
theorem sourceInverseVCoordinate_fderiv_bound {N : ℕ} (x : SourcePoint N)
    (i : Fin N) (C : ℝ) (hC : 0≤C)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 i))
    (hv : ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (x.1,x.2 i)‖≤C) :
    ‖fderiv ℂ (sourceInverseVCoordinate i) x‖≤C := by
  let L : SourcePoint N →L[ℂ] (ℂ × ℂ) :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)).prod
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ)))
  have hL : ‖L‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro h
    change max ‖h.1‖ ‖h.2 i‖≤1*‖h‖
    simpa only [one_mul] using max_le (norm_fst_le h)
      ((norm_le_pi_norm h.2 i).trans (norm_snd_le h))
  have hh := (inverseV_joint_analytic x.1 (x.2 i) hU).differentiableAt.hasFDerivAt.comp x L.hasFDerivAt
  have he : fderiv ℂ (sourceInverseVCoordinate i) x =
      (fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (x.1,x.2 i)).comp L := hh.fderiv
  rw [he]
  exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
    ((mul_le_mul hv hL (norm_nonneg _) hC).trans_eq (mul_one C))

/-- Actual first jets of inverse-V differences are uniformly bounded. -/
theorem sourceInverseVPair_fderiv_bound {N : ℕ} (x : SourcePoint N)
    (i j : Fin N) (C : ℝ) (hC : 0≤C)
    (hU : ∀ k, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (x.1,x.2 k))
    (hv : ∀ k, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (x.1,x.2 k)‖≤C) :
    ‖fderiv ℂ (fun z => sourceInverseVCoordinate i z-sourceInverseVCoordinate j z) x‖≤2*C := by
  rw [fderiv_fun_sub (sourceInverseVCoordinate_analyticAt x i (hU i)).differentiableAt
    (sourceInverseVCoordinate_analyticAt x j (hU j)).differentiableAt]
  exact (norm_sub_le _ _).trans (by linarith
    [sourceInverseVCoordinate_fderiv_bound x i C hC (hU i) (hv i),
     sourceInverseVCoordinate_fderiv_bound x j C hC (hU j) (hv j)])

end
end IsingBulk.HT22
