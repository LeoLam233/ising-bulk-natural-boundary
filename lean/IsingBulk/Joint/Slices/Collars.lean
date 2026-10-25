import IsingBulk.Joint.Geometry.Collars
import IsingBulk.Joint.Slices.EdgeTransfer

namespace IsingBulk.Joint
noncomputable section
open Set Metric Filter
open scoped Topology

/-- An inward motion into an interior ball yields the literal component collar. -/
theorem hasScalarCollar_of_inward_motion {D : Set ℂ} (hD : IsOpen D)
    (hm : ∀ P ∈ frontier D, ∀ ε > (0 : ℝ), ∃ f : ℂ → ℂ,
      Continuous f ∧ f P ∈ D ∩ ball P ε ∧
      ∀ Q ∈ D, segment ℝ Q (f Q) ⊆ D) : HasLocalCollar D := by
  intro P hP U hU hPU a ha hPa
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU P hPU
  obtain ⟨f,hf,hfP,hseg⟩ := hm P hP ε hε
  obtain ⟨δ,hδ,hδD⟩ := Metric.isOpen_iff.mp (hD.inter isOpen_ball) (f P) hfP
  let V := ball P ε ∩ f ⁻¹' ball (f P) δ
  have hV : IsOpen V := isOpen_ball.inter (isOpen_ball.preimage hf)
  have hPV : P ∈ V := ⟨mem_ball_self hε,mem_ball_self hδ⟩
  have hVU : V ⊆ U := fun _ h => hεU h.1
  have hcommon : D ∩ V ⊆ connectedComponentIn (D ∩ U) (f P) := by
    intro Q hQ
    have hball : ball (f P) δ ⊆ connectedComponentIn (D ∩ U) (f P) := by
      apply (convex_ball (f P) δ).isPreconnected.subset_connectedComponentIn (mem_ball_self hδ)
      intro x hx
      exact ⟨(hδD hx).1,hεU (hδD hx).2⟩
    have hfQ : f Q ∈ connectedComponentIn (D ∩ U) (f P) := hball hQ.2.2
    have hsq : segment ℝ Q (f Q) ⊆ D ∩ U := by
      intro x hx
      exact ⟨hseg Q hQ.1 hx,hεU ((convex_ball P ε).segment_subset hQ.2.1
        (hδD hQ.2.2).2 hx)⟩
    have hsame := (convex_segment (𝕜 := ℝ) Q (f Q)).isPreconnected.subset_connectedComponentIn
      (right_mem_segment ℝ Q (f Q)) hsq (left_mem_segment ℝ Q (f Q))
    rw [connectedComponentIn_eq hfQ]
    exact hsame
  obtain ⟨b,hbV,hba⟩ := mem_closure_iff.mp hPa V hV hPV
  have hbD := (connectedComponentIn_subset (D ∩ U) a hba).1
  have hbf := hcommon ⟨hbD,hbV⟩
  refine ⟨V,hV,hPV,hVU,?_⟩
  rw [connectedComponentIn_eq hba,← connectedComponentIn_eq hbf]
  exact hcommon


open IsingBulk.Anisotropic

theorem scale_closure_omegaH_mem {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ closure (omegaH lam)) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    t • z ∈ omegaH lam := by
  have hm : MapsTo (ratioSlice lam) (omegaH lam) highDomain := by
    intro w hw
    change w ∈ ratioSlice lam ⁻¹' highDomain
    rwa [highDomain_pullback hlam]
  have hc := hm.closure (ratioSlice_continuous lam) hz
  have hs := scale_closure_high_mem hc ht ht1
  have he : t • ratioSlice lam z = ratioSlice lam (t • z) := by
    ext <;> simp [ratioSlice,Complex.real_smul, mul_left_comm]
  rw [he] at hs
  change t • z ∈ ratioSlice lam ⁻¹' highDomain at hs
  rwa [highDomain_pullback hlam] at hs

theorem omegaH_hasLocalCollar {lam : ℝ} (hlam : 0 < lam) : HasLocalCollar (omegaH lam) := by
  apply hasScalarCollar_of_inward_motion (omegaH_isOpen hlam)
  intro P hP ε hε
  have hc : Continuous (fun t : ℝ => t • P) := by fun_prop
  have hN : (fun t : ℝ => t • P) ⁻¹' ball P ε ∈ 𝓝 (1 : ℝ) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa using isOpen_ball.mem_nhds (mem_ball_self (x := P) hε)
  have hcl : (1 : ℝ) ∈ closure (Ioo 0 1) := by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; simp
  obtain ⟨t,htN,ht⟩ := mem_closure_iff_nhds.mp hcl _ hN
  refine ⟨fun Q => t • Q,by fun_prop,
    ⟨scale_closure_omegaH_mem hlam (frontier_subset_closure hP) ht.1.le ht.2,htN⟩,?_⟩
  intro Q hQ
  have htQ : t • Q ∈ segment ℝ (0:ℂ) Q := by
    refine ⟨1-t,t,by linarith [ht.2],ht.1.le,by ring,?_⟩
    simp
  exact ((convex_segment (𝕜 := ℝ) 0 Q).segment_subset (right_mem_segment ℝ 0 Q) htQ).trans
    ((omegaH_starConvex hlam).segment_subset hQ)

theorem omegaL_hasLocalCollar {lam : ℝ} (hlam : 0 < lam) : HasLocalCollar (omegaL lam) := by
  apply hasScalarCollar_of_inward_motion (omegaL_isOpen hlam)
  intro P hP ε hε
  have hPc : sliceL lam P.im ≤ P.re := by
    exact closure_minimal (fun z hz => (show sliceL lam z.im < z.re from hz).le)
      (isClosed_le ((sliceL_continuous hlam).comp Complex.continuous_im) Complex.continuous_re)
      (frontier_subset_closure hP)
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  refine ⟨fun Q => Q+(δ:ℂ),by fun_prop,⟨?_,?_⟩,?_⟩
  · change sliceL lam (P+(δ:ℂ)).im < (P+(δ:ℂ)).re
    simp only [Complex.add_im,Complex.add_re,Complex.ofReal_im,Complex.ofReal_re,add_zero]
    linarith
  · rw [mem_ball,dist_eq_norm]
    simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
    dsimp [δ]
    linarith
  · intro Q hQ Z hZ
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hZ
    have hi : (a • Q+b • (Q+(δ:ℂ))).im = Q.im := by
      simp only [Complex.add_im,Complex.smul_im,Complex.ofReal_im,add_zero,smul_eq_mul]
      nlinarith [congrArg (fun x : ℝ => x*Q.im) hab]
    have hr : Q.re ≤ (a • Q+b • (Q+(δ:ℂ))).re := by
      simp only [Complex.add_re,Complex.smul_re,Complex.ofReal_re,smul_eq_mul]
      nlinarith [mul_nonneg hb hδ.le,congrArg (fun x : ℝ => x*Q.re) hab]
    change sliceL lam _ < _
    rw [hi]
    exact lt_of_lt_of_le hQ hr

end
end IsingBulk.Joint
