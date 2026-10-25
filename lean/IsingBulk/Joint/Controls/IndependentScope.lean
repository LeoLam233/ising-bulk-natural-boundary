import IsingBulk.Joint.Final.JointBoundary
import IsingBulk.Joint.FormFactors.AxisRemovability
import IsingBulk.Joint.Geometry.Collars

namespace IsingBulk.Joint.Controls
noncomputable section
open Set Metric

/-- A real open two-complex-variable neighborhood contains points on no
positive-real-ratio temperature line. -/
theorem independent_coupling_in_highDomain :
    ∃ x : ℝ, 0 < x ∧ ((x:ℂ),(x:ℂ)*Complex.I) ∈ highDomain ∧
      ¬ ∃ lam : ℝ, 0 < lam ∧ ∃ z : ℂ, ratioSlice lam z = ((x:ℂ),(x:ℂ)*Complex.I) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp highDomain_isOpen 0 zero_mem_highDomain
  let x := r/2
  have hx : 0 < x := half_pos hr
  have hnorm : ‖((x:ℂ),(x:ℂ)*Complex.I)‖ = x := by
    simp [Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
  refine ⟨x,hx,hball ?_,?_⟩
  · rw [mem_ball,dist_zero_right,hnorm]
    dsimp [x]
    linarith
  · rintro ⟨lam,_,z,he⟩
    have hz : z = (x:ℂ) := congrArg Prod.fst he
    have hw := congrArg (fun K : Coupling => K.2.im) he
    simp [ratioSlice,hz] at hw
    linarith

/-- The actual decoupled axis admits an entire extension despite an ambient
joint boundary at the same point. This refutes the false blanket slice rule. -/
theorem decoupled_axis_has_entire_extension (z : ℂ) :
    HasFullExtension ((fun t : ℂ => (t,0)) ⁻¹' highDomain)
      (fun t => FormFactors.highNormalizedBulk (t,0)) z := by
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ _,Complex.exp,?_,?_⟩
  · intro t _
    exact analyticAt_cexp
  · intro t ht
    exact (FormFactors.highNormalizedBulk_axis ht.2.1).symm

theorem decoupled_tip_mem_frontier :
    (((Real.pi/2:ℝ):ℂ)*Complex.I,0) ∈ frontier highDomain := by
  rw [highDomain_isOpen.frontier_eq]
  refine ⟨closure_high_of_nonstrict ?_ ?_ ?_ ?_,?_⟩
  · simp [abs_of_pos (half_pos Real.pi_pos)]
  · simp
    positivity
  · simp [Real.cos_pi_div_two]
  · simp
  · intro h
    have hi := h.1
    simp [abs_of_pos (half_pos Real.pi_pos)] at hi

/-- Actual counterexample to the invalid implication from ambient obstruction
to obstruction of every analytic restriction. Both statements concern the same
full physical bulk function and the same boundary point. -/
theorem ambient_obstruction_does_not_force_axis_obstruction
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    ¬HasHolomorphicFullExtension highDomain FormFactors.highNormalizedBulk
      ((((Real.pi/2:ℝ):ℂ)*Complex.I),0) ∧
    HasFullExtension ((fun t : ℂ => (t,0)) ⁻¹' highDomain)
      (fun t => FormFactors.highNormalizedBulk (t,0))
      (((Real.pi/2:ℝ):ℂ)*Complex.I) := by
  exact ⟨high_no_holomorphic_full_extension hphys decoupled_tip_mem_frontier,
    decoupled_axis_has_entire_extension _⟩

/-- The logical complex null cone is not the zero vector. -/
theorem complex_quadratic_null_cone_control :
    (1:ℂ)^2 + Complex.I^2 = 0 ∧ ((1:ℂ),Complex.I) ≠ (0 : ℂ × ℂ) := by
  constructor
  · norm_num
  · intro h
    have he := congrArg Prod.fst h
    norm_num at he

end
end IsingBulk.Joint.Controls
