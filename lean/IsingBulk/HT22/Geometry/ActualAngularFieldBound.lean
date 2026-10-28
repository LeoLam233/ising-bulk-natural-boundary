import IsingBulk.HT22.Transport.FieldNeighborhood.UniformFrameBudget
import IsingBulk.HT22.Transport.FieldNeighborhood.ActualInverseVScale
import IsingBulk.Preferred22.AngularFieldBound

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Metric IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The new fixed-v field, not the old moving-coordinate representative,
has one inverse shell-radius loss uniformly in particle count. -/
theorem actual_angular_field_shell_bound_uniform_cap (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b,
    ∃ C ε₀ τ₀ δB : ℝ,
      0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ a : Fin N, ‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ a‖≤
        C*(N:ℝ)^2/r := by
  obtain ⟨cb,hcb,hcba,hbudgetSource⟩ := actual_mixed_field_uniform_frame_budget_uniform_cap b M hM
  obtain ⟨cu,hcu,hcua,huSource⟩ := actual_inverse_uniform_domain_uniform_cap b
  obtain ⟨cv,hcv,_hcva,hvSource⟩ := actual_inverseV_square_root_scale_uniform_cap b
  let cap := min cb (min cu cv)
  refine ⟨cap,lt_min hcb (lt_min hcu hcv),(min_le_left _ _).trans_lt hcba,?_⟩
  intro B
  obtain ⟨eb,tb,db,heb,htb,hdb,hdbB,hbudget⟩ := hbudgetSource B
  obtain ⟨R,hR,hfield⟩ := hbudget 0
  obtain ⟨ru,κ,Cu,D,hru,hκ,hCu,_hconv,hupart,huimage⟩ := huSource B
  obtain ⟨Cv,ev,tv,dv,hCv,hev,htv,hdv,_hdvB,hvbound⟩ := hvSource B
  obtain ⟨tm,htm,hmatrix⟩ := preferredContourMatrix_uniform_half_row B.p B.m B.smooth B.m_smooth
    B.periodic B.m_periodic
    (fun x => by rw [abs_of_nonneg (B.lower_bound x)]; exact B.upper_bound x)
    (fun x => by change |B.p (-x)|≤1; rw [abs_of_nonneg (B.lower_bound (-x))]; exact B.upper_bound (-x))
  let e := min eb (min ru ev)
  let t := min tb (min ru (min tv tm))
  let d := min db (min ru dv)
  let L := Cu+Cv*Real.sqrt M
  let C := 4*L*(M+R*Real.sqrt M)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨C,e,t,d,by dsimp [C]; positivity,
    lt_min heb (lt_min hru hev),lt_min htb (lt_min hru (lt_min htv htm)),
    lt_min hdb (lt_min hru hdv),(min_le_left _ _).trans_lt hdbB,?_⟩
  intro N hN ε τ μ r hε he hτ ht hr hTM θ hθ hwindow i k hext hgap a
  have heb' : ε<eb := he.trans_le (min_le_left _ _)
  have heru : ε<ru := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hev' : ε<ev := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htb' : τ<tb := ht.trans_le (min_le_left _ _)
  have htru : τ<ru := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htv' : τ<tv := ht.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htm' : τ<tm := ht.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdb' : d≤db := min_le_left _ _
  have hdru : d≤ru := (min_le_right _ _).trans (min_le_left _ _)
  have hdv' : d≤dv := (min_le_right _ _).trans (min_le_right _ _)
  have hcb' : cap≤cb := min_le_left _ _
  have hcu' : cap≤cu := (min_le_right _ _).trans (min_le_left _ _)
  have hcv' : cap≤cv := (min_le_right _ _).trans (min_le_right _ _)
  have hboxb (j : Fin N) : -db≤θ j+b.b ∧ θ j≤min cb B.delta := by
    have hh := hθ j
    exact ⟨by linarith [hh.1],hh.2.trans (min_le_min hcb' le_rfl)⟩
  have hboxv (j : Fin N) : -dv≤θ j+b.b ∧ θ j≤min cv B.delta := by
    have hh := hθ j
    exact ⟨by linarith [hh.1],hh.2.trans (min_le_min hcv' le_rfl)⟩
  have hboxu (j : Fin N) : -b.b-ru≤θ j ∧ θ j≤cu := by
    have hh := hθ j
    exact ⟨by linarith [hh.1],hh.2.trans ((min_le_left _ _).trans hcu')⟩
  let s := IsingBulk.Branch.radialParameter b.alpha ε
  let v := sourceCoordinate τ B.p B.m s θ
  have hs : ‖s-preferredSelectedPoint b‖≤ru := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact heru.le
  have hv (j : Fin N) : v j∈D :=
    huimage N hN ε τ (by simpa only [abs_of_pos hε] using heru)
      (by simpa only [abs_of_nonneg hτ] using htru) θ hboxu j (mem_closedBall_self hκ.le)
  have hUt (j : Fin N) : ‖inverseT s (v j)‖≤L :=
    (hupart s (v j) hs (hv j)).2.1.trans (by dsimp [L]; exact le_add_of_nonneg_right (by positivity))
  have hUv (j : Fin N) : ‖inverseV s (v j)‖≤L := by
    have hh := hvbound N hN ε τ μ r hε hev' hτ htv' hr θ hboxv hwindow j
    have hh' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTM) hCv.le
    change ‖inverseV s (v j)‖≤_ at hh
    exact hh.trans (hh'.trans (by dsimp [L]; linarith))
  have hB : ‖sourceResidual s v‖≤R*(N:ℝ)^2*Real.sqrt M/r := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have hh := hfield N hN ε τ μ r hε heb' hτ htb' hr hTM θ hboxb hwindow i k hext hgap [] (by simp) j
    simp only [frameJet,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero,pow_one] at hh
    have hT : 0 < |μ|+r+ε := by positivity
    have hsq : Real.sqrt (|μ|+r+ε)≠0 := (Real.sqrt_pos.mpr hT).ne'
    change ‖sourceResidual s v j‖≤_ at hh
    calc
      _ ≤ R*(N:ℝ)^2/(r/Real.sqrt (|μ|+r+ε)) := hh
      _ = R*(N:ℝ)^2*Real.sqrt (|μ|+r+ε)/r  := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hTM) (by positivity)) hr.le
  have hMi := (preferred_matrix_inverse_of_row_three_quarters (preferredContourMatrix τ B.p B.m θ)
    (fun j => (hmatrix τ hτ htm'.le N hN θ j).trans (by norm_num))).2
  have hh := preferredAngularRepresentative_norm_bound (preferredContourMatrix τ B.p B.m θ)
    (fun j => inverseT s (v j)) (fun j => inverseV s (v j)) (sourceResidual s v)
    (by norm_num : (0:ℝ)≤4) hL.le (by positivity : 0≤R*(N:ℝ)^2*Real.sqrt M/r) hMi hUt hUv hB a
  have hrM : r≤M := by linarith [abs_nonneg μ]
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn2 : (1:ℝ)≤(N:ℝ)^2 := by nlinarith
  change ‖preferredAngularRepresentative _ _ _ _ a‖≤_
  calc
    _ ≤ 4*(L+L*(R*(N:ℝ)^2*Real.sqrt M/r)) := hh
    _ = 4*L*(r+R*(N:ℝ)^2*Real.sqrt M)/r := by field_simp
    _ ≤ 4*L*((M+R*Real.sqrt M)*(N:ℝ)^2)/r := by
      apply div_le_div_of_nonneg_right _ hr.le
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤4*L)
      nlinarith [mul_le_mul_of_nonneg_left hn2 hM.le]
    _ = C*(N:ℝ)^2/r := by dsimp [C]; ring

theorem actual_angular_field_shell_bound (b : PreferredBranchData)
    (B : PreferredCoareaBump b) (M : ℝ) (hM : 0<M) :
    ∃ cap C ε₀ τ₀ δB : ℝ,
      0<cap ∧ cap<b.alpha ∧ 0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ a : Fin N, ‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ a‖≤
        C*(N:ℝ)^2/r := by
  obtain ⟨cap,hcap,hcapa,hall⟩ := actual_angular_field_shell_bound_uniform_cap b M hM
  obtain ⟨C,e,t,d,hC,he,ht,hd,hdB,hbound⟩ := hall B
  exact ⟨cap,C,e,t,d,hcap,hcapa,hC,he,ht,hd,hdB,hbound⟩

theorem actual_angular_field_shell_bound_full (b : PreferredBranchData)
    (M : ℝ) (hM : 0<M) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ C ε₀ τ₀ δB : ℝ,
      0<C ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ a : Fin N, ‖angularField τ B.p B.m (IsingBulk.Branch.radialParameter b.alpha ε) θ a‖≤
        C*(N:ℝ)^2/r := by
  obtain ⟨cap,hcap,hcapa,hall⟩ := actual_angular_field_shell_bound_uniform_cap b M hM
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨C,e,t,d,hC,he,ht,hd,hdB,hbound⟩ := hall B
  refine ⟨C,e,t,d,hC,he,ht,hd,hdB,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap a
  apply hbound N hN ε τ μ r hε hεr hτ hτr hr hTM θ _ hwindow i k hext hgap a
  intro j
  exact ⟨(hθ j).1,le_min ((hθ j).2.trans hB.le) (hθ j).2⟩

end
end IsingBulk.HT22.Geometry
