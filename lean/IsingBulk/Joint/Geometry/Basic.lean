import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.Geometry.SpectralAlgebra
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

namespace IsingBulk.Joint
noncomputable section

@[fun_prop] theorem continuous_tanh : Continuous Real.tanh := by
  change Continuous (fun x : ℝ => Real.tanh x)
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

@[fun_prop] theorem continuous_S : Continuous S := Complex.continuous_sinh.comp continuous_fst
@[fun_prop] theorem continuous_T : Continuous T := Complex.continuous_sinh.comp continuous_snd
@[fun_prop] theorem continuous_A : Continuous A := by unfold A; fun_prop
@[fun_prop] theorem continuous_p : Continuous p := continuous_S.mul continuous_T

/-- Compactness of the square proves closedness without dropping a degenerate stratum. -/
theorem spectralSet_isClosed : IsClosed spectralSet := by
  let Q := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let E : Set (Coupling × Q) := {v | A v.1 =
    S v.1 * (v.2.1.1 : ℂ) + T v.1 * (v.2.1.2 : ℂ)}
  have hE : IsClosed E := by
    apply isClosed_eq <;> dsimp only [A, S, T] <;> fun_prop
  have heq : spectralSet = Prod.fst '' E := by
    ext K
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨(K, ⟨(a,b), ha,hb⟩), h, rfl⟩
    · rintro ⟨⟨K, ⟨⟨a,b⟩, ha,hb⟩⟩, h, rfl⟩
      exact ⟨a,ha,b,hb,h⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace E hE

theorem highDomain_isOpen : IsOpen highDomain := by
  exact (isOpen_lt (show Continuous (fun K : Coupling => |K.1.im|) by fun_prop) continuous_const).inter
    ((isOpen_lt (show Continuous (fun K : Coupling => |K.2.im|) by fun_prop) continuous_const).inter
    ((isOpen_lt (show Continuous (fun K : Coupling => Real.cosh K.1.re * Real.tanh |K.2.re|) by fun_prop)
      (show Continuous (fun K : Coupling => Real.cos K.1.im) by fun_prop)).inter
    (isOpen_lt (show Continuous (fun K : Coupling => Real.cosh K.2.re * Real.tanh |K.1.re|) by fun_prop)
      (show Continuous (fun K : Coupling => Real.cos K.2.im) by fun_prop))))

theorem lowDomain_isOpen : IsOpen lowDomain := by
  exact (isOpen_lt continuous_const (show Continuous (fun K : Coupling => K.1.re) by fun_prop)).inter
    ((isOpen_lt continuous_const (show Continuous (fun K : Coupling => K.2.re) by fun_prop)).inter
    ((isOpen_lt (show Continuous (fun K : Coupling => |Real.cos K.1.im|) by fun_prop)
      (show Continuous (fun K : Coupling => Real.cosh K.1.re * Real.tanh K.2.re) by fun_prop)).inter
    (isOpen_lt (show Continuous (fun K : Coupling => |Real.cos K.2.im|) by fun_prop)
      (show Continuous (fun K : Coupling => Real.cosh K.2.re * Real.tanh K.1.re) by fun_prop))))

@[simp] theorem zero_mem_highDomain : (0 : Coupling) ∈ highDomain := by
  simp only [highDomain, Set.mem_ofPred_eq, Prod.fst_zero, Prod.snd_zero,
    Complex.zero_im, Complex.zero_re, abs_zero, Real.cosh_zero, Real.tanh_zero,
    Real.cos_zero, mul_zero]
  exact ⟨by positivity, by positivity, by norm_num, by norm_num⟩

@[simp] theorem zero_not_mem_spectralSet : (0 : Coupling) ∉ spectralSet := by
  rintro ⟨a, ha, b, hb, h⟩
  simp [A, S, T] at h

/-- The complex dispersion identity uses both independent variables. -/
theorem A_sq (K : Coupling) : A K ^ 2 = (1 + S K ^ 2) * (1 + T K ^ 2) := by
  unfold A S T
  have h := Complex.cosh_sq_sub_sinh_sq K.1
  have h' := Complex.cosh_sq_sub_sinh_sq K.2
  calc
    _ = Complex.cosh K.1 ^ 2 * Complex.cosh K.2 ^ 2 := by ring
    _ = _ := by
      rw [show Complex.cosh K.1 ^ 2 = 1 + Complex.sinh K.1 ^ 2 by linear_combination h,
        show Complex.cosh K.2 ^ 2 = 1 + Complex.sinh K.2 ^ 2 by linear_combination h']

theorem corner_identity (K : Coupling) (e f : ℂ) (he : e^2 = 1) (hf : f^2 = 1) :
    A K ^ 2 - (e * S K + f * T K)^2 = (p K - e*f)^2 := by
  rw [A_sq]
  unfold p
  linear_combination -(S K)^2 * he - (T K)^2 * hf - f^2 * he - hf

/-- Axis exchange is a genuine symmetry of the independently defined spectrum. -/
theorem swap_mem_spectralSet_iff (K : Coupling) : K.swap ∈ spectralSet ↔ K ∈ spectralSet := by
  constructor <;> rintro ⟨a, ha, b, hb, h⟩
  · exact ⟨b,hb,a,ha,by simpa [A,S,T,mul_comm,add_comm] using h⟩
  · exact ⟨b,hb,a,ha,by simpa [A,S,T,mul_comm,add_comm] using h⟩

end
end IsingBulk.Joint
