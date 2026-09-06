module

public import Erdos1201.Vendor.NumberTheory.PNT.ZetaBounds
public import Erdos1201.Vendor.NumberTheory.ZetaFunctionEstimates.ZetaLogDerivativeBounds

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
The residue of `-ζ'/ζ` at the pole `s = 1`: `-(ζ'/ζ)(1+δ) - 1/δ` is `O(1)` as
`δ → 0` along the positive reals (`Z0bound_aux`), restated in terms of
`ZetaFunctionEstimates.logDerivZeta` (`Z0bound`). Bridges
`PNT.ZetaBounds.riemannZetaLogDerivResidueBigO`'s punctured-neighborhood
statement to a one-sided real approach to the pole.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by
  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹
  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO
  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by
    apply tendsto_inf.mpr
    constructor
    · have h_cont : Continuous u := continuous_const.add continuous_ofReal
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds
      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    · simp [tendsto_principal_principal]
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u, ne_eq, add_eq_right, Complex.ofReal_eq_zero]
      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos
  have h_comp := h_F_bigO.comp_tendsto h_tendsto
  convert h_comp using 1
  · ext delta
    simp only [F, u, Function.comp_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply]
    rw [inv_eq_one_div]
    aesop
  · rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end ZetaZeroFreeRegion
