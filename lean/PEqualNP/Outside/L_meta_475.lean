import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  have hmem : PEqualNP.MetaComplexity.CoverPromise.fresh φ ∈
      PEqualNP.MetaComplexity.CoverPromise.vars (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) := by
    simp only [PEqualNP.MetaComplexity.CoverPromise.vars,
      PEqualNP.MetaComplexity.CoverPromise.cvcFormula,
      List.flatMap_append, List.mem_append, List.mem_toFinset]
    right
    simp
  refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  simp only [PEqualNP.MetaComplexity.CoverPromise.cvcGraph,
    PEqualNP.MetaComplexity.CoverPromise.satGraph,
    PEqualNP.MetaComplexity.CoverPromise.satAdj]
  exact ⟨rfl, by decide, hmem⟩
