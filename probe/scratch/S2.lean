import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray

set_option maxSynthPendingDepth 1
set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry
open GroundTheory.Arith.SchemeCoh

universe w w' u

namespace Probe2

noncomputable section

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type w}
  (U : ι → Opens X) {S S' : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

set_option diagnostics true
set_option diagnostics.threshold 5
set_option Elab.async false

def a1 (m : ℕ) (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1)) :
    cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1) := e

def a2 (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact U S.f.hom S.g.hom)
    (hI : CechAcyclic S.X₂.obj U) (m : ℕ)
    (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1)) :
    cechH S.X₁.obj U (m + 2) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  ((hC.deltaEquiv hI m).symm.trans e).trans (hDeltaEquiv hS m)

def a3 (hS : S.ShortExact) [Injective S.X₂] (m : ℕ) :
    Sheaf.H.{w'} S.X₃ (m + 1) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) := hDeltaEquiv hS m

def a4 (hC : IsCechShortExact U S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj U) (m : ℕ) :
    cechH S.X₃.obj U (m + 1) ≃+ cechH S.X₁.obj U (m + 2) := hC.deltaEquiv hI m

theorem a5 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

def a6 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := AddEquiv.refl _

def a7 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := (e.trans e).trans e

end

section Print

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

set_option pp.explicit true
set_option pp.maxSteps 200000
set_option pp.deepTerms true

#check @Probe2.a5
#check @Probe2.a6
#print Probe2.a7

end Print

end Probe2
