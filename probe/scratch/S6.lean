import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray

set_option maxSynthPendingDepth 1
set_option autoImplicit false

attribute [-instance] TopCat.Sheaf.instAbelian

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry
open GroundTheory.Arith.SchemeCoh

universe w w' u

namespace Probe6

/-! N: a named instance, so the `HasSheafify` proof is an atomic application. -/
noncomputable section N

instance probeSheafify (X : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem n0 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

def n1 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := AddEquiv.refl _

def n3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n :=
  e.trans e

def n5 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n → Sheaf.H.{w'} G n := id

def n6 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x y : Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n := x + y

def n7 (G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (φ : G ⟶ G') (n : ℕ) :
    Sheaf.H.{w'} G n →+ Sheaf.H.{w'} G' n := Sheaf.H.map φ n

def n8 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) : Sheaf.H.{w'} S.X₃ n →+ Sheaf.H.{w'} S.X₁ (n + 1) :=
  hS.extClass.postcomp _ rfl

end N

/-! V: the `HasSheafify` proof is a local hypothesis. -/
noncomputable section V

variable {X : TopCat.{u}}
variable [hs : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

def v1 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := AddEquiv.refl _

def v3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n :=
  e.trans e

def v5 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n → Sheaf.H.{w'} G n := id

def v8 (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (n : ℕ) : Sheaf.H.{w'} S.X₃ n →+ Sheaf.H.{w'} S.X₁ (n + 1) :=
  hS.extClass.postcomp _ rfl

end V

section Print

set_option pp.explicit true
set_option pp.proofs true
set_option pp.maxSteps 400000
set_option pp.deepTerms true

variable {X : TopCat.{u}} in
#check (inferInstance : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u})

end Print

end Probe6
