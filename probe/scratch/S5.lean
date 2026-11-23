import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray

set_option maxSynthPendingDepth 1
set_option autoImplicit false

attribute [-instance] TopCat.Sheaf.instAbelian

open CategoryTheory Opposite TopologicalSpace Limits Abelian AlgebraicGeometry
open GroundTheory.Arith.SchemeCoh

universe w w' u

namespace Probe5

noncomputable section

variable {X : TopCat.{u}}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] {ι : Type w}
  (U : ι → Opens X) {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

theorem c0 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{w'} G n) : x = x := rfl

def c1 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := AddEquiv.refl _

def c2 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := e

def c3 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n :=
  e.trans e

def c4 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n →+ Sheaf.H.{w'} G n := AddMonoidHom.id _

def c5 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n → Sheaf.H.{w'} G n := id

def c6 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x y : Sheaf.H.{w'} G n) : Sheaf.H.{w'} G n := x + y

theorem c7 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (x y : Sheaf.H.{w'} G n) : x + y = x + y := rfl

def c8 (hS : S.ShortExact) [Injective S.X₂] (m : ℕ) :
    Sheaf.H.{w'} S.X₃ (m + 1) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) := hDeltaEquiv hS m

def c9 (hC : IsCechShortExact U S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj U) (m : ℕ) :
    cechH S.X₃.obj U (m + 1) ≃+ cechH S.X₁.obj U (m + 2) := hC.deltaEquiv hI m

def c10 (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact U S.f.hom S.g.hom)
    (hI : CechAcyclic S.X₂.obj U) (m : ℕ)
    (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1)) :
    cechH S.X₁.obj U (m + 2) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  ((hC.deltaEquiv hI m).symm.trans e).trans (hDeltaEquiv hS m)

def c11 {A : Type} [AddCommGroup A] (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (e₁ : A ≃+ Sheaf.H.{w'} G n) (e₂ : Sheaf.H.{w'} G n ≃+ A) : A ≃+ A := e₁.trans e₂

theorem c12 (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (e : Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n) : e.trans e = e.trans e := rfl

section Diag

set_option diagnostics true
set_option diagnostics.threshold 5
set_option Elab.async false

def c1d (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{w'} G n ≃+ Sheaf.H.{w'} G n := AddEquiv.refl _

def c10d (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact U S.f.hom S.g.hom)
    (hI : CechAcyclic S.X₂.obj U) (m : ℕ)
    (e : cechH S.X₃.obj U (m + 1) ≃+ Sheaf.H.{w'} S.X₃ (m + 1)) :
    cechH S.X₁.obj U (m + 2) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  ((hC.deltaEquiv hI m).symm.trans e).trans (hDeltaEquiv hS m)

end Diag

end

noncomputable section Mod

variable {Y : Scheme.{u}}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology Y.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(Y, ⊤)]

def m1 (F : Y.Modules) (n : ℕ) : Module A (Sheaf.H.{w'} (modulesAb F) n) := inferInstance

def m2 {F G : Y.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{w'} (modulesAb F) n →ₗ[A] Sheaf.H.{w'} (modulesAb G) n := H.linearMap A φ n

theorem m3 (F : Y.Modules) (n : ℕ) (a : A) (x : Sheaf.H.{w'} (modulesAb F) n) :
    a • x = a • x := rfl

theorem m4 (F : Y.Modules) (n : ℕ) (x : Sheaf.H.{w'} (modulesAb F) n) : x = x := rfl

end Mod

section Print

set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 400000
set_option pp.deepTerms true

#print Probe5.c1
#print Probe5.c3

end Print

end Probe5
