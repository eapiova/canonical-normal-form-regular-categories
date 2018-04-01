Require Import Auxiliary.Family.
Require Import Proto.ShapeSystem.
Require Import Raw.Syntax.
Require Import Raw.RawStructuralRule.
Require Import Raw.FlatRule.

Section FlatTypeTheory.

  Context {σ : shape_system}.

  (** A flat type theory is just a family of flat rules. *)
  Definition flat_type_theory (Σ : signature σ) : Type
     := family (flat_rule Σ).

  (** The closure system generated by structural rules and the flat type theory [T]. *)
  Local Definition closure_system {Σ : signature σ} (T : flat_type_theory Σ)
    : Closure.system (judgement_total Σ)
    := structural_rule Σ + Family.bind T FlatRule.closure_system.

  (** A derivation in the given flat type theory [T] from hypothesis [H],
      with structural rules included. *)
  Local Definition derivation {Σ : signature σ} (T : flat_type_theory Σ) H
    : judgement_total Σ -> Type
    := Closure.derivation (closure_system T) H.

  (** For a given judgment boundary [jbi],  *)
  Local Definition Derivation_Judgt_Bdry_Instance
      {Σ : signature σ} (T : flat_type_theory Σ)
      {jf} (jbi : Judgement.boundary Σ jf)
      (H : family (judgement_total Σ))
  : Type
  :=
    forall (i : Judgement.presupposition_of_boundary jbi),
      derivation T H (Judgement.presupposition_of_boundary _ i).

End FlatTypeTheory.

Local Definition fmap {σ : shape_system} 
      {Σ Σ' : signature σ} (f : Signature.map Σ Σ')
  : flat_type_theory Σ -> flat_type_theory Σ'.
Proof.
  apply Family.fmap, FlatRule.fmap, f.
Defined.
