From HoTT Require Import HoTT.
From GeneralTT Require Import Syntax.ScopeSystem.
From GeneralTT Require Import Auxiliary.Family.
From GeneralTT Require Import Auxiliary.WellFounded.
From GeneralTT Require Import Auxiliary.Coproduct.
From GeneralTT Require Import Syntax.All.
From GeneralTT Require Import Typing.Context.
From GeneralTT Require Import Typing.Judgement.
From GeneralTT Require Import Presented.PresentedRawRule.
From GeneralTT Require Import Presented.PresentedRawTypeTheory.
From GeneralTT Require Import Presented.TypedRule.

(** In this file: definition of well-typedness of a type-theory. *)

Section WellTypedTypeTheory.

  Context {σ : scope_system}.

  Local Definition is_well_typed (T : presented_raw_type_theory σ) : Type.
  Proof.
    simple refine (forall R : T, TypedRule.is_well_typed _ (tt_rule R)).
    refine (RawTypeTheory.fmap _ _).
    - apply PresentedRawTypeTheory.initial_segment_signature_to_rule_signature.
    - apply PresentedRawTypeTheory.flatten.
  Defined.

End WellTypedTypeTheory.

Record type_theory (σ : scope_system) : Type
  := { tt_presented_raw_type_theory :> presented_raw_type_theory σ
     ; tt_well_typed : is_well_typed tt_presented_raw_type_theory }.
