From HoTT Require Import HoTT.
From GeneralTT Require Import Auxiliary.Family.
From GeneralTT Require Import Auxiliary.WellFounded.
From GeneralTT Require Import Auxiliary.Coproduct.
From GeneralTT Require Import Syntax.All.
From GeneralTT Require Import Typing.Judgement.
From GeneralTT Require Import Presented.AlgebraicExtension.
From GeneralTT Require Import Presented.PresentedRawRule.
From GeneralTT Require Import Presented.PresentedRawTypeTheory.
From GeneralTT Require Import Presented.TypedRule.
From GeneralTT Require Import Presented.TypeTheory.

Section MartinLöfTypeTheory.
  Context {σ : scope_system}.

  Definition Σ : signature σ.
  Proof.
    refine [< _; _ >].
    - exact (class_type, [< >]). (* U *)
    - simple refine (class_type, [< (class_term, scope_empty σ) >]). (* El *)
  Defined.

  Local Definition U_formation_rule_index
    : (form * arity σ)
  := (form_object class_type  (* Formation of a type *)
       , [< >]).                (* With no (object) premises *)

  Local Definition El_formation_rule_index : (form * arity σ)
    := (form_object class_type
       , [< (class_term, scope_empty σ) >]).

  (* Definition f : *)

  Local Definition theory : type_theory σ.
   simple refine (Build_type_theory _ _ _).
   1: simple refine (Build_presented_raw_type_theory _ _ _).
   - exact ([< U_formation_rule_index ; El_formation_rule_index >]).
   - admit.
   - intros.
     destruct i as [ [] |  ].
     + (* the universe formation rule *)
       simple refine (@Build_rule _ _ _ _ _ _).
       * { simple refine (@Build_algebraic_extension _ _ _ _ _ _ _).
           - simple refine [< >]. (* no equality premises *)
           - simple refine (@Build_well_founded_order _ _ _ _).
             + intros x y.
               refine (match (x, y) with (inl x', inl y') => _ | z => _ end).
               * cbn in x'.
                 exact True.
               * destruct z.
                 destruct f2.
               * destruct z.
                 destruct f1.
             + admit.
             + admit.
           - admit.
           - admit.
         }
       * admit.

     + admit. (* the element formation rule *)
  Admitted. (* [MartinLofTypeTheory.theory] : much work to do *)

  Local Theorem is_well_typed : TypeTheory.is_well_typed theory.
  Proof.
    admit.
  Admitted.  (* [MartinLofTypeTheory.is_well_typed] : much work to do *)

End MartinLöfTypeTheory.
