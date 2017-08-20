Require Import HoTT.
Require Import Family.
Require Import ShapeSystems.
Require Import Coproduct.
Require Import RawSyntax.

Section Signature_Maps.

  Context {σ : Shape_System}.
 
  Definition Signature_Map (Σ Σ' : Signature σ) : Type
    := Family_Map Σ Σ'.

  Definition Family_Map_of_Signature_Map {Σ Σ'}
    : Signature_Map Σ Σ' -> Family_Map Σ Σ'
  := idmap.
  Coercion Family_Map_of_Signature_Map : Signature_Map >-> Family_Map.

  Definition Fmap_Raw_Syntax {Σ Σ'} (f : Signature_Map Σ Σ')
      {cl} {γ}
    : Raw_Syntax Σ cl γ -> Raw_Syntax Σ' cl γ.
  Proof.
    intros t. induction t as [ γ i | γ S ts fts].
    - exact (var_raw i).
    - refine (transport (fun cl => Raw_Syntax _ cl _) _ (symb_raw (f S) _)).
      + exact (ap fst (commutes_Family_Map _ _)).
      + refine (transport
          (fun a : Arity σ => forall i : a,
               Raw_Syntax Σ' (arg_class i) (shape_coproduct γ (arg_pcxt i)))
          _
          fts).
        exact ((ap snd (commutes_Family_Map _ _))^).
  Defined.

  Definition Fmap_Raw_Context {Σ Σ'} (f : Signature_Map Σ Σ')
    : Raw_Context Σ -> Raw_Context Σ'.
  Proof.
    intros Γ.
    exists (Proto_Context_of_Raw_Context Γ).
    intros i. refine (_ (var_type_of_Raw_Context Γ i)).
    apply (Fmap_Raw_Syntax f).
  Defined.

  Definition Fmap_Hyp_Judgt_Bdry_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Hyp_Judgt_Bdry_Instance Σ hjf γ -> Hyp_Judgt_Bdry_Instance Σ' hjf γ.
  Proof.
  Admitted.

  Definition Fmap_Hyp_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Hyp_Judgt_Form_Instance Σ hjf γ -> Hyp_Judgt_Form_Instance Σ' hjf γ.
  Proof.
  Admitted.

End Signature_Maps.
