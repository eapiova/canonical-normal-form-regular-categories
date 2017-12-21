Require Import HoTT.
Require Import Auxiliary.Family.
Require Import Proto.ShapeSystems.
Require Import Auxiliary.Coproduct.
Require Import Raw.Syntax.

(* TODO: Might it make more sense to fold these in through [Syntax], so that each construction’s functoriality lemmas can be given with the construction itself? *)

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
    intros hjbi i.
    apply (Fmap_Raw_Syntax f), hjbi.
  Defined.

  Definition Fmap_Hyp_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {hjf} {γ}
    : Hyp_Judgt_Form_Instance Σ hjf γ -> Hyp_Judgt_Form_Instance Σ' hjf γ.
  Proof.
    intros hjbi i.
    apply (Fmap_Raw_Syntax f), hjbi.    
  Defined.

  Definition Fmap_Judgt_Form_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
      {jf}
    : Judgt_Form_Instance Σ jf -> Judgt_Form_Instance Σ' jf.
  Proof.
    destruct jf as [ | hjf].
    - apply Fmap_Raw_Context, f. 
    - cbn. intros Γ_hjfi.
      exists (Fmap_Raw_Context f Γ_hjfi.1). 
      exact (Fmap_Hyp_Judgt_Form_Instance f Γ_hjfi.2). 
  Defined.

  Definition Fmap_Judgt_Instance {Σ Σ'} (f : Signature_Map Σ Σ')
    : Judgt_Instance Σ -> Judgt_Instance Σ'.
  Proof.
    intros jf_jfi.
    exists jf_jfi.1.
    exact (Fmap_Judgt_Form_Instance f jf_jfi.2).
  Defined.

  (* Metavariable extensions are bifunctorial in their two arguments.

   We give the general bifunctoriality action as [Fmap], and the special cases in each argument individually as [Fmap1], [Fmap2]. *)
  Definition Fmap_Metavariable_Extension
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      {a a' : Arity σ} (g : Family_Map a a')
    : Signature_Map (Metavariable_Extension Σ a)
                    (Metavariable_Extension Σ' a').
  Proof.
    apply Fmap_Family_Sum.
    - apply f.
    - apply Fmap_Family_Fmap, g.
  Defined.

  Definition Fmap1_Metavariable_Extension
      {Σ} {Σ'} (f : Signature_Map Σ Σ')
      (a : Arity σ)
    : Signature_Map (Metavariable_Extension Σ a)
                    (Metavariable_Extension Σ' a)
  := Fmap_Metavariable_Extension f (idmap_Family _).

  Definition Fmap2_Metavariable_Extension
      (Σ : Signature σ)
      {a a' : Arity σ} (f : Family_Map a a')
    : Signature_Map (Metavariable_Extension Σ a)
                    (Metavariable_Extension Σ a')
  := Fmap_Metavariable_Extension (idmap_Family _) f.

  Definition Fmap_Raw_Rule {Σ Σ'} (f : Signature_Map Σ Σ')
    : Raw_Rule Σ -> Raw_Rule Σ'.
  Proof.
    intros R.
    exists (RR_metas _ R).
    - refine (Fmap _ (RR_prem _ R)).
      apply Fmap_Judgt_Instance.
      apply Fmap1_Metavariable_Extension, f.
    - refine (Fmap_Judgt_Instance _ (RR_concln _ R)).
      apply Fmap1_Metavariable_Extension, f.
  Defined.

  Definition Fmap_Raw_TT {Σ Σ'} (f : Signature_Map Σ Σ')
    : Raw_Type_Theory Σ -> Raw_Type_Theory Σ'.
  Proof.
    apply Fmap, Fmap_Raw_Rule, f.
  Defined.

End Signature_Maps.

