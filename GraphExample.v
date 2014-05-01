Require Export Graph.

(* ###################################################### *)
(** * Definitions *)
(** Vertices Name [VerName] *)
Definition V4 := index 4.
Definition V3 := index 3.
Definition V2 := index 2.
Definition V1 := index 1.

(** Vertices *)
Definition vtx4 := v_cons V4 nil.
Definition vtx2 := v_cons V2 (cons (pair (pair V4 5) 5) nil ).
Definition vtx3 := v_cons V3 (cons (pair (pair V4 4) 4) 
                             (cons (pair (pair V2 6) 1) nil ) ).
Definition vtx1 := v_cons V1 (cons (pair (pair V2 10) 4) 
                             (cons (pair (pair V3 5) 5) nil ) ).

(** **** Graph Definition:
 s[1] A [2, 4/10] [3, 5/5]
  [2] A [4, 5/5] 
  [3] A [4, 4/4]  [2, 1/6]
 t[4] A []
 *)

(** Graph **)
Definition G := pair (pair (cons vtx1 (cons vtx2 (cons vtx3 (cons vtx4 nil)))) 
                          V1) V4.


Definition G' := pair (pair (cons vtx1 (cons vtx2 (cons vtx3 (cons vtx4 (cons vtx1 nil))))) 
                          V1) V4.

Check G.

(* ###################################################### *)
(** * Test Cases *)
Eval compute in (vertex_lookup G V2).
Eval compute in (vertex_lookup G (index 5)).


(* internal and external nodes *)
Example test_V1_not_internal :
  beq_internal_vertex G V1 = false.
Proof. reflexivity. Qed.

Example test_V2_V3_is_internal :
  andb (beq_internal_vertex G V2) (beq_internal_vertex G V3) = true.
Proof. reflexivity. Qed.

Example test_V4_not_internal :
  beq_internal_vertex G V4 = false.
Proof. reflexivity. Qed.

(* Weight from V1 to V4: V1 -> V3 -> V2 -> V4 *)
Example test_path_weight_V1_V4 :
  path_weight G vtx1 (cons V3 (cons V2 (cons V4 nil))) = Some 16.
Proof. reflexivity. Qed.

Example test_weight_edge_V3V2:
  edge_weight G V3 V2 = Some 6.
Proof. reflexivity. Qed.

(* Flow from V1 to V4: V1 -> V3 -> V2 -> V4 *)
Example test_path_flow_V1_V4 :
  path_flow G vtx1 (cons V3 (cons V2 (cons V4 nil))) = Some 11.
Proof. reflexivity. Qed.

Example test_edge_flow_V3V2:
  edge_flow G V3 V2 = Some 1.
Proof. reflexivity. Qed.

(* Test: Convervation of flow in vertex 3 *)
Example test_vertex_flow_conservation_1 :
  vertex_flow_out G V3 =  vertex_flow_in G V3.
Proof. reflexivity. Qed.

Example test_vertex_flow_conservation_2 :
  beq_weight (vertex_flow_out G V3) (vertex_flow_in G V3) = true.
Proof. reflexivity. Qed.

(* Test: Capacity constraint *)
Example test_capacity_constraint_1 :
  ble_weight (edge_flow G V1 V2) (edge_weight G V1 V2) = true.
Proof. reflexivity. Qed.

(** 
Definition True : Prop := forall (P:Prop), P -> P.

Theorem true_theorem:
        True.
Proof.
        unfold True.
        intros P H.
        apply H.
        Qed.
*)
(*
Definition beq_vertex' (v1 v2: vertex) : Prop :=
  match v1 with
    | v_cons vn1 vlist1 => 
      match v2 with
        | v_cons vn2 vlist2 => 
           if beq_VerName vn1 vn2 then True else False
      end 
  end.

Check beq_nat_refl.

Lemma beq_VerName_refl :
  forall (v :VerName), beq_VerName v v = true.
Proof.
  intros.
  destruct v.
  simpl. rewrite <- beq_nat_refl.
  reflexivity.
Qed.


Lemma test :
  forall (v1 v2 :vertex), v1 = v2 -> beq_vertex' v1 v2.
Proof.
  intros.
  unfold beq_vertex'.
  destruct v1.
  destruct v2. inversion H. simpl.
  rewrite beq_VerName_refl.
  admit.
Qed.
*)

Lemma eq_VerName_dec : 
  forall vn1 vn2 :VerName, {vn1 = vn2} + {vn1 <> vn2}.
Proof.
  intros vn1 vn2.
  destruct vn1 as [n1]. destruct vn2 as [n2].
  destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
  Case "n1 = n2".
    left. rewrite Heq. reflexivity.
  Case "n1 <> n2".
    right. intros contra. inversion contra. apply Hneq. apply H0.
Qed.

Lemma eq_adjacence_dec : 
  forall vls1 vls2 :adjacence, {vls1 = vls2} + {vls1 <> vls2}.
Proof.
  intros vls1 vls2.
  destruct vls1 as [p1 f1]. destruct vls2 as [p2 f2].
  destruct p1 as [vn1 w1].  destruct p2 as [vn2 w2].
  destruct (eq_VerName_dec vn1 vn2) as [Heq | Hneq].
    destruct (eq_nat_dec w1 w2) as [HWeq | HWneq];
    destruct (eq_nat_dec f1 f2) as [HFeq | HFneq];
      try (left; subst; reflexivity);
      try (right; intros contra; inversion contra; auto).
  right. intros contra. inversion contra. auto.
Qed.

Lemma eq_ladj_dec : 
  forall ls1 ls2 :list adjacence, {ls1 = ls2} + {ls1 <> ls2}.
Proof.
  intros ls1 ls2.
  apply list_eq_dec.
  apply eq_adjacence_dec.
Qed.

Lemma eq_vertex_dec : 
  forall v1 v2 :vertex, {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2.
  destruct v1 as [vn1 ls1]. destruct v2 as [vn2 ls2].
  destruct (eq_VerName_dec vn1 vn2) as [Heq | Hneq].
  destruct (eq_ladj_dec ls1 ls2) as [Hleq | Hlneq];
      try (left; subst; reflexivity);
      try (right; intros contra; inversion contra; auto).
  try (right; intros contra; inversion contra; auto).
Qed.


Print NoDup.
Print NoDup_remove_1.
SearchAbout "NoDup".

Lemma nodup_listv :
  forall l :list vertex, NoRep (l).
Proof.
  intros.
  induction l.
  apply NoRep_nil.
  apply NoRep_cons with (f:=beq_vertex). admit.
  assumption.
Qed.


(* Test: is G well-formed? *)
Print G. 
Theorem test_graph_well_formed :
  graph_well_formed G.
Proof.
  unfold G.
  apply (vtx_unique V1 vtx1 G (graph_list G)).
  simpl. reflexivity.
  apply list_eq_dec. apply eq_vertex_dec.
  simpl. reflexivity. 
  apply nodup_listv.
Qed.
