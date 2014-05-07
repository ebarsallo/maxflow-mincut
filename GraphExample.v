Require Export Graph.

(* ###################################################### *)
(** * Definitions *)
(** Vertices Name [VerName] *)
Definition V5 := index 5.  (* not in graph *)
Definition V4 := index 4.
Definition V3 := index 3.
Definition V2 := index 2.
Definition V1 := index 1.


(** Vertices *)
Definition vtx5 := v_cons V5 nil.
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

(* G' is not well-formed since has duplicated vertices*)
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

(* Test: List functions *)
Example test_in1 :
  In vtx5 (graph_list G) beq_vertex = false.
Proof. reflexivity. Qed.

Example test_in2 :
  In vtx4 (graph_list G) beq_vertex = true.
Proof. reflexivity. Qed.

Example test_in3 :
  In vtx1 (graph_list G') beq_vertex = true.
Proof. reflexivity. Qed.


Lemma norepeat_listv :
  forall l :list vertex, no_repeat l.
Proof.
  intros.
  induction l.
  Case "list is empty". apply nr_nil.
Print nr_cons.
  Case "list has elements".
    apply nr_cons. assumption (* IHl *). 
    unfold not. intros. admit.
Qed.


(* Test: is G well-formed? Yes *)
Print G. 
Theorem test_graph_well_formed_G :
  graph_well_formed G.
Proof.
  unfold G.
  apply (vtx_unique V1 vtx1 G (graph_list G)).
  simpl. reflexivity.
  apply list_eq_dec. apply eq_vertex_dec.
  simpl. reflexivity. 
  simpl. 
  apply norepeat_listv.
Qed.

(* Test: is G' well-formed? No *)
Print G'. 
Theorem test_graph_well_formed_G' :
  ~ graph_well_formed G'.
Proof.
  unfold G', not.
  intros. inversion H.
  inversion H1. 
  Abort.

